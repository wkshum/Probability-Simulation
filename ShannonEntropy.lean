import Mathlib.Tactic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog

/-

Objectives:

* We define Shannon entropy for finite and discrete probability distribution. Expectations are finite sums
and hence measure theory is avoided. (A full-blown formulation of entropy was done in the project of
polynomial Friemann-Ruzsa conjecture.)

* A discrete distribution is defined as a nonnegative real-valued function on a finite sample space, so that
the sum of all components is equal to 1. If the probabilities are p_i, for i ranging over the sample space,
the Shannon entropy is defined as the sum of - p_i log p_i. When p_i =0, the value of p_i log p_i is
defined as 0.

The function -x log x is implemented by negMulLog, which has just been introduced in Mathlib.

* The main result is the proof of the inequality that entropy is bounded between 0 and log(K), where K is the
cardinality of the sample space. This is split into two theorems:

theorem entropy_ge_zero

theorem entropy_le_log_suppsize



Natural log is employed throughout. The unit of entropy is nat.

-/





namespace entropy

noncomputable section

open BigOperators

/-
  Assume all probability distibutions are defined over a finite alphabet
-/
variable {α : Type*} [DecidableEq α] [Fintype α]


/-
 Data structure for discrete probability disribution
-/


structure DiscreteDist (α : Type*) [Fintype α] where
  dist : α → ℝ
  NonNeg : ∀ i : α ,  dist i ≥ 0
  sum_eq_one : (∑' (i : α) , dist i) = 1



-- Example: prob. distribution over a prouct of two finite sets
def dist12 : DiscreteDist (Fin 3 × Fin 4) where
  dist := λ (i : Fin 3× Fin 4) => 1/12
  NonNeg := by
    intro i
    simp
    norm_num
  sum_eq_one := by
    norm_num


/-
  Example: Uniform distribution on {1,2,...,n}
-/
def uniform_dist (n:ℕ) (hpos: n> 0) : DiscreteDist (Fin n) where
  dist := λ (i : Fin n) => 1/(n:ℝ)
  NonNeg := by
    simp
  sum_eq_one := by
    have h2: n ≠ 0 := by exact Nat.pos_iff_ne_zero.mp hpos
    norm_num
    refine mul_inv_cancel ?_
    exact Nat.cast_ne_zero.mpr h2


/-
 Example: Uniform distribution on a finite set
-/
def uniform_dist'  (hnz : Fintype.card α ≠ 0) : DiscreteDist α where
  dist := λ (i : α) => 1/(Fintype.card α)
  NonNeg := by simp
  sum_eq_one := by
    simp
    refine mul_inv_cancel ?_
    exact Nat.cast_ne_zero.mpr hnz



/-
Discrete probability distribution has values less than or equal to 1
-/
theorem prob_le_one (f : DiscreteDist α ) :
    ∀ j : α , f.dist j ≤ 1 := by
  intro j
  let g (j : α ) (i : α ) : ℝ  := if i=j then f.dist j else 0
  have h₀ : ∀ i : α  , g j i ≤ f.dist i := by
    intro i
    by_cases h2 : i=j
    · simp [h2]
    · simp [h2, f.NonNeg]
  calc
    f.dist j = ∑ i , g j i := by simp [Finset.sum_mul]
        _ ≤  ∑ i , f.dist i  := by exact Finset.sum_le_sum fun i _ ↦ h₀ i
        _ =  ∑' i , f.dist i := by exact (tsum_fintype fun b ↦ f.dist b).symm
        _ = 1 := f.sum_eq_one





/-

 Useful lemmas about summation

-/

-- Split the domain of summation into two disjoint parts
lemma split_summation_domain (F : α → ℝ )  (p : α → Prop )  [DecidablePred p] :
   ∑ i:α , F i = (∑ i: {i: α // ¬ p i } , F i) + (∑ i: {i: α // p i } , F i)  := by
  have h₀ :  ∀ i:α , (ite (¬ p i) (F i) 0) + (ite (p i) (F i) 0) = F i:= by
    intro i
    by_cases h : p i
    repeat simp [h]
  have h₁ : (∑ i: {i: α // p i } , F i) = (∑ i , ite (p i) (F i) 0) := by
    rw [← Finset.sum_toFinset_eq_subtype (fun i:α => (p i)) F]
    rw [← Fintype.sum_extend_by_zero]
    refine Fintype.sum_congr _ _ ?_
    intro x
    simp only [Set.mem_toFinset]
    simp
  have h₂ : (∑ i: {i: α // ¬ p i } , F i) = (∑ i , ite (¬ p i) (F i) 0) := by
    rw [← Finset.sum_toFinset_eq_subtype (fun i:α => (¬ p i)) F]
    rw [← Fintype.sum_extend_by_zero]
    refine Fintype.sum_congr _ _ ?_
    intro x
    simp only [Set.mem_toFinset]
    simp
  rw [← Fintype.sum_congr (fun i:α=> (ite (¬ p i) (F i) 0) + (ite (p i) (F i) 0)) F h₀]
  rw [Finset.sum_add_distrib]
  rw [h₁, h₂]

-- When computing a sum, it suffices to sum over the nonzero terms
lemma sum_eq_sum_over_support (F: α → ℝ ):
        ∑ i:α , F i  = (∑ i: {i: α // F i ≠ 0 } , F i) := by
  have h₀ : ∑ i: {i: α // F i = 0 } , F i = 0 := by
    rw [← Finset.sum_toFinset_eq_subtype (fun i:α => (F i = 0)) F]
    refine Finset.sum_eq_zero ?h
    intro x hx
    have h: x ∈ {x | F x = 0} := by exact Set.mem_toFinset.mp hx
    exact h
  rw [split_summation_domain F (fun i:α => (F i = 0))]
  conv =>
    lhs
    congr
    rfl
    rw [h₀]
  ring

lemma sum_eq_sum_nz_term (F G : α → ℝ ) (h : ∀ x: α , G x =0 → F x = 0):
        ∑ i:α , F i  = (∑ i: {i: α // G i ≠ 0 } , F i) := by
  have h₀ : ∑ i: {i: α // G i = 0 } , F i = 0 := by
    rw [← Finset.sum_toFinset_eq_subtype (fun i:α => (G i = 0)) F]
    refine Finset.sum_eq_zero ?h
    intro x hx
    have h': x ∈ {x | G x = 0} := by exact Set.mem_toFinset.mp hx
    have h'' : G x = 0 := h'
    exact h x h''
  rw [split_summation_domain F (fun i:α => (G i = 0))]
  conv =>
    lhs
    congr
    rfl
    rw [h₀]
  ring


---------------------------------------------------


/-
 Shannon entropy function for finite distribution
-/
def H (f : DiscreteDist α) : ℝ :=
  ∑ i : α , Real.negMulLog (f.dist i)




-- In the definition of entropy we can only sum over outcomes that have positive probabilities.

theorem entropy_sum_over_support (f: DiscreteDist α) :
      H f = ∑ i : {i : α // f.dist i ≠ 0} , Real.negMulLog (f.dist i) := by
  have h₀ : ∑ i: {i:α // f.dist i = 0} , Real.negMulLog (f.dist i) = 0 := by
    rw [← Finset.sum_toFinset_eq_subtype (fun i:α => (f.dist i = 0)) (fun i:α => Real.negMulLog (f.dist i))]
    refine Finset.sum_eq_zero ?h
    intro _ hx
    rw [Set.mem_toFinset.mp hx]
    exact Real.negMulLog_zero
  simp [H]
  rw [split_summation_domain (fun i:α => Real.negMulLog (f.dist i)) (fun i:α => (f.dist i = 0))]
  conv =>
    lhs
    congr
    rfl
    rw [h₀]
  ring



/-
The basic inequality in information theory:    log x ≤  x-1 for positive x
-/
example (x:ℝ) (hpos : x > 0) : Real.log x ≤ x - 1 :=
  Real.log_le_sub_one_of_pos hpos




/-
Lower and upper bound on Shannon entopy
-/

-- Entropy is nonnegative
theorem entropy_ge_zero (f : DiscreteDist α) : (H f) ≥ 0 := by
  have h1 :  ∀ i : α , f.dist i ≤ 1 := prob_le_one f
  dsimp [H, Real.negMulLog]
  simp [Finset.sum_mul]
  apply Finset.sum_nonpos
  intro i
  simp [Real.mul_log_nonpos (f.NonNeg i) (h1 i)]





-- If random variable X takes at most n values, then  H(X) ≤ log n

theorem entropy_le_log_suppsize  (hpos : (Fintype.card α)> 0) (f : DiscreteDist α) :
          (H f) ≤ Real.log (Fintype.card α) := by

  let K := Fintype.card α   -- cardinary of alphabet size = K
  have hKnez :  (K:ℝ) ≠ 0 := by   -- K as a real number is not equal to 0
    refine Nat.cast_ne_zero.mpr ?_
    apply ne_of_gt
    calc
        0 < Fintype.card α := by rel [hpos]
        _ = K := rfl

  have h₀ :  ∑ i : {i:α // f.dist i ≠ 0}  , (f.dist i) = 1 := by
    rw [← sum_eq_sum_over_support f.dist]
    rw [← tsum_fintype fun b ↦ f.dist b]
    rw [f.sum_eq_one]

  have h₁ : Real.log K = ∑ i : {i // f.dist i ≠ 0}, f.dist i * Real.log K := by
    have h₂ := by
      exact Finset.sum_toFinset_eq_subtype (fun i:α => (f.dist i ≠ 0)) (fun i:α => (f.dist i)*(Real.log K))
    have h₃ := by
      exact Finset.sum_toFinset_eq_subtype (fun i:α => (f.dist i ≠ 0)) (fun i:α => (f.dist i))
    rw [← Finset.sum_mul, h₃, h₀] at h₂
    simp at h₂
    exact h₂

  apply sub_nonpos.mp  -- It suffices to show   H f - Real.log K ≤ 0
  rw [entropy_sum_over_support f, h₁]
  rw [← Finset.sum_sub_distrib]

  have h₄ : ∑ i : { i : α // f.dist i ≠ 0 }, (Real.negMulLog (f.dist i) - f.dist i * Real.log K)
      = ∑ i : {i // f.dist i ≠ 0} , (f.dist i) * (Real.log ((f.dist i)* K)⁻¹)  := by
    refine Fintype.sum_congr _ _ ?_
    simp only [Subtype.forall]
    intro i hi
    have h₅ : Real.negMulLog (f.dist i) = -(f.dist i)*Real.log (f.dist i) := by rfl
    rw [h₅]
    calc
      -f.dist i * Real.log (f.dist i) - f.dist i * (Real.log K)
            = - (f.dist i) * (Real.log (f.dist i) +  Real.log K) := by ring
          _ = - (f.dist i) * (Real.log ((f.dist i)* K)) := by rw [Real.log_mul hi hKnez]
          _ = (f.dist i) * (- Real.log ((f.dist i)* K)) := by ring
          _ = (f.dist i) * (Real.log ((f.dist i)* K)⁻¹) := by rw [Real.log_inv]
  rw [h₄]

  have h₆ : ∑ i : {i:α // f.dist i ≠ 0}, (f.dist i) * (Real.log ((f.dist i)* K)⁻¹)
     ≤  ∑ i : {i:α // f.dist i ≠ 0} , (f.dist i)* (((f.dist i)*(K:ℝ))⁻¹ - 1) := by
    refine Finset.sum_le_sum ?_
    simp only [Subtype.forall]
    intro x
    intro hx
    intro _
    have hf_nng : 0 ≤ f.dist x := f.NonNeg x  -- f.dist x is larger than or equal 0
    have hf_pos : 0 < f.dist x  := by exact Ne.lt_of_le (Ne.symm hx) hf_nng
    have hpos1 : 0< (f.dist x * ↑(Fintype.card α))⁻¹ := by
      refine inv_pos.mpr ?_
      exact Real.mul_pos hf_pos (Nat.cast_pos.mpr hpos)
    have basic_inequality :
       (Real.log (f.dist x * ↑(Fintype.card α))⁻¹ ) ≤ (((f.dist x * ↑(Fintype.card α))⁻¹ - 1)) := by
      exact Real.log_le_sub_one_of_pos hpos1
    exact (mul_le_mul_left hf_pos).mpr basic_inequality

  have h₇ : ∑ i : {i:α // f.dist i ≠ 0} , (f.dist i)* (((f.dist i)*(K:ℝ))⁻¹ - 1)
     ≤  ∑ i : α  , ((K:ℝ)⁻¹ - f.dist i ) := by
    have h₇' : ∑ i : α,  (f.dist i)* (((f.dist i)*(K:ℝ))⁻¹ - 1)
        = ∑ i : {i:α // f.dist i ≠ 0} , (f.dist i)* (((f.dist i)*(K:ℝ))⁻¹ - 1) := by
      refine sum_eq_sum_nz_term _ (fun i:α => f.dist i) ?_
      intro x
      intro hx
      simp at hx
      rw [hx]
      norm_num
    rw [← h₇']
    refine Finset.sum_le_sum ?_
    intro x
    intro _
    by_cases hf_zero : f.dist x = 0
    · rw [hf_zero]
      simp
    · have h₇'': f.dist x * ((f.dist x * ↑K)⁻¹ - 1) = (↑K)⁻¹  - f.dist x := by
        calc
          f.dist x * ((f.dist x * ↑K)⁻¹ - 1) = f.dist x * (f.dist x * ↑K)⁻¹ - f.dist x := by ring
          _ =  f.dist x * (f.dist x)⁻¹ * (↑K)⁻¹  - f.dist x := by ring
          _ = 1*(↑K)⁻¹  - f.dist x := by rw [mul_inv_cancel hf_zero]
          _ = (↑K)⁻¹  - f.dist x := by ring
      exact Eq.le h₇''

  have h₈  : ∑ i : α , ((K:ℝ)⁻¹ - f.dist i ) = 0 := by
    have h₉ : ∑ i : α , (K:ℝ)⁻¹ = 1 := by
      simp
      refine mul_inv_cancel ?_
      refine Nat.cast_ne_zero.mpr ?_
      exact Nat.pos_iff_ne_zero.mp hpos
    have h₁₀ : ∑ i : α , f.dist i = 1 := by
      rw [(tsum_fintype fun b ↦ f.dist b).symm]
      exact f.sum_eq_one
    have h₁₁ : ∑ i : α , ((K:ℝ)⁻¹ - f.dist i ) =
       ∑ i : α , (K:ℝ)⁻¹ - ∑ i : α  , f.dist i := by
         exact Finset.sum_sub_distrib
    rw [h₁₁, h₁₀, h₉]
    ring

  exact ge_trans (ge_trans (Eq.le h₈) h₇) h₆

  done






/-
  Samples of the low-level functions used in the proof
-/

-- #check Subtype.forall

-- #check Finset.sum_toFinset_eq_subtype

-- #check Finset.sum_sub_distrib

-- #check Finset.sum_mul

-- #check Finset.sum_toFinset_eq_subtype

-- #check Equiv.subtypeEquivRight



-- x*log x is defined as 0 when x=0
example {x : ℝ} (h : x =0) : Real.negMulLog x = 0 := by
  rw [h]
  exact Real.negMulLog_zero

example {x:ℝ}  : Real.negMulLog x = -x * Real.log x := rfl

theorem nonneg  (f: α → ℝ)  (h: ∀ i : α  , f i ≥ 0 ):
  ∑ i, f i ≥ 0 := by
    calc
      ∑ i, f i ≥ ∑ i, 0 := by exact Finset.sum_le_sum fun i _ ↦ h i
      _ = 0 := by exact Fintype.sum_eq_zero (fun _ ↦ 0) (congrFun rfl)

theorem nonpos  (f: α → ℝ)  (h: ∀ i : α  , f i ≤  0 ):
  ∑ i, f i ≤  0 := by
    calc
      ∑ i, f i ≤  ∑ i, 0 := by exact Finset.sum_le_sum fun i _ ↦ h i
      _ = 0 := by exact Fintype.sum_eq_zero (fun _ ↦ 0) (congrFun rfl)

theorem monotone  (f: α → ℝ) (g: α → ℝ) (h: ∀ i : α  , f i ≤ g i ):
  ∑ i, f i ≤  ∑ i , g i := by
   exact Finset.sum_le_sum fun i _ ↦ h i

theorem additive  (f: α → ℝ) (g: α → ℝ) (_: α → ℝ) :
  ∑ i, (f i + g i) = ∑ i, f i + ∑ i , g i := by exact Finset.sum_add_distrib

example  (f: α → ℝ) (g: α → ℝ)(h: ∀ i : α  , f i = g i ) : ∑ i, f i =  ∑ i , g i := by
 exact Fintype.sum_congr f g h

example (h: n = Fintype.card α) :  n = ∑ i:α , 1  :=
  calc
   n = Fintype.card α := by rw [h]
   _ = ∑ i:α , 1 := by exact Fintype.card_eq_sum_ones


example (hn : n = Fintype.card α) (hnz : Fintype.card α ≠ 0) : ∑ i : α , (1/(n:ℝ)) = 1 := by
  simp
  rw [hn]
  exact mul_inv_cancel (Nat.cast_ne_zero.mpr hnz)
