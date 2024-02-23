import Mathlib.Tactic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog

import MyProject.DiscreteProbability

noncomputable section


open Real BigOperators Fintype Finset
open DiscreteProbability

namespace entropy

/-
  All probability distibutions in this file are defined over a finite alphabet
-/
variable {α : Type*} [DecidableEq α] [Fintype α] [Nonempty α ]
variable {β : Type*} [DecidableEq β] [Fintype β] [Nonempty β]



/-
 Shannon entropy for probability distribution over a finite sample space
-/

-- Shannon entropy is a function of a discrete pobability distribution
-- The function negMulLog  f(x) = -x log x
--   is defined as 0 when x = 0


def H (f : DiscreteDist α) : ℝ :=
  ∑ i : α , negMulLog (f i)


-- Binary entropy function
def h_binary (p:ℝ) : ℝ := negMulLog p + negMulLog (1-p)

notation:max "H(" P ")" => H P

-- Another form of the definition

theorem entropy_def (f: DiscreteDist α ) : H f = - ∑ x, (f x) * log (f x) := by
  have H_def : ∀ i:α , negMulLog (f i) = (f i) * log (f i) * (-1) := by
    intro i
    dsimp [negMulLog]
    ring
  calc
    H f = ∑ i : α , negMulLog (f i) := by dsimp [H]
     _  = ∑ i : α , (f i) * log (f i)*(-1) := by rw [Fintype.sum_congr _ _  H_def]
      _ = (∑ i : α , (f i) * log (f i))*(-1) := by rw [sum_mul univ _ _ ]
      _ = - ∑ x, (f x) * log (f x) := by ring


-- In the definition of entropy we can only sum over outcomes that have positive probabilities.

theorem entropy_sum_over_support (f: DiscreteDist α) :
      H f = ∑ i : {i : α // f i ≠ 0} , Real.negMulLog (f i) := by
  simp [H]
  refine sum_eq_sum_nz_term (fun i:α => Real.negMulLog (f i)) (f · = 0 )  ?_
  -- using the lemma sum_eq_sum_nz_term, it remains to prove that
  --   f.dist x = 0 implies negMulLog (f.dist x) = 0
  intro x hx
  dsimp
  rw [hx]
  exact Real.negMulLog_zero



/-
The basic inequality in information theory:    log x ≤ x-1 for positive x
with equality if and only if x=1
-/

example (x:ℝ) (hpos : x > 0) : Real.log x ≤ x - 1 := Real.log_le_sub_one_of_pos hpos

-- example (h1: x>0) (h2: x≠ 1) : Real.log x < x-1 := Real.log_lt_sub_one_of_pos h1 h2

theorem eq_one_of_pos_of_log_eq_sub_one (hpos: x>0) : log x = x-1 → x=1 := by
  intro h
  by_contra h1
  have h2 : log x < x-1 := Real.log_lt_sub_one_of_pos hpos h1
  exact (ne_of_lt h2) h


/-
Lower and upper bound on Shannon entopy
-/

-- Entropy is nonnegative
theorem entropy_ge_zero (f : DiscreteDist α) : (H f) ≥ 0 := by
  have h1 :  ∀ i : α , f i ≤ 1 := prob_le_one f  -- The value of f i is probability
  dsimp [H, negMulLog]
  simp [sum_mul]
  apply Finset.sum_nonpos
  intro i
  have : f i ≥ 0 := f.NonNeg i
  simp [mul_log_nonpos this (h1 i)]




-- If entropy is zero, then there exists an outcome x with probability 1
theorem eq_entropy_eq_zero (P: DiscreteDist α) :
     H P = 0 → ∃! x:α , P x = 1 ∧ ∀ y:α , y≠ x → P y = 0 := by sorry





/- Gibb's inequaliy ∑_{x} P(x) log (P(x)/Q(x)) ≥ 0

Sketch of proof:

  ∑_{x} P(x) log (Q(x)/P(x))                          (Step 0)
  ∑_{x: P x ≠ 0} P(x) log (Q(x)/P(x))                 (Step 1)
≤ ∑_{x: P x ≠ 0} P(x) [Q(x)/P(x) - 1]                 (Step 2)
≤ ∑_{x} Q(x) - ∑_{x} P(x)                             (Step 3)
= 0                                                   (Step 4)

-/

theorem Gibbs_inequality {P Q : α→ℝ} (hP: ∀ i, P i ≥ 0) (hQ: ∀ i, Q i ≥ 0)
  (hSum:  ∑ i, P i = ∑ i, Q i) (h: ∀ i, P i ≠ 0 → Q i ≠ 0) :

   ∑ i, (P i)* log (P i/Q i) ≥ 0 := by

  have : ∀ i , (P i)*log (P i/Q i) = (P i)*log (Q i/P i)*(-1) := by
    intro i
    have h₁' : log (Q i/P i)⁻¹ = - log (Q i/P i) := by exact log_inv (Q i/P i)
    have h₁'':  (P i / Q i) = (Q i/P i)⁻¹ := by field_simp
    calc
      (P i)*log (P i/Q i) = (P i)*log (Q i/P i)⁻¹ := by rw [h₁'']
                        _ = (P i)* (- log (Q i/P i)) := by rw [h₁']
                        _ =  (P i)*log (Q i/P i)*(-1) := by ring

  rw [sum_congr (fun i=>(P i)*log (P i/Q i)) (fun i=>(P i)*log (Q i/P i)*(-1)) this]
  have : (∑ i, (P i)*log ((Q i/P i)))*(-1) = ∑ i, ((P i)*log ((Q i/P i))*(-1)) := by
    exact sum_mul univ _ (-1)
  rw [← this]
  simp [neg_nonneg.mpr]

  show  ∑ i, (P i)* log (Q i/P i) ≤ 0          -- step 0

  have : ∑ i, P i * log (Q i/ P i) = ∑ i : {i // P i ≠ 0}, P i * log (Q i / P i) := by
    refine sum_eq_sum_nz_term (fun i => (P i)*log (Q i/P i)) (fun i => P i = 0) ?_
    intro i hi
    dsimp
    rw [hi]
    ring
  rw [this]

  show  ∑ i:{i // P i ≠ 0}, (P i)* log (Q i/P i) ≤ 0          -- step 1

  have h₂ : ∀ i,  P i ≠ 0 → (P i)*log (Q i/P i)  ≤ (P i)*(Q i/P i - 1) := by
    intro i hi
    have hi' : P i ≠ 0 := hi
    have hPi_pos : P i > 0 := by exact Ne.lt_of_le (id (Ne.symm hi')) (hP i)
    have hQi_pos : Q i > 0 := by exact Ne.lt_of_le (id (Ne.symm (h i hi'))) (hQ i)
    have : (Q i)/(P i) > 0 := by exact div_pos hQi_pos hPi_pos
    have basic_inequality : log (Q i/P i)  ≤ (Q i)/(P i) - 1 := by
      exact Real.log_le_sub_one_of_pos this
    exact (mul_le_mul_left hPi_pos).mpr basic_inequality

  have h₃ : ∑ i : {i // P i ≠ 0}, (P i)*log (Q i/P i) ≤ ∑ i : {i // P i ≠ 0}, (P i)*(Q i/P i - 1) := by
    refine Finset.sum_le_sum ?_
    simp only [Subtype.forall]
    intro x
    intro hx   -- hx is the condition P x ≠ 0
    simp
    exact h₂ x hx

  -- It suffices to prove the following inequality
  suffices h_step2 : ∑ i : { i // P i ≠ 0}, (P i)*(Q i/P i - 1) ≤ 0     -- step 2
    from le_trans h₃ h_step2

  have h₄:  ∑ i : { i // P i ≠ 0}, (P i)*(Q i/P i - 1) ≤ ∑ i, (Q i - P i) := by   -- step 3
    have h₄' : ∑ i, (P i)* (Q i / P i - 1) = ∑ i : {i // P i ≠ 0} , (P i)*(Q i/P i - 1) := by
      refine sum_eq_sum_nz_term _ (P · = 0) ?_
      intro x hx
      simp at hx
      rw [hx]
      norm_num
    rw [← h₄']
    refine Finset.sum_le_sum ?_
    intro i _
    by_cases h_zero : P i = 0
    · -- The case P i = 0
      rw [h_zero]
      simp
      exact hQ i
    · -- The case P i ≠ 0
      have : P i * (Q i/ P i - 1) = Q i  - P i := by
        calc
           P i * (Q i/ P i - 1)
            =  Q i * (P i/ P i) - P i := by ring
          _ =  Q i * 1 - P i := by rw [div_self h_zero]
          _ =  Q i - P i := by ring
      exact Eq.le this

  have h₅  : ∑ i, (Q i - P i ) = 0 := by   -- step 4
    rw [Finset.sum_sub_distrib]
    rw [hSum]
    ring

  rw [h₅] at h₄
  exact h₄


theorem log_sum_inequality (a b : α→ℝ) (ha: ∀ i, a i ≥ 0) (hb: ∀ i, b i ≥ 0)
  (hA:  ∑ i, a i > 0) (hB: ∑ i, b i>0) (h: ∀ i, a i ≠ 0 → b i ≠ 0) :

     ∑ i, (a i)* log (a i/b i) ≥ (∑ i, a i) * log ((∑ i, a i)/(∑ i, b i)) := by

  sorry

lemma log_div_eq_log_minus_log {a b : α → ℝ} (h : ∀ i:α , a i ≠ 0 → b i ≠ 0) :
     ∀ i:α , (a i) * log (a i / b i) = (a i)*log (a i) - (a i)* log ( b i) := by
  intro i
  by_cases ha : a i = 0
  · -- assume a i = 0
    rw [ha]
    ring
  · -- assume a i ≠ 0
    have hb : b i ≠ 0 := h i ha
    have h' : log (a i / b i) = log (a i) - log (b i) := by exact log_div ha hb
    rw [ congrArg (HMul.hMul (a i)) h']
    ring



-- If random variable X takes at most K values, then  H(X) ≤ log K

theorem entropy_le_log_suppsize  (f : DiscreteDist α):  (H f) ≤ Real.log (Fintype.card α) := by

  let K := Fintype.card α   -- cardinary of alphabet size = K
  have hKpos : K > 0 := by exact Fintype.card_pos

  have h1 :  (K:ℝ)⁻¹ ≠ 0 := by   -- K as a real number is not equal to 0
    apply inv_ne_zero    -- suffices to prove K ≠ 0
    apply Nat.cast_ne_zero.mpr
    exact ne_of_gt hKpos       -- suffices to prove K > 0

  have h2 : ∀ _x : α, (K:ℝ)⁻¹ ≥ 0 := by
    intro _
    exact LT.lt.le (inv_pos.mpr (Nat.cast_pos.mpr hKpos))

  have h3 : ∑ x:α , f x = ∑ _x :α , (K:ℝ)⁻¹  := by
    have h3' : ∑ x, f x = 1:= by exact f.sum_eq_one
    have h3'': ∑ _x:α, (K:ℝ)⁻¹ = 1 := by
      rw [sum_congr (fun _x:α => (K:ℝ)⁻¹) (fun x:α => 1*(K:ℝ)⁻¹) ]
      have :  (∑ x:α, 1)* (K:ℝ)⁻¹ = ∑ x:α, 1*(K:ℝ)⁻¹  := by exact sum_mul univ _ (K:ℝ)⁻¹
      rw [← this]
      simp
      refine mul_inv_cancel ?_
      exact Nat.cast_ne_zero.mpr (Fintype.card_ne_zero)
      · intro _
        ring
    exact Eq.trans h3' h3''.symm

  have h4 : ∀ x , f x ≠ 0 → (K:ℝ)⁻¹ ≠ 0 := by exact fun x _ ↦ h1

  -- apply Gibbs inequality
  have hG :  ∑ x, (f x)* log (f x/ (K:ℝ)⁻¹) ≥ 0 := by exact Gibbs_inequality f.NonNeg h2 h3 h4

  have h5 : ∑ x, (f x)* log (f x/ (K:ℝ)⁻¹) = ∑ x, (f x) * log (f x) - ∑ x, (f x)*log (K:ℝ)⁻¹ := by
    rw [sum_congr _ _ ( log_div_eq_log_minus_log h4)]
    exact Finset.sum_sub_distrib

  have h6 : (∑ x, (f x))*log (K:ℝ)⁻¹ = ∑ x, (f x)*log (K:ℝ)⁻¹  := by
    exact sum_mul univ _ (log (K:ℝ)⁻¹)

  have h7 : ∑ x, (f x)= 1:= by exact f.sum_eq_one

  calc
    H f = - ∑ x, (f x)*log (f x) := by exact entropy_def f
      _ = - ∑ x, (f x)*log (f x) + 0 := by ring
      _ ≤ - ∑ x, (f x)*log (f x) + ∑ x, (f x)*log (f x/ (K:ℝ)⁻¹) := by rel [hG]
      _ = - ∑ x, (f x)*log (f x) + (∑ x, (f x)*log (f x) - ∑ x, (f x)*log (K:ℝ)⁻¹) := by rw [h5]
      _ = - (∑ x, (f x)*log (K:ℝ)⁻¹) := by ring
      _ = - ((∑ x, (f x))*log (K:ℝ)⁻¹) := by rw [← h6]
      _ = - (∑ x, (f x)) * log (K:ℝ)⁻¹ := by ring
      _ = - (1) * log (K:ℝ)⁻¹ := by rw [h7]
      _ = - (log (K:ℝ)⁻¹) := by simp
      _ = - (-log (K:ℝ)) := by rw [log_inv (K:ℝ)]
      _ = log K := by ring



/-
 Uniform distribution on n outcomes has entropy log n
-/
theorem unif_dist_entropy (P : DiscreteDist α) (h: ∃ n:ℕ, n ≠ 0 ∧ ∀ (x:α), P x = 1/n) :
     H(P) = log n := by
  sorry

example {n:ℕ} [NeZero n] {P: DiscreteDist (Fin n)} (hP :  P= UniformDist n ):
  H(P) = log n := by sorry

example (P : DiscreteDist (Fin 2)) : H(P) = h_binary (P 0) := by sorry


theorem Gibb_inequality_eq_hold (P Q : DiscreteDist α)
  (h: ∑ x, negMulLog (P x) = ∑ x, -(P x) * log (Q x)) : P = Q := by sorry

end entropy

end -- section