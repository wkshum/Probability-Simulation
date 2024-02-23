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


noncomputable section


open Real BigOperators Fintype Finset

namespace DiscreteProbability

/-
  All probability distibutions in this file are defined over a finite alphabet
-/
variable {α : Type*} [DecidableEq α] [Fintype α] [Nonempty α ]
variable {β : Type*} [DecidableEq β] [Fintype β] [Nonempty β]


/-
 Data structure for discrete probability disribution

 a probabilty disribution function P is the function called dist
    bundled with two additional conditions. The type `α` represents the sample space.
    `α` is assumed to have fintite type, so that we can sum over all elements in `α`.

    The first condition `NonNeg` imposes that the values of the functions `dist`
    are nonnegative.

    The second condtiion `sum_eq_one` requires that the function
    values sum to 1.

  We make a term with type Discreteist α act like a function by making it FunLike.
  If `P` is a structure with type DiscreteDist `α`, we can directly obtain the
  probability at `x` by `P x`.

-/

@[ext]
structure DiscreteDist (α : Type*) [Fintype α] [Nonempty α] where
  dist : α → ℝ                      -- the pmf as a function from α to ℝ
  NonNeg : ∀ i : α ,  dist i ≥ 0     -- dist i is nonnegative for all i
  sum_eq_one : ∑ i : α , dist i = 1   -- sum of dist i over all is is equal to 1

-- Extend the type DiscreteDist `α` to a function-like type
instance instFunLike : FunLike (DiscreteDist α) α ℝ  where
  coe p a := (p.dist a)
  coe_injective' p q h := by
    ext a
    exact congrFun h a


-- In a discrete probability space, the sum of all probabilities is equal to 1.

theorem prob_sum_to_one (P: DiscreteDist α ): ∑ x:α , P x = 1 := P.sum_eq_one

/-
Discrete probability distribution has values less than or equal to 1
-/
theorem prob_le_one (f : DiscreteDist α ) :   ∀ j : α , f j ≤ 1 := by
  intro j
  let g (j i : α ) : ℝ  := if i=j then (f j) else 0
  have h₀ : ∀ i : α  , g j i ≤ f i := by
    intro i
    by_cases h2 : i=j
    · simp [h2]
    · simp [h2]
      exact f.NonNeg i
  calc
    f j = ∑ i , g j i := by simp [Finset.sum_mul]
        _ ≤  ∑ i , f i  :=  Finset.sum_le_sum fun i _ ↦ h₀ i
        _ = 1 := f.sum_eq_one





----------------------------------------

/-
Example of probability distribution
-/



/-
  Example: Uniform distribution on {0,1,2,...,n-1}
  It is assumed that n is not zero in order to avoid the degenerate case.
-/
def UniformDist (n:ℕ) [NeZero n] : DiscreteDist (Fin n) where
  dist := λ (i : Fin n) => 1/(n:ℝ)
  NonNeg := by simp
  sum_eq_one := by norm_num


/-
 Example: Uniform distribution on a finite set
 We assume that the type `α` is nonempty and is of finite type.
-/
def UniformDist' (α : Type*) [Fintype α] [Nonempty α]: DiscreteDist α where
  dist := λ (i : α) => 1/(Fintype.card α)
  NonNeg := by simp
  sum_eq_one := by
    simp
    refine mul_inv_cancel ?_
    exact Nat.cast_ne_zero.mpr (Fintype.card_ne_zero)  -- use assumption that cardinality is not zero




/-
 Sum of product of two functions equal the product of sums
-/

theorem sum_product_eq_product_sum  (P : α → ℝ) (Q : β  → ℝ ) :
      ∑ x : α, ∑ y:β , (Q y)*(P x) = (∑ x : α, P x)*(∑ y:β , (Q y)) := by
  have (x:α ) : (∑ y:β , Q y)*(P x) =  ∑ y:β , (Q y)*(P x)   := Finset.sum_mul Finset.univ Q (P x)
  rw [(Fintype.sum_congr ((∑ y : β, Q y) * P · ) (∑ y : β, Q y * P · ) this).symm]
  have : ∑ x:α , (∑ y:β , (Q y))*(P x)  = ∑ x:α , (P x)*(∑ y:β , (Q y)) := by
    refine Fintype.sum_congr (fun i ↦ (∑ y:β , (Q y))*(P i)) (fun i ↦ (P i)*(∑ y:β , (Q y))) ?_
    intro X
    ring
  rw [this]
  rw [(Finset.sum_mul Finset.univ (fun i ↦ P i) (∑ y : β, Q y)).symm]

theorem sum_product_eq_product_sum'  (P : α → ℝ) (Q : β  → ℝ ) :
      ∑ x : α, ∑ y:β , (P x)*(Q y) = (∑ x : α, P x)*(∑ y:β , (Q y)) := by
  have h : ∑ x : α, ∑ y:β , (P x)*(Q y) = ∑ x : α, ∑ y:β , (Q y)*(P x) := by
    refine Fintype.sum_congr (fun x:α => ∑ y:β , (P x)*(Q y)) (fun x:α => ∑ y:β , (Q y)*(P x) ) ?_
    intro x
    refine Fintype.sum_congr (fun y:β => P x * Q y) (fun y:β => Q y * P x) ?_
    intro y
    ring
  rw [h]
  exact sum_product_eq_product_sum P Q


-- Coupling two distributions on the product space so that the marginal distributions
-- are independent.
@[simp]
def ProductDist (P : DiscreteDist α) (Q: DiscreteDist β) : DiscreteDist (α×β) where
  dist := fun z: α×β =>  (Q z.2)*(P z.1)
  NonNeg := by
    intro x
    simp
    exact mul_nonneg  (Q.NonNeg x.2) (P.NonNeg x.1)
  sum_eq_one := by
    rw [Fintype.sum_prod_type]
    rw [sum_product_eq_product_sum P Q]
    rw [prob_sum_to_one P]
    rw [prob_sum_to_one Q]
    ring

-- Example: uniform distribution over a product of two finite sets
@[simp]
def UniformDistProduct (α : Type*) (β : Type*) [Fintype α] [Fintype β] [Nonempty α] [Nonempty β]
     :=  ProductDist (UniformDist' α) (UniformDist' β)


/-
  Given two distributions P and Q, we define a joint distribution R of P and Q as a distribution defined on
  the  Cartisian product of the sample spaces of P and Q, respectively, so that the two marginal
  distributions are identical to P and Q.
-/

@[ext]
class JointDist2 {α : Type*} {β : Type*} [Fintype α]  [Fintype β] [Nonempty α] [Nonempty β]
       (P : DiscreteDist α) (Q : DiscreteDist β) extends DiscreteDist (α×β) where
  -- dist := λ (i : Fin n) => 1/(n:ℝ)
  -- NonNeg := by simp
  -- sum_eq_one := by norm_num
  marginal_1 : ∀ x:α , (∑ y:β, dist ⟨x,y⟩ = P x)
  marginal_2 : ∀ y:β , (∑ x:α, dist ⟨x,y⟩ = Q y)


/- The joint disribution is also called a coupling of P and Q-/
def IsJointDist (R : DiscreteDist (α × β) ) (P : DiscreteDist α) (Q : DiscreteDist β) :=
  (∀ x:α , (∑ y:β, R ⟨x,y⟩ = P x)) ∧ (∀ y:β, (∑ x:α , R ⟨x,y⟩ =Q y))

/-
 There is one canonical way to create a coupling of distribution P and distribution Q,
 making them independent in the joint distibution.
 We take this as the default joint distribution.
 To verify that it is really an instance of joint distribution, we prove that the two
 marginal distributions of `ProductDist P Q` are precisely `P` and `Q`.
-/

instance InstanceInhabitedJointDist : Inhabited (JointDist2 (P : DiscreteDist α) (Q : DiscreteDist β)) where
  default :=
  {
    dist := ProductDist P Q

    NonNeg := by
      show ∀ (i : α × β), (ProductDist P Q) i ≥ 0
      intro z
      have : (ProductDist P Q) z = (Q z.2)*(P z.1) := rfl
      rw [this]
      have h1 : Q z.2 ≥ 0 := Q.NonNeg z.2
      have h2 : P z.1 ≥ 0 := P.NonNeg z.1
      exact mul_nonneg h1 h2

    sum_eq_one := by
      show ∑ i : α × β, (ProductDist P Q) i = 1
      have : ∀ z:α×β , (ProductDist P Q) z = (Q z.2)*(P z.1) := by
        intro z
        rfl
      rw [Fintype.sum_congr _ _ this]
      simp
      rw [sum_product_eq_product_sum P Q]
      have : ∑ x : α, P x =1:= P.sum_eq_one
      rw [this]
      have : ∑ y : β, Q y =1:= Q.sum_eq_one
      rw [this]
      ring

    marginal_1 := by
      have h1 : ∀ x:α , ∀ y:β, (ProductDist P Q) (x,y) = (Q y)*(P x) := by
        intro x y
        simp_all only [ProductDist]
        rfl
      intro x
      show ∑ y : β, (ProductDist P Q).dist (x, y) = P x
      rw [Fintype.sum_congr (fun y:β => (ProductDist P Q).dist (x,y)) (fun y:β => (Q y)*(P x)) (h1 x)]
      rw [← Finset.sum_mul Finset.univ Q (P x)]
      have : ∑ y:β, Q y = 1 := Q.sum_eq_one
      rw [this]
      ring

    marginal_2 := by
      have h2 : ∀ y:β, ∀ x:α , (ProductDist P Q).dist (x,y) = (Q y)*(P x) := by
        intro y x
        simp_all only [ProductDist]
      intro y
      show ∑ x : α , (ProductDist P Q).dist (x, y) = Q y
      rw [Fintype.sum_congr (fun x:α => (ProductDist P Q).dist (x,y)) (fun x:α  => (Q y)*(P x)) (h2 y)]
      rw [Fintype.sum_congr (fun x:α => Q y * P x) (fun x:α => P x * Q y) ]
      rw [← Finset.sum_mul Finset.univ P (Q y)]
      have : ∑ x:α  , P x = 1 := P.sum_eq_one
      rw [this]
      ring
      · intro a
        ring

    : JointDist2 P Q
  }


-- This example show that the marginals of the product obtained from P and Q are
-- equal to disributions P and Q
-- (It repeats the proof in the previous theorem)
example (P : DiscreteDist α ) (Q : DiscreteDist β) (R: DiscreteDist (α × β)) (h : R = ProductDist P Q) :
  IsJointDist R P Q := by
  rw [IsJointDist]
  have h1 : ∀ x:α , ∀ y:β, R.dist (x,y) = (Q y)*(P x) := by
    intro x y
    simp_all only [ProductDist]
  have h2 : ∀ y:β, ∀ x:α , R.dist (x,y) = (Q y)*(P x) := by
    intro y x
    simp_all only [ProductDist]
  apply And.intro
  · -- Show that the left marginal distribution is P
    intro x
    show ∑ y : β, R.dist (x, y) = P x
    rw [Fintype.sum_congr (fun y:β => R.dist (x,y)) (fun y:β => (Q y)*(P x)) (h1 x)]
    rw [← Finset.sum_mul Finset.univ Q (P x)]
    have : ∑ y:β, Q y = 1 := Q.sum_eq_one
    rw [this]
    ring
  · -- Show tha the right marginal distribution is Q
    intro y
    show ∑ x : α , R.dist (x, y) = Q y
    rw [Fintype.sum_congr (fun x:α => R.dist (x,y)) (fun x:α  => (Q y)*(P x)) (h2 y)]
    rw [Fintype.sum_congr (fun x:α => Q y * P x) (fun x:α => P x * Q y) ]
    rw [← Finset.sum_mul Finset.univ P (Q y)]
    have : ∑ x:α  , P x = 1 := P.sum_eq_one
    rw [this]
    ring
    · intro a
      ring



---------------------------------------------------------






/-

 Useful lemmas about summation

-/

-- Split the domain of summation into two disjoint parts
lemma split_summation_domain (F : α → ℝ )  (p : α → Prop )  [DecidablePred p] :
   ∑ i:α , F i = (∑ i: {i: α // ¬ p i } , F i) + (∑ i: {i: α // p i } , F i)  := by

  have  : Set.toFinset {x | ¬p x} = (Set.toFinset {x | p x})ᶜ := by
    ext x
    rw [Set.mem_toFinset, Finset.mem_compl, Set.mem_toFinset]
    trivial
  rw [← Finset.sum_toFinset_eq_subtype (fun i:α => (p i)) _]
  rw [← Finset.sum_toFinset_eq_subtype (fun i:α => (¬ p i)) _]
  rw [this]
  rw [Finset.sum_compl_add_sum (Set.toFinset {x | p x}) F]



-- We can ignore some zero terms when computing a finite sum.
-- The condition `h` encodes the knowledge that whenever `g x` is true,
-- the function value `F x` is equal to 0

lemma sum_eq_sum_nz_term (F : α → ℝ ) (g: α → Prop) (h : ∀ x: α , (g x) → F x = 0)
 [DecidablePred g] :
        ∑ i:α , F i  = (∑ i: {i: α // ¬ g i } , F i) := by
  have h₀ : ∑ i: {i: α // g i } , F i = 0 := by
    rw [← Finset.sum_toFinset_eq_subtype (fun i:α => (g i)) F]
    refine Finset.sum_eq_zero ?h
    intro x hx
    have : x ∈ {x | g x } := Set.mem_toFinset.mp hx
    exact h x this
  rw [split_summation_domain F (fun i:α => (g i))]
  conv =>
    lhs
    congr
    rfl
    rw [h₀]
  ring

-- As a special case of the previous lemma, we record the fact that
-- it suffices to sum over the nonzero terms when computing a finite sum
lemma sum_eq_sum_over_support (F: α → ℝ ):
        ∑ i:α , F i  = (∑ i: {i: α // F i ≠ 0 } , F i) := by
  refine sum_eq_sum_nz_term F (F · = 0) ?_
  intro x hx
  exact hx



end DiscreteProbability


end -- section






















/-
-- Example: uniform distribution over a product of two finite sets
def dist_mn (m n : ℕ ) (hm: m > 0) (hn: n> 0): DiscreteDist (Fin m × Fin n) where
  dist := λ (_i : Fin m × Fin n) => (m*n : ℝ )⁻¹
  NonNeg := by
    intro i
    simp
    have h₁ : (m:ℝ)⁻¹ ≥ 0 := inv_nonneg.mpr (le_of_lt (Nat.cast_pos.mpr hm))
    have h₂ : (n:ℝ)⁻¹ ≥ 0 := inv_nonneg.mpr (le_of_lt (Nat.cast_pos.mpr hn))
    exact mul_nonneg h₂ h₁
  sum_eq_one := by
    dsimp
    simp
    have h₁ : Finset.univ.card = (Fintype.card (Fin m × Fin n)) := by rfl
    rw [h₁]
    rw [Fintype.card_prod (Fin m) (Fin n) ]
    rw [Fintype.card_fin m, Fintype.card_fin n]
    simp
    calc
      (m:ℝ) * (n:ℝ) * ((n:ℝ )⁻¹ * (m:ℝ )⁻¹)
         = (m:ℝ)* (m:ℝ )⁻¹ * (n:ℝ) * (n:ℝ )⁻¹ := by ring
       _ = 1 * (n:ℝ) * (n:ℝ )⁻¹ := by rw [mul_inv_cancel (Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp hm))]
       _ = (n:ℝ) * (n:ℝ)⁻¹ := by ring
       _ =  1 := by rw [mul_inv_cancel (Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp hn))]



-/





-------------------------------------------------

/-
The rest of the file is junkyark
-/


/-
  Samples low-level functions used in the proof
-/

-- #check Subtype.forall

-- #check Finset.sum_toFinset_eq_subtype

-- #check Finset.sum_sub_distrib

-- #check Finset.sum_mul

-- #check Equiv.subtypeEquivRight

-- #check Finset.sum_union

-- #check Finset.sum_compl_add_sum s f
/-

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

example (f: α → ℝ ) (a:ℝ ): (∑ i, f i) * a = ∑ i, f i * a := by
  exact Finset.sum_mul Finset.univ f a

example (h: n = Fintype.card α) :  n = ∑ i:α , 1  :=
  calc
   n = Fintype.card α := by rw [h]
   _ = ∑ i:α , 1 := by exact Fintype.card_eq_sum_ones


example (hn : n = Fintype.card α) (hnz : Fintype.card α ≠ 0) : ∑ i : α , (1/(n:ℝ)) = 1 := by
  simp
  rw [hn]
  exact mul_inv_cancel (Nat.cast_ne_zero.mpr hnz)

example (m:ℕ ) (h: m≠ 0) : (m:ℝ) ≠ 0 := by exact Nat.cast_ne_zero.mpr h

example (m:ℕ) (h: m> 0) : m ≠ 0 := by exact Nat.pos_iff_ne_zero.mp h

example (a:ℝ) (h: a≠ 0) : a*a⁻¹ = 1:= by exact mul_inv_cancel h

example (β : Type*) [Fintype β] : Fintype.card (α × β) = (Fintype.card α)*(Fintype.card β) := by
  exact Fintype.card_prod α β

example (m : ℕ ): Fintype.card (Fin m) = m := by exact Fintype.card_fin m

example (a b : ℕ ) : (a*b :ℝ) = (a:ℝ) *(b:ℝ) := by exact rfl

example (a b:ℝ ) : a⁻¹ * b⁻¹ = (a*b)⁻¹ := by exact (mul_inv a b).symm

example (a : ℝ ) (h: a > 0) : a ≥ 0 := by exact le_of_lt h

example (a: ℕ ) (h: a> 0) : (a:ℝ ) > 0 := by exact Nat.cast_pos.mpr h

example (a:ℝ ) (h :a ≥ 0) : a⁻¹ ≥ 0 := by exact inv_nonneg.mpr h

-/

/-

An unnecessarily complicated proof
lemma split_summation_domain' (F : α → ℝ)  (p : α → Prop )  [DecidablePred p] :
    ∑ i:α , F i  =  (∑ i: {i: α // ¬ p i } , F i) + (∑ i: {i: α // p i } , F i)  := by

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


-/

/-

-- Example: uniform distribution over a product of two finite sets
def dist_mn (m n : ℕ ) (hm: m > 0) (hn: n> 0): DiscreteDist (Fin m × Fin n) where
  dist := λ (_i : Fin m × Fin n) => (m*n : ℝ )⁻¹
  NonNeg := by
    intro i
    simp
    have h₁ : (m:ℝ)⁻¹ ≥ 0 := inv_nonneg.mpr (le_of_lt (Nat.cast_pos.mpr hm))
    have h₂ : (n:ℝ)⁻¹ ≥ 0 := inv_nonneg.mpr (le_of_lt (Nat.cast_pos.mpr hn))
    exact mul_nonneg h₂ h₁
  sum_eq_one := by
    dsimp
    simp
    have : Finset.univ.card = (Fintype.card (Fin m × Fin n)) := by rfl
    rw [this]
    rw [Fintype.card_prod (Fin m) (Fin n) ]
    rw [Fintype.card_fin m, Fintype.card_fin n]
    simp
    calc
      (m:ℝ) * (n:ℝ) * ((n:ℝ )⁻¹ * (m:ℝ )⁻¹)
         = (m:ℝ)* (m:ℝ )⁻¹ * (n:ℝ) * (n:ℝ )⁻¹ := by ring
       _ = 1 * (n:ℝ) * (n:ℝ )⁻¹ := by rw [mul_inv_cancel (Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp hm))]
       _ = (n:ℝ) * (n:ℝ)⁻¹ := by ring
       _ =  1 := by rw [mul_inv_cancel (Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp hn))]

-/
