/-
Copyright (c) 2025-2026 Steven Herbert. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Steven Herbert
-/

import Mathlib

/-!
# ProbabilityVector

Stochastic matrices are frequently applied to vectors that are: finite, over the non-negative reals,
and with unit `ℓ₁` norm. Such vectors naturally represent finite discrete probability distributions,
however we do not need the full machinary of probability theory for the results and hence this file
formalises just those properties that we do need (and in the way we need them).

Vectors are typically denoted `x`.


## Main definitions

* `IsProbVector`
* `L2normSQ`
* `UniformDist`

-/

namespace ProbabilityVector

open BigOperators
open Classical
open Std
open Finset

variable {α : Type*}


/-- Any vector of non-negative reals that sums to one is a discrete probability distribution -/
noncomputable def IsProbVector (x : α → ℝ) (s : Finset α) : Prop :=
  (∑ i ∈ s, x i = 1) ∧ (∀ i ∈ s, 0 ≤ x i) ∧ (∀ i ∉ s, x i = 0)

-- # Support and basic API lemmas

---[ADDED-BY-SUPERVISOR] -----------------------
/-- All elements of a probability vector are non-negative -/
lemma IsProbVector.nonneg {x : α → ℝ} {s : Finset α} (i : α) (hx : IsProbVector x s) : 0 ≤ x i := by
  by_cases i ∈ s
  case pos h => exact hx.2.1 _ h
  case neg h => rw [hx.2.2 _ h]
-------------------------------------------------

/-- The support of a (probability) vector is the set of indices of its nonzero elements.
    This is defined a little more generally to apply to any vector -/
noncomputable def Support (x : α → ℝ) (s : Finset α) : Finset α :=
  s.filter (fun i => x i ≠ 0)

/-- The support is a subset of the total range of a vector -/
lemma Support_leq_full (x : α → ℝ) (s : Finset α) : #(Support x s) ≤ #s := by
  unfold Support
  simp only [ne_eq]
  exact card_filter_le s fun i ↦ ¬x i = 0

/-- Outside the range of a probability distribution the value is zero (by definition) -/
lemma ProbVector_zero_outside_range (x : α → ℝ)
    (s : Finset α) (hp : IsProbVector x s) : ∀ i : α, i ∉ s → x i = 0 := by
  unfold IsProbVector at hp
  exact ((hp).right).right

/-- Probability vector values are non-negative -/
lemma ProbVector_nonneg (s : Finset α) (x : α → ℝ)
    (hp : IsProbVector x s) : ∀ i ∈ Support x s, 0 ≤ x i := by
  intro i
  have h₁ : ( ∑ i ∈ s, x i = 1) ∧ (∀ i ∈ s, 0 ≤ x i) ∧ (∀ i ∉ s, x i = 0) := hp
  have h₂ : ∀ i ∈ s, 0 ≤ x i := by aesop
  have h₃ : Support x s ⊆ s := by apply Finset.filter_subset
  aesop

/-- Outside the support of a probability distribution the value is zero -/
lemma ProbVector_zero_outside_support (s : Finset α) (t : Finset α)  (x : α → ℝ)
    (hp : IsProbVector x s) : ∀ i ∈ t \ (Support x s), x i = 0 := by
  intro i hi
  unfold IsProbVector at hp
  unfold Support at hi
  have : i ∉ s ∨ x i = 0 := by
    simp only [mem_sdiff, mem_filter] at hi
    obtain ⟨_, h₁⟩ := hi
    rw [not_and_or] at h₁
    aesop
  aesop

/-- If two probability distributions over the same support are not equal, then they
    differ in at least one element -/
lemma ProbVector_neq_then_elements_differ (x y : α → ℝ) (hxy : x ≠ y)
    (s : Finset α) (hx : IsProbVector x s) (hy : IsProbVector y s) :
    ∃ i ∈ s, (x - y) i ≠ 0 := by
  have h₀: ∃ i, (x - y) i ≠ 0 := by
    have : ∃ i, x i ≠ y i := Function.ne_iff.mp hxy
    obtain ⟨i, hi⟩ := this
    use i
    simp only [Pi.sub_apply]
    exact sub_ne_zero_of_ne hi
  have h₁ : ∀ i : α, i ∉ s → x i = 0 := ProbVector_zero_outside_range x s hx
  have h₂ : ∀ i : α, i ∉ s → y i = 0 := ProbVector_zero_outside_range y s hy
  have h₃ : ∀ i : α, i ∉ s → (x - y) i = 0 := by aesop
  obtain ⟨i₀, hi₀⟩ := h₀
  by_contra! _
  have hzero := h₃ i₀ (by aesop)
  rw [hzero] at hi₀
  exact hi₀ rfl

/-- If a probability distribution is summed over just its support, the result is equal to
the sum over all elements -/
lemma ProbVector_total_sum_eq_support_sum (x : α → ℝ) (s : Finset α)  :
    ∑ i ∈ Support x s, x i = ∑ i ∈ s, x i  := by
  have h₁ : Support x s ⊆ s := by
    rw [Support]
    aesop
  have h₂ : ∀ i ∈ s, i ∉ Support x s → x i = 0 := by
    intro i h₁ h₂
    rw [Support] at h₂
    simp only [Finset.mem_filter] at h₂
    push Not at h₂
    exact h₂ h₁
  exact Finset.sum_subset h₁ h₂

/-- A probability distribution cannot have support of zero elements -/
lemma ProbVector_nonzero_support (x : α → ℝ) (s : Finset α)
    (hx : IsProbVector x s) : 0 < #(Support x s) := by
  have h₁ : ∑ i ∈ Support x s, x i = ∑ i ∈ s, x i := ProbVector_total_sum_eq_support_sum x s
  have h₂ : ∑ i ∈ s, x i = 1 := hx.1
  rw [h₂] at h₁
  by_contra h₃
  aesop

/-- A probability distribution has support of strictly positive cardinality -/
lemma ProbVector_positive_support (x : α → ℝ) (s : Finset α)
    (hx : IsProbVector x s) : 0 < #s := by
  have h₁ : Support x s ⊆ s := by
    rw [Support]
    exact Finset.filter_subset _ _
  have h₂ : #(Support x s) ≤ #s := card_le_card h₁
  have h₃ : 0 < #(Support x s) := ProbVector_nonzero_support x s hx
  exact Std.lt_of_lt_of_le h₃ h₂

/-- The sum of a probability distribution over its support equals one -/
lemma ProbVector_sum_over_support_eq_one (x : α → ℝ) (s : Finset α)  :
    ∑ i ∈ Support x s, (x i)^2 = ∑ i ∈ s, (x i)^2  := by
  have h₁ : Support x s ⊆ s := by
    rw [Support]
    aesop
  have h₂ : ∀ i ∈ s, i ∉ Support x s → (x i)^2 = 0 := by
    intro i hi hni
    rw [Support] at hni
    simp only [Finset.mem_filter] at hni
    push Not at hni
    have hnii : i ∈ s → (x i)^2 = 0 := by aesop
    exact hnii hi
  exact Finset.sum_subset h₁ h₂

/-- A probability vector is certainly nonzero somewhere -/
lemma ProbVector_has_nonzero_element (x : α → ℝ) (s : Finset α) (hx : IsProbVector x s):
    ∃ i ∈ s, x i ≠ 0 := by
  unfold IsProbVector at hx
  have hx' : ∑ i ∈ s, x i = 1 := hx.1
  by_contra h
  push Not at h
  have h₀ : ∑ i ∈ s, x i = 0 := sum_eq_zero h
  rw [h₀] at hx'
  norm_num at hx'


-- # ℓ₂ norm

/-- The `ℓ₂` Norm squared of a vector -/
noncomputable def L2normSQ (x : α → ℝ) (s : Finset α) : ℝ :=
   ∑ i ∈ s, (x i)^2

/-- The `ℓ₂` norm squared of the zero vector equals zero -/
lemma L2normSQ_zero_eq_zero (x : α → ℝ) (s : Finset α) (hx : x = 0) :
    L2normSQ x s = 0 := by
  unfold L2normSQ
  aesop

/-- If a vector is nonzero, its `ℓ₂` norm squared is greater than zero -/
lemma L2normSQ_nonzero_geq_zero [Fintype α] (x : α → ℝ) (s : Finset α) (hx : x ≠ 0)
  (hx2 : ∀ i ∉ s, x i = 0 ) :
    0 < L2normSQ x s := by
  unfold L2normSQ
  have h₀  : ∑ i, x i ^ 2 = (∑ i ∈ s, x i ^ 2) + ∑ i ∉ s, x i ^ 2 :=
    Eq.symm (sum_add_sum_compl s fun i ↦ x i ^ 2)
  have h₁ : ∑ i ∉ s, x i ^ 2 = 0 := by
    rw [Finset.sum_eq_zero]
    intro x1 hx1
    aesop
  rw [h₁] at h₀
  have h₂ : ∑ i, x i ^ 2 = ∑ i ∈ s, x i ^ 2 := by linarith
  rw [←h₂]
  have hx' : ∃ i, x i ≠ 0 := by exact Function.ne_iff.mp hx
  have hx'' : ∃ i, 0 < x i ^2 := by
    obtain ⟨ii, hii⟩ := hx'
    use ii
    exact pow_two_pos_of_ne_zero hii
  have h₃ : ∀ i, 0 ≤ x i ^ 2 := by exact fun i ↦ sq_nonneg (x i)
  obtain ⟨ii, hii⟩ := hx''
  have : ∑ i, x i ^ 2 = ∑ i ∈ {ii}, x i ^ 2 + ∑ i ∉ {ii}, x i ^ 2 := by
    exact Eq.symm (sum_add_sum_compl {ii} fun i ↦ x i ^ 2)
  rw [this]
  have h₄ : 0 < ∑ i ∈ {ii}, x i ^ 2 := by
    have : ∑ i ∈ {ii}, x i ^ 2 = x ii ^ 2 := sum_singleton (fun x_1 ↦ x x_1 ^ 2) ii
    rw [this]
    exact hii
  have h₅ : 0 ≤ ∑ i ∈ {ii}ᶜ, x i ^ 2 := by exact sum_nonneg fun i a ↦ h₃ i
  exact Right.add_pos_of_pos_of_nonneg h₄ h₅



/-- If a vector is multiplied by a constant, the square of its `ℓ₂` norm is the `ℓ₂` norm
    of the vector multiplied by the square of the constant -/
lemma L2normSQ_commute_out_constant (x : α → ℝ) (s : Finset α) (k : ℝ) :
    L2normSQ (k • x) s = k^2 * L2normSQ x s := by
  unfold L2normSQ
  have : ∑ i ∈ s, (k • x) i ^ 2 = ∑ i ∈ s, k^2 * x i ^ 2 := by
    simp only [Pi.smul_apply, mul_pow, smul_eq_mul]
  rw [this]
  exact Eq.symm (mul_sum s (fun i ↦ x i ^ 2) (k ^ 2))

/-- L2normSQ is a non-negative number -/
lemma L2normSQ_nonneg (x : α → ℝ) (s : Finset α) : 0 ≤ L2normSQ x s := by
  unfold L2normSQ
  positivity


-- Note that the following lemma is basically an alternative statement of
-- `L2normSQ_nonzero_geq_zero`, with inputs defined slightly differently:
-- keeping as is for now, but a later refactoring may remove or simplify the proof.

/-- L2normSQ is a positive number if the input is nonzero -/
lemma L2normSQ_positive (x : α → ℝ) (s : Finset α) (hx : ∃ i ∈ s, x i ≠ 0):
    0 < L2normSQ x s := by
  unfold L2normSQ
  have h₁ : ∀ i, x i ≠ 0 → 0 < (x i)^2 := by
    intro i hi
    positivity
  have h₃ : ∑ i ∈ s, x i ^ 2
      = ∑ i ∈ s.filter (x · = 0), x i ^ 2 + ∑ i ∈ s.filter (x · ≠ 0), x i ^ 2 := by
    exact Eq.symm (sum_filter_add_sum_filter_not s (fun j ↦ x j = 0) fun j ↦ x j ^ 2)
  rw [h₃]
  have h₄ : ∑ i ∈ s with x i = 0, x i ^ 2 = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    have : x i = 0 := Finset.mem_filter.mp hi |>.2
    rw [this, pow_two]
    exact zero_mul _
  have h₅ : 0 < ∑ i ∈ s with x i ≠ 0, x i ^ 2 := by
    obtain ⟨i₀, hi₀, hvi₀⟩ := hx
    have hi₀_filtered : i₀ ∈ s.filter (fun i => x i ≠ 0) := by
      rw [Finset.mem_filter]
      exact ⟨hi₀, hvi₀⟩
    have hpos_each : ∀ i ∈ s.filter (fun i => x i ≠ 0), 0 < x i ^ 2 := by
      intros i hi
      exact h₁ i (Finset.mem_filter.mp hi).2
    exact Std.lt_of_lt_of_le (hpos_each i₀ hi₀_filtered)
        (single_le_sum (fun i hi => Std.le_of_lt (hpos_each i hi)) hi₀_filtered)
  rw [h₄]
  aesop

/-- Standard result that the `ℓ₂ norm` of a vector decomposed as a sum of orthogonal components -/
lemma L2normsq_of_orthogonal { α : Type* } [Fintype α] (v : α → ℝ) (u : α → ℝ)
    (w : α → ℝ) (I : Finset α) (hv : v = w + u) (hwu : u ⬝ᵥ w = 0) (hw : ∀ i ∉ I, w i = 0) :
    L2normSQ v I = L2normSQ w I + L2normSQ u I := by
  unfold L2normSQ
  have h₁ : ∑ i ∈ I, v i ^ 2 = ∑ i ∈ I, (w + u) i ^ 2 := by aesop
  rw [h₁]
  have h₂ : ∑ i ∈ I, (w + u) i ^ 2 = ∑ i ∈ I, w i ^2
      + ∑ i ∈ I, 2 * w i * u i + ∑ i ∈ I, u i ^2 := by
    have : ∑ i ∈ I, (w + u) i ^ 2 = ∑ i ∈ I, (w i ^2 + 2 * w i * u i + u i ^ 2) := by
      simp_rw [pow_two]
      simp only [Pi.add_apply]
      ring_nf
    rw [this, sum_add_distrib, sum_add_distrib]
  rw [h₂]
  have h₃ :  ∑ i ∈ I, w i * u i = 0 := by
    have :  ∑ i , w i * u i = ∑ i ∈ I, w i * u i + ∑ i ∉ I, w i * u i := by
      exact Eq.symm (sum_add_sum_compl I fun i ↦ w i * u i)
    have : ∑ i ∈ I, w i * u i = ∑ i , w i * u i - ∑ i ∉ I, w i * u i := by linarith
    rw [this]
    have : ∑ i ∉ I, w i * u i = 0 := by
      apply sum_eq_zero
      intro i hi
      rw [hw i (mem_compl.mp hi), zero_mul]
    rw [this]
    have : ∑ i, w i * u i = 0 := by
      have : ∑ i, w i * u i = u ⬝ᵥ w := by
        have : ∑ i, w i * u i = w ⬝ᵥ u := by
          exact rfl
        rw [this]
        exact dotProduct_comm w u
      rw [this]
      exact hwu
    rw [this]
    exact zero_sub_zero
  have h₄ :  ∑ i ∈ I, 2 * w i * u i = 0 := by
    have : ∑ i ∈ I, 2 * w i * u i = 2 * ∑ i ∈ I, w i * u i := by
      simp_rw [mul_assoc]
      rw [mul_sum]
    aesop
  rw [h₄]
  simp only [add_zero]


/-- A standard bound on the dot product of two vectors -/
lemma L2normsq_bound { α : Type* } [Fintype α] [DecidableEq α]
    (I : Finset α) (u : α → ℝ) (v : α → ℝ)
    (hu : ∀ i ∉ I, u i = 0) (hv : ∀ i ∉ I, v i = 0) :
    |u  ⬝ᵥ v|   ≤ √(L2normSQ u I) * √(L2normSQ v I) := by

  -- First a rewrite to get a single square root over the whole right hand side
  have h₀ : √(L2normSQ u I) * √(L2normSQ v I) = √((L2normSQ u I) * L2normSQ v I) := by
    refine Eq.symm (Real.sqrt_mul' (L2normSQ u I) ?_)
    exact L2normSQ_nonneg v I
  rw [h₀]

  -- Second rewrite the absolute value as the square of a square
  have h₁: |u ⬝ᵥ v| = √ ((u ⬝ᵥ v)^2) := by
    have : |u ⬝ᵥ v| = √ (|u ⬝ᵥ v|^2) := by
      rw [Real.sqrt_sq_eq_abs |u ⬝ᵥ v|]
      exact Eq.symm (abs_abs (u ⬝ᵥ v))
    rw [this]
    have : |u ⬝ᵥ v|^2 = (u ⬝ᵥ v)^2 := sq_abs (u ⬝ᵥ v)
    rw [this]
  rw [h₁]

  -- Third prove a bound on the square of the dot product, which then
  -- allows the goal to easily be closed
  have h₂ : (u ⬝ᵥ v) ^ 2 ≤ L2normSQ u I * L2normSQ v I := by
    unfold dotProduct  L2normSQ
    have : ∑ i ∈ I, u i ^ 2 = ∑ i, u i ^ 2 := by
      have : ∑ i, u i ^ 2 = ∑ i ∈ I, u i ^ 2 + ∑ i ∉ I, u i ^ 2 :=
        Eq.symm (sum_add_sum_compl I fun i ↦ u i ^ 2)
      rw [this]
      have : ∑ i ∉ I, u i ^ 2 = 0 := by
        have : ∀ i ∉ I, u i ^2 = 0 := by
          intro i hi
          rw [hu i hi]
          norm_num
        apply Finset.sum_eq_zero
        intro i hi
        exact this i (Finset.mem_compl.mp hi)
      rw [this]
      simp
    rw [this]
    have : ∑ i ∈ I, v i ^ 2 =  ∑ i, v i ^ 2 := by
      have : ∑ i, v i ^ 2 = ∑ i ∈ I, v i ^ 2 + ∑ i ∉ I, v i ^ 2 :=
        Eq.symm (sum_add_sum_compl I fun i ↦ v i ^ 2)
      rw [this]
      have : ∑ i ∉ I, v i ^ 2 = 0 := by
        have : ∀ i ∉ I, v i ^2 = 0 := by
          intro i hi
          rw [hv i hi]
          norm_num
        apply Finset.sum_eq_zero
        intro i hi
        exact this i (Finset.mem_compl.mp hi)
      rw [this]
      simp
    rw [this]
    exact sum_mul_sq_le_sq_mul_sq univ u v
  exact Real.sqrt_le_sqrt h₂


-- # The uniform distribution

/-- The uniform distribution over a specified set;
    note this is only meaningful for non-empty sets -/
noncomputable def UniformDist (s : Finset α) : α → ℝ :=
  fun a => if a ∈ s then 1 / #s else 0

/-- The uniform distribution on a non-empty set is a probability vector -/
lemma UniformDist_is_ProbVector (s : Finset α) (hs : 0 < #s) :
    IsProbVector (UniformDist s) s := by
  unfold IsProbVector
  constructor
  · unfold UniformDist
    have h₁ :  (∑ i ∈ s, if i ∈ s then 1 / (#s : ℝ) else 0) = ∑ i ∈ s,  1 / (#s : ℝ) := by aesop
    rw [h₁]
    have h₂ : ∑ i ∈ s, 1 / (#s : ℝ) = #s / (#s : ℝ) := by aesop
    rw [h₂]
    field_simp
  · constructor
    · unfold UniformDist
      aesop
    · unfold UniformDist
      aesop

/-- A proposition that is true if some probility vector is the uniform distribution -/
lemma IsUniformDist (s : Finset α) (x : α → ℝ)
    (h₀ : ∀ i ∈ s, x i = 1 / (#s : ℝ )) (h₁ : ∀ i ∉ s, x i = 0) : x = UniformDist s := by
  funext a
  by_cases ha : a ∈ s
  · rw [UniformDist, ite_eq_left ha, h₀ a ha]
  · rw [UniformDist, ite_eq_right ha, h₁ a ha]


/-- The uniform distribution is nonzero -/
lemma UniformDist_nonzero (s : Finset α) (hs : 0 < #s) :
    UniformDist s ≠ 0 := by
  have : ∃ a, (UniformDist s) a ≠ 0 := by
    unfold UniformDist
    aesop
  exact Function.support_nonempty_iff.mp this


/-- Taking the inner product of the uniform distribution with itself gives a strictly positive
ouptut -/
lemma UniformDist_self_dot_product_nonzero [Fintype α] (s : Finset α) (hs : 0 < #s) :
    0 < dotProduct (UniformDist s) (UniformDist s) := by
  unfold UniformDist dotProduct
  aesop


/-- The uniform distribution has full support -/
lemma UniformDist_full_support (s : Finset α) :
    #(Support (UniformDist s) s) = #s := by
  unfold Support UniformDist
  simp only [one_div, ne_eq, ite_eq_right_iff, inv_eq_zero, Nat.cast_eq_zero, card_eq_zero,
    Classical.not_imp]
  rw [@card_filter_eq_iff]
  aesop

/-- Every element of the uniform distribution over `s` is `1/#s` -/
lemma UniformDist_element_value (s : Finset α) :
    ∀ i ∈ s, (UniformDist s) i = (1 / #s : ℝ) := by
  intro i hi
  unfold UniformDist
  simp only [hi, ite_true]

-- Note that the following lemma could be stated more generally, as the claim applies to any
-- probability vector. As it is only required for the uniform distribution in this project,
-- this has been left for a future re-factoring.

/-- The uniform distribution is a probability distribution over any superset of its support -/
lemma UniformDist_is_ProbVector_on_superset_of_support
    (s t : Finset α) (hs : 0 < #s) (ht : s ⊆ t) : IsProbVector (UniformDist s) t := by
  unfold IsProbVector
  constructor
  · unfold UniformDist
    have h₁ : (∑ i ∈ t, if i ∈ s then 1 / (#s : ℝ) else 0) = ∑ i ∈ s, 1 / (#s : ℝ) := by
      rw [←sum_filter]
      congr
      aesop
    rw [h₁]
    rw [sum_const, nsmul_eq_mul]
    field_simp
  · constructor
    · intro i hi
      unfold UniformDist
      aesop
    · have h₃ : ∀ i ∉ s, UniformDist s i = 0 := by
        intro i hi
        unfold UniformDist
        simp [hi]
      exact fun i a ↦ h₃ i fun a_1 ↦ a (ht a_1)

/-- The support of the uniform distribution is the set that was specified to construct
the uniform distribution thereover -/
lemma UniformDist_support_is_constructing_set (s : Finset α) :
    Support (UniformDist s) s = s := by
  unfold Support UniformDist
  aesop

/--When taken as a probability vector over a superset of its defining set, the support
    of the uniform distribution remains the defining set -/
lemma UniformDist_as_superset_ProbVector_has_own_support
    (s t : Finset α) (ht : s ⊆ t) : Support (UniformDist s) t = s := by
  unfold Support UniformDist
  aesop

/-- Taking the inner product of the uniform distribution with itself gives a value that is equal
to the cardinality of the support of the uniform distribution -/
lemma UniformDist_self_dot_product_eq_reciprocal_of_support_cardinality
    [Fintype α] (s : Finset α) (hs : 0 < #s) :
    dotProduct (UniformDist s) (UniformDist s) = 1/( #s : ℝ) := by
  unfold UniformDist dotProduct
  simp only [one_div, mul_ite, ite_mul, zero_mul, mul_zero, sum_ite_mem, univ_inter, inter_self,
    sum_const, nsmul_eq_mul]
  field_simp

/-- The square of the `ℓ₂` norm of the uniform distribution is the reciprocal of the
    cardinality of its support -/
lemma UniformDist_L2normSQ_eq_reciprocal_of_support_cardinality
    (s : Finset α) (hs : 0 < #s) :
    L2normSQ (UniformDist s) s = (1 / #s : ℝ) := by
  unfold L2normSQ UniformDist
  simp only [one_div, ite_pow, inv_pow, ne_eq, OfNat.ofNat_ne_zero,
      not_false_eq_true, zero_pow, sum_ite_mem,
      inter_self, sum_const, nsmul_eq_mul]
  field_simp
  --linarith

/-- If the uniform distribution is pointwise squared and then summed, the result is the
reciprocal of the cardinality of the support -/
lemma UniformDist_squared_sum_eq_reciprocal_of_support_cardinality
    (s : Finset α) (hs : 0 < #s) :
    ∑ i ∈ s, ((UniformDist s) i)^2 = (1 / #s) := by
  have : ∀ i ∈ s, (UniformDist s) i = (1 / #s : ℝ) := UniformDist_element_value s
  have : ∑ i ∈ s, (UniformDist s i) ^ 2 = ∑ i ∈ s, (1 / #s : ℝ) ^ 2 := by aesop
  rw [this]
  have : ∑ i ∈ s, ((1 / #s : ℝ) ^ 2) = (1 / #s : ℝ) := by
    calc ∑ i ∈ s, ((1 / #s : ℝ) ^ 2)
      _ = ∑ i ∈ s, (1 / #s : ℝ) ^ 2 * 1 := by aesop
      _ = (1 / #s : ℝ) ^ 2 * ∑ i ∈ s, 1 := by rw [Finset.mul_sum]
      _ =  (1 / #s : ℝ) ^ 2 * (#s : ℝ) := by aesop
      _ = (1 / #s : ℝ) := by
        field_simp
        --linarith
  exact this

/-- A special case of `ProbVector_zero_outside_support` for the uniform distribution -/
lemma UniformDist_zero_outside_support (s : Finset α) :
    ∀ i ∉ s, (UniformDist s) i = 0 := by
    unfold UniformDist
    aesop


/-- If any probability distribution is multiplied point-wise by the uniform distribution
such that the support of the uniform distribution covers that of the first probability distribution
then the result is the reciprocal of the cardinality of the support of the uniform distribution -/
lemma ProbVector_times_UniformDist (s : Finset α) (x : α → ℝ)
    (hx : IsProbVector x s) : ∑ i ∈ s, (x i) * ((UniformDist s) i) = (1/ #s : ℝ) := by
  have : ( ∑ i ∈ s, x i = 1) ∧ (∀ i ∈ s, 0 ≤ x i) ∧ (∀ i ∉ s, x i = 0) := hx
  have : ∑ i ∈ s, x i = 1 := by aesop
  have : ∀ i ∈ s, (UniformDist s) i = (1 / #s : ℝ) := UniformDist_element_value s
  have : ∑ i ∈ s, (x i) * ((UniformDist s) i) = (1 / #s : ℝ) * ∑ i ∈ s, (x i) := by
    have : ∑ i ∈ s, (x i) * ((UniformDist s) i) = ∑ i ∈ s, (x i) * (1 / #s : ℝ) := by aesop
    rw [this]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro _ _
    rw [mul_comm]
  aesop


-- The following lemma is an alternative statement of the preceeding one; in particular, the claim
-- holds when taken over all `α` and not just the support

/-- If any probability distribution is multiplied point-wise by the uniform distribution
such that the support of the uniform distribution covers that of the first probability distribution
then the result is the reciprocal of the cardinality of the support of the uniform distribution  -/
lemma ProbVector_times_UniformDist' [Fintype α] (s : Finset α) (x : α → ℝ)
    (hx : IsProbVector x s) : ∑ i, (x i) * ((UniformDist s) i) = (1/ #s : ℝ) := by
  have h₀ : ∑ i, (x i) * ((UniformDist s) i) =  ∑ i ∈ s, (x i) * ((UniformDist s) i) := by
    have : ∑ i, (x i) * ((UniformDist s) i)
        = ∑ i ∈ s, (x i) * ((UniformDist s) i) + ∑ i ∉ s, (x i) * ((UniformDist s) i) :=
      Eq.symm (sum_add_sum_compl s fun i ↦ x i * UniformDist s i)
    rw [this]
    have :  ∑ i ∉ s, (x i) * ((UniformDist s) i) = 0 := by
      apply Finset.sum_eq_zero
      intro i hi
      have : UniformDist s i = 0 := by
        have : ∀ j ∉ s, UniformDist s j = 0 :=
          fun j a ↦ UniformDist_zero_outside_support s j a
        aesop
      rw [this]
      linarith
    rw [this]
    linarith
  rw [h₀]
  exact ProbVector_times_UniformDist s x hx

  --#lint
