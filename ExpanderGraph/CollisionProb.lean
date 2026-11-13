/-
Copyright (c) 2025-2026 Steven Herbert. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Steven Herbert
-/

import Mathlib
import ExpanderGraph.ProbabilityVector

/-!

# CollisionProb

The collision probability is the probability that two samples from the same finite discrete
probalitiy distribution are the same (they 'collide'). One lemma (split here into the four main
results) is central to the proof that spectral expansion implies vertex expansion.

## Main definitions

* `CP`

## Main results

* `CP_ProbVec_minus_uniform` The collision probability of a probability distribution
  equals the ℓ₂ norm squared of the difference between the probability distribution and
  the uniform distribution, plus the reciprocal of the cardinality of the support

* `CP_reciprocal_support_leq_CP` The reciprocal of the cardinality of the support
  is less than or equal to the collision probability

* `CP_UniformDist_equal_reciprocal_support` The reciprocal of the cardinality of
  the support is equal to the collision probability for the uniform distribution

* `CP_equal_reciprocal_support_implies_uniform` The reciprocal of the cardinality of
  the support is equal to the collision probability ONLY for the uniform distribution

-/

namespace CollisionProb

open BigOperators
open Classical
open Std
open Finset
open ProbabilityVector

-- +++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++

-- [ADDED-BY-SUPERVISOR]
/-- The condition for when Cauchy-Schwarz is met with equality -/
theorem Finset.cauchy_schwarz_equality {ι : Type*}
    (s : Finset ι) (f g : ι → ℝ) (hf : ∃ i ∈ s, f i ≠ 0) (hg : ∃ i ∈ s, g i ≠ 0) :
    (∑ i ∈ s, f i * g i) ^ 2 = (∑ i ∈ s, f i ^ 2) * ∑ i ∈ s, g i ^ 2 →
    ∃ c : ℝ, ∀ i ∈ s, f i = c * g i := by
  intro h
  let x : EuclideanSpace ℝ s := WithLp.toLp _ fun i ↦ f i
  let y : EuclideanSpace ℝ s := WithLp.toLp _ fun i ↦ g i
  have hx : x ≠ 0 := by simpa [x, funext_iff]
  have hy : y ≠ 0 := by simpa [y, funext_iff]
  have : ‖inner ℝ y x‖ = ‖y‖ * ‖x‖ := by
    rw [← sq_eq_sq₀ (by positivity) (by positivity), mul_pow, PiLp.norm_sq_eq_of_L2,
      PiLp.norm_sq_eq_of_L2, PiLp.inner_apply]
    simp [x, y, Finset.sum_attach _ (fun i ↦ (f i) ^ 2), Finset.sum_attach _ (fun i ↦ (g i) ^ 2),
      Finset.sum_attach _ (fun i ↦ f i * g i), h, mul_comm]
  obtain ⟨r, -, hr⟩ := (norm_inner_eq_norm_iff (𝕜 := ℝ) hy hx).1 this
  simp only [PiLp.ext_iff, PiLp.smul_apply, smul_eq_mul, Subtype.forall,
    x, y] at hr
  exact ⟨r, hr⟩

-- +++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++

variable {α : Type*}

/-- Collision probability is the ℓ₂ norm squared of the vector. This is meant for when the
vector in question is a probability vector -/
noncomputable def CP (x : α → ℝ) (s : Finset α) : ℝ :=
  L2normSQ x s

/-- A zero-padded probability distribution has the same value of collision probability -/
lemma CP_of_superset_is_same (s t : Finset α) (x : α → ℝ)
    (hx : IsProbVector x s) (ht : (Support x s) ⊆ t) : CP x (Support x s)  = CP x t := by
  have h₀ : ∀ i ∈ t \ (Support x s), x i = 0 := ProbVector_zero_outside_support s t x hx
  unfold CP L2normSQ Support
  unfold Support at ht
  unfold Support at h₀
  have h₁ : ∑ i ∈ t, x i ^ 2 = ∑ i ∈ {i ∈ s | x i ≠ 0}, x i ^ 2 +
      ∑ i ∈ t \ {i ∈ s | x i ≠ 0}, x i ^ 2 := by aesop
  rw [h₁]
  have h₂ : ∑ i ∈ t \ {i ∈ s | x i ≠ 0}, x i ^ 2 = 0 := by
    apply sum_eq_zero
    intro i hi
    have h₃ : x i = 0 := by
      aesop
    aesop
  rw [h₂]
  aesop


/-- The collision probability of a probability distribution equals the ℓ₂ norm squared
  of the difference between the probability distribution and the uniform distribution,
  plus the reciprocal of the cardinality of the support -/
lemma CP_ProbVec_minus_uniform (s : Finset α) (x : α → ℝ)
    (hx : IsProbVector x s) : CP x s = L2normSQ  (x - UniformDist s) s + (1 / #s) := by
  let n := #s
  have hn : 0 < n := ProbVector_positive_support x s hx
  have h₁ : (L2normSQ (x - (UniformDist s)) s) + (1 / n) = ∑ i ∈ s, (x i)^2 := by
    calc (L2normSQ (x -  UniformDist s) s) + (1 / n)
        _ = ∑ i ∈ s, ((x -  UniformDist s) i)^2 + (1 / n) := by
          have h1a : L2normSQ (x -  UniformDist s) s
            = ∑ i ∈ s, ((x -  UniformDist s) i)^2 := rfl
          aesop
        _ = ∑ i ∈ s, ((x i) -  ((UniformDist s) i))^2 + (1 / n) := by aesop
        _ = ∑ i ∈ s, ((x i)^2 - 2 * (x i) * ((UniformDist s) i)
            + ((UniformDist s) i)^2) + (1 / n) := by ring_nf
        _ = ∑ i ∈ s, ((x i)^2) - ∑ i ∈ s,  2 * (x i) * ((UniformDist s) i)
            + ∑ i ∈ s, ((((UniformDist s) i)^2)) + (1 / n) := by
          rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
        _ = ∑ i ∈ s, ((x i)^2) - 2 * ∑ i ∈ s,   (x i) * ((UniformDist s) i)
            + ∑ i ∈ s, ((((UniformDist s) i)^2)) + (1 / n) := by
          rw [Finset.mul_sum]
          simp only [one_div, add_left_inj, sub_right_inj]
          apply Finset.sum_congr rfl
          intro i hi
          ring
        _ = ∑ i ∈ s, (x i)^2 := by
          have h₃ : ∑ i ∈ s, (x i) * ((UniformDist s) i) = (1/ n : ℝ) :=
            ProbVector_times_UniformDist s x hx
          have h₄ : ∑ i ∈ s, ((UniformDist s) i)^2 = (1 / n) :=
            UniformDist_squared_sum_eq_reciprocal_of_support_cardinality s hn
          rw [h₃, h₄]
          ring_nf
  exact id (Eq.symm h₁)

/-- The reciprocal of the cardinality of the support is less than or
    equal to the collision probability -/
lemma CP_reciprocal_support_leq_CP (s : Finset α) (x : α → ℝ)
    (hx : IsProbVector x s) : 1 / (#(Support x s) : ℝ) ≤  CP x s := by
  have h₁ : 1 ≤ Real.sqrt (( #(Support x s) : ℝ) * (CP x s)) := by
    calc 1
      _ = ∑ i ∈ s, (x i) := by
        have : ( ∑ i ∈ s, x i = 1) ∧ (∀ i ∈ s, 0 ≤ x i) ∧ (∀ i ∉ s, x i = 0) := hx
        aesop
      _ = ∑ i ∈ Support x s, x i := by
        rw [@ProbVector_total_sum_eq_support_sum]
      _ = ∑ i ∈ Support x s, 1 * (x i) := by aesop
      _ = ∑ i ∈ Support x s, (fun _ => 1) x * (x i) := by aesop
      _ = ∑ i ∈ Support x s, √ (((fun _ => 1) x)^2) * √ ((x i)^2) := by
        have : ∀ i ∈ Support x s, 0 ≤ x i := ProbVector_nonneg s x hx
        aesop
      _ ≤ (√ ( ∑ i ∈ Support x s, (fun _ => 1) x^2)) * ( √ (∑ i ∈ Support x s, ((x i)^2))) := by
        have ha : ∀ i : α, (0 : ℝ) ≤ ((fun _ => 1) x)^2 := by aesop
        have hb : ∀ i : α, 0 ≤ (x i)^2 := by
          intro i
          exact sq_nonneg (x i)
        exact Real.sum_sqrt_mul_sqrt_le (Support x s) ha hb
      _ = (Real.sqrt ( ∑ i ∈ Support x s, 1 )) *
          ( Real.sqrt (∑ i ∈ Support x s, ((x i)^2))) := by rw [@one_pow]
      _ = (Real.sqrt (#(Support x s) : ℝ)) * ( Real.sqrt (∑ i ∈ Support x s, (x i)^2)) := by aesop
      _ = (Real.sqrt  (#(Support x s) : ℝ)) * ( Real.sqrt (∑ i ∈ s, (x i)^2)) := by
        rw [@ProbVector_sum_over_support_eq_one]
      _ = (Real.sqrt (#(Support x s)) : ℝ) * ( Real.sqrt (L2normSQ x s)) := by rfl
      _ ≤ Real.sqrt ( #(Support x s) : ℝ) * Real.sqrt (CP x s) := by rfl
      _ = Real.sqrt (( #(Support x s) : ℝ) * (CP x s))  := by aesop
  have h₂ : 1 ≤ (#(Support x s) : ℝ) * (CP x s) := by
    exact Real.one_le_sqrt.mp h₁
  have : 0 < #(Support x s) := ProbVector_nonzero_support x s hx
  have h₃ : (0 : ℝ) < (#(Support x s) : ℝ) := by aesop
  simp only [one_div, ge_iff_le]
  have h₄ : 1 ≤ CP x s * (#(Support x s) : ℝ) := by
    rw [mul_comm]
    exact h₂
  have : 1 / (#(Support x s) : ℝ) ≤ CP x s := by
    apply (div_le_iff₀ h₃).mpr
    exact h₄
  aesop


/-- The reciprocal of the cardinality of the support is equal to the collision probability
for the uniform distribution -/
lemma CP_UniformDist_equal_reciprocal_support (s : Finset α) :
    CP (UniformDist s) s = 1 / (#(Support (UniformDist s) s))  := by
  let n := #s
  calc CP (UniformDist s) s
    _ = ∑ i ∈ s, ((UniformDist s) i)^2 := rfl
    _ = ∑ i ∈ s, (1 / n : ℝ)^2 := by
      have h₁ : ∀ i ∈ s, ((UniformDist s) i) = (1 / n : ℝ) := UniformDist_element_value s
      simp only [one_div, inv_pow, sum_const, nsmul_eq_mul]
      aesop
    _ = ∑ i ∈ s, (1 / n : ℝ)^2 * 1 := by aesop
    _ = (1 / n : ℝ)^2 * ∑ i ∈ s, 1 := by rw [Finset.mul_sum]
    _ = (1 / n : ℝ)^2 * (n : ℝ) := by
      aesop
    _ = (1 / n : ℝ) := by
      field_simp
      --linarith
    _ = 1 / (#(Support ( UniformDist s) s)) := by rw [@UniformDist_full_support]


/-- The reciprocal of the cardinality of the support is equal to the collision probability
ONLY for the uniform distribution -/
lemma CP_equal_reciprocal_support_implies_uniform
    (s : Finset α) (x : α → ℝ) (hx : IsProbVector x s) :
    ( CP x s = 1 / (#(Support (UniformDist s) s )) ) → (x = UniformDist s) := by
  intro h₀
  have h₁ : CP x s = ∑ i ∈ s, (x i)^2 := rfl
  have h₂ : #(Support (UniformDist s) s) = #s := UniformDist_full_support s
  rw [h₁] at h₀
  have h₃ : ∑ i ∈ s, 1^2 = #s := by aesop
  have h₄: (∑ i ∈ s, x i)^2 = 1 := by
    have : ∑ i ∈ s, x i = 1 := (hx).1
    aesop
  rw [h₂] at h₀
  have h₅ : (∑ i ∈ s, x i ^ 2) * ∑ i ∈ s, 1 ^ 2  = 1 := by
    rw [h₀]
    rw [← h₃]
    have : 0 < #s := ProbVector_positive_support x s hx
    field_simp
    aesop
  have h₆ : (∑ i ∈ s, x i * (fun _ => 1) i) ^ 2 = (∑ i ∈ s, x i ^ 2) * ∑ i ∈ s, (fun _ => 1) i ^ 2 →
      ∃ c : ℝ, ∀ i ∈ s, x i = c * (fun _ => 1) i := by
    have h₆a : ∃ i ∈ s, x i ≠ 0 := ProbVector_has_nonzero_element x s hx
    have h₆b : ∃ i ∈ s, (1 : ℝ) ≠ 0 := by aesop
    exact Finset.cauchy_schwarz_equality s x (fun _ ↦ 1) h₆a h₆b
  have h₇ : ∃ c : ℝ, ∀ i ∈ s, x i = c := by aesop
  obtain ⟨c, hc_eq⟩ := h₇
  have h₈ : (∀ i ∈ s, x i = c) → c = 1 / (#s : ℝ)  := by
    intro hc_eq'
    have : ∑ i ∈ s, x i = 1 := (hx).1
    have h₉ : ∑ i ∈ s, c = 1 := by aesop
    have h₁₀ : ∑ i ∈ s, c = c * (#s) := by
      field_simp
      simp only [Finset.sum_const, nsmul_eq_mul]
      exact mul_comm (#s : ℝ) c
    have : 0 < #s := ProbVector_positive_support x s hx
    rw [h₁₀] at h₉
    ring_nf
    field_simp
    exact h₉
  have h₁₁ : ∀ i ∈ s, x i =  1 / (#s : ℝ) := by
    aesop
  exact IsUniformDist s x h₁₁ ((hx).2).2

  --#lint
