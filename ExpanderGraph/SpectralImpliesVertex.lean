/-
Copyright (c) 2025-2026 Steven Herbert. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Steven Herbert
-/
import Mathlib

import ExpanderGraph.CollisionProb
import ExpanderGraph.MultiDiGraph
import ExpanderGraph.ExpansionDefs
import ExpanderGraph.ProbabilityVector
import ExpanderGraph.StochasticMatrix

/-!
# SpectralImpliesVertex

This file formalises the result that non-zero spectral expansion implies non-zero
vertex expansion

## Main results

*  `SpectralImpliesVertex` The main theorem for spectral expansion implies vertex expansion

*  `SpectralImpliesVertexCor` A notable special case of `SpectralImpliesVertex`:
    a `γ` spectral expander is in particular a `(|G| / 2, 1 + γ)` spectral expander

-/

open Finset Function BigOperators
open CollisionProb
open MultiDiGraphSpace
open ExpansionDefs
open Classical
open ProbabilityVector
open StochasticMatrixSpace

open Finset Function
open Matrix

namespace SpectralImpliesVertexSpace


-- # Some helpful lemmas

/-- A simple linear algebraic result that is extracted -/
lemma helper_lemma_1 (a b c : ℝ) (hb : 0 ≠ b) (hc : 0 ≠ c):
    a * b / c = a * b * b / (b * c) := by
  field_simp
  --linarith

/-- The support of a probability distribution over the vertices
is necessarily a subset of the vertices, and hence the reciprocal of the
cardinality of the support is at least the reciprocal of the cardinality
of the vertex set -/
lemma helper_lemma_2 {V E : Type*} (G : MultiDiGraph V E)
    (π : V → ℝ) (hπ : IsProbVector π G.vertices) :
    1 / (#G.vertices : ℝ ) ≤ 1 / (#(Support π G.vertices) : ℝ) := by
  have h₁ :  (#(Support π G.vertices) : ℝ) ≤ (#G.vertices : ℝ) := by
    unfold Support
    simp only [ne_eq, Nat.cast_le]
    exact card_filter_le G.vertices fun i ↦ ¬π i = 0
  have : 0 < #(Support π G.vertices) :=
    ProbVector_nonzero_support π G.vertices hπ
  have h₂ : 0 < (#(Support π G.vertices) : ℝ) := by aesop
  exact one_div_le_one_div_of_le h₂ h₁


-- # Key claims from the proof of the main theorem
-- Note that these lemmas are not intended for general use, and so docstrings have been omitted
-- in favour of brief comments linking the results to the claims in the dissertation.

-- This is claim `A` in the accompanying dissertation
lemma SpectralImpliesVertex_claim_A {V E : Type*} (G : MultiDiGraph V E) :
    ∀ π : V → ℝ, (IsProbVector π G.vertices) → ((CP π G.vertices) - (1 / #G.vertices : ℝ)
    = L2normSQ (π - UniformDist G.vertices) G.vertices ) := by
  intro π hπ
  let n := #G.vertices -- n as its usual use in the informal proofs as the number of vertices
  let u := UniformDist G.vertices
  have : CP π G.vertices = L2normSQ  (π - u) G.vertices + (1 / n : ℝ) := by
    rw [← CP_ProbVec_minus_uniform G.vertices π]
    exact hπ
  aesop


-- This is claim `B` in the accompanying dissertation
lemma SpectralImpliesVertex_claim_B {V E : Type*} [Fintype V] [DecidableEq V]
    [DecidableEq E] (G : MultiDiGraph V E) (hV: 0 < #G.vertices)
    (π : V → ℝ) (hπ : IsProbVector π G.vertices) (hu : π ≠ UniformDist G.vertices)
    (r : ℕ) (hr : 0 < r) (hr1 : G.isRegularOfDegree r):
    (1-G.SpectralGap)^2 ≥ ((CP ( π ᵥ* G.randomWalkMatrix) G.vertices) -
    (1 / #G.vertices : ℝ )) / ((CP π G.vertices) - (1 / #G.vertices : ℝ )) := by
  -- introduce some standard notation aligned with that in the dissertation
  let n := #G.vertices
  let M := G.randomWalkMatrix
  let u := UniformDist (G.vertices)
  have hr2 : r ≠ 0 := Nat.ne_zero_of_lt hr
  -- The remainder of the proof is a calc block which follows similar steps to the informal
  -- proof
  calc (1-G.SpectralGap)^2
    _  = (sSup { y : ℝ  | ∃ p : V → ℝ , (IsProbVector p G.vertices) ∧
        (p ≠ UniformDist G.vertices) ∧ (y = √ (L2normSQ ((p ᵥ* M) - u)
        G.vertices) / √ (L2normSQ (p-u) G.vertices)) })^2 := by
      have : G.SpectralGap = 1 - sSup { y : ℝ  | ∃ p : V → ℝ , (IsProbVector p G.vertices)
          ∧ (p ≠ UniformDist G.vertices) ∧ (y = √ (L2normSQ ((p ᵥ* M) - u)
          G.vertices) / √ (L2normSQ (p-u) G.vertices)) } := by rfl
      have : 1 - G.SpectralGap = sSup { y : ℝ  | ∃ p : V → ℝ , (IsProbVector p G.vertices)
          ∧ (p ≠ UniformDist G.vertices) ∧  (y = √ (L2normSQ ((p ᵥ* M) - u)
          G.vertices) / √ (L2normSQ (p-u) G.vertices)) } := by linarith
      exact congr_arg (fun x => x ^ 2) this
    _ ≥ (√(L2normSQ (π  ᵥ* M - u) G.vertices) / √(L2normSQ (π - u) G.vertices)) ^ 2 := by
      apply pow_le_pow_left₀
      · positivity
      apply le_csSup
      · have : ∀ x ∈ {y | ∃ p, IsProbVector p G.vertices ∧ p ≠ UniformDist G.vertices ∧ y =
            √(L2normSQ (p ᵥ* G.randomWalkMatrix - UniformDist G.vertices) G.vertices)
            / √(L2normSQ (p - UniformDist G.vertices) G.vertices)}, x ≤ 1 := by
          exact G.bound_on_L2normSQ' hV hr2 hr1
        refine bddAbove_def.mpr ?_
        use 1
      · aesop
    _ ≥ (L2normSQ ((π ᵥ* M) - u) G.vertices) / (L2normSQ (π-u) G.vertices) := by
      have : (√(L2normSQ (π ᵥ* M - u) G.vertices) / √(L2normSQ (π - u) G.vertices)) ^ 2
          = (L2normSQ (π ᵥ* M - u) G.vertices) / (L2normSQ (π - u) G.vertices) := by
        have hnom : 0 ≤ L2normSQ (π ᵥ* M - u) G.vertices :=
          L2normSQ_nonneg (π ᵥ* M - u) G.vertices
        have hdenom : 0 < L2normSQ (π - u) G.vertices := by
          have hu' : IsProbVector u G.vertices :=
              UniformDist_is_ProbVector_on_superset_of_support
                G.vertices G.vertices hV fun ⦃a⦄ a ↦ a
          have : ∃ vv ∈ G.vertices, (π - u) vv ≠ 0 :=
            ProbVector_neq_then_elements_differ π u hu G.vertices hπ hu'
          exact L2normSQ_positive (π - u) G.vertices this
        have : (√(L2normSQ (π ᵥ* M - u) G.vertices) / √(L2normSQ (π - u) G.vertices)) =
            √((L2normSQ (π ᵥ* M - u) G.vertices) / (L2normSQ (π - u) G.vertices)) := by
          aesop
        rw [this]
        apply Real.sq_sqrt
        positivity
      rw [this]
    _ = ((CP (π ᵥ* M) G.vertices) - (1 / n : ℝ)) / (L2normSQ (π-u) G.vertices) := by
      let π2 := (π ᵥ* M)
      have h₁ : (IsProbVector π G.vertices) →
          (IsProbVector (π ᵥ* G.randomWalkMatrix) G.vertices) := by
        intro hπ
        have hv : (∀ i ∈ G.vertices, 0 ≤ π i) ∧ (∑ i ∈ G.vertices, π i = 1)
            ∧ ∀ i ∉ G.vertices, π i = 0 := by (expose_names; exact and_left_comm.mp hπ_1)
        have hm : (0 < #G.vertices) ∧ ∀ i ∉ G.vertices, G.randomWalkMatrix i i = 1 := by
          constructor
          · exact hV
          · exact G.diagonal_outside_support_randomWalkMatrix
        have : (∀ j ∈ G.vertices, 0 ≤ (π ᵥ* M) j) ∧ (∑ j ∈ G.vertices, (π ᵥ* M) j = 1) ∧
             ∀ j ∉ G.vertices, (π ᵥ* M) j  = 0 :=
          pdist_subset_vecMul_of_mem_doublyStochastic
              (G.RegularrandomWalkMatrixIsDoublyStochastic hr2 hr1) G.vertices hm hv
        unfold IsProbVector
        exact and_left_comm.mp this
      have h₃ :(L2normSQ (π2 - u) G.vertices) = ((CP π2 G.vertices) - (1 / n : ℝ)) := by
        exact Eq.symm (SpectralImpliesVertex_claim_A G π2 (h₁ hπ))
      aesop
    _ = ((CP (π ᵥ* M) G.vertices) - (1 / n : ℝ)) / ((CP π G.vertices) - (1 / n : ℝ)) := by
      have : ∀ π : V → ℝ, (IsProbVector π G.vertices) → ((CP π G.vertices) - (1 / #G.vertices : ℝ)
          = L2normSQ (π - UniformDist G.vertices) G.vertices ) := SpectralImpliesVertex_claim_A G
      aesop

-- This is claim `C` in the accompanying dissertation
lemma SpectralImpliesVertex_claim_C {V E : Type*} (G : MultiDiGraph V E)
    (π : V → ℝ) (hπ : IsProbVector π G.vertices) (hu : π ≠ UniformDist G.vertices):
    (CP π G.vertices) - (1 / #G.vertices : ℝ) ≠ 0 := by
  have : ¬(π = UniformDist G.vertices) → ¬( CP π G.vertices =
      1 / (#(Support (UniformDist G.vertices) G.vertices )) ) := by
    contrapose
    --simp only [Decidable.not_not]
    exact CP_equal_reciprocal_support_implies_uniform G.vertices π hπ
  have h₂ : #(Support (UniformDist G.vertices) G.vertices) = #G.vertices :=
    UniformDist_full_support G.vertices
  have h₃ : CP π G.vertices ≠ 1 / (#G.vertices : ℝ) := by aesop
  exact sub_ne_zero.mpr h₃



set_option maxHeartbeats 600000 in
-- Note that this lemma is rather long, however it is not readily decomposible, hence the number of
-- hearbeats has been increased. Comments throughout allow the proof to be followed along with the
-- accompanying dissertation and infoview

-- This is claim `D` in the accompanying dissertation
lemma SpectralImpliesVertex_claim_D {V E : Type*} [Fintype V] [DecidableEq V]
    [DecidableEq E] (G : MultiDiGraph V E) (α : ℝ) (hα : α ∈ Set.Icc 0 1) (γ : ℝ)
    (hγ : γ ∈ Set.Ioc 0 1 ∧ spectralExpander γ G)
    (ha : ∀ S1 : Finset V, S1 ⊆ G.vertices ∧ 0 < #S1 →
        CP (UniformDist S1 ᵥ* G.randomWalkMatrix) G.vertices - (1 /  #G.vertices : ℝ )
        ≤ (1 - G.SpectralGap) ^ 2 * (CP (UniformDist S1) G.vertices - (1 /  #G.vertices : ℝ )))
        (r : ℕ) (hr : 0 < r) (hG1 : G.isRegularOfDegree r) :

    ∀ S : Finset V, (S ⊆ G.vertices) ∧ ( ( #S : ℝ ) ≤ α * (#G.vertices : ℝ )  ) → (( #S : ℝ ) /
    ((1-γ)^2 * (1-α) + α ) ≤  ( #(G.neighbourhoodOfSet S) : ℝ ))  := by

  -- introduce the terms and define standard notation
  intro S hS
  let n := #G.vertices
  have hS1 := And.left hS
  have hS2 := And.right hS
  have hr2 : r ≠ 0 := Nat.ne_zero_of_lt hr

  by_cases hsempty : S = ∅
  · aesop
  · -- Establish that `S` and therefore `G.vertices` are non-empty
    have h₁ : 0 < #S := by
      rw [@card_pos]
      exact nonempty_iff_ne_empty.mpr hsempty
    have h₁a : 0 < (#S : ℝ) := by positivity
    have h₂n : 0 < #G.vertices := by
      have : #S ≤ #G.vertices := card_le_card hS1
      exact Nat.lt_of_lt_of_le h₁ this
    have h₂a : (n : ℝ) ≠ 0 := by aesop
    have h₂b : (#S : ℝ) ≤ (n : ℝ) := by
      have : #S ≤ n := card_le_card hS1
      exact Nat.cast_le.mpr this
    -- Establish that S is a probability distribution over both
    -- `G.vertices` and `S` itself
    have hSdist : IsProbVector (UniformDist S) G.vertices :=
      UniformDist_is_ProbVector_on_superset_of_support S G.vertices h₁ hS1
    have hSdist2 : IsProbVector (UniformDist S) S := by
      exact UniformDist_is_ProbVector_on_superset_of_support S S h₁ fun ⦃a⦄ a ↦ a

    -- Establish that `α` upper bounds the ration of `S / n`
    have hSn : (#S : ℝ) / (n : ℝ) ≤ α := by
      have hn : 0 < (n : ℝ) := by aesop
      exact (div_le_iff₀ hn).mpr hS2

    -- Some lemmas around the spectral gap
    have hγ1 : γ ∈ Set.Ioc 0 1 := hγ.1
    have hγa : γ ≤ G.SpectralGap := by exact hγ.2
    have hγc : 0 ≤ 1 - γ := by aesop
    have hγd : (1 - G.SpectralGap)^2 ≤ (1 - γ)^2 := by
      have : 0 ≤ 1 - G.SpectralGap := by
        have : 0 < #G.vertices := h₂n
        have : G.SpectralGap ≤ 1 := G.SpectralGap_leq_one this
        nlinarith
      nlinarith

    -- The collision probability of `UniformDist S` treated as a probability distribution
    -- over `S` is the same as that treated as a probability distribution over `G.vertices`
    have h₂ : CP (UniformDist S) S = CP (UniformDist S) G.vertices := by
      have hSsupport : Support (UniformDist S) S = S :=
        UniformDist_as_superset_ProbVector_has_own_support S S fun ⦃a⦄ a ↦ a
      rw [← hSsupport] at hS1
      nth_rw 2 [← hSsupport]
      exact CP_of_superset_is_same S G.vertices (UniformDist S) hSdist2 hS1

    -- A few more statements that are heavily used below
    have hSn₁ : 0 ≤ 1 / (#S : ℝ) - (1 / n : ℝ) := by
      have : (1 / n : ℝ) ≤ 1 / (#S : ℝ) := one_div_le_one_div_of_le h₁a h₂b
      nlinarith
    -- The standard property of a Markov chain: when a stochastic matrix
    -- operates on a probability vector, the outcome is another probability vector
    have h₃ : (IsProbVector (UniformDist S) G.vertices) →
        IsProbVector ((UniformDist S) ᵥ* G.randomWalkMatrix) G.vertices := by
      intro _
      have hv : (∀ i ∈ G.vertices, 0 ≤ (UniformDist S) i) ∧
          (∑ i ∈ G.vertices, (UniformDist S) i = 1) ∧ ∀ i ∉ G.vertices, (UniformDist S) i = 0 :=
        and_left_comm.mp hSdist
      have hm : (0 < #G.vertices) ∧ ∀ i ∉ G.vertices, G.randomWalkMatrix i i = 1 := by
        constructor
        · exact h₂n
        · exact G.diagonal_outside_support_randomWalkMatrix
      have : (∀ j ∈ G.vertices, 0 ≤ ((UniformDist S) ᵥ* G.randomWalkMatrix) j) ∧
          (∑ j ∈ G.vertices, ((UniformDist S) ᵥ* G.randomWalkMatrix) j = 1) ∧
          ∀ j ∉ G.vertices, ((UniformDist S) ᵥ* G.randomWalkMatrix) j  = 0 :=
        pdist_subset_vecMul_of_mem_doublyStochastic
            (G.RegularrandomWalkMatrixIsDoublyStochastic hr2 hG1) G.vertices hm hv

      unfold IsProbVector
      exact and_left_comm.mp this

    -- Modus Ponens applied to `h₃` and `hSdist`
    have h₃a : IsProbVector ((UniformDist S) ᵥ* G.randomWalkMatrix)
        G.vertices := h₃ hSdist

    -- This is equation (46) in the dissertation
    -- except the connection between the neighbourhood of `S` and the support
    -- of the probability vector after one application of the random walk matrix
    -- to the uniform distribution on `S` has not yet been made
    have h₄ : (1 / (#(Support ((UniformDist S) ᵥ* G.randomWalkMatrix)
        G.vertices) : ℝ)) - (1 / (n : ℝ)) ≤ (1-G.SpectralGap)^2 *
        ( ( 1 / (#(Support (UniformDist S) S )) ) - (1 / n : ℝ)) := by
      calc (1 / (#(Support ((UniformDist S) ᵥ* G.randomWalkMatrix)
          G.vertices) : ℝ))  - (1 / (n : ℝ))
        _ ≤ CP ((UniformDist S) ᵥ* G.randomWalkMatrix) G.vertices
            - (1 / (n : ℝ)) := by
          have : (1 / (#(Support ((UniformDist S) ᵥ* G.randomWalkMatrix)
              G.vertices) : ℝ)) ≤ CP ((UniformDist S) ᵥ* G.randomWalkMatrix)
              G.vertices := CP_reciprocal_support_leq_CP G.vertices
              ((UniformDist S) ᵥ* G.randomWalkMatrix) h₃a
          linarith
        _ ≤ (1-G.SpectralGap)^2 * ( ( CP (UniformDist S) S  ) - (1 / n : ℝ)) := by
          rw [h₂]
          exact ha S ⟨ hS.1, h₁ ⟩
        _ = (1-G.SpectralGap)^2 * ( ( 1 / (#(Support (UniformDist S) S )) )
            - (1 / n : ℝ)) := by rw [← @CP_UniformDist_equal_reciprocal_support]
            --rw [CP_UniformDist_equal_reciprocal_support S h₁]

    -- Now rewrite in terms of the neighbourhood, along with some other easy rewrites
    -- This puts `h₄` in the form of equation (93)
    rw [SupportNeighbourhood G (UniformDist S) hSdist r hr hG1,
        UniformDist_full_support S,
        UniformDist_as_superset_ProbVector_has_own_support S G.vertices hS1] at h₄


    -- `h₅` is `h₄` with `(1 / n : ℝ)` added to each side; `h₅a` and `h₅b` establish
    -- non-zero nature of the denominators therein
    have h₅ : 1 / (#(G.neighbourhoodOfSet S) : ℝ) ≤
        (1 - G.SpectralGap) ^ 2 * (1 / (#S : ℝ) - (1 / n : ℝ)) + (1 / n : ℝ) := by
      linarith

    have h₅a : 0 < (#(G.neighbourhoodOfSet S) : ℝ) := by
      exact G.regular_of_non_zero_deg_neighbour_nonempty r hr hG1 S hS.1 h₁

    have h₅b : 0 < (1 - G.SpectralGap) ^ 2 * (1 / (#S : ℝ) - (1 / n : ℝ)) + (1 / n : ℝ)  := by
      by_cases h0 : (#S : ℝ) = (n : ℝ)
      · aesop
      · positivity

    -- `h₆` is the first inequality in equation (94)
    have h₆ : 1 / ( (1 - G.SpectralGap) ^ 2  * (1 / (#S : ℝ) - (1 / n : ℝ))  + (1 / n : ℝ))
        ≤ (#(G.neighbourhoodOfSet S) : ℝ) := by
      refine (one_div_le ?_ ?_).mp h₅
      · exact h₅a
      · exact h₅b

    -- the remaining analysis is elementary algebra to obtain the final form of equation (94)
    -- [check-final-number]
    have h₇ : 1 / ( (1 - γ) ^ 2  * (1 / (#S : ℝ) - (1 / n : ℝ))  + (1 / n : ℝ)) ≤
        1 / ( (1 - G.SpectralGap) ^ 2  * (1 / (#S : ℝ) - (1 / n : ℝ))  + (1 / n : ℝ)) := by
      refine one_div_le_one_div_of_le h₅b ?_
      nlinarith

    have h₈ : 1 / ( (1 - γ) ^ 2  * (1 / (#S : ℝ) - (1 / n : ℝ))  + (1 / n : ℝ))
        =  (#S : ℝ) / ( (1 - γ) ^ 2  * (1 - ( (#S : ℝ) / n : ℝ))  + ( (#S : ℝ) / n : ℝ)) := by
      field_simp --[h₁b]
      -- As of November 2026, field_simp closes, but a more detailed proof from the original is
      -- included below, commented out. (Originally, field_simp did not close).

      -- have : (1 - γ) ^ 2 * ((n : ℝ) - (#S : ℝ)) * (n : ℝ) + (#S : ℝ) * (n: ℝ)
      --     = (n : ℝ) * ((1 - γ) ^ 2 * ((n : ℝ) - (#S : ℝ)) + (#S : ℝ)) := by
      --   linarith
      -- rw [this]
      -- have : (#S : ℝ) * (n : ℝ) / (((1 - γ) ^ 2 * ((n : ℝ) - ↑(#S : ℝ)) + ↑(#S : ℝ)))
      --     = (#S : ℝ) * (n : ℝ) * (n : ℝ) / ((n : ℝ) * ((1 - γ) ^ 2
      --     * ((n : ℝ) - ↑(#S : ℝ)) + ↑(#S : ℝ))) := by
      --   have : 1 = (n : ℝ) / (n : ℝ) := by field_simp
      --   calc (#S : ℝ) * (n : ℝ) / (((1 - γ) ^ 2 * ((n : ℝ) - ↑(#S : ℝ)) + ↑(#S : ℝ)))
      --     _ = 1 * ((#S : ℝ) * (n : ℝ) / (((1 - γ) ^ 2 * ((n : ℝ) - ↑(#S : ℝ)) + ↑(#S : ℝ)))) :=
            --by
      --       linarith
      --     _ =  ((n : ℝ) / (n : ℝ)) *
      --         ((#S : ℝ) * (n : ℝ) / (((1 - γ) ^ 2 * ((n : ℝ) - ↑(#S : ℝ)) + ↑(#S : ℝ)))) := by
      --       rw [this]
      --     _ = (#S : ℝ) * (n : ℝ) * (n : ℝ) / ((n : ℝ) * ((1 - γ) ^ 2
      --         * ((n : ℝ) - ↑(#S : ℝ)) + ↑(#S : ℝ))) := by
      --       rw [this]
      --       have h₈a : 0 ≠ (1 - γ) ^ 2 * ((n : ℝ) - (#S : ℝ)) + (#S : ℝ) := by
      --         have :  0 < (1 - γ) ^ 2 * ((n : ℝ) - (#S : ℝ)) + (#S : ℝ) := by
      --           have : 0 ≤ (n : ℝ) - (#S : ℝ) := by nlinarith
      --           positivity
      --         exact ne_of_lt this
      --       field_simp
      --       linarith
      -- rw [this]
    rw [h₈] at h₇

    have : (#S : ℝ) / ((1 - γ) ^ 2 * (1 - α) + α) ≤
        (#S : ℝ) / ((1 - γ) ^ 2 * (1 - (#S : ℝ) / (n : ℝ)) + (#S : ℝ) / (n : ℝ)) := by
      have h₉ : (1 - γ)^2 < 1 := by
        have : 0 < γ := hγ1.1
        nlinarith
      have h₁₀ : 0 < 1 - (1 - γ) ^ 2 := by linarith
      have h₁₁ : (1 - γ) ^ 2 * (1 - (#S : ℝ) / (n : ℝ)) + (#S : ℝ) / (n : ℝ) =
          (1 - γ) ^ 2  + ((#S : ℝ) / (n : ℝ)) * (1 - (1 - γ) ^ 2 ) := by linarith
      rw [h₁₁]
      have h₁₂ : (1 - γ) ^ 2 * (1 - α) + α ≥
          ((1 - γ) ^ 2 + ((#S : ℝ) / n : ℝ) * (1 - (1 - γ) ^ 2)) := by
        have : (1 - γ) ^ 2 * (1 - α) + α = ((1 - γ) ^ 2 + α * (1 - (1 - γ) ^ 2)) := by
          linarith
        rw [this]
        gcongr

      gcongr
    grind


-- # The main result: spectral expansion implies vertex expansion, and a notably corollary


/-- The main theorem for spectral expansion implies vertex expansion -/
theorem SpectralImpliesVertex {V E : Type*} [Fintype V] [DecidableEq V]
    [DecidableEq E] (G : MultiDiGraph V E) (hV: 0 < #G.vertices )
    (r : ℕ) (hr : 0 < r) (hr1 : G.isRegularOfDegree r) :
    ∀ γ : ℝ, ((γ ∈ Set.Ioc 0 1) ∧ (spectralExpander γ G)
        → ( ∀ α ∈ Set.Icc 0 1 ,
        vertexExpander (α * (#G.vertices)) (1 / ((1 - α ) * (1-γ)^2 + α ) ) G )) := by
  -- introduce the terms and define standard nomenclature
  intro γ hγ α  hα
  have hra : r ≠ 0 := by exact Nat.ne_zero_of_lt hr
  let n := #G.vertices
  let u := UniformDist G.vertices
  let M := MultiDiGraph.randomWalkMatrix G
  let lambda := 1 - γ

  -- this part is getting the conditions ready to use claim `D`
  have h₁ (π : V → ℝ) (hπ : IsProbVector π G.vertices) : ( CP (π ᵥ* M) G.vertices -
      (1 / n : ℝ) ≤ (1-G.SpectralGap)^2 * ( ( CP π G.vertices ) - (1 / n : ℝ))) := by
    by_cases hu : (π ≠ UniformDist G.vertices)
    · have h₂ : (1-G.SpectralGap)^2 ≥ ((CP (π ᵥ* M) G.vertices) -
          (1 / n : ℝ )) / ((CP π G.vertices) - (1 / n : ℝ )) :=
          SpectralImpliesVertex_claim_B G hV π hπ hu r hr hr1
      have h₃ : (CP π G.vertices) - (1 / n : ℝ) ≠ 0 := SpectralImpliesVertex_claim_C G π hπ hu
      have : 1 / (#(Support π G.vertices) : ℝ) ≤ CP π G.vertices :=
        CP_reciprocal_support_leq_CP G.vertices π hπ
      have : 1 / (#G.vertices : ℝ ) ≤ 1 / (#(Support π G.vertices) : ℝ) := by
        exact helper_lemma_2 G π hπ
      have h₄: 1 / (n : ℝ) ≤ CP π G.vertices := by linarith
      have h₅ : (CP π G.vertices) ≠ (1 / n : ℝ) := sub_ne_zero.mp h₃
      have h₆ : 1 / (n : ℝ) < CP π G.vertices := lt_of_le_of_ne h₄ (id (Ne.symm h₅))
      have : (CP π G.vertices - 1 / (n : ℝ)) > 0 := sub_pos.mpr h₆
      exact (mul_inv_le_iff₀ this).mp h₂
    · have hu₂ : π = UniformDist G.vertices := by aesop
      have h₇ : π = (π ᵥ* M) := by
        rw [hu₂]
        exact DoublyStochasticUniformStationaryDist G.vertices G.randomWalkMatrix
            ⟨G.RegularrandomWalkMatrixIsDoublyStochastic hra hr1,
            G.diagonal_outside_support_randomWalkMatrix⟩
      have h₈ : (CP π G.vertices - 1 / (n : ℝ)) = 0 := by
        have h₈a : CP (UniformDist G.vertices) G.vertices = 1 / (#(Support (UniformDist
           G.vertices)  G.vertices )) := CP_UniformDist_equal_reciprocal_support G.vertices
             --CP_UniformDist_equal_reciprocal_support G.vertices hV
        have h₈b : #(Support (UniformDist G.vertices) G.vertices ) = n :=
          UniformDist_full_support G.vertices
        rw [← h₈b, hu₂]
        linarith
      have h₉ : (CP (π ᵥ* M) G.vertices - 1 / (n : ℝ)) = 0 := by rwa [h₇] at h₈
      rw [h₈]
      rw [h₉]
      linarith

  -- This uses claim `D`
  have : ∀ S : Finset V, (S ⊆ G.vertices) ∧ ( ( #S : ℝ ) ≤ α * ( n : ℝ )  ) → (( #S : ℝ ) /
      (lambda^2 * (1-α) + α ) ≤ ( #(G.neighbourhoodOfSet S) : ℝ ))  := by
    intro S hS
    have h₁₀ : ∀ S1 : Finset V, S1 ⊆ G.vertices ∧ 0 < #S1 →
        CP (UniformDist S1 ᵥ* G.randomWalkMatrix) G.vertices - (1 /  #G.vertices : ℝ )
        ≤ (1 - G.SpectralGap) ^ 2 *
        (CP (UniformDist S1) G.vertices - (1 /  #G.vertices : ℝ ))  := by
      intro S1 hS1
      have hS2 : IsProbVector (UniformDist S1)  G.vertices := by
        exact  UniformDist_is_ProbVector_on_superset_of_support S1 G.vertices hS1.2 hS1.1
      exact h₁ (UniformDist S1) hS2
    exact SpectralImpliesVertex_claim_D G α hα γ hγ h₁₀ r hr hr1 S hS

  -- concluding steps
  unfold vertexExpander
  have : ∀ S ⊆ G.vertices, (#S : ℝ) ≤ α * (n : ℝ) → (#S : ℝ) / (lambda ^ 2 * (1 - α) + α)
      ≤ (#(G.neighbourhoodOfSet S) : ℝ) := by aesop
  have : ∀ S ⊆ G.vertices, ((#S : ℝ) / (lambda ^ 2 * (1 - α) + α)
      ≤ (#(G.neighbourhoodOfSet S) : ℝ)) ∨ (¬ ((#S : ℝ) ≤ α * (n : ℝ) )) := by
    exact fun S a ↦ Or.symm (Decidable.not_or_of_imp (this S a))
  have : ∀ S ⊆ G.vertices, (#S : ℝ ) / (lambda ^ 2 * (1 - α) + α)
      = 1 / ((1 - α) * (1 - γ) ^ 2 + α) * (#S : ℝ) := by
    intro S hS
    ring
  aesop


/-- A notable special case of `SpectralImpliesVertex`: a `γ` spectral expander is in particular
a `(|G| / 2, 1 + γ)` spectral expander -/
theorem SpectralImpliesVertexCor {V E : Type*} [Fintype V] [DecidableEq V] [DecidableEq E]
    (G : MultiDiGraph V E) (hV: 0 < #G.vertices )
    (r : ℕ) (hr : 0 < r) (hr1 : G.isRegularOfDegree r) :
    ∀ γ : ℝ, (γ ∈ Set.Ioc 0 1) ∧ (spectralExpander γ G)
        → vertexExpander (1/2 * (#G.vertices : ℝ ) ) (1 + γ) G := by

  intro γ hγ
  have h₁ : ∀ γ : ℝ, ((γ ∈ Set.Ioc 0 1) ∧ (spectralExpander γ G) →
      ( ∀ α ∈ Set.Icc 0 1 , vertexExpander (α * (#G.vertices : ℝ))
      (1 / ((1 - α ) * (1-γ)^2 + α ) ) G )) := SpectralImpliesVertex G hV r hr hr1
  specialize h₁ γ
  have h₁ : 1/2 ∈ Set.Icc (0 : ℝ) (1 : ℝ) := by norm_num
  have h₂ : ∀ γ' : ℝ , γ' ∈ Set.Ioc 0  1 →  1 + γ' ≤ (1 / ((1 - 1/2 ) * (1-γ')^2 + 1/2 ) ) := by
    intro γ' hγ'
    field_simp
    norm_num
    have hγ1 : γ' ≤ 1 := hγ'.right
    have hdenom : 0 < (1 - γ')^2 + 1 := by
      apply add_pos_of_nonneg_of_pos
      · exact sq_nonneg (1 - γ')
      · norm_num
    have h₃ : (1 + γ') * ((1 - γ')^2 + 1) ≤ 2 := by
      calc (1 + γ') * ((1 - γ')^2 + 1)
        _  = (1 + γ') * (2 - 2 * γ' + γ' ^ 2) := by ring
        _ = 2 - γ' ^ 2 + γ' ^ 3 := by ring
        _ ≤ 2 := by
          have :  - γ' ^ 2 + γ' ^ 3 ≤ 0 := by nlinarith
          field_simp
          linarith
    exact RCLike.ofReal_le_ofReal.mp h₃
    --exact (le_div_iff₀ hdenom).mpr h₃
  specialize h₂ γ
  have h₄ : 1 + γ ≤ (1 / ((1 - 1/2 ) * (1-γ)^2 + 1/2 ) ) := by aesop
  have : vertexExpander (1/2 * (#G.vertices : ℝ)) (1 / ((1 - 1/2 ) *
      (1-γ)^2 + 1/2 ) ) G  → vertexExpander (1/2 * (#G.vertices : ℝ)) (1 + γ) G :=
    smallerAvertexExpander (1/2 * (#G.vertices : ℝ))
        (1 / ((1 - 1/2 ) * (1-γ)^2 + 1/2 ) ) (1 + γ) h₄ G
  aesop

--#lint
