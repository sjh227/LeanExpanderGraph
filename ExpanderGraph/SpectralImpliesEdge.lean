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
# SpectralImpliesEdge

This file formalises the result that non-zero spectral expansion implies non-zero
edge expansion

## Main results

*  `ExpanderMixingLemma` The expander mixing lemma relating spectral expansion to edge expansion

*  `SpectralImpliesEdgeExpansion` Non-zero spectral expansion implies non-zero edge expansion

-/

open Finset Function BigOperators Matrix
open CollisionProb
open MultiDiGraphSpace
open ExpansionDefs
open Classical
open ProbabilityVector
open StochasticMatrixSpace

namespace SpectralImpliesEdgeSpace



-- # Characteristic vectors of sets of vertices

/-- The characteristic vector of a set of vertices-/
def CharacteristicVectorofVertexSet {V : Type*} [DecidableEq V]
    (S : Finset V) : V → ℝ :=
  fun v => if v ∈ S then 1 else 0

/-- All elements which do not correspond to a vertex of CharacteristicVectorofVertexSet
equal zero -/
lemma CharacteristicVectorofVertexSet_is_zero_if_not_vertex
    {V : Type*} [DecidableEq V]
    (S : Finset V) : ∀ i ∉ S, CharacteristicVectorofVertexSet S i = 0 := by
  unfold CharacteristicVectorofVertexSet
  aesop

/-- All elements which do not belong to a superset of
of CharacteristicVectorofVertexSet equal zero,  -/
lemma CharacteristicVectorofVertexSet_is_zero_if_not_vertex'
    {V : Type*} [DecidableEq V] (S T : Finset V) (hT : S ⊆ T) :
    ∀ i ∉ T, CharacteristicVectorofVertexSet S i = 0 := by
  unfold CharacteristicVectorofVertexSet
  intro i hi
  have : i ∉ S := fun a ↦ hi (hT a)
  aesop

/-- The square of the `ℓ₂ norm` of `CharacteristicVectorofVertexSet S` is
equal to the cardinality of that set of vertices, `S` -/
lemma CharacteristicVector_L2normSQ_is_card {V : Type*} [DecidableEq V]
    (S : Finset V) : L2normSQ (CharacteristicVectorofVertexSet S) S = (#S : ℝ) := by
  unfold L2normSQ CharacteristicVectorofVertexSet
  aesop

/-- The `ℓ₂ norm` of `CharacteristicVectorofVertexSet S` is the same if taken over a superset
of `S` -/
lemma CharacteristicVector_L2normSQ_same_over_superset {V : Type*} [DecidableEq V]
    (S : Finset V) (P : Finset V) (h1 : S ⊆ P) : L2normSQ (CharacteristicVectorofVertexSet S) S
    = L2normSQ (CharacteristicVectorofVertexSet S) P := by
  unfold CharacteristicVectorofVertexSet L2normSQ
  simp only [ite_pow, one_pow, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, sum_ite_mem,
      inter_self, sum_const, nsmul_eq_mul, mul_one, Nat.cast_inj]
  have : P ∩ S = S := inter_eq_right.mpr h1
  rw [this]


-- # Helper lemmas

/-- Writing the cardinality of a vertex set in terms of its characteristic vector -/
lemma card_of_vertex_set_as_CharacteristicVectorofVertexSet
    {α : Type*} [Fintype α] [DecidableEq α ] (I : Finset α) (S : Finset α)
    (hS : S ⊆ I) (hI : 0 < #I ):
    #S = (CharacteristicVectorofVertexSet S) ⬝ᵥ (UniformDist I)
    / (UniformDist I) ⬝ᵥ (UniformDist I) := by
  have : UniformDist I ⬝ᵥ UniformDist I = (1 / #I : ℝ) := by
    unfold dotProduct UniformDist
    simp_all only [card_pos, one_div, mul_ite, ↓reduceIte, mul_zero,
        sum_ite_mem, univ_inter, sum_const, nsmul_eq_mul]
    field_simp
  rw [this]
  have : CharacteristicVectorofVertexSet S ⬝ᵥ UniformDist I = (#S / #I : ℝ) := by
    unfold dotProduct UniformDist CharacteristicVectorofVertexSet
    simp_all only [card_pos, one_div, mul_ite, ite_mul, one_mul,
        zero_mul, mul_zero, sum_ite_mem, univ_inter,
      sum_const, nsmul_eq_mul]
    field_simp
    have : I ∩ S = S := inter_eq_right.mpr hS
    rw [this]
  rw [this]
  field_simp

lemma L2normsq_of_characteristicVector { α : Type* } [Fintype α] [DecidableEq α] (I : Finset α)
    (S : Finset α) (hS : S ⊆ I) (hI : 0 < #I) :
    L2normSQ ( ((CharacteristicVectorofVertexSet S  ⬝ᵥ
    UniformDist I) / (UniformDist I ⬝ᵥ UniformDist I)) • UniformDist I ) I
    = (#S : ℝ)^2 / (#I : ℝ) := by
  have : #S = (CharacteristicVectorofVertexSet S) ⬝ᵥ (UniformDist I)
      / (UniformDist I) ⬝ᵥ (UniformDist I) :=
    card_of_vertex_set_as_CharacteristicVectorofVertexSet  I S hS hI
  rw [←this]
  have : L2normSQ ((#S : ℝ) • UniformDist I) I = (#S : ℝ)^2 *
      L2normSQ (UniformDist I) I := L2normSQ_commute_out_constant (UniformDist I) I (#S : ℝ)
  rw [this]
  have : L2normSQ (UniformDist I) I = (1 / #I : ℝ) :=
    UniformDist_L2normSQ_eq_reciprocal_of_support_cardinality I hI
  rw [this]
  aesop

lemma helper_lemma_1 {V : Type*} [Fintype V] (v1 v2 v3 : V → ℝ)(M : Matrix V V ℝ):
    (v1 + v2) ᵥ* M ⬝ᵥ v3 = (v1 ᵥ* M ⬝ᵥ v3) + v2 ᵥ* M ⬝ᵥ v3 := by
  rw [← @add_dotProduct, @add_vecMul]

-- Since the code was first written, field_simp has seemingly become more powerful so that
-- this helper is no longer actually used.
lemma helper_lemma_2 {V : Type*} [Fintype V] [DecidableEq V] (a : ℝ)
    (v1 v2 : V → ℝ) (M : Matrix V V ℝ):
    (a • v1) ᵥ* M ⬝ᵥ v2 = a * v1 ᵥ* M ⬝ᵥ v2 := by
  rw [smul_vecMul]
  (expose_names; rw [← diagonal_const_mulVec])
  aesop

lemma helper_lemma3 (a b : ℝ) (hab: |a| ≤ b) : a ≥ -b := neg_le_of_abs_le hab

lemma helper_lemma_4 (a : ℝ) (h₁ : 0 ≤ a) (h₂ : a ≤ 1/2) :
    a * (1-a) ≥ a / 2 := by
  have : a * (1-a) = a - a^2 := by linarith
  rw [this]
  have : a - a^2 - a/2 ≥ 0 := by
    nlinarith
  nlinarith

lemma helper_lemma5 (a b c : ℝ) (h₁ : 0 ≤ a) (h₂ : b ≥ c) :
    a * b ≥ a * c := by
  nlinarith

lemma helper_lemma6 (a b c : ℝ) (h₁ : 0 < a) (h₂ : b / a ≥ c) :
    b ≥ c * a := (le_div_iff₀ h₁).mp h₂

lemma inequality_lemma (a c b1 b2 : ℝ) (ha : 0 < a) (hc : 0 ≤ c) (hb2 : b1 ≤ b2):
    a * b1 * c ≤ a * b2 * c := by
  gcongr


-- # Main results and extracted lemmas therefrom


/-- Expresses the set of edges connecting two sets of vertices in terms of the
characteristic vectors and adjacency matrix -/
lemma eSTbyVector {V E : Type*} [Fintype V] [DecidableEq V]
    (G : MultiDiGraph V E) (S : Finset V) (T : Finset V) (r : ℕ)
    (hr : G.isRegularOfDegree r) (hS : S ⊆ G.vertices) (hT : T ⊆ G.vertices) (hr2 : 0 < r):
    (G.eST S T : ℝ) = r * ((CharacteristicVectorofVertexSet S) ᵥ*
    G.randomWalkMatrix) ⬝ᵥ (CharacteristicVectorofVertexSet T) := by

  -- first do a series of rewrites to get the vecMul and mulVec as a sum
  have h₀ : ((CharacteristicVectorofVertexSet S) ᵥ*
      G.randomWalkMatrix) = ∑ i, ((CharacteristicVectorofVertexSet S i) • (G.randomWalkMatrix i)) :=
    vecMul_eq_sum (CharacteristicVectorofVertexSet S) G.randomWalkMatrix
  rw [h₀]
  have h₁ : (∑ i, CharacteristicVectorofVertexSet S i • G.randomWalkMatrix i)
      ⬝ᵥ CharacteristicVectorofVertexSet T = ∑ j, ((∑ i, CharacteristicVectorofVertexSet S i •
      G.randomWalkMatrix i) j) *
      CharacteristicVectorofVertexSet T j := rfl
  rw [h₁]
  have h₂ : ∀ j, (∑ i, CharacteristicVectorofVertexSet S i • G.randomWalkMatrix i) j =
      (∑ i, CharacteristicVectorofVertexSet S i * G.randomWalkMatrix i j) :=
    fun j ↦ congrFun (id (Eq.symm h₀)) j
  have h₃ : ∑ j, ((∑ i, CharacteristicVectorofVertexSet S i • G.randomWalkMatrix i) j) *
      CharacteristicVectorofVertexSet T j = ∑ j, (∑ i, CharacteristicVectorofVertexSet S i *
      G.randomWalkMatrix i j) *
      CharacteristicVectorofVertexSet T j :=
    Fintype.sum_congr
      (fun a ↦
        (∑ i, CharacteristicVectorofVertexSet S i • G.randomWalkMatrix i) a *
          CharacteristicVectorofVertexSet T a)
      (fun a ↦
          (∑ i, CharacteristicVectorofVertexSet S i * G.randomWalkMatrix i a) *
          CharacteristicVectorofVertexSet T a)
      fun a ↦ congrFun (congrArg HMul.hMul (h₂ a)) (CharacteristicVectorofVertexSet T a)
  rw [h₃]
  have h₄ : ∑ j, (∑ i, CharacteristicVectorofVertexSet S i * G.randomWalkMatrix i j)
      * CharacteristicVectorofVertexSet T j =
      ∑ j, ∑ i, CharacteristicVectorofVertexSet S i * G.randomWalkMatrix i j
      * CharacteristicVectorofVertexSet T j := by
    apply Finset.sum_congr rfl
    intro x hx
    rw [@sum_mul]
  rw [h₄]
  have h₅ : (r : ℝ) * ∑ j, ∑ i, CharacteristicVectorofVertexSet S i *
      G.randomWalkMatrix i j * CharacteristicVectorofVertexSet T j =
      ∑ j, ∑ i, CharacteristicVectorofVertexSet S i *
      ((r : ℝ) * G.randomWalkMatrix i j) * CharacteristicVectorofVertexSet T j := by
    rw [mul_sum]
    apply sum_congr rfl
    intro _ _
    rw [mul_sum]
    apply sum_congr rfl
    intro _ _
    ring
  rw [h₅]

  -- Now turn the sums into sums just over the vertices
  have h₆ : ∀ i ∉ G.vertices, CharacteristicVectorofVertexSet S i = 0 := by
    unfold CharacteristicVectorofVertexSet
    intro i hi
    have hi' : i ∉ S := fun a ↦ hi (hS a)
    exact ite_eq_right hi'
  have h₇ : ∑ j, ∑ i, CharacteristicVectorofVertexSet S i * ((r : ℝ) * G.randomWalkMatrix i j) *
      CharacteristicVectorofVertexSet T j =
      ∑ j, ∑ i ∈ G.vertices, CharacteristicVectorofVertexSet S i *
      ((r : ℝ) * G.randomWalkMatrix i j) *
      CharacteristicVectorofVertexSet T j := by
    have : ∑ j, ∑ i, CharacteristicVectorofVertexSet S i * ((r : ℝ) *
        G.randomWalkMatrix i j) *
        CharacteristicVectorofVertexSet T j =
        ∑ j, ∑ i ∈ G.vertices, CharacteristicVectorofVertexSet S i * ((r : ℝ) *
        G.randomWalkMatrix i j) *
        CharacteristicVectorofVertexSet T j  +
        ∑ j, ∑ i ∉ G.vertices, CharacteristicVectorofVertexSet S i * ((r : ℝ) *
        G.randomWalkMatrix i j) *
        CharacteristicVectorofVertexSet T j := by
      rw [←sum_add_distrib]
      apply sum_congr rfl
      intro j
      exact fun a ↦
        Eq.symm
          (sum_add_sum_compl G.vertices fun i ↦
            CharacteristicVectorofVertexSet S i * (r * G.randomWalkMatrix i j : ℝ) *
              CharacteristicVectorofVertexSet T j)
    rw [this]
    have : ∑ j, ∑ i ∉ G.vertices, CharacteristicVectorofVertexSet S i * ((r : ℝ) *
        G.randomWalkMatrix i j) * CharacteristicVectorofVertexSet T j = 0 := by
      apply sum_eq_zero
      intro j _
      apply sum_eq_zero
      intro i hii
      aesop
    rw [this]
    linarith
  rw [h₇]
  have h₈ : ∀ j ∉ G.vertices, CharacteristicVectorofVertexSet T j = 0 := by
    unfold CharacteristicVectorofVertexSet
    intro j hj
    have hj' : j ∉ T := fun a ↦ hj (hT a)
    exact ite_eq_right hj'
  have h₉ : ∑ j, ∑ i ∈ G.vertices, CharacteristicVectorofVertexSet S i
      * ((r : ℝ) * G.randomWalkMatrix i j) *
      CharacteristicVectorofVertexSet T j =
      ∑ j ∈ G.vertices, ∑ i ∈ G.vertices,
      CharacteristicVectorofVertexSet S i * ((r : ℝ) * G.randomWalkMatrix i j) *
      CharacteristicVectorofVertexSet T j := by
    have : ∑ j, ∑ i ∈ G.vertices, CharacteristicVectorofVertexSet S i
        * ((r : ℝ) * G.randomWalkMatrix i j) *
        CharacteristicVectorofVertexSet T j =
        ∑ j ∈ G.vertices, ∑ i ∈ G.vertices, CharacteristicVectorofVertexSet S i
        * ((r : ℝ) * G.randomWalkMatrix i j) *
        CharacteristicVectorofVertexSet T j +
        ∑ j ∉ G.vertices, ∑ i ∈ G.vertices, CharacteristicVectorofVertexSet S i
        * ((r : ℝ) * G.randomWalkMatrix i j) *
        CharacteristicVectorofVertexSet T j :=
      Eq.symm
        (sum_add_sum_compl G.vertices fun i ↦
          ∑ i_1 ∈ G.vertices,
            CharacteristicVectorofVertexSet S i_1 * (r * G.randomWalkMatrix i_1 i : ℝ) *
              CharacteristicVectorofVertexSet T i)
    rw [this]
    have : ∑ j ∉  G.vertices,
        ∑ i ∈ G.vertices,
        CharacteristicVectorofVertexSet S i * ((r : ℝ) * G.randomWalkMatrix i j) *
        CharacteristicVectorofVertexSet T j = 0 := by
      apply sum_eq_zero
      intro x _
      apply sum_eq_zero
      intro _ _
      aesop
    rw [this]
    linarith
  rw [h₉]

  -- having established the correct finite sum, the goal is closed by unfolding `MultiDiGraph.eST`
  -- along with some other terms and then making heavy use of `simp` along with other powerful
  -- tactics
  have h₁₀ : ∀i ∈ G.vertices, ∀j, (r : ℝ)
      * G.randomWalkMatrix i j = (G.adjacencyMatrix i j : ℝ) :=
    G.regular_adjacency_is_r_times_random_walk r (Ne.symm (Nat.ne_zero_of_lt hr2)) hr
  have h₁₁ : ∑ j ∈ G.vertices, ∑ i ∈ G.vertices, CharacteristicVectorofVertexSet S i *
      ((r : ℝ) * G.randomWalkMatrix i j) * CharacteristicVectorofVertexSet T j =
      ∑ j ∈ G.vertices, ∑ i ∈ G.vertices, CharacteristicVectorofVertexSet S i *
      (G.adjacencyMatrix i j : ℝ)  * CharacteristicVectorofVertexSet T j := by
    aesop
  rw [h₁₁]
  unfold CharacteristicVectorofVertexSet MultiDiGraph.adjacencyMatrix MultiDiGraph.eST
  simp only [of_apply, ite_mul, one_mul, zero_mul, mul_ite, mul_one, mul_zero, sum_ite_irrel,
    sum_ite_mem, sum_const_zero]
  simp only [Finset.inter_eq_right.2 hT, Finset.inter_eq_right.2 hS,
      card_eq_sum_ones, sum_filter, Nat.cast_sum]
  simp_rw [sum_comm (t := G.edges)]
  apply sum_congr rfl
  intro e he
  simp only [apply_ite, ite_and]
  simp [sum_ite_eq]



-- this is the proof of the calc block in the expander mixing lemma
lemma expander_mixing_calc {V E : Type*} [Fintype V] [DecidableEq V] [DecidableEq E]
    (G : MultiDiGraph V E) (hV: 0 < #G.vertices ) (r: ℕ)
    (hr : 0 < r ∧ G.isRegularOfDegree r)
    (S : Finset V) (hS : S ⊆ G.vertices) (T : Finset V) (hT : T ⊆ G.vertices)

    (χSperp : V → ℝ)
    (hχS1 : CharacteristicVectorofVertexSet S =
        (CharacteristicVectorofVertexSet S ⬝ᵥ UniformDist G.vertices
        / UniformDist G.vertices ⬝ᵥ UniformDist G.vertices) • UniformDist G.vertices + χSperp)
    (hχS2 : UniformDist G.vertices ⬝ᵥ χSperp = 0)
    (χTperp : V → ℝ)
    (hχT1 : CharacteristicVectorofVertexSet T =
        (CharacteristicVectorofVertexSet T ⬝ᵥ UniformDist G.vertices
        / UniformDist G.vertices ⬝ᵥ UniformDist G.vertices) • UniformDist G.vertices + χTperp)
    (hχT2 : UniformDist G.vertices ⬝ᵥ χTperp = 0):


    (G.eST S T : ℝ) / ((#G.vertices : ℝ) * r) =
    ((#S : ℝ) / (#G.vertices : ℝ)) * ((#T : ℝ) / (#G.vertices : ℝ))
    + (1 / (#G.vertices : ℝ)) * (χSperp ᵥ*
    G.randomWalkMatrix) ⬝ᵥ χTperp := by

  -- define some terms that we use heavily
  let χS := CharacteristicVectorofVertexSet S
  let χT := CharacteristicVectorofVertexSet T
  let u := UniformDist G.vertices

  have hr2 : r ≠ 0 := by
    exact Nat.ne_zero_of_lt hr.1

  let n := (#G.vertices : ℝ)
  have hn: n ≠ 0 := by aesop
  let α := (#S : ℝ) / (#G.vertices : ℝ)
  let β := (#T : ℝ) / (#G.vertices : ℝ)

  -- now the main calc block
  calc (G.eST S T : ℝ) / (n * r)
    _ = (1/n) * (((α * n) • u + χSperp) ᵥ*
          G.randomWalkMatrix) ⬝ᵥ ((β * n) • u + χTperp) := by
      have : (α * n) = (χS ⬝ᵥ u / u ⬝ᵥ u) := by
        have : (α * n) = (#S : ℝ) := by
          have : α * n = ((#S : ℝ) / n) * n := by aesop
          rw [this]
          field_simp
        rw [this]
        exact card_of_vertex_set_as_CharacteristicVectorofVertexSet G.vertices S hS hV
      rw [this]
      have : (β * n) = (χT ⬝ᵥ u / u ⬝ᵥ u) := by
        have : (β * n) = (#T : ℝ) := by
          have : β * n = ((#T : ℝ) / n) * n := by trivial
          rw [this]
          --field_simp
          grind
        rw [this]
        exact card_of_vertex_set_as_CharacteristicVectorofVertexSet  G.vertices T hT hV
      rw [this, ←hχS1, ←hχT1]
      have h1 : (MultiDiGraph.eST G S T : ℝ) = r *
          ((CharacteristicVectorofVertexSet S) ᵥ*
          G.randomWalkMatrix) ⬝ᵥ (CharacteristicVectorofVertexSet T) :=
        eSTbyVector G S T r hr.2 hS hT hr.1
      field_simp

      have : χS ᵥ* G.randomWalkMatrix ⬝ᵥ χT * (n * r) = χS ᵥ*
          G.randomWalkMatrix ⬝ᵥ χT * r * n := by
        linarith
      rw [h1]
      --rw [this, h1]
      --linarith
    _ = (1/n) *
          ( (((α * n) • u) ᵥ* G.randomWalkMatrix) ⬝ᵥ ((β * n) • u + χTperp)  +
            ((χSperp ᵥ* G.randomWalkMatrix) ⬝ᵥ ((β * n) • u + χTperp))) := by
        have : ((α * n) • u + χSperp) ᵥ* G.randomWalkMatrix ⬝ᵥ ((β * n) • u + χTperp) =
            ((α * n) • u) ᵥ* G.randomWalkMatrix ⬝ᵥ ((β * n) • u + χTperp) +
            χSperp ᵥ* G.randomWalkMatrix ⬝ᵥ ((β * n) • u + χTperp) :=
          helper_lemma_1 ((α * n) • u)  χSperp ((β * n) • u + χTperp) G.randomWalkMatrix
        rw [this]
    _ = (1/n) *
          ( (((α * n) • u) ᵥ* G.randomWalkMatrix) ⬝ᵥ ((β * n) • u)  +
            (((α * n) • u) ᵥ* G.randomWalkMatrix) ⬝ᵥ χTperp +
            (χSperp ᵥ* G.randomWalkMatrix) ⬝ᵥ ((β * n) • u) +
            (χSperp ᵥ* G.randomWalkMatrix) ⬝ᵥ χTperp ) := by
        rw [←dotProduct_add]
        field_simp
        simp only [dotProduct_add, dotProduct_smul, smul_eq_mul]
        -- distributivity of matrix multiplication
        linarith
    _ = (1/n) *
          ( (α * n) * (β * n) * (u ᵥ* G.randomWalkMatrix) ⬝ᵥ u  +
            (α * n) * (u ᵥ* G.randomWalkMatrix) ⬝ᵥ χTperp +
            (β * n) * (χSperp ᵥ* G.randomWalkMatrix) ⬝ᵥ u +
            (χSperp ᵥ* G.randomWalkMatrix) ⬝ᵥ χTperp ) := by
        field_simp
        simp only [smul_vecMul, smul_dotProduct, dotProduct_smul]
        ring
        -- ring now closes this proof, but below is some further lines from
        -- the original version when it did not close it.
        -- Note that although the helper lemmas are no longer used, they have
        -- been left intact, above.

        -- have : ((n * α) • u) ᵥ* G.randomWalkMatrix ⬝ᵥ u =
        --     (α * n) * u ᵥ* G.randomWalkMatrix ⬝ᵥ u := by sorry
        --   --helper_lemma_2 (n * α) u u G.randomWalkMatrix
        -- rw [this]
        -- simp only [dotProduct_smul, smul_eq_mul, add_left_inj]
        -- rw [this]
        -- have : ((α * n) • u) ᵥ* G.randomWalkMatrix ⬝ᵥ χTperp =
        --     (α * n) * u ᵥ* G.randomWalkMatrix ⬝ᵥ χTperp :=
        --   helper_lemma_2 (α * n) u χTperp G.randomWalkMatrix
        -- rw [this]
        -- linarith
        -- commute out the constants
    _ = (1/n) *
          ( (α * n) * (β * n) * (u ᵥ* G.randomWalkMatrix) ⬝ᵥ u  +
            (α * n) * (u ᵥ* G.randomWalkMatrix) ⬝ᵥ χTperp +
            (β * n) * χSperp ⬝ᵥ (G.randomWalkMatrix *ᵥ u) +
            (χSperp ᵥ* G.randomWalkMatrix) ⬝ᵥ χTperp ) := by
        have : χSperp ᵥ* G.randomWalkMatrix ⬝ᵥ u = χSperp ⬝ᵥ G.randomWalkMatrix *ᵥ u :=
          Eq.symm (dotProduct_mulVec χSperp G.randomWalkMatrix u)
        rw [this]
        -- associativity of matrix multiplication
    _ = (1/n) *
          ( (α * n) * (β * n) * u ⬝ᵥ u  +
            (α * n) * u ⬝ᵥ χTperp +
            (β * n) * χSperp ⬝ᵥ u +
            (χSperp ᵥ* G.randomWalkMatrix) ⬝ᵥ χTperp ) := by
        have : u ᵥ* G.randomWalkMatrix = u := by
        -- standard fact when `G` is regular
          have : G.randomWalkMatrix ∈ doublyStochastic ℝ V ∧
              ∀ l ∉ G.vertices, G.randomWalkMatrix l l = 1 :=
            G.Regular_is_DoublyStochastic hr2 hr.2
          have : u = u ᵥ* G.randomWalkMatrix :=
            DoublyStochasticUniformStationaryDist G.vertices G.randomWalkMatrix this
          exact id (Eq.symm this)
        rw [this]
        have : G.randomWalkMatrix *ᵥ u = u := by
          have : G.randomWalkMatrix *ᵥ u = u ᵥ* G.randomWalkMatrix.transpose :=
            Eq.symm (vecMul_transpose G.randomWalkMatrix u)
          rw [this]
          have : G.randomWalkMatrix ∈ doublyStochastic ℝ V ∧
              ∀ l ∉ G.vertices, G.randomWalkMatrix l l = 1 :=
            G.Regular_is_DoublyStochastic hr2 hr.2
          have : G.randomWalkMatrix ∈ doublyStochastic ℝ V := this.1
          have : G.randomWalkMatrix.transpose ∈ doublyStochastic ℝ V ∧
              ∀ l ∉ G.vertices, G.randomWalkMatrix l l = 1 := by
            constructor
            · exact mem_doublyStochastic_iff_transpose.mp this
            · exact fun l a ↦ MultiDiGraph.diagonal_outside_support_randomWalkMatrix G l a
          have : u = u ᵥ* G.randomWalkMatrix.transpose :=
            DoublyStochasticUniformStationaryDist G.vertices G.randomWalkMatrix.transpose this
          exact id (Eq.symm this)
        rw [this]
    _ = (1/n) * ( (α * n) * (β * n) * u ⬝ᵥ u  +
        (χSperp ᵥ* G.randomWalkMatrix) ⬝ᵥ χTperp ) := by
        rw [hχT2]
        have hχS2a : χSperp ⬝ᵥ u = 0 := by
          rw [dotProduct_comm]
          exact hχS2
        rw [hχS2a]
        linarith
    _ = α * β + (1 / n) * (χSperp ᵥ* G.randomWalkMatrix) ⬝ᵥ χTperp := by
      have : u ⬝ᵥ u = 1 / n :=
        UniformDist_self_dot_product_eq_reciprocal_of_support_cardinality G.vertices hV
      rw [this]
      field_simp
      --linarith


set_option maxHeartbeats 600000 in
-- This has already been decomposed to a great extent, and what remains is a long - but not
-- unreasonably so (given the work that would be incurred to decompose further) - proof,
-- hence the increase in heartbeats

/-- The expander mixing lemma relating spectral expansion to edge expansion. -/
lemma ExpanderMixingLemma {V E : Type*} [Fintype V] [DecidableEq V] [DecidableEq E]
    (G : MultiDiGraph V E) (hV: 0 < #G.vertices ) (r : ℕ)
    (hr : 0 < r ∧ G.isRegularOfDegree r) (γ : ℝ) (hγ : spectralExpander γ G) :
    ∀ S ⊆ G.vertices, ∀ T ⊆ G.vertices, |((MultiDiGraph.eST G S T) : ℝ)
        / (#(G.vertices)*(r : ℝ)) - ((#S : ℝ) / (#G.vertices : ℝ))
        * ((#T : ℝ) / (#G.vertices : ℝ))| ≤ (1 - γ) * √ (((#S : ℝ) / (#G.vertices : ℝ))
        * (1- ((#S : ℝ) / (#G.vertices : ℝ)) ) * ((#T : ℝ) / (#G.vertices : ℝ))
        * (1- ((#T : ℝ) /(#G.vertices : ℝ)) )) := by

  -- initially set up some standard notation
  intro S hS T hT
  let n := (#G.vertices : ℝ)
  have hn : 0 < n := Nat.cast_pos'.mpr hV
  have hn' : 0 < (1 / n) := one_div_pos.mpr hn
  let α := (#S : ℝ) / n
  have hα : 0 ≤ α := by positivity
  have hα' : α ≤ 1 := by
    have : #S ≤ #G.vertices := card_le_card hS
    refine (div_le_one₀ ?_).mpr ?_
    · exact Nat.cast_pos'.mpr hV
    · exact Nat.cast_le.mpr this
  let β := (#T : ℝ) / n
  have hβ : 0 ≤ β := by positivity
  have hβ' : β ≤ 1 := by
    have : #T ≤ #G.vertices := card_le_card hT
    refine (div_le_one₀ ?_).mpr ?_
    · exact Nat.cast_pos'.mpr hV
    · exact Nat.cast_le.mpr this
  have hr2 : r ≠ 0 := Nat.ne_zero_of_lt hr.1

  -- defining `χS`, `χT` and `u` as used in the informal proof
  let χS := CharacteristicVectorofVertexSet S
  let χT := CharacteristicVectorofVertexSet T
  let u := UniformDist G.vertices
  have hu : 0 < u ⬝ᵥ u  := UniformDist_self_dot_product_nonzero G.vertices hV
  have hu2 : u ⬝ᵥ u  ≠ 0 := by linarith
  have hχ₀ : ∃ χSperp : V → ℝ,
    (χS = ((χS ⬝ᵥ u / (u ⬝ᵥ u )) • u + χSperp ))
    ∧ u ⬝ᵥ χSperp = 0 := existPerpVector χS u hu2
  obtain ⟨χSperp, hχS1, hχS2⟩ := hχ₀
  have hχ₁ : ∃ χTperp : V → ℝ,
    (χT = (( χT ⬝ᵥ u / (u ⬝ᵥ u )) • u + χTperp ))
    ∧ u ⬝ᵥ χTperp = 0 := existPerpVector χT u hu2
  obtain ⟨χTperp, hχT1, hχT2⟩ := hχ₁
  have hχSperp : ∀ i ∉ G.vertices, χSperp i = 0 := by
    have : χSperp = χS - (χS ⬝ᵥ u / u ⬝ᵥ u) • u := eq_sub_of_add_eq' (id (Eq.symm hχS1))
    rw [this]
    intro i hi
    have : (χS - (χS ⬝ᵥ u / u ⬝ᵥ u) • u) i = χS i - (χS ⬝ᵥ u / u ⬝ᵥ u) • u i := rfl
    rw [this]
    have : χS i = 0 := by
      have : ∀ j ∉ S, χS j = 0 := CharacteristicVectorofVertexSet_is_zero_if_not_vertex S
      exact this i fun a ↦ hi (hS a)
    rw [this]
    have : u i = 0 := UniformDist_zero_outside_support G.vertices i hi
    rw [this]
    aesop

  have hχSperp' : ∀ i ∉ G.vertices, (χSperp ᵥ* G.randomWalkMatrix) i = 0 :=
    fun i a ↦ if_not_vertex_prod_of_p_randomwalk_matrix_eq_zero G χSperp hχSperp i a

  have hχTperp : ∀ i ∉ G.vertices, χTperp i = 0 := by
    have : χTperp = χT - (χT ⬝ᵥ u / u ⬝ᵥ u) • u := eq_sub_of_add_eq' (id (Eq.symm hχT1))
    rw [this]
    intro i hi
    have : (χT - (χT ⬝ᵥ u / u ⬝ᵥ u) • u) i = χT i - (χT ⬝ᵥ u / u ⬝ᵥ u) • u i := rfl
    rw [this]
    have : χT i = 0 := by
      have : ∀ j ∉ T, χT j = 0 := CharacteristicVectorofVertexSet_is_zero_if_not_vertex T
      exact this i fun a ↦ hi (hT a)
    rw [this]
    have : u i = 0 := UniformDist_zero_outside_support G.vertices i hi
    rw [this]
    aesop

  -- leading to equation (105)
  have h₁ : (G.eST S T : ℝ) / (n * r) = α * β + (1 / n) * (χSperp ᵥ*
      G.randomWalkMatrix) ⬝ᵥ χTperp :=
    expander_mixing_calc G hV r hr S hS T hT χSperp hχS1 hχS2 χTperp hχT1 hχT2

  -- below equation (106)
  have h₂ : L2normSQ χSperp G.vertices = (α * (1 - α) * n) := by
    have ha : L2normSQ χS G.vertices = (#S : ℝ) := by
      have : L2normSQ χS G.vertices = L2normSQ χS S := by
        have : L2normSQ χS S  = L2normSQ χS G.vertices :=
          CharacteristicVector_L2normSQ_same_over_superset S G.vertices hS
        rw [←this]
      rw [this]
      exact CharacteristicVector_L2normSQ_is_card S
    have : (#S : ℝ) = α * n := by
      have : (#S : ℝ) / n * n = α * n := by trivial
      rw [←this]
      grind
    have : L2normSQ χS G.vertices = α ^ 2 * n + L2normSQ χSperp G.vertices := by
      have h₂a : L2normSQ χS G.vertices = L2normSQ ((χS ⬝ᵥ u / u ⬝ᵥ u) • u ) G.vertices
          + L2normSQ χSperp G.vertices := by
        have h₂b : ((χS ⬝ᵥ u / u ⬝ᵥ u) • u ) ⬝ᵥ χSperp = 0 := by
          calc ((χS ⬝ᵥ u / u ⬝ᵥ u) • u ) ⬝ᵥ χSperp
            _ = ((χS ⬝ᵥ u / u ⬝ᵥ u)) * (u  ⬝ᵥ χSperp) := by
              simp only [smul_dotProduct, smul_eq_mul]
            _ = ((χS ⬝ᵥ u / u ⬝ᵥ u)) * 0 := by rw [hχS2]
            _ = 0 := by linarith
        have h₂c : ∀ i ∉ G.vertices, ((χS ⬝ᵥ u / u ⬝ᵥ u) • u ) i = 0 := by
          intro i hi
          have : ((χS ⬝ᵥ u / u ⬝ᵥ u) • u) i = (χS ⬝ᵥ u / u ⬝ᵥ u) * u i := rfl
          rw [this]
          have : ∀ i ∉ G.vertices, u i = 0 :=
            UniformDist_zero_outside_support G.vertices
          specialize this i hi
          rw [this]
          exact Lean.Grind.Semiring.mul_zero (χS ⬝ᵥ u / u ⬝ᵥ u)
        have : χSperp ⬝ᵥ (χS ⬝ᵥ u / u ⬝ᵥ u) • u = 0 := by
          have : ((χS ⬝ᵥ u / u ⬝ᵥ u) • u ) ⬝ᵥ χSperp = χSperp ⬝ᵥ (χS ⬝ᵥ u / u ⬝ᵥ u) • u  :=
            dotProduct_comm ((χS ⬝ᵥ u / u ⬝ᵥ u) • u) χSperp
          rw [← this]
          exact h₂b
        exact L2normsq_of_orthogonal χS χSperp ((χS ⬝ᵥ u / u ⬝ᵥ u) • u ) G.vertices hχS1 this h₂c
      have : L2normSQ ( ((χS  ⬝ᵥ
          u) / (u ⬝ᵥ u)) • u ) G.vertices
          = (#S : ℝ)^2 / n := L2normsq_of_characteristicVector G.vertices S hS hV
      rw [this] at h₂a
      have : (#S : ℝ) ^ 2 / n = α^2 * n := by
        have : (#S : ℝ) = α * n := by gcongr
        rw [this]
        field_simp
        --linarith
      rw [this] at h₂a
      exact h₂a
    rw [this] at ha
    linarith


  -- below equation (106)
  have h₃ : L2normSQ χTperp G.vertices = (β * (1 - β) * n) := by
    have ha : L2normSQ χT G.vertices = (#T : ℝ) := by
      have : L2normSQ χT T  = L2normSQ χT G.vertices :=
          CharacteristicVector_L2normSQ_same_over_superset T G.vertices hT
      rw [←this]
      exact CharacteristicVector_L2normSQ_is_card T
    have : (#T : ℝ) = β * n := by
      have : (#T : ℝ) / n * n = β * n := by trivial
      rw [←this]
      grind
    have : L2normSQ χT G.vertices = β ^ 2 * n + L2normSQ χTperp G.vertices := by
      have h₃a : L2normSQ χT G.vertices = L2normSQ ((χT ⬝ᵥ u / u ⬝ᵥ u) • u ) G.vertices
              + L2normSQ χTperp G.vertices := by
        have h₃b : ((χT ⬝ᵥ u / u ⬝ᵥ u) • u ) ⬝ᵥ χTperp = 0 := by
          calc ((χT ⬝ᵥ u / u ⬝ᵥ u) • u ) ⬝ᵥ χTperp
            _ = ((χT ⬝ᵥ u / u ⬝ᵥ u)) * (u  ⬝ᵥ χTperp) := by
              simp only [smul_dotProduct, smul_eq_mul]
            _ = ((χT ⬝ᵥ u / u ⬝ᵥ u)) * 0 := by rw [hχT2]
            _ = 0 := by linarith
        have h₃c : ∀ i ∉ G.vertices, ((χT ⬝ᵥ u / u ⬝ᵥ u) • u ) i = 0 := by
          intro i hi
          have : ((χT ⬝ᵥ u / u ⬝ᵥ u) • u) i = (χT ⬝ᵥ u / u ⬝ᵥ u) * u i := rfl
          rw [this]
          have : ∀ i ∉ G.vertices, u i = 0 :=
            UniformDist_zero_outside_support G.vertices
          specialize this i hi
          rw [this]
          exact Lean.Grind.Semiring.mul_zero (χT ⬝ᵥ u / u ⬝ᵥ u)
        have : χTperp ⬝ᵥ (χT ⬝ᵥ u / u ⬝ᵥ u) • u = 0 := by
          have : ((χT ⬝ᵥ u / u ⬝ᵥ u) • u ) ⬝ᵥ χTperp = χTperp ⬝ᵥ (χT ⬝ᵥ u / u ⬝ᵥ u) • u  :=
            dotProduct_comm ((χT ⬝ᵥ u / u ⬝ᵥ u) • u) χTperp
          rw [← this]
          exact h₃b
        exact L2normsq_of_orthogonal χT χTperp ((χT ⬝ᵥ u / u ⬝ᵥ u) • u ) G.vertices hχT1 this h₃c
      have : L2normSQ ( ((χT  ⬝ᵥ
          u) / (u ⬝ᵥ u)) • u ) G.vertices
          = (#T : ℝ)^2 / n := L2normsq_of_characteristicVector G.vertices T hT hV
      rw [this] at h₃a
      have : (#T : ℝ) ^ 2 / n = β^2 * n := by
        have : (#T : ℝ) = β * n := by gcongr
        rw [this]
        field_simp
        --linarith
      rw [this] at h₃a
      exact h₃a
    rw [this] at ha
    linarith

  -- final calc block of informal proof
  calc |((G.eST S T) :ℝ) / (n * r) - α * β|
    _ = |(1 / n) * (χSperp ᵥ* G.randomWalkMatrix) ⬝ᵥ χTperp| := by aesop
    _ = |1 / n| * |χSperp ᵥ* G.randomWalkMatrix ⬝ᵥ χTperp| :=
      abs_mul (1 / n) (χSperp ᵥ* G.randomWalkMatrix ⬝ᵥ χTperp)
    _ = (1 / n) * |χSperp ᵥ* G.randomWalkMatrix ⬝ᵥ χTperp| := by
      aesop
    _ ≤ (1/n) * √ (L2normSQ (χSperp ᵥ* G.randomWalkMatrix) G.vertices)
      * √ (L2normSQ χTperp G.vertices) := by
      have : |χSperp ᵥ* G.randomWalkMatrix ⬝ᵥ χTperp| ≤
          √(L2normSQ (χSperp ᵥ* G.randomWalkMatrix) G.vertices)
          * √(L2normSQ χTperp G.vertices) :=
        L2normsq_bound G.vertices (χSperp ᵥ* G.randomWalkMatrix) χTperp hχSperp'  hχTperp
      nlinarith
    _ ≤ (1/n) * (1 - G.SpectralGap) * √ (L2normSQ χSperp G.vertices)
        * √ (L2normSQ χTperp G.vertices) := by
      have h₀ : √(L2normSQ (χSperp ᵥ* G.randomWalkMatrix) G.vertices)
          ≤ (1 - G.SpectralGap) * √ (L2normSQ χSperp G.vertices) :=
        G.L2norm_spectral_gap_bound hV hr2 hr.2 χSperp hχS2 hχSperp
      have h₄ : 0 < (1/n) := hn'
      have h₅ : 0 ≤ √ (L2normSQ χTperp G.vertices) := Real.sqrt_nonneg (L2normSQ χTperp G.vertices)
      have : 1 / n * √(L2normSQ (χSperp ᵥ* G.randomWalkMatrix) G.vertices)
          * √(L2normSQ χTperp G.vertices) ≤
          1 / n * ((1 - G.SpectralGap) * √(L2normSQ χSperp G.vertices))
          * √(L2normSQ χTperp G.vertices) :=
        inequality_lemma (1/n) (√ (L2normSQ χTperp G.vertices))
          (√(L2normSQ (χSperp ᵥ* G.randomWalkMatrix) G.vertices))
          ((1 - G.SpectralGap) * √ (L2normSQ χSperp G.vertices)) h₄ h₅ h₀
      linarith
    _ ≤ (1/n) * (1 - γ) * √ (L2normSQ χSperp G.vertices) * √ (L2normSQ χTperp G.vertices) := by
      have h₁ : 1-G.SpectralGap ≤ 1 - γ := tsub_le_tsub_left hγ 1
      gcongr
    _ = (1/n) * (1 - γ) * √ (α * (1-α) * n) * √ (β * (1-β) * n) := by aesop
    _ = (1/n) * (1 - γ) * √ (α * (1-α) * n * (β * (1-β) * n)) := by
      have haaα : 0 ≤ (α * (1-α) * n) := by
        field_simp
        ring_nf
        nlinarith [mul_nonneg hα (sub_nonneg.mpr hα')]
      have hbbβ : 0 ≤ (β * (1-β) * n) := by
        field_simp
        ring_nf
        nlinarith [mul_nonneg hβ (sub_nonneg.mpr hβ')]
      have : √ (α * (1-α) * n) * √ (β * (1-β) * n) = √ (α * (1-α) * n * (β * (1-β) * n)) := by
        aesop
      rw [← this]
      linarith
    _ = (1/n) * (1 - γ) * √ (α * (1-α) * n * β * (1-β) * n) := by ring_nf
    _ = (1/n) * (1 - γ) * √ (α * (1-α) * β * (1-β) * n ^ 2) := by ring_nf
    _ = (1/n) * (1 - γ) * √ (α * (1-α) * β * (1-β)) * √ (n ^ 2) := by
      rw [Real.sqrt_mul, ←mul_assoc]
      have h₆ : 0 ≤ α * (1-α) := by
        nlinarith
      have h₇ : 0 ≤ β * (1-β) := by
        nlinarith
      nlinarith
    _ = (1/n) * (1 - γ) *  √ (α * (1-α) * β * (1-β)) * n := by
      aesop
    _ = (1 - γ) * √ (α * (1-α) * β * (1-β)) := by
      field_simp





/-- Non-zero spectral expansion implies non-zero edge expansion-/
lemma SpectralImpliesEdgeExpansion {V E : Type*} [Fintype V] [DecidableEq V] [DecidableEq E]
    (G : MultiDiGraph V E) (hV: 0 < #G.vertices)
    (r : ℕ) (hr : 0 < r ∧ G.isRegularOfDegree r)  (γ : ℝ) (hγ : spectralExpander γ G) (hγ2 : 0 < γ):
    edgeExpander ((#G.vertices : ℝ) / 2) (γ / 2) r G := by

  -- establish some basic facts that are used later
  have hV2 : 0 ≠ #G.vertices := Ne.symm (Nat.ne_zero_of_lt hV)
  have hV3 : (#G.vertices : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (id (Ne.symm hV2))
  have hV4 : 0 < (#G.vertices : ℝ) := Nat.cast_pos'.mpr hV
  have hr2 : 0 < (r : ℝ) := Nat.cast_pos.2 hr.left

  -- use the expander mixing lemma in the format needed
  have h₁ : ∀ S ⊆ G.vertices, abs (((MultiDiGraph.eST G S (G.vertices \ S)) : ℝ)
        / (#(G.vertices)*(r : ℝ)) - ((#S : ℝ) / (#G.vertices : ℝ))
        * ((#(G.vertices \ S) : ℝ) / (#G.vertices : ℝ))) ≤
        (1 - γ) * Real.sqrt (((#S : ℝ) / (#G.vertices : ℝ))
        * (1- ((#S : ℝ) / (#G.vertices : ℝ)) ) * ((#(G.vertices \ S) : ℝ) / (#G.vertices : ℝ))
        * (1- ((#(G.vertices \ S) : ℝ) /(#G.vertices : ℝ)) )) := by
    have h11 : ∀ S ⊆ G.vertices, ∀ T ⊆ G.vertices, abs (((MultiDiGraph.eST G S T) : ℝ)
        / (#(G.vertices)*(r : ℝ)) - ((#S : ℝ) / (#G.vertices : ℝ))
        * ((#T : ℝ) / (#G.vertices : ℝ))) ≤
        (1 - γ) * Real.sqrt (((#S : ℝ) / (#G.vertices : ℝ))
        * (1- ((#S : ℝ) / (#G.vertices : ℝ)) ) * ((#T : ℝ) / (#G.vertices : ℝ))
        * (1- ((#T : ℝ) /(#G.vertices : ℝ)) )) :=
      fun S a T a_1 ↦ ExpanderMixingLemma G hV r hr γ hγ S a T a_1
    aesop

  -- unfold a bit of edgeExpander and specialise accordingly
  intro S hS
  specialize h₁ S hS

  -- a series of rewrites at `h₁` to obtain the required form
  have h₂ : (#(G.vertices \ S) : ℝ)  =  (#G.vertices : ℝ) - (#S : ℝ) := cast_card_sdiff hS
  rw [h₂] at h₁
  have h₃: ((#G.vertices : ℝ) - (#S : ℝ)) / (#G.vertices : ℝ)
      = 1 - (#S : ℝ) / (#G.vertices : ℝ) := by
    field_simp
  rw [h₃] at h₁
  have h₄: 1 - (1 - (#S : ℝ) / (#G.vertices : ℝ)) = (#S : ℝ) / (#G.vertices : ℝ) := by
    linarith
  rw [h₄] at h₁
  have h₅ : √((#S : ℝ) / (#G.vertices : ℝ) * (1 - (#S : ℝ) / (#G.vertices : ℝ)) *
      (1 - (#S : ℝ) / (#G.vertices : ℝ)) * ((#S : ℝ) / (#G.vertices : ℝ)))
      = (#S : ℝ) / (#G.vertices : ℝ) * (1 - (#S : ℝ) / (#G.vertices : ℝ)) := by
    -- untangling a squareroot over squared
    have : (#S : ℝ) / (#G.vertices : ℝ) * (1 - (#S : ℝ) / (#G.vertices : ℝ)) *
        (1 - (#S : ℝ) / (#G.vertices : ℝ)) * ((#S : ℝ) / (#G.vertices : ℝ)) =
        ((#S : ℝ) / (#G.vertices : ℝ) * ((#S : ℝ) / (#G.vertices : ℝ))) *
        (1 - (#S : ℝ) / (#G.vertices : ℝ)) * (1 - (#S : ℝ) / (#G.vertices : ℝ)) := by
      linarith
    rw [this]
    have : ((#S : ℝ) / (#G.vertices : ℝ) * ((#S : ℝ) / (#G.vertices : ℝ))) *
        (1 - (#S : ℝ) / (#G.vertices : ℝ)) * (1 - (#S : ℝ) / (#G.vertices : ℝ)) =
        ((#S : ℝ) / (#G.vertices : ℝ))^2 *
        (1 - (#S : ℝ) / (#G.vertices : ℝ))^2 := by linarith
    rw [this]
    have : ((#S : ℝ) / (#G.vertices : ℝ))^2 * (1 - (#S : ℝ) / (#G.vertices : ℝ))^2 =
        ((#S : ℝ) / (#G.vertices : ℝ) * (1 - (#S : ℝ) / (#G.vertices : ℝ)))^2 := by
      linarith
    rw [this]
    refine Real.sqrt_sq ?_
    have h₅a : (#S : ℝ) / (#G.vertices : ℝ) ≤ 1 := by
      have : #S ≤ #G.vertices := card_le_card hS
      have : (#S : ℝ) ≤ (#G.vertices : ℝ) := Nat.cast_le.mpr this
      exact (div_le_one₀ hV4).mpr this
    have : 0 ≤ 1 - (#S : ℝ) / (#G.vertices : ℝ) := by aesop
    positivity
  rw [h₅] at h₁

  -- some basic facts that are needed by later tactics
  have h₆ : (G.eST S (G.vertices \ S) : ℝ) / ((#G.vertices : ℝ) * r : ℝ) -
      (#S : ℝ) / (#G.vertices : ℝ) * (1 - (#S : ℝ) / (#G.vertices : ℝ)) ≥
      -(1 - γ) * ((#S : ℝ) / (#G.vertices : ℝ) * (1 - (#S : ℝ) / (#G.vertices : ℝ))) := by
    have : (G.eST S (G.vertices \ S) : ℝ) / ((#G.vertices : ℝ) * (r : ℝ))
        - (#S : ℝ) / (#G.vertices : ℝ) * (1 - (#S : ℝ) / (#G.vertices : ℝ)) ≥
        -((1 - γ) * ((#S : ℝ) / (#G.vertices : ℝ) * (1 - (#S : ℝ) / (#G.vertices : ℝ)))) :=
      helper_lemma3 ((G.eST S (G.vertices \ S) : ℝ) / ((#G.vertices : ℝ) * (r : ℝ)) -
        (#S : ℝ) / (#G.vertices : ℝ) * (1 - (#S : ℝ) / (#G.vertices : ℝ)))
        ((1 - γ) * ((#S : ℝ) / (#G.vertices : ℝ) * (1 - (#S : ℝ) / (#G.vertices : ℝ))))
        h₁
    linarith
  have h₇ : (G.eST S (G.vertices \ S) : ℝ) / ((#G.vertices : ℝ) * (r : ℝ)) ≥
      γ * ((#S : ℝ) / (#G.vertices : ℝ) * (1 - (#S : ℝ) / (#G.vertices : ℝ))) := by
    linarith

  -- the final steps to get the claimed result
  have h₈ : ¬ ((#G.vertices : ℝ) / 2 < (#S : ℝ)) →
      (γ / 2 * (#S : ℝ) * (r : ℝ) ≤ (#(G.cut S) : ℝ)) := by
    have : ¬ ((#G.vertices : ℝ) / 2 < (#S : ℝ)) ↔ ((#G.vertices : ℝ) / 2 ≥  (#S : ℝ)) := by
      aesop
    rw [this]
    intro _
    have h₈a : (#S : ℝ) / (#G.vertices : ℝ) ≤ 1/2 := by
      refine (div_le_div_iff₀ hV4 ?_).mpr ?_
      · linarith
      · linarith
    have : 0 ≤ (#S : ℝ) / (#G.vertices : ℝ) := by
      positivity
    have h₈b : ((#S : ℝ) / (#G.vertices : ℝ) * (1 - (#S : ℝ) / (#G.vertices : ℝ))) ≥
        ((#S : ℝ) / (#G.vertices : ℝ)) / 2 := helper_lemma_4 ((#S : ℝ) / (#G.vertices : ℝ)) this h₈a
    have h₈c : γ * ((#S : ℝ) / (#G.vertices : ℝ) * (1 - (#S : ℝ) / (#G.vertices : ℝ))) ≥
        γ * ((#S : ℝ) / ( (#G.vertices : ℝ)) / 2) := by
      have : 0 ≤ γ := le_of_lt hγ2
      exact helper_lemma5 γ ((#S : ℝ) / (#G.vertices : ℝ) * (1 - (#S : ℝ) / (#G.vertices : ℝ)))
          (((#S : ℝ) / ( (#G.vertices : ℝ))) / 2) this h₈b
    have : γ * ((#S : ℝ) / (#G.vertices : ℝ) / 2) = γ * (#S : ℝ) / (2 * (#G.vertices : ℝ)) := by
      field_simp
      -- have : 2 * (#G.vertices : ℝ) = (#G.vertices : ℝ) * 2 := by linarith
      -- exact mul_eq_mul_left_iff.mp (congrArg (HMul.hMul (γ * (#S : ℝ))) this)
    rw [this] at h₈c
    have h₃ : (G.eST S (G.vertices \ S) : ℝ) / ((#G.vertices : ℝ) * (r : ℝ)) ≥
        γ * (#S : ℝ) / (2 * (#G.vertices : ℝ)) :=
      Preorder.le_trans (γ * (#S : ℝ) / (2 * (#G.vertices : ℝ)))
        (γ * ((#S : ℝ) / (#G.vertices : ℝ) * (1 - (#S : ℝ) / (#G.vertices : ℝ))))
        ((G.eST S (G.vertices \ S) : ℝ) / ((#G.vertices) * r : ℝ)) h₈c h₇
    have : (G.eST S (G.vertices \ S) : ℝ) ≥ (r : ℝ) * γ * (#S : ℝ) / 2 := by
      have : 0 < (#G.vertices : ℝ) * (r : ℝ) := mul_pos hV4 hr2
      have h₁ : (G.eST S (G.vertices \ S) : ℝ)  ≥
          γ * (#S : ℝ) / (2 * (#G.vertices : ℝ)) * (#G.vertices : ℝ) * (r : ℝ) := by
        have : (G.eST S (G.vertices \ S) : ℝ) ≥
            γ * (#S : ℝ) / (2 * (#G.vertices : ℝ)) * ((#G.vertices : ℝ) * r : ℝ) :=
          helper_lemma6 ((#G.vertices : ℝ) * (r : ℝ)) (G.eST S (G.vertices \ S) : ℝ)
              (γ * (#S : ℝ) / (2 * (#G.vertices : ℝ))) this h₃
        linarith
      have : γ * (#S : ℝ) / (2 * (#G.vertices : ℝ )) * (#G.vertices : ℝ) * (r : ℝ) =
          γ * (#S : ℝ) / 2 * (r : ℝ) := by
            field_simp
            --linarith
      rw [this] at h₁
      linarith
    have : (G.eST S (G.vertices \ S) : ℝ) = (#(G.cut S) : ℝ) := by
      unfold MultiDiGraph.eST MultiDiGraph.cut
      rfl
    rw [←this]
    linarith
  exact Decidable.or_iff_not_imp_left.mpr h₈

--#lint
