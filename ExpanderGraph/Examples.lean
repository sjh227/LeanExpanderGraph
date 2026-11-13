/-
Copyright (c) 2025-2026 Steven Herbert. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Steven Herbert
-/
import Mathlib

import ExpanderGraph.CollisionProb
import ExpanderGraph.MultiDiGraph
import ExpanderGraph.ProbabilityVector
import ExpanderGraph.ExpansionDefs

/-!
# Examples

This file contains counter-examples showing that two graphs, namely `K₂ ⊕ K₂` and `K₂₂` have
spectral expansion equal to zero, but non-zero vertex expansion

When cleaning up the file in November 2026, it turned out that a minor change to how the graphs are
defined was needed, and the original definitions are left below (commented out) to preserve the full
history, in case this is every useful.

-/

open MultiDiGraphSpace
open ProbabilityVector
open Finset
open ExpansionDefs
open Matrix
open Classical


-- # First example with `K2 ⊕ K2`

section

/-- vertices of `K2 ⊕ K2`-/
-- inductive K2K2V : Type
--   | v1 : K2K2V
--   | v2 : K2K2V
--   | v3 : K2K2V
--   | v4 : K2K2V
--    deriving Fintype, DecidableEq

inductive K2K2V : Type
  | v1
  | v2
  | v3
  | v4
  deriving DecidableEq

instance : Fintype K2K2V where
  elems := {K2K2V.v1, K2K2V.v2, K2K2V.v3, K2K2V.v4}
  complete := by
    intro x
    cases x <;> simp


/-- edges of `K2 ⊕ K2`-/
inductive K2K2E : Type
  | e1a
  | e1b
  | e2a
  | e2b
  deriving DecidableEq

instance : Fintype K2K2E where
  elems := {K2K2E.e1a, K2K2E.e1b, K2K2E.e2a, K2K2E.e2b}
  complete := by
    intro x
    cases x <;> simp

-- /-- edges of `K2 ⊕ K2`-/
-- inductive K2K2E : Type
--   | e1a : K2K2E
--   | e1b : K2K2E
--   | e2a : K2K2E
--   | e2b : K2K2E
--   deriving Fintype, DecidableEq

open K2K2V K2K2E

/--Build `K2 ⊕ K2`-/
def K2K2 : MultiDiGraph K2K2V K2K2E where
  vertices := Finset.mk [v1, v2, v3, v4] (by simp)
  edges := Finset.mk [e1a, e1b, e2a, e2b] (by simp)
  edgeMap := fun
    | e1a => (v1, v2)
    | e1b => (v2, v1)
    | e2a => (v3, v4)
    | e2b => (v4, v3)
  edgesValid := by
    simp

-- # Now some lemmas about K2 ⊕ K2

lemma K2K2_neighbour_of_set_card_one_has_card_one (s : Finset K2K2V) (hs : #s = 1) :
    #(K2K2.neighbourhoodOfSet s) = 1 := by
  obtain ⟨v, rfl⟩ := Finset.card_eq_one.mp hs
  simp only [MultiDiGraph.neighbourhoodOfSet]
  fin_cases v
  all_goals
  unfold MultiDiGraph.neighbourhood
  simp_all only [card_singleton, singleton_biUnion]
  rfl

lemma K2K2_edges_of_cut_card_one (s : Finset K2K2V) (hs : #s = 1) :
    #({e ∈ K2K2.edges | (K2K2.3 e).1 ∈ s ∧
    (K2K2.3 e).2 ∈ K2K2.vertices ∧ (K2K2.3 e).2 ∉ s}) = 1 := by
  obtain ⟨e, rfl⟩ := Finset.card_eq_one.mp hs
  simp only [mem_singleton]
  fin_cases e
  all_goals
  aesop

lemma K2K2_zero_le_vertices_card : 0 < #K2K2.vertices := by
  exact Nat.zero_lt_succ [v2, v3, v4].length

lemma K2K2_regular : K2K2.regular := by
  unfold MultiDiGraph.regular MultiDiGraph.isRegularOfDegree
  use 1
  intro v hv
  fin_cases v
  all_goals
  aesop

lemma K2K2_regular' : K2K2.isRegularOfDegree 1 := by
  unfold MultiDiGraph.isRegularOfDegree
  intro v hv
  constructor
  · fin_cases v
    all_goals
    aesop
  · fin_cases v
    all_goals
    aesop


lemma sum_over_vertices (f : K2K2V → ℝ) :
    ∑ v, f v = f v1 + f v2 + f v3 + f v4 := by
  have : ∑ v, f v = ∑ v ∈ {v1, v2}, f v + ∑ v ∉ {v1, v2}, f v := by
    exact Eq.symm (sum_add_sum_compl {v1, v2} f)
  rw [this]
  have : ∑ v ∈ {v1, v2}, f v = f v1 + f v2 := by aesop
  rw [this]
  have : ∑ v ∈ {v1, v2}ᶜ, f v =  ∑ v ∈ {v3, v4}, f v := by exact rfl
  rw [this]
  have : ∑ v ∈ {v3, v4}, f v = f v3 + f v4 := by aesop
  rw [this]
  linarith

-- # Now the 16 elements of the randomwalk matrix evaluated


lemma if_stochastic_matrix_row_has_element_one_rest_are_zero (v : K2K2V)
    (va : K2K2V) (hva : va ∈ K2K2.vertices)
    (vb : K2K2V)
    (hvb : K2K2.randomWalkMatrix v vb = 1.0)
    (hv : va ≠ vb): K2K2.randomWalkMatrix v va = (0 : ℝ) := by
  have h₀ : ∀ u, 0 ≤ K2K2.randomWalkMatrix v u :=
    fun u ↦ MultiDiGraph.randomWalkMatrixNonNegative1 K2K2 v u
  have h₀a : ∀ u ∈ K2K2.vertices \ {vb}, 0 ≤ K2K2.randomWalkMatrix v u := by
    aesop
  have h₁ : ∑ u, K2K2.randomWalkMatrix v u = 1 :=
    MultiDiGraph.randomWalkMatrixSumtoOne1 K2K2 v
  have : ∑ u, K2K2.randomWalkMatrix v u = ∑ u ∈ K2K2.vertices, K2K2.randomWalkMatrix v u := rfl
  rw [this] at h₁
  have : ∑ u ∈ K2K2.vertices, K2K2.randomWalkMatrix v u =
      ∑ u ∈ {vb}, K2K2.randomWalkMatrix v u + ∑ u ∈ {vb}ᶜ, K2K2.randomWalkMatrix v u :=
    Eq.symm (sum_add_sum_compl {vb} (K2K2.randomWalkMatrix v))
  rw [this] at h₁
  have : ∑ u ∈ {vb}, K2K2.randomWalkMatrix v u = 1.0 := by
    aesop
  rw [this] at h₁
  have : {vb}ᶜ = K2K2.vertices \ {vb} := rfl
  have h₃ : ∑ u ∈ {vb}ᶜ, K2K2.randomWalkMatrix v u = (0 : ℝ) := by linarith
  have h₃a : ∑ u ∈ K2K2.vertices \ {vb}, K2K2.randomWalkMatrix v u = (0 : ℝ) := by
    exact h₃
  have h₄ : ∀ u ∈ K2K2.vertices \ {vb}, K2K2.randomWalkMatrix v u = (0 : ℝ) := by
    exact (Finset.sum_eq_zero_iff_of_nonneg h₀a).mp h₃a
  rw [←this] at h₄
  aesop


-- prove that `K2K2_v2_v1 = 1` then use the lemma to obtain zero for the rest of the row
lemma K2K2_v2_v1 : K2K2.randomWalkMatrix v2 v1 = 1.0 := by
  unfold MultiDiGraph.randomWalkMatrix
  simp only [of_apply, reduceCtorEq, ↓reduceIte]
  have : ∑ v, (K2K2.adjacencyMatrix v2 v : ℝ) =
      ∑ v ∈ K2K2.vertices, (K2K2.adjacencyMatrix v2 v : ℝ) := rfl
  rw [this]
  have : ∑ v ∈ K2K2.vertices, (K2K2.adjacencyMatrix v2 v : ℝ) = 1 := by
    have : ∑ v ∈ K2K2.vertices, (K2K2.adjacencyMatrix v2 v : ℝ) =
        (K2K2.adjacencyMatrix v2 v1 : ℝ) +
        (K2K2.adjacencyMatrix v2 v2 : ℝ) +
        (K2K2.adjacencyMatrix v2 v3 : ℝ) +
        (K2K2.adjacencyMatrix v2 v4 : ℝ) := by
      exact sum_over_vertices fun v ↦ (K2K2.adjacencyMatrix v2 v : ℝ)
    rw [this]
    have : (K2K2.adjacencyMatrix v2 v1 : ℝ) = 1 := Nat.cast_eq_one.mpr rfl
    rw [this]
    have : (K2K2.adjacencyMatrix v2 v2 : ℝ) = 0 :=
      (Lean.Grind.IsCharP.natCast_eq_zero_iff 0 (K2K2.adjacencyMatrix v2 v2)).mpr rfl
    rw [this]
    have : (K2K2.adjacencyMatrix v2 v3 : ℝ) = 0 :=
      (Lean.Grind.IsCharP.natCast_eq_zero_iff 0 (K2K2.adjacencyMatrix v2 v3)).mpr rfl
    rw [this]
    have : (K2K2.adjacencyMatrix v2 v4 : ℝ) = 0 :=
      (Lean.Grind.IsCharP.natCast_eq_zero_iff 0 (K2K2.adjacencyMatrix v2 v4)).mpr rfl
    rw [this]
    linarith
  rw [this]
  simp only [one_ne_zero, ↓reduceIte, div_one]
  have : K2K2.adjacencyMatrix v2 v1 = 1 := rfl
  rw [this]
  norm_cast
  linarith

lemma K2K2_v2_v2 : K2K2.randomWalkMatrix v2 v2 = (0 : ℝ) := by
  have : v2 ≠ v1 := not_eq_of_beq_eq_false rfl
  have hv2 : v2 ∈ K2K2.vertices := by exact insert_eq_self.mp rfl
  exact if_stochastic_matrix_row_has_element_one_rest_are_zero v2 v2 hv2 v1 K2K2_v2_v1 this

lemma K2K2_v2_v3 : K2K2.randomWalkMatrix v2 v3 = (0 : ℝ) := by
  have : v3 ≠ v1 := not_eq_of_beq_eq_false rfl
  have hv3 : v3 ∈ K2K2.vertices := by exact insert_eq_self.mp rfl
  exact if_stochastic_matrix_row_has_element_one_rest_are_zero v2 v3 hv3 v1 K2K2_v2_v1 this

lemma K2K2_v2_v4 : K2K2.randomWalkMatrix v2 v4 = (0 : ℝ) := by
  have : v4 ≠ v1 := not_eq_of_beq_eq_false rfl
  have hv4 : v4 ∈ K2K2.vertices := by exact insert_eq_self.mp rfl
  exact if_stochastic_matrix_row_has_element_one_rest_are_zero v2 v4 hv4 v1 K2K2_v2_v1 this




-- prove that `K2K2_v1_v2 = 1` then use the lemma to obtain zero for the rest of the row
lemma K2K2_v1_v2 : K2K2.randomWalkMatrix v1 v2 = 1.0 := by
  unfold MultiDiGraph.randomWalkMatrix
  simp only [of_apply, reduceCtorEq, ↓reduceIte]
  have : ∑ v, (K2K2.adjacencyMatrix v1 v : ℝ) =
      ∑ v ∈ K2K2.vertices, (K2K2.adjacencyMatrix v1 v : ℝ) := rfl
  rw [this]
  have : ∑ v ∈ K2K2.vertices, (K2K2.adjacencyMatrix v1 v : ℝ) = 1 := by
    have : ∑ v ∈ K2K2.vertices, (K2K2.adjacencyMatrix v1 v : ℝ) =
        (K2K2.adjacencyMatrix v1 v1 : ℝ) +
        (K2K2.adjacencyMatrix v1 v2 : ℝ) +
        (K2K2.adjacencyMatrix v1 v3 : ℝ) +
        (K2K2.adjacencyMatrix v1 v4 : ℝ) := by
      exact sum_over_vertices fun v ↦ (K2K2.adjacencyMatrix v1 v : ℝ)
    rw [this]
    have : (K2K2.adjacencyMatrix v1 v2 : ℝ) = 1 := Nat.cast_eq_one.mpr rfl
    rw [this]
    have : (K2K2.adjacencyMatrix v1 v1 : ℝ) = 0 :=
      (Lean.Grind.IsCharP.natCast_eq_zero_iff 0 (K2K2.adjacencyMatrix v1 v1)).mpr rfl
    rw [this]
    have : (K2K2.adjacencyMatrix v1 v3 : ℝ) = 0 :=
      (Lean.Grind.IsCharP.natCast_eq_zero_iff 0 (K2K2.adjacencyMatrix v1 v3)).mpr rfl
    rw [this]
    have : (K2K2.adjacencyMatrix v1 v4 : ℝ) = 0 :=
      (Lean.Grind.IsCharP.natCast_eq_zero_iff 0 (K2K2.adjacencyMatrix v1 v4)).mpr rfl
    rw [this]
    linarith
  rw [this]
  simp only [one_ne_zero, ↓reduceIte, div_one]
  have : K2K2.adjacencyMatrix v1 v2 = 1 := rfl
  rw [this]
  norm_cast
  linarith

lemma K2K2_v1_v1 : K2K2.randomWalkMatrix v1 v1 = (0 : ℝ) := by
  have : v1 ≠ v2 := not_eq_of_beq_eq_false rfl
  have hv1 : v1 ∈ K2K2.vertices := by exact insert_eq_self.mp rfl
  exact if_stochastic_matrix_row_has_element_one_rest_are_zero v1 v1 hv1 v2 K2K2_v1_v2 this

lemma K2K2_v1_v3 : K2K2.randomWalkMatrix v1 v3 = (0 : ℝ) := by
  have : v3 ≠ v2 := not_eq_of_beq_eq_false rfl
  have hv3 : v3 ∈ K2K2.vertices := by exact insert_eq_self.mp rfl
  exact if_stochastic_matrix_row_has_element_one_rest_are_zero v1 v3 hv3 v2 K2K2_v1_v2 this

lemma K2K2_v1_v4 : K2K2.randomWalkMatrix v1 v4 = (0 : ℝ) := by
  have : v4 ≠ v2 := not_eq_of_beq_eq_false rfl
  have hv4 : v4 ∈ K2K2.vertices := by exact insert_eq_self.mp rfl
  exact if_stochastic_matrix_row_has_element_one_rest_are_zero v1 v4 hv4 v2 K2K2_v1_v2 this


-- prove that `K2K2_v3_v4 = 1` then use the lemma to obtain zero for the rest of the row
lemma K2K2_v3_v4 : K2K2.randomWalkMatrix v3 v4 = 1.0 := by
  unfold MultiDiGraph.randomWalkMatrix
  simp only [of_apply, reduceCtorEq, ↓reduceIte]
  have : ∑ v, (K2K2.adjacencyMatrix v3 v : ℝ) =
      ∑ v ∈ K2K2.vertices, (K2K2.adjacencyMatrix v3 v : ℝ) := rfl
  rw [this]
  have : ∑ v ∈ K2K2.vertices, (K2K2.adjacencyMatrix v3 v : ℝ) = 1 := by
    have : ∑ v ∈ K2K2.vertices, (K2K2.adjacencyMatrix v3 v : ℝ) =
        (K2K2.adjacencyMatrix v3 v1 : ℝ) +
        (K2K2.adjacencyMatrix v3 v2 : ℝ) +
        (K2K2.adjacencyMatrix v3 v3 : ℝ) +
        (K2K2.adjacencyMatrix v3 v4 : ℝ) := by
      exact sum_over_vertices fun v ↦ (K2K2.adjacencyMatrix v3 v : ℝ)
    rw [this]
    have : (K2K2.adjacencyMatrix v3 v4 : ℝ) = 1 := Nat.cast_eq_one.mpr rfl
    rw [this]
    have : (K2K2.adjacencyMatrix v3 v1 : ℝ) = 0 :=
      (Lean.Grind.IsCharP.natCast_eq_zero_iff 0 (K2K2.adjacencyMatrix v3 v1)).mpr rfl
    rw [this]
    have : (K2K2.adjacencyMatrix v3 v2 : ℝ) = 0 :=
      (Lean.Grind.IsCharP.natCast_eq_zero_iff 0 (K2K2.adjacencyMatrix v3 v2)).mpr rfl
    rw [this]
    have : (K2K2.adjacencyMatrix v3 v3 : ℝ) = 0 :=
      (Lean.Grind.IsCharP.natCast_eq_zero_iff 0 (K2K2.adjacencyMatrix v3 v3)).mpr rfl
    rw [this]
    linarith
  rw [this]
  simp only [one_ne_zero, ↓reduceIte, div_one]
  have : K2K2.adjacencyMatrix v3 v4 = 1 := rfl
  rw [this]
  norm_cast
  linarith

lemma K2K2_v3_v1 : K2K2.randomWalkMatrix v3 v1 = (0 : ℝ) := by
  have : v1 ≠ v4 := not_eq_of_beq_eq_false rfl
  have hv1 : v1 ∈ K2K2.vertices := by exact insert_eq_self.mp rfl
  exact if_stochastic_matrix_row_has_element_one_rest_are_zero v3 v1 hv1 v4 K2K2_v3_v4 this

lemma K2K2_v3_v2 : K2K2.randomWalkMatrix v3 v2 = (0 : ℝ) := by
  have : v2 ≠ v4 := not_eq_of_beq_eq_false rfl
  have hv2 : v2 ∈ K2K2.vertices := by exact insert_eq_self.mp rfl
  exact if_stochastic_matrix_row_has_element_one_rest_are_zero v3 v2 hv2 v4 K2K2_v3_v4 this

lemma K2K2_v3_v3 : K2K2.randomWalkMatrix v3 v3 = (0 : ℝ) := by
  have : v3 ≠ v4 := not_eq_of_beq_eq_false rfl
  have hv3 : v3 ∈ K2K2.vertices := by exact insert_eq_self.mp rfl
  exact if_stochastic_matrix_row_has_element_one_rest_are_zero v3 v3 hv3 v4 K2K2_v3_v4 this


-- prove that `K2K2_v4_v3 = 1` then use the lemma to obtain zero for the rest of the row
lemma K2K2_v4_v3 : K2K2.randomWalkMatrix v4 v3 = 1.0 := by
  unfold MultiDiGraph.randomWalkMatrix
  simp only [of_apply, reduceCtorEq, ↓reduceIte]
  have : ∑ v, (K2K2.adjacencyMatrix v4 v : ℝ) =
      ∑ v ∈ K2K2.vertices, (K2K2.adjacencyMatrix v4 v : ℝ) := rfl
  rw [this]
  have : ∑ v ∈ K2K2.vertices, (K2K2.adjacencyMatrix v4 v : ℝ) = 1 := by
    have : ∑ v ∈ K2K2.vertices, (K2K2.adjacencyMatrix v4 v : ℝ) =
        (K2K2.adjacencyMatrix v4 v1 : ℝ) +
        (K2K2.adjacencyMatrix v4 v2 : ℝ) +
        (K2K2.adjacencyMatrix v4 v3 : ℝ) +
        (K2K2.adjacencyMatrix v4 v4 : ℝ) := by
      exact sum_over_vertices fun v ↦ (K2K2.adjacencyMatrix v4 v : ℝ)
    rw [this]
    have : (K2K2.adjacencyMatrix v4 v3 : ℝ) = 1 := Nat.cast_eq_one.mpr rfl
    rw [this]
    have : (K2K2.adjacencyMatrix v4 v1 : ℝ) = 0 :=
      (Lean.Grind.IsCharP.natCast_eq_zero_iff 0 (K2K2.adjacencyMatrix v4 v1)).mpr rfl
    rw [this]
    have : (K2K2.adjacencyMatrix v4 v2 : ℝ) = 0 :=
      (Lean.Grind.IsCharP.natCast_eq_zero_iff 0 (K2K2.adjacencyMatrix v4 v2)).mpr rfl
    rw [this]
    have : (K2K2.adjacencyMatrix v4 v4 : ℝ) = 0 :=
      (Lean.Grind.IsCharP.natCast_eq_zero_iff 0 (K2K2.adjacencyMatrix v4 v4)).mpr rfl
    rw [this]
    linarith
  rw [this]
  simp only [one_ne_zero, ↓reduceIte, div_one]
  have : K2K2.adjacencyMatrix v4 v3 = 1 := rfl
  rw [this]
  norm_cast
  linarith

lemma K2K2_v4_v1 : K2K2.randomWalkMatrix v4 v1 = (0 : ℝ) := by
  have : v1 ≠ v3 := not_eq_of_beq_eq_false rfl
  have hv1 : v1 ∈ K2K2.vertices := by exact insert_eq_self.mp rfl
  exact if_stochastic_matrix_row_has_element_one_rest_are_zero v4 v1 hv1 v3 K2K2_v4_v3 this

lemma K2K2_v4_v2 : K2K2.randomWalkMatrix v4 v2 = (0 : ℝ) := by
  have : v2 ≠ v3 := not_eq_of_beq_eq_false rfl
  have hv2 : v2 ∈ K2K2.vertices := by exact insert_eq_self.mp rfl
  exact if_stochastic_matrix_row_has_element_one_rest_are_zero v4 v2 hv2 v3 K2K2_v4_v3 this

lemma K2K2_v4_v4 : K2K2.randomWalkMatrix v4 v4 = (0 : ℝ) := by
  have : v4 ≠ v3 := not_eq_of_beq_eq_false rfl
  have hv4 : v4 ∈ K2K2.vertices := by exact insert_eq_self.mp rfl
  exact if_stochastic_matrix_row_has_element_one_rest_are_zero v4 v4 hv4 v3 K2K2_v4_v3 this



-- # Now a non-uniform stationary distribution used to prove zero spectral gap

/-- A distribution that is a fixed point of the random walk matrix of
`K₂ ⊕ k₂`, but is not the uniform distribution -/
def π : K2K2V → ℝ
  | v1 => 0.5
  | v2 => 0.5
  | v3 => 0.0
  | v4 => 0.0

lemma π_is_stationary_dist : π ᵥ* K2K2.randomWalkMatrix = π := by
  have : ∀ i, (π ᵥ* K2K2.randomWalkMatrix) i = π i := by
    intro i
    have h₀: ∀i, ((π ᵥ* K2K2.randomWalkMatrix) i) = ∑ j, π j * K2K2.randomWalkMatrix j i := by
      exact fun i ↦ rfl
    rw [h₀]
    fin_cases i
    · have : ∑ j, π j * K2K2.randomWalkMatrix j v1 =
          π v1 * K2K2.randomWalkMatrix v1 v1 +
          π v2 * K2K2.randomWalkMatrix v2 v1 +
          π v3 * K2K2.randomWalkMatrix v3 v1 +
          π v4 * K2K2.randomWalkMatrix v4 v1 :=
        sum_over_vertices fun v ↦ π v * K2K2.randomWalkMatrix v v1
      rw [this]
      have : π v1 * K2K2.randomWalkMatrix v1 v1 = 0.0 := by
        rw [K2K2_v1_v1]
        linarith
      rw [this]
      have : π v2 * K2K2.randomWalkMatrix v2 v1 = 0.5 := by
        rw [K2K2_v2_v1]
        have : π v2 = 0.5 := rfl
        rw [this]
        linarith
      rw [this]
      have : π v3 * K2K2.randomWalkMatrix v3 v1 = 0.0 := by
        rw [K2K2_v3_v1]
        linarith
      rw [this]
      have : π v4 * K2K2.randomWalkMatrix v4 v1 = 0.0 := by
        rw [K2K2_v4_v1]
        linarith
      rw [this]
      have : π v1 = 0.5 := rfl
      rw [this]
      linarith
    · have : ∑ j, π j * K2K2.randomWalkMatrix j v2 =
          π v1 * K2K2.randomWalkMatrix v1 v2 +
          π v2 * K2K2.randomWalkMatrix v2 v2 +
          π v3 * K2K2.randomWalkMatrix v3 v2 +
          π v4 * K2K2.randomWalkMatrix v4 v2 :=
        sum_over_vertices fun v ↦ π v * K2K2.randomWalkMatrix v v2
      rw [this]
      have : π v1 * K2K2.randomWalkMatrix v1 v2 = 0.5 := by
        rw [K2K2_v1_v2]
        have : π v1 = 0.5 := rfl
        rw [this]
        linarith
      rw [this]
      have : π v2 * K2K2.randomWalkMatrix v2 v2 = 0.0 := by
        rw [K2K2_v2_v2]
        linarith
      rw [this]
      have : π v3 * K2K2.randomWalkMatrix v3 v2 = 0.0 := by
        rw [K2K2_v3_v2]
        linarith
      rw [this]
      have : π v4 * K2K2.randomWalkMatrix v4 v2 = 0.0 := by
        rw [K2K2_v4_v2]
        linarith
      rw [this]
      have : π v2 = 0.5 := rfl
      rw [this]
      linarith
    · have : ∑ j, π j * K2K2.randomWalkMatrix j v3 =
          π v1 * K2K2.randomWalkMatrix v1 v3 +
          π v2 * K2K2.randomWalkMatrix v2 v3 +
          π v3 * K2K2.randomWalkMatrix v3 v3 +
          π v4 * K2K2.randomWalkMatrix v4 v3 :=
        sum_over_vertices fun v ↦ π v * K2K2.randomWalkMatrix v v3
      rw [this]
      have : π v1 * K2K2.randomWalkMatrix v1 v3 = 0.0 := by
        rw [K2K2_v1_v3]
        linarith
      rw [this]
      have : π v2 * K2K2.randomWalkMatrix v2 v3 = 0.0 := by
        rw [K2K2_v2_v3]
        linarith
      rw [this]
      have : π v3 * K2K2.randomWalkMatrix v3 v3 = 0.0 := by
        rw [K2K2_v3_v3]
        linarith
      rw [this]
      have : π v4 * K2K2.randomWalkMatrix v4 v3 = 0.0 := by
        have : π v4 = 0.0 := rfl
        rw [this]
        linarith
      rw [this]
      have : π v3 = 0.0 := rfl
      rw [this]
      linarith
    · have : ∑ j, π j * K2K2.randomWalkMatrix j v4 =
          π v1 * K2K2.randomWalkMatrix v1 v4 +
          π v2 * K2K2.randomWalkMatrix v2 v4 +
          π v3 * K2K2.randomWalkMatrix v3 v4 +
          π v4 * K2K2.randomWalkMatrix v4 v4 :=
        sum_over_vertices fun v ↦ π v * K2K2.randomWalkMatrix v v4
      rw [this]
      have : π v1 * K2K2.randomWalkMatrix v1 v4 = 0.0 := by
        rw [K2K2_v1_v4]
        linarith
      rw [this]
      have : π v2 * K2K2.randomWalkMatrix v2 v4 = 0.0 := by
        rw [K2K2_v2_v4]
        linarith
      rw [this]
      have : π v3 * K2K2.randomWalkMatrix v3 v4 = 0.0 := by
        have : π v3 = 0.0 := rfl
        rw [this]
        linarith
      rw [this]
      have hv4 : π v4 = 0.0 := rfl
      have : π v4 * K2K2.randomWalkMatrix v4 v4 = 0.0 := by
        rw [hv4]
        linarith
      rw [this, hv4]
      linarith
  aesop



lemma K2K2_SpectralGap_eq_zero : K2K2.SpectralGap = 0 := by
  have h₀ : 0 ≤ K2K2.SpectralGap := by
    have : 1 ≠ 0 := by aesop
    exact K2K2.SpectralGap_geq_zero K2K2_zero_le_vertices_card this K2K2_regular'
  have h₁ : K2K2.SpectralGap ≤ 0 := by
    unfold MultiDiGraph.SpectralGap
    let u := UniformDist K2K2.vertices
    let M := K2K2.randomWalkMatrix
    let L := K2K2.vertices
    have : sSup {y |∃ p, IsProbVector p L ∧ p ≠ u ∧ y =
        √(L2normSQ (p ᵥ* M - u) L) / √(L2normSQ (p - u) L)} ≥ 1 := by
      -- first we show that `π` is a probability vector over `K2K2.vertices`
      have hπ₁ : IsProbVector π L := by
        unfold IsProbVector
        constructor
        · have : ∑ i ∈ L, π i = ∑ i ∈ {v1, v2}, π i + ∑ i ∉ {v1, v2}, π i := by
            rw [←sum_union]
            · rfl
            · exact disjoint_sdiff
          rw [this]
          have : ∑ i ∉ {v1, v2}, π i = 0 := by
            have : ∑ i ∉ {v1, v2}, π i = ∑ i ∈ {v3, v4}, π i := by
              have h₀ : L \ {v1, v2} = {v3, v4} := by aesop
              have : {v1, v2}ᶜ = L \ {v1, v2} := by aesop
              rw [←this] at h₀
              rw [h₀]
            rw [this]
            have : ∑ i ∈ {v3, v4}, π i = π v3 + π v4 := by
              aesop
            rw [this]
            have : π v3 = 0 := by
              unfold π
              linarith
            rw [this]
            have : π v4 = 0 := by
              unfold π
              linarith
            rw [this]
            linarith
          rw [this]
          have : ∑ i ∈ {v1, v2}, π i = 1 := by
            have : ∑ i ∈ {v1, v2}, π i = π v1 + π v2 := by aesop
            rw [this]
            have : π v1 = 0.5 := by
              unfold π
              linarith
            rw [this]
            have : π v2 = 0.5 := by
              unfold π
              linarith
            rw [this]
            linarith
          rw [this]
          linarith
        · constructor
          · unfold π
            norm_num
            aesop
          · unfold π
            intro i hi
            have hv₁ : v1 ∈ L := insert_eq_self.mp rfl
            have hv₂ : v2 ∈ L := insert_eq_self.mp rfl
            have h₁ : i ≠ v1 := by aesop
            have h₂ : i ≠ v2 := by aesop
            simp_all only [ne_eq, L]
            split
            next x => simp_all only
            next x => simp_all only
            next x =>
              simp_all only [reduceCtorEq, not_false_eq_true]
              linarith
            next x =>
              simp_all only [reduceCtorEq, not_false_eq_true]
              linarith
      -- Now show that `π` is not the uniform distribution
      have hπ₂ : π ≠ UniformDist K2K2.vertices := by
        unfold π UniformDist
        have : #K2K2.vertices = 4 := by aesop
        have : 1 / (#K2K2.vertices : ℝ) = 0.25 := by
          norm_num
          aesop
        rw [this]
        have h₁ : v1 ∈ K2K2.vertices := by
          exact insert_eq_self.mp rfl
        intro h_eq
        have val := congr_fun h_eq v1
        simp [h₁] at val
        norm_num at val

      -- Now show that `π M = π`
      have hπ₃ : π ᵥ* K2K2.randomWalkMatrix = π := π_is_stationary_dist

      have hπ₄ : ∃ i ∈ K2K2.vertices, (π - UniformDist K2K2.vertices) i ≠ 0 := by
      -- because they are not equal
        have h₁ : v1 ∈ K2K2.vertices := by
          exact insert_eq_self.mp rfl
        have : UniformDist K2K2.vertices v1 ≠ π v1 := by
          have : UniformDist K2K2.vertices v1 = 0.25 := by
            unfold UniformDist
            have : #K2K2.vertices = 4 := by aesop
            have : 1 / (#K2K2.vertices : ℝ) = 0.25 := by
              norm_num
              aesop
            rw [this]
            aesop
          rw [this]
          have : π v1 = 0.5 := rfl
          rw [this]
          linarith
        have : π v1 - UniformDist K2K2.vertices v1 ≠ 0 :=
          sub_ne_zero_of_ne (id (Ne.symm this))
        aesop

      -- put all of the above pieces together to obtain the result
      have : 0 < L2normSQ (π - u) L := L2normSQ_positive (π - u) L hπ₄
      have h₁ : √(L2normSQ (π ᵥ* M - u) L) / √(L2normSQ (π - u) L) = 1 := by
        rw [hπ₃]
        field_simp
      apply le_csSup
      · have : ∀ x ∈ {y | ∃ p, IsProbVector p L ∧ p ≠ u ∧ y =
            √(L2normSQ (p ᵥ* M - u) L)
            / √(L2normSQ (p - u) L)}, x ≤ 1 := by
          have hV : 0 < #K2K2.vertices := by exact K2K2_zero_le_vertices_card
          have : 1 ≠ 0 := by aesop
          exact K2K2.bound_on_L2normSQ' hV this K2K2_regular'
        use 1
        exact this
      · aesop
    linarith
  linarith


-- # Finally, the first example

example : (vertexExpander (1 : ℝ) (1 : ℝ) K2K2) ∧ (edgeExpander (1 : ℝ) (1 : ℝ) (1 : ℕ) K2K2)
    ∧ ∀ γ : ℝ, (γ ∈ Set.Ioc 0 1) → ¬ (spectralExpander γ K2K2) := by
  constructor
  · unfold vertexExpander
    intro s hs
    by_cases h₀ : #s = 0
    · aesop
    · by_cases h₁ : #s = 1
      · have :  1 * (#s : ℝ) = 1 := by aesop
        rw [this]
        have : #(K2K2.neighbourhoodOfSet s) = 1 := by
          exact K2K2_neighbour_of_set_card_one_has_card_one s h₁
        aesop
      · have : 1 < #s := by
          have : 0 ≤ #s := Nat.zero_le #s
          omega
        aesop
  · constructor
    · unfold edgeExpander MultiDiGraph.cut
      simp only [Nat.one_lt_cast, one_mul, Nat.cast_one, mul_one, mem_sdiff, Nat.cast_le]
      intro s hs
      by_cases h₀ : #s = 0
      · aesop
      · by_cases h₁ : #s = 1
        · rw [h₁]
          have : #({e ∈ K2K2.edges | (K2K2.3 e).1 ∈ s ∧
              (K2K2.3 e).2 ∈ K2K2.vertices ∧ (K2K2.3 e).2 ∉ s}) = 1 :=
            K2K2_edges_of_cut_card_one s h₁
          rw [this]
          exact Nat.lt_or_ge 1 1
        · have : 1 < #s := by
            have : 0 ≤ #s := Nat.zero_le #s
            omega
          aesop
    · unfold spectralExpander
      have : K2K2.SpectralGap = 0 := K2K2_SpectralGap_eq_zero
      rw [this]
      aesop
end



-- # Second example with K₂₂

--/-- vertices of K22-/
-- inductive K22V : Type
--   | v1 : K22V
--   | v2 : K22V
--   | v3 : K22V
--   | v4 : K22V
--   deriving Fintype, DecidableEq

/-- vertices of K22-/
inductive K22V : Type
  | v1
  | v2
  | v3
  | v4
  deriving DecidableEq

instance : Fintype K22V where
  elems := {K22V.v1, K22V.v2, K22V.v3, K22V.v4}
  complete := by
    intro x
    cases x <;> simp

lemma card_K22V : Fintype.card K22V = 4 := rfl

--/-- edges of K22-/
-- inductive K22E : Type
--   | e1a : K22E
--   | e2a : K22E
--   | e3a : K22E
--   | e4a : K22E
--   | e1b : K22E
--   | e2b : K22E
--   | e3b : K22E
--   | e4b : K22E
--   deriving Fintype, DecidableEq

/-- edges of K22-/
inductive K22E : Type
  | e1a
  | e2a
  | e3a
  | e4a
  | e1b
  | e2b
  | e3b
  | e4b
  deriving DecidableEq

instance : Fintype K22E where
  elems := {K22E.e1a, K22E.e2a, K22E.e3a, K22E.e4a,
            K22E.e1b, K22E.e2b, K22E.e3b, K22E.e4b}
  complete := by
    intro x
    cases x <;> simp

open K22V K22E

/-- Build K22-/
def K22 : MultiDiGraph K22V K22E where
  vertices := Finset.univ
  edges := Finset.univ
  edgeMap := fun
    | e1a => (v1, v3)
    | e2a => (v1, v4)
    | e3a => (v2, v3)
    | e4a => (v2, v4)
    | e1b => (v3, v1)
    | e2b => (v4, v1)
    | e3b => (v3, v2)
    | e4b => (v4, v2)
  edgesValid := by simp

-- # Now some lemmas about K₂₂

lemma K22_neighbour_of_set_card_one_has_card_one (s : Finset K22V) (hs : #s = 1) :
    #(K22.neighbourhoodOfSet s) = 2 := by
  obtain ⟨v, rfl⟩ := Finset.card_eq_one.mp hs
  simp only [MultiDiGraph.neighbourhoodOfSet]
  fin_cases v
  all_goals
  unfold MultiDiGraph.neighbourhood
  simp_all only [card_singleton, singleton_biUnion]
  rfl

lemma K22_edges_of_cut_card_two (s : Finset K22V) (hs : #s = 1) :
    #({e ∈ K22.edges | (K22.3 e).1 ∈ s ∧
    (K22.3 e).2 ∈ K22.vertices ∧ (K22.3 e).2 ∉ s}) = 2 := by
  obtain ⟨e, rfl⟩ := Finset.card_eq_one.mp hs
  simp only [mem_singleton]
  fin_cases e
  all_goals
  aesop

lemma K22_zero_le_vertices_card : 0 < #K22.vertices := by
  exact Nat.zero_lt_succ [v2, v3, v4].length


lemma K22_regular' : K22.isRegularOfDegree 2 := by
  unfold MultiDiGraph.isRegularOfDegree
  intro v hv
  constructor
  · fin_cases v
    all_goals
    aesop
  · fin_cases v
    all_goals
    aesop

lemma sum_over_vertices_K22 (f : K22V → ℝ) :
    ∑ v, f v = f v1 + f v2 + f v3 + f v4 := by
  have : ∑ v, f v = ∑ v ∈ {v1, v2}, f v + ∑ v ∉ {v1, v2}, f v := by
    exact Eq.symm (sum_add_sum_compl {v1, v2} f)
  rw [this]
  have : ∑ v ∈ {v1, v2}, f v = f v1 + f v2 := by aesop
  rw [this]
  have : ∑ v ∈ {v1, v2}ᶜ, f v =  ∑ v ∈ {v3, v4}, f v := by exact rfl
  rw [this]
  have : ∑ v ∈ {v3, v4}, f v = f v3 + f v4 := by aesop
  rw [this]
  linarith

-- # Now the 16 elements of the randomwalk matrix evaluated


lemma K22_v1_v1 : K22.randomWalkMatrix v1 v1 = (0 : ℝ) := by
  unfold MultiDiGraph.randomWalkMatrix
  simp only [of_apply, ↓reduceIte]
  have :  ∑ v, (K22.adjacencyMatrix v1 v : ℝ) =
      ∑ v ∈ K22.vertices, (K22.adjacencyMatrix v1 v : ℝ) := rfl
  rw [this]

  have : ∑ v ∈ K22.vertices, (K22.adjacencyMatrix v1 v : ℝ) = 2 := by
    have : ∑ v ∈ K22.vertices, (K22.adjacencyMatrix v1 v : ℝ) =
        (K22.adjacencyMatrix v1 v1 : ℝ) +
        (K22.adjacencyMatrix v1 v2 : ℝ) +
        (K22.adjacencyMatrix v1 v3 : ℝ) +
        (K22.adjacencyMatrix v1 v4 : ℝ) := by
      exact sum_over_vertices_K22 fun v ↦ (K22.adjacencyMatrix v1 v : ℝ)
    rw [this]
    have : (K22.adjacencyMatrix v1 v1 : ℝ) = 0 :=
      (Lean.Grind.IsCharP.natCast_eq_zero_iff 0 (K22.adjacencyMatrix v1 v1)).mpr rfl
    rw [this]
    have : (K22.adjacencyMatrix v1 v2 : ℝ) = 0 :=
      (Lean.Grind.IsCharP.natCast_eq_zero_iff 0 (K22.adjacencyMatrix v1 v2)).mpr rfl
    rw [this]
    have : (K22.adjacencyMatrix v1 v3 : ℝ) = 1 := by exact Nat.cast_eq_one.mpr rfl
    rw [this]
    have : (K22.adjacencyMatrix v1 v4 : ℝ) = 1 := by exact Nat.cast_eq_one.mpr rfl
    rw [this]
    linarith
  rw [this]
  simp only [OfNat.ofNat_ne_zero, ↓reduceIte]
  aesop

lemma K22_v2_v1 : K22.randomWalkMatrix v2 v1 = (0 : ℝ) := by
  unfold MultiDiGraph.randomWalkMatrix
  simp only [of_apply]
  have :  ∑ v, (K22.adjacencyMatrix v2 v : ℝ) =
      ∑ v ∈ K22.vertices, (K22.adjacencyMatrix v2 v : ℝ) := rfl
  rw [this]
  have : ∑ v ∈ K22.vertices, (K22.adjacencyMatrix v2 v : ℝ) = 2 := by
    have : ∑ v ∈ K22.vertices, (K22.adjacencyMatrix v2 v : ℝ) =
        (K22.adjacencyMatrix v2 v1 : ℝ) +
        (K22.adjacencyMatrix v2 v2 : ℝ) +
        (K22.adjacencyMatrix v2 v3 : ℝ) +
        (K22.adjacencyMatrix v2 v4 : ℝ) := by
      exact sum_over_vertices_K22 fun v ↦ (K22.adjacencyMatrix v2 v : ℝ)
    rw [this]
    have : (K22.adjacencyMatrix v2 v1 : ℝ) = 0 :=
      (Lean.Grind.IsCharP.natCast_eq_zero_iff 0 (K22.adjacencyMatrix v2 v1)).mpr rfl
    rw [this]
    have : (K22.adjacencyMatrix v2 v2 : ℝ) = 0 :=
      (Lean.Grind.IsCharP.natCast_eq_zero_iff 0 (K22.adjacencyMatrix v2 v2)).mpr rfl
    rw [this]
    have : (K22.adjacencyMatrix v2 v3 : ℝ) = 1 := by exact Nat.cast_eq_one.mpr rfl
    rw [this]
    have : (K22.adjacencyMatrix v2 v4 : ℝ) = 1 := by exact Nat.cast_eq_one.mpr rfl
    rw [this]
    linarith
  rw [this]
  simp only [OfNat.ofNat_ne_zero, ↓reduceIte]
  aesop


lemma K22_v3_v1 : K22.randomWalkMatrix v3 v1 = 0.5 := by
  unfold MultiDiGraph.randomWalkMatrix
  simp only [of_apply, reduceCtorEq, ↓reduceIte]
  have : ∑ v, (K22.adjacencyMatrix v3 v : ℝ) =
      ∑ v ∈ K22.vertices, (K22.adjacencyMatrix v3 v : ℝ) := rfl
  rw [this]
  have : ∑ v ∈ K22.vertices, (K22.adjacencyMatrix v3 v : ℝ) = 2 := by
    have : ∑ v ∈ K22.vertices, (K22.adjacencyMatrix v3 v : ℝ) =
        (K22.adjacencyMatrix v3 v1 : ℝ) +
        (K22.adjacencyMatrix v3 v2 : ℝ) +
        (K22.adjacencyMatrix v3 v3 : ℝ) +
        (K22.adjacencyMatrix v3 v4 : ℝ) := by
      exact sum_over_vertices_K22 fun v ↦ (K22.adjacencyMatrix v3 v : ℝ)
    rw [this]
    have : (K22.adjacencyMatrix v3 v1 : ℝ) = 1 := Nat.cast_eq_one.mpr rfl
    rw [this]
    have : (K22.adjacencyMatrix v3 v2 : ℝ) = 1 := Nat.cast_eq_one.mpr rfl
    rw [this]
    have : (K22.adjacencyMatrix v3 v3 : ℝ) = 0 :=
      (Lean.Grind.IsCharP.natCast_eq_zero_iff 0 (K22.adjacencyMatrix v3 v3)).mpr rfl
    rw [this]
    have : (K22.adjacencyMatrix v3 v4 : ℝ) = 0 :=
      (Lean.Grind.IsCharP.natCast_eq_zero_iff 0 (K22.adjacencyMatrix v3 v4)).mpr rfl
    rw [this]
    linarith
  rw [this]
  simp only [OfNat.ofNat_ne_zero, ↓reduceIte]
  have : K22.adjacencyMatrix v3 v1 = 1 := rfl
  rw [this]
  norm_cast
  linarith

lemma K22_v4_v1 : K22.randomWalkMatrix v4 v1 = 0.5 := by
  unfold MultiDiGraph.randomWalkMatrix
  simp only [of_apply, reduceCtorEq, ↓reduceIte]
  have : ∑ v, (K22.adjacencyMatrix v4 v : ℝ) =
      ∑ v ∈ K22.vertices, (K22.adjacencyMatrix v4 v : ℝ) := rfl
  rw [this]
  have : ∑ v ∈ K22.vertices, (K22.adjacencyMatrix v4 v : ℝ) = 2 := by
    have : ∑ v ∈ K22.vertices, (K22.adjacencyMatrix v4 v : ℝ) =
        (K22.adjacencyMatrix v4 v1 : ℝ) +
        (K22.adjacencyMatrix v4 v2 : ℝ) +
        (K22.adjacencyMatrix v4 v3 : ℝ) +
        (K22.adjacencyMatrix v4 v4 : ℝ) := by
      exact sum_over_vertices_K22 fun v ↦ (K22.adjacencyMatrix v4 v : ℝ)
    rw [this]
    have : (K22.adjacencyMatrix v4 v1 : ℝ) = 1 := Nat.cast_eq_one.mpr rfl
    rw [this]
    have : (K22.adjacencyMatrix v4 v2 : ℝ) = 1 := Nat.cast_eq_one.mpr rfl
    rw [this]
    have : (K22.adjacencyMatrix v4 v3 : ℝ) = 0 :=
      (Lean.Grind.IsCharP.natCast_eq_zero_iff 0 (K22.adjacencyMatrix v4 v3)).mpr rfl
    rw [this]
    have : (K22.adjacencyMatrix v4 v4 : ℝ) = 0 :=
      (Lean.Grind.IsCharP.natCast_eq_zero_iff 0 (K22.adjacencyMatrix v4 v4)).mpr rfl
    rw [this]
    linarith
  rw [this]
  simp only [OfNat.ofNat_ne_zero, ↓reduceIte]
  have : K22.adjacencyMatrix v4 v1 = 1 := rfl
  rw [this]
  norm_cast
  linarith

lemma K22_v1_v2 : K22.randomWalkMatrix v1 v2 = (0 : ℝ) := by
  unfold MultiDiGraph.randomWalkMatrix
  simp only [of_apply]
  have :  ∑ v, (K22.adjacencyMatrix v1 v : ℝ) =
      ∑ v ∈ K22.vertices, (K22.adjacencyMatrix v1 v : ℝ) := rfl
  rw [this]

  have : ∑ v ∈ K22.vertices, (K22.adjacencyMatrix v1 v : ℝ) = 2 := by
    have : ∑ v ∈ K22.vertices, (K22.adjacencyMatrix v1 v : ℝ) =
        (K22.adjacencyMatrix v1 v1 : ℝ) +
        (K22.adjacencyMatrix v1 v2 : ℝ) +
        (K22.adjacencyMatrix v1 v3 : ℝ) +
        (K22.adjacencyMatrix v1 v4 : ℝ) := by
      exact sum_over_vertices_K22 fun v ↦ (K22.adjacencyMatrix v1 v : ℝ)
    rw [this]
    have : (K22.adjacencyMatrix v1 v1 : ℝ) = 0 :=
      (Lean.Grind.IsCharP.natCast_eq_zero_iff 0 (K22.adjacencyMatrix v1 v1)).mpr rfl
    rw [this]
    have : (K22.adjacencyMatrix v1 v2 : ℝ) = 0 :=
      (Lean.Grind.IsCharP.natCast_eq_zero_iff 0 (K22.adjacencyMatrix v1 v2)).mpr rfl
    rw [this]
    have : (K22.adjacencyMatrix v1 v3 : ℝ) = 1 := by exact Nat.cast_eq_one.mpr rfl
    rw [this]
    have : (K22.adjacencyMatrix v1 v4 : ℝ) = 1 := by exact Nat.cast_eq_one.mpr rfl
    rw [this]
    linarith
  rw [this]
  simp only [OfNat.ofNat_ne_zero, ↓reduceIte]
  aesop


lemma K22_v2_v2 : K22.randomWalkMatrix v2 v2 = (0 : ℝ) := by
  unfold MultiDiGraph.randomWalkMatrix
  simp only [of_apply, ↓reduceIte]
  have :  ∑ v, (K22.adjacencyMatrix v2 v : ℝ) =
      ∑ v ∈ K22.vertices, (K22.adjacencyMatrix v2 v : ℝ) := rfl
  rw [this]
  have : ∑ v ∈ K22.vertices, (K22.adjacencyMatrix v2 v : ℝ) = 2 := by
    have : ∑ v ∈ K22.vertices, (K22.adjacencyMatrix v2 v : ℝ) =
        (K22.adjacencyMatrix v2 v1 : ℝ) +
        (K22.adjacencyMatrix v2 v2 : ℝ) +
        (K22.adjacencyMatrix v2 v3 : ℝ) +
        (K22.adjacencyMatrix v2 v4 : ℝ) := by
      exact sum_over_vertices_K22 fun v ↦ (K22.adjacencyMatrix v2 v : ℝ)
    rw [this]
    have : (K22.adjacencyMatrix v2 v1 : ℝ) = 0 :=
      (Lean.Grind.IsCharP.natCast_eq_zero_iff 0 (K22.adjacencyMatrix v2 v1)).mpr rfl
    rw [this]
    have : (K22.adjacencyMatrix v2 v2 : ℝ) = 0 :=
      (Lean.Grind.IsCharP.natCast_eq_zero_iff 0 (K22.adjacencyMatrix v2 v2)).mpr rfl
    rw [this]
    have : (K22.adjacencyMatrix v2 v3 : ℝ) = 1 := by exact Nat.cast_eq_one.mpr rfl
    rw [this]
    have : (K22.adjacencyMatrix v2 v4 : ℝ) = 1 := by exact Nat.cast_eq_one.mpr rfl
    rw [this]
    linarith
  rw [this]
  simp only [OfNat.ofNat_ne_zero, ↓reduceIte]
  aesop


lemma K22_v3_v2 : K22.randomWalkMatrix v3 v2 = 0.5 := by
  unfold MultiDiGraph.randomWalkMatrix
  simp only [of_apply, reduceCtorEq, ↓reduceIte]
  have : ∑ v, (K22.adjacencyMatrix v3 v : ℝ) =
      ∑ v ∈ K22.vertices, (K22.adjacencyMatrix v3 v : ℝ) := rfl
  rw [this]
  have : ∑ v ∈ K22.vertices, (K22.adjacencyMatrix v3 v : ℝ) = 2 := by
    have : ∑ v ∈ K22.vertices, (K22.adjacencyMatrix v3 v : ℝ) =
        (K22.adjacencyMatrix v3 v1 : ℝ) +
        (K22.adjacencyMatrix v3 v2 : ℝ) +
        (K22.adjacencyMatrix v3 v3 : ℝ) +
        (K22.adjacencyMatrix v3 v4 : ℝ) := by
      exact sum_over_vertices_K22 fun v ↦ (K22.adjacencyMatrix v3 v : ℝ)
    rw [this]
    have : (K22.adjacencyMatrix v3 v1 : ℝ) = 1 := Nat.cast_eq_one.mpr rfl
    rw [this]
    have : (K22.adjacencyMatrix v3 v2 : ℝ) = 1 := Nat.cast_eq_one.mpr rfl
    rw [this]
    have : (K22.adjacencyMatrix v3 v3 : ℝ) = 0 :=
      (Lean.Grind.IsCharP.natCast_eq_zero_iff 0 (K22.adjacencyMatrix v3 v3)).mpr rfl
    rw [this]
    have : (K22.adjacencyMatrix v3 v4 : ℝ) = 0 :=
      (Lean.Grind.IsCharP.natCast_eq_zero_iff 0 (K22.adjacencyMatrix v3 v4)).mpr rfl
    rw [this]
    linarith
  rw [this]
  simp only [OfNat.ofNat_ne_zero, ↓reduceIte]
  have : K22.adjacencyMatrix v3 v2 = 1 := rfl
  rw [this]
  norm_cast
  linarith

lemma K22_v4_v2 : K22.randomWalkMatrix v4 v2 = 0.5 := by
  unfold MultiDiGraph.randomWalkMatrix
  simp only [of_apply, reduceCtorEq, ↓reduceIte]
  have : ∑ v, (K22.adjacencyMatrix v4 v : ℝ) =
      ∑ v ∈ K22.vertices, (K22.adjacencyMatrix v4 v : ℝ) := rfl
  rw [this]
  have : ∑ v ∈ K22.vertices, (K22.adjacencyMatrix v4 v : ℝ) = 2 := by
    have : ∑ v ∈ K22.vertices, (K22.adjacencyMatrix v4 v : ℝ) =
        (K22.adjacencyMatrix v4 v1 : ℝ) +
        (K22.adjacencyMatrix v4 v2 : ℝ) +
        (K22.adjacencyMatrix v4 v3 : ℝ) +
        (K22.adjacencyMatrix v4 v4 : ℝ) := by
      exact sum_over_vertices_K22 fun v ↦ (K22.adjacencyMatrix v4 v : ℝ)
    rw [this]
    have : (K22.adjacencyMatrix v4 v1 : ℝ) = 1 := Nat.cast_eq_one.mpr rfl
    rw [this]
    have : (K22.adjacencyMatrix v4 v2 : ℝ) = 1 := Nat.cast_eq_one.mpr rfl
    rw [this]
    have : (K22.adjacencyMatrix v4 v3 : ℝ) = 0 :=
      (Lean.Grind.IsCharP.natCast_eq_zero_iff 0 (K22.adjacencyMatrix v4 v3)).mpr rfl
    rw [this]
    have : (K22.adjacencyMatrix v4 v4 : ℝ) = 0 :=
      (Lean.Grind.IsCharP.natCast_eq_zero_iff 0 (K22.adjacencyMatrix v4 v4)).mpr rfl
    rw [this]
    linarith
  rw [this]
  simp only [OfNat.ofNat_ne_zero, ↓reduceIte]
  have : K22.adjacencyMatrix v4 v2 = 1 := rfl
  rw [this]
  norm_cast
  linarith

lemma K22_v1_v3 : K22.randomWalkMatrix v1 v3 = 0.5 := by
  unfold MultiDiGraph.randomWalkMatrix
  simp only [of_apply, reduceCtorEq, ↓reduceIte]
  have : ∑ v, (K22.adjacencyMatrix v1 v : ℝ) =
      ∑ v ∈ K22.vertices, (K22.adjacencyMatrix v1 v : ℝ) := rfl
  rw [this]
  have : ∑ v ∈ K22.vertices, (K22.adjacencyMatrix v1 v : ℝ) = 2 := by
    have : ∑ v ∈ K22.vertices, (K22.adjacencyMatrix v1 v : ℝ) =
        (K22.adjacencyMatrix v1 v1 : ℝ) +
        (K22.adjacencyMatrix v1 v2 : ℝ) +
        (K22.adjacencyMatrix v1 v3 : ℝ) +
        (K22.adjacencyMatrix v1 v4 : ℝ) := by
      exact sum_over_vertices_K22 fun v ↦ (K22.adjacencyMatrix v1 v : ℝ)
    rw [this]
    have : (K22.adjacencyMatrix v1 v3 : ℝ) = 1 := Nat.cast_eq_one.mpr rfl
    rw [this]
    have : (K22.adjacencyMatrix v1 v4 : ℝ) = 1 := Nat.cast_eq_one.mpr rfl
    rw [this]
    have : (K22.adjacencyMatrix v1 v1 : ℝ) = 0 :=
      (Lean.Grind.IsCharP.natCast_eq_zero_iff 0 (K22.adjacencyMatrix v1 v1)).mpr rfl
    rw [this]
    have : (K22.adjacencyMatrix v1 v2 : ℝ) = 0 :=
      (Lean.Grind.IsCharP.natCast_eq_zero_iff 0 (K22.adjacencyMatrix v1 v2)).mpr rfl
    rw [this]
    linarith
  rw [this]
  simp only [OfNat.ofNat_ne_zero, ↓reduceIte]
  have : K22.adjacencyMatrix v1 v3 = 1 := rfl
  rw [this]
  norm_cast
  linarith

lemma K22_v2_v3 : K22.randomWalkMatrix v2 v3 = 0.5 := by
  unfold MultiDiGraph.randomWalkMatrix
  simp only [of_apply, reduceCtorEq, ↓reduceIte]
  have : ∑ v, (K22.adjacencyMatrix v2 v : ℝ) =
      ∑ v ∈ K22.vertices, (K22.adjacencyMatrix v2 v : ℝ) := rfl
  rw [this]
  have : ∑ v ∈ K22.vertices, (K22.adjacencyMatrix v2 v : ℝ) = 2 := by
    have : ∑ v ∈ K22.vertices, (K22.adjacencyMatrix v2 v : ℝ) =
        (K22.adjacencyMatrix v2 v1 : ℝ) +
        (K22.adjacencyMatrix v2 v2 : ℝ) +
        (K22.adjacencyMatrix v2 v3 : ℝ) +
        (K22.adjacencyMatrix v2 v4 : ℝ) := by
      exact sum_over_vertices_K22 fun v ↦ (K22.adjacencyMatrix v2 v : ℝ)
    rw [this]
    have : (K22.adjacencyMatrix v2 v1 : ℝ) = 0 :=
      (Lean.Grind.IsCharP.natCast_eq_zero_iff 0 (K22.adjacencyMatrix v2 v1)).mpr rfl
    rw [this]
    have : (K22.adjacencyMatrix v2 v2 : ℝ) = 0 :=
      (Lean.Grind.IsCharP.natCast_eq_zero_iff 0 (K22.adjacencyMatrix v2 v2)).mpr rfl
    rw [this]
    have : (K22.adjacencyMatrix v2 v3 : ℝ) = 1 := Nat.cast_eq_one.mpr rfl
    rw [this]
    have : (K22.adjacencyMatrix v2 v4 : ℝ) = 1 := Nat.cast_eq_one.mpr rfl
    rw [this]
    linarith
  rw [this]
  simp only [OfNat.ofNat_ne_zero, ↓reduceIte]
  have : K22.adjacencyMatrix v2 v3 = 1 := rfl
  rw [this]
  norm_cast
  linarith

lemma K22_v3_v3 : K22.randomWalkMatrix v3 v3 = (0 : ℝ) := by
  unfold MultiDiGraph.randomWalkMatrix
  simp only [of_apply, ↓reduceIte]
  have :  ∑ v, (K22.adjacencyMatrix v3 v : ℝ) =
      ∑ v ∈ K22.vertices, (K22.adjacencyMatrix v3 v : ℝ) := rfl
  rw [this]
  have : ∑ v ∈ K22.vertices, (K22.adjacencyMatrix v3 v : ℝ) = 2 := by
    have : ∑ v ∈ K22.vertices, (K22.adjacencyMatrix v3 v : ℝ) =
        (K22.adjacencyMatrix v3 v1 : ℝ) +
        (K22.adjacencyMatrix v3 v2 : ℝ) +
        (K22.adjacencyMatrix v3 v3 : ℝ) +
        (K22.adjacencyMatrix v3 v4 : ℝ) := by
      exact sum_over_vertices_K22 fun v ↦ (K22.adjacencyMatrix v3 v : ℝ)
    rw [this]
    have : (K22.adjacencyMatrix v3 v3 : ℝ) = 0 :=
      (Lean.Grind.IsCharP.natCast_eq_zero_iff 0 (K22.adjacencyMatrix v3 v3)).mpr rfl
    rw [this]
    have : (K22.adjacencyMatrix v3 v4 : ℝ) = 0 :=
      (Lean.Grind.IsCharP.natCast_eq_zero_iff 0 (K22.adjacencyMatrix v3 v4)).mpr rfl
    rw [this]
    have : (K22.adjacencyMatrix v3 v1 : ℝ) = 1 := by exact Nat.cast_eq_one.mpr rfl
    rw [this]
    have : (K22.adjacencyMatrix v3 v2 : ℝ) = 1 := by exact Nat.cast_eq_one.mpr rfl
    rw [this]
    linarith
  rw [this]
  simp only [OfNat.ofNat_ne_zero, ↓reduceIte]
  aesop

lemma K22_v4_v3 : K22.randomWalkMatrix v4 v3 = (0 : ℝ) := by
  unfold MultiDiGraph.randomWalkMatrix
  simp only [of_apply]
  have :  ∑ v, (K22.adjacencyMatrix v4 v : ℝ) =
      ∑ v ∈ K22.vertices, (K22.adjacencyMatrix v4 v : ℝ) := rfl
  rw [this]
  have : ∑ v ∈ K22.vertices, (K22.adjacencyMatrix v4 v : ℝ) = 2 := by
    have : ∑ v ∈ K22.vertices, (K22.adjacencyMatrix v4 v : ℝ) =
        (K22.adjacencyMatrix v4 v1 : ℝ) +
        (K22.adjacencyMatrix v4 v2 : ℝ) +
        (K22.adjacencyMatrix v4 v3 : ℝ) +
        (K22.adjacencyMatrix v4 v4 : ℝ) := by
      exact sum_over_vertices_K22 fun v ↦ (K22.adjacencyMatrix v4 v : ℝ)
    rw [this]
    have : (K22.adjacencyMatrix v4 v3 : ℝ) = 0 :=
      (Lean.Grind.IsCharP.natCast_eq_zero_iff 0 (K22.adjacencyMatrix v4 v3)).mpr rfl
    rw [this]
    have : (K22.adjacencyMatrix v4 v4 : ℝ) = 0 :=
      (Lean.Grind.IsCharP.natCast_eq_zero_iff 0 (K22.adjacencyMatrix v4 v4)).mpr rfl
    rw [this]
    have : (K22.adjacencyMatrix v4 v1 : ℝ) = 1 := by exact Nat.cast_eq_one.mpr rfl
    rw [this]
    have : (K22.adjacencyMatrix v4 v2 : ℝ) = 1 := by exact Nat.cast_eq_one.mpr rfl
    rw [this]
    linarith
  rw [this]
  simp only [OfNat.ofNat_ne_zero, ↓reduceIte]
  aesop

lemma K22_v1_v4 : K22.randomWalkMatrix v1 v4 = 0.5 := by
  unfold MultiDiGraph.randomWalkMatrix
  simp only [of_apply, reduceCtorEq, ↓reduceIte]
  have : ∑ v, (K22.adjacencyMatrix v1 v : ℝ) =
      ∑ v ∈ K22.vertices, (K22.adjacencyMatrix v1 v : ℝ) := rfl
  rw [this]
  have : ∑ v ∈ K22.vertices, (K22.adjacencyMatrix v1 v : ℝ) = 2 := by
    have : ∑ v ∈ K22.vertices, (K22.adjacencyMatrix v1 v : ℝ) =
        (K22.adjacencyMatrix v1 v1 : ℝ) +
        (K22.adjacencyMatrix v1 v2 : ℝ) +
        (K22.adjacencyMatrix v1 v3 : ℝ) +
        (K22.adjacencyMatrix v1 v4 : ℝ) := by
      exact sum_over_vertices_K22 fun v ↦ (K22.adjacencyMatrix v1 v : ℝ)
    rw [this]
    have : (K22.adjacencyMatrix v1 v3 : ℝ) = 1 := Nat.cast_eq_one.mpr rfl
    rw [this]
    have : (K22.adjacencyMatrix v1 v4 : ℝ) = 1 := Nat.cast_eq_one.mpr rfl
    rw [this]
    have : (K22.adjacencyMatrix v1 v1 : ℝ) = 0 :=
      (Lean.Grind.IsCharP.natCast_eq_zero_iff 0 (K22.adjacencyMatrix v1 v1)).mpr rfl
    rw [this]
    have : (K22.adjacencyMatrix v1 v2 : ℝ) = 0 :=
      (Lean.Grind.IsCharP.natCast_eq_zero_iff 0 (K22.adjacencyMatrix v1 v2)).mpr rfl
    rw [this]
    linarith
  rw [this]
  simp only [OfNat.ofNat_ne_zero, ↓reduceIte]
  have : K22.adjacencyMatrix v1 v4 = 1 := rfl
  rw [this]
  norm_cast
  linarith

lemma K22_v2_v4 : K22.randomWalkMatrix v2 v4 = 0.5 := by
  unfold MultiDiGraph.randomWalkMatrix
  simp only [of_apply, reduceCtorEq, ↓reduceIte]
  have : ∑ v, (K22.adjacencyMatrix v2 v : ℝ) =
      ∑ v ∈ K22.vertices, (K22.adjacencyMatrix v2 v : ℝ) := rfl
  rw [this]
  have : ∑ v ∈ K22.vertices, (K22.adjacencyMatrix v2 v : ℝ) = 2 := by
    have : ∑ v ∈ K22.vertices, (K22.adjacencyMatrix v2 v : ℝ) =
        (K22.adjacencyMatrix v2 v1 : ℝ) +
        (K22.adjacencyMatrix v2 v2 : ℝ) +
        (K22.adjacencyMatrix v2 v3 : ℝ) +
        (K22.adjacencyMatrix v2 v4 : ℝ) := by
      exact sum_over_vertices_K22 fun v ↦ (K22.adjacencyMatrix v2 v : ℝ)
    rw [this]
    have : (K22.adjacencyMatrix v2 v1 : ℝ) = 0 :=
      (Lean.Grind.IsCharP.natCast_eq_zero_iff 0 (K22.adjacencyMatrix v2 v1)).mpr rfl
    rw [this]
    have : (K22.adjacencyMatrix v2 v2 : ℝ) = 0 :=
      (Lean.Grind.IsCharP.natCast_eq_zero_iff 0 (K22.adjacencyMatrix v2 v2)).mpr rfl
    rw [this]
    have : (K22.adjacencyMatrix v2 v3 : ℝ) = 1 := Nat.cast_eq_one.mpr rfl
    rw [this]
    have : (K22.adjacencyMatrix v2 v4 : ℝ) = 1 := Nat.cast_eq_one.mpr rfl
    rw [this]
    linarith
  rw [this]
  simp only [OfNat.ofNat_ne_zero, ↓reduceIte]
  have : K22.adjacencyMatrix v2 v4 = 1 := rfl
  rw [this]
  norm_cast
  linarith

lemma K22_v3_v4 : K22.randomWalkMatrix v3 v4 = (0 : ℝ) := by
  unfold MultiDiGraph.randomWalkMatrix
  simp only [of_apply]
  have :  ∑ v, (K22.adjacencyMatrix v3 v : ℝ) =
      ∑ v ∈ K22.vertices, (K22.adjacencyMatrix v3 v : ℝ) := rfl
  rw [this]
  have : ∑ v ∈ K22.vertices, (K22.adjacencyMatrix v3 v : ℝ) = 2 := by
    have : ∑ v ∈ K22.vertices, (K22.adjacencyMatrix v3 v : ℝ) =
        (K22.adjacencyMatrix v3 v1 : ℝ) +
        (K22.adjacencyMatrix v3 v2 : ℝ) +
        (K22.adjacencyMatrix v3 v3 : ℝ) +
        (K22.adjacencyMatrix v3 v4 : ℝ) := by
      exact sum_over_vertices_K22 fun v ↦ (K22.adjacencyMatrix v3 v : ℝ)
    rw [this]
    have : (K22.adjacencyMatrix v3 v3 : ℝ) = 0 :=
      (Lean.Grind.IsCharP.natCast_eq_zero_iff 0 (K22.adjacencyMatrix v3 v3)).mpr rfl
    rw [this]
    have : (K22.adjacencyMatrix v3 v4 : ℝ) = 0 :=
      (Lean.Grind.IsCharP.natCast_eq_zero_iff 0 (K22.adjacencyMatrix v3 v4)).mpr rfl
    rw [this]
    have : (K22.adjacencyMatrix v3 v1 : ℝ) = 1 := by exact Nat.cast_eq_one.mpr rfl
    rw [this]
    have : (K22.adjacencyMatrix v3 v2 : ℝ) = 1 := by exact Nat.cast_eq_one.mpr rfl
    rw [this]
    linarith
  rw [this]
  simp only [OfNat.ofNat_ne_zero, ↓reduceIte]
  aesop

lemma K22_v4_v4 : K22.randomWalkMatrix v4 v4 = (0 : ℝ) := by
  unfold MultiDiGraph.randomWalkMatrix
  simp only [of_apply, ↓reduceIte]
  have :  ∑ v, (K22.adjacencyMatrix v4 v : ℝ) =
      ∑ v ∈ K22.vertices, (K22.adjacencyMatrix v4 v : ℝ) := rfl
  rw [this]
  have : ∑ v ∈ K22.vertices, (K22.adjacencyMatrix v4 v : ℝ) = 2 := by
    have : ∑ v ∈ K22.vertices, (K22.adjacencyMatrix v4 v : ℝ) =
        (K22.adjacencyMatrix v4 v1 : ℝ) +
        (K22.adjacencyMatrix v4 v2 : ℝ) +
        (K22.adjacencyMatrix v4 v3 : ℝ) +
        (K22.adjacencyMatrix v4 v4 : ℝ) := by
      exact sum_over_vertices_K22 fun v ↦ (K22.adjacencyMatrix v4 v : ℝ)
    rw [this]
    have : (K22.adjacencyMatrix v4 v3 : ℝ) = 0 :=
      (Lean.Grind.IsCharP.natCast_eq_zero_iff 0 (K22.adjacencyMatrix v4 v3)).mpr rfl
    rw [this]
    have : (K22.adjacencyMatrix v4 v4 : ℝ) = 0 :=
      (Lean.Grind.IsCharP.natCast_eq_zero_iff 0 (K22.adjacencyMatrix v4 v4)).mpr rfl
    rw [this]
    have : (K22.adjacencyMatrix v4 v1 : ℝ) = 1 := Nat.cast_eq_one.mpr rfl
    rw [this]
    have : (K22.adjacencyMatrix v4 v2 : ℝ) = 1 := Nat.cast_eq_one.mpr rfl
    rw [this]
    linarith
  rw [this]
  simp only [OfNat.ofNat_ne_zero, ↓reduceIte]
  aesop


-- # Now a non-uniform stationary distribution used to prove zero spectral gap

/-- A vector that is has `ℓ₂` norm preserved by the random walk matrix of `K₂₂`,
but is not the uniform distribution -/
def π' : K22V → ℝ
  | v1 => 0.5
  | v2 => 0.5
  | v3 => 0.0
  | v4 => 0.0


lemma l2norm_π' : L2normSQ (π' - UniformDist K22.vertices) K22.vertices = 0.25 := by
  unfold L2normSQ
  have : ∑ i ∈ K22.vertices, (π' - UniformDist K22.vertices) i ^ 2 =
        (π' - UniformDist K22.vertices) v1 ^ 2 +
        (π' - UniformDist K22.vertices) v2 ^ 2 +
        (π' - UniformDist K22.vertices) v3 ^ 2 +
        (π' - UniformDist K22.vertices) v4 ^ 2 :=
    sum_over_vertices_K22 fun i ↦ (π' - UniformDist K22.vertices) i ^ 2
  rw [this]
  have : (π' - UniformDist K22.vertices) v1 ^ 2 = 0.0625 := by
    norm_num
    have h₁ : π' v1 = 0.5 := rfl
    rw [h₁]
    have h₂ : UniformDist K22.vertices v1 = 0.25 := by
      unfold UniformDist
      have : #K22.vertices = 4 := by rfl
      rw [this]
      have : v1 ∈ K22.vertices := by exact insert_eq_self.mp rfl
      field_simp
      ring_nf
      aesop
    rw [h₂]
    norm_num
  rw [this]
  have : (π' - UniformDist K22.vertices) v2 ^ 2 = 0.0625 := by
    norm_num
    have h₁ : π' v2 = 0.5 := rfl
    rw [h₁]
    have h₂ : UniformDist K22.vertices v2 = 0.25 := by
      unfold UniformDist
      have : #K22.vertices = 4 := by rfl
      rw [this]
      have : v2 ∈ K22.vertices := by exact insert_eq_self.mp rfl
      field_simp
      ring_nf
      aesop
    rw [h₂]
    norm_num
  rw [this]
  have : (π' - UniformDist K22.vertices) v3 ^ 2 = 0.0625 := by
    norm_num
    have h₁ : π' v3 = 0.0 := rfl
    rw [h₁]
    have h₂ : UniformDist K22.vertices v3 = 0.25 := by
      unfold UniformDist
      have : #K22.vertices = 4 := by rfl
      rw [this]
      have : v3 ∈ K22.vertices := by exact insert_eq_self.mp rfl
      field_simp
      ring_nf
      aesop
    rw [h₂]
    norm_num
  rw [this]
  have : (π' - UniformDist K22.vertices) v4 ^ 2 = 0.0625 := by
    norm_num
    have h₁ : π' v4 = 0.0 := rfl
    rw [h₁]
    have h₂ : UniformDist K22.vertices v4 = 0.25 := by
      unfold UniformDist
      have : #K22.vertices = 4 := by rfl
      rw [this]
      have : v4 ∈ K22.vertices := by exact insert_eq_self.mp rfl
      field_simp
      ring_nf
      aesop
    rw [h₂]
    norm_num
  rw [this]
  norm_num

/-- A distribution to show the spectral gap of `K₂₂` is zero -/
def π'' : K22V → ℝ
  | v1 => 0.0
  | v2 => 0.0
  | v3 => 0.5
  | v4 => 0.5

lemma l2norm_π'' : L2normSQ (π'' - UniformDist K22.vertices) K22.vertices = 0.25 := by
  unfold L2normSQ
  have : ∑ i ∈ K22.vertices, (π'' - UniformDist K22.vertices) i ^ 2 =
        (π'' - UniformDist K22.vertices) v1 ^ 2 +
        (π'' - UniformDist K22.vertices) v2 ^ 2 +
        (π'' - UniformDist K22.vertices) v3 ^ 2 +
        (π'' - UniformDist K22.vertices) v4 ^ 2 :=
    sum_over_vertices_K22 fun i ↦ (π'' - UniformDist K22.vertices) i ^ 2
  rw [this]
  have : (π'' - UniformDist K22.vertices) v1 ^ 2 = 0.0625 := by
    norm_num
    have h₁ : π'' v1 = 0.0 := rfl
    rw [h₁]
    have h₂ : UniformDist K22.vertices v1 = 0.25 := by
      unfold UniformDist
      have : #K22.vertices = 4 := by rfl
      rw [this]
      have : v1 ∈ K22.vertices := by exact insert_eq_self.mp rfl
      field_simp
      ring_nf
      aesop
    rw [h₂]
    norm_num
  rw [this]
  have : (π'' - UniformDist K22.vertices) v2 ^ 2 = 0.0625 := by
    norm_num
    have h₁ : π'' v2 = 0.0 := rfl
    rw [h₁]
    have h₂ : UniformDist K22.vertices v2 = 0.25 := by
      unfold UniformDist
      have : #K22.vertices = 4 := by rfl
      rw [this]
      have : v2 ∈ K22.vertices := by exact insert_eq_self.mp rfl
      field_simp
      ring_nf
      aesop
    rw [h₂]
    norm_num
  rw [this]
  have : (π'' - UniformDist K22.vertices) v3 ^ 2 = 0.0625 := by
    norm_num
    have h₁ : π'' v3 = 0.5 := rfl
    rw [h₁]
    have h₂ : UniformDist K22.vertices v3 = 0.25 := by
      unfold UniformDist
      have : #K22.vertices = 4 := by rfl
      rw [this]
      have : v3 ∈ K22.vertices := by exact insert_eq_self.mp rfl
      field_simp
      ring_nf
      aesop
    rw [h₂]
    norm_num
  rw [this]
  have : (π'' - UniformDist K22.vertices) v4 ^ 2 = 0.0625 := by
    norm_num
    have h₁ : π'' v4 = 0.5 := rfl
    rw [h₁]
    have h₂ : UniformDist K22.vertices v4 = 0.25 := by
      unfold UniformDist
      have : #K22.vertices = 4 := by rfl
      rw [this]
      have : v4 ∈ K22.vertices := by exact insert_eq_self.mp rfl
      field_simp
      ring_nf
      aesop
    rw [h₂]
    norm_num
  rw [this]
  norm_num



/-- `π'` is mapped to `π''` by the random walk matrix of `K₂₂`-/
lemma π'_to_π'' : π' ᵥ* K22.randomWalkMatrix = π'' := by
  have : ∀ i, (π' ᵥ* K22.randomWalkMatrix) i = π'' i := by
    intro i
    have h₀: ∀i, ((π' ᵥ* K22.randomWalkMatrix) i) = ∑ j, π' j * K22.randomWalkMatrix j i := by
      exact fun i ↦ rfl
    rw [h₀]
    fin_cases i
    · have : ∑ j, π' j * K22.randomWalkMatrix j v1 =
          π' v1 * K22.randomWalkMatrix v1 v1 +
          π' v2 * K22.randomWalkMatrix v2 v1 +
          π' v3 * K22.randomWalkMatrix v3 v1 +
          π' v4 * K22.randomWalkMatrix v4 v1 :=
        sum_over_vertices_K22 fun v ↦ π' v * K22.randomWalkMatrix v v1
      rw [this]
      have : π' v1 * K22.randomWalkMatrix v1 v1 = 0.0 := by
        rw [K22_v1_v1]
        linarith
      rw [this]
      have : π' v2 * K22.randomWalkMatrix v2 v1 = 0.0 := by
        rw [K22_v2_v1]
        -- rw [this]
        linarith
      rw [this]
      have : π' v3 * K22.randomWalkMatrix v3 v1 = 0.0 := by
        -- rw [K22_v3_v1]
        have : π' v3 = 0.0 := rfl
        rw [this]
        linarith
      rw [this]
      have : π' v4 * K22.randomWalkMatrix v4 v1 = 0.0 := by
        rw [K22_v4_v1]
        have : π' v4 = 0.0 := rfl
        linarith
      rw [this]
      have : π'' v1 = 0.0 := rfl
      rw [this]
      linarith
    · have : ∑ j, π' j * K22.randomWalkMatrix j v2 =
          π' v1 * K22.randomWalkMatrix v1 v2 +
          π' v2 * K22.randomWalkMatrix v2 v2 +
          π' v3 * K22.randomWalkMatrix v3 v2 +
          π' v4 * K22.randomWalkMatrix v4 v2 :=
        sum_over_vertices_K22 fun v ↦ π' v * K22.randomWalkMatrix v v2
      rw [this]
      have : π' v1 * K22.randomWalkMatrix v1 v2 = 0.0 := by
        rw [K22_v1_v2]
        -- rw [this]
        linarith
      rw [this]
      have : π' v2 * K22.randomWalkMatrix v2 v2 = 0.0 := by
        rw [K22_v2_v2]
        linarith
      rw [this]
      have : π' v3 * K22.randomWalkMatrix v3 v2 = 0.0 := by
        rw [K22_v3_v2]
        have : π' v3 = 0.0 := rfl
        linarith
      rw [this]
      have : π' v4 * K22.randomWalkMatrix v4 v2 = 0.0 := by
        rw [K22_v4_v2]
        have : π' v4 = 0.0 := rfl
        linarith
      rw [this]
      have : π'' v2 = 0.0 := rfl
      rw [this]
      linarith
    · have : ∑ j, π' j * K22.randomWalkMatrix j v3 =
          π' v1 * K22.randomWalkMatrix v1 v3 +
          π' v2 * K22.randomWalkMatrix v2 v3 +
          π' v3 * K22.randomWalkMatrix v3 v3 +
          π' v4 * K22.randomWalkMatrix v4 v3 :=
        sum_over_vertices_K22 fun v ↦ π' v * K22.randomWalkMatrix v v3
      rw [this]
      have : π' v1 * K22.randomWalkMatrix v1 v3 = 0.25 := by
        rw [K22_v1_v3]
        have : π' v1 = 0.5 := rfl
        rw [this]
        linarith
      rw [this]
      have : π' v2 * K22.randomWalkMatrix v2 v3 = 0.25 := by
        rw [K22_v2_v3]
        have : π' v2 = 0.5 := rfl
        linarith
      rw [this]
      have : π' v3 * K22.randomWalkMatrix v3 v3 = 0.0 := by
        rw [K22_v3_v3]
        linarith
      rw [this]
      have : π' v4 * K22.randomWalkMatrix v4 v3 = 0.0 := by
        rw [K22_v4_v3]
        -- rw [this]
        linarith
      rw [this]
      have : π'' v3 = 0.5 := rfl
      rw [this]
      linarith
    · have : ∑ j, π' j * K22.randomWalkMatrix j v4 =
          π' v1 * K22.randomWalkMatrix v1 v4 +
          π' v2 * K22.randomWalkMatrix v2 v4 +
          π' v3 * K22.randomWalkMatrix v3 v4 +
          π' v4 * K22.randomWalkMatrix v4 v4 :=
        sum_over_vertices_K22 fun v ↦ π' v * K22.randomWalkMatrix v v4
      rw [this]
      have : π' v1 * K22.randomWalkMatrix v1 v4 = 0.25 := by
        rw [K22_v1_v4]
        have : π' v1 = 0.5 := rfl
        linarith
      rw [this]
      have : π' v2 * K22.randomWalkMatrix v2 v4 = 0.25 := by
        rw [K22_v2_v4]
        have : π' v2 = 0.5 := rfl
        linarith
      rw [this]
      have : π' v3 * K22.randomWalkMatrix v3 v4 = 0.0 := by
        rw [K22_v3_v4]
        linarith
      rw [this]
      have : π' v4 * K22.randomWalkMatrix v4 v4 = 0.0 := by
        rw [K22_v4_v4]
        linarith
      have hv4 : π'' v4 = 0.5 := rfl
      rw [this, hv4]
      linarith
  aesop


lemma K22_SpectralGap_eq_zero : K22.SpectralGap = 0 := by
  have h₀ : 0 ≤ K22.SpectralGap := by
    have : 2 ≠ 0 := by aesop
    exact K22.SpectralGap_geq_zero K22_zero_le_vertices_card this K22_regular'
  have h₁ : K22.SpectralGap ≤ 0 := by
    unfold MultiDiGraph.SpectralGap
    let u := UniformDist K22.vertices
    let M := K22.randomWalkMatrix
    let L := K22.vertices
    have : sSup {y |∃ p, IsProbVector p L ∧ p ≠ u ∧ y =
        √(L2normSQ (p ᵥ* M - u) L) / √(L2normSQ (p - u) L)} ≥ 1 := by
      -- first we show that `π` is a probability vector over `K2K2.vertices`
      have hπ₁ : IsProbVector π' L := by
        unfold IsProbVector
        constructor
        · have : ∑ i ∈ L, π' i = ∑ i ∈ {v1, v2}, π' i + ∑ i ∉ {v1, v2}, π' i := by
            rw [←sum_union]
            · rfl
            · exact disjoint_sdiff
          rw [this]
          have : ∑ i ∉ {v1, v2}, π' i = 0 := by
            have : ∑ i ∉ {v1, v2}, π' i = ∑ i ∈ {v3, v4}, π' i := by
              have h₀ : L \ {v1, v2} = {v3, v4} := by aesop
              have : {v1, v2}ᶜ = L \ {v1, v2} := by aesop
              rw [←this] at h₀
              rw [h₀]
            rw [this]
            have : ∑ i ∈ {v3, v4}, π' i = π' v3 + π' v4 := by
              aesop
            rw [this]
            have : π' v3 = 0 := by
              unfold π'
              linarith
            rw [this]
            have : π' v4 = 0 := by
              unfold π'
              linarith
            rw [this]
            linarith
          rw [this]
          have : ∑ i ∈ {v1, v2}, π' i = 1 := by
            have : ∑ i ∈ {v1, v2}, π' i = π' v1 + π' v2 := by aesop
            rw [this]
            have : π' v1 = 0.5 := by
              unfold π'
              linarith
            rw [this]
            have : π' v2 = 0.5 := by
              unfold π'
              linarith
            rw [this]
            linarith
          rw [this]
          linarith
        · constructor
          · unfold π'
            norm_num
            aesop
          · unfold π'
            intro i hi
            have hv₁ : v1 ∈ L := insert_eq_self.mp rfl
            have hv₂ : v2 ∈ L := insert_eq_self.mp rfl
            have h₁ : i ≠ v1 := by aesop
            have h₂ : i ≠ v2 := by aesop
            simp_all only [ne_eq, L]
            split
            next x => simp_all only
            next x => simp_all only
            next x =>
              simp_all only [reduceCtorEq, not_false_eq_true]
              linarith
            next x =>
              simp_all only [reduceCtorEq, not_false_eq_true]
              linarith
      -- Now show that `π` is not the uniform distribution
      have hπ₂ : π' ≠ UniformDist K22.vertices := by
        unfold π' UniformDist
        have : #K22.vertices = 4 := by aesop
        have : 1 / (#K22.vertices : ℝ) = 0.25 := by
          norm_num
          aesop
        rw [this]
        have h₁ : v1 ∈ K22.vertices := by
          exact insert_eq_self.mp rfl
        intro h_eq
        have val := congr_fun h_eq v1
        simp [h₁] at val
        norm_num at val

      -- Now show that `π M = π`
      have hπ₃ : π' ᵥ* K22.randomWalkMatrix = π'' := π'_to_π''

      have hπ₄ : ∃ i ∈ K22.vertices, (π' - UniformDist K22.vertices) i ≠ 0 := by
      -- because they are not equal
        have h₁ : v1 ∈ K22.vertices := by
          exact insert_eq_self.mp rfl
        have : UniformDist K22.vertices v1 ≠ π' v1 := by
          have : UniformDist K22.vertices v1 = 0.25 := by
            unfold UniformDist
            have : #K22.vertices = 4 := by aesop
            have : 1 / (#K22.vertices : ℝ) = 0.25 := by
              norm_num
              aesop
            rw [this]
            aesop
          rw [this]
          have : π' v1 = 0.5 := rfl
          rw [this]
          linarith
        have : π' v1 - UniformDist K22.vertices v1 ≠ 0 :=
          sub_ne_zero_of_ne (id (Ne.symm this))
        aesop

      -- put all of the above pieces together to obtain the result
      have : 0 < L2normSQ (π' - u) L := L2normSQ_positive (π' - u) L hπ₄
      have h₁ : √(L2normSQ (π' ᵥ* M - u) L) / √(L2normSQ (π' - u) L) = 1 := by
        rw [hπ₃]
        field_simp
        -- need to evaluate the L2norm of top and bottom
        have : L2normSQ (π'' - u) L = 0.25 := by
          exact l2norm_π''
        rw [this]
        have : L2normSQ (π' - u) L = 0.25 := by
          exact l2norm_π'
        rw [this]
      apply le_csSup
      · have : ∀ x ∈ {y | ∃ p, IsProbVector p L ∧ p ≠ u ∧ y =
            √(L2normSQ (p ᵥ* M - u) L)
            / √(L2normSQ (p - u) L)}, x ≤ 1 := by
          have hV : 0 < #K22.vertices := by exact K22_zero_le_vertices_card
          have : 2 ≠ 0 := by aesop
          exact K22.bound_on_L2normSQ' hV this K22_regular'
        use 1
        exact this
      · aesop
    linarith
  linarith

-- # The second examples

example : (vertexExpander (1 : ℝ) (2 : ℝ) K22) ∧ (edgeExpander (1 : ℝ) (1 : ℝ) (2 : ℕ) K22)
    ∧ ∀ γ : ℝ, (γ ∈ Set.Ioc 0 1) → ¬ (spectralExpander γ K22) := by
  constructor
  · unfold vertexExpander
    intro s hs
    by_cases h₀ : #s = 0
    · aesop
    · by_cases h₁ : #s = 1
      · have :  2 * (#s : ℝ) = 2 := by aesop
        rw [this]
        have : #(K22.neighbourhoodOfSet s) = 2 :=
          K22_neighbour_of_set_card_one_has_card_one s h₁
        aesop
      · have : 1 < #s := by
          have : 0 ≤ #s := Nat.zero_le #s
          omega
        aesop
  · constructor
    · unfold edgeExpander MultiDiGraph.cut
      simp only [Nat.one_lt_cast, one_mul, mem_sdiff]
      intro s hs
      by_cases h₀ : #s = 0
      · aesop
      · by_cases h₁ : #s = 1
        · rw [h₁]
          have : #({e ∈ K22.edges | (K22.3 e).1 ∈ s ∧
              (K22.3 e).2 ∈ K22.vertices ∧ (K22.3 e).2 ∉ s}) = 2 :=
            K22_edges_of_cut_card_two s h₁
          rw [this]
          aesop
        · have : 1 < #s := by
            have : 0 ≤ #s := Nat.zero_le #s
            omega
          aesop
    · unfold spectralExpander
      have : K22.SpectralGap = 0 := K22_SpectralGap_eq_zero
      rw [this]
      aesop


--#lint
