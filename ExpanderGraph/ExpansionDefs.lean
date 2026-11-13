/-
Copyright (c) 2025-2026 Steven Herbert. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Steven Herbert
-/
import Mathlib

import ExpanderGraph.CollisionProb
import ExpanderGraph.MultiDiGraph
import ExpanderGraph.ProbabilityVector

/-!
# ExpansionDefs

This file formalises the three principal definitions of graph expansion, along with some useful
API theorems.

## Main definitions

* `vertexExpander`
* `edgeExpander`
* `spectralExpander`

-/

open CollisionProb
open MultiDiGraphSpace
open Finset
open ProbabilityVector

namespace ExpansionDefs

variable {V E : Type*}

/-- Definition of vertex expansion. That `V` is Fintype not needed in the definition,
    but in practice `V` will be a Fintype for envisaged applications -/
def vertexExpander [DecidableEq V] (K : ℝ) (A : ℝ) (G : MultiDiGraph V E ) : Prop :=
  ∀ s : Finset V, s ⊆  G.vertices →
       (A * #s ≤ #(MultiDiGraph.neighbourhoodOfSet G s)) ∨ K < #s

/-- If a graph is a `(K, A)` spectral expander, it is also so for any smaller value of `A` -/
theorem smallerAvertexExpander [DecidableEq V]
    (K : ℝ) (A₁ : ℝ) (A₂ : ℝ) (hA : A₂ ≤ A₁) (G : MultiDiGraph V E ) :
    vertexExpander K A₁ G → vertexExpander K A₂ G := by
  intro h1
  have h2 : ∀ s : Finset V, s ⊆  G.vertices →
      (A₁ * (#s : ℝ) ≤ (#(G.neighbourhoodOfSet s) : ℝ ) ∨ K < (#s : ℝ)) := by exact h1
  have h3 : ∀ s : Finset V, A₂ * (#s : ℝ) ≤ A₁ * (#s : ℝ) := by
    intro s
    exact mul_le_mul_of_nonneg_right hA (Nat.cast_nonneg s.card)
  intro s hs
  specialize h2 s hs
  specialize h3 s
  have h4 : A₂ * (#s : ℝ) ≤ A₁ * (#s : ℝ) := by aesop
  have h5 : A₁ * (#s : ℝ)  ≤ (#(G.neighbourhoodOfSet s) : ℝ)
      → A₂ * (#s : ℝ)  ≤ (#(G.neighbourhoodOfSet s) : ℝ) := by
    intro h51
    exact le_trans h4 h51
  aesop

/-- Definition of edge expansion: only valid for regular graphs. That `V` is a Fintype
    not needed in the definition, but in practice `V` will be a Fintype for envisaged applications.
    `r` is intended to be the regular degree of the graph, and that property should be assumed
    when using this definition -/
def edgeExpander [DecidableEq V] (K : ℝ) (ε : ℝ) (r : ℕ) (G : MultiDiGraph V E ) : Prop :=
  ∀ s : Finset V, s ⊆  G.vertices →
      (K < #s) ∨ (( ε * (#s : ℝ) * (r)) ≤ #(G.cut s))

/-- Definition of spectral expansion : only valid for regular graphs -/
def spectralExpander [Fintype V] [DecidableEq V] (γ : ℝ) (G : MultiDiGraph V E ) :
    Prop := γ ≤ G.SpectralGap

/-- If a graph is a spectral expander for some `γ`,
then it is also so for all smaller values of `γ`-/
theorem smallerGammaSpectralExpander [Fintype V] [DecidableEq V]
    (γ₁ : ℝ) (γ₂ : ℝ) (hγ : γ₂ ≤ γ₁) (G : MultiDiGraph V E ) :
    spectralExpander γ₁ G → spectralExpander γ₂ G := by
  intro hγ
  have h₁ : γ₁ ≤ G.SpectralGap := by exact hγ
  have h₂ : γ₂ ≤ G.SpectralGap := by linarith
  aesop

#lint
