/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Data.Fintype.Prod
public import Mathlib.GroupTheory.Perm.Support
public import TauCeti.Combinatorics.Hypergraph.Complex.TwoComplex
public import TauCeti.GroupTheory.Perm.MovedNorm

/-!
# Coboundary expansion with group coefficients: the basic definitions

Group-valued 1-cochains `Cochain X G` on a finite two-complex, with their triangle defect, gauge
cost and gauge distance, and the first coboundary Cheeger constant `h1` in the counting convention
together with its normalized form `h1Norm`. The carrier type `TauCeti.TwoComplex`, the complete
complex `TwoComplex.complete`, the conversions to and from `HypergraphComplex 3`, both round
trips, and the complete face counts come from main
(`TauCeti.Combinatorics.Hypergraph.Complex.TwoComplex`, #27759). This file does not redefine them.
The Cochain / h1 pieces needed to state the Layer 8.1 results are defined here. The norm on
permutations is `Equiv.Perm.movedNorm` of `TauCeti.GroupTheory.Perm.MovedNorm`.

These are the definitions of Layers 2.1, 2.2 and 3.1/3.3 needed to state the Layer 8.1 results:
counting convention, gauge convention `β u⁻¹ * α u v * β v`, orientation `u < v < w`, and
infimum over cochains at positive gauge distance.
-/

-- These are the specification definitions; downstream files unfold them.
@[expose] public section

noncomputable section

open Finset

namespace TauCeti.CoboundaryExpansion

variable {V : Type*} [Fintype V] [LinearOrder V]
variable {G : Type*} [Group G]

/-- A `G`-valued 1-cochain: a value on each oriented edge, inverted by reversing it. Values off
the edges are not constrained and are never read by `defect`, `cost`, or `gaugeDist`. -/
structure Cochain (X : TauCeti.TwoComplex V) (G : Type*) [Group G] where
  /-- The value on the oriented edge `(u, v)`. -/
  toFun : V → V → G
  /-- Reversing an edge inverts the value. -/
  inv_symm : ∀ u v, ({u, v} : Finset V) ∈ X.edges → toFun v u = (toFun u v)⁻¹

namespace Cochain

variable {X : TauCeti.TwoComplex V}

/-- The triangle defect `N`: the norm of the holonomy `α u v * α v w * α w u`, summed over the
triangles, each read in increasing order `u < v < w`. -/
def defect (ℓ : GroupNorm G) (α : Cochain X G) : ℝ :=
  ∑ p ∈ univ.filter (fun p : V × V × V =>
      p.1 < p.2.1 ∧ p.2.1 < p.2.2 ∧ ({p.1, p.2.1, p.2.2} : Finset V) ∈ X.triangles),
    ℓ (α.toFun p.1 p.2.1 * α.toFun p.2.1 p.2.2 * α.toFun p.2.2 p.1)

/-- The cost of a gauge `β`: the norm of `β u⁻¹ * α u v * β v`, summed over edges `u < v`. -/
def cost (ℓ : GroupNorm G) (α : Cochain X G) (β : V → G) : ℝ :=
  ∑ p ∈ univ.filter (fun p : V × V => p.1 < p.2 ∧ ({p.1, p.2} : Finset V) ∈ X.edges),
    ℓ ((β p.1)⁻¹ * α.toFun p.1 p.2 * β p.2)

/-- The gauge distance `D`: the infimum of the cost over all gauges. -/
def gaugeDist (ℓ : GroupNorm G) (α : Cochain X G) : ℝ :=
  ⨅ β : V → G, α.cost ℓ β

end Cochain

/-- The first coboundary Cheeger constant in the counting convention: the infimum of `N / D`
over cochains at positive gauge distance. -/
def h1 (X : TauCeti.TwoComplex V) (ℓ : GroupNorm G) : ℝ :=
  sInf {r : ℝ | ∃ α : Cochain X G, 0 < α.gaugeDist ℓ ∧ r = α.defect ℓ / α.gaugeDist ℓ}

/-- The Cheeger constant in the normalized convention: `h1` rescaled by the ratio of the number
of edges to the number of triangles. With Lean's `x / 0 = 0` this is `0` when `X` has no
triangle; the theorems use it only for `card V ≥ 3`. -/
def h1Norm (X : TauCeti.TwoComplex V) (ℓ : GroupNorm G) : ℝ :=
  (X.edges.card / X.triangles.card : ℝ) * h1 X ℓ

end TauCeti.CoboundaryExpansion
