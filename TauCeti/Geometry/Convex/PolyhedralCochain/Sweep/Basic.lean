/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Convex.PolyhedralCochain.Basic
public import TauCeti.Analysis.Convex.Polyhedron.Rational.Sweep
public import TauCeti.Analysis.Convex.Sweep.Basic
public import TauCeti.Analysis.Convex.Recession.Basic
public import TauCeti.LinearAlgebra.Alternating.Contraction

/-!
# Transverse sweeps of oriented cells

An oriented cell transverse to a lattice vector sweeps to an oriented cell of
one lower codimension. Its orientation is the contraction of the original
conormal orientation, with the sweeping vector inserted first. The swept cell
is strictly outgoing, and reversal of the original orientation reverses the
swept orientation. These are the generator operations for sweeping polyhedral
cochains.

The support and dimension calculations use `Set.sweep ℝ` and
`Set.finrank_vectorSpan_sweep`. Rationality uses
`IsRationalNormalPolyhedron.sweep`; the orientation uses
`Module.Ray.contract`. This file concerns generators; descent through
subdivision relations is a further step.

## Attribution

Adapted from `Mei/Geometry/Convex/PolyhedralCochain/Sweep/Basic.lean` in
[yuma-mizuno-lean/Mei](https://github.com/yuma-mizuno-lean/Mei), commit
`9cf969cdee9748087aae45dbf4888a130890655c` (Apache 2.0).
Original author: Codex; original copyright: Mei contributors.
-/

public section

open Module

noncomputable section

namespace TauCeti.OrientedCell

variable {N V : Type*} [AddCommGroup N] [NormedAddCommGroup V] [NormedSpace ℝ V]
  {i : N →+ V} {h : TauCeti.Toric.IsIntegralLattice i} {k : ℕ}

/-- Sweep an oriented cell along a transverse lattice vector. Contract its
conormal orientation by the positive sweeping vector, although its support
extends in the negative direction. -/
def sweep (σ : OrientedCell h (k + 1)) (n : N)
    (hn : i n ∉ (affineSpan ℝ σ.carrier).direction) : OrientedCell h k := by
  have := h.finiteDimensional
  refine
    { carrier := Set.sweep ℝ σ.carrier (i n)
      rational := σ.rational.sweep n
      nonempty := σ.nonempty.sweep (i n)
      finrank_direction_add := ?_
      orientation := σ.orientation.contract σ.isConormal σ.finrank_quotient_direction (i n) hn
      isConormal := ?_ }
  · rw [direction_affineSpan, Set.finrank_vectorSpan_sweep σ.nonempty
      (by simpa [direction_affineSpan] using hn)]
    have := σ.finrank_direction_add
    rw [direction_affineSpan] at this
    omega
  · simpa only [direction_affineSpan, Set.vectorSpan_sweep σ.nonempty] using
      σ.orientation.isConormal_contract σ.isConormal σ.finrank_quotient_direction (i n) hn

/-- The support of an oriented sweep is the negative-ray sweep of its support. -/
@[simp]
theorem sweep_carrier (σ : OrientedCell h (k + 1)) (n : N)
    (hn : i n ∉ (affineSpan ℝ σ.carrier).direction) :
    (σ.sweep n hn).carrier = Set.sweep ℝ σ.carrier (i n) := (rfl)

/-- The orientation of the swept cell is obtained by conormal contraction. -/
@[simp]
theorem sweep_orientation (σ : OrientedCell h (k + 1)) (n : N)
    (hn : i n ∉ (affineSpan ℝ σ.carrier).direction) :
    (σ.sweep n hn).orientation =
      σ.orientation.contract σ.isConormal σ.finrank_quotient_direction (i n) hn := (rfl)

/-- The positive sweeping vector is not a recession direction of the swept cell. -/
theorem sweep_strictlyOutgoing (σ : OrientedCell h (k + 1)) (n : N)
    (hn : i n ∉ (affineSpan ℝ σ.carrier).direction) :
    i n ∉ Set.recessionCone ℝ (σ.sweep n hn).carrier := by
  rw [sweep_carrier]
  exact Set.notMem_recessionCone_sweep σ.nonempty (by simpa [direction_affineSpan] using hn)

/-- Reversing the input orientation reverses the swept cell. -/
@[simp]
theorem sweep_reverse (σ : OrientedCell h (k + 1)) (n : N)
    (hn : i n ∉ (affineSpan ℝ σ.carrier).direction) :
    σ.reverse.sweep n (by simpa using hn) = (σ.sweep n hn).reverse := by
  ext1
  · simp
  · simp only [sweep_orientation, reverse_orientation, reverse_carrier]
    exact Module.Ray.contract_neg σ.orientation σ.isConormal
      σ.finrank_quotient_direction (i n) hn

end TauCeti.OrientedCell
