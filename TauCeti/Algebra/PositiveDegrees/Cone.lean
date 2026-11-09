/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.PositiveDegrees.FinitelyGenerated
public import TauCeti.Geometry.Toric.Algebraic.Cone.Finiteness

/-!
# Positive degrees on lattice points of rational cones

A lattice-rational cone equipped with an integral functional strictly positive on its nonzero
lattice points defines positive degree data on the lattice. Gordan's lemma
`TauCeti.Toric.IsLatticeRational.fg_comap_toAddSubmonoid` supplies finite generation of the
lattice-point monoid, and `TauCeti.PositiveDegrees.ofFG` turns the positivity of the functional
into finite cutoffs. No separate salience hypothesis is needed; salience is a consequence
(`TauCeti.Toric.IsLatticeRational.salient_of_forall_pos`).

Adapted from `Mei/Algebra/PositiveDegrees/Cone.lean` in
[yuma-mizuno-lean/Mei](https://github.com/yuma-mizuno-lean/Mei), commit
`3d2e9c869ee44c41ae9c7b5c6e2042898430d0ca`, released under Apache 2.0.
-/

public section

namespace TauCeti.PositiveDegrees

open TauCeti.Toric

variable {N V : Type*} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {σ : PointedCone ℝ V}

/-- The lattice points of a lattice-rational cone, graded by an integral functional strictly
positive on its nonzero lattice points. The finite cutoffs are consequences of the hypotheses,
rather than additional input. -/
def ofCone (hσ : IsLatticeRational i σ) (hi : IsIntegralLattice i) (δ : N →+ ℤ)
    (hδ : ∀ {n}, i n ∈ σ → n ≠ 0 → 0 < δ n) : PositiveDegrees N :=
  ofFG (hσ.fg_comap_toAddSubmonoid hi) δ hδ

/-- The allowed degrees are exactly the lattice points of the cone. -/
@[simp]
theorem ofCone_monoid (hσ : IsLatticeRational i σ) (hi : IsIntegralLattice i) (δ : N →+ ℤ)
    (hδ : ∀ {n}, i n ∈ σ → n ≠ 0 → 0 < δ n) :
    (ofCone hσ hi δ hδ).monoid = σ.toAddSubmonoid.comap i :=
  ofFG_monoid _ _ _

/-- The cone construction retains the prescribed integral functional. -/
@[simp]
theorem ofCone_degree (hσ : IsLatticeRational i σ) (hi : IsIntegralLattice i) (δ : N →+ ℤ)
    (hδ : ∀ {n}, i n ∈ σ → n ≠ 0 → 0 < δ n) :
    (ofCone hσ hi δ hδ).degree = δ :=
  ofFG_degree _ _ _

end TauCeti.PositiveDegrees
