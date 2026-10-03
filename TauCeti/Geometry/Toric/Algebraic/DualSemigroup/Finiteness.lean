/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import TauCeti.Algebra.Group.Submonoid.Finiteness
public import TauCeti.Geometry.Toric.Algebraic.DualSemigroup.Basic
public import TauCeti.Geometry.Toric.Algebraic.Cone.Basic
import Mathlib.LinearAlgebra.Dual.Basis

/-!
# Gordan's lemma for dual semigroups

The integral characters nonnegative on a lattice-rational cone form a finitely generated
additive monoid. Neither salience nor regularity is needed. This gives finite monomial
generating families for the coordinate rings of arbitrary affine toric cones.

A finite lattice generating family for the cone identifies its dual semigroup with the preimage
of the nonnegative integer vectors under evaluation. The character lattice is finitely generated,
and `AddSubmonoid.FG.comap` proves finite generation of this preimage using natural slack
variables and Mathlib's equalizer form of Gordan's lemma.

## Main declarations

* `TauCeti.Toric.IsLatticeRational.fg_dualSemigroup`: Gordan's lemma without salience.
* `TauCeti.Toric.IsToricCone.fg_dualSemigroup`: the dual semigroup of every toric cone is
  finitely generated.

## References

* W. Fulton, *Introduction to Toric Varieties*, §1.2, Proposition 1.
* D. Cox, J. Little and H. Schenck, *Toric Varieties*, §1.2, Proposition 1.2.17.
-/

public section

namespace TauCeti.Toric

variable {N V : Type*} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {σ : PointedCone ℝ V}

/-- **Gordan's lemma.** The dual semigroup of a lattice-rational cone in an integral lattice is
finitely generated. Salience is not required. -/
theorem IsLatticeRational.fg_dualSemigroup (hσ : IsLatticeRational i σ)
    (hi : IsIntegralLattice i) : AddMonoid.FG (dualSemigroup hi σ) := by
  apply (AddMonoid.fg_iff_addSubmonoid_fg _).mpr
  classical
  have := hi.free
  have := hi.finite
  let b := Module.Free.chooseBasis ℤ N
  let e := (addMonoidHomLequivInt ℤ).trans b.dualBasis.equivFun
  have : AddMonoid.FG (N →+ ℤ) := (isAddFG_congr e.toAddEquiv).mpr inferInstance
  obtain ⟨s, rfl⟩ := isLatticeRational_iff.mp hσ
  let c : (s → ℕ) →+ (s → ℤ) := (Nat.castAddMonoidHom ℤ).compLeft s
  let ev : (N →+ ℤ) →+ (s → ℤ) :=
    AddMonoidHom.pi fun a ↦ AddMonoidHom.eval a.val
  have hfg : ((AddMonoidHom.mrange c).comap ev).FG := by
    rw [AddMonoidHom.mrange_eq_map]
    exact (AddMonoid.FG.fg_top (M := s → ℕ)).map c |>.comap ev
  have heq : (AddMonoidHom.mrange c).comap ev = dualSemigroup hi (PointedCone.hull ℝ (i '' s)) := by
    ext m
    rw [AddSubmonoid.mem_comap, AddMonoidHom.mem_mrange, mem_dualSemigroup_hull_image]
    constructor
    · rintro ⟨a, ha⟩ n hn
      have h : (a ⟨n, hn⟩ : ℤ) = m n := congrFun ha ⟨n, hn⟩
      exact h ▸ Int.natCast_nonneg (a ⟨n, hn⟩)
    · intro hm
      refine ⟨fun a ↦ (m a).toNat, ?_⟩
      funext a
      exact Int.toNat_of_nonneg (hm a a.2)
  exact heq ▸ hfg

/-- The dual semigroup of every toric cone in an integral lattice is finitely generated. -/
theorem IsToricCone.fg_dualSemigroup (hσ : IsToricCone i σ) (hi : IsIntegralLattice i) :
    AddMonoid.FG (dualSemigroup hi σ) :=
  hσ.rational.fg_dualSemigroup hi

end TauCeti.Toric
