/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Toric.Algebraic.DualSemigroup.Separation

/-!
# Integral supporting characters of faces

Every face of a lattice-rational cone in an integral lattice is cut out by an integral character
nonnegative on the cone. Regularity and salience are not required. This identifies the affine
toric chart of any face with a localization at a single monomial, and hence an open subscheme of
the chart of the cone.

The separation lemma
`TauCeti.Toric.exists_mem_dualSemigroup_neg_mem_dualSemigroup_inf_ker_eq` supplies these
supporting characters. The localization and open-immersion consequences are developed in
`TauCeti.Geometry.Toric.Algebraic.FaceLocalization`.

## Main declarations

* `TauCeti.Toric.IsLatticeRational.exists_mem_dualSemigroup_inf_ker_eq`: every face is cut out
  by an integral supporting character.

## References

* W. Fulton, *Introduction to Toric Varieties*, §§1.2–1.3.
* D. Cox, J. Little and H. Schenck, *Toric Varieties*, §§1.2–1.3.
-/

public section

namespace TauCeti.Toric

variable {N V : Type*} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {σ τ : PointedCone ℝ V}

/-- Every face `τ` of a lattice-rational cone `σ` in an integral lattice is cut out by a
character in the dual semigroup of `σ`: there is `m` with `σ ⊓ ker m = τ`. -/
theorem IsLatticeRational.exists_mem_dualSemigroup_inf_ker_eq (hi : IsIntegralLattice i)
    (hσ : IsLatticeRational i σ) (hτ : τ.IsFaceOf σ) :
    ∃ m ∈ dualSemigroup hi σ,
      σ ⊓ PointedCone.ofSubmodule (LinearMap.ker (hi.realCharacter m)) = τ := by
  have hστ : σ ⊓ τ = τ := inf_eq_right.mpr hτ.le
  obtain ⟨m, hm, -, hcut, -⟩ :=
    exists_mem_dualSemigroup_neg_mem_dualSemigroup_inf_ker_eq hi hσ
      (hσ.of_isFaceOf hτ) (hστ.symm ▸ hτ) (hστ.symm ▸ PointedCone.IsFaceOf.refl τ)
  exact ⟨m, hm, hcut.trans hστ⟩

end TauCeti.Toric
