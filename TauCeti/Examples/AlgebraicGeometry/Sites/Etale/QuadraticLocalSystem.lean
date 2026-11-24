/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Polynomial.Basic
public import Mathlib.FieldTheory.IsSepClosed
public import Mathlib.FieldTheory.KrullTopology
public import TauCeti.AlgebraicGeometry.FiniteEtale.Galois.ModuleSheaf
public import TauCeti.FieldTheory.Galois.Basic
public import TauCeti.FieldTheory.Galois.Complex

/-!
# A nonconstant finite lisse `ℤ/3` sheaf on `Spec ℝ`

The quadratic character of `Gal(ℂ/ℝ)`, through which complex conjugation acts by `-1`, makes
`ℤ/3` a representation of `Gal(ℂ/ℝ)` (`TauCeti.AlgebraicGeometry.signRepresentation`). The
corresponding étale sheaf of `ℤ/3`-modules on `Spec ℝ`
(`TauCeti.AlgebraicGeometry.quadraticLocalSystem`, an instance of
`TauCeti.FiniteEtaleScheme.galoisModuleSheaf`) is finite lisse, because the cover
`Spec ℂ ⟶ Spec ℝ` is finite étale and surjective. It is not constant
(`TauCeti.FiniteEtaleScheme.not_isConstant_galoisModuleSheaf`): its sections over `Spec ℝ`
vanish, since a vector fixed by complex conjugation equals its negative and `2` is invertible in
`ℤ/3`, so a constant such sheaf would be zero, while it is nonzero.

This is a Check of EtaleCohomologyFoundations §F.0.1 in TauCetiRoadmap: on `Spec ℝ`, the quadratic
character yields a nonconstant rank-one `ℤ/3` local system. The identification of its stalk at
`Spec ℂ` with `ℤ/3`, on which complex conjugation acts by `-1`, is not part of this file.

## Main results

* `TauCeti.AlgebraicGeometry.isFiniteLisse_quadraticLocalSystem`: the sheaf is finite lisse.
* `TauCeti.AlgebraicGeometry.not_isConstant_quadraticLocalSystem`: the sheaf is not constant.
-/

public section

open CategoryTheory Limits Opposite AlgebraicGeometry FintypeCatDiscrete Complex
  TauCeti.FiniteEtaleScheme ContAction

namespace TauCeti.AlgebraicGeometry

private theorem conjAe_ne_one : (conjAe : Gal(ℂ/ℝ)) ≠ 1 := fun h ↦ by
  have := congrArg (· I) h
  norm_num [Complex.ext_iff] at this

/-- The quadratic character of `Gal(ℂ/ℝ)` as a representation on `ℤ/3`: the identity acts
trivially and complex conjugation acts by `-1`. -/
noncomputable def signRepresentation : Representation (ZMod 3) Gal(ℂ/ℝ) (ZMod 3) :=
  (DistribMulAction.toModuleEnd (ZMod 3) (ZMod 3)).comp
    (Algebra.IsQuadraticExtension.quadraticCharacter ℝ ℂ)

/-- Complex conjugation acts on `signRepresentation` by `-1`. -/
theorem signRepresentation_conjAe (m : ZMod 3) : signRepresentation conjAe m = -m := by
  simp [signRepresentation,
    (Algebra.IsQuadraticExtension.quadraticCharacter_eq_neg_one_iff ℝ ℂ).2 conjAe_ne_one]

/-- The étale sheaf of `ℤ/3`-modules on `Spec ℝ` given by the quadratic character of
`Gal(ℂ/ℝ)`. -/
noncomputable def quadraticLocalSystem :
    Sheaf (Scheme.smallEtaleTopology (Spec (.of ℝ))) (ModuleCat.{0} (ZMod 3)) :=
  galoisModuleSheaf ℝ ℂ signRepresentation

/-- **The quadratic local system is finite lisse.** It becomes constant on the finite étale
cover `Spec ℂ ⟶ Spec ℝ`. -/
theorem isFiniteLisse_quadraticLocalSystem : quadraticLocalSystem.IsFiniteLisse :=
  isFiniteLisse_galoisModuleSheaf ℝ ℂ _

/-- No nonzero element of `ℤ/3` is fixed by `signRepresentation`: a fixed element equals its
negative, and `2` is invertible in `ℤ/3`. -/
theorem eq_zero_of_forall_signRepresentation_eq (m : ZMod 3)
    (h : ∀ σ : Gal(ℂ/ℝ), signRepresentation σ m = m) : m = 0 := by
  have key : ∀ a : ZMod 3, -a = a → a = 0 := by decide
  exact key m ((signRepresentation_conjAe m).symm.trans (h conjAe))

/-- **The quadratic local system is not constant.** It has no nonzero sections over `Spec ℝ`,
since `signRepresentation` has no nonzero fixed vector, but it is nonzero. -/
theorem not_isConstant_quadraticLocalSystem :
    ¬ quadraticLocalSystem.IsConstant (Scheme.smallEtaleTopology (Spec (.of ℝ))) :=
  not_isConstant_galoisModuleSheaf _ eq_zero_of_forall_signRepresentation_eq

end TauCeti.AlgebraicGeometry
