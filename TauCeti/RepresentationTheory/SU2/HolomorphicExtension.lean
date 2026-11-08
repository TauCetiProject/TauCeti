/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.ClassicalGroups.Rational.Analytic
public import TauCeti.RepresentationTheory.SU2.Exhaustion
public import TauCeti.Geometry.Manifold.Instances.SpecialLinearGroup
public import TauCeti.LinearAlgebra.Matrix.ProjectiveSpecialLinearGroup.SpecialUnitary
import TauCeti.Topology.Algebra.Module.FiniteDimension

/-!
# Holomorphic extensions of the symmetric-power models

The continuous `SU(2)` model of degree `d` on `ℂ^{d+1}` is the restriction of a holomorphic
`SL₂(ℂ)` representation on that same space, extending further to `GL₂(ℂ)`. The extended action
takes values in the invertible continuous linear operators, carrying the native complex
Lie-group structure of units.

## Main declarations

* `TauCeti.SU2.symPowerSLHolomorphicExtension`: the native holomorphic `SL₂(ℂ)` action.
* `TauCeti.SU2.symPowerSLHolomorphicExtension_def`: restriction of the general-linear action.
* `TauCeti.SU2.symPowerSLHolomorphicExtension_apply`: its action in the weight basis.
* `TauCeti.SU2.toGL_comp_toSL`: the inclusion in `GL₂(ℂ)` factors through `SL₂(ℂ)`.
* `TauCeti.SU2.symPowerSLHolomorphicExtension_comp_toSL`: agreement with the `SU(2)` model.
* `TauCeti.SU2.contMDiff_symPowerSLHolomorphicExtension`: complex analyticity.
* `TauCeti.SU2.symPowerModelGL`: the algebraic `GL₂(ℂ)` action in the model's weight basis.
* `TauCeti.SU2.symPowerModelGL_apply`: its action on vectors.
* `TauCeti.SU2.isPolynomialRep_symPowerModelGL`: polynomiality of the algebraic model.
* `TauCeti.SU2.symPowerHolomorphicExtension`: the operator-valued `GL₂(ℂ)` homomorphism.
* `TauCeti.SU2.symPowerHolomorphicExtension_apply`: its action in the weight basis.
* `TauCeti.SU2.symPowerHolomorphicExtension_comp_toGL`: agreement with the `SU(2)` model.
* `TauCeti.SU2.contMDiff_symPowerHolomorphicExtension`: complex analyticity of the extension.

## References

* T. Bröcker and T. tom Dieck, *Representations of Compact Lie Groups*, Springer GTM 98 (1985),
  Chapter III, §8, Propositions (8.6)–(8.7), pp.154–155, for holomorphic extensions and the
  classical complexifications. Here the symmetric-power action extends to the larger group
  `GL₂(ℂ)`; its restriction to `SU(2)` is identified explicitly.
-/

public section

open Matrix Manifold
open scoped ContDiff Manifold Matrix.Norms.Operator
attribute [local instance] Matrix.linftyOpTopologicalSpace
noncomputable section
namespace TauCeti.SU2

variable (d : ℕ)

local notation "V" => EuclideanSpace ℂ (Fin (d + 1))

/-- The algebraic symmetric-power `GL₂(ℂ)` representation in the model's weight basis. -/
def symPowerModelGL : Representation ℂ (GL (Fin 2) ℂ) V :=
  ((weightEquiv d).conjRingEquiv.toMonoidHom).comp (symPowerRep ℂ 2 d)

/-- The algebraic model acts through the symmetric-power action and the weight equivalence. -/
@[simp]
theorem symPowerModelGL_apply (g : GL (Fin 2) ℂ) (v : V) :
    symPowerModelGL d g v =
      weightEquiv d (symPowerRep ℂ 2 d g ((weightEquiv d).symm v)) := by
  simp [symPowerModelGL, RingEquiv.toMonoidHom]

/-- The symmetric-power representation in the weight basis is polynomial. -/
@[simp]
theorem isPolynomialRep_symPowerModelGL : IsPolynomialRep (symPowerModelGL d) := by
  let F : Representation.IntertwiningMap (symPowerRep ℂ 2 d) (symPowerModelGL d) :=
    { toLinearMap := (weightEquiv d).toLinearMap
      isIntertwining' g := by
        ext v
        simp [symPowerModelGL_apply] }
  exact (isPolynomialRep_symPowerRep 2 d).of_surjective F (weightEquiv d).surjective

/-- The polynomial `GL₂(ℂ)` extension of the degree-`d` symmetric-power `SU(2)` model,
with values in the invertible continuous operators on `ℂ^{d+1}`. -/
def symPowerHolomorphicExtension :
    GL (Fin 2) ℂ →* (V →L[ℂ] V)ˣ :=
  ((Module.End.toContinuousLinearMap V).toMonoidHom.comp (symPowerModelGL d)).toHomUnits

/-- The extended action is the symmetric-power action in the weight basis. -/
@[simp]
theorem symPowerHolomorphicExtension_apply (g : GL (Fin 2) ℂ) (v : V) :
    (symPowerHolomorphicExtension d g : V →L[ℂ] V) v =
      weightEquiv d (symPowerRep ℂ 2 d g ((weightEquiv d).symm v)) := by
  simp [symPowerHolomorphicExtension, Module.End.toContinuousLinearMap_apply]

/-- Restricting the extension to `SU(2)` returns the original model action. -/
@[simp]
theorem symPowerHolomorphicExtension_comp_toGL :
    (symPowerHolomorphicExtension d).comp toGL = (symPowerModel d).toMonoidHom.toHomUnits := by
  ext g v
  simp only [MonoidHom.comp_apply, MonoidHom.coe_toHomUnits,
    ContRepresentation.toMonoidHom_apply,
    symPowerHolomorphicExtension_apply, symPowerModel_apply, symPower_apply]

/-- The symmetric-power extension is complex analytic as a homomorphism into invertible
continuous linear operators. -/
theorem contMDiff_symPowerHolomorphicExtension :
    ContMDiff 𝓘(ℂ, Matrix (Fin 2) (Fin 2) ℂ) 𝓘(ℂ, V →L[ℂ] V) ω
      (symPowerHolomorphicExtension d) := by
  exact (isPolynomialRep_symPowerModelGL d).isRationalRep.contMDiff_toHomUnits

/-- The degree-`d` symmetric-power representation of the native complex special linear group. -/
def symPowerSLHolomorphicExtension : SpecialLinearGroup (Fin 2) ℂ →* (V →L[ℂ] V)ˣ :=
  (symPowerHolomorphicExtension d).comp SpecialLinearGroup.toGL

/-- The special-linear action is the restriction of the general-linear action. -/
theorem symPowerSLHolomorphicExtension_def :
    symPowerSLHolomorphicExtension d =
      (symPowerHolomorphicExtension d).comp SpecialLinearGroup.toGL := (rfl)

/-- The special-linear extension acts by the symmetric power in the model's weight basis. -/
@[simp]
theorem symPowerSLHolomorphicExtension_apply (g : SpecialLinearGroup (Fin 2) ℂ) (v : V) :
    (symPowerSLHolomorphicExtension d g : V →L[ℂ] V) v =
      weightEquiv d (symPowerRep ℂ 2 d (SpecialLinearGroup.toGL g) ((weightEquiv d).symm v)) := by
  simp only [symPowerSLHolomorphicExtension_def, MonoidHom.comp_apply,
    symPowerHolomorphicExtension_apply]

/-- The inclusion of `SU(2)` in `GL₂(ℂ)` factors through `SL₂(ℂ)`. -/
@[simp]
theorem toGL_comp_toSL :
    (SpecialLinearGroup.toGL (n := Fin 2) (R := ℂ)).comp
      Matrix.specialUnitaryGroup.toSL = toGL := by
  ext g i j
  simp only [MonoidHom.comp_apply, SpecialLinearGroup.coe_GL_coe_matrix,
    Matrix.specialUnitaryGroup.coe_toSL, coe_toGL]

/-- Restricting the holomorphic special-linear action to `SU(2)` gives the original model. -/
@[simp]
theorem symPowerSLHolomorphicExtension_comp_toSL :
    (symPowerSLHolomorphicExtension d).comp Matrix.specialUnitaryGroup.toSL =
      (symPowerModel d).toMonoidHom.toHomUnits := by
  rw [symPowerSLHolomorphicExtension_def, MonoidHom.comp_assoc, toGL_comp_toSL,
    symPowerHolomorphicExtension_comp_toGL]

/-- The symmetric-power special-linear action is complex analytic. -/
theorem contMDiff_symPowerSLHolomorphicExtension :
    ContMDiff 𝓘(ℂ, SpecialLinearGroup.Model (Fin 2) ℂ) 𝓘(ℂ, V →L[ℂ] V) ω
      (symPowerSLHolomorphicExtension d) := by
  rw [symPowerSLHolomorphicExtension_def]
  exact (contMDiff_symPowerHolomorphicExtension d).comp SpecialLinearGroup.contMDiff_toGL

end TauCeti.SU2
