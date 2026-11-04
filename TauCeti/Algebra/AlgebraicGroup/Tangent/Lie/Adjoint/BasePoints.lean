/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Lie.Sl2
public import TauCeti.Algebra.AlgebraicGroup.Tangent.Lie.Adjoint.Cotangent
import TauCeti.Algebra.Lie.Sl2.Basic

/-!
# Base-valued rational points act by Lie automorphisms on the tangent Lie algebra

For a commutative Hopf algebra `H` over `R` with finite projective augmentation cotangent space,
`Derivation.adjointLieEquiv` gives the Lie-automorphism action of `A`-valued points on the scalar
extension `A ⊗[R] Lie(G)` for `A : CommAlgCat.{max u v} R`. Specializing along `R → ULift R` and
contracting the scalar factor shows that every base-valued point `g : WithConv (H →ₐ[R] R)` acts
directly on the unextended Lie algebra `Module.Dual R (Bialgebra.CotangentSpace R H)` by a Lie
algebra automorphism (`Derivation.basePointsAdjointLieEquiv`), with `R` and `H` in independent
universes. Consequently, base-valued points carry `sl₂` triples in `Lie(G)` to `sl₂` triples
(`IsSl2Triple.basePointsRepresentation_adjointComodule`).

## Main declarations

* `Derivation.basePointsRepresentation_adjointComodule_bracket`: `basePointsRepresentation` of the
  adjoint comodule preserves the Lie bracket.
* `Derivation.basePointsAdjointLieEquiv`: the Lie algebra automorphism of
  `Module.Dual R (Bialgebra.CotangentSpace R H)` attached to a base-valued point.
* `IsSl2Triple.basePointsRepresentation_adjointComodule`: the base-point adjoint action carries
  `sl₂` triples to `sl₂` triples.

## References

* J. S. Milne, *Algebraic Groups* (2017), §10.a and item 10.20.
-/

public section

open scoped TensorProduct
open WithConv

namespace Derivation

open TauCeti

universe u v

variable {R : Type u} {H : Type v} [CommRing R] [CommRing H] [HopfAlgebra R H]
variable [Module.Finite R (Bialgebra.CotangentSpace R H)]
variable [Module.Projective R (Bialgebra.CotangentSpace R H)]

/-- The representation of base-valued points on the cotangent-dual Lie algebra preserves the Lie
bracket. -/
@[simp]
theorem basePointsRepresentation_adjointComodule_bracket
    (g : WithConv (H →ₐ[R] R))
    (x y : Module.Dual R (Bialgebra.CotangentSpace R H)) :
    letI := adjointComodule (R := R) (H := H)
    Comodule.basePointsRepresentation (Module.Dual R (Bialgebra.CotangentSpace R H)) g ⁅x, y⁆ =
      ⁅Comodule.basePointsRepresentation (Module.Dual R (Bialgebra.CotangentSpace R H)) g x,
        Comodule.basePointsRepresentation (Module.Dual R (Bialgebra.CotangentSpace R H)) g y⁆ := by
  let := adjointComodule (R := R) (H := H)
  let A : CommAlgCat.{max u v} R := CommAlgCat.of R (ULift.{max u v} R)
  let g' : HopfAlgebra.points (H := H) A := AlgHom.mapValue (Algebra.ofId R A) g
  have hbr := endOfPoint_adjointComodule_bracket A g'
    ((1 : A) ⊗ₜ[R] x) ((1 : A) ⊗ₜ[R] y)
  simp only [LieAlgebra.ExtendScalars.bracket_tmul, one_mul, g',
    Comodule.endOfPoint_mapValue_algebraOfId_tmul] at hbr
  have hproj := congrArg
    ((TensorProduct.lid R (Module.Dual R (Bialgebra.CotangentSpace R H))).toLinearMap.comp
      ((ULift.algEquiv (R := R) (A := R)).toLinearMap.rTensor
        (Module.Dual R (Bialgebra.CotangentSpace R H)))) hbr
  simpa using hproj

/-- Every base-valued point acts on the cotangent-dual Lie algebra by a Lie algebra automorphism. -/
noncomputable def basePointsAdjointLieEquiv (g : WithConv (H →ₐ[R] R)) :
    LieEquiv R (Module.Dual R (Bialgebra.CotangentSpace R H))
      (Module.Dual R (Bialgebra.CotangentSpace R H)) :=
  letI := adjointComodule (R := R) (H := H)
  { toFun := Comodule.basePointsRepresentation (Module.Dual R (Bialgebra.CotangentSpace R H)) g
    invFun := Comodule.basePointsRepresentation (Module.Dual R (Bialgebra.CotangentSpace R H)) g⁻¹
    map_add' := (Comodule.basePointsRepresentation _ g).map_add'
    map_smul' := (Comodule.basePointsRepresentation _ g).map_smul'
    map_lie' := fun {x y} ↦ basePointsRepresentation_adjointComodule_bracket g x y
    left_inv := fun x ↦ by
      rw [← mul_apply_eq_comp, ← map_mul, inv_mul_cancel, map_one, one_apply_eq_self]
    right_inv := fun x ↦ by
      rw [← mul_apply_eq_comp, ← map_mul, mul_inv_cancel, map_one, one_apply_eq_self] }

/-- `Derivation.basePointsAdjointLieEquiv` acts by `Comodule.basePointsRepresentation` of the
adjoint comodule. -/
@[simp]
theorem basePointsAdjointLieEquiv_apply (g : WithConv (H →ₐ[R] R))
    (x : Module.Dual R (Bialgebra.CotangentSpace R H)) :
    letI := adjointComodule (R := R) (H := H)
    basePointsAdjointLieEquiv (R := R) (H := H) g x =
      Comodule.basePointsRepresentation (Module.Dual R (Bialgebra.CotangentSpace R H)) g x := by
  let := adjointComodule (R := R) (H := H)
  rfl

/-- The underlying linear map of `Derivation.basePointsAdjointLieEquiv` is the base-point action of
the adjoint comodule. -/
@[simp]
theorem basePointsAdjointLieEquiv_toLinearMap (g : WithConv (H →ₐ[R] R)) :
    letI := adjointComodule (R := R) (H := H)
    (basePointsAdjointLieEquiv (R := R) (H := H) g).toLinearMap =
      Comodule.basePointsRepresentation (Module.Dual R (Bialgebra.CotangentSpace R H)) g := by
  let := adjointComodule (R := R) (H := H)
  exact LinearMap.ext fun x ↦ basePointsAdjointLieEquiv_apply g x

/-- The identity point acts as the identity Lie automorphism. -/
@[simp]
theorem basePointsAdjointLieEquiv_one :
    basePointsAdjointLieEquiv (R := R) (H := H) 1 = 1 := by
  let := adjointComodule (R := R) (H := H)
  refine LieEquiv.ext fun x ↦ ?_
  simp [one_apply_eq_self]

/-- Convolution multiplication of base-valued points corresponds to composition of their adjoint
Lie automorphisms. -/
@[simp]
theorem basePointsAdjointLieEquiv_mul (g h : WithConv (H →ₐ[R] R)) :
    basePointsAdjointLieEquiv (R := R) (H := H) (g * h) =
      (basePointsAdjointLieEquiv (R := R) (H := H) h).trans
        (basePointsAdjointLieEquiv (R := R) (H := H) g) := by
  let := adjointComodule (R := R) (H := H)
  refine LieEquiv.ext fun x ↦ ?_
  simp [mul_apply_eq_comp]

/-- The inverse of the adjoint Lie automorphism of `g` is the automorphism of `g⁻¹`. -/
@[simp]
theorem basePointsAdjointLieEquiv_symm (g : WithConv (H →ₐ[R] R)) :
    (basePointsAdjointLieEquiv (R := R) (H := H) g).symm =
      basePointsAdjointLieEquiv (R := R) (H := H) g⁻¹ := by
  refine LieEquiv.ext fun x ↦ ?_
  apply (basePointsAdjointLieEquiv (R := R) (H := H) g).symm_apply_eq.mpr
  have h := congrArg
    (fun e : LieEquiv R (Module.Dual R (Bialgebra.CotangentSpace R H))
        (Module.Dual R (Bialgebra.CotangentSpace R H)) => e x)
    (basePointsAdjointLieEquiv_mul (R := R) (H := H) g g⁻¹)
  simpa only [mul_inv_cancel, basePointsAdjointLieEquiv_one, one_apply_eq_self,
    LieEquiv.trans_apply] using h

end Derivation

namespace IsSl2Triple

open TauCeti

universe u v

variable {R : Type u} {H : Type v} [CommRing R] [CommRing H] [HopfAlgebra R H]
variable [Module.Finite R (Bialgebra.CotangentSpace R H)]
variable [Module.Projective R (Bialgebra.CotangentSpace R H)]

/-- Acting by a base-valued point under the adjoint representation carries an `sl₂` triple in the
tangent Lie algebra to an `sl₂` triple. -/
theorem basePointsRepresentation_adjointComodule
    {h e f : Module.Dual R (Bialgebra.CotangentSpace R H)} (t : IsSl2Triple h e f)
    (g : WithConv (H →ₐ[R] R)) :
    letI := Derivation.adjointComodule (R := R) (H := H)
    IsSl2Triple
      (Comodule.basePointsRepresentation (Module.Dual R (Bialgebra.CotangentSpace R H)) g h)
      (Comodule.basePointsRepresentation (Module.Dual R (Bialgebra.CotangentSpace R H)) g e)
      (Comodule.basePointsRepresentation (Module.Dual R (Bialgebra.CotangentSpace R H)) g f) := by
  let := Derivation.adjointComodule (R := R) (H := H)
  let φ := Derivation.basePointsAdjointLieEquiv (R := R) (H := H) g
  simpa only [φ, LieEquiv.coe_toLieHom, Derivation.basePointsAdjointLieEquiv_apply] using
    t.map (φ : _ →ₗ⁅R⁆ _) fun hh ↦ t.h_ne_zero (φ.injective (hh.trans (map_zero φ).symm))

end IsSl2Triple
