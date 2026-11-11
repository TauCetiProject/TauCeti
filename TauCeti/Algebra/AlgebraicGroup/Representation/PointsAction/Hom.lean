/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Representation.PointsAction.Basic
public import TauCeti.Algebra.Coalgebra.Subcomodule.Induced

/-!
# Functoriality of the base-point action in the comodule

Morphisms of right `H`-comodules intertwine the action `TauCeti.Comodule.basePointsRepresentation`
of base-valued points (`TauCeti.Comodule.Hom.comp_basePointsRepresentation` and
`TauCeti.Comodule.Hom.map_basePointsRepresentation`), as well as the scalar-extended automorphism
action `TauCeti.Comodule.pointsAction` (`TauCeti.Comodule.Hom.baseChange_pointsAction`). Applied
to the inclusion of a subcomodule over a flat Hopf algebra, the induced base-point action on the
subcomodule agrees with the ambient action (`TauCeti.Subcomodule.coe_basePointsRepresentation`).

## References

* W. C. Waterhouse, *Introduction to Affine Group Schemes*, §3.2.
* J. S. Milne, *Algebraic Groups* (2017), §4.a.
-/

public section

open scoped TensorProduct
open WithConv

namespace TauCeti

universe u v w x y

namespace Comodule.Hom

variable {R : Type u} {H : Type v} {M : Type w} {N : Type x} {A : Type y}
variable [CommSemiring R] [Semiring H] [HopfAlgebra R H]
variable [AddCommMonoid M] [Module R M] [Comodule R H M]
variable [AddCommMonoid N] [Module R N] [Comodule R H N]

/-- Scalar extension of a comodule morphism intertwines the group action `pointsAction`. -/
theorem baseChange_pointsAction [CommSemiring A] [Algebra R A]
    (f : Hom R H M N) (g : WithConv (H →ₐ[R] A)) (z : A ⊗[R] M) :
    f.toLinearMap.baseChange A (pointsAction M g z) =
      pointsAction N g (f.toLinearMap.baseChange A z) := by
  have h := LinearMap.congr_fun (baseChange_comp_endOfPoint f g.ofConv) z
  simpa only [LinearMap.comp_apply, ← LinearEquiv.coe_toLinearMap, pointsAction_toLinearMap] using h

/-- A comodule morphism intertwines the representations of base-valued points on its source and
target. -/
theorem comp_basePointsRepresentation (f : Hom R H M N) (g : WithConv (H →ₐ[R] R)) :
    f.toLinearMap ∘ₗ basePointsRepresentation (H := H) M g =
      basePointsRepresentation (H := H) N g ∘ₗ f.toLinearMap := by
  ext m
  have h := LinearMap.congr_fun (baseChange_comp_endOfPoint (A := R) f g.ofConv) (1 ⊗ₜ[R] m)
  simp only [LinearMap.comp_apply, LinearMap.baseChange_tmul, endOfPoint_tmul, one_smul,
    endOfPoint_one_tmul_eq_one_tmul_basePointsRepresentation] at h
  simpa using congrArg (TensorProduct.lid R N) h

/-- A comodule morphism commutes with the action of every base-valued point. -/
@[simp]
theorem map_basePointsRepresentation (f : Hom R H M N) (g : WithConv (H →ₐ[R] R)) (m : M) :
    f (basePointsRepresentation (H := H) M g m) = basePointsRepresentation (H := H) N g (f m) :=
  LinearMap.congr_fun (f.comp_basePointsRepresentation g) m

end Comodule.Hom

namespace Subcomodule

variable {R : Type u} {H : Type v} {M : Type w}
variable [CommSemiring R] [Semiring H] [HopfAlgebra R H] [Module.Flat R H]
variable [AddCommMonoid M] [Module R M] [Comodule R H M]

/-- Over a flat Hopf algebra, the base-point action on a subcomodule agrees with the ambient
base-point action upon coercion to the ambient module. -/
@[simp]
theorem coe_basePointsRepresentation (S : Subcomodule R H M)
    (g : WithConv (H →ₐ[R] R)) (x : S) :
    (Comodule.basePointsRepresentation (H := H) S g x : M) =
      Comodule.basePointsRepresentation (H := H) M g x := by
  simpa only [subtype_apply] using (S.subtype.map_basePointsRepresentation g x)

/-- Acting by a base-valued point on a bundled element of a subcomodule acts on its underlying
vector. -/
@[simp]
theorem basePointsRepresentation_mk (S : Subcomodule R H M)
    (g : WithConv (H →ₐ[R] R)) (m : M) (hm : m ∈ S) :
    Comodule.basePointsRepresentation (H := H) S g ⟨m, hm⟩ =
      ⟨Comodule.basePointsRepresentation (H := H) M g m,
        Comodule.basePointsRepresentation_mem S g hm⟩ :=
  Subtype.ext (S.coe_basePointsRepresentation g ⟨m, hm⟩)

end Subcomodule

end TauCeti
