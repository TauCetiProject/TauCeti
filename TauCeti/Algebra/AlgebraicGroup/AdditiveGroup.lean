/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.RingTheory.Bialgebra.SymmetricAlgebra
import TauCeti.Algebra.AlgebraicGroup.FunctorOfPoints

/-!
# The additive group and the Hopf structure on a symmetric algebra

Mathlib equips `SymmetricAlgebra R M` with the cocommutative bialgebra structure in which each
generator `ι x` is primitive, `Δ(ι x) = ι x ⊗ 1 + 1 ⊗ ι x` and `ε(ι x) = 0`, but it stops short
of the antipode. Over a commutative ring `R` the symmetric algebra is a *Hopf* algebra: the
antipode is the algebra map sending each `ι x` to `-ι x`. This file supplies that antipode and
records the resulting affine group scheme.

The corresponding group scheme `Spec (SymmetricAlgebra R M)` is the **additive (vector) group**
on `M`. Its functor of points is computed here: for a commutative `R`-algebra `A`, the
convolution group of `R`-algebra maps `SymmetricAlgebra R M →ₐ[R] A` is the additive group of
`R`-linear maps `M →ₗ[R] A`, with convolution corresponding to addition. Taking `M = R`
recovers the one-dimensional additive group `𝔾ₐ = Spec R[X]`, whose `R`-points are `(A, +)`.

This is the worked example `𝔾ₐ` from the Tau Ceti reductive-groups roadmap
(`TauCetiRoadmap/ReductiveGroups/README.md`, "Worked examples" and Layer 0, "R-points as a
group"), in the same spirit as the multiplicative group `𝔾ₘ`. The antipode also fills a Layer 0
ingredient the roadmap calls for explicitly: a primitively generated Hopf algebra.

## Main declarations

* `TauCeti.AdditiveGroup.antipodeHom`: the antipode `ι x ↦ -ι x`, as an algebra map.
* `TauCeti.AdditiveGroup.instHopfAlgebra`: the Hopf algebra structure on `SymmetricAlgebra R M`
  over a commutative ring `R`.
* `TauCeti.AdditiveGroup.pointsMulEquiv`: the convolution group of points
  `SymmetricAlgebra R M →ₐ[R] A` is the additive group `M →ₗ[R] A`.

## References

The cocommutative bialgebra structure on the symmetric algebra is Robert Hawkins' Mathlib work
in `Mathlib.RingTheory.Bialgebra.SymmetricAlgebra`; the convolution group of points and the
antipode-driven inverse are Tau Ceti's `TauCeti.Algebra.AlgebraicGroup.FunctorOfPoints`, on top
of the Mathlib convolution monoid. The Hopf-algebra-from-an-antipode constructor
`HopfAlgebra.ofAlgHom` is from `Mathlib.RingTheory.HopfAlgebra.Basic`.
-/

open Coalgebra HopfAlgebra SymmetricAlgebra WithConv
open scoped TensorProduct

namespace TauCeti

namespace AdditiveGroup

universe u v w

section Hopf

variable (R : Type u) [CommRing R] (M : Type v) [AddCommMonoid M] [Module R M]

/-- The antipode of the symmetric-algebra Hopf algebra: the `R`-algebra map sending each
generator `ι x` to `-ι x`. -/
noncomputable def antipodeHom : SymmetricAlgebra R M →ₐ[R] SymmetricAlgebra R M :=
  SymmetricAlgebra.lift (-(ι R M))

@[simp]
theorem antipodeHom_ι (x : M) : antipodeHom R M (ι R M x) = -(ι R M x) := by
  simp [antipodeHom]

/-- The symmetric algebra over a commutative ring is a Hopf algebra: its antipode sends each
generator `ι x` to `-ι x`. -/
noncomputable instance instHopfAlgebra : HopfAlgebra R (SymmetricAlgebra R M) :=
  .ofAlgHom (antipodeHom R M)
    (by
      ext x
      simp [comul_ι, algebraMapInv_ι, Algebra.TensorProduct.lift_tmul])
    (by
      ext x
      simp [comul_ι, algebraMapInv_ι, Algebra.TensorProduct.lift_tmul])

@[simp]
theorem antipode_ι (x : M) : antipode R (ι R M x) = -(ι R M x) :=
  antipodeHom_ι R M x

end Hopf

section Points

variable {R : Type u} [CommRing R] {M : Type v} [AddCommMonoid M] [Module R M]
variable {A : Type w} [CommRing A] [Algebra R A]

/-- The inverse of the symmetric-algebra lift evaluates an algebra map at a generator: it sends
`H` to the linear map `x ↦ H (ι x)`. -/
theorem lift_symm_apply (H : SymmetricAlgebra R M →ₐ[R] A) (x : M) :
    SymmetricAlgebra.lift.symm H x = H (ι R M x) := by
  conv_rhs => rw [← Equiv.apply_symm_apply SymmetricAlgebra.lift H]
  rw [lift_ι_apply]

/-- The convolution product of two points of the additive group is, on each generator, the sum
of their values: `(F * G)(ι x) = F(ι x) + G(ι x)`. This is the additive group law. -/
theorem convMul_apply_ι (F G : WithConv (SymmetricAlgebra R M →ₐ[R] A)) (x : M) :
    (F * G).ofConv (ι R M x) = F.ofConv (ι R M x) + G.ofConv (ι R M x) := by
  simpa [comul_ι, Algebra.TensorProduct.lift_tmul] using AlgHom.convMul_apply F G (ι R M x)

/-- **The functor of points of the additive group.** For a commutative `R`-algebra `A`, the
convolution group of `R`-algebra maps out of `SymmetricAlgebra R M` is the additive group of
`R`-linear maps `M →ₗ[R] A`: a point `F` corresponds to the linear map `x ↦ F (ι x)`, and
convolution of points corresponds to addition of linear maps. -/
noncomputable def pointsMulEquiv :
    WithConv (SymmetricAlgebra R M →ₐ[R] A) ≃* Multiplicative (M →ₗ[R] A) where
  toFun F := Multiplicative.ofAdd (SymmetricAlgebra.lift.symm F.ofConv)
  invFun φ := toConv (SymmetricAlgebra.lift (Multiplicative.toAdd φ))
  left_inv F := by
    simp only [toAdd_ofAdd, Equiv.apply_symm_apply, toConv_ofConv]
  right_inv φ := by
    simp only [Equiv.symm_apply_apply, ofAdd_toAdd]
  map_mul' F G := by
    have h : SymmetricAlgebra.lift.symm (F * G).ofConv =
        SymmetricAlgebra.lift.symm F.ofConv + SymmetricAlgebra.lift.symm G.ofConv := by
      ext x
      rw [lift_symm_apply, convMul_apply_ι, LinearMap.add_apply, lift_symm_apply, lift_symm_apply]
    exact (congrArg Multiplicative.ofAdd h).trans (ofAdd_add _ _)

/-- A point of the additive group, as a linear map, is `x ↦ F (ι x)`. -/
@[simp]
theorem toAdd_pointsMulEquiv (F : WithConv (SymmetricAlgebra R M →ₐ[R] A)) :
    Multiplicative.toAdd (pointsMulEquiv F) = SymmetricAlgebra.lift.symm F.ofConv :=
  rfl

/-- The linear map underlying a point evaluates as `x ↦ F (ι x)`. -/
theorem toAdd_pointsMulEquiv_apply (F : WithConv (SymmetricAlgebra R M →ₐ[R] A)) (x : M) :
    Multiplicative.toAdd (pointsMulEquiv F) x = F.ofConv (ι R M x) :=
  lift_symm_apply F.ofConv x

/-- The inverse equivalence sends a linear map to the corresponding algebra map. -/
@[simp]
theorem pointsMulEquiv_symm_apply (φ : Multiplicative (M →ₗ[R] A)) :
    (pointsMulEquiv (R := R) (M := M) (A := A)).symm φ =
      toConv (SymmetricAlgebra.lift (Multiplicative.toAdd φ)) :=
  rfl

end Points

section Ga

variable {R : Type u} [CommRing R] {A : Type w} [CommRing A] [Algebra R A]

/-- **The one-dimensional additive group** `𝔾ₐ = Spec (SymmetricAlgebra R R)`. Specializing the
vector group to `M = R`, the convolution group of `R`-points is the additive group `(A, +)`. -/
noncomputable def gaPointsMulEquiv :
    WithConv (SymmetricAlgebra R R →ₐ[R] A) ≃* Multiplicative A :=
  pointsMulEquiv.trans
    (AddEquiv.toMultiplicative (LinearMap.ringLmapEquivSelf R R A).toAddEquiv)

/-- A point of `𝔾ₐ` is the additive group element obtained by evaluating it at the generator
`ι 1`. -/
theorem toAdd_gaPointsMulEquiv (F : WithConv (SymmetricAlgebra R R →ₐ[R] A)) :
    Multiplicative.toAdd (gaPointsMulEquiv F) = F.ofConv (ι R R 1) := by
  rw [gaPointsMulEquiv]
  simp [lift_symm_apply]

end Ga

end AdditiveGroup

end TauCeti
