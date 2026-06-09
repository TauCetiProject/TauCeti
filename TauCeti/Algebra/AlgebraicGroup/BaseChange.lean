/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Algebra.Category.Grp.Basic
import Mathlib.CategoryTheory.Iso
import Mathlib.RingTheory.Bialgebra.TensorProduct
import Mathlib.RingTheory.HopfAlgebra.TensorProduct
import TauCeti.Algebra.AlgebraicGroup.PointsFunctor

/-!
# Base change of bialgebra points

This file records that the usual algebraic base-change adjunction is compatible with the
convolution monoid structure on the functor of points of a bialgebra. For a bialgebra `A` over
`k`, a `k`-algebra `K`, and a commutative `K`-algebra `R`, the `R`-points of the base-changed
bialgebra `K ⊗[k] A` over `K` are the same as `k`-algebra maps `A →ₐ[k] R`, and this
identification is a monoid isomorphism for convolution. When `A` is a Hopf algebra, these are
the convolution groups of points.

This is the algebraic-group-facing form of the ReductiveGroups roadmap item "Base change.
`K ⊗[k] A` as a Hopf algebra over `K`"; it builds on Mathlib's tensor-product bialgebra
instance and `AlgHom.liftEquiv`.

## Main definitions

* `TauCeti.AlgHom.baseChangePointsMulEquiv`: the convolution monoid isomorphism between
  `A →ₐ[k] R` and `K ⊗[k] A →ₐ[K] R`.
* `TauCeti.HopfAlgebra.baseChangePointsIso`: the same equivalence, packaged as an
  isomorphism of the group-valued points of a Hopf algebra.

## References

The tensor-product bialgebra structure and algebra base-change adjunction used here are
from Mathlib, respectively `Mathlib.RingTheory.Bialgebra.TensorProduct` and
`AlgHom.liftEquiv`.
-/

open Coalgebra HopfAlgebra TensorProduct WithConv

namespace TauCeti

namespace AlgHom

variable {k K A R : Type*} [CommSemiring k] [CommSemiring K] [Semiring A]
  [CommSemiring R] [Algebra k K] [_root_.Bialgebra k A] [Algebra K R] [Algebra k R]
  [IsScalarTower k K R]

private lemma liftEquiv_map_mul
    (f g : WithConv (A →ₐ[k] R)) :
    AlgHom.liftEquiv k K A R
      (WithConv.ofConv (f * g)) =
    WithConv.ofConv
      ((WithConv.toConv (AlgHom.liftEquiv k K A R f.ofConv) *
        WithConv.toConv (AlgHom.liftEquiv k K A R g.ofConv)) :
          WithConv (K ⊗[k] A →ₐ[K] R)) := by
  ext a
  suffices
      (Algebra.TensorProduct.lift f.ofConv g.ofConv (fun _ _ => .all _ _))
        (Coalgebra.comul (R := k) a) =
      (Algebra.TensorProduct.lift (AlgHom.liftEquiv k K A R f.ofConv)
        (AlgHom.liftEquiv k K A R g.ofConv) (fun _ _ => .all _ _))
        ((AlgebraTensorModule.tensorTensorTensorComm k K k K K K A A)
          (1 ⊗ₜ[K] 1 ⊗ₜ[k] Coalgebra.comul (R := k) a)) by
    simpa only [AlgHom.coe_comp, AlgHom.coe_restrictScalars', Function.comp_apply,
      Algebra.TensorProduct.includeRight_apply, AlgHom.liftEquiv_tmul, one_smul,
      AlgHom.convMul_apply, TensorProduct.comul_tmul, Bialgebra.comul_one,
      Algebra.TensorProduct.one_def] using this
  induction Coalgebra.comul (R := k) a with
  | zero => simp only [tmul_zero, map_zero]
  | add x y hx hy => simp only [tmul_add, map_add, hx, hy]
  | tmul a₁ a₂ =>
      simp only [Algebra.TensorProduct.lift_tmul, AlgebraTensorModule.tensorTensorTensorComm_tmul,
        AlgHom.liftEquiv_tmul, Algebra.smul_def, map_one, one_mul]

/-- Base change of bialgebra points is a monoid isomorphism for the convolution product.

The forward direction sends `f : A →ₐ[k] R` to `s ⊗ a ↦ s • f a`; the inverse restricts a
`K`-algebra map `K ⊗[k] A →ₐ[K] R` along `a ↦ 1 ⊗ a`. -/
noncomputable def baseChangePointsMulEquiv :
    WithConv (A →ₐ[k] R) ≃* WithConv (K ⊗[k] A →ₐ[K] R) :=
  { WithConv.congr (AlgHom.liftEquiv k K A R) with
  map_mul' f g := by
    apply WithConv.ext
    ext a
    simp [liftEquiv_map_mul] }

/-- The base-change convolution-monoid isomorphism sends `f` to `s ⊗ a ↦ s • f a`. -/
@[simp]
lemma baseChangePointsMulEquiv_apply_ofConv (f : WithConv (A →ₐ[k] R)) :
    (baseChangePointsMulEquiv (k := k) (K := K) (A := A) (R := R) f).ofConv =
      AlgHom.liftEquiv k K A R f.ofConv :=
  rfl

/-- The inverse base-change convolution-monoid isomorphism is restriction along
`A → K ⊗[k] A`. -/
@[simp]
lemma baseChangePointsMulEquiv_symm_ofConv (f : WithConv (K ⊗[k] A →ₐ[K] R)) :
    ((baseChangePointsMulEquiv (k := k) (K := K) (A := A) (R := R)).symm f).ofConv =
      (AlgHom.liftEquiv k K A R).symm f.ofConv :=
  rfl

/-- The base-change convolution-monoid isomorphism sends `f` to `s ⊗ a ↦ s • f a`. -/
@[simp]
lemma baseChangePointsMulEquiv_apply_tmul (f : WithConv (A →ₐ[k] R)) (s : K) (a : A) :
    baseChangePointsMulEquiv (k := k) (K := K) (A := A) (R := R) f (s ⊗ₜ[k] a) =
      s • f.ofConv a :=
  rfl

/-- The inverse of the base-change convolution-monoid isomorphism restricts along
`a ↦ 1 ⊗ a`. -/
@[simp]
lemma baseChangePointsMulEquiv_symm_apply (f : WithConv (K ⊗[k] A →ₐ[K] R)) (a : A) :
    ((baseChangePointsMulEquiv (k := k) (K := K) (A := A) (R := R)).symm f).ofConv a =
      f.ofConv (1 ⊗ₜ[k] a) :=
  rfl

end AlgHom

namespace HopfAlgebra

open CategoryTheory

universe u v w

variable {k : Type u} {K R S : Type v} {H : Type w} [CommRing k]
  [CommRing K] [Semiring H] [Algebra k K] [_root_.HopfAlgebra k H]

section PointsIso

variable [CommRing R] [Algebra K R] [Algebra k R] [IsScalarTower k K R]

/-- Base change of Hopf-algebra points, as an isomorphism of groups.

For a Hopf algebra `H` over `k`, a `k`-algebra `K`, and a commutative `K`-algebra `R`, this
identifies `k`-algebra maps `H →ₐ[k] R` with `K`-algebra maps `K ⊗[k] H →ₐ[K] R`. The
group structures on both sides are the convolution groups of points. -/
noncomputable def baseChangePointsIso :
    TauCeti.HopfAlgebra.points (R := k) (H := H) (CommAlgCat.of k R) ≅
      TauCeti.HopfAlgebra.points (R := K) (H := K ⊗[k] H) (CommAlgCat.of K R) :=
  (AlgHom.baseChangePointsMulEquiv (k := k) (K := K) (A := H) (R := R)).toGrpIso

/-- The underlying multiplicative equivalence of `baseChangePointsIso` is
`AlgHom.baseChangePointsMulEquiv`. -/
lemma baseChangePointsIso_groupIsoToMulEquiv :
    (baseChangePointsIso (k := k) (K := K) (H := H) (R := R)).groupIsoToMulEquiv =
      AlgHom.baseChangePointsMulEquiv (k := k) (K := K) (A := H) (R := R) :=
  rfl

/-- Under `baseChangePointsIso`, a point `f : H →ₐ[k] R` is sent to
`s ⊗ h ↦ s • f h`. -/
@[simp]
lemma baseChangePointsIso_hom_apply_tmul
    (f : TauCeti.HopfAlgebra.points (R := k) (H := H) (CommAlgCat.of k R)) (s : K)
    (h : H) :
    (baseChangePointsIso (k := k) (K := K) (H := H) (R := R)).hom f (s ⊗ₜ[k] h) =
      s • f.ofConv h :=
  rfl

/-- The inverse of `baseChangePointsIso` restricts a base-changed point along
`h ↦ 1 ⊗ h`. -/
@[simp]
lemma baseChangePointsIso_inv_apply
    (f : TauCeti.HopfAlgebra.points (R := K) (H := K ⊗[k] H) (CommAlgCat.of K R))
    (h : H) :
    (((baseChangePointsIso (k := k) (K := K) (H := H) (R := R)).inv f).ofConv) h =
      f.ofConv (1 ⊗ₜ[k] h) :=
  rfl

end PointsIso

section Naturality

variable [CommRing R] [CommRing S] [Algebra K R] [Algebra K S] [Algebra k R] [Algebra k S]
  [IsScalarTower k K R] [IsScalarTower k K S]

/-- Base change of points is natural in the value algebra.

Post-composing an `R`-valued point with a `K`-algebra map `R →ₐ[K] S` commutes with first
transporting points across the base-change isomorphism. -/
lemma mapPoints_baseChangePointsIso_inv (φ : R →ₐ[K] S) :
    TauCeti.HopfAlgebra.mapPoints (R := K) (H := K ⊗[k] H) (CommAlgCat.ofHom φ) ≫
        (baseChangePointsIso (k := k) (K := K) (H := H) (R := S)).inv =
      (baseChangePointsIso (k := k) (K := K) (H := H) (R := R)).inv ≫
        TauCeti.HopfAlgebra.mapPoints (R := k) (H := H)
          (CommAlgCat.ofHom (φ.restrictScalars k)) := by
  ext f h
  change (((baseChangePointsIso (k := k) (K := K) (H := H) (R := S)).inv
      (TauCeti.HopfAlgebra.mapPoints (R := K) (H := K ⊗[k] H)
        (CommAlgCat.ofHom φ) f)).ofConv h) =
    ((TauCeti.HopfAlgebra.mapPoints (R := k) (H := H)
      (CommAlgCat.ofHom (φ.restrictScalars k))
      ((baseChangePointsIso (k := k) (K := K) (H := H) (R := R)).inv f)).ofConv h)
  rw [baseChangePointsIso_inv_apply]
  rw [mapPoints_apply_apply]
  rw [mapPoints_apply_apply]
  rw [baseChangePointsIso_inv_apply]
  rfl

/-- Forward naturality form of `baseChangePointsIso` in the value algebra. -/
lemma baseChangePointsIso_hom_mapPoints (φ : R →ₐ[K] S) :
    (baseChangePointsIso (k := k) (K := K) (H := H) (R := R)).hom ≫
        TauCeti.HopfAlgebra.mapPoints (R := K) (H := K ⊗[k] H) (CommAlgCat.ofHom φ) =
      TauCeti.HopfAlgebra.mapPoints (R := k) (H := H)
          (CommAlgCat.ofHom (φ.restrictScalars k)) ≫
        (baseChangePointsIso (k := k) (K := K) (H := H) (R := S)).hom := by
  ext f h
  change ((TauCeti.HopfAlgebra.mapPoints (R := K) (H := K ⊗[k] H)
      (CommAlgCat.ofHom φ)
      ((baseChangePointsIso (k := k) (K := K) (H := H) (R := R)).hom f)).ofConv
      (1 ⊗ₜ[k] h)) =
    (((baseChangePointsIso (k := k) (K := K) (H := H) (R := S)).hom
      (TauCeti.HopfAlgebra.mapPoints (R := k) (H := H)
        (CommAlgCat.ofHom (φ.restrictScalars k)) f)).ofConv (1 ⊗ₜ[k] h))
  rw [mapPoints_apply_apply]
  rw [baseChangePointsIso_hom_apply_tmul]
  rw [baseChangePointsIso_hom_apply_tmul]
  rw [mapPoints_apply_apply]
  simp only [CommAlgCat.hom_ofHom, AlgHom.coe_restrictScalars', one_smul]

end Naturality

end HopfAlgebra

end TauCeti
