/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.FunctorOfPoints
public import Mathlib.RingTheory.TensorProduct.IncludeLeftSubRight

/-!
# Faithfully flat descent for the functor of points

Let `A → B` be a faithfully flat extension of commutative `R`-algebras. The two maps
`B ⇉ B ⊗[A] B` give two restriction maps on the `B`-points represented by a Hopf algebra `H`.
This file proves that the `A`-points are exactly the `B`-points on which those restrictions agree,
as an equivalence of groups. The coordinate algebra need not be commutative for this algebraic
descent statement; the affine-group-scheme application specializes to commutative `H`.

The proof uses Mathlib's effective-descent theorem
`Algebra.IsEffective.of_faithfullyFlat`: the equalizer of
`B ⇉ B ⊗[A] B` is the image of `A`. A compatible point therefore factors through that
image, and `AlgEquiv.ofInjective` identifies the image with `A`. The resulting equivalence
respects convolution because its forward map is induced by postcomposition in the value algebra.

This is the affine, group-valued faithfully flat descent statement. The finite-presentation part of
an fppf cover is not needed for descent itself, so the result is stated at the natural faithfully
flat level.

## Main declarations

* `TauCeti.AlgHom.descentSubgroup`: the subgroup of `B`-points satisfying the
  equalizer condition over `B ⊗[A] B`.
* `TauCeti.AlgHom.faithfullyFlatDescentMulEquiv`: `A`-points are equivalent to that descent
  subgroup.

## References

This is the affine representable case of faithfully flat descent. The algebraic input is
Mathlib's `Algebra.IsEffective.of_faithfullyFlat`, following the standard Amitsur equalizer
`A → B ⇉ B ⊗[A] B`.
-/

public section

open Algebra.TensorProduct WithConv
open scoped TensorProduct

namespace TauCeti

namespace AlgHom

universe u v w x

variable {R : Type u} {H : Type v} (A : Type w) (B : Type x)
variable [CommSemiring R] [Semiring H] [HopfAlgebra R H]

section Semiring

variable [CommSemiring A] [Semiring B] [Algebra R A] [Algebra R B] [Algebra A B]
variable [IsScalarTower R A B]

private noncomputable def faithfullyFlatDescentLeft : B →ₐ[R] (B ⊗[A] B) :=
  (includeLeft : B →ₐ[A] (B ⊗[A] B)).restrictScalars R

private noncomputable def faithfullyFlatDescentRight : B →ₐ[R] (B ⊗[A] B) :=
  (includeRight : B →ₐ[A] (B ⊗[A] B)).restrictScalars R

end Semiring

section CommSemiring

variable [CommSemiring A] [CommSemiring B] [Algebra R A] [Algebra R B] [Algebra A B]
variable [IsScalarTower R A B]

/-- The subgroup of `B`-points satisfying the descent equalizer condition along `A → B`.

A point `f : H →ₐ[R] B` belongs to this subgroup exactly when its two postcompositions
`H →ₐ[R] B ⇉ B ⊗[A] B` agree. The subgroup structure comes from functoriality of
convolution in the value algebra. -/
noncomputable def descentSubgroup :
    Subgroup (WithConv (H →ₐ[R] B)) :=
  MonoidHom.eqLocus (AlgHom.mapValue (H := H) (faithfullyFlatDescentLeft (R := R) A (B := B)))
    (AlgHom.mapValue (H := H) (faithfullyFlatDescentRight (R := R) A (B := B)))

private theorem mem_descentSubgroup_iff_maps (f : WithConv (H →ₐ[R] B)) :
    f ∈ descentSubgroup (R := R) (H := H) A B ↔
      AlgHom.mapValue (H := H) (faithfullyFlatDescentLeft (R := R) A (B := B)) f =
        AlgHom.mapValue (H := H) (faithfullyFlatDescentRight (R := R) A (B := B)) f :=
  Iff.rfl

/-- Pointwise form of the descent equalizer condition. -/
@[simp]
theorem mem_descentSubgroup_iff_apply (f : WithConv (H →ₐ[R] B)) :
    f ∈ descentSubgroup (R := R) (H := H) A B ↔
      ∀ h, (includeLeft (R := A) (S := A) (A := B) (B := B)) (f h) =
        (includeRight (R := A) (A := B) (B := B)) (f h) := by
  rw [mem_descentSubgroup_iff_maps]
  simp only [AlgHom.mapValue_apply, WithConv.toConv_injective.eq_iff, DFunLike.ext_iff,
    AlgHom.comp_apply, faithfullyFlatDescentLeft, faithfullyFlatDescentRight,
    AlgHom.coe_restrictScalars']

private noncomputable def faithfullyFlatDescentHom :
    WithConv (H →ₐ[R] A) →* descentSubgroup (R := R) (H := H) A B :=
  (AlgHom.mapValue (H := H) (IsScalarTower.toAlgHom R A B)).codRestrict _ fun f => by
    rw [mem_descentSubgroup_iff_apply]
    intro h
    simp

private theorem faithfullyFlatDescentHom_apply (f : WithConv (H →ₐ[R] A)) :
    (faithfullyFlatDescentHom (R := R) (H := H) A B f : WithConv (H →ₐ[R] B)) =
      AlgHom.mapValue (H := H) (IsScalarTower.toAlgHom R A B) f :=
  rfl

end CommSemiring

section CommRing

variable [CommRing A] [CommRing B] [Algebra R A] [Algebra R B] [Algebra A B]
variable [IsScalarTower R A B] [Module.FaithfullyFlat A B]

private theorem faithfullyFlatDescentHom_bijective :
    Function.Bijective (faithfullyFlatDescentHom (R := R) (H := H) A B) := by
  constructor
  · intro f g hfg
    apply AlgHom.mapValue_injective (φ := IsScalarTower.toAlgHom R A B)
      (FaithfulSMul.algebraMap_injective A B)
    simpa only [faithfullyFlatDescentHom_apply] using congr_arg Subtype.val hfg
  · intro f
    obtain ⟨g, hg⟩ := (AlgHom.mem_mrange_mapValue_iff (H := H)
      (φ := IsScalarTower.toAlgHom R A B) (FaithfulSMul.algebraMap_injective A B)).mpr fun h => by
        have hr : f.1.ofConv h ∈ Set.range (algebraMap A B) := by
          rw [← Algebra.IsEffective.eqLocus_includeLeft_includeRight
            (Algebra.IsEffective.of_faithfullyFlat A B)]
          exact (mem_descentSubgroup_iff_apply (R := R) A B f.1).mp f.2 h
        obtain ⟨y, hy⟩ := hr
        exact (AlgHom.mem_range _).mpr ⟨y, by rw [IsScalarTower.coe_toAlgHom', hy]⟩
    exact ⟨g, Subtype.ext (by rw [faithfullyFlatDescentHom_apply, hg])⟩

/-- **Faithfully flat descent for affine group-valued points.** If `B` is faithfully flat over
`A`, base change identifies the convolution group of `A`-points of `H` with the subgroup of
`B`-points whose two restrictions to `B ⊗[A] B` agree. -/
noncomputable def faithfullyFlatDescentMulEquiv :
    WithConv (H →ₐ[R] A) ≃* descentSubgroup (R := R) (H := H) A B :=
  MulEquiv.ofBijective (faithfullyFlatDescentHom (R := R) (H := H) A B)
    (faithfullyFlatDescentHom_bijective (R := R) (H := H) A B)

/-- The faithfully flat descent equivalence sends an `A`-point to its base change to `B`. -/
@[simp]
theorem faithfullyFlatDescentMulEquiv_apply (f : WithConv (H →ₐ[R] A)) :
    (faithfullyFlatDescentMulEquiv (R := R) (H := H) A B f : WithConv (H →ₐ[R] B)) =
      AlgHom.mapValue (H := H) (IsScalarTower.toAlgHom R A B) f := by
  rw [faithfullyFlatDescentMulEquiv, MulEquiv.ofBijective_apply]
  exact faithfullyFlatDescentHom_apply (R := R) A B f

/-- Descending a compatible `B`-point and extending it back to `B` recovers the original
point. -/
@[simp]
theorem mapValue_faithfullyFlatDescentMulEquiv_symm_apply
    (f : descentSubgroup (R := R) (H := H) A B) :
    WithConv.toConv ((IsScalarTower.toAlgHom R A B).comp
      ((faithfullyFlatDescentMulEquiv (R := R) (H := H) A B).symm f).ofConv) = f.1 := by
  rw [← AlgHom.mapValue_apply, ← faithfullyFlatDescentMulEquiv_apply]
  exact congr_arg Subtype.val
    ((faithfullyFlatDescentMulEquiv (R := R) (H := H) A B).apply_symm_apply f)

end CommRing

end AlgHom

end TauCeti
