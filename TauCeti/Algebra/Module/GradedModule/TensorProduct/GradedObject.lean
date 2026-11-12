/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
public import Mathlib.CategoryTheory.GradedObject.Monoidal
public import TauCeti.Algebra.Module.GradedModule.GradedObject
public import TauCeti.Algebra.Module.GradedModule.TensorProduct.Basic
import Mathlib.Algebra.Category.ModuleCat.EpiMono

/-!
# Comparing internal and native graded tensor products

The native tensor product of the homogeneous pieces of two internally graded modules agrees
with the internal total-degree grading of their tensor product. The comparison sends a
homogeneous pure tensor to the tensor of its underlying elements. Thus equality in the native
graded tensor can be checked in the underlying ungraded tensor product, over any commutative
ring, without flatness assumptions on the modules.

The inverse uses the internal decompositions and Mathlib's `TensorProduct.directSum`.
-/

public section

open CategoryTheory
open GradedObject.Monoidal
open scoped DirectSum TensorProduct MonoidalCategory

namespace TauCeti.InternalGrading

universe u

variable {R M N : Type u} [CommRing R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]

private noncomputable def tensorGradedObjectHom (G : InternalGrading R M)
    (H : InternalGrading R N) (n : ℤ) :
    tensorObj G.toGradedObject H.toGradedObject n ⟶ (G.tensorProduct H).toGradedObject n :=
  tensorObjDesc fun p q h ↦ ModuleCat.ofHom <|
    (TensorProduct.mapIncl (G.piece p) (H.piece q)).codRestrict
      ((G.tensorProduct H).piece n) fun z ↦ by
        induction z using TensorProduct.inductionOn with
        | tmul x y =>
          simpa only [TensorProduct.map_tmul, Submodule.coe_subtype, h] using
            G.tmul_mem_tensorProduct H x.property y.property
        | add x y hx hy => simpa only [map_add] using Submodule.add_mem _ hx hy

private theorem tensorGradedObjectHom_tmul (G : InternalGrading R M)
    (H : InternalGrading R N) {p q n : ℤ} (h : p + q = n)
    (x : G.piece p) (y : H.piece q) :
    (tensorGradedObjectHom G H n
      (ιTensorObj G.toGradedObject H.toGradedObject p q n h (x ⊗ₜ[R] y)) : M ⊗[R] N) =
      (x : M) ⊗ₜ[R] (y : N) := by
  rw [← ModuleCat.comp_apply, tensorGradedObjectHom, ι_tensorObjDesc]
  rfl

private noncomputable def tensorBidegreeEquiv (G : InternalGrading R M)
    (H : InternalGrading R N) :
    M ⊗[R] N ≃ₗ[R] ⨁ d : ℤ × ℤ, G.piece d.1 ⊗[R] H.piece d.2 :=
  TensorProduct.congr (DirectSum.decomposeLinearEquiv G.piece)
      (DirectSum.decomposeLinearEquiv H.piece) ≪≫ₗ
    TensorProduct.directSum R R (fun p ↦ G.piece p) (fun q ↦ H.piece q)

private theorem tensorBidegreeEquiv_tmul (G : InternalGrading R M)
    (H : InternalGrading R N) {p q : ℤ} (x : G.piece p) (y : H.piece q) :
    tensorBidegreeEquiv G H ((x : M) ⊗ₜ[R] (y : N)) =
      DirectSum.lof R (ℤ × ℤ) (fun d ↦ G.piece d.1 ⊗[R] H.piece d.2) (p, q)
        (x ⊗ₜ[R] y) := by
  simp only [tensorBidegreeEquiv, LinearEquiv.trans_apply, TensorProduct.congr_tmul,
    DirectSum.decomposeLinearEquiv_apply_coe, TensorProduct.directSum_lof_tmul_lof]

private noncomputable def tensorGradedObjectRetraction (G : InternalGrading R M)
    (H : InternalGrading R N) (n : ℤ) :
    M ⊗[R] N →ₗ[R] (tensorObj G.toGradedObject H.toGradedObject n : ModuleCat R) :=
  (DirectSum.toModule R (ℤ × ℤ) _
    (M := fun d : ℤ × ℤ ↦ G.piece d.1 ⊗[R] H.piece d.2) fun d ↦
    if h : d.1 + d.2 = n then
      (ιTensorObj G.toGradedObject H.toGradedObject d.1 d.2 n h).hom else 0) ∘ₗ
    (tensorBidegreeEquiv G H).toLinearMap

private theorem tensorGradedObjectRetraction_tmul (G : InternalGrading R M)
    (H : InternalGrading R N) {p q n : ℤ} (h : p + q = n)
    (x : G.piece p) (y : H.piece q) :
    tensorGradedObjectRetraction G H n ((x : M) ⊗ₜ[R] (y : N)) =
      ιTensorObj G.toGradedObject H.toGradedObject p q n h (x ⊗ₜ[R] y) := by
  simp only [tensorGradedObjectRetraction, LinearMap.comp_apply, LinearEquiv.coe_coe,
    tensorBidegreeEquiv_tmul, DirectSum.toModule_lof, dite_eq_left h]

private theorem tensorGradedObjectHom_bijective (G : InternalGrading R M)
    (H : InternalGrading R N) (n : ℤ) :
    Function.Bijective (tensorGradedObjectHom G H n) := by
  have hleft : tensorGradedObjectHom G H n ≫
      ModuleCat.ofHom ((tensorGradedObjectRetraction G H n).comp
        ((G.tensorProduct H).piece n).subtype) = 𝟙 _ := by
    apply tensorObj_ext
    intro p q h
    apply ModuleCat.MonoidalCategory.tensor_ext
    intro x y
    -- The codomain is an opaque coproduct object; expose only the bundled linear-map application.
    change tensorGradedObjectRetraction G H n
      (tensorGradedObjectHom G H n
        (ιTensorObj G.toGradedObject H.toGradedObject p q n h (x ⊗ₜ[R] y)) : M ⊗[R] N) = _
    rw [tensorGradedObjectHom_tmul,
      tensorGradedObjectRetraction_tmul G H h]
    simp only [Category.comp_id]
  refine ⟨?_, ?_⟩
  · have : IsSplitMono (tensorGradedObjectHom G H n) :=
      IsSplitMono.mk' ⟨_, hleft⟩
    exact (ModuleCat.mono_iff_injective _).mp (by infer_instance)
  · have hle : (G.tensorProduct H).piece n ≤
        LinearMap.range (((G.tensorProduct H).piece n).subtype.comp
          (tensorGradedObjectHom G H n).hom) := by
      apply G.tensorProduct_piece_le H
      intro p x hx y hy
      refine ⟨ιTensorObj G.toGradedObject H.toGradedObject p (n - p) n (by omega)
        (⟨x, hx⟩ ⊗ₜ[R] ⟨y, hy⟩), ?_⟩
      exact tensorGradedObjectHom_tmul G H (by omega) ⟨x, hx⟩ ⟨y, hy⟩
    intro z
    obtain ⟨x, hx⟩ := hle z.property
    exact ⟨x, Subtype.ext hx⟩

/-- The native graded tensor of the homogeneous pieces is the internal total-degree tensor
grading. Its forward map forgets the two homogeneous membership proofs. -/
noncomputable def tensorProductGradedObjectIso (G : InternalGrading R M)
    (H : InternalGrading R N) :
    tensorObj G.toGradedObject H.toGradedObject ≅ (G.tensorProduct H).toGradedObject :=
  GradedObject.isoMk _ _ fun n ↦
    (LinearEquiv.ofBijective (tensorGradedObjectHom G H n).hom
      (tensorGradedObjectHom_bijective G H n)).toModuleIso

/-- The comparison sends a native homogeneous pure tensor to the tensor of its underlying
elements. -/
@[simp↓]
theorem tensorProductGradedObjectIso_hom_tmul (G : InternalGrading R M)
    (H : InternalGrading R N) {p q n : ℤ} (h : p + q = n)
    (x : G.piece p) (y : H.piece q) :
    ((G.tensorProductGradedObjectIso H).hom n
      (ιTensorObj G.toGradedObject H.toGradedObject p q n h (x ⊗ₜ[R] y)) : M ⊗[R] N) =
      (x : M) ⊗ₜ[R] (y : N) :=
  tensorGradedObjectHom_tmul G H h x y

/-- The inverse comparison puts a tensor of homogeneous elements in its native total-degree
summand. -/
-- The bidegrees cannot be recovered from the ambient tensor expression, so keep this rule named.
theorem tensorProductGradedObjectIso_inv_tmul (G : InternalGrading R M)
    (H : InternalGrading R N) {p q n : ℤ} (h : p + q = n)
    (x : G.piece p) (y : H.piece q) :
    (G.tensorProductGradedObjectIso H).inv n
      ⟨(x : M) ⊗ₜ[R] (y : N), h ▸ G.tmul_mem_tensorProduct H x.property y.property⟩ =
      ιTensorObj G.toGradedObject H.toGradedObject p q n h (x ⊗ₜ[R] y) := by
  let e := (GradedObject.eval n).mapIso (G.tensorProductGradedObjectIso H)
  apply e.toLinearEquiv.injective
  have hforward : e.hom
      (ιTensorObj G.toGradedObject H.toGradedObject p q n h (x ⊗ₜ[R] y)) =
      ⟨(x : M) ⊗ₜ[R] (y : N), h ▸ G.tmul_mem_tensorProduct H x.property y.property⟩ :=
    Subtype.ext (G.tensorProductGradedObjectIso_hom_tmul H h x y)
  simpa only [Iso.toLinearEquiv_apply, e, Functor.mapIso_hom, Functor.mapIso_inv,
    GradedObject.eval_map] using (ModuleCat.hom_inv_apply e _).trans hforward.symm

end TauCeti.InternalGrading
