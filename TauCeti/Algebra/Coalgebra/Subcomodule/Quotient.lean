/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.LinearAlgebra.Quotient.Basic
public import TauCeti.Algebra.Coalgebra.Subcomodule

/-!
# Quotients by subcomodules

This file equips the quotient of a right comodule by a subcomodule with the induced
right-comodule structure. The quotient coaction is the unique linear map whose composite
with the quotient map is `(N.mkQ ⊗ id) ∘ ρ`.

This is Layer 1 infrastructure for the reductive-groups roadmap target on comodules and the
finite-dimensional comodule category: after subcomodules, images, and kernels, quotient
comodules provide the basic cokernel-style construction used by later representation-category
bookkeeping.

## Main declarations

* `TauCeti.Subcomodule.quotientCoact`: the descended coaction on `M ⧸ N`.
* `TauCeti.Subcomodule.instComoduleQuotient`: the induced comodule structure.
* `TauCeti.Subcomodule.mkQ`: the quotient map as a comodule morphism.

## References

This is the standard quotient comodule construction; see Sweedler, *Hopf Algebras*,
Chapter 2. The formalization uses Mathlib's quotient-module API and tensor-product
functoriality.
-/

public section

open scoped TensorProduct

namespace TauCeti

universe u v w

variable {R : Type u} {C : Type v} {M : Type w}
variable [CommRing R]
variable [AddCommGroup C] [Module R C] [Coalgebra R C]
variable [AddCommGroup M] [Module R M] [Comodule R C M]

namespace Subcomodule

variable (N : Subcomodule R C M)

private theorem quotient_tensor_map_subtype_eq_zero
    (t : N.toSubmodule ⊗[R] C) :
    TensorProduct.map N.toSubmodule.mkQ (LinearMap.id : C →ₗ[R] C)
        (TensorProduct.map N.toSubmodule.subtype (LinearMap.id : C →ₗ[R] C) t) = 0 := by
  induction t with
  | zero => simp
  | tmul n c =>
      have hn : N.toSubmodule.mkQ (n : M) = 0 := by
        rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
        exact n.2
      simp [hn]
  | add x y hx hy =>
      simp [hx, hy]

/-- The composite `(N.mkQ ⊗ id) ∘ ρ` vanishes on a subcomodule `N`, so the coaction
descends to the quotient by `N`. -/
theorem coact_le_ker_quotientTensor :
    N.toSubmodule ≤
      LinearMap.ker
        ((TensorProduct.map N.toSubmodule.mkQ (LinearMap.id : C →ₗ[R] C)).comp
          (Comodule.coact (R := R) (C := C) (M := M))) := by
  intro m hm
  rw [LinearMap.mem_ker]
  rcases N.coact_mem hm with ⟨t, ht⟩
  change TensorProduct.map N.toSubmodule.mkQ (LinearMap.id : C →ₗ[R] C)
    (Comodule.coact (R := R) (C := C) (M := M) m) = 0
  rw [← ht]
  exact quotient_tensor_map_subtype_eq_zero N t

/-- The coaction induced on the quotient by a subcomodule. -/
@[expose] def quotientCoact : M ⧸ N.toSubmodule →ₗ[R] (M ⧸ N.toSubmodule) ⊗[R] C :=
  N.toSubmodule.liftQ
    ((TensorProduct.map N.toSubmodule.mkQ (LinearMap.id : C →ₗ[R] C)).comp
      (Comodule.coact (R := R) (C := C) (M := M)))
    (coact_le_ker_quotientTensor N)

/-- The quotient coaction applied to a quotient class. -/
@[simp]
theorem quotientCoact_mk (m : M) :
    N.quotientCoact (Submodule.Quotient.mk m) =
      TensorProduct.map N.toSubmodule.mkQ (LinearMap.id : C →ₗ[R] C)
        (Comodule.coact (R := R) (C := C) (M := M) m) :=
  Submodule.liftQ_apply _ _ _

private theorem rTensor_quotientCoact_map_mkQ_id
    (t : M ⊗[R] C) :
    (N.quotientCoact.rTensor C)
        (TensorProduct.map N.toSubmodule.mkQ (LinearMap.id : C →ₗ[R] C) t) =
      TensorProduct.map
          (TensorProduct.map N.toSubmodule.mkQ (LinearMap.id : C →ₗ[R] C))
          (LinearMap.id : C →ₗ[R] C)
        ((Comodule.coact (R := R) (C := C) (M := M)).rTensor C t) := by
  induction t with
  | zero => simp
  | tmul m c => simp
  | add x y hx hy => simp [hx, hy]

private theorem comul_lTensor_map_mkQ_id
    (t : M ⊗[R] C) :
    Coalgebra.comul.lTensor (M ⧸ N.toSubmodule)
        (TensorProduct.map N.toSubmodule.mkQ (LinearMap.id : C →ₗ[R] C) t) =
      TensorProduct.map N.toSubmodule.mkQ
          (LinearMap.id : C ⊗[R] C →ₗ[R] C ⊗[R] C)
        (Coalgebra.comul.lTensor M t) := by
  induction t with
  | zero => simp
  | tmul m c => simp [LinearMap.lTensor_tmul]
  | add x y hx hy => simp [hx, hy]

private theorem counit_lTensor_map_mkQ_id
    (t : M ⊗[R] C) :
    Coalgebra.counit.lTensor (M ⧸ N.toSubmodule)
        (TensorProduct.map N.toSubmodule.mkQ (LinearMap.id : C →ₗ[R] C) t) =
      TensorProduct.map N.toSubmodule.mkQ
          (LinearMap.id : R →ₗ[R] R)
        (Coalgebra.counit.lTensor M t) := by
  induction t with
  | zero => simp
  | tmul m c => simp [LinearMap.lTensor_tmul]
  | add x y hx hy => simp [hx, hy]

private theorem assoc_map_map_mkQ_id_id (t : M ⊗[R] C ⊗[R] C) :
    TensorProduct.assoc R (M ⧸ N.toSubmodule) C C
        (TensorProduct.map
          (TensorProduct.map N.toSubmodule.mkQ (LinearMap.id : C →ₗ[R] C))
          (LinearMap.id : C →ₗ[R] C) t) =
      TensorProduct.map N.toSubmodule.mkQ
          (LinearMap.id : C ⊗[R] C →ₗ[R] C ⊗[R] C)
        (TensorProduct.assoc R M C C t) := by
  induction t with
  | zero => simp
  | tmul mc c =>
      induction mc with
      | zero => simp
      | tmul m c' => simp
      | add x y hx hy =>
          rw [TensorProduct.add_tmul, map_add, map_add, hx, hy]
          exact (map_add _ _ _).symm
  | add x y hx hy => simp [hx, hy]

/-- The quotient of a right comodule by a subcomodule inherits a right-comodule structure. -/
instance instComoduleQuotient : Comodule R C (M ⧸ N.toSubmodule) where
  coact := N.quotientCoact
  coassoc := by
    apply Submodule.linearMap_qext
    ext m
    rw [LinearMap.comp_apply, LinearMap.comp_apply, LinearMap.comp_apply, LinearMap.comp_apply,
      Submodule.mkQ_apply, quotientCoact_mk, rTensor_quotientCoact_map_mkQ_id]
    calc
      TensorProduct.assoc R (M ⧸ N.toSubmodule) C C
          (TensorProduct.map
            (TensorProduct.map N.toSubmodule.mkQ (LinearMap.id : C →ₗ[R] C))
            (LinearMap.id : C →ₗ[R] C)
            ((Comodule.coact (R := R) (C := C) (M := M)).rTensor C
              (Comodule.coact (R := R) (C := C) (M := M) m))) =
          TensorProduct.map N.toSubmodule.mkQ
            (LinearMap.id : C ⊗[R] C →ₗ[R] C ⊗[R] C)
            (TensorProduct.assoc R M C C
              ((Comodule.coact (R := R) (C := C) (M := M)).rTensor C
                (Comodule.coact (R := R) (C := C) (M := M) m))) := by
            exact assoc_map_map_mkQ_id_id N _
      _ = (LinearMap.lTensor (M ⧸ N.toSubmodule) Coalgebra.comul ∘ₗ N.quotientCoact)
            (Submodule.Quotient.mk m) := by
            rw [Comodule.coassoc_apply, ← comul_lTensor_map_mkQ_id,
              LinearMap.comp_apply, quotientCoact_mk]
  lTensor_counit_comp_coact := by
    apply Submodule.linearMap_qext
    ext m
    rw [LinearMap.comp_apply, LinearMap.comp_apply, Submodule.mkQ_apply, quotientCoact_mk]
    rw [counit_lTensor_map_mkQ_id, Comodule.lTensor_counit_coact]
    rfl

/-- The coaction on the quotient comodule is `Subcomodule.quotientCoact`. -/
@[simp]
theorem quotient_comodule_coact :
    Comodule.coact (R := R) (C := C) (M := M ⧸ N.toSubmodule) = N.quotientCoact :=
  rfl

/-- The quotient map by a subcomodule as a comodule morphism. -/
@[expose] def mkQ : Comodule.Hom R C M (M ⧸ N.toSubmodule) where
  toLinearMap := N.toSubmodule.mkQ
  map_coact := by
    ext m
    simp

/-- The underlying linear map of the quotient comodule morphism is the quotient map. -/
@[simp]
theorem mkQ_toLinearMap : N.mkQ.toLinearMap = N.toSubmodule.mkQ :=
  rfl

/-- The quotient comodule morphism sends a vector to its quotient class. -/
@[simp]
theorem mkQ_apply (m : M) : N.mkQ m = Submodule.Quotient.mk m :=
  rfl

/-- The quotient comodule morphism is surjective. -/
theorem mkQ_surjective : Function.Surjective N.mkQ :=
  N.toSubmodule.mkQ_surjective

end Subcomodule

end TauCeti
