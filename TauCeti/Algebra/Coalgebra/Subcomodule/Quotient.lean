/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.LinearAlgebra.Quotient.Basic
public import TauCeti.Algebra.Coalgebra.Subcomodule.Comap

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
* `TauCeti.Subcomodule.liftQ`: the comodule morphism induced from a morphism killing `N`.

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

/-- The composite `(N.mkQ ⊗ id) ∘ ρ` vanishes on a subcomodule `N`, so the coaction
descends to the quotient by `N`. -/
theorem le_ker_tensorProduct_mkQ_comp_coact :
    N.toSubmodule ≤
      LinearMap.ker
        ((TensorProduct.map N.toSubmodule.mkQ (LinearMap.id : C →ₗ[R] C)).comp
          (Comodule.coact (R := R) (C := C) (M := M))) := by
  intro m hm
  rw [LinearMap.mem_ker, LinearMap.comp_apply]
  rcases N.coact_mem hm with ⟨t, ht⟩
  rw [← ht]
  exact rTensor_mkQ_map_subtype (R := R) (C := C) (N₁ := M) N.toSubmodule t

/-- The coaction induced on the quotient by a subcomodule. -/
def quotientCoact : M ⧸ N.toSubmodule →ₗ[R] (M ⧸ N.toSubmodule) ⊗[R] C :=
  N.toSubmodule.liftQ
    ((TensorProduct.map N.toSubmodule.mkQ (LinearMap.id : C →ₗ[R] C)).comp
      (Comodule.coact (R := R) (C := C) (M := M)))
    (le_ker_tensorProduct_mkQ_comp_coact N)

/-- The quotient coaction applied to a quotient class. -/
@[simp]
theorem quotientCoact_mk (m : M) :
    N.quotientCoact (Submodule.Quotient.mk m) =
      TensorProduct.map N.toSubmodule.mkQ (LinearMap.id : C →ₗ[R] C)
        (Comodule.coact (R := R) (C := C) (M := M) m) :=
  Submodule.liftQ_apply _ _ _

/-- The quotient of a right comodule by a subcomodule inherits a right-comodule structure. -/
instance instComoduleQuotient : Comodule R C (M ⧸ N.toSubmodule) where
  coact := N.quotientCoact
  coassoc := by
    apply Submodule.linearMap_qext
    ext m
    have hquot :
        N.quotientCoact.comp N.toSubmodule.mkQ =
          (TensorProduct.map N.toSubmodule.mkQ (LinearMap.id : C →ₗ[R] C)).comp
            (Comodule.coact (R := R) (C := C) (M := M)) := by
      ext m
      exact N.quotientCoact_mk m
    rw [LinearMap.comp_apply, LinearMap.comp_apply, LinearMap.comp_apply, LinearMap.comp_apply,
      Submodule.mkQ_apply, quotientCoact_mk, LinearMap.rTensor_map]
    rw [hquot]
    calc
      TensorProduct.assoc R (M ⧸ N.toSubmodule) C C
          (TensorProduct.map
            ((TensorProduct.map N.toSubmodule.mkQ (LinearMap.id : C →ₗ[R] C)).comp
              (Comodule.coact (R := R) (C := C) (M := M)))
            (LinearMap.id : C →ₗ[R] C)
            (Comodule.coact (R := R) (C := C) (M := M) m)) =
          TensorProduct.assoc R (M ⧸ N.toSubmodule) C C
            (TensorProduct.map
              (TensorProduct.map N.toSubmodule.mkQ (LinearMap.id : C →ₗ[R] C))
              (LinearMap.id : C →ₗ[R] C)
              ((Comodule.coact (R := R) (C := C) (M := M)).rTensor C
                (Comodule.coact (R := R) (C := C) (M := M) m))) := by
            rw [LinearMap.rTensor_def, TensorProduct.map_map]
            simp
      _ =
          TensorProduct.map N.toSubmodule.mkQ
            (TensorProduct.map (LinearMap.id : C →ₗ[R] C) (LinearMap.id : C →ₗ[R] C))
            (TensorProduct.assoc R M C C
              ((Comodule.coact (R := R) (C := C) (M := M)).rTensor C
                (Comodule.coact (R := R) (C := C) (M := M) m))) := by
            exact
              (TensorProduct.map_map_assoc N.toSubmodule.mkQ LinearMap.id LinearMap.id _).symm
      _ =
          TensorProduct.map N.toSubmodule.mkQ
            (LinearMap.id : C ⊗[R] C →ₗ[R] C ⊗[R] C)
            (Coalgebra.comul.lTensor M
              (Comodule.coact (R := R) (C := C) (M := M) m)) := by
            rw [Comodule.coassoc_apply]
            simp
      _ =
          Coalgebra.comul.lTensor (M ⧸ N.toSubmodule)
            (TensorProduct.map N.toSubmodule.mkQ (LinearMap.id : C →ₗ[R] C)
              (Comodule.coact (R := R) (C := C) (M := M) m)) := by
            rw [LinearMap.lTensor_map]
            simp
      _ = (LinearMap.lTensor (M ⧸ N.toSubmodule) Coalgebra.comul ∘ₗ N.quotientCoact)
            (Submodule.Quotient.mk m) := by
            rw [LinearMap.comp_apply, quotientCoact_mk]
  lTensor_counit_comp_coact := by
    apply Submodule.linearMap_qext
    ext m
    rw [LinearMap.comp_apply, LinearMap.comp_apply, Submodule.mkQ_apply, quotientCoact_mk]
    calc
      Coalgebra.counit.lTensor (M ⧸ N.toSubmodule)
          (TensorProduct.map N.toSubmodule.mkQ (LinearMap.id : C →ₗ[R] C)
            (Comodule.coact (R := R) (C := C) (M := M) m)) =
        TensorProduct.map N.toSubmodule.mkQ
          (Coalgebra.counit.comp (LinearMap.id : C →ₗ[R] C))
          (Comodule.coact (R := R) (C := C) (M := M) m) := by
          exact
            LinearMap.lTensor_map (R := R) M Coalgebra.counit N.toSubmodule.mkQ
              (LinearMap.id : C →ₗ[R] C)
              (Comodule.coact (R := R) (C := C) (M := M) m)
      _ =
        TensorProduct.map N.toSubmodule.mkQ (LinearMap.id : R →ₗ[R] R)
          (Coalgebra.counit.lTensor M
            (Comodule.coact (R := R) (C := C) (M := M) m)) := by
          rw [LinearMap.lTensor_def, TensorProduct.map_map]
          simp
      _ = ((TensorProduct.mk R (M ⧸ N.toSubmodule) R).flip 1)
            (Submodule.Quotient.mk m) := by
          rw [Comodule.lTensor_counit_coact]
          rfl

/-- The coaction on the quotient comodule is `Subcomodule.quotientCoact`. -/
@[simp]
theorem quotient_comodule_coact :
    Comodule.coact (R := R) (C := C) (M := M ⧸ N.toSubmodule) = N.quotientCoact :=
  rfl

/-- The quotient map by a subcomodule as a comodule morphism. -/
abbrev mkQ : Comodule.Hom R C M (M ⧸ N.toSubmodule) where
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

variable [Module.Flat R C]
variable {P : Type*} [AddCommGroup P] [Module R P] [Comodule R C P]

/-- A comodule morphism out of `M` that vanishes on `N` descends to the quotient by `N`. -/
def liftQ (f : Comodule.Hom R C M P) (hf : N ≤ Comodule.Hom.ker (R := R) (C := C) f) :
    Comodule.Hom R C (M ⧸ N.toSubmodule) P where
  toLinearMap :=
    N.toSubmodule.liftQ f.toLinearMap (by
      intro m hm
      rw [LinearMap.mem_ker]
      exact Comodule.Hom.mem_ker.mp (hf (by simpa using hm)))
  map_coact := by
    apply Submodule.linearMap_qext
    ext m
    rw [LinearMap.comp_apply, LinearMap.comp_apply, quotient_comodule_coact]
    rw [show N.toSubmodule.mkQ m = Submodule.Quotient.mk m from rfl]
    rw [quotientCoact_mk]
    rw [LinearMap.comp_apply, LinearMap.comp_apply]
    rw [show N.toSubmodule.mkQ m = Submodule.Quotient.mk m from rfl]
    rw [Submodule.liftQ_apply]
    calc
      TensorProduct.map
          (N.toSubmodule.liftQ f.toLinearMap (by
            intro m hm
            rw [LinearMap.mem_ker]
            exact Comodule.Hom.mem_ker.mp (hf (by simpa using hm))))
          (LinearMap.id : C →ₗ[R] C)
          (TensorProduct.map N.toSubmodule.mkQ (LinearMap.id : C →ₗ[R] C)
            (Comodule.coact (R := R) (C := C) (M := M) m)) =
        TensorProduct.map f.toLinearMap (LinearMap.id : C →ₗ[R] C)
          (Comodule.coact (R := R) (C := C) (M := M) m) := by
          simp [TensorProduct.map_map]
      _ = Comodule.coact (R := R) (C := C) (M := P) (f m) := by
          exact Comodule.Hom.map_coact_apply f m

/-- The descended quotient morphism applied to a quotient class. -/
@[simp]
theorem liftQ_apply (f : Comodule.Hom R C M P)
    (hf : N ≤ Comodule.Hom.ker (R := R) (C := C) f) (m : M) :
    N.liftQ f hf (Submodule.Quotient.mk m) = f m :=
  Submodule.liftQ_apply _ _ _

/-- Precomposing the descended quotient morphism with the quotient map recovers the original
morphism. -/
@[simp]
theorem liftQ_comp_mkQ (f : Comodule.Hom R C M P)
    (hf : N ≤ Comodule.Hom.ker (R := R) (C := C) f) :
    (N.liftQ f hf).comp N.mkQ = f := by
  ext m
  simp

/-- Alias for `Subcomodule.liftQ_comp_mkQ`, named after Mathlib's quotient API. -/
@[simp]
theorem liftQ_mkQ (f : Comodule.Hom R C M P)
    (hf : N ≤ Comodule.Hom.ker (R := R) (C := C) f) :
    (N.liftQ f hf).comp N.mkQ = f :=
  N.liftQ_comp_mkQ f hf

omit [Module.Flat R C] in
/-- Two morphisms out of a quotient are equal if they agree after precomposition with the
quotient map. -/
theorem hom_ext {f g : Comodule.Hom R C (M ⧸ N.toSubmodule) P}
    (h : f.comp N.mkQ = g.comp N.mkQ) : f = g := by
  ext q
  rcases N.mkQ_surjective q with ⟨m, rfl⟩
  exact congr_fun (congrArg DFunLike.coe h) m

/-- Uniqueness of the morphism descended to a quotient. -/
theorem liftQ_unique (f : Comodule.Hom R C M P)
    (hf : N ≤ Comodule.Hom.ker (R := R) (C := C) f)
    (g : Comodule.Hom R C (M ⧸ N.toSubmodule) P) (hg : g.comp N.mkQ = f) :
    g = N.liftQ f hf := by
  apply N.hom_ext
  rw [hg, liftQ_comp_mkQ]

/-- The kernel of the quotient comodule morphism is the subcomodule being quotiented. -/
@[simp]
theorem ker_mkQ : Comodule.Hom.ker (R := R) (C := C) N.mkQ = N := by
  ext m
  rw [Comodule.Hom.mem_ker, mkQ_apply, Submodule.Quotient.mk_eq_zero]
  rfl

end Subcomodule

end TauCeti
