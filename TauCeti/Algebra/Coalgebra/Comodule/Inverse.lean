/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Coalgebra.Comodule.Basic

/-!
# Inverses of bijective comodule morphisms

The inverse linear map of a bijective comodule morphism respects coactions. This is the
unbundled, independently universe-polymorphic counterpart of `ComoduleCat.isoOfLinearEquiv`.
It allows additional structure, such as a grading and a differential, to be transported to
an inverse without changing the carriers.
-/

public section

open scoped TensorProduct

namespace TauCeti.Comodule.Hom

universe uR uC uM uN

variable {R : Type uR} {C : Type uC} {M : Type uM} {N : Type uN}
  [CommSemiring R] [AddCommMonoid C] [Module R C] [Coalgebra R C]
  [AddCommMonoid M] [Module R M] [Comodule R C M]
  [AddCommMonoid N] [Module R N] [Comodule R C N]

/-- The inverse of a bijective comodule morphism, with the inverse underlying linear map. -/
noncomputable def inverse (f : Hom R C M N) (hf : Function.Bijective f) : Hom R C N M :=
  let e := LinearEquiv.ofBijective f.toLinearMap hf
  { toLinearMap := e.symm.toLinearMap
    map_coact := by
      ext n
      have hn := f.map_coact_apply (e.symm n)
      have he : f (e.symm n) = n := e.apply_symm_apply n
      rw [he] at hn
      have hn' := congrArg (TensorProduct.map e.symm.toLinearMap (LinearMap.id : C →ₗ[R] C)) hn
      have hecomp : e.symm.toLinearMap ∘ₗ f.toLinearMap = LinearMap.id :=
        LinearMap.ext e.symm_apply_apply
      simpa only [TensorProduct.map_map, LinearMap.id_comp, hecomp,
        TensorProduct.map_id, LinearMap.id_apply, LinearMap.comp_apply,
        LinearEquiv.coe_coe] using hn'.symm }

/-- The inverse comodule morphism has the inverse linear equivalence underneath. -/
@[simp]
theorem inverse_toLinearMap (f : Hom R C M N) (hf : Function.Bijective f) :
    (f.inverse hf).toLinearMap = (LinearEquiv.ofBijective f.toLinearMap hf).symm.toLinearMap :=
  (rfl)

/-- The inverse comodule morphism is a left inverse. -/
@[simp]
theorem inverse_apply_apply (f : Hom R C M N) (hf : Function.Bijective f) (m : M) :
    f.inverse hf (f m) = m :=
  (LinearEquiv.ofBijective f.toLinearMap hf).symm_apply_apply m

/-- The inverse comodule morphism is a right inverse. -/
@[simp]
theorem apply_inverse_apply (f : Hom R C M N) (hf : Function.Bijective f) (n : N) :
    f (f.inverse hf n) = n :=
  (LinearEquiv.ofBijective f.toLinearMap hf).apply_symm_apply n

end TauCeti.Comodule.Hom
