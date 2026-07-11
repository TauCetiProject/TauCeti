/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.RingTheory.Flat.Basic
public import TauCeti.Algebra.Coalgebra.ComoduleCat
public import TauCeti.Algebra.Coalgebra.Subcomodule

/-!
# The induced comodule on a subcomodule

This file equips a subcomodule with its inherited right-comodule structure.  The definition is
made under the flatness hypothesis on the coalgebra: flatness makes
`N ⊗ C → M ⊗ C` injective for the subtype map of a subcomodule `N ≤ M`, so the ambient
coaction has a unique lift to `N ⊗ C`.

This is Layer 1 infrastructure for the reductive-groups roadmap target "Comodules over a
coalgebra/Hopf algebra": finite-dimensional subcomodules and categorical kernels need
subcomodules to be usable as comodules in their own right.

## Main declarations

* `TauCeti.Subcomodule.inducedCoact`: the coaction on the subtype of a subcomodule.
* `TauCeti.Subcomodule.instComodule`: the induced right-comodule structure.
* `TauCeti.Subcomodule.subtype`: the inclusion as a comodule morphism.
* `TauCeti.ComoduleCat.ofSubcomodule`: the bundled comodule attached to a subcomodule.

## References

This is the standard inherited comodule structure on a subcomodule; see Sweedler,
*Hopf Algebras*, Chapter 2.  The formalization uses Mathlib's
`LinearMap.codRestrictOfInjective` and flatness preservation of injective maps under tensor
product.
-/

public section

open scoped TensorProduct

namespace TauCeti

universe u v w

variable {R : Type u} {C : Type v} {M : Type w}
variable [CommSemiring R]
variable [AddCommMonoid C] [Module R C] [Coalgebra R C] [Module.Flat R C]
variable [AddCommMonoid M] [Module R M] [Comodule R C M]

namespace Subcomodule

variable (N : Subcomodule R C M)

/-- The underlying linear inclusion of a subcomodule into the ambient comodule. -/
@[expose] def subtypeLinear : N →ₗ[R] M :=
  N.toSubmodule.subtype

private theorem subtype_rTensor_injective :
    Function.Injective (N.subtypeLinear.rTensor C) :=
  Module.Flat.rTensor_preserves_injective_linearMap N.subtypeLinear Subtype.val_injective

/-- The coaction induced on the subtype of a subcomodule.

It is the unique lift of the ambient coaction along `N ⊗ C → M ⊗ C`. -/
noncomputable def inducedCoact : N →ₗ[R] N ⊗[R] C :=
  LinearMap.codRestrictOfInjective
    ((Comodule.coact (R := R) (C := C) (M := M)).comp N.subtypeLinear)
    (N.subtypeLinear.rTensor C) (subtype_rTensor_injective N)
    (fun n => by
      change Comodule.coact (R := R) (C := C) (M := M) (N.carrier.subtype n) ∈
        LinearMap.range (TensorProduct.map N.carrier.subtype (LinearMap.id : C →ₗ[R] C))
      exact N.coact_mem n.2)

/-- The induced coaction, included back into `M ⊗ C`, is the ambient coaction. -/
@[simp]
theorem subtype_rTensor_inducedCoact (n : N) :
    N.subtypeLinear.rTensor C (N.inducedCoact n) =
      Comodule.coact (R := R) (C := C) (M := M) n :=
  LinearMap.codRestrictOfInjective_comp_apply
    ((Comodule.coact (R := R) (C := C) (M := M)).comp N.subtypeLinear)
    (N.subtypeLinear.rTensor C) (subtype_rTensor_injective N)
    (fun n => by
      change Comodule.coact (R := R) (C := C) (M := M) (N.carrier.subtype n) ∈
        LinearMap.range (TensorProduct.map N.carrier.subtype (LinearMap.id : C →ₗ[R] C))
      exact N.coact_mem n.2) n

/-- The induced coaction included into the ambient tensor product, as an equality of linear maps. -/
@[simp]
theorem subtype_rTensor_comp_inducedCoact :
    N.subtypeLinear.rTensor C ∘ₗ N.inducedCoact =
      (Comodule.coact (R := R) (C := C) (M := M)).comp N.subtypeLinear := by
  ext n
  exact subtype_rTensor_inducedCoact N n

private theorem subtype_rTensor_tensor_injective :
    Function.Injective ((N.subtypeLinear.rTensor C).rTensor C) :=
  Module.Flat.rTensor_preserves_injective_linearMap
    (N.subtypeLinear.rTensor C) (subtype_rTensor_injective N)

omit [Module.Flat R C] in
private theorem subtype_rTensor_lTensor_injective :
    Function.Injective (N.subtypeLinear.rTensor R) :=
  Module.Flat.rTensor_preserves_injective_linearMap N.subtypeLinear
    Subtype.val_injective

private theorem map_rTensor_inducedCoact (t : N ⊗[R] C) :
    TensorProduct.map (N.subtypeLinear.rTensor C) (LinearMap.id : C →ₗ[R] C)
        (TensorProduct.map N.inducedCoact (LinearMap.id : C →ₗ[R] C) t) =
      TensorProduct.map (Comodule.coact (R := R) (C := C) (M := M))
        (LinearMap.id : C →ₗ[R] C)
        (TensorProduct.map N.subtypeLinear (LinearMap.id : C →ₗ[R] C) t) := by
  induction t with
  | zero => simp
  | tmul n c =>
      simp only [TensorProduct.map_tmul, LinearMap.id_coe, id_eq]
      rw [subtype_rTensor_inducedCoact]
      change Comodule.coact (R := R) (C := C) (M := M) n ⊗ₜ[R] c =
        Comodule.coact (R := R) (C := C) (M := M) n ⊗ₜ[R] c
      rfl
  | add x y hx hy => simp [hx, hy]

omit [Module.Flat R C] in
private theorem assoc_symm_tmul_natural (n : N) (z : C ⊗[R] C) :
    (TensorProduct.assoc R M C C).symm (N.subtypeLinear n ⊗ₜ[R] z) =
      (N.subtypeLinear.rTensor C).rTensor C
        ((TensorProduct.assoc R N C C).symm (n ⊗ₜ[R] z)) := by
  induction z with
  | zero => simp
  | tmul c₁ c₂ =>
      change (N.subtypeLinear n ⊗ₜ[R] c₁) ⊗ₜ[R] c₂ =
        (N.subtypeLinear n ⊗ₜ[R] c₁) ⊗ₜ[R] c₂
      rfl
  | add x y hx hy => simpa [TensorProduct.tmul_add, map_add] using congrArg₂ (· + ·) hx hy

omit [Module.Flat R C] in
private theorem assoc_symm_lTensor_comul_natural (t : N ⊗[R] C) :
    (TensorProduct.assoc R M C C).symm
        (Coalgebra.comul.lTensor M (N.subtypeLinear.rTensor C t)) =
      (N.subtypeLinear.rTensor C).rTensor C
        ((TensorProduct.assoc R N C C).symm (Coalgebra.comul.lTensor N t)) := by
  induction t with
  | zero => simp
  | tmul n c =>
      simp only [LinearMap.rTensor_def, LinearMap.lTensor_def, TensorProduct.map_tmul,
        LinearMap.id_coe, id_eq]
      exact assoc_symm_tmul_natural N n (Coalgebra.comul (R := R) c)
  | add x y hx hy => simp [hx, hy]

omit [Module.Flat R C] in
private theorem lTensor_counit_natural (t : N ⊗[R] C) :
    N.subtypeLinear.rTensor R (Coalgebra.counit.lTensor N t) =
      Coalgebra.counit.lTensor M (N.subtypeLinear.rTensor C t) := by
  induction t with
  | zero => simp
  | tmul n c => rfl
  | add x y hx hy => simp [hx, hy]

/-- The subtype of a subcomodule carries the inherited right-comodule structure. -/
noncomputable instance instComodule : Comodule R C N where
  coact := N.inducedCoact
  coassoc := by
    ext n
    apply (subtype_rTensor_tensor_injective N).comp
      (TensorProduct.assoc R N C C).symm.injective
    simp only [LinearMap.comp_apply, LinearMap.rTensor_def]
    calc
      (N.subtypeLinear.rTensor C).rTensor C
          ((TensorProduct.assoc R N C C).symm
            (TensorProduct.assoc R N C C
              (TensorProduct.map N.inducedCoact (LinearMap.id : C →ₗ[R] C)
                (N.inducedCoact n)))) =
          TensorProduct.map (N.subtypeLinear.rTensor C) (LinearMap.id : C →ₗ[R] C)
            (TensorProduct.map N.inducedCoact (LinearMap.id : C →ₗ[R] C)
              (N.inducedCoact n)) := by
            rw [LinearEquiv.symm_apply_apply]
            rfl
      _ =
          (Comodule.coact (R := R) (C := C) (M := M)).rTensor C
            (Comodule.coact (R := R) (C := C) (M := M) n) := by
            rw [map_rTensor_inducedCoact]
            change TensorProduct.map (Comodule.coact (R := R) (C := C) (M := M))
                (LinearMap.id : C →ₗ[R] C)
                (N.subtypeLinear.rTensor C (N.inducedCoact n)) =
              TensorProduct.map (Comodule.coact (R := R) (C := C) (M := M))
                (LinearMap.id : C →ₗ[R] C)
                (Comodule.coact (R := R) (C := C) (M := M) n)
            rw [subtype_rTensor_inducedCoact]
      _ =
          (TensorProduct.assoc R M C C).symm
            (Coalgebra.comul.lTensor M
              (Comodule.coact (R := R) (C := C) (M := M) n)) := by
            apply (TensorProduct.assoc R M C C).injective
            simp [Comodule.coassoc_apply (R := R) (C := C) (M := M)]
      _ =
          (N.subtypeLinear.rTensor C).rTensor C
            ((TensorProduct.assoc R N C C).symm
              (Coalgebra.comul.lTensor N (N.inducedCoact n))) := by
            rw [← assoc_symm_lTensor_comul_natural]
            rw [subtype_rTensor_inducedCoact]
  lTensor_counit_comp_coact := by
    ext n
    apply subtype_rTensor_lTensor_injective N
    simp only [LinearMap.comp_apply]
    calc
      N.subtypeLinear.rTensor R
          (Coalgebra.counit.lTensor N (N.inducedCoact n)) =
          Coalgebra.counit.lTensor M
            (N.subtypeLinear.rTensor C (N.inducedCoact n)) := by
            exact lTensor_counit_natural N (N.inducedCoact n)
      _ = (n : M) ⊗ₜ[R] 1 := by
            simp
      _ = N.subtypeLinear.rTensor R (n ⊗ₜ[R] 1) := by
            change (n : M) ⊗ₜ[R] 1 = (n : M) ⊗ₜ[R] 1
            rfl

/-- The inherited coaction on a subcomodule is `Subcomodule.inducedCoact`. -/
@[simp]
theorem induced_coact :
    Comodule.coact (R := R) (C := C) (M := N) = N.inducedCoact :=
  rfl

/-- The inherited coaction, included back into `M ⊗ C`, is the ambient coaction. -/
@[simp]
theorem subtype_rTensor_coact (n : N) :
    N.subtypeLinear.rTensor C (Comodule.coact (R := R) (C := C) (M := N) n) =
      Comodule.coact (R := R) (C := C) (M := M) n :=
  subtype_rTensor_inducedCoact N n

/-- The subtype map of a subcomodule as a morphism of right comodules. -/
@[expose] noncomputable def subtype : Comodule.Hom R C N M where
  toLinearMap := N.toSubmodule.subtype
  map_coact := by
    ext n
    exact subtype_rTensor_coact N n

/-- The underlying linear map of the subcomodule inclusion is the submodule subtype map. -/
@[simp]
theorem subtype_toLinearMap : (Subcomodule.subtype N).toLinearMap = N.toSubmodule.subtype :=
  rfl

/-- The subcomodule inclusion acts as the underlying subtype coercion. -/
@[simp]
theorem subtype_apply (n : N) : Subcomodule.subtype N n = n :=
  rfl

end Subcomodule

namespace ComoduleCat

variable (R C)

/-- A subcomodule, bundled as a right comodule via its inherited coaction. -/
noncomputable abbrev ofSubcomodule (N : Subcomodule R C M) :
    _root_.TauCeti.ComoduleCat.{u, v, w} R C :=
  _root_.TauCeti.ComoduleCat.of R C N

variable {R C}

/-- The bundled subcomodule has the inherited coaction. -/
@[simp]
theorem ofSubcomodule_coact (N : Subcomodule R C M) :
    Comodule.coact (R := R) (C := C) (M := ofSubcomodule (R := R) (C := C) N) =
      N.inducedCoact :=
  rfl

/-- The inclusion of a bundled subcomodule into its ambient comodule. -/
noncomputable abbrev ofSubcomoduleSubtype (N : Subcomodule R C M) :
    ofSubcomodule (R := R) (C := C) N ⟶ _root_.TauCeti.ComoduleCat.of R C M :=
  Subcomodule.subtype N

/-- The bundled subcomodule inclusion acts as the subtype coercion. -/
@[simp]
theorem ofSubcomoduleSubtype_apply (N : Subcomodule R C M)
    (n : ofSubcomodule (R := R) (C := C) N) :
    ofSubcomoduleSubtype (R := R) (C := C) N n = n :=
  rfl

end ComoduleCat

end TauCeti
