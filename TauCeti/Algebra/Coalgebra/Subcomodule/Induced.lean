/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Flat.Basic
public import TauCeti.Algebra.Coalgebra.Comodule.OfInjective
public import TauCeti.Algebra.Coalgebra.Subcomodule.Basic

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
* `TauCeti.Subcomodule.coact_coe_eq_tmul_one`: a fixed vector of a subcomodule is fixed in the
  ambient comodule.
* `TauCeti.Subcomodule.subtype`: the inclusion as a comodule morphism.
* `TauCeti.Comodule.Hom.codRestrict`: a comodule morphism corestricted to a
  subcomodule containing its image.

## References

This is the standard inherited comodule structure on a subcomodule; see Sweedler,
*Hopf Algebras*, Chapter 2.  The formalization uses Mathlib's
`LinearMap.codRestrictOfInjective` and flatness preservation of injective maps under tensor
product; the comodule laws are inherited along the inclusion by `TauCeti.Comodule.ofInjective`.
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

private theorem subtype_rTensor_injective :
    Function.Injective ((SMulMemClass.subtype N).rTensor C) :=
  Module.Flat.rTensor_preserves_injective_linearMap (SMulMemClass.subtype N)
    Subtype.val_injective

omit [Module.Flat R C] in
/-- The ambient coaction of an element of a subcomodule lies in the range of the tensored
inclusion `N ⊗ C → M ⊗ C`. -/
private theorem coact_mem_range (n : N) :
    ((Comodule.coact (R := R) (C := C) (M := M)).comp (SMulMemClass.subtype N)) n ∈
      LinearMap.range ((SMulMemClass.subtype N).rTensor C) := by
  rw [LinearMap.comp_apply, LinearMap.rTensor_def, SMulMemClass.subtype_apply]
  exact N.coact_mem n.2

/-- The coaction induced on the subtype of a subcomodule.

It is the unique lift of the ambient coaction along `N ⊗ C → M ⊗ C`. -/
noncomputable def inducedCoact : N →ₗ[R] N ⊗[R] C :=
  LinearMap.codRestrictOfInjective
    ((Comodule.coact (R := R) (C := C) (M := M)).comp (SMulMemClass.subtype N))
    ((SMulMemClass.subtype N).rTensor C) (subtype_rTensor_injective N) (coact_mem_range N)

/-- The induced coaction, included back into `M ⊗ C`, is the ambient coaction. -/
@[simp]
theorem subtype_rTensor_inducedCoact (n : N) :
    (SMulMemClass.subtype N).rTensor C (N.inducedCoact n) =
      Comodule.coact (R := R) (C := C) (M := M) n :=
  LinearMap.codRestrictOfInjective_comp_apply
    ((Comodule.coact (R := R) (C := C) (M := M)).comp (SMulMemClass.subtype N))
    ((SMulMemClass.subtype N).rTensor C) (subtype_rTensor_injective N) (coact_mem_range N) n

/-- The induced coaction included into the ambient tensor product, as an equality of linear maps. -/
@[simp]
theorem subtype_rTensor_comp_inducedCoact : (SMulMemClass.subtype N).rTensor C ∘ₗ N.inducedCoact =
      (Comodule.coact (R := R) (C := C) (M := M)).comp (SMulMemClass.subtype N) := by
  ext n
  exact subtype_rTensor_inducedCoact N n

/-- The subtype of a subcomodule carries the inherited right-comodule structure. -/
noncomputable instance instComodule : Comodule R C N :=
  Comodule.ofInjective N.inducedCoact (SMulMemClass.subtype N) Subtype.val_injective
    (Module.Flat.rTensor_preserves_injective_linearMap _ Subtype.val_injective)
    (subtype_rTensor_comp_inducedCoact N)

/-- The inherited coaction on a subcomodule is `Subcomodule.inducedCoact`. -/
@[simp]
theorem induced_coact :
    Comodule.coact (R := R) (C := C) (M := N) = N.inducedCoact :=
  Comodule.ofInjective_coact ..

/-- The inherited coaction, included back into `M ⊗ C`, is the ambient coaction. -/
theorem subtype_rTensor_coact (n : N) :
    (SMulMemClass.subtype N).rTensor C (Comodule.coact (R := R) (C := C) (M := N) n) =
      Comodule.coact (R := R) (C := C) (M := M) n := by
  rw [induced_coact, subtype_rTensor_inducedCoact]

/-- A vector of a subcomodule whose inherited coaction is `v ↦ v ⊗ 1` is fixed by the ambient
coaction too. -/
theorem coact_coe_eq_tmul_one [One C] {n : N}
    (hn : Comodule.coact (R := R) (C := C) (M := N) n = n ⊗ₜ[R] (1 : C)) :
    Comodule.coact (R := R) (C := C) (M := M) (n : M) = (n : M) ⊗ₜ[R] (1 : C) := by
  have h := congrArg ((SMulMemClass.subtype N).rTensor C) hn
  rwa [subtype_rTensor_coact, LinearMap.rTensor_tmul, SMulMemClass.subtype_apply] at h

/-- The subtype map of a subcomodule as a morphism of right comodules. -/
noncomputable def subtype : Comodule.Hom R C N M where
  toLinearMap := SMulMemClass.subtype N
  map_coact := by
    ext n
    exact subtype_rTensor_coact N n

/-- The underlying linear map of the subcomodule inclusion is the linear inclusion. -/
@[simp]
theorem subtype_toLinearMap : (Subcomodule.subtype N).toLinearMap = SMulMemClass.subtype N :=
  (rfl)

/-- The subcomodule inclusion acts as the underlying subtype coercion. -/
@[simp]
theorem subtype_apply (n : N) : Subcomodule.subtype N n = n :=
  (rfl)

end Subcomodule

namespace Comodule.Hom

variable {N : Type*}
variable [AddCommMonoid N] [Module R N] [Comodule R C N]

/-- Corestrict a comodule morphism to a subcomodule containing its image. -/
noncomputable def codRestrict (f : Hom R C M N) (P : Subcomodule R C N)
    (h : ∀ m, f m ∈ P) : Hom R C M P :=
  let g : M →ₗ[R] P :=
    { toFun := fun m ↦ ⟨f m, h m⟩
      map_add' := fun x y ↦ Subtype.ext (map_add f.toLinearMap x y)
      map_smul' := fun r x ↦ Subtype.ext (map_smul f.toLinearMap r x) }
  { toLinearMap := g
    map_coact := by
      ext m
      apply Module.Flat.rTensor_preserves_injective_linearMap
        (SMulMemClass.subtype P) Subtype.val_injective
      simp only [LinearMap.comp_apply]
      calc
        (SMulMemClass.subtype P).rTensor C
            (TensorProduct.map g LinearMap.id
              (Comodule.coact (R := R) (C := C) (M := M) m)) =
          TensorProduct.map f.toLinearMap LinearMap.id
            (Comodule.coact (R := R) (C := C) (M := M) m) := by
              rw [LinearMap.rTensor_def, TensorProduct.map_map]
              rfl
        _ = Comodule.coact (R := R) (C := C) (M := N) (f m) :=
          f.map_coact_apply m
        _ = (SMulMemClass.subtype P).rTensor C
            (Comodule.coact (R := R) (C := C) (M := P) ⟨f m, h m⟩) :=
          (Subcomodule.subtype_rTensor_coact P ⟨f m, h m⟩).symm }

private theorem codRestrict_toLinearMap_def (f : Hom R C M N) (P : Subcomodule R C N)
    (h : ∀ m, f m ∈ P) :
    (f.codRestrict P h).toLinearMap = f.toLinearMap.codRestrict P.toSubmodule h :=
  LinearMap.ext fun _ ↦ rfl

private theorem codRestrict_apply_def (f : Hom R C M N) (P : Subcomodule R C N)
    (h : ∀ m, f m ∈ P) (m : M) : (f.codRestrict P h m : N) = f m :=
  rfl

/-- The underlying linear map of a corestricted comodule morphism is the ordinary linear
corestriction. -/
@[simp]
theorem codRestrict_toLinearMap (f : Hom R C M N) (P : Subcomodule R C N)
    (h : ∀ m, f m ∈ P) :
    (f.codRestrict P h).toLinearMap = f.toLinearMap.codRestrict P.toSubmodule h :=
  by exact codRestrict_toLinearMap_def f P h

/-- Corestricting a comodule morphism changes only its codomain. -/
@[simp]
theorem codRestrict_apply (f : Hom R C M N) (P : Subcomodule R C N)
    (h : ∀ m, f m ∈ P) (m : M) : (f.codRestrict P h m : N) = f m :=
  by exact codRestrict_apply_def f P h m

/-- Composing a corestricted comodule morphism with the subcomodule inclusion recovers the
original morphism. -/
@[simp]
theorem subtype_comp_codRestrict (f : Hom R C M N) (P : Subcomodule R C N)
    (h : ∀ m, f m ∈ P) :
    Comodule.Hom.comp (Subcomodule.subtype P) (f.codRestrict P h) = f := by
  ext m
  simp

end Comodule.Hom

end TauCeti
