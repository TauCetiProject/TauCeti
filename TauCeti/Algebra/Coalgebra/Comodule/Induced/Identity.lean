/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.Coalgebra.Comodule.Induced.Basic

/-!
# Induction along the identity coalgebra map

For a flat coalgebra `C` over a commutative ring, the cotensor product `M □_C C` is naturally
isomorphic to `M`. The forward map evaluates the last factor by the counit, and its inverse
is the coaction of `M`. These maps are comodule morphisms and commute with coefficient
morphisms, without a flatness or finiteness assumption on `M`.

The unbundled maps allow independent universes for `C` and `M`. Their bundled isomorphism
uses a common universe containing the coalgebra, so that both objects belong to the same
comodule category. This is the identity comparison for algebraic induction.

## References

* J. C. Jantzen, *Representations of Algebraic Groups*, Part I, §§3.3–3.4.
* M. Takeuchi, *Morita theorems for categories of comodules*, J. Fac. Sci. Univ. Tokyo 24
  (1977), for cotensor induction and reciprocity.
-/

public section

open CategoryTheory
open scoped TensorProduct

attribute [local instance] TauCeti.Comodule.cofree

namespace TauCeti.Comodule

universe u v w x

variable {R : Type u} [CommRing R]
variable {C : Type v} [AddCommMonoid C] [Module R C] [Coalgebra R C] [Module.Flat R C]
variable (M : Type w) [AddCommMonoid M] [Module R M] [Comodule R C M]

/-- Counit evaluation identifies identity-induced tensors with their coefficient vectors,
as a morphism of `C`-comodules. -/
noncomputable def inducedIdHom : Hom R C (induced (CoalgHom.id R C) M) M where
  toLinearMap := by
    letI := Corestrict (M := induced (CoalgHom.id R C) M) (CoalgHom.id R C)
    exact (inducedEval (CoalgHom.id R C)).toLinearMap
  map_coact := by
    have h := letI := Corestrict (M := induced (CoalgHom.id R C) M) (CoalgHom.id R C)
      (inducedEval (CoalgHom.id R C) (M := M)).map_coact
    simpa only [corestrict_coact, corestrictCoact_id] using h

/-- The identity-induction comparison evaluates the last tensor factor by the counit. -/
@[simp]
theorem inducedIdHom_apply (t : induced (CoalgHom.id R C) M) :
    inducedIdHom (R := R) (C := C) M t =
      TensorProduct.rid R M ((Coalgebra.counit (R := R) (A := C)).lTensor M t) := by
  unfold inducedIdHom
  exact inducedEval_apply (CoalgHom.id R C) t

/-- The inverse identity-induction comparison is the coaction, with codomain restricted to
the cotensor equalizer. -/
noncomputable def inducedIdInv : Hom R C M (induced (CoalgHom.id R C) M) :=
  (Hom.cofreeUnit (R := R) (C := C) M).codRestrict _ fun m ↦ by
    rw [mem_induced_iff]
    simpa only [CoalgHom.id_toLinearMap, LinearMap.rTensor_id, LinearMap.id_comp,
      Hom.cofreeUnit_apply] using (coassoc_symm_apply (R := R) (C := C) m).symm

/-- The inverse comparison has the original coaction as its ambient tensor map. -/
@[simp]
theorem coe_inducedIdInv_apply (m : M) :
    (inducedIdInv (R := R) (C := C) M m : M ⊗[R] C) = coact (R := R) (C := C) m := by
  simp [inducedIdInv]

/-- The coaction after identity-induced counit evaluation recovers the original tensor. -/
-- Cancel the inverse pair before `inducedIdHom_apply` expands counit evaluation.
@[simp↓]
theorem inducedIdInv_inducedIdHom (t : induced (CoalgHom.id R C) M) :
    inducedIdInv (R := R) (C := C) M (inducedIdHom (R := R) (C := C) M t) = t := by
  apply Subtype.ext
  rw [coe_inducedIdInv_apply, ← Hom.map_coact_apply, ← LinearMap.rTensor_def]
  have h := LinearMap.congr_fun (congrArg Hom.toLinearMap
    (Hom.cofreeLift_cofreeCounit_comp
      (Subcomodule.subtype (induced (CoalgHom.id R C) M)))) t
  have he : (inducedIdHom (R := R) (C := C) M).toLinearMap =
      cofreeCounit R C M ∘ₗ (Subcomodule.subtype (induced (CoalgHom.id R C) M)).toLinearMap := by
    ext s
    simp [cofreeCounit_def]
  rw [he]
  simpa only [Hom.cofreeLift_toLinearMap, LinearMap.comp_apply,
    Hom.coe_toLinearMap, Subcomodule.subtype_apply] using h

variable {M}
variable {N : Type x} [AddCommMonoid N] [Module R N] [Comodule R C N]

/-- Counit evaluation for identity induction is natural in the coefficient comodule. -/
theorem inducedIdHom_naturality (f : Hom R C M N) :
    Hom.comp (inducedIdHom (R := R) (C := C) N) (inducedMap (CoalgHom.id R C) f) =
      Hom.comp f (inducedIdHom (R := R) (C := C) M) := by
  ext t
  simp only [Hom.comp_apply, inducedIdHom_apply, coe_inducedMap_apply]
  simpa [cofreeCounit_def] using
    LinearMap.congr_fun (cofreeCounit_comp_rTensor (R := R) (C := C) f.toLinearMap) t

/-- The inverse identity-induction comparison is natural in the coefficient comodule. -/
theorem inducedIdInv_naturality (f : Hom R C M N) :
    Hom.comp (inducedMap (CoalgHom.id R C) f) (inducedIdInv (R := R) (C := C) M) =
      Hom.comp (inducedIdInv (R := R) (C := C) N) f := by
  apply Hom.ext
  intro m
  apply Subtype.ext
  simp only [Hom.comp_apply, coe_inducedMap_apply, coe_inducedIdInv_apply]
  exact f.map_coact_apply m

end TauCeti.Comodule

namespace TauCeti.ComoduleCat

universe u v w

variable {R : Type u} [CommRing R]
variable {C : Type v} [AddCommMonoid C] [Module R C] [Coalgebra R C] [Module.Flat R C]

/-- Induction along the identity coalgebra map is canonically isomorphic to the original
comodule. Its forward map is counit evaluation and its inverse is the coaction. -/
noncomputable def inducedIdIso (M : ComoduleCat.{u, v, max v w} R C) :
    of R C (Comodule.induced (CoalgHom.id R C) M) ≅ M where
  hom := Comodule.inducedIdHom (R := R) (C := C) M
  inv := Comodule.inducedIdInv (R := R) (C := C) M
  hom_inv_id := by
    apply hom_ext
    intro t
    exact Comodule.inducedIdInv_inducedIdHom M t
  inv_hom_id := by
    apply hom_ext
    intro m
    rw [comp_apply, id_apply]
    simp

/-- The forward bundled comparison is the unbundled counit-evaluation morphism. -/
@[simp]
theorem inducedIdIso_hom (M : ComoduleCat.{u, v, max v w} R C) :
    (inducedIdIso M).hom = Comodule.inducedIdHom (R := R) (C := C) M :=
  (rfl)

/-- The inverse bundled comparison is the unbundled coaction morphism. -/
@[simp]
theorem inducedIdIso_inv (M : ComoduleCat.{u, v, max v w} R C) :
    (inducedIdIso M).inv = Comodule.inducedIdInv (R := R) (C := C) M :=
  (rfl)

/-- The canonical isomorphism for identity induction commutes with coefficient morphisms. -/
theorem inducedIdIso_naturality {M N : ComoduleCat.{u, v, max v w} R C} (f : M ⟶ N) :
    ofHom (R := R) (C := C) (Comodule.inducedMap (CoalgHom.id R C) f) ≫ (inducedIdIso N).hom =
      (inducedIdIso M).hom ≫ f :=
  Comodule.inducedIdHom_naturality f

end TauCeti.ComoduleCat
