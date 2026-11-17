/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import Mathlib.Basic.Finite.Sum
public import Mathlib.CategoryTheory.Monoidal.Limits.Cokernels
public import TauCeti.Algebra.Category.ModuleCat.Sheaf.TensorProduct.Closed

/-!
# Tensor products of presentations of sheaves of modules

Let `R` be a sheaf of commutative rings on a small site. If `M` is the cokernel of
`f : free ι ⟶ free σ` and `N` is the cokernel of `g : free κ ⟶ free τ`, then `M ⊗ N` is the
cokernel of the morphism

`(free ι ⊗ free τ) ⨿ (free σ ⊗ free κ) ⟶ free σ ⊗ free τ`

given by `f ▷ free τ` and `free σ ◁ g`, and the tensor product of two free sheaves of modules is
free on the product of the index types. Hence a presentation of `M` and a presentation of `N`
give a presentation of `M ⊗ N`, with generators indexed by `σ × τ` and relations indexed by
`ι × τ ⊕ σ × κ`. This is the local input for the tensor product of quasi-coherent sheaves.

The right exactness of the tensor product comes from its closed structure, and the cokernel
computation is Mathlib's `CategoryTheory.Limits.CokernelCofork.isColimitTensor`.
The generator-and-relation construction is the sheaf-level analogue of
Mathlib's `Module.Presentation.tensor` in `Mathlib.Algebra.Module.Presentation.Tensor`, by
Joël Riou.

## Main declarations

* `TauCeti.SheafOfModules.freeTensorFreeIso`: `free I ⊗ free I' ≅ free (I × I')`;
* `SheafOfModules.GeneratingSections.tensor`: the generating sections of `M ⊗ N` built from
  generating sections of `M` and `N`, indexed by pairs of generators; it is finite when both
  families are finite (`SheafOfModules.GeneratingSections.isFiniteType_tensor`), and its generating
  morphism is an isomorphism when both generating morphisms are
  (`SheafOfModules.GeneratingSections.isIso_tensor_π`);
* `SheafOfModules.Presentation.tensor`: the presentation of `M ⊗ N` built from presentations of
  `M` and `N`; it is finite when both presentations are finite, and its generating morphism is
  an isomorphism when both generating morphisms are
  (`SheafOfModules.Presentation.isIso_tensor_generators_π`).
-/

public section

open CategoryTheory Limits MonoidalCategory

namespace TauCeti

universe u

noncomputable section

namespace SheafOfModules

open _root_.SheafOfModules

variable {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
  {R : Sheaf J CommRingCat.{u}}

/-- The tensor product of the free sheaves of modules on `I` and on `I'` is the free sheaf of
modules on `I × I'`. The generator indexed by `(i, i')` corresponds to the tensor product of the
generators indexed by `i` and `i'` (`ιFree_freeTensorFreeIso_inv`). -/
def freeTensorFreeIso (I I' : Type u) :
    free (R := ringCatSheaf R) I ⊗ free I' ≅ free (I × I') :=
  (isColimitFreeCofan (R := ringCatSheaf R) (I × I')).coconePointsIsoOfNatIso
    (Cofan.IsColimit.prod
      (fun _ ↦ Cofan.mk (unit _ ⊗ free I') fun j ↦ unit _ ◁ ιFree j)
      (fun _ ↦ isColimitCofanMkObjOfIsColimit (tensorLeft (unit _)) _ _
        (isColimitFreeCofan (R := ringCatSheaf R) I'))
      (Cofan.mk (free I ⊗ free I') fun i ↦ ιFree i ▷ free I')
      (isColimitCofanMkObjOfIsColimit (tensorRight (free I')) _ _
        (isColimitFreeCofan (R := ringCatSheaf R) I)))
    (Discrete.natIso fun _ ↦ (λ_ (unit (ringCatSheaf R))).symm)
  |>.symm

/-- Under `freeTensorFreeIso`, the generator indexed by `(i, i')` is the tensor product of the
generators indexed by `i` and `i'`. -/
@[reassoc (attr := simp)]
theorem ιFree_freeTensorFreeIso_inv {I I' : Type u} (i : I) (i' : I') :
    ιFree (i, i') ≫ (freeTensorFreeIso (R := R) I I').inv =
      (λ_ (unit (ringCatSheaf R))).inv ≫ (ιFree i ⊗ₘ ιFree i') := by
  rw [tensorHom_def', freeTensorFreeIso, Iso.symm_inv]
  exact IsColimit.comp_coconePointsIsoOfNatIso_hom _ _ _ (Discrete.mk (i, i'))

variable {M N : SheafOfModules.{u} (ringCatSheaf R)}

/-- The tensor product of generating sections of `M` and `N` gives generating sections of `M ⊗ N`,
indexed by pairs of generators. -/
def _root_.SheafOfModules.GeneratingSections.tensor
    (σ : M.GeneratingSections) (τ : N.GeneratingSections) :
    (M ⊗ N).GeneratingSections where
  I := σ.I × τ.I
  s := (M ⊗ N).freeHomEquiv ((freeTensorFreeIso (R := R) σ.I τ.I).inv ≫ (σ.π ⊗ₘ τ.π))
  epi := by
    rw [Equiv.symm_apply_apply, tensorHom_def]
    have : Epi (σ.π ▷ free τ.I) := (tensorRight (free τ.I)).map_epi σ.π
    have : Epi (M ◁ τ.π) := (tensorLeft M).map_epi τ.π
    exact epi_comp _ _

/-- The tensor product of generating sections is indexed by pairs of generators. -/
@[simp]
theorem _root_.SheafOfModules.GeneratingSections.tensor_I
    (σ : M.GeneratingSections) (τ : N.GeneratingSections) :
    (σ.tensor τ).I = (σ.I × τ.I) :=
  (rfl)

/-- The generating morphism of the tensor product of generating sections is the tensor product of
the generating morphisms, read through `freeTensorFreeIso`. -/
@[simp]
theorem _root_.SheafOfModules.GeneratingSections.tensor_π
    (σ : M.GeneratingSections) (τ : N.GeneratingSections) :
    eqToHom (congrArg (free (R := ringCatSheaf R)) (σ.tensor_I τ).symm) ≫ (σ.tensor τ).π =
      (freeTensorFreeIso (R := R) σ.I τ.I).inv ≫ (σ.π ⊗ₘ τ.π) :=
  -- `tensor_I` is `rfl`, so the `eqToHom` is the identity, and `(σ.tensor τ).π` is
  -- `freeHomEquiv.symm (freeHomEquiv _)`.
  (Category.id_comp _).trans ((M ⊗ N).freeHomEquiv.symm_apply_apply _)

/-- The tensor product of two bases of generating sections has an invertible generating morphism. -/
instance _root_.SheafOfModules.GeneratingSections.isIso_tensor_π
    (σ : M.GeneratingSections) (τ : N.GeneratingSections) [IsIso σ.π] [IsIso τ.π] :
    IsIso (σ.tensor τ).π := by
  have h : IsIso (eqToHom (congrArg (free (R := ringCatSheaf R)) (σ.tensor_I τ).symm) ≫
      (σ.tensor τ).π) := by
    rw [GeneratingSections.tensor_π]
    exact IsIso.comp_isIso' (Iso.isIso_inv _) inferInstance
  exact IsIso.of_isIso_comp_left
    (eqToHom (congrArg (free (R := ringCatSheaf R)) (σ.tensor_I τ).symm)) (σ.tensor τ).π

/-- The tensor product of two finite families of generating sections is finite. -/
instance _root_.SheafOfModules.GeneratingSections.isFiniteType_tensor
    (σ : M.GeneratingSections) (τ : N.GeneratingSections) [σ.IsFiniteType] [τ.IsFiniteType] :
    (σ.tensor τ).IsFiniteType where
  finite := by
    rw [GeneratingSections.tensor_I]
    exact inferInstanceAs (Finite (σ.I × τ.I))

/-- The tensor product of presentations of `M` and `N` is a presentation of `M ⊗ N`. Its
generators are indexed by pairs of generators, and its relations by a relation of `M` paired
with a generator of `N`, or a generator of `M` paired with a relation of `N`. -/
@[expose, simps! generators_I relations_I relations_s]
def _root_.SheafOfModules.Presentation.tensor (P : M.Presentation) (Q : N.Presentation) :
    (M ⊗ N).Presentation :=
  presentationOfIsCokernelFree
    (ι := P.relations.I × Q.generators.I ⊕ P.generators.I × Q.relations.I)
    (σ := P.generators.I × Q.generators.I)
    ((freeSumIso _ _).inv ≫ coprod.map (freeTensorFreeIso _ _).inv (freeTensorFreeIso _ _).inv ≫
      coprod.desc
        (((freeHomEquiv _).symm P.relations.s ≫ kernel.ι _) ▷ free Q.generators.I)
        (free P.generators.I ◁ ((freeHomEquiv _).symm Q.relations.s ≫ kernel.ι _)) ≫
      (freeTensorFreeIso _ _).hom)
    ((freeTensorFreeIso _ _).inv ≫ (P.generators.π ⊗ₘ Q.generators.π))
    (by
      have h := ((CokernelCofork.ofπ (f := (freeHomEquiv _).symm P.relations.s ≫ kernel.ι _)
        P.generators.π (by simp)).tensor
        (CokernelCofork.ofπ (f := (freeHomEquiv _).symm Q.relations.s ≫ kernel.ι _)
          Q.generators.π (by simp))).condition
      simp only [CokernelCofork.π_ofπ] at h
      simp only [Category.assoc, Iso.hom_inv_id_assoc, h, comp_zero]) <|
  IsCokernel.ofIso _ (CokernelCofork.isColimitTensor P.isColimit Q.isColimit) _
    (coprod.mapIso (freeTensorFreeIso _ _) (freeTensorFreeIso _ _) ≪≫ freeSumIso _ _)
    (freeTensorFreeIso _ _) (Iso.refl _) (by simp) (by simp)

/-- The generating morphism of the tensor presentation is the tensor product of the generating
morphisms, read through `freeTensorFreeIso`. -/
@[simp]
theorem _root_.SheafOfModules.Presentation.tensor_generators_π (P : M.Presentation)
    (Q : N.Presentation) :
    (P.tensor Q).generators.π =
      (freeTensorFreeIso _ _).inv ≫ (P.generators.π ⊗ₘ Q.generators.π) :=
  -- As for Mathlib's `generatorsOfIsCokernelFree_π`: the generating sections of `P.tensor Q` are
  -- by construction the image under `freeHomEquiv` of the generating morphism. Rewriting with
  -- `presentationOfIsCokernelFree_generators` fails because the index type is dependent.
  (M ⊗ N).freeHomEquiv.symm_apply_apply _

/-- If the generating morphisms of `P` and `Q` are isomorphisms, that is, `P` and `Q` exhibit
`M` and `N` as free, then so is the generating morphism of `P.tensor Q`. -/
theorem _root_.SheafOfModules.Presentation.isIso_tensor_generators_π (P : M.Presentation)
    (Q : N.Presentation) (hP : IsIso P.generators.π) (hQ : IsIso Q.generators.π) :
    IsIso (P.tensor Q).generators.π := by
  rw [Presentation.tensor_generators_π]
  exact IsIso.comp_isIso' (Iso.isIso_inv _) inferInstance

/-- The tensor product of two finite presentations is finite. -/
instance _root_.SheafOfModules.Presentation.isFinite_tensor (P : M.Presentation)
    (Q : N.Presentation) [P.IsFinite] [Q.IsFinite] :
    (P.tensor Q).IsFinite where
  isFiniteType_generators := ⟨by simp only [Presentation.tensor_generators_I]; infer_instance⟩
  isFiniteType_relations := ⟨by simp only [Presentation.tensor_relations_I]; infer_instance⟩

end SheafOfModules

end

end TauCeti
