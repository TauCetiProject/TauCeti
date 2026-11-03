/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Almost.Module

/-!
# Linear representatives of almost morphisms

For a basic setup `(V, m)`, morphisms `Mᵃ → Nᵃ` are naturally identified with linear maps
`(m ⊗[V] m) ⊗[V] M →ₗ[V] N`. The comparison uses the equivalence with firm modules and the
adjunction between their inclusion and firmification. It is linear and natural in both modules.

## References

* O. Gabber, L. Ramero, *Almost ring theory*, §2.2, (2.2.4).
* B. Bhatt, *Lecture notes for a class on perfectoid spaces*, §4.1, Proposition 4.1.7.
-/

public section

open CategoryTheory TensorProduct

namespace TauCeti.Almost.Module

universe u

variable {V : Type u} [CommRing V] (S : BasicSetup V)

/-- The equivalence between the Serre quotient of modules and the firm-module model. -/
noncomputable def firmEquiv : Module S ≌ S.Firm :=
  Localization.uniq (toAlmost S) S.firm S.almostZero.isoModSerre

/-- The firm representative of an almostification is its firmification. -/
noncomputable def toAlmostCompFirmIso : toAlmost S ⋙ (firmEquiv S).functor ≅ S.firm :=
  Localization.compUniqFunctor (toAlmost S) S.firm S.almostZero.isoModSerre

noncomputable instance :
    Localization.Lifting (toAlmost S) S.almostZero.isoModSerre S.firm (firmEquiv S).functor :=
  ⟨toAlmostCompFirmIso S⟩

instance : (firmEquiv S).functor.Linear V :=
  (Localization.functor_linear_iff (toAlmost S) S.almostZero.isoModSerre V S.firm
    (firmEquiv S).functor).mp inferInstance

instance : (firmEquiv S).functor.Additive :=
  Functor.additive_of_preserves_binary_products _

private noncomputable def homEquiv (M N : ModuleCat.{u} V) :
    ((toAlmost S).obj M ⟶ (toAlmost S).obj N) ≃ (S.isFirm.ι.obj (S.firm.obj M) ⟶ N) :=
  (firmEquiv S).fullyFaithfulFunctor.homEquiv.trans <|
    (Iso.homCongr ((toAlmostCompFirmIso S).app M) ((toAlmostCompFirmIso S).app N)).trans
      (S.firmInclusionAdj.homEquiv (S.firm.obj M) N).symm

private theorem homEquiv_apply (M N : ModuleCat.{u} V)
    (f : (toAlmost S).obj M ⟶ (toAlmost S).obj N) :
    homEquiv S M N f = S.isFirm.ι.map ((toAlmostCompFirmIso S).inv.app M ≫
      (firmEquiv S).functor.map f ≫ (toAlmostCompFirmIso S).hom.app N) ≫
        S.firmInclusionAdj.counit.app N := by
  exact S.firmInclusionAdj.homEquiv_symm_apply (S.firm.obj M) N _

private noncomputable def homEquivLinear (M N : ModuleCat.{u} V) :
    ((toAlmost S).obj M ⟶ (toAlmost S).obj N) ≃ₗ[V] (S.isFirm.ι.obj (S.firm.obj M) ⟶ N) where
  toEquiv := homEquiv S M N
  map_add' f g := by
    -- The structure field uses `Equiv.toFun`; expose its coercion for the characteristic lemma.
    change homEquiv S M N (f + g) = homEquiv S M N f + homEquiv S M N g
    rw [homEquiv_apply S M N (f + g), homEquiv_apply S M N f, homEquiv_apply S M N g]
    simp only [Functor.map_add, Preadditive.add_comp, Preadditive.comp_add]
  map_smul' r f := by
    -- As above, use the equivalence coercion rather than the inherited `toFun` projection.
    change homEquiv S M N (r • f) = r • homEquiv S M N f
    rw [homEquiv_apply S M N (r • f), homEquiv_apply S M N f]
    simp only [Functor.map_smul, Linear.smul_comp, Linear.comp_smul]

/-- A morphism of almostifications has a unique linear representative on `m~ ⊗ M`.
This is Gabber–Ramero's almost-Hom formula (2.2.4). -/
noncomputable def homLinearEquiv (M N : ModuleCat.{u} V) :
    ((toAlmost S).obj M ⟶ (toAlmost S).obj N) ≃ₗ[V] (S.tilde ⊗[V] M →ₗ[V] N) :=
  (homEquivLinear S M N).trans <|
    (Linear.homCongr V (eqToIso (S.firm_obj_obj M)) (Iso.refl N)).trans
      (ModuleCat.homLinearEquiv (S := V))

private theorem ofHom_homLinearEquiv (M N : ModuleCat.{u} V)
    (f : (toAlmost S).obj M ⟶ (toAlmost S).obj N) :
    (ModuleCat.ofHom (homLinearEquiv S M N f) : ModuleCat.of V (S.tilde ⊗[V] M) ⟶ N) =
      (eqToIso (S.firm_obj_obj M)).inv ≫ homEquiv S M N f := by
  rfl

private theorem firm_map_homEquiv (M N : ModuleCat.{u} V)
    (f : (toAlmost S).obj M ⟶ (toAlmost S).obj N) :
    S.firm.map (homEquiv S M N f) = S.firm.map (S.firmInclusionAdj.counit.app M) ≫
      (toAlmostCompFirmIso S).inv.app M ≫ (firmEquiv S).functor.map f ≫
        (toAlmostCompFirmIso S).hom.app N := by
  apply (cancel_epi (S.firmInclusionAdj.unit.app (S.firm.obj M))).mp
  have h := (S.firmInclusionAdj.homEquiv (S.firm.obj M) N).apply_symm_apply
    ((toAlmostCompFirmIso S).inv.app M ≫ (firmEquiv S).functor.map f ≫
      (toAlmostCompFirmIso S).hom.app N)
  rw [Adjunction.homEquiv_apply] at h
  refine h.trans ?_
  exact ((Category.id_comp _).symm.trans
    (congrArg (fun g => g ≫ _) (S.firmInclusionAdj.right_triangle_components M).symm)).trans
      (Category.assoc _ _ _)

/-- Almostifying the linear representative of `f` is precomposition of `f` with the action
map `m~ ⊗ M → M`. This equation fixes the comparison without unfolding its construction. -/
theorem homLinearEquiv_apply (M N : ModuleCat.{u} V)
    (f : (toAlmost S).obj M ⟶ (toAlmost S).obj N) :
    (toAlmost S).map (ModuleCat.ofHom (homLinearEquiv S M N f) :
      ModuleCat.of V (S.tilde ⊗[V] M) ⟶ N) =
      (toAlmost S).map (ModuleCat.ofHom (S.tildeAct M) :
        ModuleCat.of V (S.tilde ⊗[V] M) ⟶ M) ≫ f := by
  have act : (eqToIso (S.firm_obj_obj M)).inv ≫ S.firmInclusionAdj.counit.app M =
      (ModuleCat.ofHom (S.tildeAct M) : ModuleCat.of V (S.tilde ⊗[V] M) ⟶ M) := by
    apply ModuleCat.hom_ext
    simp only [ModuleCat.hom_comp, BasicSetup.firmInclusionAdj_counit_app_hom]
    rfl
  apply (firmEquiv S).functor.map_injective
  rw [Functor.map_comp, ← Functor.comp_map, ← NatIso.naturality_2 (toAlmostCompFirmIso S),
    ← Functor.comp_map, ← NatIso.naturality_2 (toAlmostCompFirmIso S),
    ofHom_homLinearEquiv, Functor.map_comp, firm_map_homEquiv]
  simp only [Category.assoc]
  rw [← Category.assoc (S.firm.map (eqToIso (S.firm_obj_obj M)).inv),
    ← Functor.map_comp, act]
  rw [Iso.hom_inv_id_app (toAlmostCompFirmIso S) N]
  simp only [Functor.comp_obj, Category.comp_id]

/-- The action map is inverted by almostification. -/
instance isIso_toAlmost_map_tildeAct (M : ModuleCat.{u} V) :
    IsIso ((toAlmost S).map (ModuleCat.ofHom (S.tildeAct M) :
      ModuleCat.of V (S.tilde ⊗[V] M) ⟶ M)) :=
  (isIso_toAlmost_map_iff S _).mpr (S.isAlmostIso_tildeAct M)

/-- Recover an almost morphism from its linear representative by inverting the almostified
action map. -/
theorem homLinearEquiv_symm_apply (M N : ModuleCat.{u} V)
    (g : S.tilde ⊗[V] M →ₗ[V] N) :
    (homLinearEquiv S M N).symm g =
      inv ((toAlmost S).map (ModuleCat.ofHom (S.tildeAct M) :
        ModuleCat.of V (S.tilde ⊗[V] M) ⟶ M)) ≫
          (toAlmost S).map (ModuleCat.ofHom g : ModuleCat.of V (S.tilde ⊗[V] M) ⟶ N) := by
  apply (cancel_epi ((toAlmost S).map (ModuleCat.ofHom (S.tildeAct M) :
    ModuleCat.of V (S.tilde ⊗[V] M) ⟶ M))).mp
  rw [← homLinearEquiv_apply, LinearEquiv.apply_symm_apply]
  simp

/-- The representative of an almostified ordinary morphism is its composite with the action
map. -/
@[simp]
theorem homLinearEquiv_toAlmost_map {M N : ModuleCat.{u} V} (g : M ⟶ N) :
    homLinearEquiv S M N ((toAlmost S).map g) = g.hom ∘ₗ S.tildeAct M := by
  apply (homLinearEquiv S M N).symm.injective
  rw [LinearEquiv.symm_apply_apply, homLinearEquiv_symm_apply]
  have h : (ModuleCat.ofHom (g.hom ∘ₗ S.tildeAct M) :
      ModuleCat.of V (S.tilde ⊗[V] M) ⟶ N) =
      (ModuleCat.ofHom (S.tildeAct M) : ModuleCat.of V (S.tilde ⊗[V] M) ⟶ M) ≫ g := rfl
  rw [h, Functor.map_comp]
  simp

/-- The identity almost morphism is represented by the action map. -/
@[simp]
theorem homLinearEquiv_id (M : ModuleCat.{u} V) :
    homLinearEquiv S M M (𝟙 _) = S.tildeAct M := by
  simpa using homLinearEquiv_toAlmost_map S (𝟙 M)

/-- Linear representatives are natural in both ordinary modules. -/
theorem homLinearEquiv_natural {M' M N N' : ModuleCat.{u} V} (a : M' ⟶ M) (b : N ⟶ N')
    (f : (toAlmost S).obj M ⟶ (toAlmost S).obj N) :
    homLinearEquiv S M' N' ((toAlmost S).map a ≫ f ≫ (toAlmost S).map b) =
      b.hom ∘ₗ homLinearEquiv S M N f ∘ₗ a.hom.lTensor S.tilde := by
  apply (homLinearEquiv S M' N').symm.injective
  rw [LinearEquiv.symm_apply_apply, homLinearEquiv_symm_apply]
  apply (IsIso.eq_inv_comp _).mpr
  have h : (ModuleCat.ofHom (S.tildeAct M') :
      ModuleCat.of V (S.tilde ⊗[V] M') ⟶ M') ≫ a =
      (ModuleCat.ofHom (a.hom.lTensor S.tilde) :
        ModuleCat.of V (S.tilde ⊗[V] M') ⟶ ModuleCat.of V (S.tilde ⊗[V] M)) ≫
          (ModuleCat.ofHom (S.tildeAct M) : ModuleCat.of V (S.tilde ⊗[V] M) ⟶ M) := by
    apply ModuleCat.hom_ext
    exact (S.tildeAct_comp_lTensor a.hom).symm
  rw [← Category.assoc, ← Category.assoc, ← Functor.map_comp, h, Functor.map_comp]
  simp only [Category.assoc]
  rw [← Category.assoc _ f ((toAlmost S).map b), ← homLinearEquiv_apply S M N f]
  rw [← Functor.map_comp, ← Functor.map_comp]
  rfl

/-- Hom-modules of almost modules contain no nonzero almost zero elements. -/
theorem hom_eq_zero_of_ideal_smul {M N : Module S} (f : M ⟶ N)
    (hf : ∀ ε ∈ S.ideal, ε • f = 0) : f = 0 := by
  apply (firmEquiv S).functor.map_injective
  rw [Functor.map_zero]
  apply S.isFirm.ι.map_injective
  rw [Functor.map_zero]
  apply ModuleCat.hom_ext
  rw [ModuleCat.hom_zero]
  apply ((S.isFirm_iff _).mp ((firmEquiv S).functor.obj M).property).linearMap_eq_zero_of_ideal_smul
  intro ε hε
  have h := congrArg (fun g => (S.isFirm.ι.map ((firmEquiv S).functor.map g)).hom) (hf ε hε)
  simpa only [Functor.map_smul, Functor.map_zero, ModuleCat.hom_smul, ModuleCat.hom_zero] using h

end TauCeti.Almost.Module
