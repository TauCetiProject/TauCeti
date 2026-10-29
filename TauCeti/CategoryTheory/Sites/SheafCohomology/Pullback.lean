/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Map
public import Mathlib.CategoryTheory.Sites.SheafCohomology.ExactSequences
public import TauCeti.CategoryTheory.Sites.ConstantSheaf

/-!
# Pullback of sheaf cohomology

Let `pb : Sheaf J Ab ⥤ Sheaf K Ab` be an exact additive functor between categories of abelian
sheaves on sites `(C, J)` and `(D, K)`, together with a map `c : ℤ_K ⟶ pb ℤ_J` from the constant
sheaf `ℤ` on `(D, K)` to the image of the constant sheaf `ℤ` on `(C, J)`. Since Mathlib's sheaf
cohomology `Sheaf.H G n` is `Ext^n(ℤ_J, G)`, the pair `(pb, c)` induces
`Sheaf.H.pullback pb c G n : Hⁿ(C, G) →+ Hⁿ(D, pb G)`, the image of a class under `pb`
precomposed with `c`. Without `c` an exact functor does not specify a map on cohomology.

The main case is a morphism of sites: a continuous functor `u : C ⥤ D` that is final (for
instance representably flat) and whose sheaf pullback `u^* = u.sheafPullback` is exact. Then `c`
is the inverse of the canonical isomorphism `u^* ℤ_J ≅ ℤ_K`
(`CategoryTheory.Functor.sheafPullbackConstantSheafIso`), and `Sheaf.H.pullback` is the
pullback `Hⁿ(C, G) → Hⁿ(D, u^* G)` along the morphism of sites. (The Stacks Project, Tag 08J6,
constructs this pullback through the derived pushforward instead; that description is not
formalised here.) In degree zero it is restriction of global sections:
`Sheaf.H.equiv₀_pullback_sheafPullback`.

## Main declarations

* `CategoryTheory.Sheaf.H.pullback`: the pullback of cohomology along `(pb, c)`.
* `CategoryTheory.Sheaf.H.addEquiv₀_pullback`: in degree zero, a map `f : ℤ_J ⟶ G` goes to
  `c ≫ pb.map f`.
* `CategoryTheory.Sheaf.H.pullback_naturality`, `pullback_id`, `pullback_comp_apply`,
  `pullback_δ`:
  naturality in the coefficient sheaf, the identity, composition, and compatibility with the
  connecting homomorphisms of a short exact sequence and its image under `pb`.
* `CategoryTheory.Sheaf.H.equiv₀_pullback_sheafPullback`: for a morphism of sites, the pullback
  in degree zero is restriction of global sections along the unit of `u^* ⊣ u_*`.
-/

public section

open CategoryTheory Abelian Limits Opposite AddCommGrpCat

universe w w₁ w₂ w₃

namespace CategoryTheory.Sheaf.H

variable {C : Type*} [Category* C] {J : GrothendieckTopology C}
  {D : Type*} [Category* D] {K : GrothendieckTopology D}
  [HasSheafify J AddCommGrpCat.{w}] [HasSheafify K AddCommGrpCat.{w}]
  [HasExt.{w₁} (Sheaf J AddCommGrpCat.{w})] [HasExt.{w₂} (Sheaf K AddCommGrpCat.{w})]

section General

variable (pb : Sheaf J AddCommGrpCat.{w} ⥤ Sheaf K AddCommGrpCat.{w}) [pb.Additive]
  [PreservesFiniteLimits pb] [PreservesFiniteColimits pb]
  (c : (constantSheaf K AddCommGrpCat.{w}).obj (of (ULift ℤ)) ⟶
    pb.obj ((constantSheaf J AddCommGrpCat.{w}).obj (of (ULift ℤ))))

noncomputable section

/-- The pullback `Hⁿ(C, G) →+ Hⁿ(D, pb G)` of sheaf cohomology along an exact additive functor
`pb` between categories of abelian sheaves, given a map `c : ℤ_K ⟶ pb ℤ_J` between constant
sheaves: a class in `Ext^n(ℤ_J, G)` is sent to its image under `pb`, precomposed with `c`. -/
def pullback (G : Sheaf J AddCommGrpCat.{w}) (n : ℕ) : H G n →+ H (pb.obj G) n :=
  ((Ext.mk₀ c).precomp _ (zero_add n)).comp (pb.mapExtAddHom _ G n)

lemma pullback_apply {G : Sheaf J AddCommGrpCat.{w}} {n : ℕ} (x : H G n) :
    pullback pb c G n x = (Ext.mk₀ c).comp (x.mapExactFunctor pb) (zero_add n) := (rfl)

/-- In degree zero, the pullback sends the class of a map `f : ℤ_J ⟶ G` to `c ≫ pb.map f`. -/
@[simp]
lemma addEquiv₀_pullback {G : Sheaf J AddCommGrpCat.{w}} (x : H G 0) :
    Ext.addEquiv₀ (pullback pb c G 0 x) = c ≫ pb.map (Ext.addEquiv₀ x) := by
  obtain ⟨f, rfl⟩ := Ext.addEquiv₀.symm.surjective x
  rw [AddEquiv.apply_symm_apply, Ext.addEquiv₀_symm_apply, pullback_apply,
    Ext.mapExactFunctor_mk₀, Ext.mk₀_comp_mk₀, ← Ext.addEquiv₀_symm_apply,
    AddEquiv.apply_symm_apply]

/-- The pullback is natural in the coefficient sheaf. -/
lemma pullback_naturality {G₁ G₂ : Sheaf J AddCommGrpCat.{w}} (f : G₁ ⟶ G₂) {n : ℕ}
    (x : H G₁ n) :
    pullback pb c G₂ n (H.map f n x) = H.map (pb.map f) n (pullback pb c G₁ n x) := by
  simp [pullback_apply, H.map_apply, Ext.mapExactFunctor_comp, Ext.mapExactFunctor_mk₀]

/-- The pullback along the identity functor with the identity comparison is the identity. -/
@[simp]
lemma pullback_id (G : Sheaf J AddCommGrpCat.{w}) (n : ℕ) :
    pullback (𝟭 _) (𝟙 _) G n = AddMonoidHom.id _ := by
  ext x
  rw [pullback_apply]
  simp

/-- Elementwise form of `pullback_id`. -/
lemma pullback_id_apply (G : Sheaf J AddCommGrpCat.{w}) (n : ℕ) (x : H G n) :
    pullback (𝟭 _) (𝟙 _) G n x = x := by
  simp

/-- The pullback along a composite of exact functors is the composite of the pullbacks, for the
composite comparison `ℤ ⟶ pb₂ ℤ ⟶ pb₂ (pb₁ ℤ)`. -/
lemma pullback_comp_apply {E : Type*} [Category* E] {L : GrothendieckTopology E}
    [HasSheafify L AddCommGrpCat.{w}] [HasExt.{w₃} (Sheaf L AddCommGrpCat.{w})]
    (pb₂ : Sheaf K AddCommGrpCat.{w} ⥤ Sheaf L AddCommGrpCat.{w}) [pb₂.Additive]
    [PreservesFiniteLimits pb₂] [PreservesFiniteColimits pb₂]
    (c₂ : (constantSheaf L AddCommGrpCat.{w}).obj (of (ULift ℤ)) ⟶
      pb₂.obj ((constantSheaf K AddCommGrpCat.{w}).obj (of (ULift ℤ))))
    (G : Sheaf J AddCommGrpCat.{w}) (n : ℕ) (x : H G n) :
    pullback (pb ⋙ pb₂) (c₂ ≫ pb₂.map c) G n x =
      pullback pb₂ c₂ (pb.obj G) n (pullback pb c G n x) := by
  simp [pullback_apply, Ext.comp_mapExactFunctor, Ext.mapExactFunctor_comp,
    Ext.mapExactFunctor_mk₀]

/-- The pullback commutes with the connecting homomorphisms of a short exact sequence of
abelian sheaves and of its image under `pb`. -/
lemma pullback_δ {S : ShortComplex (Sheaf J AddCommGrpCat.{w})} (hS : S.ShortExact)
    (n₀ n₁ : ℕ) (h : n₀ + 1 = n₁) (x : H S.X₃ n₀) :
    pullback pb c S.X₁ n₁ (H.δ hS n₀ n₁ h x) =
      H.δ (hS.map_of_exact pb) n₀ n₁ h (pullback pb c S.X₃ n₀ x) := by
  simp only [pullback_apply, H.δ, AddMonoidHom.flip_apply, Ext.bilinearComp_apply_apply,
    Ext.mapExactFunctor_comp, Ext.mapExactFunctor_extClass]
  exact (Ext.comp_assoc _ _ _ (zero_add n₀) h (by lia)).symm

end

end General

end CategoryTheory.Sheaf.H

namespace CategoryTheory.Sheaf.H

variable {C : Type*} [Category* C] {J : GrothendieckTopology C}
  {D : Type*} [Category* D] {K : GrothendieckTopology D}
  [HasSheafify J AddCommGrpCat.{w}] [HasSheafify K AddCommGrpCat.{w}]
  [HasExt.{w₁} (Sheaf J AddCommGrpCat.{w})] [HasExt.{w₂} (Sheaf K AddCommGrpCat.{w})]
  (u : C ⥤ D) [u.IsContinuous J K]
  [(u.sheafPushforwardContinuous AddCommGrpCat.{w} J K).IsRightAdjoint] [u.Final]
  [PreservesFiniteLimits (u.sheafPullback AddCommGrpCat.{w} J K)]

local instance : (u.sheafPullback AddCommGrpCat.{w} J K).Additive :=
  Functor.additive_of_preserves_binary_products _

local instance : PreservesFiniteColimits (u.sheafPullback AddCommGrpCat.{w} J K) :=
  letI := (u.sheafAdjunctionContinuous AddCommGrpCat.{w} J K).leftAdjoint_preservesColimits.{0, 0}
  inferInstance

/-- For a morphism of sites `u`, the pullback in degree zero is restriction of global sections:
under `Sheaf.H.equiv₀` at a terminal object `T` of `C` whose image `u(T)` is terminal in `D`, it
is the unit `G(T) ⟶ (u^* G)(u(T))` of the adjunction `u^* ⊣ u_*`. -/
lemma equiv₀_pullback_sheafPullback {T : C} (hT : IsTerminal T) (huT : IsTerminal (u.obj T))
    (G : Sheaf J AddCommGrpCat.{w}) (x : H G 0) :
    H.equiv₀ _ huT (pullback (u.sheafPullback AddCommGrpCat.{w} J K)
      (u.sheafPullbackConstantSheafIso AddCommGrpCat.{w} J K (of (ULift ℤ))).inv G 0 x) =
      ((u.sheafAdjunctionContinuous AddCommGrpCat.{w} J K).unit.app G).hom.app (op T)
        (H.equiv₀ G hT x) := by
  obtain ⟨f, rfl⟩ := Ext.addEquiv₀.symm.surjective x
  rw [equiv₀, equiv₀, AddEquiv.trans_apply, AddEquiv.trans_apply, AddEquiv.trans_apply,
    AddEquiv.trans_apply, addEquiv₀_pullback, AddEquiv.apply_symm_apply]
  have key := congrArg (fun α => α.app (op T))
    (u.whiskerLeft_toSheafify_comp_sheafPullbackConstantSheafIso_inv AddCommGrpCat.{w} J K
      (of (ULift ℤ)))
  have nat := congrArg (fun φ => φ.hom.app (op T))
    ((u.sheafAdjunctionContinuous AddCommGrpCat.{w} J K).unit_naturality f)
  simp only [ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app,
    Functor.sheafPushforwardContinuous_map_hom_app] at nat
  have hM : (constantSheafAdj K AddCommGrpCat.{w} huT).homAddEquiv _ _
      ((u.sheafPullbackConstantSheafIso AddCommGrpCat.{w} J K (of (ULift ℤ))).inv ≫
        (u.sheafPullback AddCommGrpCat.{w} J K).map f) =
      (constantSheafAdj J AddCommGrpCat.{w} hT).homAddEquiv _ _ f ≫
        ((u.sheafAdjunctionContinuous AddCommGrpCat.{w} J K).unit.app G).hom.app (op T) := by
    -- `constantSheafAdj` is the composite of `constantPresheafAdj` with sheafification, whose left
    -- adjoint is `Functor.const _ ⋙ presheafToSheaf _ _`, the definition of `constantSheaf`.
    -- Unfolding `constantSheaf` lets the lemmas on composite adjunctions match syntactically.
    unfold constantSheaf at f key ⊢
    simp only [Adjunction.homAddEquiv, constantSheafAdj, AddEquiv.coe_mk, Adjunction.comp_homEquiv,
      Equiv.trans_apply, Adjunction.homEquiv_unit, Functor.comp_obj, Functor.op_obj,
      Functor.const_obj_obj, Functor.whiskerLeft_comp, NatTrans.comp_app, Functor.whiskerLeft_app,
      Functor.id_obj, Functor.flip_obj_obj, ObjectProperty.ι_obj, evaluation_obj_obj,
      constantPresheafAdj_unit_app, evaluation_obj_map, Category.id_comp] at key ⊢
    exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) key).trans
      ((Category.assoc _ _ _).trans (congrArg (_ ≫ ·) nat)))
  rw [hM]
  -- Both sides evaluate the same morphism `ℤ ⟶ (u^* G)(u(T))` at `1`.
  rfl

end CategoryTheory.Sheaf.H
