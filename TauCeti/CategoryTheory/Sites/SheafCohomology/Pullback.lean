/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Map
public import Mathlib.CategoryTheory.Sites.SheafCohomology.ExactSequences
public import Mathlib.CategoryTheory.Sites.SheafCohomology.MayerVietoris
public import TauCeti.CategoryTheory.Sites.ConstantSheaf
public import TauCeti.CategoryTheory.Sites.SheafCohomology.FreeYoneda

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
* `CategoryTheory.Functor.sheafPullback_additive`, `preservesFiniteColimits_sheafPullback`: the
  pullback of abelian sheaves along a continuous functor is additive and right exact, as a left
  adjoint.

## Cohomology over objects and Mayer-Vietoris sequences

The same construction applies to the cohomology `Hⁿ(U, G) = Ext^n(ℤ[U], G)` over an object `U` of
the site, where `ℤ[U]` is the free abelian sheaf on `U`. Now the comparison is a natural
transformation `c : ℤ[u(-)] ⟶ pb ℤ[-]` along a functor `u : C ⥤ D`; for a continuous functor `u`
with pullback `u^*` it is `CategoryTheory.Functor.freeYonedaSheafToSheafPullback`. Given a
morphism `ψ : V ⟶ u(U)`, a class over `U` is sent by `pb` and precomposition with
`ℤ[V] ⟶ ℤ[u(U)] ⟶ pb ℤ[U]` to a class over `V`. These maps commute with restriction on both
sides, and they map the Mayer-Vietoris sequence of a Mayer-Vietoris square `S` in `C` to that of a
Mayer-Vietoris square `S'` in `D` equipped with a morphism of squares from `S'` to the image of `S`
under `u`. For the inverse image along a continuous map, this compares the Mayer-Vietoris
sequences of two open subsets and of their preimages. Such comparisons drive Mayer-Vietoris
inductions over the affine opens of a quasi-compact quasi-separated scheme, transporting a
statement about the cohomology of quasi-coherent sheaves from affine opens to the whole scheme.

* `CategoryTheory.Sheaf.H'.pullback`: the pullback `Hⁿ(U, G) ⟶ Hⁿ(V, pb G)` along `ψ`.
* `CategoryTheory.Sheaf.H'.pullback_comp_map`, `map_comp_pullback`: compatibility with
  restriction.
* `CategoryTheory.Sheaf.H'.addEquiv₀_pullback`: in degree zero, the pullback of the class of
  `g : ℤ[U] ⟶ G` is the class of `ℤ[V] ⟶ ℤ[u(U)] ⟶ pb ℤ[U] ⟶ pb G`.
* `CategoryTheory.Sheaf.H'.toBiprod_comp_pullback`, `fromBiprod_comp_pullback`,
  `δ_comp_pullback`, and `mayerVietorisSequencePullback`: the morphism between the
  Mayer-Vietoris sequences, with components `mayerVietorisSequencePullback_app_zero` through
  `mayerVietorisSequencePullback_app_five`.
* `CategoryTheory.Sheaf.H'.cohomologyZeroSectionsEquiv_pullback_sheafPullback`: for a morphism
  of sites, the pullback in degree zero is the unit of `u^* ⊣ u_*` on sections over `U`,
  followed by restriction along `ψ`.
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

namespace CategoryTheory.Functor

variable {C : Type*} [Category* C] {J : GrothendieckTopology C}
  {D : Type*} [Category* D] {K : GrothendieckTopology D}
  (u : C ⥤ D) [u.IsContinuous J K]
  [(u.sheafPushforwardContinuous AddCommGrpCat.{w} J K).IsRightAdjoint]

/-- The pullback of abelian sheaves along a continuous functor is additive, as a left adjoint. -/
instance sheafPullback_additive : (u.sheafPullback AddCommGrpCat.{w} J K).Additive :=
  haveI : (u.sheafPushforwardContinuous AddCommGrpCat.{w} J K).Additive :=
    Functor.additive_of_preserves_binary_products _
  (u.sheafAdjunctionContinuous AddCommGrpCat.{w} J K).left_adjoint_additive

/-- The pullback of abelian sheaves along a continuous functor preserves finite colimits, as a
left adjoint. -/
instance preservesFiniteColimits_sheafPullback :
    PreservesFiniteColimits (u.sheafPullback AddCommGrpCat.{w} J K) :=
  letI := (u.sheafAdjunctionContinuous AddCommGrpCat.{w} J K).leftAdjoint_preservesColimits.{0, 0}
  inferInstance

end CategoryTheory.Functor

namespace CategoryTheory.Sheaf.H

variable {C : Type*} [Category* C] {J : GrothendieckTopology C}
  {D : Type*} [Category* D] {K : GrothendieckTopology D}
  [HasSheafify J AddCommGrpCat.{w}] [HasSheafify K AddCommGrpCat.{w}]
  [HasExt.{w₁} (Sheaf J AddCommGrpCat.{w})] [HasExt.{w₂} (Sheaf K AddCommGrpCat.{w})]
  (u : C ⥤ D) [u.IsContinuous J K]
  [(u.sheafPushforwardContinuous AddCommGrpCat.{w} J K).IsRightAdjoint] [u.Final]
  [PreservesFiniteLimits (u.sheafPullback AddCommGrpCat.{w} J K)]

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

namespace CategoryTheory.Sheaf.H'

open TauCeti TauCeti.CategoryTheory

universe v u₁ u₂

variable {C : Type u₁} [Category.{v} C] {J : GrothendieckTopology C}
  {D : Type u₂} [Category.{v} D] {K : GrothendieckTopology D}
  [HasSheafify J AddCommGrpCat.{v}] [HasSheafify K AddCommGrpCat.{v}]
  (pb : Sheaf J AddCommGrpCat.{v} ⥤ Sheaf K AddCommGrpCat.{v}) [pb.Additive]
  {u : C ⥤ D} (c : u ⋙ freeYonedaSheafFunctor K ⟶ freeYonedaSheafFunctor J ⋙ pb)

noncomputable section

section Comparison

omit [pb.Additive] in
@[reassoc]
private lemma map_comp_app_comp_map {U₁ U₂ : C} {V : D} (ψ : V ⟶ u.obj U₁) (i : U₁ ⟶ U₂) :
    (freeYonedaSheafFunctor K).map ψ ≫ c.app U₁ ≫ pb.map ((freeYonedaSheafFunctor J).map i) =
      (freeYonedaSheafFunctor K).map (ψ ≫ u.map i) ≫ c.app U₂ := by
  rw [Functor.map_comp, Category.assoc]
  exact congrArg _ (c.naturality i).symm

omit [pb.Additive] in
private lemma map_comp_app_comp_map_of_comm {U₁ U₂ : C} {V₁ V₂ : D} (ψ₁ : V₁ ⟶ u.obj U₁)
    (ψ₂ : V₂ ⟶ u.obj U₂) (i : U₁ ⟶ U₂) (j : V₁ ⟶ V₂) (h : j ≫ ψ₂ = ψ₁ ≫ u.map i) :
    ((freeYonedaSheafFunctor K).map ψ₁ ≫ c.app U₁) ≫ pb.map ((freeYonedaSheafFunctor J).map i) =
      (freeYonedaSheafFunctor K).map j ≫ (freeYonedaSheafFunctor K).map ψ₂ ≫ c.app U₂ := by
  rw [Category.assoc, map_comp_app_comp_map, ← h, Functor.map_comp, Category.assoc]

/-- The square relating the first maps of the short complexes of free sheaves of two
Mayer-Vietoris squares, in terms of the squares relating their components. -/
private lemma comp_map_biprod_lift {A₁ A₂ A₃ : Sheaf K AddCommGrpCat.{v}}
    {B₁ B₂ B₃ : Sheaf J AddCommGrpCat.{v}} {a₁ : A₁ ⟶ pb.obj B₁} {a₂ : A₂ ⟶ pb.obj B₂}
    {a₃ : A₃ ⟶ pb.obj B₃} {x : B₁ ⟶ B₂} {x' : B₁ ⟶ B₃} {y : A₁ ⟶ A₂} {y' : A₁ ⟶ A₃}
    (h : a₁ ≫ pb.map x = y ≫ a₂) (h' : a₁ ≫ pb.map x' = y' ≫ a₃) :
    a₁ ≫ pb.map (biprod.lift x (-x')) =
      biprod.lift y (-y') ≫ biprod.desc (a₂ ≫ pb.map biprod.inl) (a₃ ≫ pb.map biprod.inr) := by
  rw [biprod.lift_desc, biprod.lift_eq]
  simp only [Functor.map_add, Functor.map_comp, Functor.map_neg, Preadditive.comp_add,
    Preadditive.comp_neg, Preadditive.neg_comp, reassoc_of% h, reassoc_of% h']

omit [pb.Additive] in
/-- The square relating the second maps of the short complexes of free sheaves of two
Mayer-Vietoris squares, in terms of the squares relating their components. -/
private lemma biprod_desc_comp_map {A₂ A₃ A₄ : Sheaf K AddCommGrpCat.{v}}
    {B₂ B₃ B₄ : Sheaf J AddCommGrpCat.{v}} {a₂ : A₂ ⟶ pb.obj B₂} {a₃ : A₃ ⟶ pb.obj B₃}
    {a₄ : A₄ ⟶ pb.obj B₄} {z : B₂ ⟶ B₄} {z' : B₃ ⟶ B₄} {w : A₂ ⟶ A₄} {w' : A₃ ⟶ A₄}
    (h : a₂ ≫ pb.map z = w ≫ a₄) (h' : a₃ ≫ pb.map z' = w' ≫ a₄) :
    biprod.desc (a₂ ≫ pb.map biprod.inl) (a₃ ≫ pb.map biprod.inr) ≫ pb.map (biprod.desc z z') =
      biprod.desc w w' ≫ a₄ := by
  apply biprod.hom_ext'
  · rw [biprod.inl_desc_assoc, biprod.inl_desc_assoc, Category.assoc, ← Functor.map_comp,
      biprod.inl_desc, h]
  · rw [biprod.inr_desc_assoc, biprod.inr_desc_assoc, Category.assoc, ← Functor.map_comp,
      biprod.inr_desc, h']

/-- The short complex `ℤ[S'.X₁] ⟶ ℤ[S'.X₂] ⊞ ℤ[S'.X₃] ⟶ ℤ[S'.X₄]` of a Mayer-Vietoris square `S'`
maps to the image under `pb` of that of `S`, through `ψ` and `c`. -/
private def shortComplexMap [HasWeakSheafify J (Type v)] [HasWeakSheafify K (Type v)]
    (S : J.MayerVietorisSquare) (S' : K.MayerVietorisSquare)
    (ψ : S'.toSquare ⟶ S.toSquare.map u) :
    S'.shortComplex ⟶ S.shortComplex.map pb where
  τ₁ := (freeYonedaSheafFunctor K).map ψ.τ₁ ≫ c.app S.X₁
  τ₂ := biprod.desc (((freeYonedaSheafFunctor K).map ψ.τ₂ ≫ c.app S.X₂) ≫ pb.map biprod.inl)
      (((freeYonedaSheafFunctor K).map ψ.τ₃ ≫ c.app S.X₃) ≫ pb.map biprod.inr)
  τ₃ := (freeYonedaSheafFunctor K).map ψ.τ₄ ≫ c.app S.X₄
  comm₁₂ := comp_map_biprod_lift pb
    (map_comp_app_comp_map_of_comm pb c ψ.τ₁ ψ.τ₂ S.f₁₂ S'.f₁₂ ψ.comm₁₂)
    (map_comp_app_comp_map_of_comm pb c ψ.τ₁ ψ.τ₃ S.f₁₃ S'.f₁₃ ψ.comm₁₃)
  comm₂₃ := biprod_desc_comp_map pb
    (map_comp_app_comp_map_of_comm pb c ψ.τ₂ ψ.τ₄ S.f₂₄ S'.f₂₄ ψ.comm₂₄)
    (map_comp_app_comp_map_of_comm pb c ψ.τ₃ ψ.τ₄ S.f₃₄ S'.f₃₄ ψ.comm₃₄)

end Comparison

variable [HasExt.{w} (Sheaf J AddCommGrpCat.{v})] [HasExt.{w} (Sheaf K AddCommGrpCat.{v})]
  [PreservesFiniteLimits pb] [PreservesFiniteColimits pb]

/-- The pullback `Hⁿ(U, G) ⟶ Hⁿ(V, pb G)` of the cohomology over an object `U` of `C` along an exact
additive functor `pb` and a natural comparison `c : ℤ[u(-)] ⟶ pb ℤ[-]` of free abelian sheaves,
for a morphism `ψ : V ⟶ u(U)` in `D`: a class in `Ext^n(ℤ[U], G)` is sent to its image under
`pb`, precomposed with `ℤ[V] ⟶ ℤ[u(U)] ⟶ pb ℤ[U]`. -/
def pullback (G : Sheaf J AddCommGrpCat.{v}) (n : ℕ) {U : C} {V : D} (ψ : V ⟶ u.obj U) :
    G.H' n U ⟶ (pb.obj G).H' n V :=
  AddCommGrpCat.ofHom (((Ext.mk₀ ((freeYonedaSheafFunctor K).map ψ ≫ c.app U)).precomp _
    (zero_add n)).comp (pb.mapExtAddHom _ G n))

/-- The defining formula of `pullback`. -/
lemma pullback_apply (G : Sheaf J AddCommGrpCat.{v}) (n : ℕ) {U : C} {V : D}
    (ψ : V ⟶ u.obj U) (x : G.H' n U) :
    pullback pb c G n ψ x = (Ext.mk₀ ((freeYonedaSheafFunctor K).map ψ ≫ c.app U)).comp
      (Ext.mapExactFunctor pb x) (zero_add n) :=
  (rfl)

/-- Restricting the pullback along `j : V' ⟶ V` is pulling back along `j ≫ ψ`. -/
@[reassoc]
lemma pullback_comp_map (G : Sheaf J AddCommGrpCat.{v}) (n : ℕ) {U : C} {V V' : D}
    (ψ : V ⟶ u.obj U) (j : V' ⟶ V) :
    pullback pb c G n ψ ≫ ((pb.obj G).cohomologyPresheaf n).map j.op =
      pullback pb c G n (j ≫ ψ) := by
  refine AddCommGrpCat.ext fun (x : Ext ((freeYonedaSheafFunctor J).obj U) G n) ↦ ?_
  -- The groups `H'` are by definition `Ext` groups out of free sheaves, and the restriction maps
  -- are precompositions with the induced maps of free sheaves.
  change (Ext.mk₀ ((freeYonedaSheafFunctor K).map j)).comp
      ((Ext.mk₀ ((freeYonedaSheafFunctor K).map ψ ≫ c.app U)).comp (x.mapExactFunctor pb)
        (zero_add n)) (zero_add n) =
    (Ext.mk₀ ((freeYonedaSheafFunctor K).map (j ≫ ψ) ≫ c.app U)).comp (x.mapExactFunctor pb)
      (zero_add n)
  rw [Ext.mk₀_comp_mk₀_assoc, Functor.map_comp, Category.assoc]

/-- Pulling back after restricting along `i : U₁ ⟶ U₂` is pulling back along `ψ ≫ u(i)`. -/
@[reassoc]
lemma map_comp_pullback (G : Sheaf J AddCommGrpCat.{v}) (n : ℕ) {U₁ U₂ : C} {V : D}
    (i : U₁ ⟶ U₂) (ψ : V ⟶ u.obj U₁) :
    (G.cohomologyPresheaf n).map i.op ≫ pullback pb c G n ψ =
      pullback pb c G n (ψ ≫ u.map i) := by
  refine AddCommGrpCat.ext fun (x : Ext ((freeYonedaSheafFunctor J).obj U₂) G n) ↦ ?_
  -- As in `pullback_comp_map`, the restriction map is precomposition of `Ext` classes.
  change (Ext.mk₀ ((freeYonedaSheafFunctor K).map ψ ≫ c.app U₁)).comp
      (((Ext.mk₀ ((freeYonedaSheafFunctor J).map i)).comp x (zero_add n)).mapExactFunctor pb)
        (zero_add n) =
    (Ext.mk₀ ((freeYonedaSheafFunctor K).map (ψ ≫ u.map i) ≫ c.app U₂)).comp
      (x.mapExactFunctor pb) (zero_add n)
  rw [Ext.mapExactFunctor_comp, Ext.mapExactFunctor_mk₀, Ext.mk₀_comp_mk₀_assoc, Category.assoc,
    map_comp_app_comp_map]

/-- In degree zero, the pullback sends the class of a map `g : ℤ[U] ⟶ G` to the composite
`ℤ[V] ⟶ ℤ[u(U)] ⟶ pb ℤ[U] ⟶ pb G`. -/
@[simp]
lemma addEquiv₀_pullback (G : Sheaf J AddCommGrpCat.{v}) {U : C} {V : D} (ψ : V ⟶ u.obj U)
    (x : G.H' 0 U) :
    Ext.addEquiv₀ (X := (freeYonedaSheafFunctor K).obj V) (pullback pb c G 0 ψ x) =
      (freeYonedaSheafFunctor K).map ψ ≫ c.app U ≫
        pb.map (Ext.addEquiv₀ (X := (freeYonedaSheafFunctor J).obj U) x) := by
  obtain ⟨g, rfl⟩ :=
    (Ext.addEquiv₀ (X := (freeYonedaSheafFunctor J).obj U) (Y := G)).symm.surjective x
  refine (ext_addEquiv₀_mk₀_comp _ ((Ext.addEquiv₀.symm g).mapExactFunctor pb)).trans ?_
  rw [AddEquiv.apply_symm_apply, Ext.addEquiv₀_symm_apply, Ext.mapExactFunctor_mk₀,
    ← Ext.addEquiv₀_symm_apply, AddEquiv.apply_symm_apply, Category.assoc]

section MayerVietoris

variable [HasWeakSheafify J (Type v)] [HasWeakSheafify K (Type v)]
  (S : J.MayerVietorisSquare) (S' : K.MayerVietorisSquare) (ψ : S'.toSquare ⟶ S.toSquare.map u)

/-- The pullback commutes with the first maps of the Mayer-Vietoris sequences of `S` and `S'`,
the sums of the restriction maps. -/
@[reassoc]
lemma toBiprod_comp_pullback (G : Sheaf J AddCommGrpCat.{v}) (n : ℕ) :
    S.toBiprod G n ≫ biprod.map (pullback pb c G n ψ.τ₂) (pullback pb c G n ψ.τ₃) =
      pullback pb c G n ψ.τ₄ ≫ S'.toBiprod (pb.obj G) n := by
  obtain ⟨ψ₁, ψ₂, ψ₃, ψ₄, -, -, h₂, h₃⟩ := ψ
  -- The components of `ψ` land in the objects of `S.toSquare.map u`, which are the images under
  -- `u` of those of `S` only after unfolding `Square.map`.
  change S'.X₂ ⟶ u.obj S.X₂ at ψ₂
  change S'.X₃ ⟶ u.obj S.X₃ at ψ₃
  change S'.X₄ ⟶ u.obj S.X₄ at ψ₄
  change S'.f₂₄ ≫ ψ₄ = ψ₂ ≫ u.map S.f₂₄ at h₂
  change S'.f₃₄ ≫ ψ₄ = ψ₃ ≫ u.map S.f₃₄ at h₃
  dsimp only
  apply biprod.hom_ext
  · simp only [GrothendieckTopology.MayerVietorisSquare.toBiprod, Category.assoc, biprod.map_fst,
      biprod.lift_fst, biprod.lift_fst_assoc]
    rw [map_comp_pullback, pullback_comp_map, h₂]
  · simp only [GrothendieckTopology.MayerVietorisSquare.toBiprod, Category.assoc, biprod.map_snd,
      biprod.lift_snd, biprod.lift_snd_assoc]
    rw [map_comp_pullback, pullback_comp_map, h₃]

/-- The pullback commutes with the middle maps of the Mayer-Vietoris sequences of `S` and `S'`,
the differences of the restriction maps. -/
@[reassoc]
lemma fromBiprod_comp_pullback (G : Sheaf J AddCommGrpCat.{v}) (n : ℕ) :
    S.fromBiprod G n ≫ pullback pb c G n ψ.τ₁ =
      biprod.map (pullback pb c G n ψ.τ₂) (pullback pb c G n ψ.τ₃) ≫
        S'.fromBiprod (pb.obj G) n := by
  obtain ⟨ψ₁, ψ₂, ψ₃, ψ₄, h₂, h₃, -, -⟩ := ψ
  -- As in `toBiprod_comp_pullback`, read the components of `ψ` on the objects of `S`.
  change S'.X₁ ⟶ u.obj S.X₁ at ψ₁
  change S'.X₂ ⟶ u.obj S.X₂ at ψ₂
  change S'.X₃ ⟶ u.obj S.X₃ at ψ₃
  change S'.f₁₂ ≫ ψ₂ = ψ₁ ≫ u.map S.f₁₂ at h₂
  change S'.f₁₃ ≫ ψ₃ = ψ₁ ≫ u.map S.f₁₃ at h₃
  dsimp only
  apply biprod.hom_ext'
  · simp only [GrothendieckTopology.MayerVietorisSquare.fromBiprod, biprod.inl_desc_assoc,
      biprod.inl_map_assoc, biprod.inl_desc]
    rw [map_comp_pullback, pullback_comp_map, h₂]
  · simp only [GrothendieckTopology.MayerVietorisSquare.fromBiprod, biprod.inr_desc_assoc,
      biprod.inr_map_assoc, biprod.inr_desc, Preadditive.neg_comp, Preadditive.comp_neg]
    rw [map_comp_pullback, pullback_comp_map, h₃]

/-- The pullback commutes with the connecting maps of the Mayer-Vietoris sequences of `S` and
`S'`. -/
@[reassoc]
lemma δ_comp_pullback (G : Sheaf J AddCommGrpCat.{v}) (n₀ n₁ : ℕ) (h : n₀ + 1 = n₁) :
    S.δ G n₀ n₁ h ≫ pullback pb c G n₁ ψ.τ₄ =
      pullback pb c G n₀ ψ.τ₁ ≫ S'.δ (pb.obj G) n₀ n₁ h := by
  let φ := shortComplexMap pb c S S' ψ
  have hS := S.shortComplex_shortExact
  have hS' := S'.shortComplex_shortExact
  refine AddCommGrpCat.ext fun (x : Ext S.shortComplex.X₁ G n₀) ↦ ?_
  -- The connecting maps are precomposition with the extension classes of the short exact
  -- sequences of free sheaves, and `pullback` is precomposition after applying `pb`; the
  -- extension classes are compatible along the morphism `φ` of short exact sequences.
  change (Ext.mk₀ φ.τ₃).comp ((hS.extClass.comp x (by lia)).mapExactFunctor pb) (zero_add n₁) =
    hS'.extClass.comp ((Ext.mk₀ φ.τ₁).comp (x.mapExactFunctor pb) (zero_add n₀)) (by lia)
  rw [Ext.mapExactFunctor_comp, Ext.mapExactFunctor_extClass,
    ← Ext.comp_assoc _ _ _ (zero_add 1) (show 1 + n₀ = n₁ by lia) (show 0 + 1 + n₀ = n₁ by lia),
    ← hS'.extClass_naturality (hS.map_of_exact pb) φ,
    Ext.comp_assoc _ _ _ (add_zero 1) (zero_add n₀) (show 1 + 0 + n₀ = n₁ by lia)]

/-- The pullback as a morphism from the Mayer-Vietoris sequence of `G` for `S` to the
Mayer-Vietoris sequence of `pb G` for `S'`. -/
def mayerVietorisSequencePullback (G : Sheaf J AddCommGrpCat.{v}) (n₀ n₁ : ℕ)
    (h : n₀ + 1 = n₁) :
    S.sequence G n₀ n₁ h ⟶ S'.sequence (pb.obj G) n₀ n₁ h :=
  ComposableArrows.homMk₅ (pullback pb c G n₀ ψ.τ₄)
    (biprod.map (pullback pb c G n₀ ψ.τ₂) (pullback pb c G n₀ ψ.τ₃))
    (pullback pb c G n₀ ψ.τ₁) (pullback pb c G n₁ ψ.τ₄)
    (biprod.map (pullback pb c G n₁ ψ.τ₂) (pullback pb c G n₁ ψ.τ₃))
    (pullback pb c G n₁ ψ.τ₁)
    (toBiprod_comp_pullback pb c S S' ψ G n₀)
    (fromBiprod_comp_pullback pb c S S' ψ G n₀)
    (δ_comp_pullback pb c S S' ψ G n₀ n₁ h)
    (toBiprod_comp_pullback pb c S S' ψ G n₁)
    (fromBiprod_comp_pullback pb c S S' ψ G n₁)

section Components

variable (G : Sheaf J AddCommGrpCat.{v}) (n₀ n₁ : ℕ) (h : n₀ + 1 = n₁)

/-- The component of `mayerVietorisSequencePullback` on `H^{n₀}(S.X₄, G)`. -/
@[simp]
lemma mayerVietorisSequencePullback_app_zero :
    (mayerVietorisSequencePullback pb c S S' ψ G n₀ n₁ h).app 0 = pullback pb c G n₀ ψ.τ₄ :=
  (rfl)

/-- The component of `mayerVietorisSequencePullback` on `H^{n₀}(S.X₂, G) ⊞ H^{n₀}(S.X₃, G)`. -/
@[simp]
lemma mayerVietorisSequencePullback_app_one :
    (mayerVietorisSequencePullback pb c S S' ψ G n₀ n₁ h).app 1 =
      biprod.map (pullback pb c G n₀ ψ.τ₂) (pullback pb c G n₀ ψ.τ₃) :=
  (rfl)

/-- The component of `mayerVietorisSequencePullback` on `H^{n₀}(S.X₁, G)`. -/
@[simp]
lemma mayerVietorisSequencePullback_app_two :
    (mayerVietorisSequencePullback pb c S S' ψ G n₀ n₁ h).app 2 = pullback pb c G n₀ ψ.τ₁ :=
  (rfl)

/-- The component of `mayerVietorisSequencePullback` on `H^{n₁}(S.X₄, G)`. -/
@[simp]
lemma mayerVietorisSequencePullback_app_three :
    (mayerVietorisSequencePullback pb c S S' ψ G n₀ n₁ h).app 3 = pullback pb c G n₁ ψ.τ₄ :=
  (rfl)

/-- The component of `mayerVietorisSequencePullback` on `H^{n₁}(S.X₂, G) ⊞ H^{n₁}(S.X₃, G)`. -/
@[simp]
lemma mayerVietorisSequencePullback_app_four :
    (mayerVietorisSequencePullback pb c S S' ψ G n₀ n₁ h).app 4 =
      biprod.map (pullback pb c G n₁ ψ.τ₂) (pullback pb c G n₁ ψ.τ₃) :=
  (rfl)

/-- The component of `mayerVietorisSequencePullback` on `H^{n₁}(S.X₁, G)`. -/
@[simp]
lemma mayerVietorisSequencePullback_app_five :
    (mayerVietorisSequencePullback pb c S S' ψ G n₀ n₁ h).app 5 = pullback pb c G n₁ ψ.τ₁ :=
  (rfl)

end Components

end MayerVietoris

end

end CategoryTheory.Sheaf.H'

namespace CategoryTheory.Sheaf.H'

open TauCeti TauCeti.CategoryTheory

universe v u₁ u₂

variable {C : Type u₁} [Category.{v} C] {J : GrothendieckTopology C}
  {D : Type u₂} [Category.{v} D] {K : GrothendieckTopology D}
  [HasSheafify J AddCommGrpCat.{v}] [HasSheafify K AddCommGrpCat.{v}]
  [HasExt.{v} (Sheaf J AddCommGrpCat.{v})] [HasExt.{v} (Sheaf K AddCommGrpCat.{v})]
  (u : C ⥤ D) [u.IsContinuous J K]
  [(u.sheafPushforwardContinuous AddCommGrpCat.{v} J K).IsRightAdjoint]
  [PreservesFiniteLimits (u.sheafPullback AddCommGrpCat.{v} J K)]

/-- For a morphism of sites `u`, the pullback in degree zero, read on sections, is the unit
`G(U) ⟶ (u^* G)(u(U))` of the adjunction `u^* ⊣ u_*` followed by restriction along
`ψ : V ⟶ u(U)`. -/
lemma cohomologyZeroSectionsEquiv_pullback_sheafPullback (G : Sheaf J AddCommGrpCat.{v})
    {U : C} {V : D} (ψ : V ⟶ u.obj U) (x : G.H' 0 U) :
    cohomologyZeroSectionsEquiv _ V (pullback (u.sheafPullback AddCommGrpCat.{v} J K)
        (u.freeYonedaSheafToSheafPullback J K) G 0 ψ x) =
      ((u.sheafPullback AddCommGrpCat.{v} J K).obj G).obj.map ψ.op
        (((u.sheafAdjunctionContinuous AddCommGrpCat.{v} J K).unit.app G).hom.app (op U)
          (cohomologyZeroSectionsEquiv G U x)) := by
  rw [cohomologyZeroSectionsEquiv_apply, addEquiv₀_pullback,
    freeYonedaSheafSectionsEquiv_naturality_left, freeYonedaSheafSectionsEquiv_naturality_right,
    Functor.freeYonedaSheafSectionsEquiv_freeYonedaSheafToSheafPullback_app,
    cohomologyZeroSectionsEquiv_apply,
    Functor.sheafAdjunctionContinuous_unit_app_hom_app_freeYonedaSheafSectionsEquiv J K u
      (Ext.addEquiv₀ (X := (freeYonedaSheafFunctor J).obj U) x)]

end CategoryTheory.Sheaf.H'
