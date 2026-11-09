/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.EnoughInjectives
public import Mathlib.CategoryTheory.Adjunction.Triple
public import Mathlib.CategoryTheory.Linear.Yoneda
public import Mathlib.CategoryTheory.Monad.Limits
public import Mathlib.CategoryTheory.Preadditive.Injective.Preserves
public import Mathlib.RingTheory.Flat.CategoryTheory
public import TauCeti.RingTheory.Almost.Hom
public import TauCeti.RingTheory.Almost.Module

/-!
# Almost elements and the left adjoint of almostification

Let `S = (V, m)` be a basic setup and `m~ = m ⊗[V] m`. The almostification functor
`M ↦ M^a` from `V`-modules to almost `V`-modules has a right adjoint, the functor of
*almost elements* `M ↦ M_* = Hom(V^a, M)`, and a left adjoint `M ↦ M_! = m~ ⊗[V] M_*`. Both
adjoints are fully faithful, so the category of almost modules is at once a reflective and a
coreflective subcategory of `ModuleCat V`. The left adjoint is moreover exact, since `m~` is
flat.

These adjunctions carry the basic properties of the category of almost modules: it is complete
and cocomplete, almostification preserves all limits and colimits, and it has enough injectives.
For every `V`-module `N` the unit `N → (N^a)_*` and the counit `(N^a)_! → N` are almost
isomorphisms; they are not isomorphisms in general.

Both adjunctions are built from Bhatt's model of almost modules as firm modules: the category
`Module S` is equivalent to the category `S.Firm` of firm modules
(`TauCeti.Almost.Module.firmEquiv`), under which almostification becomes `M ↦ m~ ⊗[V] M`, almost
elements become `N ↦ Hom_V(m~, N)` and `M_!` becomes the inclusion of firm modules.

## Main definitions

* `TauCeti.Almost.Module.elements`: the functor of almost elements `M ↦ M_* = Hom(V^a, M)`.
* `TauCeti.Almost.Module.shriek`: the functor `M ↦ M_! = m~ ⊗[V] M_*`.

## Main results

* `TauCeti.Almost.Module.adjElements`: almostification is left adjoint to `elements`, with unit
  `x ↦ (V → M, 1 ↦ x)^a` (`TauCeti.Almost.Module.adjElements_unit_app_hom_apply`).
* `TauCeti.Almost.Module.adjShriek`: `shriek` is left adjoint to almostification.
* `TauCeti.Almost.Module.fullyFaithfulElements` and `TauCeti.Almost.Module.fullyFaithfulShriek`:
  both adjoints are fully faithful, so the counit `(M_*)^a → M` and the unit `M → (M_!)^a` are
  isomorphisms.
* `TauCeti.Almost.Module.isAlmostIso_adjElements_unit_app` and
  `TauCeti.Almost.Module.isAlmostIso_adjShriek_counit_app`: the unit `N → (N^a)_*` and the counit
  `(N^a)_! → N` are almost isomorphisms.
* `TauCeti.Almost.Module.toAlmostCompShriekIso`: `(N^a)_! ≅ m~ ⊗[V] N`, naturally in `N`, under
  which the counit `(N^a)_! → N` is the action map (`TauCeti.Almost.Module.adjShriek_counit_app`).
  This counit is an isomorphism exactly when `N` is firm
  (`TauCeti.Almost.Module.isIso_adjShriek_counit_app_iff`).
* `TauCeti.Almost.Module.toAlmostCompElementsIso`: `(N^a)_* ≅ Hom_V(m~, N)`, naturally in `N`.
* `TauCeti.Almost.Module.adjTriple` and `TauCeti.Almost.Module.shriekToElements`: the adjoint triple
  `(−)_! ⊣ (−)^a ⊣ (−)_*` and its comparison `M_! → M_*`, an almost isomorphism
  (`TauCeti.Almost.Module.isAlmostIso_shriekToElements_app`).
* `TauCeti.Almost.Module.hasLimits`, `TauCeti.Almost.Module.hasColimits` and
  `TauCeti.Almost.Module.enoughInjectives`: almost modules form a complete and cocomplete category
  with enough injectives.

## References

* O. Gabber, L. Ramero, *Almost ring theory*, Lecture Notes in Mathematics 1800, §2.2,
  Proposition 2.2.13, Corollary 2.2.15 and Proposition 2.2.21.
* B. Bhatt, *Lecture notes for a class on perfectoid spaces*, §4.1, Construction 4.1.5 and
  Proposition 4.1.7.
* P. Scholze, *Perfectoid spaces*, Publ. Math. IHÉS 116 (2012), §4.
-/

public section

universe u

open CategoryTheory Limits Opposite TensorProduct

namespace TauCeti.Almost.Module

variable {V : Type u} [CommRing V] (S : BasicSetup V)

/-! ### The firm model -/

/-- Almostification, written through the firm model. -/
private noncomputable def firmCompInverseIso : S.firm ⋙ (firmEquiv S).inverse ≅ toAlmost S :=
  (Iso.isoCompInverse (toAlmostCompFirmIso S)).symm

/-! ### Almost elements -/

/-- The functor of **almost elements** `M ↦ M_* = Hom(V^a, M)` (Gabber–Ramero, §2.2), with the
`V`-module structure of the Hom-modules of almost modules. -/
@[expose] noncomputable def elements : Module S ⥤ ModuleCat.{u} V :=
  (linearCoyoneda V (Module S)).obj (op ((toAlmost S).obj (ModuleCat.of V V)))

@[simp]
theorem elements_obj (M : Module S) :
    (elements S).obj M = ModuleCat.of V ((toAlmost S).obj (ModuleCat.of V V) ⟶ M) :=
  (rfl)

@[simp]
theorem elements_map_hom_apply {M N : Module S} (f : M ⟶ N)
    (x : (toAlmost S).obj (ModuleCat.of V V) ⟶ M) :
    ((elements S).map f).hom x = x ≫ f :=
  (rfl)

instance : (elements S).Additive :=
  inferInstanceAs (Functor.Additive ((linearCoyoneda V (Module S)).obj _))

instance : (elements S).Linear V :=
  inferInstanceAs (Functor.Linear V ((linearCoyoneda V (Module S)).obj _))

/-- The right adjoint of almostification in the firm model, `N ↦ Hom_V(m~, N)`. -/
private noncomputable def elementsFirm : Module S ⥤ ModuleCat.{u} V :=
  (firmEquiv S).functor ⋙ S.closure

/-- Almostification is left adjoint to `elementsFirm`. -/
private noncomputable def adjElementsFirm : toAlmost S ⊣ elementsFirm S :=
  (S.firmAdj.comp (firmEquiv S).symm.toAdjunction).ofNatIsoLeft (firmCompInverseIso S)

/-- The inverse of the Hom-equivalence of an adjunction out of `toAlmost S`, as a `V`-linear
equivalence. -/
private noncomputable def homEquivSymmLinearEquiv {R : Module S ⥤ ModuleCat.{u} V}
    (adj : toAlmost S ⊣ R) (M : ModuleCat.{u} V) (N : Module S) :
    (M ⟶ R.obj N) ≃ₗ[V] ((toAlmost S).obj M ⟶ N) where
  __ := (adj.homEquiv M N).symm
  map_add' f g := by simp [Adjunction.homEquiv_counit]
  map_smul' c f := by simp [Adjunction.homEquiv_counit]

/-- For a right adjoint `R` of almostification, `R N ≃ Hom(V^a, N)`, sending `x` to the map
corresponding to `V → R N`, `1 ↦ x`. -/
private noncomputable def rightAdjointElementsEquiv {R : Module S ⥤ ModuleCat.{u} V}
    (adj : toAlmost S ⊣ R) (N : Module S) : R.obj N ≃ₗ[V] (elements S).obj N :=
  (LinearMap.ringLmapEquivSelf V V (R.obj N)).symm ≪≫ₗ
    (ModuleCat.homLinearEquiv (M := ModuleCat.of V V) (N := R.obj N) (S := V)).symm ≪≫ₗ
    homEquivSymmLinearEquiv S adj _ N

private theorem rightAdjointElementsEquiv_apply {R : Module S ⥤ ModuleCat.{u} V}
    (adj : toAlmost S ⊣ R) (N : Module S) (x : R.obj N) :
    rightAdjointElementsEquiv S adj N x =
      (adj.homEquiv _ _).symm (ModuleCat.ofHom (LinearMap.toSpanSingleton V _ x)) :=
  (rfl)

/-- A right adjoint `R` of almostification computes almost elements: `R N ≅ Hom(V^a, N)`. -/
private noncomputable def rightAdjointIsoElements {R : Module S ⥤ ModuleCat.{u} V}
    (adj : toAlmost S ⊣ R) : R ≅ elements S :=
  NatIso.ofComponents (fun N ↦ (rightAdjointElementsEquiv S adj N).toModuleIso)
    fun {N N'} f ↦ by
      ext x
      -- Both sides are the adjoint of the map `V → R N'`, `1 ↦ R f x`.
      simp only [ModuleCat.hom_comp, LinearMap.comp_apply, LinearEquiv.toModuleIso_hom,
        ModuleCat.hom_ofHom, LinearEquiv.coe_coe, rightAdjointElementsEquiv_apply,
        elements_map_hom_apply]
      have h : ModuleCat.ofHom (LinearMap.toSpanSingleton V _ x) ≫ R.map f =
          ModuleCat.ofHom (LinearMap.toSpanSingleton V _ ((R.map f).hom x)) := by
        ext
        simp
      exact (congrArg _ h).symm.trans (adj.homEquiv_naturality_right_symm _ _)

private theorem rightAdjointIsoElements_hom_app_hom_apply {R : Module S ⥤ ModuleCat.{u} V}
    (adj : toAlmost S ⊣ R) (N : Module S) (x : R.obj N) :
    ((rightAdjointIsoElements S adj).hom.app N).hom x =
      (adj.homEquiv _ _).symm (ModuleCat.ofHom (LinearMap.toSpanSingleton V _ x)) :=
  (rfl)

/-- **Almostification is left adjoint to almost elements** (Gabber–Ramero, Proposition
2.2.13(ii)). -/
noncomputable def adjElements : toAlmost S ⊣ elements S :=
  (adjElementsFirm S).ofNatIsoRight (rightAdjointIsoElements S (adjElementsFirm S))

/-- The unit `M → (M^a)_*` of `adjElements` sends `x` to the almostification of the map `V → M`,
`1 ↦ x`. -/
theorem adjElements_unit_app_hom_apply (M : ModuleCat.{u} V) (x : M) :
    ((adjElements S).unit.app M).hom x =
      (toAlmost S).map (ModuleCat.ofHom (LinearMap.toSpanSingleton V M x)) := by
  have h : ModuleCat.ofHom (LinearMap.toSpanSingleton V M x) ≫ (adjElementsFirm S).unit.app M =
      ModuleCat.ofHom (LinearMap.toSpanSingleton V _ (((adjElementsFirm S).unit.app M).hom x)) := by
    ext
    simp
  rw [← Adjunction.homEquiv_id, adjElements, Adjunction.homEquiv_ofNatIsoRight_apply,
    ModuleCat.comp_apply, rightAdjointIsoElements_hom_app_hom_apply, Adjunction.homEquiv_id, ← h,
    Adjunction.homEquiv_naturality_left_symm, Adjunction.homEquiv_counit]
  -- `rw` cannot use the triangle identity here: the motive mentions `(elements S).obj`, whose
  -- carrier is a Hom-type of `Module S` only up to unfolding its category instance.
  exact (congrArg _ ((adjElementsFirm S).left_triangle_components M)).trans (Category.comp_id _)

/-- The Hom-equivalence of `adjElements` sends `f : M^a ⟶ N` to the map `M → N_*` sending `x` to
the composite of `f` with the almostification of `V → M`, `1 ↦ x`. -/
@[simp]
theorem adjElements_homEquiv_apply_hom_apply {M : ModuleCat.{u} V} {N : Module S}
    (f : (toAlmost S).obj M ⟶ N) (x : M) :
    (((adjElements S).homEquiv M N) f).hom x =
      (toAlmost S).map (ModuleCat.ofHom (LinearMap.toSpanSingleton V M x)) ≫ f := by
  rw [Adjunction.homEquiv_unit, ModuleCat.comp_apply, adjElements_unit_app_hom_apply,
    elements_map_hom_apply]

/-- The functor of almost elements is fully faithful (Gabber–Ramero, Proposition 2.2.13(iii)). -/
noncomputable def fullyFaithfulElements : (elements S).FullyFaithful :=
  ((firmEquiv S).fullyFaithfulFunctor.comp S.fullyFaithfulClosure).ofIso
    (rightAdjointIsoElements S (adjElementsFirm S))

instance : (elements S).Full :=
  (fullyFaithfulElements S).full

instance : (elements S).Faithful :=
  (fullyFaithfulElements S).faithful

/-- Almost modules form a reflective subcategory of `ModuleCat V`, through almost elements. -/
noncomputable instance : Reflective (elements S) where
  L := toAlmost S
  adj := adjElements S

/-- For every `V`-module `N`, the unit `N → (N^a)_*` is an almost isomorphism (Gabber–Ramero,
(2.2.9)). -/
theorem isAlmostIso_adjElements_unit_app (N : ModuleCat.{u} V) :
    S.IsAlmostIso ((adjElements S).unit.app N).hom := by
  rw [← isIso_toAlmost_map_iff]
  infer_instance

/-- The counit `(M_*)^a → M` of `adjElements` sends the almostification of `1 ↦ x : V → M_*` to
the almost element `x : V^a → M` itself. -/
@[simp]
theorem toAlmost_map_toSpanSingleton_comp_adjElements_counit_app (M : Module S)
    (x : (toAlmost S).obj (ModuleCat.of V V) ⟶ M) :
    (toAlmost S).map (ModuleCat.ofHom (LinearMap.toSpanSingleton V ((elements S).obj M) x)) ≫
      (adjElements S).counit.app M = x := by
  have h := adjElements_homEquiv_apply_hom_apply S ((adjElements S).counit.app M) x
  rw [Adjunction.homEquiv_unit, Adjunction.right_triangle_components] at h
  exact h.symm.trans (ModuleCat.id_apply ((elements S).obj M) x)

/-- The almost-Hom formula for `Hom(V^a, N^a)`:
`Hom(V^a, N^a) ≅ Hom_V(m~ ⊗[V] V, N) ≅ Hom_V(m~, N)`. -/
private noncomputable def toAlmostElementsEquiv (N : ModuleCat.{u} V) :
    ((toAlmost S).obj (ModuleCat.of V V) ⟶ (toAlmost S).obj N) ≃ₗ[V]
      (ModuleCat.of V S.tilde ⟶ N) :=
  homLinearEquiv S (ModuleCat.of V V) N ≪≫ₗ
    LinearEquiv.arrowCongr (TensorProduct.rid V S.tilde) (LinearEquiv.refl V N) ≪≫ₗ
    (ModuleCat.homLinearEquiv (M := ModuleCat.of V S.tilde) (N := N) (S := V)).symm

private theorem toAlmostElementsEquiv_apply (N : ModuleCat.{u} V)
    (f : (toAlmost S).obj (ModuleCat.of V V) ⟶ (toAlmost S).obj N) :
    toAlmostElementsEquiv S N f = ModuleCat.ofHom
      (homLinearEquiv S _ N f ∘ₗ (TensorProduct.rid V S.tilde).symm.toLinearMap) :=
  rfl

/-- **The almost elements of an almostification**: `(N^a)_* ≅ Hom_V(m~, N)`, naturally in `N`
(Gabber–Ramero, Proposition 2.2.13(iii)). It is given by the almost-Hom formula `homLinearEquiv`
(`toAlmostCompElementsIso_hom_app_apply`). -/
noncomputable def toAlmostCompElementsIso :
    toAlmost S ⋙ elements S ≅ ihom (ModuleCat.of V S.tilde) :=
  NatIso.ofComponents (fun N ↦ (toAlmostElementsEquiv S N).toModuleIso) fun {N N'} g ↦ by
    refine ModuleCat.hom_ext (LinearMap.ext
      fun (f : (toAlmost S).obj (ModuleCat.of V V) ⟶ (toAlmost S).obj N) ↦ ?_)
    -- Both composites are evaluations of composed linear maps; this unfolds them.
    change toAlmostElementsEquiv S N' (f ≫ (toAlmost S).map g) = toAlmostElementsEquiv S N f ≫ g
    -- Postcomposition with `g^a` becomes postcomposition with `g` on representatives.
    have h := homLinearEquiv_natural S (𝟙 (ModuleCat.of V V)) g f
    rw [CategoryTheory.Functor.map_id, Category.id_comp] at h
    rw [toAlmostElementsEquiv_apply, toAlmostElementsEquiv_apply, h]
    ext t
    simp

/-- The isomorphism `(N^a)_* ≅ Hom_V(m~, N)` is the almost-Hom formula `homLinearEquiv` for
`Hom(V^a, N^a)`, composed with `m~ ≅ m~ ⊗[V] V`. -/
@[simp]
theorem toAlmostCompElementsIso_hom_app_apply (N : ModuleCat.{u} V)
    (f : (toAlmost S).obj (ModuleCat.of V V) ⟶ (toAlmost S).obj N) :
    dsimp% only [Functor.comp_obj] ((toAlmostCompElementsIso S).hom.app N).hom f = ModuleCat.ofHom
      (homLinearEquiv S _ N f ∘ₗ (TensorProduct.rid V S.tilde).symm.toLinearMap) :=
  toAlmostElementsEquiv_apply S N f

/-! ### The left adjoint `M ↦ M_!` -/

/-- The functor `M ↦ M_! = m~ ⊗[V] M_*` (Gabber–Ramero, (2.2.20)), left adjoint to
almostification. -/
@[expose] noncomputable def shriek : Module S ⥤ ModuleCat.{u} V :=
  elements S ⋙ MonoidalCategory.tensorLeft (ModuleCat.of V S.tilde)

@[simp]
theorem shriek_obj (M : Module S) :
    (shriek S).obj M = ModuleCat.of V (S.tilde ⊗[V] ((elements S).obj M)) :=
  (rfl)

@[simp]
theorem shriek_map_hom_tmul {M N : Module S} (f : M ⟶ N) (t : S.tilde)
    (x : (toAlmost S).obj (ModuleCat.of V V) ⟶ M) :
    ((shriek S).map f).hom (t ⊗ₜ[V] x) = t ⊗ₜ[V] (x ≫ f) :=
  (rfl)

/-- The left adjoint of almostification in the firm model, the inclusion of firm modules. -/
private noncomputable def shriekFirm : Module S ⥤ ModuleCat.{u} V :=
  (firmEquiv S).functor ⋙ S.isFirm.ι

/-- `shriekFirm` is left adjoint to almostification. -/
private noncomputable def adjShriekFirm : shriekFirm S ⊣ toAlmost S :=
  ((firmEquiv S).toAdjunction.comp S.firmInclusionAdj).ofNatIsoRight (firmCompInverseIso S)

/-- `M_!` is the firm module corresponding to `M`: for a firm module `N`, the evaluation map
`m~ ⊗[V] Hom_V(m~, N) → N` is an isomorphism. -/
private noncomputable def shriekIsoShriekFirm : shriek S ≅ shriekFirm S :=
  Functor.isoWhiskerRight (rightAdjointIsoElements S (adjElementsFirm S)).symm _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (firmEquiv S).functor
      ((Functor.isoWhiskerLeft S.closure (S.isFirm.liftCompιIso _ _)).symm ≪≫
        (Functor.associator _ _ _).symm ≪≫ Functor.isoWhiskerRight (asIso S.firmAdj.counit) _ ≪≫
        Functor.leftUnitor _)

/-- **`M ↦ M_!` is left adjoint to almostification** (Gabber–Ramero, Proposition 2.2.21). -/
noncomputable def adjShriek : shriek S ⊣ toAlmost S :=
  (adjShriekFirm S).ofNatIsoLeft (shriekIsoShriekFirm S).symm

/-- The functor `M ↦ M_!` is fully faithful (Gabber–Ramero, Proposition 2.2.21). -/
noncomputable def fullyFaithfulShriek : (shriek S).FullyFaithful :=
  ((firmEquiv S).fullyFaithfulFunctor.comp S.isFirm.fullyFaithfulι).ofIso
    (shriekIsoShriekFirm S).symm

instance : (shriek S).Full :=
  (fullyFaithfulShriek S).full

instance : (shriek S).Faithful :=
  (fullyFaithfulShriek S).faithful

/-- Almost modules form a coreflective subcategory of `ModuleCat V`, through `M ↦ M_!`. -/
noncomputable instance : Coreflective (shriek S) where
  R := toAlmost S
  adj := adjShriek S

/-- For a `V`-module `N`, `(N^a)_! ≅ m~ ⊗[V] N`, naturally in `N` (Gabber–Ramero, (2.2.20)). -/
noncomputable def toAlmostCompShriekIso :
    toAlmost S ⋙ shriek S ≅ MonoidalCategory.tensorLeft (ModuleCat.of V S.tilde) :=
  Functor.isoWhiskerLeft _ (shriekIsoShriekFirm S) ≪≫ (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (toAlmostCompFirmIso S) _ ≪≫ S.isFirm.liftCompιIso _ _

/-- Under `(N^a)_! ≅ m~ ⊗[V] N`, the counit `(N^a)_! → N` of `adjShriek` is the action map
`m~ ⊗[V] N → N`, `(x ⊗ y) ⊗ n ↦ (x * y) • n`. -/
theorem adjShriek_counit_app (N : ModuleCat.{u} V) :
    (adjShriek S).counit.app N =
      (toAlmostCompShriekIso S).hom.app N ≫ ModuleCat.ofHom (S.tildeAct N) := by
  simp only [Functor.comp_obj, Functor.id_obj, adjShriek, Adjunction.ofNatIsoLeft_counit,
    Iso.symm_inv, NatTrans.comp_app, Functor.whiskerLeft_app,
    MonoidalCategory.curriedTensor_obj_obj, ModuleCat.of_coe, toAlmostCompShriekIso,
    Iso.trans_hom, Functor.isoWhiskerLeft_hom, Category.assoc, NatIso.cancel_natIso_hom_left]
  -- The counit transported along `ofNatIsoRight` is the old counit precomposed with the image of
  -- the comparison isomorphism (`Adjunction.ofNatIsoRight_counit`).
  have h1 : (adjShriekFirm S).counit.app N =
      ((firmEquiv S).functor ⋙ S.isFirm.ι).map ((firmCompInverseIso S).inv.app N) ≫
        ((firmEquiv S).toAdjunction.comp S.firmInclusionAdj).counit.app N :=
    rfl
  have h3 : (firmEquiv S).functor.map ((firmCompInverseIso S).inv.app N) ≫
      (firmEquiv S).counit.app (S.firm.obj N) = (toAlmostCompFirmIso S).hom.app N := by
    simp [firmCompInverseIso, Iso.isoCompInverse_hom_app]
  rw [h1]
  -- The associator and `liftCompιIso` are identity isomorphisms, so the comparison is the
  -- whiskering of `toAlmostCompFirmIso`.
  change _ = S.isFirm.ι.map ((toAlmostCompFirmIso S).hom.app N) ≫ ModuleCat.ofHom (S.tildeAct N)
  rw [Adjunction.comp_counit_app, Functor.comp_map, Equivalence.toAdjunction_counit,
    ← Category.assoc, ← Functor.map_comp, h3]
  congr 1
  exact ModuleCat.hom_ext (S.firmInclusionAdj_counit_app_hom N)

/-- The counit `(N^a)_! → N` is an isomorphism exactly when `N` is firm. -/
theorem isIso_adjShriek_counit_app_iff (N : ModuleCat.{u} V) :
    IsIso ((adjShriek S).counit.app N) ↔ S.IsFirm N := by
  rw [adjShriek_counit_app, isIso_comp_left_iff, ConcreteCategory.isIso_iff_bijective,
    S.isFirm_iff_bijective]
  simp

/-- For every `V`-module `N`, the counit `(N^a)_! → N` is an almost isomorphism (Gabber–Ramero,
(2.2.9)). -/
theorem isAlmostIso_adjShriek_counit_app (N : ModuleCat.{u} V) :
    S.IsAlmostIso ((adjShriek S).counit.app N).hom := by
  rw [← isIso_toAlmost_map_iff]
  infer_instance

/-- The functor `M ↦ M_!` is left exact, because `m~` is flat; being a left adjoint, it is
therefore exact. -/
instance : PreservesFiniteLimits (shriek S) :=
  inferInstanceAs (PreservesFiniteLimits (elements S ⋙ _))

/-- The module `M_!` is firm. -/
theorem isFirm_shriek_obj (M : Module S) : S.isFirm ((shriek S).obj M) :=
  S.isFirm.prop_of_iso ((shriekIsoShriekFirm S).app M).symm ((firmEquiv S).functor.obj M).property

/-! ### The comparison `M_! → M_*` -/

/-- The adjoint triple `(−)_! ⊣ (−)^a ⊣ (−)_*`. -/
noncomputable def adjTriple : Adjunction.Triple (shriek S) (toAlmost S) (elements S) :=
  ⟨adjShriek S, adjElements S⟩

/-- The natural map `M_! → M_*` (Gabber–Ramero, (2.2.9)): Mathlib's comparison
`Adjunction.Triple.leftToRight` for the adjoint triple `adjTriple`, whose outer functors are fully
faithful. It corresponds under `adjElements` to the inverse of the unit isomorphism
`M ≅ (M_!)^a` (`shriekToElements_app`). -/
noncomputable abbrev shriekToElements : shriek S ⟶ elements S :=
  (adjTriple S).leftToRight

/-- The component `M_! → M_*` is the image under `adjElements` of the inverse of the unit
isomorphism `M ≅ (M_!)^a` of `adjShriek`. -/
theorem shriekToElements_app (M : Module S) :
    (shriekToElements S).app M = (adjElements S).homEquiv _ _ (inv ((adjShriek S).unit.app M)) := by
  rw [Adjunction.Triple.leftToRight_app, Adjunction.homEquiv_unit, Functor.map_inv]
  simp only [adjTriple]

/-- The map `M_! → M_*` sends `x` to `(V → M_!, 1 ↦ x)^a` followed by `(M_!)^a ≅ M`. -/
@[simp]
theorem shriekToElements_app_apply (M : Module S) (x : (shriek S).obj M) :
    ((shriekToElements S).app M).hom x =
      (toAlmost S).map (ModuleCat.ofHom (LinearMap.toSpanSingleton V _ x)) ≫
        inv ((adjShriek S).unit.app M) := by
  rw [shriekToElements_app]
  exact adjElements_homEquiv_apply_hom_apply S _ x

/-- The map `M_! → M_*` is an almost isomorphism (Gabber–Ramero, (2.2.9)). -/
theorem isAlmostIso_shriekToElements_app (M : Module S) :
    S.IsAlmostIso ((shriekToElements S).app M).hom := by
  rw [← isIso_toAlmost_map_iff, shriekToElements_app]
  have h := ((adjElements S).homEquiv _ _).symm_apply_apply (inv ((adjShriek S).unit.app M))
  rw [Adjunction.homEquiv_counit] at h
  have : IsIso ((toAlmost S).map ((adjElements S).homEquiv _ _ (inv ((adjShriek S).unit.app M))) ≫
      (adjElements S).counit.app ((𝟭 (Module S)).obj M)) := by
    rw [h]
    infer_instance
  exact IsIso.of_isIso_comp_right _ ((adjElements S).counit.app ((𝟭 (Module S)).obj M))

/-! ### Limits, colimits and injectives -/

/-- **Almost modules form a complete category** (Gabber–Ramero, Corollary 2.2.15). -/
instance hasLimits : HasLimits (Module S) :=
  hasLimits_of_reflective (elements S)

/-- **Almost modules form a cocomplete category** (Gabber–Ramero, Corollary 2.2.15). -/
instance hasColimits : HasColimits (Module S) :=
  hasColimits_of_reflective (elements S)

/-- Almostification preserves all limits, being right adjoint to `M ↦ M_!`. -/
instance : PreservesLimits (toAlmost S) :=
  (adjShriek S).rightAdjoint_preservesLimits

/-- Almostification preserves all colimits, being left adjoint to almost elements. -/
instance : PreservesColimits (toAlmost S) :=
  (adjElements S).leftAdjoint_preservesColimits

/-- Almost elements preserve all limits. -/
instance : PreservesLimits (elements S) :=
  (adjElements S).rightAdjoint_preservesLimits

/-- `M ↦ M_!` preserves all colimits. -/
instance : PreservesColimits (shriek S) :=
  (adjShriek S).leftAdjoint_preservesColimits

/-- Almost elements of an injective almost module form an injective `V`-module. -/
instance : (elements S).PreservesInjectiveObjects :=
  Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms (adjElements S)

/-- Almostification preserves injective objects, being right adjoint to the exact functor
`M ↦ M_!`. -/
instance : (toAlmost S).PreservesInjectiveObjects :=
  Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms (adjShriek S)

/-- **Almost modules have enough injectives** (Gabber–Ramero, Corollary 2.2.15). -/
instance enoughInjectives : EnoughInjectives (Module S) :=
  EnoughInjectives.of_adjunction (adjShriek S)

end TauCeti.Almost.Module
