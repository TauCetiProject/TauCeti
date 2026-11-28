/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Bicategory.Path.Strict
public import Mathlib.CategoryTheory.Bicategory.Functor.Pseudofunctor

/-!
# Evaluation of the strict path bicategory

Evaluation defines a pseudofunctor from the strict bicategory `Paths B` to `B`.
Its composition constraint is the canonical comparison between evaluation of a
concatenation and composition of evaluations. In particular, the associator of `B`
is recovered by splitting a three-arrow path after its first arrow.

On each hom-category evaluation is an equivalence: the inverse sends an arrow to
its singleton path, and a path is compared with the singleton of its evaluation
by the identity 2-cell of its evaluation. These comparisons retain all genuine
2-cells of `B` and make explicit the representation of arbitrary paths. The inverse
local functors are the action of the singleton pseudofunctor `singleton`; composing
this pseudofunctor with evaluation recovers the identity pseudofunctor of `B`.

## References

* A. D. Fairbanks and M. Shulman, *Doubly weak double categories*, Applied Categorical
  Structures **34** (2026), article 26; arXiv:2506.23651, Proposition 2.5 and
  comparisons 2.7, 2.9–2.10.
-/

public section

open CategoryTheory CategoryTheory.Bicategory Quiver

universe w v u

namespace TauCeti.Bicategory.Paths

variable (B : Type u) [Bicategory.{w, v} B]

/-- Evaluation of paths as a pseudofunctor. Its composition comparison is
`Quiver.Path.evalComp`, and its action on 2-cells is the identity. -/
-- The object and arrow maps must compute in the types of mapped 2-cells.
@[expose]
def evaluation : Paths B ⥤ᵖ B where
  obj a := a.as
  map p := p.eval
  map₂ θ := θ
  map₂_id _ := rfl
  map₂_comp _ _ := rfl
  mapId _ := Iso.refl _
  mapComp p q := Path.evalComp p q
  map₂_whisker_left p _ _ θ := Path.whiskerLeftEval_def p θ
  map₂_whisker_right θ q := Path.whiskerRightEval_def θ q
  map₂_associator p q r := by
    -- Reduce the strict path associator to transport of its evaluated endpoints.
    change eqToHom (congrArg Path.eval (Path.comp_assoc p q r)) = _
    simp only [comp_def]
    rw [← cancel_mono ((Path.evalComp p (q.comp r)).hom ≫
      p.eval ◁ (Path.evalComp q r).hom)]
    simp only [Category.assoc, Iso.inv_hom_id_assoc, ← whiskerLeft_comp,
      Iso.inv_hom_id, whiskerLeft_id, Category.comp_id]
    exact (Path.evalComp_assoc_hom p q r).symm
  map₂_left_unitor p := by
    -- The path unitor is transport along nil_comp; evaluation preserves this transport.
    change eqToHom (congrArg Path.eval (Path.nil_comp p)) = _
    simp [id_def, Path.nil_evalComp_hom]
  map₂_right_unitor p := by
    -- Concatenation with an empty right path reduces definitionally to the same path.
    change 𝟙 p.eval = _
    simp only [id_def, Path.evalComp_nil, Iso.symm_hom, Iso.refl_hom,
      Path.eval_nil, whiskerLeft_id, Category.id_comp]
    exact (Iso.inv_hom_id (ρ_ p.eval)).symm

variable {B} {a b c d : Paths B}

@[simp]
theorem evaluation_obj (a : Paths B) : (evaluation B).obj a = a.as :=
  (rfl)

@[simp]
theorem evaluation_map (p : a ⟶ b) : (evaluation B).map p = p.eval :=
  (rfl)

@[simp]
theorem evaluation_map₂ {p q : a ⟶ b} (θ : p ⟶ q) : (evaluation B).map₂ θ = θ :=
  (rfl)

@[simp]
theorem evaluation_mapId (a : Paths B) : (evaluation B).mapId a = Iso.refl (𝟙 a.as) :=
  (rfl)

@[simp]
theorem evaluation_mapComp (p : a ⟶ b) (q : b ⟶ c) :
    (evaluation B).mapComp p q = Path.evalComp p q :=
  (rfl)

private theorem singleton_associator {x y z t : B} (f : x ⟶ y) (g : y ⟶ z) (h : z ⟶ t) :
    (α_ f g h).hom = 𝟙 _ ≫ Path.whiskerRightEval (p := (f ≫ g).toPath)
      (p' := f.toPath.comp g.toPath) (𝟙 (f ≫ g)) h.toPath ≫
      eqToHom (congrArg Path.eval (Path.comp_assoc f.toPath g.toPath h.toPath)) ≫
      Path.whiskerLeftEval f.toPath (q := g.toPath.comp h.toPath)
        (q' := (g ≫ h).toPath) (𝟙 (g ≫ h)) ≫ 𝟙 _ := by
  -- The path associator is transport; the nontrivial comparison is evalComp on [f,g,h].
  erw [Path.whiskerLeftEval_def, Path.whiskerRightEval_def]
  simp only [Path.comp_toPath_eq_cons, Path.evalComp_toPath_cons, Path.evalComp_toPath]
  simp [Quiver.Hom.toPath, Path.evalCons_cons]

variable (B) in
/-- The singleton pseudofunctor into the strict path bicategory. Its unit and
composition constraints are identity 2-cells between paths with the same evaluation.
The body is exposed because its object and arrow maps occur in mapped-cell types. -/
@[expose]
def singleton : B ⥤ᵖ Paths B where
  obj a := ⟨a⟩
  map f := f.toPath
  map₂ θ := θ
  map₂_id _ := rfl
  map₂_comp _ _ := rfl
  mapId a := {
    hom := 𝟙 (𝟙 a)
    inv := 𝟙 (𝟙 a)
    hom_inv_id := Category.id_comp _
    inv_hom_id := Category.id_comp _ }
  mapComp f g := {
    hom := 𝟙 (f ≫ g)
    inv := 𝟙 (f ≫ g)
    hom_inv_id := Category.id_comp _
    inv_hom_id := Category.id_comp _ }
  map₂_whisker_left f g h θ := by
    -- Compute the singleton constraints and path whiskering in the hom-category of B.
    change f ◁ θ = 𝟙 _ ≫ Path.whiskerLeftEval f.toPath (q := g.toPath) (q' := h.toPath) θ ≫ 𝟙 _
    erw [Path.whiskerLeftEval_def]
    simp only [Path.evalComp_toPath]
    simp [Quiver.Hom.toPath, Path.evalCons_cons]
  map₂_whisker_right {a b c} {f g} θ h := by
    -- Compute the singleton constraints and path whiskering in the hom-category of B.
    change θ ▷ h = 𝟙 _ ≫ Path.whiskerRightEval (p := f.toPath) (p' := g.toPath) θ h.toPath ≫ 𝟙 _
    erw [Path.whiskerRightEval_def]
    simp only [Path.evalComp_toPath]
    simp [Quiver.Hom.toPath, Path.evalCons_cons]
  map₂_associator f g h := by exact singleton_associator f g h
  map₂_left_unitor {a b} f := by
    -- The empty path is distinct from the singleton identity; evaluate its comparison.
    change (λ_ f).hom = 𝟙 _ ≫ Path.whiskerRightEval (p := (𝟙 a).toPath) (p' := .nil)
      (𝟙 (𝟙 a)) f.toPath ≫
      eqToHom (congrArg Path.eval (Path.nil_comp f.toPath))
    erw [Path.whiskerRightEval_def]
    simp only [Path.evalComp_toPath]
    simp [Quiver.Hom.toPath, Path.evalCons_cons, Path.evalCons_nil_inv]
  map₂_right_unitor {a b} f := by
    -- The right unit comparison similarly uses the inverse right unitor of B.
    change (ρ_ f).hom = 𝟙 _ ≫ Path.whiskerLeftEval f.toPath (q := (𝟙 b).toPath) (q' := .nil)
      (𝟙 (𝟙 b)) ≫
      eqToHom (congrArg Path.eval (Path.comp_nil f.toPath))
    erw [Path.whiskerLeftEval_def]
    simp only [Path.evalComp_toPath]
    simp [Quiver.Hom.toPath, Path.evalCons_cons]

@[simp]
theorem singleton_obj (x : B) : (singleton B).obj x = ⟨x⟩ :=
  (rfl)

@[simp]
theorem singleton_map {x y : B} (f : x ⟶ y) : (singleton B).map f = f.toPath :=
  (rfl)

@[simp]
theorem singleton_map₂ {x y : B} {f g : x ⟶ y} (θ : f ⟶ g) :
    (singleton B).map₂ θ = θ :=
  (rfl)

@[simp]
theorem singleton_mapId_hom (x : B) : ((singleton B).mapId x).hom = 𝟙 (𝟙 x) :=
  (rfl)

@[simp]
theorem singleton_mapId_inv (x : B) : ((singleton B).mapId x).inv = 𝟙 (𝟙 x) :=
  (rfl)

@[simp]
theorem singleton_mapComp_hom {x y z : B} (f : x ⟶ y) (g : y ⟶ z) :
    ((singleton B).mapComp f g).hom = 𝟙 (f ≫ g) :=
  (rfl)

@[simp]
theorem singleton_mapComp_inv {x y z : B} (f : x ⟶ y) (g : y ⟶ z) :
    ((singleton B).mapComp f g).inv = 𝟙 (f ≫ g) :=
  (rfl)

/-- A path is represented by the singleton of its evaluation. Both comparison
2-cells are the identity of the evaluated arrow. -/
def representationIso (p : a ⟶ b) : p ≅ (singleton B).map p.eval where
  hom := 𝟙 p.eval
  inv := 𝟙 p.eval
  hom_inv_id := Category.id_comp _
  inv_hom_id := Category.id_comp _

@[simp]
theorem representationIso_hom (p : a ⟶ b) :
    (representationIso p).hom = 𝟙 p.eval :=
  (rfl)

@[simp]
theorem representationIso_inv (p : a ⟶ b) :
    (representationIso p).inv = 𝟙 p.eval :=
  (rfl)

/-- The comparison of a singleton path with its representing singleton is the identity. -/
@[simp]
theorem representationIso_toPath (f : a.as ⟶ b.as) :
    representationIso (a := a) (b := b) f.toPath = Iso.refl (C := a ⟶ b) f.toPath := by
  rfl

/-- Evaluation is an equivalence on every hom-category. Its inverse is the singleton
embedding and its unit is the representation comparison of each path. -/
-- Its functor projections compute in the types of its unit and counit components.
@[expose]
def homEquivalence (a b : Paths B) : (a ⟶ b) ≌ (a.as ⟶ b.as) where
  functor := (evaluation B).mapFunctor a b
  inverse := (singleton B).mapFunctor a.as b.as
  unitIso := NatIso.ofComponents representationIso (by
    intros
    exact (Category.comp_id _).trans (Category.id_comp _).symm)
  counitIso := NatIso.ofComponents (fun _ ↦ Iso.refl _) (by
    intros
    exact (Category.comp_id _).trans (Category.id_comp _).symm)
  functor_unitIso_comp p := by
    -- Compute the local evaluation map and the two natural-isomorphism components.
    change (representationIso p).hom ≫ 𝟙 p.eval = 𝟙 p.eval
    rw [representationIso_hom]
    exact Category.id_comp _

@[simp]
theorem homEquivalence_functor (a b : Paths B) :
    (homEquivalence a b).functor = (evaluation B).mapFunctor a b :=
  (rfl)

@[simp]
theorem homEquivalence_inverse (a b : Paths B) :
    (homEquivalence a b).inverse = (singleton B).mapFunctor a.as b.as :=
  (rfl)

@[simp]
theorem homEquivalence_unitIso_app (p : a ⟶ b) :
    (homEquivalence a b).unitIso.app p = representationIso p :=
  (rfl)

@[simp]
theorem homEquivalence_counitIso_app (f : a.as ⟶ b.as) :
    (homEquivalence a b).counitIso.app f = Iso.refl f :=
  (rfl)

/-- Local evaluation is fully faithful and essentially surjective. -/
instance (a b : Paths B) : ((evaluation B).mapFunctor a b).IsEquivalence :=
  (homEquivalence a b).isEquivalence_functor

/-- The singleton pseudofunctor is an equivalence on each hom-category. -/
instance (x y : B) : ((singleton B).mapFunctor x y).IsEquivalence :=
  (homEquivalence (B := B) ⟨x⟩ ⟨y⟩).isEquivalence_inverse

/-- Taking singleton paths and then evaluating recovers the identity pseudofunctor,
including its unit and composition constraints. -/
@[simp]
theorem singleton_comp_evaluation : (singleton B).comp (evaluation B) = Pseudofunctor.id B := by
  -- Compute the common object, arrow and 2-cell maps before comparing constraints.
  dsimp only [Pseudofunctor.comp, PrelaxFunctor.comp, PrelaxFunctorStruct.comp,
    Pseudofunctor.id, PrelaxFunctor.id, PrelaxFunctorStruct.id, singleton, evaluation]
  congr 1
  · funext x
    apply Iso.ext
    -- Evaluate the map on the singleton unit constraint and the empty-path identity.
    change 𝟙 (𝟙 x) ≫ 𝟙 (𝟙 x) = 𝟙 (𝟙 x)
    exact Category.id_comp _
  · funext x y z f g
    apply Iso.ext
    -- Evaluate the map on the singleton binary constraint before reducing evalComp.
    change 𝟙 (f ≫ g) ≫ (Path.evalComp f.toPath g.toPath).hom = 𝟙 (f ≫ g)
    rw [Path.evalComp_toPath]
    simp [Quiver.Hom.toPath, Path.evalCons_cons]

end TauCeti.Bicategory.Paths
