/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.CategoryTheory.Monoidal.Cartesian.Mod
public import TauCeti.CategoryTheory.Monoidal.Grp.Translation
public import TauCeti.CategoryTheory.Monoidal.Mod.Basic

/-!
# Orbit morphisms and translations for internal actions

An action in a cartesian monoidal category gives an orbit morphism from the acting
monoid to the acted-on object for each global point. For a group object, translation
by a global group point is an automorphism. The orbit morphism intertwines left
translation on the group with translation on the acted-on object. Moving its base
point corresponds instead to right multiplication on the group.

A morphism is equivariant exactly when it commutes with the action on points with values in
every object (`TauCeti.isModHom_iff_map_smul`). A point `x : Z ⟶ X` of a pseudo-torsor, an
action for which `(g, x) ↦ (g • x, x)` is an isomorphism, trivialises it over `Z`
(`TauCeti.isIso_lift_smul_snd_of_isIso_leftSMul`).

A pseudo-torsor `X` under `G` has a **difference morphism** `TauCeti.ModObj.diff G X : X ⊗ X ⟶ G`,
sending `(x, y)` to the unique `g` with `g • x = y` (`TauCeti.ModObj.lift_diff_smul`,
`TauCeti.ModObj.eq_lift_diff_iff`). It needs no point of `X`; a point `β` of `X` over `T`
identifies the points of `X` over `T` with those of `G` (`TauCeti.ModObj.diffEquiv`).

These constructions apply in particular to group schemes acting on schemes over a
base. All identities are identities of morphisms, rather than only of global points.
They use Mathlib's `Hom.mulAction` and the existing group-object `TauCeti.leftTranslation`.
-/

public section

open CategoryTheory MonoidalCategory CartesianMonoidalCategory MonObj ModObj

namespace TauCeti

universe u v

variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C]

section Monoid

variable (G : C) [MonObj G] {X Y : C} [ModObj G X] [ModObj G Y]

/-- The orbit morphism of a global point, sending `g` to `g • x`. -/
def orbitMap (x : 𝟙_ C ⟶ X) : G ⟶ X :=
  (𝟙 G) • (toUnit G ≫ x)

/-- Evaluation of the orbit morphism on an arbitrary test-object point. -/
@[reassoc (attr := simp)]
theorem comp_orbitMap {T : C} (g : T ⟶ G) (x : 𝟙_ C ⟶ X) :
    g ≫ orbitMap G x = g • (toUnit T ≫ x) := by
  simp [orbitMap, comp_smul]

/-- The orbit morphism intertwines multiplication with the action morphism. -/
@[reassoc]
theorem mul_orbitMap (x : 𝟙_ C ⟶ X) :
    μ[G] ≫ orbitMap G x = G ◁ orbitMap G x ≫ γ[G, X] := by
  calc
    μ[G] ≫ orbitMap G x = (fst G G * snd G G) ≫ orbitMap G x := by
      simp [Hom.mul_def]
    _ = fst G G • (snd G G ≫ orbitMap G x) := by
      simp [comp_orbitMap, SemigroupAction.mul_smul]
    _ = G ◁ orbitMap G x ≫ γ[G, X] := by
      rw [Hom.smul_def, ← lift_whiskerLeft, lift_fst_snd, Category.id_comp]

/-- An equivariant morphism carries an orbit morphism to the orbit morphism of the image. -/
@[reassoc]
theorem orbitMap_comp (x : 𝟙_ C ⟶ X) (f : X ⟶ Y) [IsModHom G f] :
    orbitMap G x ≫ f = orbitMap G (x ≫ f) := by
  simp [orbitMap, IsModHom.map_smul, Category.assoc]

variable {G} in
/-- A morphism is equivariant if and only if it commutes with the action on points with values
in every object. -/
theorem isModHom_iff_map_smul (f : X ⟶ Y) :
    IsModHom G f ↔ ∀ (T : C) (g : T ⟶ G) (x : T ⟶ X), (g • x) ≫ f = g • (x ≫ f) := by
  refine ⟨fun _ T g x ↦ IsModHom.map_smul f g x, fun hf ↦ ⟨?_⟩⟩
  have := hf (G ⊗ X) (fst G X) (snd G X)
  simp only [Hom.smul_def, ← lift_whiskerLeft, lift_fst_snd, Category.id_comp] at this
  exact this

variable {G} in
/-- A point `x : Z ⟶ X` of a pseudo-torsor trivialises it over `Z`: when
`(g, x) ↦ (g • x, x)` is an isomorphism `G ⊗ X ≅ X ⊗ X`, the morphism `(g, z) ↦ (g • x z, z)`
is an isomorphism `G ⊗ Z ≅ X ⊗ Z`. -/
theorem isIso_lift_smul_snd_of_isIso_leftSMul [IsIso (ModObj.leftSMul G X)] {Z : C}
    (x : Z ⟶ X) : IsIso (lift (fst G Z • (snd G Z ≫ x)) (snd G Z)) := by
  have H := (ModObj.isIso_leftSMul_iff (M := G) (X := X)).1 ‹_›
  have key {T : C} (g : T ⟶ G) (z : T ⟶ Z) :
      lift g z ≫ lift (fst G Z • (snd G Z ≫ x)) (snd G Z) = lift (g • (z ≫ x)) z := by
    simp [comp_smul]
  rw [isIso_iff_yoneda_map_bijective]
  refine fun T ↦ ⟨fun t t' htt ↦ ?_, fun y ↦ ?_⟩
  · dsimp only at htt
    rw [← lift_comp_fst_snd t, ← lift_comp_fst_snd t', key, key] at htt
    have h₂ : t ≫ snd G Z = t' ≫ snd G Z := by simpa using congrArg (· ≫ snd X Z) htt
    have h₁ : (t ≫ fst G Z) • (t ≫ snd G Z ≫ x) = (t' ≫ fst G Z) • (t' ≫ snd G Z ≫ x) := by
      simpa using congrArg (· ≫ fst X Z) htt
    refine CartesianMonoidalCategory.hom_ext _ _
      ((H T (t ≫ snd G Z ≫ x) _).unique rfl ?_).symm h₂
    rw [h₁, reassoc_of% h₂]
  · obtain ⟨g, hg, -⟩ := H T (y ≫ snd X Z ≫ x) (y ≫ fst X Z)
    refine ⟨lift g (y ≫ snd X Z), ?_⟩
    dsimp only
    rw [key, Category.assoc, hg, lift_comp_fst_snd]

namespace ModObj

variable [IsIso (leftSMul G X)]

/-- The inverse of `(g, x) ↦ (g • x, x)` keeps the second component. -/
@[reassoc (attr := simp)]
theorem inv_leftSMul_snd : inv (leftSMul G X) ≫ snd G X = snd X X := by
  rw [IsIso.inv_comp_eq, leftSMul_snd]

variable (X) in
/-- The **difference morphism** of a pseudo-torsor `X` under `G`, an action for which
`(g, x) ↦ (g • x, x)` is an isomorphism: it sends `(x, y)` to the unique `g` with `g • x = y`
(`TauCeti.ModObj.eq_lift_diff_iff`). It is defined without a point of `X`, which need not
exist. -/
noncomputable def diff : X ⊗ X ⟶ G :=
  lift (snd X X) (fst X X) ≫ inv (leftSMul G X) ≫ fst G X

/-- The inverse of `(g, x) ↦ (g • x, x)` sends `(y, x)` to `(diff (x, y), x)`. -/
theorem lift_comp_inv_leftSMul {T : C} (x y : T ⟶ X) :
    lift y x ≫ inv (leftSMul G X) = lift (lift x y ≫ diff G X) x := by
  ext
  · simp only [diff, comp_lift_assoc, lift_snd, lift_fst, Category.assoc]
  · simp

/-- **The difference acts as a translation**: `diff (x, y) • x = y`. -/
@[simp]
theorem lift_diff_smul {T : C} (x y : T ⟶ X) : (lift x y ≫ diff G X) • x = y := by
  rw [← lift_leftSMul_eq_lift_iff, ← lift_comp_inv_leftSMul, Category.assoc, IsIso.inv_hom_id,
    Category.comp_id]

/-- The difference `diff (x, y)` is the unique `m` with `m • x = y`. -/
theorem eq_lift_diff_iff {T : C} (x y : T ⟶ X) (m : T ⟶ G) :
    m = lift x y ≫ diff G X ↔ m • x = y :=
  ⟨fun h ↦ h ▸ lift_diff_smul G x y, fun h ↦
    ((isIso_leftSMul_iff (M := G) (X := X)).1 ‹_› T x y).unique h (lift_diff_smul G x y)⟩

/-- The difference of a translate: `diff (x, m • x) = m`. -/
@[simp]
theorem lift_smul_diff {T : C} (x : T ⟶ X) (m : T ⟶ G) : lift x (m • x) ≫ diff G X = m :=
  ((eq_lift_diff_iff G x _ m).2 rfl).symm

/-- The difference of a point with itself is the unit: `diff (x, x) = 1`. -/
@[simp]
theorem lift_self_diff {T : C} (x : T ⟶ X) : lift x x ≫ diff G X = 1 :=
  ((eq_lift_diff_iff G x x 1).2 (one_smul _ x)).symm

/-- **A change of origin is a translation.** A point `β : T ⟶ X` of a pseudo-torsor identifies
the points of `X` over `T` with those of `G`, by `x ↦ diff (β, x)`, with inverse `m ↦ m • β`.
These bijections are compatible with base change along `g : T' ⟶ T` when `β` is replaced by
`g ≫ β` (`TauCeti.ModObj.diffEquiv_comp`). -/
@[expose, simps]
noncomputable def diffEquiv {T : C} (β : T ⟶ X) : (T ⟶ X) ≃ (T ⟶ G) where
  toFun x := lift β x ≫ diff G X
  invFun m := m • β
  left_inv x := lift_diff_smul G β x
  right_inv m := lift_smul_diff G β m

/-- The change of origin commutes with base change: `diffEquiv (g ≫ β) (g ≫ x)` is the base
change `g ≫ diffEquiv β x`. -/
theorem diffEquiv_comp {T T' : C} (g : T' ⟶ T) (β x : T ⟶ X) :
    diffEquiv G (g ≫ β) (g ≫ x) = g ≫ diffEquiv G β x := by
  rw [diffEquiv_apply, diffEquiv_apply, comp_lift_assoc]

end ModObj

end Monoid

variable {G X Y : C} [GrpObj G] [ModObj G X] [ModObj G Y]

namespace ModObj

/-- The difference is antisymmetric: `diff (x, y)⁻¹ = diff (y, x)`. -/
theorem inv_lift_diff [IsIso (leftSMul G X)] {T : C} (x y : T ⟶ X) :
    (lift x y ≫ diff G X)⁻¹ = lift y x ≫ diff G X := by
  refine (eq_lift_diff_iff G y x _).2 ?_
  have h := lift_diff_smul G x y
  calc (lift x y ≫ diff G X)⁻¹ • y = (lift x y ≫ diff G X)⁻¹ • (lift x y ≫ diff G X) • x := by
        rw [h]
    _ = x := inv_smul_smul _ _

/-- For a group acting on itself by left multiplication, the difference of `x` and `y` is
`y * x⁻¹`. The action is any `ModObj G G` whose action morphism is the multiplication, such as
`ModObj.regular G`. -/
theorem lift_diff_eq_mul_inv [ModObj G G] [IsIso (leftSMul G G)] (h : γ[G,G] = μ[G]) {T : C}
    (x y : T ⟶ G) : lift x y ≫ diff G G = y * x⁻¹ :=
  ((eq_lift_diff_iff G x y _).2 (by rw [Hom.smul_def, h, ← Hom.mul_def, inv_mul_cancel_right])).symm

end ModObj

/-- Translation of an acted-on object by a global group point. -/
noncomputable def translation (X : C) [ModObj G X] (g : 𝟙_ C ⟶ G) : X ≅ X where
  hom := (toUnit X ≫ g) • 𝟙 X
  inv := (toUnit X ≫ g⁻¹) • 𝟙 X
  hom_inv_id := by simp [comp_smul, ← SemigroupAction.mul_smul, ← MonObj.comp_mul]
  inv_hom_id := by simp [comp_smul, ← SemigroupAction.mul_smul, ← MonObj.comp_mul]

/-- Translation acts on points by the native test-object action. -/
@[reassoc (attr := simp)]
theorem comp_translation_hom {T : C} (x : T ⟶ X) (g : 𝟙_ C ⟶ G) :
    x ≫ (translation X g).hom = (toUnit T ≫ g) • x := by
  simp [translation, comp_smul]

/-- Inverse translation acts by the inverse group point. -/
@[reassoc (attr := simp)]
theorem comp_translation_inv {T : C} (x : T ⟶ X) (g : 𝟙_ C ⟶ G) :
    x ≫ (translation X g).inv = (toUnit T ≫ g⁻¹) • x := by
  simp [translation, comp_smul]

/-- Translation by the identity is the identity isomorphism. -/
@[simp]
theorem translation_one : translation X (1 : 𝟙_ C ⟶ G) = Iso.refl X := by
  apply Iso.ext
  simp [translation, MonObj.comp_one]

/-- Translation by a product composes translations in action order. -/
@[simp]
theorem translation_mul (g h : 𝟙_ C ⟶ G) :
    translation X (g * h) = translation X h ≪≫ translation X g := by
  apply Iso.ext
  simp [translation, comp_smul, MonObj.comp_mul, SemigroupAction.mul_smul]

/-- Translation by the inverse point is the inverse translation isomorphism. -/
@[simp]
theorem translation_inv (g : 𝟙_ C ⟶ G) :
    translation X g⁻¹ = (translation X g).symm := by
  apply Iso.ext
  rfl

/-- Equivariant morphisms intertwine translations. -/
@[reassoc]
theorem translation_hom_comp (g : 𝟙_ C ⟶ G) (f : X ⟶ Y) [IsModHom G f] :
    (translation X g).hom ≫ f = f ≫ (translation Y g).hom := by
  simp [translation, IsModHom.map_smul, comp_smul]

/-- The orbit morphism intertwines left translation with the action on its target. -/
@[reassoc]
theorem leftTranslation_hom_orbitMap (g : 𝟙_ C ⟶ G) (x : 𝟙_ C ⟶ X) :
    (TauCeti.leftTranslation g).hom ≫ orbitMap G x =
      orbitMap G x ≫ (translation X g).hom := by
  simp [TauCeti.leftTranslation_hom, comp_smul, SemigroupAction.mul_smul, orbitMap]

/-- Moving the base point of an orbit morphism amounts to right multiplication on the group.
The order of multiplication matters for a noncommutative group. -/
theorem orbitMap_smul (g : 𝟙_ C ⟶ G) (x : 𝟙_ C ⟶ X) :
    orbitMap G (g • x) = (GrpObj.mulRight g).hom ≫ orbitMap G x := by
  simp [orbitMap, ← Hom.mul_def, comp_smul, SemigroupAction.mul_smul]

end TauCeti

namespace CategoryTheory.Functor

open scoped Obj

variable {C D : Type*} [Category C] [Category D]
  [CartesianMonoidalCategory C] [CartesianMonoidalCategory D]
  (F : C ⥤ D) [F.Monoidal] (G X : C) [MonObj G] [ModObj G X]

/-- A monoidal functor between cartesian categories preserves orbit morphisms, with
the base point transported by its unit comparison. -/
theorem map_orbitMap (x : 𝟙_ C ⟶ X) :
    letI := F.modObjObj G X
    F.map (TauCeti.orbitMap G x) =
      TauCeti.orbitMap (F.obj G) (LaxMonoidal.ε F ≫ F.map x) := by
  let := F.modObjObj G X
  simp only [TauCeti.orbitMap, Hom.smul_def, modObjObj_smul]
  rw [Monoidal.toUnit_ε_assoc, ← F.map_comp, ← F.map_id G,
    Monoidal.lift_μ_assoc, ← F.map_comp]

end CategoryTheory.Functor
