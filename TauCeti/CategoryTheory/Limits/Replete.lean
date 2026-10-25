/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Filtered.Final
public import Mathlib.CategoryTheory.Functor.OfSequence
public import Mathlib.CategoryTheory.Limits.Types.Images
public import Mathlib.CategoryTheory.MorphismProperty.Limits

/-!
# Replete categories

A category is *replete* (Bhatt–Scholze) when sequential limits of epimorphisms are epimorphisms:
for every tower `⋯ ⟶ F (n + 1) ⟶ F n ⟶ ⋯ ⟶ F 0` whose transition maps are epimorphisms, the
projection `lim F ⟶ F 0` is an epimorphism. The category of types is replete. Repleteness is what
makes inverse limits of sheaves behave like inverse limits of sets: on a replete topos, countable
products are exact and derived limits of towers have amplitude `[0, 1]` (Bhatt–Scholze,
Propositions 3.1.9 and 3.1.11).

The main result here is that, in a replete category in which epimorphisms are stable under
base change, a morphism of towers `φ : F ⟶ G` induces an epimorphism `lim F ⟶ lim G` as soon as
`F 0 ⟶ G 0` and every comparison map `F (n + 1) ⟶ F n ×_{G n} G (n + 1)` are epimorphisms
(`TauCeti.IsReplete.epi_isLimitMap`). Levelwise epimorphisms do not suffice, already for sets.
Light condensed sets and modules are replete, see `TauCeti.Condensed.Light.Replete`.

## Main declarations

* `TauCeti.IsReplete`: replete categories.
* `TauCeti.IsReplete.epi_π_app`: in a replete category, every projection of a sequential limit
  of epimorphisms is an epimorphism.
* `TauCeti.IsReplete.of_equivalence`: repleteness is invariant under equivalence of categories.
* `TauCeti.IsReplete.epi_isLimitMap`: the induced map of limits of a morphism of towers whose
  comparison maps are epimorphisms is an epimorphism.
* `TauCeti.isReplete_type`: the category of types is replete.

## Implementation notes

`TauCeti.IsReplete.epi_isLimitMap` applies repleteness to the tower `lim G ×_{G n} F n`, whose
transition maps are base changes of the comparison maps and whose limit is `lim F`.

## References

* B. Bhatt and P. Scholze, *The pro-étale topology for schemes*, Astérisque 369 (2015),
  Definition 3.1.1 and Lemma 3.1.8.
-/

public section

universe v v' u u'

open CategoryTheory Limits

namespace TauCeti

variable (C : Type u) [Category.{v} C]

/-- A category is **replete** when sequential limits of epimorphisms are epimorphisms: for every
tower `⋯ ⟶ F (n + 1) ⟶ F n ⟶ ⋯ ⟶ F 0` whose transition maps are epimorphisms, the projection
`lim F ⟶ F 0` of every limit cone is an epimorphism. Every projection `lim F ⟶ F n` is then an
epimorphism (`TauCeti.IsReplete.epi_π_app`). -/
class IsReplete : Prop where
  epi_π_app_zero {F : ℕᵒᵖ ⥤ C} (hF : ∀ n, Epi (F.map (homOfLE (Nat.le_succ n)).op))
    {c : Cone F} (hc : IsLimit c) : Epi (c.π.app ⟨0⟩)

/-- The category of types is replete: a sequential limit of surjections is surjective. -/
instance isReplete_type : IsReplete (Type u) where
  epi_π_app_zero hF _ hc := (epi_iff_surjective _).2 <|
    Types.surjective_π_app_zero_of_surjective_map hc fun n ↦ (epi_iff_surjective _).1 (hF n)

namespace IsReplete

variable {C}

/-- In a replete category, every projection `lim F ⟶ F n` of a sequential limit of epimorphisms is
an epimorphism. -/
theorem epi_π_app [IsReplete C] {F : ℕᵒᵖ ⥤ C} (hF : ∀ n, Epi (F.map (homOfLE (Nat.le_succ n)).op))
    {c : Cone F} (hc : IsLimit c) (n : ℕ) : Epi (c.π.app ⟨n⟩) := by
  -- Reindex along `m ↦ n + m`, which is cofinal, so that the `n`-th projection becomes the first.
  -- The transition maps of the reindexed tower are those of `F`, and its first projection is
  -- `c.π.app ⟨n + 0⟩ = c.π.app ⟨n⟩`, by unfolding `Monotone.functor` and `Nat.add`.
  have hmono : Monotone fun m : ℕ ↦ n + m := fun _ _ h ↦ Nat.add_le_add_left h n
  have : hmono.functor.Final := hmono.final_functor_iff.2 fun m ↦ ⟨m, Nat.le_add_left m n⟩
  exact epi_π_app_zero (F := hmono.functor.op ⋙ F) (c := c.whisker hmono.functor.op)
    (fun m ↦ hF (n + m)) ((Functor.Initial.isLimitWhiskerEquiv hmono.functor.op c).symm hc)

/-- **Repleteness is invariant under equivalence of categories.** -/
theorem of_equivalence [IsReplete C] {D : Type u'} [Category.{v'} D] (e : C ≌ D) : IsReplete D where
  epi_π_app_zero {F} hF c hc := by
    have := epi_π_app_zero (F := F ⋙ e.inverse) (fun n ↦ e.inverse.map_epi _)
      (isLimitOfPreserves e.inverse hc)
    exact e.inverse.epi_of_epi_map this

section Map

variable [HasPullbacks C] {F G : ℕᵒᵖ ⥤ C} (φ : F ⟶ G) (cG : Cone G)

/-- The map `lim G ×_{G (n + 1)} F (n + 1) ⟶ lim G ×_{G n} F n` induced by the transition map
of `F`. -/
private noncomputable def pullbackTowerMap (n : ℕ) :
    pullback (cG.π.app ⟨n + 1⟩) (φ.app ⟨n + 1⟩) ⟶ pullback (cG.π.app ⟨n⟩) (φ.app ⟨n⟩) :=
  pullback.lift (pullback.fst _ _) (pullback.snd _ _ ≫ F.map (homOfLE (Nat.le_succ n)).op) (by
    rw [Category.assoc, φ.naturality, ← cG.w (homOfLE (Nat.le_succ n)).op,
      pullback.condition_assoc])

/-- The tower `lim G ×_{G n} F n` used in the proof of `TauCeti.IsReplete.epi_isLimitMap`. -/
private noncomputable def pullbackTower : ℕᵒᵖ ⥤ C :=
  Functor.ofOpSequence (X := fun n ↦ pullback (cG.π.app ⟨n⟩) (φ.app ⟨n⟩)) (pullbackTowerMap φ cG)

namespace pullbackTower

/-- The projection `lim G ×_{G n} F n ⟶ lim G`. -/
private noncomputable def fst (n : ℕ) : (pullbackTower φ cG).obj ⟨n⟩ ⟶ cG.pt :=
  pullback.fst (cG.π.app ⟨n⟩) (φ.app ⟨n⟩)

/-- The projection `lim G ×_{G n} F n ⟶ F n`. -/
private noncomputable def snd (n : ℕ) : (pullbackTower φ cG).obj ⟨n⟩ ⟶ F.obj ⟨n⟩ :=
  pullback.snd (cG.π.app ⟨n⟩) (φ.app ⟨n⟩)

/-- The map into `lim G ×_{G n} F n` given by compatible maps into `lim G` and `F n`. -/
private noncomputable def lift {Z : C} (n : ℕ) (a : Z ⟶ cG.pt) (b : Z ⟶ F.obj ⟨n⟩)
    (w : a ≫ cG.π.app ⟨n⟩ = b ≫ φ.app ⟨n⟩) : Z ⟶ (pullbackTower φ cG).obj ⟨n⟩ :=
  pullback.lift a b w

@[reassoc (attr := simp)]
private lemma lift_fst {Z : C} (n : ℕ) (a : Z ⟶ cG.pt) (b : Z ⟶ F.obj ⟨n⟩)
    (w : a ≫ cG.π.app ⟨n⟩ = b ≫ φ.app ⟨n⟩) : lift φ cG n a b w ≫ fst φ cG n = a :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
private lemma lift_snd {Z : C} (n : ℕ) (a : Z ⟶ cG.pt) (b : Z ⟶ F.obj ⟨n⟩)
    (w : a ≫ cG.π.app ⟨n⟩ = b ≫ φ.app ⟨n⟩) : lift φ cG n a b w ≫ snd φ cG n = b :=
  pullback.lift_snd _ _ _

private lemma hom_ext {Z : C} {n : ℕ} {f g : Z ⟶ (pullbackTower φ cG).obj ⟨n⟩}
    (h₁ : f ≫ fst φ cG n = g ≫ fst φ cG n) (h₂ : f ≫ snd φ cG n = g ≫ snd φ cG n) : f = g :=
  pullback.hom_ext h₁ h₂

@[reassoc]
private lemma condition (n : ℕ) : fst φ cG n ≫ cG.π.app ⟨n⟩ = snd φ cG n ≫ φ.app ⟨n⟩ :=
  pullback.condition

private lemma map_succ (n : ℕ) :
    (pullbackTower φ cG).map (homOfLE (Nat.le_succ n)).op = pullbackTowerMap φ cG n :=
  Functor.ofOpSequence_map_homOfLE_succ _ n

@[reassoc (attr := simp)]
private lemma map_succ_fst (n : ℕ) :
    (pullbackTower φ cG).map (homOfLE (Nat.le_succ n)).op ≫ fst φ cG n = fst φ cG (n + 1) := by
  rw [map_succ]
  exact pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
private lemma map_succ_snd (n : ℕ) :
    (pullbackTower φ cG).map (homOfLE (Nat.le_succ n)).op ≫ snd φ cG n =
      snd φ cG (n + 1) ≫ F.map (homOfLE (Nat.le_succ n)).op := by
  rw [map_succ]
  exact pullback.lift_snd _ _ _

/-- The first projection of a cone over the tower `lim G ×_{G n} F n` does not depend on `n`. -/
private lemma π_app_fst (s : Cone (pullbackTower φ cG)) (n : ℕ) :
    s.π.app ⟨n⟩ ≫ fst φ cG n = s.π.app ⟨0⟩ ≫ fst φ cG 0 := by
  induction n with
  | zero => rfl
  | succ n ih => rw [← ih, ← s.w (homOfLE (Nat.le_succ n)).op, Category.assoc, map_succ_fst]

/-- The transition maps of the tower `lim G ×_{G n} F n` are base changes of the comparison maps
`F (n + 1) ⟶ F n ×_{G n} G (n + 1)`, along the map
`lim G ×_{G n} F n ⟶ F n ×_{G n} G (n + 1)` induced by the projection `lim G ⟶ G (n + 1)`. -/
private lemma isPullback_map_succ (n : ℕ) :
    IsPullback (snd φ cG (n + 1)) ((pullbackTower φ cG).map (homOfLE (Nat.le_succ n)).op)
      (pullback.lift (F.map (homOfLE (Nat.le_succ n)).op) (φ.app ⟨n + 1⟩) (φ.naturality _))
      (pullback.lift (snd φ cG n) (fst φ cG n ≫ cG.π.app ⟨n + 1⟩) (by
        rw [← condition, Category.assoc, cG.w (homOfLE (Nat.le_succ n)).op])) := by
  -- Paste below it the square comparing `lim G ×_{G n} F n` with `F n ×_{G n} G (n + 1)`, which
  -- is itself a pullback because pasting it with the square defining `F n ×_{G n} G (n + 1)`
  -- gives the square defining `lim G ×_{G n} F n`.
  have hbot : IsPullback
      (pullback.lift (snd φ cG n) (fst φ cG n ≫ cG.π.app ⟨n + 1⟩) (by
        rw [← condition, Category.assoc, cG.w (homOfLE (Nat.le_succ n)).op]))
      (fst φ cG n) (pullback.snd _ _) (cG.π.app ⟨n + 1⟩) := by
    refine IsPullback.of_right ?_ (pullback.lift_snd _ _ _) (IsPullback.of_hasPullback _ _)
    rw [pullback.lift_fst, cG.w (homOfLE (Nat.le_succ n)).op]
    exact (IsPullback.of_hasPullback (cG.π.app ⟨n⟩) (φ.app ⟨n⟩)).flip
  refine IsPullback.of_bot ?_ (pullback.hom_ext (by simp) (by simp [condition])) hbot
  rw [map_succ_fst, pullback.lift_snd]
  exact (IsPullback.of_hasPullback (cG.π.app ⟨n + 1⟩) (φ.app ⟨n + 1⟩)).flip

private lemma isPullback_fst_zero :
    IsPullback (snd φ cG 0) (fst φ cG 0) (φ.app ⟨0⟩) (cG.π.app ⟨0⟩) :=
  (IsPullback.of_hasPullback (cG.π.app ⟨0⟩) (φ.app ⟨0⟩)).flip

variable {cG} (hcG : IsLimit cG) (cF : Cone F)

/-- The cone over the tower `lim G ×_{G n} F n` with vertex `lim F`, with components given by
the induced map `lim F ⟶ lim G` and the projections `lim F ⟶ F n`. -/
private noncomputable abbrev cone : Cone (pullbackTower φ cG) where
  pt := cF.pt
  π := NatTrans.ofOpSequence
    (fun n ↦ lift φ cG n (hcG.map cF φ) (cF.π.app ⟨n⟩) (IsLimit.map_π _ _ _ _)) fun n ↦
      hom_ext φ cG (by simp) (by simp)

private lemma cone_π_app_fst (n : ℕ) : (cone φ hcG cF).π.app ⟨n⟩ ≫ fst φ cG n = hcG.map cF φ :=
  lift_fst _ _ _ _ _ _

private lemma cone_π_app_snd (n : ℕ) : (cone φ hcG cF).π.app ⟨n⟩ ≫ snd φ cG n = cF.π.app ⟨n⟩ :=
  lift_snd _ _ _ _ _ _

/-- The cone `pullbackTower.cone` is a limit cone: `lim F` is the limit of the tower
`lim G ×_{G n} F n`. -/
private noncomputable def isLimitCone (hcF : IsLimit cF) :
    IsLimit (cone φ hcG cF) where
  lift s := hcF.lift
    { pt := s.pt
      π := NatTrans.ofOpSequence (fun n ↦ s.π.app ⟨n⟩ ≫ snd φ cG n) fun n ↦ by
        dsimp only [Functor.const_obj_obj, Functor.const_obj_map]
        rw [Category.id_comp, Category.assoc, ← map_succ_snd, ← Category.assoc, s.w] }
  fac s := by
    rintro ⟨n⟩
    refine hom_ext φ cG (hcG.hom_ext fun ⟨m⟩ ↦ ?_) (by simp)
    simp only [Category.assoc, NatTrans.ofOpSequence_app, lift_fst_assoc, IsLimit.map_π,
      IsLimit.fac_assoc]
    rw [← condition, ← Category.assoc, ← Category.assoc, π_app_fst φ cG s m, π_app_fst φ cG s n]
  uniq s m hm := hcF.hom_ext fun ⟨n⟩ ↦ by
    rw [IsLimit.fac, NatTrans.ofOpSequence_app, ← hm, Category.assoc, cone_π_app_snd]

end pullbackTower

variable {cG} (hcG : IsLimit cG) [(MorphismProperty.epimorphisms C).IsStableUnderBaseChange]
  [IsReplete C]

/-- **Epimorphisms of inverse limits** (Bhatt–Scholze, Lemma 3.1.8). In a replete category in
which epimorphisms are stable under base change, let `φ : F ⟶ G` be a morphism of towers such that
`F 0 ⟶ G 0` and every comparison map `F (n + 1) ⟶ F n ×_{G n} G (n + 1)` are epimorphisms. Then
the induced map `lim F ⟶ lim G` is an epimorphism. -/
theorem epi_isLimitMap {cF : Cone F} (hcF : IsLimit cF) (h₀ : Epi (φ.app ⟨0⟩))
    (h : ∀ n, Epi (pullback.lift (F.map (homOfLE (Nat.le_succ n)).op) (φ.app ⟨n + 1⟩)
      (φ.naturality _))) :
    Epi (hcG.map cF φ) := by
  have hW (n : ℕ) : Epi ((pullbackTower φ cG).map (homOfLE (Nat.le_succ n)).op) :=
    MorphismProperty.of_isPullback (P := MorphismProperty.epimorphisms C)
      (pullbackTower.isPullback_map_succ φ cG n) (h n)
  have hfst : Epi (pullbackTower.fst φ cG 0) :=
    MorphismProperty.of_isPullback (P := MorphismProperty.epimorphisms C)
      (pullbackTower.isPullback_fst_zero φ cG) h₀
  have hπ := epi_π_app_zero hW (pullbackTower.isLimitCone φ hcG cF hcF)
  rw [← pullbackTower.cone_π_app_fst φ hcG cF 0]
  exact epi_comp _ _

end Map

end IsReplete

end TauCeti
