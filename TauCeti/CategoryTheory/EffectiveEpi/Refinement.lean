/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.EffectiveEpi.Descent

/-!
# Refining a cover in descent data

A descent datum relative to `p : S' ⟶ S` pulls back along a morphism `q : T ⟶ S'` to a
descent datum relative to `q ≫ p`. If all base changes of `q` are effective epimorphisms,
effectivity can be checked after this refinement. This permits replacing a cover by an
affine cover of its source before constructing the descended object. In particular,
`refineHomEquiv` gives full faithfulness and
`exists_baseChange_hom_isIso_iff_refine` preserves each possible descended model.

The construction uses the action form of `TauCeti.DescentDatum` and the universal property of
`TauCeti.descendHom`. The comparison with canonical data uses Mathlib's
`CategoryTheory.Limits.pullbackLeftPullbackSndIso`.

## References

* [The Stacks Project, Tag 02W0](https://stacks.math.columbia.edu/tag/02W0),
  full faithfulness under refinement.
-/

public section

open CategoryTheory Limits

namespace TauCeti.DescentDatum

universe v u

variable {C : Type u} [Category.{v} C] [HasPullbacks C]
  {S S' T : C} {p : S' ⟶ S} (q : T ⟶ S') {X Y : Over S'}

/-- The map from the refined action space to the original action space. -/
noncomputable def refineActionComparison (X : Over S') :
    pullback (q ≫ p) (((Over.pullback q).obj X).hom ≫ q ≫ p) ⟶ pullback p (X.hom ≫ p) :=
  pullback.lift (pullback.fst _ _ ≫ q) (pullback.snd _ _ ≫ pullback.fst X.hom q) (by
    simp only [Category.assoc]
    rw [pullback.condition_assoc]
    exact pullback.condition)

@[reassoc (attr := simp)]
theorem refineActionComparison_fst (X : Over S') :
    refineActionComparison (p := p) q X ≫ pullback.fst p (X.hom ≫ p) = pullback.fst _ _ ≫ q :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem refineActionComparison_snd (X : Over S') :
    refineActionComparison (p := p) q X ≫ pullback.snd p (X.hom ≫ p) =
      pullback.snd _ _ ≫ pullback.fst X.hom q :=
  pullback.lift_snd _ _ _

/-- Refine a descent datum along `q : T ⟶ S'`: the action sends `(t, (x, t₀))` to
`(q(t) · x, t)`. -/
noncomputable def refine (D : DescentDatum p X) :
    DescentDatum (q ≫ p) ((Over.pullback q).obj X) where
  act := pullback.lift (refineActionComparison (p := p) q X ≫ D.act) (pullback.fst _ _) (by simp)
  act_hom := by simp
  lift_act := by
    apply pullback.hom_ext
    · have h : pullback.lift ((Over.pullback q).obj X).hom (𝟙 _) (by simp) ≫
          refineActionComparison (p := p) q X =
          pullback.fst X.hom q ≫ pullback.lift (f := p) X.hom (𝟙 _) (by simp) := by
        apply pullback.hom_ext <;> simp [pullback.condition]
      simp only [Category.assoc, pullback.lift_fst]
      rw [reassoc_of% h, D.lift_act]
      simp
    · simp
  act_assoc := by
    apply pullback.hom_ext
    · -- Compare twice-iterated action spaces, where the original cocycle applies.
      let a : pullback (q ≫ p)
          (pullback.fst (q ≫ p) (((Over.pullback q).obj X).hom ≫ q ≫ p) ≫ q ≫ p) ⟶
          pullback p (pullback.fst p (X.hom ≫ p) ≫ p) := pullback.lift (f := p)
          (g := pullback.fst p (X.hom ≫ p) ≫ p) (pullback.fst (q ≫ p)
          (pullback.fst (q ≫ p) (((Over.pullback q).obj X).hom ≫ q ≫ p) ≫ q ≫ p) ≫ q)
          (pullback.snd _ _ ≫ refineActionComparison (p := p) q X) (by
            simp only [Category.assoc, refineActionComparison_fst_assoc]
            exact pullback.condition)
      have h := a ≫= D.act_assoc
      simp only [Category.assoc, pullback.lift_fst]
      simp only [← Category.assoc] at h ⊢
      convert h using 2 <;> apply pullback.hom_ext <;> simp [a]
    · simp

@[reassoc (attr := simp)]
theorem refine_act_fst (D : DescentDatum p X) :
    (D.refine q).act ≫ pullback.fst X.hom q = refineActionComparison (p := p) q X ≫ D.act :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem refine_act_snd (D : DescentDatum p X) :
    (D.refine q).act ≫ pullback.snd X.hom q = pullback.fst _ _ :=
  pullback.lift_snd _ _ _

/-- Refinement acts on morphisms of descent data by pullback along `q`. -/
noncomputable def Hom.refine {D : DescentDatum p X} {E : DescentDatum p Y} (f : Hom D E) :
    Hom (D.refine q) (E.refine q) where
  hom := (Over.pullback q).map f.hom
  map_act := by
    apply pullback.hom_ext
    · simp only [Category.assoc, refine_act_fst, refine_act_fst_assoc, Over.pullback_map_left,
        pullback.lift_fst]
      rw [← f.map_act]
      simp only [← Category.assoc]
      congr 1
      apply pullback.hom_ext <;> simp
    · simp

@[simp]
theorem Hom.refine_hom {D : DescentDatum p X} {E : DescentDatum p Y} (f : Hom D E) :
    (f.refine q).hom = (Over.pullback q).map f.hom := (rfl)

@[simp]
theorem Hom.refine_id (D : DescentDatum p X) : (Hom.id D).refine q = Hom.id (D.refine q) := by
  apply Hom.ext
  simp

@[simp]
theorem Hom.refine_comp {Z : Over S'} {D : DescentDatum p X} {E : DescentDatum p Y}
    {F : DescentDatum p Z} (f : Hom D E) (g : Hom E F) :
    (g.comp f).refine q = (g.refine q).comp (f.refine q) := by
  apply Hom.ext
  simp

instance Hom.isIso_refine_hom {D : DescentDatum p X} {E : DescentDatum p Y} (f : Hom D E)
    [IsIso f.hom] : IsIso (f.refine q).hom := by
  rw [Hom.refine_hom]
  infer_instance

/-- Refining a canonical descent datum agrees with canonical descent along the composite cover.
The underlying isomorphism is the standard comparison between iterated and direct pullbacks. -/
noncomputable def baseChangeRefineHom (X₀ : Over S) :
    Hom ((baseChange p X₀).refine q) (baseChange (q ≫ p) X₀) where
  hom := Over.homMk (pullbackLeftPullbackSndIso X₀.hom p q).hom
  map_act := by
    apply pullback.hom_ext <;> simp [refine, refineActionComparison]

@[simp]
theorem baseChangeRefineHom_hom_left (X₀ : Over S) :
    (baseChangeRefineHom (p := p) q X₀).hom.left =
      (pullbackLeftPullbackSndIso X₀.hom p q).hom := (rfl)

instance isIso_baseChangeRefineHom_hom (X₀ : Over S) :
    IsIso (baseChangeRefineHom (p := p) q X₀).hom := by
  have : IsIso ((Over.forget T).map (baseChangeRefineHom (p := p) q X₀).hom) :=
    inferInstanceAs (IsIso (pullbackLeftPullbackSndIso X₀.hom p q).hom)
  exact isIso_of_reflects_iso _ (Over.forget T)

-- When two points lie over the same point of `S'`, the original action is the identity.
private theorem lift_refine_act {Z : C} (D : DescentDatum p X)
    (a : Z ⟶ T) (b : Z ⟶ ((Over.pullback q).obj X).left)
    (h : a ≫ q = b ≫ pullback.fst X.hom q ≫ X.hom) :
    pullback.lift (f := q ≫ p) (g := ((Over.pullback q).obj X).hom ≫ q ≫ p) a b
      (by simpa [Category.assoc, pullback.condition] using h =≫ p) ≫ (D.refine q).act ≫
      pullback.fst X.hom q = b ≫ pullback.fst X.hom q := by
  rw [refine_act_fst]
  have h' : pullback.lift (f := q ≫ p) (g := ((Over.pullback q).obj X).hom ≫ q ≫ p) a b
      (by simpa [Category.assoc, pullback.condition] using h =≫ p) ≫
      refineActionComparison (p := p) q X =
      b ≫ pullback.fst X.hom q ≫ pullback.lift (f := p) X.hom (𝟙 _) (by simp) := by
    apply pullback.hom_ext <;> simp [h]
  rw [reassoc_of% h', D.lift_act]
  simp

private theorem Hom.comp_fst_eq_of_refine {D : DescentDatum p X} {E : DescentDatum p Y}
    (f : Hom (D.refine q) (E.refine q)) {Z : C}
    (a b : Z ⟶ ((Over.pullback q).obj X).left)
    (h : a ≫ pullback.fst X.hom q = b ≫ pullback.fst X.hom q) :
    a ≫ f.hom.left ≫ pullback.fst Y.hom q = b ≫ f.hom.left ≫ pullback.fst Y.hom q := by
  have ht : a ≫ pullback.snd X.hom q ≫ q = b ≫ pullback.fst X.hom q ≫ X.hom := by
    rw [← pullback.condition]
    simpa only [Category.assoc] using h =≫ X.hom
  let j := pullback.lift (f := q ≫ p) (g := ((Over.pullback q).obj X).hom ≫ q ≫ p)
    (a ≫ pullback.snd X.hom q) b
    (by simpa [Category.assoc, pullback.condition] using ht =≫ p)
  have hj : j ≫ (D.refine q).act = a := by
    apply pullback.hom_ext
    · simpa [j, h] using lift_refine_act q D (a ≫ pullback.snd X.hom q) b
        (by simpa only [Category.assoc] using ht)
    · simp [j]
  have he := j ≫= f.map_act =≫ pullback.fst Y.hom q
  simp only [Category.assoc] at he
  rw [reassoc_of% hj] at he
  refine he.symm.trans ?_
  have hw : f.hom.left ≫ pullback.snd Y.hom q = pullback.snd X.hom q := Over.w f.hom
  have ht' : a ≫ pullback.snd X.hom q ≫ q =
      (b ≫ f.hom.left) ≫ pullback.fst Y.hom q ≫ Y.hom := by
    simp only [Category.assoc, pullback.condition, reassoc_of% hw]
    simpa only [pullback.condition] using ht
  have hm : j ≫ pullback.map (q ≫ p) (((Over.pullback q).obj X).hom ≫ q ≫ p) (q ≫ p)
      (((Over.pullback q).obj Y).hom ≫ q ≫ p) (𝟙 T) f.hom.left (𝟙 S) (by simp)
        (by simp [reassoc_of% hw]) =
      pullback.lift (f := q ≫ p) (g := ((Over.pullback q).obj Y).hom ≫ q ≫ p)
        (a ≫ pullback.snd X.hom q) (b ≫ f.hom.left)
        (by simpa [Category.assoc, pullback.condition] using ht' =≫ p) := by
    apply pullback.hom_ext <;> simp [j]
  simpa only [Category.assoc] using
    (congrArg (· ≫ (E.refine q).act ≫ pullback.fst Y.hom q) hm).trans
      (lift_refine_act q E _ _ (by simpa only [Category.assoc] using ht'))

section Effective

variable [∀ {Z : C} (g : Z ⟶ S'), EffectiveEpi (pullback.fst g q)]
  {D : DescentDatum p X} {E : DescentDatum p Y}

private noncomputable def Hom.unrefineHom (f : Hom (D.refine q) (E.refine q)) : X ⟶ Y :=
  descendHom q f.hom (f.comp_fst_eq_of_refine q _ _ (by simp))

@[reassoc (attr := simp)]
private theorem Hom.fst_unrefineHom_left (f : Hom (D.refine q) (E.refine q)) :
    pullback.fst X.hom q ≫ (f.unrefineHom q).left = f.hom.left ≫ pullback.fst Y.hom q :=
  fst_comp_descendHom_left q _ _

private theorem Hom.unrefineHom_map_act (f : Hom (D.refine q) (E.refine q)) :
    pullback.map p (X.hom ≫ p) p (Y.hom ≫ p) (𝟙 S') (f.unrefineHom q).left (𝟙 S)
      (by simp)
      (by simpa only [Category.assoc, Category.comp_id] using
        (Over.w (f.unrefineHom q) =≫ p).symm) ≫
      E.act = D.act ≫ (f.unrefineHom q).left := by
  -- Lift the two `S'` coordinates separately along `q`. Both resulting projections are
  -- effective epimorphisms, so the refined intertwining identity detects the original one.
  let r₁ := pullback.fst (pullback.fst p (X.hom ≫ p)) q
  let r₂ := pullback.fst (r₁ ≫ pullback.snd p (X.hom ≫ p) ≫ X.hom) q
  have : Epi r₁ := inferInstanceAs (Epi (pullback.fst _ q))
  have : Epi r₂ := inferInstanceAs (Epi (pullback.fst _ q))
  rw [← cancel_epi r₁, ← cancel_epi r₂]
  let b := pullback.lift (r₂ ≫ r₁ ≫ pullback.snd p (X.hom ≫ p))
    (pullback.snd (r₁ ≫ pullback.snd p (X.hom ≫ p) ≫ X.hom) q) (by
      simpa only [Category.assoc, r₂] using pullback.condition)
  let a := r₂ ≫ pullback.snd (pullback.fst p (X.hom ≫ p)) q
  have ha : a ≫ q = r₂ ≫ r₁ ≫ pullback.fst p (X.hom ≫ p) := by
    simp [a, r₁, pullback.condition]
  let j : _ ⟶ pullback (q ≫ p) (((Over.pullback q).obj X).hom ≫ q ≫ p) :=
    pullback.lift a b (by
      simp only [Over.pullback_obj_hom, b, pullback.lift_snd_assoc]
      rw [reassoc_of% ha, pullback.condition]
      simpa only [Category.assoc, r₂] using
        (pullback.condition_assoc (f := r₁ ≫ pullback.snd p (X.hom ≫ p) ≫ X.hom)
          (g := q) p))
  have hj : j ≫ refineActionComparison (p := p) q X = r₂ ≫ r₁ := by
    apply pullback.hom_ext <;> simp [j, a, b, ha]
  have hD : r₂ ≫ r₁ ≫ D.act ≫ (f.unrefineHom q).left =
      j ≫ (D.refine q).act ≫ f.hom.left ≫ pullback.fst Y.hom q := by
    have hh := (j ≫ (D.refine q).act) ≫= f.fst_unrefineHom_left q
    simpa only [Category.assoc, refine_act_fst_assoc, reassoc_of% hj] using hh
  rw [hD]
  have h := j ≫= f.map_act =≫ pullback.fst Y.hom q
  simp only [Category.assoc, refine_act_fst] at h
  rw [← h]
  simp only [← Category.assoc]
  congr 1
  apply pullback.hom_ext
  · simp [j, ha]
  · have hh := b ≫= f.fst_unrefineHom_left q
    simpa only [Category.assoc, j, b, refineActionComparison, pullback.map,
      pullback.lift_fst, pullback.lift_fst_assoc, pullback.lift_snd,
      pullback.lift_snd_assoc, Category.id_comp, Category.comp_id] using hh

/-- A morphism between refined descent data descends to a morphism of the original data
when every base change of the refining map is an effective epimorphism. -/
noncomputable def Hom.unrefine (f : Hom (D.refine q) (E.refine q)) : Hom D E where
  hom := f.unrefineHom q
  map_act := f.unrefineHom_map_act q

/-- The morphism descended from a refinement agrees with the given morphism after pullback. -/
@[reassoc (attr := simp)]
theorem Hom.fst_unrefine_hom_left (f : Hom (D.refine q) (E.refine q)) :
    pullback.fst X.hom q ≫ (f.unrefine q).hom.left =
      f.hom.left ≫ pullback.fst Y.hom q :=
  f.fst_unrefineHom_left q

/-- Pulling the descended morphism back to the refinement recovers the given morphism. -/
@[simp]
theorem Hom.refine_unrefine (f : Hom (D.refine q) (E.refine q)) :
    (f.unrefine q).refine q = f := by
  apply Hom.ext
  apply Over.OverMorphism.ext
  apply pullback.hom_ext
  · simp [Hom.unrefine, Hom.fst_unrefineHom_left]
  · simpa [Hom.refine, Hom.unrefine] using (Over.w f.hom).symm

/-- Refinement followed by descent recovers a morphism of the original descent data. -/
@[simp]
theorem Hom.unrefine_refine (f : Hom D E) : (f.refine q).unrefine q = f := by
  apply Hom.ext
  apply (Over.pullback q).map_injective
  exact congrArg Hom.hom (Hom.refine_unrefine q (f.refine q))

/-- Refinement is fully faithful on descent data along a universally effective epimorphism. -/
noncomputable def refineHomEquiv : Hom D E ≃ Hom (D.refine q) (E.refine q) where
  toFun := Hom.refine q
  invFun := Hom.unrefine q
  left_inv := Hom.unrefine_refine q
  right_inv := Hom.refine_unrefine q

@[simp]
theorem refineHomEquiv_apply (f : Hom D E) : refineHomEquiv q f = f.refine q := (rfl)

@[simp]
theorem refineHomEquiv_symm_apply (f : Hom (D.refine q) (E.refine q)) :
    (refineHomEquiv q).symm f = f.unrefine q := (rfl)

/-- A fixed object is a model of a descent datum exactly when it is a model after refining
by a universally effective epimorphism. The comparison retains the full descent datum. -/
theorem exists_baseChange_hom_isIso_iff_refine (D : DescentDatum p X) (X₀ : Over S) :
    (∃ f : Hom (baseChange p X₀) D, IsIso f.hom) ↔
      ∃ f : Hom (baseChange (q ≫ p) X₀) (D.refine q), IsIso f.hom := by
  constructor
  · rintro ⟨f, hf⟩
    exact ⟨(f.refine q).comp (baseChangeRefineHom q X₀).inv, by
      rw [Hom.comp_hom]
      infer_instance⟩
  · rintro ⟨f, hf⟩
    let g := f.comp (baseChangeRefineHom q X₀)
    have : IsIso g.hom := by
      dsimp only [g]
      rw [Hom.comp_hom]
      infer_instance
    have : IsIso ((Over.pullback q).map (g.unrefine q).hom) := by
      rw [← Hom.refine_hom, Hom.refine_unrefine]
      infer_instance
    exact ⟨g.unrefine q, isIso_of_reflects_iso _ (Over.pullback q)⟩

end Effective

end TauCeti.DescentDatum
