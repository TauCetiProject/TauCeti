/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Comma.Over.Pullback
public import Mathlib.CategoryTheory.Limits.Shapes.KernelPair
public import TauCeti.CategoryTheory.Limits.Shapes.Pullback.DescentDatum
public import TauCeti.CategoryTheory.Limits.Shapes.Pullback.Section

/-!
# Descent of sections and morphisms along effective epimorphisms

Let `p : S' ⟶ S` be a morphism in a category with pullbacks, and let `S'' = S' ×_S S'`, with
projections `pr₁ pr₂ : S'' ⟶ S'`. For an object `X` over `S` write `X' = X ×_S S'` and
`X'' = X ×_S S''`; the projections induce `pr₁^*, pr₂^* : X'' ⟶ X'`, the base changes of the
second factor along `pr₁` and `pr₂` (`pullback.mapSnd`).

This file proves effective descent, with uniqueness, of sections and of morphisms.

* A section `s'` of `Y' ⟶ S'` whose two pullbacks to `S''` agree is the base change of a unique
  section of `Y ⟶ S`, provided that `p` is an effective epimorphism. A section of
  `Y ×_S S'' ⟶ S''` is determined by its `S''`-point of `Y`, so the condition says
  `pr₁ ≫ s' ≫ fst = pr₂ ≫ s' ≫ fst`.
* A morphism `φ : X' ⟶ Y'` over `S'` whose two pullbacks to `S''` agree is the base change of a
  unique morphism `X ⟶ Y` over `S`, provided that the base change `X' ⟶ X` of `p` is an
  effective epimorphism. A morphism `X'' ⟶ Y ×_S S''` over `S''` is determined by its composite
  to `Y`, so the condition says `pr₁^* ≫ φ ≫ fst = pr₂^* ≫ φ ≫ fst`.

In both cases base change is a bijection onto the sections, respectively morphisms, satisfying
the descent condition (`sectionDescentEquiv`, `homDescentEquiv`). The proof of the second case
uses that `pr₁^*, pr₂^*` form the kernel pair of `X' ⟶ X` (`pullback.isKernelPair_mapSnd`), so
that `X' ⟶ X` is their coequalizer.
Uniqueness on its own only needs base change of `p` to be an epimorphism, and is Mathlib's
`CategoryTheory.Over.faithful_pullback`.

In the language of descent data (`TauCeti.DescentDatum`), a morphism
`baseChange p X ⟶ baseChange p Y` of canonical descent data is a morphism over `S'` satisfying the
descent condition. So base change from objects over `S` to descent data relative to `p` is fully
faithful (`DescentDatum.baseChangeHomEquiv`). This is the uniqueness half of effective descent of
objects: an object `X` over `S` with an isomorphism of descent data `baseChange p X ≅ D` is unique
up to a unique isomorphism compatible with the descent data (`DescentDatum.Hom.descendIso`).

For schemes, Mathlib shows that a flat surjective morphism which is quasi-compact, or locally of
finite presentation, is an effective epimorphism, and these properties are stable under base
change (`Mathlib.AlgebraicGeometry.Sites.Fpqc`). Instance search therefore discharges the
hypotheses here for any fpqc or fppf morphism `p : S' ⟶ S` of schemes, and the results are
effective fpqc (and fppf) descent of sections and morphisms of schemes.

## Main definitions

* `TauCeti.descendSection`: the section of `Y ⟶ S` descended from a section of `Y ×_S S' ⟶ S'`
  satisfying the descent condition.
* `TauCeti.descendHom`: the morphism `X ⟶ Y` over `S` descended from a morphism
  `X ×_S S' ⟶ Y ×_S S'` over `S'` satisfying the descent condition.
* `TauCeti.sectionDescentEquiv`, `TauCeti.homDescentEquiv`: base change as a bijection onto the
  sections, respectively morphisms, satisfying the descent condition.
* `TauCeti.DescentDatum.baseChangeHomEquiv`: base change as a bijection from morphisms over `S`
  to morphisms of canonical descent data.
* `TauCeti.DescentDatum.Hom.descendIso`: the isomorphism between two objects over `S` whose
  canonical descent data are isomorphic to the same descent datum, unique by
  `DescentDatum.Hom.eq_descendIso`.

## References

* [A. Vistoli, *Notes on Grothendieck topologies, fibered categories and descent theory*],
  Theorem 2.55 (representable functors are fpqc sheaves).
-/

public section

namespace TauCeti

open CategoryTheory Limits

universe v u

variable {C : Type u} [Category.{v} C] [HasPullbacks C] {S S' : C} (p : S' ⟶ S)

section Section

variable {Y : C} (g : Y ⟶ S) [EffectiveEpi p]

/-- **Descent of a section.** Let `p : S' ⟶ S` be an effective epimorphism and `g : Y ⟶ S`. A
morphism `s' : S' ⟶ Y ×_S S'` whose two pullbacks to `S' ×_S S'` agree as `S' ×_S S'`-points of
`Y` descends to a morphism `S ⟶ Y` (`comp_descendSection`). If `s'` is a section of
`Y ×_S S' ⟶ S'`, its descent is a section of `g` (`descendSection_comp`) whose base change is `s'`
(`pullbackSection_descendSection`). -/
noncomputable def descendSection (s' : S' ⟶ pullback g p)
    (h : pullback.fst p p ≫ s' ≫ pullback.fst g p = pullback.snd p p ≫ s' ≫ pullback.fst g p) :
    S ⟶ Y :=
  Cofork.IsColimit.desc (isColimitCoforkOfEffectiveEpi p _ (pullback.isLimit p p))
    (s' ≫ pullback.fst g p) h

/-- The descended section, pulled back to `S'`, is the `S'`-point of `Y` given by `s'`. -/
@[reassoc (attr := simp)]
theorem comp_descendSection (s' : S' ⟶ pullback g p)
    (h : pullback.fst p p ≫ s' ≫ pullback.fst g p = pullback.snd p p ≫ s' ≫ pullback.fst g p) :
    p ≫ descendSection p g s' h = s' ≫ pullback.fst g p := by
  simpa [descendSection, Cofork.π_ofπ] using
    Cofork.IsColimit.π_desc' (isColimitCoforkOfEffectiveEpi p _ (pullback.isLimit p p)) _ h

/-- The descent of a section of `Y ×_S S' ⟶ S'` is a section of `g`. -/
@[reassoc (attr := simp)]
theorem descendSection_comp (s' : S' ⟶ pullback g p) (hs' : s' ≫ pullback.snd g p = 𝟙 S')
    (h : pullback.fst p p ≫ s' ≫ pullback.fst g p = pullback.snd p p ≫ s' ≫ pullback.fst g p) :
    descendSection p g s' h ≫ g = 𝟙 S := by
  rw [← cancel_epi p, comp_descendSection_assoc, pullback.condition, reassoc_of% hs',
    Category.comp_id]

/-- **Uniqueness of descended sections.** A morphism `S ⟶ Y` whose pullback to `S'` is the
`S'`-point of `Y` given by `s'` is the descended section. -/
theorem eq_descendSection (s' : S' ⟶ pullback g p)
    (h : pullback.fst p p ≫ s' ≫ pullback.fst g p = pullback.snd p p ≫ s' ≫ pullback.fst g p)
    (s : S ⟶ Y) (hs : p ≫ s = s' ≫ pullback.fst g p) : s = descendSection p g s' h := by
  rw [← cancel_epi p, hs, comp_descendSection]

/-- **Effectiveness of descent of sections.** The base change of the descended section is `s'`. -/
theorem pullbackSection_descendSection (s' : S' ⟶ pullback g p)
    (hs' : s' ≫ pullback.snd g p = 𝟙 S')
    (h : pullback.fst p p ≫ s' ≫ pullback.fst g p = pullback.snd p p ≫ s' ≫ pullback.fst g p) :
    pullbackSection g p (p ≫ descendSection p g s' h)
        (by rw [Category.assoc, descendSection_comp p g s' hs' h, Category.comp_id]) = s' := by
  ext <;> simp [hs']

/-- **Descent of sections.** Base change along an effective epimorphism `p : S' ⟶ S` is a
bijection from the sections of `g : Y ⟶ S` to the sections of `Y ×_S S' ⟶ S'` whose two pullbacks
to `S' ×_S S'` agree. -/
noncomputable def sectionDescentEquiv :
    {s : S ⟶ Y // s ≫ g = 𝟙 S} ≃
      {s' : S' ⟶ pullback g p // s' ≫ pullback.snd g p = 𝟙 S' ∧
        pullback.fst p p ≫ s' ≫ pullback.fst g p = pullback.snd p p ≫ s' ≫ pullback.fst g p} where
  toFun s := ⟨pullbackSection g p (p ≫ s.1) (by rw [Category.assoc, s.2, Category.comp_id]),
    pullbackSection_snd _ _ _ _, by simp [pullback.condition_assoc]⟩
  invFun s' := ⟨descendSection p g s'.1 s'.2.2, descendSection_comp p g _ s'.2.1 _⟩
  left_inv s := Subtype.ext <| Eq.symm <| eq_descendSection p g _
    (by simp [pullback.condition_assoc]) s.1 (pullbackSection_fst _ _ _ _).symm
  right_inv s' := Subtype.ext (pullbackSection_descendSection p g s'.1 s'.2.1 s'.2.2)

/-- `sectionDescentEquiv` sends a section `s` of `g` to its base change. -/
@[simp]
theorem sectionDescentEquiv_apply_coe (s : {s : S ⟶ Y // s ≫ g = 𝟙 S}) :
    (sectionDescentEquiv p g s : S' ⟶ pullback g p) =
      pullbackSection g p (p ≫ s.1) (by rw [Category.assoc, s.2, Category.comp_id]) :=
  (rfl)

/-- The inverse of `sectionDescentEquiv` is descent of sections. -/
@[simp]
theorem sectionDescentEquiv_symm_apply_coe
    (s' : {s' : S' ⟶ pullback g p // s' ≫ pullback.snd g p = 𝟙 S' ∧
      pullback.fst p p ≫ s' ≫ pullback.fst g p = pullback.snd p p ≫ s' ≫ pullback.fst g p}) :
    ((sectionDescentEquiv p g).symm s' : S ⟶ Y) = descendSection p g s'.1 s'.2.2 :=
  (rfl)

end Section

section Hom

variable {X Y : Over S}

variable [EffectiveEpi (pullback.fst X.hom p)]

/-- The morphism `X ⟶ Y` underlying `descendHom`, descended from `φ` along the coequalizer
`X ×_S S' ⟶ X` of `pr₁^*, pr₂^*`. -/
private noncomputable def descendHomLeft
    (φ : (Over.pullback p).obj X ⟶ (Over.pullback p).obj Y)
    (h : pullback.mapSnd X.hom p _ (pullback.fst p p) rfl ≫ φ.left ≫ pullback.fst Y.hom p =
      pullback.mapSnd X.hom p _ (pullback.snd p p) pullback.condition.symm ≫ φ.left ≫
        pullback.fst Y.hom p) :
    X.left ⟶ Y.left :=
  Cofork.IsColimit.desc ((EffectiveEpi.getStruct _).isColimitCoforkOfIsPullback
    (pullback.isKernelPair_mapSnd X.hom p)) (φ.left ≫ pullback.fst Y.hom p) h

@[reassoc]
private theorem fst_comp_descendHomLeft
    (φ : (Over.pullback p).obj X ⟶ (Over.pullback p).obj Y)
    (h : pullback.mapSnd X.hom p _ (pullback.fst p p) rfl ≫ φ.left ≫ pullback.fst Y.hom p =
      pullback.mapSnd X.hom p _ (pullback.snd p p) pullback.condition.symm ≫ φ.left ≫
        pullback.fst Y.hom p) :
    pullback.fst X.hom p ≫ descendHomLeft p φ h = φ.left ≫ pullback.fst Y.hom p := by
  simpa [descendHomLeft, Cofork.π_ofπ] using
    Cofork.IsColimit.π_desc' ((EffectiveEpi.getStruct _).isColimitCoforkOfIsPullback
      (pullback.isKernelPair_mapSnd X.hom p)) _ h

/-- **Descent of a morphism.** A morphism `φ : X ×_S S' ⟶ Y ×_S S'` over `S'`, whose two pullbacks
to `S' ×_S S'` agree, descends to a morphism `X ⟶ Y` over `S`, provided that the base change
`X ×_S S' ⟶ X` of `p` is an effective epimorphism. Its base change is `φ`
(`pullback_map_descendHom`). -/
noncomputable def descendHom (φ : (Over.pullback p).obj X ⟶ (Over.pullback p).obj Y)
    (h : pullback.mapSnd X.hom p _ (pullback.fst p p) rfl ≫ φ.left ≫ pullback.fst Y.hom p =
      pullback.mapSnd X.hom p _ (pullback.snd p p) pullback.condition.symm ≫ φ.left ≫
        pullback.fst Y.hom p) :
    X ⟶ Y :=
  Over.homMk (descendHomLeft p φ h) <| by
    rw [← cancel_epi (pullback.fst X.hom p), fst_comp_descendHomLeft_assoc, pullback.condition]
    simpa using (Over.w φ =≫ p).trans pullback.condition.symm

/-- The descended morphism, composed with the projection `X ×_S S' ⟶ X`, is `φ` followed by
the projection `Y ×_S S' ⟶ Y`. -/
@[reassoc (attr := simp)]
theorem fst_comp_descendHom_left (φ : (Over.pullback p).obj X ⟶ (Over.pullback p).obj Y)
    (h : pullback.mapSnd X.hom p _ (pullback.fst p p) rfl ≫ φ.left ≫ pullback.fst Y.hom p =
      pullback.mapSnd X.hom p _ (pullback.snd p p) pullback.condition.symm ≫ φ.left ≫
        pullback.fst Y.hom p) :
    pullback.fst X.hom p ≫ (descendHom p φ h).left = φ.left ≫ pullback.fst Y.hom p := by
  simp only [descendHom, Over.homMk_left, fst_comp_descendHomLeft]

/-- **Uniqueness of descended morphisms.** A morphism `X ⟶ Y` over `S` whose composite with the
projection `X ×_S S' ⟶ X` is `φ` followed by the projection `Y ×_S S' ⟶ Y` is the descended
morphism. -/
theorem eq_descendHom (φ : (Over.pullback p).obj X ⟶ (Over.pullback p).obj Y)
    (h : pullback.mapSnd X.hom p _ (pullback.fst p p) rfl ≫ φ.left ≫ pullback.fst Y.hom p =
      pullback.mapSnd X.hom p _ (pullback.snd p p) pullback.condition.symm ≫ φ.left ≫
        pullback.fst Y.hom p)
    (u : X ⟶ Y) (hu : pullback.fst X.hom p ≫ u.left = φ.left ≫ pullback.fst Y.hom p) :
    u = descendHom p φ h := by
  ext
  rw [← cancel_epi (pullback.fst X.hom p), hu, fst_comp_descendHom_left]

/-- **Effectiveness of descent of morphisms.** The base change of the descended morphism is
`φ`. -/
@[simp]
theorem pullback_map_descendHom (φ : (Over.pullback p).obj X ⟶ (Over.pullback p).obj Y)
    (h : pullback.mapSnd X.hom p _ (pullback.fst p p) rfl ≫ φ.left ≫ pullback.fst Y.hom p =
      pullback.mapSnd X.hom p _ (pullback.snd p p) pullback.condition.symm ≫ φ.left ≫
        pullback.fst Y.hom p) :
    (Over.pullback p).map (descendHom p φ h) = φ := by
  ext1
  refine pullback.hom_ext ?_ ?_
  · simp
  · simpa using (Over.w φ).symm

/-- **Descent of morphisms.** If the base change `X ×_S S' ⟶ X` of `p : S' ⟶ S` is an effective
epimorphism, then base change along `p` is a bijection from the morphisms `X ⟶ Y` over `S` to the
morphisms `X ×_S S' ⟶ Y ×_S S'` over `S'` whose two pullbacks to `S' ×_S S'` agree. -/
noncomputable def homDescentEquiv :
    (X ⟶ Y) ≃ {φ : (Over.pullback p).obj X ⟶ (Over.pullback p).obj Y //
      pullback.mapSnd X.hom p _ (pullback.fst p p) rfl ≫ φ.left ≫ pullback.fst Y.hom p =
        pullback.mapSnd X.hom p _ (pullback.snd p p) pullback.condition.symm ≫ φ.left ≫
          pullback.fst Y.hom p} where
  toFun u := ⟨(Over.pullback p).map u, by simp⟩
  invFun φ := descendHom p φ.1 φ.2
  left_inv u := (eq_descendHom p _ _ u (by simp)).symm
  right_inv φ := Subtype.ext (pullback_map_descendHom p φ.1 φ.2)

/-- `homDescentEquiv` sends a morphism over `S` to its base change. -/
@[simp]
theorem homDescentEquiv_apply_coe (u : X ⟶ Y) :
    (homDescentEquiv p u : (Over.pullback p).obj X ⟶ (Over.pullback p).obj Y) =
      (Over.pullback p).map u :=
  (rfl)

/-- The inverse of `homDescentEquiv` is descent of morphisms. -/
@[simp]
theorem homDescentEquiv_symm_apply
    (φ : {φ : (Over.pullback p).obj X ⟶ (Over.pullback p).obj Y //
      pullback.mapSnd X.hom p _ (pullback.fst p p) rfl ≫ φ.left ≫ pullback.fst Y.hom p =
        pullback.mapSnd X.hom p _ (pullback.snd p p) pullback.condition.symm ≫ φ.left ≫
          pullback.fst Y.hom p}) :
    (homDescentEquiv p).symm φ = descendHom p φ.1 φ.2 :=
  (rfl)

end Hom

namespace DescentDatum

variable {X Y : Over S}

/-- The morphism `X ×_S (S' ×_S S') ⟶ S' ×_S (X ×_S S')`, `(x, (s₁, s₂)) ↦ (s₂, (x, s₁))`.
Followed by the second projection it is `pr₁^*`, and followed by the canonical action it is
`pr₂^*`. -/
private noncomputable def swap (X : Over S) :
    pullback X.hom (pullback.fst p p ≫ p) ⟶
      pullback p (((Over.pullback p).obj X).hom ≫ p) :=
  pullback.lift (pullback.snd _ _ ≫ pullback.snd p p)
    (pullback.mapSnd X.hom p _ (pullback.fst p p) rfl) <| by
      simp [← pullback.condition]

@[reassoc]
private theorem swap_snd (X : Over S) :
    swap p X ≫ pullback.snd _ _ = pullback.mapSnd X.hom p _ (pullback.fst p p) rfl :=
  pullback.lift_snd _ _ _

@[reassoc]
private theorem swap_act (X : Over S) :
    swap p X ≫ (baseChange p X).act =
      pullback.mapSnd X.hom p _ (pullback.snd p p) pullback.condition.symm := by
  refine pullback.hom_ext ?_ ?_ <;> simp [swap]

/-- The underlying morphism of a morphism of canonical descent data satisfies the descent
condition of `homDescentEquiv`: its two pullbacks to `S' ×_S S'` agree. -/
private theorem Hom.mapSnd_comp_hom_left_comp_fst
    (φ : Hom (baseChange p X) (baseChange p Y)) :
    pullback.mapSnd X.hom p _ (pullback.fst p p) rfl ≫ φ.hom.left ≫ pullback.fst Y.hom p =
      pullback.mapSnd X.hom p _ (pullback.snd p p) pullback.condition.symm ≫ φ.hom.left ≫
        pullback.fst Y.hom p := by
  have h := φ.map_act =≫ pullback.fst Y.hom p
  simp only [Category.assoc, baseChange_act_fst, pullback.lift_snd_assoc] at h
  rw [← swap_snd_assoc, ← swap_act_assoc, ← h]

variable {p} [EffectiveEpi (pullback.fst X.hom p)]

/-- **Descent of morphisms of canonical descent data.** A morphism
`baseChange p X ⟶ baseChange p Y` of descent data descends to a morphism `X ⟶ Y` over `S`,
provided that the base change `X ×_S S' ⟶ X` of `p` is an effective epimorphism. Its base change
is `φ` (`baseChangeHom_descend`). -/
noncomputable def Hom.descend (φ : Hom (baseChange p X) (baseChange p Y)) : X ⟶ Y :=
  descendHom p φ.hom (mapSnd_comp_hom_left_comp_fst p φ)

/-- The descended morphism, composed with the projection `X ×_S S' ⟶ X`, is `φ` followed by the
projection `Y ×_S S' ⟶ Y`. -/
@[reassoc (attr := simp)]
theorem Hom.fst_comp_descend_left (φ : Hom (baseChange p X) (baseChange p Y)) :
    pullback.fst X.hom p ≫ φ.descend.left = φ.hom.left ≫ pullback.fst Y.hom p :=
  fst_comp_descendHom_left p _ _

/-- **Effectiveness.** The base change of the descended morphism is `φ`. -/
@[simp]
theorem baseChangeHom_descend (φ : Hom (baseChange p X) (baseChange p Y)) :
    baseChangeHom p φ.descend = φ :=
  Hom.ext <| by rw [baseChangeHom_hom]; exact pullback_map_descendHom p _ _

variable (p) in
/-- **Uniqueness.** Descending the base change of a morphism `u : X ⟶ Y` over `S` recovers
`u`. -/
@[simp]
theorem Hom.descend_baseChangeHom (u : X ⟶ Y) : (baseChangeHom p u).descend = u :=
  (eq_descendHom p _ _ u (by simp)).symm

variable (p X Y) in
/-- **Full faithfulness of base change into descent data.** If the base change `X ×_S S' ⟶ X`
of `p : S' ⟶ S` is an effective epimorphism, then base change along `p` is a bijection from the
morphisms `X ⟶ Y` over `S` to the morphisms of canonical descent data
`baseChange p X ⟶ baseChange p Y`. -/
noncomputable def baseChangeHomEquiv : (X ⟶ Y) ≃ Hom (baseChange p X) (baseChange p Y) where
  toFun := baseChangeHom p
  invFun φ := φ.descend
  left_inv := Hom.descend_baseChangeHom p
  right_inv := baseChangeHom_descend

variable (p) in
/-- `baseChangeHomEquiv` sends a morphism over `S` to its base change. -/
@[simp]
theorem baseChangeHomEquiv_apply (u : X ⟶ Y) : baseChangeHomEquiv p X Y u = baseChangeHom p u :=
  (rfl)

/-- The inverse of `baseChangeHomEquiv` is descent of morphisms of canonical descent data. -/
@[simp]
theorem baseChangeHomEquiv_symm_apply (φ : Hom (baseChange p X) (baseChange p Y)) :
    (baseChangeHomEquiv p X Y).symm φ = φ.descend :=
  (rfl)

section Iso

variable [EffectiveEpi (pullback.fst Y.hom p)] {W : Over S'} {D : DescentDatum p W}
  (f : Hom (baseChange p X) D) (g : Hom (baseChange p Y) D) [IsIso f.hom] [IsIso g.hom]

/-- **Uniqueness of effective descent.** Two objects `X` and `Y` over `S` whose canonical
descent data are both isomorphic to the same descent datum `D`, through `f` and `g`, are
isomorphic over `S`; the isomorphism is compatible with `f` and `g`
(`Hom.comp_baseChangeHom_descendIso`), and it is the only such isomorphism
(`Hom.eq_descendIso`). -/
noncomputable def Hom.descendIso : X ≅ Y where
  hom := (g.inv.comp f).descend
  inv := (f.inv.comp g).descend
  hom_inv_id := (baseChangeHomEquiv p X X).injective <| by
    simp [Hom.comp_assoc, ← Hom.comp_assoc g]
  inv_hom_id := (baseChangeHomEquiv p Y Y).injective <| by
    simp [Hom.comp_assoc, ← Hom.comp_assoc f]

/-- The forward map of `Hom.descendIso f g` descends `g⁻¹ ∘ f`. -/
@[simp]
theorem Hom.descendIso_hom : (f.descendIso g).hom = (g.inv.comp f).descend :=
  (rfl)

/-- The inverse map of `Hom.descendIso f g` descends `f⁻¹ ∘ g`. -/
@[simp]
theorem Hom.descendIso_inv : (f.descendIso g).inv = (f.inv.comp g).descend :=
  (rfl)

/-- The isomorphism `Hom.descendIso f g : X ≅ Y` carries `f` to `g`. -/
theorem Hom.comp_baseChangeHom_descendIso :
    g.comp (baseChangeHom p (f.descendIso g).hom) = f := by
  simp [← Hom.comp_assoc]

/-- `Hom.descendIso f g` is the only isomorphism `X ≅ Y` carrying `f` to `g`. -/
theorem Hom.eq_descendIso (e : X ≅ Y) (he : g.comp (baseChangeHom p e.hom) = f) :
    e = f.descendIso g := by
  ext1
  rw [descendIso_hom, ← he, ← Hom.comp_assoc, inv_comp_self, Hom.id_comp, descend_baseChangeHom]

end Iso

end DescentDatum

end TauCeti
