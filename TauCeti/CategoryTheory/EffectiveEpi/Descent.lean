/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Comma.Over.Pullback
public import Mathlib.CategoryTheory.Limits.Shapes.KernelPair
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

end TauCeti
