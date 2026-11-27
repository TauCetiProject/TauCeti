/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.Embedding.RestrictionHomology
public import Mathlib.Algebra.Homology.HomologySequence
public import Mathlib.Algebra.Category.ModuleCat.Abelian
import TauCeti.Algebra.Homology.ModuleCat.Basic

/-!
# The homology sequence of a restricted short exact sequence

Let `e : c.Embedding c'` be an embedding of complex shapes and `S` a short exact sequence of
complexes of shape `c'`. Restricting `S` along `e` gives a short exact sequence of complexes of
shape `c` (`CategoryTheory.ShortComplex.ShortExact.restriction`), since in each degree it is the
short complex of `S` in the corresponding degree. Mathlib identifies the homology of a restricted
complex in degree `j` with the homology of the original complex in degree `e.f j`
(`HomologicalComplex.restrictionHomologyIso`). For complexes of modules, this file shows that the
connecting maps of the two homology sequences correspond under these identifications
(`CategoryTheory.ShortComplex.ShortExact.moduleCat_restrictionHomologyIso_inv_δ_hom`).

This is what allows a connecting map computed on a complex reindexed along an embedding, such as
a chain complex regraded as a cochain complex along `n ↦ -n`, to be compared with the connecting
map of the original complex. It is the restriction counterpart of
`CategoryTheory.ShortComplex.ShortExact.extend_δ_comp_extendHomologyIso_hom`.

## Main results

* `CategoryTheory.ShortComplex.ShortExact.restriction`: restricting a short exact sequence of
  complexes along an embedding of complex shapes gives a short exact sequence.
* `CategoryTheory.ShortComplex.ShortExact.moduleCat_restrictionHomologyIso_inv_δ_hom`: for
  complexes of modules, the connecting maps of a short exact sequence and of its restriction
  correspond under `HomologicalComplex.restrictionHomologyIso`.
-/

public section

open CategoryTheory Limits HomologicalComplex

namespace CategoryTheory.ShortComplex.ShortExact

variable {ι ι' : Type*} {c : ComplexShape ι} {c' : ComplexShape ι'}

/-- Restricting a short exact sequence of complexes along an embedding of complex shapes gives a
short exact sequence: in each degree it is the short complex of the original sequence in the
corresponding degree. -/
lemma restriction {C : Type*} [Category* C] [Abelian C] {S : ShortComplex (HomologicalComplex C c')}
    (hS : S.ShortExact) (e : c.Embedding c') [e.IsRelIff] :
    (S.map (e.restrictionFunctor C)).ShortExact :=
  shortExact_of_degreewise_shortExact _ fun i ↦
    (shortExact_iff_degreewise_shortExact S).1 hS (e.f i)

variable {R : Type*} [Ring R] {S : ShortComplex (HomologicalComplex (ModuleCat R) c')}
  (hS : S.ShortExact) (e : c.Embedding c') [e.IsRelIff]

/-- **The connecting maps of a restricted short exact sequence of complexes of modules.** Under
the identifications `HomologicalComplex.restrictionHomologyIso` of the homology of the restricted
complexes with the homology of the original ones, the connecting map of the restriction of `S`
along `e` in degrees `i ⟶ j` is the connecting map of `S` in degrees `e.f i ⟶ e.f j`. The
neighbouring indices of `i` and `j` used by the identifications are given by equations, for
flexibility. -/
theorem moduleCat_restrictionHomologyIso_inv_δ_hom (i₀ i j₃ i₁ j k : ι) (hij : c.Rel i j)
    (h₀ : c.prev i = i₀) (h₃ : c.next i = j₃) (h₁ : c.prev j = i₁) (hk : c.next j = k)
    {i₀' i' j₃' i₁' j' k' : ι'} (h₀' : e.f i₀ = i₀') (hi' : e.f i = i') (h₃' : e.f j₃ = j₃')
    (h₁' : e.f i₁ = i₁') (hj' : e.f j = j') (hk' : e.f k = k') (h₀'' : c'.prev i' = i₀')
    (h₃'' : c'.next i' = j₃') (h₁'' : c'.prev j' = i₁') (hk'' : c'.next j' = k')
    (hij' : c'.Rel i' j') :
    (S.X₃.restrictionHomologyIso e i₀ i j₃ h₀ h₃ h₀' hi' h₃' h₀'' h₃'').inv ≫
        (hS.restriction e).δ i j hij ≫
          (S.X₁.restrictionHomologyIso e i₁ j k h₁ hk h₁' hj' hk' h₁'' hk'').hom =
      hS.δ i' j' hij' := by
  have hj₃ : j = j₃ := (c.next_eq' hij).symm.trans h₃
  have hi₁ : i = i₁ := (c.prev_eq' hij).symm.trans h₁
  subst hj₃ hi₁
  subst h₀' hi' h₃' hj' h₁' hk'
  ext x
  -- Represent `x` by a cycle `z₃`, lift it to `x₂`, and read off the cycle `z₁` of `S.X₁` whose
  -- class is the connecting map of `x`.
  obtain ⟨z₁, hz₁⟩ := S.X₁.moduleCat_homologyπ_surjective _ ((hS.δ _ _ hij').hom x)
  obtain ⟨x₂, z₃, hx₂, hgx₂, rfl⟩ :=
    hS.moduleCat_exists_d_eq_of_δ_eq _ _ hij' x z₁ hz₁.symm
  rw [← hz₁]
  -- The cycles `z₃` and `z₁` seen as cycles of the restricted complexes keep their underlying
  -- elements, and their classes correspond under `restrictionHomologyIso`.
  have hc₃ (w : S.X₃.cycles (e.f i)) : ((S.X₃.restriction e).iCycles i).hom
      ((S.X₃.restrictionCyclesIso e i j h₃ rfl rfl h₃'').inv.hom w) = (S.X₃.iCycles _).hom w := by
    rw [← LinearMap.comp_apply, ← ModuleCat.hom_comp,
      S.X₃.restrictionCyclesIso_inv_iCycles e i j h₃ rfl rfl h₃'']
    simp [restrictionXIso]
  have hc₁ (w : S.X₁.cycles (e.f j)) : ((S.X₁.restriction e).iCycles j).hom
      ((S.X₁.restrictionCyclesIso e j k hk rfl rfl hk'').inv.hom w) = (S.X₁.iCycles _).hom w := by
    rw [← LinearMap.comp_apply, ← ModuleCat.hom_comp,
      S.X₁.restrictionCyclesIso_inv_iCycles e j k hk rfl rfl hk'']
    simp [restrictionXIso]
  have hπ₃ (w : S.X₃.cycles (e.f i)) :
      (S.X₃.restrictionHomologyIso e i₀ i j h₀ h₃ rfl rfl rfl h₀'' h₃'').inv.hom
          ((S.X₃.homologyπ _).hom w) =
        ((S.X₃.restriction e).homologyπ i).hom
          ((S.X₃.restrictionCyclesIso e i j h₃ rfl rfl h₃'').inv.hom w) :=
    congrArg (fun φ ↦ φ.hom w) (S.X₃.homologyπ_restrictionHomologyIso_inv e i₀ i j h₀ h₃ rfl rfl
      rfl h₀'' h₃'')
  have hπ₁ (w : (S.X₁.restriction e).cycles j) :
      (S.X₁.restrictionHomologyIso e i j k h₁ hk rfl rfl rfl h₁'' hk'').hom.hom
          (((S.X₁.restriction e).homologyπ j).hom w) =
        (S.X₁.homologyπ _).hom ((S.X₁.restrictionCyclesIso e j k hk rfl rfl hk'').hom.hom w) :=
    congrArg (fun φ ↦ φ.hom w) (S.X₁.homologyπ_restrictionHomologyIso_hom e i j k h₁ hk rfl rfl
      rfl h₁'' hk'')
  -- The connecting map of the restricted sequence, computed from the same lift `x₂`.
  have key : ((hS.restriction e).δ i j hij).hom (((S.X₃.restriction e).homologyπ i).hom
      ((S.X₃.restrictionCyclesIso e i j h₃ rfl rfl h₃'').inv.hom z₃)) =
        ((S.X₁.restriction e).homologyπ j).hom
          ((S.X₁.restrictionCyclesIso e j k hk rfl rfl hk'').inv.hom z₁) :=
    (hS.restriction e).moduleCat_δ_homologyπ i j hij _ x₂ (hgx₂.trans (hc₃ z₃).symm) _
      ((hc₁ z₁).symm ▸ hx₂.symm)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply]
  rw [hπ₃, key, hπ₁]
  exact congrArg (S.X₁.homologyπ _).hom
    (congrArg (fun φ ↦ φ.hom z₁) (S.X₁.restrictionCyclesIso e j k hk rfl rfl hk'').inv_hom_id)

end CategoryTheory.ShortComplex.ShortExact
