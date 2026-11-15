/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Homotopy.Equiv
public import TauCeti.Topology.Maps.Proper.Basic

/-!
# Proper homotopies and proper homotopy equivalences

A homotopy `F : Homotopy f₀ f₁` is *proper* when its underlying map `I × X → Y` is proper; its two
endpoints are then proper as well, and properness is preserved by reversing, concatenating and
composing homotopies.

A continuous map `f : X → Y` is a *proper homotopy equivalence*
(`ContinuousMap.HasProperHomotopyInverse`) if it is proper and has a proper homotopy inverse
`g : Y → X` for which both homotopies `g ∘ f ≃ id` and `f ∘ g ≃ id` are proper as maps
`I × X → X` and `I × Y → Y`. These are the equivalences of the proper homotopy category, in which
invariants at infinity such as simple connectivity at infinity live.

Proper homotopy equivalences contain identities and homeomorphisms, admit proper homotopy inverses
that are themselves proper homotopy equivalences, are closed under composition and under proper
homotopy, and satisfy two-out-of-three among proper maps. Forgetting properness recovers an
ordinary homotopy equivalence (`ContinuousMap.HasProperHomotopyInverse.exists_homotopyEquiv`).

## Main declarations

* `ContinuousMap.Homotopy.isProperMap_left`, `ContinuousMap.Homotopy.isProperMap_right`: the
  endpoints of a proper homotopy are proper.
* `ContinuousMap.Homotopy.isProperMap_refl_iff`, `ContinuousMap.Homotopy.isProperMap_symm_iff`,
  `ContinuousMap.Homotopy.isProperMap_trans`, `ContinuousMap.Homotopy.isProperMap_comp`,
  `ContinuousMap.Homotopy.isProperMap_compContinuousMap`: properness of constant, reversed,
  concatenated and composed homotopies.
* `ContinuousMap.HasProperHomotopyInverse`: the predicate that a continuous map is a proper
  homotopy equivalence.
* `ContinuousMap.HasProperHomotopyInverse.id`, `ContinuousMap.HasProperHomotopyInverse.comp`,
  `ContinuousMap.HasProperHomotopyInverse.exists_hasProperHomotopyInverse`,
  `ContinuousMap.HasProperHomotopyInverse.of_homotopy`,
  `ContinuousMap.HasProperHomotopyInverse.of_postcomp`,
  `ContinuousMap.HasProperHomotopyInverse.of_precomp`: closure under identity, composition,
  inversion, proper homotopy and two-out-of-three.

## References

* F. T. Farrell, L. R. Taylor, J. B. Wagoner, *The Whitehead theorem in the proper category*,
  Compositio Math. 27 (1973), 1–23.
-/

public section

open scoped unitInterval

namespace ContinuousMap

section Homotopy

variable {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]

namespace Homotopy

/-- The initial map of a proper homotopy is proper. -/
theorem isProperMap_left {f₀ f₁ : C(X, Y)} {F : Homotopy f₀ f₁} (hF : IsProperMap F) :
    IsProperMap f₀ := by
  convert hF.comp (isProperMap_prodMk_left (0 : I)) using 1
  ext x
  exact (F.apply_zero x).symm

/-- The final map of a proper homotopy is proper. -/
theorem isProperMap_right {f₀ f₁ : C(X, Y)} {F : Homotopy f₀ f₁} (hF : IsProperMap F) :
    IsProperMap f₁ := by
  convert hF.comp (isProperMap_prodMk_left (1 : I)) using 1
  ext x
  exact (F.apply_one x).symm

/-- The constant homotopy on `f` is proper if and only if `f` is proper. -/
@[simp]
theorem isProperMap_refl_iff {f : C(X, Y)} : IsProperMap (Homotopy.refl f) ↔ IsProperMap f :=
  ⟨isProperMap_left, fun hf ↦ hf.comp (isProperMap_snd_of_compactSpace (X := I))⟩

/-- The constant homotopy on a proper map is proper. -/
theorem isProperMap_refl {f : C(X, Y)} (hf : IsProperMap f) : IsProperMap (Homotopy.refl f) :=
  isProperMap_refl_iff.2 hf

/-- Reversing a proper homotopy yields a proper homotopy. -/
theorem isProperMap_symm {f₀ f₁ : C(X, Y)} {F : Homotopy f₀ f₁} (hF : IsProperMap F) :
    IsProperMap F.symm :=
  hF.comp ((isProperMap_snd_of_compactSpace (X := I)).prodMk_of_t2_left
    (unitInterval.continuous_symm.comp continuous_fst))

/-- A reversed homotopy is proper if and only if the original homotopy is proper. -/
@[simp]
theorem isProperMap_symm_iff {f₀ f₁ : C(X, Y)} {F : Homotopy f₀ f₁} :
    IsProperMap F.symm ↔ IsProperMap F :=
  ⟨fun h ↦ by simpa only [symm_symm] using isProperMap_symm h, isProperMap_symm⟩

/-- Casting the endpoints of a homotopy preserves properness. -/
@[simp]
theorem isProperMap_cast_iff {f₀ f₁ g₀ g₁ : C(X, Y)} {F : Homotopy f₀ f₁} (h₀ : f₀ = g₀)
    (h₁ : f₁ = g₁) : IsProperMap (F.cast h₀ h₁) ↔ IsProperMap F := by
  subst h₀ h₁
  rfl

/-- Concatenating two proper homotopies yields a proper homotopy. -/
theorem isProperMap_trans {f₀ f₁ f₂ : C(X, Y)} {F : Homotopy f₀ f₁} {G : Homotopy f₁ f₂}
    (hF : IsProperMap F) (hG : IsProperMap G) : IsProperMap (F.trans G) := by
  -- Cover `I × X` by its closed lower and upper halves `[0, 1/2] × X` and `[1/2, 1] × X`.
  let s : Set (I × X) := {p | (p.1 : ℝ) ≤ 1 / 2}
  let t : Set (I × X) := {p | 1 / 2 ≤ (p.1 : ℝ)}
  have hs : IsClosed s := isClosed_le (continuous_subtype_val.comp continuous_fst) continuous_const
  have ht : IsClosed t := isClosed_le continuous_const (continuous_subtype_val.comp continuous_fst)
  have hcov : s ∪ t = Set.univ := Set.eq_univ_of_forall fun p ↦ le_total (p.1 : ℝ) (1 / 2)
  refine IsProperMap.of_union_isClosed hs ht hcov ?_ ?_
  · convert (hF.comp ((isProperMap_snd_of_compactSpace (X := I)).prodMk_of_t2_left
      (f := fun p : I × X ↦ Set.projIcc 0 1 zero_le_one (2 * (p.1 : ℝ))) (by fun_prop))).restrict
      hs using 1
    ext ⟨⟨u, x⟩, hu⟩
    have hu' : (u : ℝ) ≤ 1 / 2 := hu
    rw [trans_apply, dite_eq_left hu']
    congr 2
    exact (Set.projIcc_of_mem _ ⟨by linarith [u.2.1], by linarith⟩).symm
  · convert (hG.comp ((isProperMap_snd_of_compactSpace (X := I)).prodMk_of_t2_left
      (f := fun p : I × X ↦ Set.projIcc 0 1 zero_le_one (2 * (p.1 : ℝ) - 1))
      (by fun_prop))).restrict ht using 1
    ext ⟨⟨u, x⟩, hu⟩
    have hu' : 1 / 2 ≤ (u : ℝ) := hu
    rw [trans_apply]
    split_ifs with h
    · have heq : (u : ℝ) = 1 / 2 := le_antisymm h hu'
      have h₁ : (⟨2 * (u : ℝ), (unitInterval.mul_pos_mem_iff zero_lt_two).2 ⟨u.2.1, h⟩⟩ : I) = 1 :=
        Subtype.ext (by norm_num [heq])
      have h₀ : Set.projIcc 0 1 zero_le_one (2 * (u : ℝ) - 1) = 0 :=
        Subtype.ext (by norm_num [heq])
      rw [h₁, F.apply_one]
      simpa only [Function.comp_apply, h₀] using (G.apply_zero x).symm
    · congr 2
      exact (Set.projIcc_of_mem _ ⟨by linarith, by linarith [u.2.2]⟩).symm

/-- Horizontal composition of proper homotopies is proper. -/
theorem isProperMap_comp {f₀ f₁ : C(X, Y)} {g₀ g₁ : C(Y, Z)} {G : Homotopy g₀ g₁}
    {F : Homotopy f₀ f₁} (hG : IsProperMap G) (hF : IsProperMap F) : IsProperMap (G.comp F) :=
  hG.comp (hF.prodMk_of_t2_left continuous_fst)

/-- Whiskering a proper homotopy on the right by a proper map yields a proper homotopy. -/
theorem isProperMap_compContinuousMap {g₀ g₁ : C(Y, Z)} {G : Homotopy g₀ g₁} {f : C(X, Y)}
    (hG : IsProperMap G) (hf : IsProperMap f) : IsProperMap (G.compContinuousMap f) :=
  isProperMap_comp hG (isProperMap_refl hf)

end Homotopy

end Homotopy

variable {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]

/-- A continuous map `f : X → Y` is a **proper homotopy equivalence** if it is proper and has a
proper homotopy inverse `g`, with both homotopies `g ∘ f ≃ id` and `f ∘ g ≃ id` proper as maps
`I × X → X` and `I × Y → Y`. -/
def HasProperHomotopyInverse (f : C(X, Y)) : Prop :=
  IsProperMap f ∧ ∃ g : C(Y, X), IsProperMap g ∧
    ∃ H : Homotopy (g.comp f) (ContinuousMap.id X), ∃ H' : Homotopy (f.comp g) (ContinuousMap.id Y),
      IsProperMap H ∧ IsProperMap H'

namespace HasProperHomotopyInverse

/-- A proper map with a proper inverse `g` up to proper homotopies `g ∘ f ≃ id` and
`f ∘ g ≃ id` is a proper homotopy equivalence. -/
theorem intro {f : C(X, Y)} (hf : IsProperMap f) (g : C(Y, X)) (hg : IsProperMap g)
    (H : Homotopy (g.comp f) (ContinuousMap.id X)) (H' : Homotopy (f.comp g) (ContinuousMap.id Y))
    (hH : IsProperMap H) (hH' : IsProperMap H') : f.HasProperHomotopyInverse :=
  ⟨hf, g, hg, H, H', hH, hH'⟩

/-- A proper homotopy equivalence is a proper map. -/
theorem isProperMap {f : C(X, Y)} (hf : f.HasProperHomotopyInverse) : IsProperMap f :=
  hf.1

/-- A proper homotopy equivalence has a proper homotopy inverse `g`, with proper homotopies
`g ∘ f ≃ id` and `f ∘ g ≃ id`. -/
theorem exists_inverse {f : C(X, Y)} (hf : f.HasProperHomotopyInverse) :
    ∃ g : C(Y, X), IsProperMap g ∧
      ∃ H : Homotopy (g.comp f) (ContinuousMap.id X),
        ∃ H' : Homotopy (f.comp g) (ContinuousMap.id Y), IsProperMap H ∧ IsProperMap H' :=
  hf.2

/-- A proper homotopy equivalence admits a proper homotopy inverse that is itself a proper
homotopy equivalence. -/
theorem exists_hasProperHomotopyInverse {f : C(X, Y)} (hf : f.HasProperHomotopyInverse) :
    ∃ g : C(Y, X), g.HasProperHomotopyInverse ∧
      ∃ H : Homotopy (g.comp f) (ContinuousMap.id X),
        ∃ H' : Homotopy (f.comp g) (ContinuousMap.id Y), IsProperMap H ∧ IsProperMap H' := by
  obtain ⟨g, hg, H, H', hH, hH'⟩ := hf.exists_inverse
  exact ⟨g, .intro hg f hf.isProperMap H' H hH' hH, H, H', hH, hH'⟩

/-- A proper homotopy equivalence `f` is a homotopy equivalence: forgetting properness gives a
homotopy equivalence whose forward map is `f`. -/
theorem exists_homotopyEquiv {f : C(X, Y)} (hf : f.HasProperHomotopyInverse) :
    ∃ e : X ≃ₕ Y, (e : X → Y) = f := by
  obtain ⟨g, -, H, H', -, -⟩ := hf.exists_inverse
  exact ⟨⟨f, g, ⟨H⟩, ⟨H'⟩⟩, rfl⟩

/-- The identity map of any space is a proper homotopy equivalence. -/
protected theorem id : (ContinuousMap.id X).HasProperHomotopyInverse :=
  .intro isProperMap_id (.id X) isProperMap_id (.refl _) (.refl _)
    (Homotopy.isProperMap_refl isProperMap_id) (Homotopy.isProperMap_refl isProperMap_id)

/-- **Proper homotopy invariance.** A map properly homotopic to a proper homotopy equivalence is
itself a proper homotopy equivalence, with the same proper homotopy inverse. -/
theorem of_homotopy {f₀ f₁ : C(X, Y)} (hf : f₀.HasProperHomotopyInverse) (F : Homotopy f₀ f₁)
    (hF : IsProperMap F) : f₁.HasProperHomotopyInverse := by
  obtain ⟨g, hg, H, H', hH, hH'⟩ := hf.exists_inverse
  refine .intro (Homotopy.isProperMap_right hF) g hg
    (((Homotopy.refl g).comp F.symm).trans H) ((F.symm.compContinuousMap g).trans H')
    (Homotopy.isProperMap_trans (Homotopy.isProperMap_comp
      (Homotopy.isProperMap_refl hg) (Homotopy.isProperMap_symm hF)) hH)
    (Homotopy.isProperMap_trans
      (Homotopy.isProperMap_compContinuousMap (Homotopy.isProperMap_symm hF) hg) hH')

/-- **Composition of proper homotopy equivalences.** If `f : X → Y` and `g : Y → Z` are proper
homotopy equivalences, then so is `g ∘ f`. -/
theorem comp {f : C(X, Y)} {g : C(Y, Z)} (hg : g.HasProperHomotopyInverse)
    (hf : f.HasProperHomotopyInverse) : (g.comp f).HasProperHomotopyInverse := by
  obtain ⟨f', hf', Hf, Hf', hHf, hHf'⟩ := hf.exists_inverse
  obtain ⟨g', hg', Hg, Hg', hHg, hHg'⟩ := hg.exists_inverse
  refine .intro (hg.isProperMap.comp hf.isProperMap) (f'.comp g') (hf'.comp hg')
    ((((Homotopy.refl f').comp (Hg.compContinuousMap f)).cast rfl rfl).trans Hf)
    ((((Homotopy.refl g).comp (Hf'.compContinuousMap g')).cast rfl rfl).trans Hg') ?_ ?_
  · exact Homotopy.isProperMap_trans ((Homotopy.isProperMap_cast_iff _ _).2
      (Homotopy.isProperMap_comp (Homotopy.isProperMap_refl hf')
        (Homotopy.isProperMap_compContinuousMap hHg hf.isProperMap))) hHf
  · exact Homotopy.isProperMap_trans ((Homotopy.isProperMap_cast_iff _ _).2
      (Homotopy.isProperMap_comp (Homotopy.isProperMap_refl hg.isProperMap)
        (Homotopy.isProperMap_compContinuousMap hHf' hg'))) hHg'

/-- **Two out of three, left cancellation.** If `f : X → Y` is proper and both `g` and `g ∘ f` are
proper homotopy equivalences, then `f` is a proper homotopy equivalence. -/
theorem of_postcomp {f : C(X, Y)} {g : C(Y, Z)} (hf : IsProperMap f)
    (hg : g.HasProperHomotopyInverse) (hgf : (g.comp f).HasProperHomotopyInverse) :
    f.HasProperHomotopyInverse := by
  obtain ⟨g', hg', Hg, -, hHg, -⟩ := hg.exists_hasProperHomotopyInverse
  exact (hg'.comp hgf).of_homotopy ((Hg.compContinuousMap f).cast rfl (id_comp f))
    ((Homotopy.isProperMap_cast_iff _ _).2 (Homotopy.isProperMap_compContinuousMap hHg hf))

/-- **Two out of three, right cancellation.** If `g : Y → Z` is proper and both `f` and `g ∘ f`
are proper homotopy equivalences, then `g` is a proper homotopy equivalence. -/
theorem of_precomp {f : C(X, Y)} {g : C(Y, Z)} (hf : f.HasProperHomotopyInverse)
    (hg : IsProperMap g) (hgf : (g.comp f).HasProperHomotopyInverse) :
    g.HasProperHomotopyInverse := by
  obtain ⟨f', hf', -, Hf', -, hHf'⟩ := hf.exists_hasProperHomotopyInverse
  exact (hgf.comp hf').of_homotopy (((Homotopy.refl g).comp Hf').cast rfl (comp_id g))
    ((Homotopy.isProperMap_cast_iff _ _).2
      (Homotopy.isProperMap_comp (Homotopy.isProperMap_refl hg) hHf'))

end HasProperHomotopyInverse

/-- Proper homotopy equivalences are invariant under proper homotopy on either side. -/
theorem hasProperHomotopyInverse_iff_of_homotopy {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] {f₀ f₁ : C(X, Y)} (F : Homotopy f₀ f₁) (hF : IsProperMap F) :
    f₀.HasProperHomotopyInverse ↔ f₁.HasProperHomotopyInverse :=
  ⟨fun h ↦ h.of_homotopy F hF, fun h ↦ h.of_homotopy F.symm (Homotopy.isProperMap_symm hF)⟩

end ContinuousMap

/-- A homeomorphism is a proper homotopy equivalence, with constant homotopies: these are the
projections `I × X → X` and `I × Y → Y`, which are proper as `I` is compact. -/
theorem Homeomorph.hasProperHomotopyInverse {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] (e : X ≃ₜ Y) : (e : C(X, Y)).HasProperHomotopyInverse := by
  refine .intro e.isProperMap e.symm e.symm.isProperMap
    ((ContinuousMap.Homotopy.refl _).cast rfl e.symm_comp_toContinuousMap)
    ((ContinuousMap.Homotopy.refl _).cast rfl e.toContinuousMap_comp_symm) ?_ ?_ <;>
  · convert isProperMap_snd_of_compactSpace (X := I) using 1
    ext x
    simp
