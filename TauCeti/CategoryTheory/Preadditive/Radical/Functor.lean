/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Preadditive.Radical.Basic
public import TauCeti.CategoryTheory.Preadditive.MorphismIdeal.Functor
public import TauCeti.CategoryTheory.Preadditive.MorphismIdeal.Mul
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor

/-!
# The radical under fully faithful functors and equivalences

A fully faithful additive functor `F` preserves and reflects the radical: `F.map f` is radical
exactly when `f` is. Indeed every morphism `F.obj Y ⟶ F.obj X` is `F.map g`, and
`𝟙 - F.map f ≫ F.map g = F.map (𝟙 - f ≫ g)` is invertible exactly when `𝟙 - f ≫ g` is. So the
radical ideal of the source is the pullback of the radical ideal of the target.

For an equivalence of categories the same holds for every power of the radical ideal: the
pullback along an equivalence commutes with products of ideals, because the middle object of a
composite in the target can be replaced by an isomorphic object in the image of the functor.

## Main results

* `TauCeti.map_mem_jacobsonRadical_iff`: a fully faithful additive functor preserves and reflects
  radical morphisms.
* `TauCeti.jacobsonRadicalIdeal_comap`: the radical ideal is the pullback of the radical ideal of
  the target along a fully faithful additive functor.
* `TauCeti.MorphismIdeal.comap_mul_of_equivalence`: pullback along an equivalence commutes with
  products of ideals.
* `TauCeti.jacobsonRadicalIdeal_pow_comap`: an equivalence carries each power of the radical
  ideal to the corresponding power.
-/

public section

namespace TauCeti

open CategoryTheory

variable {C D : Type*} [Category* C] [Category* D] [Preadditive C] [Preadditive D]

/-- **A fully faithful additive functor preserves and reflects the radical.** -/
theorem map_mem_jacobsonRadical_iff (F : C ⥤ D) [F.Additive] [F.Full] [F.Faithful] {X Y : C}
    (f : X ⟶ Y) : F.map f ∈ jacobsonRadical (F.obj X) (F.obj Y) ↔ f ∈ jacobsonRadical X Y := by
  simp only [mem_jacobsonRadical_iff_isIso_id_sub_comp_right]
  refine ⟨fun h g ↦ ?_, fun h g ↦ ?_⟩
  · have := h (F.map g)
    rw [← F.map_comp, ← F.map_id, ← F.map_sub] at this
    exact isIso_of_fully_faithful F _
  · obtain ⟨g, rfl⟩ := F.map_surjective g
    rw [← F.map_comp, ← F.map_id, ← F.map_sub]
    infer_instance

/-- The radical ideal is the pullback of the radical ideal of the target along a fully faithful
additive functor. -/
theorem jacobsonRadicalIdeal_comap (F : C ⥤ D) [F.Additive] [F.Full] [F.Faithful] :
    (jacobsonRadicalIdeal D).comap F = jacobsonRadicalIdeal C := by
  ext X Y f
  rw [MorphismIdeal.mem_comap_hom, jacobsonRadicalIdeal_hom, jacobsonRadicalIdeal_hom,
    map_mem_jacobsonRadical_iff]

/-- **Pullback along an equivalence commutes with products of ideals.** The middle object of a
composite in the target is replaced by an isomorphic object in the image of the functor. -/
theorem MorphismIdeal.comap_mul_of_equivalence [Limits.HasBinaryBiproducts D] (e : C ≌ D)
    [e.functor.Additive] (I J : MorphismIdeal D) :
    (I * J).comap e.functor = I.comap e.functor * J.comap e.functor := by
  apply le_antisymm
  · rw [MorphismIdeal.le_def]
    intro X Y h hh
    rw [MorphismIdeal.mem_comap_hom, MorphismIdeal.mem_mul_iff_exists_comp] at hh
    obtain ⟨Z, g, f, hg, hf, hgf⟩ := hh
    -- Replace `Z` by `e.functor.obj (e.inverse.obj Z)`.
    let ε := e.counitIso.app Z
    obtain ⟨g', hg'⟩ := e.functor.map_surjective (g ≫ ε.inv)
    obtain ⟨f', hf'⟩ := e.functor.map_surjective (ε.hom ≫ f)
    have h' : h = g' ≫ f' := e.functor.map_injective (by simp [hg', hf', hgf])
    rw [h']
    refine MorphismIdeal.comp_mem_mul ?_ ?_
    · rw [MorphismIdeal.mem_comap_hom, hg']
      exact J.comp_mem_right _ hg
    · rw [MorphismIdeal.mem_comap_hom, hf']
      exact I.comp_mem_left _ hf
  · rw [MorphismIdeal.mul_le_iff]
    intro X Z Y g f hg hf
    rw [MorphismIdeal.mem_comap_hom] at hg hf ⊢
    rw [Functor.map_comp]
    exact MorphismIdeal.comp_mem_mul hg hf

/-- **An equivalence carries each power of the radical ideal to the corresponding power.** -/
theorem jacobsonRadicalIdeal_pow_comap [Limits.HasBinaryBiproducts D] (e : C ≌ D)
    [e.functor.Additive] (n : ℕ) :
    (jacobsonRadicalIdeal D ^ n).comap e.functor = jacobsonRadicalIdeal C ^ n := by
  induction n with
  | zero =>
    ext X Y f
    simp [MorphismIdeal.one_eq_top, MorphismIdeal.mem_comap_hom]
  | succ n ih =>
    rw [pow_succ, pow_succ, MorphismIdeal.comap_mul_of_equivalence, ih,
      jacobsonRadicalIdeal_comap]

end TauCeti
