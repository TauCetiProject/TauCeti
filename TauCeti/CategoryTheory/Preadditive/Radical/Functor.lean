/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Preadditive.Radical.Basic
public import TauCeti.CategoryTheory.Preadditive.MorphismIdeal.Equivalence

/-!
# The radical under fully faithful functors and equivalences

A fully faithful additive functor `F` preserves and reflects the radical: `F.map f` is radical
exactly when `f` is. Indeed every morphism `F.obj Y ⟶ F.obj X` is `F.map g`, and
`𝟙 - F.map f ≫ F.map g = F.map (𝟙 - f ≫ g)` is invertible exactly when `𝟙 - f ≫ g` is. So the
radical ideal of the source is the pullback of the radical ideal of the target.

For an equivalence of categories the same holds for every power of the radical ideal, since the
pullback along an equivalence commutes with products of arbitrary ideals
(`TauCeti.MorphismIdeal.comap_mul_of_equivalence`).

## Main results

* `CategoryTheory.Functor.map_mem_jacobsonRadical_iff`: a fully faithful additive functor
  preserves and reflects radical morphisms.
* `CategoryTheory.Functor.jacobsonRadicalIdeal_comap`: the radical ideal is the pullback of the
  radical ideal of the target along a fully faithful additive functor.
* `CategoryTheory.Equivalence.jacobsonRadicalIdeal_pow_comap`: an equivalence carries each power
  of the radical ideal to the corresponding power, by
  `TauCeti.MorphismIdeal.comap_mul_of_equivalence` for products of arbitrary ideals.
-/

public section

namespace CategoryTheory

open TauCeti

variable {C D : Type*} [Category* C] [Category* D] [Preadditive C] [Preadditive D]

/-- **A fully faithful additive functor preserves and reflects the radical.** -/
@[simp]
theorem Functor.map_mem_jacobsonRadical_iff (F : C ⥤ D) [F.Additive] [F.Full] [F.Faithful] {X Y : C}
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
@[simp]
theorem Functor.jacobsonRadicalIdeal_comap (F : C ⥤ D) [F.Additive] [F.Full] [F.Faithful] :
    (jacobsonRadicalIdeal D).comap F = jacobsonRadicalIdeal C := by
  ext X Y f
  rw [MorphismIdeal.mem_comap_hom, jacobsonRadicalIdeal_hom, jacobsonRadicalIdeal_hom,
    F.map_mem_jacobsonRadical_iff]

/-- **An equivalence carries each power of the radical ideal to the corresponding power.** -/
@[simp]
theorem Equivalence.jacobsonRadicalIdeal_pow_comap (e : C ≌ D) [e.functor.Additive] (n : ℕ) :
    (jacobsonRadicalIdeal D ^ n).comap e.functor = jacobsonRadicalIdeal C ^ n := by
  induction n with
  | zero =>
    ext X Y f
    simp [MorphismIdeal.one_eq_top, MorphismIdeal.mem_comap_hom]
  | succ n ih =>
    rw [pow_succ, pow_succ, MorphismIdeal.comap_mul_of_equivalence, ih,
      e.functor.jacobsonRadicalIdeal_comap]

end CategoryTheory
