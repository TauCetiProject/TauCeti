/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Orientation.Basic

/-!
# The sign of a linear map between oriented spaces

For orientations `o` of `V` and `o'` of `W` with the same index type, the sign
`Orientation.linearMapSign o o' L` of a linear map `L : V → W` is `1` when `L` is an isomorphism
carrying `o` to `o'`, `-1` when it is an isomorphism not carrying `o` to `o'` (that is, carrying
`o` to `-o'` when `Fintype.card ι = finrank R W`), and `0` when it is not an isomorphism.

## Main results

* `Orientation.linearMapSign_eq_one_or_eq_neg_one_of_bijective`: an isomorphism has sign `±1`.
* `Orientation.exists_linearMapSign_eq_and_map_eq`, `Orientation.linearMapSign_eq_of_map_eq`: an
  isomorphism carries `o` to `o'` scaled by its sign, and the sign can be read off from the
  transported orientation.
* `Orientation.linearMapSign_neg_left`, `Orientation.linearMapSign_neg_right`: reversing either
  orientation reverses the sign.
* `Orientation.linearMapSign_map_map`: the sign is unchanged when the map is conjugated by linear
  equivalences of the source and the target and the orientations are transported along them.
* `Orientation.linearMapSign_smul_of_pos`: a positive multiple of a map has the same sign.
-/

public section

open Function Module

namespace Orientation

section CommRing

variable {R : Type*} [CommRing R] [PartialOrder R] [IsStrictOrderedRing R]
  {V W : Type*} [AddCommGroup V] [Module R V] [AddCommGroup W] [Module R W] {ι : Type*}

open scoped Classical in
/-- The **sign of a linear map** `L : V → W` for orientations `o` of `V` and `o'` of `W`: `1`
when `L` is an isomorphism carrying `o` to `o'`, `-1` when it is an isomorphism not carrying `o`
to `o'`, and `0` when it is not an isomorphism. -/
noncomputable def linearMapSign (o : Orientation R V ι) (o' : Orientation R W ι)
    (L : V →ₗ[R] W) : ℤ :=
  if h : Bijective L then
    if Orientation.map ι (LinearEquiv.ofBijective L h) o = o' then 1 else -1
  else 0

variable {o : Orientation R V ι} {o' : Orientation R W ι} {L : V →ₗ[R] W}

open scoped Classical in
/-- For an isomorphism, the sign compares the orientation it carries `o` to with `o'`. -/
theorem linearMapSign_of_bijective (h : Bijective L) :
    linearMapSign o o' L =
      if Orientation.map ι (LinearEquiv.ofBijective L h) o = o' then 1 else -1 := by
  simp only [linearMapSign, h, ↓reduceDIte]

/-- A linear map that is not an isomorphism has sign `0`. -/
theorem linearMapSign_of_not_bijective (h : ¬Bijective L) : linearMapSign o o' L = 0 := by
  simp only [linearMapSign, h, ↓reduceDIte]

/-- **An isomorphism has sign `±1`.** -/
theorem linearMapSign_eq_one_or_eq_neg_one_of_bijective (h : Bijective L) :
    linearMapSign o o' L = 1 ∨ linearMapSign o o' L = -1 := by
  rw [linearMapSign_of_bijective h]
  split_ifs <;> simp

/-- **Reading off the sign.** If a linear equivalence `e` agrees with `L` and carries `o` to `o'`
scaled by a unit sign `u`, the sign of `L` is `u`. -/
theorem linearMapSign_eq_of_map_eq [IsDomain R] (e : V ≃ₗ[R] W) (he : ∀ v, e v = L v) {u : ℤˣ}
    (hu : Orientation.map ι e o = Units.map (Int.castRingHom R).toMonoidHom u • o') :
    linearMapSign o o' L = u := by
  have h : Bijective L := by
    rw [← funext he]
    exact e.bijective
  rw [linearMapSign_of_bijective h,
    show LinearEquiv.ofBijective L h = e from LinearEquiv.ext fun v ↦ (he v).symm, hu,
    intCast_units_smul_eq_ite]
  rcases Int.units_eq_one_or u with rfl | rfl
  · simp
  · simp [(Module.Ray.ne_neg_self _).symm]

/-- **Conjugation invariance.** If `L' ∘ eV = eW ∘ L` for linear equivalences `eV : V ≃ V'` and
`eW : W ≃ W'`, the sign of `L'` for the orientations transported along `eV` and `eW` is the sign
of `L`. -/
theorem linearMapSign_map_map {V' W' : Type*} [AddCommGroup V'] [Module R V'] [AddCommGroup W']
    [Module R W'] (eV : V ≃ₗ[R] V') (eW : W ≃ₗ[R] W') {L' : V' →ₗ[R] W'}
    (hL : ∀ v, L' (eV v) = eW (L v)) :
    linearMapSign (Orientation.map ι eV o) (Orientation.map ι eW o') L' =
      linearMapSign o o' L := by
  have hL' : ⇑L' = eW ∘ L ∘ eV.symm := funext fun w ↦ by simpa using hL (eV.symm w)
  have hL'' : ⇑L = eW.symm ∘ L' ∘ eV := funext fun v ↦ by simp [hL]
  by_cases h : Bijective L
  · have h' : Bijective L' := by
      rw [hL']
      exact eW.bijective.comp (h.comp eV.symm.bijective)
    have hmap : eV.trans (LinearEquiv.ofBijective L' h') = (LinearEquiv.ofBijective L h).trans eW :=
      LinearEquiv.ext hL
    rw [linearMapSign_of_bijective h, linearMapSign_of_bijective h', ← map_trans, hmap, map_trans,
      (Orientation.map ι eW).injective.eq_iff]
  · have h' : ¬Bijective L' := fun h' ↦ h (by
      rw [hL'']
      exact eW.symm.bijective.comp (h'.comp eV.bijective))
    rw [linearMapSign_of_not_bijective h, linearMapSign_of_not_bijective h']

end CommRing

section Field

variable {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
  {V W : Type*} [AddCommGroup V] [Module R V] [AddCommGroup W] [Module R W] {ι : Type*}
  [Fintype ι] {o : Orientation R V ι} {o' : Orientation R W ι} {L : V →ₗ[R] W}

/-- **The sign as a unit.** When the index type has the dimension of the target, an isomorphism
carries `o` to `o'` scaled by a unit sign `u`, and its sign is `u`. -/
theorem exists_linearMapSign_eq_and_map_eq (hι : Fintype.card ι = finrank R W)
    (h : Bijective L) :
    ∃ u : ℤˣ, linearMapSign o o' L = u ∧
      Orientation.map ι (LinearEquiv.ofBijective L h) o =
        Units.map (Int.castRingHom R).toMonoidHom u • o' := by
  classical
  refine ⟨if Orientation.map ι (LinearEquiv.ofBijective L h) o = o' then 1 else -1, ?_,
    (intCast_units_smul_ite_eq _ _ hι).symm⟩
  rw [linearMapSign_of_bijective h]
  split_ifs <;> simp

/-- **Reversing the orientation at the source reverses the sign**, when the index type has the
dimension of the target. -/
theorem linearMapSign_neg_left (hι : Fintype.card ι = finrank R W) :
    linearMapSign (-o) o' L = -linearMapSign o o' L := by
  by_cases h : Bijective L
  · rw [linearMapSign_of_bijective h, linearMapSign_of_bijective h, Orientation.map_neg]
    exact ite_neg_eq_eq_neg_ite hι
  · rw [linearMapSign_of_not_bijective h, linearMapSign_of_not_bijective h, neg_zero]

/-- **Reversing the orientation at the target reverses the sign**, when the index type has the
dimension of the target. -/
theorem linearMapSign_neg_right (hι : Fintype.card ι = finrank R W) :
    linearMapSign o (-o') L = -linearMapSign o o' L := by
  by_cases h : Bijective L
  · rw [linearMapSign_of_bijective h, linearMapSign_of_bijective h]
    exact ite_eq_neg_eq_neg_ite hι
  · rw [linearMapSign_of_not_bijective h, linearMapSign_of_not_bijective h, neg_zero]

omit [Fintype ι] in
/-- **A positive multiple has the same sign**: a positive homothety of the target preserves every
orientation. -/
theorem linearMapSign_smul_of_pos [Finite ι] {c : R} (hc : 0 < c) :
    linearMapSign o o' (c • L) = linearMapSign o o' L := by
  have h := linearMapSign_map_map (o := o) (o' := o') (L := L) (L' := c • L)
    (LinearEquiv.refl R V) (LinearEquiv.smulOfNeZero R W c hc.ne') fun _ ↦ by simp
  rwa [Orientation.map_refl, Orientation.map_smulOfNeZero_of_pos o' hc] at h

end Field

end Orientation
