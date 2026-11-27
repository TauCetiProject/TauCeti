/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.SemidirectProduct
public import TauCeti.LinearAlgebra.Matrix.SpecialLinearGroup.Action

import TauCeti.GroupTheory.SemidirectProduct

/-!
# Conjugacy classes in `ℤ² ⋊ G` for `G` acting through `SL(2, ℤ)`

Let `ι : G →* SL(2, ℤ)` and form `ℤ² ⋊ G` with `G` acting on column vectors through `ι`
(`TauCeti.slTwoAction`). This file reduces the ICC condition of Murray and von Neumann's factor
theorem for `ℤ² ⋊ G` to a statement about `G`-orbits on `ℤ²`.

An element `(n, g)` with `ι g ≠ 1` has an infinite conjugacy class with no hypothesis on `G`:
conjugating by translations `w ∈ ℤ²` changes `n` by `w - ι g • w`, and `1 - ι g` is a nonzero
integer matrix, so its image is infinite. The conjugacy class of a translation `v ∈ ℤ²` is the
`G`-orbit of `v`, again with no hypothesis on `G`. So for injective `ι`, the group `ℤ² ⋊ G` is ICC
exactly when every nonzero vector of `ℤ²` has an infinite `G`-orbit. That nonamenable `G` have
this property is proved in `TauCeti.GroupTheory.SemidirectProduct.SpecialLinear`.

## Main statements

* `TauCeti.infinite_setOf_isConj_inl_semidirectProduct_slTwo_iff`: the conjugacy class of a
  translation `v` is infinite exactly when its `G`-orbit is.
* `TauCeti.infinite_setOf_isConj_semidirectProduct_slTwo_of_map_right_ne_one`: elements whose
  linear part maps to a nontrivial element of `SL(2, ℤ)` have infinite conjugacy classes.
* `TauCeti.forall_infinite_setOf_isConj_semidirectProduct_slTwo_iff_of_injective`: for injective
  `ι`, the group `ℤ² ⋊ G` is ICC exactly when every nonzero vector has an infinite orbit.

## References

* C. Anantharaman and S. Popa, *An Introduction to II₁ Factors*, Example 18.1.5 and
  Theorem 18.3.2, where `ℤ² ⋊ F_n` is used as an ICC group.
-/

public section

open Matrix Multiplicative SemidirectProduct
open scoped MatrixGroups

namespace TauCeti

section Conjugacy

variable {G : Type*} [Group G] {ι : G →* SL(2, ℤ)}

/-- The conjugacy class of the translation by `v` in `ℤ² ⋊ G` is infinite exactly when the orbit
of `v` under `G` is infinite. -/
theorem infinite_setOf_isConj_inl_semidirectProduct_slTwo_iff (v : Fin 2 → ℤ) :
    {y : Multiplicative (Fin 2 → ℤ) ⋊[slTwoAction.comp ι] G |
        IsConj (inl (ofAdd v)) y}.Infinite ↔
      (Set.range fun g => ι g • v).Infinite := by
  have hconj : {y : Multiplicative (Fin 2 → ℤ) ⋊[slTwoAction.comp ι] G |
      IsConj (inl (ofAdd v)) y} = (fun w => inl (ofAdd w)) '' Set.range fun g => ι g • v := by
    ext y
    simp only [Set.mem_ofPred_eq, isConj_iff, Set.mem_image, Set.mem_range,
      exists_exists_eq_and]
    constructor
    · rintro ⟨c, rfl⟩
      refine ⟨c.right, ?_⟩
      rw [mul_inl_mul_inv, mul_inv_cancel_comm]
      exact congrArg inl (toAdd.injective (by simp [slTwoAction_apply]))
    · rintro ⟨g, rfl⟩
      refine ⟨inr g, ?_⟩
      rw [mul_inl_mul_inv, mul_inv_cancel_comm]
      exact congrArg inl (toAdd.injective (by simp [slTwoAction_apply]))
  rw [hconj, Set.infinite_image_iff fun _ _ _ _ h => ofAdd.injective (inl_injective h)]

/-- An element of `ℤ² ⋊ G` whose linear part acts nontrivially on `ℤ²` has an infinite conjugacy
class: conjugating by translations already produces infinitely many conjugates. -/
theorem infinite_setOf_isConj_semidirectProduct_slTwo_of_map_right_ne_one
    {x : Multiplicative (Fin 2 → ℤ) ⋊[slTwoAction.comp ι] G} (hx : ι x.right ≠ 1) :
    {y | IsConj x y}.Infinite := by
  obtain ⟨u, hu⟩ : ∃ u : Fin 2 → ℤ, ι x.right • u ≠ u := by
    by_contra! h
    exact hx (SpecialLinearGroup.toLin'_injective (LinearEquiv.ext fun u => by
      simpa [SpecialLinearGroup.toLin'_apply, SpecialLinearGroup.smul_def] using h u))
  have hd : u - ι x.right • u ≠ 0 := sub_ne_zero.2 hu.symm
  let f : ℤ → Multiplicative (Fin 2 → ℤ) ⋊[slTwoAction.comp ι] G :=
    fun k => inl (ofAdd (k • u)) * x * (inl (ofAdd (k • u)))⁻¹
  have hleft (k : ℤ) : toAdd (f k).left = toAdd x.left + k • (u - ι x.right • u) := by
    simp [f, slTwoAction_apply, smul_sub, smul_comm]
    abel
  refine Set.infinite_of_injective_forall_mem (f := f) (fun k l hkl => ?_)
    (fun k => isConj_iff.2 ⟨_, rfl⟩)
  have := congrArg (fun y => toAdd y.left) hkl
  simp only [hleft, add_right_inj] at this
  exact smul_left_injective ℤ hd this

/-- For injective `ι`, every nontrivial conjugacy class of `ℤ² ⋊ G` is infinite exactly when every
nonzero vector of `ℤ²` has an infinite `G`-orbit. -/
theorem forall_infinite_setOf_isConj_semidirectProduct_slTwo_iff_of_injective
    (hι : Function.Injective ι) :
    (∀ x : Multiplicative (Fin 2 → ℤ) ⋊[slTwoAction.comp ι] G, x ≠ 1 →
        {y | IsConj x y}.Infinite) ↔
      ∀ v : Fin 2 → ℤ, v ≠ 0 → (Set.range fun g => ι g • v).Infinite := by
  refine ⟨fun h v hv => (infinite_setOf_isConj_inl_semidirectProduct_slTwo_iff v).1 (h _ ?_),
    fun h x hx => ?_⟩
  · rwa [ne_eq, map_eq_one_iff _ inl_injective, ← toAdd_eq_zero, toAdd_ofAdd]
  · by_cases hr : x.right = 1
    · rw [← inl_left_mul_inr_right x, hr, map_one, mul_one] at hx ⊢
      rw [← ofAdd_toAdd x.left] at hx ⊢
      refine (infinite_setOf_isConj_inl_semidirectProduct_slTwo_iff _).2 (h _ fun h0 => hx ?_)
      rw [h0, ofAdd_zero, map_one]
    · exact infinite_setOf_isConj_semidirectProduct_slTwo_of_map_right_ne_one fun h1 =>
        hr (hι (h1.trans (map_one ι).symm))

end Conjugacy

end TauCeti
