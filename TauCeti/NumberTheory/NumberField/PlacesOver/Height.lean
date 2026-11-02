/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.PlacesOver.FinitePlace
public import TauCeti.NumberTheory.Height.FundamentalInequality

/-!
# Height bounds above finite places

Absolute values of a number field extension lying over distinct finite places of the base give
local factors whose product is bounded by the relative height in the extension. The absolute
values need not themselves be finite places: they are positive roots of distinct finite places,
with exponents at most one. Taking such a root moves both truncated factors toward one.

The upper bound uses `max (w x) 1`; for nonzero `x` the corresponding product of `min 1 (w x)`
is bounded below by the reciprocal height. The single-place upper bound controls the size of
algebraic targets in local polynomial estimates, while the product bounds are the finite-place
part of the fundamental inequality in an extension.

## References

* E. Bombieri and W. Gubler, *Heights in Diophantine Geometry* (2006), §§1.3 and 1.5.
-/

public section

open Height

namespace NumberField

variable {K F : Type*} [Field K] [Field F] [NumberField K] [NumberField F] [Algebra K F]

/-- The product of the upper truncated local factors at absolute values lying over distinct
finite places of the base is at most the relative height in the extension. -/
theorem prod_max_apply_one_le_mulHeight₁_of_liesOver
    (S : Finset (FinitePlace K)) (w : FinitePlace K → AbsoluteValue F ℝ)
    (hw : ∀ v ∈ S, (w v).LiesOver v.1) (x : F) :
    ∏ v ∈ S, max (w v x) 1 ≤ mulHeight₁ x := by
  classical
  obtain ⟨V, t, hV, ht⟩ := exists_injective_finitePlace_rpow_eq_of_liesOver
    (S : Set (FinitePlace K)) (fun v ↦ w v.val) (fun v ↦ hw v.val v.prop)
  have hlocal (v : ↥S) : max (w v.val x) 1 ≤ max (V v x) 1 := by
    calc
      max (w v.val x) 1 = max (V v x) 1 ^ t v := by
        rw [(ht v).2.2, Real.rpow_max (by positivity) zero_le_one (ht v).1.le,
          Real.one_rpow]
      _ ≤ max (V v x) 1 := Real.rpow_le_self_of_one_le (le_max_right _ _) (ht v).2.1
  calc
    ∏ v ∈ S, max (w v x) 1 = ∏ v ∈ S.attach, max (w v.val x) 1 :=
      (Finset.prod_attach S _).symm
    _ ≤ ∏ v ∈ S.attach, max (V v x) 1 := Finset.prod_le_prod₀
      (fun _ _ ↦ by positivity) (fun v _ ↦ hlocal v)
    _ = ∏ v ∈ S.attach.image V, max (v x) 1 :=
      (Finset.prod_image (f := fun v : FinitePlace F ↦ max (v x) 1)
        (s := S.attach) hV.injOn).symm
    _ ≤ mulHeight₁ x := by
      simpa using prod_max_apply_one_le_mulHeight₁
        (∅ : Finset (InfinitePlace F)) (S.attach.image V) x

/-- The product of the lower truncated local factors at absolute values lying over distinct
finite places of the base is at least the reciprocal relative height of a nonzero element. -/
theorem inv_mulHeight₁_le_prod_min_one_apply_of_liesOver
    (S : Finset (FinitePlace K)) (w : FinitePlace K → AbsoluteValue F ℝ)
    (hw : ∀ v ∈ S, (w v).LiesOver v.1) {x : F} (hx : x ≠ 0) :
    (mulHeight₁ x)⁻¹ ≤ ∏ v ∈ S, min 1 (w v x) := by
  have h := prod_max_apply_one_le_mulHeight₁_of_liesOver S w hw x⁻¹
  have hinv (v : FinitePlace K) : max (w v x⁻¹) 1 = (min 1 (w v x))⁻¹ := by
    rw [map_inv₀]
    rcases le_total (w v x) 1 with hle | hle
    · rw [min_eq_right hle, max_eq_left ((one_le_inv₀ ((w v).pos hx)).mpr hle)]
    · rw [min_eq_left hle, inv_one,
        max_eq_right ((inv_le_one₀ ((w v).pos hx)).mpr hle)]
  simp only [hinv, Finset.prod_inv_distrib, mulHeight₁_inv] at h
  exact (inv_le_comm₀ (Finset.prod_pos fun v _ ↦ lt_min zero_lt_one ((w v).pos hx))
    (mulHeight₁_pos x)).mp h

/-- An absolute value lying over a finite place of the base is bounded by the relative height
in the extension, even when it is not itself a finite place. -/
theorem FinitePlace.max_apply_one_le_mulHeight₁_of_liesOver (v : FinitePlace K)
    (w : AbsoluteValue F ℝ) [w.LiesOver v.1] (x : F) :
    max (w x) 1 ≤ mulHeight₁ x := by
  simpa using prod_max_apply_one_le_mulHeight₁_of_liesOver {v} (fun _ ↦ w)
    (by intro u hu; obtain rfl := Finset.mem_singleton.mp hu; infer_instance) x

/-- At an absolute value above a finite place, the lower truncated factor of a nonzero element
is bounded below by its reciprocal relative height. -/
theorem FinitePlace.inv_mulHeight₁_le_min_one_apply_of_liesOver (v : FinitePlace K)
    (w : AbsoluteValue F ℝ) [w.LiesOver v.1] {x : F} (hx : x ≠ 0) :
    (mulHeight₁ x)⁻¹ ≤ min 1 (w x) := by
  simpa using inv_mulHeight₁_le_prod_min_one_apply_of_liesOver {v} (fun _ ↦ w)
    (by intro u hu; obtain rfl := Finset.mem_singleton.mp hu; infer_instance) hx

end NumberField
