/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.Height.FundamentalInequality

import TauCeti.NumberTheory.NumberField.PlacesOver.FinitePlace
import TauCeti.NumberTheory.NumberField.PlacesOver.InfinitePlace

/-!
# Height bounds above places

Let `F / K` be an extension of fields with `F` a number field. Absolute values of `F` lying over
distinct places of `K` contribute truncated local factors whose product is bounded by the
multiplicative height `Height.mulHeight₁` in `F`:

* Above distinct infinite places `Sinf : Finset (InfinitePlace K)` (for any base field `K`, without
  assuming `[NumberField K]`), each `w v` is an infinite place `V v` of `F` lying over `v`
  (`NumberField.exists_injective_infinitePlace_eq_of_liesOver`), and `v.mult ≤ (V v).mult`
  (`NumberField.InfinitePlace.mult_comap_le`), so
  `max (w v x) 1 ^ v.mult ≤ max (V v x) 1 ^ (V v).mult`.
* Above distinct finite places `Sfin : Finset (FinitePlace K)` (with `[NumberField K]`), each `w v`
  is a positive root `V v ^ t` with `0 < t ≤ 1` of a distinct finite place `V v` of `F`
  (`NumberField.exists_injective_finitePlace_rpow_eq_of_liesOver`), so
  `max (w v x) 1 ≤ max (V v x) 1`.

Combining the two bounds with `NumberField.prod_max_apply_one_le_mulHeight₁` gives the upper bound
`(∏ v ∈ Sinf, max (winf v x) 1 ^ v.mult) * ∏ v ∈ Sfin, max (wfin v x) 1 ≤ mulHeight₁ x`, and
applying it to `x⁻¹` for `x ≠ 0` gives the reciprocal lower bound on the product of `min 1 (w v x)`.

## Main results

* `NumberField.InfinitePlace.prod_max_apply_one_pow_mult_le_mulHeight₁_of_liesOver` and
  `NumberField.InfinitePlace.inv_mulHeight₁_le_prod_min_one_apply_pow_mult_of_liesOver`: product
  bounds above finitely many infinite places of a base field `K` (weighted by `v.mult`).
* `NumberField.FinitePlace.prod_max_apply_one_le_mulHeight₁_of_liesOver` and
  `NumberField.FinitePlace.inv_mulHeight₁_le_prod_min_one_apply_of_liesOver`: product bounds above
  finitely many finite places of a base number field `K`.
* `NumberField.prod_max_apply_one_le_mulHeight₁_of_liesOver` and
  `NumberField.inv_mulHeight₁_le_prod_min_one_apply_of_liesOver`: combined `(Sinf, Sfin)` product
  bounds for an extension `F / K` of number fields.
* `NumberField.InfinitePlace.max_apply_one_pow_mult_le_mulHeight₁_of_liesOver`,
  `NumberField.InfinitePlace.max_apply_one_le_mulHeight₁_of_liesOver`,
  `NumberField.InfinitePlace.inv_mulHeight₁_le_min_one_apply_pow_mult_of_liesOver`,
  `NumberField.InfinitePlace.inv_mulHeight₁_le_min_one_apply_of_liesOver`,
  `NumberField.FinitePlace.max_apply_one_le_mulHeight₁_of_liesOver`,
  `NumberField.FinitePlace.inv_mulHeight₁_le_min_one_apply_of_liesOver`,
  `NumberField.max_apply_one_le_mulHeight₁_of_liesOver`, and
  `NumberField.inv_mulHeight₁_le_min_one_apply_of_liesOver`: single-place height bounds.

## References

* E. Bombieri and W. Gubler, *Heights in Diophantine Geometry*, Cambridge University Press, 2006,
  §§1.3 and 1.5.
-/

public section

open Height

namespace NumberField

section InfinitePlaces

variable {K F : Type*} [Field K] [Field F] [NumberField F] [Algebra K F]

omit [NumberField F] in
private theorem exists_finset_infinitePlace_prod_max_le
    (S : Finset (InfinitePlace K)) (w : InfinitePlace K → AbsoluteValue F ℝ)
    (hw : ∀ v ∈ S, (w v).LiesOver v.1) (x : F) :
    ∃ T : Finset (InfinitePlace F),
      ∏ v ∈ S, max (w v x) 1 ^ v.mult ≤ ∏ u ∈ T, max (u x) 1 ^ u.mult := by
  classical
  obtain ⟨V, hV, hVw⟩ := exists_injective_infinitePlace_eq_of_liesOver
    (S : Set (InfinitePlace K)) (fun v ↦ w v.val) (fun v ↦ hw v.val v.prop)
  have hlocal (v : ↥S) : max (w v.val x) 1 ^ v.val.mult ≤ max (V v x) 1 ^ (V v).mult := by
    let := (hVw v).1
    have hmult : v.val.mult ≤ (V v).mult := by
      rw [← InfinitePlace.LiesOver.comap_eq (V v) v.val]
      exact InfinitePlace.mult_comap_le _ _
    have hval : w v.val x = V v x := congrArg (· x) (hVw v).2.symm
    rw [hval]
    exact pow_le_pow_right₀ (le_max_right _ _) hmult
  refine ⟨S.attach.image V, ?_⟩
  calc
    ∏ v ∈ S, max (w v x) 1 ^ v.mult = ∏ v ∈ S.attach, max (w v.val x) 1 ^ v.val.mult :=
      (Finset.prod_attach S _).symm
    _ ≤ ∏ v ∈ S.attach, max (V v x) 1 ^ (V v).mult :=
      Finset.prod_le_prod₀ (fun _ _ ↦ by positivity) (fun v _ ↦ hlocal v)
    _ = ∏ u ∈ S.attach.image V, max (u x) 1 ^ u.mult :=
      (Finset.prod_image (f := fun u : InfinitePlace F ↦ max (u x) 1 ^ u.mult)
        (s := S.attach) hV.injOn).symm

/-- The product of the upper truncated local factors at absolute values lying over distinct
infinite places of a base field `K`, weighted by `v.mult`, is at most the multiplicative height in
the number field `F`. -/
theorem InfinitePlace.prod_max_apply_one_pow_mult_le_mulHeight₁_of_liesOver
    (S : Finset (InfinitePlace K)) (w : InfinitePlace K → AbsoluteValue F ℝ)
    (hw : ∀ v ∈ S, (w v).LiesOver v.1) (x : F) :
    ∏ v ∈ S, max (w v x) 1 ^ v.mult ≤ mulHeight₁ x := by
  obtain ⟨T, hT⟩ := exists_finset_infinitePlace_prod_max_le S w hw x
  exact hT.trans (by simpa using prod_max_apply_one_le_mulHeight₁ T (∅ : Finset (FinitePlace F)) x)

/-- The product of the lower truncated local factors at absolute values lying over distinct
infinite places of a base field `K`, weighted by `v.mult`, is at least the reciprocal multiplicative
height of a nonzero element in the number field `F`. -/
theorem InfinitePlace.inv_mulHeight₁_le_prod_min_one_apply_pow_mult_of_liesOver
    (S : Finset (InfinitePlace K)) (w : InfinitePlace K → AbsoluteValue F ℝ)
    (hw : ∀ v ∈ S, (w v).LiesOver v.1) {x : F} (hx : x ≠ 0) :
    (mulHeight₁ x)⁻¹ ≤ ∏ v ∈ S, min 1 (w v x) ^ v.mult := by
  have h := InfinitePlace.prod_max_apply_one_pow_mult_le_mulHeight₁_of_liesOver S w hw x⁻¹
  have hinv (v : InfinitePlace K) : max (w v x⁻¹) 1 = (min 1 (w v x))⁻¹ := by
    simpa [map_inv₀, max_comm] using
      (AntitoneOn.map_min (s := Set.Ioi (0 : ℝ)) (fun _ ha _ _ hle ↦ inv_anti₀ ha hle)
        zero_lt_one ((w v).pos hx)).symm
  simp only [hinv, inv_pow, Finset.prod_inv_distrib, mulHeight₁_inv] at h
  exact (inv_le_comm₀ (Finset.prod_pos fun v _ ↦ pow_pos (lt_min zero_lt_one ((w v).pos hx)) _)
    (mulHeight₁_pos x)).mp h

/-- At an absolute value of a number field `F` lying over an infinite place `v` of a base field `K`,
the upper truncated factor weighted by `v.mult` is at most the multiplicative height in `F`. -/
theorem InfinitePlace.max_apply_one_pow_mult_le_mulHeight₁_of_liesOver (v : InfinitePlace K)
    (w : AbsoluteValue F ℝ) [w.LiesOver v.1] (x : F) :
    max (w x) 1 ^ v.mult ≤ mulHeight₁ x := by
  simpa using InfinitePlace.prod_max_apply_one_pow_mult_le_mulHeight₁_of_liesOver {v} (fun _ ↦ w)
    (by intro u hu; obtain rfl := Finset.mem_singleton.mp hu; infer_instance) x

/-- At an absolute value of a number field `F` lying over an infinite place `v` of a base field `K`,
the upper truncated factor is at most the multiplicative height in `F`. -/
theorem InfinitePlace.max_apply_one_le_mulHeight₁_of_liesOver (v : InfinitePlace K)
    (w : AbsoluteValue F ℝ) [w.LiesOver v.1] (x : F) :
    max (w x) 1 ≤ mulHeight₁ x :=
  (le_self_pow₀ (le_max_right _ _) v.mult_ne_zero).trans
    (v.max_apply_one_pow_mult_le_mulHeight₁_of_liesOver w x)

/-- At an absolute value of a number field `F` lying over an infinite place `v` of a base field `K`,
the lower truncated factor of a nonzero element weighted by `v.mult` is at least its reciprocal
multiplicative height in `F`. -/
theorem InfinitePlace.inv_mulHeight₁_le_min_one_apply_pow_mult_of_liesOver (v : InfinitePlace K)
    (w : AbsoluteValue F ℝ) [w.LiesOver v.1] {x : F} (hx : x ≠ 0) :
    (mulHeight₁ x)⁻¹ ≤ min 1 (w x) ^ v.mult := by
  simpa using InfinitePlace.inv_mulHeight₁_le_prod_min_one_apply_pow_mult_of_liesOver {v}
    (fun _ ↦ w) (by intro u hu; obtain rfl := Finset.mem_singleton.mp hu; infer_instance) hx

/-- At an absolute value of a number field `F` lying over an infinite place `v` of a base field `K`,
the lower truncated factor of a nonzero element is at least its reciprocal multiplicative height in
`F`. -/
theorem InfinitePlace.inv_mulHeight₁_le_min_one_apply_of_liesOver (v : InfinitePlace K)
    (w : AbsoluteValue F ℝ) [w.LiesOver v.1] {x : F} (hx : x ≠ 0) :
    (mulHeight₁ x)⁻¹ ≤ min 1 (w x) :=
  (v.inv_mulHeight₁_le_min_one_apply_pow_mult_of_liesOver w hx).trans <|
    pow_le_of_le_one (le_min zero_le_one (w.nonneg _)) (min_le_left _ _) v.mult_ne_zero

end InfinitePlaces

section NumberFieldExtension

variable {K F : Type*} [Field K] [Field F] [NumberField K] [NumberField F] [Algebra K F]

private theorem exists_finset_finitePlace_prod_max_le
    (S : Finset (FinitePlace K)) (w : FinitePlace K → AbsoluteValue F ℝ)
    (hw : ∀ v ∈ S, (w v).LiesOver v.1) (x : F) :
    ∃ T : Finset (FinitePlace F), ∏ v ∈ S, max (w v x) 1 ≤ ∏ u ∈ T, max (u x) 1 := by
  classical
  obtain ⟨V, t, hV, ht⟩ := exists_injective_finitePlace_rpow_eq_of_liesOver
    (S : Set (FinitePlace K)) (fun v ↦ w v.val) (fun v ↦ hw v.val v.prop)
  have hlocal (v : ↥S) : max (w v.val x) 1 ≤ max (V v x) 1 := by
    calc
      max (w v.val x) 1 = max (V v x) 1 ^ t v := by
        rw [(ht v).2.2, Real.rpow_max (by positivity) zero_le_one (ht v).1.le, Real.one_rpow]
      _ ≤ max (V v x) 1 := Real.rpow_le_self_of_one_le (le_max_right _ _) (ht v).2.1
  refine ⟨S.attach.image V, ?_⟩
  calc
    ∏ v ∈ S, max (w v x) 1 = ∏ v ∈ S.attach, max (w v.val x) 1 :=
      (Finset.prod_attach S _).symm
    _ ≤ ∏ v ∈ S.attach, max (V v x) 1 :=
      Finset.prod_le_prod₀ (fun _ _ ↦ by positivity) (fun v _ ↦ hlocal v)
    _ = ∏ u ∈ S.attach.image V, max (u x) 1 :=
      (Finset.prod_image (f := fun u : FinitePlace F ↦ max (u x) 1)
        (s := S.attach) hV.injOn).symm

/-- The product of the upper truncated local factors at absolute values lying over distinct
infinite places `Sinf` (weighted by `v.mult`) and distinct finite places `Sfin` of the base number
field `K` is at most the multiplicative height in the extension `F`. -/
theorem prod_max_apply_one_le_mulHeight₁_of_liesOver
    (Sinf : Finset (InfinitePlace K)) (Sfin : Finset (FinitePlace K))
    (winf : InfinitePlace K → AbsoluteValue F ℝ) (wfin : FinitePlace K → AbsoluteValue F ℝ)
    (hwinf : ∀ v ∈ Sinf, (winf v).LiesOver v.1) (hwfin : ∀ v ∈ Sfin, (wfin v).LiesOver v.1)
    (x : F) :
    (∏ v ∈ Sinf, max (winf v x) 1 ^ v.mult) * ∏ v ∈ Sfin, max (wfin v x) 1 ≤ mulHeight₁ x := by
  obtain ⟨Tinf, hinf⟩ := exists_finset_infinitePlace_prod_max_le Sinf winf hwinf x
  obtain ⟨Tfin, hfin⟩ := exists_finset_finitePlace_prod_max_le Sfin wfin hwfin x
  exact (mul_le_mul hinf hfin (Finset.prod_nonneg fun _ _ ↦ by positivity) (by positivity)).trans
    (prod_max_apply_one_le_mulHeight₁ Tinf Tfin x)

/-- The product of the lower truncated local factors at absolute values lying over distinct
infinite places `Sinf` (weighted by `v.mult`) and distinct finite places `Sfin` of the base number
field `K` is at least the reciprocal multiplicative height of a nonzero element in `F`. -/
theorem inv_mulHeight₁_le_prod_min_one_apply_of_liesOver
    (Sinf : Finset (InfinitePlace K)) (Sfin : Finset (FinitePlace K))
    (winf : InfinitePlace K → AbsoluteValue F ℝ) (wfin : FinitePlace K → AbsoluteValue F ℝ)
    (hwinf : ∀ v ∈ Sinf, (winf v).LiesOver v.1) (hwfin : ∀ v ∈ Sfin, (wfin v).LiesOver v.1)
    {x : F} (hx : x ≠ 0) :
    (mulHeight₁ x)⁻¹ ≤
      (∏ v ∈ Sinf, min 1 (winf v x) ^ v.mult) * ∏ v ∈ Sfin, min 1 (wfin v x) := by
  have h := prod_max_apply_one_le_mulHeight₁_of_liesOver Sinf Sfin winf wfin hwinf hwfin x⁻¹
  have hinv (u : AbsoluteValue F ℝ) : max (u x⁻¹) 1 = (min 1 (u x))⁻¹ := by
    simpa [map_inv₀, max_comm] using
      (AntitoneOn.map_min (s := Set.Ioi (0 : ℝ)) (fun _ ha _ _ hle ↦ inv_anti₀ ha hle)
        zero_lt_one (u.pos hx)).symm
  simp only [hinv, inv_pow, Finset.prod_inv_distrib, ← mul_inv, mulHeight₁_inv] at h
  have hpos : 0 < (∏ v ∈ Sinf, min 1 (winf v x) ^ v.mult) * ∏ v ∈ Sfin, min 1 (wfin v x) :=
    mul_pos (Finset.prod_pos fun v _ ↦ pow_pos (lt_min zero_lt_one ((winf v).pos hx)) _)
      (Finset.prod_pos fun v _ ↦ lt_min zero_lt_one ((wfin v).pos hx))
  exact (inv_le_comm₀ hpos (mulHeight₁_pos x)).mp h

/-- The product of the upper truncated local factors at absolute values lying over distinct
finite places of the base is at most the multiplicative height in the extension. -/
theorem FinitePlace.prod_max_apply_one_le_mulHeight₁_of_liesOver
    (S : Finset (FinitePlace K)) (w : FinitePlace K → AbsoluteValue F ℝ)
    (hw : ∀ v ∈ S, (w v).LiesOver v.1) (x : F) :
    ∏ v ∈ S, max (w v x) 1 ≤ mulHeight₁ x := by
  simpa using NumberField.prod_max_apply_one_le_mulHeight₁_of_liesOver ∅ S
    (fun v ↦ (InfinitePlace.comap_surjective v).choose.1) w (by simp) hw x

/-- The product of the lower truncated local factors at absolute values lying over distinct
finite places of the base is at least the reciprocal multiplicative height of a nonzero element. -/
theorem FinitePlace.inv_mulHeight₁_le_prod_min_one_apply_of_liesOver
    (S : Finset (FinitePlace K)) (w : FinitePlace K → AbsoluteValue F ℝ)
    (hw : ∀ v ∈ S, (w v).LiesOver v.1) {x : F} (hx : x ≠ 0) :
    (mulHeight₁ x)⁻¹ ≤ ∏ v ∈ S, min 1 (w v x) := by
  simpa using NumberField.inv_mulHeight₁_le_prod_min_one_apply_of_liesOver ∅ S
    (fun v ↦ (InfinitePlace.comap_surjective v).choose.1) w (by simp) hw hx

/-- An absolute value lying over a finite place of the base is bounded by the multiplicative height
in the extension, even when it is not itself a finite place. -/
theorem FinitePlace.max_apply_one_le_mulHeight₁_of_liesOver (v : FinitePlace K)
    (w : AbsoluteValue F ℝ) [w.LiesOver v.1] (x : F) :
    max (w x) 1 ≤ mulHeight₁ x := by
  simpa using FinitePlace.prod_max_apply_one_le_mulHeight₁_of_liesOver {v} (fun _ ↦ w)
    (by intro u hu; obtain rfl := Finset.mem_singleton.mp hu; infer_instance) x

/-- At an absolute value above a finite place, the lower truncated factor of a nonzero element
is bounded below by its reciprocal multiplicative height. -/
theorem FinitePlace.inv_mulHeight₁_le_min_one_apply_of_liesOver (v : FinitePlace K)
    (w : AbsoluteValue F ℝ) [w.LiesOver v.1] {x : F} (hx : x ≠ 0) :
    (mulHeight₁ x)⁻¹ ≤ min 1 (w x) := by
  simpa using FinitePlace.inv_mulHeight₁_le_prod_min_one_apply_of_liesOver {v} (fun _ ↦ w)
    (by intro u hu; obtain rfl := Finset.mem_singleton.mp hu; infer_instance) hx

/-- At an absolute value of `F` lying over an infinite or finite place `v` of `K`, the upper
truncated local factor is at most the multiplicative height in `F`. -/
theorem max_apply_one_le_mulHeight₁_of_liesOver {v : AbsoluteValue K ℝ}
    (hv : IsInfinitePlace v ∨ IsFinitePlace v) (w : AbsoluteValue F ℝ) [w.LiesOver v] (x : F) :
    max (w x) 1 ≤ mulHeight₁ x := by
  rcases hv.imp (isInfinitePlace_iff v).mp (isFinitePlace_iff v).mp with ⟨u, rfl⟩ | ⟨u, rfl⟩
  · exact u.max_apply_one_le_mulHeight₁_of_liesOver w x
  · exact u.max_apply_one_le_mulHeight₁_of_liesOver w x

/-- At an absolute value of `F` lying over an infinite or finite place `v` of `K`, the lower
truncated local factor of a nonzero element is at least its reciprocal multiplicative height in
`F`. -/
theorem inv_mulHeight₁_le_min_one_apply_of_liesOver {v : AbsoluteValue K ℝ}
    (hv : IsInfinitePlace v ∨ IsFinitePlace v) (w : AbsoluteValue F ℝ) [w.LiesOver v] {x : F}
    (hx : x ≠ 0) : (mulHeight₁ x)⁻¹ ≤ min 1 (w x) := by
  rcases hv.imp (isInfinitePlace_iff v).mp (isFinitePlace_iff v).mp with ⟨u, rfl⟩ | ⟨u, rfl⟩
  · exact u.inv_mulHeight₁_le_min_one_apply_of_liesOver w hx
  · exact u.inv_mulHeight₁_le_min_one_apply_of_liesOver w hx

/-- The lower bound fails at `x = 0`, where `(mulHeight₁ (0 : F))⁻¹ = 1` while `min 1 (w 0) = 0`. -/
example (w : AbsoluteValue F ℝ) : ¬ (mulHeight₁ (0 : F))⁻¹ ≤ min 1 (w 0) := by
  simp

end NumberFieldExtension

end NumberField
