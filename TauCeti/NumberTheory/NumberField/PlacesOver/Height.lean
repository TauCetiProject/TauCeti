/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.PlacesOver.Basic
public import TauCeti.NumberTheory.Height.FundamentalInequality

/-!
# Height bounds above places

Absolute values of a number field extension `F / K` lying over distinct places of `K` give local
factors whose product is bounded by the relative height `mulHeight₁` in `F`:

* Above distinct infinite places `v ∈ Sinf`, the chosen absolute values are distinct infinite
  places `W v` of `F` (`NumberField.exists_injective_infinitePlace_eq_of_liesOver`), with
  `v.mult ≤ (W v).mult` (`NumberField.InfinitePlace.mult_comap_le`), so raising `max (w x) 1 ≥ 1`
  to `v.mult` does not exceed the `F`-normalized factor `max (W v x) 1 ^ (W v).mult`.
* Above distinct finite places `v ∈ Sfin`, the chosen absolute values are roots `V v ^ t v` of
  distinct finite places of `F` with `0 < t v ≤ 1`, which again shrinks `max (w x) 1` toward `1`.

Multiplying both halves bounds the combined `(Sinf, Sfin)` truncated product by `mulHeight₁ x`
(`NumberField.prod_max_apply_one_pow_mult_mul_prod_le_mulHeight₁_of_liesOver`), and for `x ≠ 0`
inversion bounds the lower truncated product below by `(mulHeight₁ x)⁻¹`
(`NumberField.inv_mulHeight₁_le_prod_min_one_apply_pow_mult_mul_prod_of_liesOver`). Specializing
gives the archimedean-only, nonarchimedean-only, and single-place bounds (including the uniform
single-place bounds `NumberField.max_apply_one_le_mulHeight₁_of_liesOver` and
`NumberField.inv_mulHeight₁_le_min_one_apply_of_liesOver` for
`IsInfinitePlace v ∨ IsFinitePlace v`).

## References

* E. Bombieri and W. Gubler, *Heights in Diophantine Geometry* (2006), §§1.3 and 1.5.
-/

public section

open Height

namespace NumberField

private theorem max_inv_eq_inv_min {F : Type*} [Field F] (u : AbsoluteValue F ℝ)
    {x : F} (hx : x ≠ 0) : max (u x⁻¹) 1 = (min 1 (u x))⁻¹ := by
  rw [map_inv₀]
  rcases le_total (u x) 1 with hle | hle
  · rw [min_eq_right hle, max_eq_left ((one_le_inv₀ (u.pos hx)).mpr hle)]
  · rw [min_eq_left hle, inv_one, max_eq_right ((inv_le_one₀ (u.pos hx)).mpr hle)]

private theorem exists_finset_prod_max_apply_one_pow_mult_le
    {K F : Type*} [Field K] [Field F] [Algebra K F]
    (Sinf : Finset (InfinitePlace K)) (winf : InfinitePlace K → AbsoluteValue F ℝ)
    (hwinf : ∀ v ∈ Sinf, (winf v).LiesOver v.1) (x : F) :
    ∃ T : Finset (InfinitePlace F),
      ∏ v ∈ Sinf, max (winf v x) 1 ^ v.mult ≤ ∏ v ∈ T, max (v x) 1 ^ v.mult := by
  classical
  obtain ⟨W, hW, hWeq⟩ := exists_injective_infinitePlace_eq_of_liesOver
    (Sinf : Set (InfinitePlace K)) (fun v ↦ winf v.val) (fun v ↦ hwinf v.val v.prop)
  refine ⟨Sinf.attach.image W, ?_⟩
  rw [← Finset.prod_attach Sinf, Finset.prod_image hW.injOn]
  refine Finset.prod_le_prod₀ (fun _ _ ↦ by positivity) fun v _ ↦ ?_
  let := (hWeq v).1
  have hmult : v.val.mult ≤ (W v).mult := by
    rw [← InfinitePlace.LiesOver.comap_eq (W v) v.val]
    exact InfinitePlace.mult_comap_le (algebraMap K F) (W v)
  have hxW : winf v.val x = W v x := by rw [← (hWeq v).2, InfinitePlace.coe_apply]
  rw [hxW]
  exact pow_le_pow_right₀ (le_max_right _ _) hmult

section Infinite

variable {K F : Type*} [Field K] [Field F] [NumberField F] [Algebra K F]

/-- The product of the `v.mult`-weighted upper truncated local factors at absolute values lying
over distinct infinite places of `K` is at most the relative height in `F`. -/
theorem prod_max_apply_one_pow_mult_le_mulHeight₁_of_liesOver
    (S : Finset (InfinitePlace K)) (w : InfinitePlace K → AbsoluteValue F ℝ)
    (hw : ∀ v ∈ S, (w v).LiesOver v.1) (x : F) :
    ∏ v ∈ S, max (w v x) 1 ^ v.mult ≤ mulHeight₁ x := by
  obtain ⟨T, hT⟩ := exists_finset_prod_max_apply_one_pow_mult_le S w hw x
  exact hT.trans (by simpa using prod_max_apply_one_le_mulHeight₁ T (∅ : Finset (FinitePlace F)) x)

/-- The product of the `v.mult`-weighted lower truncated local factors at absolute values lying
over distinct infinite places of `K` is at least the reciprocal relative height of `x ≠ 0`. -/
theorem inv_mulHeight₁_le_prod_min_one_apply_pow_mult_of_liesOver
    (S : Finset (InfinitePlace K)) (w : InfinitePlace K → AbsoluteValue F ℝ)
    (hw : ∀ v ∈ S, (w v).LiesOver v.1) {x : F} (hx : x ≠ 0) :
    (mulHeight₁ x)⁻¹ ≤ ∏ v ∈ S, min 1 (w v x) ^ v.mult := by
  have h := prod_max_apply_one_pow_mult_le_mulHeight₁_of_liesOver S w hw x⁻¹
  simp only [max_inv_eq_inv_min _ hx, inv_pow, Finset.prod_inv_distrib, mulHeight₁_inv] at h
  exact (inv_le_comm₀ (Finset.prod_pos fun v _ ↦ pow_pos (lt_min zero_lt_one ((w v).pos hx)) _)
    (mulHeight₁_pos x)).mp h

/-- At an absolute value above an infinite place `v`, the `v.mult`-weighted upper truncated factor
is at most the relative height in the extension. -/
theorem InfinitePlace.max_apply_one_pow_mult_le_mulHeight₁_of_liesOver (v : InfinitePlace K)
    (w : AbsoluteValue F ℝ) [w.LiesOver v.1] (x : F) :
    max (w x) 1 ^ v.mult ≤ mulHeight₁ x := by
  simpa using prod_max_apply_one_pow_mult_le_mulHeight₁_of_liesOver {v} (fun _ ↦ w)
    (by intro u hu; obtain rfl := Finset.mem_singleton.mp hu; infer_instance) x

/-- An absolute value lying over an infinite place of the base is bounded by the relative height
in the extension. -/
theorem InfinitePlace.max_apply_one_le_mulHeight₁_of_liesOver (v : InfinitePlace K)
    (w : AbsoluteValue F ℝ) [w.LiesOver v.1] (x : F) :
    max (w x) 1 ≤ mulHeight₁ x :=
  (le_self_pow₀ (le_max_right _ _) v.mult_ne_zero).trans
    (v.max_apply_one_pow_mult_le_mulHeight₁_of_liesOver w x)

/-- At an absolute value above an infinite place `v`, the `v.mult`-weighted lower truncated factor
of a nonzero element is at least its reciprocal relative height. -/
theorem InfinitePlace.inv_mulHeight₁_le_min_one_apply_pow_mult_of_liesOver (v : InfinitePlace K)
    (w : AbsoluteValue F ℝ) [w.LiesOver v.1] {x : F} (hx : x ≠ 0) :
    (mulHeight₁ x)⁻¹ ≤ min 1 (w x) ^ v.mult := by
  simpa using inv_mulHeight₁_le_prod_min_one_apply_pow_mult_of_liesOver {v} (fun _ ↦ w)
    (by intro u hu; obtain rfl := Finset.mem_singleton.mp hu; infer_instance) hx

/-- At an absolute value above an infinite place, the lower truncated factor of a nonzero element
is bounded below by its reciprocal relative height. -/
theorem InfinitePlace.inv_mulHeight₁_le_min_one_apply_of_liesOver (v : InfinitePlace K)
    (w : AbsoluteValue F ℝ) [w.LiesOver v.1] {x : F} (hx : x ≠ 0) :
    (mulHeight₁ x)⁻¹ ≤ min 1 (w x) :=
  (v.inv_mulHeight₁_le_min_one_apply_pow_mult_of_liesOver w hx).trans
    (pow_le_of_le_one (by positivity) (min_le_left _ _) v.mult_ne_zero)

end Infinite

section NumberField

variable {K F : Type*} [Field K] [Field F] [NumberField K] [NumberField F] [Algebra K F]

/-- **Truncated fundamental inequality in an extension, upper bound.** For absolute values of `F`
lying over distinct infinite places `Sinf` (weighted by `v.mult`) and distinct finite places
`Sfin` of `K`, the product of the upper truncated local factors is at most `mulHeight₁ x` in `F`. -/
theorem prod_max_apply_one_pow_mult_mul_prod_le_mulHeight₁_of_liesOver
    (Sinf : Finset (InfinitePlace K)) (Sfin : Finset (FinitePlace K))
    (winf : InfinitePlace K → AbsoluteValue F ℝ) (wfin : FinitePlace K → AbsoluteValue F ℝ)
    (hwinf : ∀ v ∈ Sinf, (winf v).LiesOver v.1) (hwfin : ∀ v ∈ Sfin, (wfin v).LiesOver v.1)
    (x : F) :
    (∏ v ∈ Sinf, max (winf v x) 1 ^ v.mult) * ∏ v ∈ Sfin, max (wfin v x) 1 ≤ mulHeight₁ x := by
  classical
  obtain ⟨Tinf, hinf⟩ := exists_finset_prod_max_apply_one_pow_mult_le Sinf winf hwinf x
  obtain ⟨V, t, hV, ht⟩ := exists_injective_finitePlace_rpow_eq_of_liesOver
    (Sfin : Set (FinitePlace K)) (fun v ↦ wfin v.val) (fun v ↦ hwfin v.val v.prop)
  have hfin : ∏ v ∈ Sfin, max (wfin v x) 1 ≤ ∏ v ∈ Sfin.attach.image V, max (v x) 1 := by
    rw [← Finset.prod_attach Sfin, Finset.prod_image hV.injOn]
    refine Finset.prod_le_prod₀ (fun _ _ ↦ by positivity) fun v _ ↦ ?_
    rw [(ht v).2.2, ← Real.one_rpow (t v),
      ← Real.rpow_max (by positivity) zero_le_one (ht v).1.le, Real.one_rpow]
    exact Real.rpow_le_self_of_one_le (le_max_right _ _) (ht v).2.1
  exact (mul_le_mul hinf hfin (Finset.prod_nonneg fun _ _ ↦ by positivity)
    (Finset.prod_nonneg fun _ _ ↦ by positivity)).trans
    (prod_max_apply_one_le_mulHeight₁ Tinf (Sfin.attach.image V) x)

/-- **Truncated fundamental inequality in an extension, lower bound.** For a nonzero `x : F` and
absolute values of `F` lying over distinct infinite places `Sinf` (weighted by `v.mult`) and
distinct finite places `Sfin` of `K`, the product of the lower truncated local factors is at least
`(mulHeight₁ x)⁻¹`. -/
theorem inv_mulHeight₁_le_prod_min_one_apply_pow_mult_mul_prod_of_liesOver
    (Sinf : Finset (InfinitePlace K)) (Sfin : Finset (FinitePlace K))
    (winf : InfinitePlace K → AbsoluteValue F ℝ) (wfin : FinitePlace K → AbsoluteValue F ℝ)
    (hwinf : ∀ v ∈ Sinf, (winf v).LiesOver v.1) (hwfin : ∀ v ∈ Sfin, (wfin v).LiesOver v.1)
    {x : F} (hx : x ≠ 0) :
    (mulHeight₁ x)⁻¹ ≤
      (∏ v ∈ Sinf, min 1 (winf v x) ^ v.mult) * ∏ v ∈ Sfin, min 1 (wfin v x) := by
  have h := prod_max_apply_one_pow_mult_mul_prod_le_mulHeight₁_of_liesOver
    Sinf Sfin winf wfin hwinf hwfin x⁻¹
  simp only [max_inv_eq_inv_min _ hx, inv_pow, Finset.prod_inv_distrib, ← mul_inv,
    mulHeight₁_inv] at h
  have hpos : 0 < (∏ v ∈ Sinf, min 1 (winf v x) ^ v.mult) * ∏ v ∈ Sfin, min 1 (wfin v x) :=
    mul_pos (Finset.prod_pos fun v _ ↦ pow_pos (lt_min zero_lt_one ((winf v).pos hx)) _)
      (Finset.prod_pos fun v _ ↦ lt_min zero_lt_one ((wfin v).pos hx))
  exact (inv_le_comm₀ hpos (mulHeight₁_pos x)).mp h

/-- The product of the upper truncated local factors at absolute values lying over distinct
finite places of the base is at most the relative height in the extension. -/
theorem prod_max_apply_one_le_mulHeight₁_of_liesOver
    (S : Finset (FinitePlace K)) (w : FinitePlace K → AbsoluteValue F ℝ)
    (hw : ∀ v ∈ S, (w v).LiesOver v.1) (x : F) :
    ∏ v ∈ S, max (w v x) 1 ≤ mulHeight₁ x := by
  classical
  simpa using prod_max_apply_one_pow_mult_mul_prod_le_mulHeight₁_of_liesOver
    ∅ S (fun _ ↦ .trivial) w (by simp) hw x

/-- The product of the lower truncated local factors at absolute values lying over distinct
finite places of the base is at least the reciprocal relative height of a nonzero element. -/
theorem inv_mulHeight₁_le_prod_min_one_apply_of_liesOver
    (S : Finset (FinitePlace K)) (w : FinitePlace K → AbsoluteValue F ℝ)
    (hw : ∀ v ∈ S, (w v).LiesOver v.1) {x : F} (hx : x ≠ 0) :
    (mulHeight₁ x)⁻¹ ≤ ∏ v ∈ S, min 1 (w v x) := by
  classical
  simpa using inv_mulHeight₁_le_prod_min_one_apply_pow_mult_mul_prod_of_liesOver
    ∅ S (fun _ ↦ .trivial) w (by simp) hw hx

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

/-- An absolute value of `F` lying over any infinite or finite place of `K` is bounded above by
`mulHeight₁ x`. -/
theorem max_apply_one_le_mulHeight₁_of_liesOver {v : AbsoluteValue K ℝ}
    (hv : IsInfinitePlace v ∨ IsFinitePlace v)
    (w : AbsoluteValue F ℝ) [w.LiesOver v] (x : F) :
    max (w x) 1 ≤ mulHeight₁ x := by
  rcases hv with hinf | hfin
  · obtain ⟨v', rfl⟩ := (isInfinitePlace_iff v).mp hinf
    exact v'.max_apply_one_le_mulHeight₁_of_liesOver w x
  · obtain ⟨v', rfl⟩ := (isFinitePlace_iff v).mp hfin
    exact v'.max_apply_one_le_mulHeight₁_of_liesOver w x

/-- At an absolute value of `F` lying over any infinite or finite place of `K`, `min 1 (w x)` for
`x ≠ 0` is bounded below by `(mulHeight₁ x)⁻¹`. -/
theorem inv_mulHeight₁_le_min_one_apply_of_liesOver {v : AbsoluteValue K ℝ}
    (hv : IsInfinitePlace v ∨ IsFinitePlace v)
    (w : AbsoluteValue F ℝ) [w.LiesOver v] {x : F} (hx : x ≠ 0) :
    (mulHeight₁ x)⁻¹ ≤ min 1 (w x) := by
  rcases hv with hinf | hfin
  · obtain ⟨v', rfl⟩ := (isInfinitePlace_iff v).mp hinf
    exact v'.inv_mulHeight₁_le_min_one_apply_of_liesOver w hx
  · obtain ⟨v', rfl⟩ := (isFinitePlace_iff v).mp hfin
    exact v'.inv_mulHeight₁_le_min_one_apply_of_liesOver w hx

end NumberField

end NumberField
