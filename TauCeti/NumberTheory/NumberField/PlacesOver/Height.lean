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

For a number field `F` over a subfield `K`, absolute values of `F` chosen above distinct infinite
places `Sinf` (weighted by `v.mult`) and distinct finite places `Sfin` of `K` satisfy
local-to-global height bounds in terms of the relative height `Height.mulHeight₁` on `F`:

* `NumberField.prod_max_apply_one_mul_le_mulHeight₁_of_liesOver`:
  `(∏ v ∈ Sinf, max (winf v x) 1 ^ v.mult) * ∏ v ∈ Sfin, max (wfin v x) 1 ≤ mulHeight₁ x`.
* `NumberField.inv_mulHeight₁_le_prod_min_one_apply_mul_of_liesOver`: for `x ≠ 0`,
  `(mulHeight₁ x)⁻¹ ≤ (∏ v ∈ Sinf, min 1 (winf v x) ^ v.mult) * ∏ v ∈ Sfin, min 1 (wfin v x)`.

Specializing gives the corresponding bounds over a finite set of infinite places alone, over a
finite set of finite places alone, and at a single infinite, finite, or combined place (`max (w x) 1
≤ mulHeight₁ x` and, for `x ≠ 0`, `(mulHeight₁ x)⁻¹ ≤ min 1 (w x)`).

## References

* E. Bombieri and W. Gubler, *Heights in Diophantine Geometry* (2006), §§1.3 and 1.5.
-/

public section

open Height

namespace NumberField

section Combined

variable {K F : Type*} [Field K] [Field F] [NumberField K] [NumberField F] [Algebra K F]

/-- The product of the upper truncated local factors at absolute values chosen above distinct
infinite places `Sinf` (weighted by `v.mult`) and distinct finite places `Sfin` of the base is at
most the relative height in the extension. -/
theorem prod_max_apply_one_mul_le_mulHeight₁_of_liesOver
    (Sinf : Finset (InfinitePlace K)) (Sfin : Finset (FinitePlace K))
    (winf : InfinitePlace K → AbsoluteValue F ℝ) (wfin : FinitePlace K → AbsoluteValue F ℝ)
    (hwinf : ∀ v ∈ Sinf, (winf v).LiesOver v.1) (hwfin : ∀ v ∈ Sfin, (wfin v).LiesOver v.1)
    (x : F) :
    (∏ v ∈ Sinf, max (winf v x) 1 ^ v.mult) * ∏ v ∈ Sfin, max (wfin v x) 1 ≤ mulHeight₁ x := by
  classical
  obtain ⟨W, hW, hWeq⟩ := exists_injective_infinitePlace_eq_of_liesOver
    (Sinf : Set (InfinitePlace K)) (fun v ↦ winf v.val) (fun v ↦ hwinf v.val v.prop)
  obtain ⟨V, t, hV, ht⟩ := exists_injective_finitePlace_rpow_eq_of_liesOver
    (Sfin : Set (FinitePlace K)) (fun v ↦ wfin v.val) (fun v ↦ hwfin v.val v.prop)
  have hlocalInf (v : ↥Sinf) :
      max (winf v.val x) 1 ^ v.val.mult ≤ max (W v x) 1 ^ (W v).mult := by
    let := (hWeq v).1
    have hval : winf v.val x = W v x := by
      rw [← (hWeq v).2, InfinitePlace.coe_apply]
    have hmult : v.val.mult ≤ (W v).mult := by
      rw [← InfinitePlace.LiesOver.comap_eq (W v) v.val]
      exact InfinitePlace.mult_comap_le (algebraMap K F) (W v)
    rw [hval]
    exact pow_le_pow_right₀ (le_max_right _ _) hmult
  have hlocalFin (v : ↥Sfin) : max (wfin v.val x) 1 ≤ max (V v x) 1 := by
    calc
      max (wfin v.val x) 1 = max (V v x) 1 ^ t v := by
        rw [(ht v).2.2, Real.rpow_max (by positivity) zero_le_one (ht v).1.le, Real.one_rpow]
      _ ≤ max (V v x) 1 := Real.rpow_le_self_of_one_le (le_max_right _ _) (ht v).2.1
  have hprodInf :
      ∏ v ∈ Sinf, max (winf v x) 1 ^ v.mult ≤
        ∏ w ∈ Sinf.attach.image W, max (w x) 1 ^ w.mult := by
    calc
      ∏ v ∈ Sinf, max (winf v x) 1 ^ v.mult =
          ∏ v ∈ Sinf.attach, max (winf v.val x) 1 ^ v.val.mult := (Finset.prod_attach Sinf _).symm
      _ ≤ ∏ v ∈ Sinf.attach, max (W v x) 1 ^ (W v).mult :=
          Finset.prod_le_prod₀ (fun _ _ ↦ by positivity) (fun v _ ↦ hlocalInf v)
      _ = ∏ w ∈ Sinf.attach.image W, max (w x) 1 ^ w.mult :=
          (Finset.prod_image (f := fun w : InfinitePlace F ↦ max (w x) 1 ^ w.mult)
            (s := Sinf.attach) hW.injOn).symm
  have hprodFin :
      ∏ v ∈ Sfin, max (wfin v x) 1 ≤ ∏ v ∈ Sfin.attach.image V, max (v x) 1 := by
    calc
      ∏ v ∈ Sfin, max (wfin v x) 1 = ∏ v ∈ Sfin.attach, max (wfin v.val x) 1 :=
          (Finset.prod_attach Sfin _).symm
      _ ≤ ∏ v ∈ Sfin.attach, max (V v x) 1 :=
          Finset.prod_le_prod₀ (fun _ _ ↦ by positivity) (fun v _ ↦ hlocalFin v)
      _ = ∏ v ∈ Sfin.attach.image V, max (v x) 1 :=
          (Finset.prod_image (f := fun v : FinitePlace F ↦ max (v x) 1)
            (s := Sfin.attach) hV.injOn).symm
  exact (mul_le_mul hprodInf hprodFin
    (Finset.prod_nonneg fun _ _ ↦ by positivity) (by positivity)).trans
    (prod_max_apply_one_le_mulHeight₁ (Sinf.attach.image W) (Sfin.attach.image V) x)

/-- The product of the lower truncated local factors at absolute values chosen above distinct
infinite places `Sinf` (weighted by `v.mult`) and distinct finite places `Sfin` of the base is at
least the reciprocal relative height of a nonzero element in the extension. -/
theorem inv_mulHeight₁_le_prod_min_one_apply_mul_of_liesOver
    (Sinf : Finset (InfinitePlace K)) (Sfin : Finset (FinitePlace K))
    (winf : InfinitePlace K → AbsoluteValue F ℝ) (wfin : FinitePlace K → AbsoluteValue F ℝ)
    (hwinf : ∀ v ∈ Sinf, (winf v).LiesOver v.1) (hwfin : ∀ v ∈ Sfin, (wfin v).LiesOver v.1)
    {x : F} (hx : x ≠ 0) :
    (mulHeight₁ x)⁻¹ ≤
      (∏ v ∈ Sinf, min 1 (winf v x) ^ v.mult) * ∏ v ∈ Sfin, min 1 (wfin v x) := by
  have h := prod_max_apply_one_mul_le_mulHeight₁_of_liesOver Sinf Sfin winf wfin hwinf hwfin x⁻¹
  have hinv (u : AbsoluteValue F ℝ) : max (u x⁻¹) 1 = (min 1 (u x))⁻¹ := by
    rw [map_inv₀]
    rcases le_total (u x) 1 with hle | hle
    · rw [min_eq_right hle, max_eq_left ((one_le_inv₀ (u.pos hx)).mpr hle)]
    · rw [min_eq_left hle, inv_one, max_eq_right ((inv_le_one₀ (u.pos hx)).mpr hle)]
  simp only [hinv, inv_pow, Finset.prod_inv_distrib, ← mul_inv, mulHeight₁_inv] at h
  have hpos :
      0 < (∏ v ∈ Sinf, min 1 (winf v x) ^ v.mult) * ∏ v ∈ Sfin, min 1 (wfin v x) :=
    mul_pos
      (Finset.prod_pos fun v _ ↦ pow_pos (lt_min zero_lt_one ((winf v).pos hx)) _)
      (Finset.prod_pos fun v _ ↦ lt_min zero_lt_one ((wfin v).pos hx))
  exact (inv_le_comm₀ hpos (mulHeight₁_pos x)).mp h

end Combined

section InfinitePlace

variable {K F : Type*} [Field K] [Field F] [NumberField F] [Algebra K F]

/-- The product of the upper truncated local factors at absolute values lying over distinct
infinite places of the base, weighted by `v.mult`, is at most the relative height in the
extension. -/
theorem prod_max_apply_one_pow_mult_le_mulHeight₁_of_liesOver
    (S : Finset (InfinitePlace K)) (w : InfinitePlace K → AbsoluteValue F ℝ)
    (hw : ∀ v ∈ S, (w v).LiesOver v.1) (x : F) :
    ∏ v ∈ S, max (w v x) 1 ^ v.mult ≤ mulHeight₁ x := by
  classical
  have : CharZero K := (algebraMap K F).charZero
  have : NumberField K := NumberField.of_tower ℚ F K
  simpa using prod_max_apply_one_mul_le_mulHeight₁_of_liesOver S ∅ w
    (fun _ ↦ AbsoluteValue.trivial) hw (by simp) x

/-- The product of the lower truncated local factors at absolute values lying over distinct
infinite places of the base, weighted by `v.mult`, is at least the reciprocal relative height of a
nonzero element. -/
theorem inv_mulHeight₁_le_prod_min_one_apply_pow_mult_of_liesOver
    (S : Finset (InfinitePlace K)) (w : InfinitePlace K → AbsoluteValue F ℝ)
    (hw : ∀ v ∈ S, (w v).LiesOver v.1) {x : F} (hx : x ≠ 0) :
    (mulHeight₁ x)⁻¹ ≤ ∏ v ∈ S, min 1 (w v x) ^ v.mult := by
  classical
  have : CharZero K := (algebraMap K F).charZero
  have : NumberField K := NumberField.of_tower ℚ F K
  simpa using inv_mulHeight₁_le_prod_min_one_apply_mul_of_liesOver S ∅ w
    (fun _ ↦ AbsoluteValue.trivial) hw (by simp) hx

/-- At an absolute value lying over an infinite place `v` of the base, `max (w x) 1 ^ v.mult` is
at most the relative height in the extension. -/
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

/-- At an absolute value above an infinite place `v` of the base, `min 1 (w x) ^ v.mult` for a
nonzero element is bounded below by its reciprocal relative height. -/
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
    (pow_le_of_le_one (le_min zero_le_one (w.nonneg x)) (min_le_left _ _) v.mult_ne_zero)

end InfinitePlace

section FiniteAndCombined

variable {K F : Type*} [Field K] [Field F] [NumberField K] [NumberField F] [Algebra K F]

/-- The product of the upper truncated local factors at absolute values lying over distinct
finite places of the base is at most the relative height in the extension. -/
theorem prod_max_apply_one_le_mulHeight₁_of_liesOver
    (S : Finset (FinitePlace K)) (w : FinitePlace K → AbsoluteValue F ℝ)
    (hw : ∀ v ∈ S, (w v).LiesOver v.1) (x : F) :
    ∏ v ∈ S, max (w v x) 1 ≤ mulHeight₁ x := by
  classical
  simpa using prod_max_apply_one_mul_le_mulHeight₁_of_liesOver ∅ S
    (fun _ ↦ AbsoluteValue.trivial) w (by simp) hw x

/-- The product of the lower truncated local factors at absolute values lying over distinct
finite places of the base is at least the reciprocal relative height of a nonzero element. -/
theorem inv_mulHeight₁_le_prod_min_one_apply_of_liesOver
    (S : Finset (FinitePlace K)) (w : FinitePlace K → AbsoluteValue F ℝ)
    (hw : ∀ v ∈ S, (w v).LiesOver v.1) {x : F} (hx : x ≠ 0) :
    (mulHeight₁ x)⁻¹ ≤ ∏ v ∈ S, min 1 (w v x) := by
  classical
  simpa using inv_mulHeight₁_le_prod_min_one_apply_mul_of_liesOver ∅ S
    (fun _ ↦ AbsoluteValue.trivial) w (by simp) hw hx

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

/-- An absolute value of `F` lying over any infinite or finite place of `K` is bounded above by the
relative height in `F`. -/
theorem max_apply_one_le_mulHeight₁_of_liesOver {v : AbsoluteValue K ℝ}
    (hv : IsInfinitePlace v ∨ IsFinitePlace v) (w : AbsoluteValue F ℝ) [w.LiesOver v] (x : F) :
    max (w x) 1 ≤ mulHeight₁ x := by
  rcases hv with hinf | hfin
  · obtain ⟨v', rfl⟩ := (isInfinitePlace_iff v).mp hinf
    exact v'.max_apply_one_le_mulHeight₁_of_liesOver w x
  · obtain ⟨v', rfl⟩ := (isFinitePlace_iff v).mp hfin
    exact v'.max_apply_one_le_mulHeight₁_of_liesOver w x

/-- At an absolute value of `F` lying over any infinite or finite place of `K`, the lower truncated
factor of a nonzero element is bounded below by its reciprocal relative height. -/
theorem inv_mulHeight₁_le_min_one_apply_of_liesOver {v : AbsoluteValue K ℝ}
    (hv : IsInfinitePlace v ∨ IsFinitePlace v) (w : AbsoluteValue F ℝ) [w.LiesOver v]
    {x : F} (hx : x ≠ 0) :
    (mulHeight₁ x)⁻¹ ≤ min 1 (w x) := by
  rcases hv with hinf | hfin
  · obtain ⟨v', rfl⟩ := (isInfinitePlace_iff v).mp hinf
    exact v'.inv_mulHeight₁_le_min_one_apply_of_liesOver w hx
  · obtain ⟨v', rfl⟩ := (isFinitePlace_iff v).mp hfin
    exact v'.inv_mulHeight₁_le_min_one_apply_of_liesOver w hx

end FiniteAndCombined

end NumberField
