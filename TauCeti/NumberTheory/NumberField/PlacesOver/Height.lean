/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.PlacesOver.FinitePlace
public import TauCeti.NumberTheory.NumberField.PlacesOver.InfinitePlace
public import TauCeti.NumberTheory.Height.FundamentalInequality

/-!
# Height bounds above places of a subfield

Absolute values of a number field extension `F / K` lying over distinct places of `K` give local
factors whose product is bounded by the relative height `Height.mulHeight₁` in `F`:

* Above distinct infinite places `v ∈ Sinf`, the absolute values `w v` are distinct infinite places
  `W v` of `F` (`NumberField.exists_injective_infinitePlace_eq_of_liesOver`) whose multiplicities
  satisfy `v.mult ≤ (W v).mult` (`NumberField.InfinitePlace.mult_comap_le`), so
  `max (w v x) 1 ^ v.mult ≤ max (W v x) 1 ^ (W v).mult`.
* Above distinct finite places `v ∈ Sfin`, the absolute values `w v` are positive roots of distinct
  finite places `V v` of `F` with exponents at most one
  (`NumberField.exists_injective_finitePlace_rpow_eq_of_liesOver`), and taking such a root moves
  both truncated factors toward one.

Combining the two regimes gives the fundamental inequality in `F` for local factors indexed by
places of `K` (`NumberField.prod_max_apply_one_pow_mult_mul_prod_le_mulHeight₁_of_liesOver`,
`NumberField.inv_mulHeight₁_le_prod_min_one_apply_pow_mult_mul_prod_of_liesOver`), from which the
infinite-only, finite-only, and single-place bounds follow.

## References

* E. Bombieri and W. Gubler, *Heights in Diophantine Geometry* (2006), §§1.3 and 1.5.
-/

public section

open Height

namespace NumberField

private theorem max_apply_inv_one {F : Type*} [Field F] (u : AbsoluteValue F ℝ) {x : F}
    (hx : x ≠ 0) : max (u x⁻¹) 1 = (min 1 (u x))⁻¹ := by
  rw [map_inv₀]
  rcases le_total (u x) 1 with hle | hle
  · rw [min_eq_right hle, max_eq_left ((one_le_inv₀ (u.pos hx)).mpr hle)]
  · rw [min_eq_left hle, inv_one, max_eq_right ((inv_le_one₀ (u.pos hx)).mpr hle)]

section InfinitePlacesOnly

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

private theorem prod_infinitePlace_max_le
    (S : Finset (InfinitePlace K)) (w : InfinitePlace K → AbsoluteValue F ℝ)
    (hw : ∀ v ∈ S, (w v).LiesOver v.1) (x : F) :
    ∃ T : Finset (InfinitePlace F),
      ∏ v ∈ S, max (w v x) 1 ^ v.mult ≤ ∏ u ∈ T, max (u x) 1 ^ u.mult := by
  classical
  obtain ⟨W, hW, hW_spec⟩ := exists_injective_infinitePlace_eq_of_liesOver
    (S : Set (InfinitePlace K)) (fun v ↦ w v.val) (fun v ↦ hw v.val v.prop)
  have hlocal (v : ↥S) : max (w v.val x) 1 ^ v.val.mult ≤ max (W v x) 1 ^ (W v).mult := by
    let := (hW_spec v).1
    have hmult : v.val.mult ≤ (W v).mult := by
      rw [← InfinitePlace.LiesOver.comap_eq (W v) v.val]
      exact InfinitePlace.mult_comap_le _ _
    have hwx : w v.val x = W v x := by
      rw [← (hW_spec v).2, InfinitePlace.coe_apply]
    rw [hwx]
    exact pow_le_pow_right₀ (le_max_right _ _) hmult
  refine ⟨S.attach.image W, ?_⟩
  calc
    ∏ v ∈ S, max (w v x) 1 ^ v.mult = ∏ v ∈ S.attach, max (w v.val x) 1 ^ v.val.mult :=
      (Finset.prod_attach S _).symm
    _ ≤ ∏ v ∈ S.attach, max (W v x) 1 ^ (W v).mult :=
      Finset.prod_le_prod₀ (fun _ _ ↦ by positivity) (fun v _ ↦ hlocal v)
    _ = ∏ u ∈ S.attach.image W, max (u x) 1 ^ u.mult :=
      (Finset.prod_image (f := fun u : InfinitePlace F ↦ max (u x) 1 ^ u.mult)
        (s := S.attach) hW.injOn).symm

variable [NumberField F]

/-- The product of the upper truncated local factors at absolute values lying over distinct infinite
places of the base, weighted by the base multiplicities, is at most the relative height in `F`. -/
theorem InfinitePlace.prod_max_apply_one_pow_mult_le_mulHeight₁_of_liesOver
    (S : Finset (InfinitePlace K)) (w : InfinitePlace K → AbsoluteValue F ℝ)
    (hw : ∀ v ∈ S, (w v).LiesOver v.1) (x : F) :
    ∏ v ∈ S, max (w v x) 1 ^ v.mult ≤ mulHeight₁ x := by
  obtain ⟨T, hT⟩ := prod_infinitePlace_max_le S w hw x
  exact hT.trans <| by simpa using prod_max_apply_one_le_mulHeight₁ T (∅ : Finset (FinitePlace F)) x

/-- The product of the lower truncated local factors at absolute values lying over distinct infinite
places of the base, weighted by the base multiplicities, is at least the reciprocal relative height
of a nonzero element of `F`. -/
theorem InfinitePlace.inv_mulHeight₁_le_prod_min_one_apply_pow_mult_of_liesOver
    (S : Finset (InfinitePlace K)) (w : InfinitePlace K → AbsoluteValue F ℝ)
    (hw : ∀ v ∈ S, (w v).LiesOver v.1) {x : F} (hx : x ≠ 0) :
    (mulHeight₁ x)⁻¹ ≤ ∏ v ∈ S, min 1 (w v x) ^ v.mult := by
  have h := InfinitePlace.prod_max_apply_one_pow_mult_le_mulHeight₁_of_liesOver S w hw x⁻¹
  simp only [max_apply_inv_one _ hx, inv_pow, Finset.prod_inv_distrib, mulHeight₁_inv] at h
  exact (inv_le_comm₀ (Finset.prod_pos fun v _ ↦ pow_pos (lt_min zero_lt_one ((w v).pos hx)) _)
    (mulHeight₁_pos x)).mp h

/-- At an absolute value lying over an infinite place `v`, the upper truncated factor weighted by
`v.mult` is at most the relative height in `F`. -/
theorem InfinitePlace.max_apply_one_pow_mult_le_mulHeight₁_of_liesOver (v : InfinitePlace K)
    (w : AbsoluteValue F ℝ) [w.LiesOver v.1] (x : F) :
    max (w x) 1 ^ v.mult ≤ mulHeight₁ x := by
  simpa using InfinitePlace.prod_max_apply_one_pow_mult_le_mulHeight₁_of_liesOver {v} (fun _ ↦ w)
    (by intro u hu; obtain rfl := Finset.mem_singleton.mp hu; infer_instance) x

/-- An absolute value lying over an infinite place of the base is bounded by the relative height in
`F`. -/
theorem InfinitePlace.max_apply_one_le_mulHeight₁_of_liesOver (v : InfinitePlace K)
    (w : AbsoluteValue F ℝ) [w.LiesOver v.1] (x : F) :
    max (w x) 1 ≤ mulHeight₁ x :=
  (le_self_pow₀ (le_max_right _ _) v.mult_ne_zero).trans
    (v.max_apply_one_pow_mult_le_mulHeight₁_of_liesOver w x)

/-- At an absolute value above an infinite place `v`, the lower truncated factor of a nonzero
element weighted by `v.mult` is bounded below by its reciprocal relative height. -/
theorem InfinitePlace.inv_mulHeight₁_le_min_one_apply_pow_mult_of_liesOver (v : InfinitePlace K)
    (w : AbsoluteValue F ℝ) [w.LiesOver v.1] {x : F} (hx : x ≠ 0) :
    (mulHeight₁ x)⁻¹ ≤ min 1 (w x) ^ v.mult := by
  simpa using InfinitePlace.inv_mulHeight₁_le_prod_min_one_apply_pow_mult_of_liesOver {v}
    (fun _ ↦ w) (by intro u hu; obtain rfl := Finset.mem_singleton.mp hu; infer_instance) hx

/-- At an absolute value above an infinite place, the lower truncated factor of a nonzero element is
bounded below by its reciprocal relative height. -/
theorem InfinitePlace.inv_mulHeight₁_le_min_one_apply_of_liesOver (v : InfinitePlace K)
    (w : AbsoluteValue F ℝ) [w.LiesOver v.1] {x : F} (hx : x ≠ 0) :
    (mulHeight₁ x)⁻¹ ≤ min 1 (w x) :=
  (v.inv_mulHeight₁_le_min_one_apply_pow_mult_of_liesOver w hx).trans <|
    pow_le_of_le_one (le_min zero_le_one (w.nonneg _)) (min_le_left _ _) v.mult_ne_zero

end InfinitePlacesOnly

variable {K F : Type*} [Field K] [Field F] [NumberField K] [NumberField F] [Algebra K F]

private theorem prod_finitePlace_max_le
    (S : Finset (FinitePlace K)) (w : FinitePlace K → AbsoluteValue F ℝ)
    (hw : ∀ v ∈ S, (w v).LiesOver v.1) (x : F) :
    ∃ T : Finset (FinitePlace F),
      ∏ v ∈ S, max (w v x) 1 ≤ ∏ u ∈ T, max (u x) 1 := by
  classical
  obtain ⟨V, t, hV, ht⟩ := exists_injective_finitePlace_rpow_eq_of_liesOver
    (S : Set (FinitePlace K)) (fun v ↦ w v.val) (fun v ↦ hw v.val v.prop)
  have hlocal (v : ↥S) : max (w v.val x) 1 ≤ max (V v x) 1 := by
    calc
      max (w v.val x) 1 = max (V v x) 1 ^ t v := by
        rw [(ht v).2.2, Real.rpow_max (by positivity) zero_le_one (ht v).1.le,
          Real.one_rpow]
      _ ≤ max (V v x) 1 := Real.rpow_le_self_of_one_le (le_max_right _ _) (ht v).2.1
  refine ⟨S.attach.image V, ?_⟩
  calc
    ∏ v ∈ S, max (w v x) 1 = ∏ v ∈ S.attach, max (w v.val x) 1 :=
      (Finset.prod_attach S _).symm
    _ ≤ ∏ v ∈ S.attach, max (V v x) 1 := Finset.prod_le_prod₀
      (fun _ _ ↦ by positivity) (fun v _ ↦ hlocal v)
    _ = ∏ v ∈ S.attach.image V, max (v x) 1 :=
      (Finset.prod_image (f := fun v : FinitePlace F ↦ max (v x) 1)
        (s := S.attach) hV.injOn).symm

/-- **Combined height upper bound above places of the base.** For finite sets `Sinf` of infinite
places and `Sfin` of finite places of `K` and absolute values of `F` lying over them, the product of
the upper truncated local factors, weighted by `mult` at the infinite places, is at most the
relative height in `F`. -/
theorem prod_max_apply_one_pow_mult_mul_prod_le_mulHeight₁_of_liesOver
    (Sinf : Finset (InfinitePlace K)) (Sfin : Finset (FinitePlace K))
    (wInf : InfinitePlace K → AbsoluteValue F ℝ) (wFin : FinitePlace K → AbsoluteValue F ℝ)
    (hwInf : ∀ v ∈ Sinf, (wInf v).LiesOver v.1) (hwFin : ∀ v ∈ Sfin, (wFin v).LiesOver v.1)
    (x : F) :
    (∏ v ∈ Sinf, max (wInf v x) 1 ^ v.mult) * (∏ v ∈ Sfin, max (wFin v x) 1) ≤ mulHeight₁ x := by
  obtain ⟨Tinf, hTinf⟩ := prod_infinitePlace_max_le Sinf wInf hwInf x
  obtain ⟨Tfin, hTfin⟩ := prod_finitePlace_max_le Sfin wFin hwFin x
  exact (mul_le_mul hTinf hTfin (Finset.prod_nonneg fun _ _ ↦ by positivity)
    (Finset.prod_nonneg fun _ _ ↦ by positivity)).trans
    (prod_max_apply_one_le_mulHeight₁ Tinf Tfin x)

/-- **Combined height lower bound above places of the base.** For finite sets `Sinf` of infinite
places and `Sfin` of finite places of `K` and absolute values of `F` lying over them, the product of
the lower truncated local factors of a nonzero element `x : F`, weighted by `mult` at the infinite
places, is at least `(mulHeight₁ x)⁻¹`. -/
theorem inv_mulHeight₁_le_prod_min_one_apply_pow_mult_mul_prod_of_liesOver
    (Sinf : Finset (InfinitePlace K)) (Sfin : Finset (FinitePlace K))
    (wInf : InfinitePlace K → AbsoluteValue F ℝ) (wFin : FinitePlace K → AbsoluteValue F ℝ)
    (hwInf : ∀ v ∈ Sinf, (wInf v).LiesOver v.1) (hwFin : ∀ v ∈ Sfin, (wFin v).LiesOver v.1)
    {x : F} (hx : x ≠ 0) :
    (mulHeight₁ x)⁻¹ ≤
      (∏ v ∈ Sinf, min 1 (wInf v x) ^ v.mult) * (∏ v ∈ Sfin, min 1 (wFin v x)) := by
  have h := prod_max_apply_one_pow_mult_mul_prod_le_mulHeight₁_of_liesOver
    Sinf Sfin wInf wFin hwInf hwFin x⁻¹
  simp only [max_apply_inv_one _ hx, inv_pow, Finset.prod_inv_distrib, ← mul_inv,
    mulHeight₁_inv] at h
  have hpos :
      0 < (∏ v ∈ Sinf, min 1 (wInf v x) ^ v.mult) * ∏ v ∈ Sfin, min 1 (wFin v x) :=
    mul_pos (Finset.prod_pos fun v _ ↦ pow_pos (lt_min zero_lt_one ((wInf v).pos hx)) _)
      (Finset.prod_pos fun v _ ↦ lt_min zero_lt_one ((wFin v).pos hx))
  exact (inv_le_comm₀ hpos (mulHeight₁_pos x)).mp h

/-- The product of the upper truncated local factors at absolute values lying over distinct
finite places of the base is at most the relative height in the extension. -/
theorem prod_max_apply_one_le_mulHeight₁_of_liesOver
    (S : Finset (FinitePlace K)) (w : FinitePlace K → AbsoluteValue F ℝ)
    (hw : ∀ v ∈ S, (w v).LiesOver v.1) (x : F) :
    ∏ v ∈ S, max (w v x) 1 ≤ mulHeight₁ x := by
  simpa using prod_max_apply_one_pow_mult_mul_prod_le_mulHeight₁_of_liesOver
    (∅ : Finset (InfinitePlace K)) S (fun _ ↦ (Classical.arbitrary (InfinitePlace F)).1) w
    (by simp) hw x

/-- The product of the lower truncated local factors at absolute values lying over distinct
finite places of the base is at least the reciprocal relative height of a nonzero element. -/
theorem inv_mulHeight₁_le_prod_min_one_apply_of_liesOver
    (S : Finset (FinitePlace K)) (w : FinitePlace K → AbsoluteValue F ℝ)
    (hw : ∀ v ∈ S, (w v).LiesOver v.1) {x : F} (hx : x ≠ 0) :
    (mulHeight₁ x)⁻¹ ≤ ∏ v ∈ S, min 1 (w v x) := by
  simpa using inv_mulHeight₁_le_prod_min_one_apply_pow_mult_mul_prod_of_liesOver
    (∅ : Finset (InfinitePlace K)) S (fun _ ↦ (Classical.arbitrary (InfinitePlace F)).1) w
    (by simp) hw hx

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

/-- An absolute value lying over any place (infinite or finite) of the base is bounded by the
relative height in the extension. -/
theorem max_apply_one_le_mulHeight₁_of_liesOver {v : AbsoluteValue K ℝ}
    (hv : IsInfinitePlace v ∨ IsFinitePlace v) (w : AbsoluteValue F ℝ) [w.LiesOver v] (x : F) :
    max (w x) 1 ≤ mulHeight₁ x := by
  rcases hv with hinf | hfin
  · obtain ⟨v', rfl⟩ := (isInfinitePlace_iff v).mp hinf
    exact v'.max_apply_one_le_mulHeight₁_of_liesOver w x
  · obtain ⟨v', rfl⟩ := (isFinitePlace_iff v).mp hfin
    exact v'.max_apply_one_le_mulHeight₁_of_liesOver w x

/-- At an absolute value lying over any place (infinite or finite) of the base, the lower truncated
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

end NumberField
