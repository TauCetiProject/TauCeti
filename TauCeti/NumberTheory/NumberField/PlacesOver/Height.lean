/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.PlacesOver.FinitePlace
public import TauCeti.NumberTheory.Height.FundamentalInequality
import TauCeti.NumberTheory.Height.NumberField
import TauCeti.NumberTheory.NumberField.PlacesOver.InfinitePlace

/-!
# Height bounds above places, and Liouville's inequality

Let `F/K` be an extension of number fields. Choose finite sets `Sinf` of infinite places and
`Sfin` of finite places of `K`, and at each such place `v` an absolute value `w v` of `F` lying
over `v`. The local factors at these absolute values satisfy the fundamental inequality of `F`:

```text
(∏ v ∈ Sinf, max (w v x) 1 ^ mult v) * ∏ v ∈ Sfin, max (w v x) 1 ≤ mulHeight₁ x,
```

and the corresponding lower bound by `(mulHeight₁ x)⁻¹` for the factors `min 1 (w v x)` of a
nonzero `x`, with the relative height of `F`. The absolute values need not themselves be places
of `F`. Above an infinite place `w v` is an infinite place of `F`
(`NumberField.isInfinitePlace_of_liesOver`) whose multiplicity is at least that of `v`. Above a
finite place it is a positive root, with exponent at most one, of a finite place of `F`. Lowering
the multiplicity from that of the place of `F` to that of `v`, or taking such a root, only moves a
truncated factor toward one, and absolute values over distinct places of `K` come from distinct
places of `F`, so each bound follows from the fundamental inequality of `F`.

**Liouville's inequality over a number field** (`NumberField.inv_le_prod_min_one_sub`) is the
lower bound at `x = β - α` for `α ∈ F` and `β ∈ K`, with the height of `β - α` bounded by
`2 ^ [F : ℚ] H(α) H(β) ^ [F : K]`, the height of `β` over `F` being its height over `K` raised
to `[F : K]`. It is the local step of the proofs of Roth's theorem and of the Subspace Theorem: a
point of `K` cannot approximate an algebraic number `α ≠ β` better, over finitely many places,
than a power of its height allows.

## Main results

* `NumberField.prod_max_apply_one_le_mulHeight₁_of_liesOver` and
  `NumberField.inv_mulHeight₁_le_prod_min_one_apply_of_liesOver`: the fundamental inequality at
  absolute values lying over finitely many places of the base.
* `NumberField.InfinitePlace.max_apply_one_le_mulHeight₁_of_liesOver`,
  `NumberField.FinitePlace.max_apply_one_le_mulHeight₁_of_liesOver` and their lower-bound
  companions: the bounds at a single absolute value over a place.
* `NumberField.inv_le_prod_min_one_sub`: Liouville's inequality over a number field.

## References

* E. Bombieri and W. Gubler, *Heights in Diophantine Geometry* (2006), §§1.3 and 1.5, the
  fundamental inequality (1.8), and Theorem 1.5.21 (Liouville's inequality).
-/

public section

open Height Module

namespace NumberField

variable {K F : Type*} [Field K] [Field F] [NumberField K] [NumberField F] [Algebra K F]

variable (Sinf : Finset (InfinitePlace K)) (Sfin : Finset (FinitePlace K))
  (w : AbsoluteValue K ℝ → AbsoluteValue F ℝ)

/-- **The fundamental inequality above places of the base**, upper bound: the truncated local
factors `max (w v x) 1` at absolute values lying over distinct places of the base, weighted by
`mult v` above the infinite places, multiply to at most the relative height in the
extension. -/
theorem prod_max_apply_one_le_mulHeight₁_of_liesOver
    (hinf : ∀ v ∈ Sinf, (w v.1).LiesOver v.1) (hfin : ∀ v ∈ Sfin, (w v.1).LiesOver v.1)
    (x : F) :
    (∏ v ∈ Sinf, max (w v.1 x) 1 ^ v.mult) * ∏ v ∈ Sfin, max (w v.1 x) 1 ≤ mulHeight₁ x := by
  classical
  obtain ⟨W, hW, hWw⟩ := exists_injective_infinitePlace_eq_of_liesOver
    (Sinf : Set (InfinitePlace K)) (fun v ↦ w v.val.1) (fun v ↦ hinf v.val v.prop)
  obtain ⟨V, t, hV, ht⟩ := exists_injective_finitePlace_rpow_eq_of_liesOver
    (Sfin : Set (FinitePlace K)) (fun v ↦ w v.val.1) (fun v ↦ hfin v.val v.prop)
  -- Above an infinite place, the multiplicity can only go up.
  have hinfLocal (v : ↥Sinf) : max (w v.val.1 x) 1 ^ v.val.mult ≤ max (W v x) 1 ^ (W v).mult := by
    rw [InfinitePlace.coe_apply, (hWw v).1]
    exact pow_le_pow_right₀ (le_max_right _ _) (hWw v).2
  -- Above a finite place, a root with exponent at most one moves the factor toward one.
  have hfinLocal (v : ↥Sfin) : max (w v.val.1 x) 1 ≤ max (V v x) 1 := by
    calc
      max (w v.val.1 x) 1 = max (V v x) 1 ^ t v := by
        rw [(ht v).2.2, Real.rpow_max (by positivity) zero_le_one (ht v).1.le,
          Real.one_rpow]
      _ ≤ max (V v x) 1 := Real.rpow_le_self_of_one_le (le_max_right _ _) (ht v).2.1
  have hinf' : ∏ v ∈ Sinf, max (w v.1 x) 1 ^ v.mult ≤
      ∏ u ∈ Sinf.attach.image W, max (u x) 1 ^ u.mult := by
    rw [Finset.prod_image (f := fun u : InfinitePlace F ↦ max (u x) 1 ^ u.mult) hW.injOn,
      ← Finset.prod_attach Sinf]
    exact Finset.prod_le_prod₀ (fun _ _ ↦ by positivity) fun v _ ↦ hinfLocal v
  have hfin' : ∏ v ∈ Sfin, max (w v.1 x) 1 ≤ ∏ u ∈ Sfin.attach.image V, max (u x) 1 := by
    rw [Finset.prod_image (f := fun u : FinitePlace F ↦ max (u x) 1) hV.injOn,
      ← Finset.prod_attach Sfin]
    exact Finset.prod_le_prod₀ (fun _ _ ↦ by positivity) fun v _ ↦ hfinLocal v
  exact (mul_le_mul hinf' hfin' (by positivity) (by positivity)).trans
    (prod_max_apply_one_le_mulHeight₁ _ _ x)

/-- **The fundamental inequality above places of the base**, lower bound: the truncated local
factors `min 1 (w v x)` of a nonzero `x` at absolute values lying over distinct places of the
base, weighted by `mult v` above the infinite places, multiply to at least the reciprocal of the
relative height in the extension. -/
theorem inv_mulHeight₁_le_prod_min_one_apply_of_liesOver
    (hinf : ∀ v ∈ Sinf, (w v.1).LiesOver v.1) (hfin : ∀ v ∈ Sfin, (w v.1).LiesOver v.1)
    {x : F} (hx : x ≠ 0) :
    (mulHeight₁ x)⁻¹ ≤ (∏ v ∈ Sinf, min 1 (w v.1 x) ^ v.mult) * ∏ v ∈ Sfin, min 1 (w v.1 x) := by
  have h := prod_max_apply_one_le_mulHeight₁_of_liesOver Sinf Sfin w hinf hfin x⁻¹
  have hinv (u : AbsoluteValue F ℝ) : max (u x⁻¹) 1 = (min 1 (u x))⁻¹ := by
    rw [map_inv₀]
    rcases le_total (u x) 1 with hle | hle
    · rw [min_eq_right hle, max_eq_left ((one_le_inv₀ (u.pos hx)).mpr hle)]
    · rw [min_eq_left hle, inv_one, max_eq_right ((inv_le_one₀ (u.pos hx)).mpr hle)]
  simp only [hinv, inv_pow, Finset.prod_inv_distrib, ← mul_inv, mulHeight₁_inv] at h
  have hpos : 0 < (∏ v ∈ Sinf, min 1 (w v.1 x) ^ v.mult) * ∏ v ∈ Sfin, min 1 (w v.1 x) :=
    mul_pos (Finset.prod_pos fun v _ ↦ pow_pos (lt_min zero_lt_one ((w v.1).pos hx)) _)
      (Finset.prod_pos fun v _ ↦ lt_min zero_lt_one ((w v.1).pos hx))
  exact (inv_le_comm₀ hpos (mulHeight₁_pos x)).mp h

/-- An absolute value lying over an infinite place of the base is bounded by the relative height
in the extension. -/
theorem InfinitePlace.max_apply_one_le_mulHeight₁_of_liesOver (v : InfinitePlace K)
    (w : AbsoluteValue F ℝ) [w.LiesOver v.1] (x : F) :
    max (w x) 1 ≤ mulHeight₁ x :=
  InfinitePlace.max_apply_one_le_mulHeight₁ ⟨w, isInfinitePlace_of_liesOver v w⟩ x

/-- At an absolute value above an infinite place, the lower truncated factor of a nonzero element
is bounded below by its reciprocal relative height. -/
theorem InfinitePlace.inv_mulHeight₁_le_min_one_apply_of_liesOver (v : InfinitePlace K)
    (w : AbsoluteValue F ℝ) [w.LiesOver v.1] {x : F} (hx : x ≠ 0) :
    (mulHeight₁ x)⁻¹ ≤ min 1 (w x) :=
  InfinitePlace.inv_mulHeight₁_le_min_one_apply ⟨w, isInfinitePlace_of_liesOver v w⟩ hx

/-- An absolute value lying over a finite place of the base is bounded by the relative height
in the extension, even when it is not itself a finite place. -/
theorem FinitePlace.max_apply_one_le_mulHeight₁_of_liesOver (v : FinitePlace K)
    (w : AbsoluteValue F ℝ) [w.LiesOver v.1] (x : F) :
    max (w x) 1 ≤ mulHeight₁ x := by
  simpa using prod_max_apply_one_le_mulHeight₁_of_liesOver ∅ {v} (fun _ ↦ w) (by simp)
    (by intro u hu; obtain rfl := Finset.mem_singleton.mp hu; infer_instance) x

/-- At an absolute value above a finite place, the lower truncated factor of a nonzero element
is bounded below by its reciprocal relative height. -/
theorem FinitePlace.inv_mulHeight₁_le_min_one_apply_of_liesOver (v : FinitePlace K)
    (w : AbsoluteValue F ℝ) [w.LiesOver v.1] {x : F} (hx : x ≠ 0) :
    (mulHeight₁ x)⁻¹ ≤ min 1 (w x) := by
  simpa using inv_mulHeight₁_le_prod_min_one_apply_of_liesOver ∅ {v} (fun _ ↦ w) (by simp)
    (by intro u hu; obtain rfl := Finset.mem_singleton.mp hu; infer_instance) hx

/-- **Liouville's inequality over a number field** (Bombieri–Gubler, Theorem 1.5.21): for
`α ∈ F` and `β ∈ K` with `β ≠ α`, and absolute values `w v` of `F` lying over distinct places
`v` of `K`, the truncated local factors of `β - α` multiply to at least
`(2 ^ [F : ℚ] H(α) H(β) ^ [F : K])⁻¹`. The heights are relative: that of `α` over `F` and that
of `β` over `K`. -/
theorem inv_le_prod_min_one_sub
    (hinf : ∀ v ∈ Sinf, (w v.1).LiesOver v.1) (hfin : ∀ v ∈ Sfin, (w v.1).LiesOver v.1)
    {α : F} {β : K} (hne : algebraMap K F β ≠ α) :
    (2 ^ finrank ℚ F * mulHeight₁ α * mulHeight₁ β ^ finrank K F)⁻¹ ≤
      (∏ v ∈ Sinf, min 1 (w v.1 (algebraMap K F β - α)) ^ v.mult) *
        ∏ v ∈ Sfin, min 1 (w v.1 (algebraMap K F β - α)) := by
  refine le_trans ?_ (inv_mulHeight₁_le_prod_min_one_apply_of_liesOver Sinf Sfin w hinf hfin
    (sub_ne_zero.mpr hne))
  refine inv_anti₀ (mulHeight₁_pos _) ?_
  calc mulHeight₁ (algebraMap K F β - α)
      ≤ 2 ^ totalWeight F * mulHeight₁ (algebraMap K F β) * mulHeight₁ α :=
        mulHeight₁_sub_le _ _
    _ = 2 ^ finrank ℚ F * mulHeight₁ α * mulHeight₁ β ^ finrank K F := by
        rw [totalWeight_eq_finrank, mulHeight₁_algebraMap]
        ring

end NumberField
