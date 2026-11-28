/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-!
# The differential inequality `y' ≤ C yᵖ`

Let `y` be a positive function, continuous on `[a, b]` and differentiable in its interior, with
`y' ≤ C yᵖ` there. For an exponent `p ≠ 1`, the primitive `Φ(y) = y ^ (1 - p) / (1 - p)` of
`y ^ (-p)` satisfies `(Φ ∘ y)' = y' y ^ (-p) ≤ C`, so

`y b ^ (1 - p) / (1 - p) - y a ^ (1 - p) / (1 - p) ≤ C (b - a)`

(`TauCeti.rpow_one_sub_div_sub_le_of_deriv_le_mul_rpow`). This is the differential form of
Bihari's nonlinear Grönwall inequality for a power nonlinearity; neither the sign of `C` nor that
of `y'` matters.

For a superlinear power `p > 1` the inequality reads
`y a ^ (1 - p) - (p - 1) C (b - a) ≤ y b ^ (1 - p)`, and it has two consequences used in the
energy method for evolution equations, where `y` is a norm of the solution.

* **Bounds before blow-up.** As long as `(p - 1) C (b - a) < y a ^ (1 - p)`, the function `y`
  stays below the solution of `z' = C zᵖ` with `z a = y a`. For `p = n + 1` this is
  `y b ^ n ≤ y a ^ n / (1 - n C (b - a) y a ^ n)`
  (`TauCeti.pow_le_div_one_sub_of_deriv_le_mul_pow`); for `n = 1` it is the Riccati bound
  `y b ≤ y a / (1 - C (b - a) y a)`, which bounds an `Hˢ` energy on a time interval of length
  comparable to `1 / (C y a)`.
* **Blow-up rates.** If `y` is unbounded on `[t, T)`, then `y t ^ (1 - p) ≤ (p - 1) C (T - t)`
  (`TauCeti.rpow_one_sub_le_of_deriv_le_mul_rpow_of_not_bddAbove`): `y t` is at least the value
  at `t` of the solution of `z' = C zᵖ` that blows up at `T`, so `y` cannot blow up more slowly
  than that solution, and a small value `y t` forces a late blow-up time `T`. For `p = n + 1`
  this is `1 / (n C (T - t)) ≤ y t ^ n`
  (`TauCeti.inv_le_pow_of_deriv_le_mul_pow_of_not_bddAbove`); for `n = 2` and `y = ‖∇u‖₂²`
  along a Navier–Stokes solution, whose enstrophy satisfies `y' ≤ C ν⁻³ y³`, it is Leray's
  lower bound on the rate of blow-up.

The explicit solution `z t = (C (T - t))⁻¹` of `z' = C z²` attains both bounds for `n = 1`, so
their constants are optimal.

## Main results

* `TauCeti.rpow_one_sub_div_sub_le_of_deriv_le_mul_rpow`: the comparison for every `p ≠ 1`.
* `TauCeti.rpow_one_sub_sub_mul_le_of_deriv_le_mul_rpow`: its form for `p > 1`.
* `TauCeti.rpow_one_sub_le_of_deriv_le_mul_rpow_of_not_bddAbove`: the blow-up rate for `p > 1`.
* `TauCeti.pow_le_div_one_sub_of_deriv_le_mul_pow`: the bound before blow-up for `p = n + 1`.
* `TauCeti.inv_le_pow_of_deriv_le_mul_pow_of_not_bddAbove`: the blow-up rate for `p = n + 1`.

## References

* I. Bihari, *A generalization of a lemma of Bellman and its application to uniqueness problems
  of differential equations*, Acta Math. Acad. Sci. Hungar. 7 (1956), 81–94.
* W. S. Ozanski and B. C. Pooley, *Leray's fundamental work on the Navier–Stokes equations: a
  modern review of "Sur le mouvement d'un liquide visqueux emplissant l'espace"*, in Partial
  Differential Equations in Fluid Mechanics, LMS Lecture Note Series 452 (2018), Corollaries
  3.11 and 3.12.
-/

public section

open Set

namespace TauCeti

variable {y y' : ℝ → ℝ} {C p : ℝ}

/-- **Bihari's inequality for a power nonlinearity.** If a positive function `y`, continuous on
`[a, b]`, satisfies `y' ≤ C yᵖ` in the interior for an exponent `p ≠ 1`, then the primitive
`y ^ (1 - p) / (1 - p)` of `y ^ (-p)` grows by at most `C (b - a)` from `a` to `b`. -/
theorem rpow_one_sub_div_sub_le_of_deriv_le_mul_rpow {a b : ℝ} (hab : a ≤ b) (hp : p ≠ 1)
    (hy : ContinuousOn y (Icc a b)) (hpos : ∀ t ∈ Icc a b, 0 < y t)
    (hy' : ∀ t ∈ Ioo a b, HasDerivAt y (y' t) t) (hle : ∀ t ∈ Ioo a b, y' t ≤ C * y t ^ p) :
    y b ^ (1 - p) / (1 - p) - y a ^ (1 - p) / (1 - p) ≤ C * (b - a) := by
  have hq : 1 - p ≠ 0 := sub_ne_zero.2 hp.symm
  -- The function `t ↦ C t - Φ (y t)` has the nonnegative derivative `C - y' y ^ (-p)`.
  have hmono : MonotoneOn (fun t ↦ C * t - y t ^ (1 - p) / (1 - p)) (Icc a b) := by
    refine monotoneOn_of_hasDerivWithinAt_nonneg (f' := fun t ↦ C - y' t * y t ^ (-p))
      (convex_Icc a b) ((continuousOn_const.mul continuousOn_id).sub
        ((hy.rpow_const fun t ht ↦ Or.inl (hpos t ht).ne').div_const _)) (fun t ht ↦ ?_)
        (fun t ht ↦ ?_) <;> rw [interior_Icc] at ht <;> have hyt := hpos t (Ioo_subset_Icc_self ht)
    · refine HasDerivAt.hasDerivWithinAt ?_
      convert ((hasDerivAt_id' t).const_mul C).sub
        (((hy' t ht).rpow_const (p := 1 - p) (Or.inl hyt.ne')).div_const (1 - p)) using 1
      rw [show 1 - p - 1 = -p by ring]
      field_simp
    · have : y' t * y t ^ (-p) ≤ C := by
        calc y' t * y t ^ (-p) ≤ C * y t ^ p * y t ^ (-p) := by
              gcongr
              exact hle t ht
          _ = C := by rw [mul_assoc, ← Real.rpow_add hyt, add_neg_cancel, Real.rpow_zero, mul_one]
      linarith
  have h := hmono (left_mem_Icc.2 hab) (right_mem_Icc.2 hab) hab
  simp only at h
  linarith

/-- **Bihari's inequality for a superlinear power.** If a positive function `y`, continuous on
`[a, b]`, satisfies `y' ≤ C yᵖ` in the interior with `p > 1`, then
`y a ^ (1 - p) - (p - 1) C (b - a) ≤ y b ^ (1 - p)`. -/
theorem rpow_one_sub_sub_mul_le_of_deriv_le_mul_rpow {a b : ℝ} (hab : a ≤ b) (hp : 1 < p)
    (hy : ContinuousOn y (Icc a b)) (hpos : ∀ t ∈ Icc a b, 0 < y t)
    (hy' : ∀ t ∈ Ioo a b, HasDerivAt y (y' t) t) (hle : ∀ t ∈ Ioo a b, y' t ≤ C * y t ^ p) :
    y a ^ (1 - p) - (p - 1) * C * (b - a) ≤ y b ^ (1 - p) := by
  have h := rpow_one_sub_div_sub_le_of_deriv_le_mul_rpow hab hp.ne' hy hpos hy' hle
  rw [← sub_div, div_le_iff_of_neg (by linarith)] at h
  linarith

/-- **The blow-up rate for `y' ≤ C yᵖ`.** If a positive function `y`, continuous on `[t, T)`,
satisfies `y' ≤ C yᵖ` on `(t, T)` with `p > 1` and is unbounded on `[t, T)`, then
`y t ^ (1 - p) ≤ (p - 1) C (T - t)`: `y t` is at least the value at `t` of the solution
`((p - 1) C (T - s)) ^ (-1 / (p - 1))` of `z' = C zᵖ` that blows up at `T`. -/
theorem rpow_one_sub_le_of_deriv_le_mul_rpow_of_not_bddAbove {t T : ℝ} (hp : 1 < p)
    (hy : ContinuousOn y (Ico t T)) (hpos : ∀ s ∈ Ico t T, 0 < y s)
    (hy' : ∀ s ∈ Ioo t T, HasDerivAt y (y' s) s) (hle : ∀ s ∈ Ioo t T, y' s ≤ C * y s ^ p)
    (hunb : ¬BddAbove (y '' Ico t T)) :
    y t ^ (1 - p) ≤ (p - 1) * C * (T - t) := by
  have hq : 1 - p < 0 := by linarith
  by_contra! hlt
  -- Otherwise `y ^ (1 - p)` stays above `m > 0` on `[t, T)`, so `y` stays below `m ^ (1 - p)⁻¹`.
  have ht : t ∈ Ico t T := by
    by_contra h
    exact hunb (by simp [Ico_eq_empty fun hT ↦ h ⟨le_rfl, hT⟩])
  set m := y t ^ (1 - p) - max 0 ((p - 1) * C * (T - t)) with hm_def
  have hm : 0 < m := by
    have := Real.rpow_pos_of_pos (hpos t ht) (1 - p)
    rw [hm_def, sub_pos, max_lt_iff]
    exact ⟨this, hlt⟩
  refine hunb ⟨m ^ (1 - p)⁻¹, ?_⟩
  rintro _ ⟨r, hr, rfl⟩
  refine (Real.le_rpow_inv_iff_of_neg (hpos r hr) hm hq).2 ?_
  have hsub : Icc t r ⊆ Ico t T := Icc_subset_Ico_right hr.2
  have hcomp := rpow_one_sub_sub_mul_le_of_deriv_le_mul_rpow hr.1 hp (hy.mono hsub)
    (fun s hs ↦ hpos s (hsub hs)) (fun s hs ↦ hy' s (Ioo_subset_Ioo_right hr.2.le hs))
    (fun s hs ↦ hle s (Ioo_subset_Ioo_right hr.2.le hs))
  have hmax : (p - 1) * C * (r - t) ≤ max 0 ((p - 1) * C * (T - t)) := by
    rcases le_total 0 C with hC | hC
    · exact le_max_of_le_right
        (mul_le_mul_of_nonneg_left (by linarith [hr.2]) (mul_nonneg (by linarith) hC))
    · exact le_max_of_le_left (mul_nonpos_of_nonpos_of_nonneg
        (mul_nonpos_of_nonneg_of_nonpos (by linarith) hC) (by linarith [hr.1]))
  linarith

/-- **The bound before blow-up for `y' ≤ C yⁿ⁺¹`.** If a positive function `y`, continuous on
`[a, b]`, satisfies `y' ≤ C yⁿ⁺¹` in the interior, and `n C (b - a) y a ^ n < 1`,
then `y b ^ n ≤ y a ^ n / (1 - n C (b - a) y a ^ n)`. For `n = 1` this is the Riccati bound
`y b ≤ y a / (1 - C (b - a) y a)`. -/
theorem pow_le_div_one_sub_of_deriv_le_mul_pow {a b : ℝ} {n : ℕ} (hab : a ≤ b)
    (hy : ContinuousOn y (Icc a b)) (hpos : ∀ t ∈ Icc a b, 0 < y t)
    (hy' : ∀ t ∈ Ioo a b, HasDerivAt y (y' t) t) (hle : ∀ t ∈ Ioo a b, y' t ≤ C * y t ^ (n + 1))
    (hlt : n * C * (b - a) * y a ^ n < 1) :
    y b ^ n ≤ y a ^ n / (1 - n * C * (b - a) * y a ^ n) := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  have hya := hpos a (left_mem_Icc.2 hab)
  have hyb := hpos b (right_mem_Icc.2 hab)
  have h := rpow_one_sub_sub_mul_le_of_deriv_le_mul_rpow (p := n + 1) hab
    (by have : (1 : ℝ) ≤ n := Nat.one_le_cast.2 (Nat.one_le_iff_ne_zero.2 hn); linarith) hy hpos
    hy' fun t ht ↦ by exact_mod_cast hle t ht
  rw [show (1 : ℝ) - (n + 1) = -n by ring, Real.rpow_neg hya.le, Real.rpow_neg hyb.le,
    Real.rpow_natCast, Real.rpow_natCast, add_sub_cancel_right] at h
  have hA := pow_pos hya n
  have hB := pow_pos hyb n
  rw [le_div_iff₀ (by linarith)]
  -- Multiply `(y a ^ n)⁻¹ - n C (b - a) ≤ (y b ^ n)⁻¹` by `y a ^ n * y b ^ n`.
  have := mul_le_mul_of_nonneg_left h (mul_pos hA hB).le
  rw [mul_sub, show y a ^ n * y b ^ n * (y a ^ n)⁻¹ = y b ^ n by field_simp,
    show y a ^ n * y b ^ n * (y b ^ n)⁻¹ = y a ^ n by field_simp] at this
  linarith

/-- **The blow-up rate for `y' ≤ C yⁿ⁺¹`.** If a positive function `y`, continuous on `[t, T)`,
satisfies `y' ≤ C yⁿ⁺¹` on `(t, T)` and is unbounded on `[t, T)`, then
`1 / (n C (T - t)) ≤ y t ^ n`. For `n = 2` this is Leray's lower bound on the rate of blow-up of
the enstrophy. -/
theorem inv_le_pow_of_deriv_le_mul_pow_of_not_bddAbove {t T : ℝ} {n : ℕ}
    (hy : ContinuousOn y (Ico t T)) (hpos : ∀ s ∈ Ico t T, 0 < y s)
    (hy' : ∀ s ∈ Ioo t T, HasDerivAt y (y' s) s) (hle : ∀ s ∈ Ioo t T, y' s ≤ C * y s ^ (n + 1))
    (hunb : ¬BddAbove (y '' Ico t T)) :
    (n * C * (T - t))⁻¹ ≤ y t ^ n := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  have ht : t ∈ Ico t T := by
    by_contra h
    exact hunb (by simp [Ico_eq_empty fun hT ↦ h ⟨le_rfl, hT⟩])
  have hyt := hpos t ht
  have h := rpow_one_sub_le_of_deriv_le_mul_rpow_of_not_bddAbove (p := n + 1)
    (by have : (1 : ℝ) ≤ n := Nat.one_le_cast.2 (Nat.one_le_iff_ne_zero.2 hn); linarith) hy hpos
    hy' (fun s hs ↦ by exact_mod_cast hle s hs) hunb
  rw [show (1 : ℝ) - (n + 1) = -n by ring, Real.rpow_neg hyt.le, Real.rpow_natCast,
    add_sub_cancel_right] at h
  simpa using inv_anti₀ (inv_pos.2 (pow_pos hyt n)) h

end TauCeti
