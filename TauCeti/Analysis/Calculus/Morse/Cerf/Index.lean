/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.Morse.Cerf
public import TauCeti.Analysis.Calculus.Morse.Index
public import TauCeti.Analysis.Matrix.HermitianSignature.Crossing
-- Private: used only inside proofs.
import TauCeti.Analysis.Calculus.ContDiff.Prod
import TauCeti.Analysis.Calculus.FDeriv.Prod

/-!
# Morse indices near a birth–death point

Let `f t : E → ℝ` be a one-parameter family of functions on a finite-dimensional real normed
space, jointly `C³`, and let `x₀` be a degenerate critical point of `f t₀` at which the family is
transverse: the derivative of the parametrized differential `(t, x) ↦ d(f t)_x` is onto. The
Hessian of `f t₀` at `x₀` then has a one-dimensional kernel, spanned by some `v ≠ 0`
(`TauCeti.exists_eq_smul_of_fderiv_fderiv_apply_eq_zero`). Write `k` for the Morse index of
`f t₀` at `x₀`, the number of negative directions of its Hessian, and

`κ = D³(f t₀)_{x₀} (v, v, v)`

for the third derivative along the kernel; `κ ≠ 0` is the cubic condition of a birth–death point.

Along a curve `c = (τ, ξ)` through `(t₀, x₀)` with velocity `(0, v)`, such as the curve of
critical points through a birth–death point (`TauCeti.exists_curve_fderiv_eq_zero`), this file
computes the Morse index of `f τ(σ)` at `ξ(σ)` for small `σ ≠ 0`:

* for `σ > 0` it is `k + 1` if `κ < 0` and `k` if `κ > 0`
  (`TauCeti.eventually_nhdsGT_morseIndex_eq`);
* for `σ < 0` it is `k + 1` if `κ > 0` and `k` if `κ < 0`
  (`TauCeti.eventually_nhdsLT_morseIndex_eq`).

So the critical points on the two sides of a birth–death point have Morse indices `k` and `k + 1`,
as in Cerf's normal form `x₁³ / 3 - s x₁ - x₂² / 2 - ⋯ - x_{k+1}² / 2 + x_{k+2}² / 2 + ⋯`, whose
pair of critical points for `s > 0` has indices `k + 1` and `k`
(`TauCeti.morseIndex_separatedSum_birthDeathPotential_neg_sqrt`,
`TauCeti.morseIndex_separatedSum_birthDeathPotential_sqrt`). Nothing about the curve beyond its
velocity at `0` enters: the statement concerns the Hessians along it, whose Morse indices are
defined whether or not the points are critical.

The proof views `σ ↦ Hess(f τ(σ))_{ξ(σ)}` as a path of symmetric bilinear forms through the
Hessian at `(t₀, x₀)`, with derivative `(u, w) ↦ D³(f t₀)_{x₀} (v, u, w)` at `0`, since the
velocity of `c` has no parameter component. Its crossing form at `0`, the restriction of that
derivative to the kernel `ℝ v` of the Hessian, is `a v ↦ a² κ`: nondegenerate, with negative
index `1` exactly when `κ < 0` and positive index `1` exactly when `κ > 0`
(`TauCeti.sigNeg_crossingForm_fderiv_fderiv`,
`TauCeti.sigPos_crossingForm_fderiv_fderiv`). The negative index of a path of symmetric forms
just after and just before a regular crossing is computed from the crossing form
(`ContinuousLinearMap.eventually_sigNeg_eq_add_sigNeg_crossingForm`,
`ContinuousLinearMap.eventually_sigNeg_eq_add_sigPos_crossingForm`).

## Main results

* `TauCeti.nondegenerate_crossingForm_fderiv_fderiv`: at a transverse point whose Hessian
  has a kernel vector `v`, the crossing form of the Hessian and of a bilinear form `B'` with
  `B' (v, v) ≠ 0` is nondegenerate; for the derivative of the Hessians along the curve,
  `B' (v, v) = κ`.
* `TauCeti.sigNeg_crossingForm_fderiv_fderiv` and
  `TauCeti.sigPos_crossingForm_fderiv_fderiv`: its indices are those of `B' (v, v)`.
* `TauCeti.eventually_nhdsGT_morseIndex_eq` and `TauCeti.eventually_nhdsLT_morseIndex_eq`: the
  Morse indices along a curve with velocity `(0, v)` on the two sides of `0`.

## References

* J. Cerf, *La stratification naturelle des espaces de fonctions différentiables réelles et le
  théorème de la pseudo-isotopie*, Publ. Math. IHÉS **39** (1970), 5–173, Chapter III.
* J. Robbin and D. Salamon, *The Maslov index for paths*, Topology **32** (1993), 827–844,
  Section 2 (crossing forms).
-/

public section

open Function Module Set Filter
open scoped Topology

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {f : ℝ → E → ℝ} {t : ℝ} {x : E}

/-! ### The crossing form at a birth–death point -/

section CrossingForm

variable (hf : ContDiffAt ℝ 2 (uncurry f) (t, x))
  (hs : Surjective (fderiv ℝ (fun w : ℝ × E ↦ fderiv ℝ (f w.1) w.2) (t, x))) {v : E}
  (hv : fderiv ℝ (fderiv ℝ (f t)) x v = 0) {B' : E →L[ℝ] E →L[ℝ] ℝ}
  (hB' : B' v v ≠ 0)
include hf hs hv hB'

/-- On the kernel of the Hessian at a transverse point, spanned by `v`, the crossing form of the
Hessian and of a bilinear form `B'` takes the value `a² B' (v, v)` at `a v`. -/
private theorem crossingForm_apply_eq_sq_mul (u : (fderiv ℝ (fderiv ℝ (f t)) x).ker) :
    ∃ a : ℝ, (u : E) = a • v ∧
      ContinuousLinearMap.crossingForm (fderiv ℝ (fderiv ℝ (f t)) x) B' u = a ^ 2 * B' v v := by
  have hv0 : v ≠ 0 := by rintro rfl; simp at hB'
  obtain ⟨a, ha⟩ := exists_eq_smul_of_fderiv_fderiv_apply_eq_zero hf hs hv0 hv u.property
  refine ⟨a, ha, ?_⟩
  rw [ContinuousLinearMap.crossingForm_apply, ha]
  simp only [map_smul, smul_apply, smul_eq_mul]
  ring

/-- **The crossing form at a birth–death point is nondegenerate.** At a transverse point whose
Hessian has a kernel vector `v`, the crossing form of the Hessian and of a bilinear form `B'` with
`B' (v, v) ≠ 0` is nondegenerate. -/
theorem nondegenerate_crossingForm_fderiv_fderiv :
    (ContinuousLinearMap.crossingForm (fderiv ℝ (fderiv ℝ (f t)) x) B').Nondegenerate := by
  refine QuadraticMap.nondegenerate_iff_radical_eq_bot.2 ((Submodule.eq_bot_iff _).2 fun u hu ↦ ?_)
  obtain ⟨a, hau, hQ⟩ := crossingForm_apply_eq_sq_mul hf hs hv hB' u
  have ha : a = 0 := by
    have h0 := hu.1
    rw [hQ] at h0
    exact pow_eq_zero_iff (n := 2) two_ne_zero |>.1 ((mul_eq_zero.1 h0).resolve_right hB')
  exact Subtype.ext (by simp [hau, ha])

/-- **The negative index of the crossing form at a birth–death point.** At a transverse point
whose Hessian has a kernel vector `v`, the crossing form of the Hessian and of a bilinear form
`B'` with `B' (v, v) ≠ 0` has negative index `1` if `B' (v, v) < 0` and `0` otherwise. -/
theorem sigNeg_crossingForm_fderiv_fderiv :
    sigNeg (ContinuousLinearMap.crossingForm (fderiv ℝ (fderiv ℝ (f t)) x) B') =
      if B' v v < 0 then 1 else 0 := by
  set Q := ContinuousLinearMap.crossingForm (fderiv ℝ (fderiv ℝ (f t)) x) B'
  have hv0 : v ≠ 0 := by rintro rfl; simp at hB'
  -- The kernel is the line through `v`, so the two indices add up to `1`.
  have hrank : finrank ℝ (fderiv ℝ (fderiv ℝ (f t)) x).ker = 1 := by
    refine le_antisymm (finrank_ker_fderiv_fderiv_le_one hf hs) ?_
    have hpos : 0 < finrank ℝ (fderiv ℝ (fderiv ℝ (f t)) x).ker :=
      Module.finrank_pos_iff_exists_ne_zero.2 ⟨⟨v, hv⟩, fun h ↦ hv0 (congrArg Subtype.val h)⟩
    omega
  have hsum := QuadraticForm.sigPos_add_sigNeg_of_nondegenerate Q
    (nondegenerate_crossingForm_fderiv_fderiv hf hs hv hB')
  rw [hrank] at hsum
  split_ifs with hneg
  · -- `Q` is nonpositive, so its positive index vanishes.
    have h0 : sigPos Q = 0 := (QuadraticForm.forall_nonpos_iff_sigPos_eq_zero Q).1 fun u ↦ by
      obtain ⟨a, -, hQ⟩ := crossingForm_apply_eq_sq_mul hf hs hv hB' u
      rw [hQ]
      exact mul_nonpos_of_nonneg_of_nonpos (sq_nonneg a) hneg.le
    omega
  · exact (QuadraticForm.forall_nonneg_iff_sigNeg_eq_zero Q).1 fun u ↦ by
      obtain ⟨a, -, hQ⟩ := crossingForm_apply_eq_sq_mul hf hs hv hB' u
      rw [hQ]
      exact mul_nonneg (sq_nonneg a) (not_lt.1 hneg)

/-- **The positive index of the crossing form at a birth–death point.** At a transverse point
whose Hessian has a kernel vector `v`, the crossing form of the Hessian and of a bilinear form
`B'` with `B' (v, v) ≠ 0` has positive index `1` if `0 < B' (v, v)` and `0` otherwise. -/
theorem sigPos_crossingForm_fderiv_fderiv :
    sigPos (ContinuousLinearMap.crossingForm (fderiv ℝ (fderiv ℝ (f t)) x) B') =
      if 0 < B' v v then 1 else 0 := by
  have h := sigNeg_crossingForm_fderiv_fderiv hf hs hv (B' := -B') (by simpa using hB')
  simpa only [ContinuousLinearMap.crossingForm_neg, sigNeg_neg, neg_apply, neg_lt_zero] using h

end CrossingForm

/-! ### Morse indices along a curve through a birth–death point -/

section Curve

omit [FiniteDimensional ℝ E] in
/-- Along a curve through `(t, x)` with velocity `(0, v)`, the Hessians `Hess(f τ(σ))_{ξ(σ)}`
form a path of forms through `Hess(f t)_x`, whose derivative at `0` takes the value
`D³(f t)_x (v, v, v)` at `(v, v)`. -/
private theorem exists_hasDerivAt_fderiv_fderiv_comp (hf : ContDiffAt ℝ 3 (uncurry f) (t, x))
    {v : E} {c : ℝ → ℝ × E} (hc0 : c 0 = (t, x)) (hc' : HasDerivAt c (0, v) 0) :
    ∃ B' : E →L[ℝ] E →L[ℝ] ℝ, HasDerivAt (fun σ ↦ fderiv ℝ (fderiv ℝ (f (c σ).1)) (c σ).2) B' 0 ∧
      B' v v = fderiv ℝ (fderiv ℝ (fderiv ℝ (f t))) x v v v := by
  set H : ℝ × E → E →L[ℝ] E →L[ℝ] ℝ := fun w ↦ fderiv ℝ (fderiv ℝ (f w.1)) w.2
  have hG : ContDiffAt ℝ 2 (fun w : ℝ × E ↦ fderiv ℝ (f w.1) w.2) (t, x) :=
    hf.fderiv_slice (m := 2) le_rfl
  have hH : ContDiffAt ℝ 1 H (t, x) := hG.fderiv_slice (m := 1) le_rfl
  have hH' : HasFDerivAt H (fderiv ℝ H (t, x)) (c 0) := by
    rw [hc0]
    exact (hH.differentiableAt one_ne_zero).hasFDerivAt
  have hHc : HasDerivAt (H ∘ c) (fderiv ℝ H (t, x) (0, v)) 0 := by
    simpa using (hH'.comp 0 hc'.hasFDerivAt).hasDerivAt
  refine ⟨fderiv ℝ H (t, x) (0, v), hHc, ?_⟩
  rw [fderiv_apply_eq_fderiv_slice_left_add_fderiv_slice_right (hH.differentiableAt one_ne_zero)]
  simp [H]

variable (hf : ContDiffAt ℝ 3 (uncurry f) (t, x))
  (hs : Surjective (fderiv ℝ (fun w : ℝ × E ↦ fderiv ℝ (f w.1) w.2) (t, x))) {v : E}
  (hv : fderiv ℝ (fderiv ℝ (f t)) x v = 0)
  (hκ : fderiv ℝ (fderiv ℝ (fderiv ℝ (f t))) x v v v ≠ 0) {c : ℝ → ℝ × E}
  (hc0 : c 0 = (t, x)) (hc' : HasDerivAt c (0, v) 0)
include hf hs hv hκ hc0 hc'

/-- The path of Hessians along a curve through `(t, x)` with velocity `(0, v)` has a regular
crossing at `0`, with crossing form of negative index `1` exactly when `κ < 0` and positive index
`1` exactly when `0 < κ`. -/
private theorem exists_hasDerivAt_crossingForm :
    ∃ B' : E →L[ℝ] E →L[ℝ] ℝ, HasDerivAt (fun σ ↦ fderiv ℝ (fderiv ℝ (f (c σ).1)) (c σ).2) B' 0 ∧
      (fderiv ℝ (fderiv ℝ (f t)) x).toBilinForm.IsSymm ∧
      (ContinuousLinearMap.crossingForm (fderiv ℝ (fderiv ℝ (f t)) x) B').Nondegenerate ∧
      sigNeg (ContinuousLinearMap.crossingForm (fderiv ℝ (fderiv ℝ (f t)) x) B') =
        (if fderiv ℝ (fderiv ℝ (fderiv ℝ (f t))) x v v v < 0 then 1 else 0) ∧
      sigPos (ContinuousLinearMap.crossingForm (fderiv ℝ (fderiv ℝ (f t)) x) B') =
        if 0 < fderiv ℝ (fderiv ℝ (fderiv ℝ (f t))) x v v v then 1 else 0 := by
  obtain ⟨B', hB', hB'v⟩ := exists_hasDerivAt_fderiv_fderiv_comp hf hc0 hc'
  have hf2 : ContDiffAt ℝ 2 (uncurry f) (t, x) := hf.of_le (by norm_num)
  have hκ' : B' v v ≠ 0 := by rwa [hB'v]
  refine ⟨B', hB', ⟨fun u w ↦ fderiv_fderiv_apply_comm_of_uncurry hf2 u w⟩,
    nondegenerate_crossingForm_fderiv_fderiv hf2 hs hv hκ', ?_, ?_⟩
  · rw [sigNeg_crossingForm_fderiv_fderiv hf2 hs hv hκ', hB'v]
  · rw [sigPos_crossingForm_fderiv_fderiv hf2 hs hv hκ', hB'v]

/-- **The Morse index just after a birth–death point.** Let `x` be a critical point of `f t` at
which the family, jointly `C³`, is transverse, and `v` a kernel vector of the Hessian with
`κ = D³(f t)_x (v, v, v) ≠ 0`. Along a curve `c` through `(t, x)` with velocity `(0, v)`, the
Morse index of `f (c σ).1` at `(c σ).2` for `σ > 0` close to `0` is the Morse index of `f t` at
`x`, plus one if `κ < 0`. -/
theorem eventually_nhdsGT_morseIndex_eq :
    ∀ᶠ σ in 𝓝[>] 0, morseIndex (f (c σ).1) (c σ).2 =
      morseIndex (f t) x + if fderiv ℝ (fderiv ℝ (fderiv ℝ (f t))) x v v v < 0 then 1 else 0 := by
  obtain ⟨B', hB', hsymm, hreg, hneg, -⟩ := exists_hasDerivAt_crossingForm hf hs hv hκ hc0 hc'
  have hV0 : fderiv ℝ (fderiv ℝ (f (c 0).1)) (c 0).2 = fderiv ℝ (fderiv ℝ (f t)) x := by
    rw [hc0]
  rw [← hV0] at hsymm hreg hneg
  -- The derivative within `Ici 0` or `Iic 0`, through the Fréchet derivative.
  have hB's : ∀ s, HasDerivWithinAt
      (fun σ ↦ fderiv ℝ (fderiv ℝ (f (c σ).1)) (c σ).2) B' s 0 :=
    fun _ ↦ hB'.hasFDerivAt.hasFDerivWithinAt
  filter_upwards [ContinuousLinearMap.eventually_sigNeg_eq_add_sigNeg_crossingForm hsymm (hB's _)
    hreg] with σ hσ
  rw [morseIndex_def, morseIndex_def, hessianQuadraticForm_def, hessianQuadraticForm_def, hσ,
    hneg, hV0]

/-- **The Morse index just before a birth–death point.** Let `x` be a critical point of `f t` at
which the family, jointly `C³`, is transverse, and `v` a kernel vector of the Hessian with
`κ = D³(f t)_x (v, v, v) ≠ 0`. Along a curve `c` through `(t, x)` with velocity `(0, v)`, the
Morse index of `f (c σ).1` at `(c σ).2` for `σ < 0` close to `0` is the Morse index of `f t` at
`x`, plus one if `0 < κ`. -/
theorem eventually_nhdsLT_morseIndex_eq :
    ∀ᶠ σ in 𝓝[<] 0, morseIndex (f (c σ).1) (c σ).2 =
      morseIndex (f t) x + if 0 < fderiv ℝ (fderiv ℝ (fderiv ℝ (f t))) x v v v then 1 else 0 := by
  obtain ⟨B', hB', hsymm, hreg, -, hpos⟩ := exists_hasDerivAt_crossingForm hf hs hv hκ hc0 hc'
  have hV0 : fderiv ℝ (fderiv ℝ (f (c 0).1)) (c 0).2 = fderiv ℝ (fderiv ℝ (f t)) x := by
    rw [hc0]
  rw [← hV0] at hsymm hreg hpos
  -- The derivative within `Ici 0` or `Iic 0`, through the Fréchet derivative.
  have hB's : ∀ s, HasDerivWithinAt
      (fun σ ↦ fderiv ℝ (fderiv ℝ (f (c σ).1)) (c σ).2) B' s 0 :=
    fun _ ↦ hB'.hasFDerivAt.hasFDerivWithinAt
  filter_upwards [ContinuousLinearMap.eventually_sigNeg_eq_add_sigPos_crossingForm hsymm (hB's _)
    hreg] with σ hσ
  rw [morseIndex_def, morseIndex_def, hessianQuadraticForm_def, hessianQuadraticForm_def, hσ,
    hpos, hV0]

end Curve

end TauCeti
