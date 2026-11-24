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
(`ContinuousLinearMap.sigNeg_crossingForm_of_ker_eq_span_singleton`,
`ContinuousLinearMap.sigPos_crossingForm_of_ker_eq_span_singleton`). The negative index of a
path of symmetric forms just after and just before a regular crossing is computed from the
crossing form (`ContinuousLinearMap.eventually_sigNeg_eq_add_sigNeg_crossingForm`,
`ContinuousLinearMap.eventually_sigNeg_eq_add_sigPos_crossingForm`).

## Main results

* `TauCeti.exists_hasDerivAt_fderiv_fderiv_comp`: the Hessians along a curve with velocity
  `(0, v)` are differentiable at `0`, with derivative taking the value `κ` at `(v, v)`.
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

/-! ### Morse indices along a curve through a birth–death point -/

section Curve

omit [FiniteDimensional ℝ E] in
/-- **The derivative of the Hessians along a curve.** Along a curve through `(t, x)` with velocity
`(0, v)`, for a family jointly `C³` at `(t, x)`, the Hessians `Hess(f τ(σ))_{ξ(σ)}` form a path of
forms through `Hess(f t)_x`, differentiable at `0`, whose derivative there takes the value
`D³(f t)_x (v, v, v)` at `(v, v)`. -/
theorem exists_hasDerivAt_fderiv_fderiv_comp (hf : ContDiffAt ℝ 3 (uncurry f) (t, x))
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
    ∃ B' : E →L[ℝ] E →L[ℝ] ℝ,
      (∀ s, HasDerivWithinAt (fun σ ↦ fderiv ℝ (fderiv ℝ (f (c σ).1)) (c σ).2) B' s 0) ∧
      (fderiv ℝ (fderiv ℝ (f (c 0).1)) (c 0).2).toBilinForm.IsSymm ∧
      (ContinuousLinearMap.crossingForm (fderiv ℝ (fderiv ℝ (f (c 0).1)) (c 0).2)
        B').Nondegenerate ∧
      sigNeg (ContinuousLinearMap.crossingForm (fderiv ℝ (fderiv ℝ (f (c 0).1)) (c 0).2) B') =
        (if fderiv ℝ (fderiv ℝ (fderiv ℝ (f t))) x v v v < 0 then 1 else 0) ∧
      sigPos (ContinuousLinearMap.crossingForm (fderiv ℝ (fderiv ℝ (f (c 0).1)) (c 0).2) B') =
        if 0 < fderiv ℝ (fderiv ℝ (fderiv ℝ (f t))) x v v v then 1 else 0 := by
  obtain ⟨B', hB', hB'v⟩ := exists_hasDerivAt_fderiv_fderiv_comp hf hc0 hc'
  have hf2 : ContDiffAt ℝ 2 (uncurry f) (t, x) := hf.of_le (by norm_num)
  have hκ' : B' v v ≠ 0 := by rwa [hB'v]
  have hv0 : v ≠ 0 := by rintro rfl; simp at hκ
  -- At a transverse point the kernel of the Hessian is the line through `v`.
  have hker : (fderiv ℝ (fderiv ℝ (f t)) x).ker = ℝ ∙ v :=
    le_antisymm (fun u hu ↦ by
      obtain ⟨a, rfl⟩ := exists_eq_smul_of_fderiv_fderiv_apply_eq_zero hf2 hs hv0 hv hu
      exact Submodule.smul_mem _ a (Submodule.mem_span_singleton_self v))
      ((Submodule.span_singleton_le_iff_mem _ _).2 hv)
  rw [hc0]
  -- The derivative within any set, through the Fréchet derivative: the generic
  -- `HasDerivAt.hasDerivWithinAt` needs the normed instances on the space of forms.
  refine ⟨B', fun _ ↦ hB'.hasFDerivAt.hasFDerivWithinAt,
    ⟨fun u w ↦ fderiv_fderiv_apply_comm_of_uncurry hf2 u w⟩,
    ContinuousLinearMap.nondegenerate_crossingForm_of_ker_le_span_singleton hker.le hκ', ?_, ?_⟩
  · rw [ContinuousLinearMap.sigNeg_crossingForm_of_ker_eq_span_singleton hker hκ', hB'v]
  · rw [ContinuousLinearMap.sigPos_crossingForm_of_ker_eq_span_singleton hker hκ', hB'v]

/-- **The Morse index just after a birth–death point.** Let the family, jointly `C³`, be
transverse at `(t, x)`, and let `v` be a kernel vector of the Hessian of `f t` at `x` with
`κ = D³(f t)_x (v, v, v) ≠ 0`. Along a curve `c` through `(t, x)` with velocity `(0, v)`, the
Morse index of `f (c σ).1` at `(c σ).2` for `σ > 0` close to `0` is the Morse index of `f t` at
`x`, plus one if `κ < 0`. Neither `x` nor the points of the curve need to be critical. -/
theorem eventually_nhdsGT_morseIndex_eq :
    ∀ᶠ σ in 𝓝[>] 0, morseIndex (f (c σ).1) (c σ).2 =
      morseIndex (f t) x + if fderiv ℝ (fderiv ℝ (fderiv ℝ (f t))) x v v v < 0 then 1 else 0 := by
  obtain ⟨B', hB', hsymm, hreg, hneg, -⟩ := exists_hasDerivAt_crossingForm hf hs hv hκ hc0 hc'
  filter_upwards [ContinuousLinearMap.eventually_sigNeg_eq_add_sigNeg_crossingForm hsymm (hB' _)
    hreg] with σ hσ
  rw [morseIndex_def, morseIndex_def, hessianQuadraticForm_def, hessianQuadraticForm_def, hσ,
    hneg, hc0]

/-- **The Morse index just before a birth–death point.** Let the family, jointly `C³`, be
transverse at `(t, x)`, and let `v` be a kernel vector of the Hessian of `f t` at `x` with
`κ = D³(f t)_x (v, v, v) ≠ 0`. Along a curve `c` through `(t, x)` with velocity `(0, v)`, the
Morse index of `f (c σ).1` at `(c σ).2` for `σ < 0` close to `0` is the Morse index of `f t` at
`x`, plus one if `0 < κ`. Neither `x` nor the points of the curve need to be critical. -/
theorem eventually_nhdsLT_morseIndex_eq :
    ∀ᶠ σ in 𝓝[<] 0, morseIndex (f (c σ).1) (c σ).2 =
      morseIndex (f t) x + if 0 < fderiv ℝ (fderiv ℝ (fderiv ℝ (f t))) x v v v then 1 else 0 := by
  obtain ⟨B', hB', hsymm, hreg, -, hpos⟩ := exists_hasDerivAt_crossingForm hf hs hv hκ hc0 hc'
  filter_upwards [ContinuousLinearMap.eventually_sigNeg_eq_add_sigPos_crossingForm hsymm (hB' _)
    hreg] with σ hσ
  rw [morseIndex_def, morseIndex_def, hessianQuadraticForm_def, hessianQuadraticForm_def, hσ,
    hpos, hc0]

end Curve

end TauCeti
