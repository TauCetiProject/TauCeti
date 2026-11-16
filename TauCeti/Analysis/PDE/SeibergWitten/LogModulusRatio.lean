/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.SeibergWitten.CutoffCurrent
public import TauCeti.Analysis.InnerProductSpace.Laplacian.TransverseLiouville
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import TauCeti.Analysis.Calculus.DifferentialForm.Basic

/-!
# The log-modulus ratio of two flat vortex fields with the same zeros

Let `E` be a finite-dimensional real inner product space with an orthogonal complex structure
`J`, such as `ℂ_base × ℂ_normal`, and let `(a, α)` be an abelian Higgs pair on `E` with
`a = i b`: a real one-form `b` and a complex function `α`. Fix an orthonormal basis `(eᵢ)` of `E`.
The flat vortex equations with coupling `κ` are

`∂bar_a α = 0`,  `∑ᵢ db(eᵢ, J eᵢ) = κ (|α|² - 1)`.

On the plane `ℂ` with `J = i` the sum is `2 (∂₁b₂ - ∂₂b₁) = -2 (*i F_a)`, so these are the plane
vortex equations `∂bar_a α = 0`, `*i F_a = (1 - |α|²) / 8` for `κ = 1 / 4`. On
`ℂ_base × ℂ_normal`, with `κ = 1 / 4`, they are the `(0,1)`-part of the Dirac equation and the
`ω`-component of the curvature equation in the flat limit of Taubes's large-parameter
Seiberg–Witten equations rescaled near a pseudoholomorphic curve; the pullback of a plane vortex
along the normal projection solves them.

This file compares two such pairs `(b, α)` and `(b', α')` whose sections have the same zeros with
the same multiplicities, in the form `α = h α'` for a nowhere-vanishing `C²` function `h`. The
argument is Taubes's comparison of the log-modulus ratio `w = log |h|² = log |α|² - log |α'|²`:

* Where `α'` does not vanish, `h = α / α'` is holomorphic for the difference of the connections,
  `∂bar_(a - a') h = 0` (`TauCeti.SeibergWitten.covariantDBar_sub_eq_zero_of_mul`), by the
  product rule for `∂bar`.
* For a nowhere-vanishing `h` with `∂bar_c h = 0`, the phase form `Im (h⁻¹ dh) + c` is
  `d^c_J log |h|²` (`TauCeti.SeibergWitten.covariantPhaseForm_eq_twistedDifferential_log`), and the
  phase form `Im (h⁻¹ dh)` is closed, so `dc = d d^c_J log |h|²`. Taking the `J`-trace gives
  `Δ log |h|² = ∑ᵢ dc(eᵢ, J eᵢ)` (`laplacian_log_norm_sq_eq_sum_extDeriv`,
  `TauCeti.AlmostComplexStructure.sum_extDeriv_twistedDifferential_apply_eq_laplacian`).
* With `c = b - b'` and the curvature equations of the two pairs, `w` satisfies the difference
  equation `Δ w = κ |α'|² (|h|² - 1) = κ |α'|² (eʷ - 1)` wherever `h ≠ 0`, across the common
  zeros (`laplacian_log_norm_sq_eq_mul_sub_one`). The zeros of `α'` enter only through the
  density of their complement, which carries the identity `∂bar_(a - a') h = 0` to all of `E`
  (`TauCeti.SeibergWitten.covariantDBar_sub_eq_zero_of_dense`).
* For `κ ≥ 0`, `w Δ w ≥ 0`. If `w` is bounded and both sections satisfy the transverse vacuum
  condition `|α| → 1` as the component along a nonzero subspace `K` (the normal factor) tends to
  infinity, uniformly in the complementary (base) directions, then `w → 0` in the same sense, and
  the transverse Liouville theorem
  `TauCeti.eq_zero_of_tendsto_comap_norm_starProjection_of_mul_laplacian_nonneg` gives `w = 0`.
  So `|h| = 1`, and the holomorphicity of `h` for `a - a'` determines the connection:
  `b = b' - Im (h⁻¹ dh)` (`norm_eq_one_and_eq_sub_phaseForm_of_tendsto`). That is, `(b, α)` is the
  gauge transform of `(b', α')` by the unit-modulus function `h`, in the convention
  `(b, α) ↦ (b - Im (u⁻¹ du), u α)` of `TauCeti.SeibergWitten.covariantPhaseForm_sub_phaseForm_mul`.

No decay along the base directions is assumed, which is why the transverse Liouville theorem is
used rather than its cocompact form. For two plane vortices (`K = E = ℂ`) this is the argument
of `TauCeti.Vortex.exists_eq_phaseGauge_of_forall_section_eq_mul`.

## Main results

* `TauCeti.SeibergWitten.laplacian_log_norm_sq_eq_sum_extDeriv`: `Δ log |h|² = ∑ᵢ dc(eᵢ, J eᵢ)`
  for a nowhere-vanishing `h` with `∂bar_c h = 0`.
* `TauCeti.SeibergWitten.laplacian_log_norm_sq_eq_mul_sub_one`: the difference equation of the
  log-modulus ratio.
* `TauCeti.SeibergWitten.norm_eq_one_and_eq_sub_phaseForm_of_tendsto`: under boundedness of the
  log-modulus ratio and the transverse vacuum condition, the two pairs differ by a gauge
  transformation.

## References

* C. H. Taubes, *Arbitrary N-vortex solutions to the first order Ginzburg-Landau equations*,
  Comm. Math. Phys. 72 (1980), 277–292.
* C. H. Taubes, *SW ⇒ Gr: from the Seiberg–Witten equations to pseudo-holomorphic curves*,
  J. Amer. Math. Soc. 9 (1996), 845–918.
-/

public section

noncomputable section

open ContinuousAlternatingMap Filter Set InnerProductSpace Laplacian
open scoped Topology RealInnerProductSpace

namespace TauCeti.SeibergWitten

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {J : AlmostComplexStructure E} {b b' c : E → E [⋀^Fin 1]→L[ℝ] ℝ} {α α' h : E → ℂ} {x : E}
  {ι : Type*} [Fintype ι]

/-- **The Laplacian of `log |h|²` for a holomorphic unit.** Let `J` be orthogonal and let `h` be
`C²` at `x`, with `h x ≠ 0` and `∂bar_c h = 0` near `x` for the connection form `c`. Then
`Δ log |h|² = ∑ᵢ dc(eᵢ, J eᵢ)` at `x`, for every orthonormal basis `(eᵢ)`. -/
theorem laplacian_log_norm_sq_eq_sum_extDeriv (hJ : ∀ v w, ⟪J v, J w⟫ = ⟪v, w⟫)
    (hh : ContDiffAt ℝ 2 h x) (hx : h x ≠ 0) (hdbar : ∀ᶠ y in 𝓝 x, covariantDBar J c h y = 0)
    (e : OrthonormalBasis ι ℝ E) :
    Δ (fun y ↦ Real.log (‖h y‖ ^ 2)) x = ∑ i, extDeriv c x ![e i, J (e i)] := by
  have hu : ContDiffAt ℝ 2 (fun y ↦ Real.log (‖h y‖ ^ 2)) x :=
    ContDiffAt.log (ContDiffAt.norm_sq ℝ hh) (by positivity)
  -- Near `x`, the phase form `Im (h⁻¹ dh) + c` is `d^c_J log |h|²`.
  have hev : c =ᶠ[𝓝 x]
      J.twistedDifferential (fun y ↦ Real.log (‖h y‖ ^ 2)) - phaseForm h := by
    filter_upwards [hdbar, hh.eventually (by simp), hh.continuousAt.eventually_ne hx]
      with y hy hhy hy₀
    rw [Pi.sub_apply, ← covariantPhaseForm_eq_twistedDifferential_log J
      (hhy.differentiableAt (by simp)) hy₀ hy, covariantPhaseForm_apply, add_sub_cancel_left]
  rw [← J.sum_extDeriv_twistedDifferential_apply_eq_laplacian hJ _ x e, hev.extDeriv_eq,
    extDeriv_sub ((J.contDiffAt_twistedDifferential (n := 1) hu le_rfl).differentiableAt
      one_ne_zero)
      ((contDiffAt_phaseForm hh hx le_rfl).differentiableAt one_ne_zero),
    extDeriv_phaseForm hh hx, sub_zero]

/-- **The difference equation of the log-modulus ratio.** Let `J` be orthogonal, `(eᵢ)` an
orthonormal basis, and let `(b, α)` and `(b', α')` solve the flat vortex equations
`∂bar_a α = 0` everywhere and `∑ᵢ db(eᵢ, J eᵢ) = κ (|α|² - 1)` at `x`, with differentiable
connection forms. If `α = h α'` for a `C²` function `h`, `α'` is differentiable and nonzero on a
dense set, and `h x ≠ 0`, then the log-modulus ratio `w = log |h|²` satisfies
`Δ w = κ |α'|² (|h|² - 1)` at `x`, even if `α'` vanishes there. -/
theorem laplacian_log_norm_sq_eq_mul_sub_one (hJ : ∀ v w, ⟪J v, J w⟫ = ⟪v, w⟫)
    (e : OrthonormalBasis ι ℝ E) {κ : ℝ} (hb : Differentiable ℝ b) (hb' : Differentiable ℝ b')
    (hh : ContDiff ℝ 2 h) (hα' : Differentiable ℝ α') (hα : α = h * α')
    (hdense : Dense {y | α' y ≠ 0}) (hdbar : ∀ y, covariantDBar J b α y = 0)
    (hdbar' : ∀ y, covariantDBar J b' α' y = 0)
    (hF : ∑ i, extDeriv b x ![e i, J (e i)] = κ * (‖α x‖ ^ 2 - 1))
    (hF' : ∑ i, extDeriv b' x ![e i, J (e i)] = κ * (‖α' x‖ ^ 2 - 1)) (hx : h x ≠ 0) :
    Δ (fun y ↦ Real.log (‖h y‖ ^ 2)) x = κ * ‖α' x‖ ^ 2 * (‖h x‖ ^ 2 - 1) := by
  have hratio := covariantDBar_sub_eq_zero_of_dense J hb.continuous hb'.continuous
    (hh.of_le (by norm_num)) hα' hα hdense hdbar hdbar'
  rw [laplacian_log_norm_sq_eq_sum_extDeriv hJ hh.contDiffAt hx
      (Eventually.of_forall fun y ↦ congrFun hratio y) e, extDeriv_sub (hb x) (hb' x)]
  simp only [ContinuousAlternatingMap.sub_apply, Finset.sum_sub_distrib, hF, hF', hα,
    Pi.mul_apply, norm_mul]
  ring

/-- **Flat vortex fields with the same zeros differ by a gauge transformation.** Let `J` be
orthogonal, `(eᵢ)` an orthonormal basis, `κ ≥ 0`, and let `(b, α)` and `(b', α')` solve the flat
vortex equations `∂bar_a α = 0`, `∑ᵢ db(eᵢ, J eᵢ) = κ (|α|² - 1)` with differentiable connection
forms. Suppose `α = h α'` for a nowhere-vanishing `C²` function `h`, that `α'` is differentiable
and nonzero on a dense set, and that the log-modulus ratio `log |h|²` is bounded. If both
sections satisfy the transverse vacuum condition `|α| → 1` as the component along a nonzero
subspace `K` tends to infinity, then `|h| = 1` and `b = b' - Im (h⁻¹ dh)`: the pair `(b, α)` is
the gauge transform of `(b', α')` by `h`. -/
theorem norm_eq_one_and_eq_sub_phaseForm_of_tendsto (hJ : ∀ v w, ⟪J v, J w⟫ = ⟪v, w⟫)
    (e : OrthonormalBasis ι ℝ E) {κ : ℝ} (hκ : 0 ≤ κ) {K : Submodule ℝ E} (hK : K ≠ ⊥)
    (hb : Differentiable ℝ b) (hb' : Differentiable ℝ b') (hh : ContDiff ℝ 2 h)
    (hα' : Differentiable ℝ α') (hh₀ : ∀ y, h y ≠ 0) (hα : α = h * α')
    (hdense : Dense {y | α' y ≠ 0}) (hdbar : ∀ y, covariantDBar J b α y = 0)
    (hdbar' : ∀ y, covariantDBar J b' α' y = 0)
    (hF : ∀ y, ∑ i, extDeriv b y ![e i, J (e i)] = κ * (‖α y‖ ^ 2 - 1))
    (hF' : ∀ y, ∑ i, extDeriv b' y ![e i, J (e i)] = κ * (‖α' y‖ ^ 2 - 1))
    (hbdd : Bornology.IsBounded (range fun y ↦ Real.log (‖h y‖ ^ 2)))
    (hlim : Tendsto (fun y ↦ ‖α y‖) (comap (fun y ↦ ‖K.starProjection y‖) atTop) (𝓝 1))
    (hlim' : Tendsto (fun y ↦ ‖α' y‖) (comap (fun y ↦ ‖K.starProjection y‖) atTop) (𝓝 1)) :
    (∀ y, ‖h y‖ = 1) ∧ b = b' - phaseForm h := by
  have hpos (y : E) : 0 < ‖h y‖ ^ 2 := by have := hh₀ y; positivity
  have hw : ContDiff ℝ 2 fun y ↦ Real.log (‖h y‖ ^ 2) :=
    ContDiff.log (ContDiff.norm_sq ℝ hh) fun y ↦ (hpos y).ne'
  -- `log |h|²` and `|h|² - 1` have the same sign, so `w Δ w ≥ 0` for `w = log |h|²`.
  have hsign (y : E) : 0 ≤ Real.log (‖h y‖ ^ 2) * Δ (fun y ↦ Real.log (‖h y‖ ^ 2)) y := by
    rw [laplacian_log_norm_sq_eq_mul_sub_one hJ e hb hb' hh hα' hα hdense hdbar hdbar' (hF y)
      (hF' y) (hh₀ y)]
    have hκα : 0 ≤ κ * ‖α' y‖ ^ 2 := by positivity
    rcases le_total (‖h y‖ ^ 2) 1 with h1 | h1
    · nlinarith [mul_nonneg (neg_nonneg.2 (Real.log_nonpos (hpos y).le h1)) (sub_nonneg.2 h1)]
    · nlinarith [mul_nonneg (Real.log_nonneg h1) (sub_nonneg.2 h1)]
  -- Transversally, `log |h|² = log (|α|² / |α'|²) → log 1 = 0`.
  have hwlim : Tendsto (fun y ↦ Real.log (‖h y‖ ^ 2))
      (comap (fun y ↦ ‖K.starProjection y‖) atTop) (𝓝 0) := by
    have hq := ((hlim.pow 2).div (hlim'.pow 2) (by norm_num)).log (by norm_num)
    rw [one_pow, div_one, Real.log_one] at hq
    refine hq.congr' ?_
    filter_upwards [hlim'.eventually_ne one_ne_zero] with y hy
    rw [Pi.div_apply, hα, Pi.mul_apply, norm_mul, mul_pow,
      mul_div_cancel_right₀ _ (pow_ne_zero 2 hy)]
  have hw₀ := eq_zero_of_tendsto_comap_norm_starProjection_of_mul_laplacian_nonneg hK hw hsign
    hbdd hwlim
  refine ⟨fun y ↦ (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).1
    (Real.eq_one_of_pos_of_log_eq_zero (hpos y) (congrFun hw₀ y)), funext fun y ↦ ?_⟩
  -- The phase form `Im (h⁻¹ dh) + (b - b')` is `d^c_J log |h|² = 0`.
  have hratio := covariantDBar_sub_eq_zero_of_dense J hb.continuous hb'.continuous
    (hh.of_le (by norm_num)) hα' hα hdense hdbar hdbar'
  have hτ := covariantPhaseForm_eq_twistedDifferential_log J (hh.differentiable (by simp) y)
    (hh₀ y) (congrFun hratio y)
  rw [hw₀, J.twistedDifferential_zero, Pi.zero_apply, covariantPhaseForm_apply, Pi.sub_apply] at hτ
  rw [Pi.sub_apply, ← sub_eq_zero, ← hτ]
  abel

end TauCeti.SeibergWitten
