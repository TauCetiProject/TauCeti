/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.UpperHalfPlane.Nontangential.Bounds
public import TauCeti.Analysis.Complex.UpperHalfPlane.Poisson.Function

/-!
# Nontangential maximal bounds for the Poisson integral of a function

For a complex function `h` on `ℝ`, the Poisson integral `P[h](z) = ∫ P(z, x) h(x) dx`
(`TauCeti.upperHalfPlanePoissonIntegralFun`) is dominated on the open upper half-plane by the
extended Poisson integral of the measure `|h| dx`:
`‖P[h](z)‖ₑ ≤ ∫ P(z, x) |h(x)| dx` (`TauCeti.enorm_upperHalfPlanePoissonIntegralFun_le`).
So the nontangential maximal bounds proved for `P[|h| dx]` hold for `P[h]`:

* the cone domination `M^α_k P[h] ≤ max 2 (1 + 2 α ^ 2) · M h`, which is `3 M h` for `α = 1`;
* the strong type bound `∫ (M^α_k P[h]) ^ p ≤ C ^ p K_p ∫ |h| ^ p` for `1 < p`;
* the weak type bound `t |{M^α_k P[h] > t}| ≤ 4 C ∫ |h|`;
* for `h ∈ L¹(Π)`, the localisation
  `M_1 P[h](x) ≤ 3 M(h 1_{[-R-2, R+2]})(x) + 2 (R + 2) ^ 2 / π · ∫ |h| dΠ` for `|x| ≤ R` and the
  local weak type bound `t |{x ∈ [-R, R] : M_1 P[h](x) > t}| ≤ C_R ∫ |h| dΠ`.

## Main results

* `TauCeti.nontangentialMaximalFunction_upperHalfPlanePoissonIntegralFun_le`: the cone domination.
* `TauCeti.lintegral_rpow_nontangentialMaximalFunction_upperHalfPlanePoissonIntegralFun_le`: the
  strong type bound.
* `TauCeti.mul_volume_lt_nontangentialMaximalFunction_upperHalfPlanePoissonIntegralFun_le`: the
  weak type bound.
* `TauCeti.nontangentialMaximalFunction_one_one_upperHalfPlanePoissonIntegralFun_le` and
  `TauCeti.exists_mul_volume_lt_nontangentialMaximalFunction_upperHalfPlanePoissonIntegralFun_le`:
  the localisation and the local weak type bound for `h ∈ L¹(Π)`.

## References

* J. B. Garnett, *Bounded Analytic Functions*, revised 1st ed., Springer (2007), Chapter I, §4.
* L. Mauth, *On pointwise convergence of the non-linear Fourier transform*, arXiv:2210.12286
  (2022), Lemmas 5 and 6 and Corollary 1.
-/

public section

noncomputable section

namespace TauCeti

open Complex MeasureTheory Set

open scoped Real ENNReal

/-- The nontangential maximal function of `P[h]` is at most that of the Poisson integral of
`|h| dx`. -/
theorem
    nontangentialMaximalFunction_upperHalfPlanePoissonIntegralFun_le_upperHalfPlanePoissonLIntegral
    (α : ℝ) (k : ℝ≥0∞) (h : ℝ → ℂ) (x : ℝ) :
    nontangentialMaximalFunction α k (upperHalfPlanePoissonIntegralFun h) x ≤
      nontangentialMaximalFunction α k
        (upperHalfPlanePoissonLIntegral (volume.withDensity fun s => ‖h s‖ₑ)) x :=
  nontangentialMaximalFunction_mono_fun fun _ hz => by
    simpa using enorm_upperHalfPlanePoissonIntegralFun_le h (mem_nontangentialCone.1 hz).1

/-- **The nontangential maximal bound for `P[h]`.** Over cones of aperture `α` and any height,
`M^α_k P[h] ≤ max 2 (1 + 2 α ^ 2) · M h`. -/
theorem nontangentialMaximalFunction_upperHalfPlanePoissonIntegralFun_le (α : ℝ) (k : ℝ≥0∞)
    (h : ℝ → ℂ) (x : ℝ) :
    nontangentialMaximalFunction α k (upperHalfPlanePoissonIntegralFun h) x ≤
      ENNReal.ofReal (max 2 (1 + 2 * α ^ 2)) * maximalFunction volume h x :=
  (nontangentialMaximalFunction_upperHalfPlanePoissonIntegralFun_le_upperHalfPlanePoissonLIntegral
    α k h x).trans (nontangentialMaximalFunction_upperHalfPlanePoissonLIntegral_le α k h x)

/-- **The nontangential maximal bound for `P[h]` with aperture one.** `M_k P[h] ≤ 3 M h`. -/
theorem nontangentialMaximalFunction_one_upperHalfPlanePoissonIntegralFun_le (k : ℝ≥0∞)
    (h : ℝ → ℂ) (x : ℝ) :
    nontangentialMaximalFunction 1 k (upperHalfPlanePoissonIntegralFun h) x ≤
      3 * maximalFunction volume h x :=
  (nontangentialMaximalFunction_upperHalfPlanePoissonIntegralFun_le 1 k h x).trans_eq
    (by norm_num)

/-- **The strong type bound for `P[h]`.** For `1 < p`,
`∫ (M^α_k P[h]) ^ p ≤ C ^ p K_p ∫ |h| ^ p` with `C = max 2 (1 + 2 α ^ 2)` and `K_p` the constant
of the strong type bound for the Hardy–Littlewood maximal function on `ℝ`. -/
theorem lintegral_rpow_nontangentialMaximalFunction_upperHalfPlanePoissonIntegralFun_le (α : ℝ)
    (k : ℝ≥0∞) {h : ℝ → ℂ} (hh : AEMeasurable (fun x => ‖h x‖ₑ)) {p : ℝ} (hp : 1 < p) :
    ∫⁻ x, nontangentialMaximalFunction α k (upperHalfPlanePoissonIntegralFun h) x ^ p ≤
      ENNReal.ofReal (max 2 (1 + 2 * α ^ 2)) ^ p * maximalFunctionConst 1 p *
        ∫⁻ x, ‖h x‖ₑ ^ p :=
  (lintegral_mono fun x => ENNReal.rpow_le_rpow
    (nontangentialMaximalFunction_upperHalfPlanePoissonIntegralFun_le_upperHalfPlanePoissonLIntegral
      α k h x) (by linarith)).trans
    (lintegral_rpow_nontangentialMaximalFunction_upperHalfPlanePoissonLIntegral_le α k hh hp)

/-- **The weak type bound for `P[h]`.** `t |{M^α_k P[h] > t}| ≤ 4 C ∫ |h|` with
`C = max 2 (1 + 2 α ^ 2)`. -/
theorem mul_volume_lt_nontangentialMaximalFunction_upperHalfPlanePoissonIntegralFun_le (α : ℝ)
    (k : ℝ≥0∞) (h : ℝ → ℂ) (t : ℝ≥0∞) :
    t * volume {x | t < nontangentialMaximalFunction α k (upperHalfPlanePoissonIntegralFun h) x} ≤
      4 * ENNReal.ofReal (max 2 (1 + 2 * α ^ 2)) * ∫⁻ x, ‖h x‖ₑ :=
  (mul_le_mul' le_rfl (measure_mono <| ofPred_subset_ofPred.2 fun x hx => hx.trans_le
    (nontangentialMaximalFunction_upperHalfPlanePoissonIntegralFun_le_upperHalfPlanePoissonLIntegral
      α k h x))).trans
    (mul_volume_lt_nontangentialMaximalFunction_upperHalfPlanePoissonLIntegral_le α k h t)

/-- **Localisation of the nontangential maximal function of `P[h]`.** For `h ∈ L¹(Π)` and
`|x| ≤ R`, `M_1 P[h](x) ≤ 3 M(h 1_{[-R-2, R+2]})(x) + 2 (R + 2) ^ 2 / π · ∫ |h| dΠ`, where `M_1`
is the nontangential maximal function over cones of aperture and height one. -/
theorem nontangentialMaximalFunction_one_one_upperHalfPlanePoissonIntegralFun_le {h : ℝ → ℂ}
    (hh : AEMeasurable (fun s => ‖h s‖ₑ)) {R x : ℝ} (hx : |x| ≤ R) :
    nontangentialMaximalFunction 1 1 (upperHalfPlanePoissonIntegralFun h) x ≤
      3 * maximalFunction volume ((Icc (-(R + 2)) (R + 2)).indicator h) x +
        ENNReal.ofReal (2 * (R + 2) ^ 2 / π) *
          ∫⁻ s, ‖h s‖ₑ ∂upperHalfPlanePoissonMeasure :=
  (nontangentialMaximalFunction_upperHalfPlanePoissonIntegralFun_le_upperHalfPlanePoissonLIntegral
    1 1 h x).trans (nontangentialMaximalFunction_one_one_upperHalfPlanePoissonLIntegral_le hh hx)

/-- **The local weak type bound for `P[h]`.** For `R` there is a constant `C_R`, depending only
on `R`, such that `t |{x ∈ [-R, R] : M_1 P[h](x) > t}| ≤ C_R ∫ |h| dΠ` for every `h` with `‖h‖ₑ`
a.e.-measurable and every `t`. -/
theorem exists_mul_volume_lt_nontangentialMaximalFunction_upperHalfPlanePoissonIntegralFun_le
    (R : ℝ) : ∃ C : ℝ≥0∞, C ≠ ∞ ∧ ∀ h : ℝ → ℂ, AEMeasurable (fun s => ‖h s‖ₑ) → ∀ t : ℝ≥0∞,
      t * volume {x ∈ Icc (-R) R | t < nontangentialMaximalFunction 1 1
          (upperHalfPlanePoissonIntegralFun h) x} ≤
        C * ∫⁻ s, ‖h s‖ₑ ∂upperHalfPlanePoissonMeasure := by
  obtain ⟨C, hC, hbound⟩ :=
    exists_mul_volume_lt_nontangentialMaximalFunction_upperHalfPlanePoissonLIntegral_le
      (F := ℂ) R
  refine ⟨C, hC, fun h hh t => (mul_le_mul' le_rfl (measure_mono <|
    ofPred_subset_ofPred.2 fun x hx => ⟨hx.1, hx.2.trans_le
    (nontangentialMaximalFunction_upperHalfPlanePoissonIntegralFun_le_upperHalfPlanePoissonLIntegral
      1 1 h x)⟩)).trans (hbound h hh t)⟩

end TauCeti
