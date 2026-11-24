/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Contour.Cycle.HomologyCauchy
public import TauCeti.Analysis.Contour.Residue.Cycle
import TauCeti.Analysis.Calculus.IteratedFDeriv.CompLinear

/-!
# Polar parts and Cauchy's integral formula for contour cycles

The residue theorem for a contour cycle `C` in an open `U`, null-homologous there, whose trace
avoids the finite set `S` off which `f` is differentiable,

`Cycle.integral f C = 2πi · ∑_{s ∈ S} n_s(C) · Res_s f`,

is `TauCeti.Contour.Cycle.classicalResidueTheorem_nullHomologous`, in
`TauCeti.Analysis.Contour.Residue.Cycle`. This file adds two of its companions.

For `f` meromorphic at the points of `S`, a fixed polar-part decomposition `f = g + ∑_{s ∈ S} P_s`
on `U` splits the residue sum off the cycle integral before any null-homology hypothesis is used:
the single-curve identity

`∮_γ f = ∮_γ g + 2πi · ∑_{s ∈ S} n_s(γ) · Res_s f`

(`PolarPartDecomposition.intervalIntegral_deriv_smul_eq_analyticRemainder_add_sum`), summed over the
generators of `C` with their coefficients, leaves the integral of the analytic remainder `g`
standing. Null homology is imposed on `C` alone, and its individual generators need not be
null-homologous — the whole point of allowing formal integer combinations is that a cycle can bound
while its pieces do not.

Cauchy's integral formula for a cycle follows, as usual, by applying the residue theorem to the
Cauchy kernel `w ↦ f w / (w − z) ^ (k + 1)`, whose only singularity in `U` is at `z`. For a
function with values in a complex Banach space, the formula follows from the scalar one, since
continuous linear functionals commute with the cycle integral and separate points.

## Main results

* `TauCeti.Contour.Cycle.integral_eq_analyticRemainder_add_sum` — the residue sum splits off the
  cycle integral for a fixed polar-part decomposition, before any null-homology hypothesis is used.
* `TauCeti.Contour.Cycle.cauchyIntegralFormula_iteratedDeriv_nullHomologous`,
  `TauCeti.Contour.Cycle.cauchyIntegralFormula_nullHomologous` and
  `TauCeti.Contour.Cycle.cauchyIntegralFormula_deriv_nullHomologous` — Cauchy's integral formula
  for a cycle, for every iterated derivative and for `f` and `f'` themselves.
* `TauCeti.Contour.Cycle.cauchyIntegralFormula_iteratedDeriv_smul_nullHomologous`,
  `TauCeti.Contour.Cycle.cauchyIntegralFormula_smul_nullHomologous` and
  `TauCeti.Contour.Cycle.cauchyIntegralFormula_deriv_smul_nullHomologous`: the same formulas for
  functions with values in a complex Banach space, with the Cauchy kernel acting by scalar
  multiplication.

## References

* N. Hungerbühler, M. Wasem, *Non-integer valued winding numbers and a generalized Residue
  Theorem*, arXiv:1808.00997 (2018), §3.
* S. Lang, *Complex Analysis* (GTM 103), Ch. VI (the homology form of the residue theorem for
  cycles).
* L. Ahlfors, *Complex Analysis*, Ch. 4.

## Provenance

No formal source is vendored: the statements are assembled here from the repository's polar-part
decomposition and its homology Cauchy theorem for cycles, which are themselves migrated from the
AINTLIB `LeanModularForms` development.
-/

public section

open Complex MeasureTheory Set

open scoped Interval

namespace TauCeti.Contour.Cycle

variable {f : ℂ → ℂ} {S : Finset ℂ} {U : Set ℂ}

/-- **The residue sum splits off a cycle integral.** For a fixed polar-part decomposition of `f` on
`U` at `S`, a cycle lying in `U` whose trace avoids `S` integrates to the integral of the analytic
remainder plus `2πi` times the winding-weighted residue sum.

Nothing is assumed here about `f` beyond the decomposition, and — crucially for the cycle case —
nothing about null-homology: the identity is summed from its single-curve form
(`TauCeti.Contour.PolarPartDecomposition.intervalIntegral_deriv_smul_eq_analyticRemainder_add_sum`)
over the generators of the cycle, each of which may wind arbitrarily around the holes of `U`. -/
theorem integral_eq_analyticRemainder_add_sum (decomp : PolarPartDecomposition f S U) {C : Cycle}
    (hCU : IsIn C U) (hoff : ∀ s ∈ S, s ∉ trace C) :
    integral f C = integral decomp.analyticRemainder C
      + 2 * (Real.pi : ℂ) * Complex.I * ∑ s ∈ S, windingNumber s C * residue f s := by
  classical
  -- The single-curve splitting, applied to each generator in the canonical support.
  have hgen : ∀ γ ∈ FreeAddCommGroup.support C,
      (∫ t in γ.a..γ.b, deriv (⇑γ) t • f (γ t))
        = (∫ t in γ.a..γ.b, deriv (⇑γ) t • decomp.analyticRemainder (γ t))
          + 2 * (Real.pi : ℂ) * Complex.I *
              ∑ s ∈ S, TauCeti.Contour.windingNumber (⇑γ) γ.a γ.b s * residue f s := fun γ hγ ↦
    decomp.intervalIntegral_deriv_smul_eq_analyticRemainder_add_sum
      γ.absolutelyContinuousOnInterval
      (hCU.mapsTo_of_mem_support hγ) γ.source_eq_target
      (fun t ht hmem ↦ hoff _ (Finset.mem_coe.mp hmem) (mem_trace_iff.mpr ⟨γ, hγ, t, ht, rfl⟩))
  calc
    integral f C
        = ∑ γ ∈ FreeAddCommGroup.support C, FreeAddCommGroup.coeff γ C •
            ((∫ t in γ.a..γ.b, deriv (⇑γ) t • decomp.analyticRemainder (γ t))
              + 2 * (Real.pi : ℂ) * Complex.I *
                  ∑ s ∈ S, TauCeti.Contour.windingNumber (⇑γ) γ.a γ.b s * residue f s) := by
          rw [integral_eq_sum_support]
          exact Finset.sum_congr rfl fun γ hγ ↦ by rw [hgen γ hγ]
    _ = integral decomp.analyticRemainder C
          + 2 * (Real.pi : ℂ) * Complex.I * ∑ s ∈ S, windingNumber s C * residue f s :=
          sum_support_smul_eq_integral_add_windingNumber_sum _ _ _ _ _

/-- **Cauchy's integral formula for a cycle, for the `k`-th derivative.** Let `f` be holomorphic on
an open `U`, let `C` be a contour cycle in `U` that is null-homologous there, and let `z` lie
off the trace of `C`. Then for every `k`,

`Cycle.integral (fun w ↦ f w / (w − z) ^ (k + 1)) C = 2πi · n_z(C) · f⁽ᵏ⁾(z) / k !`.

Only the residue at `z` contributes: the residue theorem for a null-homologous cycle applied to the
Cauchy kernel `w ↦ f w / (w − z) ^ (k + 1)`, whose only possible singularity in `U` is at `z`. -/
theorem cauchyIntegralFormula_iteratedDeriv_nullHomologous {z : ℂ} (hU : IsOpen U)
    (hf : DifferentiableOn ℂ f U) {C : Cycle} (hCU : IsIn C U) (hnull : IsNullHomologous C U)
    (hoff : z ∉ trace C) (k : ℕ) :
    integral (fun w ↦ f w / (w - z) ^ (k + 1)) C
      = 2 * (Real.pi : ℂ) * Complex.I * windingNumber z C *
          (iteratedDeriv k f z / (k.factorial : ℂ)) := by
  have hker := classicalResidueTheorem_nullHomologous (f := fun w ↦ f w / (w - z) ^ (k + 1))
    (S := {z}) hU ?_ hCU ?_ hnull
  · by_cases hz : z ∈ U
    · rw [hker, Finset.sum_singleton,
        residue_div_sub_pow_of_analyticAt (hf.analyticOnNhd hU z hz) k]
      ring
    · rw [hker, Finset.sum_singleton, isNullHomologous_iff.mp hnull z hz]
      simp
  · -- Off `z` the kernel is a quotient of holomorphic functions with non-vanishing denominator.
    rw [Finset.coe_singleton]
    exact fun w hw ↦ ((hf w hw.1).mono Set.sdiff_subset).div (by fun_prop)
      (pow_ne_zero _ (sub_ne_zero.mpr hw.2))
  · exact fun s hs ↦ (Finset.mem_singleton.mp hs) ▸ hoff

/-- **Cauchy's integral formula for a cycle.** For `f` holomorphic on an open `U`, `C` a contour
cycle in `U` that is null-homologous there, and `z` off the trace of `C`,

`Cycle.integral (fun w ↦ f w / (w − z)) C = 2πi · n_z(C) · f z`,

so that `f z · n_z(C) = (2πi)⁻¹ ∮_C f(w)/(w − z) dw`: the Cauchy-type integral over the cycle
recovers the value of `f` at `z`, counted with the multiplicity with which `C` winds around it. The
`S = ∅` companion of this statement is the homology Cauchy theorem for cycles
(`TauCeti.Contour.Cycle.homologyCauchyTheorem`). -/
theorem cauchyIntegralFormula_nullHomologous {z : ℂ} (hU : IsOpen U) (hf : DifferentiableOn ℂ f U)
    {C : Cycle} (hCU : IsIn C U) (hnull : IsNullHomologous C U)
    (hoff : z ∉ trace C) :
    integral (fun w ↦ f w / (w - z)) C
      = 2 * (Real.pi : ℂ) * Complex.I * windingNumber z C * f z := by
  simpa using cauchyIntegralFormula_iteratedDeriv_nullHomologous hU hf hCU hnull hoff 0

/-- **Cauchy's integral formula for a cycle, first derivative.** The `k = 1` case of
`TauCeti.Contour.Cycle.cauchyIntegralFormula_iteratedDeriv_nullHomologous`, stated with
`deriv f z`:

`Cycle.integral (fun w ↦ f w / (w − z) ^ 2) C = 2πi · n_z(C) · f' z`. -/
theorem cauchyIntegralFormula_deriv_nullHomologous {z : ℂ} (hU : IsOpen U)
    (hf : DifferentiableOn ℂ f U) {C : Cycle} (hCU : IsIn C U) (hnull : IsNullHomologous C U)
    (hoff : z ∉ trace C) :
    integral (fun w ↦ f w / (w - z) ^ 2) C
      = 2 * (Real.pi : ℂ) * Complex.I * windingNumber z C * deriv f z := by
  simpa [iteratedDeriv_one] using
    cauchyIntegralFormula_iteratedDeriv_nullHomologous hU hf hCU hnull hoff 1

section VectorValued

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

/-- **Cauchy's integral formula for a cycle, for the `k`-th derivative of a Banach-valued
function.** Let `f` be holomorphic on an open `U` with values in a complex Banach space, let `C` be
a contour cycle in `U` that is null-homologous there, and let `z` lie off the trace of `C`.
Then for every `k`,

`Cycle.integral (fun w ↦ ((w − z) ^ (k + 1))⁻¹ • f w) C = (2πi · n_z(C) / k !) • f⁽ᵏ⁾(z)`.

For `E = ℂ` this is `TauCeti.Contour.Cycle.cauchyIntegralFormula_iteratedDeriv_nullHomologous`. -/
theorem cauchyIntegralFormula_iteratedDeriv_smul_nullHomologous {f : ℂ → E} {z : ℂ}
    (hU : IsOpen U) (hf : DifferentiableOn ℂ f U) {C : Cycle} (hCU : IsIn C U)
    (hnull : IsNullHomologous C U) (hoff : z ∉ trace C) (k : ℕ) :
    integral (fun w ↦ ((w - z) ^ (k + 1))⁻¹ • f w) C
      = (2 * (Real.pi : ℂ) * Complex.I * windingNumber z C / (k.factorial : ℂ)) •
          iteratedDeriv k f z := by
  have hcont : ContinuousOn (fun w ↦ ((w - z) ^ (k + 1))⁻¹ • f w) (trace C) :=
    (((continuousOn_id.sub continuousOn_const).pow _).inv₀ fun w hw ↦
      pow_ne_zero _ (sub_ne_zero.mpr (by rintro rfl; exact hoff hw))).smul
        (hf.continuousOn.mono (isIn_iff.mp hCU))
  refine (SeparatingDual.eq_iff_forall_dual_eq (R := ℂ)).2 fun ℓ ↦ ?_
  rw [← integral_comp_comm (fun _ ↦ intervalIntegrable_of_mem_support hcont), map_smul]
  by_cases hz : z ∈ U
  · rw [← ℓ.iteratedDeriv_comp_left ((hf.contDiffOn (n := k) hU).contDiffAt (hU.mem_nhds hz))
      le_rfl]
    simp only [map_smul, smul_eq_mul, ← div_eq_inv_mul, Function.comp_def]
    rw [cauchyIntegralFormula_iteratedDeriv_nullHomologous (f := fun w ↦ ℓ (f w)) hU
      (ℓ.differentiable.comp_differentiableOn hf) hCU hnull hoff k]
    ring
  · have hw := isNullHomologous_iff.mp hnull z hz
    simp only [map_smul, smul_eq_mul, ← div_eq_inv_mul]
    rw [cauchyIntegralFormula_iteratedDeriv_nullHomologous (f := fun w ↦ ℓ (f w)) hU
      (ℓ.differentiable.comp_differentiableOn hf) hCU hnull hoff k, hw]
    simp

/-- **Cauchy's integral formula for a cycle, for a Banach-valued function.** For `f` holomorphic
on an open `U` with values in a complex Banach space, `C` a contour cycle in `U` that is
null-homologous there, and `z` off the trace of `C`,

`Cycle.integral (fun w ↦ (w − z)⁻¹ • f w) C = (2πi · n_z(C)) • f z`. -/
theorem cauchyIntegralFormula_smul_nullHomologous {f : ℂ → E} {z : ℂ} (hU : IsOpen U)
    (hf : DifferentiableOn ℂ f U) {C : Cycle} (hCU : IsIn C U) (hnull : IsNullHomologous C U)
    (hoff : z ∉ trace C) :
    integral (fun w ↦ (w - z)⁻¹ • f w) C
      = (2 * (Real.pi : ℂ) * Complex.I * windingNumber z C) • f z := by
  simpa using cauchyIntegralFormula_iteratedDeriv_smul_nullHomologous hU hf hCU hnull hoff 0

/-- **Cauchy's integral formula for a cycle, first derivative of a Banach-valued function.** The
`k = 1` case of `TauCeti.Contour.Cycle.cauchyIntegralFormula_iteratedDeriv_smul_nullHomologous`,
stated with `deriv f z`:

`Cycle.integral (fun w ↦ ((w − z) ^ 2)⁻¹ • f w) C = (2πi · n_z(C)) • f' z`. -/
theorem cauchyIntegralFormula_deriv_smul_nullHomologous {f : ℂ → E} {z : ℂ} (hU : IsOpen U)
    (hf : DifferentiableOn ℂ f U) {C : Cycle} (hCU : IsIn C U) (hnull : IsNullHomologous C U)
    (hoff : z ∉ trace C) :
    integral (fun w ↦ ((w - z) ^ 2)⁻¹ • f w) C
      = (2 * (Real.pi : ℂ) * Complex.I * windingNumber z C) • deriv f z := by
  simpa [iteratedDeriv_one] using
    cauchyIntegralFormula_iteratedDeriv_smul_nullHomologous hU hf hCU hnull hoff 1

end VectorValued

end TauCeti.Contour.Cycle

end
