/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Distribution.TestFunction.Divergence
public import TauCeti.Analysis.Sobolev.WeakDeriv.Basic
import TauCeti.Analysis.Distribution.TestFunction.NormDuality
import TauCeti.Analysis.Sobolev.WeakDeriv.Divergence
import TauCeti.Analysis.Sobolev.WeakDeriv.Lipschitz

/-!
# The total variation of a function on an open set

Let `Ω` be an open set of a finite-dimensional real inner product space `E`. The
**total variation** of a function `u : E → ℝ` on `Ω` is the extended supremum

`|Du|(Ω) = ⨆ { ∫ u div φ | φ ∈ 𝓓(Ω, E), ‖φ x‖ ≤ 1 for all x }`

over smooth vector fields compactly supported in `Ω` with pointwise norm at most one
(`TauCeti.totalVariationOn`). The functions of bounded variation on `Ω` are the
`u ∈ L¹(Ω)` for which it is finite, and the perimeter of a set is the total variation of its
indicator. When the distributional derivative `Du` is a vector-valued Radon measure, this
supremum is the total variation measure `|Du|` evaluated on `Ω`; that comparison is not proved
here. The definition by duality is meaningful for every locally integrable function, with no
differentiability assumption, which is what lower semicontinuity and compactness arguments need.

The measure `μ` is a parameter, as in `TauCeti.HasWeakFDerivOn`. The pairing `∫ u div φ ∂μ` is
the distributional pairing for an additive Haar measure `μ`, and that hypothesis is carried by
the results that need it: a constant function has total variation zero only against a
translation-invariant measure.

For `u` not locally integrable on `Ω` the integrals in the supremum may be Mathlib's junk value
`0` for non-integrable functions, so the results that split integrals assume local integrability.

## Main declarations

* `TauCeti.totalVariationOn μ Ω u`: the total variation of `u` on `Ω`.
* `TauCeti.ofReal_abs_integral_le_totalVariationOn`: every admissible pairing is bounded by the
  total variation, and `TauCeti.totalVariationOn_le_iff` characterises upper bounds.
* `TauCeti.ofReal_abs_integral_le_ofReal_mul_totalVariationOn`: a test vector field bounded by `c`
  pairs to at most `c |Du|(Ω)`.
* `TauCeti.totalVariationOn_congr_ae`: the total variation only sees `u` almost everywhere on
  `Ω`.
* `TauCeti.totalVariationOn_mono` and `TauCeti.totalVariationOn_iSup`: monotonicity and inner
  continuity in the open set.
* `TauCeti.totalVariationOn_neg`, `TauCeti.totalVariationOn_smul` and
  `TauCeti.totalVariationOn_add_le`: the total variation is a seminorm.
* `TauCeti.totalVariationOn_add_const` and `TauCeti.totalVariationOn_const`: against an additive
  Haar measure, constants have no variation.
* `TauCeti.totalVariationOn_le_liminf_of_tendsto_integral` and
  `TauCeti.totalVariationOn_le_liminf`: lower semicontinuity under distributional convergence and
  under convergence in `L¹_loc(Ω)`.
* `TauCeti.HasWeakFDerivOn.totalVariationOn_le_setLIntegral_enorm`: a weakly differentiable
  function has total variation at most the integral of the norm of its weak derivative.
* `TauCeti.HasWeakFDerivOn.totalVariationOn_eq_setLIntegral_enorm`: against an additive Haar
  measure this is an equality, so a `W^{1,1}(Ω)` function has bounded variation on `Ω`, with
  variation the `L¹` norm of its weak derivative
  (`TauCeti.HasWeakFDerivOn.totalVariationOn_lt_top_iff_integrableOn`).
* `LocallyLipschitzOn.totalVariationOn_eq_setLIntegral_enorm_fderiv`: for a locally Lipschitz
  function, in particular a `C¹` one, the total variation is `∫_Ω ‖Du‖` for its classical
  derivative.

## References

* L. Ambrosio, N. Fusco, D. Pallara, *Functions of Bounded Variation and Free Discontinuity
  Problems*, Definition 3.4 and Remark 3.5.
* F. Maggi, *Sets of Finite Perimeter and Geometric Variational Problems*, §12.1.
-/

public section

noncomputable section

namespace TauCeti

open MeasureTheory TopologicalSpace Filter TestFunction
open scoped ENNReal Distributions Topology

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] {μ : Measure E} {Ω Ω' : Opens E} {u v : E → ℝ}

/-- The **total variation** of `u : E → ℝ` on the open set `Ω`, relative to the measure `μ`:
the extended supremum of `∫ div φ * u ∂μ` over test vector fields `φ ∈ 𝓓(Ω, E)` with
`‖φ x‖ ≤ 1` everywhere. For `μ` an additive Haar measure this is the variation `|Du|(Ω)` of the
distributional derivative of `u` on `Ω`, defined by duality. -/
def totalVariationOn (μ : Measure E) (Ω : Opens E) (u : E → ℝ) : ℝ≥0∞ :=
  ⨆ (φ : 𝓓(Ω, E)) (_ : ∀ x, ‖φ x‖ ≤ 1), ENNReal.ofReal (∫ x, divergenceCLM φ x * u x ∂μ)

/-- The defining supremum of `TauCeti.totalVariationOn`. -/
theorem totalVariationOn_def : totalVariationOn μ Ω u =
    ⨆ (φ : 𝓓(Ω, E)) (_ : ∀ x, ‖φ x‖ ≤ 1), ENNReal.ofReal (∫ x, divergenceCLM φ x * u x ∂μ) :=
  (rfl)

/-- An admissible test vector field bounds the total variation from below. -/
theorem ofReal_integral_le_totalVariationOn (φ : 𝓓(Ω, E)) (hφ : ∀ x, ‖φ x‖ ≤ 1) :
    ENNReal.ofReal (∫ x, divergenceCLM φ x * u x ∂μ) ≤ totalVariationOn μ Ω u :=
  le_iSup₂ (f := fun (φ : 𝓓(Ω, E)) (_ : ∀ x, ‖φ x‖ ≤ 1) =>
    ENNReal.ofReal (∫ x, divergenceCLM φ x * u x ∂μ)) φ hφ

/-- Upper bounds for the total variation are tested on admissible test vector fields. -/
theorem totalVariationOn_le_iff {c : ℝ≥0∞} : totalVariationOn μ Ω u ≤ c ↔
    ∀ φ : 𝓓(Ω, E), (∀ x, ‖φ x‖ ≤ 1) → ENNReal.ofReal (∫ x, divergenceCLM φ x * u x ∂μ) ≤ c :=
  iSup₂_le_iff

/-- Every admissible pairing is bounded in absolute value by the total variation. -/
theorem ofReal_abs_integral_le_totalVariationOn (φ : 𝓓(Ω, E)) (hφ : ∀ x, ‖φ x‖ ≤ 1) :
    ENNReal.ofReal |∫ x, divergenceCLM φ x * u x ∂μ| ≤ totalVariationOn μ Ω u := by
  rcases le_total 0 (∫ x, divergenceCLM φ x * u x ∂μ) with h | h
  · rw [abs_of_nonneg h]
    exact ofReal_integral_le_totalVariationOn φ hφ
  · have hneg : -∫ x, divergenceCLM φ x * u x ∂μ = ∫ x, divergenceCLM (-φ) x * u x ∂μ := by
      simp [← integral_neg]
    rw [abs_of_nonpos h, hneg]
    exact ofReal_integral_le_totalVariationOn (-φ) fun x => by simpa using hφ x

/-- The total variation of the zero function vanishes. -/
@[simp]
theorem totalVariationOn_zero : totalVariationOn μ Ω 0 = 0 := by
  simp [totalVariationOn_def]

/-- **Locality.** The total variation on `Ω` only depends on `u` almost everywhere on `Ω`. -/
theorem totalVariationOn_congr_ae (h : u =ᵐ[μ.restrict Ω] v) :
    totalVariationOn μ Ω u = totalVariationOn μ Ω v := by
  simp_rw [totalVariationOn_def]
  refine iSup_congr fun φ => iSup_congr fun _ => congrArg ENNReal.ofReal ?_
  have hu := setIntegral_smul_eq_integral_smul (μ := μ) (w := u) (divergenceCLM φ)
  have hv := setIntegral_smul_eq_integral_smul (μ := μ) (w := v) (divergenceCLM φ)
  simp only [smul_eq_mul] at hu hv
  rw [← hu, ← hv]
  exact integral_congr_ae (h.mono fun x hx => by simp only [hx])

/-- **Monotonicity in the open set.** A test vector field on a smaller open set is one on the
larger set, so the total variation grows with the open set. -/
theorem totalVariationOn_mono (h : Ω' ≤ Ω) :
    totalVariationOn μ Ω' u ≤ totalVariationOn μ Ω u := by
  refine totalVariationOn_le_iff.mpr fun φ hφ => ?_
  have hcoe : ((monoCLM ℝ φ : 𝓓(Ω, E)) : E → E) = φ := by
    simp [monoCLM_apply, h]
  simpa only [divergenceCLM_monoCLM h] using
    ofReal_integral_le_totalVariationOn (μ := μ) (u := u) (monoCLM ℝ φ : 𝓓(Ω, E))
      fun x => by simpa only [hcoe] using hφ x

/-- **Inner continuity in the open set.** The total variation on the union of a directed family
of open sets is the supremum of the total variations on its members. -/
theorem totalVariationOn_iSup {ι : Type*} [Nonempty ι] {Ω : ι → Opens E}
    (hΩ : Directed (· ≤ ·) Ω) :
    totalVariationOn μ (⨆ i, Ω i) u = ⨆ i, totalVariationOn μ (Ω i) u := by
  refine le_antisymm (totalVariationOn_le_iff.mpr fun φ hφ => ?_)
    (iSup_le fun i => totalVariationOn_mono (le_iSup Ω i))
  -- The compact support of a test vector field lies in one member of the family.
  obtain ⟨i, hi⟩ := φ.hasCompactSupport.isCompact.elim_directed_cover (fun i => (Ω i : Set E))
    (fun i => (Ω i).isOpen) (by simpa using φ.tsupport_subset) (hΩ.mono_comp _ fun _ _ h => h)
  let φ' : 𝓓(Ω i, E) := ⟨φ, φ.contDiff, φ.hasCompactSupport, hi⟩
  have hφ' (x : E) : divergenceCLM φ' x = divergenceCLM φ x := by simp [φ']
  refine le_iSup_of_le i ?_
  simpa only [hφ'] using ofReal_integral_le_totalVariationOn (μ := μ) (u := u) φ' hφ

/-- The total variation of `-u` is that of `u`. -/
@[simp]
theorem totalVariationOn_neg : totalVariationOn μ Ω (-u) = totalVariationOn μ Ω u := by
  have key : ∀ w : E → ℝ, totalVariationOn μ Ω (-w) ≤ totalVariationOn μ Ω w := fun w =>
    totalVariationOn_le_iff.mpr fun φ hφ => by
      have : ∫ x, divergenceCLM φ x * (-w) x ∂μ = ∫ x, divergenceCLM (-φ) x * w x ∂μ := by
        simp
      rw [this]
      exact ofReal_integral_le_totalVariationOn (-φ) fun x => by simpa using hφ x
  exact le_antisymm (key u) (by simpa using key (-u))

/-- The total variation is positively homogeneous: `|D(c u)|(Ω) = c |Du|(Ω)` for `c ≥ 0`. -/
theorem totalVariationOn_smul_of_nonneg {c : ℝ} (hc : 0 ≤ c) :
    totalVariationOn μ Ω (c • u) = ENNReal.ofReal c * totalVariationOn μ Ω u := by
  simp_rw [totalVariationOn_def, ENNReal.mul_iSup]
  refine iSup_congr fun φ => iSup_congr fun _ => ?_
  rw [← ENNReal.ofReal_mul hc, ← integral_const_mul]
  congr 2 with x
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

/-- The total variation is absolutely homogeneous: `|D(c u)|(Ω) = |c| |Du|(Ω)`. -/
theorem totalVariationOn_smul (c : ℝ) :
    totalVariationOn μ Ω (c • u) = ‖c‖ₑ * totalVariationOn μ Ω u := by
  rw [Real.enorm_eq_ofReal_abs]
  rcases le_total 0 c with hc | hc
  · rw [abs_of_nonneg hc, totalVariationOn_smul_of_nonneg hc]
  · rw [abs_of_nonpos hc, ← totalVariationOn_smul_of_nonneg (neg_nonneg.mpr hc), neg_smul,
      totalVariationOn_neg]

/-- A test vector field bounded by `c` pairs to at most `c |Du|(Ω)`. -/
theorem ofReal_abs_integral_le_ofReal_mul_totalVariationOn (φ : 𝓓(Ω, E)) {c : ℝ}
    (hφ : ∀ x, ‖φ x‖ ≤ c) :
    ENNReal.ofReal |∫ x, divergenceCLM φ x * u x ∂μ| ≤
      ENNReal.ofReal c * totalVariationOn μ Ω u := by
  rcases le_or_gt c 0 with hc | hc
  · have hφ0 : φ = 0 := by
      ext x
      exact norm_le_zero_iff.1 ((hφ x).trans hc)
    simp [hφ0]
  -- Pair `c⁻¹ • φ`, which is admissible, with `c • u`.
  rw [← totalVariationOn_smul_of_nonneg hc.le]
  convert ofReal_abs_integral_le_totalVariationOn (u := c • u) (c⁻¹ • φ) fun x => ?_ using 3
  · congr 1 with x
    simp only [map_smul, smul_apply, Pi.smul_apply, smul_eq_mul]
    field_simp
  · simpa [norm_smul, abs_of_pos hc, inv_mul_le_iff₀ hc] using hφ x

/-- **Subadditivity.** For functions locally integrable on `Ω`,
`|D(u + v)|(Ω) ≤ |Du|(Ω) + |Dv|(Ω)`. -/
theorem totalVariationOn_add_le [OpensMeasurableSpace E] (hu : LocallyIntegrableOn u Ω μ)
    (hv : LocallyIntegrableOn v Ω μ) :
    totalVariationOn μ Ω (u + v) ≤ totalVariationOn μ Ω u + totalVariationOn μ Ω v := by
  refine totalVariationOn_le_iff.mpr fun φ hφ => ?_
  have hsplit : ∫ x, divergenceCLM φ x * (u + v) x ∂μ =
      ∫ x, divergenceCLM φ x * u x ∂μ + ∫ x, divergenceCLM φ x * v x ∂μ := by
    simp_rw [Pi.add_apply, mul_add]
    exact integral_add (by simpa using integrable_smul_of_locallyIntegrableOn hu (divergenceCLM φ))
      (by simpa using integrable_smul_of_locallyIntegrableOn hv (divergenceCLM φ))
  rw [hsplit]
  exact (ENNReal.ofReal_add_le).trans (add_le_add (ofReal_integral_le_totalVariationOn φ hφ)
    (ofReal_integral_le_totalVariationOn φ hφ))

section Haar

variable [BorelSpace E] [μ.IsAddHaarMeasure]

/-- Against an additive Haar measure, adding a constant does not change the total variation.
No integrability of `u` is needed. -/
@[simp]
theorem totalVariationOn_add_const (c : ℝ) :
    totalVariationOn μ Ω (fun x => u x + c) = totalVariationOn μ Ω u := by
  simp_rw [totalVariationOn_def]
  refine iSup_congr fun φ => iSup_congr fun _ => congrArg ENNReal.ofReal ?_
  have hc : Integrable (fun x => divergenceCLM φ x * c) μ :=
    ((divergenceCLM φ).integrable ((locallyIntegrable_const 1).locallyIntegrableOn _)).mul_const c
  have hc0 : ∫ x, divergenceCLM φ x * c ∂μ = 0 := by
    rw [integral_mul_const, integral_divergenceCLM_eq_zero, zero_mul]
  simp_rw [mul_add]
  by_cases hu : Integrable (fun x => divergenceCLM φ x * u x) μ
  · rw [integral_add hu hc, hc0, add_zero]
  · rw [integral_undef hu, integral_undef fun h => hu <| by
      simpa only [Pi.sub_def, add_sub_cancel_right] using h.sub hc]

/-- Against an additive Haar measure, a constant function has total variation zero. -/
@[simp]
theorem totalVariationOn_const (c : ℝ) : totalVariationOn μ Ω (fun _ => c) = 0 := by
  simpa using totalVariationOn_add_const (μ := μ) (Ω := Ω) (u := 0) c

end Haar

/-! ### Lower semicontinuity -/

/-- **Lower semicontinuity under distributional convergence.** If `u i → u₀` as distributions
on `Ω`, that is `∫ ψ * u i → ∫ ψ * u₀` for every scalar test function `ψ` on `Ω`, then
`|Du₀|(Ω) ≤ liminf |Du i|(Ω)`. -/
theorem totalVariationOn_le_liminf_of_tendsto_integral {ι : Type*} {l : Filter ι} [l.NeBot]
    {u : ι → E → ℝ} {u₀ : E → ℝ}
    (h : ∀ ψ : 𝓓(Ω, ℝ), Tendsto (fun i => ∫ x, ψ x * u i x ∂μ) l (𝓝 (∫ x, ψ x * u₀ x ∂μ))) :
    totalVariationOn μ Ω u₀ ≤ liminf (fun i => totalVariationOn μ Ω (u i)) l := by
  refine totalVariationOn_le_iff.mpr fun φ hφ => ?_
  rw [← ((ENNReal.continuous_ofReal.tendsto _).comp (h (divergenceCLM φ))).liminf_eq]
  exact liminf_le_liminf (.of_forall fun i => ofReal_integral_le_totalVariationOn φ hφ)

/-- **Lower semicontinuity under `L¹_loc` convergence.** If `u i → u₀` in `L¹_loc(Ω)`, that is
`∫_K |u i - u₀| → 0` for every compact `K ⊆ Ω`, then `|Du₀|(Ω) ≤ liminf |Du i|(Ω)`. -/
theorem totalVariationOn_le_liminf [OpensMeasurableSpace E] {ι : Type*} {l : Filter ι}
    [l.NeBot] {u : ι → E → ℝ} {u₀ : E → ℝ} (hu : ∀ᶠ i in l, LocallyIntegrableOn (u i) Ω μ)
    (hu₀ : LocallyIntegrableOn u₀ Ω μ)
    (h : ∀ K, IsCompact K → K ⊆ Ω → Tendsto (fun i => ∫⁻ x in K, ‖u i x - u₀ x‖ₑ ∂μ) l (𝓝 0)) :
    totalVariationOn μ Ω u₀ ≤ liminf (fun i => totalVariationOn μ Ω (u i)) l := by
  refine totalVariationOn_le_liminf_of_tendsto_integral fun ψ => ?_
  -- The pairing with `ψ` is bounded by `‖ψ‖_∞ ∫_K |w|`, where `K = tsupport ψ`.
  have hbound (w : E → ℝ) : ‖∫ x, ψ x * w x ∂μ‖ₑ ≤
      ‖(ψ : BoundedContinuousFunction E ℝ)‖ₑ * ∫⁻ x in tsupport ψ, ‖w x‖ₑ ∂μ := by
    rw [← lintegral_const_mul' _ _ enorm_ne_top,
      ← lintegral_indicator (isClosed_tsupport _).measurableSet]
    refine (enorm_integral_le_lintegral_enorm _).trans (lintegral_mono fun x => ?_)
    by_cases hx : x ∈ tsupport ψ
    · rw [Set.indicator_of_mem hx, enorm_mul]
      gcongr
      exact enorm_le_iff_norm_le.mpr <| by
        simpa using (ψ : BoundedContinuousFunction E ℝ).norm_coe_le_norm x
    · simp [image_eq_zero_of_notMem_tsupport hx]
  rw [tendsto_iff_edist_tendsto_0]
  have hlim := ENNReal.Tendsto.const_mul (a := ‖(ψ : BoundedContinuousFunction E ℝ)‖ₑ)
    (h _ ψ.hasCompactSupport.isCompact ψ.tsupport_subset) (Or.inr enorm_ne_top)
  rw [mul_zero] at hlim
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim
    (.of_forall fun _ => zero_le) (hu.mono fun i hi => ?_)
  rw [edist_eq_enorm_sub,
    ← integral_sub (by simpa using integrable_smul_of_locallyIntegrableOn hi ψ)
      (by simpa using integrable_smul_of_locallyIntegrableOn hu₀ ψ)]
  simpa only [mul_sub] using hbound fun x => u i x - u₀ x

/-! ### Weakly differentiable functions -/

/-- **A weakly differentiable function has variation at most `∫_Ω ‖Du‖`.** If `u` has weak
derivative `U` on `Ω`, then `|Du|(Ω) ≤ ∫_Ω ‖U‖`. In particular a function in `W^{1,1}(Ω)` has
bounded variation on `Ω`. -/
theorem HasWeakFDerivOn.totalVariationOn_le_setLIntegral_enorm [OpensMeasurableSpace E]
    {U : E → E →L[ℝ] ℝ} (h : HasWeakFDerivOn μ Ω u U) :
    totalVariationOn μ Ω u ≤ ∫⁻ x in Ω, ‖U x‖ₑ ∂μ := by
  refine totalVariationOn_le_iff.mpr fun φ hφ => ?_
  rw [h.integral_divergenceCLM_mul_eq_neg_integral φ]
  refine (ENNReal.ofReal_le_ofReal (neg_le_abs _)).trans ?_
  rw [← Real.enorm_eq_ofReal_abs]
  exact φ.enorm_integral_apply_le_setLIntegral_enorm hφ U

section Haar

variable [BorelSpace E] [μ.IsAddHaarMeasure]

/-- **The total variation of a weakly differentiable function.** If `u` has weak derivative `U`
on `Ω`, then against an additive Haar measure `|Du|(Ω) = ∫_Ω ‖U‖`. In particular a function in
`W^{1,1}(Ω)` has bounded variation on `Ω`, and its variation is the `L¹(Ω)` norm of its weak
derivative. -/
theorem HasWeakFDerivOn.totalVariationOn_eq_setLIntegral_enorm {U : E → E →L[ℝ] ℝ}
    (h : HasWeakFDerivOn μ Ω u U) :
    totalVariationOn μ Ω u = ∫⁻ x in Ω, ‖U x‖ₑ ∂μ := by
  rw [← h.locallyIntegrableOn_deriv.iSup_ofReal_integral_apply_eq_setLIntegral_enorm,
    totalVariationOn_def]
  -- Integration by parts turns `∫ div φ * u` into `∫ U (-φ)`, and `φ ↦ -φ` permutes the
  -- admissible test vector fields.
  have key (φ : 𝓓(Ω, E)) :
      ∫ x, divergenceCLM φ x * u x ∂μ = ∫ x, U x ((-φ : 𝓓(Ω, E)) x) ∂μ := by
    rw [h.integral_divergenceCLM_mul_eq_neg_integral φ, ← integral_neg]
    simp
  simp_rw [key]
  refine le_antisymm (iSup₂_le fun φ hφ => ?_) (iSup₂_le fun φ hφ => ?_)
  · exact le_iSup₂_of_le (f := fun (φ : 𝓓(Ω, E)) (_ : ∀ x, ‖φ x‖ ≤ 1) =>
      ENNReal.ofReal (∫ x, U x (φ x) ∂μ)) (-φ) (fun x => by simpa using hφ x) le_rfl
  · exact le_iSup₂_of_le (f := fun (φ : 𝓓(Ω, E)) (_ : ∀ x, ‖φ x‖ ≤ 1) =>
      ENNReal.ofReal (∫ x, U x ((-φ : 𝓓(Ω, E)) x) ∂μ)) (-φ) (fun x => by simpa using hφ x)
      (by simp)

/-- A weakly differentiable function has finite total variation on `Ω`, against an additive Haar
measure, exactly when its weak derivative is integrable on `Ω`. -/
theorem HasWeakFDerivOn.totalVariationOn_lt_top_iff_integrableOn {U : E → E →L[ℝ] ℝ}
    (h : HasWeakFDerivOn μ Ω u U) : totalVariationOn μ Ω u < ∞ ↔ IntegrableOn U Ω μ := by
  rw [h.totalVariationOn_eq_setLIntegral_enorm, ← hasFiniteIntegral_iff_enorm]
  exact ⟨fun hfi => ⟨h.locallyIntegrableOn_deriv.aestronglyMeasurable, hfi⟩,
    Integrable.hasFiniteIntegral⟩

/-- **The total variation of a locally Lipschitz function**, in particular of a `C¹` function,
is the integral of the norm of its classical derivative: `|Du|(Ω) = ∫_Ω ‖Du‖`, against an
additive Haar measure. -/
theorem _root_.LocallyLipschitzOn.totalVariationOn_eq_setLIntegral_enorm_fderiv
    (hu : LocallyLipschitzOn Ω u) :
    totalVariationOn μ Ω u = ∫⁻ x in Ω, ‖fderiv ℝ u x‖ₑ ∂μ :=
  hu.hasWeakFDerivOn_fderiv.totalVariationOn_eq_setLIntegral_enorm

end Haar

end TauCeti
