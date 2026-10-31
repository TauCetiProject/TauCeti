/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.BoundedVariation.VariationMeasure
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.MeasureTheory.Integral.CompactlySupported
import TauCeti.Analysis.BoundedVariation.DerivativeMeasure
import TauCeti.Analysis.Distribution.AELeOfIntegral
import TauCeti.Analysis.Distribution.TestFunction.Integral
import TauCeti.MeasureTheory.Integral.Lebesgue.OpenSet
import TauCeti.MeasureTheory.Measure.Decomposition.RadonNikodym

/-!
# The polar decomposition of the derivative of a function of locally bounded variation

Let `Ω` be an open set of a finite-dimensional real inner product space `E` and let `u : E → ℝ` be
locally integrable on `Ω`, with locally finite variation: every compact `K ⊆ Ω` has an open
neighbourhood `U` with `|Du|(U) < ∞`. The distributional derivative `Du` is then a vector-valued
Radon measure on `Ω`, absolutely continuous with respect to its variation measure `|Du|`
(`TauCeti.variationMeasure`) with a density of norm one:

`Du = σ_u |Du|`, that is, `∫ u div φ dμ = -∫ ⟪φ, σ_u⟫ d|Du|` for every `φ ∈ 𝓓(Ω, E)`,

with `‖σ_u‖ = 1` at `|Du|`-almost every point. This is the structure theorem for functions of
locally bounded variation. The **polar density** `σ_u` is `TauCeti.polarDensity`. It is unique
`|Du|`-almost everywhere (`TauCeti.ae_eq_polarDensity`). For the indicator `χ_E` of a set of
locally finite perimeter, the sign convention `Dχ_E = -ν_E |Dχ_E|` makes `-σ_{χ_E}` the
measure-theoretic outer unit normal `ν_E`.

The proof assembles the directional derivatives `∂_{bᵢ} u` along an orthonormal basis, each a
difference of two regular measures (`TauCeti.exists_regular_lineDeriv_ofFun_apply_eq`). With
respect to a common reference measure `ρ`, which also dominates `|Du|`, their Radon–Nikodym
densities form a vector field `g` with `∫ u div φ dμ = -∫ ⟪φ, g⟫ dρ`. A pairing with a test vector
field of norm at most one supported in `U` is bounded by `|Du|(U)`, so `‖g‖` is at most the density
of `|Du|` with respect to `ρ` (`TauCeti.ae_enorm_le_of_forall_enorm_integral_inner_le`), and
`σ_u = g / (d|Du|/dρ)` has norm at most one. Testing the definition of `|Du|(U)` as a supremum
against this representation gives `|Du|(U) ≤ ∫_U ‖σ_u‖ d|Du|`, hence `‖σ_u‖ = 1`.

## Main declarations

* `TauCeti.polarDensity μ Ω u`: the polar density `σ_u : Ω → E` of `Du` with respect to `|Du|`.
* `TauCeti.integral_divergenceCLM_mul_eq_neg_integral_inner_polarDensity`: the representation
  `∫ u div φ dμ = -∫ ⟪φ, σ_u⟫ d|Du|`.
* `TauCeti.ae_norm_polarDensity_eq_one`: `‖σ_u‖ = 1` at `|Du|`-almost every point.
* `TauCeti.locallyIntegrable_polarDensity`: `σ_u` is locally integrable with respect to `|Du|`.
* `TauCeti.ae_eq_polarDensity`: a locally integrable vector field representing `Du` against `|Du|`
  is `σ_u` almost everywhere.
* `TauCeti.enorm_integral_divergenceCLM_mul_le_lintegral_enorm`: the pairing is bounded by
  `∫ ‖φ‖ d|Du|`.

## References

* L. C. Evans, R. F. Gariepy, *Measure Theory and Fine Properties of Functions*, revised edition,
  §5.1, Theorem 5.1 (the structure theorem for functions of locally bounded variation).
* L. Ambrosio, N. Fusco, D. Pallara, *Functions of Bounded Variation and Free Discontinuity
  Problems*, §1.4 (polar decomposition) and §3.1.
-/

public section

noncomputable section

namespace TauCeti

open MeasureTheory TopologicalSpace TestFunction Set Filter LineDeriv
open scoped ENNReal Distributions RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {μ : Measure E} {Ω : Opens E} {u : E → ℝ}

variable (hu : LocallyIntegrableOn u Ω μ)
  (hfin : ∀ K, IsCompact K → K ⊆ Ω → ∃ U : Opens E, K ⊆ (U : Set E) ∧ totalVariationOn μ U u ≠ ∞)
include hu hfin

/-- Existence of a density of norm at most one representing `Du` against `|Du|`. -/
private theorem exists_le_one :
    ∃ σ : Ω → E, Measurable σ ∧ (∀ᵐ x ∂variationMeasure μ Ω u, ‖σ x‖ ≤ 1) ∧
      ∀ φ : 𝓓(Ω, E), ∫ x, divergenceCLM φ x * u x ∂μ =
        -∫ x, ⟪φ x, σ x⟫ ∂variationMeasure μ Ω u := by
  have := Ω.isOpen.locallyCompactSpace
  set lam := variationMeasure μ Ω u
  let b := stdOrthonormalBasis ℝ E
  choose ν₁ ν₂ h₁ h₂ hν using fun i => exists_regular_lineDeriv_ofFun_apply_eq (μ := μ) hfin (b i)
  -- A reference measure `ρ`, finite on compact sets, dominating `|Du|` and every `νᵢ`.
  set ρ : Measure Ω := lam + ∑ i, (ν₁ i + ν₂ i) with hρ
  have : IsFiniteMeasureOnCompacts ρ := ⟨fun K hK => by
    simp only [hρ, Measure.coe_add, Measure.coe_finsetSum, Pi.add_apply, Finset.sum_apply]
    exact ENNReal.add_lt_top.2 ⟨hK.measure_lt_top, ENNReal.sum_lt_top.2 fun i _ =>
      ENNReal.add_lt_top.2 ⟨(h₁ i).lt_top_of_isCompact hK, (h₂ i).lt_top_of_isCompact hK⟩⟩⟩
  have hlam : lam ≪ ρ := Measure.AbsolutelyContinuous.rfl.add_right _
  have hac {i} {ν : Measure Ω} (hν : ν = ν₁ i ∨ ν = ν₂ i) : ν ≪ ρ := fun s hs => by
    simp only [hρ, Measure.coe_add, Measure.coe_finsetSum, Pi.add_apply, Finset.sum_apply,
      add_eq_zero, Finset.sum_eq_zero_iff, Finset.mem_univ, true_implies] at hs
    rcases hν with rfl | rfl
    exacts [(hs.2 i).1, (hs.2 i).2]
  -- The vector field `g` of densities of the directional derivatives.
  set f : _ → Ω → ℝ := fun i x => ((ν₁ i).rnDeriv ρ x).toReal - ((ν₂ i).rnDeriv ρ x).toReal
  have hloc (i) : LocallyIntegrable (f i) ρ :=
    Measure.locallyIntegrable_toReal_rnDeriv.sub Measure.locallyIntegrable_toReal_rnDeriv
  set g : Ω → E := fun x => ∑ i, f i x • b i with hg
  have hgm : Measurable g := Finset.measurable_sum _ fun i _ =>
    ((Measure.measurable_rnDeriv _ _).ennreal_toReal.sub
      (Measure.measurable_rnDeriv _ _).ennreal_toReal).smul_const _
  have hrep (φ : 𝓓(Ω, E)) : ∫ x, divergenceCLM φ x * u x ∂μ = -∫ x, ⟪φ x, g x⟫ ∂ρ := by
    -- The components of `φ` in the basis `b`.
    set ψ : _ → 𝓓(Ω, ℝ) := fun i => postcompCLM (innerSL ℝ (b i)) φ
    have hφ : φ = ∑ i, postcompCLM (ContinuousLinearMap.toSpanSingleton ℝ (b i)) (ψ i) := by
      ext x
      simp [ψ, b.sum_repr']
    calc ∫ x, divergenceCLM φ x * u x ∂μ
        = Distribution.ofFun Ω u μ ⊤ (divergenceCLM φ) := by
          simp [Distribution.ofFun_apply hu]
      _ = -∑ i, ∂_{b i} (Distribution.ofFun Ω u μ ⊤) (ψ i) := by
          conv_lhs => rw [hφ]
          simp [divergenceCLM_postcompCLM_toSpanSingleton]
      _ = -∑ i, ∫ x, ψ i x * f i x ∂ρ := by
          simp only [hν, (ψ _).integral_sub_integral_eq_integral_mul_sub_rnDeriv
            (hac (Or.inl rfl)) (hac (Or.inr rfl)), f]
      _ = -∫ x, ⟪φ x, g x⟫ ∂ρ := by
          rw [← integral_finsetSum _ fun i _ => (show Integrable (fun x : Ω => ψ i x * f i x) ρ from
            (ψ i).integrable_bilin_subtype (ContinuousLinearMap.mul ℝ ℝ) (hloc i))]
          congr 2 with x
          simp [hg, ψ, inner_sum, inner_smul_right, real_inner_comm, mul_comm]
  -- `‖g‖` is bounded by the density `k` of `|Du|` with respect to `ρ`.
  have hbound : ∀ᵐ x ∂ρ, ‖g x‖ₑ ≤ 1 * lam.rnDeriv ρ x := by
    simp_rw [one_mul]
    refine ae_enorm_le_of_forall_enorm_integral_inner_le
      (locallyIntegrable_iff.2 fun K hK => integrable_finsetSum _ fun i _ =>
        ((hloc i).integrableOn_isCompact hK).smul_const _)
      (Measure.measurable_rnDeriv _ _)
      (fun K hK => ne_top_of_le_ne_top hK.measure_lt_top.ne (Measure.setLIntegral_rnDeriv_le K))
      fun U hU φ hφU hφ => ?_
    rw [Measure.setLIntegral_rnDeriv hlam, ← enorm_neg, ← hrep]
    exact enorm_integral_divergenceCLM_mul_le_variationMeasure hu hfin hU φ hφU hφ
  -- Normalize `g` by the density of `|Du|`.
  refine ⟨fun x => (lam.rnDeriv ρ x).toReal⁻¹ • g x,
    ((Measure.measurable_rnDeriv _ _).ennreal_toReal.inv).smul hgm,
    (Measure.ae_enorm_inv_toReal_rnDeriv_smul_le hlam hbound).mono fun x hx => ?_, fun φ => ?_⟩
  · rwa [← ofReal_norm, ENNReal.ofReal_le_one] at hx
  · rw [hrep, ← integral_toReal_rnDeriv_mul hlam]
    congr 1
    refine integral_congr_ae ?_
    filter_upwards [Measure.toReal_rnDeriv_smul_inv_smul_ae_eq hbound] with x hx
    conv_lhs => rw [← hx]
    rw [inner_smul_right]

/-- A density of norm at most one representing `Du` against `|Du|` has norm one almost
everywhere. -/
private theorem ae_norm_eq_one_of_le_one {σ : Ω → E}
    (hσ1 : ∀ᵐ x ∂variationMeasure μ Ω u, ‖σ x‖ ≤ 1)
    (hσ : ∀ φ : 𝓓(Ω, E), ∫ x, divergenceCLM φ x * u x ∂μ =
      -∫ x, ⟪φ x, σ x⟫ ∂variationMeasure μ Ω u) :
    ∀ᵐ x ∂variationMeasure μ Ω u, ‖σ x‖ = 1 := by
  have := Ω.isOpen.locallyCompactSpace
  set lam := variationMeasure μ Ω u
  -- Testing the supremum defining `|Du|(V)` gives `|Du|(V) ≤ ∫_V ‖σ‖ d|Du|` on open sets.
  have hopen (V : Set Ω) (hV : IsOpen V) : lam V ≤ ∫⁻ x in V, ‖σ x‖ₑ ∂lam := by
    set U : Opens E := ⟨(↑) '' V, Ω.isOpen.isOpenMap_subtype_val V hV⟩
    have hU : U ≤ Ω := Subtype.coe_image_subset _ _
    have hUV : ((↑) : Ω → E) ⁻¹' (U : Set E) = V := preimage_image_eq V Subtype.val_injective
    rw [← hUV, variationMeasure_preimage_coe hu hfin hU, totalVariationOn_le_iff]
    intro φ hφ
    let φΩ : 𝓓(Ω, E) := ⟨φ, φ.contDiff, φ.hasCompactSupport, φ.tsupport_subset.trans hU⟩
    have hdiv (x : E) : divergenceCLM φ x = divergenceCLM φΩ x := by simp [φΩ]
    simp_rw [hdiv, hσ φΩ]
    refine (ENNReal.ofReal_le_ofReal (neg_le_abs _)).trans ?_
    rw [← Real.enorm_eq_ofReal_abs, ← lintegral_indicator (hUV ▸ hV.measurableSet)]
    refine (enorm_integral_le_lintegral_enorm _).trans (lintegral_mono fun x => ?_)
    by_cases hx : x ∈ ((↑) : Ω → E) ⁻¹' (U : Set E)
    · rw [indicator_of_mem hx, ← ofReal_norm, ← ofReal_norm]
      exact ENNReal.ofReal_le_ofReal ((norm_inner_le_norm _ _).trans
        (mul_le_of_le_one_left (norm_nonneg _) (hφ x)))
    · have : φΩ x = 0 := image_eq_zero_of_notMem_tsupport fun h => hx (φ.tsupport_subset h)
      simp [this]
  filter_upwards [ae_eq_one_of_forall_isOpen_le_setLIntegral
    (hσ1.mono fun x hx => by rwa [← ofReal_norm, ENNReal.ofReal_le_one]) hopen] with x hx
  rwa [← ofReal_norm, ENNReal.ofReal_eq_one] at hx

private theorem exists_polarDensity :
    ∃ σ : Ω → E, Measurable σ ∧ (∀ᵐ x ∂variationMeasure μ Ω u, ‖σ x‖ = 1) ∧
      ∀ φ : 𝓓(Ω, E), ∫ x, divergenceCLM φ x * u x ∂μ =
        -∫ x, ⟪φ x, σ x⟫ ∂variationMeasure μ Ω u :=
  let ⟨σ, hσm, hσ1, hσ⟩ := exists_le_one hu hfin
  ⟨σ, hσm, ae_norm_eq_one_of_le_one hu hfin hσ1 hσ, hσ⟩

omit hu hfin

open scoped Classical in
/-- The **polar density** `σ_u` of the derivative of `u` on `Ω` with respect to its variation
measure `|Du|`: if `u` is locally integrable on `Ω` with locally finite variation there, it is a
measurable vector field `σ_u : Ω → E` with `‖σ_u‖ = 1` at `|Du|`-almost every point
(`TauCeti.ae_norm_polarDensity_eq_one`) such that `Du = σ_u |Du|`, that is,
`∫ u div φ dμ = -∫ ⟪φ, σ_u⟫ d|Du|` for every test vector field `φ` on `Ω`
(`TauCeti.integral_divergenceCLM_mul_eq_neg_integral_inner_polarDensity`). It is determined
`|Du|`-almost everywhere (`TauCeti.ae_eq_polarDensity`). If no such field exists it is `0` by
convention. -/
def polarDensity (μ : Measure E) (Ω : Opens E) (u : E → ℝ) : Ω → E :=
  if h : ∃ σ : Ω → E, Measurable σ ∧ (∀ᵐ x ∂variationMeasure μ Ω u, ‖σ x‖ = 1) ∧
      ∀ φ : 𝓓(Ω, E), ∫ x, divergenceCLM φ x * u x ∂μ =
        -∫ x, ⟪φ x, σ x⟫ ∂variationMeasure μ Ω u then h.choose
  else 0

/-- The polar density is measurable. -/
@[fun_prop]
theorem measurable_polarDensity : Measurable (polarDensity μ Ω u) := by
  unfold polarDensity
  split_ifs with h
  exacts [h.choose_spec.1, measurable_const]

include hu hfin

private theorem polarDensity_spec :
    (∀ᵐ x ∂variationMeasure μ Ω u, ‖polarDensity μ Ω u x‖ = 1) ∧
      ∀ φ : 𝓓(Ω, E), ∫ x, divergenceCLM φ x * u x ∂μ =
        -∫ x, ⟪φ x, polarDensity μ Ω u x⟫ ∂variationMeasure μ Ω u := by
  rw [polarDensity, dite_eq_left (exists_polarDensity hu hfin)]
  exact (exists_polarDensity hu hfin).choose_spec.2

/-- **The polar decomposition `Du = σ_u |Du|`.** For `u` locally integrable on `Ω` with locally
finite variation, `∫ u div φ dμ = -∫ ⟪φ, σ_u⟫ d|Du|` for every test vector field `φ` on `Ω`. -/
theorem integral_divergenceCLM_mul_eq_neg_integral_inner_polarDensity (φ : 𝓓(Ω, E)) :
    ∫ x, divergenceCLM φ x * u x ∂μ =
      -∫ x, ⟪φ x, polarDensity μ Ω u x⟫ ∂variationMeasure μ Ω u :=
  (polarDensity_spec hu hfin).2 φ

/-- The polar density of a function of locally finite variation has norm one at `|Du|`-almost
every point. -/
theorem ae_norm_polarDensity_eq_one :
    ∀ᵐ x ∂variationMeasure μ Ω u, ‖polarDensity μ Ω u x‖ = 1 :=
  (polarDensity_spec hu hfin).1

/-- The polar density of a function of locally finite variation is locally integrable with
respect to `|Du|`. -/
theorem locallyIntegrable_polarDensity :
    LocallyIntegrable (polarDensity μ Ω u) (variationMeasure μ Ω u) := by
  have := Ω.isOpen.locallyCompactSpace
  exact locallyIntegrable_iff.2 fun K hK => Measure.integrableOn_of_bounded hK.measure_lt_top.ne
    measurable_polarDensity.aestronglyMeasurable (M := 1)
    (ae_restrict_of_ae ((ae_norm_polarDensity_eq_one hu hfin).mono fun x hx => hx.le))

/-- **Uniqueness of the polar density.** A locally integrable vector field `σ` on `Ω` with
`∫ u div φ dμ = -∫ ⟪φ, σ⟫ d|Du|` for every test vector field `φ` agrees with `σ_u` at
`|Du|`-almost every point. -/
theorem ae_eq_polarDensity {σ : Ω → E} (hσ : LocallyIntegrable σ (variationMeasure μ Ω u))
    (h : ∀ φ : 𝓓(Ω, E), ∫ x, divergenceCLM φ x * u x ∂μ =
      -∫ x, ⟪φ x, σ x⟫ ∂variationMeasure μ Ω u) :
    σ =ᵐ[variationMeasure μ Ω u] polarDensity μ Ω u := by
  have := Ω.isOpen.locallyCompactSpace
  have hσ' := locallyIntegrable_polarDensity hu hfin
  have hint {τ : Ω → E} (hτ : LocallyIntegrable τ (variationMeasure μ Ω u)) (φ : 𝓓(Ω, E)) :
      Integrable (fun x : Ω => ⟪φ x, τ x⟫) (variationMeasure μ Ω u) := by
    exact (φ.integrable_bilin_subtype (innerSL ℝ) hτ).congr
      (ae_of_all _ fun x => innerSL_apply_apply ℝ _ _)
  have h0 := ae_enorm_le_of_forall_enorm_integral_inner_le (k := 0) (hσ.sub hσ') measurable_const
    (by simp) fun U _ φ _ _ => by
      simp only [Pi.sub_apply, inner_sub_right]
      rw [integral_sub (hint hσ φ) (hint hσ' φ),
        ← neg_inj.1 ((h φ).symm.trans
          (integral_divergenceCLM_mul_eq_neg_integral_inner_polarDensity hu hfin φ))]
      simp
  filter_upwards [h0] with x hx
  simpa [sub_eq_zero] using hx

/-- The pairing of `u` with a test vector field `φ` on `Ω` is bounded by `∫ ‖φ‖ d|Du|`. -/
theorem enorm_integral_divergenceCLM_mul_le_lintegral_enorm (φ : 𝓓(Ω, E)) :
    ‖∫ x, divergenceCLM φ x * u x ∂μ‖ₑ ≤ ∫⁻ x, ‖φ x‖ₑ ∂variationMeasure μ Ω u := by
  rw [integral_divergenceCLM_mul_eq_neg_integral_inner_polarDensity hu hfin, enorm_neg]
  refine (enorm_integral_le_lintegral_enorm _).trans (lintegral_mono_ae ?_)
  filter_upwards [ae_norm_polarDensity_eq_one hu hfin] with x hx
  rw [← ofReal_norm, ← ofReal_norm]
  exact ENNReal.ofReal_le_ofReal ((norm_inner_le_norm _ _).trans_eq (by rw [hx, mul_one]))

end TauCeti
