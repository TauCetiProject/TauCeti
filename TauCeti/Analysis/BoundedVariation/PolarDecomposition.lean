/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.BoundedVariation.VariationMeasure
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.MeasureTheory.Integral.CompactlySupported
import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
import TauCeti.Analysis.BoundedVariation.DerivativeMeasure
import TauCeti.Analysis.Distribution.AELeOfIntegral
import TauCeti.Analysis.Distribution.TestFunction.Integral
import TauCeti.Analysis.Sobolev.WeakDeriv.Divergence

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
* `TauCeti.polarDensity_congr_ae` and `TauCeti.polarDensity_const_sub`: `σ_u` only depends on `u`
  almost everywhere on `Ω`, and `σ_{c - u} = -σ_u` against an additive Haar measure.

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
  -- Integrals against `ν₁ i` and `ν₂ i` as integrals against `ρ`.
  have hrn {i} {ν : Measure Ω} (hν : ν = ν₁ i ∨ ν = ν₂ i) (ψ : 𝓓(Ω, ℝ)) :
      Integrable (fun x => (ν.rnDeriv ρ x).toReal * ψ x) ρ ∧
        ∫ x, ψ x ∂ν = ∫ x, (ν.rnDeriv ρ x).toReal * ψ x ∂ρ := by
    have : ν.Regular := by rcases hν with rfl | rfl; exacts [h₁ i, h₂ i]
    have hψ : Integrable (fun x : Ω => ψ x) ν := by
      have h := ψ.toCompactlySupportedContinuousMap.integrable (μ := ν)
      exact h.congr (ae_of_all _ (toCompactlySupportedContinuousMap_apply ψ))
    exact ⟨(integrable_toReal_rnDeriv_mul_iff (hac hν)).2 hψ,
      (integral_toReal_rnDeriv_mul (hac hν)).symm⟩
  -- The vector field `g` of densities of the directional derivatives.
  set f : _ → Ω → ℝ := fun i x => ((ν₁ i).rnDeriv ρ x).toReal - ((ν₂ i).rnDeriv ρ x).toReal
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
    have hf (i) : ∫ x, f i x * ψ i x ∂ρ = ∫ x, ψ i x ∂ν₁ i - ∫ x, ψ i x ∂ν₂ i := by
      rw [(hrn (i := i) (Or.inl rfl) (ψ i)).2, (hrn (i := i) (Or.inr rfl) (ψ i)).2,
        ← integral_sub (hrn (i := i) (Or.inl rfl) (ψ i)).1 (hrn (i := i) (Or.inr rfl) (ψ i)).1]
      simp only [f, sub_mul]
    calc ∫ x, divergenceCLM φ x * u x ∂μ
        = Distribution.ofFun Ω u μ ⊤ (divergenceCLM φ) := by
          simp [Distribution.ofFun_apply hu]
      _ = -∑ i, ∂_{b i} (Distribution.ofFun Ω u μ ⊤) (ψ i) := by
          conv_lhs => rw [hφ]
          simp [divergenceCLM_postcompCLM_toSpanSingleton]
      _ = -∑ i, ∫ x, f i x * ψ i x ∂ρ := by simp only [hν, hf]
      _ = -∫ x, ⟪φ x, g x⟫ ∂ρ := by
          rw [← integral_finsetSum _ fun i _ =>
            ((hrn (i := i) (Or.inl rfl) (ψ i)).1.sub (hrn (i := i) (Or.inr rfl) (ψ i)).1).congr
              (ae_of_all _ fun x => by simp [f, sub_mul])]
          congr 2 with x
          simp [hg, ψ, inner_sum, inner_smul_right, real_inner_comm]
  -- `‖g‖` is bounded by the density `k` of `|Du|` with respect to `ρ`.
  set k := lam.rnDeriv ρ
  have hbound : ∀ᵐ x ∂ρ, ‖g x‖ₑ ≤ k x := by
    refine ae_enorm_le_of_forall_enorm_integral_inner_le
      (locallyIntegrable_iff.2 fun K hK => integrable_finsetSum _ fun i _ => ?_)
      (Measure.measurable_rnDeriv _ _)
      (fun K hK => ne_top_of_le_ne_top hK.measure_lt_top.ne (Measure.setLIntegral_rnDeriv_le K))
      fun U hU φ hφU hφ => ?_
    · have hint {ν : Measure Ω} (hν : ν = ν₁ i ∨ ν = ν₂ i) :
          IntegrableOn (fun x => (ν.rnDeriv ρ x).toReal) K ρ := by
        have : ν.Regular := by rcases hν with rfl | rfl; exacts [h₁ i, h₂ i]
        exact integrable_toReal_of_lintegral_ne_top (Measure.measurable_rnDeriv _ _).aemeasurable
          (ne_top_of_le_ne_top hK.measure_lt_top.ne (Measure.setLIntegral_rnDeriv_le K))
      exact ((hint (Or.inl rfl)).sub (hint (Or.inr rfl))).smul_const _
    rw [Measure.setLIntegral_rnDeriv hlam, ← enorm_neg, ← hrep]
    exact enorm_integral_divergenceCLM_mul_le_variationMeasure hu hfin hU φ hφU hφ
  -- Normalize `g` by `k`.
  refine ⟨fun x => (k x).toReal⁻¹ • g x,
    ((Measure.measurable_rnDeriv _ _).ennreal_toReal.inv).smul hgm, hlam.ae_le ?_, fun φ => ?_⟩
  · filter_upwards [hbound, Measure.rnDeriv_lt_top lam ρ] with x hx hk
    have hle : ‖g x‖ ≤ (k x).toReal := by
      rwa [← ofReal_norm, ENNReal.ofReal_le_iff_le_toReal hk.ne] at hx
    rw [norm_smul, norm_inv, Real.norm_of_nonneg ENNReal.toReal_nonneg, inv_mul_eq_div]
    exact div_le_one_of_le₀ hle ENNReal.toReal_nonneg
  · rw [hrep, ← integral_toReal_rnDeriv_mul hlam]
    congr 1
    refine integral_congr_ae ?_
    filter_upwards [hbound, Measure.rnDeriv_lt_top lam ρ] with x hx hk
    rw [inner_smul_right, ← mul_assoc]
    rcases eq_or_ne (k x).toReal 0 with h0 | h0
    · have : g x = 0 := by
        rw [ENNReal.toReal_eq_zero_iff] at h0
        rcases h0 with h0 | h0
        · simpa [h0] using hx
        · exact absurd h0 hk.ne
      simp [this]
    · rw [mul_inv_cancel₀ h0, one_mul]

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
  -- Hence `1 ≤ ‖σ‖` almost everywhere on every open set of finite measure.
  have hloc (V : Set Ω) (hV : IsOpen V) (hVfin : lam V ≠ ∞) :
      ∀ᵐ x ∂lam.restrict V, 1 ≤ ‖σ x‖ₑ := by
    have hle : ∀ᵐ x ∂lam.restrict V, ‖σ x‖ₑ ≤ 1 := ae_restrict_of_ae <| hσ1.mono fun x hx => by
      rwa [← ofReal_norm, ENNReal.ofReal_le_one]
    have hint : ∫⁻ x in V, ‖σ x‖ₑ ∂lam ≠ ∞ :=
      ne_top_of_le_ne_top hVfin ((lintegral_mono_ae hle).trans_eq (by simp))
    filter_upwards [ae_eq_of_ae_le_of_lintegral_le hle hint aemeasurable_const
      (by simpa using hopen V hV)] with x hx
    exact hx.symm.le
  -- Cover `Ω` by countably many open sets of finite measure.
  choose V hKV hVo hVfin using fun n =>
    (isCompact_compactCovering Ω n).exists_open_superset_measure_lt_top lam
  have hVU : ⋃ n, V n = univ :=
    eq_univ_of_univ_subset ((iUnion_compactCovering Ω).symm.subset.trans (iUnion_mono hKV))
  rw [← Measure.restrict_univ (μ := lam), ← hVU, ae_restrict_iUnion_iff]
  intro n
  filter_upwards [hloc (V n) (hVo n) (hVfin n).ne, ae_restrict_of_ae hσ1] with x h1 h2
  rw [← ofReal_norm, ENNReal.one_le_ofReal] at h1
  exact le_antisymm h2 h1

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

omit hu hfin

/-- **Locality of the polar density.** If `u = v` almost everywhere on `Ω`, then `σ_u = σ_v` at
`|Du|`-almost every point. -/
theorem polarDensity_congr_ae (h : u =ᵐ[μ.restrict Ω] v) :
    polarDensity μ Ω u =ᵐ[variationMeasure μ Ω u] polarDensity μ Ω v := by
  by_cases hu : LocallyIntegrableOn u Ω μ ∧
      ∀ K, IsCompact K → K ⊆ Ω → ∃ U : Opens E, K ⊆ (U : Set E) ∧ totalVariationOn μ U u ≠ ∞
  · by_cases hv : LocallyIntegrableOn v Ω μ ∧
        ∀ K, IsCompact K → K ⊆ Ω → ∃ U : Opens E, K ⊆ (U : Set E) ∧ totalVariationOn μ U v ≠ ∞
    · have hσ := locallyIntegrable_polarDensity hv.1 hv.2
      rw [← variationMeasure_congr_ae h] at hσ
      refine (ae_eq_polarDensity hu.1 hu.2 hσ fun φ => ?_).symm
      rw [integral_divergenceCLM_mul_congr_ae h,
        integral_divergenceCLM_mul_eq_neg_integral_inner_polarDensity hv.1 hv.2,
        variationMeasure_congr_ae h]
    · rw [variationMeasure_congr_ae h, variationMeasure_eq_zero_of_not hv]
      simp [EventuallyEq]
  · rw [variationMeasure_eq_zero_of_not hu]
    simp [EventuallyEq]

/-- Against an additive Haar measure, the polar density of `c - u` is `-σ_u` at `|Du|`-almost
every point. In particular the polar densities of the indicators of a set and of its complement
are opposite. -/
theorem polarDensity_const_sub [μ.IsAddHaarMeasure] (c : ℝ) :
    polarDensity μ Ω (fun x => c - u x) =ᵐ[variationMeasure μ Ω u] -polarDensity μ Ω u := by
  by_cases hu : LocallyIntegrableOn u Ω μ ∧
      ∀ K, IsCompact K → K ⊆ Ω → ∃ U : Opens E, K ⊆ (U : Set E) ∧ totalVariationOn μ U u ≠ ∞
  · have hc : LocallyIntegrableOn (fun _ : E => c) Ω μ :=
      (locallyIntegrable_const c).locallyIntegrableOn _
    have hv : LocallyIntegrableOn (fun x => c - u x) Ω μ ∧ ∀ K, IsCompact K → K ⊆ Ω →
        ∃ U : Opens E, K ⊆ (U : Set E) ∧ totalVariationOn μ U (fun x => c - u x) ≠ ∞ :=
      ⟨hc.sub hu.1, fun K hK hKΩ => by simpa only [totalVariationOn_const_sub] using hu.2 K hK hKΩ⟩
    have hσ := (locallyIntegrable_polarDensity hu.1 hu.2).neg
    rw [← variationMeasure_const_sub (u := u) c] at hσ ⊢
    refine (ae_eq_polarDensity hv.1 hv.2 hσ fun φ => ?_).symm
    have hiu : Integrable (fun x => divergenceCLM φ x * u x) μ := by
      simpa using integrable_smul_of_locallyIntegrableOn hu.1 (divergenceCLM φ)
    have hic : Integrable (fun x => divergenceCLM φ x * c) μ :=
      ((divergenceCLM φ).integrable ((locallyIntegrable_const 1).locallyIntegrableOn _)).mul_const c
    simp_rw [mul_sub]
    rw [integral_sub hic hiu, integral_mul_const, integral_divergenceCLM_eq_zero, zero_mul,
      zero_sub, integral_divergenceCLM_mul_eq_neg_integral_inner_polarDensity hu.1 hu.2,
      variationMeasure_const_sub]
    simp [inner_neg_right, integral_neg]
  · rw [variationMeasure_eq_zero_of_not hu]
    simp [EventuallyEq]

end TauCeti
