/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Wirtinger.Mollification
public import TauCeti.Analysis.Complex.Wirtinger.InteriorEstimate
public import TauCeti.Analysis.Sobolev.TestFunctionLp.Basic
import TauCeti.MeasureTheory.Function.Lp.ApproximateIdentity
import TauCeti.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.Topology.MetricSpace.Thickening

/-!
# Interior test bounds for a distributional Cauchy–Riemann equation

For `1 < p < ∞`, an `Lᵖ` solution of the normalized distributional equation
`barpartial u = f`, with `f ∈ Lᵖ`, has directional distributional derivatives bounded on
smaller domains by the conjugate `Lᵠ` test norm. The equation is imposed as an integral
identity, and no weak derivative of the solution is assumed. Coefficients may lie in any
complex Hilbert space. On a finite-measure outer domain the solution remainder may instead
be measured in any larger exponent, including infinity.

The proof mollifies zero extensions inside the original domain, uses the classical interior
Cauchy–Riemann estimate and the normalized-bump contraction, and passes to the limit in the
test pairings. The resulting test bound is the input to `Lᵖ` weak-derivative representation.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  Appendix B.
-/

public section

namespace TauCeti

open MeasureTheory TopologicalSpace ContinuousLinearMap Complex Set Metric Filter
open scoped ContDiff Convolution Distributions ENNReal NNReal Topology

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
  {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)] [p.HolderConjugate q]

private theorem eLpNorm_fderiv_indicator_convolution_le
    (hp_top : p ≠ (∞ : ℝ≥0∞)) {U : Opens ℂ} {W K : Set ℂ} {C : ℝ≥0}
    (hC : ∀ v : ℂ → F, ContDiffOn ℝ ∞ v W →
      eLpNorm (fderiv ℝ v) p (volume.restrict K) ≤
        C * (eLpNorm (fun z => conjWirtingerDeriv v z 1) p (volume.restrict W) +
          eLpNorm v p (volume.restrict W)))
    {u f : ℂ → F} (hu : MemLp u p (volume.restrict U))
    (hf : MemLp f p (volume.restrict U))
    (h : ∀ φ : 𝓓(U, ℝ),
      (∫ z, lineDeriv ℝ (φ : ℂ → ℝ) z 1 • u z) +
        I • (∫ z, lineDeriv ℝ (φ : ℂ → ℝ) z I • u z) =
          -(2 : ℝ) • (∫ z, (φ : ℂ → ℝ) z • f z))
    (ρ : ContDiffBump (0 : ℂ)) (hW : MeasurableSet W)
    (hshift : ∀ x ∈ W, ∀ y ∈ tsupport (ρ.normed volume), x - y ∈ U) :
    eLpNorm (fderiv ℝ (ρ.normed volume ⋆[lsmul ℝ ℝ] ((U : Set ℂ).indicator u))) p
      (volume.restrict K) ≤
        C * (eLpNorm f p (volume.restrict U) + eLpNorm u p (volume.restrict U)) := by
  let u₀ := (U : Set ℂ).indicator u
  let f₀ := (U : Set ℂ).indicator f
  have hu₀ : MemLp u₀ p volume :=
    (memLp_indicator_iff_restrict U.isOpen.measurableSet.nullMeasurableSet).2 hu
  have hf₀ : MemLp f₀ p volume :=
    (memLp_indicator_iff_restrict U.isOpen.measurableSet.nullMeasurableSet).2 hf
  have hzero : ∀ φ : 𝓓(U, ℝ),
      (∫ z, lineDeriv ℝ (φ : ℂ → ℝ) z 1 • u₀ z) +
        I • (∫ z, lineDeriv ℝ (φ : ℂ → ℝ) z I • u₀ z) =
          -(2 : ℝ) • (∫ z, (φ : ℂ → ℝ) z • f₀ z) := by
    intro φ
    have hder (v : ℂ) : ∫ z, lineDeriv ℝ (φ : ℂ → ℝ) z v • u₀ z =
        ∫ z, lineDeriv ℝ (φ : ℂ → ℝ) z v • u z := by
      simp only [u₀, ← indicator_smul_apply (U : Set ℂ)
        (fun z => lineDeriv ℝ (φ : ℂ → ℝ) z v) u]
      rw [integral_indicator U.isOpen.measurableSet,
        setIntegral_lineDeriv_smul_eq_integral_lineDeriv_smul φ v]
    have hfun : ∫ z, (φ : ℂ → ℝ) z • f₀ z = ∫ z, (φ : ℂ → ℝ) z • f z := by
      simp only [f₀, ← indicator_smul_apply]
      rw [integral_indicator U.isOpen.measurableSet, setIntegral_smul_eq_integral_smul φ]
    rw [hder, hder, hfun]
    exact h φ
  have heq (x : ℂ) (hx : x ∈ W) :
      conjWirtingerDeriv (ρ.normed volume ⋆[lsmul ℝ ℝ] u₀) x 1 =
        (ρ.normed volume ⋆[lsmul ℝ ℝ] f₀) x := by
    simpa only [convolution_flip (lsmul ℝ ℝ)] using
      conjWirtingerDeriv_convolution_right_of_integral_eq
        (hu₀.locallyIntegrable Fact.out) hzero (ρ.normed volume) ρ.contDiff_normed
        ρ.hasCompactSupport_normed x (hshift x hx)
  have hsmooth : ContDiff ℝ ∞ (ρ.normed volume ⋆[lsmul ℝ ℝ] u₀) :=
    ρ.hasCompactSupport_normed.contDiff_convolution_left (lsmul ℝ ℝ)
      ρ.contDiff_normed (hu₀.locallyIntegrable Fact.out)
  calc eLpNorm (fderiv ℝ (ρ.normed volume ⋆[lsmul ℝ ℝ] u₀)) p (volume.restrict K) ≤
      C * (eLpNorm (fun z => conjWirtingerDeriv
        (ρ.normed volume ⋆[lsmul ℝ ℝ] u₀) z 1) p (volume.restrict W) +
          eLpNorm (ρ.normed volume ⋆[lsmul ℝ ℝ] u₀) p (volume.restrict W)) :=
            hC _ hsmooth.contDiffOn
    _ = C * (eLpNorm (ρ.normed volume ⋆[lsmul ℝ ℝ] f₀) p (volume.restrict W) +
        eLpNorm (ρ.normed volume ⋆[lsmul ℝ ℝ] u₀) p (volume.restrict W)) := by
          congr 2
          exact eLpNorm_congr_ae (ae_restrict_of_forall_mem hW heq)
    _ ≤ C * (eLpNorm f₀ p volume + eLpNorm u₀ p volume) := by
      gcongr
      · exact (eLpNorm_mono_measure _ Measure.restrict_le_self).trans
          (eLpNorm_normed_convolution_le hp_top ρ hf₀)
      · exact (eLpNorm_mono_measure _ Measure.restrict_le_self).trans
          (eLpNorm_normed_convolution_le hp_top ρ hu₀)
    _ = _ := by
      rw [eLpNorm_indicator_eq_eLpNorm_restrict U.isOpen.measurableSet.nullMeasurableSet,
        eLpNorm_indicator_eq_eLpNorm_restrict U.isOpen.measurableSet.nullMeasurableSet]

/-- An `Lᵖ` distributional Cauchy–Riemann solution with nonzero `Lᵖ` source has directional
weak-derivative test bounds on a smaller neighborhood of every compact subset. The bound uses
the conjugate test exponent and assumes no classical or weak differentiability of the solution. -/
theorem exists_enorm_integral_lineDeriv_smul_le_of_integral_conjWirtingerDeriv_eq
    (hp : 1 < p) (hp_top : p ≠ (∞ : ℝ≥0∞)) {U : Opens ℂ} {K : Set ℂ}
    (hK : IsCompact K) (hKU : K ⊆ U) :
    ∃ V : Opens ℂ, K ⊆ V ∧ IsCompact (closure (V : Set ℂ)) ∧
      closure (V : Set ℂ) ⊆ U ∧ ∃ C : ℝ≥0,
      ∀ (u f : ℂ → F), MemLp u p (volume.restrict U) → MemLp f p (volume.restrict U) →
      (∀ φ : 𝓓(U, ℝ),
        (∫ z, lineDeriv ℝ (φ : ℂ → ℝ) z 1 • u z) +
          I • (∫ z, lineDeriv ℝ (φ : ℂ → ℝ) z I • u z) =
            -(2 : ℝ) • (∫ z, (φ : ℂ → ℝ) z • f z)) →
      ∀ (φ : 𝓓(V, ℝ)) (v : ℂ),
        ‖∫ z, lineDeriv ℝ (φ : ℂ → ℝ) z v • u z‖ₑ ≤
          C * ‖v‖ₑ * (eLpNorm f p (volume.restrict U) + eLpNorm u p (volume.restrict U)) *
            eLpNorm (φ : ℂ → ℝ) q volume := by
  obtain ⟨R, hR, hRU⟩ := hK.exists_cthickening_subset_open U.isOpen hKU
  let δ := R / 4
  have hδ : 0 < δ := by positivity
  let V : Opens ℂ := ⟨thickening δ K, isOpen_thickening⟩
  let Q := cthickening δ K
  let W := thickening (2 * δ) K
  have hVQ : (V : Set ℂ) ⊆ Q := thickening_subset_cthickening δ K
  have hQU : Q ⊆ U := (cthickening_mono (by dsimp [δ]; linarith) K).trans hRU
  have hQW : Q ⊆ W := cthickening_subset_thickening' (by positivity) (by linarith) K
  obtain ⟨C, hC⟩ :=
    exists_eLpNorm_fderiv_le_eLpNorm_conjWirtingerDeriv_add_eLpNorm (F := F) hp hp_top
      (U := W) (K := Q) isOpen_thickening hK.cthickening hQW
  refine ⟨V, self_subset_thickening hδ K,
    hK.cthickening.of_isClosed_subset isClosed_closure
      (closure_thickening_subset_cthickening δ K),
    (closure_thickening_subset_cthickening δ K).trans hQU, C, ?_⟩
  intro u f hu hf h φ v
  let u₀ := (U : Set ℂ).indicator u
  have hu₀ : MemLp u₀ p volume :=
    (memLp_indicator_iff_restrict U.isOpen.measurableSet.nullMeasurableSet).2 hu
  let ρ : ℕ → ContDiffBump (0 : ℂ) := ContDiffBump.shrinking hδ
  let uε : ℕ → ℂ → F := fun n => (ρ n).normed volume ⋆[lsmul ℝ ℝ] u₀
  have hr (n : ℕ) : (ρ n).rOut ≤ δ := by
    rw [ContDiffBump.rOut_shrinking]
    exact div_le_self hδ.le (by have : 0 ≤ (n : ℝ) := Nat.cast_nonneg n; linarith)
  have hshift (n : ℕ) (x : ℂ) (hx : x ∈ W) (y : ℂ)
      (hy : y ∈ tsupport ((ρ n).normed volume)) : x - y ∈ U := by
    obtain ⟨z, hz, hxz⟩ := mem_thickening_iff.1 hx
    have hyδ : ‖y‖ ≤ δ := by
      rw [(ρ n).tsupport_normed_eq, mem_closedBall_zero_iff] at hy
      exact hy.trans (hr n)
    apply hRU
    apply mem_cthickening_of_dist_le (x - y) z R K hz
    calc dist (x - y) z ≤ dist (x - y) x + dist x z := dist_triangle _ _ _
      _ = ‖y‖ + dist x z := by simp [dist_eq_norm]
      _ ≤ δ + 2 * δ := add_le_add hyδ hxz.le
      _ ≤ R := by dsimp [δ]; linarith
  have hbound (n : ℕ) : eLpNorm (fderiv ℝ (uε n)) p (volume.restrict Q) ≤
      C * (eLpNorm f p (volume.restrict U) + eLpNorm u p (volume.restrict U)) :=
    eLpNorm_fderiv_indicator_convolution_le hp_top hC hu hf h (ρ n)
      isOpen_thickening.measurableSet (hshift n)
  have hsmooth (n : ℕ) : ContDiff ℝ ∞ (uε n) :=
    (ρ n).hasCompactSupport_normed.contDiff_convolution_left (lsmul ℝ ℝ)
      (ρ n).contDiff_normed (hu₀.locallyIntegrable Fact.out)
  have htest (n : ℕ) : ‖∫ z, lineDeriv ℝ (φ : ℂ → ℝ) z v • uε n z‖ₑ ≤
      C * ‖v‖ₑ * (eLpNorm f p (volume.restrict U) + eLpNorm u p (volume.restrict U)) *
        eLpNorm (φ : ℂ → ℝ) q volume := by
    calc ‖∫ z, lineDeriv ℝ (φ : ℂ → ℝ) z v • uε n z‖ₑ ≤
        eLpNorm (φ : ℂ → ℝ) q volume * ‖v‖ₑ *
          eLpNorm (fderiv ℝ (uε n)) p (volume.restrict V) :=
            ((hsmooth n).of_le (by simp)).contDiffOn.enorm_integral_lineDeriv_smul_le φ v
      _ ≤ eLpNorm (φ : ℂ → ℝ) q volume * ‖v‖ₑ *
          (C * (eLpNorm f p (volume.restrict U) + eLpNorm u p (volume.restrict U))) := by
            gcongr
            exact (eLpNorm_mono_measure _ (Measure.restrict_mono hVQ le_rfl)).trans (hbound n)
      _ = _ := by ring
  have hψ : MemLp (fun z => lineDeriv ℝ (φ : ℂ → ℝ) z v) q volume := by
    let ψ : 𝓓(V, ℝ) := TestFunction.lineDerivCLM ℝ v φ
    have hψ := ψ.continuous.memLp_of_hasCompactSupport ψ.hasCompactSupport
      (p := q) (μ := (volume : Measure ℂ))
    simpa only [ψ, TestFunction.coe_lineDerivCLM] using hψ
  have hlim := tendsto_integral_smul_normed_convolution hp_top
    (ContDiffBump.tendsto_rOut_shrinking hδ) hψ hu₀
  have hnormlim := (continuous_enorm.tendsto _).comp hlim
  have hfinal := le_of_tendsto hnormlim (Filter.Eventually.of_forall htest)
  have heq : (∫ z, lineDeriv ℝ (φ : ℂ → ℝ) z v • u₀ z) =
      ∫ z, lineDeriv ℝ (φ : ℂ → ℝ) z v • u z := by
    apply integral_congr_ae
    filter_upwards with z
    by_cases hz : z ∈ (U : Set ℂ)
    · simp [u₀, hz]
    · have hzφ : z ∉ tsupport (φ : ℂ → ℝ) :=
        fun hmem => hz (hQU (hVQ (φ.tsupport_subset hmem)))
      rw [lineDeriv_of_notMem_tsupport hzφ v]
      simp
  rwa [heq] at hfinal

/-- On a finite-measure outer domain, the solution remainder may be measured in any larger
`Lʳ` exponent. In particular this gives the `Lʳ` remainder on relatively compact planar domains;
the source still needs only `Lᵖ` integrability. -/
theorem exists_enorm_integral_lineDeriv_smul_le_of_integral_conjWirtingerDeriv_eq_of_le
    (hp : 1 < p) (hp_top : p ≠ (∞ : ℝ≥0∞)) {r : ℝ≥0∞} (hpr : p ≤ r)
    {U : Opens ℂ} [IsFiniteMeasure (volume.restrict (U : Set ℂ))] {K : Set ℂ}
    (hK : IsCompact K) (hKU : K ⊆ U) :
    ∃ V : Opens ℂ, K ⊆ V ∧ IsCompact (closure (V : Set ℂ)) ∧
      closure (V : Set ℂ) ⊆ U ∧ ∃ C : ℝ≥0,
      ∀ (u f : ℂ → F), MemLp u r (volume.restrict U) → MemLp f p (volume.restrict U) →
      (∀ φ : 𝓓(U, ℝ),
        (∫ z, lineDeriv ℝ (φ : ℂ → ℝ) z 1 • u z) +
          I • (∫ z, lineDeriv ℝ (φ : ℂ → ℝ) z I • u z) =
            -(2 : ℝ) • (∫ z, (φ : ℂ → ℝ) z • f z)) →
      ∀ (φ : 𝓓(V, ℝ)) (v : ℂ),
        ‖∫ z, lineDeriv ℝ (φ : ℂ → ℝ) z v • u z‖ₑ ≤
          C * ‖v‖ₑ * (eLpNorm f p (volume.restrict U) + eLpNorm u r (volume.restrict U)) *
            eLpNorm (φ : ℂ → ℝ) q volume := by
  have hp0 : p ≠ 0 := (zero_lt_one.trans hp).ne'
  have hexp : 0 ≤ 1 / p.toReal - 1 / r.toReal := by
    simp only [one_div, ← ENNReal.toReal_inv]
    exact sub_nonneg.2 (ENNReal.toReal_mono (by simpa using hp0)
      (ENNReal.inv_le_inv.mpr hpr))
  have hfinite : (volume.restrict (U : Set ℂ)) univ ^ (1 / p.toReal - 1 / r.toReal) ≠ ⊤ :=
    ENNReal.rpow_ne_top_of_nonneg hexp (measure_ne_top _ _)
  let A := ((volume.restrict (U : Set ℂ)) univ ^ (1 / p.toReal - 1 / r.toReal)).toNNReal
  let B := max 1 A
  have hB1 : (1 : ℝ≥0∞) ≤ B := by exact_mod_cast (le_max_left (1 : ℝ≥0) A)
  have hBA : (A : ℝ≥0∞) ≤ B := by exact_mod_cast (le_max_right (1 : ℝ≥0) A)
  obtain ⟨V, hKV, hVc, hVU, C, hC⟩ :=
    exists_enorm_integral_lineDeriv_smul_le_of_integral_conjWirtingerDeriv_eq
      (F := F) (q := q) hp hp_top hK hKU
  refine ⟨V, hKV, hVc, hVU, C * B, fun u f hu hf h φ v => ?_⟩
  have hemb : eLpNorm u p (volume.restrict U) ≤ A * eLpNorm u r (volume.restrict U) := by
    calc eLpNorm u p (volume.restrict U) ≤ eLpNorm u r (volume.restrict U) *
        (volume.restrict (U : Set ℂ)) univ ^ (1 / p.toReal - 1 / r.toReal) :=
          eLpNorm_le_eLpNorm_mul_rpow_measure_univ hpr hu.aestronglyMeasurable
      _ = A * eLpNorm u r (volume.restrict U) := by
        rw [ENNReal.coe_toNNReal hfinite]
        exact mul_comm _ _
  have hsum : eLpNorm f p (volume.restrict U) + eLpNorm u p (volume.restrict U) ≤
      B * (eLpNorm f p (volume.restrict U) + eLpNorm u r (volume.restrict U)) := by
    calc _ ≤ eLpNorm f p (volume.restrict U) + A * eLpNorm u r (volume.restrict U) :=
        add_le_add le_rfl hemb
      _ ≤ B * eLpNorm f p (volume.restrict U) + B * eLpNorm u r (volume.restrict U) := by
        apply add_le_add
        · simpa only [one_mul] using
            mul_le_mul' hB1 (le_refl (eLpNorm f p (volume.restrict U)))
        · exact mul_le_mul' hBA le_rfl
      _ = _ := (mul_add ..).symm
  calc ‖∫ z, lineDeriv ℝ (φ : ℂ → ℝ) z v • u z‖ₑ ≤
      C * ‖v‖ₑ * (eLpNorm f p (volume.restrict U) + eLpNorm u p (volume.restrict U)) *
        eLpNorm (φ : ℂ → ℝ) q volume := hC u f (hu.mono_exponent hpr) hf h φ v
    _ ≤ C * ‖v‖ₑ *
        (B * (eLpNorm f p (volume.restrict U) + eLpNorm u r (volume.restrict U))) *
          eLpNorm (φ : ℂ → ℝ) q volume :=
            mul_le_mul' (mul_le_mul' le_rfl hsum) le_rfl
    _ = _ := by push_cast; ring

end TauCeti
