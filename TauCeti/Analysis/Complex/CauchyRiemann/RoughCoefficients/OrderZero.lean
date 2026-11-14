/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.CauchyRiemann.RoughCoefficients.Laplace
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import TauCeti.Analysis.Distribution.TestFunction.Inner
import TauCeti.Analysis.Distribution.TestFunction.LineDeriv
import TauCeti.Analysis.Sobolev.Local.Multiplication
import TauCeti.Analysis.Sobolev.Local.SobolevEmbedding

/-!
# Order-zero interior regularity for Cauchy–Riemann operators with Sobolev coefficients

Let `Ω ⊆ ℂ` be open, write `z = s + i t`, and let `V` be a finite-dimensional real inner product
space. For Sobolev coefficients `J ∈ W^{1,p}_loc(Ω; V →L[ℝ] V)` and `S ∈ Lᵖ_loc(Ω; V →L[ℝ] V)`
with `2 < p < ∞` and `J² = -1` almost everywhere on `Ω`, consider a weak solution `ξ ∈ L^q_loc(Ω)`
of

`∂_s ξ + J ∂_t ξ + S ξ = η`

in the sense of `TauCeti.IsWeakCRSolution q Ω J DJ S ξ η`, where `DJ` is a weak derivative of `J`.

Building on the divergence-form Laplace reduction
`TauCeti.IsSobolevCRCoefficients.integral_laplacian_smul_eq` of
`TauCeti.Analysis.Complex.CauchyRiemann.RoughCoefficients.Laplace`, this file proves the order-zero
interior regularity theorem (McDuff–Salamon, Lemma B.4.6 and the base case `k = 0` of Proposition
B.4.9) and shows that the complex-structure hypothesis `J² = -1` cannot be omitted:

1. **Single-step Sobolev gain** (`TauCeti.IsWeakCRSolution.memWkpLoc_one_of_inv_add_inv_le`,
   McDuff–Salamon Lemma B.4.6). For `2 < p < ∞`, `1 < r < ∞`, `p⁻¹ + q⁻¹ ≤ r⁻¹` and `η ∈ Lʳ_loc`,
   Morrey's embedding supplies a continuous representative of `J` with square `-1` everywhere on
   `Ω`, the auxiliary fields `f` and `g` lie in `Lʳ_loc`, and
   `TauCeti.memWkpLoc_one_of_forall_integral_laplacian_smul_eq` yields `ξ ∈ W^{1,r}_loc(Ω)`.
2. **Bootstrap across the critical exponent**
   (`TauCeti.IsWeakCRSolution.memWkpLoc_one_of_memLpLoc` and
   `TauCeti.IsWeakCRSolution.memWkpLoc_one`). When `p⁻¹ + q⁻¹ < 1` and `η ∈ Lʳ_loc` with
   `1 < r ≤ p`, iterating the single-step gain with the two-dimensional Sobolev embedding
   decreases `q⁻¹` by `(2⁻¹ - p⁻¹) / 2 > 0` at each step until the product exponent exceeds `2`,
   where Morrey's embedding puts `ξ` in `L^∞_loc` and one final step reaches `W^{1,r}_loc(Ω)`.
3. **Sharpness of `J² = -1`** (`TauCeti.exists_isWeakCRSolution_zero_not_memWkpLoc_one`). With
   `J = 0` and `S = 0`, the upper-half-plane indicator is a bounded weak solution of `∂_s ξ = 0`
   that fails to lie in `W^{1,q}_loc(Ω)` for `q > 2` whenever `Ω` meets the real axis.

## Main declarations

* `TauCeti.IsWeakCRSolution.memWkpLoc_one_of_inv_add_inv_le`: single-step regularity
  `ξ ∈ W^{1,r}_loc` when `p⁻¹ + q⁻¹ ≤ r⁻¹` and `η ∈ Lʳ_loc`.
* `TauCeti.IsWeakCRSolution.memWkpLoc_one_of_memLpLoc`: full order-zero gain `ξ ∈ W^{1,r}_loc`
  for `p⁻¹ + q⁻¹ < 1`, `1 < r ≤ p` and `η ∈ Lʳ_loc`.
* `TauCeti.IsWeakCRSolution.memWkpLoc_one`: order-zero regularity `ξ ∈ W^{1,q}_loc` for
  `1 < q ≤ p`, `p⁻¹ + q⁻¹ < 1` and `η ∈ L^q_loc`.
* `TauCeti.exists_isWeakCRSolution_zero_not_memWkpLoc_one`: without `J² = -1`, a bounded weak
  solution for smooth coefficients need not lie in `W^{1,q}_loc`.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  Appendix B.4 (Lemma B.4.6, Proposition B.4.9).
-/

public noncomputable section

open Complex Filter Function LineDeriv MeasureTheory Metric Set TopologicalSpace
open scoped ContDiff Distributions ENNReal InnerProductSpace NNReal Topology

namespace TauCeti

section OrderZeroRegularity

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  {Ω : Opens ℂ} {J S : ℂ → V →L[ℝ] V} {DJ : ℂ → ℂ →L[ℝ] V →L[ℝ] V} {ξ η : ℂ → V}

/-- **Single-step interior Sobolev gain** (McDuff–Salamon, Lemma B.4.6). Suppose `2 < p < ∞`,
`1 < r < ∞`, `p⁻¹ + q⁻¹ ≤ r⁻¹` (allowing `q = ∞`), `J ∈ W^{1,p}_loc(Ω)` with `J² = -1` almost
everywhere on `Ω`, `S ∈ Lᵖ_loc(Ω)` and `η ∈ Lʳ_loc(Ω)`. Every weak solution `ξ ∈ L^q_loc(Ω)` of
`∂_s ξ + J ∂_t ξ + S ξ = η` lies in `W^{1,r}_loc(Ω)`. -/
theorem IsWeakCRSolution.memWkpLoc_one_of_inv_add_inv_le {p q r : ℝ≥0∞} (hp2 : 2 < p) (hp : p ≠ ⊤)
    (hr1 : 1 < r) (hr : r ≠ ⊤) (hpqr : p⁻¹ + q⁻¹ ≤ r⁻¹)
    (hc : IsSobolevCRCoefficients p Ω J DJ S)
    (hJsq : ∀ᵐ z ∂volume.restrict Ω, J z * J z = -1) (hη : MemLpLoc r Ω η)
    (hsol : IsWeakCRSolution q Ω J DJ S ξ η) :
    MemWkpLoc r Ω 1 ξ := by
  have hpq : p⁻¹ + q⁻¹ ≤ 1 := hpqr.trans (ENNReal.inv_le_one.2 hr1.le)
  have hq1 : 1 ≤ q := ENNReal.inv_le_one.1 (le_add_self.trans hpq)
  have hJW1p : MemWkpLoc p Ω 1 J := memWkpLoc_succ_iff_of_isOpen.2
    ⟨hc.memLpLoc_coeff, DJ, hc.hasWeakFDerivOn, memWkpLoc_zero_iff.2 hc.memLpLoc_deriv⟩
  set J' := TauCeti.MeasureTheory.preciseRepresentative volume J
  have hJ'cont : ContinuousOn J' Ω := hJW1p.continuousOn_preciseRepresentative hp2
  have hJJ' : J =ᵐ[volume.restrict Ω] J' :=
    hc.memLpLoc_coeff.ae_eq_preciseRepresentative (one_le_two.trans hp2.le)
  have hc' : IsSobolevCRCoefficients p Ω J' DJ S :=
    ⟨hc.hasWeakFDerivOn.congr_ae hJJ', hc.memLpLoc_coeff.congr_ae hJJ',
      hc.memLpLoc_deriv, hc.memLpLoc_zeroth⟩
  have hsol' : IsWeakCRSolution q Ω J' DJ S ξ η :=
    (isWeakCRSolution_congr_ae hJJ' .rfl .rfl .rfl .rfl).1 hsol
  have hJ'sq_ae : (fun z => J' z * J' z) =ᵐ[volume.restrict Ω] fun _ => -1 := by
    filter_upwards [hJsq, hJJ'] with z hsq hJ' using by rw [← hJ', hsq]
  have hJ'sq : ∀ z ∈ (Ω : Set ℂ), J' z * J' z = -1 :=
    Measure.eqOn_open_of_ae_eq hJ'sq_ae Ω.isOpen (hJ'cont.mul hJ'cont) continuousOn_const
  have hDJ1 : MemLpLoc p Ω (fun z => DJ z 1) :=
    hc.memLpLoc_deriv.clm_comp (ContinuousLinearMap.apply ℝ (V →L[ℝ] V) 1)
  have hDJI : MemLpLoc p Ω (fun z => DJ z I) :=
    hc.memLpLoc_deriv.clm_comp (ContinuousLinearMap.apply ℝ (V →L[ℝ] V) I)
  have hJ'ξ : MemLpLoc q Ω (fun z => J' z (ξ z)) := hsol'.memLpLoc.continuousOn_clm_apply hJ'cont
  have hf : MemLpLoc r Ω (fun z => η z + DJ z I (ξ z) - S z (ξ z)) :=
    (hη.add (hDJI.clm_apply_of_inv_add_inv_le hsol'.memLpLoc hpqr)).sub
      (hc'.memLpLoc_zeroth.clm_apply_of_inv_add_inv_le hsol'.memLpLoc hpqr)
  have hg : MemLpLoc r Ω
      (fun z => -J' z (η z + DJ z I (ξ z) - S z (ξ z)) - DJ z 1 (ξ z) - DJ z I (J' z (ξ z))) :=
    ((hf.continuousOn_clm_apply hJ'cont).neg.sub
      (hDJ1.clm_apply_of_inv_add_inv_le hsol'.memLpLoc hpqr)).sub
      (hDJI.clm_apply_of_inv_add_inv_le hJ'ξ hpqr)
  exact memWkpLoc_one_of_forall_integral_laplacian_smul_eq hr1 hr
    (hsol'.memLpLoc.locallyIntegrableOn hq1 Ω.isOpen.isLocallyClosed) hf hg
    (hc'.integral_laplacian_smul_eq hp hpq hJ'cont hJ'sq hsol')

/-- Upgrading `MemLpLoc` membership of `ξ` upgrades the exponent of `IsWeakCRSolution`. -/
private theorem IsWeakCRSolution.of_memLpLoc {q q' : ℝ≥0∞}
    (hsol : IsWeakCRSolution q Ω J DJ S ξ η) (hξ : MemLpLoc q' Ω ξ) :
    IsWeakCRSolution q' Ω J DJ S ξ η :=
  isWeakCRSolution_iff.2 ⟨hξ, hsol.locallyIntegrableOn, fun φ =>
    ⟨hsol.integrable_inner_crFormalAdjoint φ, hsol.integral_inner_crFormalAdjoint φ⟩⟩

/-- Subcritical Sobolev-embedding step: when `m = (p⁻¹ + q₀⁻¹)⁻¹` satisfies `1 < m ≤ 2` and
`2 < p`, `MemWkpLoc m Ω 1 ξ` embeds into `MemLpLoc s Ω ξ` with
`s⁻¹ = q₀⁻¹ - (2⁻¹ - p⁻¹) / 2`. -/
private theorem memLpLoc_step_of_memWkpLoc_le_two {p q₀ m : ℝ≥0} (hp : 2 < p) (hm1 : 1 < m)
    (hm2 : ¬ 2 < m) (hm_inv : (m : ℝ)⁻¹ = (p : ℝ)⁻¹ + (q₀ : ℝ)⁻¹)
    (hξm : MemWkpLoc m Ω 1 ξ) :
    ∃ s : ℝ≥0, 0 < s ∧ (s : ℝ)⁻¹ = (q₀ : ℝ)⁻¹ - (2⁻¹ - (p : ℝ)⁻¹) / 2 ∧
      MemLpLoc s Ω ξ := by
  have hp2 : (2 : ℝ) < p := by exact_mod_cast hp
  have hp_inv_pos : 0 < (p : ℝ)⁻¹ := by positivity
  have hp_inv_lt : (p : ℝ)⁻¹ < 2⁻¹ := (inv_lt_inv₀ (by positivity) two_pos).2 hp2
  have hm2_le : (m : ℝ) ≤ 2 := by exact_mod_cast not_lt.1 hm2
  have hm_inv_ge : 2⁻¹ ≤ (p : ℝ)⁻¹ + (q₀ : ℝ)⁻¹ := by
    rw [← hm_inv]
    exact (inv_le_inv₀ two_pos (zero_lt_one.trans (by exact_mod_cast hm1))).2 hm2_le
  have hsinv_pos : 0 < (q₀ : ℝ)⁻¹ - (2⁻¹ - (p : ℝ)⁻¹) / 2 := by linarith
  let s : ℝ≥0 := ⟨((q₀ : ℝ)⁻¹ - (2⁻¹ - (p : ℝ)⁻¹) / 2)⁻¹, by positivity⟩
  have hs_pos : 0 < s := by exact_mod_cast inv_pos.2 hsinv_pos
  have hs_inv : (s : ℝ)⁻¹ = (q₀ : ℝ)⁻¹ - (2⁻¹ - (p : ℝ)⁻¹) / 2 := inv_inv _
  have hms : m ≤ s := by
    have : (m : ℝ) ≤ s :=
      (inv_le_inv₀ (by exact_mod_cast hs_pos)
        (zero_lt_one.trans (by exact_mod_cast hm1))).1 (by rw [hm_inv, hs_inv]; linarith)
    exact_mod_cast this
  have hgap : (m : ℝ)⁻¹ - (s : ℝ)⁻¹ ≤ 2⁻¹ := by
    rw [hm_inv, hs_inv]
    linarith
  exact ⟨s, hs_pos, hs_inv, hξm.memLpLoc_of_inv_sub_inv_le hm1.le hms hgap⟩

/-- Inductive exponent-climbing loop for `IsWeakCRSolution.memWkpLoc_one_of_memLpLoc`: each step
decreases `(q₀ : ℝ)⁻¹` by `(2⁻¹ - (p : ℝ)⁻¹) / 2 > 0` until either `(p : ℝ)⁻¹ + q₀⁻¹ ≤ r⁻¹` or the
intermediate Sobolev exponent exceeds `2`. -/
private theorem memWkpLoc_one_bootstrap_aux {p r : ℝ≥0} (hp : 2 < p) (hr : 1 < r) (hrp : r ≤ p)
    (hc : IsSobolevCRCoefficients p Ω J DJ S)
    (hJsq : ∀ᵐ z ∂volume.restrict Ω, J z * J z = -1) (hη : MemLpLoc r Ω η) :
    ∀ (N : ℕ) {q₀ : ℝ≥0}, 0 < q₀ → (p : ℝ)⁻¹ + (q₀ : ℝ)⁻¹ < 1 →
      (q₀ : ℝ)⁻¹ ≤ (N : ℝ) * ((2⁻¹ - (p : ℝ)⁻¹) / 2) →
      IsWeakCRSolution q₀ Ω J DJ S ξ η → MemWkpLoc r Ω 1 ξ
  | 0, q₀, hq0, _, hN, _ => by
      have hq_pos : 0 < (q₀ : ℝ)⁻¹ := inv_pos.2 (by exact_mod_cast hq0)
      simp only [Nat.cast_zero, zero_mul] at hN
      linarith
  | N + 1, q₀, hq0, hpq, hN, hsol => by
      have hp2 : (2 : ℝ) < p := by exact_mod_cast hp
      have hr_pos : (0 : ℝ) < r := zero_lt_one.trans (by exact_mod_cast hr)
      have hp_inv_lt : (p : ℝ)⁻¹ < 2⁻¹ := (inv_lt_inv₀ (by positivity) two_pos).2 hp2
      by_cases hle : (p : ℝ)⁻¹ + (q₀ : ℝ)⁻¹ ≤ (r : ℝ)⁻¹
      · have hle' : (p : ℝ≥0∞)⁻¹ + (q₀ : ℝ≥0∞)⁻¹ ≤ (r : ℝ≥0∞)⁻¹ := by
          rw [← ENNReal.coe_inv (zero_lt_two.trans hp).ne', ← ENNReal.coe_inv hq0.ne',
            ← ENNReal.coe_inv (zero_lt_one.trans hr).ne', ← ENNReal.coe_add]
          exact_mod_cast hle
        exact hsol.memWkpLoc_one_of_inv_add_inv_le (by exact_mod_cast hp) ENNReal.coe_ne_top
          (by exact_mod_cast hr) ENNReal.coe_ne_top hle' hc hJsq hη
      · rw [not_le] at hle
        set m : ℝ≥0 := (p⁻¹ + q₀⁻¹)⁻¹
        have hm_inv : (m : ℝ)⁻¹ = (p : ℝ)⁻¹ + (q₀ : ℝ)⁻¹ := by
          simp [m, NNReal.coe_inv, NNReal.coe_add]
        have hm1 : 1 < m := by
          have : 1 < (m : ℝ) := by
            rw [← inv_inv (m : ℝ), hm_inv]
            exact (one_lt_inv₀ (by positivity)).2 hpq
          exact_mod_cast this
        have hmr : m ≤ r := by
          have : (m : ℝ) ≤ r := (inv_le_inv₀ hr_pos
            (zero_lt_one.trans (by exact_mod_cast hm1))).1 (by linarith)
          exact_mod_cast this
        have hpqm : (p : ℝ≥0∞)⁻¹ + (q₀ : ℝ≥0∞)⁻¹ ≤ (m : ℝ≥0∞)⁻¹ := by
          rw [← ENNReal.coe_inv (zero_lt_two.trans hp).ne', ← ENNReal.coe_inv hq0.ne',
            ← ENNReal.coe_inv (zero_lt_one.trans hm1).ne', ← ENNReal.coe_add]
          exact le_of_eq (by simp [m])
        have hξm : MemWkpLoc m Ω 1 ξ :=
          hsol.memWkpLoc_one_of_inv_add_inv_le (by exact_mod_cast hp) ENNReal.coe_ne_top
            (by exact_mod_cast hm1) ENNReal.coe_ne_top hpqm hc hJsq
            (hη.mono_exponent (by exact_mod_cast hmr))
        by_cases hm2 : 2 < m
        · have : Fact (1 ≤ (m : ℝ≥0∞)) := ⟨by exact_mod_cast hm1.le⟩
          have : ENNReal.HolderTriple (m : ℝ≥0∞) (⊤ : ℝ≥0∞) m := ⟨by simp⟩
          have hξ_top : MemLpLoc ⊤ Ω ξ := hξm.memLpLoc_of_holderTriple hm2 le_rfl
          have hpr : (p : ℝ≥0∞)⁻¹ + (⊤ : ℝ≥0∞)⁻¹ ≤ (r : ℝ≥0∞)⁻¹ := by
            simpa using ENNReal.inv_le_inv.2 (ENNReal.coe_le_coe.2 hrp)
          exact (hsol.of_memLpLoc hξ_top).memWkpLoc_one_of_inv_add_inv_le
            (by exact_mod_cast hp) ENNReal.coe_ne_top (by exact_mod_cast hr) ENNReal.coe_ne_top
            hpr hc hJsq hη
        · obtain ⟨s, hs_pos, hs_inv, hξs⟩ :=
            memLpLoc_step_of_memWkpLoc_le_two hp hm1 hm2 hm_inv hξm
          refine memWkpLoc_one_bootstrap_aux hp hr hrp hc hJsq hη N hs_pos ?_ ?_
            (hsol.of_memLpLoc hξs)
          · rw [hs_inv]
            linarith
          · rw [hs_inv]
            push_cast at hN
            linarith

/-- **Order-zero interior regularity with general right-hand side** (McDuff–Salamon, Proposition
B.4.9 at `k = 0`). Let `2 < p`, `1 < r ≤ p`, and `(p : ℝ≥0∞)⁻¹ + q⁻¹ < 1` (allowing `q = ∞`). If
`J ∈ W^{1,p}_loc(Ω)` with `J² = -1` almost everywhere on `Ω`, `S ∈ Lᵖ_loc(Ω)`, and
`η ∈ Lʳ_loc(Ω)`, then every weak solution `ξ ∈ L^q_loc(Ω)` of `∂_s ξ + J ∂_t ξ + S ξ = η` lies in
`W^{1,r}_loc(Ω)`. -/
theorem IsWeakCRSolution.memWkpLoc_one_of_memLpLoc {p r : ℝ≥0} {q : ℝ≥0∞} (hp : 2 < p)
    (hr : 1 < r) (hrp : r ≤ p) (hpq : (p : ℝ≥0∞)⁻¹ + q⁻¹ < 1)
    (hc : IsSobolevCRCoefficients p Ω J DJ S)
    (hJsq : ∀ᵐ z ∂volume.restrict Ω, J z * J z = -1) (hη : MemLpLoc r Ω η)
    (hsol : IsWeakCRSolution q Ω J DJ S ξ η) :
    MemWkpLoc r Ω 1 ξ := by
  rcases eq_or_ne q ⊤ with rfl | hqt
  · have hpr : (p : ℝ≥0∞)⁻¹ + (⊤ : ℝ≥0∞)⁻¹ ≤ (r : ℝ≥0∞)⁻¹ := by
      simpa using ENNReal.inv_le_inv.2 (ENNReal.coe_le_coe.2 hrp)
    exact hsol.memWkpLoc_one_of_inv_add_inv_le (by exact_mod_cast hp) ENNReal.coe_ne_top
      (by exact_mod_cast hr) ENNReal.coe_ne_top hpr hc hJsq hη
  have hq0 : q ≠ 0 := by
    rintro rfl
    simp at hpq
  lift q to ℝ≥0 using hqt
  have hq_pos : 0 < q := pos_iff_ne_zero.2 (by exact_mod_cast hq0)
  have hp_pos : 0 < p := zero_lt_two.trans hp
  have hpq' : (p : ℝ)⁻¹ + (q : ℝ)⁻¹ < 1 := by
    rw [← ENNReal.coe_inv hp_pos.ne', ← ENNReal.coe_inv hq_pos.ne', ← ENNReal.coe_add] at hpq
    exact_mod_cast hpq
  have hp2 : (2 : ℝ) < p := by exact_mod_cast hp
  have hp_inv_lt : (p : ℝ)⁻¹ < 2⁻¹ := (inv_lt_inv₀ (by positivity) two_pos).2 hp2
  have hδ : 0 < (2⁻¹ - (p : ℝ)⁻¹) / 2 := by linarith
  refine memWkpLoc_one_bootstrap_aux hp hr hrp hc hJsq hη
    ⌈(q : ℝ)⁻¹ / ((2⁻¹ - (p : ℝ)⁻¹) / 2)⌉₊ hq_pos hpq' ?_ hsol
  exact (div_le_iff₀ hδ).1 (Nat.le_ceil _)

/-- **Order-zero interior regularity** (McDuff–Salamon, Proposition B.4.9, `k = 0`). Let `2 < p`,
`1 < q ≤ p`, and `(p : ℝ≥0∞)⁻¹ + (q : ℝ≥0∞)⁻¹ < 1`. If `J ∈ W^{1,p}_loc(Ω)` with `J² = -1` almost
everywhere on `Ω`, `S ∈ Lᵖ_loc(Ω)`, and `η ∈ L^q_loc(Ω)`, then every weak solution
`ξ ∈ L^q_loc(Ω)` of `∂_s ξ + J ∂_t ξ + S ξ = η` lies in `W^{1,q}_loc(Ω)`. -/
theorem IsWeakCRSolution.memWkpLoc_one {p q : ℝ≥0} (hp : 2 < p) (hq : 1 < q) (hqp : q ≤ p)
    (hpq : (p : ℝ≥0∞)⁻¹ + (q : ℝ≥0∞)⁻¹ < 1) (hc : IsSobolevCRCoefficients p Ω J DJ S)
    (hJsq : ∀ᵐ z ∂volume.restrict Ω, J z * J z = -1) (hη : MemLpLoc q Ω η)
    (hsol : IsWeakCRSolution q Ω J DJ S ξ η) :
    MemWkpLoc q Ω 1 ξ :=
  hsol.memWkpLoc_one_of_memLpLoc hp hq hqp hpq hc hJsq hη

end OrderZeroRegularity

section Counterexample

/-- Horizontal-line fundamental theorem of calculus for `(∂_1 φ)(s + i t)`: integrating in `s : ℝ`
vanishes for every fixed `t : ℝ`. -/
private theorem integral_lineDerivOp_one_slice_eq_zero {Ω : Opens ℂ} (φ : 𝓓(Ω, ℝ)) (t : ℝ) :
    (∫ s : ℝ, (∂_{(1 : ℂ)} φ : 𝓓(Ω, ℝ)) ((s : ℂ) + t * I)) = 0 := by
  let emb : ℝ → ℂ := fun s => (s : ℂ) + t * I
  let g : ℝ → ℝ := fun s => (φ : ℂ → ℝ) (emb s)
  let g' : ℝ → ℝ := fun s => (∂_{(1 : ℂ)} φ : 𝓓(Ω, ℝ)) (emb s)
  have hg_deriv (s : ℝ) : HasDerivAt g (g' s) s := by
    have hemb : HasFDerivAt emb Complex.ofRealCLM s :=
      (Complex.ofRealCLM.hasFDerivAt (x := s)).add_const ((t : ℂ) * I)
    have hd := ((φ.contDiff.differentiable (by simp) (emb s)).hasFDerivAt.comp s hemb).hasDerivAt
    simpa only [g, g', Function.comp_def, TestFunction.lineDerivOp_apply_eq_fderiv,
      ContinuousLinearMap.comp_apply, Complex.ofRealCLM_apply, Complex.ofReal_one] using hd
  obtain ⟨R, hR⟩ := φ.hasCompactSupport.isCompact.isBounded.subset_closedBall (0 : ℂ)
  have hcs (θ : 𝓓(Ω, ℝ)) (hθ : tsupport (θ : ℂ → ℝ) ⊆ tsupport (φ : ℂ → ℝ)) :
      Integrable (fun s : ℝ => (θ : ℂ → ℝ) (emb s)) := by
    refine (θ.continuous.comp (Complex.continuous_ofReal.add
      continuous_const)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_support_subset_isCompact (isCompact_Icc (a := -R) (b := R))
        fun s hs => ?_)
    have hz : emb s ∈ closedBall (0 : ℂ) R := hR (hθ (subset_tsupport _ hs))
    rw [mem_closedBall_zero_iff] at hz
    have hre : (emb s).re = s := by simp [emb]
    exact abs_le.1 (hre ▸ (Complex.abs_re_le_norm (emb s)).trans hz)
  exact integral_eq_zero_of_hasDerivAt_of_integrable hg_deriv
    (hcs (∂_{(1 : ℂ)} φ) (φ.tsupport_lineDerivOp_subset 1)) (hcs φ subset_rfl)

/-- The indicator of the upper half-plane solves `∂_s ξ = 0` weakly in `L^∞_loc(Ω)` on every open
planar domain `Ω`. -/
private theorem isWeakCRSolution_upperHalfPlaneIndicator (Ω : Opens ℂ) :
    IsWeakCRSolution ⊤ Ω 0 0 0 ({z : ℂ | 0 < z.im}.indicator fun _ => (1 : ℝ)) 0 := by
  set ξ : ℂ → ℝ := {z : ℂ | 0 < z.im}.indicator fun _ => 1
  have hmeas : MeasurableSet {z : ℂ | 0 < z.im} := measurableSet_lt measurable_const measurable_im
  have hξ_top : MemLpLoc ⊤ Ω ξ := memLpLoc_iff.2 fun K _ hK => by
    have : IsFiniteMeasure (volume.restrict K) := ⟨by simpa using hK.measure_lt_top⟩
    exact memLp_indicator_const ⊤ hmeas.nullMeasurableSet 1 (Or.inr (measure_ne_top _ _))
  refine isWeakCRSolution_iff.2 ⟨hξ_top, locallyIntegrableOn_zero, fun φ => ?_⟩
  have hloc := hξ_top.locallyIntegrableOn le_top Ω.isOpen.isLocallyClosed
  have hint₀ : Integrable (fun z => fderiv ℝ (φ : ℂ → ℝ) z 1 * ξ z) := by
    simpa [mul_comm] using φ.integrable_inner_fderiv hloc 1
  have hadj (z : ℂ) : ⟪crFormalAdjoint 0 0 0 φ z, ξ z⟫_ℝ = -(fderiv ℝ (φ : ℂ → ℝ) z 1 * ξ z) := by
    rw [inner_crFormalAdjoint]; simp [mul_comm]
  simp_rw [hadj]
  refine ⟨hint₀.neg, ?_⟩
  simp only [Pi.zero_apply, inner_zero_right, integral_zero, integral_neg, neg_eq_zero]
  rw [← (Complex.volume_preserving_equiv_real_prod.symm _).integral_comp'
    (fun z => fderiv ℝ (φ : ℂ → ℝ) z 1 * ξ z), Measure.volume_eq_prod]
  have hp_int : Integrable (fun p : ℝ × ℝ =>
      fderiv ℝ (φ : ℂ → ℝ) (Complex.measurableEquivRealProd.symm p) 1 *
        ξ (Complex.measurableEquivRealProd.symm p)) (volume.prod volume) := by
    rw [← Measure.volume_eq_prod]
    exact ((Complex.volume_preserving_equiv_real_prod.symm _).integrable_comp_emb
      Complex.measurableEquivRealProd.symm.measurableEmbedding).2 hint₀
  rw [integral_prod_symm _ hp_int]
  refine integral_eq_zero_of_ae (.of_forall fun t => ?_)
  simp only [Pi.zero_apply]
  by_cases ht : 0 < t
  · have hξt (s : ℝ) : ξ (Complex.measurableEquivRealProd.symm (s, t)) = 1 :=
      indicator_of_mem ht _
    have hsymm (s : ℝ) : Complex.measurableEquivRealProd.symm (s, t) = (s : ℂ) + t * I := by
      apply Complex.ext <;> simp
    simp_rw [hξt, mul_one, hsymm, ← TestFunction.lineDerivOp_apply_eq_fderiv]
    exact integral_lineDerivOp_one_slice_eq_zero φ t
  · have hξt (s : ℝ) : ξ (Complex.measurableEquivRealProd.symm (s, t)) = 0 :=
      indicator_of_notMem ht _
    simp_rw [hξt, mul_zero, integral_zero]

/-- Any continuous function `g` on `Ω` agreeing almost everywhere on `Ω` with the upper-half-plane
indicator equals `1` on `ball z₀ ε ∩ {z | 0 < z.im}` and `0` on `ball z₀ ε ∩ {z | z.im < 0}`
whenever `ball z₀ ε ⊆ Ω`. -/
private theorem eqOn_ball_inter_upper_lower {Ω : Opens ℂ} {g : ℂ → ℝ} (hg_cont : ContinuousOn g Ω)
    (hg_ae : ({z : ℂ | 0 < z.im}.indicator fun _ => (1 : ℝ)) =ᵐ[volume.restrict Ω] g)
    {z₀ : ℂ} {ε : ℝ} (hball : ball z₀ ε ⊆ Ω) :
    EqOn (fun _ => (1 : ℝ)) g (ball z₀ ε ∩ {z | 0 < z.im}) ∧
      EqOn (fun _ => (0 : ℝ)) g (ball z₀ ε ∩ {z | z.im < 0}) := by
  set Up : Set ℂ := ball z₀ ε ∩ {z | 0 < z.im}
  set Un : Set ℂ := ball z₀ ε ∩ {z | z.im < 0}
  have hUp_open : IsOpen Up := isOpen_ball.inter (isOpen_lt continuous_const continuous_im)
  have hUn_open : IsOpen Un := isOpen_ball.inter (isOpen_lt continuous_im continuous_const)
  have hgp_ae : (fun _ : ℂ => (1 : ℝ)) =ᵐ[volume.restrict Up] g := by
    filter_upwards [ae_restrict_of_ae_restrict_of_subset (inter_subset_left.trans hball) hg_ae,
      ae_restrict_mem hUp_open.measurableSet] with z hzg hz
    exact hzg ▸ (indicator_of_mem hz.2 (fun _ => (1 : ℝ))).symm
  have hgn_ae : (fun _ : ℂ => (0 : ℝ)) =ᵐ[volume.restrict Un] g := by
    filter_upwards [ae_restrict_of_ae_restrict_of_subset (inter_subset_left.trans hball) hg_ae,
      ae_restrict_mem hUn_open.measurableSet] with z hzg hz
    have hzim : z ∉ {w : ℂ | 0 < w.im} := fun hpos =>
      ((mem_ofPred.1 hz.2).trans (mem_ofPred.1 hpos)).false
    exact hzg ▸ (indicator_of_notMem hzim (fun _ => (1 : ℝ))).symm
  exact ⟨Measure.eqOn_open_of_ae_eq hgp_ae hUp_open continuousOn_const
      (hg_cont.mono (inter_subset_left.trans hball)),
    Measure.eqOn_open_of_ae_eq hgn_ae hUn_open continuousOn_const
      (hg_cont.mono (inter_subset_left.trans hball))⟩

/-- On an open set `Ω` meeting the real axis, the indicator of the upper half-plane does not belong
to `W^{1,q}_loc(Ω)` for any `q > 2`. -/
private theorem not_memWkpLoc_one_upperHalfPlaneIndicator {Ω : Opens ℂ} {z₀ : ℂ} (hz₀ : z₀ ∈ Ω)
    (him : z₀.im = 0) {q : ℝ≥0∞} (hq : 2 < q) :
    ¬ MemWkpLoc q Ω 1 ({z : ℂ | 0 < z.im}.indicator fun _ => (1 : ℝ)) := by
  intro hW
  set ξ : ℂ → ℝ := {z : ℂ | 0 < z.im}.indicator fun _ => 1
  set g := TauCeti.MeasureTheory.preciseRepresentative volume ξ
  have hg_cont : ContinuousOn g Ω := hW.continuousOn_preciseRepresentative hq
  have hg_ae : ξ =ᵐ[volume.restrict Ω] g :=
    hW.memLpLoc.ae_eq_preciseRepresentative (one_le_two.trans hq.le)
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 Ω.isOpen z₀ hz₀
  obtain ⟨hgp, hgn⟩ := eqOn_ball_inter_upper_lower hg_cont hg_ae hball
  let δ : ℕ → ℝ := fun n => ε / ((n : ℝ) + 2)
  have hδ_pos (n : ℕ) : 0 < δ n := div_pos hε (by positivity)
  have hδ_lt (n : ℕ) : δ n < ε := div_lt_self hε (by linarith [Nat.cast_nonneg (α := ℝ) n])
  have hseq : Tendsto (fun n : ℕ => (δ n : ℂ) * I) atTop (𝓝 0) := by
    simpa [δ] using (Complex.continuous_ofReal.tendsto 0).comp
      ((tendsto_const_nhds (x := ε)).div_atTop
        (tendsto_atTop_add_const_right _ 2 tendsto_natCast_atTop_atTop)) |>.mul_const I
  have hlim_p : Tendsto (fun n : ℕ => z₀ + (δ n : ℂ) * I) atTop (𝓝 z₀) := by
    simpa using tendsto_const_nhds.add hseq
  have hlim_n : Tendsto (fun n : ℕ => z₀ - (δ n : ℂ) * I) atTop (𝓝 z₀) := by
    simpa using tendsto_const_nhds.sub hseq
  have hmem_p (n : ℕ) : z₀ + (δ n : ℂ) * I ∈ ball z₀ ε ∩ {z | 0 < z.im} := by
    refine ⟨?_, by simp [him, hδ_pos n]⟩
    rw [mem_ball, dist_self_add_left, norm_mul, Complex.norm_I, mul_one,
      Complex.norm_real, Real.norm_of_nonneg (hδ_pos n).le]
    exact hδ_lt n
  have hmem_n (n : ℕ) : z₀ - (δ n : ℂ) * I ∈ ball z₀ ε ∩ {z | z.im < 0} := by
    refine ⟨?_, by simp [him, hδ_pos n]⟩
    rw [mem_ball, sub_eq_add_neg, dist_self_add_left, norm_neg, norm_mul, Complex.norm_I,
      mul_one, Complex.norm_real, Real.norm_of_nonneg (hδ_pos n).le]
    exact hδ_lt n
  have hc_z₀ := (hg_cont z₀ hz₀).continuousAt (Ω.isOpen.mem_nhds hz₀)
  have h1 : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 (g z₀)) :=
    (hc_z₀.tendsto.comp hlim_p).congr fun n => (hgp (hmem_p n)).symm
  have h0 : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 (g z₀)) :=
    (hc_z₀.tendsto.comp hlim_n).congr fun n => (hgn (hmem_n n)).symm
  have h10 : (1 : ℝ) = 0 :=
    (tendsto_nhds_unique tendsto_const_nhds h1).trans (tendsto_nhds_unique h0 tendsto_const_nhds)
  norm_num at h10

/-- **Sharpness of `J² = -1`.** With `J = 0` and `S = 0` (smooth coefficients violating
`J² = -1`), the indicator of the upper half-plane is a bounded weak solution of `∂_s ξ = 0` on
every open set `Ω`, yet on any `Ω` meeting the real axis it fails to lie in `W^{1,q}_loc(Ω)` for
every `q > 2`. -/
theorem exists_isWeakCRSolution_zero_not_memWkpLoc_one {Ω : Opens ℂ} {z₀ : ℂ} (hz₀ : z₀ ∈ Ω)
    (him : z₀.im = 0) {q : ℝ≥0∞} (hq : 2 < q) :
    ∃ ξ : ℂ → ℝ, IsWeakCRSolution ⊤ Ω 0 0 0 ξ 0 ∧ ¬ MemWkpLoc q Ω 1 ξ :=
  ⟨_, isWeakCRSolution_upperHalfPlaneIndicator Ω,
    not_memWkpLoc_one_upperHalfPlaneIndicator hz₀ him hq⟩

end Counterexample

end TauCeti
