/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.CauchyRiemann.RoughCoefficients.Laplace
import TauCeti.Analysis.Complex.Wirtinger.DivergenceLaplace
import TauCeti.Analysis.Distribution.TestFunction.Inner
import TauCeti.Analysis.Green.HalfPlane
import TauCeti.Analysis.Sobolev.Local.ChangeOfVariables
import TauCeti.Analysis.Sobolev.Local.Examples
import TauCeti.Analysis.Sobolev.Local.Multiplication
import TauCeti.Analysis.Sobolev.Local.SobolevEmbedding
import TauCeti.Data.ENNReal.Inv

/-!
# Order-zero interior regularity for Cauchy–Riemann operators with Sobolev coefficients

Let `Ω ⊆ ℂ` be open, write `z = s + i t`, and let `V` be a finite-dimensional real inner product
space. For Sobolev coefficients `J ∈ W^{1,p}_loc(Ω; V →L[ℝ] V)` and `S ∈ Lᵖ_loc(Ω; V →L[ℝ] V)`
with `2 < p ≤ ∞` and `J² = -1` almost everywhere on `Ω`, consider a weak solution `ξ ∈ L^q_loc(Ω)`
of

`∂_s ξ + J ∂_t ξ + S ξ = η`

in the sense of `TauCeti.IsWeakCRSolution q Ω J DJ S ξ η`, where `DJ` is a weak derivative of `J`.

Building on the divergence-form Laplace reduction
`TauCeti.IsSobolevCRCoefficients.integral_laplacian_smul_eq` of
`TauCeti.Analysis.Complex.CauchyRiemann.RoughCoefficients.Laplace`, this file proves the order-zero
interior regularity theorem (McDuff–Salamon, Lemma B.4.6 and the base case `k = 0` of Proposition
B.4.9) and shows that the complex-structure hypothesis `J² = -1` cannot be omitted:

1. **Single-step Sobolev gain** (`TauCeti.IsWeakCRSolution.memWkpLoc_one_of_inv_add_inv_le`,
   McDuff–Salamon Lemma B.4.6). For `2 < p ≤ ∞`, `1 < r < ∞`, `p⁻¹ + q⁻¹ ≤ r⁻¹` and `η ∈ Lʳ_loc`,
   Morrey's embedding supplies a continuous representative of `J` with square `-1` everywhere on
   `Ω`, the auxiliary fields `f` and `g` lie in `Lʳ_loc`, and
   `TauCeti.memWkpLoc_one_of_forall_integral_laplacian_smul_eq` yields `ξ ∈ W^{1,r}_loc(Ω)`.
2. **Bootstrap across the critical exponent**
   (`TauCeti.IsWeakCRSolution.memWkpLoc_one_of_memLpLoc` and
   `TauCeti.IsWeakCRSolution.memWkpLoc_one`). When `2 < p ≤ ∞`, `p⁻¹ + q⁻¹ < 1`, and `η ∈ Lʳ_loc`
   with `1 < r < ∞` and `r ≤ p`, truncating `p` to a finite exponent `p₀ > 2` and iterating the
   single-step gain with the two-dimensional Sobolev embedding decreases `q⁻¹` by
   `(2⁻¹ - p₀⁻¹) / 2 > 0` at each step until the product exponent exceeds `2`, where Morrey's
   embedding puts `ξ` in `L^∞_loc` and one final step reaches `W^{1,r}_loc(Ω)`.
3. **Sharpness of `J² = -1`** (`TauCeti.exists_isWeakCRSolution_zero_not_memWkpLoc_one`). On any
   nonempty open set `Ω`, with `J = 0` and `S = 0`, there exists a weak solution `ξ ∈ L^∞_loc(Ω)`
   of `∂_s ξ = 0` that fails to lie in `W^{1,q}_loc(Ω)` for every `q : ℝ≥0∞`.

## Main declarations

* `TauCeti.IsWeakCRSolution.memWkpLoc_one_of_inv_add_inv_le`: single-step regularity
  `ξ ∈ W^{1,r}_loc` when `2 < p ≤ ∞`, `1 < r < ∞`, `p⁻¹ + q⁻¹ ≤ r⁻¹` and `η ∈ Lʳ_loc`.
* `TauCeti.IsWeakCRSolution.memWkpLoc_one_of_memLpLoc`: full order-zero gain `ξ ∈ W^{1,r}_loc`
  for `2 < p ≤ ∞`, `p⁻¹ + q⁻¹ < 1`, `1 < r < ∞`, `r ≤ p`, and `η ∈ Lʳ_loc`.
* `TauCeti.IsWeakCRSolution.memWkpLoc_one`: order-zero regularity `ξ ∈ W^{1,q}_loc` for
  `2 < p ≤ ∞`, `q < ∞`, `q ≤ p`, `p⁻¹ + q⁻¹ < 1`, and `η ∈ L^q_loc`.
* `TauCeti.exists_isWeakCRSolution_zero_not_memWkpLoc_one`: on any nonempty open `Ω`, without
  `J² = -1` there exists a weak solution in `L^∞_loc(Ω)` for smooth coefficients that lies in
  `W^{1,q}_loc(Ω)` for no `q : ℝ≥0∞`.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  Appendix B.4 (Lemma B.4.6, Proposition B.4.9).
-/

public noncomputable section

open Complex Filter Function MeasureTheory Metric Set TopologicalSpace
open scoped ContDiff Distributions ENNReal InnerProductSpace NNReal Topology

namespace TauCeti

section OrderZeroRegularity

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  {Ω : Opens ℂ} {J S : ℂ → V →L[ℝ] V} {DJ : ℂ → ℂ →L[ℝ] V →L[ℝ] V} {ξ η : ℂ → V}

/-- **Single-step interior Sobolev gain** (McDuff–Salamon, Lemma B.4.6). Suppose `2 < p ≤ ∞`,
`1 < r < ∞`, `p⁻¹ + q⁻¹ ≤ r⁻¹` (allowing `p = ∞` and `q = ∞`), `J ∈ W^{1,p}_loc(Ω)` with
`J² = -1` almost everywhere on `Ω`, `S ∈ Lᵖ_loc(Ω)` and `η ∈ Lʳ_loc(Ω)`. Every weak solution
`ξ ∈ L^q_loc(Ω)` of `∂_s ξ + J ∂_t ξ + S ξ = η` lies in `W^{1,r}_loc(Ω)`. -/
theorem IsWeakCRSolution.memWkpLoc_one_of_inv_add_inv_le {p q r : ℝ≥0∞} (hp2 : 2 < p)
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
  refine memWkpLoc_one_of_forall_integral_laplacian_smul_eq hr1 hr
    (hsol'.memLpLoc.locallyIntegrableOn hq1 Ω.isOpen.isLocallyClosed) hf hg fun φ => ?_
  rcases ne_or_eq p ⊤ with hp | rfl
  · exact hc'.integral_laplacian_smul_eq hp hpq hJ'cont hJ'sq hsol' φ
  · have hr_inv : r⁻¹ < 1 := ENNReal.inv_lt_one.2 hr1
    have hp0 : (1 - r⁻¹)⁻¹ ≠ ⊤ := ENNReal.inv_ne_top.2 (tsub_pos_of_lt hr_inv).ne'
    have hq_le : q⁻¹ ≤ r⁻¹ := by simpa using hpqr
    have hp0q : ((1 - r⁻¹)⁻¹)⁻¹ + q⁻¹ ≤ 1 := by
      rw [inv_inv]
      exact (by gcongr : 1 - r⁻¹ + q⁻¹ ≤ 1 - r⁻¹ + r⁻¹).trans_eq (tsub_add_cancel_of_le hr_inv.le)
    have hc0 : IsSobolevCRCoefficients (1 - r⁻¹)⁻¹ Ω J' DJ S :=
      ⟨hc'.hasWeakFDerivOn, hc'.memLpLoc_coeff.mono_exponent le_top,
        hc'.memLpLoc_deriv.mono_exponent le_top, hc'.memLpLoc_zeroth.mono_exponent le_top⟩
    exact hc0.integral_laplacian_smul_eq hp0 hp0q hJ'cont hJ'sq hsol' φ

/-- Endpoint `q = ⊤` of `IsWeakCRSolution.memWkpLoc_one_of_memLpLoc`: a locally bounded weak
solution reaches `W^{1,r}_loc(Ω)` in a single step whenever `1 < r ≤ p`. -/
private theorem memWkpLoc_one_of_isWeakCRSolution_top {p r : ℝ≥0} (hp : 2 < p) (hr : 1 < r)
    (hrp : r ≤ p) (hc : IsSobolevCRCoefficients p Ω J DJ S)
    (hJsq : ∀ᵐ z ∂volume.restrict Ω, J z * J z = -1) (hη : MemLpLoc r Ω η)
    (hsol : IsWeakCRSolution ⊤ Ω J DJ S ξ η) :
    MemWkpLoc r Ω 1 ξ := by
  have hpr : (p : ℝ≥0∞)⁻¹ + (⊤ : ℝ≥0∞)⁻¹ ≤ (r : ℝ≥0∞)⁻¹ := by
    simpa using ENNReal.inv_le_inv.2 (ENNReal.coe_le_coe.2 hrp)
  exact hsol.memWkpLoc_one_of_inv_add_inv_le (by exact_mod_cast hp) (by exact_mod_cast hr)
    ENNReal.coe_ne_top hpr hc hJsq hη

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
      have hr_pos : (0 : ℝ) < r := zero_lt_one.trans (by exact_mod_cast hr)
      -- Branch 1: `p⁻¹ + q₀⁻¹ ≤ r⁻¹`, so a single gain step already reaches `W^{1,r}_loc`.
      by_cases hle : (p : ℝ)⁻¹ + (q₀ : ℝ)⁻¹ ≤ (r : ℝ)⁻¹
      · have hle' : (p : ℝ≥0∞)⁻¹ + (q₀ : ℝ≥0∞)⁻¹ ≤ (r : ℝ≥0∞)⁻¹ := by
          rw [← ENNReal.coe_inv (zero_lt_two.trans hp).ne', ← ENNReal.coe_inv hq0.ne',
            ← ENNReal.coe_inv (zero_lt_one.trans hr).ne', ← ENNReal.coe_add]
          exact_mod_cast hle
        exact hsol.memWkpLoc_one_of_inv_add_inv_le (by exact_mod_cast hp) (by exact_mod_cast hr)
          ENNReal.coe_ne_top hle' hc hJsq hη
      · -- Otherwise gain one derivative at the intermediate Hölder exponent `m = (p⁻¹ + q₀⁻¹)⁻¹`.
        rw [not_le] at hle
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
          hsol.memWkpLoc_one_of_inv_add_inv_le (by exact_mod_cast hp) (by exact_mod_cast hm1)
            ENNReal.coe_ne_top hpqm hc hJsq (hη.mono_exponent (by exact_mod_cast hmr))
        by_cases hm2 : 2 < m
        · -- Branch 2: `2 < m`, so Morrey's embedding puts `ξ` in `L^∞_loc` and one step finishes.
          have : Fact (1 ≤ (m : ℝ≥0∞)) := ⟨by exact_mod_cast hm1.le⟩
          have : ENNReal.HolderTriple (m : ℝ≥0∞) (⊤ : ℝ≥0∞) m := ⟨by simp⟩
          exact memWkpLoc_one_of_isWeakCRSolution_top hp hr hrp hc hJsq hη
            (hsol.of_memLpLoc (hξm.memLpLoc_of_holderTriple hm2 le_rfl))
        · -- Branch 3: `m ≤ 2`, so Sobolev embedding decreases `q₀⁻¹` by `(2⁻¹ - p⁻¹) / 2`.
          obtain ⟨s, hs_pos, hs_inv, hξs⟩ :=
            memLpLoc_step_of_memWkpLoc_le_two hp hm1 hm2 hm_inv hξm
          have hp_inv_lt : (p : ℝ)⁻¹ < 2⁻¹ :=
            (inv_lt_inv₀ (by positivity) two_pos).2 (by exact_mod_cast hp)
          refine memWkpLoc_one_bootstrap_aux hp hr hrp hc hJsq hη N hs_pos
            (by rw [hs_inv]; linarith) ?_ (hsol.of_memLpLoc hξs)
          rw [hs_inv]; push_cast at hN; linarith

/-- **Order-zero interior regularity with general right-hand side** (McDuff–Salamon, Proposition
B.4.9 at `k = 0`). Let `2 < p ≤ ∞`, `1 < r < ∞`, `r ≤ p`, and `p⁻¹ + q⁻¹ < 1` (allowing `p = ∞`
and `q = ∞`). If `J ∈ W^{1,p}_loc(Ω)` with `J² = -1` almost everywhere on `Ω`, `S ∈ Lᵖ_loc(Ω)`,
and `η ∈ Lʳ_loc(Ω)`, then every weak solution `ξ ∈ L^q_loc(Ω)` of `∂_s ξ + J ∂_t ξ + S ξ = η` lies
in `W^{1,r}_loc(Ω)`. -/
theorem IsWeakCRSolution.memWkpLoc_one_of_memLpLoc {p q r : ℝ≥0∞} (hp : 2 < p)
    (hr : 1 < r) (hr_top : r ≠ ⊤) (hrp : r ≤ p) (hpq : p⁻¹ + q⁻¹ < 1)
    (hc : IsSobolevCRCoefficients p Ω J DJ S)
    (hJsq : ∀ᵐ z ∂volume.restrict Ω, J z * J z = -1) (hη : MemLpLoc r Ω η)
    (hsol : IsWeakCRSolution q Ω J DJ S ξ η) :
    MemWkpLoc r Ω 1 ξ := by
  obtain ⟨p₀, hp₀, hrp₀, hp₀p, hp₀q⟩ :=
    ENNReal.exists_nnreal_two_lt_and_le_and_inv_add_inv_lt_one hp hr_top hrp hpq
  lift r to ℝ≥0 using hr_top
  have hr' : 1 < r := by exact_mod_cast hr
  have hrp₀' : r ≤ p₀ := ENNReal.coe_le_coe.1 hrp₀
  have hc₀ := hc.mono_exponent hp₀p
  rcases eq_or_ne q ⊤ with rfl | hqt
  · exact memWkpLoc_one_of_isWeakCRSolution_top hp₀ hr' hrp₀' hc₀ hJsq hη hsol
  have hq0 : q ≠ 0 := by rintro rfl; simp at hp₀q
  lift q to ℝ≥0 using hqt
  have hq_pos : 0 < q := pos_iff_ne_zero.2 (by exact_mod_cast hq0)
  have hp₀_pos : 0 < p₀ := zero_lt_two.trans hp₀
  have hp₀q' : (p₀ : ℝ)⁻¹ + (q : ℝ)⁻¹ < 1 := by
    rw [← ENNReal.coe_inv hp₀_pos.ne', ← ENNReal.coe_inv hq_pos.ne', ← ENNReal.coe_add] at hp₀q
    exact_mod_cast hp₀q
  have hp₀2 : (2 : ℝ) < p₀ := by exact_mod_cast hp₀
  have hp₀_inv_lt : (p₀ : ℝ)⁻¹ < 2⁻¹ := (inv_lt_inv₀ (by positivity) two_pos).2 hp₀2
  have hδ : 0 < (2⁻¹ - (p₀ : ℝ)⁻¹) / 2 := by linarith
  refine memWkpLoc_one_bootstrap_aux hp₀ hr' hrp₀' hc₀ hJsq hη
    ⌈(q : ℝ)⁻¹ / ((2⁻¹ - (p₀ : ℝ)⁻¹) / 2)⌉₊ hq_pos hp₀q' ?_ hsol
  exact (div_le_iff₀ hδ).1 (Nat.le_ceil _)

/-- **Order-zero interior regularity** (McDuff–Salamon, Proposition B.4.9, `k = 0`). Let
`2 < p ≤ ∞`, `q < ∞`, `q ≤ p`, and `p⁻¹ + q⁻¹ < 1` (which in particular forces `1 < q`). If
`J ∈ W^{1,p}_loc(Ω)` with `J² = -1` almost everywhere on `Ω`, `S ∈ Lᵖ_loc(Ω)`, and
`η ∈ L^q_loc(Ω)`, then every weak solution `ξ ∈ L^q_loc(Ω)` of `∂_s ξ + J ∂_t ξ + S ξ = η` lies in
`W^{1,q}_loc(Ω)`. -/
theorem IsWeakCRSolution.memWkpLoc_one {p q : ℝ≥0∞} (hp : 2 < p) (hq_top : q ≠ ⊤) (hqp : q ≤ p)
    (hpq : p⁻¹ + q⁻¹ < 1) (hc : IsSobolevCRCoefficients p Ω J DJ S)
    (hJsq : ∀ᵐ z ∂volume.restrict Ω, J z * J z = -1) (hη : MemLpLoc q Ω η)
    (hsol : IsWeakCRSolution q Ω J DJ S ξ η) :
    MemWkpLoc q Ω 1 ξ :=
  hsol.memWkpLoc_one_of_memLpLoc hp (ENNReal.inv_lt_one.1 (le_add_self.trans_lt hpq)) hq_top hqp
    hpq hc hJsq hη

end OrderZeroRegularity

section Counterexample

/-- The indicator of the horizontal half-plane `{z : ℂ | t₀ < z.im}` solves `∂_s ξ = 0` weakly in
`L^∞_loc(Ω)` on every open planar domain `Ω`. -/
private theorem isWeakCRSolution_upperHalfPlaneIndicator (t₀ : ℝ) (Ω : Opens ℂ) :
    IsWeakCRSolution ⊤ Ω 0 0 0 ({z : ℂ | t₀ < z.im}.indicator fun _ => (1 : ℝ)) 0 := by
  set ξ : ℂ → ℝ := {z : ℂ | t₀ < z.im}.indicator fun _ => 1
  have hmeas : MeasurableSet {z : ℂ | t₀ < z.im} := measurableSet_lt measurable_const measurable_im
  have hmeas0 : MeasurableSet {z : ℂ | 0 < z.im} := measurableSet_lt measurable_const measurable_im
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
  let c : ℂ := Complex.I * (t₀ : ℂ)
  let g : ℂ → ℝ := (φ : ℂ → ℝ) ∘ fun z => z + c
  have hg_diff : ContDiff ℝ 1 g :=
    (φ.contDiff.of_le (by simp)).comp (contDiff_id.add contDiff_const)
  have hg_supp : HasCompactSupport g :=
    φ.hasCompactSupport.comp_homeomorph (Homeomorph.addRight c)
  have hshift (z : ℂ) :
      ({w : ℂ | t₀ < w.im}.indicator fun w => fderiv ℝ (φ : ℂ → ℝ) w 1) (z + c) =
        {w : ℂ | 0 < w.im}.indicator (fun w => fderiv ℝ g w 1) z := by
    have hdf : fderiv ℝ g z 1 = fderiv ℝ (φ : ℂ → ℝ) (z + c) 1 := by
      have hd := (((φ.contDiff.of_le (by simp)).differentiable one_ne_zero
        (z + c)).hasFDerivAt.comp z ((hasFDerivAt_id z).add_const c)).fderiv
      simpa [g] using congr($hd 1)
    simp [Set.indicator_apply, c, hdf]
  have hind : (fun z => fderiv ℝ (φ : ℂ → ℝ) z 1 * ξ z) =
      {z : ℂ | t₀ < z.im}.indicator fun z => fderiv ℝ (φ : ℂ → ℝ) z 1 := by
    ext z; by_cases hz : t₀ < z.im <;> simp [ξ, hz]
  simp only [Pi.zero_apply, inner_zero_right, integral_zero, integral_neg, neg_eq_zero, hind]
  rw [← integral_add_right_eq_self _ c]
  simp_rw [hshift]
  rw [integral_indicator hmeas0]
  exact setIntegral_im_pos_fderiv_one_eq_zero hg_diff hg_supp

/-- Around any point `z₀ ∈ Ω`, the indicator of `{z : ℂ | z₀.im < z.im}` does not belong to
`W^{1,q}_loc(Ω)` for any `q : ℝ≥0∞`. -/
private theorem not_memWkpLoc_one_upperHalfPlaneIndicator {Ω : Opens ℂ} {z₀ : ℂ} (hz₀ : z₀ ∈ Ω)
    (q : ℝ≥0∞) :
    ¬ MemWkpLoc q Ω 1 ({z : ℂ | z₀.im < z.im}.indicator fun _ => (1 : ℝ)) := by
  intro hW
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 Ω.isOpen z₀ hz₀
  let A : ℂ ≃L[ℝ] ℂ :=
    ((LinearEquiv.smulOfNeZero ℂ ℂ Complex.I Complex.I_ne_zero).restrictScalars ℝ
      ).toContinuousLinearEquiv
  have hA (z : ℂ) : A z = Complex.I * z := by simp [A]
  have hmaps : MapsTo (fun z => A z + z₀) (ball 0 ε) Ω := fun z hz => by
    refine hball ?_
    rw [mem_ball, dist_eq_norm, add_sub_cancel_right, hA, norm_mul, Complex.norm_I, one_mul]
    simpa using hz
  have h' : MemWkpLoc q (ball 0 ε) 1 ({z : ℂ | 0 < z.re}.indicator fun _ => (1 : ℝ)) := by
    convert hW.comp_continuousLinearEquiv_add A z₀ hmaps using 2 with z
    by_cases hz : 0 < z.re <;> simp [hA, hz]
  have h0 : (0 : ℂ) ∈ interior (ball (0 : ℂ) ε) := by
    rw [isOpen_ball.interior_eq]; exact mem_ball_self hε
  exact not_memWkpLoc_indicator_re_pos (k := 0) h0 Complex.zero_re h'

/-- **Sharpness of `J² = -1`.** On any nonempty open planar set `Ω`, there exists a weak solution
`ξ ∈ L^∞_loc(Ω)` of the homogeneous equation `∂_s ξ = 0` (`J = 0`, `S = 0`, smooth coefficients
violating `J² = -1`) that fails to belong to `W^{1,q}_loc(Ω)` for every `q : ℝ≥0∞`. -/
theorem exists_isWeakCRSolution_zero_not_memWkpLoc_one {Ω : Opens ℂ}
    (hΩ : (Ω : Set ℂ).Nonempty) :
    ∃ ξ : ℂ → ℝ, IsWeakCRSolution ⊤ Ω 0 0 0 ξ 0 ∧ ∀ q, ¬ MemWkpLoc q Ω 1 ξ := by
  obtain ⟨z₀, hz₀⟩ := hΩ
  exact ⟨_, isWeakCRSolution_upperHalfPlaneIndicator z₀.im Ω,
    not_memWkpLoc_one_upperHalfPlaneIndicator hz₀⟩

end Counterexample

end TauCeti
