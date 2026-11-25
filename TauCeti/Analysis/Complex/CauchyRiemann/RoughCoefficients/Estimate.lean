/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Basic
public import TauCeti.Analysis.Complex.CauchyRiemann.RoughCoefficients.OrderZero
public import TauCeti.Analysis.Sobolev.Local.Norm
import TauCeti.Analysis.Complex.Wirtinger.DivergenceLaplace.Estimate
import TauCeti.Analysis.Sobolev.Local.SobolevEmbedding
import TauCeti.Data.ENNReal.Holder
import TauCeti.Topology.Sets.Opens

/-!
# The order-zero estimate for real Cauchy–Riemann equations with Sobolev coefficients

Let `Ω ⊆ ℂ` be open, write `z = s + i t`, and let `V` be a finite-dimensional real inner product
space. For coefficients `J ∈ W^{1,p}(Ω; End V)` with `J² = -1` and `S ∈ Lᵖ(Ω; End V)`, `p > 2`,
let `ξ ∈ L^q_loc` be a weak solution of

`∂_s ξ + J ∂_t ξ + S ξ = η`

in the sense of `TauCeti.IsWeakCRSolution`, with `η ∈ Lʳ_loc`, `1 < r < ∞` and
`1/p + 1/q ≤ 1/r`. The order-zero lemma `TauCeti.IsWeakCRSolution.memWkpLoc_one` shows
`ξ ∈ W^{1,r}_loc(Ω)`. This file proves the accompanying estimate (McDuff–Salamon, Lemma B.4.6):
for every set `U` with compact closure in `Ω`,

`‖ξ‖_{W^{1,r}(U)} ≤ C (‖η‖_{Lʳ(Ω)} + ‖ξ‖_{L^q(Ω)})`,

where `C` depends only on `p`, `q`, `r`, `U`, `Ω`, `V` and a bound `M` for `‖J‖_{W^{1,p}(Ω)}`
and `‖S‖_{Lᵖ(Ω)}` (`TauCeti.exists_eLpNormWkp_one_le_of_isWeakCRSolution`). The constant is
chosen before the coefficients, so a single constant serves every pair `(J, S)` in a bounded set:
this is the uniformity clause of the estimate at order zero.

## The argument

Shrink `Ω` to an open set `W` with `closure U ⊆ W` and compact closure `closure W ⊆ Ω`. On `W` the
solution satisfies the divergence-form Laplace equation `Δξ = ∂_s f + ∂_t g` with the data
`f = TauCeti.crDivergenceDataS DJ S ξ η` and `g = TauCeti.crDivergenceDataT J DJ S ξ η`
(`TauCeti.IsWeakCRSolution.integral_laplacian_smul_eq`), so the interior estimate for that
equation (`TauCeti.exists_eLpNormWkp_one_le_of_integral_laplacian_smul_eq`) bounds
`‖ξ‖_{W^{1,r}(U)}` by `‖f‖_{Lʳ(W)} + ‖g‖_{Lʳ(W)} + ‖ξ‖_{L^q(W)}`. Each term of `f` and `g` is a
product of `η` or `ξ` with factors among `J`, `DJ` and `S`. Hölder's inequality bounds it by
`‖J‖_{L^∞(W)}`, `‖DJ‖_{Lᵖ(Ω)}` and `‖S‖_{Lᵖ(Ω)}` times `‖η‖_{Lʳ(Ω)}` or `‖ξ‖_{L^{q'}(W)}`, where
`1/p + 1/q' = 1/r` and `q' ≤ q`, so that `‖ξ‖_{L^{q'}(W)}` is at most a multiple of
`‖ξ‖_{L^q(Ω)}` because `W` has finite measure. Morrey's embedding bounds `‖J‖_{L^∞(W)}` by a
multiple of `‖J‖_{W^{1,p}(Ω)}` (`TauCeti.exists_eLpNorm_top_le_mul_eLpNormWkp_one`).

## Main results

* `TauCeti.exists_eLpNormWkp_one_le_of_isWeakCRSolution`: the order-zero interior estimate, with
  a constant uniform over coefficients bounded in `W^{1,p} × Lᵖ`.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  Appendix B.4, Lemma B.4.6 and its proof.
-/

public section

open MeasureTheory TopologicalSpace Complex Set
open scoped ENNReal NNReal

namespace TauCeti

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  {Ω : Opens ℂ} {p q r : ℝ≥0∞}

/-- On a set `W` with compact closure, `‖u‖_{L^{q'}(W)} ≤ c ‖u‖_{L^q(W)}` for `q' ≤ q`, with `c`
independent of `u`. -/
private theorem exists_eLpNorm_le_mul_eLpNorm_of_le {E : Type*} [NormedAddCommGroup E]
    {q' : ℝ≥0∞} (hq'q : q' ≤ q) {W : Set ℂ} (hWc : IsCompact (closure W)) :
    ∃ c : ℝ≥0, ∀ u : ℂ → E, AEStronglyMeasurable u (volume.restrict W) →
      eLpNorm u q' (volume.restrict W) ≤ c * eLpNorm u q (volume.restrict W) := by
  by_cases hW0 : volume W = 0
  · exact ⟨0, fun u _ => by simp [Measure.restrict_eq_zero.2 hW0]⟩
  have hWt : volume W ≠ ⊤ :=
    ((measure_mono subset_closure).trans_lt hWc.measure_lt_top).ne
  refine ⟨(volume W ^ (1 / q'.toReal - 1 / q.toReal)).toNNReal, fun u hu => ?_⟩
  rw [ENNReal.coe_toNNReal (ENNReal.rpow_ne_top_of_ne_zero hW0 hWt), mul_comm]
  simpa using eLpNorm_le_eLpNorm_mul_rpow_measure_univ hq'q hu

/-- For `p ≠ 0` and `1/p + 1/q ≤ 1/r` there is `q' ≤ q` with `1/p + 1/q' = 1/r`. -/
private theorem exists_holderTriple_le (hp : p ≠ 0) (hpqr : p⁻¹ + q⁻¹ ≤ r⁻¹) :
    ∃ q', ENNReal.HolderTriple p q' r ∧ q' ≤ q := by
  refine ⟨(r⁻¹ - p⁻¹)⁻¹, .of_le (ENNReal.inv_le_inv.1 (le_self_add.trans hpqr)),
    ENNReal.inv_le_inv.1 ?_⟩
  rw [inv_inv]
  exact ENNReal.le_sub_of_add_le_left (ENNReal.inv_ne_top.2 hp) hpqr

/-- The final bookkeeping of the order-zero estimate:
`C ((1 + k) a + 3 (1 + k) m (c b) + b) ≤ C (2 + k + 3 (1 + k) m c) (a + b)`. -/
private theorem mul_add_le_mul_mul_add (C k m c a b : ℝ≥0∞) :
    C * ((1 + k) * a + 3 * (1 + k) * m * (c * b) + b) ≤
      C * (2 + k + 3 * (1 + k) * m * c) * (a + b) :=
  calc C * ((1 + k) * a + 3 * (1 + k) * m * (c * b) + b)
      ≤ C * ((1 + k) * a + 3 * (1 + k) * m * (c * b) + b +
          ((3 * (1 + k) * m * c + 1) * a + (1 + k) * b)) := mul_le_mul_right le_self_add _
    _ = C * (2 + k + 3 * (1 + k) * m * c) * (a + b) := by ring

section DivergenceData

variable {μ : Measure ℂ} [ENNReal.HolderTriple p q r] {J S : ℂ → V →L[ℝ] V}
  {DJ : ℂ → ℂ →L[ℝ] V →L[ℝ] V} {ξ η : ℂ → V}

omit [CompleteSpace V] in
/-- Hölder's inequality for `z ↦ A z (w z)` with `A ∈ Lᵃ` and `w ∈ Lᵇ`. -/
private theorem eLpNorm_apply_le {a b c : ℝ≥0∞} [ENNReal.HolderTriple a b c] {A : ℂ → V →L[ℝ] V}
    {w : ℂ → V} (hA : AEStronglyMeasurable A μ) (hw : AEStronglyMeasurable w μ) :
    eLpNorm (fun z => A z (w z)) c μ ≤ eLpNorm A a μ * eLpNorm w b μ := by
  simpa using eLpNorm_le_eLpNorm_mul_eLpNorm_of_norm (p := a) (q := b)
    (fun (B : V →L[ℝ] V) (v : V) => B v) 1 isBoundedBilinearMap_apply.continuous hA hw
    (.of_forall fun z => by simpa using (A z).le_opNorm (w z))

omit [CompleteSpace V] in
/-- Hölder's inequality for `z ↦ DJ z c (w z)` with `‖c‖ = 1`, `DJ ∈ Lᵃ` and `w ∈ Lᵇ`. -/
private theorem eLpNorm_apply_apply_le {a b c' : ℝ≥0∞} [ENNReal.HolderTriple a b c'] {c : ℂ}
    (hc : ‖c‖ = 1) {w : ℂ → V} (hDJ : AEStronglyMeasurable DJ μ)
    (hw : AEStronglyMeasurable w μ) :
    eLpNorm (fun z => DJ z c (w z)) c' μ ≤ eLpNorm DJ a μ * eLpNorm w b μ := by
  simpa using eLpNorm_le_eLpNorm_mul_eLpNorm_of_norm (p := a) (q := b)
    (fun (B : ℂ →L[ℝ] V →L[ℝ] V) (v : V) => B c v) 1
    ((continuous_fst.clm_apply continuous_const).clm_apply continuous_snd) hDJ hw
    (.of_forall fun z => by
      simpa [hc] using ((DJ z c).le_opNorm (w z)).trans
        (mul_le_mul_of_nonneg_right ((DJ z).le_opNorm c) (norm_nonneg _)))

omit [CompleteSpace V] in
/-- The `Lʳ` bound for the data `f = η + (∂_t J) ξ - S ξ`. -/
private theorem eLpNorm_crDivergenceDataS_le (hr : 1 ≤ r) (hDJ : AEStronglyMeasurable DJ μ)
    (hS : AEStronglyMeasurable S μ) (hξ : AEStronglyMeasurable ξ μ) :
    eLpNorm (crDivergenceDataS DJ S ξ η) r μ ≤ eLpNorm η r μ +
      eLpNorm DJ p μ * eLpNorm ξ q μ + eLpNorm S p μ * eLpNorm ξ q μ := by
  rw [show crDivergenceDataS DJ S ξ η = η + (fun z => DJ z I (ξ z)) - fun z => S z (ξ z) from
    funext (crDivergenceDataS_apply DJ S ξ η)]
  exact (eLpNorm_sub_le hr).trans (add_le_add ((eLpNorm_add_le hr).trans (add_le_add le_rfl
    (eLpNorm_apply_apply_le (a := p) (b := q) norm_I hDJ hξ)))
    (eLpNorm_apply_le (a := p) (b := q) hS hξ))

omit [CompleteSpace V] in
/-- The `Lʳ` bound for the data `g = J S ξ - J η - (∂_s J) ξ - (∂_t J) J ξ - J (∂_t J) ξ`. -/
private theorem eLpNorm_crDivergenceDataT_le (hr : 1 ≤ r) (hJ : AEStronglyMeasurable J μ)
    (hDJ : AEStronglyMeasurable DJ μ) (hS : AEStronglyMeasurable S μ)
    (hξ : AEStronglyMeasurable ξ μ) (hη : AEStronglyMeasurable η μ) :
    eLpNorm (crDivergenceDataT J DJ S ξ η) r μ ≤
      eLpNorm J ∞ μ * (eLpNorm S p μ * eLpNorm ξ q μ) + eLpNorm J ∞ μ * eLpNorm η r μ +
        eLpNorm DJ p μ * eLpNorm ξ q μ + eLpNorm DJ p μ * (eLpNorm J ∞ μ * eLpNorm ξ q μ) +
        eLpNorm J ∞ μ * (eLpNorm DJ p μ * eLpNorm ξ q μ) := by
  have hA : Continuous fun x : (V →L[ℝ] V) × V => x.1 x.2 :=
    isBoundedBilinearMap_apply.continuous
  have hSξ : AEStronglyMeasurable (fun z => S z (ξ z)) μ := hA.comp_aestronglyMeasurable₂ hS hξ
  have hJξ : AEStronglyMeasurable (fun z => J z (ξ z)) μ := hA.comp_aestronglyMeasurable₂ hJ hξ
  have hDJξ : AEStronglyMeasurable (fun z => DJ z I (ξ z)) μ :=
    ((continuous_fst.clm_apply continuous_const).clm_apply continuous_snd :
      Continuous fun x : (ℂ →L[ℝ] V →L[ℝ] V) × V => x.1 I x.2).comp_aestronglyMeasurable
        (hDJ.prodMk hξ)
  -- Hölder's inequality for each of the five terms.
  have t1 := (eLpNorm_apply_le (a := ∞) (b := r) (c := r) hJ hSξ).trans
    (mul_le_mul_right (eLpNorm_apply_le (a := p) (b := q) (c := r) hS hξ) (eLpNorm J ∞ μ))
  have t2 := eLpNorm_apply_le (a := ∞) (b := r) (c := r) hJ hη
  have t3 := eLpNorm_apply_apply_le (a := p) (b := q) (c' := r) norm_one hDJ hξ
  have t4 := (eLpNorm_apply_apply_le (a := p) (b := q) (c' := r) norm_I hDJ hJξ).trans
    (mul_le_mul_right (eLpNorm_apply_le (a := ∞) (b := q) (c := q) hJ hξ) (eLpNorm DJ p μ))
  have t5 := (eLpNorm_apply_le (a := ∞) (b := r) (c := r) hJ hDJξ).trans
    (mul_le_mul_right (eLpNorm_apply_apply_le (a := p) (b := q) (c' := r) norm_I hDJ hξ)
      (eLpNorm J ∞ μ))
  rw [show crDivergenceDataT J DJ S ξ η = (fun z => J z (S z (ξ z))) - (fun z => J z (η z)) -
      (fun z => DJ z 1 (ξ z)) - (fun z => DJ z I (J z (ξ z))) - fun z => J z (DJ z I (ξ z)) from
    funext (crDivergenceDataT_apply J DJ S ξ η)]
  exact (eLpNorm_sub_le hr).trans (add_le_add ((eLpNorm_sub_le hr).trans
    (add_le_add ((eLpNorm_sub_le hr).trans (add_le_add ((eLpNorm_sub_le hr).trans
      (add_le_add t1 t2)) t3)) t4)) t5)

omit [CompleteSpace V] in
/-- The `Lʳ` bound for the divergence-form data `f` and `g` together, in terms of bounds `k` for
`‖J‖_{L^∞}`, `m` for `‖DJ‖_{Lᵖ}` and `‖S‖_{Lᵖ}`, `a` for `‖η‖_{Lʳ}` and `x` for `‖ξ‖_{L^q}`. -/
private theorem eLpNorm_crDivergenceData_add_le (hr : 1 ≤ r) (hJ : AEStronglyMeasurable J μ)
    (hDJ : AEStronglyMeasurable DJ μ) (hS : AEStronglyMeasurable S μ)
    (hξ : AEStronglyMeasurable ξ μ) (hη : AEStronglyMeasurable η μ) {k m a x : ℝ≥0∞}
    (hJk : eLpNorm J ∞ μ ≤ k) (hDJm : eLpNorm DJ p μ ≤ m) (hSm : eLpNorm S p μ ≤ m)
    (hηa : eLpNorm η r μ ≤ a) (hξx : eLpNorm ξ q μ ≤ x) :
    eLpNorm (crDivergenceDataS DJ S ξ η) r μ + eLpNorm (crDivergenceDataT J DJ S ξ η) r μ ≤
      (1 + k) * a + 3 * (1 + k) * m * x :=
  calc eLpNorm (crDivergenceDataS DJ S ξ η) r μ + eLpNorm (crDivergenceDataT J DJ S ξ η) r μ
      ≤ (a + m * x + m * x) + (k * (m * x) + k * a + m * x + m * (k * x) + k * (m * x)) :=
        add_le_add ((eLpNorm_crDivergenceDataS_le hr hDJ hS hξ).trans (by gcongr))
          ((eLpNorm_crDivergenceDataT_le hr hJ hDJ hS hξ hη).trans (by gcongr))
    _ = (1 + k) * a + 3 * (1 + k) * m * x := by ring

end DivergenceData

/-- **The order-zero interior estimate for real Cauchy–Riemann equations with Sobolev
coefficients** (McDuff–Salamon, Lemma B.4.6). Let `V` be finite-dimensional, `p > 2`,
`1 < r < ∞` and `1/p + 1/q ≤ 1/r`, let `U` have compact closure in `Ω`, and let `M ≥ 0`. There is
a constant `C` such that for all coefficients `J ∈ W^{1,p}(Ω)` with `J² = -1` almost everywhere
and `S ∈ Lᵖ(Ω)`, in the sense of `TauCeti.IsSobolevCRCoefficients`, with
`‖J‖_{W^{1,p}(Ω)} ≤ M` and `‖S‖_{Lᵖ(Ω)} ≤ M`, every weak solution `ξ ∈ L^q_loc` of
`∂_s ξ + J ∂_t ξ + S ξ = η` on `Ω` with `η ∈ Lʳ_loc` satisfies
`‖ξ‖_{W^{1,r}(U)} ≤ C (‖η‖_{Lʳ(Ω)} + ‖ξ‖_{L^q(Ω)})`.

The constant depends only on `p`, `q`, `r`, `U`, `Ω`, `V` and `M`, and not on `(J, S)`: one
constant serves every pair of coefficients in a bounded set. -/
theorem exists_eLpNormWkp_one_le_of_isWeakCRSolution [FiniteDimensional ℝ V] (hp : 2 < p)
    (hpqr : p⁻¹ + q⁻¹ ≤ r⁻¹) (hr : 1 < r) (hr_top : r ≠ ⊤) {U : Set ℂ}
    (hUc : IsCompact (closure U)) (hUΩ : closure U ⊆ Ω) (M : ℝ≥0) :
    ∃ C : ℝ≥0, ∀ (J S : ℂ → V →L[ℝ] V) (DJ : ℂ → ℂ →L[ℝ] V →L[ℝ] V) (ξ η : ℂ → V),
      IsWeakCRSolution q Ω J DJ S ξ η → IsSobolevCRCoefficients p Ω J DJ S →
      (∀ᵐ z ∂volume.restrict Ω, J z * J z = -1) → eLpNormWkp p Ω 1 J ≤ M →
      eLpNorm S p (volume.restrict Ω) ≤ M → MemLpLoc r Ω η →
      eLpNormWkp r U 1 ξ ≤ C * (eLpNorm η r (volume.restrict Ω) +
        eLpNorm ξ q (volume.restrict Ω)) := by
  have hr1 : 1 ≤ r := hr.le
  have hpq1 : p⁻¹ + q⁻¹ ≤ 1 := hpqr.trans (ENNReal.inv_le_one.2 hr1)
  have hq1 : 1 ≤ q := ENNReal.one_le_right_of_inv_add_inv_le_one hpq1
  obtain ⟨q', _, hq'q⟩ := exists_holderTriple_le (zero_lt_two.trans hp).ne' hpqr
  -- An intermediate open set `W` with `closure U ⊆ W` and `closure W` compact in `Ω`.
  obtain ⟨W, hUW, hWΩ, hWc⟩ := Opens.exists_between_and_isCompact_closure hUc hUΩ
  have hWle : W ≤ Ω := subset_closure.trans hWΩ
  -- The divergence-form Laplace estimate on `W`, the Morrey bound for `J` on `W`, and the
  -- comparison of `L^{q'}(W)` with `L^q(W)`.
  obtain ⟨CL, hCL⟩ := exists_eLpNormWkp_one_le_of_integral_laplacian_smul_eq (V := V) hr hr_top
    hq1 hUc hUW
  obtain ⟨Cm, hCm⟩ := exists_eLpNorm_top_le_mul_eLpNormWkp_one (F := V →L[ℝ] V) hp hWc hWΩ
  obtain ⟨c, hc⟩ := exists_eLpNorm_le_mul_eLpNorm_of_le (E := V) hq'q hWc
  refine ⟨CL * (2 + Cm * M + 3 * (1 + Cm * M) * M * c),
    fun J S DJ ξ η h hco hJ2 hJM hSM hη => ?_⟩
  set μ := volume.restrict (W : Set ℂ)
  have hμ : μ ≤ volume.restrict Ω := Measure.restrict_mono hWle le_rfl
  -- The solution satisfies the divergence-form Laplace equation on `W`.
  have hW : IsWeakCRSolution q W J DJ S ξ η := h.mono hWle
  have hcW : IsSobolevCRCoefficients p W J DJ S :=
    ⟨hco.hasWeakFDerivOn.mono hWle, hco.memLpLoc_coeff.mono_set hWle,
      hco.memLpLoc_deriv.mono_set hWle, hco.memLpLoc_zeroth.mono_set hWle⟩
  obtain ⟨hf, hg⟩ := hW.memLpLoc_crDivergenceData hcW (hcW.memLpLoc_top_coeff hp) hpqr
    (hη.mono_set hWle)
  have hmain := hCL ξ _ _ (hW.memLpLoc.locallyIntegrableOn hq1 W.isOpen.isLocallyClosed) hf hg
    (hW.integral_laplacian_smul_eq hcW hp (ae_mono hμ hJ2) hpq1)
  -- Bounds for the factors on `W`.
  have hm {s : ℝ≥0∞} {u : ℂ → V →L[ℝ] V} (hu : MemLpLoc s Ω u) : AEStronglyMeasurable u μ :=
    (hu.memLp_restrict_of_isCompact_closure hWc hWΩ).aestronglyMeasurable
  have hmV {s : ℝ≥0∞} {u : ℂ → V} (hu : MemLpLoc s Ω u) : AEStronglyMeasurable u μ :=
    (hu.memLp_restrict_of_isCompact_closure hWc hWΩ).aestronglyMeasurable
  have hJk : eLpNorm J ∞ μ ≤ (Cm * M : ℝ≥0) := (hCm J).trans <| by
    rw [ENNReal.coe_mul]
    gcongr
  have hDJM : eLpNorm DJ p μ ≤ M := by
    refine (eLpNorm_mono_measure _ hμ).trans (le_trans ?_ hJM)
    rw [eLpNormWkp_succ_eq_of_hasWeakFDerivOn (k := 0) hco.hasWeakFDerivOn, eLpNormWkp_zero]
    exact le_add_self
  have hdata := eLpNorm_crDivergenceData_add_le (q := q') hr1 (hm hco.memLpLoc_coeff)
    (hco.memLpLoc_deriv.memLp_restrict_of_isCompact_closure hWc hWΩ).aestronglyMeasurable
    (hm hco.memLpLoc_zeroth) (hmV h.memLpLoc) (hmV hη) hJk hDJM
    ((eLpNorm_mono_measure _ hμ).trans hSM) (eLpNorm_mono_measure _ hμ)
    ((hc ξ (hmV h.memLpLoc)).trans (mul_le_mul_right (eLpNorm_mono_measure _ hμ) _))
  -- Collect the terms.
  refine hmain.trans ((mul_le_mul_right (add_le_add hdata (eLpNorm_mono_measure _ hμ)) _).trans ?_)
  convert mul_add_le_mul_mul_add CL _ M c _ _ using 2
  push_cast
  ring

end TauCeti
