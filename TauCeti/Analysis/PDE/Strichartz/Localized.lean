/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Strichartz.TTStar
import TauCeti.Analysis.PDE.Strichartz.Retarded
import TauCeti.Analysis.SpecialFunctions.Pow.NNReal
import TauCeti.MeasureTheory.Function.L2Space
import TauCeti.MeasureTheory.Function.Lp.LIntegralRpow
import TauCeti.MeasureTheory.Function.Lp.Integral.Functional
import TauCeti.MeasureTheory.Integral.Kernel.Pairing
import TauCeti.MeasureTheory.Integral.Lebesgue.SlidingWindow

/-!
# Time pairings localized to a dyadic time separation

Let `U(t) : H → L²(X, μ)`, `t ∈ ℝ`, be a family of bounded operators from a Hilbert space into an
`L²` space, as in `TauCeti.Analysis.PDE.Strichartz.TTStar`. The retarded `TT*` form

`T(F, G) = ∫∫_{s < t} ⟪U(s)* F(s), U(t)* G(t)⟫ ds dt`

controls the inhomogeneous Strichartz estimates. At the endpoint `q = 2` the time kernel is not
integrable, and Keel and Tao split `T` into the pieces `T_L` in which the time separation is of
size `L`, with `L` running over the powers of two:

`T_L(F, G) = ∫ ⟪∫_{t - 2L ≤ s < t - L} U(s)* F(s) ds, U(t)* G(t)⟫ dt`.

Each piece satisfies bounds in `L²_t L^{a'}_x × L²_t L^{b'}_x` with an explicit power of `L`, and
these localized bounds are then summed over `L` by bilinear real interpolation. This file proves
them at the corners from which Keel and Tao obtain the general exponents by interpolation
(Keel–Tao, proof of Lemma 4.1).

* **The decay corner.** If the time pairings decay like `A |s - t| ^ (-γ)` from `L^{r'}` to
  `L^r`, `γ ≥ 0`, then on the region `L < t - s ≤ 2L` they are at most `A L^{-γ}`, and the window
  kernel has `L²` operator norm `L`. Hence
  `∫∫_{t - 2L ≤ s < t - L} |⟪U(s)* F(s), U(t)* G(t)⟫| ≤ A L^{1-γ} ‖F‖_{L² L^{r'}} ‖G‖_{L² L^{r'}}`.
  For `r = ∞` and the decay `|s - t| ^ (-σ)` of a dispersive estimate, this is Keel and Tao's
  case `(a, b) = (∞, ∞)`; for general `r` it is the diagonal case `a = b = r`.
* **The energy corner.** If `‖U(t)‖ ≤ B` and the pairings decay like `A |s - t| ^ (-2/q)` from
  `L^{r'}` to `L^r` with `2 < q < ∞`, then the non-endpoint dual estimate
  `‖∫_J U(s)* F(s) ds‖ ≤ C A^{1/2} ‖F‖_{L^{q'}(J; L^{r'})}` of the `TT*` argument, applied on the
  window `J = [t - 2L, t - L)` of length `L`, together with Hölder's inequality in time on `J`
  gives `|T_L(F, G)| ≤ C A^{1/2} B L^{1 - 1/q} ‖F‖_{L² L^{r'}} ‖G‖_{L² L²}`, Keel and Tao's case
  `b = 2`.
* **The exchanged energy corner.** Exchanging the order of integration writes `T_L(F, G)` as
  `∫ ⟪U(s)* F(s), ∫_{s + L < t ≤ s + 2L} U(t)* G(t) dt⟫ ds`, and the same argument on the windows
  `(s + L, s + 2L]` gives `|T_L(F, G)| ≤ C A^{1/2} B L^{1 - 1/q} ‖F‖_{L² L²} ‖G‖_{L² L^{r'}}`,
  Keel and Tao's case `a = 2`.

Both corners are proved for an arbitrary measurable window `W` of time separations `s - t`: the
decay bound for windows whose points satisfy `|w| ≥ ρ > 0`, and the energy bound from an abstract
dual estimate with a time exponent `p ≤ 2`. The dyadic time shells of
`TauCeti.Analysis.PDE.Strichartz.TimeShell` are the symmetric windows `ρ ≤ |s - t| < 2ρ`.

## Main declarations

* `TauCeti.enorm_setIntegral_adjoint_le_of_le_two`: a dual estimate with a time exponent `p ≤ 2`
  on a set of times, with an `L²` norm in time.
* `TauCeti.lintegral_setLIntegral_sub_preimage_enorm_inner_adjoint_le`: the decay bound for an
  arbitrary measurable window.
* `TauCeti.lintegral_setLIntegral_enorm_inner_adjoint_le`: the decay corner for the absolute
  values of the localized pairings.
* `TauCeti.enorm_integral_inner_setIntegral_adjoint_le`: the decay corner for `T_L`.
* `TauCeti.enorm_integral_inner_setIntegral_sub_preimage_adjoint_le`: the energy bound for an
  arbitrary measurable window and an abstract dual estimate.
* `TauCeti.exists_enorm_integral_inner_setIntegral_sub_preimage_adjoint_le`: the energy bound for
  an arbitrary measurable window at a non-endpoint exponent.
* `TauCeti.exists_enorm_integral_inner_setIntegral_adjoint_le`: the energy corner for `T_L`.
* `TauCeti.exists_enorm_integral_inner_setIntegral_adjoint_le'`: the exchanged energy corner.

## References

* M. Keel and T. Tao, *Endpoint Strichartz estimates*, Amer. J. Math. 120 (1998), 955–980,
  Section 4, Lemma 4.1.
* T. Tao, *Nonlinear Dispersive Equations: Local and Global Analysis*, CBMS Regional Conference
  Series in Mathematics 106, AMS, 2006, Section 2.3.
-/

public section

open MeasureTheory Set
open scoped ENNReal NNReal InnerProductSpace InnerProduct ComplexConjugate Pointwise

namespace TauCeti

variable {𝕜 X E H : Type*} [RCLike 𝕜] {mX : MeasurableSpace X} {μ : Measure X}
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
  [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]
  {r r' : ℝ≥0∞} [r'.HolderConjugate r]

/-- The window `[t - 2L, t - L)` is the translate by `t` of `[-2L, -L)`. -/
private theorem Ico_sub_eq_preimage (L t : ℝ) :
    Ico (t - 2 * L) (t - L) = (fun s ↦ s - t) ⁻¹' Ico (-(2 * L)) (-L) := by
  rw [preimage_sub_const_Ico, neg_add_eq_sub, neg_add_eq_sub]

private theorem volume_Ico_neg (L : ℝ) : volume (Ico (-(2 * L)) (-L)) = ENNReal.ofReal L := by
  rw [Real.volume_Ico]
  congr 1
  ring

/-- **The decay bound on sliding windows.** Let `U(t) : H → L²(X, μ)` be bounded operators whose
time pairings decay from `L^{r'}` to `L^r`, `‖U(s) U(t)* g‖_r ≤ A |s - t| ^ (-γ) ‖g‖_{r'}` for
`s ≠ t`, with `γ ≥ 0`. Let `W ⊆ ℝ` be a measurable window whose points satisfy `|w| ≥ ρ > 0`.
Then for almost everywhere strongly measurable `F, G : ℝ → L²(X, μ)`,

`∫∫_{s - t ∈ W} |⟪U(s)* F(s), U(t)* G(t)⟫| ≤ A ρ^{-γ} |W| ‖F‖_{L² L^{r'}} ‖G‖_{L² L^{r'}}`. -/
theorem lintegral_setLIntegral_sub_preimage_enorm_inner_adjoint_le {U : ℝ → H →L[𝕜] Lp E 2 μ}
    {A : ℝ≥0∞} {γ ρ : ℝ} (hγ : 0 ≤ γ) (hρ : 0 < ρ)
    (hU : ∀ s t, s ≠ t → ∀ g : Lp E 2 μ,
      eLpNorm (U s (((U t)†) g)) r μ ≤ A * ‖s - t‖ₑ ^ (-γ) * eLpNorm g r' μ)
    {W : Set ℝ} (hW : MeasurableSet W) (hWρ : ∀ w ∈ W, ρ ≤ |w|)
    {F G : ℝ → Lp E 2 μ} (hF : AEStronglyMeasurable F) (hG : AEStronglyMeasurable G) :
    ∫⁻ t, ∫⁻ s in (fun s ↦ s - t) ⁻¹' W, ‖⟪((U s)†) (F s), ((U t)†) (G t)⟫_𝕜‖ₑ ≤
      A * ENNReal.ofReal ρ ^ (-γ) * volume W * eLpNorm (fun s ↦ eLpNorm (F s) r' μ) 2 *
        eLpNorm (fun t ↦ eLpNorm (G t) r' μ) 2 := by
  set a := fun s ↦ eLpNorm (F s) r' μ
  set b := fun t ↦ eLpNorm (G t) r' μ
  have ha : AEMeasurable a := hF.aemeasurable_eLpNorm_Lp .rfl r'
  have hb : AEMeasurable b := hG.aemeasurable_eLpNorm_Lp .rfl r'
  -- On the window the separation `|s - t|` is at least `ρ`, so the pairing is at most
  -- `A ρ^{-γ} a(s) b(t)`.
  have hpt (t : ℝ) : ∀ s ∈ (fun s ↦ s - t) ⁻¹' W,
      ‖⟪((U s)†) (F s), ((U t)†) (G t)⟫_𝕜‖ₑ ≤ A * ENNReal.ofReal ρ ^ (-γ) * a s * b t :=
    fun s hs ↦ by
    have hsep : ρ ≤ |s - t| := hWρ _ hs
    have hst : s ≠ t := fun h ↦ by simp only [h, sub_self, abs_zero] at hsep; linarith
    calc _ ≤ A * ‖s - t‖ₑ ^ (-γ) * a s * b t := enorm_inner_adjoint_le hU hst _ _
      _ ≤ A * ENNReal.ofReal ρ ^ (-γ) * a s * b t := by
          gcongr A * ?_ * a s * b t
          refine ENNReal.rpow_le_rpow_of_nonpos ?_ (neg_nonpos.2 hγ)
          rw [Real.eNorm_eq_ofReal_abs]
          exact ENNReal.ofReal_le_ofReal hsep
  set c := A * ENNReal.ofReal ρ ^ (-γ)
  have hm : AEMeasurable fun t ↦ (∫⁻ s in (fun s ↦ s - t) ⁻¹' W, a s) * b t :=
    (measurable_setLIntegral_sub_preimage hW ha).aemeasurable.mul hb
  calc ∫⁻ t, ∫⁻ s in (fun s ↦ s - t) ⁻¹' W, ‖⟪((U s)†) (F s), ((U t)†) (G t)⟫_𝕜‖ₑ
      ≤ ∫⁻ t, ∫⁻ s in (fun s ↦ s - t) ⁻¹' W, c * a s * b t :=
        lintegral_mono fun t ↦ setLIntegral_mono' (measurable_sub_const t hW) (hpt t)
    _ = ∫⁻ t, c * ((∫⁻ s in (fun s ↦ s - t) ⁻¹' W, a s) * b t) := by
        refine lintegral_congr fun t ↦ ?_
        rw [lintegral_mul_const'' _ (ha.const_mul c).restrict,
          lintegral_const_mul'' _ ha.restrict, mul_assoc]
    _ = c * ∫⁻ t, (∫⁻ s in (fun s ↦ s - t) ⁻¹' W, a s) * b t := lintegral_const_mul'' _ hm
    _ ≤ c * (volume W * eLpNorm a 2 * eLpNorm b 2) := by
        gcongr
        exact lintegral_setLIntegral_sub_preimage_mul_le hW ha hb
    _ = A * ENNReal.ofReal ρ ^ (-γ) * volume W * eLpNorm a 2 * eLpNorm b 2 := by ring
  -- The chained `≤` is `Preorder.toLE` while the goal uses the `ℝ≥0∞` order instance directly;
  -- `calc` does not unfold instances to match them, so the last comparison is closed here.
  exact le_rfl

/-- **The decay corner of the localized `TT*` form.** Let `U(t) : H → L²(X, μ)` be bounded
operators whose time pairings decay from `L^{r'}` to `L^r`,
`‖U(s) U(t)* g‖_r ≤ A |s - t| ^ (-γ) ‖g‖_{r'}` for `s ≠ t`, with `γ ≥ 0`. Then for every `L` and
almost everywhere strongly measurable `F, G : ℝ → L²(X, μ)`, the pairings with time separation
`L < t - s ≤ 2L` satisfy

`∫∫_{t - 2L ≤ s < t - L} |⟪U(s)* F(s), U(t)* G(t)⟫| ≤ A L^{1-γ} ‖F‖_{L² L^{r'}} ‖G‖_{L² L^{r'}}`.

This is `TauCeti.lintegral_setLIntegral_sub_preimage_enorm_inner_adjoint_le` for the window
`[-2L, -L)`. -/
theorem lintegral_setLIntegral_enorm_inner_adjoint_le {U : ℝ → H →L[𝕜] Lp E 2 μ} {A : ℝ≥0∞}
    {γ L : ℝ} (hγ : 0 ≤ γ)
    (hU : ∀ s t, s ≠ t → ∀ g : Lp E 2 μ,
      eLpNorm (U s (((U t)†) g)) r μ ≤ A * ‖s - t‖ₑ ^ (-γ) * eLpNorm g r' μ)
    {F G : ℝ → Lp E 2 μ} (hF : AEStronglyMeasurable F) (hG : AEStronglyMeasurable G) :
    ∫⁻ t, ∫⁻ s in Ico (t - 2 * L) (t - L), ‖⟪((U s)†) (F s), ((U t)†) (G t)⟫_𝕜‖ₑ ≤
      A * ENNReal.ofReal L ^ (1 - γ) * eLpNorm (fun s ↦ eLpNorm (F s) r' μ) 2 *
        eLpNorm (fun t ↦ eLpNorm (G t) r' μ) 2 := by
  -- For `L ≤ 0` the windows are empty.
  rcases le_or_gt L 0 with hL | hL
  · have h (t : ℝ) : Ico (t - 2 * L) (t - L) = ∅ := Ico_eq_empty (by linarith)
    simp [h]
  simp only [Ico_sub_eq_preimage]
  refine (lintegral_setLIntegral_sub_preimage_enorm_inner_adjoint_le hγ hL hU measurableSet_Ico
    (fun w hw ↦ ?_) hF hG).trans_eq ?_
  · rw [abs_of_neg (by linarith [hw.2])]
    linarith [hw.2]
  · have hL0 : ENNReal.ofReal L ≠ 0 := ENNReal.ofReal_ne_zero_iff.2 hL
    rw [volume_Ico_neg, sub_eq_neg_add, ENNReal.rpow_add _ _ hL0 ENNReal.ofReal_ne_top,
      ENNReal.rpow_one]
    ring

variable [NormedSpace ℝ H]

/-- **The decay corner of `T_L`.** Under the hypotheses of
`TauCeti.lintegral_setLIntegral_enorm_inner_adjoint_le`, the localized retarded form

`T_L(F, G) = ∫ ⟪∫_{t - 2L ≤ s < t - L} U(s)* F(s) ds, U(t)* G(t)⟫ dt`

satisfies `|T_L(F, G)| ≤ A L^{1-γ} ‖F‖_{L² L^{r'}} ‖G‖_{L² L^{r'}}`. -/
theorem enorm_integral_inner_setIntegral_adjoint_le {U : ℝ → H →L[𝕜] Lp E 2 μ} {A : ℝ≥0∞}
    {γ L : ℝ} (hγ : 0 ≤ γ)
    (hU : ∀ s t, s ≠ t → ∀ g : Lp E 2 μ,
      eLpNorm (U s (((U t)†) g)) r μ ≤ A * ‖s - t‖ₑ ^ (-γ) * eLpNorm g r' μ)
    {F G : ℝ → Lp E 2 μ} (hF : AEStronglyMeasurable F) (hG : AEStronglyMeasurable G) :
    ‖∫ t, ⟪∫ s in Ico (t - 2 * L) (t - L), ((U s)†) (F s), ((U t)†) (G t)⟫_𝕜‖ₑ ≤
      A * ENNReal.ofReal L ^ (1 - γ) * eLpNorm (fun s ↦ eLpNorm (F s) r' μ) 2 *
        eLpNorm (fun t ↦ eLpNorm (G t) r' μ) 2 := by
  refine (eNorm_integral_le_lintegral_eNorm _).trans (le_trans (lintegral_mono fun t ↦ ?_)
    (lintegral_setLIntegral_enorm_inner_adjoint_le hγ hU hF hG))
  -- Move the inner integral out of the pairing; a non-integrable window integral is `0`.
  by_cases hi : IntegrableOn (fun s ↦ ((U s)†) (F s)) (Ico (t - 2 * L) (t - L))
  · rw [← integral_inner_left hi]
    exact eNorm_integral_le_lintegral_eNorm _
  · simp [integral_undef hi]

/-- The time exponents of the energy corner: for Hölder conjugate `p` and `q > 2`,
`1 / p = 1 - 1 / q` and `p ≤ 2`. -/
private theorem holderConjugate_inv_eq_and_le_two {p q : ℝ≥0} (hq : 2 < q)
    (hpq : p.HolderConjugate q) : (p : ℝ)⁻¹ = 1 - (q : ℝ)⁻¹ ∧ (p : ℝ≥0∞) ≤ 2 := by
  have h := hpq.coe.inv_add_inv_eq_one
  refine ⟨by linarith, ?_⟩
  have hp0 : (0 : ℝ) < p := hpq.coe.pos
  have hq2 : (q : ℝ)⁻¹ ≤ 2⁻¹ := inv_anti₀ (by norm_num) (by exact_mod_cast hq.le)
  have : (p : ℝ) ≤ 2 := (inv_le_inv₀ (by norm_num : (0 : ℝ) < 2) hp0).1 (by linarith)
  exact_mod_cast this

/-- **The dual estimate on a set of times.** If the dual estimate
`‖∫ U(s)* F(s) ds‖ ≤ K ‖F‖_{L^p L^r}` holds with a time exponent `p ≤ 2`, then restricting `F` to a
measurable set `S` of times and applying Hölder's inequality in time on `S` gives
`‖∫_S U(s)* F(s) ds‖ ≤ K |S|^{1/p - 1/2} ‖F‖_{L²(S; L^r)}`. -/
theorem enorm_setIntegral_adjoint_le_of_le_two {p a : ℝ≥0∞} (hp : p ≤ 2)
    {U : ℝ → H →L[𝕜] Lp E 2 μ} {K : ℝ≥0∞}
    (hK : ∀ F : ℝ → Lp E 2 μ, AEStronglyMeasurable F → Integrable (fun s ↦ ((U s)†) (F s)) →
      ‖∫ s, ((U s)†) (F s)‖ₑ ≤ K * eLpNorm (fun s ↦ eLpNorm (F s) a μ) p)
    {F : ℝ → Lp E 2 μ} (hF : AEStronglyMeasurable F) {S : Set ℝ} (hS : MeasurableSet S)
    (hUF : IntegrableOn (fun s ↦ ((U s)†) (F s)) S) :
    ‖∫ s in S, ((U s)†) (F s)‖ₑ ≤ K * volume S ^ (p.toReal⁻¹ - 2⁻¹) *
      (∫⁻ s in S, eLpNorm (F s) a μ ^ (2 : ℝ)) ^ (2⁻¹ : ℝ) := by
  set b := fun s ↦ eLpNorm (F s) a μ
  have hb : AEMeasurable b := hF.aemeasurable_eLpNorm_Lp .rfl a
  calc ‖∫ s in S, ((U s)†) (F s)‖ₑ
      ≤ K * eLpNorm (S.indicator b) p := enorm_setIntegral_adjoint_le hK hS hF.restrict hUF
    _ = K * eLpNorm b p (volume.restrict S) := by
        rw [eLpNorm_indicator_eq_eLpNorm_restrict hS.nullMeasurableSet]
    _ ≤ K * (eLpNorm b 2 (volume.restrict S) *
          volume S ^ (1 / p.toReal - 1 / (2 : ℝ≥0∞).toReal)) := by
        gcongr
        rw [← Measure.restrict_apply_univ]
        exact eLpNorm_le_eLpNorm_mul_rpow_measure_univ hp hb.restrict.aestronglyMeasurable
    _ = K * volume S ^ (p.toReal⁻¹ - 2⁻¹) * (∫⁻ s in S, b s ^ (2 : ℝ)) ^ (2⁻¹ : ℝ) := by
        rw [eLpNorm_eq_lintegral_rpow two_ne_zero ENNReal.ofNat_ne_top hb.restrict]
        simp only [ENNReal.toReal_ofNat, one_div]
        ring

omit [CompleteSpace E] in
/-- **Exchanging the order of integration** in a pairing localized to `s - t ∈ W`: for integrable
`f, g : ℝ → H`,

`∫ ⟪∫_{s - t ∈ W} f(s) ds, g(t)⟫ dt = ∫ ⟪f(s), ∫_{t - s ∈ -W} g(t) dt⟫ ds`. -/
private theorem integral_inner_setIntegral_sub_preimage_eq {f g : ℝ → H} (hf : Integrable f)
    (hg : Integrable g) {W : Set ℝ} (hW : MeasurableSet W) :
    ∫ t, ⟪∫ s in (fun s ↦ s - t) ⁻¹' W, f s, g t⟫_𝕜 =
      ∫ s, ⟪f s, ∫ t in (fun t ↦ t - s) ⁻¹' (-W), g t⟫_𝕜 := by
  set S := {z : ℝ × ℝ | z.2 - z.1 ∈ W}
  set Φ := S.indicator fun z : ℝ × ℝ ↦ ⟪f z.2, g z.1⟫_𝕜
  -- The integrand on the region `s - t ∈ W` is integrable on `ℝ × ℝ`.
  have hΦ : Integrable Φ (volume.prod volume) :=
    (hf.inner_fst_snd (𝕜 := 𝕜) hg).swap.indicator ((measurable_snd.sub measurable_fst) hW)
  -- Both windows describe the same region: `s - t ∈ W` exactly when `t - s ∈ -W`.
  have hmem (t s : ℝ) : (t, s) ∈ S ↔ s ∈ (fun s ↦ s - t) ⁻¹' W := by
    simp only [S, mem_ofPred_eq, mem_preimage]
  have hmem' (t s : ℝ) : (t, s) ∈ S ↔ t ∈ (fun t ↦ t - s) ⁻¹' (-W) := by
    simp only [S, mem_ofPred_eq, mem_preimage, mem_neg, neg_sub]
  calc ∫ t, ⟪∫ s in (fun s ↦ s - t) ⁻¹' W, f s, g t⟫_𝕜
      = ∫ t, ∫ s, Φ (t, s) := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun t ↦ ?_)
        dsimp only
        rw [← integral_inner_left hf.integrableOn, ← integral_indicator (measurable_sub_const t hW)]
        exact integral_congr_ae (Filter.Eventually.of_forall fun s ↦
          indicator_eq_indicator (hmem t s).symm rfl)
    _ = ∫ s, ∫ t, Φ (t, s) := integral_integral_swap hΦ
    _ = ∫ s, ⟪f s, ∫ t in (fun t ↦ t - s) ⁻¹' (-W), g t⟫_𝕜 := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun s ↦ ?_)
        dsimp only
        rw [← integral_inner hg.integrableOn, ← integral_indicator (measurable_sub_const s hW.neg)]
        exact integral_congr_ae (Filter.Eventually.of_forall fun t ↦
          indicator_eq_indicator (hmem' t s) rfl)

/-- **The energy bound on sliding windows.** Let `U(t) : H → L²(X, μ)` be bounded operators,
`‖U(t)‖ ≤ M`, satisfying a dual estimate with a time exponent `p ≤ 2`,
`‖∫ U(s)* F(s) ds‖ ≤ K ‖F‖_{L^p L^a}`. Then for every measurable window `W ⊆ ℝ` and almost
everywhere strongly measurable `F, G : ℝ → L²(X, μ)`,

`|∫ ⟪∫_{s - t ∈ W} U(s)* F(s) ds, U(t)* G(t)⟫ dt| ≤ M K |W|^{1/p} ‖F‖_{L² L^a} ‖G‖_{L² L²}`.

The dual estimate on each window `{s | s - t ∈ W}` and Hölder's inequality in time bound the
window integral by `K |W|^{1/p - 1/2}` times the `L²` norm of `‖F(s)‖_a` over the window, and the
square-function bound `MeasureTheory.lintegral_rpow_setLIntegral_sub_preimage_mul_le` sums these
over `t`. -/
theorem enorm_integral_inner_setIntegral_sub_preimage_adjoint_le {p a : ℝ≥0∞} (hp : p ≤ 2)
    {U : ℝ → H →L[𝕜] Lp E 2 μ} {M K : ℝ≥0∞} (hM : ∀ t, ‖U t‖ₑ ≤ M)
    (hK : ∀ F' : ℝ → Lp E 2 μ, AEStronglyMeasurable F' → Integrable (fun s ↦ ((U s)†) (F' s)) →
      ‖∫ s, ((U s)†) (F' s)‖ₑ ≤ K * eLpNorm (fun s ↦ eLpNorm (F' s) a μ) p)
    {W : Set ℝ} (hW : MeasurableSet W) {F G : ℝ → Lp E 2 μ} (hF : AEStronglyMeasurable F)
    (hG : AEStronglyMeasurable G) :
    ‖∫ t, ⟪∫ s in (fun s ↦ s - t) ⁻¹' W, ((U s)†) (F s), ((U t)†) (G t)⟫_𝕜‖ₑ ≤
      M * K * volume W ^ p.toReal⁻¹ * eLpNorm (fun s ↦ eLpNorm (F s) a μ) 2 *
        eLpNorm (fun t ↦ ‖G t‖ₑ) 2 := by
  set b := fun s ↦ eLpNorm (F s) a μ
  have hb : AEMeasurable b := hF.aemeasurable_eLpNorm_Lp .rfl a
  -- For `p = 0` the dual estimate forces every window integral to vanish.
  rcases eq_or_ne p 0 with rfl | hp0
  · have h0 (t : ℝ) : ∫ s in (fun s ↦ s - t) ⁻¹' W, ((U s)†) (F s) = 0 := by
      by_cases hi : IntegrableOn (fun s ↦ ((U s)†) (F s)) ((fun s ↦ s - t) ⁻¹' W)
      · have h := enorm_setIntegral_adjoint_le hK (measurable_sub_const t hW) hF.restrict hi
        rwa [eLpNorm_exponent_zero (hb.indicator (measurable_sub_const t hW)).aestronglyMeasurable,
          mul_zero, nonpos_iff_eq_zero, eNorm_eq_zero] at h
      · exact integral_undef hi
    simp [h0]
  have hGm : AEMeasurable fun t ↦ ‖G t‖ₑ := hG.eNorm
  -- The `L²` norms of `b` over the windows, and their measurability.
  set φ := fun t ↦ (∫⁻ s in (fun s ↦ s - t) ⁻¹' W, b s ^ (2 : ℝ)) ^ (2⁻¹ : ℝ)
  have hφ : Measurable φ :=
    (measurable_setLIntegral_sub_preimage hW (hb.pow_const _)).pow_const _
  set c := K * volume W ^ (p.toReal⁻¹ - 2⁻¹)
  -- On each window, the dual estimate and Hölder's inequality in time.
  have hwin (t : ℝ) : ‖∫ s in (fun s ↦ s - t) ⁻¹' W, ((U s)†) (F s)‖ₑ ≤ c * φ t := by
    by_cases hi : IntegrableOn (fun s ↦ ((U s)†) (F s)) ((fun s ↦ s - t) ⁻¹' W)
    · have h := enorm_setIntegral_adjoint_le_of_le_two hp hK hF (measurable_sub_const t hW) hi
      rwa [(measurePreserving_sub_right volume t).measure_preimage hW.nullMeasurableSet] at h
    · simp [integral_undef hi]
  have hp2 : (2⁻¹ : ℝ) ≤ p.toReal⁻¹ :=
    inv_anti₀ (ENNReal.toReal_pos hp0 (ne_top_of_le_ne_top ENNReal.ofNat_ne_top hp))
      (by simpa using ENNReal.toReal_mono ENNReal.ofNat_ne_top hp)
  refine (eNorm_integral_le_lintegral_eNorm _).trans ?_
  calc ∫⁻ t, ‖⟪∫ s in (fun s ↦ s - t) ⁻¹' W, ((U s)†) (F s), ((U t)†) (G t)⟫_𝕜‖ₑ
      ≤ ∫⁻ t, c * M * (φ t * ‖G t‖ₑ) := lintegral_mono fun t ↦ by
        calc _ ≤ ‖∫ s in (fun s ↦ s - t) ⁻¹' W, ((U s)†) (F s)‖ₑ * ‖((U t)†) (G t)‖ₑ :=
              eNorm_inner_le_eNorm _ _
          _ ≤ c * φ t * (M * ‖G t‖ₑ) := by
              gcongr
              · exact hwin t
              · refine (((U t)†).le_opENorm _).trans ?_
                rw [ContinuousLinearMap.adjoint.eNorm_map]
                gcongr
                exact hM t
          _ = c * M * (φ t * ‖G t‖ₑ) := by ring
    _ = c * M * ∫⁻ t, φ t * ‖G t‖ₑ := lintegral_const_mul'' _ (hφ.aemeasurable.mul hGm)
    _ ≤ c * M * (volume W ^ (2⁻¹ : ℝ) * eLpNorm b 2 * eLpNorm (fun t ↦ ‖G t‖ₑ) 2) := by
        gcongr
        exact lintegral_rpow_setLIntegral_sub_preimage_mul_le hW hb hGm
    _ = M * K * volume W ^ p.toReal⁻¹ * eLpNorm b 2 * eLpNorm (fun t ↦ ‖G t‖ₑ) 2 := by
        rw [show p.toReal⁻¹ = (p.toReal⁻¹ - 2⁻¹) + 2⁻¹ by ring,
          ENNReal.rpow_add_of_nonneg _ _ (sub_nonneg.2 hp2) (by norm_num)]
        ring
  -- The chained `≤` is `Preorder.toLE` while the goal uses the `ℝ≥0∞` order instance directly;
  -- `calc` does not unfold instances to match them, so the last comparison is closed here.
  exact le_rfl

/-- **The energy bound on sliding windows at a non-endpoint exponent.** Let `2 < q < ∞` with
Hölder conjugate `p`. There is `C` such that the following holds. Let `U(t) : H → L²(X, μ)` be
bounded operators with `‖U(t)‖ ≤ B` whose time pairings decay from `L^{r'}` to `L^r`,
`‖U(s) U(t)* g‖_r ≤ A |s - t| ^ (-2 / q) ‖g‖_{r'}` for `s ≠ t`. Then for every measurable window
`W ⊆ ℝ` and almost everywhere strongly measurable `F, G : ℝ → L²(X, μ)`,

`|∫ ⟪∫_{s - t ∈ W} U(s)* F(s) ds, U(t)* G(t)⟫ dt| ≤
  C A^{1/2} B |W|^{1 - 1/q} ‖F‖_{L² L^{r'}} ‖G‖_{L² L²}`.

The constant `C` is independent of the family `U`, of `A`, `B`, `W`, `F` and `G`. This is
`TauCeti.enorm_integral_inner_setIntegral_sub_preimage_adjoint_le` for the non-endpoint dual
estimate `TauCeti.exists_enorm_integral_adjoint_le`. -/
theorem exists_enorm_integral_inner_setIntegral_sub_preimage_adjoint_le {p q : ℝ≥0} (hq : 2 < q)
    (hpq : p.HolderConjugate q) :
    ∃ C : ℝ≥0, ∀ (U : ℝ → H →L[𝕜] Lp E 2 μ) (A B : ℝ≥0∞), (∀ t, ‖U t‖ₑ ≤ B) →
      (∀ s t, s ≠ t → ∀ g : Lp E 2 μ,
        eLpNorm (U s (((U t)†) g)) r μ ≤ A * ‖s - t‖ₑ ^ (-(2 / q : ℝ)) * eLpNorm g r' μ) →
      ∀ {W : Set ℝ}, MeasurableSet W → ∀ F G : ℝ → Lp E 2 μ, AEStronglyMeasurable F →
        AEStronglyMeasurable G →
        ‖∫ t, ⟪∫ s in (fun s ↦ s - t) ⁻¹' W, ((U s)†) (F s), ((U t)†) (G t)⟫_𝕜‖ₑ ≤
          C * A ^ (2⁻¹ : ℝ) * B * volume W ^ (1 - (q : ℝ)⁻¹) *
            eLpNorm (fun s ↦ eLpNorm (F s) r' μ) 2 * eLpNorm (fun t ↦ ‖G t‖ₑ) 2 := by
  obtain ⟨C, hC⟩ := exists_enorm_integral_adjoint_le (𝕜 := 𝕜) (H := H) (E := E) (μ := μ)
    (r := r) (r' := r') hq hpq
  obtain ⟨hpinv, hp2⟩ := holderConjugate_inv_eq_and_le_two hq hpq
  refine ⟨C, fun U A B hB hU W hW F G hF hG ↦ ?_⟩
  have h := enorm_integral_inner_setIntegral_sub_preimage_adjoint_le hp2 hB (hC U A hU) hW hF hG
  rw [ENNReal.coe_toReal, hpinv] at h
  refine h.trans_eq ?_
  ring

/-- **The energy corner of `T_L`.** Let `2 < q < ∞` with Hölder conjugate `p`. There is `C` such
that the following holds. Let `U(t) : H → L²(X, μ)` be bounded operators with `‖U(t)‖ ≤ B` whose
time pairings decay from `L^{r'}` to `L^r`, `‖U(s) U(t)* g‖_r ≤ A |s - t| ^ (-2 / q) ‖g‖_{r'}` for
`s ≠ t`. Then for every `L` and almost everywhere strongly measurable `F, G : ℝ → L²(X, μ)`,
the localized retarded form satisfies

`|∫ ⟪∫_{t - 2L ≤ s < t - L} U(s)* F(s) ds, U(t)* G(t)⟫ dt| ≤
  C A^{1/2} B L^{1 - 1/q} ‖F‖_{L² L^{r'}} ‖G‖_{L² L²}`.

The constant `C` is independent of the family `U`, of `A`, `B`, `L`, `F` and `G`. This is
`TauCeti.exists_enorm_integral_inner_setIntegral_sub_preimage_adjoint_le` for the window
`[-2L, -L)`. The bound with the roles of `F` and `G` exchanged is
`TauCeti.exists_enorm_integral_inner_setIntegral_adjoint_le'`. -/
theorem exists_enorm_integral_inner_setIntegral_adjoint_le {p q : ℝ≥0} (hq : 2 < q)
    (hpq : p.HolderConjugate q) :
    ∃ C : ℝ≥0, ∀ (U : ℝ → H →L[𝕜] Lp E 2 μ) (A B : ℝ≥0∞), (∀ t, ‖U t‖ₑ ≤ B) →
      (∀ s t, s ≠ t → ∀ g : Lp E 2 μ,
        eLpNorm (U s (((U t)†) g)) r μ ≤ A * ‖s - t‖ₑ ^ (-(2 / q : ℝ)) * eLpNorm g r' μ) →
      ∀ (L : ℝ) (F G : ℝ → Lp E 2 μ), AEStronglyMeasurable F → AEStronglyMeasurable G →
        ‖∫ t, ⟪∫ s in Ico (t - 2 * L) (t - L), ((U s)†) (F s), ((U t)†) (G t)⟫_𝕜‖ₑ ≤
          C * A ^ (2⁻¹ : ℝ) * B * ENNReal.ofReal L ^ (1 - (q : ℝ)⁻¹) *
            eLpNorm (fun s ↦ eLpNorm (F s) r' μ) 2 * eLpNorm (fun t ↦ ‖G t‖ₑ) 2 := by
  obtain ⟨C, hC⟩ := exists_enorm_integral_inner_setIntegral_sub_preimage_adjoint_le (𝕜 := 𝕜)
    (H := H) (E := E) (μ := μ) (r := r) (r' := r') hq hpq
  refine ⟨C, fun U A B hB hU L F G hF hG ↦ ?_⟩
  simp only [Ico_sub_eq_preimage, ← volume_Ico_neg]
  exact hC U A B hB hU measurableSet_Ico F G hF hG

/-- **The energy corner of `T_L` with the roles exchanged.** Under the hypotheses of
`TauCeti.exists_enorm_integral_inner_setIntegral_adjoint_le`, if both `s ↦ U(s)* F(s)` and
`t ↦ U(t)* G(t)` are integrable, the localized retarded form satisfies

`|∫ ⟪∫_{t - 2L ≤ s < t - L} U(s)* F(s) ds, U(t)* G(t)⟫ dt| ≤
  C A^{1/2} B L^{1 - 1/q} ‖F‖_{L² L²} ‖G‖_{L² L^{r'}}`.

Exchanging the order of integration and conjugating, this is
`TauCeti.exists_enorm_integral_inner_setIntegral_sub_preimage_adjoint_le` for the window
`(L, 2L]` with `F` and `G` exchanged. -/
theorem exists_enorm_integral_inner_setIntegral_adjoint_le' {p q : ℝ≥0} (hq : 2 < q)
    (hpq : p.HolderConjugate q) :
    ∃ C : ℝ≥0, ∀ (U : ℝ → H →L[𝕜] Lp E 2 μ) (A B : ℝ≥0∞), (∀ t, ‖U t‖ₑ ≤ B) →
      (∀ s t, s ≠ t → ∀ g : Lp E 2 μ,
        eLpNorm (U s (((U t)†) g)) r μ ≤ A * ‖s - t‖ₑ ^ (-(2 / q : ℝ)) * eLpNorm g r' μ) →
      ∀ (L : ℝ) (F G : ℝ → Lp E 2 μ), AEStronglyMeasurable F →
        Integrable (fun s ↦ ((U s)†) (F s)) → AEStronglyMeasurable G →
        Integrable (fun t ↦ ((U t)†) (G t)) →
        ‖∫ t, ⟪∫ s in Ico (t - 2 * L) (t - L), ((U s)†) (F s), ((U t)†) (G t)⟫_𝕜‖ₑ ≤
          C * A ^ (2⁻¹ : ℝ) * B * ENNReal.ofReal L ^ (1 - (q : ℝ)⁻¹) *
            eLpNorm (fun s ↦ ‖F s‖ₑ) 2 * eLpNorm (fun t ↦ eLpNorm (G t) r' μ) 2 := by
  obtain ⟨C, hC⟩ := exists_enorm_integral_inner_setIntegral_sub_preimage_adjoint_le (𝕜 := 𝕜)
    (H := H) (E := E) (μ := μ) (r := r) (r' := r') hq hpq
  refine ⟨C, fun U A B hB hU L F G hF hUF hG hUG ↦ ?_⟩
  simp only [Ico_sub_eq_preimage]
  rw [integral_inner_setIntegral_sub_preimage_eq hUF hUG measurableSet_Ico]
  set W := -Ico (-(2 * L)) (-L)
  have hW : volume W = ENNReal.ofReal L := by rw [Measure.measure_neg, volume_Ico_neg]
  -- Conjugating puts the window integral in the left slot of every pairing.
  have hconj : ∫ s, ⟪((U s)†) (F s), ∫ t in (fun t ↦ t - s) ⁻¹' W, ((U t)†) (G t)⟫_𝕜 =
      conj (∫ s, ⟪∫ t in (fun t ↦ t - s) ⁻¹' W, ((U t)†) (G t), ((U s)†) (F s)⟫_𝕜) := by
    rw [← integral_conj]
    simp only [inner_conj_symm]
  rw [hconj, RCLike.eNorm_conj]
  refine (hC U A B hB hU measurableSet_Ico.neg G F hG hF).trans_eq ?_
  rw [hW]
  ring

end TauCeti
