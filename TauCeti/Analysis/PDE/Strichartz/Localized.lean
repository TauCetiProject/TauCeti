/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Strichartz.TTStar
import TauCeti.Analysis.SpecialFunctions.Pow.NNReal
import TauCeti.MeasureTheory.Function.Lp.IntegralFunctional
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

## Main declarations

* `TauCeti.lintegral_setLIntegral_enorm_inner_adjoint_le`: the decay corner for the absolute
  values of the localized pairings.
* `TauCeti.enorm_integral_inner_setIntegral_adjoint_le`: the decay corner for `T_L`.
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
open scoped ENNReal NNReal InnerProductSpace InnerProduct

namespace TauCeti

variable {𝕜 X E H : Type*} [RCLike 𝕜] {mX : MeasurableSpace X} {μ : Measure X}
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
  [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]
  {r r' : ℝ≥0∞} [r'.HolderConjugate r]

/-- The window `[t - 2L, t - L)` is the translate by `t` of `[-2L, -L)`. -/
private theorem Ico_sub_eq_preimage (L t : ℝ) :
    Ico (t - 2 * L) (t - L) = (fun s ↦ s - t) ⁻¹' Ico (-(2 * L)) (-L) := by
  ext s
  simp only [mem_Ico, mem_preimage]
  constructor <;> rintro ⟨h₁, h₂⟩ <;> constructor <;> linarith

private theorem volume_Ico_neg (L : ℝ) : volume (Ico (-(2 * L)) (-L)) = ENNReal.ofReal L := by
  rw [Real.volume_Ico]
  congr 1
  ring

/-- **The decay corner of the localized `TT*` form.** Let `U(t) : H → L²(X, μ)` be bounded
operators whose time pairings decay from `L^{r'}` to `L^r`,
`‖U(s) U(t)* g‖_r ≤ A |s - t| ^ (-γ) ‖g‖_{r'}` for `s ≠ t`, with `γ ≥ 0`. Then for `L > 0` and
almost everywhere strongly measurable `F, G : ℝ → L²(X, μ)`, the pairings with time separation
`L < t - s ≤ 2L` satisfy

`∫∫_{t - 2L ≤ s < t - L} |⟪U(s)* F(s), U(t)* G(t)⟫| ≤ A L^{1-γ} ‖F‖_{L² L^{r'}} ‖G‖_{L² L^{r'}}`. -/
theorem lintegral_setLIntegral_enorm_inner_adjoint_le {U : ℝ → H →L[𝕜] Lp E 2 μ} {A : ℝ≥0∞}
    {γ L : ℝ} (hγ : 0 ≤ γ) (hL : 0 < L)
    (hU : ∀ s t, s ≠ t → ∀ g : Lp E 2 μ,
      eLpNorm (U s (((U t)†) g)) r μ ≤ A * ‖s - t‖ₑ ^ (-γ) * eLpNorm g r' μ)
    {F G : ℝ → Lp E 2 μ} (hF : AEStronglyMeasurable F) (hG : AEStronglyMeasurable G) :
    ∫⁻ t, ∫⁻ s in Ico (t - 2 * L) (t - L), ‖⟪((U s)†) (F s), ((U t)†) (G t)⟫_𝕜‖ₑ ≤
      A * ENNReal.ofReal L ^ (1 - γ) * eLpNorm (fun s ↦ eLpNorm (F s) r' μ) 2 *
        eLpNorm (fun t ↦ eLpNorm (G t) r' μ) 2 := by
  set a := fun s ↦ eLpNorm (F s) r' μ
  set b := fun t ↦ eLpNorm (G t) r' μ
  have ha : AEMeasurable a := hF.aemeasurable_eLpNorm_Lp .rfl r'
  have hb : AEMeasurable b := hG.aemeasurable_eLpNorm_Lp .rfl r'
  set W := Ico (-(2 * L)) (-L)
  -- On the window the separation `t - s` is at least `L`, so the pairing is at most
  -- `A L^{-γ} a(s) b(t)`.
  have hpt (t : ℝ) : ∀ s ∈ Ico (t - 2 * L) (t - L),
      ‖⟪((U s)†) (F s), ((U t)†) (G t)⟫_𝕜‖ₑ ≤ A * ENNReal.ofReal L ^ (-γ) * a s * b t :=
    fun s hs ↦ by
    have hst : s ≠ t := by linarith [hs.2]
    have hsep : ENNReal.ofReal L ≤ ‖s - t‖ₑ := by
      rw [Real.enorm_eq_ofReal_abs, abs_sub_comm, abs_of_pos (by linarith [hs.2])]
      exact ENNReal.ofReal_le_ofReal (by linarith [hs.2])
    calc _ ≤ A * ‖s - t‖ₑ ^ (-γ) * a s * b t := enorm_inner_adjoint_le hU hst _ _
      _ ≤ A * ENNReal.ofReal L ^ (-γ) * a s * b t := by
          gcongr A * ?_ * a s * b t
          exact ENNReal.rpow_le_rpow_of_nonpos hsep (neg_nonpos.2 hγ)
  set c := A * ENNReal.ofReal L ^ (-γ)
  have hm : AEMeasurable fun t ↦ (∫⁻ s in (fun s ↦ s - t) ⁻¹' W, a s) * b t :=
    (measurable_setLIntegral_sub_preimage measurableSet_Ico ha).aemeasurable.mul hb
  calc ∫⁻ t, ∫⁻ s in Ico (t - 2 * L) (t - L), ‖⟪((U s)†) (F s), ((U t)†) (G t)⟫_𝕜‖ₑ
      ≤ ∫⁻ t, ∫⁻ s in Ico (t - 2 * L) (t - L), c * a s * b t :=
        lintegral_mono fun t ↦ setLIntegral_mono' measurableSet_Ico (hpt t)
    _ = ∫⁻ t, c * ((∫⁻ s in (fun s ↦ s - t) ⁻¹' W, a s) * b t) := by
        refine lintegral_congr fun t ↦ ?_
        rw [Ico_sub_eq_preimage, lintegral_mul_const'' _ (ha.const_mul c).restrict,
          lintegral_const_mul'' _ ha.restrict, mul_assoc]
    _ = c * ∫⁻ t, (∫⁻ s in (fun s ↦ s - t) ⁻¹' W, a s) * b t := lintegral_const_mul'' _ hm
    _ ≤ c * (volume W * eLpNorm a 2 * eLpNorm b 2) := by
        gcongr
        exact lintegral_setLIntegral_sub_preimage_mul_le measurableSet_Ico ha hb
    _ = A * ENNReal.ofReal L ^ (1 - γ) * eLpNorm a 2 * eLpNorm b 2 := by
        have hL0 : ENNReal.ofReal L ≠ 0 := ENNReal.ofReal_ne_zero_iff.2 hL
        rw [volume_Ico_neg, sub_eq_neg_add, ENNReal.rpow_add _ _ hL0 ENNReal.ofReal_ne_top,
          ENNReal.rpow_one]
        ring
  exact le_rfl

variable [NormedSpace ℝ H]

/-- **The decay corner of `T_L`.** Under the hypotheses of
`TauCeti.lintegral_setLIntegral_enorm_inner_adjoint_le`, and if `s ↦ U(s)* F(s)` is integrable,
the localized retarded form

`T_L(F, G) = ∫ ⟪∫_{t - 2L ≤ s < t - L} U(s)* F(s) ds, U(t)* G(t)⟫ dt`

satisfies `|T_L(F, G)| ≤ A L^{1-γ} ‖F‖_{L² L^{r'}} ‖G‖_{L² L^{r'}}`. -/
theorem enorm_integral_inner_setIntegral_adjoint_le {U : ℝ → H →L[𝕜] Lp E 2 μ} {A : ℝ≥0∞}
    {γ L : ℝ} (hγ : 0 ≤ γ) (hL : 0 < L)
    (hU : ∀ s t, s ≠ t → ∀ g : Lp E 2 μ,
      eLpNorm (U s (((U t)†) g)) r μ ≤ A * ‖s - t‖ₑ ^ (-γ) * eLpNorm g r' μ)
    {F G : ℝ → Lp E 2 μ} (hF : AEStronglyMeasurable F) (hG : AEStronglyMeasurable G)
    (hUF : Integrable fun s ↦ ((U s)†) (F s)) :
    ‖∫ t, ⟪∫ s in Ico (t - 2 * L) (t - L), ((U s)†) (F s), ((U t)†) (G t)⟫_𝕜‖ₑ ≤
      A * ENNReal.ofReal L ^ (1 - γ) * eLpNorm (fun s ↦ eLpNorm (F s) r' μ) 2 *
        eLpNorm (fun t ↦ eLpNorm (G t) r' μ) 2 := by
  refine (enorm_integral_le_lintegral_enorm _).trans (le_trans (lintegral_mono fun t ↦ ?_)
    (lintegral_setLIntegral_enorm_inner_adjoint_le hγ hL hU hF hG))
  -- Move the inner integral out of the pairing.
  calc ‖⟪∫ s in Ico (t - 2 * L) (t - L), ((U s)†) (F s), ((U t)†) (G t)⟫_𝕜‖ₑ
      = ‖∫ s in Ico (t - 2 * L) (t - L), ⟪((U t)†) (G t), ((U s)†) (F s)⟫_𝕜‖ₑ := by
        rw [← ofReal_norm, norm_inner_symm, ofReal_norm, integral_inner hUF.integrableOn]
    _ ≤ ∫⁻ s in Ico (t - 2 * L) (t - L), ‖⟪((U t)†) (G t), ((U s)†) (F s)⟫_𝕜‖ₑ :=
        enorm_integral_le_lintegral_enorm _
    _ = ∫⁻ s in Ico (t - 2 * L) (t - L), ‖⟪((U s)†) (F s), ((U t)†) (G t)⟫_𝕜‖ₑ := by
        refine lintegral_congr fun s ↦ ?_
        rw [← ofReal_norm, norm_inner_symm, ofReal_norm]

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

/-- **The dual estimate on a set of times.** If the non-endpoint dual estimate
`‖∫ U(s)* F(s) ds‖ ≤ C A^{1/2} ‖F‖_{L^p L^{r'}}` holds with `1 / p = 1 - 1 / q`, `q > 2`, then
restricting `F` to a measurable set `S` of times and applying Hölder's inequality in time on `S`
gives `‖∫_S U(s)* F(s) ds‖ ≤ C A^{1/2} |S|^{1/2 - 1/q} ‖F‖_{L²(S; L^{r'})}`. -/
private theorem enorm_setIntegral_adjoint_le {p q : ℝ≥0} (hq : 2 < q)
    (hpq : p.HolderConjugate q) {U : ℝ → H →L[𝕜] Lp E 2 μ} {A : ℝ≥0∞} {C : ℝ≥0}
    (hC : ∀ F : ℝ → Lp E 2 μ, AEStronglyMeasurable F → Integrable (fun s ↦ ((U s)†) (F s)) →
      ‖∫ s, ((U s)†) (F s)‖ₑ ≤ C * A ^ (2⁻¹ : ℝ) * eLpNorm (fun s ↦ eLpNorm (F s) r' μ) p)
    {F : ℝ → Lp E 2 μ} (hF : AEStronglyMeasurable F) (hUF : Integrable fun s ↦ ((U s)†) (F s))
    {S : Set ℝ} (hS : MeasurableSet S) :
    ‖∫ s in S, ((U s)†) (F s)‖ₑ ≤ C * A ^ (2⁻¹ : ℝ) * volume S ^ (2⁻¹ - (q : ℝ)⁻¹) *
      (∫⁻ s in S, eLpNorm (F s) r' μ ^ (2 : ℝ)) ^ (2⁻¹ : ℝ) := by
  obtain ⟨hpinv, hp2⟩ := holderConjugate_inv_eq_and_le_two hq hpq
  set a := fun s ↦ eLpNorm (F s) r' μ
  have ha : AEMeasurable a := hF.aemeasurable_eLpNorm_Lp .rfl r'
  have hind : (fun s ↦ ((U s)†) (S.indicator F s)) = S.indicator fun s ↦ ((U s)†) (F s) := by
    ext s
    by_cases hs : s ∈ S <;> simp [hs]
  have hUFS : Integrable fun s ↦ ((U s)†) (S.indicator F s) := by
    rw [hind]
    exact hUF.indicator hS
  have hnorm : (fun s ↦ eLpNorm (S.indicator F s : Lp E 2 μ) r' μ) = S.indicator a := by
    ext s
    by_cases hs : s ∈ S
    · simp [hs, a]
    · simp only [hs, not_false_eq_true, indicator_of_notMem]
      exact (eLpNorm_congr_ae (Lp.coeFn_zero E 2 μ)).trans eLpNorm_zero
  calc ‖∫ s in S, ((U s)†) (F s)‖ₑ
      = ‖∫ s, ((U s)†) (S.indicator F s)‖ₑ := by rw [hind, integral_indicator hS]
    _ ≤ C * A ^ (2⁻¹ : ℝ) * eLpNorm (fun s ↦ eLpNorm (S.indicator F s : Lp E 2 μ) r' μ) p :=
        hC _ (hF.indicator hS) hUFS
    _ = C * A ^ (2⁻¹ : ℝ) * eLpNorm a p (volume.restrict S) := by
        rw [hnorm, eLpNorm_indicator_eq_eLpNorm_restrict hS.nullMeasurableSet]
    _ ≤ C * A ^ (2⁻¹ : ℝ) * (eLpNorm a 2 (volume.restrict S) *
          volume S ^ (1 / (p : ℝ≥0∞).toReal - 1 / (2 : ℝ≥0∞).toReal)) := by
        gcongr
        rw [← Measure.restrict_apply_univ]
        exact eLpNorm_le_eLpNorm_mul_rpow_measure_univ hp2 ha.restrict.aestronglyMeasurable
    _ = C * A ^ (2⁻¹ : ℝ) * volume S ^ (2⁻¹ - (q : ℝ)⁻¹) *
          (∫⁻ s in S, a s ^ (2 : ℝ)) ^ (2⁻¹ : ℝ) := by
        rw [eLpNorm_eq_lintegral_rpow_enorm_toReal two_ne_zero ENNReal.ofNat_ne_top
          ha.restrict.aestronglyMeasurable]
        simp only [enorm_eq_self, ENNReal.toReal_ofNat, ENNReal.coe_toReal, one_div, hpinv]
        rw [show (1 : ℝ) - (q : ℝ)⁻¹ - 2⁻¹ = 2⁻¹ - (q : ℝ)⁻¹ by ring]
        ring

omit [NormedSpace ℝ H] in
/-- `‖U(t)* g‖ ≤ B ‖g‖` when `‖U(t)‖ ≤ B`. -/
private theorem enorm_adjoint_apply_le {T : H →L[𝕜] Lp E 2 μ} {B : ℝ≥0∞} (hT : ‖T‖ₑ ≤ B)
    (g : Lp E 2 μ) : ‖(T†) g‖ₑ ≤ B * ‖g‖ₑ :=
  calc ‖(T†) g‖ₑ ≤ ‖T†‖ₑ * ‖g‖ₑ := (T†).le_opENorm _
    _ ≤ B * ‖g‖ₑ := by
        gcongr
        rw [enorm_eq_nnnorm, LinearIsometryEquiv.nnnorm_map, ← enorm_eq_nnnorm]
        exact hT

/-- **The energy corner of `T_L`.** Let `2 < q < ∞` with Hölder conjugate `p`. There is `C` such
that the following holds. Let `U(t) : H → L²(X, μ)` be bounded operators with `‖U(t)‖ ≤ B` whose
time pairings decay from `L^{r'}` to `L^r`, `‖U(s) U(t)* g‖_r ≤ A |s - t| ^ (-2 / q) ‖g‖_{r'}` for
`s ≠ t`. Then for `L > 0` and almost everywhere strongly measurable `F, G : ℝ → L²(X, μ)` with
`s ↦ U(s)* F(s)` integrable, the localized retarded form satisfies

`|∫ ⟪∫_{t - 2L ≤ s < t - L} U(s)* F(s) ds, U(t)* G(t)⟫ dt| ≤
  C A^{1/2} B L^{1 - 1/q} ‖F‖_{L² L^{r'}} ‖G‖_{L² L²}`.

The constant `C` depends only on `q`. The bound with the roles of `F` and `G` exchanged is
`TauCeti.exists_enorm_integral_inner_setIntegral_adjoint_le'`. -/
theorem exists_enorm_integral_inner_setIntegral_adjoint_le {p q : ℝ≥0} (hq : 2 < q)
    (hpq : p.HolderConjugate q) :
    ∃ C : ℝ≥0, ∀ (U : ℝ → H →L[𝕜] Lp E 2 μ) (A B : ℝ≥0∞), (∀ t, ‖U t‖ₑ ≤ B) →
      (∀ s t, s ≠ t → ∀ g : Lp E 2 μ,
        eLpNorm (U s (((U t)†) g)) r μ ≤ A * ‖s - t‖ₑ ^ (-(2 / q : ℝ)) * eLpNorm g r' μ) →
      ∀ {L : ℝ}, 0 < L → ∀ F G : ℝ → Lp E 2 μ, AEStronglyMeasurable F →
        Integrable (fun s ↦ ((U s)†) (F s)) → AEStronglyMeasurable G →
        ‖∫ t, ⟪∫ s in Ico (t - 2 * L) (t - L), ((U s)†) (F s), ((U t)†) (G t)⟫_𝕜‖ₑ ≤
          C * A ^ (2⁻¹ : ℝ) * B * ENNReal.ofReal L ^ (1 - (q : ℝ)⁻¹) *
            eLpNorm (fun s ↦ eLpNorm (F s) r' μ) 2 * eLpNorm (fun t ↦ ‖G t‖ₑ) 2 := by
  obtain ⟨C, hC⟩ := exists_enorm_integral_adjoint_le (𝕜 := 𝕜) (H := H) (E := E) (μ := μ)
    (r := r) (r' := r') hq hpq
  refine ⟨C, fun U A B hB hU L hL F G hF hUF hG ↦ ?_⟩
  set a := fun s ↦ eLpNorm (F s) r' μ
  have ha : AEMeasurable a := hF.aemeasurable_eLpNorm_Lp .rfl r'
  have hGm : AEMeasurable fun t ↦ ‖G t‖ₑ := hG.enorm
  -- The `L²` norms of `a` over the windows, and their measurability.
  set φ := fun t ↦ (∫⁻ s in Ico (t - 2 * L) (t - L), a s ^ (2 : ℝ)) ^ (2⁻¹ : ℝ)
  have hφeq : φ = fun t ↦
      (∫⁻ s in (fun s ↦ s - t) ⁻¹' Ico (-(2 * L)) (-L), a s ^ (2 : ℝ)) ^ (2⁻¹ : ℝ) := by
    ext t
    simp only [φ, Ico_sub_eq_preimage]
  have hφ : Measurable φ := by
    rw [hφeq]
    exact (measurable_setLIntegral_sub_preimage measurableSet_Ico (ha.pow_const _)).pow_const _
  set c := C * A ^ (2⁻¹ : ℝ) * ENNReal.ofReal L ^ (2⁻¹ - (q : ℝ)⁻¹)
  -- On each window, the non-endpoint dual estimate and Hölder's inequality in time.
  have hwin (t : ℝ) : ‖∫ s in Ico (t - 2 * L) (t - L), ((U s)†) (F s)‖ₑ ≤ c * φ t := by
    have h := enorm_setIntegral_adjoint_le hq hpq (hC U A hU) hF hUF (S := Ico (t - 2 * L) (t - L))
      measurableSet_Ico
    rwa [Ico_sub_eq_preimage, (measurePreserving_sub_right volume t).measure_preimage
      measurableSet_Ico.nullMeasurableSet, volume_Ico_neg,
      ← Ico_sub_eq_preimage] at h
  have hφG : ∫⁻ t, φ t * ‖G t‖ₑ ≤
      ENNReal.ofReal L ^ (2⁻¹ : ℝ) * eLpNorm a 2 * eLpNorm (fun t ↦ ‖G t‖ₑ) 2 := by
    rw [hφeq, ← volume_Ico_neg]
    exact lintegral_rpow_setLIntegral_sub_preimage_mul_le measurableSet_Ico ha hGm
  refine (enorm_integral_le_lintegral_enorm _).trans ?_
  calc ∫⁻ t, ‖⟪∫ s in Ico (t - 2 * L) (t - L), ((U s)†) (F s), ((U t)†) (G t)⟫_𝕜‖ₑ
      ≤ ∫⁻ t, c * B * (φ t * ‖G t‖ₑ) := lintegral_mono fun t ↦ by
        calc _ ≤ ‖∫ s in Ico (t - 2 * L) (t - L), ((U s)†) (F s)‖ₑ * ‖((U t)†) (G t)‖ₑ :=
              enorm_inner_le_enorm _ _
          _ ≤ c * φ t * (B * ‖G t‖ₑ) := by
              gcongr
              · exact hwin t
              · exact enorm_adjoint_apply_le (hB t) _
          _ = c * B * (φ t * ‖G t‖ₑ) := by ring
    _ = c * B * ∫⁻ t, φ t * ‖G t‖ₑ := lintegral_const_mul'' _ (hφ.aemeasurable.mul hGm)
    _ ≤ c * B * (ENNReal.ofReal L ^ (2⁻¹ : ℝ) * eLpNorm a 2 * eLpNorm (fun t ↦ ‖G t‖ₑ) 2) := by
        gcongr
    _ = C * A ^ (2⁻¹ : ℝ) * B * ENNReal.ofReal L ^ (1 - (q : ℝ)⁻¹) * eLpNorm a 2 *
          eLpNorm (fun t ↦ ‖G t‖ₑ) 2 := by
        have hL0 : ENNReal.ofReal L ≠ 0 := ENNReal.ofReal_ne_zero_iff.2 hL
        have hexp : (1 : ℝ) - (q : ℝ)⁻¹ = (2⁻¹ - (q : ℝ)⁻¹) + 2⁻¹ := by ring
        rw [hexp, ENNReal.rpow_add _ _ hL0 ENNReal.ofReal_ne_top]
        ring
  exact le_rfl

/-- **The energy corner of `T_L` with the roles exchanged.** Under the hypotheses of
`TauCeti.exists_enorm_integral_inner_setIntegral_adjoint_le`, if both `s ↦ U(s)* F(s)` and
`t ↦ U(t)* G(t)` are integrable, the localized retarded form satisfies

`|∫ ⟪∫_{t - 2L ≤ s < t - L} U(s)* F(s) ds, U(t)* G(t)⟫ dt| ≤
  C A^{1/2} B L^{1 - 1/q} ‖F‖_{L² L²} ‖G‖_{L² L^{r'}}`. -/
theorem exists_enorm_integral_inner_setIntegral_adjoint_le' {p q : ℝ≥0} (hq : 2 < q)
    (hpq : p.HolderConjugate q) :
    ∃ C : ℝ≥0, ∀ (U : ℝ → H →L[𝕜] Lp E 2 μ) (A B : ℝ≥0∞), (∀ t, ‖U t‖ₑ ≤ B) →
      (∀ s t, s ≠ t → ∀ g : Lp E 2 μ,
        eLpNorm (U s (((U t)†) g)) r μ ≤ A * ‖s - t‖ₑ ^ (-(2 / q : ℝ)) * eLpNorm g r' μ) →
      ∀ {L : ℝ}, 0 < L → ∀ F G : ℝ → Lp E 2 μ, AEStronglyMeasurable F →
        Integrable (fun s ↦ ((U s)†) (F s)) → AEStronglyMeasurable G →
        Integrable (fun t ↦ ((U t)†) (G t)) →
        ‖∫ t, ⟪∫ s in Ico (t - 2 * L) (t - L), ((U s)†) (F s), ((U t)†) (G t)⟫_𝕜‖ₑ ≤
          C * A ^ (2⁻¹ : ℝ) * B * ENNReal.ofReal L ^ (1 - (q : ℝ)⁻¹) *
            eLpNorm (fun s ↦ ‖F s‖ₑ) 2 * eLpNorm (fun t ↦ eLpNorm (G t) r' μ) 2 := by
  obtain ⟨C, hC⟩ := exists_enorm_integral_adjoint_le (𝕜 := 𝕜) (H := H) (E := E) (μ := μ)
    (r := r) (r' := r') hq hpq
  refine ⟨C, fun U A B hB hU L hL F G hF hUF hG hUG ↦ ?_⟩
  set f := fun s ↦ ((U s)†) (F s)
  set g := fun t ↦ ((U t)†) (G t)
  set b := fun t ↦ eLpNorm (G t) r' μ
  have hb : AEMeasurable b := hG.aemeasurable_eLpNorm_Lp .rfl r'
  have hFm : AEMeasurable fun s ↦ ‖F s‖ₑ := hF.enorm
  set W := Ioc L (2 * L)
  have hW : volume W = ENNReal.ofReal L := by
    rw [Real.volume_Ioc]
    congr 1
    ring
  -- `s` lies in the window `[t - 2L, t - L)` exactly when `t` lies in `(s + L, s + 2L]`.
  have hmem (s t : ℝ) : s ∈ Ico (t - 2 * L) (t - L) ↔ t ∈ (fun t ↦ t - s) ⁻¹' W := by
    simp only [mem_Ico, mem_preimage, mem_Ioc, W]
    constructor <;> rintro ⟨h₁, h₂⟩ <;> constructor <;> linarith
  -- The integrand on the region `L < t - s ≤ 2L` is integrable on `ℝ × ℝ`.
  set Φ := fun z : ℝ × ℝ ↦
    {z : ℝ × ℝ | z.2 ∈ Ico (z.1 - 2 * L) (z.1 - L)}.indicator (fun z ↦ ⟪f z.2, g z.1⟫_𝕜) z
  have hΦ : Integrable Φ (volume.prod volume) := by
    have hS : MeasurableSet {z : ℝ × ℝ | z.2 ∈ Ico (z.1 - 2 * L) (z.1 - L)} :=
      (measurableSet_le (by fun_prop) (by fun_prop)).inter
        (measurableSet_lt (by fun_prop) (by fun_prop))
    refine Integrable.indicator ?_ hS
    refine (hUG.norm.mul_prod hUF.norm).mono'
      (hUF.aestronglyMeasurable.comp_snd.inner hUG.aestronglyMeasurable.comp_fst)
      (Filter.Eventually.of_forall fun z ↦ ?_)
    simp only [f, g]
    rw [mul_comm]
    exact norm_inner_le_norm _ _
  -- Exchange the order of integration.
  have hswap : ∫ t, ⟪∫ s in Ico (t - 2 * L) (t - L), f s, g t⟫_𝕜 =
      ∫ s, ⟪f s, ∫ t in (fun t ↦ t - s) ⁻¹' W, g t⟫_𝕜 := by
    calc ∫ t, ⟪∫ s in Ico (t - 2 * L) (t - L), f s, g t⟫_𝕜
        = ∫ t, ∫ s, Φ (t, s) := by
          refine integral_congr_ae (Filter.Eventually.of_forall fun t ↦ ?_)
          simp only [Φ]
          rw [← inner_conj_symm, ← integral_inner hUF.integrableOn, ← integral_conj,
            ← integral_indicator measurableSet_Ico]
          congr 1
          ext s
          by_cases hs : s ∈ Ico (t - 2 * L) (t - L)
          · rw [indicator_of_mem hs, inner_conj_symm, indicator_of_mem
              (show (t, s) ∈ {z : ℝ × ℝ | z.2 ∈ Ico (z.1 - 2 * L) (z.1 - L)} from hs)]
          · rw [indicator_of_notMem hs, indicator_of_notMem
              (show (t, s) ∉ {z : ℝ × ℝ | z.2 ∈ Ico (z.1 - 2 * L) (z.1 - L)} from hs)]
      _ = ∫ s, ∫ t, Φ (t, s) := integral_integral_swap hΦ
      _ = ∫ s, ⟪f s, ∫ t in (fun t ↦ t - s) ⁻¹' W, g t⟫_𝕜 := by
          refine integral_congr_ae (Filter.Eventually.of_forall fun s ↦ ?_)
          simp only [Φ]
          rw [← integral_inner hUG.integrableOn,
            ← integral_indicator ((measurable_sub_const s) measurableSet_Ioc)]
          congr 1
          ext t
          by_cases ht : t ∈ (fun t ↦ t - s) ⁻¹' W
          · rw [indicator_of_mem ht, indicator_of_mem
              (show (t, s) ∈ {z : ℝ × ℝ | z.2 ∈ Ico (z.1 - 2 * L) (z.1 - L)} from (hmem s t).2 ht)]
          · rw [indicator_of_notMem ht, indicator_of_notMem
              (show (t, s) ∉ {z : ℝ × ℝ | z.2 ∈ Ico (z.1 - 2 * L) (z.1 - L)} from
                fun h ↦ ht ((hmem s t).1 h))]
  set ψ := fun s ↦ (∫⁻ t in (fun t ↦ t - s) ⁻¹' W, b t ^ (2 : ℝ)) ^ (2⁻¹ : ℝ)
  have hψ : Measurable ψ :=
    (measurable_setLIntegral_sub_preimage measurableSet_Ioc (hb.pow_const _)).pow_const _
  set c := C * A ^ (2⁻¹ : ℝ) * ENNReal.ofReal L ^ (2⁻¹ - (q : ℝ)⁻¹)
  have hwin (s : ℝ) : ‖∫ t in (fun t ↦ t - s) ⁻¹' W, g t‖ₑ ≤ c * ψ s := by
    have h := enorm_setIntegral_adjoint_le hq hpq (hC U A hU) hG hUG
      (S := (fun t ↦ t - s) ⁻¹' W) ((measurable_sub_const s) measurableSet_Ioc)
    rwa [(measurePreserving_sub_right volume s).measure_preimage
      measurableSet_Ioc.nullMeasurableSet, hW] at h
  have hψF : ∫⁻ s, ψ s * ‖F s‖ₑ ≤
      ENNReal.ofReal L ^ (2⁻¹ : ℝ) * eLpNorm b 2 * eLpNorm (fun s ↦ ‖F s‖ₑ) 2 := by
    rw [← hW]
    exact lintegral_rpow_setLIntegral_sub_preimage_mul_le measurableSet_Ioc hb hFm
  rw [hswap]
  refine (enorm_integral_le_lintegral_enorm _).trans ?_
  calc ∫⁻ s, ‖⟪f s, ∫ t in (fun t ↦ t - s) ⁻¹' W, g t⟫_𝕜‖ₑ
      ≤ ∫⁻ s, c * B * (ψ s * ‖F s‖ₑ) := lintegral_mono fun s ↦ by
        calc _ ≤ ‖f s‖ₑ * ‖∫ t in (fun t ↦ t - s) ⁻¹' W, g t‖ₑ := enorm_inner_le_enorm _ _
          _ ≤ B * ‖F s‖ₑ * (c * ψ s) := by
              gcongr
              · exact enorm_adjoint_apply_le (hB s) _
              · exact hwin s
          _ = c * B * (ψ s * ‖F s‖ₑ) := by ring
    _ = c * B * ∫⁻ s, ψ s * ‖F s‖ₑ := lintegral_const_mul'' _ (hψ.aemeasurable.mul hFm)
    _ ≤ c * B * (ENNReal.ofReal L ^ (2⁻¹ : ℝ) * eLpNorm b 2 * eLpNorm (fun s ↦ ‖F s‖ₑ) 2) := by
        gcongr
    _ = C * A ^ (2⁻¹ : ℝ) * B * ENNReal.ofReal L ^ (1 - (q : ℝ)⁻¹) *
          eLpNorm (fun s ↦ ‖F s‖ₑ) 2 * eLpNorm b 2 := by
        have hL0 : ENNReal.ofReal L ≠ 0 := ENNReal.ofReal_ne_zero_iff.2 hL
        have hexp : (1 : ℝ) - (q : ℝ)⁻¹ = (2⁻¹ - (q : ℝ)⁻¹) + 2⁻¹ := by ring
        rw [hexp, ENNReal.rpow_add _ _ hL0 ENNReal.ofReal_ne_top]
        ring
  exact le_rfl

end TauCeti
