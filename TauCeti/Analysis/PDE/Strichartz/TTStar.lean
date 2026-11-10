/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import TauCeti.MeasureTheory.Function.Lp.Duality
import TauCeti.MeasureTheory.Integral.RieszPotential
import TauCeti.MeasureTheory.Integral.RieszThorin

/-!
# The `TT*` argument for Strichartz estimates

Let `H` be a complex Hilbert space, `(X, μ)` a measure space, and `U(t) : H → L²(X)`, `t ∈ ℝ`, a
family of operators with the **energy bound** `‖U(t)‖ ≤ M` and the **dispersive bound**

`‖U(s) U(t)* g‖_∞ ≤ D |s - t|^(-σ) ‖g‖₁`  for `s ≠ t`.

This is the abstract setting of Keel and Tao: for the Schrödinger propagator on `ℝⁿ` one takes
`U(t) = exp(itΔ)`, so that `U(s) U(t)* = exp(i(s - t)Δ)` and `σ = n / 2`. A pair of exponents
`2 ≤ q, r ≤ ∞` is `σ`-admissible when `1/q + σ/r = σ/2`. This file proves, for the non-endpoint
`σ`-admissible pairs with `2 < q < ∞`, the two estimates on which the Strichartz estimates rest.

* **The bilinear estimate** (`TauCeti.exists_lintegral_lintegral_enorm_inner_adjoint_apply_le`):
  for `F, G : ℝ → L²(X)` with values in `L^{r'}`,

  `∫∫ |⟪U(s)* F(s), U(t)* G(t)⟫| ds dt ≤ C K ‖F‖_{L^{q'}_t L^{r'}_x} ‖G‖_{L^{q'}_t L^{r'}_x}`,

  where `K = D^(1 - 2/r) M^(4/r)` and `C` depends only on `q`.
* **The dual homogeneous estimate** (`TauCeti.exists_enorm_integral_adjoint_apply_le`):

  `‖∫ U(t)* G(t) dt‖_H ≤ C K^(1/2) ‖G‖_{L^{q'}_t L^{r'}_x}`.

By duality the second estimate is equivalent to the homogeneous Strichartz estimate
`‖U(t) f‖_{L^q_t L^r_x} ≤ C K^(1/2) ‖f‖_H`. Since the bilinear estimate bounds the absolute
values of the pairings, it also bounds the restriction of the double integral to any region of
the `(s, t)`-plane, such as the retarded region `s < t` of the inhomogeneous estimates.

## The argument

Interpolating the dispersive bound with the energy bound `‖U(s) U(t)*‖ ≤ M²` by the
Riesz–Thorin theorem (`ContinuousLinearMap.eLpNorm_apply_le_rpow_mul_rpow_mul_eLpNorm`) gives

`‖U(s) U(t)* g‖_r ≤ K |s - t|^(-2/q) ‖g‖_{r'}`,

since admissibility says exactly `σ (1 - 2/r) = 2/q`. With Hölder's inequality in `x` this bounds
`|⟪U(s)* F(s), U(t)* G(t)⟫ | = |⟪F(s), U(s) U(t)* G(t)⟫|` by
`K |s - t|^(-2/q) ‖F(s)‖_{r'} ‖G(t)‖_{r'}`. Integrating in `s` and `t` leaves the pairing of
`‖F(·)‖_{r'}` with the one-dimensional Riesz potential of order `1 - 2/q` of `‖G(·)‖_{r'}`, which
the Hardy–Littlewood–Sobolev inequality in its bilinear form
(`TauCeti.exists_lintegral_mul_rieszPotential_le`) bounds by `‖F‖_{L^{q'}L^{r'}}` times
`‖G‖_{L^{q'}L^{r'}}`; this is where `2 < q < ∞` is needed. The dual estimate follows from the
bilinear one by expanding `‖∫ U(t)* G(t) dt‖²` as a double integral of pairings.

## Main declarations

* `TauCeti.enorm_inner_adjoint_apply_adjoint_apply_le`: the pairing bound for one pair of times.
* `TauCeti.exists_lintegral_mul_lintegral_enorm_sub_rpow_mul_le`: fractional integration in time.
* `TauCeti.exists_lintegral_lintegral_enorm_inner_adjoint_apply_le`: the bilinear estimate.
* `TauCeti.exists_enorm_integral_adjoint_apply_le`: the dual homogeneous estimate.

## References

* M. Keel and T. Tao, *Endpoint Strichartz estimates*, Amer. J. Math. **120** (1998), 955–980,
  Theorem 1.2 and Section 3 (the non-endpoint case).
* T. Tao, *Nonlinear Dispersive Equations: Local and Global Analysis*, CBMS Regional Conference
  Series in Mathematics 106, AMS, 2006, Section 2.3.
-/

public section

noncomputable section

open MeasureTheory Filter
open scoped ENNReal NNReal InnerProductSpace

namespace TauCeti

variable {X : Type*} {mX : MeasurableSpace X} {μ : Measure X}
  {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- **The `TT*` pairing bound for one pair of times.** Let `V, W : H → L²(X)` have norms at most
`M`, and suppose that `‖V W* g‖_∞ ≤ D ‖g‖₁` for every integrable `g ∈ L²`. For Hölder conjugate
exponents `r, r'` with `2 ≤ r`,

`|⟪V* f, W* g⟫| ≤ D^(1 - 2/r) M^(4/r) ‖f‖_{r'} ‖g‖_{r'}`

for every `f ∈ L²` and every `g ∈ L² ∩ L^{r'}`. -/
theorem enorm_inner_adjoint_apply_adjoint_apply_le {V W : H →L[ℂ] Lp ℂ 2 μ} {M D : ℝ≥0}
    (hV : ‖V‖ ≤ M) (hW : ‖W‖ ≤ M)
    (hD : ∀ g : Lp ℂ 2 μ, Integrable g μ →
      eLpNorm (V (ContinuousLinearMap.adjoint W g)) ∞ μ ≤ D * eLpNorm g 1 μ)
    {r r' : ℝ≥0∞} [r.HolderConjugate r'] (hr : 2 ≤ r) (f g : Lp ℂ 2 μ) (hg : MemLp g r' μ) :
    ‖⟪ContinuousLinearMap.adjoint V f, ContinuousLinearMap.adjoint W g⟫_ℂ‖ₑ ≤
      ↑(D ^ (1 - 2 * r⁻¹.toReal) * M ^ (4 * r⁻¹.toReal)) * eLpNorm f r' μ *
        eLpNorm g r' μ := by
  set T := V.comp (ContinuousLinearMap.adjoint W)
  have hT : ‖T‖ ≤ ↑(M ^ 2) := by
    calc ‖T‖ ≤ ‖V‖ * ‖ContinuousLinearMap.adjoint W‖ := V.opNorm_comp_le _
      _ ≤ M * M := by
          rw [LinearIsometryEquiv.norm_map]
          gcongr
      _ = ↑(M ^ 2) := by push_cast; ring
  have hRT := T.eLpNorm_apply_le_rpow_mul_rpow_mul_eLpNorm (M₀ := D) (M₁ := M ^ 2) hD hT hr g hg
  have hM : (M ^ 2) ^ (2 * r⁻¹.toReal) = M ^ (4 * r⁻¹.toReal) := by
    rw [← NNReal.rpow_natCast, ← NNReal.rpow_mul]
    congr 1
    push_cast
    ring
  rw [hM] at hRT
  rw [ContinuousLinearMap.adjoint_inner_left, MeasureTheory.L2.inner_def]
  calc ‖∫ x, ⟪f x, V (ContinuousLinearMap.adjoint W g) x⟫_ℂ ∂μ‖ₑ
      ≤ eLpNorm f r' μ * eLpNorm (V (ContinuousLinearMap.adjoint W g)) r μ :=
        enorm_integral_inner_le
    _ ≤ eLpNorm f r' μ * (↑(D ^ (1 - 2 * r⁻¹.toReal) * M ^ (4 * r⁻¹.toReal)) *
          eLpNorm g r' μ) := by
        gcongr
        exact hRT
    _ = _ := by ring

/-- **Fractional integration in time.** Let `2 < q < ∞` with Hölder conjugate `q'`. There is a
constant `C`, depending only on `q`, such that

`∫ a(s) ∫ |s - t|^(-2/q) b(t) dt ds ≤ C ‖a‖_{q'} ‖b‖_{q'}`

for all `a, b : ℝ → ℝ≥0∞`. This is the bilinear Hardy–Littlewood–Sobolev inequality on `ℝ` for
the Riesz potential of order `1 - 2/q`, which maps `L^{q'}` to `L^q`. -/
theorem exists_lintegral_mul_lintegral_enorm_sub_rpow_mul_le {q q' : ℝ≥0∞}
    [q.HolderConjugate q'] (hq : 2 < q) (hq_top : q ≠ ∞) :
    ∃ C : ℝ≥0, ∀ a b : ℝ → ℝ≥0∞,
      ∫⁻ s, a s * ∫⁻ t, ‖s - t‖ₑ ^ (-(2 * q⁻¹.toReal)) * b t ≤
        C * eLpNorm a q' * eLpNorm b q' := by
  set c := q⁻¹.toReal
  have hq0 : q ≠ 0 := (two_pos.trans hq).ne'
  have hc0 : 0 < c := ENNReal.toReal_pos (ENNReal.inv_ne_zero.2 hq_top) (ENNReal.inv_ne_top.2 hq0)
  have hc2 : c < 2⁻¹ := by
    have := ENNReal.toReal_strict_mono (by simp) (ENNReal.inv_lt_inv.2 hq)
    simpa [c, ENNReal.toReal_inv] using this
  -- The exponents of the Hardy–Littlewood–Sobolev inequality of order `1 - 2c` from `L^{q'}` to
  -- `L^q`: `1/q = 1/q' - (1 - 2c)` since `1/q' = 1 - c`.
  have hq'_top : q' ≠ ∞ :=
    (ENNReal.HolderConjugate.ne_top_iff_ne_one q' q).2 (ENNReal.one_lt_two.trans hq).ne'
  have hp : 1 < q'.toNNReal := by
    rw [← ENNReal.coe_lt_coe, ENNReal.coe_toNNReal hq'_top]
    exact_mod_cast (ENNReal.HolderConjugate.lt_top_iff_one_lt q q').1 hq_top.lt_top
  have hpq : (q.toNNReal : ℝ)⁻¹ = (q'.toNNReal : ℝ)⁻¹ - (1 - 2 * c) / Module.finrank ℝ ℝ := by
    rw [ENNReal.coe_toNNReal_eq_toReal, ENNReal.coe_toNNReal_eq_toReal, ← ENNReal.toReal_inv,
      ← ENNReal.toReal_inv, ← ENNReal.HolderConjugate.one_sub_inv q q', ENNReal.toReal_sub_of_le
      (ENNReal.inv_le_one.2 (one_le_two.trans hq.le)) ENNReal.one_ne_top, ENNReal.toReal_one,
      Module.finrank_self, Nat.cast_one, div_one]
    ring
  have : ((q.toNNReal : ℝ≥0) : ℝ≥0∞).HolderConjugate q' := by
    rw [ENNReal.coe_toNNReal hq_top]
    infer_instance
  obtain ⟨C, hC⟩ := exists_lintegral_mul_rieszPotential_le (F := ℝ≥0∞) (volume : Measure ℝ)
    (α := 1 - 2 * c) (q' := q') (by linarith) hp hpq
  refine ⟨C, fun a b => ?_⟩
  -- The inner integral is the Riesz potential of `b` of order `1 - 2c`.
  have hI (s : ℝ) :
      ∫⁻ t, ‖s - t‖ₑ ^ (-(2 * c)) * b t = rieszPotential volume (1 - 2 * c) b s := by
    have hexp : 1 - 2 * c - (Module.finrank ℝ ℝ : ℝ) = -(2 * c) := by
      rw [Module.finrank_self, Nat.cast_one]
      ring
    rw [rieszPotential_def, hexp]
    simp only [enorm_eq_self]
  calc ∫⁻ s, a s * ∫⁻ t, ‖s - t‖ₑ ^ (-(2 * c)) * b t
      = ∫⁻ s, a s * rieszPotential volume (1 - 2 * c) b s := by simp_rw [hI]
    _ ≤ _ := by
        -- `hC` is stated with the measurable space `Real.measurableSpace` and the goal with
        -- `MeasureSpace.toMeasurableSpace`; `convert` matches these instances argument by argument.
        convert hC b a using 2
        rw [ENNReal.coe_toNNReal hq'_top]

/-- **The bilinear `TT*` estimate, non-endpoint case.** Let `2 < q < ∞` and `2 ≤ r ≤ ∞` be
`σ`-admissible, `1/q + σ/r = σ/2`, with Hölder conjugates `q'` and `r'`. There is a constant `C`,
depending only on `q`, with the following property. Let `U(t) : H → L²(X)` satisfy the energy
bound `‖U(t)‖ ≤ M` and the dispersive bound `‖U(s) U(t)* g‖_∞ ≤ D |s - t|^(-σ) ‖g‖₁` for `s ≠ t`
and integrable `g ∈ L²`. Then for all `F, G : ℝ → L²(X)` with values almost everywhere in
`L^{r'}`,

`∫∫ |⟪U(s)* F(s), U(t)* G(t)⟫| ds dt ≤ C D^(1 - 2/r) M^(4/r) ‖F‖_{L^{q'}L^{r'}} ‖G‖_{L^{q'}L^{r'}}`,

where `‖F‖_{L^{q'}L^{r'}}` is the `L^{q'}` norm of `s ↦ ‖F(s)‖_{r'}`. -/
theorem exists_lintegral_lintegral_enorm_inner_adjoint_apply_le {σ : ℝ} {q q' r r' : ℝ≥0∞}
    [q.HolderConjugate q'] [r.HolderConjugate r'] (hq : 2 < q) (hq_top : q ≠ ∞) (hr : 2 ≤ r)
    (hσ : q⁻¹.toReal + σ * r⁻¹.toReal = σ / 2) :
    ∃ C : ℝ≥0, ∀ {M D : ℝ≥0} {U : ℝ → H →L[ℂ] Lp ℂ 2 μ}, (∀ t, ‖U t‖ ≤ M) →
      (∀ s t, s ≠ t → ∀ g : Lp ℂ 2 μ, Integrable g μ →
        eLpNorm (U s (ContinuousLinearMap.adjoint (U t) g)) ∞ μ ≤
          D * ‖s - t‖ₑ ^ (-σ) * eLpNorm g 1 μ) →
      ∀ {F G : ℝ → Lp ℂ 2 μ}, (∀ᵐ s, MemLp (F s) r' μ) → (∀ᵐ t, MemLp (G t) r' μ) →
        ∫⁻ s, ∫⁻ t, ‖⟪ContinuousLinearMap.adjoint (U s) (F s),
            ContinuousLinearMap.adjoint (U t) (G t)⟫_ℂ‖ₑ ≤
          C * ↑(D ^ (1 - 2 * r⁻¹.toReal) * M ^ (4 * r⁻¹.toReal)) *
            eLpNorm (fun s ↦ eLpNorm (F s) r' μ) q' * eLpNorm (fun t ↦ eLpNorm (G t) r' μ) q' := by
  -- Admissibility says that the decay rate in time is `σ (1 - 2/r) = 2/q`.
  set c := q⁻¹.toReal
  have hγ : σ * (1 - 2 * r⁻¹.toReal) = 2 * c := by
    have : σ * (1 - 2 * r⁻¹.toReal) = σ - 2 * (σ * r⁻¹.toReal) := by ring
    linarith
  obtain ⟨C, hC⟩ := exists_lintegral_mul_lintegral_enorm_sub_rpow_mul_le (q' := q') hq hq_top
  refine ⟨C, fun {M D U} hU hdecay {F G} hF hG => ?_⟩
  set K : ℝ≥0 := D ^ (1 - 2 * r⁻¹.toReal) * M ^ (4 * r⁻¹.toReal)
  set A : ℝ → ℝ≥0∞ := fun s ↦ eLpNorm (F s) r' μ
  set B : ℝ → ℝ≥0∞ := fun t ↦ eLpNorm (G t) r' μ
  -- The pairing bound at two distinct times, with the decay `|s - t|^(-2/q)` made explicit.
  have hpt (s t : ℝ) (hst : s ≠ t) (hGt : MemLp (G t) r' μ) :
      ‖⟪ContinuousLinearMap.adjoint (U s) (F s), ContinuousLinearMap.adjoint (U t) (G t)⟫_ℂ‖ₑ ≤
        K * (A s * (‖s - t‖ₑ ^ (-(2 * c)) * B t)) := by
    have hst' : ‖s - t‖₊ ≠ 0 := by simpa [sub_eq_zero] using hst
    have h := enorm_inner_adjoint_apply_adjoint_apply_le (hU s) (hU t)
      (D := D * ‖s - t‖₊ ^ (-σ)) (fun g hg => ?_) hr (F s) (G t) hGt
    · have hK : (D * ‖s - t‖₊ ^ (-σ)) ^ (1 - 2 * r⁻¹.toReal) * M ^ (4 * r⁻¹.toReal) =
          K * ‖s - t‖₊ ^ (-(2 * c)) := by
        rw [NNReal.mul_rpow, ← NNReal.rpow_mul, neg_mul, hγ]
        ring
      rw [hK, ENNReal.coe_mul, ENNReal.coe_rpow_of_ne_zero hst', ← enorm_eq_nnnorm] at h
      exact h.trans_eq (by ring)
    · rw [ENNReal.coe_mul, ENNReal.coe_rpow_of_ne_zero hst', ← enorm_eq_nnnorm]
      exact hdecay s t hst g hg
  calc ∫⁻ s, ∫⁻ t, ‖⟪ContinuousLinearMap.adjoint (U s) (F s),
          ContinuousLinearMap.adjoint (U t) (G t)⟫_ℂ‖ₑ
      ≤ ∫⁻ s, ∫⁻ t, K * (A s * (‖s - t‖ₑ ^ (-(2 * c)) * B t)) := by
        refine lintegral_mono fun s => lintegral_mono_ae ?_
        filter_upwards [Measure.ae_ne volume s, hG] with t hts hGt
        exact hpt s t hts.symm hGt
    _ = ∫⁻ s, K * (A s * ∫⁻ t, ‖s - t‖ₑ ^ (-(2 * c)) * B t) := by
        refine lintegral_congr_ae ?_
        filter_upwards [hF] with s hFs
        rw [lintegral_const_mul' _ _ ENNReal.coe_ne_top,
          lintegral_const_mul' _ _ hFs.eLpNorm_ne_top]
    _ = K * ∫⁻ s, A s * ∫⁻ t, ‖s - t‖ₑ ^ (-(2 * c)) * B t :=
        lintegral_const_mul' _ _ ENNReal.coe_ne_top
    _ ≤ K * (C * eLpNorm A q' * eLpNorm B q') := by
        gcongr
        exact hC A B
    _ = _ := by ring

/-- **The dual homogeneous `TT*` estimate, non-endpoint case.** In the setting of
`TauCeti.exists_lintegral_lintegral_enorm_inner_adjoint_apply_le`, there is a constant `C`,
depending only on `q`, such that

`‖∫ U(t)* G(t) dt‖ ≤ C D^(1/2 - 1/r) M^(2/r) ‖G‖_{L^{q'}L^{r'}}`

for every `G : ℝ → L²(X)` with values almost everywhere in `L^{r'}`. The integral is the Bochner
integral, which is `0` unless `t ↦ U(t)* G(t)` is integrable. By duality this estimate is
equivalent to the homogeneous Strichartz estimate for `U`. -/
theorem exists_enorm_integral_adjoint_apply_le {σ : ℝ} {q q' r r' : ℝ≥0∞}
    [q.HolderConjugate q'] [r.HolderConjugate r'] (hq : 2 < q) (hq_top : q ≠ ∞) (hr : 2 ≤ r)
    (hσ : q⁻¹.toReal + σ * r⁻¹.toReal = σ / 2) :
    ∃ C : ℝ≥0, ∀ {M D : ℝ≥0} {U : ℝ → H →L[ℂ] Lp ℂ 2 μ}, (∀ t, ‖U t‖ ≤ M) →
      (∀ s t, s ≠ t → ∀ g : Lp ℂ 2 μ, Integrable g μ →
        eLpNorm (U s (ContinuousLinearMap.adjoint (U t) g)) ∞ μ ≤
          D * ‖s - t‖ₑ ^ (-σ) * eLpNorm g 1 μ) →
      ∀ {G : ℝ → Lp ℂ 2 μ}, (∀ᵐ t, MemLp (G t) r' μ) →
        ‖∫ t, ContinuousLinearMap.adjoint (U t) (G t)‖ₑ ≤
          C * ↑(D ^ (2⁻¹ - r⁻¹.toReal) * M ^ (2 * r⁻¹.toReal)) *
            eLpNorm (fun t ↦ eLpNorm (G t) r' μ) q' := by
  obtain ⟨C, hC⟩ := exists_lintegral_lintegral_enorm_inner_adjoint_apply_le (H := H) (μ := μ)
    (q' := q') (r' := r') hq hq_top hr hσ
  refine ⟨C ^ (2⁻¹ : ℝ), fun {M D U} hU hdecay {G} hG => ?_⟩
  set w := fun t ↦ ContinuousLinearMap.adjoint (U t) (G t)
  -- If `w` is not integrable, its Bochner integral is `0`.
  by_cases hw : ¬Integrable w
  · simp [w, integral_undef hw]
  rw [not_not] at hw
  set v := ∫ t, w t
  set K : ℝ≥0 := D ^ (1 - 2 * r⁻¹.toReal) * M ^ (4 * r⁻¹.toReal)
  set B := eLpNorm (fun t ↦ eLpNorm (G t) r' μ) q'
  -- `‖v‖² = ⟪v, v⟫` is the double integral of the pairings `⟪w s, w t⟫`.
  have hvv : ⟪v, v⟫_ℂ = ∫ s, ∫ t, ⟪w s, w t⟫_ℂ := by
    rw [← inner_conj_symm, ← integral_inner hw v, ← integral_conj]
    refine integral_congr_ae (ae_of_all _ fun s => ?_)
    dsimp only
    rw [inner_conj_symm, integral_inner hw (w s)]
  have hsq : ‖v‖ₑ ^ 2 ≤ ↑(C * K) * B ^ 2 := by
    calc ‖v‖ₑ ^ 2 = ‖⟪v, v⟫_ℂ‖ₑ := by
          rw [inner_self_eq_norm_sq_to_K, enorm_pow, ← ofReal_norm, ← ofReal_norm,
            RCLike.norm_ofReal, abs_norm]
      _ ≤ ∫⁻ s, ‖∫ t, ⟪w s, w t⟫_ℂ‖ₑ := hvv ▸ enorm_integral_le_lintegral_enorm _
      _ ≤ ∫⁻ s, ∫⁻ t, ‖⟪w s, w t⟫_ℂ‖ₑ :=
          lintegral_mono fun s => enorm_integral_le_lintegral_enorm _
      _ ≤ C * K * B * B := hC hU hdecay hG hG
      _ = ↑(C * K) * B ^ 2 := by push_cast; ring
  -- Taking square roots.
  have hK : (C * K) ^ (2⁻¹ : ℝ) =
      C ^ (2⁻¹ : ℝ) * (D ^ (2⁻¹ - r⁻¹.toReal) * M ^ (2 * r⁻¹.toReal)) := by
    rw [NNReal.mul_rpow, NNReal.mul_rpow, ← NNReal.rpow_mul, ← NNReal.rpow_mul]
    ring_nf
  calc ‖v‖ₑ = (‖v‖ₑ ^ (2 : ℝ)) ^ (2⁻¹ : ℝ) := by
        rw [ENNReal.rpow_rpow_inv two_ne_zero]
    _ ≤ (↑(C * K) * B ^ (2 : ℝ)) ^ (2⁻¹ : ℝ) := by
        rw [ENNReal.rpow_two, ENNReal.rpow_two]
        gcongr
    _ = _ := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num), ENNReal.rpow_rpow_inv two_ne_zero,
          ← ENNReal.coe_rpow_of_nonneg _ (by norm_num), hK]
        push_cast
        ring

end TauCeti
