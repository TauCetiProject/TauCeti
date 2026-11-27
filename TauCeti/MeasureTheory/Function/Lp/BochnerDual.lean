/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Function.Holder
import Mathlib.Analysis.Normed.Module.DoubleDual
import Mathlib.MeasureTheory.Function.SimpleFuncDenseLp
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import TauCeti.MeasureTheory.Function.Holder
import TauCeti.MeasureTheory.Function.Lp.Duality
import TauCeti.MeasureTheory.Function.Lp.Norm

/-!
# The integral pairing of a Bochner space with the Bochner space of the dual

For Hölder conjugate exponents `p` and `q` and a normed space `X` over `ℝ` or `ℂ`, integrating
the duality pairing gives the canonical contraction

`bochnerDualMap 𝕜 μ p q : Lᵖ(μ; X⋆) → (L^q(μ; X))⋆`, `g ↦ (f ↦ ∫ g x (f x) dμ)`,

with `X⋆ = StrongDual 𝕜 X`. This file proves that it is an isometry and that its range norms
`L^q(μ; X)`:

* for `p < ∞` on an arbitrary measure space, `‖bochnerDualMap 𝕜 μ p q g‖ = ‖g‖`;
* on a σ-finite measure space this holds for all conjugate exponents, including `p = ∞`;
* dually, `f ∈ L^q(μ; X)` is normed by the pairings with `g` in the unit ball of `Lᵖ(μ; X⋆)`,
  for `q < ∞` on an arbitrary measure space and for all `q` on a σ-finite one.

Both statements are instances of a norming result for the pairing `B.lpPairing μ p q` of a
continuous bilinear form `B : E →L[𝕜] F →L[𝕜] 𝕜` that norms `E`, in the sense that
`‖e‖ ≤ ‖B e‖` for every `e`. For `p < ∞`, simple functions are dense in `Lᵖ(μ; E)`, and a simple
`g` is tested against `σ • u`, where `u` is a simple function with `‖u‖ ≤ 1` and
`‖B (g x) (u x)‖ ≥ θ ‖g x‖` for a fixed `θ < 1`, and `σ` runs through the scalar simple
functions; the scalar norming theorem for `Lᵖ` then bounds `‖g‖_p`. For `p = ∞` the function `g`
has separable range, so on a set of finite positive measure where `‖g‖` is close to its essential
supremum it stays close to a single vector `d`, and an indicator function in `L¹(μ; F)` with a
value norming `d` tests the essential supremum.

The pairing is natural in `X`: the adjoint of a bounded operator `T` on the dual side corresponds
to composition with `T` on the other side.

## Main declarations

* `ContinuousLinearMap.norm_le_norm_lpPairing_apply_of_ne_top`,
  `ContinuousLinearMap.norm_le_norm_lpPairing_apply`: norming of `Lᵖ(μ; E)` by the pairing of a
  bilinear form that norms `E`.
* `MeasureTheory.Lp.bochnerDualMap`: the integral pairing `Lᵖ(μ; X⋆) →L[𝕜] (L^q(μ; X))⋆`.
* `MeasureTheory.Lp.norm_bochnerDualMap_apply_of_ne_top`,
  `MeasureTheory.Lp.norm_bochnerDualMap_apply`: the pairing is isometric.
* `MeasureTheory.Lp.norm_flip_bochnerDualMap_apply_of_ne_top`,
  `MeasureTheory.Lp.norm_flip_bochnerDualMap_apply`: its range norms `L^q(μ; X)`.
* `MeasureTheory.Lp.bochnerDualMapₗᵢ`: on a σ-finite measure space, the integral pairing as a
  linear isometry.
* `MeasureTheory.Lp.isClosed_range_bochnerDualMap`: on a σ-finite measure space the range is
  closed.

## References

* T. Hytönen, J. van Neerven, M. Veraar, L. Weis, *Analysis in Banach Spaces, Volume I*,
  Springer, 2016, Proposition 1.3.1.
-/

public section

open MeasureTheory
open scoped ENNReal

namespace ContinuousLinearMap

section Indicator

variable {α 𝕜 E F G : Type*} [NontriviallyNormedField 𝕜] {mα : MeasurableSpace α}
  {μ : Measure α} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup F]
  [NormedSpace 𝕜 F] [NormedAddCommGroup G] [NormedSpace 𝕜 G] [NormedSpace ℝ G]
  [SMulCommClass ℝ 𝕜 G] [CompleteSpace G] {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)]
  [p.HolderConjugate q]

/-- Pairing `g ∈ Lᵖ(μ; E)` through `B` with the indicator function of a set `s` of finite measure
with value `y` gives the integral of `B (g x) y` over `s`. -/
theorem lpPairing_indicatorConstLp (B : E →L[𝕜] F →L[𝕜] G) (g : Lp E p μ) {s : Set α}
    (hs : MeasurableSet s) (hμs : μ s ≠ ∞) (y : F) :
    B.lpPairing μ p q g (indicatorConstLp q hs hμs y) = ∫ x in s, B (g x) y ∂μ := by
  rw [lpPairing_eq_integral, ← integral_indicator hs]
  refine integral_congr_ae ?_
  filter_upwards [indicatorConstLp_coeFn (p := q) (hs := hs) (hμs := hμs) (c := y)] with x hx
  rw [hx]
  by_cases hxs : x ∈ s <;> simp [hxs]

end Indicator

variable {α 𝕜 E F : Type*} [RCLike 𝕜] {mα : MeasurableSpace α} {μ : Measure α}
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)] [p.HolderConjugate q]

/-- A bilinear form that norms `E` almost attains the norm of each `e` on the unit ball. -/
private theorem exists_norm_le_one_mul_norm_le (B : E →L[𝕜] F →L[𝕜] 𝕜)
    (hB : ∀ e, ‖e‖ ≤ ‖B e‖) {θ : ℝ} (hθ : θ < 1) (e : E) :
    ∃ y : F, ‖y‖ ≤ 1 ∧ θ * ‖e‖ ≤ ‖B e y‖ := by
  rcases eq_or_ne e 0 with rfl | he
  · exact ⟨0, by simp⟩
  obtain ⟨y, hy, hlt⟩ := (B e).exists_lt_apply_of_lt_opNorm
    ((mul_lt_of_lt_one_left (norm_pos_iff.2 he) hθ).trans_le (hB e))
  exact ⟨y, hy.le, hlt.le⟩

/-- **Norming of `Lᵖ` by a norming pairing, simple functions.** For a simple function `g` and
`θ < 1`, the extended norm of `B.lpPairing μ p q g` is at least `θ ‖g‖_p`. -/
private theorem mul_eLpNorm_le_enorm_lpPairing (B : E →L[𝕜] F →L[𝕜] 𝕜)
    (hB : ∀ e, ‖e‖ ≤ ‖B e‖) (hp : p ≠ ∞) (g : Lp E p μ) (ψ : SimpleFunc α E)
    (hψ : ⇑ψ =ᵐ[μ] g) {a : ℝ≥0∞} (ha : a < 1) :
    a * eLpNorm g p μ ≤ ‖B.lpPairing μ p q g‖ₑ := by
  set θ := a.toReal
  have hθ : θ < 1 := by
    simpa [θ] using ENNReal.toReal_strict_mono ENNReal.one_ne_top ha
  choose c hc1 hc2 using exists_norm_le_one_mul_norm_le B hB hθ
  -- The scalar simple function `x ↦ B (ψ x) (c (ψ x))` dominates `θ ‖ψ‖`.
  set h : SimpleFunc α 𝕜 := ψ.map fun e ↦ B e (c e)
  have hψp : MemLp ψ p μ := (Lp.memLp g).ae_eq hψ.symm
  have hhp : MemLp h p μ := hψp.of_le_mul (c := ‖B‖) h.aestronglyMeasurable
    (ae_of_all _ fun x ↦ by
      rw [SimpleFunc.map_apply]
      exact (B.le_opNorm₂ (ψ x) (c (ψ x))).trans
        (mul_le_of_le_one_right (by positivity) (hc1 _)))
  -- The scalar norming theorem bounds `‖h‖_p` by the norm of the pairing.
  have hh : eLpNorm h p μ ≤ ‖B.lpPairing μ p q g‖ₑ := by
    refine hhp.eLpNorm_le_of_forall_enorm_integral_mul_le_of_ne_top (q' := q) hp fun σ hσ ↦ ?_
    set w : α → F := fun x ↦ σ x • c (ψ x)
    have hwm : AEStronglyMeasurable w μ :=
      σ.aestronglyMeasurable.smul (ψ.map c).aestronglyMeasurable
    have hwσ (x : α) : ‖w x‖ ≤ ‖σ x‖ := by
      simpa [w, norm_smul] using mul_le_of_le_one_right (norm_nonneg _) (hc1 (ψ x))
    have hw : MemLp w q μ := hσ.of_le hwm (ae_of_all _ hwσ)
    have hint : ∫ x, h x * σ x ∂μ = B.lpPairing μ p q g (hw.toLp w) := by
      rw [lpPairing_eq_integral]
      refine integral_congr_ae ?_
      filter_upwards [hψ, hw.coeFn_toLp] with x hx hx'
      simp [h, w, hx', ← hx, mul_comm]
    calc ‖∫ x, h x * σ x ∂μ‖ₑ ≤ ‖B.lpPairing μ p q g‖ₑ * ‖hw.toLp w‖ₑ := by
          rw [hint]; exact (B.lpPairing μ p q g).le_opENorm _
      _ ≤ ‖B.lpPairing μ p q g‖ₑ * eLpNorm σ q μ := by
          rw [Lp.eNorm_toLp]
          gcongr
          exact eLpNorm_mono hwm hwσ
  have ha' : a = ‖(θ : 𝕜)‖ₑ := by
    rw [← ofReal_norm, RCLike.norm_ofReal, abs_of_nonneg ENNReal.toReal_nonneg,
      ENNReal.ofReal_toReal (ha.trans ENNReal.one_lt_top).ne]
  calc a * eLpNorm g p μ = eLpNorm ((θ : 𝕜) • ⇑ψ) p μ := by
        rw [eLpNorm_const_smul, eLpNorm_congr_ae hψ, ha']
    _ ≤ eLpNorm h p μ := eLpNorm_mono (ψ.aestronglyMeasurable.const_smul _) fun x ↦ by
        rw [Pi.smul_apply, norm_smul, RCLike.norm_ofReal, abs_of_nonneg ENNReal.toReal_nonneg,
          SimpleFunc.map_apply]
        exact hc2 (ψ x)
    _ ≤ ‖B.lpPairing μ p q g‖ₑ := hh

/-- **Norming of `Lᵖ` by a norming pairing, `p < ∞`.** Let `B : E →L[𝕜] F →L[𝕜] 𝕜` norm `E`,
in the sense that `‖e‖ ≤ ‖B e‖` for every `e`. Then for `p < ∞` on an arbitrary measure space,
`g ∈ Lᵖ(μ; E)` is normed by its pairings with the unit ball of `L^q(μ; F)`. -/
theorem norm_le_norm_lpPairing_apply_of_ne_top (B : E →L[𝕜] F →L[𝕜] 𝕜)
    (hB : ∀ e, ‖e‖ ≤ ‖B e‖) (hp : p ≠ ∞) (g : Lp E p μ) :
    ‖g‖ ≤ ‖B.lpPairing μ p q g‖ := by
  -- Both sides are continuous in `g`, and simple functions are dense in `Lᵖ`.
  refine (Lp.simpleFunc.denseRange hp).induction_on g
    (isClosed_le continuous_norm (continuous_norm.comp (B.lpPairing μ p q).continuous))
    fun φ ↦ ?_
  rw [← toReal_eNorm, ← toReal_eNorm]
  refine ENNReal.toReal_mono eNorm_ne_top (ENNReal.le_of_forall_lt_one_mul_le fun a ha ↦ ?_)
  rw [Lp.eNorm_def]
  exact mul_eLpNorm_le_enorm_lpPairing B hB hp _ _ (Lp.simpleFunc.toSimpleFunc_eq_toFun φ) ha

/-- If `g ∈ L^∞(μ; E)` stays `ε`-close to `d` on a set `s` of finite positive measure, then
pairing `g` with the indicator function `1_s y ∈ L¹(μ; F)`, for `‖y‖ ≤ 1`, shows that
`‖B d y‖ ≤ ‖B.lpPairing μ ∞ 1 g‖ + ‖B‖ ε`. -/
private theorem norm_apply_le_norm_lpPairing_apply_top_add (B : E →L[𝕜] F →L[𝕜] 𝕜)
    (g : Lp E ∞ μ) {s : Set α} (hs : MeasurableSet s) (hspos : 0 < μ s) (hstop : μ s < ∞)
    {d : E} {ε : ℝ} (hsd : ∀ x ∈ s, ‖g x - d‖ < ε) {y : F} (hy : ‖y‖ ≤ 1) :
    ‖B d y‖ ≤ ‖B.lpPairing μ ∞ 1 g‖ + ‖B‖ * ε := by
  have hμs : 0 < μ.real s := ENNReal.toReal_pos hspos.ne' hstop.ne
  set f := indicatorConstLp 1 hs hstop.ne y
  have hf : ‖f‖ ≤ μ.real s := by
    rw [norm_indicatorConstLp one_ne_zero ENNReal.one_ne_top]
    simpa using mul_le_of_le_one_left hμs.le hy
  have hint : B.lpPairing μ ∞ 1 g f = ∫ x in s, B (g x) y ∂μ :=
    B.lpPairing_indicatorConstLp g hs hstop.ne y
  have hbound : ∀ x ∈ s, ‖B (g x) y - B d y‖ ≤ ‖B‖ * ε := fun x hx ↦ by
    rw [← sub_apply, ← map_sub]
    refine (B.le_opNorm₂ _ _).trans ?_
    have := hsd x hx
    have : ‖B‖ * ‖g x - d‖ * ‖y‖ ≤ ‖B‖ * ‖g x - d‖ * 1 := by gcongr
    nlinarith [norm_nonneg B]
  have hgs : IntegrableOn (fun x ↦ B (g x) y) s μ := by
    refine Measure.integrableOn_of_bounded (M := ‖B d y‖ + ‖B‖ * ε) hstop.ne
      ((B.flip y).continuous.comp_stronglyMeasurable
        (Lp.stronglyMeasurable g)).aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem hs] with x hx
    have := norm_sub_norm_le (B (g x) y) (B d y)
    linarith [hbound x hx]
  -- The pairing is close to `μ(s) B d y`, and bounded by `‖B.lpPairing g‖ μ(s)`.
  have hclose : ‖∫ x in s, B (g x) y ∂μ - μ.real s • B d y‖ ≤ ‖B‖ * ε * μ.real s := by
    rw [← setIntegral_const, ← integral_sub hgs (integrableOn_const hstop.ne)]
    exact norm_setIntegral_le_of_norm_le_const hstop hbound
  have hupper : ‖∫ x in s, B (g x) y ∂μ‖ ≤ ‖B.lpPairing μ ∞ 1 g‖ * μ.real s := by
    rw [← hint]
    exact ((B.lpPairing μ ∞ 1 g).le_opNorm f).trans (by gcongr)
  have := norm_le_insert' (μ.real s • B d y) (∫ x in s, B (g x) y ∂μ)
  rw [norm_sub_rev, norm_smul, Real.norm_of_nonneg hμs.le] at this
  refine le_of_mul_le_mul_left ?_ hμs
  linarith

/-- **Norming of `L^∞` by a norming pairing.** Let `B : E →L[𝕜] F →L[𝕜] 𝕜` norm `E`, in the
sense that `‖e‖ ≤ ‖B e‖` for every `e`. On a σ-finite measure space, `g ∈ L^∞(μ; E)` is normed
by its pairings with the unit ball of `L¹(μ; F)`. -/
theorem norm_le_norm_lpPairing_apply_top [SigmaFinite μ] (B : E →L[𝕜] F →L[𝕜] 𝕜)
    (hB : ∀ e, ‖e‖ ≤ ‖B e‖) (g : Lp E ∞ μ) :
    ‖g‖ ≤ ‖B.lpPairing μ ∞ 1 g‖ := by
  by_contra! hlt
  set N := ‖B.lpPairing μ ∞ 1 g‖
  obtain ⟨t, hNt, htg⟩ := exists_between hlt
  -- With `ε = (t - N) / (2 (2 + ‖B‖))`, a vector norming `d` contradicts `N < t`.
  set ε := (t - N) / (2 * (2 + ‖B‖))
  have hε : 0 < ε := div_pos (by linarith) (by positivity)
  obtain ⟨s, hs, hspos, hstop, d, hdt, hsd⟩ :=
    Lp.exists_measurableSet_forall_norm_sub_lt_of_lt_norm g ((norm_nonneg _).trans hNt.le) htg hε
  obtain ⟨y, hy, hdy⟩ := (B d).exists_lt_apply_of_lt_opNorm
    ((show t - 2 * ε < t - ε by linarith).trans (hdt.trans_le (hB d)))
  have := norm_apply_le_norm_lpPairing_apply_top_add B g hs hspos hstop hsd hy.le
  have hεB : (2 + ‖B‖) * ε = (t - N) / 2 := by
    simp only [ε]; field_simp
  nlinarith

/-- **Norming of `Lᵖ` by a norming pairing.** Let `B : E →L[𝕜] F →L[𝕜] 𝕜` norm `E`, in the
sense that `‖e‖ ≤ ‖B e‖` for every `e`. On a σ-finite measure space, `g ∈ Lᵖ(μ; E)` is normed
by its pairings with the unit ball of `L^q(μ; F)`, for all conjugate exponents. -/
theorem norm_le_norm_lpPairing_apply [SigmaFinite μ] (B : E →L[𝕜] F →L[𝕜] 𝕜)
    (hB : ∀ e, ‖e‖ ≤ ‖B e‖) (g : Lp E p μ) :
    ‖g‖ ≤ ‖B.lpPairing μ p q g‖ := by
  rcases eq_or_ne p ∞ with rfl | hp
  · obtain rfl : q = 1 := (ENNReal.HolderConjugate.eq_top_iff_eq_one ∞ q).1 rfl
    exact norm_le_norm_lpPairing_apply_top B hB g
  · exact norm_le_norm_lpPairing_apply_of_ne_top B hB hp g

end ContinuousLinearMap

namespace MeasureTheory.Lp

variable {α 𝕜 X Y : Type*} [RCLike 𝕜] {mα : MeasurableSpace α} {μ : Measure α}
  [NormedAddCommGroup X] [NormedSpace 𝕜 X] [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
  {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)] [p.HolderConjugate q]

variable (𝕜 μ p q) in
/-- The integral pairing `g ↦ (f ↦ ∫ g x (f x) dμ)` from `Lᵖ(μ; X⋆)` to the continuous dual of
`L^q(μ; X)`, for Hölder conjugate exponents `p` and `q` and `X⋆ = StrongDual 𝕜 X`. It is a
contraction (`MeasureTheory.Lp.norm_bochnerDualMap_apply_le`), and an isometry when `p < ∞` or
the measure is σ-finite. -/
noncomputable def bochnerDualMap :
    Lp (StrongDual 𝕜 X) p μ →L[𝕜] StrongDual 𝕜 (Lp X q μ) :=
  (ContinuousLinearMap.id 𝕜 (StrongDual 𝕜 X)).lpPairing μ p q

/-- The integral pairing is the Hölder pairing of the identity of `X⋆`, viewed as a bilinear form
on `X⋆ × X`. -/
theorem bochnerDualMap_eq_lpPairing :
    bochnerDualMap 𝕜 μ p q (X := X) = (ContinuousLinearMap.id 𝕜 (StrongDual 𝕜 X)).lpPairing μ p q :=
  (rfl)

/-- Evaluation of the integral pairing: `g` pairs with `f` to `∫ g x (f x) dμ`. -/
@[simp]
theorem bochnerDualMap_apply (g : Lp (StrongDual 𝕜 X) p μ) (f : Lp X q μ) :
    bochnerDualMap 𝕜 μ p q g f = ∫ x, g x (f x) ∂μ := by
  simp [bochnerDualMap_eq_lpPairing, ContinuousLinearMap.lpPairing_eq_integral]

/-- Pairing `g ∈ Lᵖ(μ; X⋆)` with the indicator function of a set `s` of finite measure with value
`x` gives the integral of `g · x` over `s`. -/
-- High priority, so that `simp` uses this lemma before unfolding the pairing.
@[simp high]
theorem bochnerDualMap_indicatorConstLp (g : Lp (StrongDual 𝕜 X) p μ) {s : Set α}
    (hs : MeasurableSet s) (hμs : μ s ≠ ∞) (x : X) :
    bochnerDualMap 𝕜 μ p q g (indicatorConstLp q hs hμs x) = ∫ y in s, g y x ∂μ :=
  (ContinuousLinearMap.id 𝕜 (StrongDual 𝕜 X)).lpPairing_indicatorConstLp g hs hμs x

/-- **Naturality of the integral pairing.** Pairing `T⋆ ∘ g` with `f` is pairing `g` with
`T ∘ f`, where `T⋆ = ContinuousLinearMap.precomp 𝕜 T` is the adjoint of `T : X →L[𝕜] Y`. -/
theorem bochnerDualMap_compLp_precomp (T : X →L[𝕜] Y) (g : Lp (StrongDual 𝕜 Y) p μ)
    (f : Lp X q μ) :
    bochnerDualMap 𝕜 μ p q
        ((ContinuousLinearMap.precomp 𝕜 T : StrongDual 𝕜 Y →L[𝕜] StrongDual 𝕜 X).compLp g) f =
      bochnerDualMap 𝕜 μ p q g (T.compLp f) := by
  rw [bochnerDualMap_apply, bochnerDualMap_apply]
  refine integral_congr_ae ?_
  filter_upwards [ContinuousLinearMap.coeFn_compLp (p := p) (μ := μ)
      (ContinuousLinearMap.precomp 𝕜 T : StrongDual 𝕜 Y →L[𝕜] StrongDual 𝕜 X) g,
    T.coeFn_compLp (p := q) (μ := μ) f] with x hx hx'
  simp [hx, hx']

/-- **Hölder's inequality** for the integral pairing: `bochnerDualMap` is a contraction. -/
theorem norm_bochnerDualMap_apply_le (g : Lp (StrongDual 𝕜 X) p μ) :
    ‖bochnerDualMap 𝕜 μ p q g‖ ≤ ‖g‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg g) fun f ↦ ?_
  rw [bochnerDualMap_eq_lpPairing]
  refine ((ContinuousLinearMap.id 𝕜 (StrongDual 𝕜 X)).norm_lpPairing_apply_apply_le g f).trans ?_
  gcongr
  exact mul_le_of_le_one_left (norm_nonneg g) ContinuousLinearMap.norm_id_le

/-- The pairing with `f ∈ L^q(μ; X)` is a functional on `Lᵖ(μ; X⋆)` of norm at most `‖f‖`. -/
theorem norm_flip_bochnerDualMap_apply_le (f : Lp X q μ) :
    ‖(bochnerDualMap 𝕜 μ p q).flip f‖ ≤ ‖f‖ :=
  ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg f) fun g ↦ by
    rw [ContinuousLinearMap.flip_apply, mul_comm]
    exact (bochnerDualMap 𝕜 μ p q g).le_of_opNorm_le (norm_bochnerDualMap_apply_le g) f

/-- **The integral pairing is isometric, `p < ∞`.** On an arbitrary measure space, the functional
`f ↦ ∫ g x (f x) dμ` on `L^q(μ; X)` has norm `‖g‖_p` for every `g ∈ Lᵖ(μ; X⋆)`. -/
theorem norm_bochnerDualMap_apply_of_ne_top (hp : p ≠ ∞) (g : Lp (StrongDual 𝕜 X) p μ) :
    ‖bochnerDualMap 𝕜 μ p q g‖ = ‖g‖ :=
  (norm_bochnerDualMap_apply_le g).antisymm
    (by
      rw [bochnerDualMap_eq_lpPairing]
      exact (ContinuousLinearMap.id 𝕜 _).norm_le_norm_lpPairing_apply_of_ne_top (fun _ ↦ le_rfl)
        hp g)

/-- **The integral pairing is isometric.** On a σ-finite measure space, the functional
`f ↦ ∫ g x (f x) dμ` on `L^q(μ; X)` has norm `‖g‖_p` for every `g ∈ Lᵖ(μ; X⋆)` and all
conjugate exponents. -/
theorem norm_bochnerDualMap_apply [SigmaFinite μ] (g : Lp (StrongDual 𝕜 X) p μ) :
    ‖bochnerDualMap 𝕜 μ p q g‖ = ‖g‖ :=
  (norm_bochnerDualMap_apply_le g).antisymm
    (by
      rw [bochnerDualMap_eq_lpPairing]
      exact (ContinuousLinearMap.id 𝕜 _).norm_le_norm_lpPairing_apply (fun _ ↦ le_rfl) g)

variable (𝕜 μ p q) in
/-- On a σ-finite measure space, the integral pairing `bochnerDualMap 𝕜 μ p q` bundled as a linear
isometry `Lᵖ(μ; X⋆) →ₗᵢ[𝕜] (L^q(μ; X))⋆`. -/
noncomputable def bochnerDualMapₗᵢ [SigmaFinite μ] :
    Lp (StrongDual 𝕜 X) p μ →ₗᵢ[𝕜] StrongDual 𝕜 (Lp X q μ) where
  toLinearMap := (bochnerDualMap 𝕜 μ p q).toLinearMap
  norm_map' := norm_bochnerDualMap_apply

@[simp]
theorem coe_bochnerDualMapₗᵢ [SigmaFinite μ] :
    ⇑(bochnerDualMapₗᵢ 𝕜 μ p q (X := X)) = bochnerDualMap 𝕜 μ p q :=
  (rfl)

/-- On a σ-finite measure space, the integral pairing is an isometry. -/
theorem isometry_bochnerDualMap [SigmaFinite μ] :
    Isometry (bochnerDualMap 𝕜 μ p q (X := X)) :=
  AddMonoidHomClass.isometry_of_norm _ norm_bochnerDualMap_apply

/-- On a σ-finite measure space, the integral pairing has closed range. -/
theorem isClosed_range_bochnerDualMap [SigmaFinite μ] :
    IsClosed (Set.range (bochnerDualMap 𝕜 μ p q (X := X))) :=
  isometry_bochnerDualMap.isClosedEmbedding.isClosed_range

/-- The pairing of `Lᵖ(μ; X⋆)` with `L^q(μ; X)`, read from the side of `X`, is the pairing of
`L^q(μ; X)` with `Lᵖ(μ; X⋆)` induced by the canonical map of `X` into its bidual. -/
private theorem flip_bochnerDualMap_apply (f : Lp X q μ) :
    (bochnerDualMap 𝕜 μ p q).flip f = (NormedSpace.inclusionInDoubleDual 𝕜 X).lpPairing μ q p f :=
  ContinuousLinearMap.ext fun g ↦ by
    simp [ContinuousLinearMap.lpPairing_eq_integral]

/-- **The range of the integral pairing is norming, `q < ∞`.** On an arbitrary measure space,
`f ∈ L^q(μ; X)` is normed by its pairings `∫ g x (f x) dμ` with the unit ball of `Lᵖ(μ; X⋆)`. -/
theorem norm_flip_bochnerDualMap_apply_of_ne_top (hq : q ≠ ∞) (f : Lp X q μ) :
    ‖(bochnerDualMap 𝕜 μ p q).flip f‖ = ‖f‖ :=
  (norm_flip_bochnerDualMap_apply_le f).antisymm <| by
    rw [flip_bochnerDualMap_apply]
    exact (NormedSpace.inclusionInDoubleDual 𝕜 X).norm_le_norm_lpPairing_apply_of_ne_top
      (fun x ↦ ((NormedSpace.inclusionInDoubleDualLi 𝕜).norm_map x).ge) hq f

/-- **The range of the integral pairing is norming.** On a σ-finite measure space,
`f ∈ L^q(μ; X)` is normed by its pairings `∫ g x (f x) dμ` with the unit ball of `Lᵖ(μ; X⋆)`,
for all conjugate exponents. -/
theorem norm_flip_bochnerDualMap_apply [SigmaFinite μ] (f : Lp X q μ) :
    ‖(bochnerDualMap 𝕜 μ p q).flip f‖ = ‖f‖ :=
  (norm_flip_bochnerDualMap_apply_le f).antisymm <| by
    rw [flip_bochnerDualMap_apply]
    exact (NormedSpace.inclusionInDoubleDual 𝕜 X).norm_le_norm_lpPairing_apply
      (fun x ↦ ((NormedSpace.inclusionInDoubleDualLi 𝕜).norm_map x).ge) f

end MeasureTheory.Lp
