/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.Poincare.Wirtinger.Basic
public import TauCeti.Analysis.Sobolev.W1p.Basic
public import TauCeti.Analysis.Sobolev.W1p.Zero
public import Mathlib.Analysis.InnerProductSpace.Laplacian
import Mathlib.Analysis.Convex.Measure
import TauCeti.Algebra.Module.ZLattice.Basic
import TauCeti.Analysis.InnerProductSpace.Laplacian.Basic
import TauCeti.Analysis.Sobolev.W1p.Density
import TauCeti.Analysis.Sobolev.WeakDeriv.Laplacian
import TauCeti.MeasureTheory.Function.Lp.BilinearMap

/-!
# A Poincaré inequality for Schrödinger forms with a potential positive off a set of finite measure

On the whole of a finite-dimensional space no Poincaré inequality `‖u‖₂ ≤ C ‖Du‖₂` holds
(`TauCeti.not_exists_eLpNorm_le_const_mul_eLpNorm_fderiv`). A nonnegative potential `P` that is
bounded below by a constant `a > 0` outside a set `B` of finite measure restores it: there is
`c > 0` with

`c ∫ ‖u‖² ≤ ∫ ‖Du‖² + ∫ P ‖u‖²`

for every compactly supported `C¹` map `u`. In other words the quadratic form of the
Schrödinger operator `-Δ + P` is bounded below by `c` times the squared `L²` norm, so `-Δ + P` has a
spectral gap, although `P` may vanish on `B`. The constant depends on `P` only through `a` and an
upper bound for the measure of `B`
(`exists_pos_forall_mul_integral_norm_sq_le_integral_norm_fderiv_sq_add_integral_mul_norm_sq`).
In particular it does not depend on where `B` lies: `B` may be a union of finitely many discs of
a fixed radius around arbitrary centres, for instance around the zeros of a field, and the bound is
uniform as the centres move apart. A ball of radius `R` is the special case where the constant
depends only on `a` and `R`.

The proof tiles the space by the lattice translates of a parallelepiped `T` of measure at least
twice the bound on `μ(B)`. On every tile `Ω`, the part `S` of `Ω` off `B` carries at least half
of its measure, so the Poincaré–Wirtinger inequality with the mean taken over `S` controls the
deviation of `u` from that mean by `Du`, and the mean itself by the integral of `‖u‖²` over `S`,
hence by the potential term (`TauCeti.setIntegral_norm_sq_le_of_convex`). The resulting
inequality on a tile (`TauCeti.mul_setIntegral_norm_sq_le_of_convex`) has constants depending only
on `a`, the measure of the tile and its diameter, which are the same for all tiles, and summing
over the tiles gives the inequality on the whole space.

Such an estimate makes `L L*` coercive for a first-order operator `L` whose Weitzenböck formula
has a potential of this kind.

For an essentially bounded potential `P` on an inner product space, the inequality extends by
density of test functions (`TauCeti.W1p.denseRange_ofTestFunctionₗ_top`) to the bounded
Schrödinger form `TauCeti.schrodingerForm`, `(u, v) ↦ ∫ ⟪∇u, ∇v⟫ + ∫ P u v`, on all of
`H¹(E) = W^{1,2}(E)`, which is then coercive.

## Main results

* `TauCeti.mul_setIntegral_norm_sq_le_of_convex`: the inequality on a bounded convex set, at
  least half of which lies off `B`.
* `exists_pos_forall_mul_integral_norm_sq_le_integral_norm_fderiv_sq_add_integral_mul_norm_sq`:
  the inequality above, with a constant depending only on `a` and the bound on `μ(B)`.
* `TauCeti.exists_pos_mul_integral_norm_sq_le_integral_norm_fderiv_sq_add_integral_mul_norm_sq`:
  the case where `B` is a ball.
* `TauCeti.schrodingerForm`: the Schrödinger form of a bounded potential as a continuous
  bilinear form on `H¹(E)`.
* `TauCeti.integral_value_mul_eq_schrodingerForm`: testing `u ∈ H¹(E)` against `-Δφ + P φ` for
  a test function `φ` is the Schrödinger form of `u` and `φ`, the link with the weak formulation
  of `-Δh + P h = g`.
* `TauCeti.exists_pos_mul_norm_sq_le_norm_gradient_sq_add_integral_mul_value_sq`: the inequality
  on `H¹(E)`, `c ‖u‖²_{H¹} ≤ ‖∇u‖₂² + ∫ P u²`.
* `TauCeti.isCoercive_schrodingerForm`: the Schrödinger form is coercive on `H¹(E)`.

## References

* D. Gilbarg and N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  Lemma 7.16 (the Poincaré–Wirtinger inequality used inside the ball).
-/

public section

namespace TauCeti

open MeasureTheory Metric Set Module Filter
open scoped ENNReal Pointwise

section TestFunction

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [Nontrivial E] [MeasurableSpace E] [BorelSpace E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [CompleteSpace F]
  {μ : Measure E} [μ.IsAddHaarMeasure]

omit [Nontrivial E] in
/-- **A Schrödinger–Poincaré inequality on a convex set.** Let `Ω` be a bounded convex set of
positive measure, and let `P` be almost everywhere nonnegative and almost everywhere at least
`a > 0` outside a set `B` of at most half the measure of `Ω`. Then, with
`K = 10 (2 μ(B(0, 1)) (diam Ω) ^ (n + 1) / μ(Ω)) ^ 2`, where `n` is the dimension of `E`,

`a ∫_Ω ‖u‖² ≤ a K ∫_Ω ‖Du‖² + 8 ∫_Ω P ‖u‖²`

for every `C¹` map `u` with `P ‖u‖²` integrable on `Ω`. The constants depend on `Ω` only through its
measure and diameter, and on `B` only through the bound on its measure. -/
theorem mul_setIntegral_norm_sq_le_of_convex {P : E → ℝ} {B Ω : Set E} {a : ℝ} (ha : 0 < a)
    (hΩc : Convex ℝ Ω) (hΩb : Bornology.IsBounded Ω) (hΩ₀ : μ Ω ≠ 0) (hB : 2 * μ B ≤ μ Ω)
    (hP₀ : ∀ᵐ z ∂μ, 0 ≤ P z) (haP : ∀ᵐ z ∂μ, z ∉ B → a ≤ P z) {u : E → F}
    (hu : ContDiff ℝ 1 u) (hPu : IntegrableOn (fun z ↦ P z * ‖u z‖ ^ 2) Ω μ) :
    a * ∫ z in Ω, ‖u z‖ ^ 2 ∂μ ≤
      a * (10 * (2 * (μ.real (ball 0 1) * diam Ω ^ (finrank ℝ E + 1)) / μ.real Ω) ^ 2) *
          ∫ z in Ω, ‖fderiv ℝ u z‖ ^ 2 ∂μ +
        8 * ∫ z in Ω, P z * ‖u z‖ ^ 2 ∂μ := by
  -- `S` is the part of `Ω` off a measurable hull of `B`; it carries at least half of `Ω`.
  set S := Ω \ toMeasurable μ B
  have hSΩ : S ⊆ Ω := sdiff_subset
  have hΩfin : μ Ω ≠ ∞ := hΩb.measure_lt_top.ne
  have hΩS : μ Ω ≤ 2 * μ S := by
    have h : μ Ω - μ B ≤ μ S := measure_toMeasurable B ▸ le_measure_sdiff
    calc μ Ω = 2 * μ Ω - μ Ω := by rw [two_mul, ENNReal.add_sub_cancel_right hΩfin]
      _ ≤ 2 * μ Ω - 2 * μ B := by gcongr
      _ = 2 * (μ Ω - μ B) := (ENNReal.mul_sub fun _ _ ↦ by simp).symm
      _ ≤ 2 * μ S := by gcongr
  have hS : NullMeasurableSet S μ :=
    (hΩc.nullMeasurableSet μ).diff (measurableSet_toMeasurable μ B).nullMeasurableSet
  have hVΩ : 0 < μ.real Ω := ENNReal.toReal_pos hΩ₀ hΩfin
  have hVS : μ.real Ω ≤ 2 * μ.real S := by
    simpa [measureReal_def, ENNReal.toReal_mul] using ENNReal.toReal_mono
      (ENNReal.mul_ne_top (by simp) (ne_top_of_le_ne_top hΩfin (measure_mono hSΩ))) hΩS
  have hVS₀ : 0 < μ.real S := by linarith
  have hS₀ : μ S ≠ 0 := fun h ↦ by simp [measureReal_def, h] at hVS₀
  -- The Poincaré inequality on `Ω` relative to `S`, with its constants bounded through
  -- `μ(Ω) ≤ 2 μ(S)`.
  have hW := setIntegral_norm_sq_le_of_convex (μ := μ) hΩc hΩb hu hSΩ hS₀
  set C := μ.real (ball (0 : E) 1) * diam Ω ^ (finrank ℝ E + 1)
  have h4 : 4 * μ.real Ω / μ.real S ≤ 8 := by rw [div_le_iff₀ hVS₀]; linarith
  have hCS : C / μ.real S ≤ 2 * C / μ.real Ω := by
    rw [div_le_div_iff₀ hVS₀ hVΩ]; nlinarith [(by positivity : 0 ≤ C)]
  have hA : (2 + 4 * μ.real Ω / μ.real S) * (C / μ.real S) ^ 2 ≤ 10 * (2 * C / μ.real Ω) ^ 2 := by
    have hsq := pow_le_pow_left₀ (by positivity : 0 ≤ C / μ.real S) hCS 2
    nlinarith [sq_nonneg (C / μ.real S)]
  -- Off `B`, the potential controls `‖u‖²`.
  have hpot : a * ∫ z in S, ‖u z‖ ^ 2 ∂μ ≤ ∫ z in Ω, P z * ‖u z‖ ^ 2 ∂μ := by
    rw [← integral_const_mul]
    have hUS : IntegrableOn (fun z ↦ ‖u z‖ ^ 2) S μ :=
      ((hu.continuous.norm.pow 2).continuousOn.integrableOn_compact
        hΩb.isCompact_closure).mono_set (hSΩ.trans subset_closure)
    refine (setIntegral_mono_on_ae₀ (hUS.const_mul a) (hPu.mono_set hSΩ) hS ?_).trans
      (setIntegral_mono_set hPu
        (ae_restrict_of_ae (hP₀.mono fun z hz ↦ by positivity)) (.of_forall hSΩ))
    filter_upwards [haP] with z hz hzS
    exact mul_le_mul_of_nonneg_right (hz fun hB ↦ hzS.2 (subset_toMeasurable μ B hB))
      (by positivity)
  calc a * ∫ z in Ω, ‖u z‖ ^ 2 ∂μ
      ≤ a * ((2 + 4 * μ.real Ω / μ.real S) * (C / μ.real S) ^ 2 *
          ∫ z in Ω, ‖fderiv ℝ u z‖ ^ 2 ∂μ + 4 * μ.real Ω / μ.real S * ∫ z in S, ‖u z‖ ^ 2 ∂μ) :=
        mul_le_mul_of_nonneg_left hW ha.le
    _ ≤ a * (10 * (2 * C / μ.real Ω) ^ 2) * ∫ z in Ω, ‖fderiv ℝ u z‖ ^ 2 ∂μ +
          8 * (a * ∫ z in S, ‖u z‖ ^ 2 ∂μ) := by
        nlinarith [mul_le_mul_of_nonneg_right hA (integral_nonneg fun _ ↦ by positivity :
          0 ≤ ∫ z in Ω, ‖fderiv ℝ u z‖ ^ 2 ∂μ), mul_le_mul_of_nonneg_right h4
          (integral_nonneg fun _ ↦ by positivity : 0 ≤ ∫ z in S, ‖u z‖ ^ 2 ∂μ)]
    _ ≤ _ := by linarith [hpot]

/-- **Uniform Poincaré inequality for Schrödinger forms.** Let `a > 0` and `M < ∞`. There is
`c > 0`, depending only on `a` and `M` (and on `E` and `μ`), with the following property. If `P`
is locally integrable, almost everywhere nonnegative, and almost everywhere at least `a` outside a
set `B` of measure at most `M`, then `c ∫ ‖u‖² ≤ ∫ ‖Du‖² + ∫ P ‖u‖²` for every compactly
supported `C¹` map `u`. The set `B` where `P` may be small is arbitrary: it need not be bounded,
connected or close to the origin. -/
theorem exists_pos_forall_mul_integral_norm_sq_le_integral_norm_fderiv_sq_add_integral_mul_norm_sq
    {a : ℝ} (ha : 0 < a) {M : ℝ≥0∞} (hM : M ≠ ∞) :
    ∃ c > 0, ∀ (P : E → ℝ) (B : Set E), LocallyIntegrable P μ → (∀ᵐ z ∂μ, 0 ≤ P z) →
      μ B ≤ M → (∀ᵐ z ∂μ, z ∉ B → a ≤ P z) →
      ∀ u : E → F, ContDiff ℝ 1 u → HasCompactSupport u →
        c * ∫ z, ‖u z‖ ^ 2 ∂μ ≤ ∫ z, ‖fderiv ℝ u z‖ ^ 2 ∂μ + ∫ z, P z * ‖u z‖ ^ 2 ∂μ := by
  -- Tile `E` by the lattice translates of a parallelepiped `T` of measure at least `2 M`.
  obtain ⟨G, T, _, hT, hTc, hTb, hTM⟩ := exists_isAddFundamentalDomain_convex_le_measure μ
    (ENNReal.mul_ne_top (by simp) hM : 2 * M ≠ ∞)
  have hT₀ : μ T ≠ 0 := hT.measure_ne_zero (NeZero.ne μ)
  set K := 10 * (2 * (μ.real (ball (0 : E) 1) * diam T ^ (finrank ℝ E + 1)) / μ.real T) ^ 2
    with hK
  have hK₀ : 0 ≤ K := by positivity
  refine ⟨a / (a * K + 8), by positivity, fun P B hP hP₀ hBM haP u hu hc ↦ ?_⟩
  have hn : HasCompactSupport fun z ↦ ‖u z‖ ^ 2 := hc.comp_left (g := fun v ↦ ‖v‖ ^ 2) (by simp)
  have hI : Integrable (fun z ↦ ‖u z‖ ^ 2) μ :=
    (hu.continuous.norm.pow 2).integrable_of_hasCompactSupport hn
  have hDc : Continuous fun z ↦ ‖fderiv ℝ u z‖ ^ 2 :=
    (hu.continuous_fderiv one_ne_zero).norm.pow 2
  have hDs : HasCompactSupport fun z ↦ ‖fderiv ℝ u z‖ ^ 2 :=
    (hc.fderiv (𝕜 := ℝ)).comp_left (g := fun L ↦ ‖L‖ ^ 2) (by simp)
  have hD : Integrable (fun z ↦ ‖fderiv ℝ u z‖ ^ 2) μ := hDc.integrable_of_hasCompactSupport hDs
  have hQ : Integrable (fun z ↦ P z * ‖u z‖ ^ 2) μ :=
    hP.integrable_smul_right_of_hasCompactSupport (g := fun z ↦ ‖u z‖ ^ 2)
      (hu.continuous.norm.pow 2) hn
  have hR : Integrable (fun z ↦ a * K * ‖fderiv ℝ u z‖ ^ 2 + 8 * (P z * ‖u z‖ ^ 2)) μ :=
    (hD.const_mul (a * K)).fun_add (hQ.const_mul 8)
  -- On each tile the inequality of `mul_setIntegral_norm_sq_le_of_convex` holds with the same
  -- constant `K`; summing over the tiles gives it on `E`.
  set f : E → ℝ := fun z ↦ a * ‖u z‖ ^ 2 - (a * K * ‖fderiv ℝ u z‖ ^ 2 + 8 * (P z * ‖u z‖ ^ 2))
    with hf
  -- The integral of `f` against any measure `ν ≤ μ`, split into its three pieces.
  have hfν (ν : Measure E) (hν : ν ≤ μ) : ∫ z, f z ∂ν = a * ∫ z, ‖u z‖ ^ 2 ∂ν -
      (a * K * ∫ z, ‖fderiv ℝ u z‖ ^ 2 ∂ν + 8 * ∫ z, P z * ‖u z‖ ^ 2 ∂ν) := by
    rw [hf, integral_sub ((hI.const_mul a).mono_measure hν) (hR.mono_measure hν),
      integral_add ((hD.const_mul (a * K)).mono_measure hν) ((hQ.const_mul 8).mono_measure hν),
      integral_const_mul, integral_const_mul, integral_const_mul]
  have htile (g : G) : ∫ z in g +ᵥ T, f z ∂μ ≤ 0 := by
    -- The tile `g +ᵥ T` is the translate of `T` by the vector `g`.
    have hgT : g +ᵥ T = (g : E) +ᵥ T := rfl
    have hμ : μ ((g : E) +ᵥ T) = μ T := measure_vadd μ (g : E) T
    have hμr : μ.real ((g : E) +ᵥ T) = μ.real T := by simp [measureReal_def, hμ]
    have h := mul_setIntegral_norm_sq_le_of_convex (μ := μ) ha (hTc.vadd (g : E))
      (hTb.vadd (g : E)) (by rwa [hμ]) (by rw [hμ]; exact (mul_le_mul_right hBM 2).trans hTM)
      hP₀ haP hu hQ.integrableOn
    rw [diam_vadd, hμr, ← hK] at h
    rw [hgT, hfν _ Measure.restrict_le_self]
    linarith
  have hsum : ∫ z, f z ∂μ ≤ 0 :=
    (hT.integral_eq_tsum f ((hI.const_mul a).sub hR)).trans_le (tsum_nonpos htile)
  rw [hfν μ le_rfl] at hsum
  have hD₀ : 0 ≤ ∫ z, ‖fderiv ℝ u z‖ ^ 2 ∂μ := integral_nonneg fun _ ↦ by positivity
  have hQ₀ : 0 ≤ ∫ z, P z * ‖u z‖ ^ 2 ∂μ :=
    integral_nonneg_of_ae (hP₀.mono fun z hz ↦ by positivity)
  rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
  nlinarith [mul_nonneg (mul_nonneg ha.le hK₀) hQ₀, mul_nonneg (by norm_num : (0 : ℝ) ≤ 8) hD₀]

/-- **Poincaré inequality for a Schrödinger form.** Let `P` be locally integrable, almost
everywhere nonnegative, and almost everywhere at least `a > 0` outside the closed ball of radius
`R`. Then there is `c > 0` such that `c ∫ ‖u‖² ≤ ∫ ‖Du‖² + ∫ P ‖u‖²` for every compactly
supported `C¹` map `u`. The constant depends on `P` only through `a` and `R`. -/
theorem exists_pos_mul_integral_norm_sq_le_integral_norm_fderiv_sq_add_integral_mul_norm_sq
    {P : E → ℝ} (hP : LocallyIntegrable P μ) (hP₀ : ∀ᵐ z ∂μ, 0 ≤ P z) {a R : ℝ} (ha : 0 < a)
    (haP : ∀ᵐ z ∂μ, R < ‖z‖ → a ≤ P z) :
    ∃ c > 0, ∀ u : E → F, ContDiff ℝ 1 u → HasCompactSupport u →
      c * ∫ z, ‖u z‖ ^ 2 ∂μ ≤ ∫ z, ‖fderiv ℝ u z‖ ^ 2 ∂μ + ∫ z, P z * ‖u z‖ ^ 2 ∂μ := by
  obtain ⟨c, hc, h⟩ :=
    exists_pos_forall_mul_integral_norm_sq_le_integral_norm_fderiv_sq_add_integral_mul_norm_sq
      (μ := μ) (F := F) ha (measure_closedBall_lt_top (μ := μ) (x := (0 : E)) (r := R)).ne
  exact ⟨c, hc, h P _ hP hP₀ le_rfl
    (haP.mono fun z h hz ↦ h (by simpa only [mem_closedBall_zero_iff, not_le] using hz))⟩

end TestFunction

/-! ### The Schrödinger form on `H¹(E)` -/

section W1p

open Filter TopologicalSpace
open scoped InnerProductSpace RealInnerProductSpace Laplacian Distributions

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {P : E → ℝ}

/-- The **Schrödinger form** `(u, v) ↦ ∫ ⟪∇u, ∇v⟫ + ∫ P u v` of an essentially bounded potential
`P`, as a continuous bilinear form on `H¹(E) = W^{1,2}(E)`. It is the `L²` inner product of the
gradients plus the `L∞`-coefficient form `TauCeti.lpBilinearMap` of `P` on the values, pulled
back along `u ↦ (∇u, u)`. -/
noncomputable def schrodingerForm (hP : MemLp P ⊤ (volume : Measure E)) :
    W1p (volume : Measure E) ⊤ 2 →L[ℝ] W1p (volume : Measure E) ⊤ 2 →L[ℝ] ℝ :=
  let μ := (volume : Measure E).restrict (⊤ : Opens E)
  let fst := ContinuousLinearMap.fst ℝ (Lp E 2 μ) (Lp ℝ 2 μ)
  let snd := ContinuousLinearMap.snd ℝ (Lp E 2 μ) (Lp ℝ 2 μ)
  let J := W1p.gradientL.prod W1p.valueL
  let V := lpBilinearMap (p := 2) (q := 2) μ ((hP.restrict _).smul_mul.toLp _)
  ((innerSL ℝ).bilinearComp (σ₁₃ := RingHom.id ℝ) fst fst + V.bilinearComp snd snd).bilinearComp J J

/-- The Schrödinger form is the integral of `⟪∇u, ∇v⟫ + P u v`. -/
theorem schrodingerForm_apply (hP : MemLp P ⊤ (volume : Measure E))
    (u v : W1p (volume : Measure E) ⊤ 2) :
    schrodingerForm hP u v = (∫ z, ⟪W1p.gradient u z, W1p.gradient v z⟫) +
      ∫ z, P z * (W1p.value u z * W1p.value v z) := by
  simp only [schrodingerForm, ContinuousLinearMap.bilinearComp_apply, add_apply,
    ContinuousLinearMap.prod_apply, ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd',
    lpBilinearMap_apply, W1p.gradientL_apply, W1p.valueL_apply]
  rw [innerSL_apply_apply, L2.inner_def]
  have hB := MemLp.coeFn_toLp (E := ℝ →L[ℝ] ℝ →L[ℝ] ℝ)
    (hP.restrict ((⊤ : Opens E) : Set E)).smul_mul
  simp only [Opens.coe_top, Measure.restrict_univ] at hB ⊢
  congr 1
  refine integral_congr_ae ?_
  filter_upwards [hB] with z hz
  simp [hz]

/-- The Schrödinger form on the diagonal is `‖∇u‖₂² + ∫ P u²`. -/
theorem schrodingerForm_self (hP : MemLp P ⊤ (volume : Measure E))
    (u : W1p (volume : Measure E) ⊤ 2) :
    schrodingerForm hP u u = ‖W1p.gradient u‖ ^ 2 + ∫ z, P z * W1p.value u z ^ 2 := by
  rw [schrodingerForm_apply, ← W1p.integral_norm_gradient_sq_eq_norm_gradient_sq]
  simp only [Opens.coe_top, Measure.restrict_univ, real_inner_self_eq_norm_sq, sq]

/-- For `u ∈ H¹(E)`, testing `u` against `-Δφ + P φ` is the Schrödinger form of `u` and `φ`. -/
theorem integral_value_mul_eq_schrodingerForm (hP : MemLp P ⊤ (volume : Measure E))
    (u : W1p (volume : Measure E) ⊤ 2) (φ : 𝓓((⊤ : Opens E), ℝ)) :
    ∫ z, W1p.value u z * (-Δ (φ : E → ℝ) z + P z * φ z) =
      schrodingerForm hP u (W1p.ofTestFunctionₗ volume ⊤ 2 φ) := by
  have hu : MemLp (W1p.value u : E → ℝ) 2 volume := W1p.memLp_value u
  have hφ2 : MemLp (φ : E → ℝ) 2 volume :=
    φ.contDiff.continuous.memLp_of_hasCompactSupport φ.hasCompactSupport
  have hΔ2 : MemLp (Δ (φ : E → ℝ)) 2 volume :=
    (φ.contDiff.of_le (by simp)).continuous_laplacian.memLp_of_hasCompactSupport
      φ.hasCompactSupport.laplacian
  have hibp := (W1p.hasWeakFDerivOn u).integral_laplacian_smul_eq_neg_integral_inner φ
  simp only [smul_eq_mul] at hibp
  have hv := W1p.value_ofTestFunctionₗ_top_ae (mu := volume) (p := 2) φ
  have hg := W1p.gradient_ofTestFunctionₗ_top_ae (mu := volume) (p := 2) φ
  rw [schrodingerForm_apply]
  have e1 : ∫ z, W1p.value u z * (-Δ (φ : E → ℝ) z + P z * φ z) =
      -(∫ z, Δ (φ : E → ℝ) z * W1p.value u z) + ∫ z, P z * (W1p.value u z * φ z) := by
    rw [← integral_neg, ← integral_add (f := fun z ↦ -(Δ (φ : E → ℝ) z * W1p.value u z))
      (hΔ2.integrable_mul hu).neg
        (memLp_one_iff_integrable.1 (hP.fun_mul (hu.fun_mul hφ2 : MemLp _ 1 volume)))]
    exact integral_congr_ae (Eventually.of_forall fun z ↦ by ring)
  rw [e1, hibp, neg_neg]
  congr 1
  · refine integral_congr_ae (hg.mono fun z hz ↦ ?_)
    simp only [hz, real_inner_comm]
  · exact integral_congr_ae (hv.mono fun z hz ↦ by simp only [hz])

/-- The Poincaré inequality for the Schrödinger form, extended from test functions to all of
`H¹(E)` by density. -/
private theorem mul_norm_value_sq_le_schrodingerForm [Nontrivial E]
    (hP : MemLp P ⊤ (volume : Measure E)) (hP₀ : ∀ᵐ z ∂volume, 0 ≤ P z) {a R : ℝ} (ha : 0 < a)
    (hPa : ∀ᵐ z ∂volume, R < ‖z‖ → a ≤ P z) :
    ∃ c > 0, ∀ u : W1p (volume : Measure E) ⊤ 2,
      c * ‖W1p.value u‖ ^ 2 ≤ schrodingerForm hP u u := by
  obtain ⟨c, hc, hgap⟩ :=
    exists_pos_mul_integral_norm_sq_le_integral_norm_fderiv_sq_add_integral_mul_norm_sq
      (μ := volume) (F := ℝ) (hP.locallyIntegrable le_top) hP₀ ha hPa
  refine ⟨c, hc, fun u ↦ ?_⟩
  refine (W1p.denseRange_ofTestFunctionₗ_top (mu := volume) (p := 2) (by norm_num)).induction_on
    u (isClosed_le (continuous_const.mul
      (((W1p.valueL (mu := volume) (Omega := ⊤) (p := 2)).continuous.congr
        W1p.valueL_apply).norm.pow 2))
      ((schrodingerForm hP).continuous.clm_apply continuous_id)) fun φ ↦ ?_
  have hv := W1p.value_ofTestFunctionₗ_top_ae (mu := volume) (p := 2) φ
  rw [schrodingerForm_self, W1p.norm_value_ofTestFunctionₗ_top_sq,
    W1p.norm_gradient_ofTestFunctionₗ_top_sq]
  have h := hgap φ (φ.contDiff.of_le (by simp)) φ.hasCompactSupport
  simp only [Real.norm_eq_abs, sq_abs] at h
  convert h using 2
  exact integral_congr_ae (hv.mono fun z hz ↦ by simp only [hz])

/-- **The Poincaré inequality for a Schrödinger form on `H¹(E)`.** Let `P` be essentially
bounded, almost everywhere nonnegative, and almost everywhere at least `a > 0` outside the closed
ball of radius `R`. Then there is `c > 0` with `c ‖u‖²_{H¹} ≤ ‖∇u‖₂² + ∫ P u²` for every
`u ∈ H¹(E)`. -/
theorem exists_pos_mul_norm_sq_le_norm_gradient_sq_add_integral_mul_value_sq [Nontrivial E]
    (hP : MemLp P ⊤ (volume : Measure E)) (hP₀ : ∀ᵐ z ∂volume, 0 ≤ P z) {a R : ℝ} (ha : 0 < a)
    (hPa : ∀ᵐ z ∂volume, R < ‖z‖ → a ≤ P z) :
    ∃ c > 0, ∀ u : W1p (volume : Measure E) ⊤ 2,
      c * ‖u‖ ^ 2 ≤ ‖W1p.gradient u‖ ^ 2 + ∫ z, P z * W1p.value u z ^ 2 := by
  obtain ⟨c, hc, hgap⟩ := mul_norm_value_sq_le_schrodingerForm hP hP₀ ha hPa
  refine ⟨min 1 c / 2, by positivity, fun u ↦ ?_⟩
  have hgap := hgap u
  rw [schrodingerForm_self] at hgap
  have hpot : 0 ≤ ∫ z, P z * W1p.value u z ^ 2 :=
    integral_nonneg_of_ae (hP₀.mono fun z hz ↦ by positivity)
  have h1 : min 1 c ≤ 1 := min_le_left _ _
  have h2 : min 1 c ≤ c := min_le_right _ _
  have _ : 0 ≤ min 1 c := le_min zero_le_one hc.le
  rw [W1p.norm_sq_eq_norm_value_sq_add_norm_gradient_sq]
  nlinarith [sq_nonneg ‖W1p.value u‖, sq_nonneg ‖W1p.gradient u‖,
    mul_le_mul_of_nonneg_right h2 (sq_nonneg ‖W1p.value u‖),
    mul_le_mul_of_nonneg_right h1 (sq_nonneg ‖W1p.gradient u‖)]

/-- **Coercivity of the Schrödinger form.** Under the hypotheses of
`TauCeti.exists_pos_mul_norm_sq_le_norm_gradient_sq_add_integral_mul_value_sq`, the Schrödinger
form is coercive on `H¹(E)`. -/
theorem isCoercive_schrodingerForm [Nontrivial E] (hP : MemLp P ⊤ (volume : Measure E))
    (hP₀ : ∀ᵐ z ∂volume, 0 ≤ P z) {a R : ℝ} (ha : 0 < a)
    (hPa : ∀ᵐ z ∂volume, R < ‖z‖ → a ≤ P z) :
    IsCoercive (schrodingerForm hP) := by
  obtain ⟨c, hc, h⟩ :=
    exists_pos_mul_norm_sq_le_norm_gradient_sq_add_integral_mul_value_sq hP hP₀ ha hPa
  exact ⟨c, hc, fun u ↦ by rw [schrodingerForm_self, mul_assoc, ← sq]; exact h u⟩

end W1p

end TauCeti
