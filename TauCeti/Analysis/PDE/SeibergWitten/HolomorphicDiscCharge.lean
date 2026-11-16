/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.AlternatingForm
public import TauCeti.Analysis.InnerProductSpace.HodgeStar.Kahler.PositiveCone
public import TauCeti.Analysis.PDE.SeibergWitten.DiscCharge
import TauCeti.MeasureTheory.Group.Integral

/-!
# Charges of pseudoholomorphic discs are almost nonnegative

Let `(b, α)` be an abelian Higgs pair on a finite-dimensional real inner product space `V` with a
constant almost complex structure `J`, such as a flat chart of a symplectic four-manifold, and let
`Θ = i F_a + d(χ(|α|²) τ)` be its cutoff current (`TauCeti.SeibergWitten.cutoffCurrent`). A `C²`
disc `σ` whose boundary circle lies in `{χ(|α|²) = 1}` carries the integer charge
`(2π)⁻¹ ∫_D σ^* Θ` (`TauCeti.SeibergWitten.exists_int_integral_cutoffCurrent_comp_closedBall`).

If `σ` is `J`-holomorphic, `∂ₜσ = J ∂ₛσ`, then `σ^* Θ = Θ(∂ₛσ, J ∂ₛσ) ds ∧ dt`, and a positive
`(1,1)`-form is nonnegative on every complex line `v ∧ J v`. So when `Θ` is a positive
`(1,1)`-form at every point of the image of `σ`, the charge of `σ` is nonnegative. In Taubes's
analysis of the large-parameter Seiberg–Witten equations, `Θ` is only close to the cone of positive
`(1,1)`-forms in an integrated sense: `∫ dist(Θ, positiveCone) = O(h)` with `h = (2r)^(-1/2)`
(`TauCeti.SeibergWitten.integral_infDist_positiveCone_le`). The integral of a function over a
four-dimensional region does not control its integral along a two-dimensional disc, so this does
not bound the charge of a single disc directly.

The charge is, however, constant under translation as long as the boundary circles of the
translated discs `σ + p`, `‖p‖ ≤ δ`, stay in `{χ(|α|²) = 1}`
(`TauCeti.SeibergWitten.integral_cutoffCurrent_comp_add_closedBall_eq`). Averaging over these
translates spreads the disc over its `δ`-neighbourhood, and the pointwise bound
`Θ(v, J v) ≥ -dist(Θ, positiveCone) ‖v ∧ J v‖`
(`TauCeti.AlmostComplexStructure.neg_infDist_positiveCone_mul_le_inner_ιMulti`) then gives

`-(Area(σ) / Vol(B_δ)) ∫_{U_δ} dist(Θ, positiveCone) ≤ ∫_D σ^* Θ`,

where `Area(σ) = ∫_D ‖∂ₛσ ∧ ∂ₜσ‖` and `U_δ` is the closed `δ`-neighbourhood of `σ(D)`
(`TauCeti.SeibergWitten.neg_mul_div_le_integral_cutoffCurrent_comp_closedBall`). The constant
depends only on the disc and on `δ`.

Consequently, along a family of pairs whose cutoff currents approach the positive cone in
`L¹(U_δ)`, the integer charge of a fixed `J`-holomorphic disc is eventually nonnegative
(`TauCeti.SeibergWitten.eventually_nonneg_integral_cutoffCurrent_comp_closedBall`). When the
charges also stabilize, for instance because the cutoff currents converge as distributions
(`TauCeti.SeibergWitten.exists_int_eventually_integral_cutoffCurrent_comp_closedBall_eq`), their
eventual value is `2π n` for a natural number `n`
(`TauCeti.SeibergWitten.exists_nat_eventually_integral_cutoffCurrent_comp_closedBall_eq`).

This is the nonnegativity half of the positivity of the charges of holomorphic discs in Taubes's
reconstruction of pseudoholomorphic curves from Seiberg–Witten solutions; it says nothing about
discs meeting the limiting zero set, whose charge is expected to be strictly positive.

## Main results

* `TauCeti.SeibergWitten.neg_mul_le_setIntegral_closedBall_setIntegral_comp_add`: for any
  continuous two-form, the average of its pullbacks by the translates of a `J`-holomorphic disc is
  bounded below by its integrated distance to the positive cone.
* `TauCeti.SeibergWitten.neg_mul_div_le_integral_cutoffCurrent_comp_closedBall`: the lower bound
  for the charge of a `J`-holomorphic disc by the integrated distance of `Θ` to the positive cone.
* `TauCeti.SeibergWitten.eventually_nonneg_integral_cutoffCurrent_comp_closedBall`: the charges of a
  `J`-holomorphic disc are eventually nonnegative when the cutoff currents approach the cone.
* `TauCeti.SeibergWitten.exists_nat_eventually_integral_cutoffCurrent_comp_closedBall_eq`: if the
  cutoff currents moreover converge as distributions, the charges are eventually `2π n` with
  `n : ℕ`.

## References

* C. H. Taubes, *SW ⇒ Gr: from the Seiberg–Witten equations to pseudo-holomorphic curves*,
  J. Amer. Math. Soc. 9 (1996), 845–918.
-/

public section

noncomputable section

open Complex Filter Set MeasureTheory Metric exteriorPower
open scoped Topology Real ContDiff

namespace TauCeti.SeibergWitten

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V] {μ : Measure V} [μ.IsAddHaarMeasure]
  {J : AlmostComplexStructure V} {χ : ℝ → ℝ}

/-- The average of a continuous two-form `Θ` on a complex line `v ∧ J v` over the translates
`x + p`, `‖p‖ ≤ δ`, is at least `-‖v ∧ J v‖` times the integral of `dist(Θ, positiveCone)` over
any compact `U ⊇ closedBall x δ`. -/
private theorem neg_mul_le_setIntegral_closedBall_comp_add {Θ : V → V [⋀^Fin 2]→L[ℝ] ℝ}
    (hΘ : Continuous Θ) {x v w : V} (hw : w = J v) {δ : ℝ} {U : Set V} (hU : IsCompact U)
    (hxU : closedBall x δ ⊆ U) :
    -(‖ιMulti ℝ 2 ![v, w]‖ * ∫ y in U,
        infDist ((alternatingFormEquiv V 2).symm (Θ y)) (J.positiveCone : Set (⋀[ℝ]^2 V)) ∂μ) ≤
      ∫ p in closedBall (0 : V) δ, Θ (x + p) ![v, w] ∂μ := by
  subst hw
  set d : V → ℝ := fun y ↦
    infDist ((alternatingFormEquiv V 2).symm (Θ y)) (J.positiveCone : Set (⋀[ℝ]^2 V))
  have hd : Continuous d := (continuous_infDist_pt _).comp
    ((LinearMap.continuous_of_finiteDimensional (alternatingFormEquiv V 2).symm.toLinearMap).comp
      hΘ)
  -- The translates `x + p` fill `closedBall x δ ⊆ U`, where `d ≥ 0`.
  have hball : ∫ p in closedBall (0 : V) δ, d (x + p) ∂μ ≤ ∫ y in U, d y ∂μ := by
    have htr : ∫ y in closedBall x δ, d y ∂μ = ∫ p in closedBall (0 : V) δ, d (x + p) ∂μ := by
      rw [setIntegral_closedBall_eq_setIntegral_closedBall_zero_add d x δ]
      simp only [add_comm _ x]
    rw [← htr]
    exact setIntegral_mono_set (hd.continuousOn.integrableOn_compact hU)
      (Eventually.of_forall fun _ ↦ infDist_nonneg) (Eventually.of_forall fun _ hy ↦ hxU hy)
  -- Pointwise, `Θ(v, J v) ≥ -dist(Θ, positiveCone) ‖v ∧ J v‖`.
  have hpt (p : V) : -(‖ιMulti ℝ 2 ![v, J v]‖ * d (x + p)) ≤ Θ (x + p) ![v, J v] := by
    have h := AlmostComplexStructure.neg_infDist_positiveCone_mul_le_inner_ιMulti (J := J)
      ((alternatingFormEquiv V 2).symm (Θ (x + p))) v
    rw [inner_alternatingFormEquiv_symm_ιMulti] at h
    linarith
  calc -(‖ιMulti ℝ 2 ![v, J v]‖ * ∫ y in U, d y ∂μ)
      ≤ -(‖ιMulti ℝ 2 ![v, J v]‖ * ∫ p in closedBall (0 : V) δ, d (x + p) ∂μ) :=
        neg_le_neg (mul_le_mul_of_nonneg_left hball (norm_nonneg _))
    _ = ∫ p in closedBall (0 : V) δ, -(‖ιMulti ℝ 2 ![v, J v]‖ * d (x + p)) ∂μ := by
        rw [integral_neg, integral_const_mul]
    _ ≤ ∫ p in closedBall (0 : V) δ, Θ (x + p) ![v, J v] ∂μ :=
        setIntegral_mono_on (((hd.comp (continuous_const.add continuous_id)).continuousOn
          |>.integrableOn_compact (isCompact_closedBall _ _)).const_mul _ |>.neg)
          (((continuous_eval_const _).comp (hΘ.comp
            (continuous_const.add continuous_id))).continuousOn.integrableOn_compact
              (isCompact_closedBall _ _)) measurableSet_closedBall fun p _ ↦ hpt p

/-- **Averaged pullbacks of an approximately positive form by a pseudoholomorphic disc.** Let `Θ`
be a continuous two-form on `V` and `σ` a `C¹` disc, `J`-holomorphic on the closed disc `D` of
radius `r` about `z₀` (`∂ₜσ = J ∂ₛσ`). Integrating the pullbacks of `Θ` by the translated discs
`σ + p` over `‖p‖ ≤ δ` gives at least `-(∫_D ‖∂ₛσ ∧ ∂ₜσ‖)` times the integral of
`dist(Θ, positiveCone)` over the closed `δ`-neighbourhood `U_δ` of `σ(D)`:

`-(∫_D ‖∂ₛσ ∧ ∂ₜσ‖) (∫_{U_δ} dist(Θ, positiveCone) dμ) ≤ ∫_{B_δ} ∫_D Θ(σ z + p)(∂ₛσ, ∂ₜσ) dz dμ(p)`.

Here `Θ` is identified with a two-vector through the inner product. -/
theorem neg_mul_le_setIntegral_closedBall_setIntegral_comp_add
    {Θ : V → V [⋀^Fin 2]→L[ℝ] ℝ} (hΘ : Continuous Θ) {σ : ℂ → V} {z₀ : ℂ} {r : ℝ}
    (hσ : ContDiff ℝ 1 σ) (hhol : ∀ z ∈ closedBall z₀ r, fderiv ℝ σ z I = J (fderiv ℝ σ z 1))
    (δ : ℝ) :
    -((∫ z in closedBall z₀ r, ‖ιMulti ℝ 2 ![fderiv ℝ σ z 1, fderiv ℝ σ z I]‖) *
        ∫ y in cthickening δ (σ '' closedBall z₀ r),
          infDist ((alternatingFormEquiv V 2).symm (Θ y)) (J.positiveCone : Set (⋀[ℝ]^2 V)) ∂μ) ≤
      ∫ p in closedBall (0 : V) δ,
        (∫ z in closedBall z₀ r, Θ (σ z + p) ![fderiv ℝ σ z 1, fderiv ℝ σ z I]) ∂μ := by
  set t : ℂ → Fin 2 → V := fun z ↦ ![fderiv ℝ σ z 1, fderiv ℝ σ z I]
  have hDσ := hσ.continuous_fderiv one_ne_zero
  have ht : Continuous t := (hDσ.clm_apply continuous_const).matrixVecCons
    ((hDσ.clm_apply continuous_const).matrixVecCons continuous_const)
  have hA : Continuous fun z ↦ ‖ιMulti ℝ 2 (t z)‖ :=
    ((ιMulti ℝ 2 : V [⋀^Fin 2]→ₗ[ℝ] ⋀[ℝ]^2 V).toMultilinearMap.continuous_of_finiteDimensional.comp
      ht).norm
  have hint : Integrable (Function.uncurry fun p z ↦ Θ (σ z + p) (t z))
      ((μ.restrict (closedBall (0 : V) δ)).prod (volume.restrict (closedBall z₀ r))) := by
    rw [Measure.prod_restrict]
    exact (continuous_eval.comp ((hΘ.comp ((hσ.continuous.comp continuous_snd).add
      continuous_fst)).prodMk (ht.comp continuous_snd))).continuousOn.integrableOn_compact
        ((isCompact_closedBall _ _).prod (isCompact_closedBall _ _))
  -- Integrate over the translations first, and bound the inner integral at each point of the disc.
  rw [integral_integral_swap hint, ← integral_mul_const, ← integral_neg]
  exact setIntegral_mono_on ((hA.mul continuous_const).neg.continuousOn.integrableOn_compact
    (isCompact_closedBall _ _)) hint.integral_prod_right measurableSet_closedBall fun z hz ↦
      neg_mul_le_setIntegral_closedBall_comp_add hΘ (hhol z hz)
        ((isCompact_closedBall z₀ r).image hσ.continuous).cthickening
        (closedBall_subset_cthickening (mem_image_of_mem σ hz) δ)

/-- **The charge of a pseudoholomorphic disc is bounded below by the cone defect.** Let `σ` be a
`C²` disc, `J`-holomorphic on the closed disc `D` of radius `r` about `z₀` (`∂ₜσ = J ∂ₛσ`), such
that the boundary circles of all the translated discs `σ + p`, `‖p‖ ≤ δ` with `δ > 0`, lie in
`{χ(|α|²) = 1}`. Then, with `U_δ` the closed `δ`-neighbourhood of `σ(D)`,

`-(∫_D ‖∂ₛσ ∧ ∂ₜσ‖) (∫_{U_δ} dist(Θ, positiveCone) dμ) / μ(B_δ) ≤ ∫_D σ^* Θ`,

where `Θ` is the cutoff current, identified with a two-vector through the inner product. -/
theorem neg_mul_div_le_integral_cutoffCurrent_comp_closedBall {α : V → ℂ}
    {b : V → V [⋀^Fin 1]→L[ℝ] ℝ} {σ : ℂ → V} {z₀ : ℂ} {r δ : ℝ} (hδ : 0 < δ)
    (hα : ContDiff ℝ 2 α) (hb : ContDiff ℝ 1 b) (hχ : ContDiff ℝ 1 χ) (hχ₀ : χ =ᶠ[𝓝 0] 0)
    (hσ : ContDiff ℝ 2 σ) (hhol : ∀ z ∈ closedBall z₀ r, fderiv ℝ σ z I = J (fderiv ℝ σ z 1))
    (hbd : ∀ p ∈ closedBall (0 : V) δ, ∀ θ,
      χ (normSq (α (σ (circleMap z₀ r θ) + p))) = 1) :
    -((∫ z in closedBall z₀ r, ‖ιMulti ℝ 2 ![fderiv ℝ σ z 1, fderiv ℝ σ z I]‖) *
        (∫ y in cthickening δ (σ '' closedBall z₀ r),
          infDist ((alternatingFormEquiv V 2).symm (cutoffCurrent χ b α y))
            (J.positiveCone : Set (⋀[ℝ]^2 V)) ∂μ) / μ.real (closedBall (0 : V) δ)) ≤
      ∫ z in closedBall z₀ r,
        (cutoffCurrent χ b α (σ z)).compContinuousLinearMap (fderiv ℝ σ z) ![1, I] := by
  have hm : 0 < μ.real (closedBall (0 : V) δ) := by
    rw [measureReal_def]
    exact ENNReal.toReal_pos (measure_closedBall_pos μ 0 hδ).ne' measure_closedBall_lt_top.ne
  -- All the translated discs carry the charge of `σ`, so the averaged pullback of
  -- `neg_mul_le_setIntegral_closedBall_setIntegral_comp_add` is `μ(B_δ)` times the charge.
  have h := neg_mul_le_setIntegral_closedBall_setIntegral_comp_add (μ := μ)
    (contDiff_cutoffCurrent (m := 0) (n := 1) hα hb hχ hχ₀ (by norm_num)).continuous
    (hσ.of_le one_le_two) hhol δ
  rw [setIntegral_congr_fun measurableSet_closedBall fun p hp ↦
    integral_cutoffCurrent_comp_add_closedBall_eq hα hb hχ hχ₀ hσ hbd hp, setIntegral_const,
    smul_eq_mul] at h
  rw [← neg_div, div_le_iff₀ hm, mul_comm _ (μ.real _)]
  exact h

/-- **The charges of a pseudoholomorphic disc are eventually nonnegative.** Let `(bₖ, αₖ)` be a
family of abelian Higgs pairs along a filter `l`, and `σ` a `C²` disc, `J`-holomorphic on the
closed disc `D`, such that eventually the boundary circles of all the translated discs `σ + p`,
`‖p‖ ≤ δ` with `δ > 0`, lie in `{χ(|αₖ|²) = 1}`. If the cutoff currents `Θₖ` approach the cone of
positive `(1,1)`-forms in `L¹` on the closed `δ`-neighbourhood of `σ(D)`, then eventually
`∫_D σ^* Θₖ ≥ 0`. -/
theorem eventually_nonneg_integral_cutoffCurrent_comp_closedBall {ι : Type*} {l : Filter ι}
    {α : ι → V → ℂ} {b : ι → V → V [⋀^Fin 1]→L[ℝ] ℝ} {σ : ℂ → V} {z₀ : ℂ} {r δ : ℝ}
    (hδ : 0 < δ) (hα : ∀ k, ContDiff ℝ 2 (α k)) (hb : ∀ k, ContDiff ℝ 1 (b k))
    (hχ : ContDiff ℝ 1 χ) (hχ₀ : χ =ᶠ[𝓝 0] 0) (hσ : ContDiff ℝ 2 σ)
    (hhol : ∀ z ∈ closedBall z₀ r, fderiv ℝ σ z I = J (fderiv ℝ σ z 1))
    (hbd : ∀ᶠ k in l, ∀ p ∈ closedBall (0 : V) δ, ∀ θ,
      χ (normSq (α k (σ (circleMap z₀ r θ) + p))) = 1)
    (hcone : Tendsto (fun k ↦ ∫ y in cthickening δ (σ '' closedBall z₀ r),
      infDist ((alternatingFormEquiv V 2).symm (cutoffCurrent χ (b k) (α k) y))
        (J.positiveCone : Set (⋀[ℝ]^2 V)) ∂μ) l (𝓝 0)) :
    ∀ᶠ k in l, 0 ≤ ∫ z in closedBall z₀ r,
      (cutoffCurrent χ (b k) (α k) (σ z)).compContinuousLinearMap (fderiv ℝ σ z) ![1, I] := by
  rcases lt_or_ge r 0 with hr | hr
  · simp [closedBall_eq_empty.2 hr]
  -- The lower bound of `neg_mul_div_le_integral_cutoffCurrent_comp_closedBall` tends to `0`, so it
  -- eventually exceeds `-2π`, and the charges lie in `2πℤ`.
  have hlim := (((hcone.const_mul (∫ z in closedBall z₀ r,
    ‖ιMulti ℝ 2 ![fderiv ℝ σ z 1, fderiv ℝ σ z I]‖)).div_const
      (μ.real (closedBall (0 : V) δ))).neg)
  rw [mul_zero, zero_div, neg_zero] at hlim
  filter_upwards [hbd, hlim.eventually (lt_mem_nhds (neg_neg_of_pos Real.two_pi_pos))] with k hk hk'
  obtain ⟨n, -, hn⟩ := exists_int_integral_cutoffCurrent_comp_closedBall hr (hα k) (hb k) hχ
    hχ₀ hσ fun θ ↦ by simpa using hk 0 (mem_closedBall_self hδ.le) θ
  have hle := hk'.trans_le
    (neg_mul_div_le_integral_cutoffCurrent_comp_closedBall hδ (hα k) (hb k) hχ hχ₀ hσ hhol hk)
  rw [hn] at hle ⊢
  have hn₁ : (-1 : ℝ) < n := by nlinarith [Real.pi_pos]
  have hn₁' : (-1 : ℤ) < n := by exact_mod_cast hn₁
  have hn₀ : (0 : ℝ) ≤ n := by exact_mod_cast (show (0 : ℤ) ≤ n by omega)
  exact mul_nonneg Real.two_pi_pos.le hn₀

/-- **The stable charge of a pseudoholomorphic disc is a natural number.** In the setting of
`TauCeti.SeibergWitten.eventually_nonneg_integral_cutoffCurrent_comp_closedBall`, if moreover the
coefficients of the cutoff currents converge as distributions, then there is `n : ℕ` with
`∫_D σ^* Θₖ = 2π n` eventually along `l`. -/
theorem exists_nat_eventually_integral_cutoffCurrent_comp_closedBall_eq {ι : Type*}
    {l : Filter ι} [l.NeBot] {α : ι → V → ℂ} {b : ι → V → V [⋀^Fin 1]→L[ℝ] ℝ} {σ : ℂ → V}
    {z₀ : ℂ} {r δ : ℝ} (hδ : 0 < δ) (hα : ∀ k, ContDiff ℝ 2 (α k))
    (hb : ∀ k, ContDiff ℝ 1 (b k)) (hχ : ContDiff ℝ 1 χ) (hχ₀ : χ =ᶠ[𝓝 0] 0)
    (hσ : ContDiff ℝ 2 σ) (hhol : ∀ z ∈ closedBall z₀ r, fderiv ℝ σ z I = J (fderiv ℝ σ z 1))
    (hbd : ∀ᶠ k in l, ∀ p ∈ closedBall (0 : V) δ, ∀ θ,
      χ (normSq (α k (σ (circleMap z₀ r θ) + p))) = 1)
    (hcone : Tendsto (fun k ↦ ∫ y in cthickening δ (σ '' closedBall z₀ r),
      infDist ((alternatingFormEquiv V 2).symm (cutoffCurrent χ (b k) (α k) y))
        (J.positiveCone : Set (⋀[ℝ]^2 V)) ∂μ) l (𝓝 0))
    (hlim : ∀ φ : V → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → ∀ m : Fin 2 → V,
      ∃ L, Tendsto (fun k ↦ ∫ y, φ y * cutoffCurrent χ (b k) (α k) y m ∂μ) l (𝓝 L)) :
    ∃ n : ℕ, ∀ᶠ k in l, ∫ z in closedBall z₀ r,
      (cutoffCurrent χ (b k) (α k) (σ z)).compContinuousLinearMap (fderiv ℝ σ z) ![1, I] =
        2 * π * n := by
  rcases lt_or_ge r 0 with hr | hr
  · exact ⟨0, Eventually.of_forall fun _ ↦ by simp [closedBall_eq_empty.2 hr]⟩
  obtain ⟨n, hn⟩ := exists_int_eventually_integral_cutoffCurrent_comp_closedBall_eq hr hδ hα hb
    hχ hχ₀ hσ hbd hlim
  obtain ⟨k, hk, hk₀⟩ := (hn.and (eventually_nonneg_integral_cutoffCurrent_comp_closedBall hδ
    hα hb hχ hχ₀ hσ hhol hbd hcone)).exists
  rw [hk] at hk₀
  have hn₀ : 0 ≤ n := by exact_mod_cast nonneg_of_mul_nonneg_right hk₀ Real.two_pi_pos
  refine ⟨n.toNat, hn.mono fun k hk ↦ ?_⟩
  rw [hk, ← Int.cast_natCast, Int.toNat_of_nonneg hn₀]

end TauCeti.SeibergWitten
