/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Ellipticity.Basic
public import TauCeti.Analysis.PDE.MaximumPrinciple.AleksandrovBakelmanPucci.Basic
public import TauCeti.Analysis.Sobolev.Wkp.Basic
import TauCeti.Analysis.Calculus.Morse.Linearization
import TauCeti.Analysis.Matrix.Contraction
import TauCeti.Analysis.Normed.Module.FiniteDimension
import TauCeti.Analysis.Sobolev.Wkp.Local.UniformApproximation

/-!
# The Aleksandrov–Bakelman–Pucci estimate for strong solutions

Let `Ω ⊆ ℝⁿ = EuclideanSpace ℝ ι`, `n ≥ 1`, be bounded and open, and let `a` be a field of
symmetric matrices, uniformly elliptic on `Ω` with constants `λ ≤ Λ`. Let `v` be continuous on
`closure Ω` and lie in `W^{2,n}_loc(Ω)`, and suppose that

`f ≤ ∑ᵢⱼ aⁱʲ ∂ᵢ∂ⱼv` almost everywhere in `Ω`,

with the weak second derivatives of `v`. Local membership is expressed on every open `U` with
compact closure in `Ω`, by an element of `W^{2,n}(U)` that agrees with `v` almost everywhere on
`U` and satisfies the inequality almost everywhere on `U`. Write `D* = (det a)^{1/n}` and
`f⁻ = max (-f) 0`, and suppose `f⁻ / D* ∈ Lⁿ(Ω)`. If `v ≤ m` on `frontier Ω`, then on `Ω`

`v ≤ m + diam Ω / (n ωₙ^{1/n}) ‖f⁻ / D*‖_{Lⁿ(Ω)}`,

where `ωₙ` is the volume of the unit ball
(`TauCeti.PDE.le_add_mul_eLpNorm_negPart_div_det_rpow_of_wkp`; Gilbarg–Trudinger, Theorem 9.1,
without drift, where the norm is taken over the upper contact set rather than over `Ω`). This
is the maximum principle of the non-divergence theory with measurable coefficients: no continuity
of `a` is assumed, the only measurability used is that of `f⁻ / D*`, through its membership in
`Lⁿ(Ω)`, and no Sobolev regularity up to the boundary is assumed. It is the estimate behind the
Krylov–Safonov Harnack inequality for strong solutions.

## The argument

The estimate for `C²` functions is `TauCeti.PDE.le_add_mul_eLpNorm_negPart_div_det_rpow`. Its
differential inequality is required at every point of the upper contact set, which may be a null
set; `TauCeti.PDE.le_add_mul_eLpNorm_negPart_div_det_rpow_of_ae` first relaxes this to an
inequality almost everywhere on the upper contact set, keeping the `Lⁿ` norm over it, by
replacing `f` with `min f (∑ᵢⱼ aⁱʲ ∂ᵢ∂ⱼu)`.

For a strong solution, fix `ε > 0`. Since `v` is uniformly continuous on the compact set
`closure Ω` and `v ≤ m` on the frontier, `v ≤ m + ε` on a boundary layer
`{y ∈ Ω : dist(y, Ωᶜ) < ρ}` (`TauCeti.exists_pos_forall_infDist_compl_lt_le_add`). Inside it
lies the open set `V = {y : dist(y, Ωᶜ) > r}`, `r < ρ`, whose closure is a compact subset of
the open set `W = {y : dist(y, Ωᶜ) > r / 2}`, itself with compact closure in `Ω`. Mollifiers `w`
of `v` converge to `v` uniformly on `closure V`, and their Hessians converge in `Lⁿ` to the weak
Hessian `D²v` of the element of `W^{2,n}(W)` representing `v`
(`TauCeti.Wkp.exists_contDiff_tendstoUniformlyOn_tendsto_eLpNorm_iteratedGradientChain_sub`). As
`|aⁱʲ| ≤ Λ` and `D* ≥ λ`, the function `w` satisfies

`-(f⁻ / D* + n² Λ / λ ‖D²w - D²v‖) D* ≤ ∑ᵢⱼ aⁱʲ ∂ᵢ∂ⱼw` almost everywhere in `V`,

and is at most `m + 2ε` on `frontier V`. The almost-everywhere estimate on `V` bounds `w`, hence
`v`, up to errors that vanish with `ε` and the mollification radius.

## Main declarations

* `TauCeti.PDE.le_add_mul_eLpNorm_negPart_div_det_rpow_of_ae`: the Aleksandrov–Bakelman–Pucci
  estimate for `C²` functions satisfying the differential inequality almost everywhere.
* `TauCeti.PDE.le_add_mul_eLpNorm_negPart_div_det_rpow_of_wkp`: **the Aleksandrov–Bakelman–Pucci
  estimate for strong solutions** in `W^{2,n}_loc(Ω) ∩ C(closure Ω)`.

## References

* D. Gilbarg, N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  Section 9.1 (Theorem 9.1).
-/

public section

noncomputable section

open Filter InnerProductSpace Matrix Metric MeasureTheory Set Topology TopologicalSpace
open scoped ENNReal Gradient RealInnerProductSpace

namespace TauCeti

namespace PDE

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {Ω : Set (EuclideanSpace ℝ ι)}
  {u v f : EuclideanSpace ℝ ι → ℝ} {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ} {m lam Lam : ℝ}
  {x : EuclideanSpace ℝ ι}

/-- **The Aleksandrov–Bakelman–Pucci estimate with an almost-everywhere inequality.** Let `Ω` be
bounded and open, let `u` be continuous on `closure Ω` and `C²` in `Ω`, and let `m` bound `u` on
`frontier Ω`. Suppose that on the upper contact set `Γ⁺` the matrices `a y` are positive
definite and `f y ≤ ∑ᵢⱼ aⁱʲ(y) ∂ᵢ∂ⱼu(y)` for almost every `y`, and that `f⁻ / D*`, with
`D* = (det a)^{1/n}`, lies in `Lⁿ(Γ⁺)`. Then on `Ω`,
`u ≤ m + diam Ω / (n ωₙ^{1/n}) ‖f⁻ / D*‖_{Lⁿ(Γ⁺)}`. -/
theorem le_add_mul_eLpNorm_negPart_div_det_rpow_of_ae [Nonempty ι]
    (hΩb : Bornology.IsBounded Ω) (hΩ : IsOpen Ω) (hcont : ContinuousOn u (closure Ω))
    (hu : ContDiffOn ℝ 2 u Ω) (ha : ∀ y ∈ upperContactSet u Ω, (a y).PosDef)
    (hf : ∀ᵐ y ∂volume.restrict (upperContactSet u Ω), f y ≤ ∑ i, ∑ j, a y i j *
      fderiv ℝ (fderiv ℝ u) y (EuclideanSpace.single i 1) (EuclideanSpace.single j 1))
    (hg : MemLp (fun y => (f y)⁻ / (a y).det ^ (Fintype.card ι : ℝ)⁻¹) (Fintype.card ι)
      (volume.restrict (upperContactSet u Ω)))
    (hm : ∀ z ∈ frontier Ω, u z ≤ m) (hx : x ∈ Ω) :
    u x ≤ m + diam Ω / (Fintype.card ι *
        (volume (ball (0 : EuclideanSpace ℝ ι) 1)).toReal ^ (Fintype.card ι : ℝ)⁻¹) *
      (eLpNorm (fun y => (f y)⁻ / (a y).det ^ (Fintype.card ι : ℝ)⁻¹) (Fintype.card ι)
        (volume.restrict (upperContactSet u Ω))).toReal := by
  -- Replacing `f` by its minimum with the principal part changes it only on a null set.
  have hae : (fun y => (min (f y) (∑ i, ∑ j, a y i j * fderiv ℝ (fderiv ℝ u) y
      (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)))⁻ /
        (a y).det ^ (Fintype.card ι : ℝ)⁻¹) =ᵐ[volume.restrict (upperContactSet u Ω)]
      fun y => (f y)⁻ / (a y).det ^ (Fintype.card ι : ℝ)⁻¹ := by
    filter_upwards [hf] with y hy
    rw [min_eq_left hy]
  have h := le_add_mul_eLpNorm_negPart_div_det_rpow hΩb hΩ hcont hu ha
    (fun y _ => min_le_right _ _) (MemLp.ae_eq hae.symm hg) hm hx
  rwa [eLpNorm_congr_ae hae] at h

/-- The pointwise comparison between the principal parts of two Hessians `H₁` and `H₂`: if
`t ≤ ∑ᵢⱼ Aᵢⱼ ⟪H₂ eᵢ, eⱼ⟫`, the entries of `A` are bounded by `Λ` and `λ ≤ D`, then
`-(t⁻ / D + n² Λ / λ ‖H₁ - H₂‖) D ≤ ∑ᵢⱼ Aᵢⱼ ⟪H₁ eᵢ, eⱼ⟫`. -/
private theorem neg_mul_le_sum_mul_inner {A : Matrix ι ι ℝ}
    {H₁ H₂ : EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ ι} {t D : ℝ} (hLam : 0 ≤ Lam)
    (hA : ∀ i j, |A i j| ≤ Lam) (hlam : 0 < lam) (hD : lam ≤ D)
    (ht : t ≤ ∑ i, ∑ j, A i j *
      ⟪H₂ (EuclideanSpace.single i 1), EuclideanSpace.single j 1⟫_ℝ) :
    -((t⁻ / D + Fintype.card ι ^ 2 * Lam / lam * ‖H₁ - H₂‖) * D) ≤
      ∑ i, ∑ j, A i j * ⟪H₁ (EuclideanSpace.single i 1), EuclideanSpace.single j 1⟫_ℝ := by
  have hD0 : 0 < D := hlam.trans_le hD
  -- The two principal parts differ by the contraction of the form `⟪(H₁ - H₂) ·, ·⟫`.
  have herr := Matrix.abs_sum_sum_mul_apply_single_single_le hA ((innerSL ℝ).comp (H₁ - H₂))
  simp only [ContinuousLinearMap.comp_apply, innerSL_apply_apply, sub_apply,
    inner_sub_left, mul_sub, Finset.sum_sub_distrib] at herr
  have hB : Fintype.card ι ^ 2 * Lam * ‖(innerSL ℝ).comp (H₁ - H₂)‖ ≤
      Fintype.card ι ^ 2 * Lam * ‖H₁ - H₂‖ :=
    mul_le_mul_of_nonneg_left ((ContinuousLinearMap.opNorm_comp_le _ _).trans
      (mul_le_of_le_one_left (norm_nonneg _) (norm_innerSL_le ℝ))) (by positivity)
  have hK : Fintype.card ι ^ 2 * Lam * ‖H₁ - H₂‖ ≤
      Fintype.card ι ^ 2 * Lam / lam * ‖H₁ - H₂‖ * D := by
    rw [div_mul_eq_mul_div, div_mul_eq_mul_div, le_div_iff₀ hlam]
    have : 0 ≤ (Fintype.card ι : ℝ) ^ 2 * Lam * ‖H₁ - H₂‖ := by positivity
    nlinarith
  have hexp : (t⁻ / D + Fintype.card ι ^ 2 * Lam / lam * ‖H₁ - H₂‖) * D =
      t⁻ + Fintype.card ι ^ 2 * Lam / lam * ‖H₁ - H₂‖ * D := by
    field_simp
  rw [hexp]
  linarith [neg_le.1 (neg_le_negPart t), (abs_le.1 herr).1, hB]

/-- **One approximation step.** Let `a` be symmetric and uniformly elliptic on the bounded set `Ω`
with `f⁻ / D* ∈ Lⁿ(Ω)`, let `V ⊆ Ω` be open, and suppose that `f ≤ ∑ᵢⱼ aⁱʲ ⟪H eᵢ, eⱼ⟫` almost
everywhere on `V` for a field `H` of Hessians. If `w` is `C²`, then on `V`, `w` is at most its
frontier bound `m'` plus the right-hand side of the estimate, where the `Lⁿ` norm of `f⁻ / D*` is
enlarged by `n² Λ / λ` times the `Lⁿ(V)` distance between the Hessian of `w` and `H`. -/
private theorem le_add_mul_add_mul_eLpNorm_iteratedGradientChain_sub [Nonempty ι]
    [Fact (1 ≤ (Fintype.card ι : ℝ≥0∞))] (hΩb : Bornology.IsBounded Ω)
    (ha : UniformlyEllipticOn Ω a lam Lam) (ha_symm : ∀ y ∈ Ω, (a y).IsSymm)
    (hg : MemLp (fun y => (f y)⁻ / (a y).det ^ (Fintype.card ι : ℝ)⁻¹) (Fintype.card ι)
      (volume.restrict Ω))
    {V : Set (EuclideanSpace ℝ ι)} (hV : IsOpen V) (hVΩ : V ⊆ Ω)
    {H : EuclideanSpace ℝ ι → IteratedGradient (EuclideanSpace ℝ ι) 1}
    (hf : ∀ᵐ y ∂volume.restrict V, f y ≤ ∑ i, ∑ j, a y i j *
      ⟪H y (EuclideanSpace.single i 1), EuclideanSpace.single j 1⟫_ℝ)
    {w : EuclideanSpace ℝ ι → ℝ} (hw : ContDiff ℝ 2 w)
    (he : MemLp (fun y => iteratedGradientChain w 1 y - H y) (Fintype.card ι) (volume.restrict V))
    {m' : ℝ} (hm : ∀ z ∈ frontier V, w z ≤ m') (hx : x ∈ V) :
    w x ≤ m' + diam Ω / (Fintype.card ι *
        (volume (ball (0 : EuclideanSpace ℝ ι) 1)).toReal ^ (Fintype.card ι : ℝ)⁻¹) *
      ((eLpNorm (fun y => (f y)⁻ / (a y).det ^ (Fintype.card ι : ℝ)⁻¹) (Fintype.card ι)
          (volume.restrict Ω)).toReal + Fintype.card ι ^ 2 * Lam / lam *
        (eLpNorm (fun y => iteratedGradientChain w 1 y - H y)
          (Fintype.card ι) (volume.restrict V)).toReal) := by
  set n := Fintype.card ι
  set D : EuclideanSpace ℝ ι → ℝ := fun y => (a y).det ^ (n : ℝ)⁻¹
  set e := fun y => iteratedGradientChain w 1 y - H y
  set Kc : ℝ := n ^ 2 * Lam / lam
  set G : EuclideanSpace ℝ ι → ℝ := (fun y => (f y)⁻ / D y) + fun y => Kc * ‖e y‖
  have hKc : 0 ≤ Kc := div_nonneg (mul_nonneg (sq_nonneg _) ha.upper_nonneg) ha.pos.le
  have hD (y : EuclideanSpace ℝ ι) (hy : y ∈ Ω) : lam ≤ D y := by
    calc lam = (lam ^ n) ^ (n : ℝ)⁻¹ :=
          (Real.pow_rpow_inv_natCast ha.pos.le Fintype.card_ne_zero).symm
      _ ≤ D y := Real.rpow_le_rpow (pow_nonneg ha.pos.le _)
          (ha.pow_card_le_det hy (ha_symm y hy)) (by positivity)
  have hμ : volume.restrict V ≤ volume.restrict Ω := Measure.restrict_mono hVΩ le_rfl
  have hμc : volume.restrict (upperContactSet w V) ≤ volume.restrict V :=
    Measure.restrict_mono (fun y hy => upperContactSet_subset hy) le_rfl
  -- On `V`, the negative part of `-(G D*)` divided by `D*` is `G`.
  have hGeq : (fun y => (-(G y * D y))⁻ / D y) =ᵐ[volume.restrict V] G := by
    filter_upwards [ae_restrict_mem hV.measurableSet] with y hy
    have hD0 : 0 < D y := ha.pos.trans_le (hD y (hVΩ hy))
    have hG0 : 0 ≤ G y :=
      add_nonneg (div_nonneg (negPart_nonneg _) hD0.le) (mul_nonneg hKc (norm_nonneg _))
    rw [negPart_eq_neg'.2 (by simpa using mul_nonneg hG0 hD0.le), neg_neg,
      mul_div_cancel_right₀ _ hD0.ne']
  have h := le_add_mul_eLpNorm_negPart_div_det_rpow_of_ae (f := fun y => -(G y * D y))
    (hΩb.subset hVΩ) hV hw.continuous.continuousOn hw.contDiffOn
    (fun y hy => ha.posDef (hVΩ (upperContactSet_subset hy))
      (ha_symm y (hVΩ (upperContactSet_subset hy)))) (ae_mono hμc ?_)
    (MemLp.ae_eq (hGeq.filter_mono (ae_mono hμc)).symm
      (((hg.mono_measure hμ).add (he.norm.const_mul Kc)).mono_measure hμc)) hm hx
  · rw [eLpNorm_congr_ae (hGeq.filter_mono (ae_mono hμc))] at h
    refine h.trans (add_le_add le_rfl (mul_le_mul
      (div_le_div_of_nonneg_right (diam_mono hVΩ hΩb) (by positivity)) ?_ ENNReal.toReal_nonneg
      (div_nonneg diam_nonneg (by positivity))))
    have hKe : (fun y => Kc * ‖e y‖) = Kc • fun y => ‖e y‖ := by
      ext y
      rw [Pi.smul_apply, smul_eq_mul]
    -- Minkowski's inequality for `G = f⁻ / D* + Kc ‖e‖`.
    have hle : eLpNorm G n (volume.restrict (upperContactSet w V)) ≤
        eLpNorm (fun y => (f y)⁻ / D y) n (volume.restrict Ω) + ‖Kc‖ₑ * eLpNorm e n
          (volume.restrict V) := by
      refine (eLpNorm_mono_measure _ hμc).trans ((eLpNorm_add_le Fact.out).trans
        (add_le_add (eLpNorm_mono_measure _ hμ) (le_of_eq ?_)))
      rw [hKe, eLpNorm_const_smul, eLpNorm_norm e he.aestronglyMeasurable]
    refine (ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨hg.eLpNorm_ne_top,
      ENNReal.mul_ne_top enorm_ne_top he.eLpNorm_ne_top⟩) hle).trans_eq ?_
    rw [ENNReal.toReal_add hg.eLpNorm_ne_top (ENNReal.mul_ne_top enorm_ne_top he.eLpNorm_ne_top),
      ENNReal.toReal_mul, toReal_enorm, Real.norm_of_nonneg hKc]
  · -- The differential inequality for `w` on `V`, from that for `H` and the Hessian comparison.
    filter_upwards [hf, ae_restrict_mem hV.measurableSet] with y hfy hy
    refine (neg_mul_le_sum_mul_inner (H₁ := iteratedGradientChain w 1 y) ha.upper_nonneg
      (ha.abs_apply_le (hVΩ hy)) ha.pos (hD y (hVΩ hy)) hfy).trans_eq ?_
    -- `H₁` is typed as a continuous linear map, the unfolding of `IteratedGradient _ 1`, so
    -- the order-one identity is applied by `exact` rather than by rewriting.
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ =>
      congrArg (a y i j * ·) (inner_iteratedGradientChain_one_apply w y _ _)

/-- **The Aleksandrov–Bakelman–Pucci estimate for strong solutions** (Gilbarg–Trudinger,
Theorem 9.1 without drift). Let `Ω ⊆ ℝⁿ`, `n ≥ 1`, be bounded and open, and let `a` be symmetric
and uniformly elliptic on `Ω` with constants `λ ≤ Λ`. Let `v` be continuous on `closure Ω` with
`v ≤ m` on `frontier Ω`, and let `v ∈ W^{2,n}_loc(Ω)` satisfy `f ≤ ∑ᵢⱼ aⁱʲ ∂ᵢ∂ⱼv` almost
everywhere: on every open `U` with compact closure in `Ω` there is an element of `W^{2,n}(U)`
agreeing almost everywhere on `U` with `v` whose weak second derivatives satisfy the inequality
almost everywhere on `U`. If `f⁻ / D*`, with `D* = (det a)^{1/n}`, lies in `Lⁿ(Ω)`, then on `Ω`,
`v ≤ m + diam Ω / (n ωₙ^{1/n}) ‖f⁻ / D*‖_{Lⁿ(Ω)}`, where `ωₙ` is the volume of the unit ball. -/
theorem le_add_mul_eLpNorm_negPart_div_det_rpow_of_wkp [Nonempty ι]
    [Fact (1 ≤ (Fintype.card ι : ℝ≥0∞))] (hΩb : Bornology.IsBounded Ω) (hΩ : IsOpen Ω)
    (hv : ContinuousOn v (closure Ω))
    (hu : ∀ U : Opens (EuclideanSpace ℝ ι), IsCompact (closure (U : Set (EuclideanSpace ℝ ι))) →
      closure (U : Set (EuclideanSpace ℝ ι)) ⊆ Ω → ∃ uU : Wkp volume U (Fintype.card ι) 2,
        (Wkp.value 2 uU : EuclideanSpace ℝ ι → ℝ) =ᵐ[volume.restrict U] v ∧
        ∀ᵐ y ∂volume.restrict (U : Set (EuclideanSpace ℝ ι)), f y ≤ ∑ i, ∑ j, a y i j *
          ⟪Wkp.iteratedGradient 1 uU y (EuclideanSpace.single i 1), EuclideanSpace.single j 1⟫_ℝ)
    (ha : UniformlyEllipticOn Ω a lam Lam) (ha_symm : ∀ y ∈ Ω, (a y).IsSymm)
    (hg : MemLp (fun y => (f y)⁻ / (a y).det ^ (Fintype.card ι : ℝ)⁻¹) (Fintype.card ι)
      (volume.restrict Ω))
    (hm : ∀ z ∈ frontier Ω, v z ≤ m) (hx : x ∈ Ω) :
    v x ≤ m + diam Ω / (Fintype.card ι *
        (volume (ball (0 : EuclideanSpace ℝ ι) 1)).toReal ^ (Fintype.card ι : ℝ)⁻¹) *
      (eLpNorm (fun y => (f y)⁻ / (a y).det ^ (Fintype.card ι : ℝ)⁻¹) (Fintype.card ι)
        (volume.restrict Ω)).toReal := by
  set n := Fintype.card ι
  set C := diam Ω / (n * (volume (ball (0 : EuclideanSpace ℝ ι) 1)).toReal ^ (n : ℝ)⁻¹)
  set N := (eLpNorm (fun y => (f y)⁻ / (a y).det ^ (n : ℝ)⁻¹) n (volume.restrict Ω)).toReal
  set Kc : ℝ := n ^ 2 * Lam / lam
  have hC : 0 ≤ C := div_nonneg diam_nonneg (by positivity)
  have hKc : 0 ≤ Kc := div_nonneg (mul_nonneg (sq_nonneg _) ha.upper_nonneg) ha.pos.le
  refine le_of_forall_pos_le_add fun ε hε => ?_
  have hΩu : Ω ≠ univ := fun h => NormedSpace.unbounded_univ ℝ (EuclideanSpace ℝ ι) (h ▸ hΩb)
  -- `v ≤ m + ε / 4` on a boundary layer `{dist(·, Ωᶜ) < ρ}`.
  obtain ⟨ρ, hρ, hlayer⟩ := exists_pos_forall_infDist_compl_lt_le_add hΩb hΩu hv hm
    (by positivity : 0 < ε / 4)
  have hxd : 0 < infDist x Ωᶜ :=
    (hΩ.isClosed_compl.notMem_iff_infDist_pos (nonempty_compl.2 hΩu)).1 (notMem_compl_iff.2 hx)
  -- `V = {dist(·, Ωᶜ) > r}` contains `x`, and its closure lies in the compact `K ⊆ Ω`.
  set r := min (ρ / 2) (infDist x Ωᶜ / 2)
  have hr : 0 < r := lt_min (half_pos hρ) (half_pos hxd)
  set V : Set (EuclideanSpace ℝ ι) := {y | r < infDist y Ωᶜ}
  set K : Set (EuclideanSpace ℝ ι) := {y | r ≤ infDist y Ωᶜ}
  have hV : IsOpen V := isOpen_lt continuous_const (continuous_infDist_pt _)
  have hKc' : IsClosed K := isClosed_le continuous_const (continuous_infDist_pt _)
  have hKΩ : K ⊆ Ω := setOf_le_infDist_compl_subset hr
  have hK : IsCompact K := hΩb.isCompact_setOf_le_infDist_compl hr
  have hVK : V ⊆ K := ofPred_subset_ofPred.2 fun _ => le_of_lt
  have hxV : x ∈ V := (min_le_right _ _).trans_lt (half_lt_self hxd)
  -- The Sobolev hypothesis on `W = {dist(·, Ωᶜ) > r / 2}`, whose closure is compact in `Ω`.
  set W₀ : Set (EuclideanSpace ℝ ι) := {y | r / 2 < infDist y Ωᶜ}
  let W : Opens (EuclideanSpace ℝ ι) := ⟨W₀, isOpen_lt continuous_const (continuous_infDist_pt _)⟩
  have hW : (W : Set (EuclideanSpace ℝ ι)) = W₀ := Opens.coe_mk
  have hWcl : closure (W : Set (EuclideanSpace ℝ ι)) ⊆ {y | r / 2 ≤ infDist y Ωᶜ} := by
    rw [hW]
    exact closure_minimal (ofPred_subset_ofPred.2 fun _ => le_of_lt)
      (isClosed_le continuous_const (continuous_infDist_pt _))
  have hWΩ : closure (W : Set (EuclideanSpace ℝ ι)) ⊆ Ω :=
    hWcl.trans (setOf_le_infDist_compl_subset (half_pos hr))
  obtain ⟨uW, huW, hfW⟩ := hu W
    ((hΩb.isCompact_setOf_le_infDist_compl (half_pos hr)).of_isClosed_subset isClosed_closure hWcl)
    hWΩ
  have hKW : K ⊆ W := by
    rw [hW]
    exact ofPred_subset_ofPred.2 fun _ => (half_lt_self hr).trans_le
  -- Mollifiers `w j` of `v`, uniformly close to `v` on `K`, with Hessians close in `Lⁿ(K)`.
  obtain ⟨w, hw, hwv, hwe⟩ :=
    Wkp.exists_contDiff_tendstoUniformlyOn_tendsto_eLpNorm_iteratedGradientChain_sub
      (ENNReal.natCast_ne_top _) 1 uW
      (hv.mono fun y hy => subset_closure (hWΩ (subset_closure hy))) huW hK hKW
  set θ := ε / 4 / ((C + 1) * (Kc + 1))
  have hθ : 0 < θ := by positivity
  obtain ⟨j, hj, hje⟩ := ((Metric.tendstoUniformlyOn_iff.1 hwv (ε / 4) (by positivity)).and
    (hwe.eventually (gt_mem_nhds (ENNReal.ofReal_pos.2 hθ)))).exists
  have hw2 : ContDiff ℝ 2 (w j) := contDiff_infty.1 (hw j) 2
  have hμ : volume.restrict V ≤ volume.restrict K := Measure.restrict_mono hVK le_rfl
  have heV := (eLpNorm_mono_measure _ hμ).trans hje.le
  have he : MemLp (fun y => iteratedGradientChain (w j) 1 y - Wkp.iteratedGradient 1 uW y) n
      (volume.restrict V) :=
    heV.trans_lt ENNReal.ofReal_lt_top
  -- On `frontier V`, `w j ≤ v + ε / 4 ≤ m + ε / 2`.
  have hfr (z) (hz : z ∈ frontier V) : w j z ≤ m + ε / 4 + ε / 4 := by
    have hzK : z ∈ K := closure_minimal hVK hKc' (frontier_subset_closure hz)
    rw [hV.frontier_eq] at hz
    have hz1 := hlayer z (hKΩ hzK) ((not_lt.1 hz.2).trans_lt
      ((min_le_left _ _).trans_lt (half_lt_self hρ)))
    have hz2 := hj z hzK
    rw [Real.dist_eq] at hz2
    linarith [(abs_lt.1 hz2).1]
  have hstep := le_add_mul_add_mul_eLpNorm_iteratedGradientChain_sub hΩb ha ha_symm hg hV
    (hVK.trans hKΩ) (ae_mono (Measure.restrict_mono (hVK.trans hKW) le_rfl) hfW) hw2 he hfr hxV
  have hx' := hj x (hVK hxV)
  rw [Real.dist_eq] at hx'
  -- The Hessian error contributes at most `C Kc θ ≤ ε / 4`.
  have herr : C * (N + Kc * (eLpNorm (fun y => iteratedGradientChain (w j) 1 y -
      Wkp.iteratedGradient 1 uW y) n (volume.restrict V)).toReal) ≤ C * N + ε / 4 := by
    have h1 : (eLpNorm (fun y => iteratedGradientChain (w j) 1 y -
        Wkp.iteratedGradient 1 uW y) n (volume.restrict V)).toReal ≤ θ :=
      ENNReal.toReal_le_of_le_ofReal hθ.le heV
    have h2 : C * Kc * θ ≤ ε / 4 := by
      calc C * Kc * θ ≤ (C + 1) * (Kc + 1) * θ := by gcongr <;> nlinarith
        _ = ε / 4 := by simp only [θ]; field_simp
    nlinarith [mul_le_mul_of_nonneg_left h1 (mul_nonneg hC hKc)]
  linarith [(abs_lt.1 hx').2]

end PDE

end TauCeti
