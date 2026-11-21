/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.Young
public import TauCeti.Analysis.PDE.Caccioppoli.Truncation
public import TauCeti.Analysis.PDE.EnergyForm.Restriction
import TauCeti.MeasureTheory.Function.Lp.Norm

/-!
# The Caccioppoli inequality with lower-order terms

Let `u ∈ H¹(Ω)` be a weak subsolution of the full divergence-form equation

`-∂ᵢ(aⁱʲ ∂ⱼu) + bⁱ ∂ᵢu + c u ≤ f` in `Ω`,

that is, `a(u, v) ≤ ∫_Ω f v` for every nonnegative `v ∈ H¹₀(Ω)`, where `a(·, ·)` is the energy
form with drift `b` and mass coefficient `c`. Let `a` be measurable and uniformly elliptic with
constants `0 < λ ≤ Λ`, and let `b` and `c` be measurable and bounded, with `‖b‖ ≤ β`. For a level
`k` with `w = (u - k)⁺ ∈ L²(Ω)`, every smooth `ψ` compactly supported in `Ω` satisfies

`∫_Ω ψ² ‖∇w‖² ≤ 2 (2Λ/λ)² ∫_Ω ‖∇ψ‖² w² + (2β/λ)² ∫_Ω ψ² w² + (4/λ) ∫_Ω ψ² (f - c u) w`.

Moving the drift and mass terms to the right-hand side makes `u` a subsolution of the principal
part with the effective forcing `f - ⟪b, ∇u⟫ - c u`, so the principal-part inequality applies.
The drift is then absorbed into the left-hand side by Young's inequality, at the cost of the
zeroth-order term `(2β/λ)² ∫ ψ² w²`. The mass term is kept on the right-hand side next to the
forcing, where its sign is visible: under the sign condition `c ≥ 0` and at a level `k ≥ 0`, the
product `c u w` is nonnegative, because `w > 0` forces `u > k ≥ 0`, so the term can be dropped.
That is the form on concentric balls `B(x₀, r) ⊆ B(x₀, R) ⊆ Ω` for subsolutions of `L u ≤ 0`:

`∫_{B(x₀, r)} ‖∇w‖² ≤ (2 (2Λ/λ)² (C/(R - r))² + (2β/λ)²) ∫_{B(x₀, R)} w²`,

with `C` depending only on the dimension. Unlike the principal-part inequality
`TauCeti.PDE.exists_setIntegral_ball_norm_gradient_posPartAbove_sq_le`, this is not invariant
under dilations: the drift term is comparable to the cutoff term only on balls with `βR/λ`
bounded. This is the energy estimate that De Giorgi's iteration needs for equations with
lower-order terms. The boundedness hypothesis on `c` serves only to make the energy form
integrable.

For a weak solution `u` of `-∂ᵢ(aⁱʲ ∂ⱼu) + bⁱ ∂ᵢu + c u = f` itself, testing against `ψ² u` and
absorbing the drift in the same way bounds the mass term by `γ ∫ ψ² u²` whatever the sign of `c`:

`∫_Ω ψ² ‖∇u‖² ≤ 2 (2Λ/λ)² ∫_Ω ‖∇ψ‖² u² + ((2β/λ)² + 4γ/λ) ∫_Ω ψ² u² + (4/λ) ∫_Ω ψ² f u`,

and on concentric balls Young's inequality splits the forcing term into `u²` and `f²`. This is
the gradient bound that turns interior regularity estimates in terms of `f`, `∇u` and `u` into
estimates in terms of `f` and `u` alone.

## Main declarations

All seven are in the namespace `TauCeti.PDE`.

* `UniformlyEllipticOn.setIntegral_sq_mul_norm_gradient_posPartAbove_sq_le_lowerOrder_of_memLp`:
  Caccioppoli's inequality for `(u - k)⁺` at an arbitrary level with an `L²` hypothesis.
* `UniformlyEllipticOn.setIntegral_sq_mul_norm_gradient_posPartAbove_sq_le_lowerOrder`: the
  nonnegative-level specialization, whose `L²` hypothesis is automatic.
* `UniformlyEllipticOn.setIntegral_sq_mul_norm_gradient_posPartAbove_sq_le_lowerOrder_of_nonpos`:
  the cutoff form for subsolutions of `L u ≤ 0` with `c ≥ 0`, at a level `k ≥ 0`, where the
  forcing and mass term drop out.
* `exists_setIntegral_ball_norm_gradient_posPartAbove_sq_le_lowerOrder`: the form on
  concentric balls for subsolutions of `L u ≤ 0` with `c ≥ 0`.
* `UniformlyEllipticOn.setIntegral_sq_mul_norm_gradient_sq_le_lowerOrder`: Caccioppoli's
  inequality for weak solutions with lower-order terms and no sign condition on `c`.
* `exists_setIntegral_ball_norm_gradient_sq_le_lowerOrder`: its form on concentric balls.
* `exists_sq_toReal_eLpNorm_gradient_ball_le`: the same in terms of `L²` norms on the balls, for
  coefficients controlled on the outer ball only.

## References

* D. Gilbarg, N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  §8.5 and §8.6.
* Q. Han, F. Lin, *Elliptic Partial Differential Equations*, Chapter 4.
-/

public section

noncomputable section

open Filter MeasureTheory Matrix Metric Set TopologicalSpace
open scoped ContDiff Gradient InnerProductSpace

namespace TauCeti

namespace PDE

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {mu : Measure (EuclideanSpace ℝ ι)}
  [mu.IsAddHaarMeasure] {Omega : Opens (EuclideanSpace ℝ ι)}
  {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ} {b : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι}
  {c : EuclideanSpace ℝ ι → ℝ} {lam Lam beta gamma : ℝ}

/-- Moving the drift and mass terms to the right-hand side: a weak subsolution of the full
equation with forcing `f` is a weak subsolution of the principal part with the effective forcing
`f - c u - ⟪b, ∇u⟫`. -/
private theorem UniformlyEllipticOn.energyFormH1_zero_zero_le_of_lowerOrder
    (h : UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ ι)) a lam Lam)
    (ha : AEStronglyMeasurable a (mu.restrict Omega))
    {f : Lp ℝ 2 (mu.restrict Omega)} {u : W1p mu Omega 2}
    (hu : ∀ v : W1p0 mu Omega 2,
      (∀ᵐ x ∂mu.restrict Omega, 0 ≤ W1p.value (v : W1p mu Omega 2) x) →
        energyFormH1 a b c u (v : W1p mu Omega 2) ≤
          ∫ x in Omega, f x * W1p.value (v : W1p mu Omega 2) x ∂mu)
    (hg : MemLp (fun x => f x - c x * W1p.value u x - ⟪b x, W1p.gradient u x⟫_ℝ) 2
      (mu.restrict Omega))
    (v : W1p0 mu Omega 2) (hv : ∀ᵐ x ∂mu.restrict Omega, 0 ≤ W1p.value (v : W1p mu Omega 2) x) :
    energyFormH1 a 0 0 u (v : W1p mu Omega 2) ≤
      ∫ x in Omega, hg.toLp _ x * W1p.value (v : W1p mu Omega 2) x ∂mu := by
  have hvLp := Lp.memLp (W1p.value (v : W1p mu Omega 2))
  have hE := h.integrable_energyIntegrand_jetField (b := 0) (c := 0) (beta := 0)
    (gamma := 0) ha aestronglyMeasurable_const aestronglyMeasurable_const
    (fun _ _ => by simp) (fun _ _ => by simp) u v
  have hfv : Integrable (fun x => f x * W1p.value (v : W1p mu Omega 2) x)
      (mu.restrict Omega) := (Lp.memLp f).integrable_mul hvLp
  have hBC : Integrable (fun x => ⟪b x, W1p.gradient u x⟫_ℝ * W1p.value (v : W1p mu Omega 2) x
      + c x * W1p.value u x * W1p.value (v : W1p mu Omega 2) x) (mu.restrict Omega) :=
    (hfv.sub (hg.integrable_mul hvLp)).congr (.of_forall fun x => by
      simp only [Pi.sub_apply, Pi.mul_apply]; ring)
  have hsplit : energyFormH1 a b c u (v : W1p mu Omega 2) =
      energyFormH1 a 0 0 u (v : W1p mu Omega 2) + ∫ x in Omega,
        (⟪b x, W1p.gradient u x⟫_ℝ * W1p.value (v : W1p mu Omega 2) x
          + c x * W1p.value u x * W1p.value (v : W1p mu Omega 2) x) ∂mu := by
    have hlower : Integrable (fun x => energyIntegrand 0 (b x) (c x) (jetField u x)
        (jetField (v : W1p mu Omega 2) x)) (mu.restrict Omega) := by
      simpa [energyIntegrand_apply, jetField_apply] using hBC
    -- Split off the lower-order part with `energyFormIntegral_principal_add_lowerOrder`, after
    -- writing the `H¹` form as `energyFormIntegral` and its vanishing coefficients as
    -- `fun _ => 0`, the form the split lemma uses.
    have hH1 : ∀ b' c', energyFormH1 a b' c' u (v : W1p mu Omega 2) =
        energyFormIntegral (mu.restrict Omega) a b' c' (jetField u)
          (jetField (v : W1p mu Omega 2)) := fun b' c' => by
      rw [energyFormH1_def, energyFormIntegral_def]
    rw [hH1, hH1, Pi.zero_def, Pi.zero_def, energyFormIntegral_principal_add_lowerOrder _ a b c
      _ _ (by simpa using hE) hlower, add_right_inj, energyFormIntegral_def]
    simp [energyIntegrand_apply, jetField_apply]
  have hforce : ∫ x in Omega, hg.toLp _ x * W1p.value (v : W1p mu Omega 2) x ∂mu =
      ∫ x in Omega, f x * W1p.value (v : W1p mu Omega 2) x ∂mu - ∫ x in Omega,
        (⟪b x, W1p.gradient u x⟫_ℝ * W1p.value (v : W1p mu Omega 2) x
          + c x * W1p.value u x * W1p.value (v : W1p mu Omega 2) x) ∂mu := by
    rw [← integral_sub hfv hBC]
    refine integral_congr_ae ?_
    filter_upwards [hg.coeFn_toLp] with x hx
    rw [hx]
    ring
  linarith [hu v hv]

omit [DecidableEq ι] in
/-- Young's inequality for the drift: for `w = (u - k)⁺` and `‖b‖ ≤ β` on `Ω`, the drift part of
the forcing `F - ⟪b, ∇u⟫`, tested against `ψ² w`, is at most `λ/4 · ∫ ψ² ‖∇w‖² + β²/λ · ∫ ψ² w²`
above the `F` part. -/
private theorem setIntegral_sq_mul_sub_inner_mul_posPartAbove_le (hlam : 0 < lam)
    (hb_bound : ∀ x ∈ (Omega : Set (EuclideanSpace ℝ ι)), ‖b x‖ ≤ beta)
    {F : EuclideanSpace ℝ ι → ℝ} (hF : MemLp F 2 (mu.restrict Omega)) {u : W1p mu Omega 2}
    (hg : MemLp (fun x => F x - ⟪b x, W1p.gradient u x⟫_ℝ) 2 (mu.restrict Omega)) {k : ℝ}
    (hwLp : MemLp (fun x => max (W1p.value u x - k) 0) 2 (mu.restrict Omega))
    {ψ : EuclideanSpace ℝ ι → ℝ} (hψ : ContDiff ℝ ∞ ψ) (hcpt : HasCompactSupport ψ) :
    let w := W1p.posPartAboveOfMemLp (by norm_num) k u hwLp
    ∫ x in Omega, ψ x ^ 2 * hg.toLp _ x * W1p.value w x ∂mu ≤
      ∫ x in Omega, ψ x ^ 2 * F x * W1p.value w x ∂mu
        + (lam / 4 * ∫ x in Omega, ψ x ^ 2 * ‖W1p.gradient w x‖ ^ 2 ∂mu
          + beta ^ 2 / lam * ∫ x in Omega, ψ x ^ 2 * W1p.value w x ^ 2 ∂mu) := by
  intro w
  obtain ⟨M, -, hψM, -⟩ := (hψ.of_le (by simp)).exists_abs_le_and_norm_gradient_le hcpt
  have hψ2 : AEStronglyMeasurable (fun x => ψ x ^ 2) (mu.restrict Omega) :=
    (hψ.continuous.pow 2).aestronglyMeasurable
  have hψ2M : ∀ᵐ x ∂mu.restrict Omega, ‖ψ x ^ 2‖ ≤ M ^ 2 := Eventually.of_forall fun x => by
    rw [Real.norm_eq_abs, abs_pow]
    exact pow_le_pow_left₀ (abs_nonneg _) (hψM x) 2
  have hX : Integrable (fun x => ψ x ^ 2 * ‖W1p.gradient w x‖ ^ 2) (mu.restrict Omega) :=
    (Lp.memLp (W1p.gradient w)).norm.integrable_sq.bdd_mul hψ2 hψ2M
  have hZ : Integrable (fun x => ψ x ^ 2 * W1p.value w x ^ 2) (mu.restrict Omega) :=
    (Lp.memLp (W1p.value w)).integrable_sq.bdd_mul hψ2 hψ2M
  have hFw : Integrable (fun x => ψ x ^ 2 * F x * W1p.value w x) (mu.restrict Omega) :=
    ((hF.integrable_mul (Lp.memLp (W1p.value w))).bdd_mul hψ2 hψ2M).congr
      (Eventually.of_forall fun x => by simp only [Pi.mul_apply]; ring)
  have hG : Integrable (fun x => ψ x ^ 2 * hg.toLp _ x * W1p.value w x) (mu.restrict Omega) :=
    (((Lp.memLp (hg.toLp _)).integrable_mul (Lp.memLp (W1p.value w))).bdd_mul hψ2
      hψ2M).congr (Eventually.of_forall fun x => by simp only [Pi.mul_apply]; ring)
  have hR : Integrable (fun x => lam / 4 * (ψ x ^ 2 * ‖W1p.gradient w x‖ ^ 2)
      + beta ^ 2 / lam * (ψ x ^ 2 * W1p.value w x ^ 2)) (mu.restrict Omega) :=
    (hX.const_mul _).add (hZ.const_mul _)
  refine (integral_mono_ae hG (hFw.add hR) ?_).trans_eq (by
    simp only [Pi.add_apply]
    rw [integral_add hFw hR, integral_add (hX.const_mul _) (hZ.const_mul _), integral_const_mul,
      integral_const_mul])
  -- On the active set `∇w = ∇u`; off it, `w` vanishes.
  filter_upwards [ae_restrict_mem Omega.isOpen.measurableSet, hg.coeFn_toLp,
    W1p.gradient_posPartAboveOfMemLp_ae (by norm_num) k u hwLp,
    W1p.value_posPartAboveOfMemLp_ae (by norm_num) k u hwLp] with x hx hgx hwg hwv
  have hactive : ⟪b x, W1p.gradient u x⟫_ℝ * W1p.value w x =
      ⟪b x, W1p.gradient w x⟫_ℝ * W1p.value w x := by
    by_cases hxu : k < W1p.value u x
    · have hxmem : x ∈ {y : EuclideanSpace ℝ ι | k < W1p.value u y} := hxu
      rw [hwg, Set.indicator_of_mem hxmem]
    · rw [hwv, max_eq_right (sub_nonpos.mpr (le_of_not_gt hxu)), mul_zero, mul_zero]
  have hyoung := two_mul_re_inner_le_add_mul_norm_sq (𝕜 := ℝ) (-(ψ x * W1p.value w x) • b x)
    (ψ x • W1p.gradient w x) (by positivity : (0 : ℝ) < 2 / lam)
  simp only [RCLike.re_to_real, real_inner_smul_left, real_inner_smul_right, norm_smul, mul_pow,
    Real.norm_eq_abs, sq_abs, inv_div] at hyoung
  have hb2 : (ψ x * W1p.value w x) ^ 2 * ‖b x‖ ^ 2 ≤ (ψ x * W1p.value w x) ^ 2 * beta ^ 2 :=
    mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) (hb_bound x hx) 2)
      (sq_nonneg _)
  rw [hgx, Pi.add_apply]
  linear_combination (hyoung + 2 / lam * hb2) / 2 - ψ x ^ 2 * hactive

/-- **The Caccioppoli inequality for a positive truncation of a weak subsolution with
lower-order terms.** Let `a` be measurable and uniformly elliptic on `Ω` with constants
`0 < λ ≤ Λ`, and let `b` and `c` be measurable with `‖b‖ ≤ β` and `‖c‖ ≤ γ` on `Ω`. Let
`u ∈ H¹(Ω)` satisfy

`a(u, v) ≤ ∫_Ω f v`

for every nonnegative `v ∈ H¹₀(Ω)`, where `a` is the energy form of
`-∂ᵢ(aⁱʲ ∂ⱼ ·) + bⁱ ∂ᵢ + c`. At any level `k` for which `w = (u - k)⁺` belongs to `L²(Ω)`, every
smooth `ψ` compactly supported in `Ω` satisfies

`∫_Ω ψ² ‖∇w‖² ≤ 2 (2Λ/λ)² ∫_Ω ‖∇ψ‖² w² + (2β/λ)² ∫_Ω ψ² w² + (4/λ) ∫_Ω ψ² (f - c u) w`.

The bound `γ` on the mass coefficient does not enter the estimate. -/
theorem
    UniformlyEllipticOn.setIntegral_sq_mul_norm_gradient_posPartAbove_sq_le_lowerOrder_of_memLp
    (h : UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ ι)) a lam Lam)
    (ha : AEStronglyMeasurable a (mu.restrict Omega))
    (hb : AEStronglyMeasurable b (mu.restrict Omega))
    (hc : AEStronglyMeasurable c (mu.restrict Omega))
    (hb_bound : ∀ x ∈ (Omega : Set (EuclideanSpace ℝ ι)), ‖b x‖ ≤ beta)
    (hc_bound : ∀ x ∈ (Omega : Set (EuclideanSpace ℝ ι)), ‖c x‖ ≤ gamma)
    {f : Lp ℝ 2 (mu.restrict Omega)} {u : W1p mu Omega 2}
    (hu : ∀ v : W1p0 mu Omega 2,
      (∀ᵐ x ∂mu.restrict Omega, 0 ≤ W1p.value (v : W1p mu Omega 2) x) →
        energyFormH1 a b c u (v : W1p mu Omega 2) ≤
          ∫ x in Omega, f x * W1p.value (v : W1p mu Omega 2) x ∂mu)
    {k : ℝ}
    (hwLp : MemLp (fun x => max (W1p.value u x - k) 0) 2 (mu.restrict Omega))
    {ψ : EuclideanSpace ℝ ι → ℝ} (hψ : ContDiff ℝ ∞ ψ)
    (hcpt : HasCompactSupport ψ) (hts : tsupport ψ ⊆ (Omega : Set (EuclideanSpace ℝ ι))) :
    let w := W1p.posPartAboveOfMemLp (by norm_num) k u hwLp
    ∫ x in Omega, ψ x ^ 2 * ‖W1p.gradient w x‖ ^ 2 ∂mu ≤
      2 * (2 * Lam / lam) ^ 2 * ∫ x in Omega, ‖∇ ψ x‖ ^ 2 * W1p.value w x ^ 2 ∂mu
        + (2 * beta / lam) ^ 2 * ∫ x in Omega, ψ x ^ 2 * W1p.value w x ^ 2 ∂mu
        + 4 / lam * ∫ x in Omega, ψ x ^ 2 * (f x - c x * W1p.value u x) * W1p.value w x ∂mu := by
  -- With the drift and mass terms moved to the right-hand side, `u` is a weak subsolution of
  -- the principal part with the effective forcing `g = f - c u - ⟪b, ∇u⟫`, so the
  -- principal-part inequality applies. The drift part of `∫ ψ² g w` is then bounded by Young's
  -- inequality and its gradient share absorbed into the left-hand side.
  dsimp only
  have hlam := h.pos
  have hB : MemLp (fun x => ⟪b x, W1p.gradient u x⟫_ℝ) 2 (mu.restrict Omega) :=
    MemLp.of_bilin (inner ℝ) 1 (memLp_top_of_bound hb beta
      (ae_restrict_of_forall_mem Omega.isOpen.measurableSet hb_bound)) (Lp.memLp _)
      continuous_inner
      (.of_forall fun x => by simpa using nnNorm_inner_le_nnNorm (b x) (W1p.gradient u x))
  have hC : MemLp (fun x => c x * W1p.value u x) 2 (mu.restrict Omega) :=
    (memLp_top_of_bound hc gamma (ae_restrict_of_forall_mem Omega.isOpen.measurableSet
      hc_bound)).fun_mul (Lp.memLp _)
  have hF : MemLp (fun x => f x - c x * W1p.value u x) 2 (mu.restrict Omega) :=
    (Lp.memLp f).sub hC
  have hg : MemLp (fun x => f x - c x * W1p.value u x - ⟪b x, W1p.gradient u x⟫_ℝ) 2
      (mu.restrict Omega) := hF.sub hB
  have hcacc := h.setIntegral_sq_mul_norm_gradient_posPartAbove_sq_le_of_memLp ha
    (h.energyFormH1_zero_zero_le_of_lowerOrder ha hu hg) hwLp hψ hcpt hts
  have hdrift := setIntegral_sq_mul_sub_inner_mul_posPartAbove_le hlam hb_bound hF hg hwLp hψ hcpt
  dsimp only at hcacc hdrift
  -- Absorb the drift's quarter of the gradient term into the left-hand side.
  set w := W1p.posPartAboveOfMemLp (by norm_num) k u hwLp
  set X := ∫ x in Omega, ψ x ^ 2 * ‖W1p.gradient w x‖ ^ 2 ∂mu
  set Z := ∫ x in Omega, ψ x ^ 2 * W1p.value w x ^ 2 ∂mu
  set F := ∫ x in Omega, ψ x ^ 2 * (f x - c x * W1p.value u x) * W1p.value w x ∂mu
  have hsplit : 2 / lam * (F + (lam / 4 * X + beta ^ 2 / lam * Z)) =
      2 / lam * F + X / 2 + (2 * beta / lam) ^ 2 / 2 * Z := by
    field_simp
    ring
  have h4 : 4 / lam * F = 2 * (2 / lam * F) := by ring
  have hmono := mul_le_mul_of_nonneg_left hdrift (by positivity : (0 : ℝ) ≤ 2 / lam)
  rw [hsplit] at hmono
  linarith

/-- **The Caccioppoli inequality for a nonnegative-level truncation of a weak subsolution with
lower-order terms.** This specializes
`UniformlyEllipticOn.setIntegral_sq_mul_norm_gradient_posPartAbove_sq_le_lowerOrder_of_memLp`;
the condition `k ≥ 0` makes `(u - k)⁺ ∈ L²(Ω)` automatic even when `Ω` has infinite measure. -/
theorem UniformlyEllipticOn.setIntegral_sq_mul_norm_gradient_posPartAbove_sq_le_lowerOrder
    (h : UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ ι)) a lam Lam)
    (ha : AEStronglyMeasurable a (mu.restrict Omega))
    (hb : AEStronglyMeasurable b (mu.restrict Omega))
    (hc : AEStronglyMeasurable c (mu.restrict Omega))
    (hb_bound : ∀ x ∈ (Omega : Set (EuclideanSpace ℝ ι)), ‖b x‖ ≤ beta)
    (hc_bound : ∀ x ∈ (Omega : Set (EuclideanSpace ℝ ι)), ‖c x‖ ≤ gamma)
    {f : Lp ℝ 2 (mu.restrict Omega)} {u : W1p mu Omega 2}
    (hu : ∀ v : W1p0 mu Omega 2,
      (∀ᵐ x ∂mu.restrict Omega, 0 ≤ W1p.value (v : W1p mu Omega 2) x) →
        energyFormH1 a b c u (v : W1p mu Omega 2) ≤
          ∫ x in Omega, f x * W1p.value (v : W1p mu Omega 2) x ∂mu)
    {k : ℝ} (hk : 0 ≤ k) {ψ : EuclideanSpace ℝ ι → ℝ} (hψ : ContDiff ℝ ∞ ψ)
    (hcpt : HasCompactSupport ψ) (hts : tsupport ψ ⊆ (Omega : Set (EuclideanSpace ℝ ι))) :
    let w := W1p.posPartAbove (by norm_num) hk u
    ∫ x in Omega, ψ x ^ 2 * ‖W1p.gradient w x‖ ^ 2 ∂mu ≤
      2 * (2 * Lam / lam) ^ 2 * ∫ x in Omega, ‖∇ ψ x‖ ^ 2 * W1p.value w x ^ 2 ∂mu
        + (2 * beta / lam) ^ 2 * ∫ x in Omega, ψ x ^ 2 * W1p.value w x ^ 2 ∂mu
        + 4 / lam * ∫ x in Omega, ψ x ^ 2 * (f x - c x * W1p.value u x) * W1p.value w x ∂mu := by
  have hgeneral := h.setIntegral_sq_mul_norm_gradient_posPartAbove_sq_le_lowerOrder_of_memLp
    ha hb hc hb_bound hc_bound hu (W1p.memLp_posPartAbove hk u) hψ hcpt hts
  rw [W1p.posPartAboveOfMemLp_eq_posPartAbove (by norm_num) hk u
    (W1p.memLp_posPartAbove hk u)] at hgeneral
  exact hgeneral

/-- **The zero-forcing Caccioppoli inequality for a nonnegative-level truncation with
lower-order terms.** Let `a` be measurable and uniformly elliptic on `Ω` with constants
`0 < λ ≤ Λ`, let `b` and `c` be measurable with `‖b‖ ≤ β`, `‖c‖ ≤ γ` and `c ≥ 0` on `Ω`, and let
`u ∈ H¹(Ω)` be a weak subsolution of `-∂ᵢ(aⁱʲ ∂ⱼu) + bⁱ ∂ᵢu + c u ≤ 0`. At any level `k ≥ 0`,
with `w = (u - k)⁺`, every smooth `ψ` compactly supported in `Ω` satisfies

`∫_Ω ψ² ‖∇w‖² ≤ 2 (2Λ/λ)² ∫_Ω ‖∇ψ‖² w² + (2β/λ)² ∫_Ω ψ² w²`.

This specializes
`UniformlyEllipticOn.setIntegral_sq_mul_norm_gradient_posPartAbove_sq_le_lowerOrder`: the
mass term `c u w` is nonnegative because `w > 0` forces `u > k ≥ 0`. -/
theorem
    UniformlyEllipticOn.setIntegral_sq_mul_norm_gradient_posPartAbove_sq_le_lowerOrder_of_nonpos
    (h : UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ ι)) a lam Lam)
    (ha : AEStronglyMeasurable a (mu.restrict Omega))
    (hb : AEStronglyMeasurable b (mu.restrict Omega))
    (hc : AEStronglyMeasurable c (mu.restrict Omega))
    (hb_bound : ∀ x ∈ (Omega : Set (EuclideanSpace ℝ ι)), ‖b x‖ ≤ beta)
    (hc_bound : ∀ x ∈ (Omega : Set (EuclideanSpace ℝ ι)), ‖c x‖ ≤ gamma)
    (hc_nonneg : ∀ x ∈ (Omega : Set (EuclideanSpace ℝ ι)), 0 ≤ c x) {u : W1p mu Omega 2}
    (hu : ∀ v : W1p0 mu Omega 2,
      (∀ᵐ x ∂mu.restrict Omega, 0 ≤ W1p.value (v : W1p mu Omega 2) x) →
        energyFormH1 a b c u (v : W1p mu Omega 2) ≤ 0)
    {k : ℝ} (hk : 0 ≤ k) {ψ : EuclideanSpace ℝ ι → ℝ} (hψ : ContDiff ℝ ∞ ψ)
    (hcpt : HasCompactSupport ψ) (hts : tsupport ψ ⊆ (Omega : Set (EuclideanSpace ℝ ι))) :
    let w := W1p.posPartAbove (by norm_num) hk u
    ∫ x in Omega, ψ x ^ 2 * ‖W1p.gradient w x‖ ^ 2 ∂mu ≤
      2 * (2 * Lam / lam) ^ 2 * ∫ x in Omega, ‖∇ ψ x‖ ^ 2 * W1p.value w x ^ 2 ∂mu
        + (2 * beta / lam) ^ 2 * ∫ x in Omega, ψ x ^ 2 * W1p.value w x ^ 2 ∂mu := by
  have hcacc := h.setIntegral_sq_mul_norm_gradient_posPartAbove_sq_le_lowerOrder ha hb hc
    hb_bound hc_bound (f := 0) (fun v hv => (hu v hv).trans_eq (integral_eq_zero_of_ae (by
      filter_upwards [Lp.coeFn_zero ℝ 2 (mu.restrict Omega)] with x hx
      rw [hx, Pi.zero_apply, zero_mul])).symm) hk hψ hcpt hts
  dsimp only at hcacc ⊢
  set w := W1p.posPartAbove (by norm_num) hk u
  have hmem : ∀ᵐ x ∂mu.restrict Omega, x ∈ (Omega : Set (EuclideanSpace ℝ ι)) :=
    ae_restrict_mem Omega.isOpen.measurableSet
  -- Under `c ≥ 0` and `k ≥ 0`, the mass term `c u w` is nonnegative, so the forcing term is not.
  have hforce : ∫ x in Omega, ψ x ^ 2 * ((0 : Lp ℝ 2 (mu.restrict Omega)) x -
      c x * W1p.value u x) * W1p.value w x ∂mu ≤ 0 := by
    refine integral_nonpos_of_ae ?_
    filter_upwards [hmem, W1p.value_posPartAbove_ae (by norm_num) hk u,
      Lp.coeFn_zero ℝ 2 (mu.restrict Omega)] with x hx hwx hzero
    rw [hwx, hzero, Pi.zero_apply, zero_sub]
    by_cases hxu : k < W1p.value u x
    · have hcu : 0 ≤ c x * W1p.value u x := mul_nonneg (hc_nonneg x hx) (by linarith)
      exact mul_nonpos_of_nonpos_of_nonneg
        (mul_nonpos_of_nonneg_of_nonpos (sq_nonneg _) (neg_nonpos.2 hcu)) (le_max_right _ _)
    · rw [max_eq_right (sub_nonpos.2 (le_of_not_gt hxu)), mul_zero]
  have hlam := h.pos
  linarith [mul_nonpos_of_nonneg_of_nonpos (by positivity : (0 : ℝ) ≤ 4 / lam) hforce]

/-- **The Caccioppoli inequality on concentric balls, with lower-order terms.** There is a
constant `C > 0`, depending only on the dimension, such that the following holds for every
additive Haar measure `μ`. Let `a` be measurable and uniformly elliptic on `Ω` with constants
`0 < λ ≤ Λ`, let `b` and `c` be measurable with `‖b‖ ≤ β`, `‖c‖ ≤ γ` and `c ≥ 0` on `Ω`, and let
`u ∈ H¹(Ω)` be a weak subsolution of `-∂ᵢ(aⁱʲ ∂ⱼu) + bⁱ ∂ᵢu + c u ≤ 0`. At any level `k ≥ 0`,
with `w = (u - k)⁺`, and for every pair of balls `B(x₀, r) ⊆ B(x₀, R) ⊆ Ω` with `r < R`,

`∫_{B(x₀, r)} ‖∇w‖² ≤ (2 (2Λ/λ)² (C / (R - r))² + (2β/λ)²) ∫_{B(x₀, R)} w²`. -/
theorem exists_setIntegral_ball_norm_gradient_posPartAbove_sq_le_lowerOrder :
    ∃ C : ℝ, 0 < C ∧ ∀ {mu : Measure (EuclideanSpace ℝ ι)} [mu.IsAddHaarMeasure]
      {Omega : Opens (EuclideanSpace ℝ ι)} {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ}
      {b : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι} {c : EuclideanSpace ℝ ι → ℝ}
      {lam Lam beta gamma : ℝ} {u : W1p mu Omega 2} {k : ℝ} (hk : 0 ≤ k)
      {x₀ : EuclideanSpace ℝ ι} {r R : ℝ},
      UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ ι)) a lam Lam →
      AEStronglyMeasurable a (mu.restrict Omega) →
      AEStronglyMeasurable b (mu.restrict Omega) →
      AEStronglyMeasurable c (mu.restrict Omega) →
      (∀ x ∈ (Omega : Set (EuclideanSpace ℝ ι)), ‖b x‖ ≤ beta) →
      (∀ x ∈ (Omega : Set (EuclideanSpace ℝ ι)), ‖c x‖ ≤ gamma) →
      (∀ x ∈ (Omega : Set (EuclideanSpace ℝ ι)), 0 ≤ c x) →
      (∀ v : W1p0 mu Omega 2,
        (∀ᵐ x ∂mu.restrict Omega, 0 ≤ W1p.value (v : W1p mu Omega 2) x) →
          energyFormH1 a b c u (v : W1p mu Omega 2) ≤ 0) →
      r < R → ball x₀ R ⊆ (Omega : Set (EuclideanSpace ℝ ι)) →
      ∫ x in ball x₀ r, ‖W1p.gradient (W1p.posPartAbove (by norm_num) hk u) x‖ ^ 2 ∂mu ≤
        (2 * (2 * Lam / lam) ^ 2 * (C / (R - r)) ^ 2 + (2 * beta / lam) ^ 2) *
          ∫ x in ball x₀ R, max (W1p.value u x - k) 0 ^ 2 ∂mu := by
  obtain ⟨C, hC0, hC⟩ := exists_setIntegral_ball_norm_gradient_sq_le_of_cutoff (ι := ι)
  refine ⟨C, hC0, ?_⟩
  intro mu _ Omega a b c lam Lam beta gamma u k hk x₀ r R h ha hb hc hb_bound hc_bound hc_nonneg
    hu hrR hball
  -- Caccioppoli's inequality for `w`, with the forcing and mass term dropped, localized to the
  -- balls.
  have hloc := hC (W1p.posPartAbove (by norm_num) hk u) (A := 2 * (2 * Lam / lam) ^ 2)
    (B := (2 * beta / lam) ^ 2) (by positivity) (sq_nonneg _) hrR hball
    fun ψ hψ hcpt hts =>
      h.setIntegral_sq_mul_norm_gradient_posPartAbove_sq_le_lowerOrder_of_nonpos ha hb hc
        hb_bound hc_bound hc_nonneg hu hk hψ hcpt hts
  refine hloc.trans_eq ?_
  rw [integral_congr_ae (ae_restrict_of_ae_restrict_of_subset hball (by
    filter_upwards [W1p.value_posPartAbove_ae (by norm_num) hk u] with x hx
    rw [hx]))]

/-! ### Weak solutions with lower-order terms -/

omit [DecidableEq ι] in
/-- The pointwise bound behind the Caccioppoli inequality with lower-order terms: with
`‖b‖ ≤ β` and `‖c‖ ≤ γ`, the forcing `f - ⟪b, ∇u⟫ - c u` of the principal equation, tested
against `ψ² u`, is at most `ψ² f u + λ/4 · ψ² ‖∇u‖² + (β²/λ + γ) ψ² u²`. -/
private theorem sub_inner_sub_mul_mul_le (hlam : 0 < lam) {s fx ux cx : ℝ}
    {bx gx : EuclideanSpace ℝ ι} (hs : 0 ≤ s) (hb : ‖bx‖ ≤ beta) (hc : ‖cx‖ ≤ gamma) :
    (fx - ⟪bx, gx⟫_ℝ - cx * ux) * (s * ux) ≤
      s * fx * ux + (lam / 4 * (s * ‖gx‖ ^ 2) + (beta ^ 2 / lam + gamma) * (s * ux ^ 2)) := by
  have hinner : |⟪bx, gx⟫_ℝ| ≤ beta * ‖gx‖ :=
    (abs_real_inner_le_norm bx gx).trans (mul_le_mul_of_nonneg_right hb (norm_nonneg _))
  have hc' : |cx| ≤ gamma := by rwa [← Real.norm_eq_abs]
  -- Young's inequality `β |u| ‖∇u‖ ≤ λ/4 ‖∇u‖² + β²/λ u²`, multiplied out by `λ`.
  have hyoung : -(⟪bx, gx⟫_ℝ * ux) ≤ lam / 4 * ‖gx‖ ^ 2 + beta ^ 2 / lam * ux ^ 2 := by
    have h1 : -(⟪bx, gx⟫_ℝ * ux) ≤ beta * ‖gx‖ * |ux| := by
      rw [← neg_mul]
      calc -⟪bx, gx⟫_ℝ * ux ≤ |-⟪bx, gx⟫_ℝ * ux| := le_abs_self _
        _ = |⟪bx, gx⟫_ℝ| * |ux| := by rw [abs_mul, abs_neg]
        _ ≤ beta * ‖gx‖ * |ux| := mul_le_mul_of_nonneg_right hinner (abs_nonneg _)
    have h2 : beta * ‖gx‖ * |ux| ≤ lam / 4 * ‖gx‖ ^ 2 + beta ^ 2 / lam * ux ^ 2 := by
      have key : lam / 4 * ‖gx‖ ^ 2 + beta ^ 2 / lam * ux ^ 2 - beta * ‖gx‖ * |ux| =
          (lam * ‖gx‖ - 2 * beta * |ux|) ^ 2 / (4 * lam) := by
        rw [← sq_abs ux]
        field_simp
        ring
      have : 0 ≤ (lam * ‖gx‖ - 2 * beta * |ux|) ^ 2 / (4 * lam) := by positivity
      linarith
    exact h1.trans h2
  have hmass : -(cx * ux * ux) ≤ gamma * ux ^ 2 := by
    have : -(cx * ux * ux) ≤ |cx| * ux ^ 2 := by
      rw [mul_assoc, ← sq, ← neg_mul]
      exact mul_le_mul_of_nonneg_right (neg_le_abs cx) (sq_nonneg _)
    exact this.trans (mul_le_mul_of_nonneg_right hc' (sq_nonneg _))
  nlinarith [mul_le_mul_of_nonneg_left hyoung hs, mul_le_mul_of_nonneg_left hmass hs]

omit [DecidableEq ι] in
/-- The lower-order part of the forcing of the principal equation, tested against `v = ψ² u`, is
bounded by Young's inequality: `∫_Ω (f - ⟪b, ∇u⟫ - c u) v` is at most
`∫_Ω ψ² f u + λ/4 ∫_Ω ψ² ‖∇u‖² + (β²/λ + γ) ∫_Ω ψ² u²`. -/
private theorem setIntegral_sub_inner_sub_mul_mul_le (hlam : 0 < lam)
    (hbM : MemLp b ⊤ (mu.restrict Omega)) (hcM : MemLp c ⊤ (mu.restrict Omega))
    (hb_bound : ∀ᵐ x ∂mu.restrict Omega, ‖b x‖ ≤ beta)
    (hc_bound : ∀ᵐ x ∂mu.restrict Omega, ‖c x‖ ≤ gamma) (f : Lp ℝ 2 (mu.restrict Omega))
    {u v : W1p mu Omega 2} {ψ : EuclideanSpace ℝ ι → ℝ}
    (hvalue : ∀ᵐ x ∂mu.restrict Omega, W1p.value v x = ψ x ^ 2 * W1p.value u x)
    (hψ : ContDiff ℝ ∞ ψ) (hcpt : HasCompactSupport ψ) :
    ∫ x in Omega, (f x - ⟪b x, W1p.gradient u x⟫_ℝ - c x * W1p.value u x) *
      W1p.value v x ∂mu ≤
      ∫ x in Omega, ψ x ^ 2 * f x * W1p.value u x ∂mu
        + (lam / 4 * ∫ x in Omega, ψ x ^ 2 * ‖W1p.gradient u x‖ ^ 2 ∂mu
          + (beta ^ 2 / lam + gamma) * ∫ x in Omega, ψ x ^ 2 * W1p.value u x ^ 2 ∂mu) := by
  obtain ⟨M, -, hψM, -⟩ := (hψ.of_le (by simp)).exists_abs_le_and_norm_gradient_le hcpt
  have hψ2 : AEStronglyMeasurable (fun x => ψ x ^ 2) (mu.restrict Omega) :=
    (hψ.continuous.pow 2).aestronglyMeasurable
  have hψ2M : ∀ᵐ x ∂mu.restrict Omega, ‖ψ x ^ 2‖ ≤ M ^ 2 := Eventually.of_forall fun x => by
    rw [Real.norm_eq_abs, abs_pow]
    exact pow_le_pow_left₀ (abs_nonneg _) (hψM x) 2
  have hX : Integrable (fun x => ψ x ^ 2 * ‖W1p.gradient u x‖ ^ 2) (mu.restrict Omega) :=
    (Lp.memLp (W1p.gradient u)).norm.integrable_sq.bdd_mul hψ2 hψ2M
  have hZ : Integrable (fun x => ψ x ^ 2 * W1p.value u x ^ 2) (mu.restrict Omega) :=
    (Lp.memLp (W1p.value u)).integrable_sq.bdd_mul hψ2 hψ2M
  have hFu : Integrable (fun x => ψ x ^ 2 * f x * W1p.value u x) (mu.restrict Omega) :=
    (((Lp.memLp f).integrable_mul (Lp.memLp (W1p.value u))).bdd_mul hψ2 hψ2M).congr
      (Eventually.of_forall fun x => by simp only [Pi.mul_apply]; ring)
  have hG : Integrable (fun x => (f x - ⟪b x, W1p.gradient u x⟫_ℝ - c x * W1p.value u x) *
      W1p.value v x) (mu.restrict Omega) :=
    (((Lp.memLp f).sub (memLp_lowerOrder hbM hcM u)).integrable_mul
      (Lp.memLp (W1p.value v))).congr
      (Eventually.of_forall fun x => by simp only [Pi.sub_apply, Pi.mul_apply]; ring)
  have hR : Integrable (fun x => lam / 4 * (ψ x ^ 2 * ‖W1p.gradient u x‖ ^ 2)
      + (beta ^ 2 / lam + gamma) * (ψ x ^ 2 * W1p.value u x ^ 2)) (mu.restrict Omega) :=
    (hX.const_mul _).add (hZ.const_mul _)
  refine (integral_mono_ae hG (hFu.add hR) ?_).trans_eq (by
    simp only [Pi.add_apply]
    rw [integral_add hFu hR, integral_add (hX.const_mul _) (hZ.const_mul _),
      integral_const_mul, integral_const_mul])
  filter_upwards [hvalue, hb_bound, hc_bound] with x hvx hbx hcx
  rw [hvx]
  exact sub_inner_sub_mul_mul_le hlam (sq_nonneg _) hbx hcx

/-- **The Caccioppoli inequality for weak solutions with lower-order terms.** Let `a` be
measurable and uniformly elliptic on `Ω` with constants `0 < λ ≤ Λ`, let `b` and `c` be measurable
with `‖b‖ ≤ β` and `‖c‖ ≤ γ` almost everywhere on `Ω`, and let `u ∈ H¹(Ω)` be a weak solution of

`-∂ᵢ(aⁱʲ ∂ⱼu) + ⟨b, ∇u⟩ + c u = f` in `Ω`, with `f ∈ L²(Ω)`,

with no boundary condition. Then every smooth `ψ` compactly supported in `Ω` satisfies

`∫_Ω ψ² ‖∇u‖² ≤ 2 (2Λ/λ)² ∫_Ω ‖∇ψ‖² u² + ((2β/λ)² + 4γ/λ) ∫_Ω ψ² u² + (4/λ) ∫_Ω ψ² f u`.

No sign condition on `c` and no smallness of `b` is needed: both enter through the zeroth-order
term in `ψ`. -/
theorem UniformlyEllipticOn.setIntegral_sq_mul_norm_gradient_sq_le_lowerOrder
    (h : UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ ι)) a lam Lam)
    (ha : AEStronglyMeasurable a (mu.restrict Omega))
    (hb : AEStronglyMeasurable b (mu.restrict Omega))
    (hc : AEStronglyMeasurable c (mu.restrict Omega))
    (hb_bound : ∀ᵐ x ∂mu.restrict Omega, ‖b x‖ ≤ beta)
    (hc_bound : ∀ᵐ x ∂mu.restrict Omega, ‖c x‖ ≤ gamma)
    {f : Lp ℝ 2 (mu.restrict Omega)} {u : W1p mu Omega 2}
    (hu : ∀ v : W1p0 mu Omega 2, energyFormH1 a b c u (v : W1p mu Omega 2) =
      ∫ x in Omega, f x * W1p.value (v : W1p mu Omega 2) x ∂mu)
    {ψ : EuclideanSpace ℝ ι → ℝ} (hψ : ContDiff ℝ ∞ ψ) (hcpt : HasCompactSupport ψ)
    (hts : tsupport ψ ⊆ (Omega : Set (EuclideanSpace ℝ ι))) :
    ∫ x in Omega, ψ x ^ 2 * ‖W1p.gradient u x‖ ^ 2 ∂mu ≤
      2 * (2 * Lam / lam) ^ 2 * ∫ x in Omega, ‖∇ ψ x‖ ^ 2 * W1p.value u x ^ 2 ∂mu
        + ((2 * beta / lam) ^ 2 + 4 * gamma / lam) *
          ∫ x in Omega, ψ x ^ 2 * W1p.value u x ^ 2 ∂mu
        + 4 / lam * ∫ x in Omega, ψ x ^ 2 * f x * W1p.value u x ∂mu := by
  -- Test the principal equation, with forcing `f - ⟪b, ∇u⟫ - c u`, against `ψ² u`, bound the
  -- lower-order part of the forcing by Young's inequality, and absorb its gradient share.
  have hlam := h.pos
  have hbM : MemLp b ⊤ (mu.restrict Omega) := memLp_top_of_bound hb beta hb_bound
  have hcM : MemLp c ⊤ (mu.restrict Omega) := memLp_top_of_bound hc gamma hc_bound
  have ha' : MemLp (fun x => energyIntegrand (a x) 0 0) ⊤ (mu.restrict Omega) := by
    simpa using memLp_energyIntegrand_of_bounds (b := 0) (c := 0) (beta := 0) (gamma := 0)
      h.upper_nonneg ha aestronglyMeasurable_const aestronglyMeasurable_const
      (fun _ hx eta xi => h.upper_bound hx eta xi) (fun _ _ => by simp) (fun _ _ => by simp)
  obtain ⟨v, hvalue, -, hstep⟩ :=
    h.exists_setIntegral_sq_mul_norm_gradient_sq_le_energyFormH1 ha u hψ hcpt (.inl hts)
  rw [energyFormH1_principal_eq_setIntegral_sub ha' hbM hcM hu v] at hstep
  have hforce := setIntegral_sub_inner_sub_mul_mul_le hlam hbM hcM hb_bound hc_bound f hvalue hψ
    hcpt
  set X := ∫ x in Omega, ψ x ^ 2 * ‖W1p.gradient u x‖ ^ 2 ∂mu
  set Z := ∫ x in Omega, ψ x ^ 2 * W1p.value u x ^ 2 ∂mu
  set F := ∫ x in Omega, ψ x ^ 2 * f x * W1p.value u x ∂mu
  have hsplit : 2 / lam * (F + (lam / 4 * X + (beta ^ 2 / lam + gamma) * Z)) =
      2 / lam * F + X / 2 + ((2 * beta / lam) ^ 2 + 4 * gamma / lam) / 2 * Z := by
    field_simp
    ring
  have hmono := mul_le_mul_of_nonneg_left hforce (by positivity : (0 : ℝ) ≤ 2 / lam)
  rw [hsplit] at hmono
  have h4 : 4 / lam * F = 2 * (2 / lam * F) := by ring
  linarith

omit [DecidableEq ι] in
/-- Young's inequality for the forcing term of Caccioppoli's inequality at the scale `R`:
`B ∫_Ω ψ² u² + (4/λ) ∫_Ω ψ² f u ≤ ∫_Ω ψ² ((B + 2/R²) u² + 2 (R/λ)² f²)`. -/
private theorem mul_setIntegral_add_div_mul_setIntegral_le (hlam : 0 < lam) {R : ℝ} (hR : 0 < R)
    (B : ℝ) (f : Lp ℝ 2 (mu.restrict Omega)) (u : W1p mu Omega 2) {ψ : EuclideanSpace ℝ ι → ℝ}
    (hψ : ContDiff ℝ ∞ ψ) (hcpt : HasCompactSupport ψ) :
    B * ∫ x in Omega, ψ x ^ 2 * W1p.value u x ^ 2 ∂mu
        + 4 / lam * ∫ x in Omega, ψ x ^ 2 * f x * W1p.value u x ∂mu ≤
      ∫ x in Omega, ψ x ^ 2 * ((B + 2 / R ^ 2) * W1p.value u x ^ 2 +
        2 * (R / lam) ^ 2 * f x ^ 2) ∂mu := by
  obtain ⟨M, -, hψM, -⟩ := (hψ.of_le (by simp)).exists_abs_le_and_norm_gradient_le hcpt
  have hψ2 : AEStronglyMeasurable (fun x => ψ x ^ 2) (mu.restrict Omega) :=
    (hψ.continuous.pow 2).aestronglyMeasurable
  have hψ2M : ∀ᵐ x ∂mu.restrict Omega, ‖ψ x ^ 2‖ ≤ M ^ 2 := Eventually.of_forall fun x => by
    rw [Real.norm_eq_abs, abs_pow]
    exact pow_le_pow_left₀ (abs_nonneg _) (hψM x) 2
  have hZ : Integrable (fun x => ψ x ^ 2 * W1p.value u x ^ 2) (mu.restrict Omega) :=
    (Lp.memLp (W1p.value u)).integrable_sq.bdd_mul hψ2 hψ2M
  have hFu : Integrable (fun x => ψ x ^ 2 * f x * W1p.value u x) (mu.restrict Omega) :=
    (((Lp.memLp f).integrable_mul (Lp.memLp (W1p.value u))).bdd_mul hψ2 hψ2M).congr
      (Eventually.of_forall fun x => by simp only [Pi.mul_apply]; ring)
  have hg : Integrable (fun x => ψ x ^ 2 * ((B + 2 / R ^ 2) * W1p.value u x ^ 2 +
      2 * (R / lam) ^ 2 * f x ^ 2)) (mu.restrict Omega) :=
    (((Lp.memLp (W1p.value u)).integrable_sq.const_mul _).add
      ((Lp.memLp f).integrable_sq.const_mul _)).bdd_mul hψ2 hψ2M
  rw [← integral_const_mul, ← integral_const_mul,
    ← integral_add (hZ.const_mul _) (hFu.const_mul _)]
  refine integral_mono ((hZ.const_mul _).add (hFu.const_mul _)) hg fun x => ?_
  -- `4 f u / λ ≤ 2 u² / R² + 2 (R / λ)² f²`, since the difference is `2 (u / R - R f / λ)²`.
  have hsq : 0 ≤ ψ x ^ 2 * (2 * (W1p.value u x / R - R / lam * f x) ^ 2) := by positivity
  have he : ψ x ^ 2 * (2 * (W1p.value u x / R - R / lam * f x) ^ 2) =
      ψ x ^ 2 * ((B + 2 / R ^ 2) * W1p.value u x ^ 2 + 2 * (R / lam) ^ 2 * f x ^ 2) -
        (B * (ψ x ^ 2 * W1p.value u x ^ 2) + 4 / lam * (ψ x ^ 2 * f x * W1p.value u x)) := by
    field_simp
    ring
  linarith

/-- **The Caccioppoli inequality on concentric balls for weak solutions with lower-order
terms.** There is a constant `C > 0`, depending only on the dimension, such that the following
holds for every additive Haar measure `μ`. Let `a` be measurable and uniformly elliptic on `Ω` with
constants `0 < λ ≤ Λ`, let `b` and `c` be measurable with `‖b‖ ≤ β` and `‖c‖ ≤ γ` almost
everywhere on `Ω`, and let `u ∈ H¹(Ω)` be a weak solution of
`-∂ᵢ(aⁱʲ ∂ⱼu) + ⟨b, ∇u⟩ + c u = f` in `Ω`, with `f ∈ L²(Ω)`. Then for every pair of balls
`B(x₀, r) ⊆ B(x₀, R) ⊆ Ω` with `r < R`,

`∫_{B(x₀, r)} ‖∇u‖² ≤ (2 (2Λ/λ)² (C/(R - r))² + (2β/λ)² + 4γ/λ + 2/R²) ∫_{B(x₀, R)} u²`
`  + 2 (R/λ)² ∫_{B(x₀, R)} f²`.

Multiplied by `R²`, the coefficients are the dimensionless `Λ/λ`, `Rβ/λ` and `R²γ/λ` and the
ratio `R/(R - r)`, so the estimate is invariant under dilations. -/
theorem exists_setIntegral_ball_norm_gradient_sq_le_lowerOrder :
    ∃ C : ℝ, 0 < C ∧ ∀ {mu : Measure (EuclideanSpace ℝ ι)} [mu.IsAddHaarMeasure]
      {Omega : Opens (EuclideanSpace ℝ ι)} {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ}
      {b : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι} {c : EuclideanSpace ℝ ι → ℝ}
      {lam Lam beta gamma : ℝ} {f : Lp ℝ 2 (mu.restrict Omega)} {u : W1p mu Omega 2}
      {x₀ : EuclideanSpace ℝ ι} {r R : ℝ},
      UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ ι)) a lam Lam →
      AEStronglyMeasurable a (mu.restrict Omega) →
      AEStronglyMeasurable b (mu.restrict Omega) →
      AEStronglyMeasurable c (mu.restrict Omega) →
      (∀ᵐ x ∂mu.restrict Omega, ‖b x‖ ≤ beta) →
      (∀ᵐ x ∂mu.restrict Omega, ‖c x‖ ≤ gamma) →
      (∀ v : W1p0 mu Omega 2, energyFormH1 a b c u (v : W1p mu Omega 2) =
        ∫ x in Omega, f x * W1p.value (v : W1p mu Omega 2) x ∂mu) →
      0 < R → r < R → ball x₀ R ⊆ (Omega : Set (EuclideanSpace ℝ ι)) →
      ∫ x in ball x₀ r, ‖W1p.gradient u x‖ ^ 2 ∂mu ≤
        (2 * (2 * Lam / lam) ^ 2 * (C / (R - r)) ^ 2 + (2 * beta / lam) ^ 2 + 4 * gamma / lam
            + 2 / R ^ 2) * ∫ x in ball x₀ R, W1p.value u x ^ 2 ∂mu
          + 2 * (R / lam) ^ 2 * ∫ x in ball x₀ R, f x ^ 2 ∂mu := by
  obtain ⟨C, hC0, hC⟩ := exists_setIntegral_ball_norm_gradient_sq_le_add_setIntegral_of_cutoff
    (ι := ι)
  refine ⟨C, hC0, ?_⟩
  intro mu _ Omega a b c lam Lam beta gamma f u x₀ r R h ha hb hc hb_bound hc_bound hu hR hrR
    hball
  have hlam := h.pos
  -- The ball has positive measure, so the almost everywhere bound forces `0 ≤ γ`.
  have : (ae (mu.restrict Omega)).NeBot := ae_restrict_neBot.2
    ((measure_ball_pos mu x₀ hR).trans_le (measure_mono hball)).ne'
  have hγ0 : 0 ≤ gamma := let ⟨_, hx⟩ := hc_bound.exists; (norm_nonneg _).trans hx
  set g := fun x => ((2 * beta / lam) ^ 2 + 4 * gamma / lam + 2 / R ^ 2) * W1p.value u x ^ 2 +
    2 * (R / lam) ^ 2 * f x ^ 2
  have hg : Integrable g (mu.restrict Omega) :=
    ((Lp.memLp (W1p.value u)).integrable_sq.const_mul _).add
      ((Lp.memLp f).integrable_sq.const_mul _)
  -- Caccioppoli's inequality, with the forcing term split by Young's inequality, localized to
  -- the balls.
  have hloc := hC u (A := 2 * (2 * Lam / lam) ^ 2) (g := g) (by positivity) hg
    (Eventually.of_forall fun x => by positivity) hrR hball fun ψ hψ hcpt hts => by
      linarith [h.setIntegral_sq_mul_norm_gradient_sq_le_lowerOrder ha hb hc hb_bound hc_bound hu
        hψ hcpt hts, mul_setIntegral_add_div_mul_setIntegral_le hlam hR
          ((2 * beta / lam) ^ 2 + 4 * gamma / lam) f u hψ hcpt]
  refine hloc.trans_eq ?_
  simp only [g]
  rw [integral_add
    (IntegrableOn.mono_set ((Lp.memLp (W1p.value u)).integrable_sq.const_mul _) hball)
    (IntegrableOn.mono_set ((Lp.memLp f).integrable_sq.const_mul _) hball), integral_const_mul,
    integral_const_mul]
  ring

/-- **Caccioppoli's inequality on balls, for coefficients controlled on the outer ball only.**
There is a constant `C`, depending only on the dimension, such that the following holds. Let
`B(x₀, r) ⊆ B(x₀, R) ⊆ Ω` with `r < R`, let `a` be measurable and uniformly elliptic on `B(x₀, R)`
with constants `0 < λ ≤ Λ`, let `b, c ∈ L∞(Ω)` with `‖b‖ ≤ β` and `|c| ≤ γ` almost everywhere on
`B(x₀, R)`, and let `u ∈ H¹(Ω)` be a weak solution of `-∂ᵢ(aⁱʲ ∂ⱼu) + ⟨b, ∇u⟩ + c u = f` in `Ω`,
with `f ∈ L²(Ω)`. Then, with `L²` norms on the indicated balls,

`‖∇u‖²_{B(x₀, r)} ≤ (2 (2Λ/λ)² (C/(R - r))² + (2β/λ)² + 4γ/λ + 2/R²) ‖u‖²_{B(x₀, R)}`
`  + 2 (R/λ)² ‖f‖²_{B(x₀, R)}`.

Nothing is assumed about the coefficients outside `B(x₀, R)`: this is
`TauCeti.PDE.exists_setIntegral_ball_norm_gradient_sq_le_lowerOrder` for the restriction of `u` to
`B(x₀, R)`. -/
theorem exists_sq_toReal_eLpNorm_gradient_ball_le :
    ∃ C : ℝ, ∀ (mu : Measure (EuclideanSpace ℝ ι)) [mu.IsAddHaarMeasure]
      ⦃Omega : Opens (EuclideanSpace ℝ ι)⦄ ⦃a : EuclideanSpace ℝ ι → Matrix ι ι ℝ⦄
      ⦃b : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι⦄ ⦃c : EuclideanSpace ℝ ι → ℝ⦄
      ⦃x₀ : EuclideanSpace ℝ ι⦄ ⦃r R lam Lam β γ : ℝ⦄
      ⦃f : Lp ℝ 2 (mu.restrict Omega)⦄ ⦃u : W1p mu Omega 2⦄,
      0 < R → r < R → Metric.ball x₀ R ⊆ Omega →
      UniformlyEllipticOn (Metric.ball x₀ R) a lam Lam →
      AEStronglyMeasurable a (mu.restrict (Metric.ball x₀ R)) →
      MemLp b ⊤ (mu.restrict Omega) → MemLp c ⊤ (mu.restrict Omega) →
      (∀ᵐ x ∂mu.restrict (Metric.ball x₀ R), ‖b x‖ ≤ β) →
      (∀ᵐ x ∂mu.restrict (Metric.ball x₀ R), |c x| ≤ γ) →
      (∀ v : W1p0 mu Omega 2, energyFormH1 a b c u (v : W1p mu Omega 2) =
        ∫ x in Omega, f x * W1p.value (v : W1p mu Omega 2) x ∂mu) →
      (eLpNorm (W1p.gradient u) 2 (mu.restrict (Metric.ball x₀ r))).toReal ^ 2 ≤
        (2 * (2 * Lam / lam) ^ 2 * (C / (R - r)) ^ 2 + (2 * β / lam) ^ 2 + 4 * γ / lam
            + 2 / R ^ 2) * (eLpNorm (W1p.value u) 2 (mu.restrict (Metric.ball x₀ R))).toReal ^ 2
          + 2 * (R / lam) ^ 2 * (eLpNorm f 2 (mu.restrict (Metric.ball x₀ R))).toReal ^ 2 := by
  obtain ⟨C, -, hcacc⟩ := exists_setIntegral_ball_norm_gradient_sq_le_lowerOrder (ι := ι)
  refine ⟨C, ?_⟩
  intro mu _ Omega a b c x₀ r R lam Lam β γ f u hR hrR hΩ ha ham hb hc hβ hγ hu
  have hrRs : Metric.ball x₀ r ⊆ Metric.ball x₀ R := Metric.ball_subset_ball hrR.le
  let U : Opens (EuclideanSpace ℝ ι) := ⟨Metric.ball x₀ R, Metric.isOpen_ball⟩
  have hUΩ : U ≤ Omega := SetLike.coe_subset_coe.mp hΩ
  have hle : mu.restrict U ≤ mu.restrict Omega := Measure.restrict_mono hΩ le_rfl
  have hfU : MemLp f 2 (mu.restrict U) := (Lp.memLp f).mono_measure hle
  have hcU := hcacc (mu := mu) (Omega := U) (f := hfU.toLp f) (u := W1p.restrictL hUΩ u)
    (x₀ := x₀) (r := r) (R := R) ha ham
    (hb.aestronglyMeasurable.mono_measure hle) (hc.aestronglyMeasurable.mono_measure hle) hβ
    (hγ.mono fun x hx => (Real.norm_eq_abs _).trans_le hx)
    (fun v => by
      rw [energyFormH1_restrictL_eq_setIntegral hUΩ hu v]
      refine integral_congr_ae ?_
      filter_upwards [hfU.coeFn_toLp] with x hx
      rw [hx])
    hR hrR subset_rfl
  -- Return from the restriction to `u` and `f`, and from integrals to `L²` norms.
  have hgrad : ∫ x in Metric.ball x₀ r, ‖W1p.gradient (W1p.restrictL hUΩ u) x‖ ^ 2 ∂mu =
      ∫ x in Metric.ball x₀ r, ‖W1p.gradient u x‖ ^ 2 ∂mu :=
    integral_congr_ae (ae_restrict_of_ae_restrict_of_subset hrRs
      ((W1p.gradient_restrictL_ae hUΩ u).mono fun x hx => by simp only [hx]))
  have hval : ∫ x in Metric.ball x₀ R, W1p.value (W1p.restrictL hUΩ u) x ^ 2 ∂mu =
      ∫ x in Metric.ball x₀ R, ‖W1p.value u x‖ ^ 2 ∂mu :=
    integral_congr_ae ((W1p.value_restrictL_ae hUΩ u).mono fun x hx => by
      simp only [hx, Real.norm_eq_abs, sq_abs])
  have hfor : ∫ x in Metric.ball x₀ R, hfU.toLp f x ^ 2 ∂mu =
      ∫ x in Metric.ball x₀ R, ‖f x‖ ^ 2 ∂mu :=
    integral_congr_ae (hfU.coeFn_toLp.mono fun x hx => by
      simp only [hx, Real.norm_eq_abs, sq_abs])
  have hmG : MemLp (W1p.gradient u) 2 (mu.restrict (Metric.ball x₀ r)) :=
    (Lp.memLp _).mono_measure (Measure.restrict_mono (hrRs.trans hΩ) le_rfl)
  have hmV : MemLp (W1p.value u) 2 (mu.restrict (Metric.ball x₀ R)) :=
    (Lp.memLp _).mono_measure hle
  have hmF : MemLp f 2 (mu.restrict (Metric.ball x₀ R)) := hfU
  rw [hgrad, hval, hfor, ← hmG.norm_toLp_sq, ← hmV.norm_toLp_sq, ← hmF.norm_toLp_sq,
    Lp.norm_toLp, Lp.norm_toLp, Lp.norm_toLp] at hcU
  exact hcU

end PDE

end TauCeti
