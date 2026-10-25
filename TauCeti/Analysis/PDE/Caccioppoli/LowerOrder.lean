/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.Young
public import TauCeti.Analysis.PDE.Caccioppoli.Truncation

/-!
# The Caccioppoli inequality for truncations with lower-order terms

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

## Main declarations

All four are in the namespace `TauCeti.PDE`.

* `UniformlyEllipticOn.setIntegral_sq_mul_norm_gradient_posPartAbove_sq_le_lowerOrder_of_memLp`:
  Caccioppoli's inequality for `(u - k)⁺` at an arbitrary level with an `L²` hypothesis.
* `UniformlyEllipticOn.setIntegral_sq_mul_norm_gradient_posPartAbove_sq_le_lowerOrder`: the
  nonnegative-level specialization, whose `L²` hypothesis is automatic.
* `UniformlyEllipticOn.setIntegral_sq_mul_norm_gradient_posPartAbove_sq_le_lowerOrder_of_nonpos`:
  the cutoff form for subsolutions of `L u ≤ 0` with `c ≥ 0`, at a level `k ≥ 0`, where the
  forcing and mass term drop out.
* `exists_setIntegral_ball_norm_gradient_posPartAbove_sq_le_lowerOrder`: the form on
  concentric balls for subsolutions of `L u ≤ 0` with `c ≥ 0`.

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
  -- the principal part with the effective forcing `g = f - ⟪b, ∇u⟫ - c u`, so the
  -- principal-part inequality applies. The drift part of `∫ ψ² g w` is then bounded by Young's
  -- inequality and its gradient share absorbed into the left-hand side.
  dsimp only
  have hlam := h.pos
  have hmem : ∀ᵐ x ∂mu.restrict Omega, x ∈ (Omega : Set (EuclideanSpace ℝ ι)) :=
    ae_restrict_mem Omega.isOpen.measurableSet
  have hB : MemLp (fun x => ⟪b x, W1p.gradient u x⟫_ℝ) 2 (mu.restrict Omega) :=
    MemLp.of_bilin (inner ℝ) 1 (memLp_top_of_bound hb beta
      (ae_restrict_of_forall_mem Omega.isOpen.measurableSet hb_bound)) (Lp.memLp _)
      continuous_inner
      (.of_forall fun x => by simpa using nnnorm_inner_le_nnnorm (b x) (W1p.gradient u x))
  have hC : MemLp (fun x => c x * W1p.value u x) 2 (mu.restrict Omega) :=
    (memLp_top_of_bound hc gamma (ae_restrict_of_forall_mem Omega.isOpen.measurableSet
      hc_bound)).fun_mul (Lp.memLp _)
  set g := fun x => f x - ⟪b x, W1p.gradient u x⟫_ℝ - c x * W1p.value u x
  have hg : MemLp g 2 (mu.restrict Omega) := ((Lp.memLp f).sub hB).sub hC
  have hu' : ∀ v : W1p0 mu Omega 2,
      (∀ᵐ x ∂mu.restrict Omega, 0 ≤ W1p.value (v : W1p mu Omega 2) x) →
        energyFormH1 a 0 0 u (v : W1p mu Omega 2) ≤
          ∫ x in Omega, hg.toLp g x * W1p.value (v : W1p mu Omega 2) x ∂mu := by
    intro v hv
    have hvLp := Lp.memLp (W1p.value (v : W1p mu Omega 2))
    have hE := h.integrable_energyIntegrand_jetField (b := 0) (c := 0) (beta := 0)
      (gamma := 0) ha aestronglyMeasurable_const aestronglyMeasurable_const
      (fun _ _ => by simp) (fun _ _ => by simp) u v
    have hfv : Integrable (fun x => f x * W1p.value (v : W1p mu Omega 2) x)
        (mu.restrict Omega) := (Lp.memLp f).integrable_mul hvLp
    have hBC : Integrable (fun x => ⟪b x, W1p.gradient u x⟫_ℝ * W1p.value (v : W1p mu Omega 2) x
        + c x * W1p.value u x * W1p.value (v : W1p mu Omega 2) x) (mu.restrict Omega) :=
      (hB.integrable_mul hvLp).add (hC.integrable_mul hvLp)
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
    have hforce : ∫ x in Omega, hg.toLp g x * W1p.value (v : W1p mu Omega 2) x ∂mu =
        ∫ x in Omega, f x * W1p.value (v : W1p mu Omega 2) x ∂mu - ∫ x in Omega,
          (⟪b x, W1p.gradient u x⟫_ℝ * W1p.value (v : W1p mu Omega 2) x
            + c x * W1p.value u x * W1p.value (v : W1p mu Omega 2) x) ∂mu := by
      rw [← integral_sub hfv hBC]
      refine integral_congr_ae ?_
      filter_upwards [hg.coeFn_toLp] with x hx
      rw [hx]
      simp only [g]
      ring
    linarith [hu v hv]
  have hcacc := h.setIntegral_sq_mul_norm_gradient_posPartAbove_sq_le_of_memLp ha hu' hwLp hψ
    hcpt hts
  dsimp only at hcacc
  set w := W1p.posPartAboveOfMemLp (by norm_num) k u hwLp
  -- Integrability of the weighted squares and of the forcing terms.
  obtain ⟨M, -, hψM, -⟩ := (hψ.of_le (by simp)).exists_abs_le_and_norm_gradient_le hcpt
  have hψ2 : AEStronglyMeasurable (fun x => ψ x ^ 2) (mu.restrict Omega) :=
    (hψ.continuous.pow 2).aestronglyMeasurable
  have hψ2M : ∀ᵐ x ∂mu.restrict Omega, ‖ψ x ^ 2‖ ≤ M ^ 2 := Eventually.of_forall fun x => by
    rw [Real.norm_eq_abs, abs_pow]
    exact pow_le_pow_left₀ (abs_nonneg _) (hψM x) 2
  have hX : Integrable (fun x => ψ x ^ 2 * ‖W1p.gradient w x‖ ^ 2) (mu.restrict Omega) :=
    (W1p.integrable_norm_gradient_sq w).bdd_mul hψ2 hψ2M
  have hZ : Integrable (fun x => ψ x ^ 2 * W1p.value w x ^ 2) (mu.restrict Omega) :=
    (W1p.integrable_value_sq w).bdd_mul hψ2 hψ2M
  have hF : Integrable (fun x => ψ x ^ 2 * (f x - c x * W1p.value u x) * W1p.value w x)
      (mu.restrict Omega) := by
    refine ((((Lp.memLp f).sub hC).integrable_mul (Lp.memLp (W1p.value w))).bdd_mul hψ2
      hψ2M).congr (Eventually.of_forall fun x => ?_)
    simp only [Pi.sub_apply, Pi.mul_apply]
    ring
  have hG : Integrable (fun x => ψ x ^ 2 * hg.toLp g x * W1p.value w x) (mu.restrict Omega) := by
    refine (((Lp.memLp (hg.toLp g)).integrable_mul (Lp.memLp (W1p.value w))).bdd_mul hψ2
      hψ2M).congr (Eventually.of_forall fun x => ?_)
    simp only [Pi.mul_apply]
    ring
  have hR : Integrable (fun x => lam / 4 * (ψ x ^ 2 * ‖W1p.gradient w x‖ ^ 2)
      + beta ^ 2 / lam * (ψ x ^ 2 * W1p.value w x ^ 2)) (mu.restrict Omega) :=
    (hX.const_mul _).add (hZ.const_mul _)
  -- On the active set the truncation gradient is `∇u`; off it, `w` vanishes. So the drift
  -- part of the forcing is `-⟪b, ∇w⟫ ψ² w`, which Young's inequality bounds.
  have hdrift : ∫ x in Omega, ψ x ^ 2 * hg.toLp g x * W1p.value w x ∂mu ≤
      ∫ x in Omega, (ψ x ^ 2 * (f x - c x * W1p.value u x) * W1p.value w x
        + (lam / 4 * (ψ x ^ 2 * ‖W1p.gradient w x‖ ^ 2)
          + beta ^ 2 / lam * (ψ x ^ 2 * W1p.value w x ^ 2))) ∂mu := by
    refine integral_mono_ae hG (hF.add hR) ?_
    filter_upwards [hmem, hg.coeFn_toLp,
      W1p.gradient_posPartAboveOfMemLp_ae (by norm_num) k u hwLp,
      W1p.value_posPartAboveOfMemLp_ae (by norm_num) k u hwLp] with x hx hgx hwg hwv
    have hactive : ⟪b x, W1p.gradient u x⟫_ℝ * W1p.value w x =
        ⟪b x, W1p.gradient w x⟫_ℝ * W1p.value w x := by
      by_cases hxu : k < W1p.value u x
      · have hxmem : x ∈ {y : EuclideanSpace ℝ ι | k < W1p.value u y} := hxu
        rw [hwg, Set.indicator_of_mem hxmem]
      · rw [hwv, max_eq_right (sub_nonpos.mpr (le_of_not_gt hxu)), mul_zero, mul_zero]
    have hyoung := two_mul_real_inner_le_add_mul_norm_sq (-(ψ x * W1p.value w x) • b x)
      (ψ x • W1p.gradient w x) (by positivity : (0 : ℝ) < 2 / lam)
    simp only [real_inner_smul_left, real_inner_smul_right, norm_smul, mul_pow, Real.norm_eq_abs,
      sq_abs, inv_div] at hyoung
    have hb2 : (ψ x * W1p.value w x) ^ 2 * ‖b x‖ ^ 2 ≤ (ψ x * W1p.value w x) ^ 2 * beta ^ 2 :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) (hb_bound x hx) 2)
        (sq_nonneg _)
    rw [hgx]
    simp only [g]
    linear_combination (hyoung + 2 / lam * hb2) / 2 - ψ x ^ 2 * hactive
  rw [integral_add hF hR, integral_add (hX.const_mul _) (hZ.const_mul _), integral_const_mul,
    integral_const_mul] at hdrift
  -- Absorb the drift's quarter of the gradient term into the left-hand side.
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
with `w = (u - k)⁺`, and for every pair of balls `B(x₀, r) ⊆ B(x₀, R) ⊆ Ω` with `0 < r < R`,

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
      0 < r → r < R → ball x₀ R ⊆ (Omega : Set (EuclideanSpace ℝ ι)) →
      ∫ x in ball x₀ r, ‖W1p.gradient (W1p.posPartAbove (by norm_num) hk u) x‖ ^ 2 ∂mu ≤
        (2 * (2 * Lam / lam) ^ 2 * (C / (R - r)) ^ 2 + (2 * beta / lam) ^ 2) *
          ∫ x in ball x₀ R, max (W1p.value u x - k) 0 ^ 2 ∂mu := by
  obtain ⟨C, hC0, hC⟩ := exists_setIntegral_ball_norm_gradient_sq_le_of_cutoff (ι := ι)
  refine ⟨C, hC0, ?_⟩
  intro mu _ Omega a b c lam Lam beta gamma u k hk x₀ r R h ha hb hc hb_bound hc_bound hc_nonneg
    hu hr hrR hball
  -- Caccioppoli's inequality for `w`, with the forcing and mass term dropped, localized to the
  -- balls.
  have hloc := hC (W1p.posPartAbove (by norm_num) hk u) (A := 2 * (2 * Lam / lam) ^ 2)
    (B := (2 * beta / lam) ^ 2) (by positivity) (sq_nonneg _) hr hrR hball
    fun ψ hψ hcpt hts =>
      h.setIntegral_sq_mul_norm_gradient_posPartAbove_sq_le_lowerOrder_of_nonpos ha hb hc
        hb_bound hc_bound hc_nonneg hu hk hψ hcpt hts
  refine hloc.trans_eq ?_
  rw [integral_congr_ae (ae_restrict_of_ae_restrict_of_subset hball (by
    filter_upwards [W1p.value_posPartAbove_ae (by norm_num) hk u] with x hx
    rw [hx]))]

end PDE

end TauCeti
