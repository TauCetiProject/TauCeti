/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Regularity.Inhomogeneous
import TauCeti.MeasureTheory.Function.EssSup
import TauCeti.MeasureTheory.Measure.Haar.NormedSpace

/-!
# The global Hölder estimate from decay at the boundary

Let `a` be measurable and uniformly elliptic on an open set `Ω ⊆ ℝⁿ`, `n ≥ 1`, and let
`u ∈ H¹(Ω)` be a weak solution of

`-∂ᵢ(aⁱʲ ∂ⱼu) = f + ∂ᵢFⁱ` in `Ω`

with `f ∈ Lʳ(Ω)`, `r > 1`, `r > n/2`, and `F ∈ L^q(Ω; ℝⁿ)`, `q > 2`, `q > n`. De Giorgi's
interior theorem (`TauCeti.PDE.exists_holderOnWith_preciseRepresentative_of_memLp_add_divergence`)
makes `u` locally Hölder continuous in `Ω`, with a constant that blows up at `∂Ω`. This file
proves that `u` is Hölder continuous up to the boundary, with one constant on all of `Ω`, as soon
as `u` is bounded and decays like a power of the distance at the points of the complement:
`|u| ≤ N (ρ / R)^β` on `Ω ∩ B(z, ρ)` for every `z ∉ Ω` and `0 < ρ ≤ R`. More precisely, the
precise representative of the extension of `u` by zero is Hölder continuous on all of `ℝⁿ`
(`TauCeti.PDE.exists_holderWith_preciseRepresentative_indicator_of_memLp_add_divergence`), with
a constant controlled by the bound of `u`, the constant `N` and the norms of the data.

No regularity of `∂Ω` is assumed: the geometry of the domain enters only through the decay
hypothesis. For a weak solution vanishing on `∂Ω`, the decay at a point `z ∉ Ω` is De Giorgi's
boundary estimate, which needs the complement of `Ω` to have positive density in the balls
`B(z, ρ)` (Gilbarg–Trudinger, Theorem 8.27); such an exterior density holds on every bounded
Lipschitz domain. The bound on `u` is the global maximum principle (Gilbarg–Trudinger,
Theorem 8.16). Together they give the case of zero boundary values of Gilbarg–Trudinger's global
Hölder estimate, Theorem 8.29.

## The argument

The proof combines the two estimates with
`TauCeti.MeasureTheory.holderWith_preciseRepresentative_of_forall_notMem`. Its interior
hypothesis is De Giorgi's interior oscillation estimate
(`TauCeti.PDE.exists_ae_value_mem_Icc_add_mul_rpow_mul_add_of_memLp_add_divergence`) with the
supremum of `|u|` on the ball in place of its scaled `L²` norm. The data terms of that estimate
on a ball of radius `ρ ≤ R` carry the factors `ρ^(2 - n/r)` and `ρ^(1 - n/q)`; lowering the
exponent `α` below both Morrey gains moves them to the outer scale `R`, where they enter through
`K (s / R)^α`.

## Main declarations

* `TauCeti.PDE.exists_holderWith_preciseRepresentative_indicator_of_memLp_add_divergence`: the
  global Hölder estimate for a bounded weak solution that decays at the points of the
  complement of `Ω`.

## References

* D. Gilbarg, N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  Theorems 8.16, 8.24, 8.27 and 8.29.
-/

public section

noncomputable section

open Filter MeasureTheory Matrix Metric Module Set TopologicalSpace TauCeti.MeasureTheory
open scoped ENNReal NNReal RealInnerProductSpace

namespace TauCeti

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {mu : Measure (EuclideanSpace ℝ ι)}
  [mu.IsAddHaarMeasure]

namespace PDE

/-- De Giorgi's interior oscillation estimate with the supremum in place of the `L²` norm: if
`|u| ≤ L` on `B(x₀, ρ) ⊆ Ω`, then on `B(x₀, s)`, `0 < s ≤ ρ/2`, the values of `u` lie in a closed
ball of radius `C (s / ρ)^α (L + (ρ^(2 - n/r) ‖f‖_{Lʳ} + ρ^(1 - n/q) ‖F‖_{L^q}) / λ)`. -/
private theorem exists_ae_mem_closedBall_of_ae_abs_value_le [Nonempty ι] {lam Lam : ℝ}
    {r q : ℝ≥0} (hr : 1 < r) (hrn : (Fintype.card ι : ℝ) < 2 * r) (hq : 2 < (q : ℝ))
    (hqn : (Fintype.card ι : ℝ) < q) :
    ∃ α C : ℝ, 0 < α ∧ α ≤ 1 ∧ 0 < C ∧ ∀ {Omega : Opens (EuclideanSpace ℝ ι)}
      {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ} {f : EuclideanSpace ℝ ι → ℝ}
      {F : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι} {u : W1p mu Omega 2}
      {x₀ : EuclideanSpace ℝ ι} {ρ s L : ℝ},
      UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ ι)) a lam Lam →
      AEStronglyMeasurable a (mu.restrict Omega) →
      MemLp f r (mu.restrict (ball x₀ ρ)) → MemLp F q (mu.restrict (ball x₀ ρ)) →
      (∀ v : W1p0 mu Omega 2, energyFormH1 a 0 0 u (v : W1p mu Omega 2) =
        ∫ x in Omega, f x * W1p.value (v : W1p mu Omega 2) x ∂mu -
          ∫ x in Omega, ⟪F x, W1p.gradient (v : W1p mu Omega 2) x⟫ ∂mu) →
      0 < s → s ≤ ρ / 2 → ball x₀ ρ ⊆ (Omega : Set (EuclideanSpace ℝ ι)) →
      (∀ᵐ x ∂mu.restrict (ball x₀ ρ), |W1p.value u x| ≤ L) →
      ∃ c : ℝ, ∀ᵐ x ∂mu.restrict (ball x₀ s), W1p.value u x ∈ closedBall c (C * (s / ρ) ^ α *
        (L + (ρ ^ (2 - (Fintype.card ι : ℝ) / r) * (eLpNorm f r (mu.restrict (ball x₀ ρ))).toReal +
          ρ ^ (1 - (Fintype.card ι : ℝ) / q) *
            (eLpNorm F q (mu.restrict (ball x₀ ρ))).toReal) / lam)) := by
  obtain ⟨α, C₁, hα, hα1, hC₁, hosc⟩ :=
    exists_ae_value_mem_Icc_add_mul_rpow_mul_add_of_memLp_add_divergence (mu := mu) (lam := lam)
      (Lam := Lam) hr hrn hq hqn
  set ω : ℝ := mu.real (ball (0 : EuclideanSpace ℝ ι) 1)
  refine ⟨α, C₁ * (√ω + 1) / 2, hα, hα1, by positivity, ?_⟩
  intro Omega a f F u x₀ ρ s L h ha hf hF hu hs hsρ hball hL
  have hρ : 0 < ρ := by linarith
  obtain ⟨m', hm'⟩ := hosc h ha hf hF hu hs hsρ hball
  set D := (ρ ^ (2 - (Fintype.card ι : ℝ) / r) * (eLpNorm f r (mu.restrict (ball x₀ ρ))).toReal +
    ρ ^ (1 - (Fintype.card ι : ℝ) / q) * (eLpNorm F q (mu.restrict (ball x₀ ρ))).toReal) / lam
  have hD : 0 ≤ D := by have := h.pos; positivity
  have hL0 : 0 ≤ L := nonneg_of_ae_restrict_abs_le (measure_ball_pos mu x₀ hρ).ne' hL
  -- The scaled `L²` norm of `u` on `B(x₀, ρ)` is at most `√|B(0, 1)| L`.
  have hint : ∫ x in ball x₀ ρ, W1p.value u x ^ 2 ∂mu ≤ L ^ 2 * mu.real (ball x₀ ρ) := by
    refine (le_abs_self _).trans ?_
    rw [← Real.norm_eq_abs]
    refine norm_setIntegral_le_of_norm_le_const_ae measure_ball_lt_top ?_
    filter_upwards [hL] with x hx
    rw [Real.norm_eq_abs, abs_pow]
    exact pow_le_pow_left₀ (abs_nonneg _) hx 2
  have hQ : ρ ^ (-(Fintype.card ι : ℝ) / 2) * √(∫ x in ball x₀ ρ, W1p.value u x ^ 2 ∂mu) ≤
      √ω * L := by
    have hpow : ρ ^ (-(Fintype.card ι : ℝ) / 2) * ρ ^ ((Fintype.card ι : ℝ) / 2) = 1 := by
      rw [← Real.rpow_add hρ, neg_div, neg_add_cancel, Real.rpow_zero]
    calc _ ≤ ρ ^ (-(Fintype.card ι : ℝ) / 2) * √(L ^ 2 * mu.real (ball x₀ ρ)) := by gcongr
      _ = √ω * L := by
        rw [Real.sqrt_mul (sq_nonneg L), Real.sqrt_sq hL0, Measure.sqrt_addHaar_real_ball mu x₀ hρ,
          finrank_euclideanSpace]
        linear_combination (L * √ω) * hpow
  set len := C₁ * (s / ρ) ^ α * (ρ ^ (-(Fintype.card ι : ℝ) / 2) *
    √(∫ x in ball x₀ ρ, W1p.value u x ^ 2 ∂mu) + D)
  have hlen : len / 2 ≤ C₁ * (√ω + 1) / 2 * (s / ρ) ^ α * (L + D) := by
    have h1 : 0 ≤ C₁ * (s / ρ) ^ α := by positivity
    have := mul_le_mul_of_nonneg_left (add_le_add_right hQ D) h1
    nlinarith [mul_nonneg h1 (mul_nonneg (Real.sqrt_nonneg ω) hD), mul_nonneg h1 hL0]
  refine ⟨m' + len / 2, ?_⟩
  filter_upwards [hm'] with x hx
  rw [Real.closedBall_eq_Icc]
  constructor <;> linarith [hx.1, hx.2]

/-- Moving the data terms of De Giorgi's estimate on a ball of radius `ρ` to the outer scale
`R ≥ ρ`: for `0 < s ≤ ρ ≤ R`, an exponent `α ≤ α₀` below both powers `γ₁, γ₂`, and data
`0 ≤ aᵢ ≤ Aᵢ`,
`(s / ρ)^α₀ (ρ^γ₁ a₁ + ρ^γ₂ a₂) / λ ≤ (s / R)^α (R^γ₁ A₁ + R^γ₂ A₂) / λ`. -/
private theorem div_rpow_mul_add_div_le {s ρ R α α₀ γ₁ γ₂ a₁ a₂ A₁ A₂ lam : ℝ} (hs : 0 < s)
    (hsρ : s ≤ ρ) (hρR : ρ ≤ R) (hαα₀ : α ≤ α₀) (hαγ₁ : α ≤ γ₁) (hαγ₂ : α ≤ γ₂) (ha₁ : 0 ≤ a₁)
    (ha₂ : 0 ≤ a₂) (hA₁ : a₁ ≤ A₁) (hA₂ : a₂ ≤ A₂) (hlam : 0 ≤ lam) :
    (s / ρ) ^ α₀ * ((ρ ^ γ₁ * a₁ + ρ ^ γ₂ * a₂) / lam) ≤
      (s / R) ^ α * ((R ^ γ₁ * A₁ + R ^ γ₂ * A₂) / lam) := by
  have hρ : 0 < ρ := hs.trans_le hsρ
  have hR : 0 < R := hρ.trans_le hρR
  -- `(s / ρ)^α ρ^γ = s^α ρ^(γ - α) ≤ (s / R)^α R^γ` for `γ ≥ α`.
  have hshift : ∀ γ, α ≤ γ → (s / ρ) ^ α * ρ ^ γ ≤ (s / R) ^ α * R ^ γ := fun γ hγ => by
    have key : ∀ t : ℝ, 0 < t → (s / t) ^ α * t ^ γ = s ^ α * t ^ (γ - α) := fun t ht => by
      rw [Real.div_rpow hs.le ht.le, Real.rpow_sub ht]
      field_simp
    rw [key ρ hρ, key R hR]
    gcongr
  have hpow : (s / ρ) ^ α₀ ≤ (s / ρ) ^ α :=
    Real.rpow_le_rpow_of_exponent_ge (by positivity) ((div_le_one hρ).2 hsρ) hαα₀
  rw [← mul_div_assoc, ← mul_div_assoc]
  refine div_le_div_of_nonneg_right ?_ hlam
  calc _ ≤ (s / ρ) ^ α * (ρ ^ γ₁ * A₁ + ρ ^ γ₂ * A₂) := by gcongr
    _ = (s / ρ) ^ α * ρ ^ γ₁ * A₁ + (s / ρ) ^ α * ρ ^ γ₂ * A₂ := by ring
    _ ≤ (s / R) ^ α * R ^ γ₁ * A₁ + (s / R) ^ α * R ^ γ₂ * A₂ :=
        add_le_add (mul_le_mul_of_nonneg_right (hshift γ₁ hαγ₁) (ha₁.trans hA₁))
          (mul_le_mul_of_nonneg_right (hshift γ₂ hαγ₂) (ha₂.trans hA₂))
    _ = _ := by ring

/-- The interior estimate in the form consumed by
`TauCeti.MeasureTheory.holderWith_preciseRepresentative_of_forall_notMem`: for every `β > 0`
there is an exponent `α ≤ min β 1` such that, if `|u| ≤ L` on `B(x₀, ρ) ⊆ Ω` with `ρ ≤ R`, then on
`B(x₀, s)`, `0 < s ≤ ρ/2`, the values of `u` lie in a closed ball of radius
`C (s / ρ)^α L + C ((R^(2 - n/r) ‖f‖_{Lʳ(Ω)} + R^(1 - n/q) ‖F‖_{L^q(Ω)}) / λ) (s / R)^α`. -/
private theorem exists_ae_mem_closedBall_add_of_ae_abs_value_le [Nonempty ι] {lam Lam : ℝ}
    {r q : ℝ≥0} (hr : 1 < r) (hrn : (Fintype.card ι : ℝ) < 2 * r) (hq : 2 < (q : ℝ))
    (hqn : (Fintype.card ι : ℝ) < q) {β : ℝ} (hβ : 0 < β) :
    ∃ α C : ℝ, 0 < α ∧ α ≤ β ∧ α ≤ 1 ∧ 0 < C ∧ ∀ {Omega : Opens (EuclideanSpace ℝ ι)}
      {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ} {f : EuclideanSpace ℝ ι → ℝ}
      {F : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι} {u : W1p mu Omega 2}
      {x₀ : EuclideanSpace ℝ ι} {ρ s L R : ℝ},
      UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ ι)) a lam Lam →
      AEStronglyMeasurable a (mu.restrict Omega) →
      MemLp f r (mu.restrict Omega) → MemLp F q (mu.restrict Omega) →
      (∀ v : W1p0 mu Omega 2, energyFormH1 a 0 0 u (v : W1p mu Omega 2) =
        ∫ x in Omega, f x * W1p.value (v : W1p mu Omega 2) x ∂mu -
          ∫ x in Omega, ⟪F x, W1p.gradient (v : W1p mu Omega 2) x⟫ ∂mu) →
      0 < s → s ≤ ρ / 2 → ρ ≤ R → ball x₀ ρ ⊆ (Omega : Set (EuclideanSpace ℝ ι)) →
      (∀ᵐ x ∂mu.restrict (ball x₀ ρ), |W1p.value u x| ≤ L) →
      ∃ c : ℝ, ∀ᵐ x ∂mu.restrict (ball x₀ s), W1p.value u x ∈ closedBall c
        (C * (s / ρ) ^ α * L + C *
          ((R ^ (2 - (Fintype.card ι : ℝ) / r) * (eLpNorm f r (mu.restrict Omega)).toReal +
            R ^ (1 - (Fintype.card ι : ℝ) / q) * (eLpNorm F q (mu.restrict Omega)).toReal) /
              lam) * (s / R) ^ α) := by
  obtain ⟨α₀, C, hα₀, hα₀1, hC, hosc⟩ :=
    exists_ae_mem_closedBall_of_ae_abs_value_le (mu := mu) (lam := lam) (Lam := Lam) hr hrn hq hqn
  have hr0 : (0 : ℝ) < r := by
    linarith only [hrn, (Nat.cast_nonneg _ : (0 : ℝ) ≤ Fintype.card ι)]
  have hq0 : (0 : ℝ) < q := (Nat.cast_nonneg _).trans_lt hqn
  have hγ₁ : 0 < 2 - (Fintype.card ι : ℝ) / r := by rw [sub_pos, div_lt_iff₀ hr0]; linarith
  have hγ₂ : 0 < 1 - (Fintype.card ι : ℝ) / q := by rw [sub_pos, div_lt_iff₀ hq0]; linarith
  -- The exponent: below De Giorgi's interior exponent, `β` and both Morrey gains.
  obtain ⟨α, hαdef⟩ : ∃ α : ℝ, α = min (min α₀ β)
      (min (2 - (Fintype.card ι : ℝ) / r) (1 - (Fintype.card ι : ℝ) / q)) := ⟨_, rfl⟩
  have hαα₀ : α ≤ α₀ := hαdef ▸ (min_le_left _ _).trans (min_le_left _ _)
  have hαγ₁ : α ≤ 2 - (Fintype.card ι : ℝ) / r := hαdef ▸ (min_le_right _ _).trans (min_le_left _ _)
  have hαγ₂ : α ≤ 1 - (Fintype.card ι : ℝ) / q :=
    hαdef ▸ (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨α, C, hαdef ▸ lt_min (lt_min hα₀ hβ) (lt_min hγ₁ hγ₂),
    hαdef ▸ (min_le_left _ _).trans (min_le_right _ _), hαα₀.trans hα₀1, hC, ?_⟩
  intro Omega a f F u x₀ ρ s L R h ha hf hF hu hs hsρ hρR hball hL
  have hρ : 0 < ρ := by linarith
  have hmono := Measure.restrict_mono hball (le_refl mu)
  obtain ⟨c, hc⟩ := hosc h ha (hf.mono_measure hmono) (hF.mono_measure hmono) hu hs hsρ hball hL
  refine ⟨c, ?_⟩
  filter_upwards [hc] with x hx
  refine closedBall_subset_closedBall ?_ hx
  have hL0 : 0 ≤ L := nonneg_of_ae_restrict_abs_le (measure_ball_pos mu x₀ hρ).ne' hL
  have hpow : (s / ρ) ^ α₀ ≤ (s / ρ) ^ α :=
    Real.rpow_le_rpow_of_exponent_ge (div_pos hs hρ) ((div_le_one hρ).2 (by linarith)) hαα₀
  have hdat := div_rpow_mul_add_div_le hs (by linarith) hρR hαα₀ hαγ₁ hαγ₂
    ENNReal.toReal_nonneg ENNReal.toReal_nonneg
    (ENNReal.toReal_mono hf.eLpNorm_ne_top (eLpNorm_mono_measure f hmono))
    (ENNReal.toReal_mono hF.eLpNorm_ne_top (eLpNorm_mono_measure F hmono)) h.pos.le
  nlinarith [mul_le_mul_of_nonneg_left hdat hC.le,
    mul_le_mul_of_nonneg_right hpow (mul_nonneg hC.le hL0)]

/-- The constant of the global Hölder estimate: for `0 < α ≤ 1`, `R > 0` and nonnegative
`C, M, N, D`, the constant `2 (5^α (N + C (N + M)) + C D + 8^α M) / R^α` of
`TauCeti.MeasureTheory.holderWith_preciseRepresentative_of_forall_notMem` is at most
`2 (13 + 6 C) R^(-α) (M + N + D)`. -/
private theorem two_mul_rpow_add_div_le {α C R D : ℝ} {M N : ℝ≥0} (hα : 0 < α) (hα1 : α ≤ 1)
    (hC : 0 ≤ C) (hR : 0 < R) (hD : 0 ≤ D) :
    2 * (5 ^ (α.toNNReal : ℝ) * (N + C.toNNReal * (N + M)) + (C * D).toNNReal +
      8 ^ (α.toNNReal : ℝ) * M) / R.toNNReal ^ (α.toNNReal : ℝ) ≤
        (2 * (13 + 6 * C) * R ^ (-(α.toNNReal : ℝ)) * (M + N + D)).toNNReal := by
  rw [Real.le_toNNReal_iff_coe_le (by positivity)]
  push_cast
  simp only [Real.coe_toNNReal _ hC, Real.coe_toNNReal _ (mul_nonneg hC hD),
    Real.coe_toNNReal _ hR.le, Real.coe_toNNReal _ hα.le]
  rw [Real.rpow_neg hR.le, div_eq_mul_inv, mul_right_comm _ _ (M + N + D : ℝ)]
  refine mul_le_mul_of_nonneg_right ?_ (by positivity)
  have h5 : (5 : ℝ) ^ α ≤ 5 := by
    simpa using Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 5) hα1
  have h8 : (8 : ℝ) ^ α ≤ 8 := by
    simpa using Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 8) hα1
  have hN := N.coe_nonneg
  have hM := M.coe_nonneg
  have hNM : (0 : ℝ) ≤ N + C * (N + M) := by positivity
  nlinarith [mul_le_mul_of_nonneg_right h5 hNM, mul_le_mul_of_nonneg_right h8 hM,
    mul_nonneg hC (add_nonneg hM hN), Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 5) α]

/-- **The global Hölder estimate from decay at the boundary.** Let `n ≥ 1` be the dimension, let
`r > 1` with `r > n/2`, let `q > 2` with `q > n`, and let `β > 0`. There are `α ∈ (0, β]` and
`C > 0`, depending only on `λ`, `Λ`, `n`, `r`, `q`, `β` and the normalization of the additive Haar
measure `mu`, such that the following holds. Let `a` be measurable and uniformly elliptic on `Ω`
with constants `λ, Λ`, let `f ∈ Lʳ(Ω)` and `F ∈ L^q(Ω; ℝⁿ)`, and let `u ∈ H¹(Ω)` be a weak solution
of `-∂ᵢ(aⁱʲ ∂ⱼu) = f + ∂ᵢFⁱ`, bounded by `M` on `Ω`. Suppose that `u` decays at the points of the
complement of `Ω` with exponent `β`: for `z ∉ Ω` and `0 < ρ ≤ R`, `|u| ≤ N (ρ / R)^β` almost
everywhere on `Ω ∩ B(z, ρ)`. Then the precise representative of the extension of `u` by zero is
Hölder continuous on the whole space with exponent `α` and constant

`C R^(-α) (M + N + (R^(2 - n/r) ‖f‖_{Lʳ(Ω)} + R^(1 - n/q) ‖F‖_{L^q(Ω)}) / λ)`.

No regularity of `∂Ω` and of the coefficients beyond measurability is assumed: the geometry of
the domain enters only through the decay hypothesis. De Giorgi's boundary estimate supplies that
hypothesis for weak solutions vanishing on `∂Ω` when the complement of `Ω` has positive density at
its points, and on a bounded domain the global maximum principle supplies the bound `M`. -/
theorem exists_holderWith_preciseRepresentative_indicator_of_memLp_add_divergence [Nonempty ι]
    {lam Lam : ℝ} {r q : ℝ≥0} (hr : 1 < r) (hrn : (Fintype.card ι : ℝ) < 2 * r)
    (hq : 2 < (q : ℝ)) (hqn : (Fintype.card ι : ℝ) < q) {β : ℝ} (hβ : 0 < β) :
    ∃ (α : ℝ≥0) (C : ℝ), 0 < α ∧ (α : ℝ) ≤ β ∧ 0 < C ∧ ∀ {Omega : Opens (EuclideanSpace ℝ ι)}
      {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ} {f : EuclideanSpace ℝ ι → ℝ}
      {F : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι} {u : W1p mu Omega 2} {R : ℝ} {M N : ℝ≥0},
      UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ ι)) a lam Lam →
      AEStronglyMeasurable a (mu.restrict Omega) →
      MemLp f r (mu.restrict Omega) → MemLp F q (mu.restrict Omega) →
      (∀ v : W1p0 mu Omega 2, energyFormH1 a 0 0 u (v : W1p mu Omega 2) =
        ∫ x in Omega, f x * W1p.value (v : W1p mu Omega 2) x ∂mu -
          ∫ x in Omega, ⟪F x, W1p.gradient (v : W1p mu Omega 2) x⟫ ∂mu) →
      0 < R → (∀ᵐ x ∂mu.restrict Omega, |W1p.value u x| ≤ M) →
      (∀ z ∉ (Omega : Set (EuclideanSpace ℝ ι)), ∀ ρ, 0 < ρ → ρ ≤ R →
        ∀ᵐ x ∂mu.restrict ((Omega : Set (EuclideanSpace ℝ ι)) ∩ ball z ρ),
          |W1p.value u x| ≤ N * (ρ / R) ^ β) →
      HolderWith (C * R ^ (-(α : ℝ)) * (M + N +
          (R ^ (2 - (Fintype.card ι : ℝ) / r) * (eLpNorm f r (mu.restrict Omega)).toReal +
            R ^ (1 - (Fintype.card ι : ℝ) / q) *
              (eLpNorm F q (mu.restrict Omega)).toReal) / lam)).toNNReal α
        (preciseRepresentative mu
          ((Omega : Set (EuclideanSpace ℝ ι)).indicator (W1p.value u))) := by
  obtain ⟨α, C, hα, hαβ, hα1, hC, hosc⟩ :=
    exists_ae_mem_closedBall_add_of_ae_abs_value_le (mu := mu) (lam := lam) (Lam := Lam) hr hrn
      hq hqn hβ
  refine ⟨α.toNNReal, 2 * (13 + 6 * C), Real.toNNReal_pos.2 hα,
    (Real.coe_toNNReal _ hα.le).trans_le hαβ, by positivity, ?_⟩
  intro Omega a f F u R M N h ha hf hF hu hR hM hbdry
  have hΩ : MeasurableSet (Omega : Set (EuclideanSpace ℝ ι)) := Omega.isOpen.measurableSet
  obtain ⟨D, hDdef⟩ : ∃ D : ℝ, D = (R ^ (2 - (Fintype.card ι : ℝ) / r) *
      (eLpNorm f r (mu.restrict Omega)).toReal + R ^ (1 - (Fintype.card ι : ℝ) / q) *
        (eLpNorm F q (mu.restrict Omega)).toReal) / lam := ⟨_, rfl⟩
  have hD : 0 ≤ D := by have := h.pos; rw [hDdef]; positivity
  rw [← hDdef]
  set g := (Omega : Set (EuclideanSpace ℝ ι)).indicator (W1p.value u) with hg
  -- The extension by zero is bounded by every `c ≥ 0` that bounds `u` on `Ω`.
  have hgle : ∀ x {c : ℝ}, 0 ≤ c → (x ∈ (Omega : Set (EuclideanSpace ℝ ι)) →
      |W1p.value u x| ≤ c) → ‖g x‖ ≤ c := fun x c hc hx => by
    rw [hg, norm_indicator_eq_indicator_norm]
    exact indicator_apply_le' (fun hxΩ => (Real.norm_eq_abs _).trans_le (hx hxΩ)) fun _ => hc
  refine (holderWith_preciseRepresentative_of_forall_notMem (μ := mu) (f := g)
    (U := (Omega : Set (EuclideanSpace ℝ ι))) (C₀ := C.toNNReal) (K := (C * D).toNNReal) (M := M)
    (N := N) (α := α.toNNReal) (R := R.toNNReal) (Real.toNNReal_pos.2 hα) (Real.toNNReal_pos.2 hR)
    (((memLp_indicator_iff_restrict hΩ.nullMeasurableSet).2
      (Lp.memLp (W1p.value u))).locallyIntegrable (by norm_num))
    (by filter_upwards [(ae_restrict_iff' hΩ).1 hM] with x hx using hgle x M.coe_nonneg hx)
    ?_ ?_).mono ?_
  · -- Decay at the points outside `Ω`, with the smaller exponent `α`.
    intro z hz ρ hρ hρR
    simp only [Real.coe_toNNReal _ hR.le, Real.coe_toNNReal _ hα.le] at hρR ⊢
    rw [ae_restrict_iff' measurableSet_ball]
    have hpow : (ρ / R) ^ β ≤ (ρ / R) ^ α :=
      Real.rpow_le_rpow_of_exponent_ge (by positivity) ((div_le_one hR).2 hρR) hαβ
    filter_upwards [(ae_restrict_iff' (hΩ.inter measurableSet_ball)).1 (hbdry z hz ρ hρ hρR)]
      with x hx hxb
    exact hgle x (by positivity) fun hxΩ =>
      (hx ⟨hxΩ, hxb⟩).trans (mul_le_mul_of_nonneg_left hpow N.coe_nonneg)
  · -- The interior estimate, transferred from `u` to its extension on balls inside `Ω`.
    intro x ρ _ hρR hball L hL s hs hsρ
    simp only [Real.coe_toNNReal _ hR.le, Real.coe_toNNReal _ hC.le,
      Real.coe_toNNReal _ (mul_nonneg hC.le hD), Real.coe_toNNReal _ hα.le] at hρR ⊢
    have hgu : ∀ᵐ y ∂mu.restrict (ball x ρ), g y = W1p.value u y := by
      filter_upwards [ae_restrict_mem measurableSet_ball] with y hy
      rw [hg, indicator_of_mem (hball hy)]
    obtain ⟨c, hc⟩ := hosc h ha hf hF hu hs hsρ hρR hball (by
      filter_upwards [hL, hgu] with y hy hy'
      rwa [hy', Real.norm_eq_abs] at hy)
    refine ⟨c, ?_⟩
    filter_upwards [hc, ae_restrict_of_ae_restrict_of_subset (ball_subset_ball (by linarith)) hgu]
      with y hy hy'
    rwa [hy', hDdef]
  · exact two_mul_rpow_add_div_le (M := M) (N := N) hα hα1 hC.le hR hD

end PDE

end TauCeti
