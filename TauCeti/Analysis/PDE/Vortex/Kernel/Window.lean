/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Vortex.Kernel.Decay
public import TauCeti.Analysis.PDE.Vortex.WeakKernel
public import TauCeti.Analysis.PDE.Vortex.UniformDerivativeDecay
import TauCeti.Analysis.SpecialFunctions.JapaneseBracket.Exp

/-!
# The kernel of the vortex operator over a compact window of divisors

Let `x` be a smooth plane vortex with the degree-`m` end framing, in the coordinates of
`TauCeti.Vortex.equation`, and let `L_x = d₀* ⊕ d₁` be its gauge-fixed operator
(`TauCeti.Vortex.gaugeFixedOperator`). Its `L²` kernel is finite dimensional and decays
exponentially at every rate below the vacuum mass `1 / 2`, and the `L²`-orthogonal projection `Π`
onto it respects that decay (`TauCeti.Analysis.PDE.Vortex.Kernel.Decay`,
`TauCeti.Analysis.PDE.Vortex.Kernel.Projection`); there the constants depend on the vortex. This
file proves the same estimates with one constant for all vortices of degree `m` whose zeros lie in
a fixed closed disc of radius `r`. Every compact window of the divisor space `Sym^m ℂ`, collisions
of zeros included, lies in such a disc. With `ρ(z) = √(1 + |z|²)`:

* every kernel element `y` satisfies `‖exp(c ρ) y‖₂ ≤ K ‖y‖₂` for `c < 1 / 2`
  (`exists_forall_eLpNorm_exp_mul_smul_le_of_mem_gaugeFixedKernel_of_forall_mem_norm_le`,
  and for the weak `L²` kernel
  `exists_forall_eLpNorm_exp_mul_smul_le_of_mem_weakGaugeFixedKernel_of_forall_mem_norm_le`);
* the kernel projection and the complementary projection satisfy
  `‖exp(c ρ) Π f‖₂ ≤ K ‖exp(c ρ) f‖₂` and `‖exp(c ρ) (f - Π f)‖₂ ≤ K ‖exp(c ρ) f‖₂` for
  `|c| < 1 / 2` (`exists_forall_eLpNorm_exp_mul_smul_starProjection_le_of_forall_mem_norm_le`,
  `exists_forall_eLpNorm_exp_mul_smul_sub_starProjection_le_of_forall_mem_norm_le`).

Together with the uniform estimate for the weak right inverse `Q` orthogonal to the kernel
(`TauCeti.Vortex.exists_forall_eLpNorm_exp_mul_smul_le_of_forall_mem_norm_le`), these are the
exponentially weighted `L²` output estimates for the splitting `y = Π y + Q (L_x y)` with constants
depending only on the window, the degree and the rate. They are the estimates used to correct
approximate solutions glued from plane vortices whose divisors range over a compact window.

**The exterior estimate.** The decay of the kernel is an Agmon estimate whose constant depends
only on the rate and on an exterior estimate `c₁² ∫ |u|² ≤ ∫ |L_x u|²` for variations vanishing on
a disc (`TauCeti.Vortex.exists_forall_eLpNorm_exp_mul_smul_le_of_mem_gaugeFixedKernel`). That
estimate holds wherever the coefficient `vortexMass x = min (P, (12 P - 1) / 8) - |∇₁ α|`, with
`P = |α|² / 4`, of the Weitzenböck formula exceeds `c₁²`
(`TauCeti.Vortex.mul_integral_norm_sq_le_integral_norm_sq_gaugeFixedOperator`). Over the window
both inputs of this coefficient are uniform: `|α|²` is close to one outside a common disc
(`TauCeti.Vortex.exists_forall_lt_normSq_of_forall_mem_norm_le`), and `∇₁ α` decays exponentially
in the distance to the zeros with a constant depending only on `m`
(`TauCeti.Vortex.exists_norm_covariantDerivative_le_mul_exp_of_forall_le_norm_sub`). So the
coefficient exceeds every `a < 1 / 4` outside a common disc
(`TauCeti.Vortex.exists_forall_lt_vortexMass_of_forall_mem_norm_le`), and `L_x` satisfies the
exterior estimate at every mass below `1 / 2` on a common exterior
(`exists_forall_exterior_integral_norm_sq_gaugeFixedOperator_ge_of_forall_mem_norm_le`).

**The projection.** For `u = Π f`, `‖u‖₂² = ⟪u, f⟫ = ⟪exp(-c ρ) u, exp(c ρ) f⟫`, so the decay of
the kernel at the rate `-c` bounds `‖u‖₂` by `‖exp(c ρ) f‖₂`, and its decay at the rate `c` then
bounds `‖exp(c ρ) u‖₂`. No basis of the kernel and no bound on its dimension enter.

The estimates for the weak kernel and the projections are stated at vortices whose coordinates
have bounded derivatives of every order, such as the vortices lying in `A_m^k` for every `k`
(`TauCeti.Vortex.exists_norm_iteratedFDeriv_le_of_forall_mem_framedFieldSpace`); every smooth framed
vortex is carried to one by a smooth framed gauge
(`TauCeti.Vortex.exists_framedGaugeGroup_smul_mem_framedFieldSpace`). Under this hypothesis the
weak kernel consists of smooth kernel elements
(`TauCeti.Vortex.exists_contDiff_and_mem_gaugeFixedKernel_ae_eq_of_mem_weakGaugeFixedKernel`);
this hypothesis is qualitative and does not enter the constants. Nothing here is uniform over the
noncompact moduli space `Sym^m ℂ`: as clusters of zeros separate, the exterior disc grows.

## Main results

All in the namespace `TauCeti.Vortex`, for a degree `m` and a radius `r`, over the smooth plane
vortices with the degree-`m` end framing whose zeros lie in the closed disc of radius `r`:

* `exists_forall_lt_vortexMass_of_forall_mem_norm_le`: `vortexMass x > a` outside a common disc,
  for every `a < 1 / 4`.
* `exists_forall_exterior_integral_norm_sq_gaugeFixedOperator_ge_of_forall_mem_norm_le`: the
  exterior estimate for `L_x` on a common exterior.
* `exists_forall_eLpNorm_exp_mul_smul_le_of_mem_gaugeFixedKernel_of_forall_mem_norm_le`,
  `exists_forall_eLpNorm_exp_mul_smul_le_of_mem_weakGaugeFixedKernel_of_forall_mem_norm_le`:
  uniform exponential decay of the kernel and of the weak kernel.
* `exists_forall_eLpNorm_exp_mul_smul_starProjection_le_of_forall_mem_norm_le`,
  `exists_forall_eLpNorm_exp_mul_smul_sub_starProjection_le_of_forall_mem_norm_le`: the uniform
  weighted estimates for the kernel projection and the complementary projection.

## References

* S. Agmon, *Lectures on Exponential Decay of Solutions of Second-Order Elliptic Equations:
  Bounds on Eigenfunctions of N-Body Schrödinger Operators*, Mathematical Notes 29, Princeton
  University Press, 1982.
* A. Jaffe and C. H. Taubes, *Vortices and Monopoles*, Progress in Physics 2, Birkhäuser, 1980,
  Chapter III.
* C. H. Taubes, *Gr ⇒ SW: From pseudo-holomorphic curves to Seiberg–Witten solutions*,
  J. Differential Geom. 51 (1999), 203–334.
-/

public section

noncomputable section

namespace TauCeti.Vortex

open Complex Filter MeasureTheory
open scoped ENNReal NNReal Topology RealInnerProductSpace ContDiff

/-! ### The exterior estimate over a window -/

/-- **A common exterior for the Weitzenböck coefficient over a window of divisors.** For every
degree `m`, radius `r` and `a < 1 / 4` there is a radius `R > 0` such that every smooth plane vortex
with the degree-`m` end framing whose zeros lie in the closed disc of radius `r` satisfies
`a < vortexMass x z` for every `z` with `‖z‖ > R`. -/
theorem exists_forall_lt_vortexMass_of_forall_mem_norm_le (m : ℕ) (r : ℝ) {a : ℝ}
    (ha : a < 1 / 4) :
    ∃ R > 0, ∀ (x : ℂ → EuclideanSpace ℝ (Fin 4)) (D : Multiset ℂ), ContDiff ℝ ∞ x →
      (∀ z, equation x z = 0) →
      Tendsto (fun z ↦ sectionValue x z * ((z / (‖z‖ : ℂ)) ^ m)⁻¹) (cocompact ℂ) (𝓝 1) →
      IsZeroMultiplicity (sectionValue x) (fun z ↦ D.count z) → (∀ b ∈ D, ‖b‖ ≤ r) →
      ∀ z, R < ‖z‖ → a < vortexMass x z := by
  set δ := 1 / 4 - a with hδa
  have hδ : 0 < δ := sub_pos.2 ha
  -- Outside `R₁`, `|α|² > 1 - δ`.
  obtain ⟨R₁, hR₁⟩ := exists_forall_lt_normSq_of_forall_mem_norm_le m r (θ := 1 - δ)
    (by linarith)
  -- At distance `ρ ≥ max R₂ ρ₀` from the zeros, `|∇₁ α| ≤ K exp (-ρ / 4) < δ / 4`.
  obtain ⟨K, R₂, hK₀, hK⟩ := exists_norm_covariantDerivative_le_mul_exp_of_forall_le_norm_sub m
    (c := 1 / 4) (by norm_num) (by norm_num)
  set ρ₀ := 4 * Real.log (4 * K / δ + 1)
  have hρ₀ : K * Real.exp (-(1 / 4 * ρ₀)) < δ / 4 := by
    have ht : 0 < 4 * K / δ + 1 := by positivity
    have he : Real.exp (-(1 / 4 * ρ₀)) = (4 * K / δ + 1)⁻¹ := by
      rw [show -(1 / 4 * ρ₀) = -Real.log (4 * K / δ + 1) by ring, Real.exp_neg, Real.exp_log ht]
    have hδK : δ / 4 * (4 * K / δ + 1) = K + δ / 4 := by field_simp
    rw [he, ← div_eq_mul_inv, div_lt_iff₀ ht, hδK]
    linarith
  refine ⟨max (max R₁ (r + max R₂ ρ₀)) 1, by positivity,
    fun x D hx hsol hframe hD hDr z hz ↦ ?_⟩
  have hz₁ : R₁ < ‖z‖ := (le_max_left _ _).trans_lt ((le_max_left _ _).trans_lt hz)
  have hz₂ : r + max R₂ ρ₀ < ‖z‖ := (le_max_right _ _).trans_lt ((le_max_left _ _).trans_lt hz)
  have hs := hR₁ x D hx hsol hframe hD hDr z hz₁
  -- Every zero is at distance at least `‖z‖ - r` from `z`.
  have hcov := hK x D hx hsol hframe hD z (‖z‖ - r) (by linarith [le_max_left R₂ ρ₀])
    (fun b hb ↦ by linarith [norm_sub_norm_le z b, hDr b hb]) 1
  rw [norm_one, mul_one] at hcov
  have hexp : K * Real.exp (-(1 / 4 * (‖z‖ - r))) ≤ K * Real.exp (-(1 / 4 * ρ₀)) :=
    mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 (by linarith [le_max_right R₂ ρ₀])) hK₀
  have hmin : 1 / 4 - 3 * δ / 8 <
      min (x z 2 ^ 2 + x z 3 ^ 2) ((12 * (x z 2 ^ 2 + x z 3 ^ 2) - 1) / 8) :=
    lt_min (by linarith) (by linarith)
  rw [vortexMass_def]
  linarith [hδa]

variable {μ : Measure ℂ} [μ.IsAddHaarMeasure]

/-- **Exterior coercivity of the vortex operator, uniformly over a window of divisors.** For every
degree `m`, radius `r` and rate `|c| < 1 / 2` there is a radius `R > 0` such that every smooth plane
vortex `x` with the degree-`m` end framing whose zeros lie in the closed disc of radius `r`
satisfies `c² ∫ |y|² ≤ ∫ |L_x y|²` for every compactly supported `C²` variation `y` vanishing on
the closed disc of radius `R`. -/
theorem exists_forall_exterior_integral_norm_sq_gaugeFixedOperator_ge_of_forall_mem_norm_le (m : ℕ)
    (r : ℝ) {c : ℝ} (hc : |c| < 1 / 2) :
    ∃ R > 0, ∀ (x : ℂ → EuclideanSpace ℝ (Fin 4)) (D : Multiset ℂ), ContDiff ℝ ∞ x →
      (∀ z, equation x z = 0) →
      Tendsto (fun z ↦ sectionValue x z * ((z / (‖z‖ : ℂ)) ^ m)⁻¹) (cocompact ℂ) (𝓝 1) →
      IsZeroMultiplicity (sectionValue x) (fun z ↦ D.count z) → (∀ b ∈ D, ‖b‖ ≤ r) →
      ∀ y : ℂ → EuclideanSpace ℝ (Fin 4), ContDiff ℝ 2 y → HasCompactSupport y →
        (∀ z, ‖z‖ ≤ R → y z = 0) →
        c ^ 2 * (∫ z, ‖y z‖ ^ 2 ∂μ) ≤ ∫ z, ‖gaugeFixedOperator x y z‖ ^ 2 ∂μ := by
  have hc2 : c ^ 2 < 1 / 4 := by nlinarith [sq_abs c, abs_nonneg c]
  obtain ⟨R, hR0, hR⟩ := exists_forall_lt_vortexMass_of_forall_mem_norm_le m r hc2
  exact ⟨R, hR0, fun x D hx hsol hframe hD hDr y hy hyc hzero ↦
    mul_integral_norm_sq_le_integral_norm_sq_gaugeFixedOperator (hx.of_le (by simp)) hy hyc
      (fun z _ ↦ hsol z) fun z hz ↦
        (hR x D hx hsol hframe hD hDr z (lt_of_not_ge fun h ↦ hz (hzero z h))).le⟩

/-! ### Uniform decay of the kernel -/

/-- **Uniform exponential decay of the vortex kernel over a window of divisors.** For every degree
`m`, radius `r` and rate `c < 1 / 2` there is a constant `K` with the following property, where
`ρ(z) = √(1 + |z|²)`. Let `x` be a smooth plane vortex with the degree-`m` end framing whose zeros
lie in the closed disc of radius `r`. Then every `C²` square-integrable solution `y` of `L_x y = 0`
satisfies

`‖exp(c ρ) y‖₂ ≤ K ‖y‖₂`.

The constant depends only on `m`, `r` and `c`, not on the vortex or on the position of its zeros
in the disc, collisions included. -/
theorem exists_forall_eLpNorm_exp_mul_smul_le_of_mem_gaugeFixedKernel_of_forall_mem_norm_le
    (m : ℕ) (r : ℝ) {c : ℝ} (hc : c < 1 / 2) :
    ∃ K : ℝ≥0, ∀ (x : ℂ → EuclideanSpace ℝ (Fin 4)) (D : Multiset ℂ), ContDiff ℝ ∞ x →
      (∀ z, equation x z = 0) →
      Tendsto (fun z ↦ sectionValue x z * ((z / (‖z‖ : ℂ)) ^ m)⁻¹) (cocompact ℂ) (𝓝 1) →
      IsZeroMultiplicity (sectionValue x) (fun z ↦ D.count z) → (∀ b ∈ D, ‖b‖ ≤ r) →
      ∀ y ∈ gaugeFixedKernel x,
        eLpNorm (fun z ↦ Real.exp (c * √(1 + ‖z‖ ^ 2)) • y z) 2 ≤ K * eLpNorm y 2 := by
  -- An exterior mass `c₁` strictly between `max c 0` and `1 / 2`.
  have hd2 : max c 0 < 1 / 2 := max_lt hc (by norm_num)
  have hc₁ : 0 < (max c 0 + 1 / 2) / 2 := by linarith [le_max_right c 0]
  obtain ⟨R, -, hR⟩ :=
    exists_forall_exterior_integral_norm_sq_gaugeFixedOperator_ge_of_forall_mem_norm_le
      (μ := volume) m r (c := (max c 0 + 1 / 2) / 2) (by rw [abs_of_pos hc₁]; linarith)
  obtain ⟨K, hK⟩ := exists_forall_eLpNorm_exp_mul_smul_le_of_mem_gaugeFixedKernel
    (c := c) (c₁ := (max c 0 + 1 / 2) / 2) (by linarith [le_max_left c 0]) hc₁ (R := R)
  exact ⟨K, fun x D hx hsol hframe hD hDr ↦
    hK x hx.continuous (hR x D hx hsol hframe hD hDr)⟩

/-- **Uniform exponential decay of the weak vortex kernel over a window of divisors.** For every
degree `m`, radius `r` and rate `c < 1 / 2` there is a constant `K` with the following property,
where `ρ(z) = √(1 + |z|²)`. Let `x` be a smooth plane vortex with the degree-`m` end framing whose
zeros lie in the closed disc of radius `r` and whose coordinates have bounded derivatives of every
order. Then every element `u` of the weak `L²` kernel of `L_x` satisfies

`‖exp(c ρ) u‖₂ ≤ K ‖u‖₂`.

The constant depends only on `m`, `r` and `c`; the bounds on the derivatives of `x` only identify
the weak kernel with the smooth one. -/
theorem exists_forall_eLpNorm_exp_mul_smul_le_of_mem_weakGaugeFixedKernel_of_forall_mem_norm_le
    (m : ℕ) (r : ℝ) {c : ℝ} (hc : c < 1 / 2) :
    ∃ K : ℝ≥0, ∀ (x : ℂ → EuclideanSpace ℝ (Fin 4)) (D : Multiset ℂ), ContDiff ℝ ∞ x →
      (∀ i n, ∃ C, ∀ z, ‖iteratedFDeriv ℝ n (fun z ↦ x z i) z‖ ≤ C) →
      (∀ z, equation x z = 0) →
      Tendsto (fun z ↦ sectionValue x z * ((z / (‖z‖ : ℂ)) ^ m)⁻¹) (cocompact ℂ) (𝓝 1) →
      IsZeroMultiplicity (sectionValue x) (fun z ↦ D.count z) → (∀ b ∈ D, ‖b‖ ≤ r) →
      ∀ u ∈ weakGaugeFixedKernel x,
        eLpNorm (fun z ↦ Real.exp (c * √(1 + ‖z‖ ^ 2)) • u z) 2 ≤ K * eLpNorm u 2 := by
  obtain ⟨K, hK⟩ :=
    exists_forall_eLpNorm_exp_mul_smul_le_of_mem_gaugeFixedKernel_of_forall_mem_norm_le m r hc
  refine ⟨K, fun x D hx hbound hsol hframe hD hDr u hu ↦ ?_⟩
  obtain ⟨y, -, -, hy, huy⟩ :=
    exists_contDiff_and_mem_gaugeFixedKernel_ae_eq_of_mem_weakGaugeFixedKernel hx hbound hu
  have hw : (fun z ↦ Real.exp (c * √(1 + ‖z‖ ^ 2)) • u z) =ᵐ[volume]
      fun z ↦ Real.exp (c * √(1 + ‖z‖ ^ 2)) • y z := huy.mono fun z hz ↦ by simp only [hz]
  rw [eLpNorm_congr_ae hw, eLpNorm_congr_ae huy]
  exact hK x D hx hsol hframe hD hDr y hy

/-! ### The kernel projection -/

/-- **The weighted estimate for the kernel projection, uniformly over a window of divisors.** For
every degree `m`, radius `r` and rate `|c| < 1 / 2` there is a constant `K` with the following
property, where `ρ(z) = √(1 + |z|²)`. Let `x` be a smooth plane vortex with the degree-`m` end
framing whose zeros lie in the closed disc of radius `r` and whose coordinates have bounded
derivatives of every order, and let `Π` be the `L²`-orthogonal projection onto the weak kernel of
`L_x`. Then every field `f` with `exp(c ρ) f` square integrable satisfies

`‖exp(c ρ) Π f‖₂ ≤ K ‖exp(c ρ) f‖₂`.

The constant depends only on `m`, `r` and `c`. -/
theorem exists_forall_eLpNorm_exp_mul_smul_starProjection_le_of_forall_mem_norm_le
    (m : ℕ) (r : ℝ) {c : ℝ} (hc : |c| < 1 / 2) :
    ∃ K : ℝ≥0, ∀ (x : ℂ → EuclideanSpace ℝ (Fin 4)) (D : Multiset ℂ), ContDiff ℝ ∞ x →
      (∀ i n, ∃ C, ∀ z, ‖iteratedFDeriv ℝ n (fun z ↦ x z i) z‖ ≤ C) →
      (∀ z, equation x z = 0) →
      Tendsto (fun z ↦ sectionValue x z * ((z / (‖z‖ : ℂ)) ^ m)⁻¹) (cocompact ℂ) (𝓝 1) →
      IsZeroMultiplicity (sectionValue x) (fun z ↦ D.count z) → (∀ b ∈ D, ‖b‖ ≤ r) →
      ∀ f : Lp (EuclideanSpace ℝ (Fin 4)) 2 (volume : Measure ℂ),
        MemLp (fun z ↦ Real.exp (c * √(1 + ‖z‖ ^ 2)) • f z) 2 volume →
        eLpNorm (fun z ↦ Real.exp (c * √(1 + ‖z‖ ^ 2)) •
            (weakGaugeFixedKernel x).starProjection f z) 2 volume ≤
          K * eLpNorm (fun z ↦ Real.exp (c * √(1 + ‖z‖ ^ 2)) • f z) 2 volume := by
  obtain ⟨K₁, hK₁⟩ :=
    exists_forall_eLpNorm_exp_mul_smul_le_of_mem_weakGaugeFixedKernel_of_forall_mem_norm_le m r
      (c := c) ((le_abs_self c).trans_lt hc)
  obtain ⟨K₂, hK₂⟩ :=
    exists_forall_eLpNorm_exp_mul_smul_le_of_mem_weakGaugeFixedKernel_of_forall_mem_norm_le m r
      (c := -c) ((neg_le_abs c).trans_lt hc)
  refine ⟨K₁ * K₂, fun x D hx hbound hsol hframe hD hDr f hf ↦ ?_⟩
  set u := (weakGaugeFixedKernel x).starProjection f
  have hu : u ∈ weakGaugeFixedKernel x := (weakGaugeFixedKernel x).starProjection_apply_mem f
  set N := (eLpNorm (fun z ↦ Real.exp (c * √(1 + ‖z‖ ^ 2)) • f z) 2 volume).toReal
  -- The weighted field `exp(-c ρ) u` has `L²` norm at most `K₂ ‖u‖₂`.
  have hu₂ := hK₂ x D hx hbound hsol hframe hD hDr u hu
  have hu₂' : MemLp (fun z ↦ Real.exp (-c * √(1 + ‖z‖ ^ 2)) • u z) 2 volume :=
    memLp_iff.2 (hu₂.trans_lt (ENNReal.mul_lt_top ENNReal.coe_lt_top (Lp.eLpNorm_lt_top u)))
  have hnorm₂ :
      (eLpNorm (fun z ↦ Real.exp (-c * √(1 + ‖z‖ ^ 2)) • u z) 2 volume).toReal ≤ K₂ * ‖u‖ :=
    (ENNReal.toReal_mono (by finiteness) hu₂).trans_eq (by simp [ENNReal.toReal_mul, Lp.norm_def])
  -- `‖u‖₂² = ⟪u, f⟫ = ⟪exp(-c ρ) u, exp(c ρ) f⟫ ≤ K₂ ‖u‖₂ ‖exp(c ρ) f‖₂`.
  have hself : ⟪u, u⟫ = ⟪u, f⟫ := by
    have h := (weakGaugeFixedKernel x).starProjection_inner_eq_zero f u hu
    rw [inner_sub_left] at h
    rw [real_inner_comm f u]
    exact (sub_eq_zero.1 h).symm
  have hsq : ‖u‖ * ‖u‖ ≤ ‖u‖ * (K₂ * N) := by
    rw [← real_inner_self_eq_norm_mul_norm, hself]
    refine (le_abs_self _).trans ((abs_inner_le_of_memLp_exp_mul_smul hu₂' hf).trans ?_)
    exact (mul_le_mul_of_nonneg_right hnorm₂ ENNReal.toReal_nonneg).trans_eq (by ring)
  have hu_le : eLpNorm u 2 volume ≤
      K₂ * eLpNorm (fun z ↦ Real.exp (c * √(1 + ‖z‖ ^ 2)) • f z) 2 volume := by
    refine (ENNReal.toReal_le_toReal (Lp.eLpNorm_ne_top u)
      (ENNReal.mul_ne_top ENNReal.coe_ne_top hf.eLpNorm_ne_top)).1 ?_
    rw [← Lp.norm_def, ENNReal.toReal_mul, ENNReal.coe_toReal]
    rcases (norm_nonneg u).eq_or_lt with h | h
    · rw [← h]
      positivity
    · exact le_of_mul_le_mul_left hsq h
  -- Then `‖exp(c ρ) u‖₂ ≤ K₁ ‖u‖₂ ≤ K₁ K₂ ‖exp(c ρ) f‖₂`.
  calc _ ≤ K₁ * eLpNorm u 2 volume := hK₁ x D hx hbound hsol hframe hD hDr u hu
    _ ≤ K₁ * (K₂ * eLpNorm (fun z ↦ Real.exp (c * √(1 + ‖z‖ ^ 2)) • f z) 2 volume) := by
      gcongr
    _ = _ := by rw [ENNReal.coe_mul, mul_assoc]

/-- **The weighted estimate for the complementary projection, uniformly over a window of
divisors.** For every degree `m`, radius `r` and rate `|c| < 1 / 2` there is a constant `K` with the
following property, where `ρ(z) = √(1 + |z|²)`. Let `x` be a smooth plane vortex with the
degree-`m` end framing whose zeros lie in the closed disc of radius `r` and whose coordinates have
bounded derivatives of every order, and let `Π` be the `L²`-orthogonal projection onto the weak
kernel of `L_x`. Then every field `f` with `exp(c ρ) f` square integrable satisfies

`‖exp(c ρ) (f - Π f)‖₂ ≤ K ‖exp(c ρ) f‖₂`.

The constant depends only on `m`, `r` and `c`. -/
theorem exists_forall_eLpNorm_exp_mul_smul_sub_starProjection_le_of_forall_mem_norm_le
    (m : ℕ) (r : ℝ) {c : ℝ} (hc : |c| < 1 / 2) :
    ∃ K : ℝ≥0, ∀ (x : ℂ → EuclideanSpace ℝ (Fin 4)) (D : Multiset ℂ), ContDiff ℝ ∞ x →
      (∀ i n, ∃ C, ∀ z, ‖iteratedFDeriv ℝ n (fun z ↦ x z i) z‖ ≤ C) →
      (∀ z, equation x z = 0) →
      Tendsto (fun z ↦ sectionValue x z * ((z / (‖z‖ : ℂ)) ^ m)⁻¹) (cocompact ℂ) (𝓝 1) →
      IsZeroMultiplicity (sectionValue x) (fun z ↦ D.count z) → (∀ b ∈ D, ‖b‖ ≤ r) →
      ∀ f : Lp (EuclideanSpace ℝ (Fin 4)) 2 (volume : Measure ℂ),
        MemLp (fun z ↦ Real.exp (c * √(1 + ‖z‖ ^ 2)) • f z) 2 volume →
        eLpNorm (fun z ↦ Real.exp (c * √(1 + ‖z‖ ^ 2)) •
            (f - (weakGaugeFixedKernel x).starProjection f) z) 2 volume ≤
          K * eLpNorm (fun z ↦ Real.exp (c * √(1 + ‖z‖ ^ 2)) • f z) 2 volume := by
  obtain ⟨K, hK⟩ :=
    exists_forall_eLpNorm_exp_mul_smul_starProjection_le_of_forall_mem_norm_le m r hc
  refine ⟨1 + K, fun x D hx hbound hsol hframe hD hDr f hf ↦ ?_⟩
  set g := (weakGaugeFixedKernel x).starProjection f
  -- `exp(c ρ) (f - Π f) = exp(c ρ) f - exp(c ρ) Π f` almost everywhere.
  have hsub : (fun z ↦ Real.exp (c * √(1 + ‖z‖ ^ 2)) • (f - g) z) =ᵐ[volume]
      (fun z ↦ Real.exp (c * √(1 + ‖z‖ ^ 2)) • f z) -
        fun z ↦ Real.exp (c * √(1 + ‖z‖ ^ 2)) • g z := by
    filter_upwards [Lp.coeFn_sub f g] with z hz
    rw [hz, Pi.sub_apply, Pi.sub_apply, smul_sub]
  rw [eLpNorm_congr_ae hsub]
  refine (eLpNorm_sub_le one_le_two).trans ?_
  rw [ENNReal.coe_add, ENNReal.coe_one, add_mul, one_mul]
  gcongr
  exact hK x D hx hbound hsol hframe hD hDr f hf

end TauCeti.Vortex
