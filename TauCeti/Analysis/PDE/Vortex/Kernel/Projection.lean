/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Vortex.ExponentialRegularity
public import TauCeti.Analysis.PDE.Vortex.Kernel.Decay
public import TauCeti.Analysis.PDE.Vortex.WeakKernel
import TauCeti.Analysis.PDE.Vortex.DerivativeDecay

/-!
# Weighted Sobolev estimates for the kernel projection at a plane vortex

At a plane vortex `x`, the gauge-fixed operator `L_x = d₀* ⊕ d₁` (`gaugeFixedOperator`) has a
finite-dimensional weak `L²` kernel `ker L_x = weakGaugeFixedKernel x`, of real dimension `2m` in
degree `m`. The `L²`-orthogonal projection `Π` onto it (`Submodule.starProjection`) and the weak
right inverse `Q` of `L_x` orthogonal to it
(`exists_continuousLinearMap_integral_inner_gaugeFixedAdjoint_eq`) split every `y ∈ H¹` as
`y = Π y + Q (L_x y)`. Correcting approximate solutions built from plane vortices uses both
operators on errors that decay exponentially away from the vortex cores, measured with the weight
`exp(c ρ)`, `ρ(z) = √(1 + |z|²)`, for `|c| < 1/2`. For `Q` the weighted Sobolev estimate
`‖exp(c ρ) Q f‖_(H^(k+1)) ≤ K ‖exp(c ρ) f‖_(H^k)` is
`exists_norm_exp_mul_smul_le_mul_norm_of_integral_inner_gaugeFixedAdjoint_eq`. This file proves the
corresponding estimates for `Π` and for the complementary projection `1 - Π`.

**The kernel.** Every element `u` of the weak kernel decays exponentially at every rate `c < 1/2`:
`exp(c ρ) u` is square integrable (`memLp_exp_mul_smul_of_mem_weakGaugeFixedKernel`), by the
exponential decay of the smooth kernel elements (`memLp_exp_mul_smul_of_mem_gaugeFixedKernel`)
and the elliptic identification of the weak kernel with the smooth one. As a weak solution of
`L_x u = 0`, `exp(c ρ) u` then lies in `H^s` for every `s`
(`exp_mul_smul_mem_sobolevFields_of_mem_weakGaugeFixedKernel`), by weighted elliptic regularity
(`exp_mul_smul_mem_sobolevFields_natCast_add_one_of_memLp`).

**The projection.** For an orthonormal basis `(eᵢ)` of the kernel, `Π f = ∑ᵢ ⟪eᵢ, f⟫ eᵢ`. Writing
`⟪eᵢ, f⟫ = ∫ ⟪exp(-c ρ) eᵢ, exp(c ρ) f⟫` and using the decay of `eᵢ` at the rate `-c`, the
coefficients are bounded by the weighted `L²` norm of `f`, and the decay of `eᵢ` at the rate `c`
with all its derivatives gives

`‖exp(c ρ) Π f‖_(H^s) ≤ K ‖exp(c ρ) f‖_(L²)`

for every `s ≥ 0` (`exists_norm_exp_mul_smul_starProjection_le_mul_eLpNorm`). Only the weighted
`L²` norm of `f` enters, so `Π` gains every derivative; for `c > 0` it maps fields decaying like
`exp(-c ρ)` in `L²` to fields decaying at the same rate with all their derivatives. Consequently
the complementary projection satisfies
`‖exp(c ρ) (f - Π f)‖_(H^s) ≤ K ‖exp(c ρ) f‖_(H^s)`
(`exists_norm_exp_mul_smul_sub_starProjection_le_mul_norm`). Sobolev norms are those of the
coordinates in Mathlib's Bessel-potential spaces `H^s(ℂ)`, as in
`TauCeti.Analysis.PDE.Vortex.EllipticEstimate`.

The statements are given at a smooth vortex with `|α| → 1` whose coordinates have bounded
derivatives of every order, and at a continuous vortex lying in the affine field space `A_m^k` for
every `k` (`exists_norm_exp_mul_smul_starProjection_le_mul_eLpNorm_of_forall_mem_framedFieldSpace`,
`exists_norm_exp_mul_smul_sub_starProjection_le_mul_norm_of_forall_mem_framedFieldSpace`). The
constants depend on the vortex; nothing here is uniform over the moduli space of vortices.

## Main results

* `TauCeti.Vortex.memLp_exp_mul_smul_of_mem_weakGaugeFixedKernel`: weak kernel elements decay
  exponentially in `L²` at every rate below `1/2`.
* `TauCeti.Vortex.exp_mul_smul_mem_sobolevFields_of_mem_weakGaugeFixedKernel`: they decay in every
  Sobolev space `H^s`.
* `TauCeti.Vortex.exists_norm_exp_mul_smul_starProjection_le_mul_eLpNorm`: the weighted Sobolev
  estimate for the kernel projection.
* `TauCeti.Vortex.exists_norm_exp_mul_smul_sub_starProjection_le_mul_norm`: the weighted Sobolev
  estimate for the complementary projection.

## References

* A. Jaffe and C. H. Taubes, *Vortices and Monopoles*, Progress in Physics 2, Birkhäuser, 1980,
  Chapter III.
* C. H. Taubes, *Gr ⇒ SW: From pseudo-holomorphic curves to Seiberg–Witten solutions*,
  J. Differential Geom. 51 (1999), 203–334.
-/

public section

noncomputable section

namespace TauCeti.Vortex

open Complex MeasureTheory Filter BesselPotentialSpace
open scoped Topology RealInnerProductSpace ContDiff BesselPotentialSpace

variable {x : ℂ → EuclideanSpace ℝ (Fin 4)}

/-! ### Exponential decay of the weak kernel -/

/-- **Weak kernel elements decay exponentially.** Let `x` be a smooth solution of the plane vortex
equations with `|α| → 1` at infinity whose coordinates have bounded derivatives of every order. For
every rate `c < 1/2` and every element `u` of the weak `L²` kernel of `L_x`, the field
`exp(c ρ) u`, `ρ(z) = √(1 + |z|²)`, is square integrable. -/
theorem memLp_exp_mul_smul_of_mem_weakGaugeFixedKernel (hx : ContDiff ℝ ∞ x)
    (hbound : ∀ i n, ∃ C, ∀ z, ‖iteratedFDeriv ℝ n (fun z ↦ x z i) z‖ ≤ C)
    (hsol : ∀ z, equation x z = 0)
    (hlim : Tendsto (fun z ↦ 4 * (x z 2 ^ 2 + x z 3 ^ 2)) (cocompact ℂ) (𝓝 1))
    {c : ℝ} (hc : c < 1 / 2) {u : Lp (EuclideanSpace ℝ (Fin 4)) 2 (volume : Measure ℂ)}
    (hu : u ∈ weakGaugeFixedKernel x) :
    MemLp (fun z ↦ Real.exp (c * √(1 + ‖z‖ ^ 2)) • u z) 2 volume := by
  obtain ⟨y, -, -, hy, huy⟩ :=
    exists_contDiff_and_mem_gaugeFixedKernel_ae_eq_of_mem_weakGaugeFixedKernel hx hbound hu
  have hcov := tendsto_covariantDerivative_cocompact (contDiff_euclidean.1 hx 0).continuous
    ((contDiff_euclidean.1 hx 2).of_le (by simp))
    ((contDiff_euclidean.1 hx 3).of_le (by simp)) hsol hlim 1
  refine (memLp_exp_mul_smul_of_mem_gaugeFixedKernel (hx.of_le (by exact_mod_cast le_top)) hsol
    hlim hcov hc hy).ae_eq ?_
  filter_upwards [huy] with z hz
  rw [hz]

/-- **Weak kernel elements decay exponentially in every Sobolev space.** Let `x` be a smooth
solution of the plane vortex equations with `|α| → 1` at infinity whose coordinates have bounded
derivatives of every order. For every rate `c < 1/2` and every element `u` of the weak `L²` kernel
of `L_x`, the field `exp(c ρ) u`, `ρ(z) = √(1 + |z|²)`, lies in `H^s` for every `s`. -/
theorem exp_mul_smul_mem_sobolevFields_of_mem_weakGaugeFixedKernel (hx : ContDiff ℝ ∞ x)
    (hbound : ∀ i n, ∃ C, ∀ z, ‖iteratedFDeriv ℝ n (fun z ↦ x z i) z‖ ≤ C)
    (hsol : ∀ z, equation x z = 0)
    (hlim : Tendsto (fun z ↦ 4 * (x z 2 ^ 2 + x z 3 ^ 2)) (cocompact ℂ) (𝓝 1))
    {c : ℝ} (hc : c < 1 / 2) {u : Lp (EuclideanSpace ℝ (Fin 4)) 2 (volume : Measure ℂ)}
    (hu : u ∈ weakGaugeFixedKernel x) (s : ℝ) :
    (fun z ↦ Real.exp (c * √(1 + ‖z‖ ^ 2)) • u z) ∈ sobolevFields s := by
  obtain ⟨k, hk⟩ := exists_nat_ge s
  have hweak : ∀ η : ℂ → EuclideanSpace ℝ (Fin 4), ContDiff ℝ ∞ η → HasCompactSupport η →
      ∫ z, ⟪u z, gaugeFixedAdjoint x η z⟫ = ∫ z, ⟪(0 : ℂ → EuclideanSpace ℝ (Fin 4)) z, η z⟫ :=
    fun η hη hηc ↦ by
      simpa using (mem_weakGaugeFixedKernel_iff hx.continuous).1 hu η hη hηc
  have hwf : (fun z ↦ Real.exp (c * √(1 + ‖z‖ ^ 2)) • (0 : ℂ → EuclideanSpace ℝ (Fin 4)) z) ∈
      sobolevFields k := by
    convert (sobolevFields k).zero_mem using 1
    funext z
    simp
  refine sobolevFields_mono (s := (k : ℝ) + 1) (by linarith) ?_
  exact exp_mul_smul_mem_sobolevFields_natCast_add_one_of_memLp k hx (fun i n _ ↦ hbound i n)
    (Lp.memLp u) MemLp.zero hweak
    (memLp_exp_mul_smul_of_mem_weakGaugeFixedKernel hx hbound hsol hlim hc hu) hwf

/-! ### The kernel projection -/

/-- The `L²` pairing of a kernel element `e` with a field `f` is bounded by the weighted `L²` norms
`‖exp(-c ρ) e‖₂ ‖exp(c ρ) f‖₂`. -/
private theorem abs_inner_le_of_mem_weakGaugeFixedKernel (hx : ContDiff ℝ ∞ x)
    (hbound : ∀ i n, ∃ C, ∀ z, ‖iteratedFDeriv ℝ n (fun z ↦ x z i) z‖ ≤ C)
    (hsol : ∀ z, equation x z = 0)
    (hlim : Tendsto (fun z ↦ 4 * (x z 2 ^ 2 + x z 3 ^ 2)) (cocompact ℂ) (𝓝 1))
    {c : ℝ} (hc : -c < 1 / 2) {e : Lp (EuclideanSpace ℝ (Fin 4)) 2 (volume : Measure ℂ)}
    (he : e ∈ weakGaugeFixedKernel x) {f : Lp (EuclideanSpace ℝ (Fin 4)) 2 (volume : Measure ℂ)}
    (hf : MemLp (fun z ↦ Real.exp (c * √(1 + ‖z‖ ^ 2)) • f z) 2 volume) :
    |⟪e, f⟫| ≤ (eLpNorm (fun z ↦ Real.exp (-c * √(1 + ‖z‖ ^ 2)) • e z) 2 volume).toReal *
      (eLpNorm (fun z ↦ Real.exp (c * √(1 + ‖z‖ ^ 2)) • f z) 2 volume).toReal := by
  have he' := memLp_exp_mul_smul_of_mem_weakGaugeFixedKernel hx hbound hsol hlim hc he
  -- Moving the weight across the pairing: `⟪e, f⟫ = ⟪exp(-c ρ) e, exp(c ρ) f⟫` in `L²`.
  have hinner : ⟪e, f⟫ = ⟪he'.toLp _, hf.toLp _⟫ := by
    rw [L2.inner_def, L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards [he'.coeFn_toLp, hf.coeFn_toLp] with z hez hfz
    simp only [hez, hfz, real_inner_smul_left, real_inner_smul_right, ← mul_assoc, ← Real.exp_add,
      ← add_mul, add_neg_cancel, zero_mul, Real.exp_zero, one_mul]
  rw [hinner, ← Lp.norm_toLp _ he', ← Lp.norm_toLp _ hf]
  exact abs_real_inner_le_norm _ _

/-- **The weighted Sobolev estimate for the kernel projection.** Let `x` be a smooth solution of the
plane vortex equations with `|α| → 1` at infinity whose coordinates have bounded derivatives of
every order, let `ρ(z) = √(1 + |z|²)`, `|c| < 1/2` and `s ≥ 0`, and let `Π` be the `L²`-orthogonal
projection onto the weak kernel of `L_x`. There is a constant `K` such that for every field `f`
with `exp(c ρ) f` square integrable, `exp(c ρ) Π f` lies in `H^s` with
`‖exp(c ρ) Π f‖_(H^s) ≤ K ‖exp(c ρ) f‖_(L²)`, the Sobolev norm being that of the coordinates. -/
theorem exists_norm_exp_mul_smul_starProjection_le_mul_eLpNorm {s : ℝ} (hs : 0 ≤ s)
    (hx : ContDiff ℝ ∞ x)
    (hbound : ∀ i n, ∃ C, ∀ z, ‖iteratedFDeriv ℝ n (fun z ↦ x z i) z‖ ≤ C)
    (hsol : ∀ z, equation x z = 0)
    (hlim : Tendsto (fun z ↦ 4 * (x z 2 ^ 2 + x z 3 ^ 2)) (cocompact ℂ) (𝓝 1))
    {c : ℝ} (hc : |c| < 1 / 2) :
    ∃ K ≥ 0, ∀ f : Lp (EuclideanSpace ℝ (Fin 4)) 2 (volume : Measure ℂ),
      MemLp (fun z ↦ Real.exp (c * √(1 + ‖z‖ ^ 2)) • f z) 2 volume →
      ∃ u : Fin 4 → H^{s}(ℂ),
        (∀ a, ⇑(inclusionLp hs (u a)) =ᵐ[volume] fun z ↦
          ((Real.exp (c * √(1 + ‖z‖ ^ 2)) • (weakGaugeFixedKernel x).starProjection f z) a : ℂ)) ∧
        ‖u‖ ≤ K * (eLpNorm (fun z ↦ Real.exp (c * √(1 + ‖z‖ ^ 2)) • f z) 2 volume).toReal := by
  have := finiteDimensional_weakGaugeFixedKernel_of_tendsto_normSq hx hbound
    (fun w ↦ by simp [hsol w]) hlim
  set b := stdOrthonormalBasis ℝ (weakGaugeFixedKernel x)
  set e : _ → Lp (EuclideanSpace ℝ (Fin 4)) 2 (volume : Measure ℂ) := fun i ↦ b i
  have he (i) : e i ∈ weakGaugeFixedKernel x := (b i).property
  -- The Sobolev coordinates `v i` of the weighted basis vectors `exp(c ρ) eᵢ`.
  have hv (i) := (mem_sobolevFields_iff_exists_inclusionLp_ae_eq hs).1
    (exp_mul_smul_mem_sobolevFields_of_mem_weakGaugeFixedKernel hx hbound hsol hlim
      (lt_of_le_of_lt (le_abs_self c) hc) (he i) s)
  choose v hv using hv
  set C : _ → ℝ := fun i ↦
    (eLpNorm (fun z ↦ Real.exp (-c * √(1 + ‖z‖ ^ 2)) • e i z) 2 volume).toReal
  refine ⟨∑ i, C i * ‖v i‖, by positivity, fun f hf ↦ ?_⟩
  set N := (eLpNorm (fun z ↦ Real.exp (c * √(1 + ‖z‖ ^ 2)) • f z) 2 volume).toReal
  refine ⟨∑ i, (⟪e i, f⟫ : ℂ) • v i, fun a ↦ ?_, ?_⟩
  · -- Coordinates: `exp(c ρ) Π f = ∑ᵢ ⟪eᵢ, f⟫ exp(c ρ) eᵢ`.
    have hproj : ⇑((weakGaugeFixedKernel x).starProjection f) =ᵐ[volume]
        fun z ↦ ∑ i, ⟪e i, f⟫ • e i z := by
      rw [b.starProjection_eq_sum_rankOne]
      simp only [FunLike.coe_sum, Finset.sum_apply, InnerProductSpace.rankOne_apply]
      refine (Lp.coeFn_finsetSum _ _).trans
        ((eventuallyEq_sum fun i _ ↦ Lp.coeFn_smul _ _).trans ?_)
      filter_upwards with z
      simp [e]
    have hcoord : ⇑(inclusionLp hs ((∑ i, (⟪e i, f⟫ : ℂ) • v i) a)) =ᵐ[volume]
        fun z ↦ ∑ i, (⟪e i, f⟫ : ℂ) * inclusionLp hs (v i a) z := by
      simp only [Finset.sum_apply, Pi.smul_apply, map_sum, map_smul]
      refine (Lp.coeFn_finsetSum _ _).trans
        ((eventuallyEq_sum fun i _ ↦ Lp.coeFn_smul _ _).trans ?_)
      filter_upwards with z
      simp
    filter_upwards [hcoord, hproj, ae_all_iff.2 fun i ↦ hv i a] with z hz hprojz hvz
    simp only [hz, hvz, hprojz, Finset.smul_sum, smul_comm (Real.exp _)]
    simp
  · -- Norm: each coefficient is at most `‖exp(-c ρ) eᵢ‖₂ ‖exp(c ρ) f‖₂`.
    rw [Finset.sum_mul]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ ↦ ?_)
    rw [norm_smul, Complex.norm_real, Real.norm_eq_abs]
    have h := abs_inner_le_of_mem_weakGaugeFixedKernel hx hbound hsol hlim
      (lt_of_le_of_lt (neg_le_abs c) hc) (he i) hf
    calc |⟪e i, f⟫| * ‖v i‖ ≤ C i * N * ‖v i‖ := by gcongr
      _ = C i * ‖v i‖ * N := by ring

/-- **The weighted Sobolev estimate for the complementary projection.** Let `x` be a smooth solution
of the plane vortex equations with `|α| → 1` at infinity whose coordinates have bounded derivatives
of every order, let `ρ(z) = √(1 + |z|²)`, `|c| < 1/2` and `s ≥ 0`, and let `Π` be the
`L²`-orthogonal projection onto the weak kernel of `L_x`. There is a constant `K` such that for
every field `f` with `exp(c ρ) f ∈ H^s`, the component `f - Π f` orthogonal to the kernel satisfies
`‖exp(c ρ) (f - Π f)‖_(H^s) ≤ K ‖exp(c ρ) f‖_(H^s)`, the Sobolev norms being those of the
coordinates. -/
theorem exists_norm_exp_mul_smul_sub_starProjection_le_mul_norm {s : ℝ} (hs : 0 ≤ s)
    (hx : ContDiff ℝ ∞ x)
    (hbound : ∀ i n, ∃ C, ∀ z, ‖iteratedFDeriv ℝ n (fun z ↦ x z i) z‖ ≤ C)
    (hsol : ∀ z, equation x z = 0)
    (hlim : Tendsto (fun z ↦ 4 * (x z 2 ^ 2 + x z 3 ^ 2)) (cocompact ℂ) (𝓝 1))
    {c : ℝ} (hc : |c| < 1 / 2) :
    ∃ K ≥ 0, ∀ f : Lp (EuclideanSpace ℝ (Fin 4)) 2 (volume : Measure ℂ), ∀ v : Fin 4 → H^{s}(ℂ),
      (∀ a, ⇑(inclusionLp hs (v a)) =ᵐ[volume]
        fun z ↦ ((Real.exp (c * √(1 + ‖z‖ ^ 2)) • f z) a : ℂ)) →
      ∃ u : Fin 4 → H^{s}(ℂ),
        (∀ a, ⇑(inclusionLp hs (u a)) =ᵐ[volume] fun z ↦
          ((Real.exp (c * √(1 + ‖z‖ ^ 2)) •
            (f - (weakGaugeFixedKernel x).starProjection f) z) a : ℂ)) ∧
        ‖u‖ ≤ K * ‖v‖ := by
  obtain ⟨K, hK, hKproj⟩ :=
    exists_norm_exp_mul_smul_starProjection_le_mul_eLpNorm hs hx hbound hsol hlim hc
  refine ⟨1 + 4 * K, by positivity, fun f v hv ↦ ?_⟩
  have hf : MemLp (fun z ↦ Real.exp (c * √(1 + ‖z‖ ^ 2)) • f z) 2 volume :=
    memLp_of_forall_inclusionLp_ae_eq hs hv
  obtain ⟨w, hw, hwK⟩ := hKproj f hf
  refine ⟨v - w, fun a ↦ ?_, ?_⟩
  · have hsub : ⇑(inclusionLp hs (v a - w a)) =ᵐ[volume]
        ⇑(inclusionLp hs (v a)) - ⇑(inclusionLp hs (w a)) := by
      rw [map_sub]
      exact Lp.coeFn_sub _ _
    filter_upwards [hsub, hv a, hw a,
      Lp.coeFn_sub f ((weakGaugeFixedKernel x).starProjection f)] with z hz hvz hwz hfz
    simp only [Pi.sub_apply, hz, hvz, hwz, hfz, smul_sub, PiLp.sub_apply, Complex.ofReal_sub]
  · -- `‖exp(c ρ) f‖_(L²) ≤ 4 ‖v‖`.
    have hN : (eLpNorm (fun z ↦ Real.exp (c * √(1 + ‖z‖ ^ 2)) • f z) 2 volume).toReal ≤
        4 * ‖v‖ :=
      ENNReal.toReal_le_of_le_ofReal (by positivity) (eLpNorm_le_of_forall_inclusionLp_ae_eq hs hv)
    calc ‖v - w‖ ≤ ‖v‖ + ‖w‖ := norm_sub_le _ _
      _ ≤ ‖v‖ + K * (4 * ‖v‖) := by gcongr; exact hwK.trans (by gcongr)
      _ = (1 + 4 * K) * ‖v‖ := by ring

/-! ### Vortices of every `A_m^k` -/

/-- **The weighted Sobolev estimate for the kernel projection at a vortex of every `A_m^k`.** Let
`x` be a continuous solution of the plane vortex equations lying in the affine field space `A_m^k`
for every `k`, let `ρ(z) = √(1 + |z|²)`, `|c| < 1/2` and `s ≥ 0`. There is a constant `K` such that
`‖exp(c ρ) Π f‖_(H^s) ≤ K ‖exp(c ρ) f‖_(L²)` for the `L²`-orthogonal projection `Π` onto the weak
kernel of `L_x`, in the sense of `exists_norm_exp_mul_smul_starProjection_le_mul_eLpNorm`. -/
theorem exists_norm_exp_mul_smul_starProjection_le_mul_eLpNorm_of_forall_mem_framedFieldSpace
    {s : ℝ} (hs : 0 ≤ s) {b : ContDiffBump (0 : ℝ)} {m : ℕ} (hx : Continuous x)
    (hmem : ∀ k : ℕ, x ∈ framedFieldSpace b m k) (hsol : ∀ z, equation x z = 0) {c : ℝ}
    (hc : |c| < 1 / 2) :
    ∃ K ≥ 0, ∀ f : Lp (EuclideanSpace ℝ (Fin 4)) 2 (volume : Measure ℂ),
      MemLp (fun z ↦ Real.exp (c * √(1 + ‖z‖ ^ 2)) • f z) 2 volume →
      ∃ u : Fin 4 → H^{s}(ℂ),
        (∀ a, ⇑(inclusionLp hs (u a)) =ᵐ[volume] fun z ↦
          ((Real.exp (c * √(1 + ‖z‖ ^ 2)) • (weakGaugeFixedKernel x).starProjection f z) a : ℂ)) ∧
        ‖u‖ ≤ K * (eLpNorm (fun z ↦ Real.exp (c * √(1 + ‖z‖ ^ 2)) • f z) 2 volume).toReal :=
  exists_norm_exp_mul_smul_starProjection_le_mul_eLpNorm hs
    (contDiff_of_forall_mem_framedFieldSpace hx hmem)
    (exists_norm_iteratedFDeriv_le_of_forall_mem_framedFieldSpace hx hmem) hsol
    (tendsto_normSq_of_mem_framedFieldSpace one_lt_two (by exact_mod_cast hmem 2) hx) hc

/-- **The weighted Sobolev estimate for the complementary projection at a vortex of every
`A_m^k`.** Let `x` be a continuous solution of the plane vortex equations lying in the affine field
space `A_m^k` for every `k`, let `ρ(z) = √(1 + |z|²)`, `|c| < 1/2` and `s ≥ 0`. There is a constant
`K` such that `‖exp(c ρ) (f - Π f)‖_(H^s) ≤ K ‖exp(c ρ) f‖_(H^s)` for the `L²`-orthogonal
projection `Π` onto the weak kernel of `L_x`, in the sense of
`exists_norm_exp_mul_smul_sub_starProjection_le_mul_norm`. -/
theorem exists_norm_exp_mul_smul_sub_starProjection_le_mul_norm_of_forall_mem_framedFieldSpace
    {s : ℝ} (hs : 0 ≤ s) {b : ContDiffBump (0 : ℝ)} {m : ℕ} (hx : Continuous x)
    (hmem : ∀ k : ℕ, x ∈ framedFieldSpace b m k) (hsol : ∀ z, equation x z = 0) {c : ℝ}
    (hc : |c| < 1 / 2) :
    ∃ K ≥ 0, ∀ f : Lp (EuclideanSpace ℝ (Fin 4)) 2 (volume : Measure ℂ), ∀ v : Fin 4 → H^{s}(ℂ),
      (∀ a, ⇑(inclusionLp hs (v a)) =ᵐ[volume]
        fun z ↦ ((Real.exp (c * √(1 + ‖z‖ ^ 2)) • f z) a : ℂ)) →
      ∃ u : Fin 4 → H^{s}(ℂ),
        (∀ a, ⇑(inclusionLp hs (u a)) =ᵐ[volume] fun z ↦
          ((Real.exp (c * √(1 + ‖z‖ ^ 2)) •
            (f - (weakGaugeFixedKernel x).starProjection f) z) a : ℂ)) ∧
        ‖u‖ ≤ K * ‖v‖ :=
  exists_norm_exp_mul_smul_sub_starProjection_le_mul_norm hs
    (contDiff_of_forall_mem_framedFieldSpace hx hmem)
    (exists_norm_iteratedFDeriv_le_of_forall_mem_framedFieldSpace hx hmem) hsol
    (tendsto_normSq_of_mem_framedFieldSpace one_lt_two (by exact_mod_cast hmem 2) hx) hc

end TauCeti.Vortex
