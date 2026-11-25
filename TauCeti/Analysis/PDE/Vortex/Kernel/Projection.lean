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
import TauCeti.Analysis.SpecialFunctions.JapaneseBracket.Exp

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
`⟪eᵢ, f⟫ = ∫ ⟪exp(-c ρ) eᵢ, exp(c ρ) f⟫` (`TauCeti.abs_inner_le_of_memLp_exp_mul_smul`) and
using the decay of `eᵢ` at the rate `-c`, the coefficients are bounded by the weighted `L²` norm
of `f`, and the decay of `eᵢ` at the rate `c` with all its derivatives gives

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
constants of these Sobolev estimates depend on the vortex.

**Uniformity over windows of divisors.** In `L²`, the weighted estimates hold with one constant for
all smooth framed vortices of degree `m` whose zeros lie in a fixed disc, collisions of zeros
included; every compact window of `Sym ℂ m` lies in such a disc. The decay of the kernel is uniform
there (`exists_forall_eLpNorm_exp_mul_smul_le_of_mem_weakGaugeFixedKernel_of_forall_mem_norm_le`),
because the exterior estimate behind it is. The projection is then estimated without a basis of
the kernel: `p = Π f` satisfies `‖p‖₂² = ⟪p, f⟫ ≤ ‖exp(-c ρ) p‖₂ ‖exp(c ρ) f‖₂`, and of the two
weights `exp(± c ρ)` on `p` one is at most one while the other is controlled by the uniform decay.
This gives `‖exp(c ρ) Π f‖₂ ≤ K ‖exp(c ρ) f‖₂` and `‖exp(c ρ) (f - Π f)‖₂ ≤ K ‖exp(c ρ) f‖₂` with
`K` depending only on `m`, the radius of the disc and `c`
(`exists_forall_eLpNorm_exp_mul_smul_starProjection_le_of_forall_mem_norm_le`,
`exists_forall_eLpNorm_exp_mul_smul_sub_starProjection_le_of_forall_mem_norm_le`). Nothing here is
uniform over the whole noncompact moduli space of vortices.

## Main results

* `TauCeti.Vortex.memLp_exp_mul_smul_of_mem_weakGaugeFixedKernel`: weak kernel elements decay
  exponentially in `L²` at every rate below `1/2`.
* `TauCeti.Vortex.exp_mul_smul_mem_sobolevFields_of_mem_weakGaugeFixedKernel`: they decay in every
  Sobolev space `H^s`.
* `TauCeti.Vortex.exists_norm_exp_mul_smul_starProjection_le_mul_eLpNorm`: the weighted Sobolev
  estimate for the kernel projection.
* `TauCeti.Vortex.exists_norm_exp_mul_smul_sub_starProjection_le_mul_norm`: the weighted Sobolev
  estimate for the complementary projection.
* `TauCeti.Vortex.exists_forall_eLpNorm_exp_mul_smul_starProjection_le_of_forall_mem_norm_le`,
  `TauCeti.Vortex.exists_forall_eLpNorm_exp_mul_smul_sub_starProjection_le_of_forall_mem_norm_le`:
  the weighted `L²` estimates for both projections, uniformly over a window of divisors.

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
open scoped Topology RealInnerProductSpace ContDiff BesselPotentialSpace NNReal ENNReal

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
    have h := abs_inner_le_of_memLp_exp_mul_smul
      (memLp_exp_mul_smul_of_mem_weakGaugeFixedKernel hx hbound hsol hlim
        (lt_of_le_of_lt (neg_le_abs c) hc) (he i)) hf
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
    memLp_of_mem_sobolevFields ((mem_sobolevFields_iff_exists_inclusionLp_ae_eq hs).2 ⟨v, hv⟩)
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

/-! ### Uniformity over windows of divisors -/

/-- **Exponential decay of the weak kernel, uniformly over a window of divisors.** For every
degree `m`, radius `R₀` and rate `c < 1/2` there is a constant `K` with the following property,
where `ρ(z) = √(1 + |z|²)`. Let `x` be a smooth plane vortex with the degree-`m` end framing whose
zeros lie in the closed disc of radius `R₀` and whose coordinates have bounded derivatives of every
order. Then every element `u` of the weak `L²` kernel of `L_x` satisfies `‖exp(c ρ) u‖₂ ≤ K ‖u‖₂`.
The constant depends only on `m`, `R₀` and `c`; the derivative bounds only serve to identify the
weak kernel with the smooth one. -/
theorem exists_forall_eLpNorm_exp_mul_smul_le_of_mem_weakGaugeFixedKernel_of_forall_mem_norm_le
    (m : ℕ) (R₀ : ℝ) {c : ℝ} (hc : c < 1 / 2) :
    ∃ K : ℝ≥0, ∀ (x : ℂ → EuclideanSpace ℝ (Fin 4)) (D : Multiset ℂ), ContDiff ℝ ∞ x →
      (∀ i n, ∃ C, ∀ z, ‖iteratedFDeriv ℝ n (fun z ↦ x z i) z‖ ≤ C) →
      (∀ z, equation x z = 0) →
      Tendsto (fun z ↦ sectionValue x z * ((z / (‖z‖ : ℂ)) ^ m)⁻¹) (cocompact ℂ) (𝓝 1) →
      IsZeroMultiplicity (sectionValue x) (fun z ↦ D.count z) → (∀ b ∈ D, ‖b‖ ≤ R₀) →
      ∀ u ∈ weakGaugeFixedKernel x,
        eLpNorm (fun z ↦ Real.exp (c * √(1 + ‖z‖ ^ 2)) • u z) 2 volume ≤
          K * eLpNorm u 2 volume := by
  obtain ⟨K, hK⟩ :=
    exists_forall_eLpNorm_exp_mul_smul_le_of_mem_gaugeFixedKernel_of_forall_mem_norm_le m R₀ hc
  refine ⟨K, fun x D hx hbound hsol hframe hD hD₀ u hu ↦ ?_⟩
  obtain ⟨y, -, -, hy, huy⟩ :=
    exists_contDiff_and_mem_gaugeFixedKernel_ae_eq_of_mem_weakGaugeFixedKernel hx hbound hu
  have hw : (fun z ↦ Real.exp (c * √(1 + ‖z‖ ^ 2)) • u z) =ᵐ[volume]
      fun z ↦ Real.exp (c * √(1 + ‖z‖ ^ 2)) • y z := by
    filter_upwards [huy] with z hz
    rw [hz]
  rw [eLpNorm_congr_ae hw, eLpNorm_congr_ae huy]
  exact hK x D hx hsol hframe hD hD₀ y hy

/-- At a vortex, the projection `p = Π f` onto the weak kernel satisfies
`‖p‖₂² = ⟪p, f⟫ ≤ ‖exp(-c ρ) p‖₂ ‖exp(c ρ) f‖₂`. So if the weight `exp(-c ρ)` costs at most `a` on
`p` and the weight `exp(c ρ)` at most `b`, then `‖exp(c ρ) p‖₂ ≤ b a ‖exp(c ρ) f‖₂`. -/
private theorem eLpNorm_exp_mul_smul_starProjection_le (hx : ContDiff ℝ ∞ x)
    (hbound : ∀ i n, ∃ C, ∀ z, ‖iteratedFDeriv ℝ n (fun z ↦ x z i) z‖ ≤ C)
    (hsol : ∀ z, equation x z = 0)
    (hlim : Tendsto (fun z ↦ 4 * (x z 2 ^ 2 + x z 3 ^ 2)) (cocompact ℂ) (𝓝 1))
    {c : ℝ} (hc : -c < 1 / 2) {f : Lp (EuclideanSpace ℝ (Fin 4)) 2 (volume : Measure ℂ)}
    (hf : MemLp (fun z ↦ Real.exp (c * √(1 + ‖z‖ ^ 2)) • f z) 2 volume) {a b : ℝ≥0}
    (ha : eLpNorm (fun z ↦ Real.exp (-c * √(1 + ‖z‖ ^ 2)) •
      (weakGaugeFixedKernel x).starProjection f z) 2 volume ≤
        a * eLpNorm ((weakGaugeFixedKernel x).starProjection f) 2 volume)
    (hb : eLpNorm (fun z ↦ Real.exp (c * √(1 + ‖z‖ ^ 2)) •
      (weakGaugeFixedKernel x).starProjection f z) 2 volume ≤
        b * eLpNorm ((weakGaugeFixedKernel x).starProjection f) 2 volume) :
    eLpNorm (fun z ↦ Real.exp (c * √(1 + ‖z‖ ^ 2)) •
      (weakGaugeFixedKernel x).starProjection f z) 2 volume ≤
        (b * a : ℝ≥0) * eLpNorm (fun z ↦ Real.exp (c * √(1 + ‖z‖ ^ 2)) • f z) 2 volume := by
  set p := (weakGaugeFixedKernel x).starProjection f
  set N := eLpNorm (fun z ↦ Real.exp (c * √(1 + ‖z‖ ^ 2)) • f z) 2 volume
  -- `‖p‖₂² = ⟪p, f⟫`, since `f - p` is orthogonal to the kernel.
  have hpf : ⟪p, f⟫ = ‖p‖ ^ 2 := by
    have h := (weakGaugeFixedKernel x).re_inner_starProjection_eq_normSq f
    rwa [RCLike.re_to_real, ← Submodule.norm_coe, ← Submodule.starProjection_apply] at h
  have hpair : |⟪p, f⟫| ≤
      (eLpNorm (fun z ↦ Real.exp (-c * √(1 + ‖z‖ ^ 2)) • p z) 2 volume).toReal * N.toReal :=
    abs_inner_le_of_memLp_exp_mul_smul (memLp_exp_mul_smul_of_mem_weakGaugeFixedKernel hx hbound
      hsol hlim hc ((weakGaugeFixedKernel x).starProjection_apply_mem f)) hf
  have ha' : (eLpNorm (fun z ↦ Real.exp (-c * √(1 + ‖z‖ ^ 2)) • p z) 2 volume).toReal ≤
      a * ‖p‖ := by
    simpa [Lp.norm_def, ENNReal.toReal_mul] using ENNReal.toReal_mono
      (ENNReal.mul_ne_top ENNReal.coe_ne_top (Lp.eLpNorm_ne_top p)) ha
  -- Hence `‖p‖₂ ≤ a ‖exp(c ρ) f‖₂`.
  have hP : ‖p‖ ≤ a * N.toReal := by
    have h₁ : ‖p‖ ^ 2 ≤ a * ‖p‖ * N.toReal := by
      rw [← hpf]
      exact (le_abs_self _).trans
        (hpair.trans (mul_le_mul_of_nonneg_right ha' ENNReal.toReal_nonneg))
    rcases (norm_nonneg p).eq_or_lt with h | h
    · rw [← h]
      positivity
    · nlinarith
  calc _ ≤ b * eLpNorm p 2 volume := hb
    _ = b * ENNReal.ofReal ‖p‖ := by rw [Lp.norm_def, ENNReal.ofReal_toReal (Lp.eLpNorm_ne_top p)]
    _ ≤ b * ENNReal.ofReal (a * N.toReal) := by gcongr
    _ = (b * a : ℝ≥0) * N := by
      rw [ENNReal.ofReal_mul a.coe_nonneg, ENNReal.ofReal_coe_nnreal,
        ENNReal.ofReal_toReal hf.eLpNorm_ne_top, ENNReal.coe_mul, mul_assoc]

/-- **The weighted estimate for the kernel projection, uniformly over a window of divisors.** For
every degree `m`, radius `R₀` and rate `|c| < 1/2` there is a constant `K` with the following
property, where `ρ(z) = √(1 + |z|²)`. Let `x` be a smooth plane vortex with the degree-`m` end
framing whose zeros lie in the closed disc of radius `R₀` and whose coordinates have bounded
derivatives of every order, and let `Π` be the `L²`-orthogonal projection onto the weak kernel of
`L_x`. Then every field `f` with `exp(c ρ) f` square integrable satisfies

`‖exp(c ρ) Π f‖₂ ≤ K ‖exp(c ρ) f‖₂`.

The constant depends only on `m`, `R₀` and `c`, not on the vortex or on the position of its zeros
in the disc, collisions included. -/
theorem exists_forall_eLpNorm_exp_mul_smul_starProjection_le_of_forall_mem_norm_le (m : ℕ)
    (R₀ : ℝ) {c : ℝ} (hc : |c| < 1 / 2) :
    ∃ K : ℝ≥0, ∀ (x : ℂ → EuclideanSpace ℝ (Fin 4)) (D : Multiset ℂ), ContDiff ℝ ∞ x →
      (∀ i n, ∃ C, ∀ z, ‖iteratedFDeriv ℝ n (fun z ↦ x z i) z‖ ≤ C) →
      (∀ z, equation x z = 0) →
      Tendsto (fun z ↦ sectionValue x z * ((z / (‖z‖ : ℂ)) ^ m)⁻¹) (cocompact ℂ) (𝓝 1) →
      IsZeroMultiplicity (sectionValue x) (fun z ↦ D.count z) → (∀ b ∈ D, ‖b‖ ≤ R₀) →
      ∀ f : Lp (EuclideanSpace ℝ (Fin 4)) 2 (volume : Measure ℂ),
        MemLp (fun z ↦ Real.exp (c * √(1 + ‖z‖ ^ 2)) • f z) 2 volume →
        eLpNorm (fun z ↦ Real.exp (c * √(1 + ‖z‖ ^ 2)) •
          (weakGaugeFixedKernel x).starProjection f z) 2 volume ≤
            K * eLpNorm (fun z ↦ Real.exp (c * √(1 + ‖z‖ ^ 2)) • f z) 2 volume := by
  obtain ⟨K, hK⟩ :=
    exists_forall_eLpNorm_exp_mul_smul_le_of_mem_weakGaugeFixedKernel_of_forall_mem_norm_le m R₀
      hc
  refine ⟨K, fun x D hx hbound hsol hframe hD hD₀ f hf ↦ ?_⟩
  set p := (weakGaugeFixedKernel x).starProjection f
  have hKp := hK x D hx hbound hsol hframe hD hD₀ p
    ((weakGaugeFixedKernel x).starProjection_apply_mem f)
  -- A smaller rate gives a smaller weighted norm.
  have hmono (c' c'' : ℝ) (h : c' ≤ c'') :
      eLpNorm (fun z ↦ Real.exp (c' * √(1 + ‖z‖ ^ 2)) • p z) 2 volume ≤
        eLpNorm (fun z ↦ Real.exp (c'' * √(1 + ‖z‖ ^ 2)) • p z) 2 volume := by
    have hW : Continuous fun z : ℂ ↦ Real.exp (c' * √(1 + ‖z‖ ^ 2)) :=
      (contDiff_exp_mul_sqrt_add_norm_sq (n := 0) c' one_pos).continuous
    refine eLpNorm_mono (hW.aestronglyMeasurable.smul (Lp.aestronglyMeasurable p)) fun z ↦ ?_
    rw [norm_smul, norm_smul, Real.norm_of_nonneg (Real.exp_pos _).le,
      Real.norm_of_nonneg (Real.exp_pos _).le]
    gcongr
  -- So the weights of rate at most `|c|` cost at most `K`, those of rate at most `0` at most `1`.
  have hw (c' : ℝ) (h : c' ≤ |c|) :
      eLpNorm (fun z ↦ Real.exp (c' * √(1 + ‖z‖ ^ 2)) • p z) 2 volume ≤
        K * eLpNorm p 2 volume := (hmono c' |c| h).trans hKp
  have hw₀ (c' : ℝ) (h : c' ≤ 0) :
      eLpNorm (fun z ↦ Real.exp (c' * √(1 + ‖z‖ ^ 2)) • p z) 2 volume ≤
        (1 : ℝ≥0) * eLpNorm p 2 volume := by
    simpa using hmono c' 0 h
  have hlim := tendsto_normSq_of_tendsto_sectionValue_mul_inv_pow hframe
  have hc' : -c < 1 / 2 := (neg_le_abs c).trans_lt hc
  rcases le_total 0 c with h0 | h0
  · simpa using eLpNorm_exp_mul_smul_starProjection_le hx hbound hsol hlim hc' hf
      (hw₀ (-c) (by linarith)) (hw c (le_abs_self c))
  · simpa using eLpNorm_exp_mul_smul_starProjection_le hx hbound hsol hlim hc' hf
      (hw (-c) (neg_le_abs c)) (hw₀ c h0)

/-- **The weighted estimate for the complementary projection, uniformly over a window of
divisors.** For every degree `m`, radius `R₀` and rate `|c| < 1/2` there is a constant `K` such
that, under the hypotheses of
`exists_forall_eLpNorm_exp_mul_smul_starProjection_le_of_forall_mem_norm_le`, the component
`f - Π f` orthogonal to the weak kernel satisfies `‖exp(c ρ) (f - Π f)‖₂ ≤ K ‖exp(c ρ) f‖₂`. The
constant depends only on `m`, `R₀` and `c`. -/
theorem exists_forall_eLpNorm_exp_mul_smul_sub_starProjection_le_of_forall_mem_norm_le (m : ℕ)
    (R₀ : ℝ) {c : ℝ} (hc : |c| < 1 / 2) :
    ∃ K : ℝ≥0, ∀ (x : ℂ → EuclideanSpace ℝ (Fin 4)) (D : Multiset ℂ), ContDiff ℝ ∞ x →
      (∀ i n, ∃ C, ∀ z, ‖iteratedFDeriv ℝ n (fun z ↦ x z i) z‖ ≤ C) →
      (∀ z, equation x z = 0) →
      Tendsto (fun z ↦ sectionValue x z * ((z / (‖z‖ : ℂ)) ^ m)⁻¹) (cocompact ℂ) (𝓝 1) →
      IsZeroMultiplicity (sectionValue x) (fun z ↦ D.count z) → (∀ b ∈ D, ‖b‖ ≤ R₀) →
      ∀ f : Lp (EuclideanSpace ℝ (Fin 4)) 2 (volume : Measure ℂ),
        MemLp (fun z ↦ Real.exp (c * √(1 + ‖z‖ ^ 2)) • f z) 2 volume →
        eLpNorm (fun z ↦ Real.exp (c * √(1 + ‖z‖ ^ 2)) •
          (f - (weakGaugeFixedKernel x).starProjection f) z) 2 volume ≤
            K * eLpNorm (fun z ↦ Real.exp (c * √(1 + ‖z‖ ^ 2)) • f z) 2 volume := by
  obtain ⟨K, hK⟩ := exists_forall_eLpNorm_exp_mul_smul_starProjection_le_of_forall_mem_norm_le m
    R₀ hc
  refine ⟨1 + K, fun x D hx hbound hsol hframe hD hD₀ f hf ↦ ?_⟩
  set p := (weakGaugeFixedKernel x).starProjection f
  have hw : (fun z ↦ Real.exp (c * √(1 + ‖z‖ ^ 2)) • (f - p) z) =ᵐ[volume]
      (fun z ↦ Real.exp (c * √(1 + ‖z‖ ^ 2)) • f z) -
        fun z ↦ Real.exp (c * √(1 + ‖z‖ ^ 2)) • p z := by
    filter_upwards [Lp.coeFn_sub f p] with z hz
    rw [hz]
    simp only [Pi.sub_apply, smul_sub]
  rw [eLpNorm_congr_ae hw, ENNReal.coe_add, ENNReal.coe_one, add_mul, one_mul]
  exact (eLpNorm_sub_le one_le_two).trans
    (add_le_add le_rfl (hK x D hx hbound hsol hframe hD hD₀ f hf))

end TauCeti.Vortex
