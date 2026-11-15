/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.SpecialFunctions.JacobiElliptic.Basic
import TauCeti.Analysis.SpecialFunctions.EllipticIntegral.Elementary
import TauCeti.Analysis.SpecialFunctions.Hyperbolic
import TauCeti.Topology.Algebra.Order.Field

/-!
# Hyperbolic limits of the real Jacobi elliptic functions

As the modulus tends to one from below, the Jacobi amplitude tends pointwise to
`arcsin (tanh u)`. Consequently `sn` tends to `tanh`, and both `cn` and `dn` tend to
`1 / cosh`. These limits describe the transition from periodic elliptic functions to
hyperbolic functions.

The amplitude is nonexpansive in its argument, uniformly in the modulus. Thus convergence
of `F(φ, k)` to `artanh (sin φ)` at a fixed interior amplitude transfers to convergence
of its inverse, without differentiating with respect to the modulus.

## References

* NIST *Digital Library of Mathematical Functions*, §22.5(ii), Table 22.5.4,
  <https://dlmf.nist.gov/22.5>.
-/

public section

namespace TauCeti.Real

open _root_.Real Filter Set
open scoped Topology

/-- As the modulus tends to one from below, the Jacobi amplitude tends pointwise to
`arcsin (tanh u)`. -/
theorem tendsto_jacobiAm_nhdsLT_one (u : ℝ) :
    Tendsto (fun k ↦ jacobiAm k u) (𝓝[<] 1) (𝓝 (arcsin (tanh u))) := by
  have hφ : |arcsin (tanh u)| < π / 2 := by
    rw [abs_lt]
    constructor
    · exact (neg_pi_div_two_lt_arcsin).2 (neg_one_lt_tanh u)
    · exact (arcsin_lt_pi_div_two).2 (tanh_lt_one u)
  have hF : Tendsto (fun k ↦ legendreF (arcsin (tanh u)) k) (𝓝[<] 1) (𝓝 u) := by
    simpa only [sin_arcsin (neg_one_lt_tanh u).le (tanh_lt_one u).le, artanh_tanh]
      using tendsto_legendreF_nhdsLT_one hφ
  have herr : Tendsto (fun k ↦ dist u (legendreF (arcsin (tanh u)) k))
      (𝓝[<] 1) (𝓝 0) := by
    simpa using (tendsto_const_nhds (x := u)).dist hF
  refine tendsto_iff_dist_tendsto_zero.2 (squeeze_zero' ?_ ?_ herr)
  · exact Eventually.of_forall fun _ ↦ dist_nonneg
  · filter_upwards [eventually_sq_lt_one_nhdsLT_one] with k hk
    simpa only [NNReal.coe_one, one_mul, jacobiAm_legendreF hk] using
      (lipschitzWith_jacobiAm k).dist_le_mul u (legendreF (arcsin (tanh u)) k)

/-- `sn(u, k)` tends to `tanh u` as the modulus tends to one from below. -/
theorem tendsto_jacobiSn_nhdsLT_one (u : ℝ) :
    Tendsto (fun k ↦ jacobiSn k u) (𝓝[<] 1) (𝓝 (tanh u)) := by
  simp_rw [jacobiSn_def]
  simpa only [Function.comp_def, sin_arcsin (neg_one_lt_tanh u).le (tanh_lt_one u).le]
    using continuous_sin.continuousAt.tendsto.comp (tendsto_jacobiAm_nhdsLT_one u)

/-- `cn(u, k)` tends to `1 / cosh u` as the modulus tends to one from below. -/
theorem tendsto_jacobiCn_nhdsLT_one (u : ℝ) :
    Tendsto (fun k ↦ jacobiCn k u) (𝓝[<] 1) (𝓝 (1 / cosh u)) := by
  simp_rw [jacobiCn_def]
  simpa only [Function.comp_def, cos_arcsin, sqrt_one_sub_tanh_sq, one_div]
    using continuous_cos.continuousAt.tendsto.comp (tendsto_jacobiAm_nhdsLT_one u)

/-- `dn(u, k)` tends to `1 / cosh u` as the modulus tends to one from below. -/
theorem tendsto_jacobiDn_nhdsLT_one (u : ℝ) :
    Tendsto (fun k ↦ jacobiDn k u) (𝓝[<] 1) (𝓝 (1 / cosh u)) := by
  have hk : Tendsto (fun k : ℝ ↦ k) (𝓝[<] 1) (𝓝 (1 : ℝ)) :=
    tendsto_id.mono_left nhdsWithin_le_nhds
  simpa only [← jacobiDn_def, one_pow, one_mul, sqrt_one_sub_tanh_sq, one_div] using
    ((tendsto_const_nhds (x := (1 : ℝ))).sub
      ((hk.pow 2).mul ((tendsto_jacobiSn_nhdsLT_one u).pow 2))).sqrt

end TauCeti.Real
