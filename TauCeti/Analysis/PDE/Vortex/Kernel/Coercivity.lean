/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Vortex.WeakKernel
import TauCeti.MeasureTheory.Function.Lp.Norm

/-!
# Coercivity of the gauge-fixed vortex operator modulo its kernel

At a field `x`, the gauge-fixed vortex operator `L_x = d₀* ⊕ d₁` (`gaugeFixedOperator`) has the
weak `L²` kernel `K = weakGaugeFixedKernel x`, a closed subspace of `L²(ℂ; ℝ⁴)`, and its formal
adjoint `L_x*` (`gaugeFixedAdjoint`) is bounded below at a plane vortex by the spectral gap of
`L_x L_x*`. This file shows that the same lower bound controls `L_x` on the `L²`-orthogonal
complement of `K`: if `c ∫ |η|² ≤ ∫ |L_x* η|²` for every compactly supported `C²` field `η`, then
every compactly supported `C¹` field `y`, with `L²` class `u` and `Π` the orthogonal projection
onto `K`, satisfies

`c ‖u - Π u‖² ≤ ∫ |L_x y|²`

(`TauCeti.Vortex.mul_norm_sub_starProjection_sq_le_integral_norm_sq_gaugeFixedOperator`). Indeed,
`y` is a weak solution of `L_x y = f` for its classical image `f = L_x y`, and so is the value
`Q f` of the weak right inverse, which is orthogonal to `K` and has norm at most `c^(-1/2) ‖f‖`
(`TauCeti.Vortex.exists_continuousLinearMap_isMinimalGaugeFixedWeakSolution_of_mul_le`). Their
difference is a weak solution of `L_x w = 0`, so it lies in `K`, and the decomposition
`u = (u - Q f) + Q f` is the orthogonal one: `u - Π u = Q f`.

At a plane vortex with `|α| → 1` the spectral gap supplies the constant
(`TauCeti.Vortex.exists_pos_mul_norm_sub_starProjection_sq_le_integral_norm_sq_gaugeFixedOperator`),
and over the smooth framed vortices of degree `m` one constant serves for the whole moduli space
`Sym^m ℂ`
(`exists_pos_forall_mul_norm_sub_starProjection_sq_le_integral_norm_sq_gaugeFixedOperator`).
At a smooth framed vortex of degree `m`, `K` has dimension `2m`, so `L_x` is coercive away from
a finite-dimensional space: this is the estimate behind the complementary inverses of the normal
block of Taubes's normal model near a pseudoholomorphic curve, where `L_x` acts on each normal
slice.

## Main results

* `TauCeti.Vortex.mul_norm_sub_starProjection_sq_le_integral_norm_sq_gaugeFixedOperator`: a lower
  bound on `L_x*` bounds `L_x` below on the orthogonal complement of its weak kernel.
* `TauCeti.Vortex.exists_pos_mul_norm_sub_starProjection_sq_le_integral_norm_sq_gaugeFixedOperator`:
  the bound at a plane vortex with `|α| → 1`.
* `exists_pos_forall_mul_norm_sub_starProjection_sq_le_integral_norm_sq_gaugeFixedOperator`:
  one constant for all smooth framed plane vortices of degree `m`.

## References

* C. H. Taubes, *Arbitrary N-vortex solutions to the first order Ginzburg–Landau equations*,
  Comm. Math. Phys. 72 (1980), 277–292.
* C. H. Taubes, *Gr ⇒ SW: From pseudo-holomorphic curves to Seiberg–Witten solutions*,
  J. Differential Geom. 51 (1999), 203–334.
-/

public section

namespace TauCeti.Vortex

open MeasureTheory Filter
open scoped RealInnerProductSpace Topology ContDiff

variable {x : ℂ → EuclideanSpace ℝ (Fin 4)}

/-- **Coercivity of `L_x` modulo its weak kernel.** Let `x` be a continuous field and suppose
that `c ∫ |η|² ≤ ∫ |L_x* η|²` for every compactly supported `C²` field `η`, with `c > 0`. Let `y`
be a compactly supported `C¹` field and `u` its class in `L²(ℂ; ℝ⁴)`. Then, with `Π` the
orthogonal projection onto the weak kernel of `L_x`, `c ‖u - Π u‖² ≤ ∫ |L_x y|²`. -/
theorem mul_norm_sub_starProjection_sq_le_integral_norm_sq_gaugeFixedOperator (hx : Continuous x)
    {c : ℝ} (hc : 0 < c)
    (hgap : ∀ η : ℂ → EuclideanSpace ℝ (Fin 4), ContDiff ℝ 2 η → HasCompactSupport η →
      c * ∫ z, ‖η z‖ ^ 2 ≤ ∫ z, ‖gaugeFixedAdjoint x η z‖ ^ 2)
    {y : ℂ → EuclideanSpace ℝ (Fin 4)} (hy : ContDiff ℝ 1 y) (hyc : HasCompactSupport y)
    {u : Lp (EuclideanSpace ℝ (Fin 4)) 2 (volume : Measure ℂ)} (hu : u =ᵐ[volume] y) :
    c * ‖u - (weakGaugeFixedKernel x).starProjection u‖ ^ 2 ≤
      ∫ z, ‖gaugeFixedOperator x y z‖ ^ 2 := by
  obtain ⟨Q, hQn, hQ⟩ := exists_continuousLinearMap_isMinimalGaugeFixedWeakSolution_of_mul_le
    (μ := volume) hx hc hgap
  -- The classical image `f = L_x y` is square integrable.
  have hf : MemLp (gaugeFixedOperator x y) 2 (volume : Measure ℂ) :=
    (continuous_gaugeFixedOperator hx hy).memLp_of_hasCompactSupport
      (hasCompactSupport_gaugeFixedOperator hyc)
  set f := hf.toLp (gaugeFixedOperator x y)
  -- By integration by parts, `u` is a weak solution of `L_x u = f`.
  have hwu : IsGaugeFixedWeakSolution volume x f u := by
    refine isGaugeFixedWeakSolution_iff.2 fun η hη _ ↦ ?_
    calc ∫ z, ⟪u z, gaugeFixedAdjoint x η z⟫
        = ∫ z, ⟪y z, gaugeFixedAdjoint x η z⟫ :=
          integral_congr_ae (hu.mono fun z hz ↦ congrArg (⟪·, gaugeFixedAdjoint x η z⟫) hz)
      _ = ∫ z, ⟪gaugeFixedOperator x y z, η z⟫ :=
          (integral_inner_gaugeFixedOperator hy (hη.of_le one_le_two) (Or.inl hyc)).symm
      _ = ∫ z, ⟪f z, η z⟫ :=
          integral_congr_ae (hf.coeFn_toLp.mono fun z hz ↦ (congrArg (⟪·, η z⟫) hz).symm)
  -- `u - Q f` lies in the weak kernel and `Q f` is orthogonal to it, so `u - Π u = Q f`.
  have hQf := (isMinimalGaugeFixedWeakSolution_iff_mem_orthogonal hx).1 (hQ f)
  have hker : u - Q f ∈ weakGaugeFixedKernel x := by
    rw [← isGaugeFixedWeakSolution_zero_iff_mem_weakGaugeFixedKernel hx, ← sub_self f]
    exact hwu.sub hx hQf.1
  have hproj : (weakGaugeFixedKernel x).starProjection u = u - Q f :=
    Submodule.eq_starProjection_of_mem_orthogonal hker (by rw [sub_sub_cancel]; exact hQf.2)
  rw [hproj, sub_sub_cancel, ← hf.norm_toLp_sq]
  -- `‖Q f‖ ≤ c^(-1/2) ‖f‖`.
  have hle : √c * ‖Q f‖ ≤ ‖f‖ := by
    calc √c * ‖Q f‖ ≤ √c * ((√c)⁻¹ * ‖f‖) :=
          mul_le_mul_of_nonneg_left ((Q.le_opNorm f).trans
            (mul_le_mul_of_nonneg_right hQn (norm_nonneg f))) (Real.sqrt_nonneg c)
      _ = ‖f‖ := by
          rw [← mul_assoc, mul_inv_cancel₀ (Real.sqrt_pos.2 hc).ne', one_mul]
  calc c * ‖Q f‖ ^ 2 = (√c * ‖Q f‖) ^ 2 := by rw [mul_pow, Real.sq_sqrt hc.le]
    _ ≤ ‖f‖ ^ 2 := pow_le_pow_left₀ (by positivity) hle 2

/-- **Coercivity modulo the kernel at a plane vortex.** Let `x` be a `C¹` solution of the plane
vortex equation whose section has modulus tending to one at infinity. There is `c > 0` such that
every compactly supported `C¹` field `y`, with `L²` class `u`, satisfies
`c ‖u - Π u‖² ≤ ∫ |L_x y|²`, where `Π` is the orthogonal projection onto the weak kernel of
`L_x`. -/
theorem exists_pos_mul_norm_sub_starProjection_sq_le_integral_norm_sq_gaugeFixedOperator
    (hx : ContDiff ℝ 1 x) (hsol : ∀ z, equation x z = 0)
    (hlim : Tendsto (fun z ↦ 4 * (x z 2 ^ 2 + x z 3 ^ 2)) (cocompact ℂ) (𝓝 1)) :
    ∃ c > 0, ∀ y : ℂ → EuclideanSpace ℝ (Fin 4), ContDiff ℝ 1 y → HasCompactSupport y →
      ∀ u : Lp (EuclideanSpace ℝ (Fin 4)) 2 (volume : Measure ℂ), u =ᵐ[volume] y →
        c * ‖u - (weakGaugeFixedKernel x).starProjection u‖ ^ 2 ≤
          ∫ z, ‖gaugeFixedOperator x y z‖ ^ 2 := by
  obtain ⟨c, hc, hgap⟩ :=
    exists_pos_mul_integral_norm_sq_le_integral_norm_sq_gaugeFixedAdjoint (μ := volume) hx hsol
      hlim
  exact ⟨c, hc, fun y hy hyc u hu ↦
    mul_norm_sub_starProjection_sq_le_integral_norm_sq_gaugeFixedOperator hx.continuous hc hgap hy
      hyc hu⟩

/-- **Uniform coercivity modulo the kernel over the vortices of degree `m`.** There is `c > 0`,
depending only on `m`, such that at every smooth plane vortex `x` with the degree-`m` end framing
and zero divisor `D`, every compactly supported `C¹` field `y`, with `L²` class `u`, satisfies
`c ‖u - Π u‖² ≤ ∫ |L_x y|²`, where `Π` is the orthogonal projection onto the weak kernel of
`L_x`. The constant is uniform over the whole moduli space `Sym^m ℂ`. -/
theorem exists_pos_forall_mul_norm_sub_starProjection_sq_le_integral_norm_sq_gaugeFixedOperator
    (m : ℕ) :
    ∃ c > 0, ∀ (x : ℂ → EuclideanSpace ℝ (Fin 4)) (D : Multiset ℂ), ContDiff ℝ ∞ x →
      (∀ z, equation x z = 0) →
      Tendsto (fun z ↦ sectionValue x z * ((z / (‖z‖ : ℂ)) ^ m)⁻¹) (cocompact ℂ) (𝓝 1) →
      IsZeroMultiplicity (sectionValue x) (fun z ↦ D.count z) →
      ∀ y : ℂ → EuclideanSpace ℝ (Fin 4), ContDiff ℝ 1 y → HasCompactSupport y →
      ∀ u : Lp (EuclideanSpace ℝ (Fin 4)) 2 (volume : Measure ℂ), u =ᵐ[volume] y →
        c * ‖u - (weakGaugeFixedKernel x).starProjection u‖ ^ 2 ≤
          ∫ z, ‖gaugeFixedOperator x y z‖ ^ 2 := by
  obtain ⟨c, hc, hgap⟩ :=
    exists_pos_forall_mul_integral_norm_sq_le_integral_norm_sq_gaugeFixedAdjoint (μ := volume) m
  exact ⟨c, hc, fun x D hx hsol hlim hD y hy hyc u hu ↦
    mul_norm_sub_starProjection_sq_le_integral_norm_sq_gaugeFixedOperator hx.continuous hc
      (hgap x D hx hsol hlim hD) hy hyc hu⟩

end TauCeti.Vortex
