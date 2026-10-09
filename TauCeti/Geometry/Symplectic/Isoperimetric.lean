/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Fourier.Wirtinger
public import TauCeti.Geometry.Symplectic.CompatibleMetric

/-!
# The isoperimetric inequality in a symplectic vector space

Let `V` be a finite-dimensional real inner product space carrying a symplectic form `ω` and an
almost complex structure `J` whose metric `ω(·, J ·)` is the inner product of `V`, as for the
standard triple `(ω₀, J₀, ⟪·, ·⟫)` on `ℝ²ⁿ`. The symplectic area enclosed by a loop
`γ : [a, b] → V` is `a(γ) = ½ ∫ ω(γ, γ')`: it is `∫ γ^*λ` for the primitive
`λ_x(v) = ½ ω(x, v)` of `ω`, hence the symplectic area of any disc bounding `γ`. The
**isoperimetric inequality** bounds it by the energy of the loop,

`|∫ x in a..b, ω (γ x) (γ' x)| ≤ (b - a) / (2π) * ∫ x in a..b, ‖γ' x‖ ^ 2`
(`TauCeti.SymplecticForm.abs_integral_apply_le`),

that is `|a(γ)| ≤ (b - a) / (4π) * ∫ ‖γ'‖²`. For a loop on `[0, 1]` traversed at constant speed
the right side is `ℓ(γ)² / (4π)`, where `ℓ(γ)` is the length; the constant is attained by round
circles in a complex line. This is the estimate behind removal of singularities for holomorphic
curves: the energy of a holomorphic curve `u` on a disc is the symplectic area enclosed by the
boundary loop `θ ↦ u(r e^{iθ})`, so it is bounded by the energy of that loop.

The inequality comes from Wirtinger's inequality
(`ContinuousLinearMap.norm_integral_apply_apply_le`) and the Cauchy--Schwarz bound
`|ω(v, w)| ≤ ‖v‖ ‖w‖` of a compatible triple (`TauCeti.SymplecticForm.abs_apply_le_norm_mul_norm`,
in `CompatibleMetric.lean`).

## Main results

* `TauCeti.SymplecticForm.abs_integral_apply_le`: the isoperimetric inequality.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed., AMS
  Colloquium Publications **52**, 2012, Section 4.4.
-/

public section

open MeasureTheory Set
open scoped Real Interval RealInnerProductSpace

namespace TauCeti

namespace SymplecticForm

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  {ω : SymplecticForm V} {J : AlmostComplexStructure V} {a b : ℝ}

/-- **The isoperimetric inequality.** If the inner product of `V` is the metric `ω(·, J ·)`, then
for a loop `γ` on `[a, b]` with square-integrable derivative, twice the symplectic area
`∫ ω(γ, γ')` it encloses is bounded by `(b - a) / (2π)` times its energy `∫ ‖γ'‖²`. -/
theorem abs_integral_apply_le (hg : ∀ v w, ω v (J w) = ⟪v, w⟫) (hab : a < b) {γ γ' : ℝ → V}
    (hγ : ∀ x ∈ [[a, b]], HasDerivAt γ (γ' x) x) (hγab : γ a = γ b)
    (hγ' : MemLp γ' 2 (volume.restrict (Ioc a b))) :
    |∫ x in a..b, ω (γ x) (γ' x)| ≤ (b - a) / (2 * π) * ∫ x in a..b, ‖γ' x‖ ^ 2 := by
  let B : V →L[ℝ] V →L[ℝ] ℝ := LinearMap.mkContinuous₂ ω.toBilinForm 1 fun v w => by
    rw [one_mul, Real.norm_eq_abs]
    exact abs_apply_le_norm_mul_norm hg v w
  have hB : ‖B‖ ≤ 1 := LinearMap.mkContinuous₂_norm_le _ zero_le_one _
  have hE : 0 ≤ ∫ x in a..b, ‖γ' x‖ ^ 2 :=
    intervalIntegral.integral_nonneg hab.le fun x _ => by positivity
  have hc : 0 ≤ (b - a) / (2 * π) := div_nonneg (sub_pos.2 hab).le (by positivity)
  calc |∫ x in a..b, ω (γ x) (γ' x)| = ‖∫ x in a..b, B (γ x) (γ' x)‖ := by
        simp [B, Real.norm_eq_abs]
    _ ≤ ‖B‖ * ((b - a) / (2 * π)) * ∫ x in a..b, ‖γ' x‖ ^ 2 :=
      B.norm_integral_apply_apply_le hab hγ hγab hγ'
    _ ≤ 1 * ((b - a) / (2 * π)) * ∫ x in a..b, ‖γ' x‖ ^ 2 := by gcongr
    _ = (b - a) / (2 * π) * ∫ x in a..b, ‖γ' x‖ ^ 2 := by rw [one_mul]

end SymplecticForm

end TauCeti
