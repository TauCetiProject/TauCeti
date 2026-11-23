/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import TauCeti.Analysis.Calculus.ParametricFDeriv

/-!
# Consistent reference demand

A reference demand `D(x, y)` for an asset, as a function of its spot price `x > 0` and of the
income `y > 0` of the reference traders, is *consistent* with exponent `γ`
(`TauCeti.Finance.IsConsistentDemand`) if its partial derivatives satisfy

`D_y / D_x = -γ x / y`

throughout the open positive quadrant. In the feedback model of Sircar and Papanicolaou this is
the coefficient condition under which, without program trading, an income with percentage
volatility `η` induces through market clearing an asset price with the constant percentage
volatility `γ η` of the Black–Scholes model. This file treats only the analytic condition on `D`;
no asset, income process or clearing equilibrium is constructed.

The prototype is a demand `U (y ^ γ / x)` that depends on spot and income only through the
invariant coordinate `y ^ γ / x` (`TauCeti.Finance.consistentDemand`), the linear demand
`d₀ y ^ γ / x` being the case `U z = d₀ z`. The main result is that these are all consistent
demands: for jointly `C¹` demand with negative spot derivative, the ratio identity holds on the
quadrant if and only if `D = U (y ^ γ / x)` there for a `C¹` profile `U` with `U' > 0` on
`(0, ∞)` (`TauCeti.Finance.isConsistentDemand_iff_exists_profile`).

* Away from zeros of `D_x`, the ratio identity is the first-order equation
  `γ x D_x + y D_y = 0` (`TauCeti.Finance.isConsistentDemand_iff_of_deriv_ne_zero`), which says
  that `D` is constant along the scaling orbits `s ↦ (c s ^ γ, s)` of the vector field
  `γ x ∂_x + y ∂_y`. Each orbit meets the line `y = 1` exactly once, at spot `x / y ^ γ`, so a
  differentiable solution is `D x y = D (x / y ^ γ) 1`, that is, `D = U (y ^ γ / x)` with profile
  `U z = D z⁻¹ 1` (`TauCeti.Finance.eq_consistentDemand_of_scaling`). This holds for every real
  `γ`; the profile on the line `x = 1` is `z ↦ D 1 (z ^ γ⁻¹)` when `γ ≠ 0`
  (`TauCeti.Finance.consistentDemand_one_rpow_inv`).
* The profile has derivative `U'(z) = -D_x(z⁻¹, 1) / z²`
  (`TauCeti.Finance.hasDerivAt_profile_inv_one`), so negative spot derivative gives `U' > 0`;
  strict monotonicity of `D` in spot alone would not give this derivative bound.
* Conversely, every profile with nonvanishing derivative on `(0, ∞)` gives a consistent demand
  (`TauCeti.Finance.isConsistentDemand_consistentDemand`), with `D_x = -(y ^ γ / x ²) U'` and
  `D_y = γ y ^ (γ - 1) / x U'`; in particular `U' > 0` gives `D_x < 0` and, for `γ > 0`,
  `D_y > 0`.
* The profile of a consistent demand is unique on `(0, ∞)`
  (`TauCeti.Finance.consistentDemand_eq_consistentDemand_iff`).

The characterization uses the ratio identity on the whole quadrant. It does not determine `D`
from consistency on a single clearing level set, nor treat time- or state-dependent
coefficients.

## References

* K. R. Sircar and G. Papanicolaou, *General Black–Scholes models accounting for increased
  market volatility from hedging strategies*, Applied Mathematical Finance 5 (1998), 45–82,
  Proposition 1.
-/

public section

noncomputable section

open Set Function

namespace TauCeti.Finance

variable {γ x y : ℝ} {U V : ℝ → ℝ} {D E : ℝ → ℝ → ℝ}

/-! ### Demand through the invariant coordinate -/

/-- The reference demand `U (y ^ γ / x)` with profile `U`, at spot `x` and income `y`. It depends
on spot and income only through the invariant coordinate `y ^ γ / x`. -/
def consistentDemand (γ : ℝ) (U : ℝ → ℝ) (x y : ℝ) : ℝ :=
  U (y ^ γ / x)

/-- Unfolding lemma for `consistentDemand`. -/
theorem consistentDemand_def (γ : ℝ) (U : ℝ → ℝ) (x y : ℝ) :
    consistentDemand γ U x y = U (y ^ γ / x) :=
  (rfl)

/-- At unit income and spot `z⁻¹` the demand is the profile value `U z`. -/
@[simp]
theorem consistentDemand_inv_one (γ : ℝ) (U : ℝ → ℝ) (z : ℝ) :
    consistentDemand γ U z⁻¹ 1 = U z := by
  simp [consistentDemand_def]

/-- At unit spot and income `z ^ γ⁻¹` the demand is the profile value `U z`. -/
theorem consistentDemand_one_rpow_inv (U : ℝ → ℝ) (hγ : γ ≠ 0) {z : ℝ} (hz : 0 ≤ z) :
    consistentDemand γ U 1 (z ^ γ⁻¹) = U z := by
  rw [consistentDemand_def, Real.rpow_inv_rpow hz hγ, div_one]

/-- The profile of a demand through the invariant coordinate is unique on `(0, ∞)`: two profiles
give the same demand on the open positive quadrant exactly when they agree on `(0, ∞)`. -/
theorem consistentDemand_eq_consistentDemand_iff :
    (∀ x y, 0 < x → 0 < y → consistentDemand γ U x y = consistentDemand γ V x y) ↔
      EqOn U V (Ioi 0) := by
  refine ⟨fun h z hz => ?_, fun h x y hx hy => h (by positivity : 0 < y ^ γ / x)⟩
  simpa using h z⁻¹ 1 (inv_pos.2 hz) one_pos

/-- The spot derivative of `U (y ^ γ / x)` is `-(y ^ γ / x ²) U'(y ^ γ / x)`. -/
theorem hasDerivAt_consistentDemand_spot {u : ℝ} (hU : HasDerivAt U u (y ^ γ / x))
    (hx : x ≠ 0) :
    HasDerivAt (fun x' => consistentDemand γ U x' y) (-(y ^ γ / x ^ 2) * u) x := by
  have h₁ : HasDerivAt (fun x' => y ^ γ / x') (y ^ γ * -(x ^ 2)⁻¹) x := by
    simpa only [div_eq_mul_inv] using (hasDerivAt_inv hx).const_mul (y ^ γ)
  have h := hU.comp x h₁
  simp only [comp_def] at h
  convert h using 1
  · ext x'
    rw [consistentDemand_def]
  · ring

/-- The income derivative of `U (y ^ γ / x)` is `γ y ^ (γ - 1) / x · U'(y ^ γ / x)`. -/
theorem hasDerivAt_consistentDemand_income {u : ℝ} (hU : HasDerivAt U u (y ^ γ / x))
    (hy : y ≠ 0 ∨ 1 ≤ γ) :
    HasDerivAt (consistentDemand γ U x) (γ * y ^ (γ - 1) / x * u) y := by
  have h := hU.comp y ((Real.hasDerivAt_rpow_const hy).div_const x)
  simp only [comp_def] at h
  convert h using 1
  · ext y'
    rw [consistentDemand_def]
  · ring

/-- If the profile has positive derivative at `y ^ γ / x`, the spot derivative of the demand at
`(x, y)` is negative. -/
theorem deriv_consistentDemand_spot_neg (hx : x ≠ 0) (hy : 0 < y)
    (hU : 0 < deriv U (y ^ γ / x)) :
    deriv (fun x' => consistentDemand γ U x' y) x < 0 := by
  rw [(hasDerivAt_consistentDemand_spot
    (differentiableAt_of_deriv_ne_zero hU.ne').hasDerivAt hx).deriv]
  have : 0 < y ^ γ / x ^ 2 := div_pos (Real.rpow_pos_of_pos hy γ) (by positivity)
  nlinarith

/-- If the profile has positive derivative at `y ^ γ / x`, then for a positive exponent `γ` the
income derivative of the demand at `(x, y)` is positive. -/
theorem deriv_consistentDemand_income_pos (hγ : 0 < γ) (hx : 0 < x) (hy : 0 < y)
    (hU : 0 < deriv U (y ^ γ / x)) :
    0 < deriv (consistentDemand γ U x) y := by
  rw [(hasDerivAt_consistentDemand_income
    (differentiableAt_of_deriv_ne_zero hU.ne').hasDerivAt (Or.inl hy.ne')).deriv]
  have : 0 < y ^ (γ - 1) := Real.rpow_pos_of_pos hy _
  positivity

/-! ### The consistency relation -/

/-- A reference demand `D x y`, at spot `x` and income `y`, is **consistent** with exponent `γ`
if `D_y / D_x = -γ x / y` at every point of the open positive quadrant.

The partial derivatives are Mathlib's `deriv`, which is `0` where the demand is not
differentiable, and the quotient is Lean's division, which is `0` where `D_x = 0`. So the identity
is meaningful only where `D_x ≠ 0`, which every theorem about it here assumes; without that
assumption, for `γ = 0` the predicate holds for any demand with `D_x ≡ 0`, such as `D x y = y`. -/
def IsConsistentDemand (γ : ℝ) (D : ℝ → ℝ → ℝ) : Prop :=
  ∀ x y, 0 < x → 0 < y → deriv (D x) y / deriv (fun x' => D x' y) x = -γ * x / y

/-- Unfolding lemma for `IsConsistentDemand`. -/
theorem isConsistentDemand_iff :
    IsConsistentDemand γ D ↔
      ∀ x y, 0 < x → 0 < y → deriv (D x) y / deriv (fun x' => D x' y) x = -γ * x / y :=
  Iff.rfl

/-- Consistency depends only on the values of the demand on the open positive quadrant. -/
theorem IsConsistentDemand.congr (h : IsConsistentDemand γ D)
    (hDE : ∀ x y, 0 < x → 0 < y → D x y = E x y) : IsConsistentDemand γ E := by
  intro x y hx hy
  have hy' : D x =ᶠ[nhds y] E x :=
    (eventually_gt_nhds hy).mono fun y' hy' => hDE x y' hx hy'
  have hx' : (fun x' => D x' y) =ᶠ[nhds x] fun x' => E x' y :=
    (eventually_gt_nhds hx).mono fun x' hx' => hDE x' y hx' hy
  rw [← hy'.deriv_eq, ← hx'.deriv_eq]
  exact h x y hx hy

/-- Where the spot derivative does not vanish, consistency is the first-order equation
`γ x D_x + y D_y = 0`: the demand is annihilated by the scaling vector field
`γ x ∂_x + y ∂_y`. -/
theorem isConsistentDemand_iff_of_deriv_ne_zero
    (hDx : ∀ x y, 0 < x → 0 < y → deriv (fun x' => D x' y) x ≠ 0) :
    IsConsistentDemand γ D ↔
      ∀ x y, 0 < x → 0 < y → γ * x * deriv (fun x' => D x' y) x + y * deriv (D x) y = 0 := by
  refine forall₄_congr fun x y hx hy => ?_
  rw [div_eq_div_iff (hDx x y hx hy) hy.ne']
  constructor <;> intro h <;> linear_combination h

/-- A profile with nonvanishing derivative on `(0, ∞)` gives a consistent demand, for every
exponent `γ`. -/
theorem isConsistentDemand_consistentDemand (hU : ∀ z, 0 < z → deriv U z ≠ 0) :
    IsConsistentDemand γ (consistentDemand γ U) := by
  intro x y hx hy
  have hz : 0 < y ^ γ / x := by positivity
  have hd := (differentiableAt_of_deriv_ne_zero (hU _ hz)).hasDerivAt
  rw [(hasDerivAt_consistentDemand_income hd (Or.inl hy.ne')).deriv,
    (hasDerivAt_consistentDemand_spot hd hx.ne').deriv, Real.rpow_sub_one hy.ne']
  have := hU _ hz
  field_simp

/-! ### Consistent demands factor through the invariant coordinate -/

/-- **Constancy along scaling orbits.** A demand differentiable on the open positive quadrant and
satisfying `γ x D_x + y D_y = 0` there is constant along the orbits `s ↦ (c s ^ γ, s)` of the
scaling vector field. Following the orbit through `(x, y)` to unit income gives
`D x y = D (x / y ^ γ) 1`, that is, `D` is the demand `U (y ^ γ / x)` with profile `U z = D z⁻¹ 1`.
This holds for every real exponent `γ`. -/
theorem eq_consistentDemand_of_scaling
    (hD : ∀ x y, 0 < x → 0 < y → DifferentiableAt ℝ (uncurry D) (x, y))
    (hscale : ∀ x y, 0 < x → 0 < y →
      γ * x * deriv (fun x' => D x' y) x + y * deriv (D x) y = 0)
    (hx : 0 < x) (hy : 0 < y) :
    D x y = consistentDemand γ (fun z => D z⁻¹ 1) x y := by
  set c := x / y ^ γ with hc_def
  have hc : 0 < c := by positivity
  -- Along the orbit `s ↦ (c s ^ γ, s)` the demand `g` has derivative zero.
  set g : ℝ → ℝ := fun s => D (c * s ^ γ) s with hg_def
  have hg : ∀ s ∈ Ioi (0 : ℝ), HasDerivAt g 0 s := by
    intro s (hs : 0 < s)
    have hcs : 0 < c * s ^ γ := mul_pos hc (Real.rpow_pos_of_pos hs γ)
    have hDs := hD _ _ hcs hs
    have horbit : HasDerivAt (fun s' => c * s' ^ γ) (c * (γ * s ^ (γ - 1))) s :=
      (Real.hasDerivAt_rpow_const (Or.inl hs.ne')).const_mul c
    have hcomp := hDs.hasFDerivAt.comp_hasDerivAt (f := fun s' => (c * s' ^ γ, s')) s
      (horbit.prodMk (hasDerivAt_id' s))
    -- Split the velocity `(c γ s ^ (γ - 1), 1)` into its spot and income components.
    have hsplit : ((c * (γ * s ^ (γ - 1)), 1) : ℝ × ℝ) =
        (c * (γ * s ^ (γ - 1))) • ((1 : ℝ), (0 : ℝ)) + ((0 : ℝ), (1 : ℝ)) := by
      simp
    rw [hsplit, map_add, map_smul, smul_eq_mul,
      ← (TauCeti.hasDerivAt_parameterCurve_uncurry hDs).deriv,
      ← (TauCeti.hasDerivAt_timeSlice_uncurry hDs).deriv] at hcomp
    refine hcomp.congr_deriv ?_
    have hpow : s ^ γ = s ^ (γ - 1) * s := by rw [← Real.rpow_add_one hs.ne', sub_add_cancel]
    apply mul_left_cancel₀ hs.ne'
    linear_combination hscale _ _ hcs hs - γ * c * deriv (fun x' => D x' s) (c * s ^ γ) * hpow
  have hconst := isOpen_Ioi.is_const_of_deriv_eq_zero (convex_Ioi 0).isPreconnected
    (fun s hs => (hg s hs).differentiableAt.differentiableWithinAt)
    (fun s hs => (hg s hs).deriv) (mem_Ioi.2 hy) (mem_Ioi.2 one_pos)
  have hxy : c * y ^ γ = x := by
    rw [hc_def, div_mul_cancel₀ _ (Real.rpow_pos_of_pos hy γ).ne']
  simp only [hg_def, hxy, Real.one_rpow, mul_one] at hconst
  rw [hconst, consistentDemand_def, inv_div]

/-- A consistent demand, differentiable on the open positive quadrant with nonvanishing spot
derivative there, is the demand `U (y ^ γ / x)` with profile `U z = D z⁻¹ 1`. -/
theorem IsConsistentDemand.eq_consistentDemand (h : IsConsistentDemand γ D)
    (hD : ∀ x y, 0 < x → 0 < y → DifferentiableAt ℝ (uncurry D) (x, y))
    (hDx : ∀ x y, 0 < x → 0 < y → deriv (fun x' => D x' y) x ≠ 0) (hx : 0 < x) (hy : 0 < y) :
    D x y = consistentDemand γ (fun z => D z⁻¹ 1) x y :=
  eq_consistentDemand_of_scaling hD ((isConsistentDemand_iff_of_deriv_ne_zero hDx).1 h) hx hy

/-- The profile `U z = D z⁻¹ 1` of a demand `D` has derivative `U'(z) = -D_x(z⁻¹, 1) / z²`
wherever the demand at unit income is differentiable in spot at `z⁻¹`. -/
theorem hasDerivAt_profile_inv_one {z : ℝ} (hD : DifferentiableAt ℝ (fun x' => D x' 1) z⁻¹)
    (hz : z ≠ 0) :
    HasDerivAt (fun z => D z⁻¹ 1) (-deriv (fun x' => D x' 1) z⁻¹ / z ^ 2) z :=
  (hD.hasDerivAt.comp z (hasDerivAt_inv hz)).congr_deriv (by ring)

/-- **Profile characterization of consistent demand.** A consistent demand that is `C¹` on the
open positive quadrant with negative spot derivative there is `U (y ^ γ / x)` for a profile `U`
that is `C¹` on `(0, ∞)` with positive derivative. -/
theorem IsConsistentDemand.exists_profile (h : IsConsistentDemand γ D)
    (hD : ContDiffOn ℝ 1 (uncurry D) (Ioi 0 ×ˢ Ioi 0))
    (hDx : ∀ x y, 0 < x → 0 < y → deriv (fun x' => D x' y) x < 0) :
    ∃ U : ℝ → ℝ, ContDiffOn ℝ 1 U (Ioi 0) ∧ (∀ z, 0 < z → 0 < deriv U z) ∧
      ∀ x y, 0 < x → 0 < y → D x y = consistentDemand γ U x y := by
  have hdiff : ∀ x y, 0 < x → 0 < y → DifferentiableAt ℝ (uncurry D) (x, y) := fun x y hx hy =>
    (hD.contDiffAt ((isOpen_Ioi.prod isOpen_Ioi).mem_nhds (mk_mem_prod hx hy))).differentiableAt
      one_ne_zero
  refine ⟨fun z => D z⁻¹ 1, ?_, fun z hz => ?_, fun x y hx hy =>
    h.eq_consistentDemand hdiff (fun x y hx hy => (hDx x y hx hy).ne) hx hy⟩
  · exact hD.comp ((contDiffOn_id.inv fun z (hz : 0 < z) => hz.ne').prodMk contDiffOn_const)
      fun z (hz : 0 < z) => mk_mem_prod (inv_pos.2 hz) one_pos
  · rw [(hasDerivAt_profile_inv_one (TauCeti.hasDerivAt_parameterCurve_uncurry
      (hdiff _ _ (inv_pos.2 hz) one_pos)).differentiableAt hz.ne').deriv]
    exact div_pos (neg_pos.2 (hDx _ _ (inv_pos.2 hz) one_pos)) (pow_pos hz 2)

/-- **Consistent demands are exactly demands through the invariant coordinate.** For a demand
that is `C¹` on the open positive quadrant with negative spot derivative there, the consistency
relation `D_y / D_x = -γ x / y` holds on the quadrant if and only if `D = U (y ^ γ / x)` there for
a profile `U` that is `C¹` on `(0, ∞)` with positive derivative. -/
theorem isConsistentDemand_iff_exists_profile
    (hD : ContDiffOn ℝ 1 (uncurry D) (Ioi 0 ×ˢ Ioi 0))
    (hDx : ∀ x y, 0 < x → 0 < y → deriv (fun x' => D x' y) x < 0) :
    IsConsistentDemand γ D ↔
      ∃ U : ℝ → ℝ, ContDiffOn ℝ 1 U (Ioi 0) ∧ (∀ z, 0 < z → 0 < deriv U z) ∧
        ∀ x y, 0 < x → 0 < y → D x y = consistentDemand γ U x y := by
  refine ⟨fun h => h.exists_profile hD hDx, fun ⟨U, _, hU, hDU⟩ => ?_⟩
  exact (isConsistentDemand_consistentDemand fun z hz => (hU z hz).ne').congr
    fun x y hx hy => (hDU x y hx hy).symm

end TauCeti.Finance
