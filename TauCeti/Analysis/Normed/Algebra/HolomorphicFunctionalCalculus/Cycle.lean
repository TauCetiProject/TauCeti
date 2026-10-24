/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Algebra.GelfandFormula
public import Mathlib.Topology.Algebra.Polynomial
public import TauCeti.Algebra.Algebra.Resolvent
public import TauCeti.Analysis.Contour.Cycle.Circle
public import TauCeti.Analysis.Contour.Cycle.HomologyCauchy
public import TauCeti.Analysis.Normed.Algebra.Resolvent

/-!
# Resolvent integrals over contour cycles

Let `a` be an element of a complex Banach algebra `A`. The holomorphic functional calculus defines

`f(a) = (2πi)⁻¹ ∫_Γ f(z) (z1 - a)⁻¹ dz`

for `f` holomorphic on an open neighbourhood `U` of the spectrum `σ(a)` and `Γ` a cycle in
`U \ σ(a)` that is null-homologous in `U` and winds once around every point of `σ(a)`. This file
proves the basic properties of these resolvent integrals for a fixed cycle `Γ`, written with
Mathlib's `resolvent a z = (z1 - a)⁻¹` as `Cycle.integral (fun z ↦ f z • resolvent a z) Γ`.

* The integral does not depend on `Γ`: by the homology Cauchy theorem, two such cycles give the
  same value.
* For a polynomial `p`, the integral of `p(z) (z1 - a)⁻¹` is `2πi · p(a)`. The case `p = 1` is
  obtained by comparing `Γ` with a large circle, where `(z1 - a)⁻¹ - z⁻¹ 1` is small; the general
  case then follows from `z (z1 - a)⁻¹ = 1 + a (z1 - a)⁻¹`, since the integrals of polynomials
  vanish.
* Every element commuting with `a` commutes with the integral.

No normalization `‖1‖ = 1` of the norm is assumed.

## Main results

* `TauCeti.Contour.Cycle.integral_smul_resolvent_eq_of_windingNumber_eq`: independence of the
  cycle.
* `TauCeti.Contour.Cycle.integral_resolvent`: `∫_Γ (z1 - a)⁻¹ dz = 2πi · 1`.
* `TauCeti.Contour.Cycle.integral_pow_smul_resolvent`: `∫_Γ zⁿ (z1 - a)⁻¹ dz = 2πi · aⁿ`.
* `TauCeti.Contour.Cycle.integral_eval_smul_resolvent`: `∫_Γ p(z) (z1 - a)⁻¹ dz = 2πi · p(a)`.
* `TauCeti.Contour.Cycle.commute_integral_smul_resolvent`: elements commuting with `a` commute
  with the resolvent integral.

## References

* H. G. Dales, *Banach Algebras and Automatic Continuity*, §2.4.
* J. B. Conway, *A Course in Functional Analysis*, second edition, VII.4.
-/

public section

noncomputable section

open Complex Metric Set Filter

open scoped Real

namespace TauCeti.Contour.Cycle

variable {A : Type*} [NormedRing A] [NormedAlgebra ℂ A] [CompleteSpace A] {a : A} {Γ : Cycle}

/-- The resolvent of `a` is continuous on the trace of a cycle avoiding the spectrum. -/
private theorem continuousOn_resolvent (hΓ : IsIn Γ (resolventSet ℂ a)) :
    ContinuousOn (resolvent a) (trace Γ) :=
  (spectrum.differentiableOn_resolvent a).continuousOn.mono (isIn_iff.mp hΓ)

/-- **Independence of the cycle.** Let `f` be holomorphic on an open set `U`, and let `Γ₁` and `Γ₂`
be cycles in `U \ σ(a)` that are null-homologous in `U` and have the same winding number about each
point of the spectrum `σ(a)`, typically `1`. Then `∫ f(z) (z1 - a)⁻¹ dz` is the same over `Γ₁` and
over `Γ₂`. -/
theorem integral_smul_resolvent_eq_of_windingNumber_eq {U : Set ℂ} (hU : IsOpen U) {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f U) {Γ₁ Γ₂ : Cycle} (h₁ : IsIn Γ₁ (U \ spectrum ℂ a))
    (h₂ : IsIn Γ₂ (U \ spectrum ℂ a)) (hU₁ : IsNullHomologous Γ₁ U)
    (hU₂ : IsNullHomologous Γ₂ U)
    (h : ∀ z ∈ spectrum ℂ a, windingNumber z Γ₁ = windingNumber z Γ₂) :
    integral (fun z ↦ f z • resolvent a z) Γ₁ = integral (fun z ↦ f z • resolvent a z) Γ₂ :=
  integral_eq_of_windingNumber_eq hU (spectrum.isClosed a)
    ((hf.mono sdiff_subset).smul ((spectrum.differentiableOn_resolvent a).mono
      fun _ hz ↦ spectrum.notMem_iff.mp hz.2)) h₁ h₂ hU₁ hU₂ h

omit [CompleteSpace A] in
/-- If the spectrum of `a` lies in the open disc of radius `R₀` about `0`, then every circle about
`0` of radius at least `R₀` lies in the resolvent set. -/
private theorem sphere_subset_resolventSet {R₀ R : ℝ} (hR₀ : spectrum ℂ a ⊆ ball 0 R₀)
    (hR : R₀ ≤ R) : sphere (0 : ℂ) R ⊆ resolventSet ℂ a := fun z hz ↦
  spectrum.notMem_iff.mp fun hσ ↦
    (mem_ball_zero_iff.mp (hR₀ hσ)).not_ge (by rwa [mem_sphere_zero_iff_norm.mp hz])

/-- If the spectrum of `a` lies in the open disc of radius `R` about `0`, and a cycle `Γ` avoids
the spectrum and winds once around each of its points, then the resolvent has the same integral
over `Γ` as over the circle of radius `R`. -/
private theorem integral_resolvent_eq_circleIntegral (hΓ : IsIn Γ (resolventSet ℂ a))
    (hwind : ∀ z ∈ spectrum ℂ a, windingNumber z Γ = 1) {R : ℝ}
    (hR : spectrum ℂ a ⊆ ball 0 R) :
    integral (resolvent a) Γ = ∮ z in C(0, R), resolvent a z := by
  rw [← integral_circleCycle]
  refine integral_eq_of_windingNumber_eq isOpen_univ (spectrum.isClosed a)
    ((spectrum.differentiableOn_resolvent a).mono fun z hz ↦ spectrum.notMem_iff.mp hz.2) ?_ ?_
    (isNullHomologous_univ _) (isNullHomologous_univ _) fun z hz ↦ ?_
  · exact isIn_iff.mpr fun z hz ↦ ⟨trivial, fun hσ ↦
      spectrum.mem_iff.mp hσ (spectrum.mem_resolventSet_iff.mp (isIn_iff.mp hΓ hz))⟩
  · rw [isIn_iff, trace_circleCycle]
    exact fun z hz ↦ ⟨trivial, fun hσ ↦ spectrum.mem_iff.mp hσ
      (spectrum.mem_resolventSet_iff.mp (sphere_subset_resolventSet hR (le_abs_self R) hz))⟩
  · rw [hwind z hz, windingNumber_circleCycle_eq_one_of_dist_lt (hR hz)]

/-- **The resolvent integral of the constant function `1`.** If a cycle `Γ` avoids the spectrum
of `a` and winds once around each of its points, then `∫_Γ (z1 - a)⁻¹ dz = 2πi · 1`. -/
theorem integral_resolvent (hΓ : IsIn Γ (resolventSet ℂ a))
    (hwind : ∀ z ∈ spectrum ℂ a, windingNumber z Γ = 1) :
    integral (resolvent a) Γ = (2 * π * I) • (1 : A) := by
  obtain ⟨R₀, hR₀pos, hR₀⟩ := (spectrum.isCompact (𝕜 := ℂ) a).isBounded.subset_ball_lt 0 0
  -- Comparing with a large circle, the difference from `2πi · 1` is the circle integral of
  -- `z⁻¹ a (z1 - a)⁻¹`.
  have hdiff : ∀ R, R₀ ≤ R → integral (resolvent a) Γ - (2 * π * I) • (1 : A) =
      ∮ z in C(0, R), z⁻¹ • (a * resolvent a z) := by
    intro R hR
    have hR0 : 0 < R := hR₀pos.trans_le hR
    have hinv : (∮ z in C(0, R), z⁻¹) = 2 * π * I := by
      simpa using circleIntegral.integral_sub_center_inv 0 hR0.ne'
    rw [integral_resolvent_eq_circleIntegral hΓ hwind (hR₀.trans (ball_subset_ball hR)), ← hinv,
      ← circleIntegral.integral_smul_const,
      ← circleIntegral.integral_sub (f := resolvent a) (g := fun z ↦ z⁻¹ • (1 : A))
        (((spectrum.differentiableOn_resolvent a).continuousOn.mono
          (sphere_subset_resolventSet hR₀ hR)).circleIntegrable hR0.le)
        (((continuousOn_inv₀.mono fun z hz ↦ ne_zero_of_mem_sphere hR0.ne' ⟨z, hz⟩).smul
          continuousOn_const).circleIntegrable hR0.le)]
    exact circleIntegral.integral_congr hR0.le fun z hz ↦
      spectrum.resolvent_sub_inv_smul_one (sphere_subset_resolventSet hR₀ hR hz)
        (ne_zero_of_mem_sphere hR0.ne' ⟨z, hz⟩)
  -- That circle integral is small for large radii, since the resolvent tends to `0` at infinity.
  rw [← sub_eq_zero, ← norm_le_zero_iff]
  refine le_of_forall_pos_le_add fun ε hε ↦ ?_
  set c := 2 * π * ‖a‖ + 1 with hc_def
  have hc : 0 < c := by positivity
  obtain ⟨r, -, hr⟩ := Filter.hasBasis_cobounded_norm.eventually_iff.mp
    ((spectrum.resolvent_tendsto_cobounded (𝕜 := ℂ) a).eventually
      (closedBall_mem_nhds (0 : A) (div_pos hε hc)))
  set R := max R₀ r
  have hR0 : 0 < R := hR₀pos.trans_le (le_max_left _ _)
  rw [hdiff R (le_max_left _ _), zero_add]
  calc ‖∮ z in C(0, R), z⁻¹ • (a * resolvent a z)‖
      ≤ 2 * π * R * (R⁻¹ * (‖a‖ * (ε / c))) := by
        refine circleIntegral.norm_integral_le_of_norm_le_const hR0.le fun z hz ↦ ?_
        have hzR : ‖z‖ = R := mem_sphere_zero_iff_norm.mp hz
        have hrz : r ≤ ‖z‖ := hzR ▸ le_max_right R₀ r
        have hsmall : ‖resolvent a z‖ ≤ ε / c := by simpa using hr hrz
        rw [norm_smul, norm_inv, hzR]
        gcongr
        exact (norm_mul_le _ _).trans (by gcongr)
    _ = ε * (2 * π * ‖a‖ / c) := by field_simp
    _ ≤ ε := by
        refine mul_le_of_le_one_right hε.le ((div_le_one hc).mpr ?_)
        rw [hc_def]
        linarith

/-- **The resolvent integral of a power.** If a cycle `Γ` avoids the spectrum of `a` and winds
once around each of its points, then `∫_Γ zⁿ (z1 - a)⁻¹ dz = 2πi · aⁿ`. -/
theorem integral_pow_smul_resolvent (hΓ : IsIn Γ (resolventSet ℂ a))
    (hwind : ∀ z ∈ spectrum ℂ a, windingNumber z Γ = 1) (n : ℕ) :
    integral (fun z ↦ z ^ n • resolvent a z) Γ = (2 * π * I) • a ^ n := by
  induction n with
  | zero => simpa using integral_resolvent hΓ hwind
  | succ n ih =>
    have hcont : ContinuousOn (fun z ↦ z ^ n • resolvent a z) (trace Γ) :=
      (continuous_pow n).continuousOn.smul (continuousOn_resolvent hΓ)
    -- Multiplying by `z` shifts the power onto `a`, up to the integral of a polynomial.
    have hshift := integral_comp_comm (f := fun z ↦ z ^ n • resolvent a z)
      (fun _ ↦ intervalIntegrable_of_mem_support hcont) (ContinuousLinearMap.mul ℂ A a)
    simp only [ContinuousLinearMap.mul_apply'] at hshift
    calc integral (fun z ↦ z ^ (n + 1) • resolvent a z) Γ
        = integral (fun z ↦ z ^ n • (1 : A) + a * (z ^ n • resolvent a z)) Γ :=
          integral_congr fun z hz ↦ by
            rw [pow_succ, mul_smul,
              spectrum.smul_resolvent_eq_one_add_mul_resolvent (isIn_iff.mp hΓ hz), smul_add,
              mul_smul_comm]
      _ = integral (fun z ↦ z ^ n • (1 : A)) Γ +
            integral (fun z ↦ a * (z ^ n • resolvent a z)) Γ :=
          integral_add ((continuous_pow n).continuousOn.smul continuousOn_const)
            (continuousOn_const.mul hcont)
      _ = (2 * π * I) • a ^ (n + 1) := by
          rw [homologyCauchyTheorem isOpen_univ (isIn_iff.mpr (subset_univ _))
            ((differentiable_pow n).smul_const _).differentiableOn
            (isNullHomologous_univ _), zero_add, hshift, ih,
            mul_smul_comm, pow_succ']

/-- **The resolvent integral of a polynomial.** If a cycle `Γ` avoids the spectrum of `a` and
winds once around each of its points, then `∫_Γ p(z) (z1 - a)⁻¹ dz = 2πi · p(a)` for every complex
polynomial `p`. -/
theorem integral_eval_smul_resolvent (hΓ : IsIn Γ (resolventSet ℂ a))
    (hwind : ∀ z ∈ spectrum ℂ a, windingNumber z Γ = 1) (p : Polynomial ℂ) :
    integral (fun z ↦ p.eval z • resolvent a z) Γ = (2 * π * I) • Polynomial.aeval a p := by
  have hres := continuousOn_resolvent hΓ
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    simp only [Polynomial.eval_add, add_smul, map_add, smul_add]
    rw [integral_add (f := fun z ↦ p.eval z • resolvent a z) (g := fun z ↦ q.eval z • resolvent a z)
      (p.continuous.continuousOn.smul hres) (q.continuous.continuousOn.smul hres), hp, hq]
  | monomial n c =>
    simp only [Polynomial.eval_monomial, mul_smul c, Polynomial.aeval_monomial,
      ← Algebra.smul_def]
    rw [integral_smul, integral_pow_smul_resolvent hΓ hwind, smul_comm]

/-- Every element commuting with `a` commutes with the resolvent integral
`∫_Γ f(z) (z1 - a)⁻¹ dz`, for `f` continuous on the trace of a cycle `Γ` avoiding the spectrum. -/
theorem commute_integral_smul_resolvent {b : A} (hb : Commute b a) {f : ℂ → ℂ}
    (hf : ContinuousOn f (trace Γ)) (hΓ : IsIn Γ (resolventSet ℂ a)) :
    Commute b (integral (fun z ↦ f z • resolvent a z) Γ) := by
  have hint : ∀ γ ∈ FreeAbelianGroup.support Γ,
      IntervalIntegrable (fun t ↦ deriv γ t • (f (γ t) • resolvent a (γ t)))
        MeasureTheory.volume γ.a γ.b :=
    fun _ ↦ intervalIntegrable_of_mem_support (hf.smul (continuousOn_resolvent hΓ))
  have hl := integral_comp_comm (f := fun z ↦ f z • resolvent a z) hint
    (ContinuousLinearMap.mul ℂ A b)
  have hr := integral_comp_comm (f := fun z ↦ f z • resolvent a z) hint
    ((ContinuousLinearMap.mul ℂ A).flip b)
  simp only [ContinuousLinearMap.mul_apply', ContinuousLinearMap.flip_apply] at hl hr
  rw [Commute, SemiconjBy, ← hl, ← hr]
  exact integral_congr fun z _ ↦ by
    rw [mul_smul_comm, smul_mul_assoc, (hb.resolvent_right z).eq]

end TauCeti.Contour.Cycle
