/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.PowerSeries.Entire.Eval
public import TauCeti.RingTheory.PowerSeries.OpenDisc.Topology

/-!
# Evaluation of power series on an open disc

A power series `f = ∑ aₙ Xⁿ` on the open disc of radius `R₀` (`PowerSeries.OnOpenDisc`) can be
evaluated at every point `b` with `‖b‖ < R₀` of a complete normed algebra `A`: the series is
restricted at a radius strictly between `‖b‖` and `R₀`, so the terms `aₙ • bⁿ` are absolutely
summable and `PowerSeries.evalAt f b = ∑ₙ aₙ • bⁿ` is an honest sum. The Cauchy product formula
makes evaluation at `b` a ring homomorphism on the subring of series on the open disc. Neither the
coefficient ring nor the algebra needs an ultrametric norm for this, and the algebra need not be
commutative.

The evaluation agrees with the evaluation of restricted series at every radius between `‖b‖` and
`R₀`, and with the evaluation of entire series. For an ultrametric coefficient ring it is
continuous for the topology of the Gauss norms at all radii below `R₀`
(`TauCeti.PowerSeries.OnOpenDisc.uniformSpace`): for any `r` strictly between `‖b‖` and `R₀`, the
value at `b` is bounded by a constant multiple of the Gauss norm at `r`
(`PowerSeries.norm_evalAt_le_mul_gaussNorm`).

## Main definitions

* `PowerSeries.OnOpenDisc.evalAtHom`: evaluation at `b` with `‖b‖ < R₀` as a ring homomorphism on
  the series on the open disc of radius `R₀`.

## Main results

* `PowerSeries.OnOpenDisc.hasSum_evalAt`: the series `∑ aₙ • bⁿ` converges to `f(b)`.
* `PowerSeries.OnOpenDisc.evalAt_add`, `PowerSeries.OnOpenDisc.evalAt_mul`: evaluation is additive
  and multiplicative.
* `PowerSeries.OnOpenDisc.map_evalAt`: naturality in continuous algebra homomorphisms.
* `PowerSeries.OnOpenDisc.evalAtHom_comp_inclusion`: entire series are evaluated as such.
* `TauCeti.PowerSeries.OnOpenDisc.isRestrictedEvalAtHom_comp_restrict`: restricting to a closed
  disc containing `b` and evaluating there is evaluation on the open disc.
* `TauCeti.PowerSeries.OnOpenDisc.continuous_evalAtHom`: evaluation is continuous.

## References

* P. Colmez, *Fonctions d'une variable p-adique*, Astérisque 330 (2010), §I.4.
-/

public section

namespace PowerSeries

section SMulZeroClass

variable {R A : Type*} [NormedRing R] [SeminormedRing A] [SMulZeroClass R A] [IsBoundedSMul R A]
  {R₀ : ℝ} {f : R⟦X⟧} {b : A}

/-- For a series `f = ∑ aₙ Xⁿ` on the open disc of radius `R₀` and a point `b` with `‖b‖ < R₀`,
the terms `aₙ • bⁿ` are absolutely summable. -/
theorem OnOpenDisc.summable_norm_smul_pow (hf : f.OnOpenDisc R₀) (hb : ‖b‖ < R₀) :
    Summable fun n ↦ ‖coeff n f • b ^ n‖ :=
  summable_norm_smul_pow_of_summable_norm_mul_pow
    (hf.summable_norm_coeff_mul_pow (by rwa [abs_norm]))

end SMulZeroClass

section Seminormed

variable {R A : Type*} [NormedCommRing R] [SeminormedRing A] [Algebra R A] [IsBoundedSMul R A]
  [CompleteSpace A] {R₀ : ℝ} {f : R⟦X⟧} {b : A}

/-- **Evaluation of series on an open disc.** For a series `f = ∑ aₙ Xⁿ` on the open disc of
radius `R₀` and a point `b` with `‖b‖ < R₀` of a complete seminormed algebra, the series
`∑ aₙ • bⁿ` converges to `f(b)`. -/
theorem OnOpenDisc.hasSum_evalAt (hf : f.OnOpenDisc R₀) (hb : ‖b‖ < R₀) :
    HasSum (fun n ↦ coeff n f • b ^ n) (f.evalAt b) :=
  hasSum_evalAt_of_summable_norm (hf.summable_norm_smul_pow hb)

/-- Evaluation of series on an open disc commutes with continuous algebra homomorphisms:
`ψ (f(b)) = f(ψ b)`. -/
theorem OnOpenDisc.map_evalAt {B F : Type*} [Semiring B] [Algebra R B] [TopologicalSpace B]
    [T2Space B] [FunLike F A B] [AlgHomClass F R A B] (hf : f.OnOpenDisc R₀) (ψ : F)
    (hψ : Continuous ψ) (hb : ‖b‖ < R₀) : ψ (f.evalAt b) = f.evalAt (ψ b) := by
  rw [← ((hf.hasSum_evalAt hb).map ψ hψ).tsum_eq, evalAt_def]
  simp [map_smul, map_pow]

end Seminormed

section Normed

variable {R A : Type*} [NormedCommRing R] [NormedRing A] [Algebra R A] [IsBoundedSMul R A]
  [CompleteSpace A] {R₀ : ℝ} {f g : R⟦X⟧} {b : A}

/-- Evaluation at a point of norm less than `R₀` is additive on series on the open disc of radius
`R₀`. -/
theorem OnOpenDisc.evalAt_add (hf : f.OnOpenDisc R₀) (hg : g.OnOpenDisc R₀) (hb : ‖b‖ < R₀) :
    (f + g).evalAt b = f.evalAt b + g.evalAt b :=
  evalAt_add_of_summable_norm (hf.summable_norm_smul_pow hb) (hg.summable_norm_smul_pow hb)

/-- Evaluation at a point of norm less than `R₀` is multiplicative on series on the open disc of
radius `R₀`. -/
theorem OnOpenDisc.evalAt_mul (hf : f.OnOpenDisc R₀) (hg : g.OnOpenDisc R₀) (hb : ‖b‖ < R₀) :
    (f * g).evalAt b = f.evalAt b * g.evalAt b :=
  evalAt_mul_of_summable_norm (hf.summable_norm_smul_pow hb) (hg.summable_norm_smul_pow hb)

variable (R) in
/-- **Evaluation of series on an open disc at `b`** as a ring homomorphism from the series on the
open disc of radius `R₀` to a complete normed algebra, for a point `b` with `‖b‖ < R₀`. -/
noncomputable def OnOpenDisc.evalAtHom (hb : ‖b‖ < R₀) : OnOpenDisc.subring R R₀ →+* A where
  toFun f := (f : R⟦X⟧).evalAt b
  map_one' := evalAt_one b
  map_mul' f g := (OnOpenDisc.mem_subring.mp f.2).evalAt_mul (OnOpenDisc.mem_subring.mp g.2) hb
  map_zero' := evalAt_zero b
  map_add' f g := (OnOpenDisc.mem_subring.mp f.2).evalAt_add (OnOpenDisc.mem_subring.mp g.2) hb

/-- The evaluation homomorphism at `b` sends a series `f` on the open disc to `f(b)`. -/
@[simp]
theorem OnOpenDisc.evalAtHom_apply (hb : ‖b‖ < R₀) (f : OnOpenDisc.subring R R₀) :
    OnOpenDisc.evalAtHom R hb f = (f : R⟦X⟧).evalAt b :=
  (rfl)

/-- On entire series, evaluation as series on an open disc is the evaluation of entire series. -/
theorem OnOpenDisc.evalAtHom_comp_inclusion (hb : ‖b‖ < R₀) :
    (OnOpenDisc.evalAtHom R hb).comp (Subring.inclusion (IsEntire.subring_le_onOpenDiscSubring R₀))
      = IsEntire.evalAtHom R b := by
  ext f
  simp

end Normed

end PowerSeries

open Filter PowerSeries
open scoped Topology

namespace TauCeti.PowerSeries.OnOpenDisc

variable {R A : Type*} [NormedCommRing R] [IsUltrametricDist R] [NormedRing A] [Algebra R A]
  [IsBoundedSMul R A] [CompleteSpace A] {R₀ : ℝ} {b : A}

-- Supply the positivity witness used by the Gauss-norm instances on each closed disc.
attribute [local instance] radius_pos

/-- Restricting a series on the open disc of radius `R₀` to a closed disc of radius `r < R₀`
containing `b`, and evaluating it there at `b`, is evaluation at `b` on the open disc. -/
theorem isRestrictedEvalAtHom_comp_restrict [IsUltrametricDist A] (r : Set.Ioo (0 : ℝ) R₀)
    (hbr : ‖b‖ ≤ r) :
    (IsRestricted.evalAtHom R hbr).comp (restrict r) =
      OnOpenDisc.evalAtHom R (hbr.trans_lt r.2.2) := by
  ext f
  simp

/-- Evaluation of series on the open disc of radius `R₀` at a point `b` with `‖b‖ < R₀` is
continuous for the topology of the Gauss norms at all radii below `R₀`. -/
theorem continuous_evalAtHom (hb : ‖b‖ < R₀) : Continuous (OnOpenDisc.evalAtHom R hb) := by
  -- Evaluation at `b` is controlled by the Gauss norm at a radius `r` strictly between `‖b‖`
  -- and `R₀`, through the geometric ratio `q = ‖b‖ / r < 1`.
  obtain ⟨r, hbr⟩ : ∃ r : Set.Ioo (0 : ℝ) R₀, ‖b‖ < r := by
    obtain ⟨r, hbr, hrR⟩ := exists_between hb
    exact ⟨⟨r, (norm_nonneg b).trans_lt hbr, hrR⟩, hbr⟩
  have hr : 0 < (r : ℝ) := r.2.1
  set q := ‖b‖ / r
  have hq₀ : 0 ≤ q := by positivity
  have hq₁ : q < 1 := (div_lt_one hr).mpr hbr
  have hbq : ‖b‖ ≤ q * r := (div_mul_cancel₀ _ hr.ne').ge
  refine continuous_of_continuousAt_zero _ ?_
  rw [ContinuousAt, map_zero]
  have h : Tendsto (restrict (R := R) r) (𝓝 0) (𝓝 0) := by
    simpa only [map_zero] using (uniformContinuous_restrict (R := R) r).continuous.tendsto 0
  refine squeeze_zero_norm
    (a := fun f ↦ (‖(1 : A)‖ + 1) * ‖restrict r f‖ * (1 - q)⁻¹) (fun f ↦ ?_) ?_
  · have hf := TauCeti.PowerSeries.hasGaussNorm_of_isRestricted (restrict r f).2
    rw [coe_restrict] at hf
    rw [OnOpenDisc.evalAtHom_apply, TauCeti.PowerSeries.norm_eq_gaussNorm, coe_restrict]
    exact norm_evalAt_le_mul_gaussNorm hf hq₀ hq₁ hbq
  · simpa using (h.norm.const_mul (‖(1 : A)‖ + 1)).mul_const (1 - q)⁻¹

end TauCeti.PowerSeries.OnOpenDisc
