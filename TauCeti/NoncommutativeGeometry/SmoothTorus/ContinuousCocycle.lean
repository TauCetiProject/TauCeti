/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NoncommutativeGeometry.SmoothTorus.Derivation
public import TauCeti.NoncommutativeGeometry.SmoothTorus.Topology
public import TauCeti.RingTheory.CyclicCohomology.Continuous.Cohomology
public import TauCeti.RingTheory.CyclicCohomology.Continuous.Derivation

/-!
# Continuous cyclic cocycles of the smooth noncommutative torus

The lattice derivations are continuous for the weighted ℓ¹ seminorms: applying a derivation
costs one power of the weight. Consequently the odd cocycles `τ(a₀ δⱼ(a₁))` and the oriented
fundamental two-cocycle are jointly continuous. This file lifts the existing algebraic
cocycles to `continuousCyclicCocycles`, so they define classes in continuous cyclic cohomology
without changing their normalization. All statements allow arbitrary real rotation parameters.

## References

* A. Connes, *Noncommutative Geometry*, Chapter III, §2.β and Chapter IV, §6.

The algebraic cocycles are those of `SmoothTorus.Derivation`; the seminorm topology is that
of `SmoothTorus.Topology`.
-/

public section

open Complex Real

noncomputable section

namespace TauCeti.SmoothNoncommutativeTorus

variable {θ : ℝ}

/-- A lattice derivation loses at most one weight in the defining seminorms. -/
theorem seminorm_gaugeDerivation_le (ℓ : ℤ × ℤ →+ ℂ) (k : ℕ)
    (a : SmoothNoncommutativeTorus θ) :
    seminorm θ k ((gaugeDerivation θ ℓ : Module.End ℂ _) a) ≤
      (‖ℓ (1, 0)‖ + ‖ℓ (0, 1)‖) * seminorm θ (k + 1) a := by
  rw [seminorm_apply, seminorm_apply, ← tsum_mul_left]
  have hd := IsRapidDecay.summable_norm_mul_weight_pow
    ((gaugeDerivation θ ℓ : Module.End ℂ (SmoothNoncommutativeTorus θ)) a).isRapidDecay_coeff k
  have ha := (a.isRapidDecay_coeff.summable_norm_mul_weight_pow (k + 1)).mul_left
    (‖ℓ (1, 0)‖ + ‖ℓ (0, 1)‖)
  apply Summable.tsum_le_tsum _ hd ha
  intro x
  rw [coeff_gaugeDerivation, norm_mul, pow_succ]
  calc ‖ℓ x‖ * ‖a.coeff x‖ * weight x ^ k ≤
      ((‖ℓ (1, 0)‖ + ‖ℓ (0, 1)‖) * weight x) * ‖a.coeff x‖ * weight x ^ k := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (norm_addMonoidHom_apply_le_mul_weight ℓ x)
            (norm_nonneg _)) (pow_nonneg (weight_pos x).le _)
    _ = _ := by ring

/-- Every lattice derivation is continuous in the Fréchet topology. -/
@[fun_prop]
theorem continuous_gaugeDerivation (ℓ : ℤ × ℤ →+ ℂ) :
    Continuous (gaugeDerivation θ ℓ : Module.End ℂ (SmoothNoncommutativeTorus θ)) := by
  apply (withSeminorms θ).continuous_of_isBounded (withSeminorms θ)
  apply Seminorm.IsBounded.of_real
  intro k
  refine ⟨{k + 1}, ‖ℓ (1, 0)‖ + ‖ℓ (0, 1)‖, fun a ↦ ?_⟩
  simpa using seminorm_gaugeDerivation_le ℓ k a

/-- The first coordinate derivation is continuous. -/
@[fun_prop]
theorem continuous_derivation₁ :
    Continuous (derivation₁ θ : Module.End ℂ (SmoothNoncommutativeTorus θ)) := by
  rw [derivation₁_def]
  exact continuous_gaugeDerivation _

/-- The second coordinate derivation is continuous. -/
@[fun_prop]
theorem continuous_derivation₂ :
    Continuous (derivation₂ θ : Module.End ℂ (SmoothNoncommutativeTorus θ)) := by
  rw [derivation₂_def]
  exact continuous_gaugeDerivation _

/-- Joint continuity of the first odd cocycle. -/
@[fun_prop]
theorem continuous_oddCocycle₁ :
    Continuous ((oddCocycle₁ θ).1 :
      MultilinearMap ℂ (fun _ : Fin 2 ↦ SmoothNoncommutativeTorus θ) ℂ) := by
  simpa only [coe_oddCocycle₁] using
    continuous_traceDerivationCochain continuous_trace continuous_derivation₁

/-- Joint continuity of the second odd cocycle. -/
@[fun_prop]
theorem continuous_oddCocycle₂ :
    Continuous ((oddCocycle₂ θ).1 :
      MultilinearMap ℂ (fun _ : Fin 2 ↦ SmoothNoncommutativeTorus θ) ℂ) := by
  simpa only [coe_oddCocycle₂] using
    continuous_traceDerivationCochain continuous_trace continuous_derivation₂

/-- Joint continuity of the oriented fundamental cocycle, with its `(2πi)⁻¹` factor. -/
@[fun_prop]
theorem continuous_fundamentalCocycle :
    Continuous ((fundamentalCocycle θ).1 :
      MultilinearMap ℂ (fun _ : Fin 3 ↦ SmoothNoncommutativeTorus θ) ℂ) := by
  apply (continuous_congr fun a ↦ fundamentalCocycle_apply a).2
  simpa only [traceDerivationPairCochain_apply] using
    (continuous_traceDerivationPairCochain continuous_trace
      continuous_derivation₁ continuous_derivation₂).const_mul ((2 * π * I)⁻¹)

variable (θ) in
/-- The continuous cyclic cocycle `τ(a₀ δ₁(a₁))`. -/
def continuousOddCocycle₁ : continuousCyclicCocycles ℂ (SmoothNoncommutativeTorus θ) ℂ 1 :=
  cyclicCocycles.toContinuous (oddCocycle₁ θ) continuous_oddCocycle₁

variable (θ) in
/-- The continuous cyclic cocycle `τ(a₀ δ₂(a₁))`. -/
def continuousOddCocycle₂ : continuousCyclicCocycles ℂ (SmoothNoncommutativeTorus θ) ℂ 1 :=
  cyclicCocycles.toContinuous (oddCocycle₂ θ) continuous_oddCocycle₂

variable (θ) in
/-- The continuous oriented fundamental two-cocycle. -/
def continuousFundamentalCocycle :
    continuousCyclicCocycles ℂ (SmoothNoncommutativeTorus θ) ℂ 2 :=
  cyclicCocycles.toContinuous (fundamentalCocycle θ) continuous_fundamentalCocycle

/-- Forgetting continuity recovers the first odd cochain. -/
@[simp]
theorem toMultilinearMap_continuousOddCocycle₁ :
    (continuousOddCocycle₁ θ).1.1.toMultilinearMap = (oddCocycle₁ θ).1.1 := by
  rw [continuousOddCocycle₁, cyclicCocycles.toMultilinearMap_toContinuous]

/-- Forgetting continuity recovers the second odd cochain. -/
@[simp]
theorem toMultilinearMap_continuousOddCocycle₂ :
    (continuousOddCocycle₂ θ).1.1.toMultilinearMap = (oddCocycle₂ θ).1.1 := by
  rw [continuousOddCocycle₂, cyclicCocycles.toMultilinearMap_toContinuous]

/-- Forgetting continuity recovers the fundamental cochain, including its normalization. -/
@[simp]
theorem toMultilinearMap_continuousFundamentalCocycle :
    (continuousFundamentalCocycle θ).1.1.toMultilinearMap = (fundamentalCocycle θ).1.1 := by
  rw [continuousFundamentalCocycle, cyclicCocycles.toMultilinearMap_toContinuous]

/-- Evaluation of the first continuous odd cocycle. -/
@[simp]
theorem continuousOddCocycle₁_apply (a : Fin 2 → SmoothNoncommutativeTorus θ) :
    (continuousOddCocycle₁ θ).1.1 a =
      trace θ (a 0 * (derivation₁ θ : Module.End ℂ _) (a 1)) := by
  rw [continuousOddCocycle₁, cyclicCocycles.toContinuous_apply,
    coe_oddCocycle₁, traceDerivationCochain_apply]

/-- Evaluation of the second continuous odd cocycle. -/
@[simp]
theorem continuousOddCocycle₂_apply (a : Fin 2 → SmoothNoncommutativeTorus θ) :
    (continuousOddCocycle₂ θ).1.1 a =
      trace θ (a 0 * (derivation₂ θ : Module.End ℂ _) (a 1)) := by
  rw [continuousOddCocycle₂, cyclicCocycles.toContinuous_apply,
    coe_oddCocycle₂, traceDerivationCochain_apply]

/-- Evaluation of the continuous fundamental cocycle agrees with the algebraic one. -/
@[simp]
theorem continuousFundamentalCocycle_apply (a : Fin 3 → SmoothNoncommutativeTorus θ) :
    (continuousFundamentalCocycle θ).1.1 a = (fundamentalCocycle θ).1.1 a := by
  rw [continuousFundamentalCocycle, cyclicCocycles.toContinuous_apply]

end TauCeti.SmoothNoncommutativeTorus
