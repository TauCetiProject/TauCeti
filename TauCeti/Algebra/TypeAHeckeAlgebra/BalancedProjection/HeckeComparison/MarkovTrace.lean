/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.TypeAHeckeAlgebra.BalancedProjection.HeckeComparison.Basic
public import TauCeti.Algebra.TypeAHeckeAlgebra.BalancedProjection.MarkovTrace
public import TauCeti.Algebra.TypeAHeckeAlgebra.MarkovTrace
import Mathlib.Tactic.LinearCombination

/-!
# Markov trace comparison between the balanced projection and type-A Hecke algebras

When `τ * (q + q⁻¹) ^ 2 = 1`, projection Markov traces of parameter `η` on
`BalancedProjectionAlgebra R τ` correspond bijectively under `heckeEquiv` to Hecke Markov traces
of parameter `z = q * η - q⁻¹ * (1 - η)`.

## Main results

* `TauCeti.BalancedProjectionAlgebra.isMarkovTrace_comp_heckeEquiv_iff`,
  `TauCeti.BalancedProjectionAlgebra.heckeParam_eq`: Markov trace transport and parameter recovery.
* `TauCeti.InfiniteTypeAHeckeAlgebra.IsMarkovTrace.map_heckeEquiv_mul_e`: projection parameter of a
  Hecke Markov trace.

## References

* H. Wenzl, *Hecke algebras of type A_n and subfactors*, Invent. Math. 92 (1988), 349–383, §§2–3.
* V. F. R. Jones, *Hecke algebra representations of braid groups and link polynomials*,
  Ann. of Math. 126 (1987), 335–388, §§5, 11.
-/

public section

namespace TauCeti

namespace BalancedProjectionAlgebra

open InfiniteTypeAHeckeAlgebra (T)

variable {R : Type*} [CommRing R] {τ : R}

/-- Transporting along `heckeEquiv` identifies Hecke Markov traces of parameter
`z = q * η - q⁻¹ * (1 - η)` with projection Markov traces of parameter `η`. -/
theorem isMarkovTrace_comp_heckeEquiv_iff {q : Rˣ} (hτ : τ * ((q : R) + ↑q⁻¹) ^ 2 = 1)
    {z η : R} (hz : z = (q : R) * η - ↑q⁻¹ * (1 - η))
    {μ : InfiniteTypeAHeckeAlgebra R q →ₗ[R] R} :
    IsMarkovTrace η (μ.comp (heckeEquiv q hτ).toLinearMap) ↔
      InfiniteTypeAHeckeAlgebra.IsMarkovTrace z μ := by
  constructor
  · intro hμ
    refine ⟨by simpa only [LinearMap.comp_apply, AlgEquiv.toLinearMap_apply, map_one] using
          hμ.map_one,
      fun x y ↦ by
        simpa only [LinearMap.comp_apply, AlgEquiv.toLinearMap_apply, map_mul,
          AlgEquiv.apply_symm_apply] using
          hμ.map_mul_comm ((heckeEquiv q hτ).symm x) ((heckeEquiv q hτ).symm y),
      fun {n x} hx ↦ ?_⟩
    have hmem : (heckeEquiv q hτ).symm x ∈ stage R τ (n + 1) := by
      simpa only [← heckeEquiv_mem_stage_iff hτ, AlgEquiv.apply_symm_apply] using hx
    have hmul : μ (x * heckeEquiv q hτ (e τ n)) = η * μ x := by
      simpa only [LinearMap.comp_apply, AlgEquiv.toLinearMap_apply, map_mul,
        AlgEquiv.apply_symm_apply] using hμ.map_mul_e hmem
    let L : InfiniteTypeAHeckeAlgebra R q →ₗ[R] R := μ.comp (LinearMap.mul R _ x)
    calc μ (x * T q n)
        = L (((q : R) + ↑q⁻¹) • heckeEquiv q hτ (e τ n) - algebraMap R _ ↑q⁻¹) := by
          rw [← T_eq_smul_heckeEquiv_e_sub hτ n]
          simp only [L, LinearMap.comp_apply, LinearMap.mul_apply']
      _ = ((q : R) + ↑q⁻¹) * (η * μ x) - ↑q⁻¹ * μ x := by
          simp only [L, Algebra.algebraMap_eq_smul_one, map_sub, map_smul, LinearMap.comp_apply,
            LinearMap.mul_apply', mul_one, hmul, smul_eq_mul]
      _ = z * μ x := by
          rw [hz]
          ring
  · intro hμ
    refine ⟨by simpa only [LinearMap.comp_apply, AlgEquiv.toLinearMap_apply, map_one] using
          hμ.map_one,
      fun x y ↦ by
        simpa only [LinearMap.comp_apply, AlgEquiv.toLinearMap_apply, map_mul] using
          hμ.map_mul_comm (heckeEquiv q hτ x) (heckeEquiv q hτ y),
      fun {n w} hw ↦ ?_⟩
    have hw' : heckeEquiv q hτ w ∈ InfiniteTypeAHeckeAlgebra.stage R q (n + 1) :=
      (heckeEquiv_mem_stage_iff hτ).2 hw
    simpa only [LinearMap.comp_apply, AlgEquiv.toLinearMap_apply, map_mul, heckeEquiv_e,
      ← val_inv_addInvUnit hτ] using
      hμ.map_mul_eigenprojection (addInvUnit hτ) (val_addInvUnit hτ) hz hw'

/-- Recovering the Hecke Markov parameter `z` from the transported balanced-projection parameter
`η = τ * (q + q⁻¹) * (z + q⁻¹)` when `τ * (q + q⁻¹) ^ 2 = 1`. -/
theorem heckeParam_eq {q : Rˣ} (hτ : τ * ((q : R) + ↑q⁻¹) ^ 2 = 1) (z : R) :
    z = (q : R) * (τ * ((q : R) + ↑q⁻¹) * (z + ↑q⁻¹)) -
      ↑q⁻¹ * (1 - τ * ((q : R) + ↑q⁻¹) * (z + ↑q⁻¹)) := by
  linear_combination -(z + ↑q⁻¹) * hτ

end BalancedProjectionAlgebra

namespace InfiniteTypeAHeckeAlgebra.IsMarkovTrace

open BalancedProjectionAlgebra

variable {R : Type*} [CommRing R] {τ : R} {q : Rˣ} {z : R}
  {μ : InfiniteTypeAHeckeAlgebra R q →ₗ[R] R}

/-- **The projection parameter of a Hecke Markov trace.** Transported along the isomorphism with
the balanced projection algebra, a Markov trace with parameter `z` multiplies by
`η = (z + q⁻¹) / (q + q⁻¹)` when a new last projection is appended: for `w` in the stage of the
first `n + 1` strands, `μ (w * e n) = η * μ w`. Here `(q + q⁻¹)⁻¹ = τ * (q + q⁻¹)`. -/
theorem map_heckeEquiv_mul_e (hμ : IsMarkovTrace z μ) (hτ : τ * ((q : R) + ↑q⁻¹) ^ 2 = 1)
    {n : ℕ} {w : BalancedProjectionAlgebra R τ}
    (hw : w ∈ BalancedProjectionAlgebra.stage R τ (n + 1)) :
    μ (heckeEquiv q hτ (w * e τ n)) =
      τ * ((q : R) + ↑q⁻¹) * (z + ↑q⁻¹) * μ (heckeEquiv q hτ w) :=
  ((isMarkovTrace_comp_heckeEquiv_iff hτ (heckeParam_eq hτ z)).mpr hμ).map_mul_e hw

end InfiniteTypeAHeckeAlgebra.IsMarkovTrace

end TauCeti
