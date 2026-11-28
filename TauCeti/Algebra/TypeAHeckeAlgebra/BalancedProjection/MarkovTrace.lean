/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.TypeAHeckeAlgebra.BalancedProjection.Complement

/-!
# Markov traces on the balanced projection algebra

A Markov trace with projection parameter `η : R` on `BalancedProjectionAlgebra R τ` is a
normalized tracial `R`-linear functional `μ` satisfying `μ (w * e n) = η * μ w` for every
`w ∈ stage R τ (n + 1)`.

Precomposing with `complementEquiv` sends `η` to `1 - η`. Comparison with Hecke Markov traces
along `heckeEquiv` is in
`TauCeti.Algebra.TypeAHeckeAlgebra.BalancedProjection.HeckeComparison.MarkovTrace`.

## Main definitions and results

* `TauCeti.BalancedProjectionAlgebra.IsMarkovTrace`: Markov trace predicate on
  `BalancedProjectionAlgebra R τ`.
* `TauCeti.BalancedProjectionAlgebra.IsMarkovTrace.unique`: uniqueness of Markov traces.
* `TauCeti.BalancedProjectionAlgebra.isMarkovTrace_character`: every scalar character is a Markov
  trace.
* `TauCeti.BalancedProjectionAlgebra.IsMarkovTrace.comp_complementEquiv`,
  `isMarkovTrace_comp_complementEquiv_iff`: complement symmetry of Markov traces.

## References

* H. Wenzl, *Hecke algebras of type A_n and subfactors*, Invent. Math. 92 (1988), 349–383, §§2–3.
* V. F. R. Jones, *Hecke algebra representations of braid groups and link polynomials*,
  Ann. of Math. 126 (1987), 335–388, §§5, 11.
-/

public section

namespace TauCeti.BalancedProjectionAlgebra

variable {R : Type*} [CommRing R] {τ : R}

/-- A Markov trace with projection parameter `η : R` on `BalancedProjectionAlgebra R τ`: a
normalized tracial `R`-linear functional satisfying `μ (w * e n) = η * μ w` on
`stage R τ (n + 1)`. -/
structure IsMarkovTrace (η : R) (μ : BalancedProjectionAlgebra R τ →ₗ[R] R) : Prop where
  /-- A Markov trace is normalized at `1`. -/
  map_one : μ 1 = 1
  /-- A Markov trace is tracial. -/
  map_mul_comm (x y : BalancedProjectionAlgebra R τ) : μ (x * y) = μ (y * x)
  /-- Appending `e n` to an element of `stage R τ (n + 1)` multiplies the trace by `η`. -/
  map_mul_e {n : ℕ} {w : BalancedProjectionAlgebra R τ} (hw : w ∈ stage R τ (n + 1)) :
    μ (w * e τ n) = η * μ w

namespace IsMarkovTrace

variable {η : R} {μ : BalancedProjectionAlgebra R τ →ₗ[R] R}

/-- A Markov trace recovers scalars along `algebraMap`. -/
theorem map_algebraMap (hμ : IsMarkovTrace η μ) (r : R) : μ (algebraMap R _ r) = r := by
  rw [Algebra.algebraMap_eq_smul_one, map_smul, hμ.map_one, smul_eq_mul, mul_one]

/-- Every generator has trace equal to the projection parameter `η`. -/
theorem map_e (hμ : IsMarkovTrace η μ) (i : ℕ) : μ (e τ i) = η := by
  simpa [hμ.map_one] using hμ.map_mul_e (n := i) (Subalgebra.one_mem _)

/-- Two Markov traces on `BalancedProjectionAlgebra R τ` with the same parameter `η` are equal. -/
theorem unique {μ' : BalancedProjectionAlgebra R τ →ₗ[R] R}
    (hμ : IsMarkovTrace η μ) (hμ' : IsMarkovTrace η μ') : μ = μ' :=
  eq_of_markov hμ.map_one hμ.map_mul_comm hμ.map_mul_e hμ'.map_one hμ'.map_mul_comm hμ'.map_mul_e

/-- Precomposing a Markov trace of parameter `η` with `complementEquiv` produces a Markov trace of
parameter `1 - η`. -/
theorem comp_complementEquiv (hμ : IsMarkovTrace η μ) :
    IsMarkovTrace (1 - η) (μ.comp (complementEquiv τ).toLinearMap) where
  map_one := by simpa using hμ.map_one
  map_mul_comm x y := by simpa using hμ.map_mul_comm (complementEquiv τ x) (complementEquiv τ y)
  map_mul_e hw := by
    simp only [LinearMap.comp_apply, AlgEquiv.toLinearMap_apply, map_mul, complementEquiv_e,
      mul_sub, mul_one, map_sub]
    rw [hμ.map_mul_e ((complementEquiv_mem_stage_iff τ).2 hw)]
    ring

end IsMarkovTrace

/-- Each scalar character `e i ↦ c` is a Markov trace with projection parameter `c`. -/
theorem isMarkovTrace_character (c : R) (hc : IsIdempotentElem c) :
    IsMarkovTrace c (character (τ := τ) c hc).toLinearMap where
  map_one := map_one (character (τ := τ) c hc)
  map_mul_comm x y := by simp [mul_comm]
  map_mul_e _ := by simp [mul_comm]

@[simp]
theorem isMarkovTrace_comp_complementEquiv_iff {η : R}
    {μ : BalancedProjectionAlgebra R τ →ₗ[R] R} :
    IsMarkovTrace (1 - η) (μ.comp (complementEquiv τ).toLinearMap) ↔ IsMarkovTrace η μ :=
  ⟨fun h ↦ by
    have hc :
        (μ.comp (complementEquiv τ).toLinearMap).comp (complementEquiv τ).toLinearMap = μ := by
      ext x; simp
    simpa only [hc, sub_sub_cancel] using h.comp_complementEquiv,
    IsMarkovTrace.comp_complementEquiv⟩

end TauCeti.BalancedProjectionAlgebra
