/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Analysis.Semigroups.Generator.Basic
import Mathlib.Analysis.Calculus.Deriv.Slope

/-!
# Differentiability of semigroup orbits

This file characterizes membership in the infinitesimal generator domain by right
differentiability of the orbit at zero, and identifies the right derivative there with the
generator.

## References

The argument follows Engel--Nagel, *One-Parameter Semigroups for Linear Evolution
Equations*, Lemma II.1.3(ii).
-/

public section

noncomputable section

open scoped Topology

namespace TauCeti.Semigroups

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

namespace StronglyContinuousSemigroup


/-- At time zero, the right derivative of the orbit of a generator-domain vector is its
generator. -/
theorem realOperator_hasDerivWithinAt_zero (S : StronglyContinuousSemigroup X)
    (x : S.domain) :
    HasDerivWithinAt (fun s : ℝ => S.realOperator s (x : X))
      (S.generator ⟨x, by rw [S.generator_domain]; exact x.property⟩) (Set.Ici 0) 0 := by
  rw [hasDerivWithinAt_iff_tendsto_slope]
  unfold slope
  simpa [S.realOperator_zero_apply] using S.generator_tendsto x

/-- The orbit of a generator-domain vector is right-differentiable at time zero. -/
theorem realOperator_differentiableWithinAt_zero (S : StronglyContinuousSemigroup X)
    (x : S.domain) :
    DifferentiableWithinAt ℝ (fun s : ℝ => S.realOperator s (x : X)) (Set.Ici 0) 0 :=
  (S.realOperator_hasDerivWithinAt_zero x).differentiableWithinAt

/-- The right derivative at zero of the orbit of a generator-domain vector is its generator. -/
@[simp]
theorem realOperator_derivWithin_zero (S : StronglyContinuousSemigroup X)
    (x : S.domain) :
    derivWithin (fun s : ℝ => S.realOperator s (x : X)) (Set.Ici 0) 0 =
      S.generator ⟨x, by rw [S.generator_domain]; exact x.property⟩ :=
  (S.realOperator_hasDerivWithinAt_zero x).derivWithin (uniqueDiffWithinAt_Ici 0)

/-- The orbit has right derivative `y` at zero exactly when its initial vector belongs to the
generator domain and the generator value is `y`. -/
theorem realOperator_hasDerivWithinAt_zero_iff (S : StronglyContinuousSemigroup X)
    (x y : X) :
    HasDerivWithinAt (fun s : ℝ => S.realOperator s x) y (Set.Ici 0) 0 ↔
      ∃ hx : x ∈ S.domain,
        S.generator ⟨x, by rw [S.generator_domain]; exact hx⟩ = y := by
  constructor
  · intro h
    rw [hasDerivWithinAt_iff_tendsto_slope] at h
    unfold slope at h
    have ht : Filter.Tendsto (fun t => (1 / t) • (S.realOperator t x - x))
        (nhdsWithin 0 (Set.Ioi 0)) (nhds y) := by
      simpa [S.realOperator_zero_apply] using h
    have hx : x ∈ S.domain := (S.mem_domain_iff_tendsto x).2 ⟨y, ht⟩
    exact ⟨hx, S.generator_eq_of_tendsto hx ht⟩
  · rintro ⟨hx, hxy⟩
    rw [← hxy]
    exact S.realOperator_hasDerivWithinAt_zero ⟨x, hx⟩

/-- A vector belongs to the generator domain exactly when its orbit is right-differentiable
at time zero. -/
theorem mem_domain_iff_differentiableWithinAt_realOperator_zero
    (S : StronglyContinuousSemigroup X) (x : X) :
    x ∈ S.domain ↔
      DifferentiableWithinAt ℝ (fun s : ℝ => S.realOperator s x) (Set.Ici 0) 0 := by
  constructor
  · intro hx
    exact S.realOperator_differentiableWithinAt_zero ⟨x, hx⟩
  · intro hx
    obtain ⟨y, hy⟩ := hx
    have hy' := hy.hasDerivWithinAt
    refine (S.mem_domain_iff_tendsto x).2 ⟨y 1, ?_⟩
    rw [hasDerivWithinAt_iff_tendsto_slope] at hy'
    unfold slope at hy'
    simpa [S.realOperator_zero_apply] using hy'

end StronglyContinuousSemigroup

end TauCeti.Semigroups
