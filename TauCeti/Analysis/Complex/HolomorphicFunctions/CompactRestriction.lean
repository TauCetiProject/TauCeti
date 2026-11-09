/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.HolomorphicFunctions.RestrictionEstimate

/-!
# Small restriction to compact subsets

For a compact subset `s` of an open complex domain `U`, restriction to `s` is arbitrarily
small on a subspace of finite codimension: given `ε > 0`, finitely many linear conditions
on a holomorphic function ensure that every uniform bound `M` on `U` improves to `ε * M`
on `s`. The conditions are imposed simultaneously at finitely many centres of discs
covering `s`. No connectedness of `U`, boundary regularity, or boundedness of `U` is needed.

This is the compact-set version of the disc restriction estimate, used when comparing
holomorphic cochains on nested finite covers. The functions keep their compact-open
topology; the estimate does not require a new normed function space.

## References

* Otto Forster, *Lectures on Riemann Surfaces*, §14, for small restriction on a subspace
  of finite codimension in the finiteness proof for analytic cohomology.
-/

public noncomputable section

open Metric Set TopologicalSpace

namespace TauCeti.HolomorphicFunctions

/-- Fix the inherited additive group before forming quotients. -/
local instance (U : Opens ℂ) : AddCommGroup (holomorphicFunctions U) := inferInstance

/-- Linear maps use the same monoid projection as the quotient's additive group. -/
local instance (U : Opens ℂ) : AddCommMonoid (holomorphicFunctions U) :=
  (inferInstance : AddCommGroup (holomorphicFunctions U)).toAddCommMonoid

/-- Restriction to any compact subset of an open complex domain is arbitrarily small on a
subspace of finite codimension. The same subspace works for every uniform bound `M` on the
original domain. In particular, the zero or a negative bound is not excluded. -/
theorem exists_finiteDimensional_quotient_norm_le_of_isCompact {U : Opens ℂ} {s : Set ℂ}
    (hs : IsCompact s) (hsU : s ⊆ U) {ε : ℝ} (hε : 0 < ε) :
    ∃ K : Submodule ℂ (holomorphicFunctions U),
      FiniteDimensional ℂ (holomorphicFunctions U ⧸ K) ∧
      ∀ f ∈ K, ∀ M : ℝ, (∀ z ∈ U, ‖extend f z‖ ≤ M) →
        ∀ z ∈ s, ‖extend f z‖ ≤ ε * M := by
  classical
  -- Cover the compact set by smaller discs whose larger partners remain in the domain.
  have hballs (a : s) : ∃ R : ℝ, 0 < R ∧ ball (a : ℂ) R ⊆ U :=
    isOpen_iff.mp U.isOpen a (hsU a.property)
  choose R hR hRU using hballs
  obtain ⟨t, ht⟩ := hs.elim_finite_subcover (fun a : s => ball (a : ℂ) (R a / 2))
    (fun _ => isOpen_ball) (fun a ha =>
      mem_iUnion.mpr ⟨⟨a, ha⟩, mem_ball_self (half_pos (hR ⟨a, ha⟩))⟩)
  have hlocal (a : t) : ∃ K : Submodule ℂ (holomorphicFunctions U),
      FiniteDimensional ℂ (holomorphicFunctions U ⧸ K) ∧
      ∀ f ∈ K, ∀ M : ℝ, (∀ z ∈ ball (a.val : ℂ) (R a.val), ‖extend f z‖ ≤ M) →
        ∀ z ∈ closedBall (a.val : ℂ) (R a.val / 2), ‖extend f z‖ ≤ ε * M :=
    exists_finiteDimensional_quotient_norm_le (hR a.val) (hRU a.val)
      (half_pos (hR a.val)).le (half_lt_self (hR a.val)) hε
  choose K hfinite hsmall using hlocal
  -- A single map to a finite product of finite-dimensional quotients imposes all conditions.
  let q : holomorphicFunctions U →ₗ[ℂ] ((a : t) → holomorphicFunctions U ⧸ K a) :=
    LinearMap.pi fun a => (K a).mkQ
  let (a : t) : FiniteDimensional ℂ (holomorphicFunctions U ⧸ K a) := hfinite a
  refine ⟨q.ker, ?_, fun f hf M hM z hz => ?_⟩
  · exact q.quotKerEquivRange.symm.finiteDimensional
  · obtain ⟨a, ha, hza⟩ := mem_iUnion₂.mp (ht hz)
    have hfa : f ∈ K ⟨a, ha⟩ := by
      exact (Submodule.Quotient.mk_eq_zero (K ⟨a, ha⟩)).mp
        (congrFun (LinearMap.mem_ker.mp hf) ⟨a, ha⟩)
    exact hsmall ⟨a, ha⟩ f hfa M (fun w hw => hM w (hRU a hw))
      z (ball_subset_closedBall hza)

end TauCeti.HolomorphicFunctions
