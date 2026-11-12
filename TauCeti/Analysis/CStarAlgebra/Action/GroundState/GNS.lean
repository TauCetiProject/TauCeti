/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.CStarAlgebra.Action.Covariant.GNS
public import TauCeti.Analysis.CStarAlgebra.Action.GroundState.Basic
import TauCeti.Topology.Algebra.Module.LinearPMap.GraphCore

/-!
# Ground states and the GNS Hamiltonian

Let `α` be a point-norm continuous real action on a possibly nonunital C⋆-algebra `A`. An
invariant state `ω` has a GNS Hamiltonian `CStarAction.gnsHamiltonian`, the self-adjoint
generator `H` of its GNS implementing group, `U_t = exp (i t H)`. The classes `[a]` of the
elements `a` of the domain of the generator `δ` of `α` form a core for `H`,
`CStarAction.gnsHamiltonian_hasCore`, on which `⟪[a], H [a]⟫ = -i ω (a⋆ δ(a))`.

A ground state `ω` is invariant, and its GNS Hamiltonian is nonnegative,
`CStarAction.IsGroundState.inner_gnsHamiltonian_nonneg`: by the generator inequality
`-i ω (a⋆ δ(a)) ≥ 0` the quadratic form of `H` is nonnegative on the core, hence on the closed
graph of `H`. Conversely an invariant state with nonnegative GNS Hamiltonian satisfies the
generator inequality, and so is a ground state. Thus the ground states are exactly the invariant
states with nonnegative GNS Hamiltonian,
`CStarAction.isGroundState_iff_exists_inner_gnsHamiltonian_nonneg`.

## References

Bratteli--Robinson, *Operator Algebras and Quantum Statistical Mechanics 2*, second edition,
Proposition 5.3.19, for the equivalence of the ground-state condition, the generator inequality,
and invariance with a positive GNS Hamiltonian.
-/

public section

noncomputable section

open Complex PositiveLinearMap
open scoped ComplexOrder InnerProductSpace

namespace TauCeti.CStarAction

variable {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  {α : CStarAction (Multiplicative ℝ) A} {ω : A →P[ℂ] ℂ}

/-- **The GNS Hamiltonian of a ground state is nonnegative**: `0 ≤ ⟪ξ, H ξ⟫` on its domain. -/
theorem IsGroundState.inner_gnsHamiltonian_nonneg (hω : α.IsGroundState ω)
    (hf : ∀ t a, (ω : A →ₚ[ℂ] ℂ) (α t a) = (ω : A →ₚ[ℂ] ℂ) a)
    (ξ : (α.gnsHamiltonian hf).domain) :
    0 ≤ ⟪(ξ : (ω : A →ₚ[ℂ] ℂ).GNS), α.gnsHamiltonian hf ξ⟫_ℂ := by
  -- The quadratic form is nonnegative on the graph of the restriction of `H` to the core, hence on
  -- its closure, the graph of `H`.
  refine (α.gnsHamiltonian_hasCore hf).graph_subset_of_isClosed (s := {p | 0 ≤ ⟪p.1, p.2⟫_ℂ})
    (isClosed_le continuous_const (continuous_fst.inner continuous_snd)) ?_
    ((α.gnsHamiltonian hf).mem_graph ξ)
  rintro ⟨_, _⟩ hp
  obtain ⟨⟨_, hv⟩, h1, h2⟩ := (LinearPMap.mem_graph_iff _).mp hp
  obtain ⟨a, ha, rfl⟩ := Submodule.mem_map.mp (Submodule.mem_inf.mp hv).1
  simp only at h1 h2
  subst h1 h2
  rw [Set.mem_ofPred_eq, LinearPMap.domRestrict_le.2 (x := ⟨_, hv⟩)
    (y := ⟨_, α.toPreGNS_mem_gnsHamiltonian_domain hf ⟨a, ha⟩⟩) (by simp),
    ContinuousLinearMap.coe_coe, toGNS_apply, inner_toPreGNS_gnsHamiltonian_apply_toPreGNS]
  simpa using hω.neg_I_mul_apply_star_mul_generator_nonneg ⟨a, ha⟩

/-- **Ground states are the invariant states with nonnegative GNS Hamiltonian.** A state `ω` is a
ground state of `α` exactly when it is `α`-invariant and its GNS Hamiltonian `H` satisfies
`0 ≤ ⟪ξ, H ξ⟫` on its domain. -/
theorem isGroundState_iff_exists_inner_gnsHamiltonian_nonneg :
    α.IsGroundState ω ↔ ‖(ω : A →L[ℂ] ℂ)‖ = 1 ∧
      ∃ hf : ∀ t a, (ω : A →ₚ[ℂ] ℂ) (α t a) = (ω : A →ₚ[ℂ] ℂ) a,
        ∀ ξ : (α.gnsHamiltonian hf).domain,
          0 ≤ ⟪(ξ : (ω : A →ₚ[ℂ] ℂ).GNS), α.gnsHamiltonian hf ξ⟫_ℂ := by
  refine ⟨fun hω => ⟨hω.norm_eq_one, fun t a => by simpa using hω.apply_action t a,
    hω.inner_gnsHamiltonian_nonneg _⟩, fun ⟨hnorm, hf, h⟩ =>
    isGroundState_iff_neg_I_mul_apply_star_mul_generator_nonneg.mpr ⟨hnorm, fun a => ?_⟩⟩
  have ha := h ⟨_, α.toPreGNS_mem_gnsHamiltonian_domain hf a⟩
  rwa [inner_toPreGNS_gnsHamiltonian_apply_toPreGNS] at ha

end TauCeti.CStarAction
