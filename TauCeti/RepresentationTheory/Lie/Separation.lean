/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import TauCeti.Algebra.Lie.Prod

/-!
# Separating a finite-dimensional Lie algebra by representations

A family of representations separates a Lie algebra when every nonzero element acts nontrivially
in at least one member. For a finite-dimensional Lie algebra, pointwise separation already gives a
single faithful finite-dimensional representation.

This criterion lets downstream constructions prove faithfulness by supplying a finite-dimensional
representation separately for each nonzero element; the detecting carriers and maps need not be
chosen uniformly.

## Main result

* `TauCeti.exists_faithfulRepresentation_of_pointSeparating`: locally detecting every nonzero
  element by a finite-dimensional representation produces one faithful finite-dimensional
  representation.
-/

public section

namespace TauCeti

attribute [local instance 100] LieRing.ofAssociativeRing

universe u v w

variable (K : Type u) [Field K]
variable (L : Type v) [LieRing L] [LieAlgebra K L]

/-- If every nonzero element of a finite-dimensional Lie algebra acts nontrivially in some
finite-dimensional representation, then one finite-dimensional representation is faithful. -/
theorem exists_faithfulRepresentation_of_pointSeparating [FiniteDimensional K L]
    (hseparates : ∀ x : L, x ≠ 0 →
      ∃ (V : Type w) (_ : AddCommGroup V) (_ : Module K V) (_ : FiniteDimensional K V)
        (rho : L →ₗ⁅K⁆ Module.End K V), rho x ≠ 0) :
    ∃ (V : Type w) (_ : AddCommGroup V) (_ : Module K V) (_ : FiniteDimensional K V)
      (rho : L →ₗ⁅K⁆ Module.End K V), Function.Injective rho := by
  let kernelRanks : Set ℕ := {n | ∃ (V : Type w) (_ : AddCommGroup V) (_ : Module K V)
    (_ : FiniteDimensional K V) (rho : L →ₗ⁅K⁆ Module.End K V),
      Module.finrank K rho.ker = n}
  have kernelRanks_nonempty : kernelRanks.Nonempty := by
    refine ⟨Module.finrank K (0 : L →ₗ⁅K⁆ Module.End K PUnit).ker, PUnit,
      inferInstance, inferInstance, inferInstance, 0, rfl⟩
  let n := wellFounded_lt.min kernelRanks kernelRanks_nonempty
  have hn : n ∈ kernelRanks := wellFounded_lt.min_mem kernelRanks kernelRanks_nonempty
  rcases hn with ⟨V, _, _, _, rho, hrank⟩
  refine ⟨V, inferInstance, inferInstance, inferInstance, rho, ?_⟩
  by_contra hrho
  have hker : rho.ker ≠ ⊥ := fun hbot ↦
    hrho ((LieHom.ker_eq_bot (f := rho)).mp hbot)
  obtain ⟨x, hxker, hxbot⟩ := IsConcreteLE.exists_of_lt (bot_lt_iff_ne_bot.mpr hker)
  have hxne : x ≠ 0 := by
    simpa using hxbot
  obtain ⟨W, _, _, _, sigma, hsigma⟩ := hseparates x hxne
  let tau : L →ₗ⁅K⁆ Module.End K (V × W) := rho.prodRepresentation sigma
  have htau_mem : Module.finrank K tau.ker ∈ kernelRanks := by
    exact ⟨V × W, inferInstance, inferInstance, inferInstance, tau, rfl⟩
  have htau_ker : tau.ker = rho.ker ⊓ sigma.ker := by
    exact LieHom.ker_prodRepresentation rho sigma
  have htau_lt : tau.ker < rho.ker := by
    rw [htau_ker]
    constructor
    · exact inf_le_left
    · intro hle
      have hxinf : x ∈ rho.ker ⊓ sigma.ker := hle hxker
      exact hsigma (LieHom.mem_ker.mp hxinf.2)
  have hrank_lt : Module.finrank K tau.ker < Module.finrank K rho.ker :=
    Submodule.finrank_lt_finrank_of_lt htau_lt
  exact (wellFounded_lt.not_lt_min kernelRanks htau_mem) (hrank_lt.trans_le hrank.le)

end TauCeti
