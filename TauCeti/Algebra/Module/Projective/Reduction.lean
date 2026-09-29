/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Module.ProjectiveCover.Basic

/-!
# Projective modules are determined by a radical quotient

Finitely generated projective modules over a ring are determined by their reductions modulo an
ideal in the Jacobson radical.  Indeed, the quotient map from a projective module to its reduction
is a projective cover, and uniqueness of projective covers identifies the two projective modules.

This is the algebraic lifting step used when integral projective modules are compared through a
residue-field calculation.  The result applies to noncommutative rings and does not require the
ideal itself to be the whole Jacobson radical.

## Main result

* `TauCeti.nonempty_linearEquiv_of_quotient_smul_top`: two finitely generated projective modules
  with isomorphic quotients by an ideal in the Jacobson radical are isomorphic.

## References

See T. Y. Lam, *A First Course in Noncommutative Rings*, Section 24, for projective covers over
semiperfect rings and their uniqueness.
-/

public section

namespace TauCeti

universe u v w

variable {R : Type u} [Ring R] (I : Ideal R) (M : Type v) (N : Type w)
  [AddCommGroup M] [Module R M] [Module.Finite R M] [Module.Projective R M]
  [AddCommGroup N] [Module R N] [Module.Finite R N] [Module.Projective R N]

/-- **Finitely generated projectives are determined by a radical quotient.** If `I` lies in the
Jacobson radical of `R`, then an `R`-linear equivalence between `M / IM` and `N / IN` implies that
the finitely generated projective modules `M` and `N` are `R`-linearly equivalent.

Only existence of the resulting equivalence is asserted: both quotient maps are projective covers
of the same reduced module, so uniqueness of projective covers identifies their sources. -/
theorem nonempty_linearEquiv_of_quotient_smul_top (hI : I ≤ Ring.jacobson R)
    (h : Nonempty
      ((M ⧸ (I • (⊤ : Submodule R M))) ≃ₗ[R] (N ⧸ (I • (⊤ : Submodule R N))))) :
    Nonempty (M ≃ₗ[R] N) := by
  let e := h.some
  have hMsmall : IsSuperfluous (I • (⊤ : Submodule R M)) :=
    isSuperfluous_of_le_jacobson <|
      (Submodule.smul_mono hI le_rfl).trans (Ring.jacobson_smul_top_le R M)
  have hNsmall : IsSuperfluous (I • (⊤ : Submodule R N)) :=
    isSuperfluous_of_le_jacobson <|
      (Submodule.smul_mono hI le_rfl).trans (Ring.jacobson_smul_top_le R N)
  have hMcover : IsProjectiveCover
      (e.toLinearMap ∘ₗ (I • (⊤ : Submodule R M)).mkQ) :=
    (isProjectiveCover_mkQ_iff.mpr hMsmall).comp e.surjective <| by
      rw [LinearMap.ker_eq_bot.mpr e.injective]
      exact isSuperfluous_bot
  have hNcover : IsProjectiveCover (I • (⊤ : Submodule R N)).mkQ :=
    isProjectiveCover_mkQ_iff.mpr hNsmall
  exact ⟨(hMcover.exists_linearEquiv hNcover).choose⟩

end TauCeti
