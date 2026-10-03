/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.Projective
public import Mathlib.RingTheory.Jacobson.Radical
public import Mathlib.RingTheory.SimpleModule.Basic
public import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.RingTheory.Artinian.Module
import TauCeti.Algebra.Module.ProjectiveCover.Basic
import TauCeti.RingTheory.Jacobson.Semiprimary
import TauCeti.RingTheory.Semisimple.Multiplicity

/-!
# Projective modules are determined by a radical quotient

Projective modules over a ring whose submodule lattices are coatomic (for instance, finitely
generated projective modules) are determined by their reductions modulo an ideal in the Jacobson
radical.  Indeed, the quotient map from a projective module to its reduction
is a projective cover, and uniqueness of projective covers identifies the two projective modules.

This is the algebraic lifting step used when integral projective modules are compared through a
residue-field calculation.  The result applies to noncommutative rings and does not require the
ideal itself to be the whole Jacobson radical.

When the radical quotient `R ⧸ J` of the ring is finite, as for a finite ring or for the group
algebra of a finite group over `ℤ_p`, the radical quotient `P ⧸ J • P` of a finitely generated
module is semisimple and is determined by its composition factors. These are counted by the
numbers of maps from `P` to the simple modules, `#Hom(P, S) = #End(S) ^ [P ⧸ J • P : S]`, so a
finitely generated projective module is determined by the numbers `#Hom(P, S)`. This is the form in
which a computation of such counts, for instance through characters, identifies a projective
module.

## Main results

* `Ideal.nonempty_linearEquiv_of_quotient_smul_top`: two projective modules with coatomic
  submodule lattices (e.g. finitely generated ones) and isomorphic quotients by an ideal in the
  Jacobson radical are isomorphic.
* `TauCeti.nonempty_linearEquiv_of_projective_of_natCard_linearMap_eq`: over a ring with finite
  radical quotient, two finitely generated projective modules with equally many maps to every
  simple module are isomorphic.

## References

See T. Y. Lam, *A First Course in Noncommutative Rings*, Section 24, for projective covers over
semiperfect rings and their uniqueness.
-/

public section

open TauCeti

namespace Ideal

universe u v w

variable {R : Type u} [Ring R] (I : Ideal R) (M : Type v) (N : Type w)
  [AddCommGroup M] [Module R M] [IsCoatomic (Submodule R M)] [Module.Projective R M]
  [AddCommGroup N] [Module R N] [IsCoatomic (Submodule R N)] [Module.Projective R N]

/-- **Projectives are determined by a radical quotient.** If `I` lies in the Jacobson radical of
`R`, then an `R`-linear equivalence between `M / IM` and `N / IN` implies that the projective
modules `M` and `N` are `R`-linearly equivalent, provided their submodule lattices are coatomic
(as is the case for finitely generated modules).

Only existence of the resulting equivalence is asserted: both quotient maps are projective covers
of the same reduced module, so uniqueness of projective covers identifies their sources. -/
theorem nonempty_linearEquiv_of_quotient_smul_top (hI : I ≤ Ring.jacobson R)
    (h : Nonempty
      ((M ⧸ (I • (⊤ : Submodule R M))) ≃ₗ[R] (N ⧸ (I • (⊤ : Submodule R N))))) :
    Nonempty (M ≃ₗ[R] N) := by
  let e := h.some
  have hMcover : IsProjectiveCover
      (e.toLinearMap ∘ₗ (I • (⊤ : Submodule R M)).mkQ) :=
    (isProjectiveCover_mkQ_iff_le_jacobson.mpr <|
      (Submodule.smul_mono hI le_rfl).trans (Ring.jacobson_smul_top_le R M)).comp
        e.surjective <| by
      rw [LinearMap.ker_eq_bot.mpr e.injective]
      exact isSuperfluous_bot
  have hNcover : IsProjectiveCover (I • (⊤ : Submodule R N)).mkQ :=
    isProjectiveCover_mkQ_iff_le_jacobson.mpr <|
      (Submodule.smul_mono hI le_rfl).trans (Ring.jacobson_smul_top_le R N)
  exact ⟨(hMcover.exists_linearEquiv hNcover).choose⟩

end Ideal

namespace TauCeti

universe u v w

variable {R : Type u} [Ring R]

/-- **Projectives are determined by their maps to simple modules**, over a ring `R` whose radical
quotient `R ⧸ J` is finite (a finite ring, or the group algebra of a finite group over `ℤ_p`).
Two finitely generated projective `R`-modules `P` and `Q` are isomorphic as soon as, for every
simple module `S`, there are as many `R`-linear maps `P → S` as `Q → S`.

The number of maps `P → S` is `#End_R(S) ^ [P ⧸ J • P : S]`, and `End_R(S)` is a finite ring with
at least two elements, so the hypothesis says that the semisimple radical quotients of `P` and `Q`
have the same composition factors. They are then isomorphic, and projective covers lift the
isomorphism to `P ≃ Q`. -/
theorem nonempty_linearEquiv_of_projective_of_natCard_linearMap_eq
    [Finite (R ⧸ Ring.jacobson R)] (P : Type v) (Q : Type w)
    [AddCommGroup P] [Module R P] [Module.Finite R P] [Module.Projective R P]
    [AddCommGroup Q] [Module R Q] [Module.Finite R Q] [Module.Projective R Q]
    (h : ∀ (S : Type u) [AddCommGroup S] [Module R S] [IsSimpleModule R S],
      Nat.card (P →ₗ[R] S) = Nat.card (Q →ₗ[R] S)) :
    Nonempty (P ≃ₗ[R] Q) := by
  have : IsArtinianRing (R ⧸ Ring.jacobson R) := isArtinian_of_finite
  have : IsSemisimpleRing (R ⧸ Ring.jacobson R) :=
    IsArtinianRing.isSemisimpleRing_iff_jacobson.mpr (Ring.jacobson_quotient_jacobson R)
  have := isSemisimpleModule_quotient_smul_top R (Ring.jacobson R) P
  have := isSemisimpleModule_quotient_smul_top R (Ring.jacobson R) Q
  refine (Ring.jacobson R).nonempty_linearEquiv_of_quotient_smul_top P Q le_rfl
    (IsSemisimpleModule.nonempty_linearEquiv_of_jordanHolderMultiplicity_eq _ _ fun S _ _ _ ↦ ?_)
  -- `#Hom(P, S) = #End(S) ^ [P ⧸ J • P : S]`, where `End(S)` is finite with at least two elements.
  have := IsSimpleModule.finite_of_finite_quotient_jacobson (R := R) S
  have := IsSimpleModule.nontrivial R S
  have : Finite (Module.End R S) := Finite.of_injective _ DFunLike.coe_injective
  refine Nat.pow_right_injective (Finite.one_lt_card (α := Module.End R S)) ?_
  simp only [← natCard_linearMap_eq_pow_jordanHolderMultiplicity,
    Nat.card_congr (linearMapQuotientJacobsonEquiv _ S).toEquiv]
  exact h S

end TauCeti
