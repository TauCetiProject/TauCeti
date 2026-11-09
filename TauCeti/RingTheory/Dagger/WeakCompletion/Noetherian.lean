/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Dagger.WeakCompletion.Polynomial
public import TauCeti.RingTheory.Dagger.WeakCompletion.Surjective
public import TauCeti.RingTheory.Dagger.IntegralWashnitzer.Noetherian

/-!
# Noetherianity of weak completions

A finite family in an algebra over the valuation unit ball `K°` of a complete ultrametric
field defines evaluation of integral overconvergent series into its weak completion.
For a generating family this evaluation is surjective. Consequently the weak completion
of a finitely generated `K°`-algebra is noetherian whenever `K°` is noetherian, in particular
for a complete discretely valued field. Neither flatness nor parameter-adic separatedness
of the original algebra is required.

## References

* M. van der Put, *The cohomology of Monsky and Washnitzer*, §2, (2.1)–(2.2).
-/

public section

namespace TauCeti.Dagger.weakCompletion

variable {K S σ : Type*} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  [CommRing S] [Algebra (Subring.unitClosedBall K) S]
  [Algebra.FiniteType (Subring.unitClosedBall K) S] [Finite σ]

local notation "O" => Subring.unitClosedBall K

/-- Evaluation of integral overconvergent series at a finite family, with values in the weak
completion. Its restriction to polynomials is the usual polynomial evaluation. -/
noncomputable def evalIntWashnitzerAlgebra {π : O} (hπ : π ≠ 0) (hπ1 : ‖(π : K)‖ < 1)
    (x : σ → S) : intWashnitzerAlgebra σ K →ₐ[O] weakCompletion π S :=
  (map π (MvPolynomial.aeval x)).comp (polynomialEquiv hπ hπ1).symm.toAlgHom

/-- Integral overconvergent evaluation fixes the original polynomial evaluation in the
weak completion. -/
@[simp]
theorem evalIntWashnitzerAlgebra_ofMvPolynomial {π : O} (hπ : π ≠ 0)
    (hπ1 : ‖(π : K)‖ < 1) (x : σ → S) (p : MvPolynomial σ O) :
    evalIntWashnitzerAlgebra hπ hπ1 x (intWashnitzerAlgebra.ofMvPolynomial σ K p) =
      of π S (MvPolynomial.aeval x p) := by
  simp [evalIntWashnitzerAlgebra]

/-- A finite polynomial generating family presents the weak completion as a quotient of the
integral Monsky–Washnitzer algebra. -/
theorem evalIntWashnitzerAlgebra_surjective {π : O} (hπ : π ≠ 0)
    (hπ1 : ‖(π : K)‖ < 1) (x : σ → S) (hx : Algebra.adjoin O (Set.range x) = ⊤) :
    Function.Surjective (evalIntWashnitzerAlgebra hπ hπ1 x) :=
  (map_aeval_surjective π x hx).comp (polynomialEquiv hπ hπ1).symm.surjective

/-- Weak completions of finitely generated algebras over a noetherian valuation unit ball
are noetherian. This includes all complete discretely valued coefficient fields. -/
theorem isNoetherianRing [IsNoetherianRing O] {π : O} (hπ : π ≠ 0) (hπ1 : ‖(π : K)‖ < 1) :
    IsNoetherianRing (weakCompletion π S) := by
  obtain ⟨s, hs⟩ := Algebra.FiniteType.out (R := O) (A := S)
  have hx : Algebra.adjoin O (Set.range ((↑) : s → S)) = ⊤ := by
    simpa only [Subtype.range_coe_subtype, Finset.setOfPred_mem] using hs
  exact isNoetherianRing_of_surjective (intWashnitzerAlgebra s K) (weakCompletion π S)
    (evalIntWashnitzerAlgebra hπ hπ1 ((↑) : s → S)).toRingHom
    (evalIntWashnitzerAlgebra_surjective hπ hπ1 _ hx)

/-! The comparison retains coordinates and applies to nonreduced and nonflat algebras. -/

example {π : O} (hπ : π ≠ 0) (hπ1 : ‖(π : K)‖ < 1) :
    (polynomialEquiv hπ hπ1
      (of π (MvPolynomial (Fin 1) O) (MvPolynomial.X 0)) :
        MvPowerSeries (Fin 1) K) = MvPowerSeries.X 0 := by
  simp [intWashnitzerAlgebra.coe_ofMvPolynomial]

example [IsNoetherianRing O] {π : O} (hπ : π ≠ 0) (hπ1 : ‖(π : K)‖ < 1) :
    IsNoetherianRing (weakCompletion π (MvPolynomial (Fin 1) O ⧸
      Ideal.span {(MvPolynomial.X 0 : MvPolynomial (Fin 1) O) ^ 2})) :=
  isNoetherianRing hπ hπ1

example [IsNoetherianRing O] {π : O} (hπ : π ≠ 0) (hπ1 : ‖(π : K)‖ < 1) :
    IsNoetherianRing (weakCompletion π (O ⧸ Ideal.span {π})) :=
  isNoetherianRing hπ hπ1

end TauCeti.Dagger.weakCompletion
