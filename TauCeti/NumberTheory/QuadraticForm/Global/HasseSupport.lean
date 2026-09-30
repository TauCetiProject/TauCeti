/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.QuadraticForm.RegularFormClass.Basic
public import TauCeti.NumberTheory.QuadraticForm.Global.FiniteHasse
public import TauCeti.NumberTheory.QuadraticForm.Global.HilbertSymbol
import TauCeti.RingTheory.DedekindDomain.SelmerGroup

/-!
# Finite support of global Hasse signs

For one diagonalization of a regular quadratic form over a number field, the pairwise product of
local Hilbert symbols equals one away from the dyadic places and the primes supporting its
coefficients. In particular that product has finite support. This is the diagonal calculation
that bounds the support of the finite Hasse invariant.

The exceptional set is the union of the dyadic places and the primes supporting the diagonal
coefficients. Every regular global form has a diagonalization with this finite support property.
This packages the good-place Hilbert-symbol calculation proved in `HilbertSymbol` for finite
diagonal forms. Consequently, the Hasse signs of any regular global quadratic form are nontrivial
at only finitely many finite places.

## Main result

* `QuadraticForm.hasFiniteMulSupport_finiteHasse`: the finite-place Hasse signs of a regular
  global form have finite multiplicative support.

The good-place calculation follows O'Meara, *Introduction to Quadratic Forms*, 66:6, using the
unramified norm-equation calculation for each pair of coefficients.
-/

public section

open Finset IsDedekindDomain IsDedekindDomain.HeightOneSpectrum NumberField

namespace TauCeti

variable {K : Type*} [Field K] [NumberField K]

/-- At a finite place where two and every diagonal coefficient are units, every pairwise Hilbert
symbol, and hence their product, equals one. -/
theorem diagonalHasse_eq_one_of_valuation_eq_one {n : ℕ} (a : Fin n → Kˣ)
    (v : HeightOneSpectrum (𝓞 K)) (h2 : v.valuation K 2 = 1)
    (ha : ∀ i, v.valuation K (a i) = 1) :
    ∏ ij ∈ univ.filter (fun ij : Fin n × Fin n => ij.1 < ij.2),
      hilbertSymbol (v.unitAtFinitePlace (a ij.1)) (v.unitAtFinitePlace (a ij.2)) = 1 := by
  apply prod_eq_one
  intro ij hij
  exact hilbertSymbol_unitAtFinitePlace_eq_one h2 (ha ij.1) (ha ij.2)

/-- The pairwise Hasse product of a global diagonal form is one outside the dyadic places and
the primes supporting its coefficients. -/
@[simp] theorem diagonalHasse_eq_one_of_not_mem_exceptional {n : ℕ} (a : Fin n → Kˣ)
    {v : HeightOneSpectrum (𝓞 K)}
    (hv : v ∉ {v | v.valuation K 2 ≠ 1} ∪
      ⋃ i : Fin n, {v | v.valuation K (a i) ≠ 1}) :
    ∏ ij ∈ univ.filter (fun ij : Fin n × Fin n => ij.1 < ij.2),
      hilbertSymbol (v.unitAtFinitePlace (a ij.1)) (v.unitAtFinitePlace (a ij.2)) = 1 := by
  simp only [Set.mem_union, Set.mem_ofPred_eq, Set.mem_iUnion, not_or, not_exists,
    not_not] at hv
  exact diagonalHasse_eq_one_of_valuation_eq_one a v hv.1 hv.2

/-- The explicit exceptional set for a diagonal form is finite. -/
theorem finite_diagonalHasse_exceptional {n : ℕ} (a : Fin n → Kˣ) :
    ({v : HeightOneSpectrum (𝓞 K) | v.valuation K 2 ≠ 1} ∪
      ⋃ i : Fin n, {v | v.valuation K (a i) ≠ 1}).Finite :=
  (HeightOneSpectrum.finite_setOfPred_valuation_ne_one (two_ne_zero' K)).union
    (Set.finite_iUnion fun i =>
      HeightOneSpectrum.finite_setOfPred_valuation_ne_one (a i).ne_zero)

/-- For any global diagonal form, the pairwise local Hasse product differs from one at only
finitely many finite places. -/
theorem finite_setOf_diagonalHasse_ne_one {n : ℕ} (a : Fin n → Kˣ) :
    {v : HeightOneSpectrum (𝓞 K) |
      (∏ ij ∈ univ.filter (fun ij : Fin n × Fin n => ij.1 < ij.2),
        hilbertSymbol (v.unitAtFinitePlace (a ij.1))
          (v.unitAtFinitePlace (a ij.2))) ≠ 1}.Finite := by
  apply (finite_diagonalHasse_exceptional a).subset
  intro v hv
  by_contra hbad
  exact hv (diagonalHasse_eq_one_of_not_mem_exceptional a hbad)

/-- A regular global quadratic form admits one diagonalization whose pairwise local Hasse
products have finite support, with an explicit finite exceptional set of places. The form is
inferred from the nondegeneracy hypothesis. -/
theorem exists_diagonalization_diagonalHasse_finite_support
    {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    {Q : _root_.QuadraticForm K V} (hQ : Q.Nondegenerate) :
    ∃ p : RegularFormPresentation K, Q.Equivalent (presentedForm p) ∧
      ({v : HeightOneSpectrum (𝓞 K) |
        (∏ ij ∈ univ.filter (fun ij : Fin p.1 × Fin p.1 => ij.1 < ij.2),
          hilbertSymbol (v.unitAtFinitePlace (p.2 ij.1))
            (v.unitAtFinitePlace (p.2 ij.2))) ≠ 1}.Finite) := by
  let : Invertible (2 : K) := invertibleOfNonzero two_ne_zero
  obtain ⟨p, hp⟩ := exists_presentedForm_equivalent Q hQ
  exact ⟨p, hp, finite_setOf_diagonalHasse_ne_one p.2⟩

/-- **Almost-all triviality of the finite Hasse sign.** The Hasse sign of a regular quadratic
form over a number field is one at all but finitely many finite places. -/
theorem _root_.QuadraticForm.hasFiniteMulSupport_finiteHasse
    {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (Q : _root_.QuadraticForm K V) (hQ : Q.Nondegenerate) :
    Function.HasFiniteMulSupport (Q.finiteHasse hQ) := by
  obtain ⟨p, hp, hfinite⟩ := exists_diagonalization_diagonalHasse_finite_support hQ
  have hp' : Q.Equivalent
      (QuadraticMap.weightedSumSquares K fun i ↦ (p.2 i : K)) := by
    rwa [← presentedForm_eq_weightedSumSquares_coe]
  rw [Function.HasFiniteMulSupport, Function.mulSupport]
  refine hfinite.subset fun v hv ↦ ?_
  simp only [Set.mem_ofPred_eq] at hv ⊢
  rw [Q.finiteHasse_eq_prod_hilbertSymbol hQ hp' v] at hv
  classical
  have hpairs :
      (∏ i, ∏ j ∈ Ioi i,
          hilbertSymbol (v.unitAtFinitePlace (p.2 i)) (v.unitAtFinitePlace (p.2 j))) =
        ∏ ij ∈ univ.filter (fun ij : Fin p.1 × Fin p.1 ↦ ij.1 < ij.2),
          hilbertSymbol (v.unitAtFinitePlace (p.2 ij.1))
            (v.unitAtFinitePlace (p.2 ij.2)) := by
    calc
      _ = ∏ i, ∏ j, if i < j then
          hilbertSymbol (v.unitAtFinitePlace (p.2 i)) (v.unitAtFinitePlace (p.2 j)) else 1 := by
        apply Finset.prod_congr rfl
        intro i _
        rw [← Finset.filter_lt_eq_Ioi, Finset.prod_filter]
      _ = ∏ ij ∈ univ.product univ, if ij.1 < ij.2 then
          hilbertSymbol (v.unitAtFinitePlace (p.2 ij.1))
            (v.unitAtFinitePlace (p.2 ij.2)) else 1 := by
        simpa using (Finset.prod_product univ univ
          (fun ij : Fin p.1 × Fin p.1 ↦ if ij.1 < ij.2 then
            hilbertSymbol (v.unitAtFinitePlace (p.2 ij.1))
              (v.unitAtFinitePlace (p.2 ij.2)) else 1)).symm
      _ = _ := by
        have huniv : (univ : Finset (Fin p.1 × Fin p.1)) = univ.product univ := by
          ext
          simp
        rw [← huniv]
        rw [Finset.prod_filter]
  rwa [hpairs] at hv

end TauCeti
