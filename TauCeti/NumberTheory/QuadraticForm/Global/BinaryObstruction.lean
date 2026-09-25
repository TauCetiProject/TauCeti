/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.QuadraticForm.Binary
public import TauCeti.NumberTheory.LocalField.Padic
public import TauCeti.NumberTheory.QuadraticForm.Global.Localization
public import Mathlib.NumberTheory.Padics.HeightOneSpectrum
import Mathlib.NumberTheory.LSeries.PrimesInAP

/-!
# Infinitely many anisotropic places of a binary quadratic form

The binary form `⟨1, 1⟩` over `ℚ` is anisotropic at every finite place above a prime
`p ≡ 3 (mod 4)`, and there are infinitely many such places. It is also anisotropic at
all real places. Thus a binary complement in a four-dimensional quadratic form can have
infinitely many anisotropic places; the finite-exceptional-set argument for dimensions
at least five cannot be applied to it.

The finite-place calculation transfers the nonsquareness of `-1` in `ℚ_[p]` through
Mathlib's isomorphism between `ℚ_[p]` and the canonical finite completion of `ℚ`.

## References

* O. T. O'Meara, *Introduction to Quadratic Forms*, §66, on the separate treatment of
  quaternary forms.
* Dirichlet's theorem on primes in arithmetic progressions, as formalized in Mathlib.
-/

public section
noncomputable section

open IsDedekindDomain NumberField QuadraticMap

namespace TauCeti.NumberField.QuadraticForm

/-- The binary form `⟨1, 1⟩` over `ℚ`, used to exhibit infinitely many anisotropic
finite places of a binary complement. -/
noncomputable def sumTwoSquares : _root_.QuadraticForm ℚ (Fin 2 → ℚ) :=
  weightedSumSquares ℚ ![1, 1]

/-- The value of `⟨1, 1⟩` at `(x, y)` is `x² + y²`. -/
@[simp]
theorem sumTwoSquares_apply (x : Fin 2 → ℚ) :
    sumTwoSquares x = x 0 ^ 2 + x 1 ^ 2 := by
  simp [sumTwoSquares, weightedSumSquares_apply, Fin.sum_univ_two, pow_two]

/-- The form `⟨1, 1⟩` over `ℚ` is anisotropic at a finite place whose rational prime is
congruent to `3` modulo `4`. -/
theorem anisotropic_sumTwoSquares_atFinitePlace
    (v : HeightOneSpectrum (𝓞 ℚ))
    (hv : (Rat.HeightOneSpectrum.primesEquiv v).1 % 4 = 3) :
    (sumTwoSquares.atFinitePlace v).Anisotropic := by
  let p := Rat.HeightOneSpectrum.primesEquiv v
  have hp : Fact p.1.Prime := ⟨p.2⟩
  have hneg : ¬ IsSquare (-1 : v.adicCompletion ℚ) := by
    intro hs
    have hs' : IsSquare (-1 : ℚ_[p.1]) := by
      have h := hs.map (Rat.HeightOneSpectrum.adicCompletion.padicEquiv v).toRingHom
      simpa using h
    exact Padic.not_isSquare_neg_one_of_mod_four_eq_three p.1
      (by simpa [p] using hv) hs'
  have he : (sumTwoSquares.atFinitePlace v).IsometryEquiv
      (weightedSumSquares (v.adicCompletion ℚ) fun i =>
        algebraMap ℚ (v.adicCompletion ℚ) (![(1 : ℚ), 1] i)) := by
    unfold sumTwoSquares
    exact _root_.QuadraticForm.atFinitePlaceWeightedSumSquares v (![(1 : ℚ), 1])
  have hani : (weightedSumSquares (v.adicCompletion ℚ) fun i =>
      algebraMap ℚ (v.adicCompletion ℚ) (![(1 : ℚ), 1] i)).Anisotropic := by
    convert TauCeti.anisotropic_binary_one_one_iff.mpr hneg using 1
    congr 1
    funext i
    fin_cases i <;> simp
  exact (QuadraticMap.Equivalent.anisotropic_iff ⟨he⟩).mpr hani

/-- There are infinitely many finite places of `ℚ` at which `⟨1, 1⟩` is anisotropic. -/
theorem infinite_anisotropic_sumTwoSquares_atFinitePlace :
    Set.Infinite {v : HeightOneSpectrum (𝓞 ℚ) |
      (sumTwoSquares.atFinitePlace v).Anisotropic} := by
  have hNat : Set.Infinite {n : ℕ | n.Prime ∧ n % 4 = 3} := by
    convert Nat.infinite_setOfPred_prime_and_modEq (q := 4) (a := 3)
      (by decide) (by decide) using 1
    ext n
    simp [Nat.ModEq]
  let S := {n : ℕ | n.Prime ∧ n % 4 = 3}
  have hInfS : Infinite S := Set.infinite_coe_iff.mpr hNat
  let f : S → HeightOneSpectrum (𝓞 ℚ) := fun n =>
    (Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)).symm ⟨n.1, n.2.1⟩
  have hinj : Function.Injective f := by
    intro a b h
    have h' := (Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)).symm.injective h
    apply Subtype.ext
    exact congrArg (fun x : Nat.Primes => x.1) h'
  have hmaps : Set.MapsTo f Set.univ
      {v : HeightOneSpectrum (𝓞 ℚ) |
        (sumTwoSquares.atFinitePlace v).Anisotropic} := by
    intro n hn
    apply anisotropic_sumTwoSquares_atFinitePlace
    have heq : Rat.HeightOneSpectrum.primesEquiv (f n) = (⟨n.1, n.2.1⟩ : Nat.Primes) := by
      exact Equiv.apply_symm_apply _ _
    rw [heq]
    exact n.2.2
  exact Set.infinite_of_injOn_mapsTo hinj.injOn hmaps
    (Set.infinite_univ_iff.mpr hInfS)

/-- The form `⟨1, 1⟩` remains anisotropic at every real place of `ℚ`. -/
theorem anisotropic_sumTwoSquares_atRealPlace
    (w : {w : InfinitePlace ℚ // w.IsReal}) :
    let : Algebra ℚ ℝ := (InfinitePlace.embedding_of_isReal w.2).toAlgebra
    (sumTwoSquares.atRealPlace w).Anisotropic := by
  let : Algebra ℚ ℝ := (InfinitePlace.embedding_of_isReal w.2).toAlgebra
  have hneg : ¬ IsSquare (-1 : ℝ) := by
    rintro ⟨z, hz⟩
    have hz0 : 0 ≤ z * z := mul_self_nonneg z
    linarith
  have he : (sumTwoSquares.atRealPlace w).IsometryEquiv
      (weightedSumSquares ℝ fun i =>
        InfinitePlace.embedding_of_isReal w.2 (![(1 : ℚ), 1] i)) := by
    unfold sumTwoSquares
    exact _root_.QuadraticForm.atRealPlaceWeightedSumSquares w (![(1 : ℚ), 1])
  have hcoeff : (fun i : Fin 2 =>
      InfinitePlace.embedding_of_isReal w.2 (![(1 : ℚ), 1] i)) = ![(1 : ℝ), 1] := by
    funext i
    fin_cases i <;> simp
  have hani : (weightedSumSquares ℝ fun i =>
      InfinitePlace.embedding_of_isReal w.2 (![(1 : ℚ), 1] i)).Anisotropic := by
    rw [hcoeff]
    exact TauCeti.anisotropic_binary_one_one_iff.mpr hneg
  exact (QuadraticMap.Equivalent.anisotropic_iff ⟨he⟩).mpr hani

end TauCeti.NumberField.QuadraticForm
