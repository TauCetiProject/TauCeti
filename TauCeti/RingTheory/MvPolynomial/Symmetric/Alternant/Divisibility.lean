/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.MvPolynomial.Symmetric.Alternant
import Mathlib.GroupTheory.GroupAction.MultipleTransitivity
import TauCeti.RingTheory.MvPolynomial.Symmetric.Discriminant

/-!
# Divisibility by the Vandermonde alternant

Over any integral domain `R`, the linear factors `X j - X i` (`i < j`) of the Vandermonde
alternant `TauCeti.alternant (Fin m) R (fun j => (j : ℕ))` are pairwise non-associated primes in
`MvPolynomial (Fin m) R`. Consequently:

* If a polynomial `p` whose variable permutations remain associated to `p` (in particular, any
  symmetric or antisymmetric polynomial) is divisible by one root difference `X i₀ - X j₀`
  (`i₀ ≠ j₀`), then it is divisible by the entire Vandermonde alternant
  (`TauCeti.alternant_fin_val_dvd_of_associated_rename`,
  `TauCeti.alternant_fin_val_dvd_of_isSymmetric`), with no unique factorization assumption on `R`.

## Main results

* `TauCeti.alternant_fin_val_dvd_of_associated_rename`,
  `TauCeti.alternant_fin_val_dvd_of_isSymmetric`: divisibility by the Vandermonde alternant from
  a single root-difference divisor.
-/

public section

namespace TauCeti

open MvPolynomial Equiv Finset

variable {R : Type*} [CommRing R]

/-- Over an integral domain `R`, if `p : MvPolynomial (Fin m) R` satisfies
`Associated (rename e p) p` for every permutation `e` (in particular, if `p` is symmetric or
antisymmetric) and is divisible by one root difference `X i₀ - X j₀` (`i₀ ≠ j₀`), then it is
divisible by the Vandermonde alternant `alternant (Fin m) R (fun j => (j : ℕ))`. -/
theorem alternant_fin_val_dvd_of_associated_rename [IsDomain R] {m : ℕ}
    {p : MvPolynomial (Fin m) R} (hp : ∀ e : Equiv.Perm (Fin m), Associated (rename e p) p)
    {i₀ j₀ : Fin m} (h₀ : i₀ ≠ j₀) (hdvd₀ : X i₀ - X j₀ ∣ p) :
    alternant (Fin m) R (fun j => (j : ℕ)) ∣ p := by
  rw [alternant_fin_val_eq_vandermonde]
  refine vandermonde_dvd_of_forall_dvd fun i j hij => ?_
  obtain ⟨e, he1, he2⟩ := MulAction.is_two_pretransitive_iff.mp
    (Equiv.Perm.isMultiplyPretransitive (Fin m) 2) h₀ hij.ne'
  simp only [Equiv.Perm.smul_def] at he1 he2
  have hmap : X j - X i ∣ rename (R := R) e p := by
    have hd := _root_.map_dvd (rename (R := R) e) hdvd₀
    simpa [he1, he2] using hd
  exact hmap.trans (hp e).dvd

/-- Over an integral domain `R`, if a symmetric polynomial in `Fin m` is divisible by one root
difference `X i₀ - X j₀` (`i₀ ≠ j₀`), then it is divisible by the Vandermonde alternant
`alternant (Fin m) R (fun j => (j : ℕ))`. -/
theorem alternant_fin_val_dvd_of_isSymmetric [IsDomain R] {m : ℕ}
    {p : MvPolynomial (Fin m) R} (hp : p.IsSymmetric) {i₀ j₀ : Fin m}
    (h₀ : i₀ ≠ j₀) (hdvd₀ : X i₀ - X j₀ ∣ p) :
    alternant (Fin m) R (fun j => (j : ℕ)) ∣ p :=
  alternant_fin_val_dvd_of_associated_rename (fun e => by rw [hp e]) h₀ hdvd₀

end TauCeti
