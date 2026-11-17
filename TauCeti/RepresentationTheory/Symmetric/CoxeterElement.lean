/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.RootsOfUnity.Complex
public import TauCeti.GroupTheory.Perm.Coxeter
public import TauCeti.LinearAlgebra.Charpoly.Permutation
public import TauCeti.RepresentationTheory.SymmetricAlgebra.Standard

/-!
# Eigenvalues of the Coxeter elements of the symmetric group

A Coxeter element of `S_n`, viewed as the Coxeter group of type `A_{n-1}` through
`TauCeti.permCoxeterSystem n`, is a product of all the adjacent transpositions, each taken once
in any order. It is an `n`-cycle (`TauCeti.cycleType_wordProd_permCoxeterSystem`), so its order,
the Coxeter number of type `A_{n-1}`, is `h = n`. This file computes its eigenvalues.

* On the permutation representation `K[Fin n]`, over any commutative ring, its characteristic
  polynomial is `X ^ n - 1`, read off the cycle type.
* On the reflection representation of `S_n`, the standard representation on the trace-zero
  hyperplane `V₀ ⊆ K[Fin n]`, over any field, its characteristic polynomial is
  `1 + X + ⋯ + X ^ (n - 1)`: `V₀` is a subrepresentation of `K[Fin n]` with trivial
  one-dimensional quotient, which removes the factor `X - 1`
  (`TauCeti.charpoly_augmentationSubrepresentation_mul_X_sub_one`). No hypothesis on the
  characteristic is needed.
* Its eigenvalues on `V₀`, with multiplicity, are therefore the `ζ ^ e` for a primitive `n`-th
  root of unity `ζ` and the exponents `e = 1, …, n - 1`, each once; over `ℂ` these are the
  `exp (2πi e / n)`.
* The basic invariants of `V₀` have degrees `2, …, n`
  (`TauCeti.map_univ_eq_of_bijective_aeval_standardRepresentation_dual`), so these exponents are
  the degrees lowered by one: for every system of basic invariants with degrees `dᵢ`, the
  eigenvalues are the `exp (2πi (dᵢ - 1) / h)`. This is the type `A` case of the relation between
  invariant degrees and Coxeter eigenvalues for a Weyl group.

The value of `1 + X + ⋯ + X ^ (n - 1)` at `1` is `n`. So, for `n ≥ 2`, `1` is an eigenvalue on `V₀`
exactly when the characteristic of `K` divides `n`; then the constant vectors have coefficient sum
`n = 0` and form a fixed line inside `V₀`. Over `ℂ` it is not an eigenvalue.

## Main results

* `TauCeti.charpoly_ofMulAction_wordProd_permCoxeterSystem`: on the permutation representation,
  the characteristic polynomial of a Coxeter element is `X ^ n - 1`.
* `TauCeti.charpoly_standardRepresentation_wordProd_permCoxeterSystem`: on the reflection
  representation it is `∑ i < n, X ^ i`.
* `TauCeti.roots_charpoly_standardRepresentation_wordProd_permCoxeterSystem_of_isPrimitiveRoot`:
  its eigenvalues on the reflection representation are the `ζ ^ e`, `e = 1, …, n - 1`, for a
  primitive `n`-th root of unity `ζ`.
* `TauCeti.roots_charpoly_standardRepresentation_wordProd_permCoxeterSystem`: over `ℂ`, they are
  the `exp (2πi e / n)`, `e = 1, …, n - 1`.
* `TauCeti.roots_charpoly_standardRepresentation_wordProd_permCoxeterSystem_eq_map_degrees`: these
  are the `exp (2πi (dᵢ - 1) / n)` over the degrees `dᵢ` of any system of basic invariants.

## References

* J. E. Humphreys, *Reflection Groups and Coxeter Groups*, Cambridge University Press (1990),
  §§ 3.16–3.19.
* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4--6*, Ch. V, §6, and Plate I.
-/

public section

open Polynomial

namespace TauCeti

variable {n : ℕ} {ω : List (Fin (n - 1))}

/-- **A Coxeter element of `S_n` on the permutation representation.** A product of all the
adjacent transpositions, each taken once in any order, acts on `R[Fin n]` with characteristic
polynomial `X ^ n - 1`. -/
theorem charpoly_ofMulAction_wordProd_permCoxeterSystem (R : Type*) [CommRing R]
    (hω : ω.Perm (List.finRange (n - 1))) (hn : n ≠ 0) :
    (Representation.ofMulAction R (Equiv.Perm (Fin n)) (Fin n)
      ((permCoxeterSystem n).wordProd ω)).charpoly = X ^ n - 1 := by
  have hperm : (MulAction.toPerm ((permCoxeterSystem n).wordProd ω) : Equiv.Perm (Fin n)) =
      (permCoxeterSystem n).wordProd ω :=
    Equiv.ext fun _ ↦ rfl
  rw [Representation.charpoly_ofMulAction, hperm,
    Equiv.Perm.fullCycleType_of_forall_sameCycle _
      (sameCycle_wordProd_permCoxeterSystem hω ⟨0, Nat.pos_of_ne_zero hn⟩),
    Multiset.map_singleton, Multiset.prod_singleton, Fintype.card_fin]

/-- **A Coxeter element of `S_n` on the reflection representation.** A product of all the
adjacent transpositions, each taken once in any order, acts on the trace-zero hyperplane of
`K[Fin n]` with characteristic polynomial `1 + X + ⋯ + X ^ (n - 1)`, in every characteristic. -/
theorem charpoly_standardRepresentation_wordProd_permCoxeterSystem (K : Type*) [Field K]
    (hω : ω.Perm (List.finRange (n - 1))) (hn : n ≠ 0) :
    (standardRepresentation K (Fin n) ((permCoxeterSystem n).wordProd ω)).charpoly =
      ∑ i ∈ Finset.range n, X ^ i := by
  have : NeZero n := ⟨hn⟩
  refine mul_right_cancel₀ (b := X - 1) (by simpa using X_sub_C_ne_zero (1 : K)) ?_
  rw [← toRepresentation_augmentationSubrepresentation,
    charpoly_augmentationSubrepresentation_mul_X_sub_one,
    charpoly_ofMulAction_wordProd_permCoxeterSystem K hω hn, geom_sum_mul]

/-- The reflection representation of `S_0` is zero, so its characteristic polynomials have no
roots. -/
private theorem roots_charpoly_standardRepresentation_fin_zero {K : Type*} [Field K]
    (g : Equiv.Perm (Fin 0)) : (standardRepresentation K (Fin 0) g).charpoly.roots = 0 := by
  rw [eq_one_of_monic_natDegree_zero (LinearMap.charpoly_monic _)
    (by rw [LinearMap.charpoly_natDegree]; simp), roots_one, Multiset.empty_eq_zero]

/-- **The eigenvalues of a Coxeter element of `S_n` on its reflection representation.** Over a
field containing a primitive `n`-th root of unity `ζ`, they are the `ζ ^ e` for the exponents
`e = 1, …, n - 1`, each with multiplicity one. For `n = 0` the reflection representation is zero
and there are no eigenvalues. -/
theorem roots_charpoly_standardRepresentation_wordProd_permCoxeterSystem_of_isPrimitiveRoot
    {K : Type*} [Field K] {ζ : K} (hζ : IsPrimitiveRoot ζ n)
    (hω : ω.Perm (List.finRange (n - 1))) :
    (standardRepresentation K (Fin n) ((permCoxeterSystem n).wordProd ω)).charpoly.roots =
      (Multiset.range (n - 1)).map fun e ↦ ζ ^ (e + 1) := by
  obtain rfl | hn := eq_or_ne n 0
  · simp [roots_charpoly_standardRepresentation_fin_zero]
  set p := (standardRepresentation K (Fin n) ((permCoxeterSystem n).wordProd ω)).charpoly
  have : NeZero n := ⟨hn⟩
  -- The roots of `p * (X - 1) = X ^ n - 1` are the `n`-th roots of unity `ζ ^ k`, `k < n`, and the
  -- root `1 = ζ ^ 0` comes from the factor `X - 1`.
  have hp : p * (X - C 1) = X ^ n - C 1 := by
    rw [C_1, ← charpoly_ofMulAction_wordProd_permCoxeterSystem K hω hn,
      ← charpoly_augmentationSubrepresentation_mul_X_sub_one,
      toRepresentation_augmentationSubrepresentation]
  have hroots : p.roots + {1} = (Multiset.range n).map fun k ↦ ζ ^ k * 1 := by
    rw [← roots_X_sub_C, ← roots_mul (hp ▸ X_pow_sub_C_ne_zero (Nat.pos_of_ne_zero hn) 1), hp,
      ← nthRoots, hζ.nthRoots_eq (one_pow n)]
  -- Split off the exponent `0` of the root `1`: `range n = {0} + (range (n - 1)).map (1 + ·)`.
  obtain ⟨m, rfl⟩ : ∃ m, n = 1 + m := ⟨n - 1, by omega⟩
  rw [Multiset.range_add, show Multiset.range 1 = {0} from rfl, Multiset.map_add,
    Multiset.map_singleton, pow_zero, one_mul, Multiset.map_map, add_comm] at hroots
  rw [add_left_cancel hroots, Nat.add_sub_cancel_left]
  exact Multiset.map_congr rfl fun e _ ↦ by simp [add_comm]

/-- **The eigenvalues of a Coxeter element of `S_n` on its complex reflection representation** are
the `exp (2πi e / n)` for the exponents `e = 1, …, n - 1`, each with multiplicity one. -/
theorem roots_charpoly_standardRepresentation_wordProd_permCoxeterSystem
    (hω : ω.Perm (List.finRange (n - 1))) :
    (standardRepresentation ℂ (Fin n) ((permCoxeterSystem n).wordProd ω)).charpoly.roots =
      (Multiset.range (n - 1)).map
        fun e : ℕ ↦ Complex.exp (2 * Real.pi * Complex.I * (e + 1 : ℕ) / n) := by
  obtain rfl | hn := eq_or_ne n 0
  · simp [roots_charpoly_standardRepresentation_fin_zero]
  rw [roots_charpoly_standardRepresentation_wordProd_permCoxeterSystem_of_isPrimitiveRoot
    (Complex.isPrimitiveRoot_exp n hn) hω]
  refine Multiset.map_congr rfl fun e _ ↦ ?_
  rw [← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

/-- **The eigenvalues of a Coxeter element of `S_n` from the invariant degrees.** Let `dᵢ` be the
degrees of any system of basic invariants of the reflection representation `V₀` of `S_n` over
`ℂ`, that is, of homogeneous invariant polynomial functions on `V₀` on which the invariant algebra
is a polynomial algebra. Then the eigenvalues of every Coxeter element on `V₀`, with multiplicity,
are the `exp (2πi (dᵢ - 1) / h)`, where `h = n` is the Coxeter number, the order of a Coxeter
element (`TauCeti.orderOf_wordProd_permCoxeterSystem`). The exponents of type `A_{n-1}` are the
degrees lowered by one. -/
theorem roots_charpoly_standardRepresentation_wordProd_permCoxeterSystem_eq_map_degrees
    (hω : ω.Perm (List.finRange (n - 1))) (hn : n ≠ 0) {ι : Type*} [Fintype ι]
    {f : ι → (standardRepresentation ℂ (Fin n)).dual.symmetricAlgebraInvariants} {d : ι → ℕ}
    (hf : ∀ i, (f i : SymmetricAlgebra ℂ (Module.Dual ℂ
        (augmentationSubrepresentation ℂ (Equiv.Perm (Fin n)) (Fin n)).toSubmodule)) ∈
      SymmetricAlgebra.homogeneousSubmodule ℂ _ (d i))
    (hbij : Function.Bijective (MvPolynomial.aeval (R := ℂ) f)) :
    (standardRepresentation ℂ (Fin n) ((permCoxeterSystem n).wordProd ω)).charpoly.roots =
      (Finset.univ.val.map d).map
        fun d : ℕ ↦ Complex.exp (2 * Real.pi * Complex.I * (d - 1 : ℕ) / n) := by
  rw [map_univ_eq_of_bijective_aeval_standardRepresentation_dual ℂ (n := n - 1)
      (by simpa using hn) (by rw [Fintype.card_fin]; omega) hf hbij,
    Multiset.map_map, roots_charpoly_standardRepresentation_wordProd_permCoxeterSystem hω]
  refine Multiset.map_congr rfl fun e _ ↦ ?_
  simp

end TauCeti
