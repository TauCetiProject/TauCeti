/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.IntegralLattice.Gram
public import TauCeti.LinearAlgebra.IntegralLattice.PosDef.Finite
import TauCeti.LinearAlgebra.BilinearForm.FiniteClasses

/-!
# Finitely many classes of positive definite lattices

There are only finitely many isometry classes of positive definite integral lattices of a given
rank and bounded determinant. This is the positive definite case of the finiteness of the class
number; definiteness is essential to the proof, which is Hermite's reduction
(`LinearMap.BilinForm.exists_finset_forall_exists_toMatrix_mem`).

The statement takes two forms. First, a single finite set of integral matrices contains a Gram
matrix of every such lattice, whatever its ambient rational space. Second, since lattices with
bases of equal Gram matrices are isometric (`TauCeti.IntegralLattice.Isometry.ofGramMatrixEq`), a
family of pairwise non-isometric such lattices is finite.

## Main results

* `TauCeti.IntegralLattice.exists_finset_forall_exists_gramMatrix_mem`: a finite set of matrices
  containing a Gram matrix of every positive definite lattice of rank `n` and determinant at
  most `D`.
* `TauCeti.IntegralLattice.finite_of_pairwise_isEmpty_isometry`: a family of pairwise non-isometric
  positive definite lattices of rank `n` and determinant at most `D` is finite.

## References

* C. Hermite, *Extraits de lettres de M. Ch. Hermite à M. Jacobi sur différents objets de la
  théorie des nombres*, J. Reine Angew. Math. 40 (1850), 261–315.
* J. W. S. Cassels, *Rational Quadratic Forms*, Chapter 9, §1.
-/

public section

open Module

namespace TauCeti.IntegralLattice

universe u

/-- **Finitely many Gram matrices represent all positive definite lattices of given rank and
bounded determinant.** For every rank `n` and bound `D` there is a finite set `S` of integral
matrices such that every positive definite integral lattice of rank `n` and determinant at most
`D`, in any rational space, has a Gram matrix in `S`. -/
theorem exists_finset_forall_exists_gramMatrix_mem (n : ℕ) (D : ℤ) :
    ∃ S : Finset (Matrix (Fin n) (Fin n) ℤ), ∀ {V : Type u} [AddCommGroup V] [Module ℚ V]
      (L : IntegralLattice V), L.IsPosDef → finrank ℤ L = n → L.determinant ≤ D →
        ∃ b : Basis (Fin n) ℤ L, L.gramMatrix b ∈ S := by
  obtain ⟨S, hS⟩ := LinearMap.BilinForm.exists_finset_forall_exists_toMatrix_mem.{u} n D
  refine ⟨S, fun {V} _ _ L hL hn hD ↦ ?_⟩
  let b := Module.finBasisOfFinrankEq ℤ L hn
  rw [L.determinant_eq_gramDet b, gramDet_def, gramMatrix_eq_toMatrix] at hD
  obtain ⟨c, hc⟩ := hS L.integralForm L.isSymm_integralForm
    (fun x hx ↦ by simpa [integralNorm_apply] using hL.posDef_integralNorm x hx) b hD
  exact ⟨c, by rwa [gramMatrix_eq_toMatrix]⟩

/-- **There are finitely many classes of positive definite lattices of given rank and bounded
determinant.** A family of pairwise non-isometric positive definite integral lattices of rank `n`
and determinant at most `D` is finite. -/
theorem finite_of_pairwise_isEmpty_isometry {ι : Type*} {V : ι → Type u}
    [∀ i, AddCommGroup (V i)] [∀ i, Module ℚ (V i)] (L : ∀ i, IntegralLattice (V i)) {n : ℕ}
    {D : ℤ} (hpos : ∀ i, (L i).IsPosDef) (hrank : ∀ i, finrank ℤ (L i) = n)
    (hdet : ∀ i, (L i).determinant ≤ D)
    (hL : Pairwise fun i j ↦ IsEmpty (Isometry (L i) (L j))) : Finite ι := by
  obtain ⟨S, hS⟩ := exists_finset_forall_exists_gramMatrix_mem.{u} n D
  choose b hb using fun i ↦ hS (L i) (hpos i) (hrank i) (hdet i)
  refine Finite.of_injective (fun i ↦ (⟨(L i).gramMatrix (b i), hb i⟩ : S)) fun i j hij ↦ ?_
  by_contra hne
  exact (hL hne).false (Isometry.ofGramMatrixEq (b i) (b j) (congrArg Subtype.val hij))

end TauCeti.IntegralLattice
