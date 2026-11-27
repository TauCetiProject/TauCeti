/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.Data.Finset.NoncommProd
import Mathlib.LinearAlgebra.Eigenspace.Minpoly
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.RingTheory.Adjoin.Polynomial.Basic
import TauCeti.LinearAlgebra.End.Aeval

/-!
# Relative-degree selectors for abelian powers

Multiplication by `N ≥ 2` on an abelian scheme of relative dimension `g` acts in relative degree
`j` by `N ^ j`. The Lagrange basis polynomial for the node `N`, with the degrees from
`0` through `2 * g`, selects relative degree one. For several factors, the product of these
polynomial operators selects the part of relative degree one in every factor.

The action formula here applies to any simultaneous eigenvector of the factor endomorphisms.
When these eigenvectors span, their selector is idempotent. The polynomial formula also
defines the selector before passing to graded pieces, where the endomorphisms need not be
semisimple.

## References

* R. Taylor and T. Yoshida, *Compatibility of local and global Langlands correspondences*,
  arXiv:math/0412357v2, §2.
-/

public section

namespace TauCeti.KugaSato

open Polynomial
open scoped Function

variable (K : Type*) [Field K]

/-- The Lagrange basis polynomial at `N` for the nodes `N ^ j` in degrees `0 ≤ j ≤ 2 * g`.
We include the degree-one node also when `g = 0`, so the formula still kills degree zero. -/
noncomputable def relativeDegreeOnePolynomial (g N : ℕ) : K[X] :=
  Lagrange.basis (insert 1 (Finset.range (2 * g + 1))) (fun j ↦ (N : K) ^ j) 1

/-- The product formula for the relative-degree-one polynomial. -/
theorem relativeDegreeOnePolynomial_def (g N : ℕ) :
    relativeDegreeOnePolynomial K g N =
      ∏ j ∈ (Finset.range (2 * g + 1)).erase 1,
        C ((N : K) - (N : K) ^ j)⁻¹ * (X - C ((N : K) ^ j)) := by
  simp [relativeDegreeOnePolynomial, Lagrange.basis, Lagrange.basisDivisor]

/-- In an admissible relative degree, the selector evaluates to the indicator of degree one. -/
@[simp]
theorem eval_relativeDegreeOnePolynomial [CharZero K] {g N j : ℕ} (hN : 2 ≤ N)
    (hj : j ≤ 2 * g) :
    (relativeDegreeOnePolynomial K g N).eval ((N : K) ^ j) = if j = 1 then 1 else 0 := by
  by_cases h : j = 1
  · subst j
    rw [ite_eq_left rfl, relativeDegreeOnePolynomial]
    apply Lagrange.eval_basis_self _ (Finset.mem_insert_self _ _)
    intro i _ l _ hil
    have hpow : N ^ i = N ^ l :=
      Nat.cast_injective (R := K) (by simpa only [Nat.cast_pow] using hil)
    exact pow_right_injective₀ (by omega : 0 < N) (by omega : N ≠ 1) hpow
  · rw [ite_eq_right h, relativeDegreeOnePolynomial]
    exact Lagrange.eval_basis_of_ne (Ne.symm h) (Finset.mem_insert_of_mem (Finset.mem_range.mpr
      (Nat.lt_succ_of_le hj)))

variable {K} {V ι : Type*} [AddCommGroup V] [Module K V]

/-- Evaluating the degree-one polynomial on pairwise commuting endomorphisms gives pairwise
commuting factors. -/
theorem pairwise_commute_relativeDegreeOne (g N : ℕ) {T : ι → Module.End K V}
    (hT : Pairwise (Commute on T)) :
    Pairwise (Commute on (fun i ↦ aeval (T i) (relativeDegreeOnePolynomial K g N))) := by
  intro i j hij
  have h := Algebra.commute_of_mem_adjoin_singleton_of_commute
    (aeval_mem_adjoin_singleton K (T i) (p := relativeDegreeOnePolynomial K g N)) (hT hij).symm
  exact Algebra.commute_of_mem_adjoin_singleton_of_commute
    (aeval_mem_adjoin_singleton K (T j) (p := relativeDegreeOnePolynomial K g N)) h.symm

/-- The product of the degree-one selectors in the endomorphism for each abelian factor. -/
noncomputable def relativeDegreeSelector [Fintype ι] (g N : ℕ) (T : ι → Module.End K V)
    (hT : Pairwise (Commute on T)) : Module.End K V :=
  Finset.univ.noncommProd (fun i ↦ aeval (T i) (relativeDegreeOnePolynomial K g N))
    ((pairwise_commute_relativeDegreeOne g N hT).set_pairwise _)

/-- The relative-degree selector is the finite product of the degree-one polynomial evaluations. -/
theorem relativeDegreeSelector_def [Fintype ι] (g N : ℕ) (T : ι → Module.End K V)
    (hT : Pairwise (Commute on T)) :
    relativeDegreeSelector g N T hT =
      Finset.univ.noncommProd (fun i ↦ aeval (T i) (relativeDegreeOnePolynomial K g N))
        ((pairwise_commute_relativeDegreeOne g N hT).set_pairwise _) := (rfl)

/-- The selector fixes a simultaneous eigenvector in relative degree one in every factor and
kills it if any of its relative degrees differs from one. -/
theorem relativeDegreeSelector_apply_of_eigenvalues [CharZero K] [Fintype ι] {g N : ℕ}
    (hN : 2 ≤ N) (T : ι → Module.End K V) (hT : Pairwise (Commute on T)) (j : ι → ℕ)
    (hj : ∀ i, j i ≤ 2 * g) {v : V} (hv : ∀ i, T i v = (N : K) ^ j i • v) :
    relativeDegreeSelector g N T hT v = if ∀ i, j i = 1 then v else 0 := by
  classical
  have hfactor (i : ι) : aeval (T i) (relativeDegreeOnePolynomial K g N) v =
      (if j i = 1 then (1 : K) else 0) • v := by
    rw [Module.End.aeval_apply_of_mem_apply_eq_smul (hx := hv i),
      eval_relativeDegreeOnePolynomial K hN (hj i)]
  unfold relativeDegreeSelector
  by_cases hall : ∀ i, j i = 1
  · rw [ite_eq_left hall]
    refine Finset.noncommProd_induction _ _ _ (fun f : Module.End K V ↦ f v = v) ?_ rfl fun i _ ↦ ?_
    · intro A B hA hB
      rw [_root_.mul_apply_eq_comp, hB, hA]
    · simpa [hall i] using hfactor i
  · rw [ite_eq_right hall]
    push Not at hall
    obtain ⟨i, hi⟩ := hall
    have hprod := Finset.noncommProd_erase_mul Finset.univ (Finset.mem_univ i)
      (fun k ↦ aeval (T k) (relativeDegreeOnePolynomial K g N))
      ((pairwise_commute_relativeDegreeOne g N hT).set_pairwise _)
    exact (congrArg (fun A : Module.End K V ↦ A v) hprod.symm).trans (by
      simp only [_root_.mul_apply_eq_comp, hfactor, ite_eq_right hi, zero_smul, map_zero])

/-- In the empty abelian power, there are no relative degrees to select. -/
@[simp]
theorem relativeDegreeSelector_of_isEmpty [Fintype ι] [IsEmpty ι] (g N : ℕ)
    (T : ι → Module.End K V) (hT : Pairwise (Commute on T)) :
    relativeDegreeSelector g N T hT = 1 := by
  unfold relativeDegreeSelector
  have h : (Finset.univ : Finset ι) = ∅ := by simp
  exact (Finset.noncommProd_congr h (fun _ _ ↦ rfl) _).trans (Finset.noncommProd_empty _ _)

/-- A linear map intertwining all multiplication endomorphisms also intertwines the relative
selectors, in particular after passing to a stable subquotient. -/
theorem relativeDegreeSelector_comp_eq [Fintype ι] {W : Type*} [AddCommGroup W] [Module K W]
    (g N : ℕ) {T : ι → Module.End K V} {T' : ι → Module.End K W} {f : V →ₗ[K] W}
    (hT : Pairwise (Commute on T)) (hT' : Pairwise (Commute on T'))
    (hf : ∀ i, (T' i).comp f = f.comp (T i)) :
    (relativeDegreeSelector g N T' hT').comp f =
      f.comp (relativeDegreeSelector g N T hT) := by
  classical
  let A (i : ι) := aeval (T i) (relativeDegreeOnePolynomial K g N)
  let A' (i : ι) := aeval (T' i) (relativeDegreeOnePolynomial K g N)
  have hA : Pairwise (Commute on A) := pairwise_commute_relativeDegreeOne g N hT
  have hA' : Pairwise (Commute on A') := pairwise_commute_relativeDegreeOne g N hT'
  have hfactor (i : ι) : (A' i).comp f = f.comp (A i) :=
    Module.End.aeval_comp_of_comp_eq (hf i) _
  have hprod (s : Finset ι) :
      (s.noncommProd A' (hA'.set_pairwise _)).comp f =
        f.comp (s.noncommProd A (hA.set_pairwise _)) := by
    induction s using Finset.induction_on with
    | empty => simp only [Finset.noncommProd_empty, Module.End.one_eq_id,
        LinearMap.id_comp, LinearMap.comp_id]
    | insert i s hi ih =>
      simp only [Finset.noncommProd_insert_of_notMem _ _ _ _ hi, Module.End.mul_eq_comp]
      rw [LinearMap.comp_assoc, ih, ← LinearMap.comp_assoc, hfactor, LinearMap.comp_assoc]
  exact hprod Finset.univ

/-- The relative selector is idempotent on a module spanned by simultaneous eigenvectors with
the indicated relative degrees. -/
theorem isIdempotentElem_relativeDegreeSelector [CharZero K] [Fintype ι] {g N : ℕ}
    (hN : 2 ≤ N) (T : ι → Module.End K V) (hT : Pairwise (Commute on T))
    {κ : Type*} (v : κ → V) (j : κ → ι → ℕ) (hj : ∀ a i, j a i ≤ 2 * g)
    (hv : ∀ a i, T i (v a) = (N : K) ^ j a i • v a)
    (hspan : Submodule.span K (Set.range v) = ⊤) :
    IsIdempotentElem (relativeDegreeSelector g N T hT) := by
  classical
  rw [IsIdempotentElem]
  apply LinearMap.ext_on_range hspan
  intro a
  have ha := relativeDegreeSelector_apply_of_eigenvalues hN T hT (j a) (hj a) (hv a)
  rw [_root_.mul_apply_eq_comp, ha]
  split_ifs with h
  · simpa [h] using ha
  · exact map_zero _

end TauCeti.KugaSato
