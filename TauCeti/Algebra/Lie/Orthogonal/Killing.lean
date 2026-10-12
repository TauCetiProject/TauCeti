/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Lie.CartanCriterion
public import Mathlib.Algebra.Lie.Classical
public import Mathlib.Algebra.Lie.Matrix
public import Mathlib.Algebra.Lie.Semisimple.Lemmas
public import TauCeti.LinearAlgebra.Matrix.Alternating

/-!
# The Killing form of the orthogonal Lie algebra

The standard module `l → K` of the orthogonal Lie algebra `LieAlgebra.Orthogonal.so l K` of the
standard symmetric form is irreducible over every field, as soon as `l` has at least three
elements. Together with faithfulness and vanishing traces, Mathlib's reductivity criterion for
faithful irreducible modules then shows that `so l K` has trivial radical in characteristic zero,
provided each element acts triangularizably on the standard module (for instance over an
algebraically closed field). Cartan's criterion turns this into nondegeneracy of the Killing form.

The irreducibility argument uses the elements `v ↦ ⟪a, v⟫ b - ⟪b, v⟫ a` of `so l K`, where
`⟪x, y⟫ = x ⬝ᵥ y`. For standard basis vectors `eᵢ` they move a vector `v` with `vᵢ ≠ 0` first to
`vᵢ eⱼ - vⱼ eᵢ` and then, for a third index `m`, to `vᵢ eₘ`. So a Lie submodule containing `v`
contains `eₘ` for every `m ≠ i`, and applying the same step to `eₘ` gives `eᵢ`. With fewer than
three indices this fails: `so l K` is then abelian.

## Main results

* `TauCeti.isIrreducible_so_standard`: the standard module of `so l K` is irreducible when `l`
  has at least three elements.
* `TauCeti.hasTrivialRadical_so`: `so l K` has trivial radical in characteristic zero, given
  triangularizability of its standard module; in particular its Killing form is nondegenerate.

## References

* W. Fulton and J. Harris, *Representation Theory*, Lecture 18 (the orthogonal Lie algebras).
* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, §§1.2, 5 and 19.
-/

public section

namespace TauCeti

open Matrix LieAlgebra LieModule

attribute [local instance 100] LieRing.ofAssociativeRing

variable {l : Type*} [DecidableEq l] [Fintype l]

section CommRing

variable {R : Type*} [CommRing R]

/-- The skew-symmetric matrix `v ↦ ⟪a, v⟫ b - ⟪b, v⟫ a` attached to two vectors, where `⟪·, ·⟫`
is the standard symmetric form. -/
private def wedgeMatrix (a b : l → R) : Matrix l l R :=
  vecMulVec b a - vecMulVec a b

private theorem wedgeMatrix_mem_so (a b : l → R) :
    wedgeMatrix a b ∈ Orthogonal.so l R := by
  rw [Orthogonal.mem_so, wedgeMatrix, transpose_sub, transpose_vecMulVec, transpose_vecMulVec,
    neg_sub]

omit [DecidableEq l] in
private theorem wedgeMatrix_mulVec (a b v : l → R) :
    wedgeMatrix a b *ᵥ v = (a ⬝ᵥ v) • b - (b ⬝ᵥ v) • a := by
  simp [wedgeMatrix, sub_mulVec, vecMulVec_mulVec]

end CommRing

section Field

variable {K : Type*} [Field K]

/-- A Lie submodule of the standard module of `so l K` that contains a vector with nonzero
`i`-th coordinate contains every standard basis vector `eₘ` with `m ≠ i`, provided some index
differs from both `i` and `m`. -/
private theorem single_mem_of_apply_ne_zero (N : LieSubmodule K (Orthogonal.so l K) (l → K))
    {v : l → K} (hv : v ∈ N) {i m j : l} (hi : v i ≠ 0) (hji : j ≠ i) (hjm : j ≠ m)
    (hmi : m ≠ i) : Pi.single m 1 ∈ N := by
  have hmem (A : Matrix l l K) (hA : A ∈ Orthogonal.so l K) {u : l → K} (hu : u ∈ N) :
      A *ᵥ u ∈ N := by
    have h := N.lie_mem (x := ⟨A, hA⟩) hu
    rwa [LieSubalgebra.coe_bracket_of_module, Matrix.lie_apply] at h
  have h := hmem _ (wedgeMatrix_mem_so (Pi.single j 1) (Pi.single m 1))
    (hmem _ (wedgeMatrix_mem_so (Pi.single i 1) (Pi.single j 1)) hv)
  simp only [wedgeMatrix_mulVec, mulVec_sub, mulVec_smul, single_dotProduct, one_mul,
    Pi.single_apply, hji, hjm.symm, hmi, ite_true, ite_false, zero_smul, sub_zero, one_smul,
    smul_zero] at h
  simpa [smul_smul, inv_mul_cancel₀ hi] using N.smul_mem (v i)⁻¹ h

/-- **The standard module of the orthogonal Lie algebra is irreducible** over every field, for an
index type with at least three elements. -/
theorem isIrreducible_so_standard (hl : 2 < Fintype.card l) :
    IsIrreducible K (Orthogonal.so l K) (l → K) := by
  -- Every index has two others distinct from it.
  have hthird (a b : l) : ∃ c, c ≠ a ∧ c ≠ b := by
    by_contra! h
    have hsub : (Finset.univ : Finset l) ⊆ {a, b} := fun c _ ↦ by
      by_cases hc : c = a
      · simp [hc]
      · simp [h c hc]
    have := (Finset.card_le_card hsub).trans Finset.card_le_two
    rw [Finset.card_univ] at this
    omega
  have : Nonempty l := Fintype.card_pos_iff.mp (by omega)
  apply IsIrreducible.mk
  intro N hN
  obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot
    ((LieSubmodule.toSubmodule_eq_bot N).not.mpr hN)
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hv0
  -- Every standard basis vector other than `eᵢ` lies in `N`, and then so does `eᵢ`.
  have hne (m : l) (hmi : m ≠ i) : Pi.single m 1 ∈ N := by
    obtain ⟨j, hji, hjm⟩ := hthird i m
    exact single_mem_of_apply_ne_zero N hv hi hji hjm hmi
  have hsingle (m : l) : Pi.single m (1 : K) ∈ N := by
    by_cases hmi : m = i
    · obtain ⟨m', hm'i, -⟩ := hthird i i
      obtain ⟨j, hjm', hji⟩ := hthird m' i
      rw [hmi]
      exact single_mem_of_apply_ne_zero N (hne m' hm'i) (by simp) hjm' hji hm'i.symm
    · exact hne m hmi
  rw [eq_top_iff]
  intro w _
  rw [← Finset.univ_sum_single w]
  refine N.sum_mem fun m _ ↦ ?_
  convert N.smul_mem (w m) (hsingle m) using 1
  ext j
  simp [Pi.single_apply]

end Field

section CharZero

variable (K : Type*) [Field K] [CharZero K]

/-- **The orthogonal Lie algebra has trivial radical** in characteristic zero, for an index type
with at least three elements, provided each of its elements acts triangularizably on the standard
module, which holds over every algebraically closed field. By Cartan's criterion its Killing form
is then nondegenerate. -/
theorem hasTrivialRadical_so (hl : 2 < Fintype.card l)
    [IsTriangularizable K (Orthogonal.so l K) (l → K)] :
    HasTrivialRadical K (Orthogonal.so l K) := by
  have : IsIrreducible K (Orthogonal.so l K) (l → K) := isIrreducible_so_standard hl
  let : Invertible (2 : K) := invertibleOfNonzero two_ne_zero
  exact hasTrivialRadical_of_isIrreducible_of_isFaithful K (Orthogonal.so l K) (l → K)
    fun ⟨x, hx⟩ ↦ by
      simpa using Matrix.trace_eq_zero_of_transpose_eq_neg x ((Orthogonal.mem_so l K x).mp hx)

end CharZero

end TauCeti
