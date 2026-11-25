/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Elementary
public import Mathlib.GroupTheory.SpecificGroups.Alternating

/-!
# Permutation matrices in the elementary subgroup

Over a possibly noncommutative ring `A`, the signed Weyl word
`nᵢⱼ = eᵢⱼ(1) eⱼᵢ(-1) eᵢⱼ(1)` is a product of three elementary matrices. It is the permutation
matrix of the transposition of `i` and `j` with one row negated
(`TauCeti.transvectionWeylElement_eq_diagGL_mul_permutationGL`), and the product of two such words
can cancel the signs: the permutation matrix of the three-cycle `(i j) (i k)` is `nᵢⱼ nₖᵢ`
(`TauCeti.permutationGL_swap_mul_swap_same_eq_transvectionWeylElement_mul`). Since the
three-cycles generate the alternating group, **every even permutation matrix is elementary**, over
every ring.

The parity condition cannot be dropped in general: over a commutative ring the determinant of the
permutation matrix of `σ` is the sign of `σ`, and elementary matrices have determinant one, so
when `-1 ≠ 1` the permutation matrix of `σ` is elementary exactly when `σ` is even. When
`-1 = 1`, as over `𝔽₂`, the signed Weyl word is itself the permutation matrix of a
transposition, and every permutation matrix is elementary.

Even permutation matrices let one move elementary matrices and blocks between coordinates by
conjugation inside the elementary subgroup, without leaving it.

## Main results

* `TauCeti.transvectionWeylElement_mem_elementarySubgroup`: the signed Weyl word is elementary.
* `TauCeti.permutationGL_mem_elementarySubgroup`: the permutation matrix of an even permutation
  is elementary.
* `TauCeti.permutationGL_mem_elementarySubgroup_of_neg_one_eq_one`: if `-1 = 1` in `A`, every
  permutation matrix is elementary.
* `TauCeti.permutationGL_mem_elementarySubgroup_iff`: over a commutative ring in which
  `-1 ≠ 1`, a permutation matrix is elementary exactly when the permutation is even.

## References

* C. A. Weibel, *The K-book: An Introduction to Algebraic K-Theory*, Graduate Studies in
  Mathematics 145 (2013), Chapter III, 1.2.1, where the signed Weyl word and the elementary
  even permutation matrices appear.
* J. Milnor, *Introduction to Algebraic K-Theory*, Annals of Mathematics Studies 72 (1971), §9,
  where `wᵢⱼ(u) = xᵢⱼ(u) xⱼᵢ(-u⁻¹) xᵢⱼ(u)` is the Steinberg-group lift of the signed Weyl word.
-/

public section

open Matrix Equiv

namespace TauCeti

variable {n : Type*} [DecidableEq n] [Fintype n]

section Ring

variable {A : Type*} [Ring A]

/-- The signed Weyl word `eᵢⱼ(1) eⱼᵢ(-1) eᵢⱼ(1)` is elementary. -/
theorem transvectionWeylElement_mem_elementarySubgroup {i j : n} (hij : i ≠ j) :
    transvectionWeylElement (A := A) hij ∈ elementarySubgroup n A := by
  rw [transvectionWeylElement_def]
  exact mul_mem (mul_mem (transvectionUnit_mem_elementarySubgroup hij 1)
    (transvectionUnit_mem_elementarySubgroup hij.symm (-1)))
    (transvectionUnit_mem_elementarySubgroup hij 1)

/-- **Even permutation matrices are elementary.** Over every ring, the permutation matrix of an
even permutation is a product of elementary matrices. -/
theorem permutationGL_mem_elementarySubgroup {σ : Perm n} (hσ : σ ∈ alternatingGroup n) :
    permutationGL σ ∈ elementarySubgroup n A := by
  rw [← Perm.closure_three_cycles_eq_alternating] at hσ
  refine (Subgroup.closure_le ((elementarySubgroup n A).comap permutationGL)).2 ?_ hσ
  intro g hg
  -- A three-cycle `g` moving `a` is `(g a, a) (g a, g (g a))`.
  obtain ⟨a, ha⟩ := Finset.ne_empty_iff_nonempty.1 (mt Perm.support_eq_empty_iff.1 hg.ne_one)
  have hga : g a ≠ a := Perm.mem_support.1 ha
  have hgga : g a ≠ g (g a) := fun h ↦ hga (g.injective h).symm
  rw [SetLike.mem_coe, Subgroup.mem_comap, hg.eq_swap_mul_swap_iff_mem_support.2 ha,
    Equiv.swap_comm a, permutationGL_swap_mul_swap_same_eq_transvectionWeylElement_mul hga hgga]
  exact mul_mem (transvectionWeylElement_mem_elementarySubgroup hga)
    (transvectionWeylElement_mem_elementarySubgroup hgga.symm)

/-- If `-1 = 1` in `A`, as over `𝔽₂`, every permutation matrix is elementary: the signed Weyl word
is then the permutation matrix of a transposition. -/
theorem permutationGL_mem_elementarySubgroup_of_neg_one_eq_one (h : (-1 : A) = 1)
    (σ : Perm n) : permutationGL σ ∈ elementarySubgroup n A := by
  have hu : (-1 : Aˣ) = 1 := Units.ext h
  refine (Subgroup.closure_le ((elementarySubgroup n A).comap permutationGL)).2 ?_
    (Perm.closure_isSwap (α := n) ▸ Subgroup.mem_top σ)
  rintro _ ⟨i, j, hij, rfl⟩
  have hw := transvectionWeylElement_eq_diagGL_mul_permutationGL (A := A) hij
  rw [hu, Pi.mulSingle_one, map_one, one_mul] at hw
  rw [SetLike.mem_coe, Subgroup.mem_comap, ← hw]
  exact transvectionWeylElement_mem_elementarySubgroup hij

end Ring

section CommRing

variable {R : Type*} [CommRing R]

/-- Over a commutative ring in which `-1 ≠ 1`, the permutation matrix of `σ` is elementary
exactly when `σ` is even: elementary matrices have determinant one, and the determinant of a
permutation matrix is the sign of the permutation. -/
theorem permutationGL_mem_elementarySubgroup_iff (h : (-1 : R) ≠ 1) {σ : Perm n} :
    permutationGL σ ∈ elementarySubgroup n R ↔ σ ∈ alternatingGroup n := by
  refine ⟨fun hσ ↦ ?_, permutationGL_mem_elementarySubgroup⟩
  have hdet : GeneralLinearGroup.det (permutationGL (k := R) σ) = 1 :=
    elementarySubgroup_le_ker_det hσ
  rw [det_permutationGL] at hdet
  rw [Perm.mem_alternatingGroup]
  rcases Int.units_eq_one_or (Perm.sign σ) with hs | hs
  · exact hs
  · rw [hs] at hdet
    exact absurd (congrArg Units.val hdet) (by simpa using h)

end CommRing

end TauCeti
