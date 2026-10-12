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
elements. In characteristic zero the standard module is also faithful and trace-free, so
`LieAlgebra.hasTrivialRadical_of_isIrreducible_of_isFaithful` shows that `so l K` has trivial
radical, provided each element acts triangularizably on the standard module (for instance over an
algebraically closed field). Cartan's criterion turns this into nondegeneracy of the Killing form.

The irreducibility argument uses the elements `E_ab - E_ba` of `so l K`, which send `v` to
`v_b e_a - v_a e_b`. Given `v` with `vᵢ ≠ 0` and two further indices `j` and `m`, the element
`E_ji - E_ij` sends `v` to `vᵢ eⱼ - vⱼ eᵢ`, and then `E_mj - E_jm` sends this to `vᵢ eₘ`. So a
Lie submodule containing `v` contains `eₘ` for every `m ≠ i`, and the same step applied to such an
`eₘ` gives `eᵢ`. The argument needs a third index.

The structure follows the symplectic case in `TauCeti/Algebra/Lie/Symplectic/Killing.lean`
(`TauCeti.isIrreducible_sp_standard`, `TauCeti.hasTrivialRadical_sp`).

## Main results

* `TauCeti.isIrreducible_so_standard`: the standard module of `so l K` is irreducible when `l`
  has at least three elements.
* `TauCeti.hasTrivialRadical_so`: `so l K` has trivial radical in characteristic zero, given
  triangularizability of its standard module; in particular its Killing form is nondegenerate.

## References

* W. Fulton and J. Harris, *Representation Theory*, Lecture 18 (the orthogonal Lie algebras).
* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, §§1.2, 5 and 19.
* Mathlib's `LieAlgebra.hasTrivialRadical_of_isIrreducible_of_isFaithful` (faithful irreducible
  modules and reductivity).
-/

public section

namespace TauCeti

open Matrix LieAlgebra LieModule

attribute [local instance 100] LieRing.ofAssociativeRing

variable {l : Type*} [DecidableEq l] [Fintype l] {K : Type*} [Field K]

/-- A Lie submodule of the standard module of `so l K` that contains a vector with nonzero
`i`-th coordinate contains every standard basis vector `eₘ` with `m ≠ i`, provided some index
`j` differs from both `i` and `m`. -/
private theorem single_mem_of_apply_ne_zero (N : LieSubmodule K (Orthogonal.so l K) (l → K))
    {v : l → K} (hv : v ∈ N) {i m j : l} (hi : v i ≠ 0) (hji : j ≠ i) (hjm : j ≠ m)
    (hmi : m ≠ i) : Pi.single m 1 ∈ N := by
  have hmem (a b : l) {u : l → K} (hu : u ∈ N) : (single a b 1 - single b a 1) *ᵥ u ∈ N := by
    have h := N.lie_mem
      (x := ⟨_, (Orthogonal.mem_so l K _).2 (transpose_single_sub_single a b (1 : K))⟩) hu
    rwa [LieSubalgebra.coe_bracket_of_module, Matrix.lie_apply] at h
  have h := hmem m j (hmem j i hv)
  simp only [sub_mulVec, single_mulVec_eq, mulVec_sub, mulVec_smul, one_mul, Pi.single_eq_same,
    Pi.single_eq_of_ne hji, Pi.single_eq_of_ne hjm.symm, Pi.single_eq_of_ne hmi, zero_smul,
    one_smul, smul_zero, sub_zero] at h
  exact (N.toSubmodule.smul_mem_iff hi).mp h

/-- **The standard module of the orthogonal Lie algebra is irreducible** over every field, for an
index type with at least three elements. -/
theorem isIrreducible_so_standard (hl : 3 ≤ Fintype.card l) :
    IsIrreducible K (Orthogonal.so l K) (l → K) := by
  -- Every index has two others distinct from it.
  have hthird (a b : l) : ∃ c, c ≠ a ∧ c ≠ b :=
    ENat.exists_ne_ne_of_three_le (by rw [ENat.card_eq_coe_fintype_card]; exact_mod_cast hl) a b
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
  rw [← LieSubmodule.toSubmodule_eq_top,
    Submodule.eq_top_iff_forall_basis_mem (Pi.basisFun K l)]
  simpa using hsingle

variable (K) [CharZero K]

/-- **The orthogonal Lie algebra has trivial radical** in characteristic zero, for an index type
with at least three elements, provided each of its elements acts triangularizably on the standard
module, which holds over every algebraically closed field. By Cartan's criterion its Killing form
is then nondegenerate. -/
theorem hasTrivialRadical_so (hl : 3 ≤ Fintype.card l)
    [IsTriangularizable K (Orthogonal.so l K) (l → K)] :
    HasTrivialRadical K (Orthogonal.so l K) := by
  have : IsIrreducible K (Orthogonal.so l K) (l → K) := isIrreducible_so_standard hl
  let : Invertible (2 : K) := invertibleOfNonzero two_ne_zero
  exact hasTrivialRadical_of_isIrreducible_of_isFaithful K (Orthogonal.so l K) (l → K)
    fun ⟨x, hx⟩ ↦ by
      simpa using Matrix.trace_eq_zero_of_transpose_eq_neg x ((Orthogonal.mem_so l K x).mp hx)

end TauCeti
