/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.CharP.Two
public import Mathlib.LinearAlgebra.QuadraticForm.Basic

/-!
# Basic properties of quadratic maps

This file records elementary consequences of the quadratic-map axioms.

## Main results

* `QuadraticMap.Anisotropic.comp`: injective pullback preserves anisotropy.
* `QuadraticMap.nontrivial_of_ne_zero`: the source of a nonzero quadratic map is nontrivial.
* `QuadraticMap.map_sum_of_polar_eq_zero`: a quadratic map is additive on a finite family of
  pairwise polar-orthogonal vectors.
* `QuadraticMap.isAlt_polarBilin`: in characteristic two the polar form is alternating.
-/

public section

namespace QuadraticMap

/-- The source of a nonzero quadratic map is nontrivial. -/
theorem nontrivial_of_ne_zero {S V N : Type*} [CommSemiring S] [AddCommMonoid V]
    [Module S V] [AddCommMonoid N] [Module S N] {Q : QuadraticMap S V N} (hQ : Q ≠ 0) :
    Nontrivial V := by
  obtain ⟨v, hv⟩ := DFunLike.ne_iff.mp hQ
  exact nontrivial_of_ne v 0 (fun h ↦ hv (by simp [h]))

/-- An injective pullback of an anisotropic quadratic map is anisotropic. -/
theorem Anisotropic.comp {R M N P : Type*} [CommSemiring R]
    [AddCommMonoid M] [Module R M] [AddCommMonoid N] [Module R N]
    [AddCommMonoid P] [Module R P] {Q : QuadraticMap R M N} (hQ : Q.Anisotropic)
    (f : P →ₗ[R] M) (hf : Function.Injective f) : (Q.comp f).Anisotropic := by
  intro x hx
  apply hf
  rw [map_zero]
  exact hQ _ hx

/-- A quadratic map is additive on a finite family of vectors whose distinct members are
orthogonal for its polar form. -/
theorem map_sum_of_polar_eq_zero {R M N ι : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] (Q : QuadraticMap R M N) (s : Finset ι) (f : ι → M)
    (hf : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → polar Q (f i) (f j) = 0) :
    Q (∑ i ∈ s, f i) = ∑ i ∈ s, Q (f i) := by
  classical
  rw [Q.map_sum, add_eq_left]
  refine Finset.sum_eq_zero fun ij hij => ?_
  induction ij using Sym2.ind with
  | _ i j =>
    rw [Finset.mem_filter, Finset.mk_mem_sym2_iff, Sym2.mk_isDiag_iff] at hij
    rw [Sym2.map_mk, polarSym2_sym2Mk]
    exact hf i hij.1.1 j hij.1.2 hij.2

/-- In characteristic two the polar form of a quadratic map is alternating, since
`polar Q x x = 2 • Q x`. -/
theorem isAlt_polarBilin {R M N : Type*} [CommRing R] [CharP R 2] [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] (Q : QuadraticMap R M N) : Q.polarBilin.IsAlt := fun x => by
  rw [polarBilin_apply_apply, polar_self, ← Nat.cast_smul_eq_nsmul R, Nat.cast_ofNat,
    CharTwo.two_eq_zero, zero_smul]

end QuadraticMap
