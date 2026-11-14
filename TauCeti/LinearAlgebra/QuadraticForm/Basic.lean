/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.CharP.Defs
public import Mathlib.LinearAlgebra.QuadraticForm.Basic

/-!
# Basic properties of quadratic maps

This file records elementary consequences of the quadratic-map axioms.

## Main results

* `QuadraticMap.Anisotropic.comp`: injective pullback preserves anisotropy.
* `QuadraticMap.nontrivial_of_ne_zero`: the source of a nonzero quadratic map is nontrivial.
* `QuadraticMap.polar_self_eq_zero` and `QuadraticMap.isAlt_polarBilin`: in characteristic two, the
  polar form of a quadratic map has vanishing diagonal and so is alternating.
* `QuadraticMap.map_sum_of_polar_eq_zero`: a quadratic map commutes with finite sums along a family
  whose distinct elements are pairwise orthogonal for the polar form.
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

/-- Over a commutative ring of characteristic two, the polar form of any quadratic map vanishes on
the diagonal. -/
theorem polar_self_eq_zero {R M P : Type*} [CommRing R] [CharP R 2]
    [AddCommGroup M] [Module R M] [AddCommGroup P] [Module R P]
    (Q : QuadraticMap R M P) (x : M) : polar Q x x = 0 := by
  rw [polar_self, ← Nat.cast_smul_eq_nsmul R, CharP.cast_eq_zero (R := R) 2, zero_smul]

/-- Over a commutative ring of characteristic two, the polar bilinear map of any quadratic map is
alternating. -/
theorem isAlt_polarBilin {R M P : Type*} [CommRing R] [CharP R 2]
    [AddCommGroup M] [Module R M] [AddCommGroup P] [Module R P]
    (Q : QuadraticMap R M P) : Q.polarBilin.IsAlt :=
  fun x ↦ Q.polar_self_eq_zero x

/-- For a family whose distinct elements are pairwise orthogonal for the polar form, a quadratic map
commutes with finite sums. -/
theorem map_sum_of_polar_eq_zero {ι R M P : Type*} [CommRing R]
    [AddCommGroup M] [Module R M] [AddCommGroup P] [Module R P]
    (Q : QuadraticMap R M P) (s : Finset ι) (f : ι → M)
    (horth : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → polar Q (f i) (f j) = 0) :
    Q (∑ i ∈ s, f i) = ∑ i ∈ s, Q (f i) := by
  induction s using Finset.cons_induction with
  | empty => simp
  | cons a s ha ih =>
    have hpolar : polar Q (f a) (∑ i ∈ s, f i) = 0 := by
      rw [← polarBilin_apply_apply, map_sum]
      exact Finset.sum_eq_zero fun i hi ↦ by
        simpa using horth a (Finset.mem_cons_self a s) i (Finset.mem_cons_of_mem hi)
          (ne_of_mem_of_not_mem hi ha).symm
    rw [Finset.sum_cons, Finset.sum_cons, QuadraticMap.map_add Q, hpolar, add_zero,
      ih fun i hi j hj ↦ horth i (Finset.mem_cons_of_mem hi) j (Finset.mem_cons_of_mem hj)]

end QuadraticMap
