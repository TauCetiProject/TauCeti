/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Henselian
import Mathlib.Tactic.LinearCombination
import TauCeti.RingTheory.Henselian.Ideal
import TauCeti.RingTheory.Henselian.RootCriterion

/-!
# Henselian pairs sharing an ideal

Whether a pair `(A, I)` is henselian depends only on the ideal `I` viewed as a non-unital ring,
not on the ambient ring `A`. Precisely, if a ring map `φ : A →+* A'` restricts to a bijection
from `I` onto an ideal `I'` of `A'`, then `(A, I)` is henselian if and only if `(A', I')` is
(`RingHom.henselianRing_iff_of_bijOn`). One direction needs only that every element of `I'` is
the image of an element of `I` (`RingHom.henselianRing_of_surjOn`).

The main application compares a ring with a subring: if `J` is an ideal of `R'` contained in a
subring `R`, then `(R, J)` is henselian if and only if `(R', J)` is
(`Subring.henselianRing_comap_subtype_iff`). For instance, if `ϖ ∈ R` and `ϖⁿ R' ⊆ R`, as for two
rings of definition of a Tate ring with pseudouniformizer `ϖ`, then `ϖⁿ⁺¹ R'` is such a common
ideal, and since henselianity depends only on the radical, `(R, ϖ R)` is henselian if and only if
`(R', ϖ R')` is (`Subring.henselianRing_span_singleton_iff`).

The proof uses Gabber's criterion: `(A, I)` is henselian exactly when `I` lies in the Jacobson
radical and every polynomial `Xⁿ (X - 1) + aₙ Xⁿ + ⋯ + a₀` with all `aᵢ ∈ I` has a root in
`1 + I`. Both conditions only involve elements of `1 + I` and equations between elements of `I`.

## Main results

* `RingHom.henselianRing_of_surjOn`: if every element of `I'` is the image of an element of `I`
  and `(A, I)` is henselian, then so is `(A', I')`.
* `RingHom.henselianRing_iff_of_bijOn`: if `φ` restricts to a bijection `I → I'`, then `(A, I)` is
  henselian if and only if `(A', I')` is.
* `Subring.henselianRing_comap_subtype_iff`: an ideal of `R'` contained in a subring `R` is
  henselian in `R` if and only if it is henselian in `R'`.
* `Subring.henselianRing_span_singleton_iff`: if `ϖ ∈ R` and `ϖⁿ R' ⊆ R`, then `(R, ϖ R)` is
  henselian if and only if `(R', ϖ R')` is.

## References

* O. Gabber, L. Ramero, *Almost ring theory*, arXiv v3, §5.1, Remark 5.1.9(ii).
* B. Bhatt, *Lecture notes for a class on perfectoid spaces*, proof of Lemma 7.2.3(3).
* [Stacks Project, Lemma 15.11.6](https://stacks.math.columbia.edu/tag/09XI), condition (5).
-/

public section

open Polynomial

namespace RingHom

variable {A A' : Type*} [CommRing A] [CommRing A'] (φ : A →+* A') {I : Ideal A} {I' : Ideal A'}

/-- If every element of `I'` is the image under a ring map `φ` of an element of `I`, and `(A, I)`
is henselian, then `(A', I')` is henselian. Neither injectivity nor surjectivity of `φ` is needed,
and `φ` need not map `I` into `I'`. -/
theorem henselianRing_of_surjOn (hφ : Set.SurjOn φ I I') [HenselianRing A I] :
    HenselianRing A' I' := by
  -- The smaller ideal `K = I ∩ φ⁻¹(I')` is still henselian, and `φ` maps it onto `I'`.
  set K := I ⊓ I'.comap φ
  have : HenselianRing A K := Ideal.henselianRing_of_le inf_le_left
  have hsurj : ∀ y ∈ I', ∃ x ∈ K, φ x = y := fun y hy ↦ by
    obtain ⟨x, hx, rfl⟩ := hφ hy
    exact ⟨x, ⟨hx, hy⟩, rfl⟩
  rw [TauCeti.henselianRing_iff_forall_exists_isRoot_X_pow_mul_X_sub_one_add]
  refine ⟨fun y hy ↦ Ring.mem_jacobson_iff.mpr fun z ↦ ?_, fun n _ p hpn hp ↦ ?_⟩
  · -- `1 + yz` is the image of the unit `1 + x` for some `x ∈ K`.
    obtain ⟨x, hx, hxy⟩ := hsurj _ (I'.mul_mem_right z hy)
    have hunit := Ring.mem_jacobson_iff.mp (HenselianRing.jac hx) 1
    simpa [hxy] using hunit.map φ
  · -- Lift the coefficients of `p` into `K`, and push a root near `1` forward.
    choose c hcK hc using fun k ↦ hsurj _ (hp k)
    set q : A[X] := ∑ k ∈ Finset.range (n + 1), monomial k (c k)
    have hqK : ∀ k, q.coeff k ∈ K := fun k ↦ by
      rw [finsetSum_coeff]
      exact sum_mem fun j _ ↦ by rw [coeff_monomial_apply]; split_ifs <;> simp [hcK]
    have hqp : q.map φ = p := by
      simp only [q, Polynomial.map_sum, map_monomial, hc]
      exact (as_sum_range' p (n + 1) (by omega)).symm
    obtain ⟨a, ha, ha1⟩ := TauCeti.HenselianRing.exists_isRoot_X_pow_mul_X_sub_one_add n hqK
    refine ⟨φ a, ?_, by simpa using ha1.2⟩
    have := congrArg φ ha.eq_zero
    rw [← eval_map_apply] at this
    simpa [IsRoot, hqp] using this

/-- **Henselian pairs depend only on the ideal.** If a ring map `φ : A →+* A'` restricts to a
bijection from `I` onto `I'`, then `(A, I)` is henselian if and only if `(A', I')` is. -/
theorem henselianRing_iff_of_bijOn (hφ : Set.BijOn φ I I') :
    HenselianRing A I ↔ HenselianRing A' I' := by
  refine ⟨fun _ ↦ φ.henselianRing_of_surjOn hφ.surjOn, fun _ ↦ ?_⟩
  -- An element of `I` killed by `φ` is zero.
  have hzero : ∀ x ∈ I, φ x = 0 → x = 0 := fun x hx h ↦
    hφ.injOn hx I.zero_mem (by rw [h, map_zero])
  rw [TauCeti.henselianRing_iff_forall_exists_isRoot_X_pow_mul_X_sub_one_add]
  refine ⟨fun x hx ↦ Ring.mem_jacobson_iff.mpr fun z ↦ ?_, fun n _ p _ hp ↦ ?_⟩
  · -- The inverse of the unit `1 + φ(xz)` is `1 + φ y` for some `y ∈ I`, and `y` inverts
    -- `1 + xz` since `(1 + xz)(1 + y) - 1 ∈ I` is killed by `φ`.
    have hxz : x * z ∈ I := I.mul_mem_right z hx
    obtain ⟨u, hu⟩ := Ring.mem_jacobson_iff.mp (HenselianRing.jac (hφ.mapsTo hxz)) 1
    have hu1 : (↑u⁻¹ : A') - 1 ∈ I' := by
      have : (↑u⁻¹ : A') - 1 = -(φ (x * z) * ↑u⁻¹) := by
        linear_combination u.inv_mul - (↑u⁻¹ : A') * hu
      rw [this]
      exact I'.neg_mem (I'.mul_mem_right _ (hφ.mapsTo hxz))
    obtain ⟨y, hy, hyu⟩ := hφ.surjOn hu1
    have hprod : (x * z + 1) * (1 + y) - 1 = 0 := hzero _ (by
      have : (x * z + 1) * (1 + y) - 1 = x * z * (1 + y) + y := by ring
      rw [this]
      exact I.add_mem (I.mul_mem_right _ hxz) hy) (by
      rw [map_sub, map_mul, map_add, map_add, map_one, hyu]
      linear_combination u.inv_mul - (↑u⁻¹ : A') * hu)
    exact IsUnit.of_mul_eq_one _ (sub_eq_zero.mp hprod)
  · -- Push `p` forward, take a root near `1` in `A'`, and pull it back.
    have hpI : ∀ k, (p.map φ).coeff k ∈ I' := fun k ↦ by
      rw [coeff_map]
      exact hφ.mapsTo (hp k)
    obtain ⟨a', ha', ha'1⟩ := TauCeti.HenselianRing.exists_isRoot_X_pow_mul_X_sub_one_add n hpI
    obtain ⟨y, hy, hya⟩ := hφ.surjOn ha'1
    refine ⟨1 + y, hzero _ ?_ ?_, by simpa using hy⟩
    · -- The value at `1 + y` lies in `I`, since the polynomial is `Xⁿ (X - 1)` modulo `I`.
      have hp₀ : p.map (Ideal.Quotient.mk I) = 0 := by
        ext k
        simpa using Ideal.Quotient.eq_zero_iff_mem.mpr (hp k)
      rw [← Ideal.Quotient.eq_zero_iff_mem, ← eval_map_apply]
      simp [Polynomial.map_add, hp₀, Ideal.Quotient.eq_zero_iff_mem.mpr hy]
    · rw [← eval_map_apply, map_add, map_one, hya]
      simpa [Polynomial.map_add, Polynomial.map_mul] using ha'.eq_zero

end RingHom

namespace Subring

variable {R' : Type*} [CommRing R'] (R : Subring R')

/-- **Henselian pairs and subrings.** If an ideal `J` of `R'` is contained in a subring `R`, then
`(R, J)` is henselian if and only if `(R', J)` is. -/
theorem henselianRing_comap_subtype_iff {J : Ideal R'} (hJ : (J : Set R') ⊆ R) :
    HenselianRing R (J.comap R.subtype) ↔ HenselianRing R' J :=
  R.subtype.henselianRing_iff_of_bijOn
    ⟨fun _ hx ↦ hx, R.subtype_injective.injOn, fun y hy ↦ ⟨⟨y, hJ hy⟩, hy, rfl⟩⟩

/-- **Henselian pairs along a principal ideal and subrings.** Let `R` be a subring of `R'` and
`ϖ ∈ R` with `ϖⁿ R' ⊆ R`, for instance two rings of definition of a Tate ring with
pseudouniformizer `ϖ`. Then `(R, ϖ R)` is henselian if and only if `(R', ϖ R')` is. -/
theorem henselianRing_span_singleton_iff (ϖ : R) {n : ℕ}
    (hn : ∀ x : R', (ϖ : R') ^ n * x ∈ R) :
    HenselianRing R (Ideal.span {ϖ}) ↔ HenselianRing R' (Ideal.span {(ϖ : R')}) := by
  -- `J = ϖⁿ⁺¹ R'` is an ideal of `R'` contained in `ϖ R`.
  set J : Ideal R' := Ideal.span {(ϖ : R') ^ (n + 1)}
  have hJ : ∀ y ∈ J, ∃ r ∈ Ideal.span {ϖ}, (r : R') = y := fun y hy ↦ by
    obtain ⟨x, rfl⟩ := Ideal.mem_span_singleton'.mp hy
    exact ⟨ϖ * ⟨_, hn x⟩, Ideal.mem_span_singleton'.mpr ⟨_, mul_comm _ _⟩,
      by simp only [coe_mul]; ring⟩
  -- In `R`, the ideal `J ∩ R` lies between `ϖⁿ⁺¹ R` and `ϖ R`, so it has the radical of `ϖ R`.
  have hradR : (J.comap R.subtype).radical = (Ideal.span {ϖ}).radical := by
    refine le_antisymm (Ideal.radical_mono fun r hr ↦ ?_) (Ideal.radical_le_radical_iff.mpr
      (Ideal.span_le.mpr (Set.singleton_subset_iff.mpr ⟨n + 1, by simp [J]⟩)))
    obtain ⟨s, hs, hsr⟩ := hJ _ hr
    rwa [← R.subtype_injective hsr]
  have hradR' : J.radical = (Ideal.span {(ϖ : R')}).radical := by
    rw [← Ideal.radical_pow (.span {(ϖ : R')}) n.succ_ne_zero, Ideal.span_singleton_pow]
  -- Henselianity depends only on the radical.
  rw [← Ideal.henselianRing_radical_iff, ← hradR, Ideal.henselianRing_radical_iff,
    R.henselianRing_comap_subtype_iff fun y hy ↦ ?_, ← Ideal.henselianRing_radical_iff, hradR',
    Ideal.henselianRing_radical_iff]
  obtain ⟨r, -, rfl⟩ := hJ y hy
  exact r.property

end Subring
