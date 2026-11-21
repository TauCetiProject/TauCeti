/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.Splits
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed

import Mathlib.Algebra.Polynomial.Lifts
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.RingTheory.Localization.Integer
import Mathlib.RingTheory.Polynomial.ScaleRoots

/-!
# Absolutely integrally closed rings

A commutative ring `A` is *absolutely integrally closed* when every monic polynomial of positive
degree over `A` has a root in `A`. No domain or nontriviality hypothesis is built in: the zero ring
is absolutely integrally closed, and so is any product of algebraically closed fields. For a field
the notion is algebraic closedness, and for a domain it means being integrally closed with
algebraically closed fraction field. Absolutely integrally closed valuation domains are the test
objects of the v- and arc-topologies, which is why the notion is needed for general rings: it must
be stable under the quotients and localizations used to cut a valuation ring into prime intervals.

## Main definitions

* `TauCeti.IsAbsolutelyIntegrallyClosed A`: every monic polynomial of positive degree over `A` has
  a root in `A`.

## Main results

* `TauCeti.IsAbsolutelyIntegrallyClosed.splits` and
  `TauCeti.isAbsolutelyIntegrallyClosed_iff_forall_splits`: `A` is absolutely integrally closed if
  and only if every monic polynomial over `A` is a product of monic linear factors.
* `TauCeti.isAbsolutelyIntegrallyClosed_iff_isAlgClosed`: for a field, the notion is
  `IsAlgClosed`.
* `TauCeti.IsAbsolutelyIntegrallyClosed.of_surjective` and
  `TauCeti.IsAbsolutelyIntegrallyClosed.of_isLocalization`: quotients and localizations of an
  absolutely integrally closed ring are absolutely integrally closed. Arbitrary products are too.
* `TauCeti.isAbsolutelyIntegrallyClosed_iff_isIntegrallyClosed_and_isAlgClosed`: a domain is
  absolutely integrally closed if and only if it is integrally closed and its fraction field is
  algebraically closed.
* `TauCeti.not_isAbsolutelyIntegrallyClosed_rat`: `ℚ` is not absolutely integrally closed, as
  `X ^ 2 - 2` has no rational root.

## References

* B. Bhatt, A. Mathew, *The arc-topology*, Forum Math. Pi 9 (2021), Definition 3.26.
* The Stacks Project, *More on Algebra*, the section on absolutely integrally closed rings.
-/

public section

open Polynomial

namespace TauCeti

/-- A commutative ring `A` is *absolutely integrally closed* if every monic polynomial of positive
degree over `A` has a root in `A`. The constant polynomial `1` imposes no condition, so the zero
ring is absolutely integrally closed; see `IsAbsolutelyIntegrallyClosed.splits` for the
equivalent formulation that every monic polynomial is a product of linear factors. -/
class IsAbsolutelyIntegrallyClosed (A : Type*) [CommRing A] : Prop where
  /-- Every monic polynomial of positive degree has a root. -/
  exists_root (p : A[X]) (hp : p.Monic) (hdeg : 0 < p.natDegree) : ∃ x, p.IsRoot x

variable {A B : Type*} [CommRing A] [CommRing B]

namespace IsAbsolutelyIntegrallyClosed

/-- Over an absolutely integrally closed ring every monic polynomial splits: it is a product of
monic linear factors `X - C a`. -/
theorem splits [IsAbsolutelyIntegrallyClosed A] {p : A[X]} (hp : p.Monic) : p.Splits := by
  induction h : p.natDegree generalizing p with
  | zero => simp [eq_one_of_monic_natDegree_zero hp h]
  | succ n ih =>
    obtain _ | _ := subsingleton_or_nontrivial A
    · simp [natDegree_of_subsingleton] at h
    obtain ⟨a, ha⟩ := exists_root p hp (by omega)
    have hq : (X - C a) * (p /ₘ (X - C a)) = p := mul_divByMonic_eq_iff_isRoot.mpr ha
    have hqdeg : (p /ₘ (X - C a)).natDegree = n := by
      rw [natDegree_divByMonic _ (monic_X_sub_C a), natDegree_X_sub_C, h, Nat.add_sub_cancel]
    exact hq ▸ (Splits.X_sub_C a).mul
      (ih ((monic_X_sub_C a).of_mul_monic_left (hq.symm ▸ hp)) hqdeg)

/-- The zero ring is absolutely integrally closed: no polynomial over it has positive degree. -/
theorem of_subsingleton [Subsingleton A] : IsAbsolutelyIntegrallyClosed A where
  exists_root p _ hdeg := by simp [natDegree_of_subsingleton] at hdeg

/-- The image of an absolutely integrally closed ring under a surjective ring homomorphism is
absolutely integrally closed: lift a monic polynomial to a monic polynomial of the same degree and
map one of its roots. -/
theorem of_surjective [IsAbsolutelyIntegrallyClosed A] (f : A →+* B)
    (hf : Function.Surjective f) : IsAbsolutelyIntegrallyClosed B where
  exists_root q hq hdeg := by
    obtain ⟨p, rfl, hpdeg, hp⟩ := lifts_and_natDegree_eq_and_monic
      ((lifts_iff_coeff_lifts q).mpr fun _ ↦ hf _) hq
    obtain ⟨a, ha⟩ := exists_root p hp (hpdeg ▸ hdeg)
    exact ⟨f a, ha.map f⟩

/-- A quotient of an absolutely integrally closed ring is absolutely integrally closed. -/
instance quotient [IsAbsolutelyIntegrallyClosed A] (I : Ideal A) :
    IsAbsolutelyIntegrallyClosed (A ⧸ I) :=
  of_surjective _ Ideal.Quotient.mk_surjective

/-- A localization of an absolutely integrally closed ring is absolutely integrally closed. For a
monic `q` of degree `n` over `B` and a common denominator `s` of its coefficients, the rescaled
polynomial with coefficients `qᵢ sⁿ⁻ⁱ` is monic with coefficients from `A`, and a root `y` of it
gives the root `y / s` of `q`. -/
theorem of_isLocalization [IsAbsolutelyIntegrallyClosed A] [Algebra A B] (M : Submonoid A)
    [IsLocalization M B] : IsAbsolutelyIntegrallyClosed B where
  exists_root q hq hdeg := by
    obtain ⟨s, hs⟩ := IsLocalization.exist_integer_multiples M (Finset.range q.natDegree) q.coeff
    have hu : IsUnit (algebraMap A B s) := IsLocalization.map_units B s
    have hlifts : q.scaleRoots (algebraMap A B s) ∈ lifts (algebraMap A B) := by
      refine (lifts_iff_coeff_lifts _).mpr fun i ↦ ?_
      rw [coeff_scaleRoots]
      rcases lt_or_ge i q.natDegree with hi | hi
      · obtain ⟨b, hb⟩ := hs i (Finset.mem_range.mpr hi)
        obtain ⟨k, hk⟩ : ∃ k, q.natDegree - i = k + 1 := ⟨_, (Nat.succ_pred_eq_of_pos
          (Nat.sub_pos_of_lt hi)).symm⟩
        refine ⟨b * (s : A) ^ k, ?_⟩
        rw [hk, map_mul, hb, map_pow, Algebra.smul_def]
        ring
      · rw [Nat.sub_eq_zero_of_le hi, pow_zero, mul_one]
        rcases hi.eq_or_lt with rfl | hi
        · exact ⟨1, by rw [map_one, hq.coeff_natDegree]⟩
        · exact ⟨0, by rw [map_zero, coeff_eq_zero_of_natDegree_lt hi]⟩
    obtain ⟨p, hpq, hpdeg, hp⟩ :=
      lifts_and_natDegree_eq_and_monic hlifts ((monic_scaleRoots_iff _).mpr hq)
    rw [natDegree_scaleRoots] at hpdeg
    obtain ⟨y, hy⟩ := exists_root p hp (hpdeg ▸ hdeg)
    refine ⟨IsLocalization.mk' B y s, (hu.pow q.natDegree).mul_right_eq_zero.mp ?_⟩
    rw [← scaleRoots_eval_mul, mul_comm, IsLocalization.mk'_spec, ← hpq]
    exact hy.map (algebraMap A B)

instance localization [IsAbsolutelyIntegrallyClosed A] (M : Submonoid A) :
    IsAbsolutelyIntegrallyClosed (Localization M) :=
  of_isLocalization M

/-- An arbitrary product of absolutely integrally closed rings is absolutely integrally closed:
find a root in each nontrivial factor. In particular a finite product of algebraically closed
fields is absolutely integrally closed, although it is not a domain. -/
instance pi {ι : Type*} {R : ι → Type*} [∀ i, CommRing (R i)]
    [∀ i, IsAbsolutelyIntegrallyClosed (R i)] : IsAbsolutelyIntegrallyClosed (∀ i, R i) where
  exists_root q hq hdeg := by
    have key (i : ι) : ∃ x, (q.map (Pi.evalRingHom R i)).IsRoot x := by
      obtain _ | _ := subsingleton_or_nontrivial (R i)
      · exact ⟨0, Subsingleton.elim _ _⟩
      · exact exists_root _ (hq.map _) ((hq.natDegree_map (Pi.evalRingHom R i)).symm ▸ hdeg)
    choose x hx using key
    refine ⟨x, funext fun i ↦ ?_⟩
    rw [Pi.zero_apply, ← Pi.evalRingHom_apply R i (eval x q), ← eval₂_hom, Pi.evalRingHom_apply,
      ← eval_map]
    exact hx i

end IsAbsolutelyIntegrallyClosed

/-- A ring is absolutely integrally closed if and only if every monic polynomial over it splits
into monic linear factors. -/
theorem isAbsolutelyIntegrallyClosed_iff_forall_splits :
    IsAbsolutelyIntegrallyClosed A ↔ ∀ p : A[X], p.Monic → p.Splits :=
  ⟨fun _ _ ↦ IsAbsolutelyIntegrallyClosed.splits, fun h ↦ ⟨fun p hp hdeg ↦
    (h p hp).exists_eval_eq_zero (natDegree_pos_iff_degree_pos.mp hdeg).ne'⟩⟩

/-- An algebraically closed field is absolutely integrally closed. -/
instance (priority := 100) IsAbsolutelyIntegrallyClosed.of_isAlgClosed {K : Type*} [Field K]
    [IsAlgClosed K] : IsAbsolutelyIntegrallyClosed K where
  exists_root p _ hdeg := IsAlgClosed.exists_root p (natDegree_pos_iff_degree_pos.mp hdeg).ne'

/-- A field is absolutely integrally closed if and only if it is algebraically closed. -/
theorem isAbsolutelyIntegrallyClosed_iff_isAlgClosed {K : Type*} [Field K] :
    IsAbsolutelyIntegrallyClosed K ↔ IsAlgClosed K :=
  ⟨fun _ ↦ IsAlgClosed.of_exists_root K fun p hp hirr ↦
    IsAbsolutelyIntegrallyClosed.exists_root p hp hirr.natDegree_pos, fun _ ↦ inferInstance⟩

/-- An absolutely integrally closed domain is integrally closed: an integral element of the
fraction field is a root of a monic polynomial over `A`, which is a product of linear factors
over `A`. -/
instance (priority := 100) IsAbsolutelyIntegrallyClosed.isIntegrallyClosed [IsDomain A]
    [IsAbsolutelyIntegrallyClosed A] : IsIntegrallyClosed A := by
  refine (isIntegrallyClosed_iff (FractionRing A)).mpr fun {x} ⟨p, hp, hpx⟩ ↦ ?_
  obtain ⟨m, hm⟩ := splits_iff_exists_multiset.mp (IsAbsolutelyIntegrallyClosed.splits hp)
  rw [hp.leadingCoeff, map_one, one_mul] at hm
  rw [hm, eval₂_multiset_prod, Multiset.prod_eq_zero_iff, Multiset.map_map,
    Multiset.mem_map] at hpx
  obtain ⟨a, -, ha⟩ := hpx
  exact ⟨a, (sub_eq_zero.mp (by simpa using ha)).symm⟩

section FractionRing

variable (K : Type*) [Field K] [Algebra A K] [IsFractionRing A K]

/-- The fraction field of an absolutely integrally closed domain is algebraically closed. -/
theorem IsAbsolutelyIntegrallyClosed.isAlgClosed [IsAbsolutelyIntegrallyClosed A] :
    IsAlgClosed K :=
  have := IsAbsolutelyIntegrallyClosed.of_isLocalization (B := K) (nonZeroDivisors A)
  isAbsolutelyIntegrallyClosed_iff_isAlgClosed.mp this

/-- An integrally closed domain with algebraically closed fraction field is absolutely integrally
closed: a monic polynomial over `A` has a root in the fraction field, which is integral over `A`
and hence lies in `A`. -/
theorem IsAbsolutelyIntegrallyClosed.of_isIntegrallyClosed_of_isAlgClosed [IsIntegrallyClosed A]
    [IsAlgClosed K] : IsAbsolutelyIntegrallyClosed A where
  exists_root p hp hdeg := by
    obtain ⟨x, hx⟩ := IsAlgClosed.exists_root (p.map (algebraMap A K))
      (natDegree_pos_iff_degree_pos.mp ((hp.natDegree_map (algebraMap A K)).symm ▸ hdeg)).ne'
    obtain ⟨y, rfl⟩ :=
      (isIntegrallyClosed_iff K).mp ‹IsIntegrallyClosed A› ⟨p, hp, by rwa [← eval_map]⟩
    refine ⟨y, IsFractionRing.injective A K ?_⟩
    simpa [eval_map, eval₂_at_apply] using hx

/-- A domain is absolutely integrally closed if and only if it is integrally closed and its
fraction field is algebraically closed. -/
theorem isAbsolutelyIntegrallyClosed_iff_isIntegrallyClosed_and_isAlgClosed :
    IsAbsolutelyIntegrallyClosed A ↔ IsIntegrallyClosed A ∧ IsAlgClosed K :=
  have := (IsFractionRing.isDomain_iff_isField (R := A) (K := K)).mpr (Field.toIsField K)
  ⟨fun _ ↦ ⟨inferInstance, IsAbsolutelyIntegrallyClosed.isAlgClosed (A := A) K⟩,
    fun ⟨_, _⟩ ↦ IsAbsolutelyIntegrallyClosed.of_isIntegrallyClosed_of_isAlgClosed K⟩

end FractionRing

/-- `ℚ` is not absolutely integrally closed: the monic polynomial `X ^ 2 - 2` has no rational
root. -/
theorem not_isAbsolutelyIntegrallyClosed_rat : ¬ IsAbsolutelyIntegrallyClosed ℚ := by
  intro h
  obtain ⟨x, hx⟩ := h.exists_root (X ^ 2 - C 2) (monic_X_pow_sub_C 2 two_ne_zero)
    (by rw [natDegree_X_pow_sub_C]; norm_num)
  have hx2 : x ^ 2 = 2 := by simpa [sub_eq_zero] using hx
  refine irrational_sqrt_two ⟨|x|, ?_⟩
  have hx2' : (x : ℝ) ^ 2 = 2 := by exact_mod_cast hx2
  rw [Rat.cast_abs, ← Real.sqrt_sq_eq_abs, hx2']

end TauCeti
