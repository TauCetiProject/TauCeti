/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.IsSepClosed
public import TauCeti.FieldTheory.RatFunc.Specialization
import Mathlib.FieldTheory.KummerPolynomial
import TauCeti.FieldTheory.FunctionField.Place.RatFunc.XPowSubCX

/-!
# Hilbert sets and Hilbertian fields

A field `K` is *Hilbertian* if every finite family of irreducible separable polynomials
`p(T, Y) ∈ K(T)[Y]` has a common parameter `t ∈ K` at which every coefficient is regular, the
degree in `Y` is preserved, and every specialization `p(t, Y) ∈ K[Y]` is irreducible. This is the
polynomial form, on the affine line, of the Hilbert property used to pass from regular Galois
extensions of `K(T)` to Galois extensions of `K` with the same group. Hilbert's irreducibility
theorem says that number fields are Hilbertian, and rational function fields `K(T)` are Hilbertian
over every field `K`; neither theorem is proved here.

This file defines the Hilbert set of a family of polynomials and the predicate `IsHilbertian`, and
proves the elementary consequences of the definition. A nonzero polynomial `g ∈ K[T]` can be
adjoined to any family through the linear polynomial `Y - 1/g`, whose Hilbert set is exactly the
set where `g` does not vanish. Hence over a Hilbertian field the Hilbert set of a family meets
the complement of the zeros of any nonzero `g` and of any finite set, so it is infinite, and a
Hilbertian field is infinite. The Hilbert set of `Y ^ n - T` consists of parameters that are not
`n`-th powers, so a separably closed field is not Hilbertian.

## Main definitions

* `TauCeti.RationalSpecialization.hilbertSet s`: the parameters `t ∈ K` at which every member of
  `s ⊆ K(T)[Y]` has regular coefficients, keeps its degree and has irreducible specialization.
* `TauCeti.IsHilbertian K`: every finite family of irreducible separable polynomials in `K(T)[Y]`
  has nonempty Hilbert set.

## Main results

* `TauCeti.RationalSpecialization.mem_hilbertSet_singleton_iff`: `t` lies in the Hilbert set of
  `p` exactly when the specialization guard of `p` does not vanish at `t` and `p(t, Y)` is
  irreducible.
* `TauCeti.RationalSpecialization.hilbertSet_singleton_X_sub_C`: the Hilbert set of `Y - f` is
  the set where `f` is regular.
* `TauCeti.RationalSpecialization.mem_hilbertSet_singleton_X_pow_sub_C_X_iff_of_prime`: for a
  prime `q`, the Hilbert set of `Y ^ q - T` is the set of non-`q`-th powers.
* `TauCeti.IsHilbertian.exists_notMem_eval_ne_zero_mem_hilbertSet`: over a Hilbertian field,
  every admissible family has a common parameter outside a prescribed finite set at which a
  prescribed nonzero polynomial does not vanish.
* `TauCeti.isHilbertian_iff_forall_infinite_hilbertSet`: a field is Hilbertian exactly when every
  admissible family has an infinite Hilbert set; in particular a Hilbertian field is infinite
  (`TauCeti.IsHilbertian.infinite`).
* `TauCeti.isHilbertian_iff_of_charZero`: in characteristic zero the separability condition is
  automatic.
* `TauCeti.IsHilbertian.infinite_setOf_forall_pow_ne` and
  `TauCeti.not_isHilbertian_of_isSepClosed`: a Hilbertian field has infinitely many non-`n`-th
  powers for every `n ≠ 1` invertible in it, and a separably closed field is not Hilbertian.

## References

* P. Dèbes, *Arithmétique des revêtements de la droite*, §5.2.1, Définition 5.2.2.
* J.-P. Serre, *Topics in Galois Theory*, §3.1.
* M. Fried, M. Jarden, *Field Arithmetic*, 3rd ed., §§12.1 and 13.4.
-/

public section

noncomputable section

open Polynomial

namespace TauCeti

namespace RationalSpecialization

variable {K : Type*} [Field K]

/-- The **Hilbert set** of a family `s` of polynomials in `K(T)[Y]`: the parameters `t ∈ K` at
which every member of `s` has coefficients regular at `t`, keeps its degree in `Y` under
specialization, and has irreducible specialization `p(t, Y) ∈ K[Y]`. -/
def hilbertSet (s : Set (RatFunc K)[X]) : Set K :=
  {t | ∀ p ∈ s, (∀ n, (p.coeff n).denom.eval t ≠ 0) ∧
    (specialize t p).natDegree = p.natDegree ∧ Irreducible (specialize t p)}

@[simp]
theorem mem_hilbertSet {s : Set (RatFunc K)[X]} {t : K} :
    t ∈ hilbertSet s ↔ ∀ p ∈ s, (∀ n, (p.coeff n).denom.eval t ≠ 0) ∧
      (specialize t p).natDegree = p.natDegree ∧ Irreducible (specialize t p) :=
  Iff.rfl

@[simp]
theorem hilbertSet_empty : hilbertSet (∅ : Set (RatFunc K)[X]) = Set.univ := by
  ext; simp

/-- Enlarging the family shrinks its Hilbert set. -/
theorem hilbertSet_anti : Antitone (hilbertSet (K := K)) :=
  fun _ _ hst _ ht p hp ↦ ht p (hst hp)

theorem hilbertSet_union (s s' : Set (RatFunc K)[X]) :
    hilbertSet (s ∪ s') = hilbertSet s ∩ hilbertSet s' := by
  ext t
  simp only [Set.mem_inter_iff, mem_hilbertSet, Set.mem_union]
  exact ⟨fun h ↦ ⟨fun p hp ↦ h p (.inl hp), fun p hp ↦ h p (.inr hp)⟩,
    fun h p hp ↦ hp.elim (h.1 p) (h.2 p)⟩

theorem hilbertSet_insert (p : (RatFunc K)[X]) (s : Set (RatFunc K)[X]) :
    hilbertSet (insert p s) = hilbertSet {p} ∩ hilbertSet s := by
  rw [Set.insert_eq, hilbertSet_union]

/-- **The polynomial Hilbert set and the specialization guard.** A parameter `t` lies in the
Hilbert set of `p` exactly when the guard `D(p) · num(lc(p))` does not vanish at `t` and the
specialization `p(t, Y)` is irreducible. -/
theorem mem_hilbertSet_singleton_iff {p : (RatFunc K)[X]} {t : K} :
    t ∈ hilbertSet {p} ↔ (specializationGuard p).eval t ≠ 0 ∧ Irreducible (specialize t p) := by
  simp only [mem_hilbertSet, Set.mem_singleton_iff, forall_eq]
  refine ⟨fun ⟨hden, hdeg, hirr⟩ ↦ ⟨?_, hirr⟩, fun ⟨hg, hirr⟩ ↦
    ⟨eval_denom_coeff_ne_zero_of_eval_specializationGuard_ne_zero hg,
      natDegree_specialize_of_eval_specializationGuard_ne_zero hg, hirr⟩⟩
  -- The value of the leading coefficient of `p` is the leading coefficient of `p(t, Y)`, which
  -- is nonzero, so the numerator of `lc(p)` does not vanish at `t`.
  have hlc : RatFunc.eval (RingHom.id K) t p.leadingCoeff ≠ 0 := by
    rw [leadingCoeff, ← coeff_specialize, ← hdeg]
    exact leadingCoeff_ne_zero.mpr hirr.ne_zero
  rw [RatFunc.eval_id_eq_div] at hlc
  rw [specializationGuard_def, eval_mul]
  exact mul_ne_zero (eval_denomProduct_ne_zero_iff.mpr hden) fun h ↦ hlc (by rw [h, zero_div])

/-- The Hilbert set of the linear polynomial `Y - f` is the set of parameters at which `f` is
regular. -/
theorem hilbertSet_singleton_X_sub_C (f : RatFunc K) :
    hilbertSet {X - C f} = {t | f.denom.eval t ≠ 0} := by
  ext t
  simp only [mem_hilbertSet, Set.mem_singleton_iff, forall_eq, Set.mem_ofPred_eq,
    natDegree_X_sub_C]
  -- The leading coefficient `1` has value `1`, so the specialization has degree one.
  have hdeg : (specialize t (X - C f)).natDegree = 1 := by
    rw [natDegree_specialize_of_eval_leadingCoeff_ne_zero (by simp), natDegree_X_sub_C]
  have hirr : Irreducible (specialize t (X - C f)) :=
    irreducible_of_degree_eq_one (degree_eq_iff_natDegree_eq_of_pos one_pos |>.mpr hdeg)
  simp_rw [← mem_regularSubring_iff]
  refine ⟨fun h ↦ ?_, fun h ↦ ⟨fun n ↦ ?_, hdeg, hirr⟩⟩
  · simpa using h.1 0
  · rw [coeff_sub]
    refine sub_mem ?_ ?_
    · rw [coeff_X]
      split_ifs <;> simp
    · rw [coeff_C]
      split_ifs
      exacts [h, zero_mem _]

/-- The Hilbert set of `Y - 1/h` for a nonzero polynomial `h ∈ K[T]` is the set of parameters at
which `h` does not vanish. Adjoining this polynomial to a family imposes the condition
`h(t) ≠ 0`. -/
theorem hilbertSet_singleton_X_sub_C_inv_algebraMap {h : K[X]} (hh : h ≠ 0) :
    hilbertSet {X - C (algebraMap K[X] (RatFunc K) h)⁻¹} = {t | h.eval t ≠ 0} := by
  ext t
  rw [hilbertSet_singleton_X_sub_C, Set.mem_ofPred_eq, Set.mem_ofPred_eq,
    ← mem_regularSubring_iff, inv_algebraMap_mem_regularSubring_iff hh]

/-- The Hilbert set of `Y ^ n - T` is the set of parameters `t` for which `Y ^ n - t` is
irreducible. -/
theorem mem_hilbertSet_singleton_X_pow_sub_C_X_iff {n : ℕ} {t : K} :
    t ∈ hilbertSet {X ^ n - C (RatFunc.X : RatFunc K)} ↔ Irreducible (X ^ n - C t) := by
  have hmap : (X ^ n - C (RatFunc.X : RatFunc K)) =
      (X ^ n - C X : K[X][X]).map (algebraMap K[X] (RatFunc K)) := by
    simp [RatFunc.algebraMap_X]
  -- The coefficients are polynomials in `T`, regular everywhere, and both degrees are `n`.
  simp only [mem_hilbertSet, Set.mem_singleton_iff, forall_eq, hmap, coeff_map,
    RatFunc.denom_algebraMap, eval_one, specialize_map_algebraMap]
  simp

/-- For a prime `q`, the Hilbert set of `Y ^ q - T` is the set of parameters that are not `q`-th
powers in `K`. -/
theorem mem_hilbertSet_singleton_X_pow_sub_C_X_iff_of_prime {q : ℕ} (hq : q.Prime) {t : K} :
    t ∈ hilbertSet {X ^ q - C (RatFunc.X : RatFunc K)} ↔ ∀ b : K, b ^ q ≠ t := by
  rw [mem_hilbertSet_singleton_X_pow_sub_C_X_iff, irreducible_X_pow_sub_C_iff_of_prime hq]

end RationalSpecialization

open RationalSpecialization

/-- A field `K` is **Hilbertian** if every finite family of irreducible separable polynomials in
`K(T)[Y]` has a common parameter `t ∈ K` at which every coefficient of every member is regular,
the degree in `Y` is preserved, and every specialization is irreducible in `K[Y]`. This is the
polynomial form, on the affine line, of the Hilbert property; positivity of the degrees is
automatic for irreducible polynomials. A finite set of excluded parameters and a nonzero guard
`g(t) ≠ 0` can be imposed as well (`IsHilbertian.exists_notMem_eval_ne_zero_mem_hilbertSet`). -/
def IsHilbertian (K : Type*) [Field K] : Prop :=
  ∀ s : Finset (RatFunc K)[X], (∀ p ∈ s, Irreducible p ∧ p.Separable) →
    (hilbertSet (s : Set (RatFunc K)[X])).Nonempty

variable {K : Type*} [Field K]

theorem isHilbertian_iff : IsHilbertian K ↔ ∀ s : Finset (RatFunc K)[X],
    (∀ p ∈ s, Irreducible p ∧ p.Separable) → (hilbertSet (s : Set (RatFunc K)[X])).Nonempty :=
  Iff.rfl

/-- In characteristic zero every irreducible polynomial over `K(T)` is separable, so `K` is
Hilbertian exactly when every finite family of irreducible polynomials has nonempty Hilbert
set. -/
theorem isHilbertian_iff_of_charZero [CharZero K] : IsHilbertian K ↔
    ∀ s : Finset (RatFunc K)[X], (∀ p ∈ s, Irreducible p) →
      (hilbertSet (s : Set (RatFunc K)[X])).Nonempty :=
  ⟨fun hK s hs ↦ hK s fun p hp ↦ ⟨hs p hp, (hs p hp).separable⟩,
    fun hK s hs ↦ hK s fun p hp ↦ (hs p hp).1⟩

namespace IsHilbertian

/-- **Finite avoidance and guards.** Over a Hilbertian field, every finite family of irreducible
separable polynomials in `K(T)[Y]` has a common parameter `t`, outside any prescribed finite set
`A`, at which a prescribed nonzero polynomial `g ∈ K[T]` does not vanish, every coefficient is
regular, every degree is preserved and every specialization is irreducible. -/
theorem exists_notMem_eval_ne_zero_mem_hilbertSet (hK : IsHilbertian K)
    {s : Finset (RatFunc K)[X]} (hs : ∀ p ∈ s, Irreducible p ∧ p.Separable) {g : K[X]}
    (hg : g ≠ 0) {A : Set K} (hA : A.Finite) :
    ∃ t ∉ A, g.eval t ≠ 0 ∧ t ∈ hilbertSet (s : Set (RatFunc K)[X]) := by
  classical
  -- The guard `h = g · ∏_{a ∈ A} (T - a)` vanishes on `A` and at the roots of `g`; adjoin the
  -- linear polynomial `Y - 1/h`, whose Hilbert set is the complement of the zeros of `h`.
  set h : K[X] := g * ∏ a ∈ hA.toFinset, (X - C a) with h_def
  have hh : h ≠ 0 :=
    mul_ne_zero hg (Finset.prod_ne_zero_iff.mpr fun a _ ↦ X_sub_C_ne_zero a)
  set q : (RatFunc K)[X] := X - C (algebraMap K[X] (RatFunc K) h)⁻¹
  obtain ⟨t, ht⟩ := hK (insert q s) (by
    simpa [q, irreducible_X_sub_C, separable_X_sub_C] using hs)
  rw [Finset.coe_insert, hilbertSet_insert, hilbertSet_singleton_X_sub_C_inv_algebraMap hh] at ht
  obtain ⟨hht, hts⟩ := ht
  rw [Set.mem_ofPred_eq, h_def, eval_mul, eval_prod] at hht
  refine ⟨t, fun htA ↦ ?_, left_ne_zero_of_mul hht, hts⟩
  exact Finset.prod_ne_zero_iff.mp (right_ne_zero_of_mul hht) t (hA.mem_toFinset.mpr htA)
    (by simp)

/-- Over a Hilbertian field the Hilbert set of every finite family of irreducible separable
polynomials in `K(T)[Y]` is infinite. -/
theorem infinite_hilbertSet (hK : IsHilbertian K) {s : Finset (RatFunc K)[X]}
    (hs : ∀ p ∈ s, Irreducible p ∧ p.Separable) :
    (hilbertSet (s : Set (RatFunc K)[X])).Infinite := fun hfin ↦ by
  obtain ⟨t, htA, -, ht⟩ := hK.exists_notMem_eval_ne_zero_mem_hilbertSet hs one_ne_zero hfin
  exact htA ht

/-- A Hilbertian field is infinite: the Hilbert set of the empty family is the whole field. -/
theorem infinite (hK : IsHilbertian K) : Infinite K :=
  Set.infinite_univ_iff.mp (by simpa using hK.infinite_hilbertSet (s := ∅) (by simp))

/-- A Hilbertian field has infinitely many elements that are not `n`-th powers, for every
`n ≠ 1` invertible in it: they contain the Hilbert set of `Y ^ n - T`. -/
theorem infinite_setOf_forall_pow_ne (hK : IsHilbertian K) {n : ℕ} (hn : n ≠ 1)
    (hnK : (n : K) ≠ 0) : {t : K | ∀ b : K, b ^ n ≠ t}.Infinite := by
  have := NeZero.mk (fun h : n = 0 ↦ hnK (by rw [h, Nat.cast_zero]))
  have hsep : (X ^ n - C (RatFunc.X : RatFunc K)).Separable := by
    refine separable_X_pow_sub_C _ ?_ RatFunc.X_ne_zero
    rwa [← map_natCast (algebraMap K (RatFunc K)), _root_.map_ne_zero]
  refine (hK.infinite_hilbertSet (s := {X ^ n - C RatFunc.X})
    (by simpa using ⟨irreducible_X_pow_sub_C_X K n, hsep⟩)).mono fun t ht ↦ ?_
  rw [Finset.coe_singleton, mem_hilbertSet_singleton_X_pow_sub_C_X_iff] at ht
  exact pow_ne_of_irreducible_X_pow_sub_C ht dvd_rfl hn

end IsHilbertian

/-- A field is Hilbertian exactly when the Hilbert set of every finite family of irreducible
separable polynomials in `K(T)[Y]` is infinite. -/
theorem isHilbertian_iff_forall_infinite_hilbertSet : IsHilbertian K ↔
    ∀ s : Finset (RatFunc K)[X], (∀ p ∈ s, Irreducible p ∧ p.Separable) →
      (hilbertSet (s : Set (RatFunc K)[X])).Infinite :=
  ⟨fun hK _ hs ↦ hK.infinite_hilbertSet hs, fun h s hs ↦ (h s hs).nonempty⟩

/-- A separably closed field is not Hilbertian: every element is an `n`-th power for `n = 2` or
`n = 3`, one of which is invertible in it, so the Hilbert set of `Y ^ n - T` is empty. In
particular algebraically closed fields such as `ℂ` are not Hilbertian. -/
theorem not_isHilbertian_of_isSepClosed [IsSepClosed K] : ¬ IsHilbertian K := by
  intro hK
  -- One of `2` and `3` is invertible in `K`, since `3 - 2 = 1`.
  obtain ⟨n, hn, hnK⟩ : ∃ n : ℕ, n ≠ 1 ∧ (n : K) ≠ 0 := by
    by_cases h2 : (2 : K) = 0
    · refine ⟨3, by norm_num, fun h3 ↦ one_ne_zero (α := K) ?_⟩
      linear_combination (norm := (push_cast; ring_nf)) h3 - h2
    · exact ⟨2, by norm_num, by exact_mod_cast h2⟩
  have := NeZero.mk hnK
  obtain ⟨t, ht⟩ := (hK.infinite_setOf_forall_pow_ne hn hnK).nonempty
  obtain ⟨b, hb⟩ := IsSepClosed.exists_pow_nat_eq t n
  exact ht b hb

end TauCeti
