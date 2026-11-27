/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.Finite.Extension
import Mathlib.Data.Nat.ModEq

/-!
# The roots of an irreducible polynomial over a finite field, with multiplicity

Let `P` be irreducible of degree `d` over a finite field `k` with `q` elements, and let `x` be a
root of `P` in a field `K ⊇ k`. Then the roots of `P` in `K`, counted with multiplicity, are the
Frobenius conjugates `x, x ^ q, …, x ^ q ^ (d - 1)`, and those of `P ^ j` are
`x ^ q ^ i` for `i < j d`.

## Main results

* `TauCeti.FiniteField.pow_card_pow_eq_self_iff`: `x ^ q ^ n = x` if and only if `d ∣ n`.
* `TauCeti.FiniteField.aroots_eq_map_pow_card_pow`: the roots of `P` are `x ^ q ^ i`, `i < d`.
* `TauCeti.FiniteField.aroots_pow_eq_map_pow_card_pow`: the roots of `P ^ j` are `x ^ q ^ i`,
  `i < deg (P ^ j)`.

## References

* Adapted from `src/Lib/General/NumberTheory/FrobeniusOrbits.lean` in grh-lean
  (https://github.com/lsernau/grh-lean, Apache 2.0, Copyright 2026 Anthropic PBC):
  `New.root_pow_card_pow_eq_self_iff`, `New.root_pow_card_pow_eq_iff_modEq`,
  `New.aroots_eq_frobenius_orbit` and `New.aroots_pow_eq_frobenius_orbit`. See also
  `TauCeti.FiniteField.orbit_eq_rootSet_minpoly` for the root set as an orbit.
-/

public section

open Polynomial

namespace TauCeti.FiniteField

variable {k K : Type*} [Field k] [Fintype k] [Field K] [Algebra k K] {P : k[X]}
  (hP : Irreducible P) {x : K} (hx : aeval x P = 0)

include hP hx

/-- `x ^ q ^ n = x` if and only if the degree of `P` divides `n`. -/
theorem pow_card_pow_eq_self_iff {n : ℕ} : x ^ Fintype.card k ^ n = x ↔ P.natDegree ∣ n := by
  rw [hP.natDegree_dvd_iff_dvd_X_pow_card_pow_sub_X, ← hP.dvd_iff_aeval_eq_zero hx]
  simp [sub_eq_zero, Nat.card_eq_fintype_card]

/-- `x ^ q ^ a = x ^ q ^ b` if and only if `a ≡ b` modulo the degree of `P`. -/
theorem pow_card_pow_eq_pow_card_pow_iff {a b : ℕ} :
    x ^ Fintype.card k ^ a = x ^ Fintype.card k ^ b ↔ a ≡ b [MOD P.natDegree] := by
  -- The Frobenius is injective: cancel it until one exponent is `0`.
  have h_inj {u v : K} : u ^ Fintype.card k = v ^ Fintype.card k ↔ u = v := by
    simpa [_root_.FiniteField.coe_frobeniusAlgHom] using
      (_root_.FiniteField.frobeniusAlgHom k K).injective.eq_iff (a := u) (b := v)
  induction a, b using Nat.recDiagAux with
  | zero_left n =>
    simpa [eq_comm, Nat.modEq_iff_dvd' n.zero_le] using pow_card_pow_eq_self_iff hP hx
  | zero_right m => simpa [Nat.modEq_zero_iff_dvd] using pow_card_pow_eq_self_iff hP hx
  | succ_succ m n ih =>
    simp only [pow_succ, pow_mul, h_inj, ih, Nat.ModEq.add_iff_right (.refl 1)]

/-- The roots of `P` in `K`, with multiplicity, are `x ^ q ^ i` for `i < deg P`. -/
theorem aroots_eq_map_pow_card_pow :
    P.aroots K = (Multiset.range P.natDegree).map fun i ↦ x ^ Fintype.card k ^ i := by
  -- The `x ^ q ^ i` are roots, images of `x` under powers of the Frobenius, and distinct for
  -- `i < deg P`; there are `deg P` of them.
  have h_root (i : ℕ) : aeval (x ^ Fintype.card k ^ i) P = 0 := by
    simpa [_root_.FiniteField.coe_frobeniusAlgHom, hx] using
      aeval_algHom_apply (_root_.FiniteField.frobeniusAlgHom k K ^ i) x P
  have h_nodup : ((Multiset.range P.natDegree).map fun i ↦ x ^ Fintype.card k ^ i).Nodup :=
    (Multiset.nodup_range P.natDegree).map_on fun a ha b hb h_eq ↦
      ((pow_card_pow_eq_pow_card_pow_iff hP hx).1 h_eq).eq_of_lt_of_lt
        (Multiset.mem_range.1 ha) (Multiset.mem_range.1 hb)
  have h_le : ((Multiset.range P.natDegree).map fun i ↦ x ^ Fintype.card k ^ i) ≤ P.aroots K :=
    (Multiset.le_iff_subset h_nodup).2
      (by simpa [Multiset.subset_iff, hP.ne_zero] using fun i _ ↦ h_root i)
  exact (Multiset.eq_of_le_of_card_le h_le
    (by simpa using card_roots' (P.map (algebraMap k K)))).symm

/-- The roots of `P ^ j` in `K`, with multiplicity, are `x ^ q ^ i` for `i < deg (P ^ j)`. -/
theorem aroots_pow_eq_map_pow_card_pow (j : ℕ) :
    (P ^ j).aroots K =
      (Multiset.range (P ^ j).natDegree).map (fun i ↦ x ^ Fintype.card k ^ i) := by
  -- The roots of `P` form one Frobenius orbit, which each further factor `P` repeats.
  have h_fixed (j : ℕ) : x ^ Fintype.card k ^ (j * P.natDegree) = x :=
    (pow_card_pow_eq_self_iff hP hx).2 (dvd_mul_left P.natDegree j)
  rw [natDegree_pow]
  induction j with
  | zero => simp
  | succ j ih =>
    rw [pow_succ, aroots_mul (by simp [hP.ne_zero]), ih, aroots_eq_map_pow_card_pow hP hx]
    simp only [add_one_mul, Multiset.range_add, Multiset.map_add, Multiset.map_map,
      Function.comp_def, pow_add, pow_mul x, h_fixed]

end TauCeti.FiniteField
