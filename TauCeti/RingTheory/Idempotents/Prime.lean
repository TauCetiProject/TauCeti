/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.LocalizedModule.Basic
public import Mathlib.Algebra.Module.Submodule.Pointwise
public import Mathlib.Algebra.Ring.Idempotent
public import Mathlib.RingTheory.Ideal.Prime
import TauCeti.RingTheory.Idempotents.Module

/-!
# Idempotents and prime ideals

An idempotent `e` and its complement `1 - e` multiply to `0` and add up to `1`, so a prime ideal
contains exactly one of them. On the prime spectrum of a commutative ring this says that the basic
open sets of `e` and `1 - e` are complementary. In particular, at a prime containing `e` the
complement `1 - e` becomes a unit, so the piece `e • M` of a module localizes to zero there.

## Main results

* `IsIdempotentElem.one_sub_mem_iff_notMem`: a prime ideal contains exactly one of `e` and
  `1 - e`.
* `IsIdempotentElem.subsingleton_localizedModule_smul_top`: the piece `e • M` localizes to zero at
  a prime containing `e`.
-/

public section

open scoped Pointwise

/-- A prime ideal contains exactly one of an idempotent `e` and its complement `1 - e`. -/
theorem IsIdempotentElem.one_sub_mem_iff_notMem {R : Type*} [Ring R] {e : R}
    (he : IsIdempotentElem e) {P : Ideal R} [hP : P.IsPrime] : 1 - e ∈ P ↔ e ∉ P := by
  refine ⟨fun h he' ↦ hP.ne_top ((Ideal.eq_top_iff_one _).2 (by simpa using P.add_mem he' h)),
    fun h ↦ (hP.mem_or_mem ?_).resolve_left h⟩
  rw [he.mul_one_sub_self]
  exact P.zero_mem

/-- **The piece cut out by an idempotent vanishes at primes containing it**: if `e ∈ P` then the
localization of `e • M` at `P` is zero, because `1 - e ∉ P` and `1 - e` kills `e • M`. -/
theorem IsIdempotentElem.subsingleton_localizedModule_smul_top {R M : Type*} [CommRing R]
    [AddCommMonoid M] [Module R M] {e : R} (he : IsIdempotentElem e) {P : Ideal R} [P.IsPrime]
    (hP : e ∈ P) :
    Subsingleton (LocalizedModule P.primeCompl ↥(e • (⊤ : Submodule R M))) := by
  refine LocalizedModule.subsingleton_iff.2 fun x ↦
    ⟨1 - e, he.one_sub_mem_iff_notMem.not.2 (not_not.2 hP), Subtype.ext ?_⟩
  rw [Submodule.coe_smul, ← he.smul_eq_self_of_mem_smul_top x.property, smul_smul,
    he.one_sub_mul_self, zero_smul, ZeroMemClass.coe_zero]
