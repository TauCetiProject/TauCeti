/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.RingTheory.Algebraic.Defs
public import Mathlib.RingTheory.Jacobson.Ideal
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Tactic.LinearCombination
import TauCeti.RingTheory.Algebraic.Basic
import TauCeti.RingTheory.Idempotents.Jacobson
import TauCeti.RingTheory.Jacobson.Basic

/-!
# Idempotents from algebraic elements

Let `x` be an element of an algebra over a field `K`, algebraic over `K` and not nilpotent. Write
a nonzero polynomial annihilating `x` and divisible by `X` as `X ^ k * g` with `k ≥ 1` and
`g (0) ≠ 0`. As `X ^ k` and `g` are coprime, `a * X ^ k + b * g = 1` for some polynomials `a` and
`b`, and `e = a (x) * x ^ k` is an idempotent of the form `p (x) * x`. It is nonzero, for
otherwise `b (x) * g (x) = 1` would force `x ^ k = 0`.

A left ideal consisting of nilpotent elements lies in the Jacobson radical, so a left ideal of
algebraic elements lies in the radical exactly when its only idempotent is `0`. Every element of
a finite-dimensional left ideal is algebraic, so this applies to finite-dimensional left ideals.
In a semisimple algebra, meaning one with zero Jacobson radical, every nonzero finite-dimensional
left ideal contains a nonzero idempotent. This is the source of the idempotents in the structure
theory of separating ideals of Banach algebras.

## Main results

* `IsAlgebraic.exists_isIdempotentElem_aeval_mul_ne_zero`: an algebraic element `x` that is not
  nilpotent has a multiple `p (x) * x` that is a nonzero idempotent.
* `Submodule.exists_isIdempotentElem_ne_zero_mem_of_isAlgebraic`: a left ideal of algebraic
  elements not contained in the Jacobson radical contains a nonzero idempotent.
* `Submodule.exists_isIdempotentElem_ne_zero_mem`: a finite-dimensional left ideal not contained
  in the Jacobson radical contains a nonzero idempotent.
* `Submodule.le_jacobson_iff_forall_isIdempotentElem_eq_zero_of_isAlgebraic`: a left ideal of
  algebraic elements lies in the Jacobson radical exactly when its only idempotent is `0`.
* `Submodule.le_jacobson_iff_forall_isIdempotentElem_eq_zero`: a finite-dimensional left ideal
  lies in the Jacobson radical exactly when its only idempotent is `0`.
* `Submodule.exists_isIdempotentElem_ne_zero_mem_of_jacobson_eq_bot`: in an algebra with zero
  Jacobson radical, every nonzero finite-dimensional left ideal contains a nonzero idempotent.

## References

* H. G. Dales, *Banach Algebras and Automatic Continuity*, §1.5, for the idempotents of
  finite-dimensional ideals, and §5.2, for their use in the structure of separating ideals.
* T. Y. Lam, *A First Course in Noncommutative Rings*, §4: nil one-sided ideals lie in the
  Jacobson radical.
-/

public section

open Polynomial

variable {K B : Type*} [Field K] [Ring B] [Algebra K B]

namespace IsAlgebraic

/-- **Idempotents from algebraic elements.** If `x` is algebraic over a field `K` and not
nilpotent, then for some polynomial `p` over `K` the element `p (x) * x` is a nonzero
idempotent. -/
theorem exists_isIdempotentElem_aeval_mul_ne_zero {x : B} (hx : IsAlgebraic K x)
    (hnil : ¬ IsNilpotent x) :
    ∃ p : K[X], IsIdempotentElem (aeval x p * x) ∧ aeval x p * x ≠ 0 := by
  obtain ⟨q, hq0, hq⟩ := hx
  -- Split `X * q`, which annihilates `x`, as `X ^ k * g` with `k ≥ 1` and `X ∤ g`.
  have hf0 : X * q ≠ 0 := mul_ne_zero X_ne_zero hq0
  obtain ⟨g, hfg, hg⟩ := exists_eq_pow_rootMultiplicity_mul_and_not_dvd (X * q) hf0 0
  set k := (X * q).rootMultiplicity 0
  rw [map_zero, sub_zero] at hfg hg
  have hk : k ≠ 0 := ((rootMultiplicity_pos hf0).2 (by simp)).ne'
  have hxg : aeval x (X ^ k * g) = 0 := by rw [← hfg, map_mul, hq, mul_zero]
  obtain ⟨a, b, hab⟩ := ((prime_X.coprime_iff_not_dvd).2 hg).pow_left (m := k)
  have he : aeval x (a * X ^ (k - 1)) * x = aeval x (a * X ^ k) := by
    simp [mul_assoc, pow_sub_one_mul hk]
  refine ⟨a * X ^ (k - 1), ?_, ?_⟩ <;> rw [he]
  ·-- `a X ^ k (1 - a X ^ k) = a b X ^ k g` vanishes at `x`.
    have h : a * X ^ k * (a * X ^ k) = a * X ^ k - a * b * (X ^ k * g) := by
      linear_combination (a * X ^ k) * hab
    rw [IsIdempotentElem, ← map_mul, h, map_sub, map_mul (aeval x) (a * b), hxg, mul_zero,
      sub_zero]
  · -- Otherwise `x ^ k = x ^ k * (a (x) * x ^ k) + b (x) * x ^ k * g (x) = 0`.
    intro he
    refine hnil ⟨k, ?_⟩
    have h : X ^ k = X ^ k * (a * X ^ k) + b * (X ^ k * g) := by
      linear_combination (-X ^ k : K[X]) * hab
    simpa [he, hxg] using congrArg (aeval x) h

end IsAlgebraic

namespace Submodule

/-- **Idempotents in left ideals outside the radical.** A left ideal `J` of an algebra `B` over a
field, given as a scalar submodule closed under left multiplication, whose elements are algebraic
and which is not contained in the Jacobson radical of `B` contains a nonzero idempotent. -/
theorem exists_isIdempotentElem_ne_zero_mem_of_isAlgebraic (J : Submodule K B)
    (hJ : ∀ (b : B) {y : B}, y ∈ J → b * y ∈ J) (halg : ∀ y ∈ J, IsAlgebraic K y)
    (hrad : ¬ J ≤ (Ring.jacobson B).restrictScalars K) :
    ∃ e ∈ J, IsIdempotentElem e ∧ e ≠ 0 := by
  -- A left ideal of nilpotent elements lies in the radical.
  obtain ⟨x, hxJ, hnil⟩ : ∃ x ∈ J, ¬ IsNilpotent x := by
    by_contra! h
    exact hrad fun x hx ↦ TauCeti.Ring.mem_jacobson_of_forall_isNilpotent_mul fun y ↦
      h _ (hJ y hx)
  obtain ⟨q, he, he0⟩ := (halg x hxJ).exists_isIdempotentElem_aeval_mul_ne_zero hnil
  exact ⟨_, hJ _ hxJ, he, he0⟩

/-- **Idempotents in finite-dimensional left ideals.** A finite-dimensional left ideal `J` of an
algebra `B` over a field, given as a scalar submodule closed under left multiplication, that is
not contained in the Jacobson radical of `B` contains a nonzero idempotent. -/
theorem exists_isIdempotentElem_ne_zero_mem (J : Submodule K B) [FiniteDimensional K J]
    (hJ : ∀ (b : B) {y : B}, y ∈ J → b * y ∈ J)
    (hrad : ¬ J ≤ (Ring.jacobson B).restrictScalars K) :
    ∃ e ∈ J, IsIdempotentElem e ∧ e ≠ 0 :=
  J.exists_isIdempotentElem_ne_zero_mem_of_isAlgebraic hJ (fun _ ↦ J.isAlgebraic_of_mem hJ) hrad

/-- A left ideal of algebraic elements of an algebra over a field, given as a scalar submodule
closed under left multiplication, lies in the Jacobson radical exactly when its only idempotent is
`0`. -/
theorem le_jacobson_iff_forall_isIdempotentElem_eq_zero_of_isAlgebraic (J : Submodule K B)
    (hJ : ∀ (b : B) {y : B}, y ∈ J → b * y ∈ J) (halg : ∀ y ∈ J, IsAlgebraic K y) :
    J ≤ (Ring.jacobson B).restrictScalars K ↔ ∀ e ∈ J, IsIdempotentElem e → e = 0 := by
  refine ⟨fun h e he hidem ↦ hidem.eq_zero_of_mem_jacobson_bot ?_, fun h ↦ ?_⟩
  · rw [Ideal.jacobson_bot]
    exact (restrictScalars_mem K _ e).1 (h he)
  · by_contra hrad
    obtain ⟨e, he, hidem, he0⟩ := J.exists_isIdempotentElem_ne_zero_mem_of_isAlgebraic hJ halg hrad
    exact he0 (h e he hidem)

/-- A finite-dimensional left ideal of an algebra over a field, given as a scalar submodule closed
under left multiplication, lies in the Jacobson radical exactly when its only idempotent is `0`. -/
theorem le_jacobson_iff_forall_isIdempotentElem_eq_zero (J : Submodule K B)
    [FiniteDimensional K J] (hJ : ∀ (b : B) {y : B}, y ∈ J → b * y ∈ J) :
    J ≤ (Ring.jacobson B).restrictScalars K ↔ ∀ e ∈ J, IsIdempotentElem e → e = 0 :=
  J.le_jacobson_iff_forall_isIdempotentElem_eq_zero_of_isAlgebraic hJ
    fun _ ↦ J.isAlgebraic_of_mem hJ

/-- In an algebra over a field with zero Jacobson radical, every nonzero finite-dimensional left
ideal, given as a scalar submodule closed under left multiplication, contains a nonzero
idempotent. -/
theorem exists_isIdempotentElem_ne_zero_mem_of_jacobson_eq_bot (J : Submodule K B)
    [FiniteDimensional K J] (hJ : ∀ (b : B) {y : B}, y ∈ J → b * y ∈ J)
    (hB : Ring.jacobson B = ⊥) (hJ0 : J ≠ ⊥) : ∃ e ∈ J, IsIdempotentElem e ∧ e ≠ 0 :=
  J.exists_isIdempotentElem_ne_zero_mem hJ fun h ↦ hJ0 <| eq_bot_iff.2 <| by
    simpa [hB] using h

end Submodule
