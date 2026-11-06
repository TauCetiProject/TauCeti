/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.Div
public import Mathlib.Algebra.Squarefree.Basic
public import Mathlib.RingTheory.Ideal.Operations
public import Mathlib.RingTheory.Polynomial.UniqueFactorization

/-!
# Radical monic polynomial ideals by extension of coefficients

A monic polynomial generates a radical ideal if its image under an injective coefficient
map generates a radical ideal. In particular, squarefreeness over a field containing the
coefficient ring suffices. Monic division reflects divisibility without requiring the
coefficient ring to be integrally closed or factorial.
-/

public section

namespace Polynomial.Monic

variable {R S : Type*} [CommRing R] [CommRing S] {p : R[X]}

/-- A monic polynomial ideal is radical if it is radical after an injective extension
of coefficients. -/
theorem isRadical_span_of_map (hp : p.Monic) (f : R →+* S)
    (hf : Function.Injective f) (h : (Ideal.span {p.map f}).IsRadical) :
    (Ideal.span {p}).IsRadical := by
  apply (Ideal.isRadical_iff_pow_one_lt 2 (by decide)).mpr
  intro q hq
  rw [Ideal.mem_span_singleton] at hq ⊢
  apply (Polynomial.map_dvd_map f hf hp).mp
  apply Ideal.mem_span_singleton.mp
  apply (Ideal.isRadical_iff_pow_one_lt 2 (by decide)).mp h
  rw [Ideal.mem_span_singleton, ← Polynomial.map_pow]
  exact Polynomial.map_dvd f hq

/-- A monic polynomial with squarefree image in a field generates a radical ideal. -/
theorem isRadical_span_of_map_squarefree {K : Type*} [Field K] (hp : p.Monic)
    (f : R →+* K) (hf : Function.Injective f) (h : Squarefree (p.map f)) :
    (Ideal.span {p}).IsRadical := by
  apply hp.isRadical_span_of_map f hf
  apply (Ideal.isRadical_iff_pow_one_lt 2 (by decide)).mpr
  intro q hq
  rw [Ideal.mem_span_singleton] at hq ⊢
  exact (h.dvd_pow_iff_dvd (by decide : 2 ≠ 0)).mp hq

end Polynomial.Monic
