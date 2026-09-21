/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.PurelyInseparable.Basic

/-!
# A quadratic extension away from characteristic two is separable

An extension of fields of degree `2` is separable unless `2 = 0` in the base field. Indeed the
separable degree divides the degree, so it is `1` or `2`; the value `2` is separability itself,
while the value `1` makes the extension purely inseparable, hence of degree a power of the
exponential characteristic — and `2` is a power of the exponential characteristic only in
characteristic two.

The characteristic-two exception is genuine: over `K = 𝔽₂(t)` the extension `K(√t) / K` has
degree `2` and is purely inseparable.

## Main results

* `TauCeti.Algebra.isSeparable_of_finrank_eq_two`
-/

public section

namespace TauCeti

namespace Algebra

open Module

/-- **A field extension of degree two with `2 ≠ 0` in the base field is separable.**

The hypothesis is the nonvanishing of `2` in the base field rather than a `CharP` assumption, so
that it transfers along any field extension by injectivity of the structure map. -/
theorem isSeparable_of_finrank_eq_two {K L : Type*} [Field K] [Field L] [Algebra K L]
    (h2 : (2 : K) ≠ 0) (h : finrank K L = 2) : Algebra.IsSeparable K L := by
  have : FiniteDimensional K L := Module.finite_of_finrank_pos (by omega)
  have hdvd : Field.finSepDegree K L ∣ 2 := h ▸ Field.finSepDegree_dvd_finrank K L
  rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h1 | h1
  · -- Separable degree one: the extension is purely inseparable, so `2` is a power of the
    -- exponential characteristic, which forces characteristic two.
    exfalso
    have : IsPurelyInseparable K L := isPurelyInseparable_of_finSepDegree_eq_one h1
    obtain ⟨q, hq⟩ := ExpChar.exists K
    have _ : ExpChar K q := hq
    obtain ⟨n, hn⟩ := IsPurelyInseparable.finrank_eq_pow K L q
    rw [h] at hn
    cases hq with
    | zero => simp at hn
    | prime hp =>
      have hn0 : n ≠ 0 := by rintro rfl; simp at hn
      have hq2 : q = 2 :=
        (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (by rw [hn]; exact dvd_pow_self q hn0)
      subst hq2
      exact h2 (by exact_mod_cast CharP.cast_eq_zero K 2)
  · exact (Field.finSepDegree_eq_finrank_iff K L).mp (h1.trans h.symm)

end Algebra

end TauCeti
