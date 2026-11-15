/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Polynomial.UniversalFactorizationRing

/-!
# Quotient naturality of the universal coprime factorization ring

Composing a point of `Polynomial.UniversalCoprimeFactorizationRing` with values in `R` with the
reduction `R → R ⧸ I` reduces both factors modulo `I`
(`Polynomial.UniversalCoprimeFactorizationRing.homEquiv_mkₐ_comp_fst` and
`Polynomial.UniversalCoprimeFactorizationRing.homEquiv_mkₐ_comp_snd`).
-/

public section

open Polynomial

namespace Polynomial.UniversalCoprimeFactorizationRing

variable {R : Type*} [CommRing R] (I : Ideal R) {n : ℕ} (m k : ℕ) (hn : n = m + k)
  (P : MonicDegreeEq R n) (φ : UniversalCoprimeFactorizationRing m k hn P →ₐ[R] R)

/-- Composing a point of the universal coprime factorization ring with values in `R` with the
reduction `R → R ⧸ I` reduces its first factor modulo `I`. -/
lemma homEquiv_mkₐ_comp_fst :
    (homEquiv (R ⧸ I) m k hn P ((Ideal.Quotient.mkₐ R I).comp φ)).1.1.1 =
      (homEquiv R m k hn P φ).1.1.1.map (Ideal.Quotient.mk I) := by
  rw [homEquiv_comp_fst, ← AlgHom.toRingHom_eq_coe, Ideal.Quotient.mkₐ_toRingHom]
  simp

/-- Composing a point of the universal coprime factorization ring with values in `R` with the
reduction `R → R ⧸ I` reduces its second factor modulo `I`. -/
lemma homEquiv_mkₐ_comp_snd :
    (homEquiv (R ⧸ I) m k hn P ((Ideal.Quotient.mkₐ R I).comp φ)).1.2.1 =
      (homEquiv R m k hn P φ).1.2.1.map (Ideal.Quotient.mk I) := by
  rw [homEquiv_comp_snd, ← AlgHom.toRingHom_eq_coe, Ideal.Quotient.mkₐ_toRingHom]
  simp

end Polynomial.UniversalCoprimeFactorizationRing
