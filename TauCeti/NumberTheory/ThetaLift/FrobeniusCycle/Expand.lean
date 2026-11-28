/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.MvPolynomial.Expand
public import TauCeti.NumberTheory.ThetaLift.FrobeniusCycle.Forms

import Mathlib.Algebra.CharP.Frobenius

/-!
# Commutation of Frobenius-cycle twisted actions with q-power expansion

In characteristic `T.p`, the Frobenius congruences of a Frobenius cycle `T` become exact
identities `T.ι (s + 1) y = T.ι s y ^ T.P`. Iterating around the cycle of length `N` shows that
every letter embedding is fixed by raising to any power of `T.q = T.P ^ N`, and hence the
twisted action `T.twistedAction g` commutes with the polynomial expansion
`MvPolynomial.expand (T.q ^ j)`:

* `TauCeti.FrobeniusCycle.ι_pow_q_pow`: `T.ι s y ^ T.q ^ j = T.ι s y` in characteristic `T.p`.
* `TauCeti.FrobeniusCycle.twistedAction_commute_expand`: `T.twistedAction g` commutes with
  `MvPolynomial.expand m` whenever `m = T.q ^ j`.
* `TauCeti.FrobeniusCycle.twistedAction_expand_apply`: pointwise form of
  `twistedAction_commute_expand`.

## Provenance

Adapted from `grh-lean` (`https://github.com/lsernau/grh-lean`, commit
`72fead102f663d5c7a407964a13dc0cf9d977207`), file
`src/New/UpperBound/ElementaryDivisors/DefectCount.lean`
(`New.FrobeniusCycle.embedding_pow_q_pow`, `New.FrobeniusCycle.polyAction_commute_expand`).
-/

public section

open MvPolynomial

namespace TauCeti.FrobeniusCycle

variable {W : Type*} [CommRing W] [IsLocalRing W] {R : Type*} [CommRing R] {N : ℕ}
  (T : FrobeniusCycle W R N)

/-- In characteristic `T.p`, every value of a letter embedding `T.ι s` is fixed by raising to the
power `T.q ^ j`, where `T.q = T.P ^ N`. -/
theorem ι_pow_q_pow [CharP R T.p] (s : ZMod N) (y : W) (j : ℕ) :
    T.ι s y ^ T.q ^ j = T.ι s y := by
  have h_dvd := T.dvd_ι_add_natCast_sub_pow s y (N * j)
  rw [show s + (N * j : ℕ) = s by simp, CharP.cast_eq_zero R T.p,
    zero_dvd_iff, sub_eq_zero] at h_dvd
  rw [q_def, ← pow_mul, ← h_dvd]

/-- In characteristic `T.p`, the twisted action `T.twistedAction g` commutes with the variable
power expansion `MvPolynomial.expand m` for every power `m = T.q ^ j`. -/
theorem twistedAction_commute_expand [CharP R T.p] {k m j : ℕ} (hm : m = T.q ^ j)
    (g : GL (Fin k) W) :
    Commute (T.twistedAction (k := k) g) (MvPolynomial.expand (R := R) m) := by
  have : Fact T.p.Prime := ⟨T.prime⟩
  have h_pow : m = T.p ^ (T.e * (N * j)) := by
    rw [hm, q_def, P_def, ← pow_mul, ← pow_mul]
  have h_fixed (s : ZMod N) (y : W) : T.ι s y ^ m = T.ι s y := by
    rw [hm, T.ι_pow_q_pow]
  subst h_pow
  refine MvPolynomial.algHom_ext fun ⟨c, s⟩ ↦ ?_
  have h_entry (b : Fin k) : (T.letterMatrix s g b c) ^ T.p ^ (T.e * (N * j)) =
      T.letterMatrix s g b c := by
    cases hs : T.isEven s
    · rw [T.letterMatrix_of_not_isEven hs, Matrix.map_apply, h_fixed]
    · rw [T.letterMatrix_of_isEven hs, Matrix.map_apply, h_fixed]
  simp only [AlgHom.mul_apply, twistedAction_X, map_sum, map_pow, expand_X, sum_pow_char_pow,
    smul_pow, map_smul, h_entry]

/-- Pointwise form of `twistedAction_commute_expand`: in characteristic `T.p`, the twisted action
`T.twistedAction g` commutes with `MvPolynomial.expand (T.q ^ j)`. -/
theorem twistedAction_expand_apply [CharP R T.p] {k : ℕ} (j : ℕ) (g : GL (Fin k) W)
    (f : MvPolynomial (Fin k × ZMod N) R) :
    T.twistedAction g (MvPolynomial.expand (T.q ^ j) f) =
      MvPolynomial.expand (T.q ^ j) (T.twistedAction g f) :=
  AlgHom.congr_fun (T.twistedAction_commute_expand rfl g) f

end TauCeti.FrobeniusCycle
