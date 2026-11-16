/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import TauCeti.RingTheory.WittVector.Quotient
import Mathlib.FieldTheory.Finite.Basic

/-!
# Checks for reduction of Witt quotients

The principal-ideal calculation specializes to `p - [a]`, as in mixed-characteristic
untilting, without requiring a primitive generator. The finite-field checks distinguish
zero and one and record that reduction modulo `p` alone also accepts `(p²)`.
-/

noncomputable section

open Ideal WittVector

variable {p : ℕ} [Fact p.Prime] {S : Type*} [CommRing S] [CharP S p] [PerfectRing S p]

-- The principal-ideal form needed for an integral untilt.
example (ξ : WittVector p S) :
    (WittVector p S ⧸ span {ξ}) ⧸ span {(p : WittVector p S ⧸ span {ξ})} ≃+*
      S ⧸ span {ξ.coeff 0} :=
  (wittVectorQuotientPEquiv (span {ξ})).trans (Ideal.quotEquivOfEq (by simp [Ideal.map_span]))

-- In particular, the quotient by `p - [a]` reduces to `S / (a)`.
example (a : S) :
    (WittVector p S ⧸ span {(p : WittVector p S) - teichmuller p a}) ⧸
      span {(p : WittVector p S ⧸ span {(p : WittVector p S) - teichmuller p a})} ≃+*
        S ⧸ span {a} :=
  (wittVectorQuotientPEquiv (span {(p : WittVector p S) - teichmuller p a})).trans
    (Ideal.quotEquivOfEq (by
      simp only [Ideal.map_span, Set.image_singleton, map_sub, map_natCast]
      simp [Ideal.span_singleton_neg]))

-- The forward equivalence sends a Teichmüller representative to its scalar residue class.
example (I : Ideal (WittVector p S)) (s : S) :
    I.wittVectorQuotientPEquiv
      (Ideal.Quotient.mk _ (Ideal.Quotient.mk I (teichmuller p s))) =
        Ideal.Quotient.mk _ s := by
  simp

-- Over a finite field, the zero and one residue classes remain distinct.
example :
    wittVectorQuotientPEquiv (span {(p : WittVector p (ZMod p))})
      (Ideal.Quotient.mk _ (Ideal.Quotient.mk _ 1)) ≠ 0 := by
  have hmap : (span {(p : WittVector p (ZMod p))}).map constantCoeff = ⊥ := by
    simp [Ideal.map_span]
  rw [wittVectorQuotientPEquiv_mk_mk, one_coeff_zero]
  intro h
  rw [hmap] at h
  exact (one_ne_zero : (1 : ZMod p) ≠ 0)
    (by simpa using congrArg (RingEquiv.quotientBot (ZMod p)) h)

-- Reduction cannot detect primitivity: `(p²)` has the same reduction as `(p)`.
example :
    (WittVector p (ZMod p) ⧸ span {(p : WittVector p (ZMod p)) ^ 2}) ⧸
      span {(p : WittVector p (ZMod p) ⧸ span {(p : WittVector p (ZMod p)) ^ 2})} ≃+*
        ZMod p :=
  (wittVectorQuotientPEquiv (span {(p : WittVector p (ZMod p)) ^ 2})).trans
    ((Ideal.quotEquivOfEq (by simp [Ideal.map_span, -constantCoeff_apply])).trans
      (RingEquiv.quotientBot _))

-- Surjectivity is available on the actual double quotient, with no primality condition on `I`.
example (I : Ideal (WittVector p (ZMod p))) :
    Function.Surjective
      (fun x : (WittVector p (ZMod p) ⧸ I) ⧸ span {(p : WittVector p (ZMod p) ⧸ I)} ↦ x ^ p) :=
  I.surjective_pow_wittVector_quotient_span_natCast
