/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Computability.SingleOracle.Substitution.Basic

/-!
# Translating indices of diagonal halting questions

A program supplying the source oracle translates a diagonal halting question into one for the
target oracle. Substitution inlines the query program, and fixing the input to the original
index makes the translation one-to-one. The translation is primitive recursive in both the
query program and the index.
-/

public section

open Denumerable

namespace TauCeti.Oracle.Single.Code

/-- Translate a diagonal halting question using a program `d` that supplies the source oracle.
The target program has the queries in program `e` replaced by `d` and fixes its input to `e`. -/
def jumpIndex (d : Code) (e : ℕ) : ℕ :=
  ((ofNat Code e).subst d).haltingIndex e

/-- Decoding a translated index recovers the substituted program with its input fixed. -/
@[simp]
theorem ofNat_jumpIndex (d : Code) (e : ℕ) :
    ofNat Code (d.jumpIndex e) = ((ofNat Code e).subst d).fixInput e := by
  rw [jumpIndex, ofNat_haltingIndex]

/-- Translation of diagonal indices is primitive recursive in the query program and index. -/
theorem primrec₂_jumpIndex : Primrec₂ jumpIndex :=
  primrec₂_haltingIndex.comp (primrec₂_subst.comp ((Primrec.ofNat Code).comp Primrec.snd)
    Primrec.fst) Primrec.snd

/-- For a fixed query program the jump-index translation is one-to-one. -/
theorem jumpIndex_injective (d : Code) : Function.Injective d.jumpIndex :=
  fun _ _ h => by
    simp only [jumpIndex, haltingIndex_inj] at h
    exact h.2

end TauCeti.Oracle.Single.Code
