/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Finsupp.Fin
public import Mathlib.Data.Finsupp.MonomialOrder.DegLex
import TauCeti.Data.Finsupp.Fin
import TauCeti.Data.Finsupp.MapDomain

/-!
# Order-preservation lemmas for graded lexicographic order (`DegLex`)

Pushing forward natural-valued finitely supported functions along a strictly monotone map preserves
and reflects `DegLex` (`Finsupp.toDegLex_mapDomain_lt_iff`), specializing to order isomorphisms
(`Finsupp.toDegLex_equivMapDomain_lt_iff`) and `Fin.succ` (`Finsupp.toDegLex_cons_zero_lt_iff`).
-/

public section

namespace Finsupp

/-- Pushing forward along a strictly monotone map of indices preserves and reflects the strict
graded lexicographic order `DegLex`. -/
theorem toDegLex_mapDomain_lt_iff {σ τ : Type*} [LinearOrder σ] [Preorder τ] {f : σ → τ}
    (hf : StrictMono f) {α β : σ →₀ ℕ} :
    toDegLex (α.mapDomain f) < toDegLex (β.mapDomain f) ↔ toDegLex α < toDegLex β := by
  simp only [DegLex.lt_iff, ofDegLex_toDegLex, degree_mapDomain,
    toLex_mapDomain_lt_toLex_mapDomain_iff hf]

/-- Reindexing along an order isomorphism preserves and reflects the strict graded lexicographic
order `DegLex`. -/
theorem toDegLex_equivMapDomain_lt_iff {σ τ : Type*} [LinearOrder σ] [Preorder τ] (e : σ ≃o τ)
    {α β : σ →₀ ℕ} :
    toDegLex (equivMapDomain e.toEquiv α) < toDegLex (equivMapDomain e.toEquiv β) ↔
      toDegLex α < toDegLex β := by
  simpa only [equivMapDomain_eq_mapDomain] using
    toDegLex_mapDomain_lt_iff (f := e.toEquiv) e.strictMono

/-- Prepending `0` at coordinate `0` preserves and reflects the strict graded lexicographic order
`DegLex`. -/
@[simp] theorem toDegLex_cons_zero_lt_iff {n : ℕ} {α' β' : Fin n →₀ ℕ} :
    toDegLex (cons 0 α') < toDegLex (cons 0 β') ↔ toDegLex α' < toDegLex β' := by
  rw [← mapDomain_finSucc, ← mapDomain_finSucc, toDegLex_mapDomain_lt_iff Fin.strictMono_succ]

end Finsupp
