/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Extension.Cotangent.Basic
public import TauCeti.RingTheory.FittingIdeal.Basic

/-!
# Fitting ideals of Kähler differentials of a finitely generated algebra

If `S` is generated as an `R`-algebra by a finite family indexed by `ι`, then `Ω[S⁄R]` is a
quotient of the free module on the differentials of the generators
(`Algebra.Extension.toKaehler_surjective`), so `Fitt_k(Ω[S⁄R])` is the unit ideal once `k ≥ #ι`.
In particular the singular locus `S ⧸ Fitt_k(Ω[S⁄R])` is empty in that range.
-/

public section

open TauCeti

namespace Algebra.Generators

variable {R S ι : Type*} [CommRing R] [CommRing S] [Algebra R S] [Module.Finite S Ω[S⁄R]]
  [Finite ι]

/-- If `S` is generated over `R` by a finite family indexed by `ι`, then `Fitt_k(Ω[S⁄R]) = S` for
every `k ≥ #ι`: `Ω[S⁄R]` is a quotient of the free module of rank `#ι` on the differentials of
the generators. -/
theorem fittingIdeal_kaehlerDifferential_eq_top (P : Generators R S ι) {k : ℕ}
    (hk : Nat.card ι ≤ k) : fittingIdeal S Ω[S⁄R] k = ⊤ := by
  nontriviality S
  have := Fintype.ofFinite ι
  let b := P.cotangentSpaceBasis
  have : Module.Free S P.toExtension.CotangentSpace := .of_basis b
  have : Module.Finite S P.toExtension.CotangentSpace := .of_basis b
  exact fittingIdeal_eq_top_of_surjective P.toExtension.toKaehler_surjective
    (by rwa [Module.finrank_eq_card_basis b, ← Nat.card_eq_fintype_card])

end Algebra.Generators
