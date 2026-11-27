/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Etale.Kaehler
public import Mathlib.RingTheory.Extension.Cotangent.Basic
public import Mathlib.RingTheory.Flat.Localization
public import TauCeti.RingTheory.FittingIdeal.Basic
import TauCeti.RingTheory.FittingIdeal.BaseChange
import TauCeti.RingTheory.Flat.Localization

/-!
# Fitting ideals of Kähler differentials of a finitely generated algebra

If `S` is generated as an `R`-algebra by a finite family indexed by `ι`, then `Ω[S⁄R]` is a
quotient of the free module on the differentials of the generators
(`Algebra.Extension.toKaehler_surjective`), so `Fitt_k(Ω[S⁄R])` is the unit ideal once `k ≥ #ι`.
In particular the singular locus `S ⧸ Fitt_k(Ω[S⁄R])` is empty in that range.

The ideal `((Fitt₁(Ω[S⁄R])).map (S → S_q)).comap (R → S_q)` of `R` cut out by the singular locus
at a prime `q` of `S` does not change along a flat, formally étale map `S → T`
(`TauCeti.comap_map_fittingIdeal_localization_comap_eq`).
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

namespace TauCeti

/-- The ideal of `R` cut out by the singular locus at a prime does not change along a flat,
formally étale map `S → T`: it is the same at a prime `Q` of `T` and at `Q ∩ S`. The first Fitting
ideal of the differentials base-changes along `S → T`, and `S_{Q ∩ S} → T_Q` is faithfully
flat. -/
theorem comap_map_fittingIdeal_localization_comap_eq {R S T : Type*} [CommRing R] [CommRing S]
    [CommRing T] [Algebra R S] [Module.Finite S Ω[S⁄R]] [Algebra S T] [Algebra.FormallyEtale S T]
    [Module.Flat S T] [Algebra R T] [IsScalarTower R S T] [Module.Finite T Ω[T⁄R]] (Q : Ideal T)
    [Q.IsPrime] :
    ((fittingIdeal S Ω[S⁄R] 1).map
        (algebraMap S (Localization.AtPrime (Q.comap (algebraMap S T))))).comap
      (algebraMap R (Localization.AtPrime (Q.comap (algebraMap S T)))) =
      ((fittingIdeal T Ω[T⁄R] 1).map (algebraMap T (Localization.AtPrime Q))).comap
        (algebraMap R (Localization.AtPrime Q)) := by
  have hST : fittingIdeal T Ω[T⁄R] 1 = (fittingIdeal S Ω[S⁄R] 1).map (algebraMap S T) :=
    IsBaseChange.fittingIdeal_eq_map (KaehlerDifferential.isBaseChange_of_formallyEtale R S T) 1
  rw [IsScalarTower.algebraMap_eq R S, ← Ideal.comap_comap,
    ← Ideal.comap_map_localization_atPrime_of_flat, Ideal.comap_comap,
    ← IsScalarTower.algebraMap_eq, IsScalarTower.algebraMap_eq S T, ← Ideal.map_map, ← hST]

end TauCeti
