/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang, The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.QuasiFinite.Basic
public import Mathlib.RingTheory.Spectrum.Maximal.Defs
public import TauCeti.RingTheory.LocalRing.Localization
import Mathlib.RingTheory.Ideal.GoingUp

/-!
# Artinian fibres, residue fields, and maximal spectra of quasi-finite algebras

For a prime `q` at which `S` is quasi-finite over `R`, the local-ring localization equivalence
identifies the fibre `S_q ⧸ (q.under R) S_q` with an Artinian quotient of the localization of
`S_q` at its maximal ideal.

For a quasi-finite local homomorphism `R → S` of local rings, the residue field of `S` is a finite
extension of the residue field of `R`. More generally, an integral quasi-finite algebra over a ring
with finitely many maximal ideals itself has finitely many maximal ideals.

## Main results

* `Ideal.isArtinianRing_quotient_of_quasiFiniteAt`: the local fibre at a quasi-finite prime is
  Artinian.
* `IsLocalRing.ResidueField.finite_of_quasiFinite`: the residue field extension of a quasi-finite
  local homomorphism of local rings is finite.
* `TauCeti.finite_maximalSpectrum_of_isIntegral_of_quasiFinite`: an integral quasi-finite algebra
  over a ring with finitely many maximal ideals has finitely many maximal ideals.

## References

* The Stacks Project, Tag 00PK (a quasi-finite ring map has finite residue field extensions).
-/

public section

namespace Ideal

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]

/-- If `S` is quasi-finite over `R` at a prime `q`, the quotient of `S_q` by the extension of
`q.under R` is an Artinian ring. -/
instance isArtinianRing_quotient_of_quasiFiniteAt (q : Ideal S) [q.IsPrime]
    [Algebra.QuasiFiniteAt R q] :
    IsArtinianRing (Localization.AtPrime q ⧸
      (q.under R).map (algebraMap R (Localization.AtPrime q))) := by
  let Sq := Localization.AtPrime q
  let m := IsLocalRing.maximalIdeal Sq
  have hunder : m.under R = q.under R := by
    rw [← Ideal.under_under (B := S), Localization.AtPrime.under_maximalIdeal]
  have : m.LiesOver (q.under R) := ⟨hunder.symm⟩
  let e := IsLocalRing.algEquivLocalizationAtMaximalIdeal R Sq
  have hmap : ((q.under R).map (algebraMap R Sq)).map
      (e.toAlgHom : Sq →+* Localization.AtPrime m) =
      (q.under R).map (algebraMap R (Localization.AtPrime m)) := by
    rw [Ideal.map_map, AlgHom.comp_algebraMap]
  exact (Ideal.quotientEquiv _ _ e.toRingEquiv hmap.symm).symm.isArtinianRing

end Ideal

namespace IsLocalRing.ResidueField

variable {R S : Type*} [CommRing R] [IsLocalRing R] [CommRing S] [IsLocalRing S] [Algebra R S]
  [IsLocalHom (algebraMap R S)]

/-- **The residue field extension of a quasi-finite local homomorphism is finite.** If `R → S` is
a local homomorphism of local rings and `S` is quasi-finite over `R`, then the residue field of
`S` is a finite extension of the residue field of `R`. Stacks, Lemma 00PK. The proof follows that
of Mathlib's instance `Module.Finite P.ResidueField Q.ResidueField` for primes of a quasi-finite
algebra in `Mathlib/RingTheory/QuasiFinite/Basic.lean`. -/
instance finite_of_quasiFinite [Algebra.QuasiFinite R S] :
    Module.Finite (ResidueField R) (ResidueField S) :=
  -- `ResidueField S` is by definition the quotient `S ⧸ maximalIdeal S`, so Mathlib's instance
  -- for a quotient of a quasi-finite algebra applies.
  have : Algebra.QuasiFinite R (ResidueField S) :=
    inferInstanceAs (Algebra.QuasiFinite R (S ⧸ maximalIdeal S))
  have : Algebra.QuasiFinite (ResidueField R) (ResidueField S) := .of_restrictScalars R _ _
  .of_quasiFinite

end IsLocalRing.ResidueField

namespace TauCeti

/-- **An integral quasi-finite algebra over a semilocal ring is semilocal**: if `R` has finitely
many maximal ideals and `B` is an integral quasi-finite `R`-algebra (in particular, a module-finite
`R`-algebra), then `B` has finitely many maximal ideals. -/
theorem finite_maximalSpectrum_of_isIntegral_of_quasiFinite (R : Type*) {B : Type*} [CommRing R]
    [Finite (MaximalSpectrum R)] [CommRing B] [Algebra R B] [Algebra.IsIntegral R B]
    [Algebra.QuasiFinite R B] : Finite (MaximalSpectrum B) := by
  -- Every maximal ideal `M` of `B` contracts to a maximal ideal of `R` by integrality, and each
  -- maximal ideal of `R` has only finitely many primes of `B` lying over it by quasi-finiteness.
  have : ∀ m : MaximalSpectrum R, Finite (m.asIdeal.primesOver B) :=
    fun m ↦ (Algebra.QuasiFinite.finite_primesOver m.asIdeal (S := B)).to_subtype
  refine Finite.of_injective (β := (m : MaximalSpectrum R) × m.asIdeal.primesOver B)
    (fun M ↦
      have := M.isMaximal
      ⟨⟨M.asIdeal.under R, inferInstance⟩, ⟨M.asIdeal, M.isMaximal.isPrime, ⟨rfl⟩⟩⟩)
    fun M₁ M₂ h ↦ MaximalSpectrum.ext (congrArg (fun x ↦ x.2.val) h)

end TauCeti
