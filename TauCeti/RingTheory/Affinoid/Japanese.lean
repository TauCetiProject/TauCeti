/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Affinoid.Basic
public import TauCeti.RingTheory.Nagata

import TauCeti.RingTheory.Affinoid.FiniteQuotient
import TauCeti.RingTheory.Affinoid.Integral.Basic
import TauCeti.RingTheory.Affinoid.NoetherNormalization
import TauCeti.RingTheory.Localization.Reduced
import TauCeti.RingTheory.MvPowerSeries.TateAlgebra.Japanese

/-!
# Affinoid domains are Japanese and affinoid algebras are Nagata

Let `K` be a complete nonarchimedean field of arbitrary characteristic. Combining the Japanese
property of unit-polyradius Tate algebras (`TauCeti.MvPowerSeries.isJapanese`) with affinoid Noether
normalization (`TauCeti.IsAffinoidAlgebra.exists_finite_injective`), every affinoid domain over `K`
is a finite extension of a Tate algebra and is therefore a Japanese domain
(`TauCeti.IsAffinoidAlgebra.isJapanese`, [bosch-guntzer-remmert], §6.1.2, Corollary 1).

Because every affinoid algebra is Noetherian (`TauCeti.IsAffinoidAlgebra.isNoetherianRing`) and its
quotient by any prime ideal is an affinoid domain (`TauCeti.IsAffinoidAlgebra.quotient`), every
affinoid algebra — including nonreduced algebras and the zero algebra — is a Nagata ring
(`TauCeti.IsAffinoidAlgebra.isNagata`). Consequently, for any affinoid algebra `A` and any reduced
`A`-algebra `B` essentially of finite type, the integral closure of `A` in `B` is a finite
`A`-module (`TauCeti.IsAffinoidAlgebra.finite_integralClosure`), and when `K` is nontrivially normed
it is again an affinoid `K`-algebra (`TauCeti.IsAffinoidAlgebra.integralClosure`). Applied to the
total ring of fractions `Localization (nonZeroDivisors A)` of a reduced affinoid algebra `A`, this
yields finiteness and the affinoid property of the normalization of `A`
([bosch-guntzer-remmert], §6.1.2, Corollary 2).

## Main results

* `TauCeti.IsAffinoidAlgebra.isJapanese`: every affinoid domain over a complete nonarchimedean field
  is a Japanese domain.
* `TauCeti.IsAffinoidAlgebra.isN1`: every affinoid domain over a complete nonarchimedean field is
  an N-1 domain.
* `TauCeti.IsAffinoidAlgebra.isNagata`: every affinoid algebra over a complete nonarchimedean field
  is a Nagata ring.
* `TauCeti.MvPowerSeries.isNagata_isRestricted_subring`: every unit-polyradius Tate algebra in
  finitely many variables over a complete nonarchimedean field is a Nagata ring.
* `TauCeti.IsAffinoidAlgebra.finite_integralClosure` and
  `TauCeti.IsAffinoidAlgebra.finite_isIntegralClosure`: finiteness of integral closures of affinoid
  algebras in reduced essentially-of-finite-type algebras.
* `TauCeti.IsAffinoidAlgebra.finite_integralClosure_of_isLocalization`: for a reduced affinoid
  algebra `A`, its integral closure in any localization (in particular in its total ring of
  fractions) is a finite `A`-module.
* `TauCeti.IsAffinoidAlgebra.integralClosure` and
  `TauCeti.IsAffinoidAlgebra.integralClosure_localization`: over a nontrivially normed complete
  nonarchimedean field, these integral closures are affinoid `K`-algebras.

## References

* [Bosch, Güntzer, Remmert, *Non-Archimedean Analysis*][bosch-guntzer-remmert], §6.1.2, Corollaries
  1 and 2.
-/

public section

namespace TauCeti

open _root_.MvPowerSeries

section NormedField

variable {K A : Type*} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  [CommRing A] [Algebra K A]

namespace IsAffinoidAlgebra

/-- **Affinoid domains are Japanese** ([bosch-guntzer-remmert], §6.1.2, Corollary 1). Every affinoid
domain over a complete nonarchimedean field (of arbitrary characteristic, trivially or nontrivially
normed) is a Japanese domain. -/
theorem isJapanese [IsDomain A] (hA : IsAffinoidAlgebra K A) : Ring.IsJapanese A := by
  obtain ⟨n, g, hg_inj, hg_fin⟩ := hA.exists_finite_injective
  let T := IsRestricted.subring (R := K) (fun _ : Fin n ↦ 1)
  let _ : Algebra T A := g.toRingHom.toAlgebra
  have : FaithfulSMul T A := (faithfulSMul_iff_algebraMap_injective T A).mpr hg_inj
  have : Module.Finite T A := hg_fin
  exact Ring.IsJapanese.of_finite T A

/-- Every affinoid domain over a complete nonarchimedean field is an N-1 domain. -/
theorem isN1 [IsDomain A] (hA : IsAffinoidAlgebra K A) : Ring.IsN1 A :=
  let := hA.isJapanese
  inferInstance

/-- **Affinoid algebras are Nagata rings.** Every affinoid algebra over a complete nonarchimedean
field — including nonreduced algebras and the zero algebra — is Noetherian and has Japanese prime
quotients. -/
theorem isNagata (hA : IsAffinoidAlgebra K A) : Ring.IsNagata A where
  toIsNoetherian := hA.isNoetherianRing
  isJapanese_quotient p _ := (hA.quotient p).isJapanese

/-- For an affinoid algebra `A` over a complete nonarchimedean field and a reduced `A`-algebra `B`
essentially of finite type, the integral closure of `A` in `B` is a finite `A`-module. -/
theorem finite_integralClosure (hA : IsAffinoidAlgebra K A) (B : Type*) [CommRing B] [IsReduced B]
    [Algebra A B] [Algebra.EssFiniteType A B] : Module.Finite A (_root_.integralClosure A B) :=
  let := hA.isNagata
  Ring.IsNagata.finite_integralClosure B

/-- Abstract integral-closure form of `IsAffinoidAlgebra.finite_integralClosure`. -/
theorem finite_isIntegralClosure (hA : IsAffinoidAlgebra K A) (B C : Type*) [CommRing B]
    [IsReduced B] [Algebra A B] [Algebra.EssFiniteType A B] [CommRing C] [Algebra A C]
    [Algebra C B] [IsScalarTower A C B] [IsIntegralClosure C A B] : Module.Finite A C :=
  have := hA.finite_integralClosure B
  .equiv (IsIntegralClosure.equiv A (_root_.integralClosure A B) B C).toLinearEquiv

/-- For a reduced affinoid algebra `A` over a complete nonarchimedean field, the integral closure of
`A` in any localization `S` of `A` — in particular in its total ring of fractions
`Localization (nonZeroDivisors A)` — is a finite `A`-module
([bosch-guntzer-remmert], §6.1.2, Corollary 2). -/
theorem finite_integralClosure_of_isLocalization [IsReduced A] (hA : IsAffinoidAlgebra K A)
    (M : Submonoid A) (S : Type*) [CommRing S] [Algebra A S] [IsLocalization M S] :
    Module.Finite A (_root_.integralClosure A S) :=
  have : IsReduced S := _root_.IsLocalization.isReduced M S
  have : Algebra.EssFiniteType A S := .of_isLocalization (S := S) M
  hA.finite_integralClosure S

end IsAffinoidAlgebra

/-- **Tate algebras are Nagata rings.** Over a complete nonarchimedean field, the unit-polyradius
Tate algebra in finitely many variables is a Nagata ring. -/
theorem MvPowerSeries.isNagata_isRestricted_subring {σ : Type*} [Finite σ] :
    Ring.IsNagata (IsRestricted.subring (R := K) (fun _ : σ ↦ 1)) :=
  (isAffinoidAlgebra_tate (K := K) (σ := σ)).isNagata

end NormedField

section NontriviallyNormedField

namespace IsAffinoidAlgebra

variable {K A : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  [CommRing A] [Algebra K A]

/-- Over a nontrivially normed complete nonarchimedean field `K`, the integral closure of an
affinoid `K`-algebra `A` in any reduced `A`-algebra `B` essentially of finite type (with a
compatible `K`-algebra structure) is an affinoid `K`-algebra. -/
theorem integralClosure (hA : IsAffinoidAlgebra K A) (B : Type*) [CommRing B] [IsReduced B]
    [Algebra K B] [Algebra A B] [IsScalarTower K A B] [Algebra.EssFiniteType A B] :
    IsAffinoidAlgebra K (_root_.integralClosure A B) :=
  have := hA.finite_integralClosure B
  hA.of_finite

/-- **Normalization of a reduced affinoid algebra is affinoid**
([bosch-guntzer-remmert], §6.1.2, Corollary 2). Over a nontrivially normed complete nonarchimedean
field `K`, the integral closure of any reduced affinoid `K`-algebra `A` in `Localization M` (for
instance in its total ring of fractions `Localization (nonZeroDivisors A)`) is an affinoid
`K`-algebra. -/
theorem integralClosure_localization [IsReduced A] (hA : IsAffinoidAlgebra K A)
    (M : Submonoid A) : IsAffinoidAlgebra K (_root_.integralClosure A (Localization M)) :=
  hA.integralClosure (Localization M)

/-!
### Non-vacuous checks on zero and reduced affinoid algebras
-/

/-- The zero quotient `K ⧸ ⊤` is an affinoid algebra (with no Noether normalization injection from
a Tate algebra) and is Nagata. -/
example : IsAffinoidAlgebra K (K ⧸ (⊤ : Ideal K)) ∧ Ring.IsNagata (K ⧸ (⊤ : Ideal K)) :=
  let h0 := (isAffinoidAlgebra_self (K := K)).quotient (⊤ : Ideal K)
  ⟨h0, h0.isNagata⟩

/-- The normalization of any reduced affinoid `K`-algebra `A` in its total ring of fractions
`Localization (nonZeroDivisors A)` is both finite over `A` and an affinoid `K`-algebra. -/
example [IsReduced A] (hA : IsAffinoidAlgebra K A) :
    Module.Finite A (_root_.integralClosure A (Localization (nonZeroDivisors A))) ∧
      IsAffinoidAlgebra K (_root_.integralClosure A (Localization (nonZeroDivisors A))) :=
  ⟨hA.finite_integralClosure_of_isLocalization (nonZeroDivisors A) _,
    hA.integralClosure_localization (nonZeroDivisors A)⟩

end IsAffinoidAlgebra

end NontriviallyNormedField

end TauCeti
