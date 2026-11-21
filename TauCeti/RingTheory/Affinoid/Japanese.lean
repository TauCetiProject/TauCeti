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
import TauCeti.RingTheory.IntegralClosure.ReducedArtinian
import TauCeti.RingTheory.Localization.Reduced
import TauCeti.RingTheory.MvPowerSeries.TateAlgebra.Japanese

/-!
# Affinoid algebras are Japanese and Nagata, and finiteness of normalization

Every affinoid domain over a complete ultrametric normed field `K` is Japanese, and every affinoid
algebra over `K`—including non-domains, non-reduced algebras, and the zero algebra—is Nagata.

By affinoid Noether normalization (`TauCeti.IsAffinoidAlgebra.exists_finite_injective`), any
affinoid domain `A` admits a finite injective `K`-algebra map from a Tate algebra
`K⟨Y₁, …, Y_d⟩`. Since Tate algebras are Japanese
(`TauCeti.MvPowerSeries.isJapanese_isRestricted_subring`) and the Japanese property passes to
finite extension domains (`TauCeti.Ring.IsJapanese.of_finite`), `A` is Japanese. For a general
affinoid algebra `A`, `A` is Noetherian (`TauCeti.IsAffinoidAlgebra.isNoetherianRing`) and every
prime quotient `A ⧸ p` is an affinoid domain and therefore Japanese, so `A` is Nagata.

Consequently (`TauCeti.Ring.IsNagata.finite_of_isIntegralClosure`), for any reduced `A`-algebra `B`
essentially of finite type, any integral closure `C` of `A` in `B` is a finite `A`-module. In
particular, when `A` is reduced, `A` is N-1 (`TauCeti.Ring.IsNagata.isN1`) so its normalization in
any total ring of fractions `F` is a finite `A`-module; when `K` is nontrivially normed,
`TauCeti.IsAffinoidAlgebra.of_finite` shows that these integral closures are again affinoid
`K`-algebras (`TauCeti.IsAffinoidAlgebra.of_isIntegralClosure`).

## Main results

* `TauCeti.IsAffinoidAlgebra.isJapanese`: every affinoid domain over a complete ultrametric normed
  field is Japanese.
* `TauCeti.IsAffinoidAlgebra.isNagata`: every affinoid algebra over a complete ultrametric normed
  field is Nagata.
* `TauCeti.MvPowerSeries.isNagata_isRestricted_subring`: the Tate algebra `K⟨X₁, …, Xₙ⟩` in
  finitely many variables is Nagata.
* `TauCeti.IsAffinoidAlgebra.of_isIntegralClosure`,
  `TauCeti.IsAffinoidAlgebra.integralClosure`,
  `TauCeti.IsAffinoidAlgebra.of_isIntegralClosure_of_isFractionRing`, and
  `TauCeti.IsAffinoidAlgebra.integralClosure_fractionRing`: over a nontrivially normed complete
  ultrametric field, these integral closures and normalizations are again affinoid `K`-algebras.

## References

* [Bosch, Güntzer, Remmert, *Non-Archimedean Analysis*][bosch-guntzer-remmert], §§5.3.1, 6.1.2.
* B. Conrad, *Irreducible components of rigid spaces*, Ann. Inst. Fourier 49 (1999), 473–541,
  §1.1.
* [Stacks Project, Tags 032R and 03GH](https://stacks.math.columbia.edu/tag/032E).
-/

public section

namespace TauCeti.IsAffinoidAlgebra

open _root_.MvPowerSeries

section NormedField

variable {K : Type*} {A : Type*} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  [CommRing A] [Algebra K A]

/-- **Affinoid domains are Japanese.** Over any complete ultrametric normed field `K` (of arbitrary
characteristic and trivial or nontrivial valuation), every affinoid domain `A` is a Japanese (N-2)
domain. -/
theorem isJapanese [IsDomain A] (hA : IsAffinoidAlgebra K A) : Ring.IsJapanese A := by
  obtain ⟨d, g, hg_inj, hg_fin⟩ := hA.exists_finite_injective
  let : Algebra (IsRestricted.subring (R := K) (fun _ : Fin d ↦ 1)) A := g.toRingHom.toAlgebra
  have : Module.Finite (IsRestricted.subring (R := K) (fun _ : Fin d ↦ 1)) A :=
    RingHom.finite_algebraMap.mp hg_fin
  have : FaithfulSMul (IsRestricted.subring (R := K) (fun _ : Fin d ↦ 1)) A :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr hg_inj
  exact Ring.IsJapanese.of_finite (IsRestricted.subring (R := K) (fun _ : Fin d ↦ 1)) A

/-- **Affinoid algebras are Nagata.** Over any complete ultrametric normed field `K`, every
affinoid `K`-algebra `A` (including non-domains, non-reduced algebras, and the zero algebra) is a
Nagata ring: it is Noetherian and every prime quotient `A ⧸ p` is a Japanese domain. -/
theorem isNagata (hA : IsAffinoidAlgebra K A) : Ring.IsNagata A where
  toIsNoetherian := hA.isNoetherianRing
  isJapanese_quotient p _ := (hA.quotient p).isJapanese

end NormedField

section NontriviallyNormedField

variable {K : Type*} {A : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]
  [CompleteSpace K] [CommRing A] [Algebra K A]

/-- Over a nontrivially normed complete ultrametric field `K`, any integral closure `C` of an
affinoid `K`-algebra `A` in a reduced `A`-algebra `B` essentially of finite type is again an
affinoid `K`-algebra. -/
theorem of_isIntegralClosure (hA : IsAffinoidAlgebra K A) (B : Type*) [CommRing B] [IsReduced B]
    [Algebra A B] [Algebra.EssFiniteType A B]
    {C : Type*} [CommRing C] [Algebra K C] [Algebra A C] [IsScalarTower K A C]
    [Algebra C B] [IsScalarTower A C B] [IsIntegralClosure C A B] :
    IsAffinoidAlgebra K C :=
  have := hA.isNagata
  have : Module.Finite A C := Ring.IsNagata.finite_of_isIntegralClosure B C
  hA.of_finite

/-- Over a nontrivially normed complete ultrametric field `K`, the integral closure of an affinoid
`K`-algebra `A` in any reduced `A`-algebra `B` essentially of finite type (with a compatible
`K`-algebra structure) is again an affinoid `K`-algebra. -/
theorem integralClosure (hA : IsAffinoidAlgebra K A) {B : Type*} [CommRing B] [IsReduced B]
    [Algebra K B] [Algebra A B] [IsScalarTower K A B] [Algebra.EssFiniteType A B] :
    IsAffinoidAlgebra K (_root_.integralClosure A B) :=
  hA.of_isIntegralClosure B

/-- Over a nontrivially normed complete ultrametric field `K`, any integral closure `C` of a
reduced affinoid `K`-algebra `A` in a total ring of fractions `F` of `A` is an affinoid
`K`-algebra. -/
theorem of_isIntegralClosure_of_isFractionRing [IsReduced A] (hA : IsAffinoidAlgebra K A)
    (F : Type*) [CommRing F] [Algebra A F] [IsFractionRing A F]
    {C : Type*} [CommRing C] [Algebra K C] [Algebra A C] [IsScalarTower K A C]
    [Algebra C F] [IsScalarTower A C F] [IsIntegralClosure C A F] :
    IsAffinoidAlgebra K C :=
  have := hA.isNagata
  have : Module.Finite A C := Ring.IsN1.finite_of_isIntegralClosure F C
  hA.of_finite

/-- Over a nontrivially normed complete ultrametric field `K`, the normalization
`_root_.integralClosure A (FractionRing A)` of a reduced affinoid `K`-algebra `A` in its total ring
of fractions is an affinoid `K`-algebra. -/
theorem integralClosure_fractionRing [IsReduced A] (hA : IsAffinoidAlgebra K A) :
    IsAffinoidAlgebra K (_root_.integralClosure A (FractionRing A)) :=
  hA.of_isIntegralClosure_of_isFractionRing (FractionRing A)

end NontriviallyNormedField

end TauCeti.IsAffinoidAlgebra

namespace TauCeti.MvPowerSeries

open _root_.MvPowerSeries

/-- **Tate algebras are Nagata.** Over any complete ultrametric normed field `K`, the Tate algebra
`K⟨X₁, …, Xₙ⟩` in finitely many variables is a Nagata ring. -/
instance isNagata_isRestricted_subring {σ : Type*} {K : Type*} [NormedField K]
    [IsUltrametricDist K] [CompleteSpace K] [Finite σ] :
    Ring.IsNagata (IsRestricted.subring (R := K) (fun _ : σ ↦ 1)) :=
  isAffinoidAlgebra_tate.isNagata

end TauCeti.MvPowerSeries

namespace TauCeti.IsAffinoidAlgebra

open _root_.MvPowerSeries

section Examples

/-- A non-reduced affinoid quotient such as `K⟨X⟩ ⧸ (X²)` is Nagata by typeclass synthesis. -/
example {K : Type*} [NormedField K] [IsUltrametricDist K] [CompleteSpace K] :
    let T := IsRestricted.subring (R := K) (fun _ : Fin 1 ↦ 1)
    let x : T := ⟨_root_.MvPowerSeries.X 0, isRestricted_X _ 0⟩
    Ring.IsNagata (T ⧸ Ideal.span ({x ^ 2} : Set T)) :=
  inferInstance

/-- Over a nontrivially normed complete ultrametric field `K`, the normalization `C` of a reduced
affinoid `K`-algebra `A` in its total ring of fractions is simultaneously finite over `A`, an
affinoid `K`-algebra, and normal (every localization at a prime of `C` is an integrally closed
domain). -/
example {K : Type*} {A : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
    [CommRing A] [IsReduced A] [Algebra K A] (hA : IsAffinoidAlgebra K A) :
    let C := _root_.integralClosure A (FractionRing A)
    Module.Finite A C ∧ IsAffinoidAlgebra K C ∧
      ∀ Q : Ideal C, [Q.IsPrime] →
        IsDomain (Localization.AtPrime Q) ∧ IsIntegrallyClosed (Localization.AtPrime Q) := by
  have := hA.isNagata
  refine ⟨Ring.IsN1.finite_integralClosure_fractionRing, hA.integralClosure_fractionRing,
    fun Q _ ↦ ?_⟩
  have := hA.isNoetherianRing
  have := IsFractionRing.isArtinianRing_of_isReduced A (FractionRing A)
  have := IsLocalization.isReduced (nonZeroDivisors A) (FractionRing A)
  have : IsIntegrallyClosedIn (_root_.integralClosure A (FractionRing A)) (FractionRing A) :=
    IsIntegrallyClosedIn.of_isIntegralClosure (R := A)
  exact ⟨IsIntegrallyClosedIn.isDomain_localization_atPrime (FractionRing A) Q,
    IsIntegrallyClosedIn.isIntegrallyClosed_localization_atPrime (FractionRing A) Q⟩

end Examples

end TauCeti.IsAffinoidAlgebra

/-! ### Further results -/

public section

namespace TauCeti

open _root_.MvPowerSeries

section NormedField

variable {K A : Type*} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  [CommRing A] [Algebra K A]

namespace IsAffinoidAlgebra

/-- Every reduced affinoid algebra over a complete nonarchimedean field is an N-1 ring. -/
theorem isN1 [IsReduced A] (hA : IsAffinoidAlgebra K A) : Ring.IsN1 A :=
  let := hA.isNagata
  inferInstance

/-- For an affinoid algebra `A` over a complete nonarchimedean field and a reduced `A`-algebra `B`
essentially of finite type, the integral closure of `A` in `B` is a finite `A`-module. -/
theorem finite_integralClosure (hA : IsAffinoidAlgebra K A) (B : Type*) [CommRing B] [IsReduced B]
    [Algebra A B] [Algebra.EssFiniteType A B] : Module.Finite A (_root_.integralClosure A B) :=
  let := hA.isNagata
  Ring.IsNagata.finite_integralClosure B

/-- Abstract integral-closure form of `IsAffinoidAlgebra.finite_integralClosure`. -/
theorem finite_of_isIntegralClosure (hA : IsAffinoidAlgebra K A) (B C : Type*) [CommRing B]
    [IsReduced B] [Algebra A B] [Algebra.EssFiniteType A B] [CommRing C] [Algebra A C]
    [Algebra C B] [IsScalarTower A C B] [IsIntegralClosure C A B] : Module.Finite A C :=
  let := hA.isNagata
  Ring.IsNagata.finite_of_isIntegralClosure B C

/-- For a reduced affinoid algebra `A` over a complete nonarchimedean field, the integral closure of
`A` in any localization `S` of `A` — in particular in its total ring of fractions
`Localization (nonZeroDivisors A)` — is a finite `A`-module
(Bosch–Güntzer–Remmert, *Non-Archimedean Analysis*, §6.1.2, Corollary 2). -/
theorem finite_integralClosure_of_isLocalization [IsReduced A] (hA : IsAffinoidAlgebra K A)
    (M : Submonoid A) (S : Type*) [CommRing S] [Algebra A S] [IsLocalization M S] :
    Module.Finite A (_root_.integralClosure A S) :=
  let := hA.isNagata
  Ring.IsNagata.finite_integralClosure_of_isLocalization M S

/-- The zero quotient `K ⧸ ⊤` is an affinoid algebra (with no Noether normalization injection from
a Tate algebra) and is Nagata. -/
example : IsAffinoidAlgebra K (K ⧸ (⊤ : Ideal K)) ∧ Ring.IsNagata (K ⧸ (⊤ : Ideal K)) :=
  let h0 := (isAffinoidAlgebra_self (K := K)).quotient (⊤ : Ideal K)
  ⟨h0, h0.isNagata⟩

end IsAffinoidAlgebra

end NormedField

section NontriviallyNormedField

namespace IsAffinoidAlgebra

variable {K A : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  [CommRing A] [Algebra K A]

/-- **Normalization of a reduced affinoid algebra is affinoid**
(Bosch–Güntzer–Remmert, *Non-Archimedean Analysis*, §6.1.2, Corollary 2). Over a nontrivially
normed complete nonarchimedean field `K`, the integral closure of any reduced affinoid `K`-algebra
`A` in any localization `S` of `A` (for instance in its total ring of fractions
`Localization (nonZeroDivisors A)`) is an affinoid `K`-algebra. -/
theorem integralClosure_of_isLocalization [IsReduced A] (hA : IsAffinoidAlgebra K A)
    (M : Submonoid A) (S : Type*) [CommRing S] [Algebra K S] [Algebra A S]
    [IsScalarTower K A S] [IsLocalization M S] :
    IsAffinoidAlgebra K (_root_.integralClosure A S) :=
  have := hA.finite_integralClosure_of_isLocalization M S
  hA.of_finite

/-- The normalization of any reduced affinoid `K`-algebra `A` in its total ring of fractions
`Localization (nonZeroDivisors A)` is both finite over `A` and an affinoid `K`-algebra. -/
example [IsReduced A] (hA : IsAffinoidAlgebra K A) :
    Module.Finite A (_root_.integralClosure A (Localization (nonZeroDivisors A))) ∧
      IsAffinoidAlgebra K (_root_.integralClosure A (Localization (nonZeroDivisors A))) :=
  ⟨hA.finite_integralClosure_of_isLocalization (nonZeroDivisors A) _,
    hA.integralClosure_of_isLocalization (nonZeroDivisors A) _⟩

end IsAffinoidAlgebra

end NontriviallyNormedField

end TauCeti
