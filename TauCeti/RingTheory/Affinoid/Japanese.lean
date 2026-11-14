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

Consequently (`TauCeti.Ring.IsNagata.finite_integralClosure`), for any reduced `A`-algebra `B`
essentially of finite type, the integral closure of `A` in `B` is a finite `A`-module. In
particular, when `A` is reduced, its normalization in any total ring of fractions `F` is a finite
`A`-module; when `K` is nontrivially normed, `TauCeti.IsAffinoidAlgebra.of_finite` shows that these
integral closures are again affinoid `K`-algebras.

## Main results

* `TauCeti.IsAffinoidAlgebra.isJapanese`: every affinoid domain over a complete ultrametric normed
  field is Japanese.
* `TauCeti.IsAffinoidAlgebra.isNagata`: every affinoid algebra over a complete ultrametric normed
  field is Nagata.
* `TauCeti.MvPowerSeries.isNagata_tate`: the Tate algebra `K⟨X₁, …, Xₙ⟩` in finitely many variables
  is Nagata.
* `TauCeti.IsAffinoidAlgebra.finite_integralClosure`: finiteness of the integral closure of an
  affinoid algebra in any reduced algebra essentially of finite type over it.
* `TauCeti.IsAffinoidAlgebra.finite_of_isIntegralClosure_of_isFractionRing` and
  `TauCeti.IsAffinoidAlgebra.finite_integralClosure_fractionRing`: finiteness of the normalization
  of a reduced affinoid algebra in its total ring of fractions.
* `TauCeti.IsAffinoidAlgebra.integralClosure`,
  `TauCeti.IsAffinoidAlgebra.of_isIntegralClosure_of_isFractionRing`, and
  `TauCeti.IsAffinoidAlgebra.integralClosure_fractionRing`: over a nontrivially normed complete
  ultrametric field, these normalizations are again affinoid `K`-algebras.

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

/-- **Finiteness of integral closures over an affinoid algebra.** For any affinoid algebra `A` over
a complete ultrametric normed field and any reduced `A`-algebra `B` essentially of finite type, the
integral closure of `A` in `B` is a finite `A`-module. -/
theorem finite_integralClosure (hA : IsAffinoidAlgebra K A) (B : Type*) [CommRing B] [IsReduced B]
    [Algebra A B] [Algebra.EssFiniteType A B] :
    Module.Finite A (_root_.integralClosure A B) := by
  have := hA.isNagata
  exact Ring.IsNagata.finite_integralClosure B

/-- **Finiteness of normalization of a reduced affinoid algebra.** For a reduced affinoid algebra
`A` over a complete ultrametric normed field, any total ring of fractions `F` of `A`, and any
integral closure `C` of `A` in `F`, `C` is a finite `A`-module. -/
theorem finite_of_isIntegralClosure_of_isFractionRing [IsReduced A] (hA : IsAffinoidAlgebra K A)
    (F : Type*) [CommRing F] [Algebra A F] [IsFractionRing A F]
    (C : Type*) [CommRing C] [Algebra A C] [Algebra C F] [IsScalarTower A C F]
    [IsIntegralClosure C A F] :
    Module.Finite A C := by
  have : IsReduced F := IsLocalization.isReduced (nonZeroDivisors A) F
  have : Algebra.EssFiniteType A F := .of_isLocalization (S := F) (nonZeroDivisors A)
  have := hA.finite_integralClosure F
  exact .equiv (IsIntegralClosure.equiv A (_root_.integralClosure A F) F C).toLinearEquiv

/-- The normalization `_root_.integralClosure A (FractionRing A)` of a reduced affinoid algebra `A`
in its canonical total ring of fractions is a finite `A`-module. -/
theorem finite_integralClosure_fractionRing [IsReduced A] (hA : IsAffinoidAlgebra K A) :
    Module.Finite A (_root_.integralClosure A (FractionRing A)) :=
  hA.finite_of_isIntegralClosure_of_isFractionRing (FractionRing A) _

end NormedField

section NontriviallyNormedField

variable {K : Type*} {A : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]
  [CompleteSpace K] [CommRing A] [Algebra K A]

/-- Over a nontrivially normed complete ultrametric field `K`, the integral closure of an affinoid
`K`-algebra `A` in any reduced `A`-algebra `B` essentially of finite type (with a compatible
`K`-algebra structure) is again an affinoid `K`-algebra. -/
theorem integralClosure (hA : IsAffinoidAlgebra K A) {B : Type*} [CommRing B] [IsReduced B]
    [Algebra K B] [Algebra A B] [IsScalarTower K A B] [Algebra.EssFiniteType A B] :
    IsAffinoidAlgebra K (_root_.integralClosure A B) := by
  have := hA.finite_integralClosure B
  exact hA.of_finite

/-- Over a nontrivially normed complete ultrametric field `K`, any integral closure `C` of a
reduced affinoid `K`-algebra `A` in a total ring of fractions `F` of `A` is an affinoid
`K`-algebra. -/
theorem of_isIntegralClosure_of_isFractionRing [IsReduced A] (hA : IsAffinoidAlgebra K A)
    (F : Type*) [CommRing F] [Algebra A F] [IsFractionRing A F]
    {C : Type*} [CommRing C] [Algebra K C] [Algebra A C] [IsScalarTower K A C]
    [Algebra C F] [IsScalarTower A C F] [IsIntegralClosure C A F] :
    IsAffinoidAlgebra K C := by
  have := hA.finite_of_isIntegralClosure_of_isFractionRing F C
  exact hA.of_finite

/-- Over a nontrivially normed complete ultrametric field `K`, the normalization
`_root_.integralClosure A (FractionRing A)` of a reduced affinoid `K`-algebra `A` in its total ring
of fractions is an affinoid `K`-algebra. -/
theorem integralClosure_fractionRing [IsReduced A] (hA : IsAffinoidAlgebra K A) :
    IsAffinoidAlgebra K (_root_.integralClosure A (FractionRing A)) :=
  hA.integralClosure

end NontriviallyNormedField

section Examples

/-- A non-reduced affinoid quotient such as `K⟨X⟩ ⧸ (X²)` is Nagata. -/
example {K : Type*} [NormedField K] [IsUltrametricDist K] [CompleteSpace K] :
    let T := IsRestricted.subring (R := K) (fun _ : Fin 1 ↦ 1)
    let x : T := ⟨_root_.MvPowerSeries.X 0, isRestricted_X _ 0⟩
    Ring.IsNagata (T ⧸ Ideal.span ({x ^ 2} : Set T)) :=
  (isAffinoidAlgebra_tate.quotient _).isNagata

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
  refine ⟨hA.finite_integralClosure_fractionRing, hA.integralClosure_fractionRing, fun Q _ ↦ ?_⟩
  have : IsNoetherianRing A := hA.isNoetherianRing
  have : IsArtinianRing (FractionRing A) :=
    IsFractionRing.isArtinianRing_of_isReduced A (FractionRing A)
  have : IsReduced (FractionRing A) :=
    IsLocalization.isReduced (nonZeroDivisors A) (FractionRing A)
  have : IsIntegrallyClosedIn (_root_.integralClosure A (FractionRing A)) (FractionRing A) :=
    IsIntegrallyClosedIn.of_isIntegralClosure (R := A)
  exact ⟨IsIntegrallyClosedIn.isDomain_localization_atPrime (FractionRing A) Q,
    IsIntegrallyClosedIn.isIntegrallyClosed_localization_atPrime (FractionRing A) Q⟩

end Examples

end TauCeti.IsAffinoidAlgebra

namespace TauCeti.MvPowerSeries

open _root_.MvPowerSeries

/-- **Tate algebras are Nagata.** Over any complete ultrametric normed field `K`, the Tate algebra
`K⟨X₁, …, Xₙ⟩` in finitely many variables is a Nagata ring. -/
theorem isNagata_tate {σ : Type*} {K : Type*} [NormedField K] [IsUltrametricDist K]
    [CompleteSpace K] [Finite σ] :
    Ring.IsNagata (IsRestricted.subring (R := K) (fun _ : σ ↦ 1)) :=
  isAffinoidAlgebra_tate.isNagata

end TauCeti.MvPowerSeries
