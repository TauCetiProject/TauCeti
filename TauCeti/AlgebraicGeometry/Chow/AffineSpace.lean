/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.AlgebraicCycle.PrimeElement
public import TauCeti.AlgebraicGeometry.Chow.DivisorClass
public import TauCeti.AlgebraicGeometry.Chow.Localization
public import Mathlib.RingTheory.Polynomial.UniqueFactorization
import Mathlib.RingTheory.KrullDimension.Polynomial
import TauCeti.AlgebraicGeometry.CartierDivisor.Factorial
import TauCeti.AlgebraicGeometry.Morphisms.FiniteType.Basic
import TauCeti.AlgebraicGeometry.StructureSheaf.Stalk

/-!
# Chow groups of affine spaces in codimension one

Let `κ` be a field and `R` a finitely generated `κ`-algebra of Krull dimension `n` which is a
unique factorization domain. Every Weil divisor on `Spec R` is principal
(`SchemeWeilDivisor.subsingleton_classGroup_of_uniqueFactorizationMonoid`), so by the divisor class
comparison `Cl(Spec R) ≃ CH_{n-1}(Spec R)` (`Chow.classGroupEquivChowGroup`) the Chow group of
codimension-one cycles vanishes:

* `Chow.subsingleton_chowGroup_of_uniqueFactorizationMonoid`: `CH_{n-1}(Spec R) = 0`.

The polynomial rings `κ[X₁, …, Xₙ]` are such algebras, which gives the following computations on
affine space `𝔸ⁿ_κ = Spec κ[X₁, …, Xₙ]` and the affine line `𝔸¹_κ = Spec κ[X]`.

* `Chow.subsingleton_chowGroup_affineSpace`: `CH_n(𝔸ⁿ⁺¹_κ) = 0`.
* `Chow.div_X_affineLine`: the principal cycle of the coordinate `t` on `𝔸¹_κ` is the cycle of the
  origin, `[0] = div(t)`.
* `Chow.subsingleton_chowGroup_zero_affineLine`: `CH_0(𝔸¹_κ) = 0`; every closed point `x` of `𝔸¹_κ`
  is the zero locus of a prime polynomial `p`, and `[x] = div(p)`.
* `Chow.subsingleton_chowGroup_zero_multiplicativeGroup`: on the open complement
  `𝔾_m = Spec κ[X][X⁻¹]` of the origin, `CH_0(𝔾_m) = 0`, as the image of `CH_0(𝔸¹_κ)` under the
  surjective restriction `CH_0(𝔸¹_κ) → CH_0(𝔾_m) → 0` of the localization sequence
  (`Chow.ChowGroup.restrict_surjective`).

These are the computations on `𝔸¹` and `𝔾_m` that accompany the localization sequence of Fulton,
*Intersection Theory*, Proposition 1.8.
-/

public section

open AlgebraicGeometry Polynomial

universe u

namespace TauCeti.AlgebraicGeometry.Chow

variable (κ : Type u) [Field κ]

/-- **The Chow group of codimension-one cycles of a unique factorization domain vanishes.** For a
finitely generated algebra `R` of Krull dimension `n` over a field `κ` which is a unique
factorization domain, `CH_{n-1}(Spec R) = 0`: every Weil divisor on `Spec R` is principal. -/
theorem subsingleton_chowGroup_of_uniqueFactorizationMonoid {R : Type u} [CommRing R] [IsDomain R]
    [IsNoetherianRing R] [Algebra κ R] [Algebra.FiniteType κ R] [UniqueFactorizationMonoid R]
    {n : ℕ}
    (hn : ringKrullDim R = n) :
    Subsingleton (ChowGroup (Spec (.of R)) (n - 1)) := by
  let _ : (Spec (.of R)).Over (Spec (.of κ)) := ⟨Spec.algebraMap κ R⟩
  have : LocallyOfFiniteType (Spec (.of R) ↘ Spec (.of κ)) :=
    LocallyOfFiniteType.Spec_algebraMap
  have hdim : topologicalKrullDim (Spec (.of R)) = n :=
    (PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim (R := R)).trans hn
  exact (classGroupEquivChowGroup κ hdim).symm.subsingleton

/-- The Chow group `CH_n(𝔸ⁿ⁺¹_κ)` of codimension-one cycles on affine space vanishes. -/
theorem subsingleton_chowGroup_affineSpace (n : ℕ) :
    Subsingleton (ChowGroup (Spec (.of (MvPolynomial (Fin (n + 1)) κ))) n) := by
  have := subsingleton_chowGroup_of_uniqueFactorizationMonoid κ
    (R := MvPolynomial (Fin (n + 1)) κ) (n := n + 1) (by
      rw [MvPolynomial.ringKrullDim_of_isNoetherianRing_of_finite, ringKrullDim_eq_zero_of_field,
        Nat.card_eq_fintype_card, Fintype.card_fin]
      simp)
  simpa using this

/-- On the affine line `𝔸¹_κ = Spec κ[X]`, the principal cycle of the coordinate `t`
is the cycle of the origin `x = (t)`: `[0] = div(t)`. The coordinate is given as the image in the
function field of the germ of `X` in the local ring at the origin. -/
theorem div_X_affineLine [DecidableEq (Spec (.of κ[X]))] {x : Spec (.of κ[X])}
    (hx : x.asIdeal = Ideal.span {X}) {t : (Spec (.of κ[X])).functionFieldˣ}
    (ht : (t : (Spec (.of κ[X])).functionField) =
      algebraMap ((Spec (.of κ[X])).presheaf.stalk x) _ (StructureSheaf.toStalk κ[X] x X)) :
    AlgebraicCycle.div t = Function.locallyFinsuppWithin.single x 1 :=
  AlgebraicCycle.div_eq_single_of_prime prime_X hx
    (ht.trans (StructureSheaf.algebraMap_functionField_toStalk x X))

/-- The Chow group `CH_0(𝔸¹_κ)` of zero-cycles on the affine line vanishes: every closed
point is the zero locus of a prime polynomial `p`, and its cycle is `div(p)`. -/
theorem subsingleton_chowGroup_zero_affineLine :
    Subsingleton (ChowGroup (Spec (.of κ[X])) 0) := by
  have := subsingleton_chowGroup_of_uniqueFactorizationMonoid κ (R := κ[X]) (n := 1) (by
    rw [Polynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field]
    norm_num)
  simpa using this

/-- The Chow group `CH_0(𝔾_m)` of zero-cycles on `𝔾_m = Spec κ[X][X⁻¹]` vanishes: the
restriction `CH_0(𝔸¹_κ) → CH_0(𝔾_m) → 0` along the open immersion of the complement of the origin
is surjective, and `CH_0(𝔸¹_κ) = 0`. -/
theorem subsingleton_chowGroup_zero_multiplicativeGroup :
    Subsingleton (ChowGroup (Spec (.of (Localization.Away (X : κ[X])))) 0) := by
  let _ : (Spec (.of κ[X])).Over (Spec (.of κ)) := ⟨Spec.algebraMap κ κ[X]⟩
  have : LocallyOfFiniteType (Spec (.of κ[X]) ↘ Spec (.of κ)) :=
    LocallyOfFiniteType.Spec_algebraMap
  -- the open immersion `𝔾_m ⟶ 𝔸¹_κ` of the complement of the origin
  let j := Spec.map (CommRingCat.ofHom (algebraMap κ[X] (Localization.Away (X : κ[X]))))
  have : IsOpenImmersion j := IsOpenImmersion.of_isLocalization (X : κ[X])
  have := subsingleton_chowGroup_zero_affineLine κ
  exact (ChowGroup.restrict_surjective κ j (n := 0)).subsingleton

end TauCeti.AlgebraicGeometry.Chow
