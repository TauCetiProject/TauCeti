/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Valuation.Discrete.IsDiscreteValuationRing
public import TauCeti.RingTheory.DiscreteValuationRing.IntegralClosure
public import TauCeti.RingTheory.Valuation.Discrete.Normalize
import Mathlib.RingTheory.Valuation.Integral
import TauCeti.RingTheory.DedekindDomain.AdicValuation.Basic
import TauCeti.RingTheory.DedekindDomain.Ideal.Basic
import TauCeti.RingTheory.Valuation.Discrete.IsDiscreteValuationRing
import TauCeti.RingTheory.Valuation.Integral.Basic

/-!
# The normalized extension of a henselian discrete valuation to a finite extension

Let `v` be a surjective `ℤᵐ⁰`-valued valuation of a field `F` whose valuation ring `R` is
henselian, for instance complete (Mathlib's `IsAdicComplete.henselianRing`), and let `E / F` be a
finite extension. There is exactly one surjective `ℤᵐ⁰`-valued valuation `w` of `E` that is at
most `1` on `R`. It is the *normalized extension* `Valuation.normalizedExtension v E hv` of `v`
to `E`: its valuation ring is the integral closure of `R` in `E`, and on `F` its order function is
a positive multiple of that of `v`, `ord_w a = e * ord_v a`. The multiple `e`, the ramification
index, is the index `Valuation.ordIndex` of the restriction of `w` to `F`.

Neither `E / F` nor the residue field extension needs to be separable, and the residue field of
`F` may be arbitrary. The construction is the adic valuation of the integral closure `S` of `R` in
`E`, which is a discrete valuation ring because `R` is henselian
(`TauCeti.integralClosure.isDiscreteValuationRing`, by Krull–Akizuki and the locality of integral
extensions of henselian rings). Uniqueness holds because a surjective valuation of `E` that is at
most `1` on `R` is at most `1` on `S`, hence is the adic valuation of a height one prime of `S`
(`Valuation.valuation_heightOneSpectrum`), and the maximal ideal is the only such prime.

In a finite tower `F ⊆ K ⊆ E` the restriction to `K` of the normalized extension to `E` is
equivalent to the normalized extension to `K`, and the ramification indices multiply.

## Main definitions

* `Valuation.normalizedExtension`: the normalized extension of `v` to a finite extension `E`.

## Main results

* `Valuation.isDiscreteValuationRing_integralClosure`: the integral closure of the valuation ring
  of `v` in `E` is a discrete valuation ring.
* `Valuation.normalizedExtension_def`: the normalized extension is the adic valuation of the
  integral closure.
* `Valuation.normalizedExtension_surjective`: the normalized extension is surjective.
* `Valuation.normalizedExtension_le_one_iff`: its valuation ring is the integral closure of the
  valuation ring of `v`; `Valuation.valuationSubring_normalizedExtension` states this as an
  equality of subrings.
* `Valuation.isEquiv_comap_normalizedExtension`: its restriction to `F` is equivalent to `v`.
* `Valuation.ord_normalizedExtension_algebraMap` and
  `Valuation.ordIndex_comap_normalizedExtension_pos`: on `F` its order function is the positive
  ramification index times the order function of `v`.
* `Valuation.eq_normalizedExtension_of_forall_le_one` and
  `Valuation.eq_normalizedExtension_of_isEquiv`: uniqueness among surjective valuations of `E`.
* `Valuation.normalizedExtension_self`: the normalized extension to `F` itself is `v`.
* `Valuation.isEquiv_comap_normalizedExtension_of_isScalarTower` and
  `Valuation.ordIndex_comap_normalizedExtension_eq_mul`: compatibility with a finite tower, and
  multiplicativity of ramification indices.

## References

* J.-P. Serre, *Local Fields*, Chapter II, §2, Proposition 3.
* P. Gille and T. Szamuely, *Central Simple Algebras and Galois Cohomology*, 2nd ed., Appendix
  A.6, Proposition A.6.8.
* The Stacks Project, Tag 09E4 and Remark 15.116.1 (Tag 09EM).
-/

public section

open IsLocalRing IsDedekindDomain

open scoped WithZero

namespace Valuation

variable {F : Type*} [Field F] (v : Valuation F ℤᵐ⁰)
  [HenselianRing v.valuationSubring (maximalIdeal v.valuationSubring)]

section Extension

variable (E : Type*) [Field E] [Algebra F E] [FiniteDimensional F E]

/-- For a surjective `ℤᵐ⁰`-valued valuation `v` of `F` with henselian valuation ring, the
integral closure of the valuation ring of `v` in a finite extension `E` is a discrete valuation
ring. This is not an instance, because it depends on the surjectivity hypothesis `hv`. -/
theorem isDiscreteValuationRing_integralClosure (hv : Function.Surjective v) :
    IsDiscreteValuationRing (integralClosure v.valuationSubring E) :=
  have := valuationSubring_isDiscreteValuationRing_of_surjective v hv
  TauCeti.integralClosure.isDiscreteValuationRing v.valuationSubring F E

/-- The **normalized extension** of a surjective `ℤᵐ⁰`-valued valuation `v` of `F`, whose
valuation ring is henselian, to a finite extension `E` of `F`: the unique surjective
`ℤᵐ⁰`-valued valuation of `E` that is at most `1` on the valuation ring of `v`
(`Valuation.eq_normalizedExtension_of_forall_le_one`). It is the adic valuation of the integral
closure of the valuation ring of `v` in `E`, which is a discrete valuation ring. -/
noncomputable def normalizedExtension (hv : Function.Surjective v) : Valuation E ℤᵐ⁰ :=
  have := isDiscreteValuationRing_integralClosure v E hv
  have := integralClosure.isFractionRing_of_finite_extension (A := v.valuationSubring) F E
  (IsDiscreteValuationRing.maximalIdeal (integralClosure v.valuationSubring E)).valuation E

variable (hv : Function.Surjective v)

/-- The normalized extension is the adic valuation of the maximal ideal of the integral closure of
the valuation ring of `v` in `E`. -/
theorem normalizedExtension_def [IsDiscreteValuationRing (integralClosure v.valuationSubring E)]
    [IsFractionRing (integralClosure v.valuationSubring E) E] :
    v.normalizedExtension E hv =
      (IsDiscreteValuationRing.maximalIdeal (integralClosure v.valuationSubring E)).valuation E :=
  (rfl)

/-- The normalized extension is surjective onto `ℤᵐ⁰`. -/
theorem normalizedExtension_surjective : Function.Surjective (v.normalizedExtension E hv) := by
  have := isDiscreteValuationRing_integralClosure v E hv
  have := integralClosure.isFractionRing_of_finite_extension (A := v.valuationSubring) F E
  rw [normalizedExtension_def]
  exact HeightOneSpectrum.valuation_surjective E _

/-- **The valuation ring of the normalized extension is the integral closure** of the valuation
ring of `v` in `E`. -/
theorem normalizedExtension_le_one_iff {x : E} :
    v.normalizedExtension E hv x ≤ 1 ↔ IsIntegral v.valuationSubring x := by
  have := isDiscreteValuationRing_integralClosure v E hv
  have := integralClosure.isFractionRing_of_finite_extension (A := v.valuationSubring) F E
  rw [normalizedExtension_def]
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · obtain ⟨y, rfl⟩ := IsDiscreteValuationRing.exists_lift_of_le_one h
    exact y.property
  · exact HeightOneSpectrum.valuation_le_one _ (⟨x, h⟩ : integralClosure v.valuationSubring E)

/-- The valuation subring of the normalized extension is the integral closure of the valuation
ring of `v` in `E`. -/
theorem valuationSubring_normalizedExtension :
    (v.normalizedExtension E hv).valuationSubring.toSubring =
      (integralClosure v.valuationSubring E).toSubring := by
  ext x
  exact normalizedExtension_le_one_iff v E hv

/-- **The restriction of the normalized extension to `F` is equivalent to `v`.** -/
theorem isEquiv_comap_normalizedExtension :
    ((v.normalizedExtension E hv).comap (algebraMap F E)).IsEquiv v :=
  isEquiv_iff_val_le_one.mpr fun {a} ↦ by
    rw [comap_apply, normalizedExtension_le_one_iff, isIntegral_algebraMap_iff_le_one]

/-- **On `F`, the order function of the normalized extension is the ramification index times
that of `v`.** The ramification index is the index of the restriction of the normalized
extension to `F`, which is positive by `Valuation.ordIndex_comap_normalizedExtension_pos`. -/
theorem ord_normalizedExtension_algebraMap (a : F) :
    ord (v.normalizedExtension E hv) (algebraMap F E a) =
      ordIndex ((v.normalizedExtension E hv).comap (algebraMap F E)) * ord v a := by
  rw [← ord_comap]
  exact IsEquiv.ord_eq_ordIndex_mul (isEquiv_comap_normalizedExtension v E hv) hv a

/-- **The ramification index of the normalized extension is positive.** -/
theorem ordIndex_comap_normalizedExtension_pos :
    0 < ordIndex ((v.normalizedExtension E hv).comap (algebraMap F E)) :=
  (isEquiv_comap_normalizedExtension v E hv).ordIndex_pos hv

/-- **Uniqueness of the normalized extension.** A surjective `ℤᵐ⁰`-valued valuation of `E` that is
at most `1` on the valuation ring of `v` is the normalized extension. -/
theorem eq_normalizedExtension_of_forall_le_one {w : Valuation E ℤᵐ⁰}
    (hw : Function.Surjective w) (h : ∀ a : F, v a ≤ 1 → w (algebraMap F E a) ≤ 1) :
    w = v.normalizedExtension E hv := by
  have := isDiscreteValuationRing_integralClosure v E hv
  have := integralClosure.isFractionRing_of_finite_extension (A := v.valuationSubring) F E
  have := isNontrivial_of_surjective hw
  -- The ring of integers of `w` is integrally closed in `E` and contains the valuation ring of
  -- `v`, so it contains the integral closure `S` of the latter.
  have hS : ∀ s : integralClosure v.valuationSubring E,
      w (algebraMap (integralClosure v.valuationSubring E) E s) ≤ 1 := fun s ↦
    (Subring.integralClosure_le_iff (R := v.valuationSubring) (T := w.integer).mpr
      fun r ↦ h r r.property) s.property
  -- So `w` is the adic valuation of a height one prime of the discrete valuation ring `S`, and the
  -- maximal ideal is the only one.
  rw [normalizedExtension_def, ← HeightOneSpectrum.eq_maximalIdeal (heightOneSpectrum _ w hS),
    valuation_heightOneSpectrum hw hS]

/-- **Uniqueness of the normalized extension.** A surjective `ℤᵐ⁰`-valued valuation of `E` whose
restriction to `F` is equivalent to `v` is the normalized extension. -/
theorem eq_normalizedExtension_of_isEquiv {w : Valuation E ℤᵐ⁰} (hw : Function.Surjective w)
    (h : (w.comap (algebraMap F E)).IsEquiv v) : w = v.normalizedExtension E hv :=
  eq_normalizedExtension_of_forall_le_one v E hv hw fun _ ha ↦ h.le_one_iff_le_one.mpr ha

end Extension

/-- **The normalized extension of `v` to `F` itself is `v`.** -/
@[simp]
theorem normalizedExtension_self (hv : Function.Surjective v) : v.normalizedExtension F hv = v :=
  (eq_normalizedExtension_of_forall_le_one v F hv hv fun _ ha ↦ by
    rwa [Algebra.algebraMap_self, RingHom.id_apply]).symm

section Tower

variable (K E : Type*) [Field K] [Field E] [Algebra F K] [Algebra F E] [Algebra K E]
  [IsScalarTower F K E] [FiniteDimensional F K] [FiniteDimensional F E]
  (hv : Function.Surjective v)

/-- **Normalized extensions in a tower.** For finite extensions `F ⊆ K ⊆ E`, the restriction to
`K` of the normalized extension of `v` to `E` is equivalent to the normalized extension of `v` to
`K`. -/
theorem isEquiv_comap_normalizedExtension_of_isScalarTower :
    ((v.normalizedExtension E hv).comap (algebraMap K E)).IsEquiv (v.normalizedExtension K hv) :=
  isEquiv_iff_val_le_one.mpr fun {x} ↦ by
    rw [comap_apply, normalizedExtension_le_one_iff, normalizedExtension_le_one_iff,
      isIntegral_algebraMap_iff]

/-- **Ramification indices multiply in a tower** `F ⊆ K ⊆ E` of finite extensions. -/
theorem ordIndex_comap_normalizedExtension_eq_mul :
    ordIndex ((v.normalizedExtension E hv).comap (algebraMap F E)) =
      ordIndex ((v.normalizedExtension E hv).comap (algebraMap K E)) *
        ordIndex ((v.normalizedExtension K hv).comap (algebraMap F K)) := by
  refine ordIndex_eq_mul_of_forall_ord_eq _ _ fun a ↦ ?_
  rw [ord_comap, ord_comap, IsScalarTower.algebraMap_apply F K E, ← ord_comap _ (algebraMap K E)]
  exact IsEquiv.ord_eq_ordIndex_mul (isEquiv_comap_normalizedExtension_of_isScalarTower v K E hv)
    (normalizedExtension_surjective v K hv) _

end Tower

end Valuation
