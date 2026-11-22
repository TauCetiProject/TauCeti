/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.AdicSpace.Spa.Basic
public import TauCeti.RingTheory.Huber.Pair
import Mathlib.RingTheory.Ideal.MinimalPrime.Localization
import TauCeti.AlgebraicGeometry.AdicSpace.RestrictToIdeal
import TauCeti.AlgebraicGeometry.AdicSpace.ValuationSpectrum.Center
import TauCeti.RingTheory.Valuation.Continuous.Horizontal
import TauCeti.RingTheory.Valuation.Continuous.TopologicallyNilpotent
import TauCeti.Topology.Algebra.Ring.Subring

/-!
# Points of an adic spectrum with prescribed centre

A point `x` of `Spa(A, A⁺)` is bounded by `1` on `A⁺`, so the elements of `A⁺` of value strictly
below `1` at `x` form a prime ideal of `A⁺`, the *centre* of `x`. A continuous valuation is
strictly below `1` at every topologically nilpotent element, so the centre contains every element
of `A⁺` that is topologically nilpotent in `A`. The centre map `x ↦ {a ∈ A⁺ : |a(x)| < 1}` is the
specialization map `Spa(A, A⁺) → Spec(A⁺ ⧸ A°°)` of Gleason, Definition 4.1.

This file shows that for a Tate ring the centre map is onto: every prime ideal `𝔭` of `A⁺` that
contains the topologically nilpotent elements of `A⁺` is the centre of a point of `Spa(A, A⁺)`
(`TauCeti.ValuationSpectrum.forall_isTopologicallyNilpotent_mem_iff_exists_mem_spa`). The
construction needs only that `A⁺` is an open subring containing a pseudouniformiser `ϖ ∈ 𝔭`
(`TauCeti.ValuationSpectrum.exists_mem_spa_forall_valuation_lt_one_iff_mem`).

## The construction

* Since `ϖ` is a unit of `A`, it is a non-zero-divisor of `A⁺`, so a minimal prime `𝔮 ⊆ 𝔭` of
  `A⁺` does not contain it.
* Some point `v` of `Spv A⁺`, bounded by `1` on `A⁺`, has support `𝔮` and centre `𝔭`
  (`TauCeti.ValuationSpectrum.exists_supp_eq_and_valuation_lt_one_iff_mem`).
* Inverting `ϖ` in the open subring `A⁺` recovers `A` (`Subring.isLocalizationAway_of_isOpen`),
  and `ϖ ∉ supp v`, so `v` extends to a point `w` of `Spv A`.
* The value `w(ϖ) < 1` need not be cofinal in the value group of `w`, so `w` need not be
  continuous. Restricting `w` to its characteristic subgroup discards the values below every
  power of `w(ϖ)`. This keeps every value `≥ 1` and every comparison with `1`, and the result is
  continuous because its open unit ball contains the neighbourhood `ϖ A⁺` of `0`
  (`Valuation.isContinuous_restrictToIdeal_top`).

## Main results

* `TauCeti.ValuationSpectrum.exists_mem_spa_forall_valuation_lt_one_iff_mem`: for an open
  subring `A⁺` containing a pseudouniformiser `ϖ`, every prime `𝔭` of `A⁺` with `ϖ ∈ 𝔭` is the
  centre of a point of `Spa(A, A⁺)`.
* `TauCeti.ValuationSpectrum.forall_isTopologicallyNilpotent_mem_iff_exists_mem_spa`: for a
  Huber pair `(A, A⁺)` with `A` a Tate ring, a prime of `A⁺` is the centre of a point of
  `Spa(A, A⁺)` exactly when it contains every element of `A⁺` topologically nilpotent in `A`.

## References

* I. Gleason, *Specialization maps for Scholze's category of diamonds*, arXiv:2012.05483,
  Definition 4.1 (the specialization map) and Proposition 4.2 (its surjectivity).
* B. Bhatt, *Lecture notes for a class on perfectoid spaces*, Remark 7.4.12.
* [T. Wedhorn, *Adic Spaces*][wedhorn_adic] (arXiv:1910.05934v1), §7.1.2 and Theorem 7.10, for
  the restriction to the characteristic subgroup.
-/

public section

open Topology TauCeti.Huber

namespace TauCeti.ValuationSpectrum

variable {A : Type*} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]

/-- **Every prime of `A⁺` containing a pseudouniformiser is a centre.** Let `A⁺` be an open
subring of `A` containing a pseudouniformiser `ϖ` of `A`. Every prime ideal `𝔭` of `A⁺` with
`ϖ ∈ 𝔭` is the centre `{a ∈ A⁺ : |a(x)| < 1}` of some point `x` of `Spa(A, A⁺)`. -/
theorem exists_mem_spa_forall_valuation_lt_one_iff_mem {Aplus : Subring A}
    (hopen : IsOpen (Aplus : Set A)) {ϖ : Aplus} (hϖ : IsPseudoUniformizer (ϖ : A))
    (𝔭 : Ideal Aplus) [𝔭.IsPrime] (hϖ𝔭 : ϖ ∈ 𝔭) :
    ∃ x ∈ spa Aplus, ∀ a : Aplus, x.valuation a < 1 ↔ a ∈ 𝔭 := by
  -- a minimal prime `𝔮 ⊆ 𝔭` avoids the non-zero-divisor `ϖ`
  obtain ⟨𝔮, h𝔮, h𝔮𝔭⟩ := Ideal.exists_minimalPrimes_le (bot_le : ⊥ ≤ 𝔭)
  have : 𝔮.IsPrime := h𝔮.isPrime
  have hϖ𝔮 : ϖ ∉ 𝔮 := fun h ↦ notMem_nonZeroDivisors_of_mem_mem_minimalPrimes h h𝔮 <|
    mem_nonZeroDivisors_of_injective (f := Aplus.subtype) Subtype.val_injective
      hϖ.isUnit.mem_nonZeroDivisors
  -- a point `v` of `Spv A⁺` with support `𝔮` and centre `𝔭`, extended to `w ∈ Spv A`
  obtain ⟨v, hsupp, hle, hlt⟩ := exists_supp_eq_and_valuation_lt_one_iff_mem h𝔮𝔭
  have := Aplus.isLocalizationAway_of_isOpen hopen ϖ hϖ.isTopologicallyNilpotent hϖ.isUnit
  let w := localizationComapSection (.powers ϖ) A v
    (Submonoid.powers_le.mpr (hsupp ▸ Ideal.mem_primeCompl_iff.mpr hϖ𝔮))
  have hw : comap (algebraMap Aplus A) w = v := comap_localizationComapSection _ _ v _
  have hwle (b : Aplus) : w.valuation b ≤ 1 := (valuation_map_le_one_iff hw b).mpr (hle b)
  have hwlt (b : Aplus) : w.valuation b < 1 ↔ b ∈ 𝔭 := (valuation_map_lt_one_iff hw b).trans (hlt b)
  -- the open unit ball of `w` contains the neighbourhood `ϖ A⁺` of `0`
  have hU : {a : A | w.valuation a < 1} ∈ 𝓝 0 := by
    let u := hϖ.isUnit.unit
    have hcont : Continuous fun a : A ↦ ((u⁻¹ : Aˣ) : A) * a := continuous_const.mul continuous_id
    refine Filter.mem_of_superset (hcont.continuousAt.preimage_mem_nhds
      (hopen.mem_nhds (by simp))) fun a ha ↦ ?_
    have ha' : a = ϖ * (((u⁻¹ : Aˣ) : A) * a) := by rw [← mul_assoc, hϖ.isUnit.mul_val_inv, one_mul]
    rw [Set.mem_ofPred_eq, ha', map_mul]
    exact mul_lt_one_of_lt_of_le ((hwlt ϖ).mpr hϖ𝔭) (hwle ⟨_, ha⟩)
  -- restrict `w` to its characteristic subgroup
  let hfg : ∃ J : Ideal A, J.FG ∧ (⊤ : Ideal A).radical = J.radical := ⟨⊤, Ideal.fg_top A, rfl⟩
  let r := w.valuation.restrictToIdeal ⊤ hfg
  have hr1 : r 1 ≠ 0 := by simp
  have hrlt (a : A) : (ofValuation r).valuation a < 1 ↔ w.valuation a < 1 := by
    rw [(isEquiv_valuation_ofValuation r).lt_one_iff_lt_one, ← map_one r,
      w.valuation.restrictToIdeal_lt_restrictToIdeal_iff ⊤ hfg hr1, map_one]
  refine ⟨ofValuation r, (mem_spa_iff _ _).mpr ⟨?_, fun a ha ↦ ?_⟩, fun a ↦ (hrlt a).trans
    (hwlt a)⟩
  · rw [isContinuous_ofValuation_iff]
    exact w.valuation.isContinuous_restrictToIdeal_top hU
  · rw [vle_ofValuation, w.valuation.restrictToIdeal_le_iff]
    exact Or.inr ⟨hr1, by simpa using hwle ⟨a, ha⟩⟩

/-- **The centres of points of `Spa(A, A⁺)` for a Tate ring.** For a Huber pair `(A, A⁺)` with
`A` a Tate ring, a prime ideal `𝔭` of `A⁺` contains every element of `A⁺` that is topologically
nilpotent in `A` exactly when it is the centre `{a ∈ A⁺ : |a(x)| < 1}` of some point `x` of
`Spa(A, A⁺)`. These primes form the closed subset `V(A°°) = Spec(A⁺ ⧸ A°°)` of `Spec A⁺`, so the
specialization map `Spa(A, A⁺) → Spec(A⁺ ⧸ A°°)` is onto. -/
theorem forall_isTopologicallyNilpotent_mem_iff_exists_mem_spa [IsTateRing A] (P : Pair A)
    (𝔭 : Ideal P.plus) [𝔭.IsPrime] :
    (∀ a : P.plus, IsTopologicallyNilpotent (a : A) → a ∈ 𝔭) ↔
      ∃ x ∈ spa P.plus, ∀ a : P.plus, x.valuation a < 1 ↔ a ∈ 𝔭 := by
  refine ⟨fun h𝔭 ↦ ?_, fun ⟨x, hx, hx𝔭⟩ a ha ↦ (hx𝔭 a).mp ?_⟩
  · obtain ⟨ϖ, hϖ⟩ := P.isRingOfIntegralElements.exists_isPseudoUniformizer
    exact exists_mem_spa_forall_valuation_lt_one_iff_mem P.isRingOfIntegralElements.isOpen hϖ 𝔭
      (h𝔭 ϖ hϖ.isTopologicallyNilpotent)
  · exact Valuation.IsContinuous.lt_one_of_isTopologicallyNilpotent
      ((isContinuous_def _).mp ((mem_spa_iff _ _).mp hx).1) ha

end TauCeti.ValuationSpectrum
