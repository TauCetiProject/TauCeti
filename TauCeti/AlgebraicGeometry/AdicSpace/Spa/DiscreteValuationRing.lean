/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Valuation.Discrete.IsDiscreteValuationRing
public import Mathlib.Topology.Algebra.Nonarchimedean.AdicTopology
public import TauCeti.AlgebraicGeometry.AdicSpace.Spa.Analytic

import Mathlib.RingTheory.Filtration
import TauCeti.AlgebraicGeometry.AdicSpace.Spa.Points
import TauCeti.RingTheory.Valuation.Continuous.TopologicallyNilpotent
import TauCeti.RingTheory.Valuation.Discrete.IsDiscreteValuationRing
import TauCeti.RingTheory.Valuation.ValuationRing
import TauCeti.Topology.Algebra.Nonarchimedean.AdicTopology

/-!
# The adic spectrum of a discrete valuation ring

Let `R` be a discrete valuation ring with maximal ideal `𝔪`, carrying its `𝔪`-adic topology. This
file computes `Spa (R, R)`: it has exactly two points.

* The point `η` of the `𝔪`-adic valuation, `ofValuation (maximalIdeal R).intValuation`. It
  compares elements by divisibility, `η(x) ≤ η(y) ↔ y ∣ x`
  (`intValuation_le_intValuation_iff_dvd`), and its support is
  `⊥`, which is not open, so `η` is analytic.
* The trivial valuation `s = trivialSection ⊤` of the maximal ideal, `⊤` being the closed point of
  `Spec R`. Its support `𝔪` is open, so `s` is not analytic.

Moreover `η` specializes to `s`. So `Spa (R, R)` is a Huber affinoid whose analytic locus is the
single point `η`, in contrast with Tate affinoids, all of whose points are analytic
(`TauCeti.ValuationSpectrum.spaAnalytic_eq_spa_of_isTateRing`). The basic example is
`Spa (ℤ_p, ℤ_p)`, treated in `TauCeti.AlgebraicGeometry.AdicSpace.Spa.PadicInt`.

No completeness of `R` is needed. The proof sorts points by their support, a prime ideal of `R`,
hence `⊥` or `𝔪`. On a point with support `𝔪`, units have value `1` and nonunits value `0`
(`TauCeti.ValuationSpectrum.eq_trivialSection_of_supp_eq`). On a point with support `⊥`, the
nonunits are topologically nilpotent and so have value below `1`, which forces comparison by
divisibility (`MonoidWithZeroHom.le_iff_dvd`).

## Main results

* `TauCeti.IsDiscreteValuationRing.isContinuous_ofValuation_intValuation`: `η` is continuous for
  the `𝔪`-adic topology, so it lies in `Spa (R, A⁺)` for every plus ring `A⁺`
  (`TauCeti.IsDiscreteValuationRing.ofValuation_intValuation_mem_spa`).
* `TauCeti.IsDiscreteValuationRing.eq_ofValuation_intValuation_of_supp_eq_bot`: `η` is the only
  point of `Spa (R, R)` with support `⊥`.
* `TauCeti.IsDiscreteValuationRing.spa_top_eq`: `Spa (R, R) = {η, s}`.
* `TauCeti.IsDiscreteValuationRing.ofValuation_intValuation_ne_trivialSection_top`: the two points
  are distinct.
* `TauCeti.IsDiscreteValuationRing.ofValuation_intValuation_specializes_trivialSection_top`:
  `η ⤳ s`.
* `TauCeti.IsDiscreteValuationRing.isAnalyticPoint_ofValuation_intValuation` and
  `TauCeti.IsDiscreteValuationRing.spaAnalytic_top_eq`: `η` is analytic, and the analytic locus of
  `Spa (R, R)` is `{η}`.

## References

* [T. Wedhorn, *Adic Spaces*][wedhorn_adic] (arXiv:1910.05934v1), Remark 4.6 for the trivial
  valuation of a prime, Definition 7.23 for `Spa`, and Definition 7.39 for analytic points.
-/

public section

namespace TauCeti.IsDiscreteValuationRing

open IsLocalRing IsDedekindDomain TauCeti.ValuationSpectrum

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]

/-- The point of the `𝔪`-adic valuation differs from the trivial valuation of the maximal ideal:
their supports are `⊥` and the nonzero maximal ideal. -/
theorem ofValuation_intValuation_ne_trivialSection_top :
    ofValuation (_root_.IsDiscreteValuationRing.maximalIdeal R).intValuation ≠
      trivialSection (⊤ : PrimeSpectrum R) := fun h ↦ by
  have := congrArg supp h
  rw [supp_ofValuation, HeightOneSpectrum.supp_intValuation, ← suppFun_asIdeal,
    suppFun_trivialSection, PrimeSpectrum.asIdeal_top] at this
  exact _root_.IsDiscreteValuationRing.not_a_field R this.symm

/-- **The point of the `𝔪`-adic valuation specializes to the trivial valuation of the maximal
ideal.** Every basic open `{v(f) ≤ v(g) ≠ 0}` containing the latter has `g` a unit, and so
contains the former. -/
theorem ofValuation_intValuation_specializes_trivialSection_top :
    ofValuation (_root_.IsDiscreteValuationRing.maximalIdeal R).intValuation ⤳
      trivialSection (⊤ : PrimeSpectrum R) := by
  refine specializes_of_forall_mem_basicOpen fun f g hg ↦ ?_
  simp only [mem_basicOpen_iff, trivialSection_vle_iff, PrimeSpectrum.asIdeal_top,
    Submodule.zero_mem, not_true_eq_false, or_false] at hg
  have hu : IsUnit g := not_not.mp ((mem_maximalIdeal g).not.mp hg.2)
  simp only [mem_basicOpen_iff, vle_ofValuation,
    intValuation_le_intValuation_iff_dvd, zero_dvd_iff]
  exact ⟨hu.dvd, hu.ne_zero⟩

variable [TopologicalSpace R]

/-- **The point of the `𝔪`-adic valuation is continuous** for the `𝔪`-adic topology. Below a
nonzero value `η(b)` lie all multiples of a power of `𝔪` that avoids `b`, and such a power exists
by Krull's intersection theorem. -/
theorem isContinuous_ofValuation_intValuation (hR : IsAdic (maximalIdeal R)) :
    (ofValuation (_root_.IsDiscreteValuationRing.maximalIdeal R).intValuation).IsContinuous := by
  have : IsTopologicalRing R := hR ▸ (maximalIdeal R).nonarchimedean.toIsTopologicalRing
  set w := (_root_.IsDiscreteValuationRing.maximalIdeal R).intValuation
  rw [isContinuous_ofValuation_iff, Valuation.isContinuous_iff_forall_ne_zero]
  intro b hb
  obtain ⟨n, hn⟩ : ∃ n, b ∉ maximalIdeal R ^ n := by
    by_contra! h
    have hmem : b ∈ ⨅ i, maximalIdeal R ^ i := (Submodule.mem_iInf _).mpr h
    rw [Ideal.iInf_pow_eq_bot_of_isLocalRing _ (maximalIdeal.isMaximal R).ne_top,
      Ideal.mem_bot] at hmem
    exact hb (by simp [hmem])
  refine AddSubgroup.isOpen_mono (H₁ := (maximalIdeal R ^ n).toAddSubgroup)
    (H₂ := w.ltAddSubgroup (Units.mk0 (w b) hb)) (fun a ha ↦ ?_) (hR.isOpen_pow n)
  rw [Valuation.mem_ltAddSubgroup_iff, Units.val_mk0, ← not_le]
  intro hba
  rw [intValuation_le_intValuation_iff_dvd] at hba
  exact hn (Ideal.mem_of_dvd _ hba ha)

/-- The point of the `𝔪`-adic valuation lies in `Spa (R, A⁺)` for every plus ring `A⁺`. -/
theorem ofValuation_intValuation_mem_spa (hR : IsAdic (maximalIdeal R)) (Aplus : Subring R) :
    ofValuation (_root_.IsDiscreteValuationRing.maximalIdeal R).intValuation ∈ spa Aplus :=
  (mem_spa_iff _ _).mpr ⟨isContinuous_ofValuation_intValuation hR,
    fun a _ ↦ by simpa using HeightOneSpectrum.intValuation_le_one _ a⟩

/-- **A point of `Spa (R, R)` with zero support is the point of the `𝔪`-adic valuation.** It is
at most `1` everywhere, below `1` on the topologically nilpotent maximal ideal, and zero only at
`0`, so it compares elements by divisibility. -/
theorem eq_ofValuation_intValuation_of_supp_eq_bot (hR : IsAdic (maximalIdeal R)) {v : Spv R}
    (hv : v ∈ spa (⊤ : Subring R)) (hsupp : v.supp = ⊥) :
    v = ofValuation (_root_.IsDiscreteValuationRing.maximalIdeal R).intValuation := by
  refine ext' fun x y ↦ ?_
  rw [vle_ofValuation, intValuation_le_intValuation_iff_dvd,
    ← valuation_le_iff]
  refine MonoidWithZeroHom.le_iff_dvd v.valuation.toMonoidWithZeroHom
    (fun a ↦ valuation_le_one_of_mem_spa hv trivial) (fun a ha ↦ ?_) (fun a ha ↦ ?_)
  · exact ((isContinuous_def v).mp ((mem_spa_iff _ v).mp hv).1).lt_one_of_isTopologicallyNilpotent
      (hR.isTopologicallyNilpotent_of_mem ((mem_maximalIdeal a).mpr ha))
  · rw [← Ideal.mem_bot, ← hsupp, supp_eq_valuation_supp]
    exact ha

/-- **The adic spectrum of a discrete valuation ring.** For a discrete valuation ring `R` with
its `𝔪`-adic topology, `Spa (R, R)` consists of exactly two points: the point of the `𝔪`-adic
valuation, with support `⊥`, and the trivial valuation of the maximal ideal. -/
theorem spa_top_eq (hR : IsAdic (maximalIdeal R)) :
    spa (⊤ : Subring R) = {ofValuation (_root_.IsDiscreteValuationRing.maximalIdeal R).intValuation,
      trivialSection (⊤ : PrimeSpectrum R)} := by
  ext v
  refine ⟨fun hv ↦ ?_, ?_⟩
  · by_cases hsupp : v.supp = ⊥
    · exact .inl (eq_ofValuation_intValuation_of_supp_eq_bot hR hv hsupp)
    · refine .inr (eq_trivialSection_of_supp_eq hv _ (maximalIdeal.isMaximal R) ?_)
      exact eq_maximalIdeal (Ideal.IsPrime.isMaximal inferInstance hsupp)
  · rintro (rfl | rfl)
    · exact ofValuation_intValuation_mem_spa hR _
    · exact (trivialSection_mem_spa_iff _ _).mpr (by simpa using hR.isOpen_pow 1)

/-- **The point of the `𝔪`-adic valuation is analytic**: its support `⊥` is not open, since no
power of the nonzero maximal ideal vanishes. -/
theorem isAnalyticPoint_ofValuation_intValuation (hR : IsAdic (maximalIdeal R)) :
    IsAnalyticPoint (ofValuation (_root_.IsDiscreteValuationRing.maximalIdeal R).intValuation) := by
  rw [isAnalyticPoint_def, supp_ofValuation, HeightOneSpectrum.supp_intValuation,
    Submodule.bot_coe]
  intro hopen
  obtain ⟨n, -, hn⟩ := hR.hasBasis_nhds_zero.mem_iff.mp (hopen.mem_nhds rfl)
  exact pow_ne_zero n (_root_.IsDiscreteValuationRing.not_a_field R)
    ((Submodule.eq_bot_iff _).mpr fun x hx ↦ hn hx)

/-- **The analytic locus of `Spa (R, R)`** for a discrete valuation ring with its `𝔪`-adic
topology is the single point of the `𝔪`-adic valuation; the trivial valuation of the maximal ideal
is a non-analytic point. -/
theorem spaAnalytic_top_eq (hR : IsAdic (maximalIdeal R)) :
    spaAnalytic (⊤ : Subring R) =
      {ofValuation (_root_.IsDiscreteValuationRing.maximalIdeal R).intValuation} := by
  ext v
  rw [mem_spaAnalytic_iff, spa_top_eq hR, Set.mem_insert_iff, Set.mem_singleton_iff]
  refine ⟨?_, fun h ↦ ⟨.inl h, h ▸ isAnalyticPoint_ofValuation_intValuation hR⟩⟩
  rintro ⟨rfl | rfl, h⟩
  · rfl
  · -- the support of the trivial valuation is the maximal ideal, which is open
    rw [isAnalyticPoint_def, ← suppFun_asIdeal, suppFun_trivialSection,
      PrimeSpectrum.asIdeal_top] at h
    exact absurd (by simpa using hR.isOpen_pow 1) h

end TauCeti.IsDiscreteValuationRing
