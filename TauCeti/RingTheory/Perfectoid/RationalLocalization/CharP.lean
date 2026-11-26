/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Huber.LocalizationTopology.Plus
public import TauCeti.RingTheory.Huber.StableUniform
public import TauCeti.RingTheory.Perfectoid.PerfectRing

import TauCeti.Algebra.CharP.Lemmas
import TauCeti.RingTheory.Huber.LocalizationTopology.Restriction
import TauCeti.RingTheory.Huber.Perfect

/-!
# Rational localizations of perfect Tate rings

The completed rational localization of a perfect complete Hausdorff Tate ring of
characteristic `p` is perfect. The inverse of Frobenius on the base extends to the
localization because the `p`-th root of a power-bounded fraction is power-bounded.
This proves that the localized ring is perfectoid and that its plus ring is perfect.
It also gives stable uniformity of the original ring.

## References

* K. S. Kedlaya, R. Liu, *Relative p-adic Hodge theory: foundations*, Proposition 3.1.7.
* K. S. Kedlaya, *Nonarchimedean geometry of Witt vectors and the tilting equivalence*,
  Theorem 2.5.3, the characteristic-`p` case.
-/

public section

open UniformSpace TauCeti.Perfectoid

namespace TauCeti.Huber

variable {A : Type*} [CommRing A] [UniformSpace A] [IsUniformAddGroup A]
  [IsTopologicalRing A] [IsTateRing A] [CompleteSpace A] [T2Space A]
  {p : ℕ} [Fact p.Prime] [PerfectRing A p]

namespace PairOfDefinition

variable (P : PairOfDefinition A) (T : Finset A) (s : A) (S : Type*) [CommRing S]
  [Algebra A S] [IsLocalization.Away s S] (hden : HasDenominatorPower P T s S)

private theorem exists_continuous_root_completion_locTopology [CharP A p] :
    letI := P.locUniformSpace T s S hden
    letI := P.isUniformAddGroup_locUniformSpace T s S hden
    letI := P.isTopologicalRing_locUniformSpace T s S hden
    ∃ g : Completion S →+* Completion S, Continuous g ∧
      g.comp (P.toCompletionLoc T s S hden) =
        (P.toCompletionLoc T s S hden).comp ((frobeniusEquiv A p).symm : A →+* A) := by
  let _ := P.locUniformSpace T s S hden
  have _ := P.isUniformAddGroup_locUniformSpace T s S hden
  have _ := P.isTopologicalRing_locUniformSpace T s S hden
  have _ := P.isHuberRing_completion_locTopology T s S hden
  let ρ := P.toCompletionLoc T s S hden
  let φ := ρ.comp ((frobeniusEquiv A p).symm : A →+* A)
  have hroot : Continuous (frobeniusEquiv A p).symm :=
    (frobeniusEquiv A p).toEquiv.continuous_symm_iff.mpr (isOpenMap_frobenius p)
  have hcont : Continuous φ := (P.continuous_toCompletionLoc T s S hden).comp hroot
  have hpow (a : A) : φ a ^ p = ρ a := by
    exact (map_pow ρ ((frobeniusEquiv A p).symm a) p).symm.trans
      (congrArg ρ (frobeniusEquiv_symm_pow_p A p a))
  have hdenUnit : IsUnit (ρ s) := P.isUnit_toCompletionLoc_of_dvd T s S hden dvd_rfl
  have hp : p.Prime := Fact.out
  have hs : IsUnit (φ s) := (isUnit_pow_iff hp.ne_zero).mp (hpow s ▸ hdenUnit)
  have hunit : hs.unit ^ p = hdenUnit.unit := by
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, hs.unit_spec, hpow, hdenUnit.unit_spec]
  refine (P.existsUnique_continuous_ringHom_completion_locTopology T s S hden hcont.continuousAt
    hs fun t ht ↦ ?_).exists
  apply IsPowerBounded.of_pow hp.ne_zero
  rw [mul_pow, hpow, ← Units.val_pow_eq_pow_val, inv_pow, hunit,
    P.toCompletionLoc_mul_unit_inv_eq_divBy T s S hden t hdenUnit]
  have _ := P.isHuberRing_locUniformSpace T s S hden
  exact isPowerBounded_completion_coe_of_isPowerBounded
    (P.isPowerBounded_divBy_locUniformSpace T s S hden ht)

/-- A completed rational localization of a perfect complete Hausdorff Tate ring in which
`p = 0` is perfect, including when the localization is the zero ring. -/
theorem perfectRing_completion_locTopology (hp0 : (p : A) = 0) :
    letI := P.locUniformSpace T s S hden
    letI := P.isUniformAddGroup_locUniformSpace T s S hden
    letI := P.isTopologicalRing_locUniformSpace T s S hden
    PerfectRing (Completion S) p := by
  let _ := P.locUniformSpace T s S hden
  have _ := P.isUniformAddGroup_locUniformSpace T s S hden
  have _ := P.isTopologicalRing_locUniformSpace T s S hden
  let ρ := P.toCompletionLoc T s S hden
  rcases subsingleton_or_nontrivial (Completion S) with _ | _
  · exact ⟨Function.bijective_of_subsingleton _⟩
  have := ρ.domain_nontrivial
  have : CharP A p := (CharP.charP_iff_prime_eq_zero Fact.out).mpr hp0
  have : CharP (Completion S) p := charP_of_ringHom_of_prime ρ p
  obtain ⟨g, hg, hgρ⟩ := P.exists_continuous_root_completion_locTopology T s S hden (p := p)
  let F := frobenius (Completion S) p
  have hF : Continuous F := continuous_pow p
  have hbase : F.comp ρ = ρ.comp (frobenius A p) :=
    RingHom.ext fun a ↦ (ρ.map_frobenius p a).symm
  have hgρ : g.comp ρ = ρ.comp ((frobeniusEquiv A p).symm : A →+* A) := hgρ
  have hleft : g.comp F = RingHom.id _ :=
    P.eq_id_of_comp_toCompletionLoc_eq_self T s S hden _ (hg.comp hF) (by
      calc
        (g.comp F).comp ρ = (g.comp ρ).comp (frobenius A p) := by
          rw [RingHom.comp_assoc, hbase, RingHom.comp_assoc]
        _ = ρ := by simp [hgρ, RingHom.comp_assoc])
  have hright : F.comp g = RingHom.id _ :=
    P.eq_id_of_comp_toCompletionLoc_eq_self T s S hden _ (hF.comp hg) (by
      calc
        (F.comp g).comp ρ = (F.comp ρ).comp ((frobeniusEquiv A p).symm : A →+* A) := by
          rw [RingHom.comp_assoc, hgρ, RingHom.comp_assoc]
        _ = ρ := by simp [hbase, RingHom.comp_assoc])
  exact ⟨⟨Function.LeftInverse.injective (DFunLike.congr_fun hleft),
    Function.RightInverse.surjective (DFunLike.congr_fun hright)⟩⟩

/-- Every completed rational localization of a perfect complete Hausdorff Tate ring in which
`p = 0` is a perfectoid Tate ring. -/
theorem isPerfectoidTateRing_completion_locTopology (hp0 : (p : A) = 0) :
    letI := P.locUniformSpace T s S hden
    letI := P.isUniformAddGroup_locUniformSpace T s S hden
    letI := P.isTopologicalRing_locUniformSpace T s S hden
    letI := P.isTateRing_completion_locTopology_of_isTateRing T s S hden
    IsPerfectoidTateRing p (Completion S) := by
  let _ := P.locUniformSpace T s S hden
  have _ := P.isUniformAddGroup_locUniformSpace T s S hden
  have _ := P.isTopologicalRing_locUniformSpace T s S hden
  have := P.isTateRing_completion_locTopology_of_isTateRing T s S hden
  rcases subsingleton_or_nontrivial (Completion S) with _ | _
  · exact Perfectoid.isPerfectoidTateRing_of_subsingleton p _
  let ρ := P.toCompletionLoc T s S hden
  have := ρ.domain_nontrivial
  have : CharP A p := (CharP.charP_iff_prime_eq_zero Fact.out).mpr hp0
  have := P.perfectRing_completion_locTopology T s S hden hp0
  have : CharP (Completion S) p := charP_of_ringHom_of_prime ρ p
  exact Perfectoid.IsPerfectoidTateRing.of_perfectRing

/-- The plus ring of a completed rational localization is perfect if the base Tate ring is
perfect, `p = 0` in it, and `Aplus` contains the image of the ideal of definition of `P`. -/
theorem perfectRing_completedPlusSubring (hp0 : (p : A) = 0) {Aplus : Subring A}
    (hIplus : ∀ j : P.ringOfDefinition, j ∈ P.idealOfDefinition → (j : A) ∈ Aplus) :
    letI := P.locUniformSpace T s S hden
    letI := P.isUniformAddGroup_locUniformSpace T s S hden
    letI := P.isTopologicalRing_locUniformSpace T s S hden
    PerfectRing (P.completedPlusSubring Aplus T s S hden) p := by
  let _ := P.locUniformSpace T s S hden
  have _ := P.isUniformAddGroup_locUniformSpace T s S hden
  have _ := P.isTopologicalRing_locUniformSpace T s S hden
  have := P.perfectRing_completion_locTopology T s S hden hp0
  have := P.isIntegrallyClosedIn_completedPlusSubring Aplus hIplus T s S hden
  exact Subring.perfectRing_of_isIntegrallyClosedIn _ p

end PairOfDefinition

/-- A perfect complete Hausdorff Tate ring in which `p = 0` is stably uniform. -/
theorem isStablyUniform_of_perfectRing (hp0 : (p : A) = 0) : IsStablyUniform A where
  isUniform_rationalLocalization P T s hT := by
    let hden := P.hasDenominatorPower_of_isOpen_span T s (Localization.Away s) hT
    let _ := P.locUniformSpace T s (Localization.Away s) hden
    have _ := P.isUniformAddGroup_locUniformSpace T s (Localization.Away s) hden
    have _ := P.isTopologicalRing_locUniformSpace T s (Localization.Away s) hden
    have := P.isTateRing_completion_locTopology_of_isTateRing T s (Localization.Away s) hden
    have := P.isPerfectoidTateRing_completion_locTopology T s (Localization.Away s) hden hp0
    exact Perfectoid.IsPerfectoidTateRing.isUniform p

end TauCeti.Huber
