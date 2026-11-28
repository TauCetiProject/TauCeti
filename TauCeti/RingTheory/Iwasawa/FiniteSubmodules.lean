/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Abelian.Projective.Dimension
public import Mathlib.RingTheory.Depth.Basic
public import TauCeti.RingTheory.Iwasawa.PseudoNull
public import TauCeti.RingTheory.RegularLocalRing.PowerSeries
import TauCeti.RingTheory.Depth.AuslanderBuchsbaum
import TauCeti.RingTheory.Ideal.Height
import TauCeti.RingTheory.RegularLocalRing.CohenMacaulay
import TauCeti.RingTheory.RegularLocalRing.ProjectiveDimension

/-!
# Projective dimension and finite Iwasawa submodules

For a finitely generated module over a two-dimensional regular local ring, projective dimension
at most one is equivalent to the absence of nonzero pseudo-null submodules
(`TauCeti.Iwasawa.hasProjectiveDimensionLE_one_iff_forall_isPseudoNull_eq_bot`). Over a power series
ring over a discrete valuation ring with finite residue field, this is equivalent to the absence
of nonzero finite submodules
(`TauCeti.Iwasawa.hasProjectiveDimensionLE_one_iff_forall_finite_eq_bot`).

The criterion combines the Auslander–Buchsbaum formula
`ModuleCat.projectiveDimension_add_depth_eq_depth` with
`TauCeti.Iwasawa.isPseudoNull_iff_annihilator`.

## References

* J. Neukirch, A. Schmidt and K. Wingberg, *Cohomology of Number Fields*, (5.3.19).
-/

public section

open CategoryTheory IsLocalRing Module
open scoped PowerSeries

namespace TauCeti.Iwasawa

universe u v

variable {R : Type u} {M : Type (max u v)} [CommRing R] [AddCommGroup M]

/-- In dimension two, a module over a Noetherian local ring has positive depth exactly when it
has no nonzero pseudo-null submodule. -/
theorem depth_ne_zero_iff_forall_isPseudoNull_eq_bot [IsLocalRing R] [IsNoetherianRing R]
    [Module R M] (hdim : ringKrullDim R = 2) :
    depth (ModuleCat.of R M) ≠ 0 ↔ ∀ N : Submodule R M, IsPseudoNull R N → N = ⊥ := by
  rw [ne_eq, depth_eq_zero_iff_maximalIdeal_mem_associatedPrimes]
  constructor
  · intro h N hN
    by_contra hbot
    have : Nontrivial N := Submodule.nontrivial_iff_ne_bot.mpr hbot
    have := hN.finite
    obtain ⟨p, hp⟩ := associatedPrimes.nonempty R N
    have hp' := AssociatedPrimes.mem_iff.mp hp
    have := hp'.isPrime
    have hheight := isPseudoNull_iff_annihilator.mp hN ⟨p, hp'.isPrime⟩
      (Submodule.annihilator_top.symm.trans_le hp'.annihilator_le)
    have hmax := (Ideal.lt_height_iff_eq_maximalIdeal (n := 1) hdim).mp hheight
    exact h (hmax ▸ associatedPrimes.subset_of_injective N.injective_subtype hp)
  · intro h hass
    obtain ⟨_, f, hf⟩ :=
      (isAssociatedPrime_iff_exists_injective_linearMap (maximalIdeal R) M).mp hass
    have hres : IsPseudoNull R (R ⧸ maximalIdeal R) :=
      (isPseudoNull_iff_exists_pow_le_annihilator hdim).mpr
        ⟨1, by rw [pow_one, Ideal.annihilator_quotient]⟩
    have hN := hres.of_surjective f.rangeRestrict f.surjective_rangeRestrict
    have : Nontrivial (R ⧸ maximalIdeal R) :=
      Ideal.Quotient.nontrivial_iff.mpr (maximalIdeal.isMaximal R).ne_top
    exact zero_ne_one (hf (by simp only [LinearMap.range_eq_bot.mp (h _ hN), LinearMap.zero_apply]))

/-- A finite module over a two-dimensional regular local ring has projective dimension at most one
if and only if it has no nonzero pseudo-null submodule. -/
theorem hasProjectiveDimensionLE_one_iff_forall_isPseudoNull_eq_bot [IsRegularLocalRing R]
    [Module R M] [Module.Finite R M] (hdim : ringKrullDim R = 2) :
    HasProjectiveDimensionLE (ModuleCat.of R M) 1 ↔
      ∀ N : Submodule R M, IsPseudoNull R N → N = ⊥ := by
  rw [← depth_ne_zero_iff_forall_isPseudoNull_eq_bot hdim, ← projectiveDimension_le_iff]
  cases subsingleton_or_nontrivial M
  · have hpd := (projectiveDimension_eq_bot_iff _).mpr
      (ModuleCat.isZero_of_subsingleton (ModuleCat.of R M))
    rw [hpd, depth_eq_top_of_subsingleton]
    exact iff_of_true bot_le ENat.top_ne_zero
  have hab : projectiveDimension (ModuleCat.of R M) +
      (depth (ModuleCat.of R M) : WithBot ℕ∞) = 2 := by
    have hpd := (ModuleCat.projectiveDimension_le_ringKrullDim (ModuleCat.of R M)).trans_eq hdim
    have htop : (2 : WithBot ℕ∞) < (⊤ : ℕ∞) := WithBot.coe_lt_coe.mpr (ENat.natCast_lt_top 2)
    exact (ModuleCat.projectiveDimension_add_depth_eq_depth _ (hpd.trans_lt htop).ne).trans
      (IsRegularLocalRing.depth_eq_ringKrullDim.trans hdim)
  constructor
  · intro h hz
    rw [hz, WithBot.coe_zero, add_zero] at hab
    exact (by simp [hab] at h)
  · intro h
    have hdepth : 1 ≤ depth (ModuleCat.of R M) := Order.one_le_iff_ne_zero.mpr h
    apply ENat.WithBot.add_le_add_one_right_iff.mp
    calc
      _ ≤ projectiveDimension (ModuleCat.of R M) + (depth (ModuleCat.of R M) : WithBot ℕ∞) :=
        add_le_add_right (WithBot.coe_le_coe.mpr hdepth) _
      _ = 1 + 1 := hab.trans (by norm_num)

/-- For a finite module over `R⟦X⟧`, with `R` a discrete valuation ring of finite residue field,
projective dimension is at most one if and only if every finite submodule is zero
(NSW (5.3.19)). -/
theorem hasProjectiveDimensionLE_one_iff_forall_finite_eq_bot [IsDomain R]
    [IsDiscreteValuationRing R] [Finite (ResidueField R)] [Module R⟦X⟧ M]
    [Module.Finite R⟦X⟧ M] :
    HasProjectiveDimensionLE (ModuleCat.of R⟦X⟧ M) 1 ↔
      ∀ N : Submodule R⟦X⟧ M, Finite N → N = ⊥ := by
  have hdim := PowerSeries.ringKrullDim_of_isDiscreteValuationRing (R := R)
  rw [hasProjectiveDimensionLE_one_iff_forall_isPseudoNull_eq_bot hdim]
  simp only [isPseudoNull_iff_finite hdim]

end TauCeti.Iwasawa
