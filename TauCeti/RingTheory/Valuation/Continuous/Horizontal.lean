/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Valuation.CofinalIdeal.Restrict
public import TauCeti.RingTheory.Valuation.Continuous.TopologicallyNilpotent

/-!
# Continuous horizontal restrictions

Restricting a valuation to its characteristic subgroup discards values smaller than every
characteristic value. If its open unit ball is a neighbourhood of zero, the resulting
valuation is continuous. Moreover, horizontal restriction preserves any continuous pullback
from a ring containing a topologically nilpotent unit. Thus an algebraic amalgam of continuous
valuations on Tate rings can be made continuous without changing either factor valuation.

## References

* T. Wedhorn, *Adic Spaces*, arXiv:1910.05934v1, §7.1.2 and Theorem 7.10.
* R. Huber, *A generalization of formal schemes and rigid analytic varieties*, Math. Z. 217
  (1994), proof of Lemma 3.9(i).
-/

public section

open Filter Topology

namespace Valuation

section

variable {R : Type*} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
  {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀]

/-- Restriction to the characteristic subgroup makes a valuation continuous whenever its
open unit ball is a neighbourhood of zero. The unit ideal selects the characteristic subgroup
in the horizontal restriction construction. -/
theorem isContinuous_restrictToIdeal_top (v : Valuation R Γ₀)
    (hU : {a : R | v a < 1} ∈ 𝓝 0) :
    (v.restrictToIdeal ⊤ ⟨⊤, Ideal.fg_top R, rfl⟩).IsContinuous := by
  let w := v.restrictToIdeal ⊤ ⟨⊤, Ideal.fg_top R, rfl⟩
  have hfull : HasFullCharacteristicGroup w := by
    have h := (characteristicSubgroupOfIdeal_eq_top_iff _).mp
      (characteristicSubgroupOfIdeal_restrictToIdeal_eq_top v ⊤ ⟨⊤, Ideal.fg_top R, rfl⟩)
    rcases h with h | h
    · have h1 := cofinalValue_iff.mp (h 1 (by trivial)) 1 zero_lt_one
      simp at h1
    · exact hasFullCharacteristicGroup_iff_characteristicSubgroup_eq_top.mpr h
  apply hfull.isContinuous
  have hball : {a : R | w a < 1} = {a : R | v a < 1} := by
    ext a
    simpa [w] using v.restrictToIdeal_lt_restrictToIdeal_iff ⊤
      ⟨⊤, Ideal.fg_top R, rfl⟩ (a := a) (b := 1) (by simp)
  rwa [hball]

end

variable {R : Type*} [Ring R] [TopologicalSpace R]
  {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀] {S : Type*} [CommRing S]

/-- Horizontal restriction preserves a continuous pullback from a ring with a topologically
nilpotent unit. In particular it preserves continuous valuations on either factor of a tensor
product over a Tate ring, including valuations of higher rank. -/
theorem isEquiv_restrictToIdeal_comap (v : Valuation S Γ₀) (I : Ideal S)
    (hfg : ∃ J : Ideal S, J.FG ∧ I.radical = J.radical) (f : R →+* S)
    (hv : (v.comap f).IsContinuous) {t : R} (ht : IsUnit t)
    (htnil : IsTopologicallyNilpotent t) :
    ((v.restrictToIdeal I hfg).comap f).IsEquiv (v.comap f) := by
  have hkeep {a : R} (ha : v (f a) ≠ 0) : v.restrictToIdeal I hfg (f a) ≠ 0 := by
    obtain ⟨n, hn⟩ := exists_pow_lt_of_isTopologicallyNilpotent
      (((isContinuous_def.mp hv) a).mem_nhds (by simpa using zero_lt_iff.mpr ha)) htnil
    apply v.restrictToIdeal_ne_zero_of_le I hfg
      (((ht.pow n).map f).map (v.restrictToIdeal I hfg).toMonoidWithZeroHom).ne_zero
    simpa using hn.le
  intro a b
  simp only [comap_apply, restrictToIdeal_le_iff]
  constructor
  · rintro (ha | ⟨_, hab⟩)
    · have ha0 : v (f a) = 0 := by
        by_contra h
        exact hkeep h ha
      simp [ha0]
    · exact hab
  · intro hab
    by_cases ha : v (f a) = 0
    · exact Or.inl (v.restrictToIdeal_apply_of_eq_zero I hfg ha)
    · exact Or.inr ⟨hkeep (fun hb ↦ ha (le_antisymm (hb ▸ hab) zero_le)), hab⟩

end Valuation
