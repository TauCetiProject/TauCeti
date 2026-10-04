/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Algebra.Group.Profinite.ProP.Basic

import TauCeti.Algebra.Module.ZMod.Dual
import TauCeti.Topology.Algebra.Group.Profinite.Basic

/-!
# Separating closed subgroups by finite characters

A closed subgroup of a profinite abelian pro-`p` group is cut out by its continuous characters
with values in the finite cyclic groups `ZMod (p ^ k)`. Given a point outside the subgroup, first
enlarge the subgroup by an open normal subgroup while still missing the point. The resulting
finite quotient is killed by a power of `p`; the `ZMod` dual separates its nonzero elements.

This is the finite duality input used in the class-module argument for a profinite group of strict
cohomological dimension two.

## Main result

* `TauCeti.exists_continuous_zmodChar_of_notMem`: a continuous finite `p`-power character is
  trivial on a prescribed closed subgroup but nontrivial on a prescribed point outside it.
-/

public section

namespace TauCeti

variable {p : ℕ} [Fact p.Prime]

/-- **Continuous finite `p`-power characters separate points from closed subgroups.** If `I` is a
closed subgroup of a profinite abelian pro-`p` group and `y ∉ I`, there is a continuous
character to some `ZMod (p ^ k)` which is trivial on `I` and nontrivial on `y`. -/
theorem exists_continuous_zmodChar_of_notMem {Y : Type*} [CommGroup Y] [TopologicalSpace Y]
    [IsTopologicalGroup Y] [CompactSpace Y] [TotallyDisconnectedSpace Y]
    (hY : IsProP p Y) (I : Subgroup Y) (hI : IsClosed (I : Set Y)) (y : Y) (hy : y ∉ I) :
    ∃ (k : ℕ) (χ : Y →* Multiplicative (ZMod (p ^ k))), Continuous χ ∧
      (∀ x ∈ I, χ x = 1) ∧ χ y ≠ 1 := by
  classical
  have hyInf : y ∉ ⨅ U : OpenNormalSubgroup Y, I ⊔ U.toSubgroup := by
    rwa [← I.eq_iInf_sup_openNormalSubgroup hI]
  simp only [Subgroup.mem_iInf, not_forall] at hyInf
  obtain ⟨U, hyU⟩ := hyInf
  let W : OpenNormalSubgroup Y :=
    ⟨⟨I ⊔ U.toSubgroup, Subgroup.isOpen_mono le_sup_right U.toOpenSubgroup.isOpen⟩,
      inferInstance⟩
  have : Finite (Y ⧸ W.toSubgroup) :=
    Subgroup.quotient_finite_of_isOpen W.toSubgroup W.toOpenSubgroup.isOpen
  obtain ⟨k, hk⟩ := hY.exists_forall_pow_pow_eq_one W
  have : NeZero (p ^ k) := ⟨pow_ne_zero k (Fact.out : p.Prime).ne_zero⟩
  have hQ : ∀ a : Additive (Y ⧸ W.toSubgroup), p ^ k • a = 0 := by
    intro a
    change Additive.ofMul (a.toMul ^ p ^ k) = Additive.ofMul 1
    rw [hk]
  have hyW : y ∉ W.toSubgroup := hyU
  have hmk : QuotientGroup.mk' W.toSubgroup y ≠ 1 := by
    intro h
    exact hyW ((QuotientGroup.eq_one_iff y).mp h)
  have ha : Additive.ofMul (QuotientGroup.mk' W.toSubgroup y) ≠ 0 := by
    simpa using hmk
  obtain ⟨f, hf⟩ := exists_addMonoidHom_zmod_apply_ne_zero hQ ha
  let χ : Y →* Multiplicative (ZMod (p ^ k)) :=
    (AddMonoidHom.toMultiplicativeRight f).comp (QuotientGroup.mk' W.toSubgroup)
  refine ⟨k, χ, ?_, ?_, ?_⟩
  · let _ : DiscreteTopology (Y ⧸ W.toSubgroup) :=
      QuotientGroup.discreteTopology W.toOpenSubgroup.isOpen
    exact (continuous_of_discreteTopology :
      Continuous (AddMonoidHom.toMultiplicativeRight f)).comp QuotientGroup.continuous_mk
  · intro x hx
    have hxW : x ∈ W.toSubgroup := (show I ≤ W.toSubgroup from le_sup_left) hx
    have hqx : QuotientGroup.mk' W.toSubgroup x = 1 :=
      (QuotientGroup.eq_one_iff x).2 hxW
    change Multiplicative.ofAdd (f (Additive.ofMul (QuotientGroup.mk' W.toSubgroup x))) = 1
    rw [hqx]
    simp
  · simpa [χ] using hf

end TauCeti
