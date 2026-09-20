/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.Padics.ProperSpace
public import TauCeti.Topology.Algebra.Group.Profinite.ProP.Basic
public import TauCeti.Topology.Algebra.Group.Profinite.Rank
import Mathlib.NumberTheory.Padics.RingHoms
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated

/-!
# The additive group of the p-adic integers

The additive group of `ℤ_[p]`, written multiplicatively as `Multiplicative ℤ_[p]`, is a
pro-`p` group. Indeed, every open subgroup contains the kernel of a truncation
`ℤ_[p] → ZMod (p ^ n)`, so its quotient is a quotient of a finite `p`-group.

The element `1 : ℤ_[p]` topologically generates this group because the integers are dense in
the `p`-adic integers. Consequently its topological generator rank is one. These facts supply
the `ℤ_p` example used when identifying the free pro-`p` group on one generator.

## Main results

* `TauCeti.isProP_multiplicative_padicInt`: `Multiplicative ℤ_[p]` is pro-`p`.
* `TauCeti.topologicallyGenerates_one_multiplicative_padicInt`: the element `1` topologically
  generates `Multiplicative ℤ_[p]`.
* `TauCeti.topologicalGeneratorRank_multiplicative_padicInt`: its topological generator rank is
  one.

## References

* L. Ribes and P. Zalesskii, *Profinite Groups*, Sections 2.2 and 4.3.
-/

public section

namespace TauCeti

/-- The additive group of the `p`-adic integers, written multiplicatively, is pro-`p`. -/
theorem isProP_multiplicative_padicInt (p : ℕ) [Fact p.Prime] :
    IsProP p (Multiplicative ℤ_[p]) := by
  rw [isProP_iff]
  intro U
  obtain ⟨ε, hε, hεU⟩ := Metric.mem_nhds_iff.mp (U.isOpen.mem_nhds U.one_mem)
  obtain ⟨n, hn⟩ := PadicInt.exists_pow_neg_lt p hε
  let f : Multiplicative ℤ_[p] →* Multiplicative (ZMod (p ^ n)) :=
    (PadicInt.toZModPow n).toAddMonoidHom.toMultiplicative
  have hf : Function.Surjective f :=
    ZMod.ringHom_surjective (PadicInt.toZModPow n)
  have hker : f.ker ≤ U.toSubgroup := by
    intro x hx
    apply hεU
    rw [Metric.mem_ball]
    have hxnorm : ‖x.toAdd‖ < ε := by
      apply lt_of_le_of_lt _ hn
      apply (PadicInt.norm_le_pow_iff_mem_span_pow x.toAdd n).mpr
      rw [← PadicInt.ker_toZModPow]
      have hxzero : PadicInt.toZModPow n x.toAdd = 0 := by
        change (PadicInt.toZModPow n).toAddMonoidHom x.toAdd = 0
        have hx' := congrArg Multiplicative.toAdd (MonoidHom.mem_ker.mp hx)
        simpa only [f, AddMonoidHom.coe_toMultiplicative, Function.comp_apply,
          toAdd_ofAdd, toAdd_one] using hx'
      exact RingHom.mem_ker.mpr hxzero
    simpa [dist_zero_right] using hxnorm
  have htarget : IsPGroup p (Multiplicative (ZMod (p ^ n))) :=
    IsPGroup.of_card (n := n) (by simp)
  have hsource : IsPGroup p (Multiplicative ℤ_[p] ⧸ f.ker) :=
    htarget.of_equiv (QuotientGroup.quotientKerEquivOfSurjective f hf).symm
  let q : Multiplicative ℤ_[p] ⧸ f.ker →*
      Multiplicative ℤ_[p] ⧸ U.toSubgroup :=
    QuotientGroup.map f.ker U.toSubgroup (MonoidHom.id _) hker
  apply hsource.of_surjective q
  exact QuotientGroup.map_surjective_of_surjective f.ker U.toSubgroup (MonoidHom.id _)
    ((QuotientGroup.mk'_surjective U.toSubgroup).comp Function.surjective_id) hker

/-- The element `1 : ℤ_[p]` topologically generates the additive group of the `p`-adic
integers. -/
@[simp]
theorem topologicallyGenerates_one_multiplicative_padicInt (p : ℕ) [Fact p.Prime] :
    (Subgroup.closure ({Multiplicative.ofAdd (1 : ℤ_[p])} : Set _)).topologicalClosure = ⊤ := by
  let f : Multiplicative ℤ →* Multiplicative ℤ_[p] :=
    (Int.castAddHom ℤ_[p]).toMultiplicative
  have hclosure :
      Subgroup.closure ({Multiplicative.ofAdd (1 : ℤ)} : Set (Multiplicative ℤ)) = ⊤ := by
    apply top_unique
    intro x _
    rw [Subgroup.mem_closure_singleton]
    refine ⟨x.toAdd, ?_⟩
    cases x
    rw [← ofAdd_zsmul]
    simp
  have hgen :
      (Subgroup.closure
        ({Multiplicative.ofAdd (1 : ℤ)} : Set (Multiplicative ℤ))).topologicalClosure = ⊤ := by
    rw [hclosure]
    exact top_unique (Subgroup.le_topologicalClosure ⊤)
  have hf : Continuous f := continuous_of_discreteTopology
  have hdense : DenseRange f := PadicInt.denseRange_intCast
  convert topologicalClosure_closure_image_eq_top hgen hf hdense using 1
  simp only [Set.image_singleton, f, AddMonoidHom.coe_toMultiplicative,
    Function.comp_apply, toAdd_ofAdd, Int.coe_castAddHom, Int.cast_one]

/-- The additive group of the `p`-adic integers is topologically finitely generated. -/
theorem isTopologicallyFinitelyGenerated_multiplicative_padicInt (p : ℕ) [Fact p.Prime] :
    IsTopologicallyFinitelyGenerated (Multiplicative ℤ_[p]) :=
  (Set.finite_singleton (Multiplicative.ofAdd (1 : ℤ_[p]))).isTopologicallyFinitelyGenerated
    (topologicallyGenerates_one_multiplicative_padicInt p)

/-- The natural-number topological generator rank of the additive group of `ℤ_[p]` is one. -/
@[simp]
theorem topologicalGeneratorRankNat_multiplicative_padicInt (p : ℕ) [Fact p.Prime] :
    topologicalGeneratorRankNat (Multiplicative ℤ_[p])
      (isTopologicallyFinitelyGenerated_multiplicative_padicInt p) = 1 := by
  let hfg := isTopologicallyFinitelyGenerated_multiplicative_padicInt p
  have hle : topologicalGeneratorRankNat (Multiplicative ℤ_[p]) hfg ≤ 1 := by
    simpa using topologicalGeneratorRankNat_le hfg
      (s := {Multiplicative.ofAdd (1 : ℤ_[p])})
      (by simp)
  have hne : topologicalGeneratorRankNat (Multiplicative ℤ_[p]) hfg ≠ 0 := by
    intro hzero
    have hrank : topologicalGeneratorRank (Multiplicative ℤ_[p]) = 0 := by
      rw [← topologicalGeneratorRankNat_eq_topologicalGeneratorRank hfg, hzero]
      simp
    have hsub := topologicalGeneratorRank_eq_zero_iff.mp hrank
    exact zero_ne_one (congrArg Multiplicative.toAdd
      (hsub.elim (Multiplicative.ofAdd (0 : ℤ_[p])) (Multiplicative.ofAdd 1)))
  omega

/-- The cardinal-valued topological generator rank of the additive group of `ℤ_[p]` is one. -/
@[simp]
theorem topologicalGeneratorRank_multiplicative_padicInt (p : ℕ) [Fact p.Prime] :
    topologicalGeneratorRank (Multiplicative ℤ_[p]) = 1 := by
  rw [← topologicalGeneratorRankNat_eq_topologicalGeneratorRank
    (isTopologicallyFinitelyGenerated_multiplicative_padicInt p),
    topologicalGeneratorRankNat_multiplicative_padicInt]
  simp

end TauCeti
