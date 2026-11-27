/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.SetTheory.Cardinal.Ordinal
public import TauCeti.ModelTheory.BackAndForth.WellOrder
public import TauCeti.ModelTheory.RelationalConfiguration.BorelComplete
public import TauCeti.ModelTheory.RelationalConfiguration.OrderClass
public import TauCeti.ModelTheory.RelationalConfiguration.Separation

/-!
# Borel complete isomorphism relations are not Borel

For a Borel complete class `K` of codes of countable structures, the set of pairs of `K × K` with
isomorphic entries is not measurable for the product of the subtype σ-algebras
(`TauCeti.RelationalConfiguration.not_measurableSet_classIso_of_borelComplete`).

The witnesses are coded linear orders. For every countable ordinal `β`, the well-orders of types
`ω ^ (1 + β)` and `ω ^ (1 + β) · 2`, coded on `ℕ`, are not isomorphic but are back-and-forth
equivalent at depth `1 + β` (`TauCeti.bfEquiv_omega0_opow_mul`), hence at depth `β`. If isomorphism
on `K` were Borel, so would be isomorphism on the coded linear orders, which reduces to it; the
non-isomorphic pairs of coded linear orders would then form a Borel, hence analytic, set, and a
single countable depth `β` would separate all of them
(`TauCeti.RelationalConfiguration.exists_uniform_bfSeparation`), against the witnesses at `β`.

## Main results

* `TauCeti.RelationalConfiguration.exists_mem_linearOrderClass_not_isoSetoid_bfEquivSetoid`: for
  every countable ordinal `β`, two coded linear orders on `ℕ` are not isomorphic but are
  back-and-forth equivalent at depth `β`.
* `TauCeti.RelationalConfiguration.not_measurableSet_classIso_of_borelComplete`: a Borel complete
  class has non-Borel isomorphism relation.
* `TauCeti.RelationalConfiguration.not_borelReducible_classIso_of_borelComplete`: isomorphism on
  a Borel complete class is Borel reducible to no equivalence relation with Borel graph.

## References

* G. Paolini and S. Shelah, *Torsion-free abelian groups are Borel complete*, Fact 1.7.
* S. Gao, *Invariant Descriptive Set Theory*, CRC Press, 2009, §13.1.
-/

public section

open FirstOrder Language MeasureTheory Ordinal Set

namespace TauCeti.RelationalConfiguration

attribute [local instance] Language.orderStructure

/-- **Non-isomorphic coded linear orders at every countable depth.** For every countable ordinal
`β`, the codes on `ℕ` of well-orders of types `ω ^ (1 + β)` and `ω ^ (1 + β) · 2` are coded linear
orders that are not isomorphic but are back-and-forth equivalent at depth `β`. -/
theorem exists_mem_linearOrderClass_not_isoSetoid_bfEquivSetoid {β : Ordinal.{0}} (hβ : β < ω₁) :
    ∃ c ∈ linearOrderClass (V := ℕ), ∃ d ∈ linearOrderClass (V := ℕ),
      ¬ isoSetoid Language.order ℕ c d ∧ bfEquivSetoid Language.order ℕ β c d := by
  have hγ : 1 + β < ω₁ := isPrincipal_add_omega 1 (one_lt_omega0.trans omega0_lt_omega_one) hβ
  have hω : ω ^ (1 + β) < ω₁ := isPrincipal_opow_omega 1 omega0_lt_omega_one hγ
  have hpos : (0 : Ordinal) < 1 + β := zero_lt_one.trans_le le_self_add
  -- the two well-orders are countable and infinite, so they are carried by `ℕ`
  have hcode (δ : Ordinal.{0}) (hδ : 0 < δ) (hδω : δ < ω) :
      Nonempty ((ω ^ (1 + β) * δ).ToType ≃ ℕ) :=
    nonempty_toType_equiv_of_omega0_le_of_lt_omega_one
      ((left_le_opow ω hpos).trans (le_mul_left _ hδ))
      (isPrincipal_mul_omega 1 hω (hδω.trans omega0_lt_omega_one))
  obtain ⟨e₁⟩ := hcode 1 zero_lt_one one_lt_omega0
  obtain ⟨e₂⟩ := hcode 2 zero_lt_two (natCast_lt_omega0 2)
  refine ⟨e₁.encodeVia, ?_, e₂.encodeVia, ?_, ?_, ?_⟩
  · rw [mem_linearOrderClass, ← mem_modelsOfTheory_linearOrderTheory,
      e₁.encodeVia_mem_modelsOfTheory_iff]
    infer_instance
  · rw [mem_linearOrderClass, ← mem_modelsOfTheory_linearOrderTheory,
      e₂.encodeVia_mem_modelsOfTheory_iff]
    infer_instance
  · rw [Equiv.isoSetoid_encodeVia_iff]
    rintro ⟨f⟩
    have := StrongHomClass.toOrderIsoClass Language.order _ _
      ((ω ^ (1 + β) * 1).ToType ≃[Language.order] (ω ^ (1 + β) * 2).ToType)
    have h := (OrderIso.ofClass f).toRelIsoLT.ordinalType_congr
    rw [type_toType, type_toType, mul_one] at h
    have h2 : ω ^ (1 + β) * 1 < ω ^ (1 + β) * 2 :=
      mul_lt_mul_iff_right₀ (opow_pos _ omega0_pos) |>.2 one_lt_two
    rw [mul_one] at h2
    exact h2.ne h
  · rw [Equiv.bfEquivSetoid_encodeVia_iff]
    exact (bfEquiv_omega0_opow_mul (1 + β) one_ne_zero two_ne_zero).mono le_add_self

variable {L : Language.{u, v}} [L.IsRelational]

/-- **Borel complete isomorphism relations are not Borel.** For a Borel complete class `K`, the
set of pairs of `K × K` with isomorphic entries is not measurable for the product of the subtype
σ-algebras. -/
theorem not_measurableSet_classIso_of_borelComplete {K : Set (RelationalConfiguration L ℕ)}
    (hK : BorelComplete K) : ¬ MeasurableSet {p : K × K | classIso K p.1 p.2} := by
  intro hm
  -- isomorphism on the coded linear orders would be Borel
  have hT := (hK.borelReducible measurableSet_linearOrderClass
    isomorphismInvariant_linearOrderClass).measurableSet_setOf hm
  have hemb : MeasurableEmbedding (Prod.map (Subtype.val : linearOrderClass (V := ℕ) → _)
      (Subtype.val : linearOrderClass (V := ℕ) → _)) :=
    (MeasurableEmbedding.subtypeVal measurableSet_linearOrderClass).prodMap
      (MeasurableEmbedding.subtypeVal measurableSet_linearOrderClass)
  -- so the non-isomorphic pairs of coded linear orders would form an analytic set
  have hS := (hemb.measurableSet_image.2 hT.compl).analyticSet
  obtain ⟨β, hβ, hsep⟩ := exists_uniform_bfSeparation.{0, 0, 0, 0} hS (by
    rintro _ ⟨p, hp, rfl⟩
    exact hp)
  obtain ⟨c, hc, d, hd, hcd, hb⟩ := exists_mem_linearOrderClass_not_isoSetoid_bfEquivSetoid hβ
  exact hsep (c, d) ⟨(⟨c, hc⟩, ⟨d, hd⟩), hcd, rfl⟩ hb

/-- Isomorphism on a Borel complete class is Borel reducible to no equivalence relation with
Borel graph: Borelness pulls back along reductions. -/
theorem not_borelReducible_classIso_of_borelComplete {K : Set (RelationalConfiguration L ℕ)}
    (hK : BorelComplete K) {Y : Type*} [MeasurableSpace Y] {F : Setoid Y}
    (hF : MeasurableSet {p : Y × Y | F p.1 p.2}) : ¬ (classIso K).BorelReducible F :=
  fun h ↦ not_measurableSet_classIso_of_borelComplete hK (h.measurableSet_setOf hF)

end TauCeti.RelationalConfiguration
