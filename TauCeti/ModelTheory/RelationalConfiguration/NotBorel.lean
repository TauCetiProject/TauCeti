/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.SetTheory.Cardinal.Ordinal
public import TauCeti.ModelTheory.BackAndForth.WellOrder
public import TauCeti.ModelTheory.RelationalConfiguration.BorelComplete
public import TauCeti.ModelTheory.RelationalConfiguration.BorelIsomorphism
public import TauCeti.ModelTheory.RelationalConfiguration.OrderClass
public import TauCeti.ModelTheory.RelationalConfiguration.Separation
public import TauCeti.SetTheory.Descriptive.EZero

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
  a Borel complete class is Borel reducible to no equivalence relation with Borel graph, in
  particular not to `E₀` (`not_borelReducible_eZero_of_borelComplete`).
* `TauCeti.RelationalConfiguration.exists_lt_scottHeight_of_borelComplete`: a Borel complete class
  has codes of unbounded countable Scott height, since a bound `β < ω₁` would make isomorphism on
  the class back-and-forth equivalence at level `β`, hence Borel.
* `TauCeti.RelationalConfiguration.not_analyticSet_setOf_not_isoSetoid_of_borelComplete`: for a
  Borel, Borel complete class `K`, the non-isomorphic pairs of `K` do not form an analytic set:
  their complement is analytic, so by Suslin's theorem both would be Borel.

## References

* G. Paolini and S. Shelah, *Torsion-free abelian groups are Borel complete*, Fact 1.7.
* S. Gao, *Invariant Descriptive Set Theory*, CRC Press, 2009, §13.1.
* A. Montalbán, *Computable Structure Theory: Beyond the Arithmetic*, Theorem XI.3, for the
  unbounded Scott ranks of a Borel complete class.
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
  refine ⟨e₁.encodeVia, e₁.encodeVia_mem_linearOrderClass, e₂.encodeVia,
    e₂.encodeVia_mem_linearOrderClass, ?_, ?_⟩
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

/-- Isomorphism on a Borel complete class is not Borel reducible to `E₀`, whose graph is Borel. -/
theorem not_borelReducible_eZero_of_borelComplete {K : Set (RelationalConfiguration L ℕ)}
    (hK : BorelComplete K) : ¬ (classIso K).BorelReducible eZero :=
  not_borelReducible_classIso_of_borelComplete hK measurableSet_eZero

variable [∀ n, Countable (L.Relations n)]

/-- **Borel complete classes have unbounded Scott height.** In a vocabulary with countably many
relation symbols of each arity, for a Borel complete class `K` and every countable ordinal `β`,
some code in `K` decodes to a structure of Scott height greater than `β`. Otherwise isomorphism
on `K` would be back-and-forth equivalence at level `β`, which is Borel. -/
theorem exists_lt_scottHeight_of_borelComplete {K : Set (RelationalConfiguration L ℕ)}
    (hK : BorelComplete K) {β : Ordinal.{0}} (hβ : β < ω₁) :
    ∃ c ∈ K, β < @scottHeight L _ ℕ c.toStructure := by
  by_contra! h
  exact not_measurableSet_classIso_of_borelComplete hK
    (measurableSet_setOf_comap_isoSetoid_of_scottHeight_le hβ h)

/-- **The non-isomorphic pairs of a Borel, Borel complete class are not analytic.** In a vocabulary
with countably many relation symbols of each arity, for a Borel set `K` of codes with
`BorelComplete K`, the set of pairs of `K × K` (in the ambient square) with non-isomorphic entries
is not analytic. Its complement, the union of the analytic set of isomorphic pairs of `K` and the
Borel complement of `K ×ˢ K`, is analytic, so by Suslin's theorem both would be Borel, and so
would isomorphism on `K`. -/
theorem not_analyticSet_setOf_not_isoSetoid_of_borelComplete
    {K : Set (RelationalConfiguration L ℕ)} (hK : BorelComplete K) (hKm : MeasurableSet K) :
    ¬ AnalyticSet {p : RelationalConfiguration L ℕ × RelationalConfiguration L ℕ |
      p ∈ K ×ˢ K ∧ ¬ isoSetoid L ℕ p.1 p.2} := by
  intro hA
  set S := {p : RelationalConfiguration L ℕ × RelationalConfiguration L ℕ |
    p ∈ K ×ˢ K ∧ ¬ isoSetoid L ℕ p.1 p.2}
  have hKK := hKm.prod hKm
  -- the complement of `S` is analytic
  have hc : AnalyticSet Sᶜ := by
    have hS : Sᶜ = (K ×ˢ K)ᶜ ∪ ({p | isoSetoid L ℕ p.1 p.2} ∩ K ×ˢ K) := by
      ext p
      simp only [S, mem_compl_iff, mem_ofPred_eq, not_and, not_not, mem_union, mem_inter_iff]
      tauto
    rw [hS]
    exact hKK.compl.analyticSet.union (analyticSet_setOf_isoSetoid.inter_measurableSet hKK)
  -- by Suslin's theorem `S` is Borel, and so is isomorphism on `K`
  have hm := hA.measurableSet_of_compl hc
  apply not_measurableSet_classIso_of_borelComplete hK
  have h : {p : K × K | classIso K p.1 p.2} =
      (fun p : K × K ↦ ((p.1 : RelationalConfiguration L ℕ), (p.2 : RelationalConfiguration L ℕ)))
        ⁻¹' Sᶜ := by
    ext p
    simp [S]
  rw [h]
  exact hm.compl.preimage ((measurable_subtypeVal.comp measurable_fst).prodMk
    (measurable_subtypeVal.comp measurable_snd))

end TauCeti.RelationalConfiguration
