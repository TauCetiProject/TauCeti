/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import TauCeti.Topology.Spectral.Quotient
import TauCeti.Topology.Constructions.Basic
import Mathlib.Topology.Compactification.OnePoint.Basic
import Mathlib.Topology.InductiveDimension.Classes

/-!
# Checks for quotients of spectral and locally spectral spaces

This file exercises the quotient criteria on degenerate relations (diagonal and total relations on
empty and non-T₂ spectral spaces) and records two sharp counterexamples:

* Even for a closed equivalence relation with generalizing projections on a profinite space, the
  saturation `E = t(s⁻¹(W))` of a compact open `W` need not be open, so no invariant open `U` can
  satisfy `W ⊆ U ⊆ E`.
* On discrete `ℕ` with the total relation, the first projection is open, generalizing, and locally
  spectral, yet neither it nor the quotient map is a spectral map (quasicompact).
-/

open Set Topology TopologicalSpace

namespace TauCeti

/-- On the Sierpiński space `Prop`, the diagonal relation has pro-constructible graph and open
first projection, so its quotient is spectral. -/
example : SpectralSpace (Quotient (⊥ : Setoid Prop)) := by
  have := spectralSpace_prop
  have hR : IsProConstructible {q : Prop × Prop | (⊥ : Setoid Prop) q.1 q.2} :=
    isProperMap_fst_of_compactSpace.isSpectralMap.isProConstructible_eq
      isProperMap_snd_of_compactSpace.isSpectralMap
  have hs_open : IsOpenMap fun q : {q : Prop × Prop // (⊥ : Setoid Prop) q.1 q.2} ↦ q.1.1 := by
    let e : Prop ≃ₜ {q : Prop × Prop // (⊥ : Setoid Prop) q.1 q.2} :=
      { toFun := fun p ↦ ⟨(p, p), rfl⟩
        invFun := fun q ↦ q.1.1
        left_inv := fun _ ↦ rfl
        right_inv := fun ⟨⟨_, _⟩, h⟩ ↦ Subtype.ext (Prod.ext rfl h)
        continuous_toFun := (continuous_id.prodMk continuous_id).subtype_mk _
        continuous_invFun := continuous_fst.comp continuous_subtype_val }
    exact e.symm.isOpenMap
  exact spectralSpace_quotient_of_isOpenMap hR hs_open

/-- On the empty spectral space, the total relation yields a spectral quotient via the explicit
basis `{∅}`. -/
example : SpectralSpace (Quotient (⊤ : Setoid Empty)) := by
  have : QuasiSober Empty := ⟨fun h _ ↦ h.nonempty.elim fun e _ ↦ e.elim⟩
  have : SpectralSpace Empty := {}
  have hR : IsProConstructible {q : Empty × Empty | (⊤ : Setoid Empty) q.1 q.2} := by
    convert isProConstructible_univ (X := Empty × Empty) using 1
    ext
    simp
  have hs : GeneralizingMap
      fun q : {q : Empty × Empty // (⊤ : Setoid Empty) q.1 q.2} ↦ q.1.1 :=
    fun q ↦ q.1.1.elim
  have hB : IsTopologicalBasis ({∅} : Set (Set (Quotient (⊤ : Setoid Empty)))) :=
    isTopologicalBasis_of_isOpen_of_nhds (by simp) fun x _ _ _ ↦
      Quotient.inductionOn x fun e ↦ e.elim
  exact spectralSpace_quotient hR hs hB fun V hV ↦ by
    rw [mem_singleton_iff.mp hV]
    exact isCompact_empty

/-- On the nonempty spectral space `Prop`, the total relation yields a spectral quotient with open,
spectral, and generalizing quotient map. -/
example : SpectralSpace (Quotient (⊤ : Setoid Prop)) ∧
    IsOpenMap (Quotient.mk (⊤ : Setoid Prop)) ∧
    IsSpectralMap (Quotient.mk (⊤ : Setoid Prop)) ∧
    GeneralizingMap (Quotient.mk (⊤ : Setoid Prop)) := by
  have := spectralSpace_prop
  have hR : IsProConstructible {q : Prop × Prop | (⊤ : Setoid Prop) q.1 q.2} := by
    convert isProConstructible_univ (X := Prop × Prop) using 1
    ext
    simp
  have hs_open : IsOpenMap fun q : {q : Prop × Prop // (⊤ : Setoid Prop) q.1 q.2} ↦ q.1.1 := by
    let e : {q : Prop × Prop // (⊤ : Setoid Prop) q.1 q.2} ≃ₜ Prop × Prop :=
      { toFun := Subtype.val
        invFun := fun q ↦ ⟨q, trivial⟩
        left_inv := fun ⟨_, _⟩ ↦ rfl
        right_inv := fun _ ↦ rfl }
    exact isOpenMap_fst.comp e.isOpenMap
  have hs_qc : IsSpectralMap fun q : {q : Prop × Prop // (⊤ : Setoid Prop) q.1 q.2} ↦ q.1.1 :=
    isProperMap_fst_of_compactSpace.isSpectralMap.comp hR.isSpectralMap_subtypeVal
  have hs_gen : GeneralizingMap
      fun q : {q : Prop × Prop // (⊤ : Setoid Prop) q.1 q.2} ↦ q.1.1 :=
    hs_qc.isLocallySpectralMap.generalizingMap_of_isOpenMap
      (hR.isLocallyProConstructible.isLocallySpectralSpace
        (SpectralSpace.isLocallySpectralSpace.prod SpectralSpace.isLocallySpectralSpace))
      SpectralSpace.isLocallySpectralSpace hs_open
  exact ⟨spectralSpace_quotient_of_isOpenMap hR hs_open,
    (⊤ : Setoid Prop).isOpenMap_quotient_mk_iff.mpr hs_open,
    (⊤ : Setoid Prop).isSpectralMap_quotient_mk_of_isOpenMap hs_qc hs_open,
    generalizingMap_quotient_mk SpectralSpace.isLocallySpectralSpace hR.isLocallyProConstructible
      hs_qc hs_gen⟩

/-- On the profinite spectral space `OnePoint ℕ`, the closed equivalence relation identifying
`∞` with `0` has generalizing projections, yet the saturation `E = {∞, 0}` of the compact open
`{0}` is not open, so no invariant open `U` satisfies `{0} ⊆ U ⊆ E`. -/
example :
    let z0 : OnePoint ℕ := (0 : ℕ)
    let r : Setoid (OnePoint ℕ) :=
      { r := fun x y ↦
          x = y ∨ (x = OnePoint.infty ∨ x = z0) ∧ (y = OnePoint.infty ∨ y = z0)
        iseqv := ⟨fun _ ↦ Or.inl rfl,
          fun h ↦ h.elim (fun h ↦ Or.inl h.symm) fun ⟨hx, hy⟩ ↦ Or.inr ⟨hy, hx⟩,
          fun h₁ h₂ ↦ h₁.elim (fun h ↦ h ▸ h₂) fun ⟨hx, _⟩ ↦
            h₂.elim (fun h ↦ h ▸ h₁) fun ⟨_, hz⟩ ↦ Or.inr ⟨hx, hz⟩⟩ }
    IsProConstructible {q : OnePoint ℕ × OnePoint ℕ | r q.1 q.2} ∧
    GeneralizingMap (fun q : {q : OnePoint ℕ × OnePoint ℕ // r q.1 q.2} ↦ q.1.1) ∧
    ¬ ∃ U : Set (OnePoint ℕ), IsOpen U ∧ (∀ ⦃x y⦄, r x y → x ∈ U → y ∈ U) ∧
      {z0} ⊆ U ∧ U ⊆ {y | ∃ x ∈ ({z0} : Set (OnePoint ℕ)), r x y} := by
  intro z0 r
  have : SpectralSpace (OnePoint ℕ) :=
    { toPrespectralSpace := .of_isTopologicalBasis isTopologicalBasis_isClopen
        fun _ hU ↦ hU.isClosed.isCompact }
  have hR_closed : IsClosed {q : OnePoint ℕ × OnePoint ℕ | r q.1 q.2} := by
    have heq : {q : OnePoint ℕ × OnePoint ℕ | r q.1 q.2} =
        diagonal (OnePoint ℕ) ∪
          ({OnePoint.infty, z0} : Set (OnePoint ℕ)) ×ˢ {OnePoint.infty, z0} := by
      ext ⟨x, y⟩
      simp only [mem_ofPred_eq, mem_union, mem_diagonal_iff, mem_prod, mem_insert_iff,
        mem_singleton_iff]
      rfl
    rw [heq]
    exact isClosed_diagonal.union
      ((isClosed_singleton.union isClosed_singleton).prod
        (isClosed_singleton.union isClosed_singleton))
  refine ⟨hR_closed.isProConstructible, ?_, ?_⟩
  · intro q y hy
    obtain rfl : y = q.1.1 := specializes_iff_eq.mp hy
    exact ⟨q, specializes_rfl, rfl⟩
  · rintro ⟨U, hUo, hUinv, h0U, hUE⟩
    have hinfU : (OnePoint.infty : OnePoint ℕ) ∈ U :=
      hUinv (Or.inr ⟨Or.inr rfl, Or.inl rfl⟩) (h0U rfl)
    have hfin : (((↑) : ℕ → OnePoint ℕ) ⁻¹' U)ᶜ.Finite :=
      isCompact_iff_finite.mp ((OnePoint.isOpen_iff_of_mem hinfU).mp hUo).2
    have hinf : (((↑) : ℕ → OnePoint ℕ) ⁻¹' U).Infinite := by
      rw [← compl_compl (((↑) : ℕ → OnePoint ℕ) ⁻¹' U)]
      exact hfin.infinite_compl
    obtain ⟨n, hnU, hnpos⟩ := hinf.exists_gt 0
    obtain ⟨x, hx0, hrxn⟩ := hUE hnU
    rw [mem_singleton_iff.mp hx0] at hrxn
    rcases hrxn with h0n | ⟨_, hinfn | h0n⟩
    · exact hnpos.ne (OnePoint.coe_injective h0n)
    · exact OnePoint.coe_ne_infty n hinfn
    · exact hnpos.ne' (OnePoint.coe_injective h0n)

/-- Global quasicompactness of the first projection cannot be dropped: on discrete `ℕ` with the
total relation, the first projection is open and generalizing, yet neither it nor the quotient map
is spectral. -/
example :
    IsOpenMap (fun q : {q : ℕ × ℕ // (⊤ : Setoid ℕ) q.1 q.2} ↦ q.1.1) ∧
    GeneralizingMap (fun q : {q : ℕ × ℕ // (⊤ : Setoid ℕ) q.1 q.2} ↦ q.1.1) ∧
    ¬ IsSpectralMap (fun q : {q : ℕ × ℕ // (⊤ : Setoid ℕ) q.1 q.2} ↦ q.1.1) ∧
    ¬ IsSpectralMap (Quotient.mk (⊤ : Setoid ℕ)) := by
  let e : {q : ℕ × ℕ // (⊤ : Setoid ℕ) q.1 q.2} ≃ₜ ℕ × ℕ :=
    { toFun := Subtype.val
      invFun := fun q ↦ ⟨q, trivial⟩
      left_inv := fun ⟨_, _⟩ ↦ rfl
      right_inv := fun _ ↦ rfl }
  refine ⟨isOpenMap_fst.comp e.isOpenMap, fun q y hy ↦ ?_, fun h ↦ ?_, fun h ↦ ?_⟩
  · obtain rfl : y = q.1.1 := specializes_iff_eq.mp hy
    exact ⟨q, specializes_rfl, rfl⟩
  · have hc := h.isCompact_preimage_of_isOpen (isOpen_discrete {0}) isCompact_singleton
    have hcN : IsCompact (univ : Set ℕ) := by
      convert hc.image (continuous_snd.comp continuous_subtype_val)
      ext n
      exact ⟨fun _ ↦ ⟨⟨(0, n), trivial⟩, rfl, rfl⟩, fun _ ↦ trivial⟩
    exact infinite_univ (isCompact_iff_finite.mp hcN)
  · have : Subsingleton (Quotient (⊤ : Setoid ℕ)) :=
      ⟨fun a b ↦ Quotient.inductionOn₂ a b fun _ _ ↦ Quotient.sound trivial⟩
    have hc := h.isCompact_preimage_of_isOpen isOpen_univ isCompact_univ
    rw [preimage_univ] at hc
    exact infinite_univ (isCompact_iff_finite.mp hc)

end TauCeti
