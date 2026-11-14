/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import TauCeti.Topology.Spectral.Quotient
import Mathlib.Topology.Compactification.OnePoint.Basic
import Mathlib.Topology.Compactification.StoneCech
import Mathlib.Topology.ContinuousMap.Basic
import Mathlib.Topology.InductiveDimension.Classes
import Mathlib.Topology.UnitInterval

/-!
# Worked examples: quotients of spectral and locally spectral spaces

These examples test the quotient criteria in `TauCeti.Topology.Spectral.Quotient` against standard
positive and negative cases.

* The trivial (`⊥`) and total (`⊤`) equivalence relations on any spectral space have
  pro-constructible graphs with open first projections, so
  `TauCeti.IsProConstructible.spectralSpace_quotient_of_isOpenMap` recovers spectrality of both
  extreme quotients (uniformly across empty and nonempty spaces).
* On the spectral space `OnePoint ℕ`, identifying `(0 : ℕ)` with `∞` defines a closed equivalence
  relation with generalizing projections for which the saturation `{(0 : ℕ), ∞}` of the compact open
  singleton `{(0 : ℕ)}` is not open, illustrating why
  `TauCeti.exists_isOpen_quotientMk_preimage_subset_sInter` enlarges the target to a saturated
  intersection `⋂₀ 𝒮` of compact opens rather than the saturation of `W` itself.
* On discrete `ℕ`, the total relation `⊤` has closed graph and open, generalizing, locally spectral
  projections, yet neither the first projection nor `Quotient.mk ⊤` is a spectral (quasi-compact)
  map, showing why local criteria require `IsSpectralMap` rather than `IsLocallySpectralMap` on the
  projections.
* Presenting `unitInterval` as a quotient of the Stone–Čech space `Ultrafilter unitInterval`
  produces a pro-constructible equivalence relation on a spectral space whose projections lift
  generalizations and whose quotient is T₀, yet `Quotient r` is homeomorphic to `[0, 1]` and
  therefore not spectral, showing that the basis hypothesis of `TauCeti.spectralSpace_quotient`
  cannot be omitted.
-/

open Set Filter Topology TopologicalSpace
open scoped OnePoint

namespace TauCeti

/-- On any spectral space `X`, the trivial setoid `⊥` has pro-constructible graph (the diagonal in
the constructible topology) and open first projection, so `Quotient (⊥ : Setoid X)` is spectral. -/
example (X : Type*) [TopologicalSpace X] [SpectralSpace X] :
    SpectralSpace (Quotient (⊥ : Setoid X)) := by
  have hR : IsProConstructible {q : X × X | (⊥ : Setoid X) q.1 q.2} :=
    (isSpectralMap_id.comp isProperMap_fst_of_compactSpace.isSpectralMap).isProConstructible_eq
      (isSpectralMap_id.comp isProperMap_snd_of_compactSpace.isSpectralMap)
  let e : {q : X × X | (⊥ : Setoid X) q.1 q.2} ≃ₜ X :=
    { toFun := fun q ↦ q.1.1
      invFun := fun x ↦ ⟨(x, x), rfl⟩
      left_inv := fun q ↦ by
        have hq : q.1.1 = q.1.2 := q.2
        exact Subtype.ext (Prod.ext rfl hq)
      right_inv := fun _ ↦ rfl
      continuous_toFun := continuous_fst.comp continuous_subtype_val
      continuous_invFun := (continuous_id.prodMk continuous_id).subtype_mk _ }
  exact hR.spectralSpace_quotient_of_isOpenMap e.isOpenMap

/-- On any spectral space `X` (empty or nonempty), the total setoid `⊤` has pro-constructible graph
`univ` and open first projection, so `Quotient (⊤ : Setoid X)` is spectral. -/
example (X : Type*) [TopologicalSpace X] [SpectralSpace X] :
    SpectralSpace (Quotient (⊤ : Setoid X)) := by
  have hR : IsProConstructible {q : X × X | (⊤ : Setoid X) q.1 q.2} := isProConstructible_univ
  have hs_open : IsOpenMap (fun q : {q : X × X | (⊤ : Setoid X) q.1 q.2} ↦ q.1.1) :=
    isOpenMap_fst.comp (Homeomorph.Set.univ (X × X)).isOpenMap
  exact hR.spectralSpace_quotient_of_isOpenMap hs_open

/-- Identifying `(0 : ℕ)` with `∞` in `OnePoint ℕ` gives a pro-constructible equivalence relation
with generalizing projections for which the saturation of the compact open `{(0 : ℕ)}` is not open,
while `TauCeti.exists_isOpen_quotientMk_preimage_subset_sInter` still produces a saturated open
neighbourhood inside a saturated intersection of compact opens. -/
example :
    let collapse : OnePoint ℕ → OnePoint ℕ :=
      fun x ↦ x.elim ((0 : ℕ) : OnePoint ℕ) fun n ↦ (n : OnePoint ℕ)
    let r : Setoid (OnePoint ℕ) := Setoid.ker collapse
    let W : Set (OnePoint ℕ) := {((0 : ℕ) : OnePoint ℕ)}
    ¬ IsOpen (Quotient.mk r ⁻¹' (Quotient.mk r '' W)) ∧
      ∃ (V : Set (Quotient r)) (𝒮 : Set (Set (OnePoint ℕ))),
        IsOpen V ∧ 𝒮.Nonempty ∧ (∀ O ∈ 𝒮, IsOpen O ∧ IsCompact O) ∧
          Quotient.mk r ⁻¹' (Quotient.mk r '' (⋂₀ 𝒮)) = ⋂₀ 𝒮 ∧
          W ⊆ Quotient.mk r ⁻¹' V ∧ Quotient.mk r ⁻¹' V ⊆ ⋂₀ 𝒮 := by
  intro collapse r W
  have hSpec : SpectralSpace (OnePoint ℕ) :=
    { toPrespectralSpace := .of_isTopologicalBasis isTopologicalBasis_isClopen
        fun _ hU ↦ hU.isClosed.isCompact }
  have hWo : IsOpen W := by
    rw [show W = ((↑) : ℕ → OnePoint ℕ) '' {0} by simp [W]]
    exact OnePoint.isOpen_image_coe.mpr (isOpen_discrete _)
  have hsat : Quotient.mk r ⁻¹' (Quotient.mk r '' W) = {((0 : ℕ) : OnePoint ℕ), ∞} := by
    ext x
    induction x using OnePoint.rec with
    | infty =>
      simp only [W, image_singleton, mem_preimage, mem_singleton_iff, mem_insert_iff, or_true,
        iff_true]
      exact Quotient.sound (s := r) (Setoid.ker_def.mpr (by simp [collapse]))
    | coe n =>
      simp only [W, image_singleton, mem_preimage, mem_singleton_iff, mem_insert_iff,
        OnePoint.coe_ne_infty, or_false, OnePoint.coe_eq_coe]
      exact ⟨fun h ↦ by
          simpa [r, collapse, Setoid.ker_def, eq_comm] using Quotient.exact (s := r) h,
        fun h ↦ by subst h; rfl⟩
  refine ⟨fun hopen ↦ ?_, ?_⟩
  · rw [hsat] at hopen
    have hc : IsCompact (((↑) : ℕ → OnePoint ℕ) ⁻¹' ({((0 : ℕ) : OnePoint ℕ), ∞} : Set _))ᶜ :=
      ((OnePoint.isOpen_iff_of_mem' (Or.inr rfl)).mp hopen).1
    have hinf : (((↑) : ℕ → OnePoint ℕ) ⁻¹' ({((0 : ℕ) : OnePoint ℕ), ∞} : Set _))ᶜ.Infinite := by
      refine infinite_of_injective_forall_mem (f := fun n : ℕ ↦ n + 1)
        (fun _ _ h ↦ Nat.succ.inj h) fun n ↦ ?_
      simp
    exact hinf (isCompact_iff_finite.mp hc)
  · have hR_eq : {q : OnePoint ℕ × OnePoint ℕ | r q.1 q.2} =
        diagonal (OnePoint ℕ) ∪
          ({((0 : ℕ) : OnePoint ℕ), ∞} ×ˢ {((0 : ℕ) : OnePoint ℕ), ∞}) := by
      ext ⟨x, y⟩
      induction x using OnePoint.rec <;> induction y using OnePoint.rec <;>
        simp +contextual [r, collapse, Setoid.ker_def, eq_comm]
    have hpair : IsClosed ({((0 : ℕ) : OnePoint ℕ), ∞} : Set (OnePoint ℕ)) :=
      (finite_singleton ∞ |>.insert _).isClosed
    have hR : IsLocallyProConstructible {q : OnePoint ℕ × OnePoint ℕ | r q.1 q.2} := by
      rw [hR_eq]
      exact (isClosed_diagonal.union (hpair.prod hpair)).isLocallyProConstructible
    have hs_qc : IsSpectralMap (fun q : {q : OnePoint ℕ × OnePoint ℕ | r q.1 q.2} ↦ q.1.1) :=
      isProperMap_fst_of_compactSpace.isSpectralMap.comp
        (isLocallyProConstructible_iff_isProConstructible.mp hR).isSpectralMap_subtypeVal
    have hs_gen : GeneralizingMap (fun q : {q : OnePoint ℕ × OnePoint ℕ | r q.1 q.2} ↦ q.1.1) := by
      intro q x' hx'
      obtain rfl := specializes_iff_eq.mp hx'
      exact ⟨q, specializes_rfl, rfl⟩
    exact exists_isOpen_quotientMk_preimage_subset_sInter SpectralSpace.isLocallySpectralSpace
      hR hs_qc hs_gen hWo isCompact_singleton

/-- On discrete `ℕ`, the total relation `⊤` has locally pro-constructible graph and open,
generalizing, locally spectral first projection, yet neither the first projection nor
`Quotient.mk ⊤` is a spectral map. -/
example :
    let r : Setoid ℕ := ⊤
    IsLocallySpectralSpace ℕ ∧
      IsLocallyProConstructible {q : ℕ × ℕ | r q.1 q.2} ∧
      IsOpenMap (fun q : {q : ℕ × ℕ | r q.1 q.2} ↦ q.1.1) ∧
      GeneralizingMap (fun q : {q : ℕ × ℕ | r q.1 q.2} ↦ q.1.1) ∧
      IsLocallySpectralMap (fun q : {q : ℕ × ℕ | r q.1 q.2} ↦ q.1.1) ∧
      ¬ IsSpectralMap (fun q : {q : ℕ × ℕ | r q.1 q.2} ↦ q.1.1) ∧
      ¬ IsSpectralMap (Quotient.mk r) := by
  intro r
  have hN : IsLocallySpectralSpace ℕ :=
    isLocallySpectralSpace_iff.mpr fun n ↦ ⟨{n}, isOpen_discrete _, rfl, {}⟩
  have hNN : IsLocallySpectralSpace (ℕ × ℕ) := hN.prod hN
  have hR : IsLocallyProConstructible {q : ℕ × ℕ | r q.1 q.2} := isLocallyProConstructible_univ
  have hs_open : IsOpenMap (fun q : {q : ℕ × ℕ | r q.1 q.2} ↦ q.1.1) :=
    isOpenMap_fst.comp (Homeomorph.Set.univ (ℕ × ℕ)).isOpenMap
  have hs_gen : GeneralizingMap (fun q : {q : ℕ × ℕ | r q.1 q.2} ↦ q.1.1) := by
    intro q x' hx'
    obtain rfl := specializes_iff_eq.mp hx'
    exact ⟨q, specializes_rfl, rfl⟩
  have hs_ls : IsLocallySpectralMap (fun q : {q : ℕ × ℕ | r q.1 q.2} ↦ q.1.1) :=
    IsLocallySpectralMap.comp hNN (hN.isLocallySpectralMap_fst hN)
      (hR.isLocallySpectralMap_subtypeVal hNN)
  refine ⟨hN, hR, hs_open, hs_gen, hs_ls, fun hs_spec ↦ ?_, fun hπ_spec ↦ ?_⟩
  · have hc := hs_spec.isCompact_preimage_of_isOpen (isOpen_discrete {0}) isCompact_singleton
    rw [isCompact_iff_finite] at hc
    exact infinite_of_injective_forall_mem
      (f := fun n : ℕ ↦ (⟨(0, n), trivial⟩ : {q : ℕ × ℕ | r q.1 q.2}))
      (fun _ _ h ↦ congrArg (fun q ↦ q.1.2) h) (fun _ ↦ rfl) hc
  · have hVo : IsOpen ({Quotient.mk r 0} : Set (Quotient r)) := by
      have hq : IsQuotientMap (Quotient.mk r) := isQuotientMap_quot_mk
      rw [← hq.isOpen_preimage]
      exact isOpen_discrete _
    have hc := hπ_spec.isCompact_preimage_of_isOpen hVo isCompact_singleton
    have hpre : Quotient.mk r ⁻¹' {Quotient.mk r 0} = univ :=
      eq_univ_of_forall fun n ↦ Quotient.sound (s := r) trivial
    rw [hpre, isCompact_iff_finite] at hc
    exact infinite_univ hc

/-- **Scholze, Remark 2.8**: presenting `unitInterval` as a quotient of the spectral Stone–Čech
space `Ultrafilter unitInterval` gives a pro-constructible equivalence relation whose projections
lift generalizations and whose quotient is T₀, yet `Quotient r` is not spectral. -/
example :
    let f : C(Ultrafilter unitInterval, unitInterval) :=
      ⟨Ultrafilter.extend id, continuous_ultrafilter_extend id⟩
    let r : Setoid (Ultrafilter unitInterval) := Setoid.ker f
    ∃ (_ : SpectralSpace (Ultrafilter unitInterval)),
      IsProConstructible {q : Ultrafilter unitInterval × Ultrafilter unitInterval | r q.1 q.2} ∧
        GeneralizingMap
          (fun q : {q : Ultrafilter unitInterval × Ultrafilter unitInterval | r q.1 q.2} ↦ q.1.1) ∧
        T0Space (Quotient r) ∧
        GeneralizingMap (Quotient.mk r) ∧
        ¬ SpectralSpace (Quotient r) := by
  intro f r
  have : SpectralSpace (Ultrafilter unitInterval) :=
    { toPrespectralSpace := .of_isTopologicalBasis ultrafilterBasis_is_basis
        fun _ ⟨s, hs⟩ ↦ hs ▸ (ultrafilter_isClosed_basic s).isCompact }
  have hR :
      IsProConstructible {q : Ultrafilter unitInterval × Ultrafilter unitInterval | r q.1 q.2} :=
    (isClosed_eq (f.continuous.comp continuous_fst)
      (f.continuous.comp continuous_snd)).isProConstructible
  have hs_gen : GeneralizingMap
      (fun q : {q : Ultrafilter unitInterval × Ultrafilter unitInterval | r q.1 q.2} ↦ q.1.1) := by
    intro q x' hx'
    obtain rfl := specializes_iff_eq.mp hx'
    exact ⟨q, specializes_rfl, rfl⟩
  refine ⟨inferInstance, hR, hs_gen, hR.t0Space_quotient hs_gen,
    hR.generalizingMap_quotientMk hs_gen, fun hspec ↦ ?_⟩
  have hf_surj : Function.Surjective f := fun y ↦ ⟨pure y, ultrafilter_extend_pure id y⟩
  have hf_quot : IsQuotientMap f := f.continuous.isClosedMap.isQuotientMap f.continuous hf_surj
  have : SpectralSpace unitInterval := hf_quot.homeomorph.spectralSpace
  exact zero_ne_one ((subsingleton_of_preconnected_totallyDisconnected (α := unitInterval)).elim
    0 1)

end TauCeti
