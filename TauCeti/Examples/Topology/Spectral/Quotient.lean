/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import TauCeti.Topology.Spectral.Quotient
import TauCeti.Topology.Spectral.Limits.Basic
import Mathlib.Topology.Algebra.ConstMulAction
import Mathlib.Topology.Compactification.OnePoint.Basic
import Mathlib.Topology.Homeomorph.Quotient
import Mathlib.Topology.InductiveDimension.Classes

/-!
# Worked examples: quotients by pro-constructible equivalence relations

These examples exercise the quotient theorems in `TauCeti.Topology.Spectral.Quotient` and verify
that their hypotheses are sharp.

* On any spectral space `X` (including the empty space), the diagonal relation `⊥ : Setoid X` and
  the total relation `⊤ : Setoid X` are pro-constructible with open projections, so their quotients
  are spectral and their quotient maps are open, spectral, and generalizing.
* For a continuous action of a finite group `G` on a spectral space `X`, the orbit relation
  `MulAction.orbitRel G X` is a finite union of equalizers of spectral maps with open projections,
  so `Quotient (MulAction.orbitRel G X)` is a spectral space.
* In `TauCeti.exists_isOpen_and_sInter_isCompact_of_isCompact`, the `r`-saturation of a
  quasi-compact open subset `W` need not be open itself: identifying `0` with `∞` in the profinite
  space `OnePoint ℕ` gives a closed equivalence relation with generalizing quasi-compact
  projections for which the saturation of `{0}` is `{0, ∞}`, which is not open.
* On a noncompact locally spectral space, open and locally spectral projections do not force the
  quotient map to be quasi-compact (`IsSpectralMap`): for discrete `ℕ` modulo `⊤`, `Quotient.mk`
  is open and locally spectral, yet the preimage of `univ` is infinite.
-/

open Set Topology OnePoint

namespace TauCeti

/-- On any spectral space `X`, the diagonal relation `⊥ : Setoid X` is pro-constructible with open
projections, so `Quotient (⊥ : Setoid X)` is spectral. -/
example {X : Type*} [TopologicalSpace X] [SpectralSpace X] :
    SpectralSpace (Quotient (⊥ : Setoid X)) := by
  have hR : IsProConstructible {q : X × X | (⊥ : Setoid X) q.1 q.2} :=
    isProperMap_fst_of_compactSpace.isSpectralMap.isProConstructible_eq
      isProperMap_snd_of_compactSpace.isSpectralMap
  have hq : IsOpenMap (Quotient.mk (⊥ : Setoid X)) :=
    (Homeomorph.quotientBot (X := X)).symm.isOpenMap
  exact spectralSpace_quotient_of_isOpenMap hR (isOpenMap_quotient_mk_iff.mp hq)

/-- On any spectral space `X` (empty or nonempty), the total relation `⊤ : Setoid X` is
pro-constructible with open projections, so `Quotient (⊤ : Setoid X)` is spectral and
`Quotient.mk (⊤ : Setoid X)` is spectral and generalizing. -/
example {X : Type*} [TopologicalSpace X] [SpectralSpace X] :
    SpectralSpace (Quotient (⊤ : Setoid X)) ∧
      IsSpectralMap (Quotient.mk (⊤ : Setoid X)) ∧
      GeneralizingMap (Quotient.mk (⊤ : Setoid X)) := by
  have hR : IsProConstructible {q : X × X | (⊤ : Setoid X) q.1 q.2} := by
    change IsProConstructible univ
    exact isProConstructible_univ
  have hs_open : IsOpenMap (fun q : {q : X × X // (⊤ : Setoid X) q.1 q.2} ↦ q.1.1) :=
    isOpenMap_fst.comp (Homeomorph.Set.univ (X × X)).isOpenMap
  have : SpectralSpace {q : X × X // (⊤ : Setoid X) q.1 q.2} := hR.spectralSpace
  have hs_qc : IsSpectralMap (fun q : {q : X × X // (⊤ : Setoid X) q.1 q.2} ↦ q.1.1) :=
    isProperMap_fst_of_compactSpace.isSpectralMap.comp hR.isSpectralMap_subtypeVal
  exact ⟨spectralSpace_quotient_of_isOpenMap hR hs_open,
    isSpectralMap_quotient_mk_of_isOpenMap hs_qc hs_open,
    generalizingMap_quotient_mk SpectralSpace.isLocallySpectralSpace hR.isLocallyProConstructible
      (hs_qc.generalizingMap_of_isOpenMap hs_open)⟩

/-- The quotient of a spectral space by a continuous action of a finite group is spectral. -/
example {G X : Type*} [Group G] [Finite G] [TopologicalSpace X] [SpectralSpace X]
    [MulAction G X] [ContinuousConstSMul G X] :
    SpectralSpace (Quotient (MulAction.orbitRel G X)) := by
  have hR_eq : {q : X × X | (MulAction.orbitRel G X) q.1 q.2} =
      ⋃ g : G, {q : X × X | g • q.2 = q.1} := by
    ext ⟨x, y⟩
    simp [MulAction.orbitRel_apply, MulAction.mem_orbit_iff]
  have hR : IsProConstructible {q : X × X | (MulAction.orbitRel G X) q.1 q.2} := by
    rw [hR_eq]
    refine IsProConstructible.iUnion fun g ↦ ?_
    exact ((Homeomorph.smul g).isProperMap.isSpectralMap.comp
      isProperMap_snd_of_compactSpace.isSpectralMap).isProConstructible_eq
      isProperMap_fst_of_compactSpace.isSpectralMap
  have hs_open :
      IsOpenMap (fun q : {q : X × X // (MulAction.orbitRel G X) q.1 q.2} ↦ q.1.1) :=
    isOpenMap_quotient_mk_iff.mp MulAction.isOpenQuotientMap_quotientMk.isOpenMap
  exact spectralSpace_quotient_of_isOpenMap hR hs_open

/-- Identifying `0` with `∞` in `OnePoint ℕ` gives a closed (hence pro-constructible) equivalence
relation with generalizing quasi-compact projections such that `{0}` is compact open, its
saturation `{0, ∞}` is not open, yet `exists_isOpen_and_sInter_isCompact_of_isCompact` produces an
open saturated neighbourhood bounded by a saturated intersection of compact opens. -/
example :
    let π : OnePoint ℕ → OnePoint ℕ := fun x ↦ x.elim ∞ fun n ↦ if n = 0 then ∞ else n
    let r : Setoid (OnePoint ℕ) := Setoid.ker π
    let W : Set (OnePoint ℕ) := {((0 : ℕ) : OnePoint ℕ)}
    ¬ IsOpen (Quotient.mk r ⁻¹' (Quotient.mk r '' W)) ∧
      ∃ (U : Set (OnePoint ℕ)) (ℬ : Set (Set (OnePoint ℕ))),
        IsOpen U ∧ Quotient.mk r ⁻¹' (Quotient.mk r '' U) = U ∧
        ℬ.Nonempty ∧ (∀ O ∈ ℬ, IsOpen O ∧ IsCompact O) ∧
        Quotient.mk r ⁻¹' (Quotient.mk r '' ⋂₀ ℬ) = ⋂₀ ℬ ∧
        W ⊆ U ∧ U ⊆ ⋂₀ ℬ := by
  intro π r W
  have : SpectralSpace (OnePoint ℕ) :=
    { toPrespectralSpace := .of_isTopologicalBasis isTopologicalBasis_isClopen
        fun _ hU ↦ hU.isClosed.isCompact }
  have hR_eq : {q : OnePoint ℕ × OnePoint ℕ | r q.1 q.2} =
      diagonal (OnePoint ℕ) ∪ {(((0 : ℕ) : OnePoint ℕ), (∞ : OnePoint ℕ))} ∪
        {((∞ : OnePoint ℕ), ((0 : ℕ) : OnePoint ℕ))} := by
    ext ⟨x, y⟩
    induction x using OnePoint.rec <;> induction y using OnePoint.rec <;>
      simp [r, π, Setoid.ker_def]
    split_ifs <;> simp_all
    omega
  have hR_cl : IsClosed {q : OnePoint ℕ × OnePoint ℕ | r q.1 q.2} := by
    rw [hR_eq]
    exact (isClosed_diagonal.union isClosed_singleton).union isClosed_singleton
  have hR : IsProConstructible {q : OnePoint ℕ × OnePoint ℕ | r q.1 q.2} :=
    hR_cl.isProConstructible
  have : SpectralSpace {q : OnePoint ℕ × OnePoint ℕ // r q.1 q.2} := hR.spectralSpace
  have hs_qc : IsSpectralMap (fun q : {q : OnePoint ℕ × OnePoint ℕ // r q.1 q.2} ↦ q.1.1) :=
    isProperMap_fst_of_compactSpace.isSpectralMap.comp hR.isSpectralMap_subtypeVal
  have hs_gen : GeneralizingMap (fun q : {q : OnePoint ℕ × OnePoint ℕ // r q.1 q.2} ↦ q.1.1) := by
    intro q y hy
    rw [specializes_iff_eq] at hy
    exact ⟨q, specializes_rfl, hy.symm⟩
  have hWo : IsOpen W := by
    change IsOpen {((0 : ℕ) : OnePoint ℕ)}
    rw [← image_singleton]
    exact OnePoint.isOpen_image_coe.mpr (isOpen_discrete _)
  refine ⟨fun hsat_open ↦ ?_,
    exists_isOpen_and_sInter_isCompact_of_isCompact SpectralSpace.isLocallySpectralSpace
      hR.isLocallyProConstructible hs_qc hs_gen hWo isCompact_singleton⟩
  have hinf_mem : ∞ ∈ Quotient.mk r ⁻¹' (Quotient.mk r '' W) :=
    ⟨(0 : ℕ), rfl, Quotient.sound (rfl : π (0 : ℕ) = π ∞)⟩
  have hc := ((OnePoint.isOpen_iff_of_mem' hinf_mem).mp hsat_open).1
  rw [isCompact_iff_finite] at hc
  refine infinite_of_injective_forall_mem (f := Nat.succ) Nat.succ_injective (fun n ↦ ?_) hc
  rintro ⟨_, rfl, h⟩
  exact OnePoint.infty_ne_coe n.succ (Quotient.exact h)

/-- On noncompact locally spectral spaces, open and locally spectral projections do not imply
quasi-compactness of the quotient map: on discrete `ℕ` modulo `⊤`, the first projection of the
graph is open and locally spectral, yet `Quotient.mk (⊤ : Setoid ℕ)` is not `IsSpectralMap`. -/
example :
    let r : Setoid ℕ := ⊤
    IsLocallySpectralSpace ℕ ∧
      IsLocallyProConstructible {q : ℕ × ℕ | r q.1 q.2} ∧
      IsLocallySpectralMap (fun q : {q : ℕ × ℕ // r q.1 q.2} ↦ q.1.1) ∧
      IsOpenMap (fun q : {q : ℕ × ℕ // r q.1 q.2} ↦ q.1.1) ∧
      ¬ IsSpectralMap (Quotient.mk r) := by
  intro r
  have hN : IsLocallySpectralSpace ℕ :=
    isLocallySpectralSpace_iff.mpr fun n ↦ ⟨{n}, isOpen_discrete _, rfl, {}⟩
  have hR : IsLocallyProConstructible {q : ℕ × ℕ | r q.1 q.2} :=
    (isClosed_discrete _).isLocallyProConstructible
  have hs_ls : IsLocallySpectralMap (fun q : {q : ℕ × ℕ // r q.1 q.2} ↦ q.1.1) :=
    (isLocallySpectralMap_fst hN).comp (hN.prod hN) hR.isLocallySpectralMap_subtypeVal
  have hs_open : IsOpenMap (fun q : {q : ℕ × ℕ // r q.1 q.2} ↦ q.1.1) :=
    isOpenMap_fst.comp (Homeomorph.Set.univ (ℕ × ℕ)).isOpenMap
  refine ⟨hN, hR, hs_ls, hs_open, fun hq ↦ ?_⟩
  have : Subsingleton (Quotient r) := ⟨by rintro ⟨a⟩ ⟨b⟩; exact Quotient.sound trivial⟩
  have : Finite (Quotient r) := Finite.of_subsingleton
  have : CompactSpace (Quotient r) := Finite.compactSpace
  have hc := hq.isCompact_preimage_of_isOpen isOpen_univ isCompact_univ
  rw [preimage_univ, isCompact_iff_finite] at hc
  exact infinite_univ hc

end TauCeti
