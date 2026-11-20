/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import TauCeti.Topology.Spectral.Limits.Basic
import TauCeti.Topology.Spectral.Quotient
import Mathlib.Topology.Compactification.OnePoint.Basic

/-!
# Checks and sharpness examples for spectral and locally spectral quotients

This file exercises the quotient theorems in `TauCeti.Topology.Spectral.Quotient` on extreme
positive cases and records three counterexamples showing that key hypotheses are sharp:

* the diagonal `⊥ : Setoid X` and the total relation `⊤ : Setoid X` on any spectral space `X`
  (empty or nonempty) satisfy `spectralSpace_quotient_of_isOpenMap`;
* on `OnePoint ℕ` with `0` identified with `∞`, all hypotheses of
  `preimage_image_quotientMk_eq_sInter` hold, yet the saturation `{(0 : ℕ), ∞}` of the
  quasi-compact open `{(0 : ℕ)}` is not itself open;
* on the spectral product `Bool × Prop`, cross-identifying `(false, True) ~ (true, False)` and
  `(false, False) ~ (true, True)` gives a pro-constructible equivalence relation whose first
  projection is not generalizing and whose quotient is indiscrete on two points, hence not T₀;
* on discrete `ℕ`, the total relation `⊤ : Setoid ℕ` has locally pro-constructible graph and open
  projections, so `Quotient (⊤ : Setoid ℕ)` is locally spectral and quasiseparated with locally
  spectral quotient map, while `Quotient.mk (⊤ : Setoid ℕ)` is not globally spectral
  (`IsSpectralMap` fails because `ℕ` is not compact).
-/

open Set Topology
open scoped OnePoint

namespace TauCeti

/-- On any spectral space `X`, the diagonal relation `⊥ : Setoid X` has pro-constructible graph and
open first projection, so `Quotient (⊥ : Setoid X)` is spectral and `Quotient.mk` is spectral. -/
example {X : Type*} [TopologicalSpace X] [SpectralSpace X] :
    SpectralSpace (Quotient (⊥ : Setoid X)) ∧
      IsSpectralMap (Quotient.mk (⊥ : Setoid X)) := by
  have hfst : IsSpectralMap (Prod.fst : X × X → X) := isProperMap_fst_of_compactSpace.isSpectralMap
  have hsnd : IsSpectralMap (Prod.snd : X × X → X) := isProperMap_snd_of_compactSpace.isSpectralMap
  have hR : IsProConstructible {q : X × X | (⊥ : Setoid X) q.1 q.2} :=
    hfst.isProConstructible_eq hsnd
  let e : {q : X × X // (⊥ : Setoid X) q.1 q.2} ≃ₜ X :=
    { toFun := fun q ↦ q.1.1
      invFun := fun x ↦ ⟨(x, x), rfl⟩
      left_inv := fun q ↦ Subtype.ext (Prod.ext rfl q.2)
      right_inv := fun _ ↦ rfl
      continuous_toFun := continuous_fst.comp continuous_subtype_val
      continuous_invFun := (continuous_id.prodMk continuous_id).subtype_mk fun _ ↦ rfl }
  have hs_open : IsOpenMap (fun q : {q : X × X // (⊥ : Setoid X) q.1 q.2} ↦ q.1.1) := e.isOpenMap
  exact ⟨spectralSpace_quotient_of_isOpenMap hR hs_open,
    hR.isSpectralMap_fst.isSpectralMap_quotientMk_of_isOpenMap hs_open⟩

/-- On any spectral space `X` (including `Empty`), the total relation `⊤ : Setoid X` has
pro-constructible graph and open first projection, so `Quotient (⊤ : Setoid X)` is spectral. -/
example {X : Type*} [TopologicalSpace X] [SpectralSpace X] :
    SpectralSpace (Quotient (⊤ : Setoid X)) := by
  have hR : IsProConstructible {q : X × X | (⊤ : Setoid X) q.1 q.2} := by
    have heq : {q : X × X | (⊤ : Setoid X) q.1 q.2} = univ := eq_univ_of_forall fun _ ↦ trivial
    rw [heq]
    exact isProConstructible_univ
  have hs_open : IsOpenMap (fun q : {q : X × X // (⊤ : Setoid X) q.1 q.2} ↦ q.1.1) := by
    intro O hO
    rw [isOpen_induced_iff] at hO
    obtain ⟨U, hUo, rfl⟩ := hO
    have heq : (fun q : {q : X × X // (⊤ : Setoid X) q.1 q.2} ↦ q.1.1) '' (Subtype.val ⁻¹' U) =
        Prod.fst '' U := by
      ext x
      exact ⟨fun ⟨q, hq, hqx⟩ ↦ ⟨q.1, hq, hqx⟩, fun ⟨p, hp, hpx⟩ ↦ ⟨⟨p, trivial⟩, hp, hpx⟩⟩
    rw [heq]
    exact isOpenMap_fst U hUo
  exact spectralSpace_quotient_of_isOpenMap hR hs_open

/-- Identifying `(0 : ℕ)` with `∞` in `OnePoint ℕ` satisfies all hypotheses of
`preimage_image_quotientMk_eq_sInter`, yet the saturation of the compact open `{(0 : ℕ)}` is
`{(0 : ℕ), ∞}`, which is not open. -/
example :
    let r : Setoid (OnePoint ℕ) :=
      Setoid.ker fun x : OnePoint ℕ ↦ x.elim ∞ fun n : ℕ ↦ if n = 0 then ∞ else (n : OnePoint ℕ)
    IsProConstructible {q : OnePoint ℕ × OnePoint ℕ | r q.1 q.2} ∧
      GeneralizingMap (fun q : {q : OnePoint ℕ × OnePoint ℕ // r q.1 q.2} ↦ q.1.1) ∧
      IsSpectralMap (fun q : {q : OnePoint ℕ × OnePoint ℕ // r q.1 q.2} ↦ q.1.1) ∧
      ¬ IsOpen (Quotient.mk r ⁻¹' (Quotient.mk r '' {((0 : ℕ) : OnePoint ℕ)})) := by
  intro r
  have : SpectralSpace (OnePoint ℕ) :=
    { toPrespectralSpace := .of_isTopologicalBasis isTopologicalBasis_isClopen
        fun _ hU ↦ hU.isClosed.isCompact }
  have hR_closed : IsClosed {q : OnePoint ℕ × OnePoint ℕ | r q.1 q.2} := by
    have heq : {q : OnePoint ℕ × OnePoint ℕ | r q.1 q.2} =
        diagonal (OnePoint ℕ) ∪ {(((0 : ℕ) : OnePoint ℕ), (∞ : OnePoint ℕ))} ∪
          {((∞ : OnePoint ℕ), ((0 : ℕ) : OnePoint ℕ))} := by
      ext ⟨x, y⟩
      induction x using OnePoint.rec <;> induction y using OnePoint.rec
      · simp [r, Setoid.ker_def]
      · rename_i m
        cases m <;> simp [r, Setoid.ker_def]
      · rename_i n
        cases n <;> simp [r, Setoid.ker_def]
      · rename_i n m
        cases n <;> cases m <;> simp [r, Setoid.ker_def]
    rw [heq]
    exact (isClosed_diagonal.union isClosed_singleton).union isClosed_singleton
  have hR : IsProConstructible {q : OnePoint ℕ × OnePoint ℕ | r q.1 q.2} :=
    hR_closed.isProConstructible
  have hs_gen : GeneralizingMap (fun q : {q : OnePoint ℕ × OnePoint ℕ // r q.1 q.2} ↦ q.1.1) := by
    intro q b hbq
    have hb : b = q.1.1 := t1Space_iff_specializes_imp_eq.mp inferInstance hbq
    exact ⟨q, specializes_rfl, hb.symm⟩
  refine ⟨hR, hs_gen, hR.isSpectralMap_fst, fun hopen ↦ ?_⟩
  have hsat : Quotient.mk r ⁻¹' (Quotient.mk r '' {((0 : ℕ) : OnePoint ℕ)}) =
      {((0 : ℕ) : OnePoint ℕ), (∞ : OnePoint ℕ)} := by
    ext x
    induction x using OnePoint.rec
    · simp [Quotient.eq, r, Setoid.ker_def]
    · rename_i n
      cases n <;> simp [Quotient.eq, r, Setoid.ker_def]
  rw [hsat] at hopen
  have hcpt : IsCompact ((((↑) : ℕ → OnePoint ℕ) ⁻¹'
      {((0 : ℕ) : OnePoint ℕ), (∞ : OnePoint ℕ)}ᶜ) : Set ℕ) := by
    have hinf : (∞ : OnePoint ℕ) ∈
        ({((0 : ℕ) : OnePoint ℕ), (∞ : OnePoint ℕ)} : Set (OnePoint ℕ)) :=
      mem_insert_of_mem _ rfl
    exact (OnePoint.isOpen_iff_of_mem hinf).mp hopen |>.2
  rw [isCompact_iff_finite] at hcpt
  have hsub : range (Nat.succ : ℕ → ℕ) ⊆
      ((↑) : ℕ → OnePoint ℕ) ⁻¹' {((0 : ℕ) : OnePoint ℕ), (∞ : OnePoint ℕ)}ᶜ := by
    rintro _ ⟨n, rfl⟩
    simp
  exact (infinite_range_of_injective Nat.succ_injective) (hcpt.subset hsub)

/-- On the spectral space `Bool × Prop`, cross-identifying `(false, True) ~ (true, False)` and
`(false, False) ~ (true, True)` gives a pro-constructible equivalence relation whose first
projection is not generalizing and whose quotient fails to be T₀. -/
example :
    let r : Setoid (Bool × Prop) :=
      Setoid.ker fun x : Bool × Prop ↦ if x.1 then ¬ x.2 else x.2
    IsProConstructible {q : (Bool × Prop) × (Bool × Prop) | r q.1 q.2} ∧
      ¬ GeneralizingMap (fun q : {q : (Bool × Prop) × (Bool × Prop) // r q.1 q.2} ↦ q.1.1) ∧
      ¬ T0Space (Quotient r) := by
  have : SpectralSpace Prop := spectralSpace_prop
  have : SpectralSpace Bool := {}
  intro r
  have hTF : True ⤳ False := by
    rw [specializes_iff_nhds, nhds_false]
    exact le_top
  have hR : IsProConstructible {q : (Bool × Prop) × (Bool × Prop) | r q.1 q.2} := by
    have hdiag : IsProConstructible {q : (Bool × Prop) × (Bool × Prop) | q.1 = q.2} :=
      isProperMap_fst_of_compactSpace.isSpectralMap.isProConstructible_eq
        isProperMap_snd_of_compactSpace.isSpectralMap
    have heq : {q : (Bool × Prop) × (Bool × Prop) | r q.1 q.2} =
        {q | q.1 = q.2} ∪ {((false, True), (true, False))} ∪ {((true, False), (false, True))} ∪
          {((false, False), (true, True))} ∪ {((true, True), (false, False))} := by
      ext ⟨⟨b₁, p₁⟩, ⟨b₂, p₂⟩⟩
      cases b₁ <;> cases b₂ <;> by_cases hp₁ : p₁ <;> by_cases hp₂ : p₂
      all_goals simp [r, Setoid.ker_def, eq_true, eq_false, hp₁, hp₂]
    rw [heq]
    exact (((hdiag.union (isProConstructible_singleton _)).union
      (isProConstructible_singleton _)).union (isProConstructible_singleton _)).union
      (isProConstructible_singleton _)
  refine ⟨hR, fun hgen ↦ ?_, fun hT0 ↦ ?_⟩
  · let q₀ : {q : (Bool × Prop) × (Bool × Prop) // r q.1 q.2} :=
      ⟨((false, False), (true, True)), by simp [r, Setoid.ker_def]⟩
    have hspec : (false, True) ⤳ q₀.1.1 := hTF.map (.prodMk_right false)
    obtain ⟨q₁, hq₁q₀, hq₁fst⟩ := hgen (a := q₀) hspec
    have hOo : IsOpen {q : {q : (Bool × Prop) × (Bool × Prop) // r q.1 q.2} |
        q.1.2 = (true, True)} := by
      have hp : IsOpen ({true} ×ˢ ({True} : Set Prop)) :=
        (isOpen_discrete {true}).prod isOpen_singleton_true
      convert hp.preimage (continuous_snd.comp continuous_subtype_val) using 1
      ext q
      simp [Prod.ext_iff]
    have hq₁O : q₁.1.2 = (true, True) :=
      specializes_iff_forall_open.mp hq₁q₀ _ hOo rfl
    have hq₁fst' : q₁.1.1 = (false, True) := hq₁fst
    have hr₁ : r (false, True) (true, True) := by
      have := q₁.2
      rwa [hq₁fst', hq₁O] at this
    simp [r, Setoid.ker_def] at hr₁
  · have h₁ : Quotient.mk r (false, True) ⤳ Quotient.mk r (false, False) :=
      (hTF.map (.prodMk_right false)).map continuous_quot_mk
    have h₂ : Quotient.mk r (true, True) ⤳ Quotient.mk r (true, False) :=
      (hTF.map (.prodMk_right true)).map continuous_quot_mk
    have heq₁ : Quotient.mk r (true, True) = Quotient.mk r (false, False) :=
      Quotient.sound (by simp [r, Setoid.ker_def])
    have heq₂ : Quotient.mk r (true, False) = Quotient.mk r (false, True) :=
      Quotient.sound (by simp [r, Setoid.ker_def])
    rw [heq₁, heq₂] at h₂
    have heq := @Inseparable.eq _ _ hT0 _ _ (h₁.antisymm h₂)
    have hrel : r (false, True) (false, False) := Quotient.exact heq
    simp [r, Setoid.ker_def] at hrel

/-- On discrete `ℕ`, the total relation `⊤ : Setoid ℕ` yields a locally spectral, quasiseparated
quotient and a locally spectral quotient map, yet `Quotient.mk (⊤ : Setoid ℕ)` is not globally
spectral because `ℕ` is not compact. -/
example :
    IsLocallySpectralSpace (Quotient (⊤ : Setoid ℕ)) ∧
      QuasiSeparatedSpace (Quotient (⊤ : Setoid ℕ)) ∧
      IsLocallySpectralMap (Quotient.mk (⊤ : Setoid ℕ)) ∧
      ¬ IsSpectralMap (Quotient.mk (⊤ : Setoid ℕ)) := by
  have hN : IsLocallySpectralSpace ℕ := isLocallySpectralSpace_iff.mpr fun n ↦
    ⟨{n}, isOpen_discrete _, rfl, {}⟩
  have hR : IsLocallyProConstructible {q : ℕ × ℕ | (⊤ : Setoid ℕ) q.1 q.2} := by
    have heq : {q : ℕ × ℕ | (⊤ : Setoid ℕ) q.1 q.2} = univ := eq_univ_of_forall fun _ ↦ trivial
    rw [heq]
    exact isLocallyProConstructible_univ
  have hs_open : IsOpenMap (fun q : {q : ℕ × ℕ // (⊤ : Setoid ℕ) q.1 q.2} ↦ q.1.1) := by
    intro O hO
    rw [isOpen_induced_iff] at hO
    obtain ⟨U, hUo, rfl⟩ := hO
    have heq : (fun q : {q : ℕ × ℕ // (⊤ : Setoid ℕ) q.1 q.2} ↦ q.1.1) '' (Subtype.val ⁻¹' U) =
        Prod.fst '' U := by
      ext n
      exact ⟨fun ⟨q, hq, hqn⟩ ↦ ⟨q.1, hq, hqn⟩, fun ⟨p, hp, hpn⟩ ↦ ⟨⟨p, trivial⟩, hp, hpn⟩⟩
    rw [heq]
    exact isOpenMap_fst U hUo
  refine ⟨isLocallySpectralSpace_quotient_of_isOpenMap hN hR hs_open,
    quasiSeparatedSpace_quotient_of_isOpenMap hN hR hs_open,
    isLocallySpectralMap_quotientMk_of_isOpenMap hN hR hs_open, fun hspec ↦ ?_⟩
  have hsub : Subsingleton (Quotient (⊤ : Setoid ℕ)) :=
    ⟨Quotient.ind₂ fun _ _ ↦ Quotient.sound trivial⟩
  have huniv_c : IsCompact (univ : Set (Quotient (⊤ : Setoid ℕ))) := subsingleton_univ.isCompact
  have hpre : IsCompact (univ : Set ℕ) :=
    hspec.isCompact_preimage_of_isOpen isOpen_univ huniv_c
  rw [isCompact_iff_finite] at hpre
  exact infinite_univ hpre

end TauCeti
