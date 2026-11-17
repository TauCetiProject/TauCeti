/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import Mathlib.Topology.Compactification.OnePoint.Basic
import Mathlib.Topology.Compactification.StoneCech
import Mathlib.Topology.InductiveDimension.Classes
import Mathlib.Topology.UnitInterval
import TauCeti.Topology.Spectral.Quotient

/-!
# Worked examples: quotients of spectral and locally spectral spaces

These examples exercise the quotient criteria of `TauCeti.Topology.Spectral.Quotient` on
positive, degenerate, and negative cases:

* The diagonal and total equivalence relations on a spectral space (including the empty space),
  handled by both `TauCeti.spectralSpace_quotient` and
  `TauCeti.spectralSpace_quotient_of_isOpenMap`.
* On `OnePoint ℕ` with `∞` identified with `0`, the saturation of the compact open `{0}` is
  `{∞, 0}`, which is not open; no invariant open subset can lie between `{0}` and its saturation,
  illustrating why `TauCeti.exists_isOpen_invariant_subset_sInter` enlarges to a larger invariant
  intersection of compact opens.
* The quotient of a spectral space by a continuous action of a finite group is spectral via
  `TauCeti.spectralSpace_quotient_of_isOpenMap`.
* The Stone–Čech presentation `Ultrafilter unitInterval → unitInterval` satisfies the
  hypotheses of `TauCeti.t0Space_quotient` and `TauCeti.generalizingMap_quotientMk`, yet its
  quotient `unitInterval` is not spectral, showing that the basis hypothesis in
  `TauCeti.spectralSpace_quotient` cannot be dropped.
* On discrete `ℕ` with the total relation, the graph projection is open, generalizing, and
  locally spectral, but not globally spectral, showing that global quasi-compactness cannot be
  replaced by `TauCeti.IsLocallySpectralMap` in the locally spectral quotient theorems.
-/

open Set Topology TopologicalSpace

namespace TauCeti

/-! ### Degenerate cases: diagonal and total relations -/

/-- For the diagonal relation `⊥` on a spectral space, `spectralSpace_quotient_of_isOpenMap`
applies. -/
example {X : Type*} [TopologicalSpace X] [SpectralSpace X] :
    SpectralSpace (Quotient (⊥ : Setoid X)) ∧
      IsOpenMap (Quotient.mk (⊥ : Setoid X)) ∧
      IsSpectralMap (Quotient.mk (⊥ : Setoid X)) ∧
      GeneralizingMap (Quotient.mk (⊥ : Setoid X)) := by
  have hR : IsProConstructible {q : X × X | (⊥ : Setoid X) q.1 q.2} :=
    isProperMap_fst_of_compactSpace.isSpectralMap.isProConstructible_eq
      isProperMap_snd_of_compactSpace.isSpectralMap
  let he : {q : X × X // (⊥ : Setoid X) q.1 q.2} ≃ₜ X :=
    { toFun := fun q ↦ q.1.1
      invFun := fun x ↦ ⟨(x, x), rfl⟩
      left_inv := fun ⟨⟨x, y⟩, hxy⟩ ↦ Subtype.ext (Prod.ext rfl hxy)
      right_inv := fun _ ↦ rfl
      continuous_toFun := continuous_fst.comp continuous_subtype_val
      continuous_invFun := (continuous_id.prodMk continuous_id).subtype_mk _ }
  have hopen : IsOpenMap (fun q : {q : X × X // (⊥ : Setoid X) q.1 q.2} ↦ q.1.1) :=
    he.isOpenMap
  exact spectralSpace_quotient_of_isOpenMap ⊥ hR hopen

/-- For the total relation `⊤` on a spectral space (whether empty or nonempty),
`spectralSpace_quotient` applies with the basis `{∅, univ}`. -/
example {X : Type*} [TopologicalSpace X] [SpectralSpace X] :
    SpectralSpace (Quotient (⊤ : Setoid X)) ∧
      IsSpectralMap (Quotient.mk (⊤ : Setoid X)) ∧
      GeneralizingMap (Quotient.mk (⊤ : Setoid X)) := by
  have hR : IsProConstructible {q : X × X | (⊤ : Setoid X) q.1 q.2} := isProConstructible_univ
  have hopen : IsOpenMap (fun q : {q : X × X // (⊤ : Setoid X) q.1 q.2} ↦ q.1.1) :=
    isOpenMap_fst.comp ((Homeomorph.Set.univ (X × X)).isOpenMap : IsOpenMap Subtype.val)
  have hgen : GeneralizingMap (fun q : {q : X × X // (⊤ : Setoid X) q.1 q.2} ↦ q.1.1) := by
    have hX : IsLocallySpectralSpace X := SpectralSpace.isLocallySpectralSpace
    have hR_lss : IsLocallySpectralSpace {q : X × X // (⊤ : Setoid X) q.1 q.2} :=
      hR.isLocallyProConstructible.isLocallySpectralSpace (hX.prod hX)
    have hls : IsLocallySpectralMap (fun q : {q : X × X // (⊤ : Setoid X) q.1 q.2} ↦ q.1.1) :=
      isLocallySpectralMap_fst.comp (hX.prod hX)
        (hR.isLocallyProConstructible.isLocallySpectralMap_subtypeVal (hX.prod hX))
    exact hls.generalizingMap_of_isOpenMap hR_lss hX hopen
  have hB : ∃ B : Set (Set (Quotient (⊤ : Setoid X))), IsTopologicalBasis B ∧
      ∀ V ∈ B, IsCompact (Quotient.mk (⊤ : Setoid X) ⁻¹' V) := by
    refine ⟨{∅, univ}, isTopologicalBasis_of_isOpen_of_nhds ?_ fun y O hyO _ ↦ ?_, ?_⟩
    · rintro _ (rfl | rfl)
      · exact isOpen_empty
      · exact isOpen_univ
    · refine ⟨univ, Or.inr rfl, mem_univ y, fun z _ ↦ ?_⟩
      obtain ⟨x₁, rfl⟩ := Quotient.exists_rep y
      obtain ⟨x₂, rfl⟩ := Quotient.exists_rep z
      have : Quotient.mk (⊤ : Setoid X) x₂ = Quotient.mk (⊤ : Setoid X) x₁ :=
        Quotient.sound trivial
      rwa [this]
    · rintro _ (rfl | rfl)
      · exact isCompact_empty
      · exact isCompact_univ
  exact spectralSpace_quotient ⊤ hR hgen hB

/-- The total relation on the empty space yields the empty spectral space. -/
example : SpectralSpace (Quotient (⊤ : Setoid Empty)) := by
  have _ : SpectralSpace Empty := spectralSpace_iff_isLocallySpectralSpace.mpr
    ⟨isLocallySpectralSpace_iff.mpr fun x ↦ x.elim, inferInstance, inferInstance⟩
  have hopen : IsOpenMap (fun q : {q : Empty × Empty // (⊤ : Setoid Empty) q.1 q.2} ↦ q.1.1) :=
    isOpenMap_fst.comp ((Homeomorph.Set.univ (Empty × Empty)).isOpenMap : IsOpenMap Subtype.val)
  exact (spectralSpace_quotient_of_isOpenMap (X := Empty) ⊤ isProConstructible_univ hopen).1

/-! ### Non-example: saturations of compact opens need not be open -/

/-- On `OnePoint ℕ` with the closed relation identifying `∞` and `0` only, the saturation of the
compact open `{0}` is `{∞, 0}`, which is not open; no `r`-invariant open subset can lie between
`{0}` and `{∞, 0}`. Meanwhile, `t0Space_quotient` still applies. -/
example :
    let r : Setoid (OnePoint ℕ) := Setoid.ker fun x : OnePoint ℕ ↦ x.elim 0 id
    (¬ ∃ U : Set (OnePoint ℕ), IsOpen U ∧ (∀ ⦃x y⦄, r x y → x ∈ U → y ∈ U) ∧
      {((0 : ℕ) : OnePoint ℕ)} ⊆ U ∧
        U ⊆ Quotient.mk r ⁻¹' (Quotient.mk r '' {((0 : ℕ) : OnePoint ℕ)})) ∧
    T0Space (Quotient r) := by
  let f : OnePoint ℕ → ℕ := fun x ↦ x.elim 0 id
  let r : Setoid (OnePoint ℕ) := Setoid.ker f
  have _ : SpectralSpace (OnePoint ℕ) :=
    { toPrespectralSpace := .of_isTopologicalBasis isTopologicalBasis_isClopen
        fun _ hU ↦ hU.isClosed.isCompact }
  refine ⟨?_, ?_⟩
  · rintro ⟨U, hUo, hUinv, h0U, hUE⟩
    have hinfU : (OnePoint.infty : OnePoint ℕ) ∈ U :=
      hUinv (rfl : r ((0 : ℕ) : OnePoint ℕ) _) (h0U rfl)
    -- Any open neighbourhood of `∞` in `OnePoint ℕ` has finite complement in `ℕ`.
    have hcompl_fin : (((↑) : ℕ → OnePoint ℕ) ⁻¹' U)ᶜ.Finite := by
      rw [← isCompact_iff_finite]
      exact ((OnePoint.isOpen_iff_of_mem hinfU).mp hUo).2
    obtain ⟨n, hn⟩ := (Set.infinite_univ.sdiff (hcompl_fin.union (finite_singleton 0))).nonempty
    have hnU : (n : OnePoint ℕ) ∈ U := by
      by_contra hnot
      exact hn.2 (Or.inl hnot)
    obtain ⟨z, hz, hzn⟩ := hUE hnU
    rw [mem_singleton_iff] at hz
    subst hz
    exact hn.2 (Or.inr (Quotient.exact hzn).symm)
  · have hRcl : IsClosed {q : OnePoint ℕ × OnePoint ℕ | r q.1 q.2} := by
      have heq : {q : OnePoint ℕ × OnePoint ℕ | r q.1 q.2} =
          diagonal (OnePoint ℕ) ∪
            {((OnePoint.infty : OnePoint ℕ), ((0 : ℕ) : OnePoint ℕ))} ∪
            {(((0 : ℕ) : OnePoint ℕ), (OnePoint.infty : OnePoint ℕ))} := by
        ext ⟨x, y⟩
        induction x using OnePoint.rec <;> induction y using OnePoint.rec <;>
          simp [r, f, eq_comm]
      rw [heq]
      exact (isClosed_diagonal.union isClosed_singleton).union isClosed_singleton
    have hR : IsProConstructible {q : OnePoint ℕ × OnePoint ℕ | r q.1 q.2} :=
      hRcl.isProConstructible
    have hgen :
        GeneralizingMap fun q : {q : OnePoint ℕ × OnePoint ℕ // r q.1 q.2} ↦ q.1.1 := by
      intro q y hy
      rw [specializes_iff_eq] at hy
      exact ⟨q, specializes_rfl, hy.symm⟩
    have hspec : IsSpectralMap fun q : {q : OnePoint ℕ × OnePoint ℕ // r q.1 q.2} ↦ q.1.1 :=
      isProperMap_fst_of_compactSpace.isSpectralMap.comp hR.isSpectralMap_subtypeVal
    exact t0Space_quotient SpectralSpace.isLocallySpectralSpace r
      hR.isLocallyProConstructible hspec hgen

/-! ### Quotients by finite group actions -/

/-- The quotient of a spectral space by a continuous action of a finite group is spectral. -/
example {G X : Type*} [Group G] [Finite G] [TopologicalSpace X] [SpectralSpace X]
    [MulAction G X] [ContinuousConstSMul G X] :
    SpectralSpace (Quotient (MulAction.orbitRel G X)) := by
  let r := MulAction.orbitRel G X
  have hR : IsProConstructible {q : X × X | r q.1 q.2} := by
    have heq : {q : X × X | r q.1 q.2} = ⋃ g : G, {q : X × X | g • q.2 = q.1} := by
      ext ⟨x, y⟩
      simp [r, MulAction.orbitRel_apply, MulAction.mem_orbit_iff]
    rw [heq]
    refine IsProConstructible.iUnion fun g ↦ ?_
    have hsmul : IsSpectralMap (fun x : X ↦ g • x) :=
      (Homeomorph.smul g).isOpenEmbedding.isSpectralMap
    exact (hsmul.comp isProperMap_snd_of_compactSpace.isSpectralMap).isProConstructible_eq
      isProperMap_fst_of_compactSpace.isSpectralMap
  have hopen : IsOpenMap fun q : {q : X × X // r q.1 q.2} ↦ q.1.1 := by
    intro O hOo
    rw [isOpen_iff_mem_nhds]
    rintro _ ⟨q, hqO, rfl⟩
    obtain ⟨g, hg⟩ := q.2
    rw [isOpen_induced_iff] at hOo
    obtain ⟨U, hUo, hUO⟩ := hOo
    have hqU : q.1 ∈ U := by
      rw [← mem_preimage, hUO]
      exact hqO
    obtain ⟨A, B, hAo, hBo, hq1A, hq2B, hABU⟩ := isOpen_prod_iff.mp hUo q.1.1 q.1.2 hqU
    let W : Set X := A ∩ (fun z : X ↦ g⁻¹ • z) ⁻¹' B
    have hWo : IsOpen W := hAo.inter (hBo.preimage (continuous_const_smul g⁻¹))
    have hq1W : q.1.1 ∈ W := ⟨hq1A, by
      dsimp only at hg
      simpa only [mem_preimage, ← hg, inv_smul_smul] using hq2B⟩
    refine Filter.mem_of_superset (hWo.mem_nhds hq1W) fun z ⟨hzA, hzB⟩ ↦ ?_
    have hrel : r z (g⁻¹ • z) := ⟨g, smul_inv_smul g z⟩
    refine ⟨⟨(z, g⁻¹ • z), hrel⟩, ?_, rfl⟩
    rw [← hUO]
    exact hABU ⟨hzA, hzB⟩
  exact (spectralSpace_quotient_of_isOpenMap r hR hopen).1

/-! ### Non-example: Stone–Čech quotient onto `[0, 1]` -/

/-- The Stone–Čech presentation `Ultrafilter unitInterval → unitInterval` satisfies the
hypotheses of `t0Space_quotient` and `generalizingMap_quotientMk`, with profinite (hence
spectral) source and closed (hence pro-constructible) equivalence relation, yet the quotient is
homeomorphic to the connected space `unitInterval` and therefore not spectral. -/
example :
    let f : Ultrafilter unitInterval → unitInterval := Ultrafilter.extend id
    let r : Setoid (Ultrafilter unitInterval) := Setoid.ker f
    SpectralSpace (Ultrafilter unitInterval) ∧
      IsProConstructible {q : Ultrafilter unitInterval × Ultrafilter unitInterval | r q.1 q.2} ∧
      GeneralizingMap
        (fun q : {q : Ultrafilter unitInterval × Ultrafilter unitInterval // r q.1 q.2} ↦
          q.1.1) ∧
      T0Space (Quotient r) ∧
      ¬ SpectralSpace (Quotient r) := by
  let f : Ultrafilter unitInterval → unitInterval := Ultrafilter.extend id
  let r : Setoid (Ultrafilter unitInterval) := Setoid.ker f
  have hf_cont : Continuous f := continuous_ultrafilter_extend id
  have hf_surj : Function.Surjective f := fun y ↦
    ⟨pure y, congrFun (ultrafilter_extend_extends (id : unitInterval → unitInterval)) y⟩
  have hXspec : SpectralSpace (Ultrafilter unitInterval) :=
    { toPrespectralSpace := .of_isTopologicalBasis ultrafilterBasis_is_basis fun _ hU ↦ by
        obtain ⟨s, rfl⟩ := hU
        exact (ultrafilter_isClosed_basic s).isCompact }
  have hR : IsProConstructible
      {q : Ultrafilter unitInterval × Ultrafilter unitInterval | r q.1 q.2} :=
    (isClosed_eq (hf_cont.comp continuous_fst) (hf_cont.comp continuous_snd)).isProConstructible
  have hgen : GeneralizingMap
      (fun q : {q : Ultrafilter unitInterval × Ultrafilter unitInterval // r q.1 q.2} ↦
        q.1.1) := by
    intro q y hy
    rw [specializes_iff_eq] at hy
    exact ⟨q, specializes_rfl, hy.symm⟩
  have hspec : IsSpectralMap
      (fun q : {q : Ultrafilter unitInterval × Ultrafilter unitInterval // r q.1 q.2} ↦ q.1.1) :=
    isProperMap_fst_of_compactSpace.isSpectralMap.comp hR.isSpectralMap_subtypeVal
  have hT0 : T0Space (Quotient r) :=
    t0Space_quotient SpectralSpace.isLocallySpectralSpace r hR.isLocallyProConstructible hspec hgen
  -- The induced bijection `Quotient r → unitInterval` is a continuous bijection from a compact
  -- space to a Hausdorff space, hence a homeomorphism.
  have hnot_spec : ¬ SpectralSpace (Quotient r) := by
    intro hQspec
    let g : Quotient r → unitInterval := Quotient.lift f fun _ _ h ↦ h
    have hg_cont : Continuous g := hf_cont.quotient_lift _
    have hg_bij : Function.Bijective g :=
      ⟨fun a b hab ↦ Quotient.inductionOn₂ a b (fun _ _ h ↦ Quotient.sound h) hab,
        fun y ↦ let ⟨x, hx⟩ := hf_surj y; ⟨Quotient.mk r x, hx⟩⟩
    let e : Quotient r ≃ₜ unitInterval :=
      hg_cont.homeoOfEquivCompactToT2 (f := Equiv.ofBijective g hg_bij)
    have hI_spec : SpectralSpace unitInterval := by
      have _ : CompactSpace unitInterval := inferInstance
      exact e.symm.isOpenEmbedding.spectralSpace
    -- In a spectral Hausdorff space every distinct pair is separated by a compact open, hence
    -- a clopen; this contradicts connectedness of `unitInterval`.
    have h01 : (0 : unitInterval) ≠ (1 : unitInterval) := zero_ne_one
    obtain ⟨U, hUo, hUc, h0U, h1U⟩ :=
      PrespectralSpace.not_specializes_iff_exists_isOpen_isCompact.mp
        (fun h ↦ h01 (specializes_iff_eq.mp h).symm)
    rcases isClopen_iff.mp ⟨hUc.isClosed, hUo⟩ with rfl | rfl
    · exact h0U
    · exact h1U (mem_univ _)
  exact ⟨hXspec, hR, hgen, hT0, hnot_spec⟩

/-! ### Non-example: global quasi-compactness is needed on noncompact locally spectral spaces -/

/-- On discrete `ℕ` with the total relation, the graph projection is open, generalizing, and
locally spectral, yet not globally spectral because the fibre over `{0}` is infinite. -/
example :
    IsLocallySpectralSpace ℕ ∧
      IsLocallyProConstructible {q : ℕ × ℕ | (⊤ : Setoid ℕ) q.1 q.2} ∧
      IsOpenMap (fun q : {q : ℕ × ℕ // (⊤ : Setoid ℕ) q.1 q.2} ↦ q.1.1) ∧
      IsLocallySpectralMap (fun q : {q : ℕ × ℕ // (⊤ : Setoid ℕ) q.1 q.2} ↦ q.1.1) ∧
      ¬ IsSpectralMap (fun q : {q : ℕ × ℕ // (⊤ : Setoid ℕ) q.1 q.2} ↦ q.1.1) := by
  have hN : IsLocallySpectralSpace ℕ :=
    isLocallySpectralSpace_iff.mpr fun n ↦ ⟨{n}, isOpen_discrete _, rfl, {}⟩
  have hR : IsLocallyProConstructible {q : ℕ × ℕ | (⊤ : Setoid ℕ) q.1 q.2} :=
    isLocallyProConstructible_univ
  have hopen : IsOpenMap (fun q : {q : ℕ × ℕ // (⊤ : Setoid ℕ) q.1 q.2} ↦ q.1.1) :=
    isOpenMap_fst.comp ((Homeomorph.Set.univ (ℕ × ℕ)).isOpenMap : IsOpenMap Subtype.val)
  have hls :
      IsLocallySpectralMap (fun q : {q : ℕ × ℕ // (⊤ : Setoid ℕ) q.1 q.2} ↦ q.1.1) := by
    have _ : PrespectralSpace ℕ := hN.prespectralSpace
    exact isLocallySpectralMap_fst.comp (hN.prod hN)
      (hR.isLocallySpectralMap_subtypeVal (hN.prod hN))
  refine ⟨hN, hR, hopen, hls, fun hs ↦ ?_⟩
  have hc := hs.isCompact_preimage_of_isOpen (isOpen_discrete ({0} : Set ℕ)) isCompact_singleton
  rw [isCompact_iff_finite] at hc
  exact infinite_of_injective_forall_mem
    (f := fun n : ℕ ↦ (⟨(0, n), trivial⟩ : {q : ℕ × ℕ // (⊤ : Setoid ℕ) q.1 q.2}))
    (fun _ _ h ↦ congrArg (fun q ↦ q.1.2) h) (fun _ ↦ rfl) hc

end TauCeti
