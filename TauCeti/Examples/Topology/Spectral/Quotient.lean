/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import TauCeti.Topology.Spectral.Quotient
import Mathlib.GroupTheory.GroupAction.Basic
import Mathlib.Topology.Algebra.ConstMulAction
import Mathlib.Topology.Compactification.OnePoint.Basic
import Mathlib.Topology.Connected.TotallyDisconnected
import Mathlib.Topology.InductiveDimension.Classes
import Mathlib.Topology.Separation.Regular

/-!
# Checks for spectral and locally spectral quotients

This file exercises the quotient theorems of `TauCeti.Topology.Spectral.Quotient` on concrete
examples and counterexamples:

1. **Diagonal relation** (`⊥ : Setoid X`): on any spectral space `X`, the diagonal is
   pro-constructible (`IsSpectralMap.isProConstructible_eq`) with homeomorphic projections, so both
   `Setoid.spectralSpace_quotient` and `Setoid.spectralSpace_quotient_of_isOpenMap` apply.
2. **Total relation** (`⊤ : Setoid X`): on any spectral space `X` (empty or nonempty), the full
   relation `X × X` has closed graph and open projections, making `Quotient (⊤ : Setoid X)`
   spectral via both criteria (including `Empty` with the basis `{∅}`).
3. **Finite group actions on profinite spaces**: for a finite group acting by homeomorphisms on a
   profinite space, `MulAction.orbitRel G X` has closed graph and open projections, so the orbit
   space is both spectral and profinite (`CompactSpace`, `T2Space`, `TotallyDisconnectedSpace`).
4. **Saturations of quasi-compact opens need not be open**: on the profinite space `OnePoint ℕ`,
   identifying `0` with `∞` only gives a closed relation with generalizing spectral projections for
   which the compact open `{(0 : ℕ)}` has non-open saturation `{(0 : ℕ), ∞}`, illustrating why
   `Setoid.exists_isCompact_isOpen_and_isOpen_preimage_image_eq` places the invariant open
   neighbourhood inside a larger compact open `W'`.
5. **Global quasi-compactness of projections is essential**: on discrete `ℕ` with the total
   relation, the graph is locally pro-constructible and its projections are open, generalizing, and
   locally spectral, yet neither the projections nor the quotient map are quasi-compact.
-/

open Set Topology TopologicalSpace OnePoint TauCeti

namespace TauCeti

/-! ### 1. Diagonal relation on a spectral space -/

/-- For the diagonal relation `⊥ : Setoid X` on a spectral space `X`, the graph is pro-constructible
and its first projection is a homeomorphism, so `Setoid.spectralSpace_quotient_of_isOpenMap`
applies. -/
example (X : Type*) [TopologicalSpace X] [SpectralSpace X] :
    SpectralSpace (Quotient (⊥ : Setoid X)) := by
  have hR : IsProConstructible {q : X × X | (⊥ : Setoid X) q.1 q.2} :=
    isProperMap_fst_of_compactSpace.isSpectralMap.isProConstructible_eq
      isProperMap_snd_of_compactSpace.isSpectralMap
  let e : {q : X × X // (⊥ : Setoid X) q.1 q.2} ≃ₜ X :=
    { toFun := fun q ↦ q.1.1
      invFun := fun x ↦ ⟨(x, x), rfl⟩
      left_inv := by rintro ⟨⟨x, y⟩, rfl : x = y⟩; rfl
      right_inv := fun _ ↦ rfl
      continuous_toFun := continuous_fst.comp continuous_subtype_val
      continuous_invFun := (continuous_id.prodMk continuous_id).subtype_mk fun _ ↦ rfl }
  exact (⊥ : Setoid X).spectralSpace_quotient_of_isOpenMap hR e.isOpenMap

/-- The basis criterion `Setoid.spectralSpace_quotient` also applies to the diagonal relation
`⊥ : Setoid X`, using the images of the quasi-compact opens of `X`. -/
example (X : Type*) [TopologicalSpace X] [SpectralSpace X] :
    SpectralSpace (Quotient (⊥ : Setoid X)) := by
  let r : Setoid X := ⊥
  have hR : IsProConstructible {q : X × X | r q.1 q.2} :=
    isProperMap_fst_of_compactSpace.isSpectralMap.isProConstructible_eq
      isProperMap_snd_of_compactSpace.isSpectralMap
  let e : {q : X × X // r q.1 q.2} ≃ₜ X :=
    { toFun := fun q ↦ q.1.1
      invFun := fun x ↦ ⟨(x, x), rfl⟩
      left_inv := by rintro ⟨⟨x, y⟩, rfl : x = y⟩; rfl
      right_inv := fun _ ↦ rfl
      continuous_toFun := continuous_fst.comp continuous_subtype_val
      continuous_invFun := (continuous_id.prodMk continuous_id).subtype_mk fun _ ↦ rfl }
  have hπ : IsOpenQuotientMap (Quotient.mk r) :=
    ⟨Quotient.mk_surjective, continuous_quotient_mk',
      r.isOpenMap_quotientMk_of_isOpenMap e.isOpenMap⟩
  have hgen : GeneralizingMap (fun q : {q : X × X // r q.1 q.2} ↦ q.1.1) :=
    fun z y hyz ↦ ⟨e.symm y, e.left_inv z ▸ hyz.map e.symm.continuous, e.right_inv y⟩
  refine r.spectralSpace_quotient hR hgen
    (hπ.isTopologicalBasis PrespectralSpace.isTopologicalBasis) ?_
  rintro _ ⟨U, ⟨_, hUc⟩, rfl⟩
  rw [preimage_image_eq U fun _ _ hxy ↦ Quotient.exact hxy]
  exact hUc

/-! ### 2. Total relation on empty and general spectral spaces -/

/-- On the empty spectral space, `{∅}` is a topological basis of `Quotient (⊤ : Setoid Empty)` with
empty (compact) inverse image, verifying `Setoid.spectralSpace_quotient`. -/
example : SpectralSpace (Quotient (⊤ : Setoid Empty)) := by
  have hB₀ : IsTopologicalBasis ({∅} : Set (Set Empty)) :=
    isTopologicalBasis_of_isOpen_of_nhds (by simp) fun x ↦ Empty.elim x
  have _ : SpectralSpace Empty :=
    { toPrespectralSpace := .of_isTopologicalBasis hB₀ (by simp) }
  let r : Setoid Empty := ⊤
  have hB : IsTopologicalBasis ({∅} : Set (Set (Quotient r))) := by
    refine isTopologicalBasis_of_isOpen_of_nhds (by simp) fun q ↦ ?_
    induction q using Quotient.inductionOn with | h x => exact Empty.elim x
  exact r.spectralSpace_quotient isClosed_univ.isProConstructible
    (fun z ↦ Empty.elim z.1.1) hB (by simp)

/-- On any spectral space `X` (empty or nonempty), the total relation `⊤ : Setoid X` has closed
graph `univ` and open first projection, so `Quotient (⊤ : Setoid X)` is spectral and the quotient
map is open, spectral, and generalizing. -/
example (X : Type*) [TopologicalSpace X] [SpectralSpace X] :
    SpectralSpace (Quotient (⊤ : Setoid X)) ∧
      IsOpenMap (Quotient.mk (⊤ : Setoid X)) ∧
      IsSpectralMap (Quotient.mk (⊤ : Setoid X)) ∧
      GeneralizingMap (Quotient.mk (⊤ : Setoid X)) := by
  let r : Setoid X := ⊤
  have hR : IsProConstructible {q : X × X | r q.1 q.2} := isClosed_univ.isProConstructible
  have hopen : IsOpenMap (fun q : {q : X × X // r q.1 q.2} ↦ q.1.1) :=
    isOpenMap_fst.comp (Homeomorph.Set.univ (X × X)).isOpenMap
  refine ⟨r.spectralSpace_quotient_of_isOpenMap hR hopen,
    r.isOpenMap_quotientMk_of_isOpenMap hopen,
    r.isSpectralMap_quotientMk_of_isOpenMap hopen (r.isSpectralMap_fst hR),
    r.generalizingMap_quotientMk_of_isOpenMap SpectralSpace.isLocallySpectralSpace
      hR.isLocallyProConstructible hopen (r.isSpectralMap_fst hR)⟩

/-! ### 3. Finite group actions on profinite spaces -/

/-- For a finite group `G` acting by homeomorphisms on a profinite space `X`, the orbit quotient
`MulAction.orbitRel.Quotient G X` is spectral, compact, Hausdorff, and totally disconnected. -/
example (G X : Type*) [Group G] [Finite G] [TopologicalSpace X] [CompactSpace X] [T2Space X]
    [TotallyDisconnectedSpace X] [MulAction G X] [ContinuousConstSMul G X] :
    SpectralSpace (MulAction.orbitRel.Quotient G X) ∧
      CompactSpace (MulAction.orbitRel.Quotient G X) ∧
      T2Space (MulAction.orbitRel.Quotient G X) ∧
      TotallyDisconnectedSpace (MulAction.orbitRel.Quotient G X) := by
  have _ : SpectralSpace X :=
    { toPrespectralSpace := .of_isTopologicalBasis isTopologicalBasis_isClopen
        fun _ hU ↦ hU.isClosed.isCompact }
  let r : Setoid X := MulAction.orbitRel G X
  have hR_eq : {q : X × X | r q.1 q.2} = ⋃ g : G, {q : X × X | g • q.2 = q.1} := by
    ext ⟨x, y⟩
    simp [r, MulAction.orbitRel_apply, MulAction.mem_orbit_iff]
  have hR_closed : IsClosed {q : X × X | r q.1 q.2} := by
    rw [hR_eq]
    exact isClosed_iUnion_of_finite fun g ↦
      isClosed_eq ((continuous_const_smul g).comp continuous_snd) continuous_fst
  have hopen : IsOpenMap (fun q : {q : X × X // r q.1 q.2} ↦ q.1.1) := by
    intro W hW
    obtain ⟨O, hO, rfl⟩ := isOpen_induced_iff.mp hW
    have himg : (fun q : {q : X × X // r q.1 q.2} ↦ q.1.1) '' (Subtype.val ⁻¹' O) =
        ⋃ g : G, (fun x : X ↦ (x, g⁻¹ • x)) ⁻¹' O := by
      ext x
      simp only [mem_image, Subtype.exists, mem_preimage, Prod.exists, mem_iUnion]
      refine ⟨fun ⟨a, b, ⟨g, hg⟩, hOab, hax⟩ ↦ ⟨g, by simpa [← hax, ← hg] using hOab⟩,
        fun ⟨g, hg⟩ ↦ ⟨x, g⁻¹ • x, ⟨g, smul_inv_smul g x⟩, hg, rfl⟩⟩
    rw [himg]
    exact isOpen_iUnion fun g ↦ hO.preimage (continuous_id.prodMk (continuous_const_smul g⁻¹))
  have hspec : SpectralSpace (Quotient r) :=
    r.spectralSpace_quotient_of_isOpenMap hR_closed.isProConstructible hopen
  have hπ_oq : IsOpenQuotientMap (Quotient.mk r) :=
    ⟨Quotient.mk_surjective, continuous_quotient_mk', r.isOpenMap_quotientMk_of_isOpenMap hopen⟩
  have _ : T2Space (Quotient r) := (t2Space_iff_of_isOpenQuotientMap hπ_oq).mpr
    (by simpa only [Quotient.eq] using hR_closed)
  have _ : ZeroDimensionalSpace (Quotient r) :=
    ZeroDimensionalSpace.of_isTopologicalBasis
      (u := {U : Set (Quotient r) | IsOpen U ∧ IsCompact U})
      (fun _ ⟨hUo, hUc⟩ ↦ ⟨hUc.isClosed, hUo⟩)
      hspec.toPrespectralSpace.isTopologicalBasis
  exact ⟨hspec, Quotient.compactSpace, inferInstance, inferInstance⟩

/-! ### 4. Saturations of quasi-compact opens need not be open -/

/-- On `OnePoint ℕ`, identifying `(0 : ℕ)` with `∞` only gives a closed relation with generalizing
projections for which `{(0 : ℕ)}` is compact open, its saturation `{(0 : ℕ), ∞}` is not open (so no
invariant open `U` lies between `{(0 : ℕ)}` and its saturation), yet
`Setoid.exists_isCompact_isOpen_and_isOpen_preimage_image_eq` produces an invariant open `U` inside
a larger compact open `W'`. -/
example :
    ∃ (r : Setoid (OnePoint ℕ)) (W : Set (OnePoint ℕ)),
      IsClosed {q : OnePoint ℕ × OnePoint ℕ | r q.1 q.2} ∧
      GeneralizingMap (fun q : {q : OnePoint ℕ × OnePoint ℕ // r q.1 q.2} ↦ q.1.1) ∧
      IsOpen W ∧ IsCompact W ∧
      ¬ IsOpen (Quotient.mk r ⁻¹' (Quotient.mk r '' W)) ∧
      ∃ W' U : Set (OnePoint ℕ), IsOpen W' ∧ IsCompact W' ∧
        Quotient.mk r ⁻¹' (Quotient.mk r '' W) ⊆ W' ∧
        IsOpen U ∧ Quotient.mk r ⁻¹' (Quotient.mk r '' U) = U ∧ W ⊆ U ∧ U ⊆ W' := by
  have _ : SpectralSpace (OnePoint ℕ) :=
    { toPrespectralSpace := .of_isTopologicalBasis isTopologicalBasis_isClopen
        fun _ hU ↦ hU.isClosed.isCompact }
  let z0 : OnePoint ℕ := ((0 : ℕ) : OnePoint ℕ)
  let r : Setoid (OnePoint ℕ) :=
    { r := fun x y ↦ x = y ∨ (x = z0 ∧ y = ∞) ∨ (x = ∞ ∧ y = z0)
      iseqv :=
        { refl := fun _ ↦ Or.inl rfl
          symm := by rintro x y (rfl | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) <;> simp
          trans := by
            rintro x y z (rfl | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) (rfl | ⟨h, rfl⟩ | ⟨h, rfl⟩) <;>
              simp_all } }
  have hR_eq : {q : OnePoint ℕ × OnePoint ℕ | r q.1 q.2} =
      diagonal (OnePoint ℕ) ∪ {(z0, ∞)} ∪ {(∞, z0)} := by
    ext ⟨x, y⟩
    simp only [mem_ofPred_eq, union_assoc, mem_union, mem_diagonal_iff,
      mem_singleton_iff, Prod.mk.injEq]
    rfl
  have hR_closed : IsClosed {q : OnePoint ℕ × OnePoint ℕ | r q.1 q.2} := by
    rw [hR_eq]
    exact (isClosed_diagonal.union isClosed_singleton).union isClosed_singleton
  have hgen : GeneralizingMap (fun q : {q : OnePoint ℕ × OnePoint ℕ // r q.1 q.2} ↦ q.1.1) :=
    fun z _ hyz ↦ ⟨z, specializes_rfl, hyz.eq.symm⟩
  have hWo : IsOpen ({z0} : Set (OnePoint ℕ)) := by
    rw [← image_singleton]
    exact OnePoint.isOpen_image_coe.mpr (isOpen_discrete _)
  have hnot_open : ¬ IsOpen (Quotient.mk r ⁻¹' (Quotient.mk r '' {z0})) := fun ho ↦ by
    have hinf_mem : (∞ : OnePoint ℕ) ∈ Quotient.mk r ⁻¹' (Quotient.mk r '' {z0}) :=
      ⟨z0, rfl, Quotient.sound (Or.inr (Or.inl ⟨rfl, rfl⟩))⟩
    have hc : IsCompact (((↑) : ℕ → OnePoint ℕ) ⁻¹'
        (Quotient.mk r ⁻¹' (Quotient.mk r '' {z0})))ᶜ :=
      ((OnePoint.isOpen_iff_of_mem' hinf_mem).mp ho).1
    have hsub : range Nat.succ ⊆
        (((↑) : ℕ → OnePoint ℕ) ⁻¹' (Quotient.mk r ⁻¹' (Quotient.mk r '' {z0})))ᶜ := by
      rintro _ ⟨n, rfl⟩ ⟨w, rfl, hwn⟩
      rcases Quotient.exact hwn with h | ⟨_, h⟩ | ⟨h, _⟩
      · exact Nat.succ_ne_zero n (OnePoint.coe_eq_coe.mp h).symm
      · exact OnePoint.coe_ne_infty (n + 1) h
      · exact OnePoint.coe_ne_infty 0 h
    exact infinite_range_of_injective Nat.succ_injective
      ((isCompact_iff_finite.mp hc).subset hsub)
  exact ⟨r, {z0}, hR_closed, hgen, hWo, isCompact_singleton, hnot_open,
    r.exists_isCompact_isOpen_and_isOpen_preimage_image_eq
      SpectralSpace.isLocallySpectralSpace hR_closed.isProConstructible.isLocallyProConstructible
      (r.isSpectralMap_fst hR_closed.isProConstructible) hgen hWo isCompact_singleton⟩

/-! ### 5. Global quasi-compactness of the graph projections is essential -/

/-- On discrete `ℕ` with the total relation `⊤ : Setoid ℕ`, the space is locally spectral and
quasiseparated, the graph is locally pro-constructible, and the first projection is open,
generalizing, and locally spectral, yet neither the first projection nor the quotient map is
quasi-compact (`IsSpectralMap`). -/
example :
    let r : Setoid ℕ := ⊤
    IsLocallySpectralSpace ℕ ∧
      IsLocallyProConstructible {q : ℕ × ℕ | r q.1 q.2} ∧
      IsOpenMap (fun q : {q : ℕ × ℕ // r q.1 q.2} ↦ q.1.1) ∧
      GeneralizingMap (fun q : {q : ℕ × ℕ // r q.1 q.2} ↦ q.1.1) ∧
      IsLocallySpectralMap (fun q : {q : ℕ × ℕ // r q.1 q.2} ↦ q.1.1) ∧
      ¬ IsSpectralMap (fun q : {q : ℕ × ℕ // r q.1 q.2} ↦ q.1.1) ∧
      ¬ IsSpectralMap (Quotient.mk r) := by
  intro r
  have hN : IsLocallySpectralSpace ℕ := isLocallySpectralSpace_iff.mpr fun n ↦
    ⟨{n}, isOpen_discrete _, rfl, {}⟩
  have hR : IsLocallyProConstructible {q : ℕ × ℕ | r q.1 q.2} :=
    isClosed_univ.isLocallyProConstructible
  have hopen : IsOpenMap (fun q : {q : ℕ × ℕ // r q.1 q.2} ↦ q.1.1) :=
    isOpenMap_fst.comp (Homeomorph.Set.univ (ℕ × ℕ)).isOpenMap
  have hnot_fst : ¬ IsSpectralMap (fun q : {q : ℕ × ℕ // r q.1 q.2} ↦ q.1.1) := fun h ↦ by
    have hc := (h.isCompact_preimage_of_isOpen (isOpen_discrete ({0} : Set ℕ))
      isCompact_singleton).image (continuous_snd.comp continuous_subtype_val)
    have himg : (fun q : {q : ℕ × ℕ // r q.1 q.2} ↦ q.1.2) ''
        ((fun q : {q : ℕ × ℕ // r q.1 q.2} ↦ q.1.1) ⁻¹' {0}) = univ :=
      eq_univ_of_forall fun n ↦ ⟨⟨(0, n), trivial⟩, rfl, rfl⟩
    exact infinite_univ (isCompact_iff_finite.mp (himg ▸ hc))
  have _ : Subsingleton (Quotient r) := ⟨Quotient.ind₂ fun _ _ ↦ Quotient.sound trivial⟩
  have hnot_quot : ¬ IsSpectralMap (Quotient.mk r) := fun h ↦
    infinite_univ (isCompact_iff_finite.mp
      (h.isCompact_preimage_of_isOpen isOpen_univ CompactSpace.isCompact_univ))
  exact ⟨hN, hR, hopen,
    (r.isLocallySpectralMap_fst hN hR).generalizingMap_of_isOpenMap
      (r.isLocallySpectralSpace_graph hN hR) hN hopen,
    r.isLocallySpectralMap_fst hN hR, hnot_fst, hnot_quot⟩

end TauCeti
