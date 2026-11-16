/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Spectral.LocallyProConstructible
import Mathlib.Order.Setoid.Basic
import Mathlib.Topology.Maps.OpenQuotient
import Mathlib.Topology.WithTopology
import TauCeti.Topology.Constructions.Basic
import TauCeti.Topology.Spectral.PatchCriterion

/-!
# Quotients of spectral and locally spectral spaces

Criteria for the quotient of a spectral or locally spectral space by a pro-constructible
equivalence relation to be T₀, locally spectral, or spectral.

For a `Setoid` `r` on a topological space `X`, swapping coordinates restricts to a
self-homeomorphism of the graph `R = {q : X × X // r q.1 q.2}` intertwining the two projections
`s, t : R → X`. Thus hypotheses such as being generalizing, spectral (quasicompact), or open
need only be assumed for the first projection `s` (see also `Setoid.isOpenMap_fst_iff_snd` and
`Setoid.isOpenMap_quotient_mk_iff` in `TauCeti.Topology.Constructions.Basic`).

When `X` is quasiseparated and locally spectral and `R` is locally pro-constructible with
quasicompact generalizing first projection `s`:

* every open subset `W` whose `r`-saturation lies in an open set `W'` admits an `r`-invariant
  open neighbourhood `U` with `W ⊆ U ⊆ W'` — and for compact open `W`, `U` lies inside an
  `r`-invariant intersection of a nonempty family of compact opens;
* `Quotient.mk r` is generalizing;
* `Quotient r` is T₀.

If `X` is spectral, `R` is pro-constructible with generalizing first projection, and `Quotient r`
admits a basis of opens with compact preimages in `X`, then `Quotient r` is spectral — proved via
the patch criterion using the coinduced constructible topology as the compact witness.

Finally, when `s : R → X` is open and quasicompact on a quasiseparated locally spectral space
with locally pro-constructible `R`, the generalizing hypothesis holds automatically, `Quotient.mk r`
is open and spectral, and `Quotient r` is quasiseparated and locally spectral (and spectral when
`X` is spectral).

## Main results

* `Setoid.generalizingMap_fst_iff_snd`, `Setoid.isSpectralMap_fst_iff_snd`: symmetry of the two
  projections `R → X` of an equivalence relation.
* `TauCeti.exists_isOpen_saturated_subset` and `TauCeti.exists_isOpen_saturated_subset_sInter`:
  invariant open neighbourhoods for locally pro-constructible equivalence relations.
* `TauCeti.generalizingMap_quotient_mk` and `TauCeti.t0Space_quotient`: the quotient map is
  generalizing and the quotient space is T₀.
* `TauCeti.spectralSpace_quotient`: the spectral quotient criterion.
* `Setoid.isSpectralMap_quotient_mk_of_isOpenMap`,
  `Setoid.quasiSeparatedSpace_quotient_of_isOpenMap`,
  `TauCeti.isLocallySpectralSpace_quotient_of_isOpenMap`, and
  `TauCeti.spectralSpace_quotient_of_isOpenMap`: quotients by open quasicompact equivalence
  relations.

## References

* P. Scholze, *Étale cohomology of diamonds*, arXiv:1709.07343, §2, Lemmas 2.7, 2.9, and 2.10.
-/

public section

namespace TauCeti

open Set Topology TopologicalSpace

variable {X : Type*} [TopologicalSpace X]

/-! ### Symmetry of equivalence-relation projections -/

/-- By symmetry of `r`, the first projection `R → X` is generalizing if and only if the second
projection is generalizing. -/
theorem _root_.Setoid.generalizingMap_fst_iff_snd (r : Setoid X) :
    GeneralizingMap (fun q : {q : X × X // r q.1 q.2} ↦ q.1.1) ↔
      GeneralizingMap (fun q : {q : X × X // r q.1 q.2} ↦ q.1.2) := by
  let e : {q : X × X // r q.1 q.2} ≃ₜ {q : X × X // r q.1 q.2} :=
    (Homeomorph.prodComm X X).subtype fun _ ↦ ⟨r.symm, r.symm⟩
  exact ⟨fun h ↦ e.isOpenEmbedding.generalizingMap.comp h,
    fun h ↦ e.symm.isOpenEmbedding.generalizingMap.comp h⟩

/-- By symmetry of `r`, the first projection `R → X` is spectral if and only if the second
projection is spectral. -/
theorem _root_.Setoid.isSpectralMap_fst_iff_snd (r : Setoid X) :
    IsSpectralMap (fun q : {q : X × X // r q.1 q.2} ↦ q.1.1) ↔
      IsSpectralMap (fun q : {q : X × X // r q.1 q.2} ↦ q.1.2) := by
  let e : {q : X × X // r q.1 q.2} ≃ₜ {q : X × X // r q.1 q.2} :=
    (Homeomorph.prodComm X X).subtype fun _ ↦ ⟨r.symm, r.symm⟩
  exact ⟨fun h ↦ h.comp e.isProperMap.isSpectralMap,
    fun h ↦ h.comp e.symm.isProperMap.isSpectralMap⟩

/-! ### Invariant neighbourhoods, generalizing quotients, and T₀ separation -/

/-- Each equivalence class of a locally pro-constructible equivalence relation on a locally
spectral space is locally pro-constructible. -/
private theorem isLocallyProConstructible_relClass (hX : IsLocallySpectralSpace X) {r : Setoid X}
    (hR : IsLocallyProConstructible {q : X × X | r q.1 q.2}) (y : X) :
    IsLocallyProConstructible {z : X | r z y} :=
  hR.preimage (hX.prod hX) (isLocallySpectralMap_prodMk_left y)

section LocallyProConstructible

variable [QuasiSeparatedSpace X]

/-- **Invariant open neighbourhoods for locally pro-constructible equivalence relations.**
Let `X` be quasiseparated and locally spectral, and let `r` be a locally pro-constructible
equivalence relation whose first projection `R → X` is quasicompact and generalizing. Whenever an
open subset `W` has its `r`-saturation contained in an open subset `W'`, there exists an
`r`-invariant open subset `U` with `W ⊆ U ⊆ W'`. -/
theorem exists_isOpen_saturated_subset (hX : IsLocallySpectralSpace X) {r : Setoid X}
    (hR : IsLocallyProConstructible {q : X × X | r q.1 q.2})
    (hs_qc : IsSpectralMap fun q : {q : X × X // r q.1 q.2} ↦ q.1.1)
    (hs_gen : GeneralizingMap fun q : {q : X × X // r q.1 q.2} ↦ q.1.1)
    {W W' : Set X} (hWo : IsOpen W) (hW'o : IsOpen W')
    (hW'sub : {y | ∃ x ∈ W, r x y} ⊆ W') :
    ∃ U : Set X,
      IsOpen U ∧ (∀ ⦃x y⦄, r x y → x ∈ U → y ∈ U) ∧ W ⊆ U ∧ U ⊆ W' := by
  have := hX.prespectralSpace
  have : QuasiSeparatedSpace (X × X) := QuasiSeparatedSpace.prod
  have hR_ls : IsLocallySpectralSpace {q : X × X // r q.1 q.2} :=
    hR.isLocallySpectralSpace (hX.prod hX)
  have : QuasiSeparatedSpace {q : X × X // r q.1 q.2} :=
    hR.quasiSeparatedSpace (hX.prod hX)
  have ht_qc : IsSpectralMap fun q : {q : X × X // r q.1 q.2} ↦ q.1.2 :=
    r.isSpectralMap_fst_iff_snd.mp hs_qc
  let F : Set X := {y | ∃ x ∈ W'ᶜ, r x y}
  have hF_eq : F = (fun q : {q : X × X // r q.1 q.2} ↦ q.1.2) ''
      ((fun q : {q : X × X // r q.1 q.2} ↦ q.1.1) ⁻¹' W'ᶜ) :=
    (r.image_snd_preimage_fst W'ᶜ).symm
  have hF_lpc : IsLocallyProConstructible F := by
    rw [hF_eq]
    exact (hW'o.isClosed_compl.preimage hs_qc.continuous).isLocallyProConstructible.image
      hR_ls ht_qc.isLocallySpectralMap ht_qc
  -- The closure of `F` is `r`-invariant because `closure F` is the set of specializations of `F`
  -- and the first projection `R → X` lifts generalizations.
  have hclF_inv : ∀ ⦃y y'⦄, r y y' → y ∈ closure F → y' ∈ closure F := by
    intro y y' hyy' hy
    rw [hF_lpc.closure_eq_setOfPred_specializes hX] at hy ⊢
    obtain ⟨z, ⟨x, hxW', hxz⟩, hzy⟩ := hy
    obtain ⟨q, hq_sp, hq1⟩ := hs_gen (a := ⟨(y, y'), hyy'⟩) hzy
    refine ⟨q.1.2, ⟨x, hxW', r.trans hxz (hq1 ▸ q.2)⟩, ?_⟩
    exact hq_sp.map (continuous_snd.comp continuous_subtype_val)
  refine ⟨(closure F)ᶜ, isClosed_closure.isOpen_compl, ?_, ?_, ?_⟩
  · intro x y hxy hxU hycl
    exact hxU (hclF_inv (r.symm hxy) hycl)
  · intro y hyW hycl
    rw [hF_lpc.closure_eq_setOfPred_specializes hX] at hycl
    obtain ⟨z, ⟨x, hxW', hxz⟩, hzy⟩ := hycl
    have hzW : z ∈ W := hzy.mem_open hWo hyW
    exact hxW' (hW'sub ⟨z, hzW, r.symm hxz⟩)
  · intro y hyU
    by_contra hyW'
    exact hyU (subset_closure ⟨y, hyW', r.refl y⟩)

/-- **Scholze [ECD] Lemma 2.7 (invariant neighbourhoods).** Under the hypotheses of
`TauCeti.exists_isOpen_saturated_subset`, every compact open subset `W ⊆ X` admits an
`r`-invariant open neighbourhood `U` contained in an `r`-invariant intersection `⋂₀ ℱ` of a
nonempty family `ℱ` of compact open subsets of `X`. -/
theorem exists_isOpen_saturated_subset_sInter (hX : IsLocallySpectralSpace X) {r : Setoid X}
    (hR : IsLocallyProConstructible {q : X × X | r q.1 q.2})
    (hs_qc : IsSpectralMap fun q : {q : X × X // r q.1 q.2} ↦ q.1.1)
    (hs_gen : GeneralizingMap fun q : {q : X × X // r q.1 q.2} ↦ q.1.1)
    {W : Set X} (hWo : IsOpen W) (hWc : IsCompact W) :
    ∃ (U : Set X) (ℱ : Set (Set X)),
      IsOpen U ∧ (∀ ⦃x y⦄, r x y → x ∈ U → y ∈ U) ∧
      ℱ.Nonempty ∧ (∀ V ∈ ℱ, IsOpen V ∧ IsCompact V) ∧
      (∀ ⦃x y⦄, r x y → x ∈ ⋂₀ ℱ → y ∈ ⋂₀ ℱ) ∧
      W ⊆ U ∧ U ⊆ ⋂₀ ℱ := by
  have := hX.prespectralSpace
  have ht_gen : GeneralizingMap fun q : {q : X × X // r q.1 q.2} ↦ q.1.2 :=
    r.generalizingMap_fst_iff_snd.mp hs_gen
  let E : Set X := {y | ∃ x ∈ W, r x y}
  have hE_eq : E = (fun q : {q : X × X // r q.1 q.2} ↦ q.1.2) ''
      ((fun q : {q : X × X // r q.1 q.2} ↦ q.1.1) ⁻¹' W) :=
    (r.image_snd_preimage_fst W).symm
  have hEc : IsCompact E := by
    rw [hE_eq]
    exact (hs_qc.isCompact_preimage_of_isOpen hWo hWc).image
      (continuous_snd.comp continuous_subtype_val)
  obtain ⟨W', hW'c, hW'o, hEW', -⟩ :=
    PrespectralSpace.exists_isCompact_and_isOpen_between hEc isOpen_univ (subset_univ _)
  obtain ⟨U, hUo, hUinv, hWU, hUW'⟩ :=
    exists_isOpen_saturated_subset hX hR hs_qc hs_gen hWo hW'o hEW'
  let E' : Set X := {y | ∃ x ∈ W', r x y}
  have hE'_eq : E' = (fun q : {q : X × X // r q.1 q.2} ↦ q.1.2) ''
      ((fun q : {q : X × X // r q.1 q.2} ↦ q.1.1) ⁻¹' W') :=
    (r.image_snd_preimage_fst W').symm
  have hE'c : IsCompact E' := by
    rw [hE'_eq]
    exact (hs_qc.isCompact_preimage_of_isOpen hW'o hW'c).image
      (continuous_snd.comp continuous_subtype_val)
  have hE'gen : StableUnderGeneralization E' := by
    rw [hE'_eq]
    exact ht_gen.stableUnderGeneralization_image
      (hW'o.preimage hs_qc.continuous).stableUnderGeneralization
  let ℱ : Set (Set X) := {V : Set X | IsOpen V ∧ IsCompact V ∧ E' ⊆ V}
  have hE'eq : E' = ⋂₀ ℱ := hE'c.eq_sInter_of_stableUnderGeneralization hE'gen
  obtain ⟨V₀, hV₀c, hV₀o, hE'V₀, -⟩ :=
    PrespectralSpace.exists_isCompact_and_isOpen_between hE'c isOpen_univ (subset_univ _)
  refine ⟨U, ℱ, hUo, hUinv, ⟨V₀, hV₀o, hV₀c, hE'V₀⟩,
    fun V hV ↦ ⟨hV.1, hV.2.1⟩, ?_, hWU, ?_⟩
  · intro x y hxy hx
    rw [← hE'eq] at hx ⊢
    obtain ⟨w, hwW', hwx⟩ := hx
    exact ⟨w, hwW', r.trans hwx hxy⟩
  · rw [← hE'eq]
    exact hUW'.trans fun y hy ↦ ⟨y, hy, r.refl y⟩

/-- The quotient map by a locally pro-constructible equivalence relation with quasicompact
generalizing first projection on a quasiseparated locally spectral space is generalizing. -/
theorem generalizingMap_quotient_mk (hX : IsLocallySpectralSpace X) {r : Setoid X}
    (hR : IsLocallyProConstructible {q : X × X | r q.1 q.2})
    (hs_qc : IsSpectralMap fun q : {q : X × X // r q.1 q.2} ↦ q.1.1)
    (hs_gen : GeneralizingMap fun q : {q : X × X // r q.1 q.2} ↦ q.1.1) :
    GeneralizingMap (Quotient.mk r) := by
  have := hX.prespectralSpace
  have ht_gen : GeneralizingMap fun q : {q : X × X // r q.1 q.2} ↦ q.1.2 :=
    r.generalizingMap_fst_iff_snd.mp hs_gen
  intro x b hb
  obtain ⟨y, rfl⟩ := Quotient.exists_rep b
  -- Show `x ∈ closure {z | r z y}` by testing against compact open neighbourhoods `W ∋ x`.
  have hxcl : x ∈ closure {z : X | r z y} := by
    refine PrespectralSpace.isTopologicalBasis.mem_closure_iff.mpr ?_
    rintro W ⟨hWo, hWc⟩ hxW
    let E : Set X := {w | ∃ u ∈ W, r u w}
    have hE_eq : E = (fun q : {q : X × X // r q.1 q.2} ↦ q.1.2) ''
        ((fun q : {q : X × X // r q.1 q.2} ↦ q.1.1) ⁻¹' W) :=
      (r.image_snd_preimage_fst W).symm
    have hEc : IsCompact E := by
      rw [hE_eq]
      exact (hs_qc.isCompact_preimage_of_isOpen hWo hWc).image
        (continuous_snd.comp continuous_subtype_val)
    have hEgen : StableUnderGeneralization E := by
      rw [hE_eq]
      exact ht_gen.stableUnderGeneralization_image
        (hWo.preimage hs_qc.continuous).stableUnderGeneralization
    have hyE : y ∈ E := by
      rw [hEc.eq_sInter_of_stableUnderGeneralization hEgen]
      rintro W' ⟨hW'o, -, hEW'⟩
      obtain ⟨U, hUo, hUinv, hWU, hUW'⟩ :=
        exists_isOpen_saturated_subset hX hR hs_qc hs_gen hWo hW'o hEW'
      have hqUo : IsOpen (Quotient.mk r '' U) :=
        r.isOpen_image_quotient_mk hUo fun _ _ hx hxy ↦ hUinv hxy hx
      obtain ⟨u, huU, huy⟩ := hb.mem_open hqUo ⟨x, hWU hxW, rfl⟩
      exact hUW' (hUinv (Quotient.exact huy) huU)
    obtain ⟨w, hwW, hwy⟩ := hyE
    exact ⟨w, hwW, hwy⟩
  rw [(isLocallyProConstructible_relClass hX hR y).closure_eq_setOfPred_specializes hX] at hxcl
  obtain ⟨z, hzy, hzx⟩ := hxcl
  exact ⟨z, hzx, Quotient.sound hzy⟩

/-- **Scholze [ECD] Lemma 2.7 (T₀ separation).** The quotient of a quasiseparated locally spectral
space by a locally pro-constructible equivalence relation with quasicompact generalizing first
projection is T₀. -/
theorem t0Space_quotient (hX : IsLocallySpectralSpace X) {r : Setoid X}
    (hR : IsLocallyProConstructible {q : X × X | r q.1 q.2})
    (hs_qc : IsSpectralMap fun q : {q : X × X // r q.1 q.2} ↦ q.1.1)
    (hs_gen : GeneralizingMap fun q : {q : X × X // r q.1 q.2} ↦ q.1.1) :
    T0Space (Quotient r) := by
  have hq_gen : GeneralizingMap (Quotient.mk r) :=
    generalizingMap_quotient_mk hX hR hs_qc hs_gen
  refine (t0Space_iff_inseparable (Quotient r)).mpr fun a b hab ↦ ?_
  obtain ⟨x, rfl⟩ := Quotient.exists_rep a
  obtain ⟨y, rfl⟩ := Quotient.exists_rep b
  obtain ⟨hxy_sp, hyx_sp⟩ := inseparable_iff_specializes_and.mp hab
  obtain ⟨U₀, hU₀o, hxU₀, hU₀s⟩ := isLocallySpectralSpace_iff.mp hX x
  have := hU₀s
  let Gx : Set U₀ := {u : U₀ | u ⤳ ⟨x, hxU₀⟩}
  let Ax : Set U₀ := (Subtype.val : U₀ → X) ⁻¹' {w : X | r w x}
  let Ay : Set U₀ := (Subtype.val : U₀ → X) ⁻¹' {w : X | r w y}
  let S : Set U₀ := Gx ∩ (Ax ∪ Ay)
  have hSpc : IsProConstructible S :=
    (isProConstructible_setOfPred_specializes (⟨x, hxU₀⟩ : U₀)).inter <|
      ((isLocallyProConstructible_relClass hX hR x).isProConstructible_preimage hU₀o).union
        ((isLocallyProConstructible_relClass hX hR y).isProConstructible_preimage hU₀o)
  have : SpectralSpace S := hSpc.spectralSpace
  -- Pick a minimal point `m ∈ S` under specialization as the generic point of an irreducible
  -- component of the spectral space `S`.
  let x₀ : S := ⟨⟨x, hxU₀⟩, specializes_rfl, Or.inl (r.refl x)⟩
  let C : irreducibleComponents S :=
    ⟨irreducibleComponent x₀, irreducibleComponent_mem_irreducibleComponents x₀⟩
  let m : S := (genericPoints.ofComponent C).1
  have hmin : ∀ z : S, z ⤳ m → z = m := fun z hzm ↦ by
    have hmgen : closure ({m} : Set S) = C.1 := genericPoints.isGenericPoint_ofComponent C
    have hsub : C.1 ⊆ closure ({z} : Set S) := hmgen ▸ specializes_iff_closure_subset.mp hzm
    have hcl_eq : closure ({z} : Set S) = closure ({m} : Set S) :=
      (C.2.eq_of_subset isIrreducible_singleton.closure hsub).symm.trans hmgen.symm
    exact (inseparable_iff_closure_eq.mpr hcl_eq).eq
  have hmx_sp : (m.1 : X) ⤳ x := m.2.1.map continuous_subtype_val
  -- Lifting a specialization into either class produces a point of `S` specializing to `m`,
  -- which by minimality must equal `m`.
  have hlift {u v : X} (hmu : r m.1.1 u) (hvu : Quotient.mk r v ⤳ Quotient.mk r u)
      (hvS : ∀ w : U₀, r w.1 v → w ∈ Ax ∪ Ay) : r m.1.1 v := by
    obtain ⟨w, hwm, hqw⟩ := hq_gen (a := m.1.1) (Quotient.sound hmu ▸ hvu)
    have hwv : r w v := Quotient.exact hqw
    have hwU₀ : w ∈ U₀ := hwm.mem_open hU₀o m.1.2
    have hwx_U₀ : (⟨w, hwU₀⟩ : U₀) ⤳ ⟨x, hxU₀⟩ :=
      IsEmbedding.subtypeVal.isInducing.specializes_iff.mp (hwm.trans hmx_sp)
    let z : S := ⟨⟨w, hwU₀⟩, hwx_U₀, hvS ⟨w, hwU₀⟩ hwv⟩
    have hzm : z ⤳ m :=
      IsEmbedding.subtypeVal.isInducing.specializes_iff.mp <|
        IsEmbedding.subtypeVal.isInducing.specializes_iff.mp hwm
    have hwm_eq : w = m.1.1 := congrArg (fun s : S ↦ s.1.1) (hmin z hzm)
    exact hwm_eq ▸ hwv
  rcases m.2.2 with hmx | hmy
  · exact Quotient.sound (r.trans (r.symm hmx) (hlift hmx hyx_sp fun _ h ↦ Or.inr h))
  · exact Quotient.sound (r.trans (r.symm (hlift hmy hxy_sp fun _ h ↦ Or.inl h)) hmy)

end LocallyProConstructible

/-! ### The spectral quotient criterion -/

/-- **The spectral quotient criterion (Scholze [ECD] Lemma 2.9).** Let `X` be a spectral space and
`r` an equivalence relation whose graph is pro-constructible in `X × X` and whose first projection
is generalizing. If the quotient topology on `Quotient r` admits a basis of open sets with compact
preimages in `X`, then `Quotient r` is spectral.

Under the same hypotheses, `Quotient.mk r` is spectral by
`TauCeti.isSpectralMap_of_isTopologicalBasis` and generalizing by
`TauCeti.generalizingMap_quotient_mk`. -/
theorem spectralSpace_quotient [SpectralSpace X] {r : Setoid X}
    (hR : IsProConstructible {q : X × X | r q.1 q.2})
    (hs : GeneralizingMap fun q : {q : X × X // r q.1 q.2} ↦ q.1.1)
    {B : Set (Set (Quotient r))} (hB : IsTopologicalBasis B)
    (hcomp : ∀ V ∈ B, IsCompact (Quotient.mk r ⁻¹' V)) :
    SpectralSpace (Quotient r) := by
  have hs_qc : IsSpectralMap fun q : {q : X × X // r q.1 q.2} ↦ q.1.1 :=
    isProperMap_fst_of_compactSpace.isSpectralMap.comp hR.isSpectralMap_subtypeVal
  have hT0 : T0Space (Quotient r) :=
    t0Space_quotient SpectralSpace.isLocallySpectralSpace hR.isLocallyProConstructible hs_qc hs
  have hgen := hB.eq_generateFrom
  have hclopen : ∀ V ∈ B, IsClopen[constructibleTopology X] (Quotient.mk r ⁻¹' V) :=
    fun V hVB ↦ (hcomp V hVB).isClopen_constructibleTopology_of_isOpen
      ((hB.isOpen hVB).preimage continuous_quotient_mk')
  let tOrig : TopologicalSpace (Quotient r) := inferInstance
  let t' : TopologicalSpace (Quotient r) :=
    TopologicalSpace.coinduced (Quotient.mk r) (constructibleTopology X)
  have hcont : @Continuous (WithConstructibleTopology X) (Quotient r) _ t'
      (Quotient.mk r ∘ WithTopology.ofTopology) :=
    @Continuous.comp (WithConstructibleTopology X) X (Quotient r) _ (constructibleTopology X) t'
      WithTopology.ofTopology (Quotient.mk r) continuous_coinduced_rng
      (WithTopology.continuous_ofTopology _)
  have hc : @CompactSpace (Quotient r) t' :=
    @Function.Surjective.compactSpace (WithConstructibleTopology X) (Quotient r) _ t'
      (Quotient.mk r ∘ WithTopology.ofTopology) hcont inferInstance
      (Quotient.mk_surjective.comp (WithTopology.ofTopology_surjective _))
  refine @spectralSpace_of_isClopen_generateFrom _ _ t' tOrig hgen hc ?_ hT0
  intro V hVB
  exact ⟨(@isClosed_coinduced X (Quotient r) (constructibleTopology X) V (Quotient.mk r)).mpr
      (hclopen V hVB).1,
    (@isOpen_coinduced X (Quotient r) (constructibleTopology X) V (Quotient.mk r)).mpr
      (hclopen V hVB).2⟩

/-! ### Quotients by open equivalence relations -/

/-- If `X` is prespectral and the first projection `R → X` is quasicompact and open, then
`Quotient.mk r` is a spectral map. On a quasiseparated space, `IsSpectralMap.isLocallySpectralMap`
then makes `Quotient.mk r` locally spectral. -/
theorem _root_.Setoid.isSpectralMap_quotient_mk_of_isOpenMap [PrespectralSpace X] (r : Setoid X)
    (hs_qc : IsSpectralMap fun q : {q : X × X // r q.1 q.2} ↦ q.1.1)
    (hs_open : IsOpenMap fun q : {q : X × X // r q.1 q.2} ↦ q.1.1) :
    IsSpectralMap (Quotient.mk r) := by
  have hq_open : IsOpenQuotientMap (Quotient.mk r) :=
    .of_isOpenMap_isQuotientMap (r.isOpenMap_quotient_mk_iff.mpr hs_open) isQuotientMap_quotient_mk'
  refine isSpectralMap_of_isTopologicalBasis
    (hq_open.isTopologicalBasis (PrespectralSpace.isTopologicalBasis (X := X)))
    continuous_quotient_mk' ?_
  rintro _ ⟨W, ⟨hWo, hWc⟩, rfl⟩
  rw [r.preimage_image_quotient_mk, ← r.image_snd_preimage_fst]
  exact (hs_qc.isCompact_preimage_of_isOpen hWo hWc).image
    (continuous_snd.comp continuous_subtype_val)

/-- If `X` is quasiseparated and prespectral and the first projection `R → X` is quasicompact and
open, then `Quotient r` is quasiseparated. -/
theorem _root_.Setoid.quasiSeparatedSpace_quotient_of_isOpenMap [PrespectralSpace X]
    [QuasiSeparatedSpace X] (r : Setoid X)
    (hs_qc : IsSpectralMap fun q : {q : X × X // r q.1 q.2} ↦ q.1.1)
    (hs_open : IsOpenMap fun q : {q : X × X // r q.1 q.2} ↦ q.1.1) :
    QuasiSeparatedSpace (Quotient r) :=
  (r.isSpectralMap_quotient_mk_of_isOpenMap hs_qc hs_open).quasiSeparatedSpace_of_surjective
    Quotient.mk_surjective

/-- **Scholze [ECD] Lemma 2.10.** Let `X` be quasiseparated and locally spectral, and let `r` be a
locally pro-constructible equivalence relation whose first projection `R → X` is quasicompact and
open. Then `Quotient r` is locally spectral. -/
theorem isLocallySpectralSpace_quotient_of_isOpenMap [QuasiSeparatedSpace X]
    (hX : IsLocallySpectralSpace X) {r : Setoid X}
    (hR : IsLocallyProConstructible {q : X × X | r q.1 q.2})
    (hs_qc : IsSpectralMap fun q : {q : X × X // r q.1 q.2} ↦ q.1.1)
    (hs_open : IsOpenMap fun q : {q : X × X // r q.1 q.2} ↦ q.1.1) :
    IsLocallySpectralSpace (Quotient r) := by
  have := hX.prespectralSpace
  have : QuasiSeparatedSpace (X × X) := QuasiSeparatedSpace.prod
  have hR_ls : IsLocallySpectralSpace {q : X × X // r q.1 q.2} :=
    hR.isLocallySpectralSpace (hX.prod hX)
  have : QuasiSeparatedSpace {q : X × X // r q.1 q.2} :=
    hR.quasiSeparatedSpace (hX.prod hX)
  have hs_gen : GeneralizingMap fun q : {q : X × X // r q.1 q.2} ↦ q.1.1 :=
    hs_qc.isLocallySpectralMap.generalizingMap_of_isOpenMap hR_ls hX hs_open
  have hq_open : IsOpenMap (Quotient.mk r) := r.isOpenMap_quotient_mk_iff.mpr hs_open
  have hq_oq : IsOpenQuotientMap (Quotient.mk r) :=
    .of_isOpenMap_isQuotientMap hq_open isQuotientMap_quotient_mk'
  have hq_spec : IsSpectralMap (Quotient.mk r) :=
    r.isSpectralMap_quotient_mk_of_isOpenMap hs_qc hs_open
  refine isLocallySpectralSpace_iff.mpr fun y ↦ ?_
  obtain ⟨x, rfl⟩ := Quotient.exists_rep y
  obtain ⟨W, hWo, hxW, hWs⟩ := isLocallySpectralSpace_iff.mp hX x
  have hWc : IsCompact W := isCompact_iff_compactSpace.mpr hWs.toCompactSpace
  let V : Set (Quotient r) := Quotient.mk r '' W
  have hVo : IsOpen V := hq_open W hWo
  have hVc : IsCompact V := hWc.image continuous_quotient_mk'
  refine ⟨V, hVo, ⟨x, hxW, rfl⟩, ?_⟩
  -- Pull back to the saturated compact open `U = q ⁻¹' V`, which is spectral, and identify `V`
  -- with the quotient of `U` by the restricted relation `r.comap Subtype.val`.
  let U : Set X := Quotient.mk r ⁻¹' V
  have hUo : IsOpen U := hVo.preimage continuous_quotient_mk'
  have hUc : IsCompact U := hq_spec.isCompact_preimage_of_isOpen hVo hVc
  have : SpectralSpace U := hX.spectralSpace_of_isOpen_of_isCompact hUo hUc
  let rU : Setoid U := Setoid.comap Subtype.val r
  let g : Quotient rU → Quotient r :=
    Quotient.lift (fun u : U ↦ Quotient.mk r u.1) fun _ _ h ↦ Quotient.sound h
  have hg_inj : Function.Injective g := fun a b hab ↦
    Quotient.inductionOn₂ a b
      (fun _ _ h ↦ Quotient.sound (s := rU) (Quotient.exact (s := r) h)) hab
  have hg_range : range g = V := by
    ext z
    constructor
    · rintro ⟨a, rfl⟩
      exact Quotient.inductionOn a fun u ↦ u.2
    · intro hzV
      obtain ⟨u, rfl⟩ := Quotient.exists_rep z
      exact ⟨Quotient.mk rU ⟨u, hzV⟩, rfl⟩
  have hg_emb : IsEmbedding g :=
    isEmbedding_of_isOpenQuotientMap_of_isInducing Subtype.val g (Quotient.mk rU) (Quotient.mk r)
      rfl IsEmbedding.subtypeVal.isInducing isQuotientMap_quotient_mk' hq_oq hg_inj <| by
        rintro z ⟨_, ⟨u, rfl⟩, hzu⟩
        refine ⟨⟨z, ?_⟩, rfl⟩
        rw [mem_preimage, ← hzu]
        exact u.2
  have hRU_pc : IsProConstructible {q : U × U | rU q.1 q.2} := by
    let e : U × U ≃ₜ (U ×ˢ U : Set (X × X)) := (Homeomorph.Set.prod U U).symm
    have : CompactSpace (U ×ˢ U : Set (X × X)) := e.compactSpace
    have : SpectralSpace (U ×ˢ U : Set (X × X)) := e.symm.isOpenEmbedding.spectralSpace
    have htrace := hR.isProConstructible_preimage (hUo.prod hUo)
    convert htrace.preimage e.isProperMap.isSpectralMap using 1
    ext q
    rfl
  have hsU_gen : GeneralizingMap fun q : {q : U × U // rU q.1 q.2} ↦ q.1.1 := by
    intro q u' hu'
    have hu'_sp : u'.1 ⤳ q.1.1.1 := hu'.map continuous_subtype_val
    obtain ⟨p, hp_sp, hp1⟩ := hs_gen (a := ⟨(q.1.1.1, q.1.2.1), q.2⟩) hu'_sp
    have hp1' : p.1.1 = u'.1 := hp1
    have hp2U : p.1.2 ∈ U :=
      (hp_sp.map (continuous_snd.comp continuous_subtype_val)).mem_open hUo q.1.2.2
    have hrp : r u'.1 p.1.2 := hp1' ▸ p.2
    refine ⟨⟨(u', ⟨p.1.2, hp2U⟩), hrp⟩, ?_, rfl⟩
    refine IsEmbedding.subtypeVal.isInducing.specializes_iff.mp ?_
    have h1 : u' ⤳ q.1.1 :=
      IsEmbedding.subtypeVal.isInducing.specializes_iff.mp <|
        hp1' ▸ hp_sp.map (continuous_fst.comp continuous_subtype_val)
    have h2 : (⟨p.1.2, hp2U⟩ : U) ⤳ q.1.2 :=
      IsEmbedding.subtypeVal.isInducing.specializes_iff.mp <|
        hp_sp.map (continuous_snd.comp continuous_subtype_val)
    exact specializes_prod.2 ⟨h1, h2⟩
  have hqU_open : IsOpenMap (Quotient.mk rU) := fun O hOo ↦ by
    have hpre : g ⁻¹' (Quotient.mk r '' (Subtype.val '' O)) = Quotient.mk rU '' O := by
      ext a
      refine Quotient.inductionOn a fun u ↦ ?_
      constructor
      · rintro ⟨_, ⟨v, hvO, rfl⟩, hvu⟩
        exact ⟨v, hvO, Quotient.sound (s := rU) (Quotient.exact (s := r) hvu)⟩
      · rintro ⟨v, hvO, hvu⟩
        exact ⟨v.1, ⟨v, hvO, rfl⟩, Quotient.sound (s := r) (Quotient.exact (s := rU) hvu)⟩
    rw [← hpre]
    exact (hq_open _ (hUo.isOpenMap_subtype_val O hOo)).preimage hg_emb.continuous
  have hqU_oq : IsOpenQuotientMap (Quotient.mk rU) :=
    .of_isOpenMap_isQuotientMap hqU_open isQuotientMap_quotient_mk'
  have : SpectralSpace (Quotient rU) := by
    refine spectralSpace_quotient hRU_pc hsU_gen
      (hqU_oq.isTopologicalBasis (PrespectralSpace.isTopologicalBasis (X := U))) ?_
    rintro _ ⟨O, ⟨hOo, hOc⟩, rfl⟩
    rw [IsEmbedding.subtypeVal.isCompact_iff]
    have himg : Subtype.val '' (Quotient.mk rU ⁻¹' (Quotient.mk rU '' O)) =
        Quotient.mk r ⁻¹' (Quotient.mk r '' (Subtype.val '' O)) := by
      ext z
      constructor
      · rintro ⟨u, ⟨v, hvO, hvu⟩, rfl⟩
        exact ⟨v.1, ⟨v, hvO, rfl⟩, Quotient.sound (s := r) (Quotient.exact (s := rU) hvu)⟩
      · rintro ⟨_, ⟨v, hvO, rfl⟩, hvz⟩
        have hzU : z ∈ U := by
          rw [mem_preimage, ← hvz]
          exact v.2
        exact ⟨⟨z, hzU⟩,
          ⟨v, hvO, Quotient.sound (s := rU) (Quotient.exact (s := r) hvz)⟩, rfl⟩
    rw [himg]
    exact hq_spec.isCompact_preimage_of_isOpen (hq_open _ (hUo.isOpenMap_subtype_val O hOo))
      ((hOc.image continuous_subtype_val).image continuous_quotient_mk')
  have hpreV : g ⁻¹' V = univ := by
    rw [← hg_range]
    exact preimage_range g
  refine (hg_emb.spectralSpace_preimage_iff (S := V) (by rw [hg_range])).mp ?_
  rw [hpreV]
  exact spectralSpace_univ

/-- The quotient of a spectral space by a pro-constructible equivalence relation whose first
projection is open is spectral. -/
theorem spectralSpace_quotient_of_isOpenMap [SpectralSpace X] {r : Setoid X}
    (hR : IsProConstructible {q : X × X | r q.1 q.2})
    (hs_open : IsOpenMap fun q : {q : X × X // r q.1 q.2} ↦ q.1.1) :
    SpectralSpace (Quotient r) := by
  have hs_qc : IsSpectralMap fun q : {q : X × X // r q.1 q.2} ↦ q.1.1 :=
    isProperMap_fst_of_compactSpace.isSpectralMap.comp hR.isSpectralMap_subtypeVal
  exact spectralSpace_iff_isLocallySpectralSpace.mpr
    ⟨isLocallySpectralSpace_quotient_of_isOpenMap SpectralSpace.isLocallySpectralSpace
      hR.isLocallyProConstructible hs_qc hs_open,
      inferInstance,
      r.quasiSeparatedSpace_quotient_of_isOpenMap hs_qc hs_open⟩

end TauCeti

end
