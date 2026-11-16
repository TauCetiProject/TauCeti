/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Spectral.LocallyProConstructible
import Mathlib.Topology.Maps.OpenQuotient
import TauCeti.Topology.Constructions.Basic
import TauCeti.Topology.Spectral.PatchCriterion

/-!
# Quotients of spectral and locally spectral spaces

Criteria for the quotient of a spectral or locally spectral space by a pro-constructible
equivalence relation to be T₀, locally spectral, or spectral.

For a `Setoid` `r` on a topological space `X`, swapping coordinates restricts to a
self-homeomorphism `r.graphSwap` of the graph `R = {q : X × X // r q.1 q.2}` intertwining the two
projections `s, t : R → X` (see `TauCeti.Topology.Constructions.Basic` for `Setoid.graphSwap`,
`Setoid.isOpenMap_fst_iff_snd`, `Setoid.generalizingMap_fst_iff_snd`, and
`Setoid.isOpenMap_quotient_mk_iff`). Thus hypotheses such as being generalizing, spectral
(quasicompact), or open need only be assumed for the first projection `s`.

When `X` is quasiseparated and locally spectral and `R` is locally pro-constructible with
quasicompact generalizing first projection `s`:

* every open subset `W` whose `r`-saturation lies in an open set `W'` admits an `r`-invariant
  open neighbourhood `U` with `W ⊆ U ⊆ W'` — and for compact open `W`, `U` lies inside an
  `r`-invariant intersection of a nonempty family of compact opens;
* `Quotient.mk r` is generalizing;
* `Quotient r` is T₀.

If `X` is spectral, `R` is pro-constructible with generalizing first projection, and `Quotient r`
admits a basis of opens with compact preimages in `X`, then `Quotient r` is spectral and
`Quotient.mk r` is spectral and generalizing — proved via the patch criterion using the coinduced
constructible topology as the compact witness.

Finally, when `s : R → X` is open and quasicompact on a quasiseparated locally spectral space
with locally pro-constructible `R`, the generalizing hypothesis holds automatically, `Quotient.mk r`
is open and spectral, and `Quotient r` is quasiseparated and locally spectral (and spectral when
`X` is spectral).

## Main results

* `Setoid.isSpectralMap_fst_iff_snd`: symmetry of quasicompactness for the two projections
  `R → X` of an equivalence relation.
* `Setoid.isCompact_saturation`: the `r`-saturation of a compact open is compact when the first
  projection is spectral.
* `TauCeti.exists_isOpen_saturated_subset` and `TauCeti.exists_isOpen_saturated_subset_sInter`:
  invariant open neighbourhoods for locally pro-constructible equivalence relations.
* `TauCeti.generalizingMap_quotient_mk` and `TauCeti.t0Space_quotient`: the quotient map is
  generalizing and the quotient space is T₀.
* `TauCeti.spectralSpace_quotient`: the spectral quotient criterion.
* `Setoid.isSpectralMap_quotient_mk_of_isOpenMap`,
  `Setoid.quasiSeparatedSpace_quotient_of_isOpenMap`,
  `TauCeti.IsLocallyProConstructible.isProConstructible_comap_subtypeVal`,
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

/-! ### Symmetry and saturation for equivalence-relation projections -/

/-- By symmetry of `r`, the first projection `R → X` is spectral if and only if the second
projection is spectral. -/
theorem _root_.Setoid.isSpectralMap_fst_iff_snd (r : Setoid X) :
    IsSpectralMap (fun q : {q : X × X // r q.1 q.2} ↦ q.1.1) ↔
      IsSpectralMap (fun q : {q : X × X // r q.1 q.2} ↦ q.1.2) :=
  ⟨fun h ↦ r.fst_comp_graphSwap ▸ h.comp r.graphSwap.isProperMap.isSpectralMap,
    fun h ↦ r.snd_comp_graphSwap ▸ h.comp r.graphSwap.isProperMap.isSpectralMap⟩

/-- If the first projection from the graph of `r` is spectral (quasicompact), then the
`r`-saturation of a compact open subset is compact. -/
theorem _root_.Setoid.isCompact_saturation (r : Setoid X)
    (hs_qc : IsSpectralMap fun q : {q : X × X // r q.1 q.2} ↦ q.1.1)
    {W : Set X} (hWo : IsOpen W) (hWc : IsCompact W) :
    IsCompact {y | ∃ x ∈ W, r x y} := by
  rw [← r.image_snd_preimage_fst]
  exact (hs_qc.isCompact_preimage_of_isOpen hWo hWc).image
    (continuous_snd.comp continuous_subtype_val)

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
  have hR_ls : IsLocallySpectralSpace {q : X × X // r q.1 q.2} :=
    hR.isLocallySpectralSpace (hX.prod hX)
  have : QuasiSeparatedSpace {q : X × X // r q.1 q.2} :=
    hR.quasiSeparatedSpace (hX.prod hX)
  have ht_qc : IsSpectralMap fun q : {q : X × X // r q.1 q.2} ↦ q.1.2 :=
    r.isSpectralMap_fst_iff_snd.mp hs_qc
  let F : Set X := {y | ∃ x ∈ W'ᶜ, r x y}
  have hF_lpc : IsLocallyProConstructible F := by
    dsimp only [F]
    rw [← r.image_snd_preimage_fst]
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
  have hEc : IsCompact {y | ∃ x ∈ W, r x y} := r.isCompact_saturation hs_qc hWo hWc
  obtain ⟨W', hW'c, hW'o, hEW', -⟩ :=
    PrespectralSpace.exists_isCompact_and_isOpen_between hEc isOpen_univ (subset_univ _)
  obtain ⟨U, hUo, hUinv, hWU, hUW'⟩ :=
    exists_isOpen_saturated_subset hX hR hs_qc hs_gen hWo hW'o hEW'
  let E' : Set X := {y | ∃ x ∈ W', r x y}
  have hE'c : IsCompact E' := r.isCompact_saturation hs_qc hW'o hW'c
  have hE'gen : StableUnderGeneralization E' :=
    r.stableUnderGeneralization_saturation hs_gen hW'o.stableUnderGeneralization
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
  intro x b hb
  obtain ⟨y, rfl⟩ := Quotient.exists_rep b
  -- Show `x ∈ closure {z | r z y}` by testing against compact open neighbourhoods `W ∋ x`.
  have hxcl : x ∈ closure {z : X | r z y} := by
    refine PrespectralSpace.isTopologicalBasis.mem_closure_iff.mpr ?_
    rintro W ⟨hWo, hWc⟩ hxW
    let E : Set X := {w | ∃ u ∈ W, r u w}
    have hEc : IsCompact E := r.isCompact_saturation hs_qc hWo hWc
    have hEgen : StableUnderGeneralization E :=
      r.stableUnderGeneralization_saturation hs_gen hWo.stableUnderGeneralization
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
  have hmin : ∀ z : S, z ⤳ m → z = m := mem_genericPoints_iff.mp (genericPoints.ofComponent C).2
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
preimages in `X`, then `Quotient r` is spectral and `Quotient.mk r` is spectral and generalizing. -/
theorem spectralSpace_quotient [SpectralSpace X] {r : Setoid X}
    (hR : IsProConstructible {q : X × X | r q.1 q.2})
    (hs : GeneralizingMap fun q : {q : X × X // r q.1 q.2} ↦ q.1.1)
    {B : Set (Set (Quotient r))} (hB : IsTopologicalBasis B)
    (hcomp : ∀ V ∈ B, IsCompact (Quotient.mk r ⁻¹' V)) :
    SpectralSpace (Quotient r) ∧ IsSpectralMap (Quotient.mk r) ∧
      GeneralizingMap (Quotient.mk r) := by
  have hs_qc : IsSpectralMap fun q : {q : X × X // r q.1 q.2} ↦ q.1.1 := hR.isSpectralMap_fst
  have hspec : SpectralSpace (Quotient r) := by
    have hT0 : T0Space (Quotient r) :=
      t0Space_quotient SpectralSpace.isLocallySpectralSpace hR.isLocallyProConstructible hs_qc hs
    have hclopen : ∀ V ∈ B, IsClopen[constructibleTopology X] (Quotient.mk r ⁻¹' V) :=
      fun V hVB ↦ (hcomp V hVB).isClopen_constructibleTopology_of_isOpen
        ((hB.isOpen hVB).preimage continuous_quotient_mk')
    have hgen := hB.eq_generateFrom
    let tOrig : TopologicalSpace (Quotient r) := inferInstance
    let t' : TopologicalSpace (Quotient r) :=
      TopologicalSpace.coinduced (Quotient.mk r) (constructibleTopology X)
    have hc : @CompactSpace (Quotient r) t' :=
      @Function.Surjective.compactSpace X (Quotient r) (constructibleTopology X) t'
        (Quotient.mk r) continuous_coinduced_rng compactSpace_constructibleTopology
        Quotient.mk_surjective
    refine @spectralSpace_of_isClopen_generateFrom _ _ t' tOrig hgen hc ?_ hT0
    intro V hVB
    exact ⟨(@isClosed_coinduced X (Quotient r) (constructibleTopology X) V (Quotient.mk r)).mpr
        (hclopen V hVB).1,
      (@isOpen_coinduced X (Quotient r) (constructibleTopology X) V (Quotient.mk r)).mpr
        (hclopen V hVB).2⟩
  exact ⟨hspec, isSpectralMap_of_isTopologicalBasis hB continuous_quotient_mk' hcomp,
    generalizingMap_quotient_mk SpectralSpace.isLocallySpectralSpace
      hR.isLocallyProConstructible hs_qc hs⟩

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
  rw [r.preimage_image_quotient_mk]
  exact r.isCompact_saturation hs_qc hWo hWc

/-- If `X` is quasiseparated and prespectral and the first projection `R → X` is quasicompact and
open, then `Quotient r` is quasiseparated. -/
theorem _root_.Setoid.quasiSeparatedSpace_quotient_of_isOpenMap [PrespectralSpace X]
    [QuasiSeparatedSpace X] (r : Setoid X)
    (hs_qc : IsSpectralMap fun q : {q : X × X // r q.1 q.2} ↦ q.1.1)
    (hs_open : IsOpenMap fun q : {q : X × X // r q.1 q.2} ↦ q.1.1) :
    QuasiSeparatedSpace (Quotient r) :=
  (r.isSpectralMap_quotient_mk_of_isOpenMap hs_qc hs_open).quasiSeparatedSpace_of_surjective
    Quotient.mk_surjective

/-- Restricting a locally pro-constructible equivalence relation to a spectral open subset gives a
pro-constructible graph. -/
theorem IsLocallyProConstructible.isProConstructible_comap_subtypeVal {r : Setoid X}
    (hR : IsLocallyProConstructible {q : X × X | r q.1 q.2})
    {U : Set X} (hUo : IsOpen U) [SpectralSpace U] :
    IsProConstructible {q : U × U | (r.comap Subtype.val) q.1 q.2} := by
  have h := isLocallyProConstructible_iff_isProConstructible.mp <|
    hR.preimage_of_isOpenEmbedding
      (hUo.isOpenEmbedding_subtypeVal.prodMap hUo.isOpenEmbedding_subtypeVal)
  convert h using 1
  ext ⟨u₁, u₂⟩
  simp [Setoid.comap_rel]

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
  have hR_ls : IsLocallySpectralSpace {q : X × X // r q.1 q.2} :=
    hR.isLocallySpectralSpace (hX.prod hX)
  have : QuasiSeparatedSpace {q : X × X // r q.1 q.2} :=
    hR.quasiSeparatedSpace (hX.prod hX)
  have hs_gen : GeneralizingMap fun q : {q : X × X // r q.1 q.2} ↦ q.1.1 :=
    hs_qc.isLocallySpectralMap.generalizingMap_of_isOpenMap hR_ls hX hs_open
  have hq_open : IsOpenMap (Quotient.mk r) := r.isOpenMap_quotient_mk_iff.mpr hs_open
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
  have hUsat : ∀ ⦃a b⦄, a ∈ U → r a b → b ∈ U := fun _ _ ha hab ↦
    show Quotient.mk r _ ∈ V from Quotient.sound hab ▸ ha
  have : SpectralSpace U := hX.spectralSpace_of_isOpen_of_isCompact hUo hUc
  let rU : Setoid U := r.comap Subtype.val
  let g : Quotient rU → Quotient r := Quotient.map' (Subtype.val : U → X) fun _ _ h ↦ h
  have hg_range : range g = V :=
    (r.range_quotient_map'_subtypeVal U).trans (image_preimage_eq V Quotient.mk_surjective)
  have hg_emb : IsEmbedding g := r.isEmbedding_quotient_map'_subtypeVal hq_open hUsat
  have hqU_oq : IsOpenQuotientMap (Quotient.mk rU) :=
    .of_isOpenMap_isQuotientMap (r.isOpenMap_quotient_mk_comap_subtypeVal hq_open hUo)
      isQuotientMap_quotient_mk'
  have : SpectralSpace (Quotient rU) :=
    (spectralSpace_quotient (hR.isProConstructible_comap_subtypeVal hUo)
      (r.generalizingMap_fst_comap_subtypeVal hs_gen hUo)
      (hqU_oq.isTopologicalBasis (PrespectralSpace.isTopologicalBasis (X := U))) fun _ hO ↦ by
        obtain ⟨O, ⟨hOo, hOc⟩, rfl⟩ := hO
        rw [IsEmbedding.subtypeVal.isCompact_iff,
          r.image_subtypeVal_preimage_image_quotient_mk_comap hUsat O]
        exact hq_spec.isCompact_preimage_of_isOpen (hq_open _ (hUo.isOpenMap_subtype_val O hOo))
          ((hOc.image continuous_subtype_val).image continuous_quotient_mk')).1
  refine (hg_emb.spectralSpace_preimage_iff (S := V) (by rw [hg_range])).mp ?_
  rw [← hg_range, preimage_range]
  exact spectralSpace_univ

/-- The quotient of a spectral space by a pro-constructible equivalence relation whose first
projection is open is spectral. -/
theorem spectralSpace_quotient_of_isOpenMap [SpectralSpace X] {r : Setoid X}
    (hR : IsProConstructible {q : X × X | r q.1 q.2})
    (hs_open : IsOpenMap fun q : {q : X × X // r q.1 q.2} ↦ q.1.1) :
    SpectralSpace (Quotient r) :=
  spectralSpace_iff_isLocallySpectralSpace.mpr
    ⟨isLocallySpectralSpace_quotient_of_isOpenMap SpectralSpace.isLocallySpectralSpace
      hR.isLocallyProConstructible hR.isSpectralMap_fst hs_open,
      inferInstance,
      r.quasiSeparatedSpace_quotient_of_isOpenMap hR.isSpectralMap_fst hs_open⟩

end TauCeti

end
