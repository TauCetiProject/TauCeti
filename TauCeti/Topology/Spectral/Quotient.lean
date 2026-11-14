/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Spectral.LocallyProConstructible
public import TauCeti.Topology.Spectral.Limits.Basic
import TauCeti.Topology.Sober
import Mathlib.Topology.ContinuousMap.Basic
import Mathlib.Topology.Homeomorph.Quotient
import Mathlib.Topology.WithTopology

/-!
# Quotients of spectral and locally spectral spaces

Let `X` be a locally spectral space and `r : Setoid X` an equivalence relation whose graph
`R = {q : X × X | r q.1 q.2}` is locally pro-constructible and whose projections `R → X` are
quasi-compact (`IsSpectralMap`) and lift generalizations (`GeneralizingMap`). Symmetry of `r`
interchanges the two projections by a homeomorphism of `R`, so each topological hypothesis need
only be assumed on the first projection `q ↦ q.1.1`.

Under these hypotheses:
* The `r`-saturation of any locally pro-constructible subset of `X` is locally pro-constructible,
  and its closure remains `r`-saturated; hence images of closures of saturated locally
  pro-constructible subsets are closed in `Quotient r`.
* The quotient projection `Quotient.mk r` lifts generalizations
  (`TauCeti.generalizingMap_quotientMk`) and `Quotient r` is a T₀ space
  (`TauCeti.t0Space_quotient`).
* Every compact open `W ⊆ X` is contained in an `r`-saturated open subset `Quotient.mk r ⁻¹' V`
  inside `E' = ⋂₀ 𝒮`, where `𝒮` is a nonempty family of compact open subsets whose intersection is
  `r`-saturated (`TauCeti.exists_isOpen_quotientMk_preimage_subset_sInter`). One cannot ask for
  `Quotient.mk r ⁻¹' V` to lie inside the saturation `E` of `W` itself, because `E` need not be
  open; instead one encloses `E` in a compact open `W'`, removes the closure of the saturation of
  `W'ᶜ`, and sets `E'` to be the saturation of `W'`.

These hypotheses alone do not make `Quotient r` spectral: every compact Hausdorff space arises as
such a quotient of the Stone–Čech compactification of its underlying discrete set. Adding a
topological basis of `Quotient r` with compact preimages under `Quotient.mk r` yields spectrality
of `Quotient r` (`TauCeti.spectralSpace_quotient`) via the patch criterion applied to the quotient
of the constructible topology of `X`, while `TauCeti.isSpectralMap_of_isTopologicalBasis` gives
spectrality of `Quotient.mk r`.

In geometric applications, the basis hypothesis is supplied by openness of `q ↦ q.1.1`: on a
quasiseparated locally spectral space `X`, if `R` is locally pro-constructible and the projection
`q ↦ q.1.1` is open and quasi-compact, then `Quotient.mk r` is open, spectral, and locally
spectral, and `Quotient r` is quasiseparated and locally spectral
(`TauCeti.isLocallySpectralSpace_quotient_of_isOpenMap`).

## Main results

* `TauCeti.generalizingMap_fst_setoid_iff`, `TauCeti.isSpectralMap_fst_setoid_iff`,
  `TauCeti.isOpenMap_fst_setoid_iff`: symmetry equivalences between the two projections of a
  setoid graph.
* `IsOpenMap.quotientMk`, `IsOpen.isOpenMap_fst_setoid_comap`, `IsOpen.quotientComapHomeomorph`:
  openness of `Quotient.mk r`, open restriction of setoid projections, and the quotient
  homeomorphism on saturated open preimages.
* `TauCeti.IsLocallyProConstructible.preimage_image_quotientMk`: `r`-saturations preserve local
  pro-constructibility.
* `TauCeti.generalizingMap_quotientMk`, `TauCeti.t0Space_quotient`: generalization lifting for
  `Quotient.mk r` and T₀ separation of `Quotient r` (Scholze, Lemma 2.7(i)).
* `TauCeti.exists_isOpen_quotientMk_preimage_subset_of_subset`,
  `TauCeti.exists_isOpen_quotientMk_preimage_subset_sInter`: saturated open neighbourhoods inside
  saturated intersections of compact opens (Scholze, Lemma 2.7(ii)).
* `TauCeti.spectralSpace_quotient`: basis criterion for spectrality of `Quotient r` (Scholze,
  Lemma 2.9).
* `TauCeti.isSpectralMap_quotientMk_of_isOpenMap`,
  `TauCeti.isLocallySpectralMap_quotientMk_of_isOpenMap`,
  `TauCeti.quasiSeparatedSpace_quotient_of_isOpenMap`,
  `TauCeti.IsProConstructible.spectralSpace_quotient_of_isOpenMap`,
  `TauCeti.isLocallySpectralSpace_quotient_of_isOpenMap`: spectrality and local spectrality of
  quotients with open projections (Scholze, Lemma 2.10).

## References

* P. Scholze, *Étale cohomology of diamonds*, arXiv:1709.07343, §2, Lemmas 2.7, 2.9, and 2.10, and
  Remark 2.8.
* [Stacks Project, Tags 0APA and 0APB](https://stacks.math.columbia.edu/tag/0APA), for the
  scheme-theoretic counterpart of the invariant-neighbourhood argument.
-/

public section

open Set Topology TopologicalSpace

namespace TauCeti

variable {X : Type*} [TopologicalSpace X] {r : Setoid X}

/-! ### Symmetry of setoid projections, saturations, and open restrictions -/

/-- Coordinate swap on `X × X` restricts to an involutive homeomorphism of the graph of any
equivalence relation `r`. -/
private def setoidSwapHomeomorph (r : Setoid X) :
    {q : X × X | r q.1 q.2} ≃ₜ {q : X × X | r q.1 q.2} :=
  (Homeomorph.prodComm X X).subtype fun _ ↦ ⟨fun h ↦ r.symm h, fun h ↦ r.symm h⟩

/-- For a setoid `r` on `X`, the first projection of `{q : X × X | r q.1 q.2}` lifts
generalizations if and only if the second projection does. -/
theorem generalizingMap_fst_setoid_iff :
    GeneralizingMap (fun q : {q : X × X | r q.1 q.2} ↦ q.1.1) ↔
      GeneralizingMap (fun q : {q : X × X | r q.1 q.2} ↦ q.1.2) := by
  let e := setoidSwapHomeomorph r
  refine ⟨fun hs q x' hx' ↦ ?_, fun ht q x' hx' ↦ ?_⟩
  · obtain ⟨p, hp, hfp⟩ := @hs (e q) x' hx'
    exact ⟨e p, hp.map e.continuous, hfp⟩
  · obtain ⟨p, hp, hfp⟩ := @ht (e q) x' hx'
    exact ⟨e p, hp.map e.continuous, hfp⟩

/-- For a setoid `r` on `X`, the first projection of `{q : X × X | r q.1 q.2}` is a spectral map
if and only if the second projection is. -/
theorem isSpectralMap_fst_setoid_iff :
    IsSpectralMap (fun q : {q : X × X | r q.1 q.2} ↦ q.1.1) ↔
      IsSpectralMap (fun q : {q : X × X | r q.1 q.2} ↦ q.1.2) :=
  ⟨fun hs ↦ hs.comp (setoidSwapHomeomorph r).isProperMap.isSpectralMap,
    fun ht ↦ ht.comp (setoidSwapHomeomorph r).isProperMap.isSpectralMap⟩

/-- For a setoid `r` on `X`, the first projection of `{q : X × X | r q.1 q.2}` is an open map if
and only if the second projection is. -/
theorem isOpenMap_fst_setoid_iff :
    IsOpenMap (fun q : {q : X × X | r q.1 q.2} ↦ q.1.1) ↔
      IsOpenMap (fun q : {q : X × X | r q.1 q.2} ↦ q.1.2) :=
  ⟨fun hs ↦ hs.comp (setoidSwapHomeomorph r).isOpenMap,
    fun ht ↦ ht.comp (setoidSwapHomeomorph r).isOpenMap⟩

omit [TopologicalSpace X] in
/-- The `r`-saturation `Quotient.mk r ⁻¹' (Quotient.mk r '' s)` of a subset `s ⊆ X` is obtained
by pulling `s` back along the second projection of `{q : X × X | r q.1 q.2}` and taking its image
under the first projection. -/
theorem preimage_image_quotientMk_eq {s : Set X} :
    Quotient.mk r ⁻¹' (Quotient.mk r '' s) =
      (fun q : {q : X × X | r q.1 q.2} ↦ q.1.1) ''
        ((fun q : {q : X × X | r q.1 q.2} ↦ q.1.2) ⁻¹' s) := by
  ext x
  simp only [mem_preimage, mem_image, Quotient.eq, Subtype.exists, Prod.exists, mem_ofPred_eq]
  exact ⟨fun ⟨y, hys, hyx⟩ ↦ ⟨x, y, r.symm hyx, hys, rfl⟩,
    fun ⟨_, y, hxy, hys, rfl⟩ ↦ ⟨y, hys, r.symm hxy⟩⟩

/-- If the first projection of `{q : X × X | r q.1 q.2}` is an open map, then the quotient map
`Quotient.mk r : X → Quotient r` is an open map. -/
theorem _root_.IsOpenMap.quotientMk
    (hs : IsOpenMap (fun q : {q : X × X | r q.1 q.2} ↦ q.1.1)) :
    IsOpenMap (Quotient.mk r) := by
  have hq : IsQuotientMap (Quotient.mk r) := isQuotientMap_quot_mk
  intro U hUo
  rw [← hq.isOpen_preimage, preimage_image_quotientMk_eq]
  exact hs _ (hUo.preimage (continuous_snd.comp continuous_subtype_val))

/-- Restricting a setoid `r` to an open subset `U ⊆ X` preserves openness of the first projection
of its graph. -/
theorem _root_.IsOpen.isOpenMap_fst_setoid_comap {U : Set X} (hU : IsOpen U)
    (hs : IsOpenMap (fun q : {q : X × X | r q.1 q.2} ↦ q.1.1)) :
    IsOpenMap (fun q : {q : U × U | (r.comap Subtype.val) q.1 q.2} ↦ q.1.1) := by
  let ι : {q : U × U | (r.comap Subtype.val) q.1 q.2} → {q : X × X | r q.1 q.2} :=
    fun q ↦ ⟨(q.1.1.1, q.1.2.1), q.2⟩
  have hι_emb : IsEmbedding ι :=
    IsEmbedding.subtypeVal.of_comp_iff.mp
      ((hU.isOpenEmbedding_subtypeVal.prodMap
        hU.isOpenEmbedding_subtypeVal).isEmbedding.comp IsEmbedding.subtypeVal)
  have hι_rng : Set.range ι = Subtype.val ⁻¹' (U ×ˢ U) := by
    ext ⟨⟨x, y⟩, hxy⟩
    exact ⟨fun ⟨q, hq⟩ ↦ by cases hq; exact ⟨q.1.1.2, q.1.2.2⟩,
      fun ⟨hx, hy⟩ ↦ ⟨⟨(⟨x, hx⟩, ⟨y, hy⟩), hxy⟩, rfl⟩⟩
  have hι : IsOpenEmbedding ι :=
    ⟨hι_emb, hι_rng ▸ (hU.prod hU).preimage continuous_subtype_val⟩
  exact hU.isOpenEmbedding_subtypeVal.isOpenMap_iff.mpr (hs.comp hι.isOpenMap)

/-- For an open subset `V` of `Quotient r`, the quotient of the saturated open preimage
`Quotient.mk r ⁻¹' V` by the induced setoid `r.comap Subtype.val` is canonically homeomorphic to
`V`. -/
noncomputable def _root_.IsOpen.quotientComapHomeomorph {V : Set (Quotient r)} (hV : IsOpen V) :
    Quotient (r.comap (Subtype.val : Quotient.mk r ⁻¹' V → X)) ≃ₜ V :=
  let g : C(Quotient.mk r ⁻¹' V, V) :=
    ⟨V.restrictPreimage (Quotient.mk r), continuous_quot_mk.restrictPreimage⟩
  have hg : IsQuotientMap g := (isQuotientMap_quot_mk (r := r.r)).restrictPreimage_isOpen hV
  (Homeomorph.Quotient.congrRight (r := r.comap Subtype.val) (r' := Setoid.ker g) fun _ _ ↦
    ⟨fun h ↦ Setoid.ker_def.mpr (Subtype.ext (Quotient.sound h)),
      fun h ↦ Quotient.exact (s := r) (congrArg Subtype.val (Setoid.ker_def.mp h))⟩).trans
    hg.homeomorph

/-! ### Locally pro-constructible equivalence relations -/

/-- Along a locally pro-constructible equivalence relation on a locally spectral space with
quasi-compact projections, the `r`-saturation of any locally pro-constructible subset is locally
pro-constructible. -/
theorem IsLocallyProConstructible.preimage_image_quotientMk {s : Set X}
    (hs : IsLocallyProConstructible s) (hX : IsLocallySpectralSpace X)
    (hR : IsLocallyProConstructible {q : X × X | r q.1 q.2})
    (hs_qc : IsSpectralMap (fun q : {q : X × X | r q.1 q.2} ↦ q.1.1)) :
    IsLocallyProConstructible (Quotient.mk r ⁻¹' (Quotient.mk r '' s)) := by
  have hXX : IsLocallySpectralSpace (X × X) := hX.prod hX
  have hR_ls : IsLocallySpectralSpace {q : X × X | r q.1 q.2} := hR.isLocallySpectralSpace hXX
  have hsub : IsLocallySpectralMap ((↑) : {q : X × X | r q.1 q.2} → X × X) :=
    hR.isLocallySpectralMap_subtypeVal hXX
  have hfst : IsLocallySpectralMap (fun q : {q : X × X | r q.1 q.2} ↦ q.1.1) :=
    IsLocallySpectralMap.comp hXX (hX.isLocallySpectralMap_fst hX) hsub
  have hsnd : IsLocallySpectralMap (fun q : {q : X × X | r q.1 q.2} ↦ q.1.2) :=
    IsLocallySpectralMap.comp hXX (hX.isLocallySpectralMap_snd hX) hsub
  rw [preimage_image_quotientMk_eq]
  exact (hs.preimage hX hsnd).image hR_ls hfst hs_qc

/-- If `s ⊆ X` is locally pro-constructible and `r`-saturated on a locally spectral space `X`,
and the first projection of `{q : X × X | r q.1 q.2}` lifts generalizations, then `closure s` is
also `r`-saturated. -/
theorem IsLocallyProConstructible.preimage_image_quotientMk_closure_eq {s : Set X}
    (hs : IsLocallyProConstructible s) (hX : IsLocallySpectralSpace X)
    (hs_gen : GeneralizingMap (fun q : {q : X × X | r q.1 q.2} ↦ q.1.1))
    (hs_sat : ∀ ⦃x y : X⦄, r x y → x ∈ s → y ∈ s) :
    Quotient.mk r ⁻¹' (Quotient.mk r '' closure s) = closure s := by
  refine Subset.antisymm (fun y hy ↦ ?_) (subset_preimage_image _ _)
  obtain ⟨x, hxcl, hxy⟩ := hy
  have hxy' : r x y := Quotient.exact hxy
  rw [hs.closure_eq_setOfPred_specializes hX] at hxcl ⊢
  obtain ⟨x', hx's, hx'x⟩ := hxcl
  obtain ⟨q', hq', hq'1⟩ := @hs_gen ⟨(x, y), hxy'⟩ x' hx'x
  have hq'2 : q'.1.2 ⤳ y := hq'.map (continuous_snd.comp continuous_subtype_val)
  exact ⟨q'.1.2, hs_sat (hq'1 ▸ q'.2) hx's, hq'2⟩

/-- Under the hypotheses of `IsLocallyProConstructible.preimage_image_quotientMk_closure_eq`, the
image `Quotient.mk r '' closure s` is closed in `Quotient r`. -/
theorem IsLocallyProConstructible.isClosed_image_quotientMk_closure {s : Set X}
    (hs : IsLocallyProConstructible s) (hX : IsLocallySpectralSpace X)
    (hs_gen : GeneralizingMap (fun q : {q : X × X | r q.1 q.2} ↦ q.1.1))
    (hs_sat : ∀ ⦃x y : X⦄, r x y → x ∈ s → y ∈ s) :
    IsClosed (Quotient.mk r '' closure s) := by
  have hq : IsQuotientMap (Quotient.mk r) := isQuotientMap_quot_mk
  rw [← hq.isClosed_preimage, hs.preimage_image_quotientMk_closure_eq hX hs_gen hs_sat]
  exact isClosed_closure

/-- Along a locally pro-constructible equivalence relation on a locally spectral space with
quasi-compact, generalizing projections, the quotient projection `Quotient.mk r` lifts
generalizations. -/
theorem generalizingMap_quotientMk (hX : IsLocallySpectralSpace X)
    (hR : IsLocallyProConstructible {q : X × X | r q.1 q.2})
    (hs_qc : IsSpectralMap (fun q : {q : X × X | r q.1 q.2} ↦ q.1.1))
    (hs_gen : GeneralizingMap (fun q : {q : X × X | r q.1 q.2} ↦ q.1.1)) :
    GeneralizingMap (Quotient.mk r) := by
  intro x b hb
  obtain ⟨z, rfl⟩ := Quotient.exists_rep b
  let Fz : Set X := Quotient.mk r ⁻¹' (Quotient.mk r '' {z})
  have hFz : IsLocallyProConstructible Fz :=
    (isLocallyProConstructible_singleton z).preimage_image_quotientMk hX hR hs_qc
  have hFz_sat : ∀ ⦃u v : X⦄, r u v → u ∈ Fz → v ∈ Fz := fun _ _ huv hu ↦ by
    simpa only [Fz, mem_preimage, ← Quotient.sound huv] using hu
  have hx : Quotient.mk r x ∈ Quotient.mk r '' closure Fz :=
    hb.mem_closed (hFz.isClosed_image_quotientMk_closure hX hs_gen hFz_sat)
      (mem_image_of_mem _ (subset_closure ⟨z, rfl, rfl⟩))
  rw [← mem_preimage, hFz.preimage_image_quotientMk_closure_eq hX hs_gen hFz_sat,
    hFz.closure_eq_setOfPred_specializes hX] at hx
  obtain ⟨x', ⟨_, rfl, hzx'⟩, hx'x⟩ := hx
  exact ⟨x', hx'x, hzx'.symm⟩

/-- **Scholze, Lemma 2.7(i)**: the quotient of a locally spectral space by a locally
pro-constructible equivalence relation with quasi-compact, generalizing projections is T₀. -/
theorem t0Space_quotient (hX : IsLocallySpectralSpace X)
    (hR : IsLocallyProConstructible {q : X × X | r q.1 q.2})
    (hs_qc : IsSpectralMap (fun q : {q : X × X | r q.1 q.2} ↦ q.1.1))
    (hs_gen : GeneralizingMap (fun q : {q : X × X | r q.1 q.2} ↦ q.1.1)) :
    T0Space (Quotient r) := by
  have hπ_gen := generalizingMap_quotientMk hX hR hs_qc hs_gen
  refine (t0Space_iff_inseparable (Quotient r)).mpr fun a b hab ↦ ?_
  obtain ⟨x, rfl⟩ := Quotient.exists_rep a
  obtain ⟨y, rfl⟩ := Quotient.exists_rep b
  let F (z : X) : Set X := Quotient.mk r ⁻¹' {Quotient.mk r z}
  have hF (z : X) : IsLocallyProConstructible (F z) := by
    simpa only [F, image_singleton] using
      (isLocallyProConstructible_singleton z).preimage_image_quotientMk hX hR hs_qc
  have hF_cl (z : X) : ∀ ⦃u v : X⦄, r u v → u ∈ closure (F z) → v ∈ closure (F z) :=
    fun u v huv hu ↦ by
      have hsat : ∀ ⦃a b : X⦄, r a b → a ∈ F z → b ∈ F z :=
        fun _ _ hab ha ↦ (Quotient.sound hab).symm.trans ha
      rw [← (hF z).preimage_image_quotientMk_closure_eq hX hs_gen hsat]
      exact ⟨u, hu, Quotient.sound huv⟩
  obtain ⟨x₀, hx₀y, hx₀x⟩ := @hπ_gen y (Quotient.mk r x) hab.specializes
  obtain ⟨y₀, hy₀x, hy₀y⟩ := @hπ_gen x (Quotient.mk r y) hab.symm.specializes
  have hy_clx : y ∈ closure (F x) := hx₀y.mem_closed isClosed_closure (subset_closure hx₀x)
  have hx_cly : x ∈ closure (F y) := hy₀x.mem_closed isClosed_closure (subset_closure hy₀y)
  -- Pick a component-generic point `η` of `Z = closure (F x) ∩ closure (F y)`; minimality under
  -- specialization forces `η ∈ F x ∩ F y`.
  let Z : Set X := closure (F x) ∩ closure (F y)
  have hZc : IsClosed Z := isClosed_closure.inter isClosed_closure
  have _ : QuasiSober X := hX.quasiSober
  have _ : T0Space X := hX.t0Space
  have _ : QuasiSober Z := hZc.isClosedEmbedding_subtypeVal.quasiSober
  obtain ⟨η, hη, -⟩ := hZc.exists_genericPoint_specializes ⟨subset_closure rfl, hx_cly⟩
  have hη_eq (z : X) (hηz : η.1 ∈ closure (F z)) (hzZ : ∀ w, Quotient.mk r w = Quotient.mk r z →
      w ∈ Z) : Quotient.mk r η.1 = Quotient.mk r z := by
    obtain ⟨z', hz'z, hz'η⟩ := ((hF z).closure_eq_setOfPred_specializes hX).subset hηz
    have hηz' : (⟨z', hzZ z' hz'z⟩ : Z) = η :=
      mem_genericPoints_iff.mp hη _ (IsInducing.subtypeVal.specializes_iff.mp hz'η)
    exact (congrArg (Quotient.mk r ∘ Subtype.val) hηz').symm.trans hz'z
  have hxη := hη_eq x η.2.1 fun w hw ↦
    ⟨subset_closure hw, hF_cl y (Quotient.exact hw.symm) hx_cly⟩
  have hyη := hη_eq y η.2.2 fun w hw ↦
    ⟨hF_cl x (Quotient.exact hw.symm) hy_clx, subset_closure hw⟩
  exact hxη.symm.trans hyη

/-- If an open set `W'` contains the `r`-saturation of an open set `W`, then removing the closure
of the `r`-saturation of `W'ᶜ` produces an open subset `V` of `Quotient r` with
`W ⊆ Quotient.mk r ⁻¹' V ⊆ W'`. -/
theorem exists_isOpen_quotientMk_preimage_subset_of_subset (hX : IsLocallySpectralSpace X)
    (hR : IsLocallyProConstructible {q : X × X | r q.1 q.2})
    (hs_qc : IsSpectralMap (fun q : {q : X × X | r q.1 q.2} ↦ q.1.1))
    (hs_gen : GeneralizingMap (fun q : {q : X × X | r q.1 q.2} ↦ q.1.1))
    {W W' : Set X} (hWo : IsOpen W) (hW'o : IsOpen W')
    (hWW' : Quotient.mk r ⁻¹' (Quotient.mk r '' W) ⊆ W') :
    ∃ V : Set (Quotient r), IsOpen V ∧ W ⊆ Quotient.mk r ⁻¹' V ∧ Quotient.mk r ⁻¹' V ⊆ W' := by
  let S : Set X := Quotient.mk r ⁻¹' (Quotient.mk r '' W'ᶜ)
  have hS : IsLocallyProConstructible S :=
    hW'o.isClosed_compl.isLocallyProConstructible.preimage_image_quotientMk hX hR hs_qc
  have hS_sat : ∀ ⦃u v : X⦄, r u v → u ∈ S → v ∈ S := fun _ _ huv hu ↦ by
    simpa only [S, mem_preimage, ← Quotient.sound huv] using hu
  let V : Set (Quotient r) := (Quotient.mk r '' closure S)ᶜ
  have hVo : IsOpen V := (hS.isClosed_image_quotientMk_closure hX hs_gen hS_sat).isOpen_compl
  have hpre : Quotient.mk r ⁻¹' V = (closure S)ᶜ := by
    rw [preimage_compl, hS.preimage_image_quotientMk_closure_eq hX hs_gen hS_sat]
  refine ⟨V, hVo, ?_, ?_⟩
  · rw [hpre]
    intro x hxW hxcl
    obtain ⟨z, hzW, ⟨w, hwW', hwz⟩⟩ := mem_closure_iff.mp hxcl W hWo hxW
    exact hwW' (hWW' ⟨z, hzW, hwz.symm⟩)
  · rw [hpre, compl_subset_comm]
    exact (subset_preimage_image _ W'ᶜ).trans subset_closure

/-- **Scholze, Lemma 2.7(ii)**: for every compact open `W ⊆ X`, there exist an open subset `V` of
`Quotient r` and a nonempty family `𝒮` of compact open subsets of `X` whose intersection `⋂₀ 𝒮` is
`r`-saturated and satisfies `W ⊆ Quotient.mk r ⁻¹' V ⊆ ⋂₀ 𝒮`. -/
theorem exists_isOpen_quotientMk_preimage_subset_sInter (hX : IsLocallySpectralSpace X)
    (hR : IsLocallyProConstructible {q : X × X | r q.1 q.2})
    (hs_qc : IsSpectralMap (fun q : {q : X × X | r q.1 q.2} ↦ q.1.1))
    (hs_gen : GeneralizingMap (fun q : {q : X × X | r q.1 q.2} ↦ q.1.1))
    {W : Set X} (hWo : IsOpen W) (hWc : IsCompact W) :
    ∃ (V : Set (Quotient r)) (𝒮 : Set (Set X)),
      IsOpen V ∧ 𝒮.Nonempty ∧ (∀ O ∈ 𝒮, IsOpen O ∧ IsCompact O) ∧
        Quotient.mk r ⁻¹' (Quotient.mk r '' (⋂₀ 𝒮)) = ⋂₀ 𝒮 ∧
        W ⊆ Quotient.mk r ⁻¹' V ∧ Quotient.mk r ⁻¹' V ⊆ ⋂₀ 𝒮 := by
  have _ : PrespectralSpace X := hX.prespectralSpace
  have ht_qc : IsSpectralMap (fun q : {q : X × X | r q.1 q.2} ↦ q.1.2) :=
    isSpectralMap_fst_setoid_iff.mp hs_qc
  -- Enclose the compact saturation `E` of `W` in a compact open `W'`.
  have hEc : IsCompact (Quotient.mk r ⁻¹' (Quotient.mk r '' W)) := by
    rw [preimage_image_quotientMk_eq]
    exact (ht_qc.isCompact_preimage_of_isOpen hWo hWc).image hs_qc.continuous
  obtain ⟨W', hW'c, hW'o, hEW', -⟩ :=
    PrespectralSpace.exists_isCompact_and_isOpen_between hEc isOpen_univ (subset_univ _)
  obtain ⟨V, hVo, hWV, hVW'⟩ :=
    exists_isOpen_quotientMk_preimage_subset_of_subset hX hR hs_qc hs_gen hWo hW'o hEW'
  -- The saturation `E'` of `W'` is compact and stable under generalization, hence `⋂₀ 𝒮`.
  let E' : Set X := Quotient.mk r ⁻¹' (Quotient.mk r '' W')
  have hE'c : IsCompact E' := by
    rw [show E' = _ from preimage_image_quotientMk_eq]
    exact (ht_qc.isCompact_preimage_of_isOpen hW'o hW'c).image hs_qc.continuous
  have hE'gen : StableUnderGeneralization E' := by
    intro x x' hx'x hx
    rw [show E' = _ from preimage_image_quotientMk_eq] at hx ⊢
    obtain ⟨q, hqW', rfl⟩ := hx
    obtain ⟨q', hq'q, hq'1⟩ := @hs_gen q x' hx'x
    exact ⟨q', hW'o.stableUnderGeneralization
      (hq'q.map (continuous_snd.comp continuous_subtype_val)) hqW', hq'1⟩
  let 𝒮 : Set (Set X) := {O : Set X | IsOpen O ∧ IsCompact O ∧ E' ⊆ O}
  have hE'eq : E' = ⋂₀ 𝒮 := hE'c.eq_sInter_of_stableUnderGeneralization hE'gen
  obtain ⟨W'', hW''c, hW''o, hE'W'', -⟩ :=
    PrespectralSpace.exists_isCompact_and_isOpen_between hE'c isOpen_univ (subset_univ _)
  refine ⟨V, 𝒮, hVo, ⟨W'', hW''o, hW''c, hE'W''⟩, fun O hO ↦ ⟨hO.1, hO.2.1⟩, ?_, hWV, ?_⟩
  · rw [← hE'eq]
    simp only [E', image_preimage_eq _ Quotient.mk_surjective]
  · rw [← hE'eq]
    exact hVW'.trans (subset_preimage_image _ W')

/-! ### Spectral quotients: the basis criterion -/

section GlobalSpectral

variable [SpectralSpace X]

/-- On a spectral space, a pro-constructible equivalence relation with generalizing first
projection has a T₀ quotient. -/
theorem IsProConstructible.t0Space_quotient
    (hR : IsProConstructible {q : X × X | r q.1 q.2})
    (hs : GeneralizingMap (fun q : {q : X × X | r q.1 q.2} ↦ q.1.1)) :
    T0Space (Quotient r) :=
  TauCeti.t0Space_quotient SpectralSpace.isLocallySpectralSpace hR.isLocallyProConstructible
    (isProperMap_fst_of_compactSpace.isSpectralMap.comp hR.isSpectralMap_subtypeVal) hs

/-- On a spectral space, the quotient map of a pro-constructible equivalence relation with
generalizing first projection lifts generalizations. -/
theorem IsProConstructible.generalizingMap_quotientMk
    (hR : IsProConstructible {q : X × X | r q.1 q.2})
    (hs : GeneralizingMap (fun q : {q : X × X | r q.1 q.2} ↦ q.1.1)) :
    GeneralizingMap (Quotient.mk r) :=
  TauCeti.generalizingMap_quotientMk SpectralSpace.isLocallySpectralSpace
    hR.isLocallyProConstructible
    (isProperMap_fst_of_compactSpace.isSpectralMap.comp hR.isSpectralMap_subtypeVal) hs

/-- **Scholze, Lemma 2.9**: let `X` be a spectral space and `r` a pro-constructible equivalence
relation on `X` whose first projection lifts generalizations. If `Quotient r` admits a topological
basis `B` whose members pull back to compact subsets of `X`, then `Quotient r` is a spectral
space. Together with `TauCeti.isSpectralMap_of_isTopologicalBasis` and
`TauCeti.IsProConstructible.generalizingMap_quotientMk`, this also shows that `Quotient.mk r` is a
generalizing spectral map. -/
theorem spectralSpace_quotient (hR : IsProConstructible {q : X × X | r q.1 q.2})
    (hs : GeneralizingMap (fun q : {q : X × X | r q.1 q.2} ↦ q.1.1))
    {B : Set (Set (Quotient r))} (hB : IsTopologicalBasis B)
    (hBc : ∀ V ∈ B, IsCompact (Quotient.mk r ⁻¹' V)) :
    SpectralSpace (Quotient r) := by
  have _ : T0Space (Quotient r) := hR.t0Space_quotient hs
  have hgen : (instTopologicalSpaceQuotient : TopologicalSpace (Quotient r)) =
      TopologicalSpace.generateFrom B := hB.eq_generateFrom
  have hBopen (V : Set (Quotient r)) (hV : V ∈ B) : IsOpen (Quotient.mk r ⁻¹' V) :=
    (hB.isOpen hV).preimage continuous_quot_mk
  let t' : TopologicalSpace (Quotient r) :=
    TopologicalSpace.coinduced (Quotient.mk r) (constructibleTopology X)
  have hc : @CompactSpace (Quotient r) t' := by
    let _ : TopologicalSpace X := constructibleTopology X
    exact (Quotient.mk_surjective.comp (WithTopology.ofTopology_surjective _)).compactSpace
      (continuous_coinduced_rng.comp (WithTopology.continuous_ofTopology _))
  refine @spectralSpace_of_isClopen_generateFrom (Quotient r) B t' instTopologicalSpaceQuotient
    hgen hc (fun V hV ↦ ?_) inferInstance
  have hclopen : IsClopen[constructibleTopology X] (Quotient.mk r ⁻¹' V) :=
    (hBc V hV).isClopen_constructibleTopology_of_isOpen (hBopen V hV)
  let _ : TopologicalSpace (Quotient r) := t'
  refine ⟨?_, isOpen_coinduced.mpr hclopen.2⟩
  rw [← isOpen_compl_iff, isOpen_coinduced, preimage_compl]
  exact hclopen.1.isOpen_compl

end GlobalSpectral

/-! ### Spectral and locally spectral quotients: the open-projection case -/

/-- When `X` is locally spectral and the first projection of `{q : X × X | r q.1 q.2}` is open and
spectral (quasi-compact), the quotient projection `Quotient.mk r` is a spectral map. -/
theorem isSpectralMap_quotientMk_of_isOpenMap (hX : IsLocallySpectralSpace X)
    (hs_qc : IsSpectralMap (fun q : {q : X × X | r q.1 q.2} ↦ q.1.1))
    (hs_open : IsOpenMap (fun q : {q : X × X | r q.1 q.2} ↦ q.1.1)) :
    IsSpectralMap (Quotient.mk r) := by
  have _ : PrespectralSpace X := hX.prespectralSpace
  have ht_qc : IsSpectralMap (fun q : {q : X × X | r q.1 q.2} ↦ q.1.2) :=
    isSpectralMap_fst_setoid_iff.mp hs_qc
  have hπ_cont : Continuous (Quotient.mk r) := continuous_quot_mk
  refine ⟨hπ_cont, fun V hVo hVc ↦ ?_⟩
  obtain ⟨W, hWc, hWV⟩ := hs_open.quotientMk.exists_opens_image_eq_of_prespectralSpace
    hπ_cont (Quotient.mk_surjective.range_eq.symm ▸ subset_univ V) hVo hVc
  rw [← hWV, preimage_image_quotientMk_eq]
  exact (ht_qc.isCompact_preimage_of_isOpen W.2 hWc).image hs_qc.continuous

/-- When `X` is a quasiseparated locally spectral space and the first projection of
`{q : X × X | r q.1 q.2}` is open and spectral, `Quotient.mk r` is a locally spectral map. -/
theorem isLocallySpectralMap_quotientMk_of_isOpenMap [QuasiSeparatedSpace X]
    (hX : IsLocallySpectralSpace X)
    (hs_qc : IsSpectralMap (fun q : {q : X × X | r q.1 q.2} ↦ q.1.1))
    (hs_open : IsOpenMap (fun q : {q : X × X | r q.1 q.2} ↦ q.1.1)) :
    IsLocallySpectralMap (Quotient.mk r) :=
  (isSpectralMap_quotientMk_of_isOpenMap hX hs_qc hs_open).isLocallySpectralMap

/-- When `X` is a quasiseparated locally spectral space and the first projection of
`{q : X × X | r q.1 q.2}` is open and spectral, `Quotient r` is quasiseparated. -/
theorem quasiSeparatedSpace_quotient_of_isOpenMap [QuasiSeparatedSpace X]
    (hX : IsLocallySpectralSpace X)
    (hs_qc : IsSpectralMap (fun q : {q : X × X | r q.1 q.2} ↦ q.1.1))
    (hs_open : IsOpenMap (fun q : {q : X × X | r q.1 q.2} ↦ q.1.1)) :
    QuasiSeparatedSpace (Quotient r) := by
  have hπ : IsSpectralMap (Quotient.mk r) := isSpectralMap_quotientMk_of_isOpenMap hX hs_qc hs_open
  refine ⟨fun V₁ V₂ hV₁o hV₁c hV₂o hV₂c ↦ ?_⟩
  have hpre : IsCompact (Quotient.mk r ⁻¹' (V₁ ∩ V₂)) :=
    QuasiSeparatedSpace.inter_isCompact _ _
      (hV₁o.preimage hπ.continuous) (hπ.isCompact_preimage_of_isOpen hV₁o hV₁c)
      (hV₂o.preimage hπ.continuous) (hπ.isCompact_preimage_of_isOpen hV₂o hV₂c)
  simpa only [image_preimage_eq _ Quotient.mk_surjective] using hpre.image hπ.continuous

/-- Global spectral case of Scholze, Lemma 2.10: if `X` is a spectral space and `r` is a
pro-constructible equivalence relation whose first projection is an open map, then `Quotient r` is
a spectral space. -/
theorem IsProConstructible.spectralSpace_quotient_of_isOpenMap [SpectralSpace X]
    (hR : IsProConstructible {q : X × X | r q.1 q.2})
    (hs_open : IsOpenMap (fun q : {q : X × X | r q.1 q.2} ↦ q.1.1)) :
    SpectralSpace (Quotient r) := by
  have hX : IsLocallySpectralSpace X := SpectralSpace.isLocallySpectralSpace
  have hXX : IsLocallySpectralSpace (X × X) := hX.prod hX
  have hs_qc : IsSpectralMap (fun q : {q : X × X | r q.1 q.2} ↦ q.1.1) :=
    isProperMap_fst_of_compactSpace.isSpectralMap.comp hR.isSpectralMap_subtypeVal
  have hs_gen : GeneralizingMap (fun q : {q : X × X | r q.1 q.2} ↦ q.1.1) :=
    (IsLocallySpectralMap.comp hXX (hX.isLocallySpectralMap_fst hX)
      (hR.isLocallyProConstructible.isLocallySpectralMap_subtypeVal
        hXX)).generalizingMap_of_isOpenMap
      (hR.isLocallyProConstructible.isLocallySpectralSpace hXX) hX hs_open
  have hπ_open : IsOpenMap (Quotient.mk r) := hs_open.quotientMk
  have hπ_spec : IsSpectralMap (Quotient.mk r) :=
    isSpectralMap_quotientMk_of_isOpenMap hX hs_qc hs_open
  have hπ_oq : IsOpenQuotientMap (Quotient.mk r) :=
    ⟨Quotient.mk_surjective, continuous_quot_mk, hπ_open⟩
  refine spectralSpace_quotient hR hs_gen
    (hπ_oq.isTopologicalBasis PrespectralSpace.isTopologicalBasis) ?_
  rintro _ ⟨W, ⟨hWo, hWc⟩, rfl⟩
  exact hπ_spec.isCompact_preimage_of_isOpen (hπ_open W hWo) (hWc.image continuous_quot_mk)

/-- **Scholze, Lemma 2.10**: let `X` be a quasiseparated locally spectral space and `r` a locally
pro-constructible equivalence relation on `X` whose first projection is open and spectral
(quasi-compact). Then `Quotient r` is a locally spectral space. -/
theorem isLocallySpectralSpace_quotient_of_isOpenMap [QuasiSeparatedSpace X]
    (hX : IsLocallySpectralSpace X)
    (hR : IsLocallyProConstructible {q : X × X | r q.1 q.2})
    (hs_qc : IsSpectralMap (fun q : {q : X × X | r q.1 q.2} ↦ q.1.1))
    (hs_open : IsOpenMap (fun q : {q : X × X | r q.1 q.2} ↦ q.1.1)) :
    IsLocallySpectralSpace (Quotient r) := by
  have _ : PrespectralSpace X := hX.prespectralSpace
  have hπ_open : IsOpenMap (Quotient.mk r) := hs_open.quotientMk
  have hπ_spec : IsSpectralMap (Quotient.mk r) :=
    isSpectralMap_quotientMk_of_isOpenMap hX hs_qc hs_open
  refine isLocallySpectralSpace_iff.mpr fun y ↦ ?_
  obtain ⟨x, rfl⟩ := Quotient.exists_rep y
  obtain ⟨W₀, ⟨hW₀o, hW₀c⟩, hxW₀, -⟩ :=
    PrespectralSpace.isTopologicalBasis.exists_subset_of_mem_open (mem_univ x) isOpen_univ
  let V₀ : Set (Quotient r) := Quotient.mk r '' W₀
  have hV₀o : IsOpen V₀ := hπ_open W₀ hW₀o
  let U : Set X := Quotient.mk r ⁻¹' V₀
  have hUo : IsOpen U := hV₀o.preimage continuous_quot_mk
  have _ : SpectralSpace U :=
    (hπ_spec.isCompact_preimage_of_isOpen hV₀o
      (hW₀c.image continuous_quot_mk)).spectralSpace_of_isOpen hUo hX
  have hR_U : IsProConstructible {q : U × U | (r.comap Subtype.val) q.1 q.2} :=
    isLocallyProConstructible_iff_isProConstructible.mp
      (hR.preimage_of_isOpenEmbedding
        (hUo.isOpenEmbedding_subtypeVal.prodMap hUo.isOpenEmbedding_subtypeVal))
  have _ : SpectralSpace (Quotient (r.comap (Subtype.val : U → X))) :=
    hR_U.spectralSpace_quotient_of_isOpenMap (hUo.isOpenMap_fst_setoid_comap hs_open)
  exact ⟨V₀, hV₀o, mem_image_of_mem _ hxW₀, hV₀o.quotientComapHomeomorph.spectralSpace⟩

end TauCeti

end
