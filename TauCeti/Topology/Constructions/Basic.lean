/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Constructions
public import Mathlib.Topology.ContinuousMap.Defs
public import Mathlib.Topology.Inseparable
public import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Topology.Maps.OpenQuotient

/-!
# Quotients by setoids and fibre products of topological spaces

This file adds to Mathlib's quotient-topology API for `Quotient.mk s`, where `s : Setoid X`, and to
the topology of the fibre product `Function.Pullback f g`, a subspace of the product.

## Main results

* `Setoid.image_quotient_mk_compl`: if `s` identifies only points of `t`, the quotient map sends
  the complement of `t` onto the complement of the image of `t`.
* `Setoid.preimage_image_quotient_mk`, `Setoid.image_snd_preimage_fst`,
  `Setoid.image_subtypeVal_preimage_image_quotient_mk_comap`: the `s`-saturation of a set
  expressed via `Quotient.mk s`, via the two projections of the graph of `s`, and under
  restriction to a saturated subset.
* `Setoid.range_quotient_map'_subtypeVal`, `Setoid.isEmbedding_quotient_map'_subtypeVal`:
  the canonical map `Quotient (s.comap Subtype.val) → Quotient s` has range `Quotient.mk s '' U`,
  and is a topological embedding when `Quotient.mk s` is open and `U` is `s`-saturated.
* `Setoid.isOpen_image_quotient_mk`: the image of an open set closed under `s` is open.
* `Setoid.isOpenEmbedding_domRestrict_quotient_mk_of_isOpen`: the quotient map restricted to an
  open set whose points are related only to themselves is an open embedding.
* `Setoid.graphSwap`: the coordinate-swap self-homeomorphism of the graph of `s`.
* `Setoid.isOpenMap_fst_iff_snd`, `Setoid.generalizingMap_fst_iff_snd`: by symmetry of `s`, the
  first projection from its graph is open (resp. generalizing) if and only if the second
  projection is.
* `Setoid.stableUnderGeneralization_saturation`: when the first projection is generalizing, the
  `s`-saturation preserves stability under generalization.
* `Setoid.isOpenMap_quotient_mk_comap_subtypeVal`, `Setoid.generalizingMap_fst_comap_subtypeVal`:
  restricting `s` to an open subset preserves openness of the quotient map and the generalizing
  property of the first projection.
* `Setoid.isOpenMap_quotient_mk_iff`: `Quotient.mk s` is an open map if and only if the first
  projection from the graph of `s` is open.
* `Function.Pullback.continuous_fst`, `Function.Pullback.continuous_snd`: the projections of the
  fibre product are continuous.
* `Topology.IsInducing.isOpenMap_rangeFactorization_snd_comp`: open maps are stable under
  pullback; the projection of a fibre product to one factor is open onto its range when the map
  from the other factor is.
* `ContinuousMap.pullbackFst`, `ContinuousMap.pullbackSnd`: the projections of the fibre product,
  bundled as continuous maps.
-/

public section

open Set Topology

namespace Setoid

variable {X : Type*} (s : Setoid X)

/-- If an equivalence relation identifies only points of a set `t`, then the quotient map sends the
complement of `t` onto the complement of the image of `t`. -/
theorem image_quotient_mk_compl {t : Set X} (hst : ∀ ⦃x y⦄, s x y → x ≠ y → x ∈ t) :
    Quotient.mk s '' tᶜ = (Quotient.mk s '' t)ᶜ := by
  ext q
  induction q using Quotient.inductionOn with | h y => ?_
  simp only [mem_image, mem_compl_iff, Quotient.eq, not_exists, not_and]
  constructor
  · rintro ⟨x, hx, hxy⟩ z hz hzy
    by_cases hne : x = z
    · exact hx (hne ▸ hz)
    · exact hx (hst (s.trans hxy (s.symm hzy)) hne)
  · intro h
    exact ⟨y, fun hy => h y hy (s.refl y), s.refl y⟩

/-- The preimage of the quotient image of `t` is its `s`-saturation. -/
theorem preimage_image_quotient_mk (t : Set X) :
    Quotient.mk s ⁻¹' (Quotient.mk s '' t) = {y | ∃ x ∈ t, s x y} := by
  ext y
  constructor
  · rintro ⟨x, hxt, hxy⟩
    exact ⟨x, hxt, Quotient.exact hxy⟩
  · rintro ⟨x, hxt, hxy⟩
    exact ⟨x, hxt, Quotient.sound hxy⟩

/-- Pulling `t` back along the first projection of the graph of `s` and pushing forward along the
second projection produces its `s`-saturation. -/
theorem image_snd_preimage_fst (t : Set X) :
    (fun q : {q : X × X // s q.1 q.2} ↦ q.1.2) ''
        ((fun q : {q : X × X // s q.1 q.2} ↦ q.1.1) ⁻¹' t) =
      {y | ∃ x ∈ t, s x y} := by
  ext y
  constructor
  · rintro ⟨⟨⟨x, y'⟩, hxy⟩, hxt, rfl⟩
    exact ⟨x, hxt, hxy⟩
  · rintro ⟨x, hxt, hxy⟩
    exact ⟨⟨(x, y), hxy⟩, hxt, rfl⟩

/-- The range of the canonical map `Quotient (s.comap Subtype.val) → Quotient s` is
`Quotient.mk s '' U`. -/
theorem range_quotient_map'_subtypeVal (U : Set X) :
    range (Quotient.map' (Subtype.val : U → X) (s₁ := s.comap Subtype.val) (s₂ := s)
        fun _ _ h ↦ h) =
      Quotient.mk s '' U := by
  ext z
  constructor
  · rintro ⟨a, rfl⟩
    exact Quotient.inductionOn a fun u ↦ ⟨u.1, u.2, rfl⟩
  · rintro ⟨u, huU, rfl⟩
    exact ⟨Quotient.mk (s.comap Subtype.val) ⟨u, huU⟩, rfl⟩

/-- For an `s`-saturated subset `U`, pushing forward the restricted saturation of `O ⊆ U` under
`Subtype.val` recovers the `s`-saturation of `Subtype.val '' O` in `X`. -/
theorem image_subtypeVal_preimage_image_quotient_mk_comap {U : Set X}
    (hsat : ∀ ⦃x y⦄, x ∈ U → s x y → y ∈ U) (O : Set U) :
    Subtype.val '' (Quotient.mk (s.comap Subtype.val) ⁻¹'
        (Quotient.mk (s.comap Subtype.val) '' O)) =
      Quotient.mk s ⁻¹' (Quotient.mk s '' (Subtype.val '' O)) := by
  ext z
  simp only [preimage_image_quotient_mk, mem_image, mem_ofPred_eq]
  constructor
  · rintro ⟨_, ⟨v, hvO, hvz⟩, rfl⟩
    exact ⟨v.1, ⟨v, hvO, rfl⟩, hvz⟩
  · rintro ⟨_, ⟨v, hvO, rfl⟩, hvz⟩
    exact ⟨⟨z, hsat v.2 hvz⟩, ⟨v, hvO, hvz⟩, rfl⟩

variable [TopologicalSpace X]

/-- The image in `Quotient s` of an open set closed under the relation `s` is open. -/
theorem isOpen_image_quotient_mk {U : Set X} (hU : IsOpen U)
    (hsat : ∀ ⦃x y⦄, x ∈ U → s x y → y ∈ U) : IsOpen (Quotient.mk s '' U) := by
  have hsatU : Quotient.mk s ⁻¹' (Quotient.mk s '' U) = U := by
    refine Subset.antisymm ?_ (subset_preimage_image _ _)
    rintro y ⟨x, hx, hxy⟩
    exact hsat hx (Quotient.exact hxy)
  have hq : IsQuotientMap (Quotient.mk s) := isQuotientMap_quotient_mk'
  rwa [← hq.isOpen_preimage, hsatU]

/-- If every point of an open set `U` is related by `s` only to itself, then the quotient map
restricted to `U` is an open embedding. -/
theorem isOpenEmbedding_domRestrict_quotient_mk_of_isOpen {U : Set X} (hU : IsOpen U)
    (hfix : ∀ ⦃x y⦄, x ∈ U → s x y → x = y) :
    IsOpenEmbedding (U.domRestrict (Quotient.mk s)) := by
  refine .of_continuous_injective_isOpenMap
    (continuous_quotient_mk'.comp continuous_subtype_val) (fun x y hxy => ?_) fun W hW => ?_
  · exact Subtype.ext (hfix x.2 (Quotient.exact hxy))
  · rw [domRestrict_eq, image_comp]
    refine isOpen_image_quotient_mk s (hU.isOpenMap_subtype_val W hW) ?_
    rintro _ y ⟨x, hx, rfl⟩ hxy
    exact hfix x.2 hxy ▸ mem_image_of_mem _ hx

/-- Swapping coordinates restricts to a self-homeomorphism of the graph of `s`. -/
def graphSwap : {q : X × X // s q.1 q.2} ≃ₜ {q : X × X // s q.1 q.2} :=
  (Homeomorph.prodComm X X).subtype fun _ ↦ ⟨s.symm, s.symm⟩

@[simp]
theorem graphSwap_apply (q : {q : X × X // s q.1 q.2}) :
    s.graphSwap q = ⟨(q.1.2, q.1.1), s.symm q.2⟩ := by
  rfl

@[simp]
theorem graphSwap_symm : s.graphSwap.symm = s.graphSwap := by
  exact Homeomorph.ext fun _ ↦ rfl

@[simp]
theorem fst_comp_graphSwap :
    (fun q : {q : X × X // s q.1 q.2} ↦ q.1.1) ∘ s.graphSwap =
      fun q : {q : X × X // s q.1 q.2} ↦ q.1.2 := by
  rfl

@[simp]
theorem snd_comp_graphSwap :
    (fun q : {q : X × X // s q.1 q.2} ↦ q.1.2) ∘ s.graphSwap =
      fun q : {q : X × X // s q.1 q.2} ↦ q.1.1 := by
  rfl

/-- By symmetry of `s`, the first projection from the graph of `s` is open if and only if the
second projection is open. -/
theorem isOpenMap_fst_iff_snd :
    IsOpenMap (fun q : {q : X × X // s q.1 q.2} ↦ q.1.1) ↔
      IsOpenMap (fun q : {q : X × X // s q.1 q.2} ↦ q.1.2) :=
  ⟨fun h ↦ s.fst_comp_graphSwap ▸ h.comp s.graphSwap.isOpenMap,
    fun h ↦ s.snd_comp_graphSwap ▸ h.comp s.graphSwap.isOpenMap⟩

/-- By symmetry of `s`, the first projection from the graph of `s` is generalizing if and only if
the second projection is generalizing. -/
theorem generalizingMap_fst_iff_snd :
    GeneralizingMap (fun q : {q : X × X // s q.1 q.2} ↦ q.1.1) ↔
      GeneralizingMap (fun q : {q : X × X // s q.1 q.2} ↦ q.1.2) :=
  ⟨fun h ↦ s.fst_comp_graphSwap ▸ s.graphSwap.isOpenEmbedding.generalizingMap.comp h,
    fun h ↦ s.snd_comp_graphSwap ▸ s.graphSwap.isOpenEmbedding.generalizingMap.comp h⟩

/-- If the first projection from the graph of `s` is generalizing, then the `s`-saturation of a
subset stable under generalization is stable under generalization. -/
theorem stableUnderGeneralization_saturation
    (hs_gen : GeneralizingMap fun q : {q : X × X // s q.1 q.2} ↦ q.1.1)
    {t : Set X} (ht : StableUnderGeneralization t) :
    StableUnderGeneralization {y | ∃ x ∈ t, s x y} := by
  rw [← s.image_snd_preimage_fst]
  exact (s.generalizingMap_fst_iff_snd.mp hs_gen).stableUnderGeneralization_image
    (ht.preimage (continuous_fst.comp continuous_subtype_val))

/-- If `Quotient.mk s` is open and `U` is `s`-saturated, then the canonical map
`Quotient (s.comap Subtype.val) → Quotient s` is a topological embedding. -/
theorem isEmbedding_quotient_map'_subtypeVal (hq : IsOpenMap (Quotient.mk s))
    {U : Set X} (hsat : ∀ ⦃x y⦄, x ∈ U → s x y → y ∈ U) :
    IsEmbedding (Quotient.map' (Subtype.val : U → X) (s₁ := s.comap Subtype.val) (s₂ := s)
      fun _ _ h ↦ h) :=
  isEmbedding_of_isOpenQuotientMap_of_isInducing Subtype.val _
    (Quotient.mk (s.comap Subtype.val)) (Quotient.mk s) rfl
    IsEmbedding.subtypeVal.isInducing isQuotientMap_quotient_mk'
    (.of_isOpenMap_isQuotientMap hq isQuotientMap_quotient_mk')
    (fun a b hab ↦ Quotient.inductionOn₂ a b
      (fun _ _ h ↦ Quotient.sound (s := s.comap Subtype.val) (Quotient.exact (s := s) h)) hab)
    (by
      rintro z ⟨_, ⟨u, rfl⟩, hzu⟩
      exact ⟨⟨z, hsat u.2 (Quotient.exact hzu)⟩, rfl⟩)

/-- Restricting a setoid with open quotient map to an open subset preserves openness of the
quotient map. -/
theorem isOpenMap_quotient_mk_comap_subtypeVal (hq : IsOpenMap (Quotient.mk s))
    {U : Set X} (hUo : IsOpen U) :
    IsOpenMap (Quotient.mk (s.comap (Subtype.val : U → X))) := fun O hOo ↦ by
  rw [isOpen_coinduced]
  have hpre : Quotient.mk' ⁻¹'
      (Quotient.mk (s.comap (Subtype.val : U → X)) '' O) =
      (Subtype.val : U → X) ⁻¹' (Quotient.mk s ⁻¹' (Quotient.mk s '' (Subtype.val '' O))) := by
    change Quotient.mk (s.comap (Subtype.val : U → X)) ⁻¹'
        (Quotient.mk (s.comap (Subtype.val : U → X)) '' O) = _
    rw [(s.comap Subtype.val).preimage_image_quotient_mk, s.preimage_image_quotient_mk]
    ext u
    simp only [mem_ofPred_eq, mem_preimage, mem_image]
    constructor
    · rintro ⟨v, hvO, hvu⟩
      exact ⟨v.1, ⟨v, hvO, rfl⟩, hvu⟩
    · rintro ⟨_, ⟨v, hvO, rfl⟩, hvu⟩
      exact ⟨v, hvO, hvu⟩
  rw [hpre]
  exact ((hq _ (hUo.isOpenMap_subtype_val O hOo)).preimage continuous_quotient_mk').preimage
    continuous_subtype_val

/-- Restricting a setoid with generalizing first projection to an open subset preserves the
generalizing property of the first projection. -/
theorem generalizingMap_fst_comap_subtypeVal
    (hs_gen : GeneralizingMap fun q : {q : X × X // s q.1 q.2} ↦ q.1.1)
    {U : Set X} (hUo : IsOpen U) :
    GeneralizingMap fun q : {q : U × U // (s.comap Subtype.val) q.1 q.2} ↦ q.1.1 := by
  intro q u' hu'
  obtain ⟨p, hp_sp, hp1⟩ := hs_gen (a := ⟨(q.1.1.1, q.1.2.1), q.2⟩)
    (hu'.map continuous_subtype_val)
  have hp1' : p.1.1 = u'.1 := hp1
  have hp2U : p.1.2 ∈ U :=
    (hp_sp.map (continuous_snd.comp continuous_subtype_val)).mem_open hUo q.1.2.2
  have hrp : s u'.1 p.1.2 := hp1' ▸ p.2
  refine ⟨⟨(u', ⟨p.1.2, hp2U⟩), hrp⟩, ?_, rfl⟩
  refine IsEmbedding.subtypeVal.isInducing.specializes_iff.mp (specializes_prod.2 ⟨?_, ?_⟩)
  · exact IsEmbedding.subtypeVal.isInducing.specializes_iff.mp <|
      hp1' ▸ hp_sp.map (continuous_fst.comp continuous_subtype_val)
  · exact IsEmbedding.subtypeVal.isInducing.specializes_iff.mp <|
      hp_sp.map (continuous_snd.comp continuous_subtype_val)

end Setoid

section Pullback

variable {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Z] {f : X → Y} {g : Z → Y}

/-- The projection `X ×_Y Z → X` is continuous. -/
@[fun_prop]
theorem Function.Pullback.continuous_fst : Continuous (Pullback.fst : f.Pullback g → X) :=
  _root_.continuous_fst.comp continuous_subtype_val

/-- The projection `X ×_Y Z → Z` is continuous. -/
@[fun_prop]
theorem Function.Pullback.continuous_snd : Continuous (Pullback.snd : f.Pullback g → Z) :=
  _root_.continuous_snd.comp continuous_subtype_val

/-- **Open maps are stable under pullback.** Let `f : X → Y` be open onto its range and
`g : Z → Y` continuous, and let `ι : P → X × Z` induce the topology of `P` and have image the
fibre product `{p | f p.1 = g p.2}`, as the inclusion of `Function.Pullback f g` does. Then the
projection `P → Z` is open onto its range.

Near each of its points, an open subset of `P` contains the part of `P` over a box `U ×ˢ V`. The
projection of that part is the part of the range lying in `V ∩ g ⁻¹' O`, where `O` is an open set
cutting `f '' U` out of the range of `f`. -/
theorem Topology.IsInducing.isOpenMap_rangeFactorization_snd_comp [TopologicalSpace Y]
    {P : Type*} [TopologicalSpace P] {ι : P → X × Z} (hι : IsInducing ι)
    (hrange : range ι = {p | f p.1 = g p.2}) (hf : IsOpenMap (rangeFactorization f))
    (hg : Continuous g) : IsOpenMap (rangeFactorization (Prod.snd ∘ ι)) := by
  have hfg (q : P) : f (ι q).1 = g (ι q).2 := hrange.subset (mem_range_self q)
  intro W hW
  rw [isOpen_iff_mem_nhds]
  rintro _ ⟨w, hw, rfl⟩
  obtain ⟨T, hT, rfl⟩ := hι.isOpen_iff.1 hW
  obtain ⟨U, V, hU, hV, hwU, hwV, hUV⟩ := isOpen_prod_iff.1 hT _ _ hw
  obtain ⟨O, hO, hOU⟩ := isOpen_induced_iff.1 (hf U hU)
  have hfU : f '' U = O ∩ range f := by
    simpa only [image_image, rangeFactorization_coe, image_preimage_eq_inter_range,
      Subtype.range_coe] using (congrArg (Subtype.val '' ·) hOU).symm
  refine Filter.mem_of_superset ((hV.inter (hO.preimage hg)).preimage continuous_subtype_val
    |>.mem_nhds ⟨hwV, ?_⟩) ?_
  · simpa [hfg w] using (hfU.subset (mem_image_of_mem f hwU)).1
  · rintro ⟨_, q, rfl⟩ ⟨hqV, hqO⟩
    obtain ⟨x, hxU, hx⟩ : g (ι q).2 ∈ f '' U := hfU ▸ ⟨hqO, (ι q).1, hfg q⟩
    obtain ⟨q', hq'⟩ : (x, (ι q).2) ∈ range ι := hrange ▸ hx
    exact ⟨q', show ι q' ∈ T from hq' ▸ hUV ⟨hxU, hqV⟩, Subtype.ext (by simp [hq'])⟩

variable (f g)

/-- The projection `X ×_Y Z → X`, bundled as a continuous map. -/
def ContinuousMap.pullbackFst : C(f.Pullback g, X) :=
  ⟨Function.Pullback.fst, Function.Pullback.continuous_fst⟩

/-- The projection `X ×_Y Z → Z`, bundled as a continuous map. -/
def ContinuousMap.pullbackSnd : C(f.Pullback g, Z) :=
  ⟨Function.Pullback.snd, Function.Pullback.continuous_snd⟩

@[simp]
theorem ContinuousMap.coe_pullbackFst : ⇑(pullbackFst f g) = Function.Pullback.fst :=
  (rfl)

@[simp]
theorem ContinuousMap.coe_pullbackSnd : ⇑(pullbackSnd f g) = Function.Pullback.snd :=
  (rfl)

end Pullback

/-- The quotient map `Quotient.mk s` is open if and only if the first projection from the graph of
`s` is open. -/
theorem Setoid.isOpenMap_quotient_mk_iff {X : Type*} [TopologicalSpace X] (s : Setoid X) :
    IsOpenMap (Quotient.mk s) ↔
      IsOpenMap (fun q : {q : X × X // s q.1 q.2} ↦ q.1.1) := by
  constructor
  · intro hq
    refine s.isOpenMap_fst_iff_snd.mpr ?_
    have hq_rf : IsOpenMap (rangeFactorization (Quotient.mk s)) := fun U hUo ↦
      isOpen_induced_iff.mpr ⟨Quotient.mk s '' U, hq U hUo, by
        ext ⟨y, _⟩
        simp [rangeFactorization]⟩
    have hrange : range (Subtype.val : {q : X × X // s q.1 q.2} → X × X) =
        {p | Quotient.mk s p.1 = Quotient.mk s p.2} := by
      ext ⟨x, y⟩
      simp [Quotient.eq]
    have hpb := IsEmbedding.subtypeVal.isInducing.isOpenMap_rangeFactorization_snd_comp
      hrange hq_rf continuous_quotient_mk'
    have hval_open : IsOpenMap
        (Subtype.val : range (fun q : {q : X × X // s q.1 q.2} ↦ q.1.2) → X) := by
      refine IsOpen.isOpenMap_subtype_val ?_
      have huniv : range (fun q : {q : X × X // s q.1 q.2} ↦ q.1.2) = univ :=
        eq_univ_iff_forall.mpr fun x ↦ ⟨⟨(x, x), s.refl x⟩, rfl⟩
      rw [huniv]
      exact isOpen_univ
    exact hval_open.comp hpb
  · intro hs U hUo
    have ht : IsOpenMap (fun q : {q : X × X // s q.1 q.2} ↦ q.1.2) :=
      s.isOpenMap_fst_iff_snd.mp hs
    have heq : Quotient.mk' ⁻¹' (Quotient.mk s '' U) =
        (fun q : {q : X × X // s q.1 q.2} ↦ q.1.2) ''
          ((fun q : {q : X × X // s q.1 q.2} ↦ q.1.1) ⁻¹' U) :=
      (s.preimage_image_quotient_mk U).trans (s.image_snd_preimage_fst U).symm
    rw [isOpen_coinduced, heq]
    exact ht _ (hUo.preimage (continuous_fst.comp continuous_subtype_val))
