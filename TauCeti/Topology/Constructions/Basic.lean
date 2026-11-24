/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Constructions
public import Mathlib.Topology.ContinuousMap.Basic
import Mathlib.Topology.SeparatedMap

/-!
# Quotients by setoids, fibre products, and subtypes of topological spaces

This file adds to Mathlib's quotient-topology API for `Quotient.mk s`, where `s : Setoid X`, to
the topology of the fibre product `Function.Pullback f g`, a subspace of the product, and to the
subtype-topology convergence API for continuous maps on subtypes.

## Main results

* `Setoid.image_quotient_mk_compl`: if `s` identifies only points of `t`, the quotient map sends
  the complement of `t` onto the complement of the image of `t`.
* `Setoid.isOpen_image_quotient_mk`: the image of an open set closed under `s` is open.
* `Setoid.isOpenEmbedding_domRestrict_quotient_mk_of_isOpen`: the quotient map restricted to an
  open set whose points are related only to themselves is an open embedding.
* `Function.Pullback.continuous_fst`, `Function.Pullback.continuous_snd`: the projections of the
  fibre product are continuous.
* `Topology.IsInducing.isOpenMap_rangeFactorization_snd_comp`: open maps are stable under
  pullback; the projection of a fibre product to one factor is open onto its range when the map
  from the other factor is.
* `ContinuousMap.pullbackFst`, `ContinuousMap.pullbackSnd`, `ContinuousMap.mapPullback`,
  `ContinuousMap.mapPullbackSnd`, `Homeomorph.pullbackComm`: bundled projections, functoriality,
  and symmetry of the fibre product.
* `ContinuousAt.tendsto_comap_val`, `Continuous.tendsto_comap_val`: a continuous function on a
  subtype tends to `f x` along `Filter.comap Subtype.val (𝓝 x.val)`.
* `Topology.IsQuotientMap.of_comp_eq_comp`: quotient maps are stable under pullback along a
  continuous injection when the pulled-back inclusion is a closed map, as for the restriction of a
  quotient map to the preimage of a closed set.
-/

public section

open Set Topology

namespace Setoid

variable {X : Type*} (s : Setoid X)

/-- If an equivalence relation identifies only points of a set `t`, then the quotient map sends the
complement of `t` onto the complement of the image of `t`. -/
theorem image_quotient_mk_compl {t : Set X} (hst : ∀ ⦃x y⦄, s x y → x ≠ y → x ∈ t) :
    Quotient.mk s '' tᶜ = (Quotient.mk s '' t)ᶜ := by
  refine Subset.antisymm ?_ (subset_image_compl Quotient.mk_surjective)
  -- a point `x ∉ t` is related to no `y ∈ t`, since `x ≠ y` and `hst` would put `x` in `t`
  rintro _ ⟨x, hx, rfl⟩ ⟨y, hy, hyx⟩
  exact hx (hst (Quotient.exact hyx.symm) fun hxy => hx (hxy ▸ hy))

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
    (continuous_quotient_mk'.comp continuous_subtypeVal) (fun x y hxy => ?_) fun W hW => ?_
  · exact Subtype.ext (hfix x.property (Quotient.exact hxy))
  · rw [domRestrict_eq, image_comp]
    refine isOpen_image_quotient_mk s (hU.isOpenMap_subtypeVal W hW) ?_
    rintro _ y ⟨x, hx, rfl⟩ hxy
    exact hfix x.property hxy ▸ mem_image_of_mem _ hx

end Setoid

section Pullback

variable {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Z] {f : X → Y} {g : Z → Y}

/-- The projection `X ×_Y Z → X` is continuous. -/
@[fun_prop]
theorem Function.Pullback.continuous_fst : Continuous (Pullback.fst : f.Pullback g → X) :=
  _root_.continuous_fst.comp continuous_subtypeVal

/-- The projection `X ×_Y Z → Z` is continuous. -/
@[fun_prop]
theorem Function.Pullback.continuous_snd : Continuous (Pullback.snd : f.Pullback g → Z) :=
  _root_.continuous_snd.comp continuous_subtypeVal

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
  refine Filter.mem_of_superset ((hV.inter (hO.preimage hg)).preimage continuous_subtypeVal
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

@[simp] theorem ContinuousMap.coe_pullbackFst : ⇑(pullbackFst f g) = Function.Pullback.fst := (rfl)

@[simp] theorem ContinuousMap.coe_pullbackSnd : ⇑(pullbackSnd f g) = Function.Pullback.snd := (rfl)

/-- Swapping the two factors of a fibre product is a homeomorphism `X ×_Y Z ≃ₜ Z ×_Y X`. -/
def Homeomorph.pullbackComm : f.Pullback g ≃ₜ g.Pullback f where
  toFun x := ⟨x.val.swap, x.property.symm⟩
  invFun y := ⟨y.val.swap, y.property.symm⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := (continuous_swap.comp continuous_subtypeVal).subtype_mk _
  continuous_invFun := (continuous_swap.comp continuous_subtypeVal).subtype_mk _

@[simp] theorem Homeomorph.coe_pullbackComm_apply (x : f.Pullback g) :
    (Homeomorph.pullbackComm f g x).val = x.val.swap := (rfl)

@[simp] theorem Homeomorph.pullbackComm_symm :
    (Homeomorph.pullbackComm f g).symm = Homeomorph.pullbackComm g f := (rfl)

@[simp] theorem Homeomorph.pullbackComm_pullbackComm (x : f.Pullback g) :
    Homeomorph.pullbackComm g f (Homeomorph.pullbackComm f g x) = x := (rfl)

@[simp] theorem Homeomorph.pullbackComm_trans_pullbackComm :
    (Homeomorph.pullbackComm f g).trans (Homeomorph.pullbackComm g f) = .refl (f.Pullback g) := by
  ext : 1; rfl

@[simp] theorem ContinuousMap.pullbackFst_comp_pullbackComm :
    (ContinuousMap.pullbackFst g f).comp
      (Homeomorph.pullbackComm f g : C(f.Pullback g, g.Pullback f)) =
      ContinuousMap.pullbackSnd f g := by
  ext : 1; rfl

@[simp] theorem ContinuousMap.pullbackSnd_comp_pullbackComm :
    (ContinuousMap.pullbackSnd g f).comp
      (Homeomorph.pullbackComm f g : C(f.Pullback g, g.Pullback f)) =
      ContinuousMap.pullbackFst f g := by
  ext : 1; rfl

@[simp] theorem ContinuousMap.pullbackComm_comp_pullbackComm :
    (Homeomorph.pullbackComm g f : C(g.Pullback f, f.Pullback g)).comp
      (Homeomorph.pullbackComm f g : C(f.Pullback g, g.Pullback f)) = .id (f.Pullback g) := by
  ext : 1; rfl

section MapPullback

variable {X₁ X₂ Y₁ Y₂ Z₁ Z₂ : Type*}
  [TopologicalSpace X₁] [TopologicalSpace X₂] [TopologicalSpace Z₁] [TopologicalSpace Z₂]
  {f₁ : X₁ → Y₁} {g₁ : Z₁ → Y₁} {f₂ : X₂ → Y₂} {g₂ : Z₂ → Y₂}
  (mapX : C(X₁, X₂)) (mapY : Y₁ → Y₂) (mapZ : C(Z₁, Z₂))
  (commX : f₂ ∘ ⇑mapX = mapY ∘ f₁) (commZ : g₂ ∘ ⇑mapZ = mapY ∘ g₁)

/-- Bundled continuous map between fibre products induced by compatible maps on the factors. -/
def ContinuousMap.mapPullback : C(f₁.Pullback g₁, f₂.Pullback g₂) :=
  ⟨Function.mapPullback mapX mapY mapZ commX commZ, mapX.continuous.mapPullback mapZ.continuous⟩

@[simp] theorem ContinuousMap.coe_mapPullback_apply (x : f₁.Pullback g₁) :
    (ContinuousMap.mapPullback mapX mapY mapZ commX commZ x).val = (mapX x.val.1, mapZ x.val.2) :=
        (rfl)

@[simp] theorem ContinuousMap.pullbackFst_comp_mapPullback :
    (ContinuousMap.pullbackFst f₂ g₂).comp
      (ContinuousMap.mapPullback mapX mapY mapZ commX commZ) =
      mapX.comp (ContinuousMap.pullbackFst f₁ g₁) := by
  ext : 1; rfl

@[simp] theorem ContinuousMap.pullbackSnd_comp_mapPullback :
    (ContinuousMap.pullbackSnd f₂ g₂).comp
      (ContinuousMap.mapPullback mapX mapY mapZ commX commZ) =
      mapZ.comp (ContinuousMap.pullbackSnd f₁ g₁) := by
  ext : 1; rfl

end MapPullback

section MapPullbackSnd

variable {X Y Z₁ Z₂ : Type*}
  [TopologicalSpace X] [TopologicalSpace Z₁] [TopologicalSpace Z₂]
  (f : X → Y) {p : Z₁ → Y} {q : Z₂ → Y} (g : C(Z₁, Z₂)) (hg : q ∘ ⇑g = p)

/-- Bundled continuous map `f.Pullback p → f.Pullback q` over `X` induced by a map
`g : C(Z₁, Z₂)` over `Y` (`q ∘ g = p`). -/
def ContinuousMap.mapPullbackSnd : C(f.Pullback p, f.Pullback q) :=
  ContinuousMap.mapPullback (f₁ := f) (f₂ := f) (.id X) id g rfl hg

@[simp] theorem ContinuousMap.coe_mapPullbackSnd_apply (x : f.Pullback p) :
    (ContinuousMap.mapPullbackSnd f g hg x).val = (x.val.1, g x.val.2) := (rfl)

@[simp] theorem ContinuousMap.pullbackFst_comp_mapPullbackSnd :
    (ContinuousMap.pullbackFst f q).comp (ContinuousMap.mapPullbackSnd f g hg) =
      ContinuousMap.pullbackFst f p := by
  ext : 1; rfl

@[simp] theorem ContinuousMap.pullbackSnd_comp_mapPullbackSnd :
    (ContinuousMap.pullbackSnd f q).comp (ContinuousMap.mapPullbackSnd f g hg) =
      g.comp (ContinuousMap.pullbackSnd f p) := by
  ext : 1; rfl

end MapPullbackSnd

end Pullback

section Subtype

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {p : X → Prop} {f : Subtype p → Y}

/-- A function on a subtype that is continuous at `x` tends to `f x` along
`Filter.comap Subtype.val (𝓝 x.val)`. -/
theorem ContinuousAt.tendsto_comap_val {x : Subtype p} (hf : ContinuousAt f x) :
    Filter.Tendsto f (Filter.comap Subtype.val (𝓝 x.val)) (𝓝 (f x)) := by
  cases x
  rw [← nhds_subtype_eq_comap]
  exact hf.tendsto

/-- A continuous function on a subtype tends to `f x` along `Filter.comap Subtype.val (𝓝 x.val)` at
every point `x`. -/
theorem Continuous.tendsto_comap_val (hf : Continuous f) (x : Subtype p) :
    Filter.Tendsto f (Filter.comap Subtype.val (𝓝 x.val)) (𝓝 (f x)) :=
  hf.continuousAt.tendsto_comap_val

end Subtype

/-- **Quotient maps are stable under closed pullback.** Let `f : X → Y` be a quotient map and
`j : Y' → Y` a continuous injection. Let `g : X' → Y'` be a continuous surjection lying over `f`
through a closed map `i : X' → X`, so `f ∘ i = j ∘ g`, whose range contains `f ⁻¹' range j`.
Then `g` is a quotient map.

The model case is the restriction of `f` over a closed subset `C ⊆ Y`, with `i` and `j` the
inclusions of `f ⁻¹' C` and `C`: unlike the restriction over an open subset
(`Topology.IsQuotientMap.restrictPreimage_isOpen`), it needs the closedness of `C`, through `i`. -/
theorem Topology.IsQuotientMap.of_comp_eq_comp {X X' Y Y' : Type*} [TopologicalSpace X]
    [TopologicalSpace X'] [TopologicalSpace Y] [TopologicalSpace Y'] {f : X → Y} {g : X' → Y'}
    {i : X' → X} {j : Y' → Y} (hf : IsQuotientMap f) (hg : Continuous g)
    (hgs : Function.Surjective g) (hi : IsClosedMap i) (hj : Continuous j)
    (hji : Function.Injective j) (hcomm : f ∘ i = j ∘ g) (hrange : f ⁻¹' range j ⊆ range i) :
    IsQuotientMap g := by
  refine isQuotientMap_iff_isClosed.2 ⟨hgs, fun s ↦ ⟨fun hs ↦ hs.preimage hg, fun hs ↦ ?_⟩⟩
  have himage : f ⁻¹' (j '' s) = i '' (g ⁻¹' s) := by
    ext x
    constructor
    · rintro ⟨y, hy, hxy⟩
      obtain ⟨x', rfl⟩ := hrange ⟨y, hxy⟩
      have hgy : g x' = y := hji ((congrFun hcomm x').symm.trans hxy.symm)
      exact ⟨x', mem_preimage.2 (hgy ▸ hy), rfl⟩
    · rintro ⟨x', hx', rfl⟩
      exact ⟨g x', hx', (congrFun hcomm x').symm⟩
  have hjs : IsClosed (j '' s) := hf.isCoinducing.isClosed_preimage.1 (himage ▸ hi _ hs)
  rw [← hji.preimage_image s]
  exact hjs.preimage hj
