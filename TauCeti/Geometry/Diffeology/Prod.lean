/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.ConstMulAction
public import TauCeti.Geometry.Diffeology.Basic
public import TauCeti.Geometry.Diffeology.Quotient
import Mathlib.Topology.CompactOpen
import Mathlib.Topology.WithTopology

/-!
# Product diffeologies

This file equips the product `X × Y` of two diffeological spaces with the product diffeology: a
map from a Cartesian space to `X × Y` is a plot exactly when both of its components are plots.
The projections are smooth, and a map into the product is smooth exactly when both of its
components are, so this is the product in the category of diffeological spaces.

A product of two subductions is a subduction. In particular the product of two quotient
diffeologies is the quotient diffeology of the product, which is how products of finite
quotient charts `U / G × V / H` are presented.

The D-topology of a product is in general strictly finer than the product of the D-topologies, so
compatibility of a topology with its D-topology does not pass to arbitrary products. It does,
however, commute with products whenever one factor's D-topology is locally compact: first `𝔼ⁿ × X`
always has the product topology as its D-topology because `𝔼ⁿ` is locally compact and `𝔼ᵐ × 𝔼ⁿ`
carries the smooth normed-space diffeology, and currying into the compact-open mapping space then
extends this to any locally compact factor. Compatibility is also recorded for products of orbit
spaces when the groups act by homeomorphisms and the D-topology of the product of the ambient
spaces is the product topology.

## Main declarations

* `TauCeti.Diffeology.instDiffeologicalSpaceProd`: the product diffeology, characterized by
  `TauCeti.Diffeology.isPlot_prod_iff`.
* `TauCeti.Diffeology.dSmooth_prodMk_iff`: the universal property of the product.
* `TauCeti.Diffeology.IsSubduction.prodMap`: a product of subductions is a subduction.
* `TauCeti.Diffeology.dTopology_prod_le`: the D-topology of a product is finer than the product of
  the D-topologies.
* `TauCeti.Diffeology.dTopology_euclideanSpace_prod`: the D-topology of `𝔼ⁿ × X` is always the
  product topology.
* `TauCeti.Diffeology.dTopology_prod_of_locallyCompactSpace_right`,
  `TauCeti.Diffeology.dTopology_prod_of_locallyCompactSpace_left`: the D-topology of `X × Y` is
  the product of the D-topologies when one factor's D-topology is locally compact.
* `TauCeti.Diffeology.instIsDTopologyCompatibleProdOfLocallyCompactSpaceRight`,
  `TauCeti.Diffeology.instIsDTopologyCompatibleProdOfLocallyCompactSpaceLeft`: D-topology
  compatibility for products with a locally compact factor.
* `TauCeti.Diffeology.instIsDTopologyCompatibleProdOrbitRelQuotient`: the D-topology of a product
  of orbit spaces is the product of the quotient topologies, for actions by homeomorphisms on
  spaces whose product has the product topology as its D-topology.

## References

* P. Iglesias-Zemmour, *Diffeology*, Mathematical Surveys and Monographs **185**, American
  Mathematical Society (2013), Article 1.55 for product diffeologies and Chapter 2 for the
  D-topology.
* J. D. Christensen, G. Sinnamon and E. Wu, *The D-topology for diffeological spaces*, Pacific J.
  Math. **272** (2014), 87–110, Lemma 4.1 and Theorem 4.12 for products with locally compact
  factors.
-/

public noncomputable section

open Function Set
open scoped ContDiff Topology

namespace TauCeti.Diffeology

local macro:max "𝔼" noWs n:superscript(term) : term =>
  `(EuclideanSpace ℝ (Fin $(⟨n.raw[0]⟩)))

variable {X Y Z Q R : Type*} [DiffeologicalSpace X] [DiffeologicalSpace Y] [DiffeologicalSpace Z]

/-! ### The product diffeology -/

/-- The product diffeology: a map into a product is a plot exactly when both of its components
are plots. -/
instance instDiffeologicalSpaceProd : DiffeologicalSpace (X × Y) :=
  DiffeologicalSpace.ofCorePlotsOn {
    isPlotOn := fun {_ u} _ p ↦ IsPlotOn u (Prod.fst ∘ p) ∧ IsPlotOn u (Prod.snd ∘ p)
    isPlotOn_congr := fun _ _ _ h ↦
      ⟨fun hp ↦ ⟨hp.1.congr h.comp_left, hp.2.congr h.comp_left⟩,
        fun hp ↦ ⟨hp.1.congr h.symm.comp_left, hp.2.congr h.symm.comp_left⟩⟩
    isPlot := fun p ↦ _root_.Diffeology.IsPlot (Prod.fst ∘ p) ∧
      _root_.Diffeology.IsPlot (Prod.snd ∘ p)
    isPlotOn_univ := by simp only [isPlotOn_univ_iff, implies_true]
    isPlot_const := fun _ ↦ ⟨_root_.Diffeology.isPlot_const, _root_.Diffeology.isPlot_const⟩
    isPlotOn_reparam := by
      intro n m u v _ _ p f h hp hf
      exact ⟨hp.1.comp_contDiffOn hf h, hp.2.comp_contDiffOn hf h⟩
    locality := fun _ _ hp ↦
      ⟨isPlotOn_of_locally fun z hz ↦
          let ⟨v, hv, hzv, h⟩ := hp z hz
          ⟨v, hv, hzv, h.1⟩,
        isPlotOn_of_locally fun z hz ↦
          let ⟨v, hv, hzv, h⟩ := hp z hz
          ⟨v, hv, hzv, h.2⟩⟩ }

/-- A map into a product is a plot exactly when both of its components are plots. -/
theorem isPlot_prod_iff {n : ℕ} {p : 𝔼ⁿ → X × Y} :
    _root_.Diffeology.IsPlot p ↔
      _root_.Diffeology.IsPlot (Prod.fst ∘ p) ∧ _root_.Diffeology.IsPlot (Prod.snd ∘ p) :=
  Iff.rfl

/-- A map into a product is a plot on a subset exactly when both of its components are. -/
theorem isPlotOn_prod_iff {n : ℕ} {u : Set (𝔼ⁿ)} {p : 𝔼ⁿ → X × Y} :
    IsPlotOn u p ↔ IsPlotOn u (Prod.fst ∘ p) ∧ IsPlotOn u (Prod.snd ∘ p) :=
  ⟨fun hp ↦ ⟨isPlotOn_iff.mpr fun _ hfu hf ↦ (isPlot_prod_iff.mp (hp.isPlot_comp hfu hf)).1,
      isPlotOn_iff.mpr fun _ hfu hf ↦ (isPlot_prod_iff.mp (hp.isPlot_comp hfu hf)).2⟩,
    fun hp ↦ isPlotOn_iff.mpr fun _ hfu hf ↦
      isPlot_prod_iff.mpr ⟨hp.1.isPlot_comp hfu hf, hp.2.isPlot_comp hfu hf⟩⟩

/-- The first projection of a product is smooth. -/
@[fun_prop]
theorem dSmooth_fst : _root_.Diffeology.DSmooth (Prod.fst : X × Y → X) :=
  fun _ _ hp ↦ (isPlot_prod_iff.mp hp).1

/-- The second projection of a product is smooth. -/
@[fun_prop]
theorem dSmooth_snd : _root_.Diffeology.DSmooth (Prod.snd : X × Y → Y) :=
  fun _ _ hp ↦ (isPlot_prod_iff.mp hp).2

/-- A map into a product is smooth if both of its components are. -/
@[fun_prop]
theorem _root_.Diffeology.DSmooth.prodMk {f : Z → X} {g : Z → Y}
    (hf : _root_.Diffeology.DSmooth f) (hg : _root_.Diffeology.DSmooth g) :
    _root_.Diffeology.DSmooth fun z ↦ (f z, g z) :=
  fun n p hp ↦ isPlot_prod_iff.mpr ⟨hf n p hp, hg n p hp⟩

/-- The universal property of the product diffeology: a map into a product is smooth exactly when
both of its components are. -/
@[simp]
theorem dSmooth_prodMk_iff {f : Z → X} {g : Z → Y} :
    _root_.Diffeology.DSmooth (fun z ↦ (f z, g z)) ↔
      _root_.Diffeology.DSmooth f ∧ _root_.Diffeology.DSmooth g :=
  ⟨fun h ↦ ⟨dSmooth_fst.comp h, dSmooth_snd.comp h⟩, fun h ↦ h.1.prodMk h.2⟩

/-- A product of smooth maps is smooth. -/
@[fun_prop]
theorem _root_.Diffeology.DSmooth.prodMap [DiffeologicalSpace Q] [DiffeologicalSpace R]
    {f : X → Q} {g : Y → R} (hf : _root_.Diffeology.DSmooth f)
    (hg : _root_.Diffeology.DSmooth g) : _root_.Diffeology.DSmooth (Prod.map f g) :=
  (hf.comp dSmooth_fst).prodMk (hg.comp dSmooth_snd)

/-- Swapping the factors of a product is smooth. -/
@[fun_prop]
theorem dSmooth_swap : _root_.Diffeology.DSmooth (Prod.swap : X × Y → Y × X) :=
  dSmooth_snd.prodMk dSmooth_fst

/-! ### Products of subductions -/

/-- A product of subductions is a subduction. -/
theorem IsSubduction.prodMap [DiffeologicalSpace Q] [DiffeologicalSpace R] {q : X → Q}
    {r : Y → R} (hq : IsSubduction q) (hr : IsSubduction r) :
    IsSubduction (Prod.map q r) where
  surjective := hq.surjective.prodMap hr.surjective
  dSmooth := hq.dSmooth.prodMap hr.dSmooth
  locallyLifts {_ p} hp := locallyLifts_iff.mpr fun z _ ↦ by
    obtain ⟨v, hv, hzv, -, a, ha, hqa⟩ :=
      locallyLifts_iff.mp (hq.locallyLifts (isPlot_prod_iff.mp hp).1) z (mem_univ z)
    obtain ⟨w, hw, hzw, -, b, hb, hrb⟩ :=
      locallyLifts_iff.mp (hr.locallyLifts (isPlot_prod_iff.mp hp).2) z (mem_univ z)
    -- Near `z`, the two components lift separately, and the pair of lifts lifts `p`.
    refine ⟨v ∩ w, hv.inter hw, ⟨hzv, hzw⟩, subset_univ _, fun x ↦ (a x, b x),
      isPlotOn_prod_iff.mpr ⟨ha.mono inter_subset_left, hb.mono inter_subset_right⟩,
      fun x hx ↦ Prod.ext (hqa hx.1) (hrb hx.2)⟩

/-- The product of the projections onto two quotients is a subduction: the product of two
quotient diffeologies is the quotient diffeology of the product. -/
theorem isSubduction_prodMap_quotient_mk (s : Setoid X) (t : Setoid Y) :
    IsSubduction (Prod.map (Quotient.mk s) (Quotient.mk t)) :=
  (isSubduction_quotient_mk s).prodMap (isSubduction_quotient_mk t)

/-! ### D-topologies -/

/-- The D-topology of a product is finer than the product of the D-topologies. -/
theorem dTopology_prod_le :
    (_root_.Diffeology.dTopology : TopologicalSpace (X × Y)) ≤
      @instTopologicalSpaceProd X Y _root_.Diffeology.dTopology _root_.Diffeology.dTopology :=
  le_inf (continuous_iff_le_induced.mp dSmooth_fst.continuous)
    (continuous_iff_le_induced.mp dSmooth_snd.continuous)

section NormedSpace

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [DiffeologicalSpace E]
  [_root_.Diffeology.IsContDiffCompatible E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [DiffeologicalSpace F] [_root_.Diffeology.IsContDiffCompatible F]

/-- The product diffeology on a product of normed spaces carrying the diffeology of smooth maps is
again the diffeology of smooth maps. -/
instance instIsContDiffCompatibleProd : _root_.Diffeology.IsContDiffCompatible (E × F) where
  isPlot_iff {_ _} := by
    rw [isPlot_prod_iff, _root_.Diffeology.IsContDiffCompatible.isPlot_iff,
      _root_.Diffeology.IsContDiffCompatible.isPlot_iff, contDiff_prod_iff]

/-- For finite-dimensional normed spaces carrying the diffeology of smooth maps, the D-topology of
the product diffeology is the product topology. -/
instance instIsDTopologyCompatibleProd [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] :
    _root_.Diffeology.IsDTopologyCompatible (E × F) where
  dTop_eq := by
    -- The D-topology of the normed-space diffeology is by construction the norm topology.
    rw [NormedSpace.isContDiffCompatible_iff_eq_toDiffeology.mp instIsContDiffCompatibleProd]
    rfl

end NormedSpace

section LocallyCompact

/-- For every Cartesian space `𝔼ⁿ` and diffeological space `X`, the D-topology of `𝔼ⁿ × X` is the
product of the Euclidean topology and the D-topology of `X`. -/
theorem dTopology_euclideanSpace_prod {n : ℕ} :
    (_root_.Diffeology.dTopology : TopologicalSpace (𝔼ⁿ × X)) =
      @instTopologicalSpaceProd (𝔼ⁿ) X inferInstance _root_.Diffeology.dTopology := by
  refine le_antisymm dTopology_prod_le ?_
  have hslice (x : WithTopology X _root_.Diffeology.dTopology) :
      Continuous fun u : 𝔼ⁿ ↦
        WithTopology.toTopology (_root_.Diffeology.dTopology : TopologicalSpace (𝔼ⁿ × X))
          (u, x.ofTopology) := by
    let : TopologicalSpace (𝔼ⁿ × X) := _root_.Diffeology.dTopology
    exact (WithTopology.continuous_toTopology _).comp
      (_root_.Diffeology.dSmooth_id.prodMk
        (_root_.Diffeology.dSmooth_const (y := x.ofTopology))).continuous
  let H : WithTopology X _root_.Diffeology.dTopology →
      C(𝔼ⁿ, WithTopology (𝔼ⁿ × X) _root_.Diffeology.dTopology) := fun x ↦ ⟨_, hslice x⟩
  have hH : Continuous H := by
    refine (continuous_coinduced_dom.trans continuous_dTopology_dom_iff).mpr fun m q hq ↦ ?_
    refine ContinuousMap.continuous_of_continuous_uncurry
      (fun v ↦ H (WithTopology.toTopology _ (q v))) ?_
    have hsm : _root_.Diffeology.DSmooth fun vu : 𝔼ᵐ × 𝔼ⁿ ↦ (vu.2, q vu.1) :=
      dSmooth_snd.prodMk (hq.dSmooth.comp dSmooth_fst)
    have hc := hsm.continuous
    rw [_root_.Diffeology.IsDTopologyCompatible.dTop_eq (𝔼ᵐ × 𝔼ⁿ)] at hc
    let : TopologicalSpace (𝔼ⁿ × X) := _root_.Diffeology.dTopology
    exact (WithTopology.continuous_toTopology _).comp hc
  have hunc : Continuous fun xu : WithTopology X _root_.Diffeology.dTopology × 𝔼ⁿ ↦
      WithTopology.toTopology (_root_.Diffeology.dTopology : TopologicalSpace (𝔼ⁿ × X))
        (xu.2, xu.1.ofTopology) :=
    ContinuousMap.continuous_uncurry_of_continuous ⟨H, hH⟩
  let : TopologicalSpace X := _root_.Diffeology.dTopology
  rw [TopologicalSpace.le_def]
  intro s hs
  have hemb : Continuous fun ux : 𝔼ⁿ × X ↦
      (WithTopology.toTopology _root_.Diffeology.dTopology ux.2, ux.1) :=
    ((WithTopology.continuous_toTopology _).comp continuous_snd).prodMk continuous_fst
  exact hemb.isOpen_preimage _ (hunc.isOpen_preimage _
    ((WithTopology.isOpen_iff (s := WithTopology.ofTopology ⁻¹' s) _).mpr hs))

/-- If the D-topology of `Y` is locally compact, then the D-topology of `X × Y` is the product of
the D-topologies of `X` and `Y`. -/
theorem dTopology_prod_of_locallyCompactSpace_right
    (hY : @LocallyCompactSpace Y _root_.Diffeology.dTopology) :
    (_root_.Diffeology.dTopology : TopologicalSpace (X × Y)) =
      @instTopologicalSpaceProd X Y _root_.Diffeology.dTopology _root_.Diffeology.dTopology := by
  refine le_antisymm dTopology_prod_le ?_
  have : LocallyCompactSpace (WithTopology Y _root_.Diffeology.dTopology) := by
    let : TopologicalSpace Y := _root_.Diffeology.dTopology
    exact (Homeomorph.isClosedEmbedding
      ⟨WithTopology.equiv Y _, WithTopology.continuous_ofTopology _,
        WithTopology.continuous_toTopology _⟩).locallyCompactSpace
  have hslice (x : WithTopology X _root_.Diffeology.dTopology) :
      Continuous fun y : WithTopology Y _root_.Diffeology.dTopology ↦
        WithTopology.toTopology (_root_.Diffeology.dTopology : TopologicalSpace (X × Y))
          (x.ofTopology, y.ofTopology) := by
    let : TopologicalSpace Y := _root_.Diffeology.dTopology
    let : TopologicalSpace (X × Y) := _root_.Diffeology.dTopology
    exact (WithTopology.continuous_toTopology _).comp <|
      ((_root_.Diffeology.dSmooth_const (y := x.ofTopology)).prodMk
        (_root_.Diffeology.dSmooth_id (X := Y))).continuous.comp
        (WithTopology.continuous_ofTopology _)
  let G : WithTopology X _root_.Diffeology.dTopology →
      C(WithTopology Y _root_.Diffeology.dTopology,
        WithTopology (X × Y) _root_.Diffeology.dTopology) := fun x ↦ ⟨_, hslice x⟩
  have hG : Continuous G := by
    refine (continuous_coinduced_dom.trans continuous_dTopology_dom_iff).mpr fun n p hp ↦ ?_
    refine ContinuousMap.continuous_of_continuous_uncurry
      (fun u ↦ G (WithTopology.toTopology _ (p u))) ?_
    let : TopologicalSpace Y := _root_.Diffeology.dTopology
    let : TopologicalSpace (X × Y) := _root_.Diffeology.dTopology
    have hc := (hp.dSmooth.prodMap (_root_.Diffeology.dSmooth_id (X := Y))).continuous
    rw [dTopology_euclideanSpace_prod] at hc
    have hmap : Continuous fun uy : 𝔼ⁿ × WithTopology Y _root_.Diffeology.dTopology ↦
        (uy.1, uy.2.ofTopology) :=
      continuous_fst.prodMk ((WithTopology.continuous_ofTopology _).comp continuous_snd)
    exact (WithTopology.continuous_toTopology _).comp (hc.comp hmap)
  have hunc : Continuous fun xy : WithTopology X _root_.Diffeology.dTopology ×
        WithTopology Y _root_.Diffeology.dTopology ↦
      WithTopology.toTopology (_root_.Diffeology.dTopology : TopologicalSpace (X × Y))
        (xy.1.ofTopology, xy.2.ofTopology) :=
    ContinuousMap.continuous_uncurry_of_continuous ⟨G, hG⟩
  let : TopologicalSpace X := _root_.Diffeology.dTopology
  let : TopologicalSpace Y := _root_.Diffeology.dTopology
  rw [TopologicalSpace.le_def]
  intro s hs
  have hemb : Continuous fun xy : X × Y ↦
      (WithTopology.toTopology _root_.Diffeology.dTopology xy.1,
        WithTopology.toTopology _root_.Diffeology.dTopology xy.2) :=
    (WithTopology.continuous_toTopology _).prodMap (WithTopology.continuous_toTopology _)
  exact hemb.isOpen_preimage _ (hunc.isOpen_preimage _
    ((WithTopology.isOpen_iff (s := WithTopology.ofTopology ⁻¹' s) _).mpr hs))

/-- For every diffeological space `X` and Cartesian space `𝔼ⁿ`, the D-topology of `X × 𝔼ⁿ` is the
product of the D-topology of `X` and the Euclidean topology. -/
theorem dTopology_prod_euclideanSpace {n : ℕ} :
    (_root_.Diffeology.dTopology : TopologicalSpace (X × 𝔼ⁿ)) =
      @instTopologicalSpaceProd X (𝔼ⁿ) _root_.Diffeology.dTopology inferInstance :=
  dTopology_prod_of_locallyCompactSpace_right (inferInstance : LocallyCompactSpace (𝔼ⁿ))

/-- If the D-topology of `X` is locally compact, then the D-topology of `X × Y` is the product of
the D-topologies of `X` and `Y`. -/
theorem dTopology_prod_of_locallyCompactSpace_left
    (hX : @LocallyCompactSpace X _root_.Diffeology.dTopology) :
    (_root_.Diffeology.dTopology : TopologicalSpace (X × Y)) =
      @instTopologicalSpaceProd X Y _root_.Diffeology.dTopology _root_.Diffeology.dTopology := by
  refine le_antisymm dTopology_prod_le ?_
  let : TopologicalSpace X := _root_.Diffeology.dTopology
  let : TopologicalSpace Y := _root_.Diffeology.dTopology
  have hswap := (dSmooth_swap (X := Y) (Y := X)).continuous
  rw [dTopology_prod_of_locallyCompactSpace_right hX] at hswap
  obtain ⟨hswap⟩ := hswap
  rw [TopologicalSpace.le_def]
  intro s hs
  exact continuous_swap.isOpen_preimage _ (hswap s hs)

/-- When `Y` carries a locally compact topology compatible with its D-topology, the D-topology of
`X × Y` is the product of the D-topology of `X` with the topology of `Y`, without requiring a
topological structure on `X` beforehand. -/
theorem dTopology_prod_eq_of_isDTopologyCompatible_right [TopologicalSpace Y]
    [_root_.Diffeology.IsDTopologyCompatible Y] [LocallyCompactSpace Y] :
    (_root_.Diffeology.dTopology : TopologicalSpace (X × Y)) =
      @instTopologicalSpaceProd X Y _root_.Diffeology.dTopology ‹TopologicalSpace Y› := by
  have hY : @LocallyCompactSpace Y _root_.Diffeology.dTopology := by
    rwa [_root_.Diffeology.IsDTopologyCompatible.dTop_eq Y]
  rw [dTopology_prod_of_locallyCompactSpace_right hY,
    _root_.Diffeology.IsDTopologyCompatible.dTop_eq Y]

/-- When `X` carries a locally compact topology compatible with its D-topology, the D-topology of
`X × Y` is the product of the topology of `X` with the D-topology of `Y`, without requiring a
topological structure on `Y` beforehand. -/
theorem dTopology_prod_eq_of_isDTopologyCompatible_left [TopologicalSpace X]
    [_root_.Diffeology.IsDTopologyCompatible X] [LocallyCompactSpace X] :
    (_root_.Diffeology.dTopology : TopologicalSpace (X × Y)) =
      @instTopologicalSpaceProd X Y ‹TopologicalSpace X› _root_.Diffeology.dTopology := by
  have hX : @LocallyCompactSpace X _root_.Diffeology.dTopology := by
    rwa [_root_.Diffeology.IsDTopologyCompatible.dTop_eq X]
  rw [dTopology_prod_of_locallyCompactSpace_left hX,
    _root_.Diffeology.IsDTopologyCompatible.dTop_eq X]

/-- If `X` and `Y` carry topologies compatible with their D-topologies and `Y` is locally compact,
then the D-topology of `X × Y` is the product topology. -/
instance instIsDTopologyCompatibleProdOfLocallyCompactSpaceRight [TopologicalSpace X]
    [_root_.Diffeology.IsDTopologyCompatible X] [TopologicalSpace Y]
    [_root_.Diffeology.IsDTopologyCompatible Y] [LocallyCompactSpace Y] :
    _root_.Diffeology.IsDTopologyCompatible (X × Y) where
  dTop_eq := by
    rw [dTopology_prod_eq_of_isDTopologyCompatible_right,
      _root_.Diffeology.IsDTopologyCompatible.dTop_eq X]

/-- If `X` and `Y` carry topologies compatible with their D-topologies and `X` is locally compact,
then the D-topology of `X × Y` is the product topology. -/
instance instIsDTopologyCompatibleProdOfLocallyCompactSpaceLeft [TopologicalSpace X]
    [_root_.Diffeology.IsDTopologyCompatible X] [LocallyCompactSpace X] [TopologicalSpace Y]
    [_root_.Diffeology.IsDTopologyCompatible Y] :
    _root_.Diffeology.IsDTopologyCompatible (X × Y) where
  dTop_eq := by
    rw [dTopology_prod_eq_of_isDTopologyCompatible_left,
      _root_.Diffeology.IsDTopologyCompatible.dTop_eq Y]

end LocallyCompact

/-- If the D-topology of `X × Y` is the product topology and the projections onto the quotients
are open quotient maps, then the D-topology of the product of the quotient diffeologies is the
product of the quotient topologies. -/
theorem isDTopologyCompatible_prod_quotient [TopologicalSpace X] [TopologicalSpace Y]
    [_root_.Diffeology.IsDTopologyCompatible (X × Y)] {s : Setoid X} {t : Setoid Y}
    (hs : IsOpenQuotientMap (Quotient.mk s)) (ht : IsOpenQuotientMap (Quotient.mk t)) :
    _root_.Diffeology.IsDTopologyCompatible (Quotient s × Quotient t) :=
  (isSubduction_prodMap_quotient_mk s t).isDTopologyCompatible (hs.prodMap ht).isQuotientMap

/-- The D-topology of a product of orbit spaces is the product of the quotient topologies, when
the groups act by homeomorphisms and the D-topology of the product of the spaces is the product
topology. -/
instance instIsDTopologyCompatibleProdOrbitRelQuotient {G H : Type*} [Group G] [Group H]
    [MulAction G X] [MulAction H Y] [TopologicalSpace X] [TopologicalSpace Y]
    [ContinuousConstSMul G X] [ContinuousConstSMul H Y]
    [_root_.Diffeology.IsDTopologyCompatible (X × Y)] :
    _root_.Diffeology.IsDTopologyCompatible
      (MulAction.orbitRel.Quotient G X × MulAction.orbitRel.Quotient H Y) :=
  isDTopologyCompatible_prod_quotient MulAction.isOpenQuotientMap_quotientMk
    MulAction.isOpenQuotientMap_quotientMk

end TauCeti.Diffeology
