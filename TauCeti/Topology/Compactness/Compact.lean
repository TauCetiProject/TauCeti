/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Compactness.Compact
public import Mathlib.Topology.Compactness.SigmaCompact
public import Mathlib.Topology.Connected.Basic
public import Mathlib.Topology.DiscreteSubset
public import Mathlib.Topology.Separation.Hausdorff
import TauCeti.Topology.Separation.InvFunOn

/-!
# Compactness utilities

General lemmas about compact and σ-compact subsets of topological spaces, limits along
ultrafilters of families eventually in a compact set, families whose values tend to the
cocompact filter, whose images therefore lie in no fixed compact set, and passing from constants
valid near each point of a compact set to one constant valid on all of it. Maps converging
continuously on a compact set eventually map it into any open set containing the image under the
limit (`IsCompact.eventually_forall_mem_of_tendsto_prod_nhds`). The fibres over `w` of a closed set
`C ⊆ P × X` that near `w₀` all lie in a fixed compact set are eventually contained in every open
neighbourhood of the fibre over `w₀` (`IsClosed.eventually_preimage_prodMk_subset`).

A continuous injection on a compact set `K` restricts to a closed embedding of `K`
(`IsCompact.isClosedEmbedding_domRestrict`), so neighbourhoods of a point of `K`
(`IsCompact.exists_mem_nhds_inter_preimage_subset`) and convergence to a point of `K` of a family
eventually in `K` (`IsCompact.tendsto_nhds_of_tendsto_comp`) can be read through it.

If two functions agree off a compact set, compactness of a closed sublevel passes from one to the
other (`IsCompact.setOf_le_of_eqOn_compl`).
-/

public section

namespace TauCeti

open Filter Set Topology

variable {X : Type*} [TopologicalSpace X]

/-- Compactness of `U ∩ S` for a compact set `U` may be checked on open pieces of `U` around
each of its points. -/
theorem _root_.IsCompact.inter_of_forall_exists {U S : Set X} (hU : IsCompact U)
    (h : ∀ x ∈ U, ∃ U' ⊆ U, IsOpen U' ∧ x ∈ U' ∧ IsCompact (U' ∩ S)) : IsCompact (U ∩ S) := by
  choose! W hWU hWo hxW hWc using h
  obtain ⟨t, htU, htf, ht⟩ :=
    hU.elim_finite_subcover_image hWo fun x hx ↦ mem_biUnion hx (hxW x hx)
  have heq : U ∩ S = ⋃ x ∈ t, W x ∩ S := by
    rw [← iUnion₂_inter]
    exact subset_antisymm (inter_subset_inter_left S ht)
      (inter_subset_inter_left S (iUnion₂_subset fun x hx ↦ hWU x (htU hx)))
  rw [heq]
  exact htf.isCompact_biUnion fun x hx ↦ hWc x (htU hx)

/-- **A locally valid constant is uniform over a compact set.** Let `p a y` be a property of a
constant `a` at a point `y`, preserved when `a` moves up for a directed relation `r`. If near each
point of a compact set `K`, within `K`, some constant works, then one constant works on all of `K`.
-/
theorem _root_.IsCompact.exists_forall_of_forall_exists_eventually {α : Type*}
    {r : α → α → Prop} [IsDirected α r] [Nonempty α] {K : Set X} (hK : IsCompact K)
    {p : α → X → Prop} (hp : ∀ ⦃a b⦄, r a b → ∀ ⦃y⦄, p a y → p b y)
    (h : ∀ y ∈ K, ∃ a, ∀ᶠ z in 𝓝[K] y, p a z) : ∃ a, ∀ y ∈ K, p a y := by
  refine hK.induction_on (p := fun t ↦ ∃ a, ∀ y ∈ t, p a y)
    ⟨Classical.arbitrary α, fun _ h ↦ h.elim⟩ (fun _ _ hst ⟨a, ha⟩ ↦ ⟨a, fun y hy ↦ ha y (hst hy)⟩)
    (fun _ _ ⟨a, ha⟩ ⟨b, hb⟩ ↦ ?_) fun y hy ↦ ?_
  · obtain ⟨c, hac, hbc⟩ := directed_of r a b
    exact ⟨c, fun y hy ↦ hy.elim (fun hy ↦ hp hac (ha y hy)) fun hy ↦ hp hbc (hb y hy)⟩
  · obtain ⟨a, ha⟩ := h y hy
    exact ⟨_, ha, a, fun _ h ↦ h⟩

/-- **Connected components of a compact set are compact.** The connected component of a compact
set `K` at a point is closed in `K`, hence compact; it is empty at a point outside `K`. -/
protected theorem _root_.IsCompact.connectedComponentIn {K : Set X} (hK : IsCompact K)
    (x : X) : IsCompact (connectedComponentIn K x) := by
  by_cases hx : x ∈ K
  · have : CompactSpace K := isCompact_iff_compactSpace.1 hK
    rw [connectedComponentIn_eq_image hx]
    exact isClosed_connectedComponent.isCompact.image continuous_subtypeVal
  · rw [connectedComponentIn_eq_empty hx]
    exact isCompact_empty

/-- **A continuous injection on a compact set maps components onto components.** If `f` is
continuous and injective on a compact set `K` with values in a Hausdorff space, and `A ⊆ K`, then
`f` maps the connected component of `A` at a point `x ∈ K` onto the connected component of
`f '' A` at `f x`. Both sides are empty when `x ∉ A`. -/
theorem _root_.IsCompact.image_connectedComponentIn {Y : Type*} [TopologicalSpace Y] [T2Space Y]
    {K A : Set X} {f : X → Y} (hK : IsCompact K) (hf : ContinuousOn f K) (hinj : InjOn f K)
    (hA : A ⊆ K) {x : X} (hx : x ∈ K) :
    f '' connectedComponentIn A x = connectedComponentIn (f '' A) (f x) := by
  have : Nonempty X := ⟨x⟩
  by_cases hxA : x ∈ A
  · refine ((hf.mono hA).image_connectedComponentIn_subset hxA).antisymm fun v hv => ?_
    -- The inverse is continuous on `f '' K`, so it maps the component at `f x` back into the
    -- component at `x`.
    have hgf : LeftInvOn (Function.invFunOn f K) f K := hinj.leftInvOn_invFunOn
    have hg := ((hf.continuousOn_invFunOn_image_of_isCompact hK subset_rfl hinj (by simp)).mono
      (image_mono hA)).image_connectedComponentIn_subset (mem_image_of_mem f hxA)
    rw [hgf.image_image' hA, hgf hx] at hg
    obtain ⟨w, hwA, rfl⟩ := connectedComponentIn_subset _ _ hv
    refine ⟨w, ?_, rfl⟩
    simpa only [hgf (hA hwA)] using hg (mem_image_of_mem _ hv)
  · have hfx : f x ∉ f '' A := fun ⟨w, hwA, hw⟩ => hxA (hinj (hA hwA) hx hw ▸ hwA)
    rw [connectedComponentIn_eq_empty hxA, connectedComponentIn_eq_empty hfx, image_empty]

/-- **A continuous injection on a compact set embeds it.** If `f` is continuous and injective on
a compact set `K` with values in a Hausdorff space, then its restriction to `K` is a closed
embedding. -/
theorem _root_.IsCompact.isClosedEmbedding_domRestrict {Y : Type*} [TopologicalSpace Y] [T2Space Y]
    {K : Set X} {f : X → Y} (hK : IsCompact K) (hf : ContinuousOn f K) (hinj : InjOn f K) :
    IsClosedEmbedding (K.domRestrict f) :=
  have := isCompact_iff_compactSpace.1 hK
  hf.domRestrict.isClosedEmbedding hinj.injective

/-- **Neighbourhoods in a compact set are read through a continuous injection.** Let `f` be
continuous and injective on a compact set `K` with values in a Hausdorff space. For `x ∈ K` and a
neighbourhood `s` of `x`, there is a neighbourhood `t` of `f x` such that every point of `K` that
`f` maps into `t` lies in `s`. -/
theorem _root_.IsCompact.exists_mem_nhds_inter_preimage_subset {Y : Type*} [TopologicalSpace Y]
    [T2Space Y] {K : Set X} {f : X → Y} (hK : IsCompact K) (hf : ContinuousOn f K)
    (hinj : InjOn f K) {x : X} (hx : x ∈ K) {s : Set X} (hs : s ∈ 𝓝 x) :
    ∃ t ∈ 𝓝 (f x), K ∩ f ⁻¹' t ⊆ s := by
  -- Inside `K`, the neighbourhoods of `x` are read through `f`.
  have hs' := continuous_subtypeVal.continuousAt (x := (⟨x, hx⟩ : K)).preimage_mem_nhds hs
  rw [(hK.isClosedEmbedding_domRestrict hf hinj).isInducing.nhds_eq_comap, mem_comap] at hs'
  obtain ⟨t, ht, hts⟩ := hs'
  refine ⟨t, ht, fun p ⟨hpK, hpt⟩ ↦ hts (a := ⟨p, hpK⟩) ?_⟩
  rwa [mem_preimage, domRestrict_apply]

/-- **Convergence in a compact set is read through a continuous injection.** Let `f` be continuous
and injective on a compact set `K` with values in a Hausdorff space, and let `g` eventually take
values in `K`. If `f ∘ g` tends to `f x` for some `x ∈ K`, then `g` tends to `x`. -/
theorem _root_.IsCompact.tendsto_nhds_of_tendsto_comp {Y ι : Type*} [TopologicalSpace Y]
    [T2Space Y] {K : Set X} {f : X → Y} (hK : IsCompact K) (hf : ContinuousOn f K)
    (hinj : InjOn f K) {l : Filter ι} {g : ι → X} (hg : ∀ᶠ i in l, g i ∈ K) {x : X} (hx : x ∈ K)
    (h : Tendsto (f ∘ g) l (𝓝 (f x))) : Tendsto g l (𝓝 x) := by
  intro s hs
  obtain ⟨t, ht, hts⟩ := hK.exists_mem_nhds_inter_preimage_subset hf hinj hx hs
  have hgt : ∀ᶠ i in l, f (g i) ∈ t := by
    simpa only [Function.comp_apply] using h.eventually_mem ht
  exact (hg.and hgt).mono fun i hi ↦ hts ⟨hi.1, hi.2⟩

/-- A family that eventually lies in a compact set `s` along an ultrafilter converges along it to
a point of `s`. -/
theorem _root_.IsCompact.exists_tendsto_of_eventually_mem {ι : Type*} {s : Set X}
    (hs : IsCompact s) {U : Ultrafilter ι} {u : ι → X} (hu : ∀ᶠ i in U, u i ∈ s) :
    ∃ x ∈ s, Tendsto u U (𝓝 x) := by
  obtain ⟨x, hx, h⟩ := hs.ultrafilter_le_nhds' (U.map u) (Ultrafilter.mem_map.2 hu)
  exact ⟨x, hx, by rwa [Ultrafilter.coe_map] at h⟩

/-- If the values `u i z` at one point `z ∈ S` tend to the cocompact filter, then no compact set
contains the images `u i '' S` for every `i`. -/
theorem not_exists_isCompact_forall_mapsTo_of_tendsto_cocompact {ι α : Type*} {l : Filter ι}
    [l.NeBot] {u : ι → α → X} {S : Set α} {z : α} (hz : z ∈ S)
    (hu : Tendsto (fun i ↦ u i z) l (cocompact X)) :
    ¬ ∃ K : Set X, IsCompact K ∧ ∀ i, MapsTo (u i) S K := by
  rintro ⟨K, hK, huK⟩
  obtain ⟨i, hi⟩ := (hu.eventually hK.compl_mem_cocompact).exists
  exact hi (huK i hz)

/-- A preconnected noncompact space has no compact connected component: its only component is the
whole space. -/
theorem not_isCompact_connectedComponent [PreconnectedSpace X] [NoncompactSpace X]
    (x : X) : ¬IsCompact (connectedComponent x) := by
  rw [PreconnectedSpace.connectedComponent_eq_univ]
  exact noncompact_univ X

/-- The component in `Sᶜ` of a point of `S` is empty, so its closure is compact. -/
theorem isCompact_closure_connectedComponentIn_compl_of_mem {S : Set X} {x : X} (hx : x ∈ S) :
    IsCompact (closure (connectedComponentIn Sᶜ x)) := by
  simp [connectedComponentIn_eq_empty (notMem_compl_iff.2 hx)]

/-- A point whose component in `Sᶜ` has noncompact closure lies outside `S`. -/
theorem notMem_of_not_isCompact_closure_connectedComponentIn_compl {S : Set X} {x : X}
    (hx : ¬IsCompact (closure (connectedComponentIn Sᶜ x))) : x ∉ S :=
  fun hxS ↦ hx (isCompact_closure_connectedComponentIn_compl_of_mem hxS)

/-- The union of two σ-compact sets is σ-compact. -/
theorem _root_.IsSigmaCompact.union {s t : Set X} (hs : IsSigmaCompact s)
    (ht : IsSigmaCompact t) : IsSigmaCompact (s ∪ t) := by
  rw [union_eq_iUnion]
  exact isSigmaCompact_iUnion _ (Bool.forall_bool.2 ⟨ht, hs⟩)

/-- **Slices of a map proper on `s ×ˢ I` are proper**: if `(s ×ˢ I) ∩ H ⁻¹' K` is compact for
every compact `K ⊆ U`, then so is `s ∩ H (·, t) ⁻¹' K` for every `t ∈ I`. -/
theorem isCompact_inter_preimage_comp_prodMk_left {Y Z : Type*} [TopologicalSpace Y]
    [TopologicalSpace Z] [T1Space Z] {s : Set X} {I : Set Z} {H : X × Z → Y}
    {U : Set Y} (hHp : ∀ K : Set Y, IsCompact K → K ⊆ U → IsCompact ((s ×ˢ I) ∩ H ⁻¹' K))
    {t : Z} (ht : t ∈ I) (K : Set Y) (hK : IsCompact K) (hKU : K ⊆ U) :
    IsCompact (s ∩ (fun x ↦ H (x, t)) ⁻¹' K) := by
  have h : s ∩ (fun x ↦ H (x, t)) ⁻¹' K =
      Prod.fst '' ((s ×ˢ I) ∩ H ⁻¹' K ∩ Prod.snd ⁻¹' {t}) := by
    ext x
    constructor
    · rintro ⟨hx, hxK⟩
      exact ⟨(x, t), ⟨⟨⟨hx, ht⟩, hxK⟩, rfl⟩, rfl⟩
    · rintro ⟨⟨y, t'⟩, ⟨⟨⟨hy, -⟩, hyK⟩, rfl : t' = t⟩, rfl⟩
      exact ⟨hy, hyK⟩
  rw [h]
  exact ((hHp K hK hKU).inter_right (isClosed_singleton.preimage continuous_snd)).image
    continuous_fst

/-- **Coincidences of two maps form a compact set.** For maps `f`, `g` into a Hausdorff space,
continuous on compact sets `s` and `t`, the pairs `(x, y) ∈ s ×ˢ t` with `f x = g y` form a
compact set. -/
theorem _root_.IsCompact.prod_inter_setOf_eq {Y Z : Type*} [TopologicalSpace Y]
    [TopologicalSpace Z] [T2Space Z] {s : Set X} {t : Set Y} (hs : IsCompact s)
    (ht : IsCompact t) {f : X → Z} {g : Y → Z} (hf : ContinuousOn f s) (hg : ContinuousOn g t) :
    IsCompact (s ×ˢ t ∩ {z | f z.1 = g z.2}) := by
  have : CompactSpace (s ×ˢ t) := isCompact_iff_compactSpace.1 (hs.prod ht)
  have hf' : Continuous fun z : s ×ˢ t ↦ f z.val.1 :=
    (hf.comp continuousOn_fst fun _ hz ↦ (mem_prod.1 hz).1).domRestrict
  have hg' : Continuous fun z : s ×ˢ t ↦ g z.val.2 :=
    (hg.comp continuousOn_snd fun _ hz ↦ (mem_prod.1 hz).2).domRestrict
  convert (isClosed_eq hf' hg').isCompact.image continuous_subtypeVal using 1
  ext z
  exact ⟨fun hz ↦ ⟨⟨z, hz.1⟩, hz.2, rfl⟩, by rintro ⟨z, hz, rfl⟩; exact ⟨z.property, hz⟩⟩

/-- The points of a compact set `C` that a map continuous on `C` sends into a closed set `K` form
a compact set. -/
theorem _root_.IsCompact.inter_preimage {Y : Type*} [TopologicalSpace Y] {C : Set X}
    {K : Set Y} {Φ : X → Y} (hC : IsCompact C) (hΦ : ContinuousOn Φ C) (hK : IsClosed K) :
    IsCompact (C ∩ Φ ⁻¹' K) := by
  have : CompactSpace C := isCompact_iff_compactSpace.1 hC
  rw [← Subtype.image_preimage_coe]
  exact (hK.preimage hΦ.domRestrict).isCompact.image continuous_subtypeVal

/-- **Solutions on an isolating set are compact.** Let `Φ` be a continuous family of maps
`X → Y` parametrized by a compact space `P`, and let `U` be a set with compact closure on whose
frontier no map of the family takes the value `y`. Then the solutions in `P × U` of
`Φ (p, x) = y` form a compact set. -/
theorem isCompact_setOf_apply_eq_of_frontier {P Y : Type*} [TopologicalSpace P] [CompactSpace P]
    [TopologicalSpace Y] [T1Space Y] {U : Set X} (hU : IsCompact (closure U))
    {Φ : P × X → Y} (hΦc : Continuous Φ) {y : Y} (hΦ : ∀ p, ∀ x ∈ frontier U, Φ (p, x) ≠ y) :
    IsCompact {z : P × U | Φ (z.1, z.2) = y} := by
  have hK : IsCompact ((univ : Set P) ×ˢ closure U ∩ Φ ⁻¹' {y}) :=
    (isCompact_univ.prod hU).inter_right (isClosed_singleton.preimage hΦc)
  let j : P × U → P × X := Prod.map id Subtype.val
  have hj : IsInducing j := IsInducing.id.prodMap IsInducing.subtypeVal
  -- The solutions in `P × closure U` avoid `P × frontier U`, so they lie in `P × U`.
  have hsub : (univ : Set P) ×ˢ closure U ∩ Φ ⁻¹' {y} ⊆ range j := by
    rintro ⟨p, x⟩ ⟨⟨-, hxc⟩, hxy⟩
    have hxU : x ∈ U := by
      by_contra hxU
      exact hΦ p x ⟨hxc, fun h ↦ hxU (interior_subset h)⟩ hxy
    exact ⟨(p, ⟨x, hxU⟩), rfl⟩
  convert (hj.isCompact_preimage_iff hsub).2 hK using 1
  ext ⟨p, x⟩
  simp [j, subset_closure x.property]

/-- A compact set contains no infinite subset all of whose subsets are closed: such a subset would
be closed, hence compact, and discrete. -/
theorem _root_.IsCompact.finite_of_forall_isClosed {K S : Set X}
    (hK : IsCompact K) (hSK : S ⊆ K) (hS : ∀ T ⊆ S, IsClosed T) : S.Finite := by
  have hd : IsDiscrete S :=
    isDiscrete_iff_forall_mem_exists_isClosed.2 fun T hT ↦
      ⟨T, hS T hT, Set.inter_eq_left.2 hT⟩
  exact (hK.of_isClosed_subset (hS S subset_rfl) hSK).finite hd

/-- In a compact Hausdorff space `X`, the punctured space `{x : X // x ≠ x₀}` is compact if and
only if `x₀` is an isolated point (`{x₀}` is open). -/
theorem compactSpace_complSingleton_iff_isOpen_singleton [CompactSpace X] [T2Space X] {x₀ : X} :
    CompactSpace {x : X // x ≠ x₀} ↔ IsOpen ({x₀} : Set X) := by
  refine ⟨fun _ ↦ ?_, fun hx ↦ isCompact_iff_compactSpace.mp hx.isClosed_compl.isCompact⟩
  rw [← isClosed_compl_iff]
  have hrange : range (Subtype.val : {x : X // x ≠ x₀} → X) = {x₀}ᶜ := by ext; simp
  rw [← hrange]
  exact (isCompact_range continuous_subtypeVal).isClosed

/-- In a compact space `X`, the inclusion of `{x : X // x ≠ x₀}` into `X` tends to `x₀` along the
cocompact filter. -/
theorem tendsto_subtypeVal_cocompact_nhds [CompactSpace X] (x₀ : X) :
    Tendsto (Subtype.val : {x : X // x ≠ x₀} → X) (cocompact {x : X // x ≠ x₀}) (𝓝 x₀) := by
  rw [hasBasis_cocompact.tendsto_left_iff]
  intro N hN
  obtain ⟨U, hU₁, hU₂, hU₃⟩ := mem_nhds_iff.mp hN
  refine ⟨Subtype.val ⁻¹' Uᶜ, ?_, by simpa using (mapsTo_preimage Subtype.val U).mono_right hU₁⟩
  have hsub : Uᶜ ⊆ range (Subtype.val : {x : X // x ≠ x₀} → X) := fun x hx ↦
    ⟨⟨x, fun h ↦ hx (h ▸ hU₃)⟩, rfl⟩
  rw [Topology.IsEmbedding.subtypeVal.isCompact_iff, image_preimage_eq_iff.mpr hsub]
  exact hU₂.isClosed_compl.isCompact

/-- In a T₀ space, a compact closed subset `S` is contained in an open subset `U` as soon as every
closed point in `S` belongs to `U`. -/
theorem _root_.IsCompact.subset_of_isClosed_of_forall_isClosed_singleton [T0Space X]
    {S U : Set X} (hSc : IsCompact S) (hS : IsClosed S) (hU : IsOpen U)
    (h : ∀ z ∈ S, IsClosed ({z} : Set X) → z ∈ U) : S ⊆ U := by
  intro z hzS
  by_contra hzU
  have : CompactSpace S := isCompact_iff_compactSpace.1 hSc
  obtain ⟨⟨w, hwS⟩, hwU, hwcl⟩ :=
    (hU.preimage continuous_subtypeVal).isClosed_compl.exists_closed_singleton ⟨⟨z, hzS⟩, hzU⟩
  exact hwU (h w hwS (by simpa [image_singleton] using
    hS.isClosedEmbedding_subtypeVal.isClosedMap _ hwcl))

/-- If maps `f i` converge to `g` continuously at every point of a compact set `A`, that is
`f p.1 p.2 → g a` as `p → (l, a)`, and `g` maps `A` into an open set `t`, then eventually along
`l` the map `f i` maps `A` into `t`. -/
theorem _root_.IsCompact.eventually_forall_mem_of_tendsto_prod_nhds {Y ι : Type*}
    [TopologicalSpace Y] {l : Filter ι} {f : ι → X → Y} {g : X → Y} {A : Set X} {t : Set Y}
    (hA : IsCompact A) (ht : IsOpen t)
    (hconv : ∀ a ∈ A, Tendsto (fun p : ι × X ↦ f p.1 p.2) (l ×ˢ 𝓝 a) (𝓝 (g a)))
    (hmem : ∀ a ∈ A, g a ∈ t) : ∀ᶠ i in l, ∀ a ∈ A, f i a ∈ t := by
  have h := hA.mem_prod_nhdsSet_of_forall (s := {p : ι × X | f p.1 p.2 ∈ t})
    fun a ha ↦ (hconv a ha).eventually (ht.mem_nhds (hmem a ha))
  exact (Filter.Eventually.curry h).mono fun _ hi ↦ hi.self_of_nhdsSet

/-- **Fibres of a closed set vary upper semicontinuously.** Let `C ⊆ P × X` be closed, and suppose
that for `w` near `w₀` the fibre `{x | (w, x) ∈ C}` lies in a fixed compact set `K`. Then every
open set `U` containing the fibre over `w₀` contains the fibres over all `w` near `w₀`. -/
theorem _root_.IsClosed.eventually_preimage_prodMk_subset {P : Type*} [TopologicalSpace P]
    {C : Set (P × X)} (hC : IsClosed C) {K : Set X} (hK : IsCompact K) {w₀ : P}
    (hKC : ∀ᶠ w in 𝓝 w₀, Prod.mk w ⁻¹' C ⊆ K) {U : Set X} (hU : IsOpen U)
    (hCU : Prod.mk w₀ ⁻¹' C ⊆ U) : ∀ᶠ w in 𝓝 w₀, Prod.mk w ⁻¹' C ⊆ U := by
  -- On the compact set `K \ U` the fibre over `w₀` is empty, hence so are nearby fibres.
  have hev : ∀ᶠ w in 𝓝 w₀, ∀ x ∈ K \ U, (w, x) ∉ C :=
    (hK.diff hU).eventually_forall_of_forall_eventually fun x hx ↦
      hC.isOpen_compl.mem_nhds fun h ↦ hx.2 (hCU h)
  filter_upwards [hKC, hev] with w hwK hwU x hx
  by_contra hxU
  exact hwU x ⟨hwK hx, hxU⟩ hx

section TubeLemma

variable {α E P : Type*} [TopologicalSpace α] [CompactSpace α] [TopologicalSpace E]
  [TopologicalSpace P] {ι : α → P} {W : Set (E × P)}

/-- If `W` is open and `ι` is continuous on a compact space, the set of parameters `x` with
`{x} × ι(α) ⊆ W` is open. -/
theorem isOpen_forall_prodMk_mem (hι : Continuous ι) (hW : IsOpen W) :
    IsOpen {x : E | ∀ y, (x, ι y) ∈ W} :=
  isOpen_iff_eventually.2 fun _ hx₀ ↦
    ((isCompact_range hι).eventually_forall_of_forall_eventually (P := fun x p ↦ (x, p) ∈ W)
      (Set.forall_mem_range.2 fun y ↦ hW.mem_nhds (hx₀ y))).mono
        fun _ h y ↦ h _ (Set.mem_range_self y)

end TubeLemma

/-- **Compact sublevels survive modification on a compact set.** If `g` agrees with `f` off a
compact set `K`, the sublevel of `f` at `c` is compact and the sublevel of `g` at `c` is closed,
then the sublevel of `g` at `c` is compact: it lies in the union of the sublevel of `f` and `K`. -/
theorem _root_.IsCompact.setOf_le_of_eqOn_compl {α : Type*} [LE α] {f g : X → α} {K : Set X}
    {c : α} (hf : IsCompact {x | f x ≤ c}) (hK : IsCompact K) (hfg : EqOn f g Kᶜ)
    (hg : IsClosed {x | g x ≤ c}) : IsCompact {x | g x ≤ c} := by
  refine (hf.union hK).of_isClosed_subset hg fun x hx ↦ ?_
  by_cases hxK : x ∈ K
  · exact Or.inr hxK
  · refine Or.inl ?_
    rw [mem_ofPred_eq, hfg hxK]
    exact hx

end TauCeti

end
