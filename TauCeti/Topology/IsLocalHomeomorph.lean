/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Finprod
public import Mathlib.Topology.Algebra.Support
public import Mathlib.Topology.Connected.LocallyPathConnected
public import Mathlib.Topology.IsLocalHomeomorph
public import Mathlib.Topology.OpenPartialHomeomorph.Constructions

/-!
# Local homeomorphisms: path-connectedness, local inverses, fiber sums, products, base change

A local homeomorphism `p : E → B` identifies a neighbourhood of each point of `E` with an open
subset of `B`, so `E` inherits any property of `B` that is local and stable under passing to open
subspaces. This file records that for local path-connectedness.

The intended use is a covering map, whose total space is therefore locally path-connected as soon
as the base is; this is what lets the covers built over a locally path-connected base be fed back
into results that require a locally path-connected source, such as the lifting criterion.

A local inverse `L` of `p` composed with `p` is a local deck transformation of `p`. Near a point
`z` it agrees with every local deck transformation of `p` that is continuous at `z` and sends `z`
into the target of `L`. This is what identifies the transition maps of charts pushed forward along
`p` with deck transformations.

The fibers of a local homeomorphism are discrete. If the support of `f : E → M` meets the preimage
of each compact set in a compact set, then summing `f` over the fibers of `p` gives a function on
`B` which near each point is a finite sum of `f` composed with local sections of `p`. This is how
the regularity of such fiber sums is controlled, as for the source map of an étale groupoid.

## Main results

* `IsLocalHomeomorph.locallyPathConnectedSpace`: the domain of a local homeomorphism into a
  locally path-connected space is locally path-connected.
* `IsLocalHomeomorph.localInverseAt_comp_eventuallyEq`: near `z`, a local inverse composed with
  `p` agrees with any continuous local deck transformation sending `z` into the target of that
  local inverse.
* `IsLocalHomeomorph.eventually_finsum_mem_preimage_singleton_eq_sum`: if the support of `f`
  meets the preimage of each compact set in a compact set, then near each point of the base the
  sum of `f` over the fibers is a fixed finite sum of `f` composed with local sections.
* `IsLocalHomeomorph.prodMap`: the product of two local homeomorphisms is a local homeomorphism.
* `IsLocalHomeomorph.pullback_snd`: the base change of a local homeomorphism along a continuous
  map is a local homeomorphism.
-/

public section

open Topology

namespace TauCeti

variable {E B : Type*} [TopologicalSpace E] [TopologicalSpace B]

/-- **A local homeomorphism with locally path-connected codomain has locally path-connected
domain.** In particular the total space of a covering of a locally path-connected space is
locally path-connected. -/
theorem _root_.IsLocalHomeomorph.locallyPathConnectedSpace [LocallyPathConnectedSpace B]
    {p : E → B} (hp : IsLocalHomeomorph p) : LocallyPathConnectedSpace E := by
  constructor
  intro e
  rw [Filter.hasBasis_self]
  intro U hU
  obtain ⟨W, hWU, hWopen, heW⟩ := mem_nhds_iff.mp hU
  let φ := hp.localInverseAt e
  have hpe_source : p e ∈ φ.source := hp.apply_self_mem_localInverseAt_source
  have hsource : IsOpen (φ.source ∩ φ ⁻¹' W) :=
    φ.continuousOn_toFun.isOpen_inter_preimage φ.open_source hWopen
  have hpe : p e ∈ φ.source ∩ φ ⁻¹' W := by
    refine ⟨hpe_source, ?_⟩
    simpa only [Set.mem_preimage, φ, hp.localInverseAt_apply_self] using heW
  obtain ⟨V, ⟨hVopen, hpeV, hVpath⟩, hVsub⟩ :=
    (isOpen_isPathConnected_basis (p e)).mem_iff.mp (hsource.mem_nhds hpe)
  refine ⟨φ '' V, ?_, hVpath.image' (φ.continuousOn_toFun.mono fun _ hv => (hVsub hv).1), ?_⟩
  · exact (φ.isOpen_image_of_subset_source hVopen
      (hVsub.trans Set.inter_subset_left)).mem_nhds ⟨p e, hpeV, by simp [φ]⟩
  · rintro z ⟨y, hyV, rfl⟩
    exact hWU (hVsub hyV).2

/-- Let `L` be a local inverse of a local homeomorphism `p` at `e`. If `φ` is continuous at `z`,
satisfies `p ∘ φ = p` near `z`, and sends `z` into the target of `L`, then `L ∘ p` agrees with `φ`
near `z`. -/
theorem _root_.IsLocalHomeomorph.localInverseAt_comp_eventuallyEq {p : E → B}
    (hp : IsLocalHomeomorph p) {e z : E} {φ : E → E} (hφ : ContinuousAt φ z)
    (hφz : φ z ∈ (hp.localInverseAt e).target) (hpφ : p ∘ φ =ᶠ[𝓝 z] p) :
    hp.localInverseAt e ∘ p =ᶠ[𝓝 z] φ := by
  set L := hp.localInverseAt e
  filter_upwards [hφ.preimage_mem_nhds (L.open_target.mem_nhds hφz), hpφ] with w hw hpw
  have hL : L (L.symm (φ w)) = φ w := L.right_inv hw
  rw [hp.localInverseAt_symm] at hL
  rwa [Function.comp_apply, ← hpw]

section FiberSum

/-- A compact set of points in one fiber of a local homeomorphism is finite. -/
theorem _root_.IsLocalHomeomorph.finite_preimage_singleton_inter {p : E → B}
    (hp : IsLocalHomeomorph p) {s : Set E} {b : B} (hs : IsCompact (p ⁻¹' {b} ∩ s)) :
    (p ⁻¹' {b} ∩ s).Finite := by
  apply hs.finite
  apply hp.isLocalHomeomorphOn.isDiscrete_of_image
  refine (Set.subsingleton_singleton (a := b)).isDiscrete.mono ?_
  rintro _ ⟨e, he, rfl⟩
  exact he.1

/-- **Sums over the fibers of a local homeomorphism are locally finite sums.** Let `p : E → B`
be a local homeomorphism of Hausdorff spaces with weakly locally compact base, and let `f` be a
function whose topological support meets the preimage of each compact set in a compact set. Let
`σ e` be a section of `p` near `p e` through `e`, continuous at `p e`. Then near each `b₀`, the
sum of `f` over the fiber of `p` is the sum of `f ∘ σ e` over a fixed finite set of points `e` of
the fiber over `b₀`. -/
theorem _root_.IsLocalHomeomorph.eventually_finsum_mem_preimage_singleton_eq_sum
    [T2Space E] [T2Space B] [WeaklyLocallyCompactSpace B] {M : Type*} [AddCommMonoid M]
    {p : E → B} (hp : IsLocalHomeomorph p) {f : E → M}
    (hf : ∀ ⦃K : Set B⦄, IsCompact K → IsCompact (p ⁻¹' K ∩ tsupport f))
    {σ : E → B → E} (hσ : ∀ e, ContinuousAt (σ e) (p e)) (hσe : ∀ e, σ e (p e) = e)
    (hpσ : ∀ e, ∀ᶠ b in 𝓝 (p e), p (σ e b) = b) (b₀ : B) :
    ∃ F : Finset E, (∀ e ∈ F, p e = b₀) ∧
      ∀ᶠ b in 𝓝 b₀, ∑ᶠ e ∈ p ⁻¹' {b}, f e = ∑ e ∈ F, f (σ e b) := by
  classical
  -- `F` is the finite set of points of the fiber over `b₀` in the support of `f`. Separate them
  -- by disjoint open sets `W e` on which `p` is injective.
  have hF := hp.finite_preimage_singleton_inter (hf (isCompact_singleton (x := b₀)))
  obtain ⟨O, hO, hdisj⟩ := hF.t2_separation
  have hW (e : E) : ∃ W : Set E, IsOpen W ∧ e ∈ W ∧ W ⊆ O e ∧ Set.InjOn p W := by
    obtain ⟨φ, heφ, rfl⟩ := hp e
    exact ⟨O e ∩ φ.source, (hO e).2.inter φ.open_source, ⟨(hO e).1, heφ⟩,
      Set.inter_subset_left, φ.injOn.mono Set.inter_subset_right⟩
  choose W hWo hWe hWO hWinj using hW
  -- Away from the image of the rest `L` of the support over a compact neighbourhood `K`, every
  -- point of a fiber in the support lies in some `W e`.
  set L := tsupport f \ ⋃ e ∈ hF.toFinset, W e
  obtain ⟨K, hK, hKb⟩ := exists_compact_mem_nhds b₀
  have hL : IsCompact (p ⁻¹' K ∩ L) :=
    (hf hK).of_isClosed_subset ((hK.isClosed.preimage hp.continuous).inter
      ((isClosed_tsupport f).sdiff (isOpen_biUnion fun e _ ↦ hWo e)))
      (Set.inter_subset_inter_right _ Set.sdiff_subset)
  have hb₀ : b₀ ∉ p '' (p ⁻¹' K ∩ L) := by
    rintro ⟨e, ⟨-, he, heW⟩, rfl⟩
    exact heW (Set.mem_biUnion (hF.mem_toFinset.2 ⟨rfl, he⟩) (hWe e))
  have hσW : ∀ᶠ b in 𝓝 b₀, ∀ e ∈ hF.toFinset, σ e b ∈ W e ∧ p (σ e b) = b := by
    refine (Filter.eventually_all_finset _).2 fun e he ↦ ?_
    rw [← (hF.mem_toFinset.1 he).1]
    exact ((hσ e).eventually_mem ((hWo e).mem_nhds ((hσe e).symm ▸ hWe e))).and (hpσ e)
  refine ⟨hF.toFinset, fun e he ↦ (hF.mem_toFinset.1 he).1, ?_⟩
  filter_upwards [hKb, (hL.image hp.continuous).isClosed.isOpen_compl.mem_nhds hb₀, hσW]
    with b hbK hbL hbσ
  rw [finsum_mem_eq_sum_of_inter_support_eq f (t := hF.toFinset.image fun e ↦ σ e b),
    Finset.sum_image]
  · -- Distinct points of `F` have sections in the disjoint sets `W e`.
    intro e he e' he' h
    by_contra hne
    exact Set.disjoint_left.mp (hdisj (hF.mem_toFinset.1 he) (hF.mem_toFinset.1 he') hne)
      (hWO e (hbσ e he).1) (by simpa only [h] using hWO e' (hbσ e' he').1)
  · ext e'
    simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff, Finset.coe_image,
      Set.mem_image, Finset.mem_coe, Function.mem_support]
    refine ⟨fun ⟨hpe', hfe'⟩ ↦ ⟨?_, hfe'⟩, fun ⟨⟨e, he, he'⟩, hfe'⟩ ↦ ⟨he' ▸ (hbσ e he).2, hfe'⟩⟩
    -- A point of the fiber over `b` in the support is not in `L`, so it is in some `W e`, where
    -- `p` is injective.
    have he'L : e' ∉ L := fun h ↦ hbL ⟨e', ⟨Set.mem_preimage.2 (hpe' ▸ hbK), h⟩, hpe'⟩
    simp only [L, Set.mem_sdiff, subset_tsupport f hfe', true_and, not_not, Set.mem_iUnion₂] at he'L
    obtain ⟨e, he, he'W⟩ := he'L
    exact ⟨e, he, hWinj e (hbσ e he).1 he'W ((hbσ e he).2.trans hpe'.symm)⟩

end FiberSum

section Prod

variable {X Y Z W : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
  [TopologicalSpace W]

/-- **The product of two local homeomorphisms is a local homeomorphism**, with the product of
local charts as local charts. -/
theorem _root_.IsLocalHomeomorph.prodMap {f : X → Y} {g : Z → W} (hf : IsLocalHomeomorph f)
    (hg : IsLocalHomeomorph g) : IsLocalHomeomorph (Prod.map f g) := by
  refine IsLocalHomeomorph.mk _ fun p ↦ ?_
  obtain ⟨e, he, rfl⟩ := hf p.1
  obtain ⟨e', he', rfl⟩ := hg p.2
  exact ⟨e.prod e', ⟨he, he'⟩, fun _ _ ↦ rfl⟩

end Prod

section Pullback

variable {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]

/-- **Local homeomorphisms are stable under base change.** If `f : X → Y` is a local
homeomorphism and `g : Z → Y` is continuous, the projection from the fiber product `X ×_Y Z` to
`Z` is a local homeomorphism. Over a local chart `e` of `f`, the fiber product is identified with
`g⁻¹ e.target` by `(x, z) ↦ z`, with inverse `z ↦ (e.symm (g z), z)`. -/
theorem _root_.IsLocalHomeomorph.pullback_snd {f : X → Y} {g : Z → Y} (hf : IsLocalHomeomorph f)
    (hg : Continuous g) : IsLocalHomeomorph (Function.Pullback.snd : f.Pullback g → Z) := by
  refine isLocalHomeomorph_iff_isOpenEmbedding_restrict.mpr fun q ↦ ?_
  obtain ⟨e, he, rfl⟩ := hf q.fst
  have hfst : Continuous (Function.Pullback.fst : (⇑e).Pullback g → X) :=
    continuous_fst.comp continuous_subtype_val
  have hsnd : Continuous (Function.Pullback.snd : (⇑e).Pullback g → Z) :=
    continuous_snd.comp continuous_subtype_val
  have hpb (p : (⇑e).Pullback g) : e p.fst = g p.snd := p.2
  let U : Set ((⇑e).Pullback g) := Function.Pullback.fst ⁻¹' e.source
  let W : Set Z := g ⁻¹' e.target
  have hgU (p : U) : g p.1.snd ∈ e.target := hpb p.1 ▸ e.map_source p.2
  have hfW (w : W) : e (e.symm (g w)) = g w := e.right_inv w.2
  -- Over the chart `e`, the projection identifies `U` with `W`.
  let φ : U ≃ₜ W :=
    { toFun p := ⟨p.1.snd, hgU p⟩
      invFun w := ⟨⟨(e.symm (g w), w), hfW w⟩, e.map_target w.2⟩
      left_inv p := by
        refine Subtype.ext (Subtype.ext (Prod.ext ?_ rfl))
        -- The first component of the round trip is `e.symm (g p.1.snd)` by definition of `φ`.
        exact (congrArg e.symm (hpb p.1)).symm.trans (e.left_inv p.2)
      right_inv _ := rfl
      continuous_toFun := (hsnd.comp continuous_subtype_val).subtype_mk _
      continuous_invFun :=
        (((e.continuousOn_symm.comp_continuous (hg.comp continuous_subtype_val) fun w ↦ w.2).prodMk
          continuous_subtype_val).subtype_mk _).subtype_mk _ }
  refine ⟨U, (e.open_source.preimage hfst).mem_nhds he, ?_⟩
  exact ((e.open_target.preimage hg).isOpenEmbedding_subtypeVal.comp φ.isOpenEmbedding :)

end Pullback

end TauCeti
