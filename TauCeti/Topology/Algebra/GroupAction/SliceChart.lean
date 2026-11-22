/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.MulAction
public import Mathlib.Topology.IsLocalHomeomorph
public import TauCeti.Algebra.GroupAction.OrbitRelQuotient
import TauCeti.Topology.IsLocalHomeomorph

/-!
# Orbit-space charts from slices

Let a group `G` act on a topological space `X`, and let `σ : S → X` be a map from a topological
space `S`, thought of as a slice. The **slice map** `(g, s) ↦ g • σ s : G × S → X` sweeps the
slice along the orbits of the action. If the slice map is injective on `G × U`, then distinct points
of `U` lie in distinct orbits (`TauCeti.MulAction.injOn_quotientMk_slice`). Suppose moreover that
`U ⊆ S` is open and that the slice map is a local homeomorphism on `G × U`. Then:

* its restriction to `G × U` is an open embedding into `X`, so it identifies `G × U` with an open
  invariant neighbourhood of the orbits through `σ '' U`
  (`TauCeti.MulAction.isOpenEmbedding_smul_slice`);
* `s ↦ [σ s]` is an open embedding of `U` into the orbit space `X ⧸ G`
  (`TauCeti.MulAction.isOpenEmbedding_quotientMk_slice`).

These are the charts of the orbit space of a free proper action of a Lie group: the inverse
function theorem makes the slice map of a transverse slice a local diffeomorphism near `(1, s₀)`
(`TauCeti.isLocalDiffeomorphAt_smul_slice_iff`), properness makes it injective on `G × U` after
shrinking the slice, and the smoothness of the transitions between these charts is
`TauCeti.exists_contMDiffAt_quotientMk_slice_eq_iff`. No properness, separation or smoothness is
used in this file.

For a topological group acting continuously, the two hypotheses of these theorems hold near a point
`x` of a slice `T ⊆ X` that has a local gauge fixing at `x`, a map `g` to `G`, continuous near `x`
with `g x = 1`, moving every point `y` near `x` into `T` by `g y`, provided that `T` meets the
orbits near `x` at most once and freely
(`TauCeti.MulAction.exists_isOpen_injOn_isLocalHomeomorphOn_smul_slice`). The local inverse of the
slice map near `u • s` is `z ↦ (u * (g w)⁻¹, g w • w)` with `w = u⁻¹ • z`. This is the form in which
the slice theorem arises in gauge theory, where `g` comes from solving the gauge-fixing equation by
the inverse function theorem.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Springer, 2013, proof of Theorem 21.10
  (the quotient manifold theorem).
* E. Meinrenken, *Group actions on manifolds*, lecture notes, University of Toronto, 2003, proof of
  Theorem 1.21.
-/

public section

open Filter Function Set Topology

variable {G X : Type*} [Group G] [MulAction G X]

namespace TauCeti.MulAction

variable {S : Type*} {σ : S → X} {U : Set S}

variable [TopologicalSpace G] [TopologicalSpace X] [TopologicalSpace S]

/-- **Slice maps parametrize open invariant neighbourhoods of orbits.** If the slice map
`(g, s) ↦ g • σ s` is injective on `G × U` and a local homeomorphism there, for an open set `U`,
then its restriction to `G × U` is an open embedding into `X`. -/
theorem isOpenEmbedding_smul_slice (hU : IsOpen U)
    (hinj : InjOn (fun p : G × S ↦ p.1 • σ p.2) (univ ×ˢ U))
    (hloc : IsLocalHomeomorphOn (fun p : G × S ↦ p.1 • σ p.2) (univ ×ˢ U)) :
    IsOpenEmbedding fun p : G × U ↦ p.1 • σ p.2 := by
  -- The restriction is the slice map composed with the inclusion `G × U → G × S`.
  have hmaps : ∀ p : G × U, (p.1, (p.2 : S)) ∈ univ ×ˢ U := fun p ↦ ⟨mem_univ _, p.2.property⟩
  refine isOpenEmbedding_iff_continuous_injective_isOpenMap.2 ⟨?_, ?_, fun W hW ↦ ?_⟩
  · exact hloc.continuousOn.comp_continuous
      (continuous_fst.prodMk (continuous_subtypeVal.comp continuous_snd)) hmaps
  · intro p q hpq
    have h1 := hinj (hmaps p) (hmaps q) hpq
    exact Prod.ext (Prod.ext_iff.1 h1).1 (Subtype.ext (Prod.ext_iff.1 h1).2)
  · -- An open subset of `G × U` is open in `G × S`, and the slice map is open on `univ ×ˢ U`.
    have hW' : IsOpen (Prod.map id ((↑) : U → S) '' W) :=
      (IsOpenMap.id.prodMap hU.isOpenMap_subtypeVal) W hW
    have h1 := (hloc.mono (image_subset_iff.2 fun p _ ↦ hmaps p)).isOpen_image hW'
    rwa [image_image] at h1

/-- **Quotient charts from slices.** If the slice map `(g, s) ↦ g • σ s` is injective on `G × U`
and a local homeomorphism there, for an open set `U`, then `s ↦ [σ s]` is an open embedding of `U`
into the orbit space `X ⧸ G`: distinct points of `U` lie in distinct orbits, and the orbits
through an open subset of `U` form an open subset of `X ⧸ G`. -/
theorem isOpenEmbedding_quotientMk_slice (hU : IsOpen U)
    (hinj : InjOn (fun p : G × S ↦ p.1 • σ p.2) (univ ×ˢ U))
    (hloc : IsLocalHomeomorphOn (fun p : G × S ↦ p.1 • σ p.2) (univ ×ˢ U)) :
    IsOpenEmbedding fun s : U ↦ Quotient.mk (MulAction.orbitRel G X) (σ s) := by
  -- On `U`, the slice `σ` is the restriction of the slice map to `{1} × U`.
  have hσ : ContinuousOn σ U := by
    have h1 : ContinuousOn (fun s : S ↦ (1 : G) • σ s) U :=
      hloc.continuousOn.comp (continuous_const.prodMk continuous_id).continuousOn
        fun s hs ↦ ⟨mem_univ _, hs⟩
    simpa only [one_smul] using h1
  refine isOpenEmbedding_iff_continuous_injective_isOpenMap.2 ⟨?_, ?_, fun W hW ↦ ?_⟩
  · exact continuous_quot_mk.comp hσ.domRestrict
  · exact fun s s' hss' ↦ Subtype.ext (injOn_quotientMk_slice hinj s.property s'.property hss')
  · -- The orbits through the image of `W` pull back to the image of the open set `G × W` under
    -- the slice map.
    have hT : IsOpen (((↑) : U → S) '' W) := hU.isOpenMap_subtypeVal W hW
    have hpre : Quotient.mk (MulAction.orbitRel G X) ⁻¹'
        ((fun s : U ↦ Quotient.mk (MulAction.orbitRel G X) (σ s)) '' W) =
        (fun p : G × S ↦ p.1 • σ p.2) '' (univ ×ˢ (((↑) : U → S) '' W)) := by
      convert MulAction.quotient_preimage_image_eq_union_mul (G := G) (σ '' (((↑) : U → S) '' W))
        using 1
      · simp only [image_image]; rfl
      · rw [image_prod (fun (g : G) (s : S) ↦ g • σ s), ← iUnion_image_left, biUnion_univ]
        simp only [image_image]
    -- The quotient topology is coinduced; `hpre` computes the preimage.
    rw [isOpen_coinduced]
    convert (hloc.mono (prod_mono_right (Subtype.coe_image_subset U W))).isOpen_image
      (isOpen_univ.prod hT) using 1
    exact hpre

/-! ### Slices with a local gauge fixing -/

section GaugeFixing

variable [IsTopologicalGroup G] [ContinuousSMul G X] {T : Set X} {x : X}

/-- **Tubes over a slice with a local gauge fixing.** Let a topological group `G` act continuously
on `X`, and let `T ⊆ X` be a slice through `x ∈ T`. Suppose that

* `T` has a local gauge fixing at `x`: a map `g : X → G`, continuous on a neighbourhood `W` of `x`
  with `g x = 1`, such that `g y • y ∈ T` for every `y ∈ W`;
* `T` meets the orbits near `x` at most once, and freely: on some neighbourhood `V` of `x`,
  `u • y = y'` with `y, y' ∈ T ∩ V` forces `u = 1`.

Then for some open neighbourhood `U` of `x` in `T`, the slice map `(u, s) ↦ u • s : G × T → X` is
injective and a local homeomorphism on `G × U`. These are the hypotheses of
`TauCeti.MulAction.isOpenEmbedding_smul_slice` and
`TauCeti.MulAction.isOpenEmbedding_quotientMk_slice`. -/
theorem exists_isOpen_injOn_isLocalHomeomorphOn_smul_slice (hx : x ∈ T) {W : Set X}
    (hW : W ∈ 𝓝 x) {g : X → G} (hg : ContinuousOn g W) (hgx : g x = 1)
    (hgT : ∀ y ∈ W, g y • y ∈ T)
    (huniq : ∃ V ∈ 𝓝 x, ∀ y ∈ T ∩ V, ∀ y' ∈ T ∩ V, ∀ u : G, u • y = y' → u = 1) :
    ∃ U : Set T, IsOpen U ∧ ⟨x, hx⟩ ∈ U ∧
      InjOn (fun p : G × T ↦ p.1 • (p.2 : X)) (univ ×ˢ U) ∧
      IsLocalHomeomorphOn (fun p : G × T ↦ p.1 • (p.2 : X)) (univ ×ˢ U) := by
  obtain ⟨V, hV, hVT⟩ := huniq
  set F : G × T → X := fun p ↦ p.1 • (p.2 : X)
  -- Shrink to an open neighbourhood `O` of `x` whose points the gauge fixing keeps inside `V`.
  have hgV : {y | g y • y ∈ V} ∈ 𝓝 x :=
    ((hg.continuousAt hW).smul continuousAt_id).preimage_mem_nhds (by simpa [hgx] using hV)
  set O := interior (W ∩ V ∩ {y | g y • y ∈ V})
  have hOx : x ∈ O := mem_interior_iff_mem_nhds.2 (inter_mem (inter_mem hW hV) hgV)
  have hOW : O ⊆ W := interior_subset.trans (inter_subset_left.trans inter_subset_left)
  have hOV : O ⊆ V := interior_subset.trans (inter_subset_left.trans inter_subset_right)
  have hOg : ∀ y ∈ O, g y • y ∈ V := fun y hy ↦ (interior_subset hy).2
  -- The gauge fixing is trivial on the slice near `x`.
  have hg1 : ∀ s ∈ T, s ∈ O → g s = 1 := fun s hsT hs ↦
    hVT s ⟨hsT, hOV hs⟩ (g s • s) ⟨hgT s (hOW hs), hOg s hs⟩ (g s) rfl
  have hU : IsOpen (((↑) : T → X) ⁻¹' O) := isOpen_interior.preimage continuous_subtypeVal
  have hinj : InjOn F (univ ×ˢ (((↑) : T → X) ⁻¹' O)) := by
    rintro ⟨u, s⟩ ⟨-, hs⟩ ⟨u', s'⟩ ⟨-, hs'⟩ (h : u • (s : X) = u' • (s' : X))
    have h1 : (u'⁻¹ * u) • (s : X) = s' := by rw [mul_smul, h, inv_smul_smul]
    obtain rfl : u' = u :=
      inv_mul_eq_one.1 (hVT s ⟨s.property, hOV hs⟩ s' ⟨s'.property, hOV hs'⟩ _ h1)
    exact Prod.ext rfl (Subtype.ext (smul_left_cancel u' h))
  refine ⟨_, hU, hOx, hinj, (isLocalHomeomorphOn_iff_isOpenEmbedding_restrict _).2 fun p hp ↦
    ⟨_, (isOpen_univ.prod hU).mem_nhds hp, ?_⟩⟩
  refine isOpenEmbedding_iff_continuous_injective_isOpenMap.2 ⟨?_, fun a b h ↦
    Subtype.ext (hinj a.property b.property h), isOpenMap_iff_nhds_le.2 fun q ↦ ?_⟩
  · exact (continuous_fst.smul (continuous_subtypeVal.comp continuous_snd)).comp
      continuous_subtypeVal
  -- Near `u • s`, a point `z` is `F (u * (g w)⁻¹, g w • w)` for `w = u⁻¹ • z`, and these
  -- coordinates tend to `(u, s)` as `z → u • s`, since `g s = 1`.
  rw [domRestrict_eq, ← map_map, map_nhds_subtypeVal_eq_nhds q.property
    ((isOpen_univ.prod hU).mem_nhds q.property)]
  obtain ⟨⟨u, s⟩, -, hs⟩ := q
  have hWs : W ∈ 𝓝 (s : X) := mem_of_superset (isOpen_interior.mem_nhds hs) hOW
  have hw : Tendsto (fun z ↦ u⁻¹ • z) (𝓝 (u • (s : X))) (𝓝 (s : X)) := by
    simpa using (continuous_const_smul u⁻¹).tendsto (u • (s : X))
  have hgw := (hg.continuousAt hWs).tendsto.comp hw
  rw [hg1 s s.property hs] at hgw
  have h₁ : Tendsto (fun z ↦ u * (g (u⁻¹ • z))⁻¹) (𝓝 (u • (s : X))) (𝓝 u) := by
    simpa using tendsto_const_nhds (x := u).mul hgw.inv
  have h₂ : Tendsto (fun z ↦ g (u⁻¹ • z) • u⁻¹ • z) (𝓝 (u • (s : X))) (𝓝 (s : X)) := by
    simpa using hgw.smul hw
  classical
  -- The slice coordinate of the local inverse, extended by `s` off `u • W`.
  let t : X → T := fun z ↦ if h : u⁻¹ • z ∈ W then ⟨_, hgT _ h⟩ else s
  have ht : ∀ᶠ z in 𝓝 (u • (s : X)), (t z : X) = g (u⁻¹ • z) • u⁻¹ • z := by
    filter_upwards [hw hWs] with z hz
    simp [t, show u⁻¹ • z ∈ W from hz]
  exact le_map_of_right_inverse (mba := fun z ↦ (u * (g (u⁻¹ • z))⁻¹, t z))
    (ht.mono fun z hz ↦ by simp [F, hz, mul_smul])
    (h₁.prodMk_nhds (tendsto_subtype_rng.2 (h₂.congr' (ht.mono fun _ h ↦ h.symm))))

end GaugeFixing

end TauCeti.MulAction
