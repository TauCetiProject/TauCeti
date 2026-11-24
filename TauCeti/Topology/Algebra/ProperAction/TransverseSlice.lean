/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Algebra.ProperAction.Orbit

/-!
# Injectivity of slice maps of proper actions, and slice charts of orbit spaces

Let a topological group `G` act on a space `X`, let `σ : S → X` be a map from a space of slice
parameters, and consider the **slice map** `(g, s) ↦ g • σ s : G × S → X`. In the proof of the
quotient manifold theorem for a free proper action, one first finds a slice through `σ s₀` for
which this map is a local diffeomorphism near `(1, s₀)`. Properness then upgrades this to
injectivity on the whole tube `G × U` over a smaller neighbourhood `U` of `s₀`. This file proves
that properness step. It is purely topological.

The main result is `ProperSMul.exists_mem_nhds_injOn_smul_slice`: if `σ` is continuous at `s₀`,
the point `σ s₀` has trivial stabilizer, and the slice map is injective near `(1, s₀)`, then it is
injective on `G × U` for some neighbourhood `U` of `s₀`. Combined with
`MulAction.injOn_smul_univ_prod_iff`, this makes the quotient chart `s ↦ ⟦σ s⟧ : U → X ⧸ G`
injective.

The proof uses `ProperSMul.mem_nhdsSet_stabilizer_iff`: for a proper action, the elements moving
a small neighbourhood of `σ s₀` to meet itself lie in any prescribed neighbourhood of the trivial
stabilizer. So if `g • σ s = g' • σ s'` with `s, s'` near `s₀`, then `g'⁻¹ * g` moves a point near
`σ s₀` to a point near `σ s₀`, so it lies near `1`. Then local injectivity gives `g = g'` and
`s = s'`.

In infinite dimensions, as in gauge theory, a slice through `x` is often cut out by a gauge
condition, and the analysis supplies a continuous gauge `γ` near `x` moving each point into the
slice `S`, unique near `1`, rather than a local diffeomorphism of the slice map. For a proper
action with trivial stabilizer at `x` this already gives the quotient chart:
`ProperSMul.exists_isOpen_isOpenEmbedding_quotientMk_inter` shows that `y ↦ [y]` is an open
embedding of `V ∩ S` into `X ⧸ G` for an open neighbourhood `V` of `x`. Properness forces a group
element carrying a point of `S` near `x` to another such point to lie near `1`, so it is `1`; and
`y ↦ γ y • y` fixes `S` near `x`, so the orbits through an open part of the slice pull back to an
open set of `X`.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Springer, 2013, proof of
  Theorem 21.10 (the quotient manifold theorem), the injectivity step.
* E. Meinrenken, *Group actions on manifolds*, lecture notes, University of Toronto, 2003,
  proof of Theorem 1.21.
* S. K. Donaldson and P. B. Kronheimer, *The Geometry of Four-Manifolds*, Oxford University Press,
  1990, Section 4.2.1, for slices of gauge group actions.
-/

public section

open Set Filter Topology
open scoped Pointwise

namespace ProperSMul

variable {G X : Type*} [Group G] [MulAction G X] [TopologicalSpace G] [TopologicalSpace X]
  [ProperSMul G X]

/-- **Slice maps of free proper actions are injective on small tubes.** Let `σ : S → X` be
continuous at `s₀`, with `σ s₀` a point of trivial stabilizer. If `(g, s) ↦ g • σ s` is injective
on a neighbourhood of `(1, s₀)`, then it is injective on `G × U` for some neighbourhood `U` of
`s₀`. -/
@[to_additive /-- **Slice maps of free proper additive actions are injective on small tubes.** Let
`σ : S → X` be continuous at `s₀`, with `σ s₀` a point of trivial stabilizer. If
`(g, s) ↦ g +ᵥ σ s` is injective on a neighbourhood of `(0, s₀)`, then it is injective on `G × U`
for some neighbourhood `U` of `s₀`. -/]
theorem exists_mem_nhds_injOn_smul_slice {S : Type*} [TopologicalSpace S] {σ : S → X} {s₀ : S}
    (hσ : ContinuousAt σ s₀) (hfree : MulAction.stabilizer G (σ s₀) = ⊥) {N : Set (G × S)}
    (hN : N ∈ 𝓝 ((1 : G), s₀)) (hinj : InjOn (fun p : G × S ↦ p.1 • σ p.2) N) :
    ∃ U ∈ 𝓝 s₀, InjOn (fun p : G × S ↦ p.1 • σ p.2) (univ ×ˢ U) := by
  obtain ⟨V, hV, U₁, hU₁, hVU⟩ := mem_nhds_prod_iff.mp hN
  have hV' : V ∈ 𝓝ˢ (MulAction.stabilizer G (σ s₀) : Set G) := by
    rwa [hfree, Subgroup.coe_bot, nhdsSet_singleton]
  obtain ⟨W, hW, hWV⟩ := mem_nhdsSet_stabilizer_iff.mp hV'
  refine ⟨U₁ ∩ σ ⁻¹' W, inter_mem hU₁ (hσ hW), ?_⟩
  rintro ⟨g, s⟩ ⟨-, hsU, hsW⟩ ⟨g', s'⟩ ⟨-, hs'U, hs'W⟩ (hgg' : g • σ s = g' • σ s')
  have hmove : (g'⁻¹ * g) • σ s = σ s' := by rw [mul_smul, hgg', inv_smul_smul]
  -- The element `g'⁻¹ * g` moves `W` to meet itself at `σ s'`, so it lies in `V`.
  have hgV : g'⁻¹ * g ∈ V := hWV ⟨σ s', ⟨σ s, hsW, hmove⟩, hs'W⟩
  -- Both `(g'⁻¹ * g, s)` and `(1, s')` lie in `N` and have the same image `σ s'`.
  have h := @hinj (g'⁻¹ * g, s) (hVU ⟨hgV, hsU⟩) (1, s') (hVU ⟨mem_of_mem_nhds hV, hs'U⟩)
    (by simpa using hmove)
  obtain ⟨hg, rfl⟩ := Prod.ext_iff.mp h
  rw [inv_mul_eq_one.mp hg]

/-- **Slices cut out by a gauge condition chart the orbit space.** Let `G` act properly on `X`, let
`x` be a point of trivial stabilizer, and let `S` be a set, the slice. Suppose that near `x` every
point is moved into `S` by a continuous choice of group element: on a neighbourhood `U` of `x`
there is `γ`, continuous on `U` with `γ x = 1`, such that `γ y • y ∈ S` for `y ∈ U`. Suppose also
that near `1` no element other than `1` moves a point of `S ∩ U` into `S`. Then there is an open
neighbourhood `V ⊆ U` of `x` such that `y ↦ [y]` is an open embedding of `V ∩ S` into the orbit
space `X ⧸ G`. -/
@[to_additive /-- **Slices cut out by a gauge condition chart the orbit space.** Let `G` act
properly on `X`, let `x` be a point of trivial stabilizer, and let `S` be a set, the slice.
Suppose that near `x` every point is moved into `S` by a continuous choice of group element: on a
neighbourhood `U` of `x` there is `γ`, continuous on `U` with `γ x = 0`, such that `γ y +ᵥ y ∈ S`
for `y ∈ U`. Suppose also that near `0` no element other than `0` moves a point of `S ∩ U` into
`S`. Then there is an open neighbourhood `V ⊆ U` of `x` such that `y ↦ [y]` is an open embedding
of `V ∩ S` into the orbit space `X ⧸ G`. -/]
theorem exists_isOpen_isOpenEmbedding_quotientMk_inter {S U : Set X} {x : X}
    (hfree : MulAction.stabilizer G x = ⊥) (hU : U ∈ 𝓝 x) {γ : X → G} (hγ : ContinuousOn γ U)
    (hγx : γ x = 1) (hγS : ∀ y ∈ U, γ y • y ∈ S) {N : Set G} (hN : N ∈ 𝓝 1)
    (huniq : ∀ y ∈ U, ∀ g ∈ N, y ∈ S → g • y ∈ S → g = 1) :
    ∃ V, IsOpen V ∧ x ∈ V ∧ V ⊆ U ∧
      IsOpenEmbedding fun y : ↥(V ∩ S) ↦ Quotient.mk (MulAction.orbitRel G X) (y : X) := by
  -- Elements moving a small neighbourhood `W` of `x` to meet itself lie in `N`.
  have hN' : N ∈ 𝓝ˢ (MulAction.stabilizer G x : Set G) := by
    rwa [hfree, Subgroup.coe_bot, nhdsSet_singleton]
  obtain ⟨W, hW, hWN⟩ := mem_nhdsSet_stabilizer_iff.mp hN'
  -- The retraction `r y = γ y • y` onto the slice fixes `x`.
  set r : X → X := fun y ↦ γ y • y with hr_def
  have hr : ContinuousOn r U := hγ.smul continuousOn_id
  have hrx : r x = x := by simp [hr_def, hγx]
  have hrW : r ⁻¹' W ∈ 𝓝 x := (hr.continuousAt hU).preimage_mem_nhds (by rwa [hrx])
  set V := interior (W ∩ U ∩ r ⁻¹' W)
  have hVW : V ⊆ W := interior_subset.trans fun y hy ↦ hy.1.1
  have hVU : V ⊆ interior U := interior_mono fun y hy ↦ hy.1.2
  -- An element carrying a point of `V ∩ S` to a point of `W ∩ S` is `1`.
  have hone {y : X} (hy : y ∈ V ∩ S) {g : G} (hgW : g • y ∈ W) (hgS : g • y ∈ S) : g = 1 :=
    huniq y (interior_subset (hVU hy.1)) g (hWN ⟨g • y, ⟨y, hVW hy.1, rfl⟩, hgW⟩) hy.2 hgS
  -- So `r` fixes the points of `V ∩ S`.
  have hfix {y : X} (hy : y ∈ V ∩ S) : r y = y := by
    have hyr : y ∈ r ⁻¹' W := (interior_subset hy.1 : y ∈ W ∩ U ∩ r ⁻¹' W).2
    simp only [hr_def]
    rw [hone hy hyr (hγS y (interior_subset (hVU hy.1))), one_smul]
  refine ⟨V, isOpen_interior, mem_interior_iff_mem_nhds.mpr (inter_mem (inter_mem hW hU) hrW),
    hVU.trans interior_subset, .of_continuous_injective_isOpenMap
      (continuous_quot_mk.comp continuous_subtypeVal) ?_ ?_⟩
  · rintro ⟨y, hy⟩ ⟨y', hy'⟩ hyy'
    obtain ⟨g, hg'⟩ :=
      MulAction.mem_orbit_iff.mp (MulAction.orbitRel_apply.mp (Quotient.exact hyy'))
    have hg1 : g = 1 := hone hy' (by rw [hg']; exact hVW hy.1) (by rw [hg']; exact hy.2)
    rw [hg1, one_smul] at hg'
    exact Subtype.ext hg'.symm
  · rintro _ ⟨t, ht, rfl⟩
    -- The orbits through `V ∩ S ∩ t` are those through the open set `interior U ∩ r⁻¹ (t ∩ V)`.
    have himage : (fun y : ↥(V ∩ S) ↦ Quotient.mk (MulAction.orbitRel G X) (y : X)) ''
        (Subtype.val ⁻¹' t) = Quotient.mk _ '' (interior U ∩ r ⁻¹' (t ∩ V)) := by
      rw [← image_image (Quotient.mk _) Subtype.val, Subtype.image_preimage_coe]
      refine Subset.antisymm ?_ ?_
      · rintro _ ⟨y, ⟨hyVS, hyt⟩, rfl⟩
        refine ⟨y, ⟨hVU hyVS.1, ?_⟩, rfl⟩
        rw [mem_preimage, hfix hyVS]
        exact ⟨hyt, hyVS.1⟩
      · rintro _ ⟨y, ⟨hyU, hyt, hyV⟩, rfl⟩
        exact ⟨r y, ⟨⟨hyV, hγS y (interior_subset hyU)⟩, hyt⟩,
          Quotient.sound (MulAction.orbitRel_apply.mpr (MulAction.mem_orbit y (γ y)))⟩
    rw [himage]
    exact MulAction.isOpenQuotientMap_quotientMk.isOpenMap _
      ((hr.mono interior_subset).isOpen_inter_preimage isOpen_interior (ht.inter isOpen_interior))

end ProperSMul
