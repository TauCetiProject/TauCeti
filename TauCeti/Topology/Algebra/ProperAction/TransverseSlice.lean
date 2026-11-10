/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.ProperAction.Basic
public import Mathlib.Topology.NhdsSet

/-!
# Injectivity of slice maps of proper actions

Let a topological group `G` act on a space `X`, let `σ : S → X` be a map from a space of slice
parameters, and consider the **slice map** `(g, s) ↦ g • σ s : G × S → X`. In the proof of the
quotient manifold theorem for a free proper action, one first finds a slice through `σ s₀` for
which this map is a local diffeomorphism near `(1, s₀)`. Properness then upgrades this to
injectivity on the whole tube `G × U` over a smaller neighbourhood `U` of `s₀`. This file proves
that properness step. It is purely topological.

* `MulAction.injOn_smul_univ_prod_iff`: the slice map is injective on `G × U` iff every point of
  `σ '' U` has trivial stabilizer and distinct parameters in `U` lie on distinct orbits, that is,
  `s ↦ ⟦σ s⟧ : U → X ⧸ G` is injective. This is the injectivity of a quotient chart.
* `ProperSMul.mem_nhdsSet_stabilizer_iff`: for a proper action, the elements moving some small
  neighbourhood `W` of `x` to meet itself shrink into any neighbourhood of the stabilizer of `x`.
  Conversely, every such set is a neighbourhood of the stabilizer. The discrete case is
  `ProperSMul.exists_nhds_image_smul_eq_self`.
* `ProperSMul.exists_mem_nhds_injOn_smul_slice`: if `σ` is continuous at `s₀`, the point `σ s₀`
  has trivial stabilizer, and the slice map is injective near `(1, s₀)`, then it is injective on
  `G × U` for some neighbourhood `U` of `s₀`.

The second statement is the general form of properness used here. The map
`Φ (g, y) = (g • y, y)` is closed, and the pairs with `g` outside an open set containing the
stabilizer form a closed set whose image misses `(x, x)`. The third follows: if
`g • σ s = g' • σ s'` with `s, s'` near `s₀`, then `g'⁻¹ * g` moves a point near `σ s₀` to a
point near `σ s₀`, so it lies near `1`. Then local injectivity gives `g = g'` and `s = s'`.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Springer, 2013, proof of
  Theorem 21.10 (the quotient manifold theorem), the injectivity step.
* E. Meinrenken, *Group actions on manifolds*, lecture notes, University of Toronto, 2003,
  proof of Theorem 1.21.
-/

public section

open Set Filter Topology
open scoped Pointwise

namespace MulAction

variable {G X S : Type*} [Group G] [MulAction G X]

/-- **Injectivity of a slice map on a tube.** The map `(g, s) ↦ g • σ s` is injective on
`G × U` iff every `σ s` with `s ∈ U` has trivial stabilizer and `s ↦ ⟦σ s⟧` is injective on `U`
as a map to the orbit space. -/
@[to_additive /-- **Injectivity of a slice map on a tube.** The map `(g, s) ↦ g +ᵥ σ s` is
injective on `G × U` iff every `σ s` with `s ∈ U` has trivial stabilizer and `s ↦ ⟦σ s⟧` is
injective on `U` as a map to the orbit space. -/]
theorem injOn_smul_univ_prod_iff {σ : S → X} {U : Set S} :
    InjOn (fun p : G × S ↦ p.1 • σ p.2) (univ ×ˢ U) ↔
      (∀ s ∈ U, stabilizer G (σ s) = ⊥) ∧
        InjOn (fun s ↦ (Quotient.mk (orbitRel G X) (σ s) : orbitRel.Quotient G X)) U := by
  constructor
  · intro h
    refine ⟨fun s hs ↦ (Subgroup.eq_bot_iff_forall _).mpr fun g hg ↦ ?_, fun s hs s' hs' hss' ↦ ?_⟩
    · have := @h (g, s) ⟨mem_univ _, hs⟩ (1, s) ⟨mem_univ _, hs⟩ (by simpa using hg)
      exact congrArg Prod.fst this
    · obtain ⟨g, hg⟩ := Quotient.exact hss'
      have := @h (g, s') ⟨mem_univ _, hs'⟩ (1, s) ⟨mem_univ _, hs⟩ (by simpa using hg)
      exact (congrArg Prod.snd this).symm
  · rintro ⟨hstab, hinj⟩ ⟨g, s⟩ ⟨-, hs⟩ ⟨g', s'⟩ ⟨-, hs'⟩ (hgg' : g • σ s = g' • σ s')
    have hmove : (g'⁻¹ * g) • σ s = σ s' := by rw [mul_smul, hgg', inv_smul_smul]
    have hrel : orbitRel G X (σ s') (σ s) := orbitRel_apply.mpr ⟨g'⁻¹ * g, hmove⟩
    obtain rfl : s = s' := hinj hs hs' (Quotient.sound hrel).symm
    have hmem : g'⁻¹ * g ∈ stabilizer G (σ s) := hmove
    rw [hstab s hs, Subgroup.mem_bot, inv_mul_eq_one] at hmem
    rw [hmem]

end MulAction

namespace ProperSMul

variable {G X : Type*} [Group G] [MulAction G X] [TopologicalSpace G] [TopologicalSpace X]
  [ProperSMul G X]

/-- **Elements moving a small neighbourhood to meet itself lie near the stabilizer.** For a
proper action, a set `V ⊆ G` is a neighbourhood of the stabilizer of `x` iff it contains every
element moving some neighbourhood `W` of `x` to meet itself. -/
@[to_additive /-- **Elements moving a small neighbourhood to meet itself lie near the
stabilizer.** For a proper additive action, a set `V ⊆ G` is a neighbourhood of the stabilizer of
`x` iff it contains every element moving some neighbourhood `W` of `x` to meet itself. -/]
theorem mem_nhdsSet_stabilizer_iff {x : X} {V : Set G} :
    V ∈ 𝓝ˢ (MulAction.stabilizer G x : Set G) ↔
      ∃ W ∈ 𝓝 x, {g : G | (g • W ∩ W).Nonempty} ⊆ V := by
  constructor
  · intro hV
    let Φ : G × X → X × X := fun p ↦ (p.1 • p.2, p.2)
    have hΦ : IsClosedMap Φ := (ProperSMul.isProperMap_smul_pair (G := G) (X := X)).isClosedMap
    -- The pairs whose label lies outside the interior of `V` form a closed set.
    have hclosed : IsClosed (Φ '' (interior V)ᶜ ×ˢ univ) :=
      hΦ _ (isOpen_interior.isClosed_compl.prod isClosed_univ)
    -- Its image misses `(x, x)`, since every element fixing `x` lies in the interior of `V`.
    have hx : (x, x) ∉ Φ '' (interior V)ᶜ ×ˢ univ := by
      rintro ⟨⟨g, y⟩, ⟨hg, -⟩, hgy⟩
      obtain ⟨hgx, rfl⟩ := Prod.ext_iff.mp hgy
      exact hg (subset_interior_iff_mem_nhdsSet.mpr hV hgx)
    obtain ⟨W₁, hW₁, W₂, hW₂, hW⟩ := mem_nhds_prod_iff.mp (hclosed.isOpen_compl.mem_nhds hx)
    refine ⟨W₁ ∩ W₂, inter_mem hW₁ hW₂, fun g ⟨_, ⟨y, hy, rfl⟩, hgy⟩ ↦ interior_subset ?_⟩
    by_contra hg
    exact hW ⟨hgy.1, hy.2⟩ ⟨(g, y), ⟨hg, mem_univ _⟩, rfl⟩
  · rintro ⟨W, hW, hWV⟩
    -- The elements carrying `x` into the interior of `W` form an open set containing the
    -- stabilizer, and each of them moves `W` to meet itself at `x`.
    refine mem_nhdsSet_iff_exists.mpr ⟨(· • x) ⁻¹' interior W,
      isOpen_interior.preimage (continuous_id.smul continuous_const), fun g hg ↦ ?_,
      fun g hg ↦ hWV ⟨g • x, smul_mem_smul_set (mem_of_mem_nhds hW), interior_subset hg⟩⟩
    rw [mem_preimage, (hg : g • x = x)]
    exact mem_interior_iff_mem_nhds.mpr hW

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

end ProperSMul
