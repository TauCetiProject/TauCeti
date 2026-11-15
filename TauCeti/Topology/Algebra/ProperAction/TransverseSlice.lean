/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Algebra.ProperAction.Orbit

/-!
# Injectivity of slice maps of proper actions

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

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Springer, 2013, proof of
  Theorem 21.10 (the quotient manifold theorem), the injectivity step.
* E. Meinrenken, *Group actions on manifolds*, lecture notes, University of Toronto, 2003,
  proof of Theorem 1.21.
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

end ProperSMul
