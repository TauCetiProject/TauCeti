/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Covering.BalancedProduct.RightTranslation
public import TauCeti.Topology.Algebra.ProperAction.Orbit

/-!
# Injectivity of the slice map after shrinking, by properness

Let a topological group `G` act properly on a space `M`, let `K` be the stabilizer of a point
`x = ι z₀`, and let `ι : Z → M` be a `K`-equivariant map from a `K`-space `Z`, continuous at a
`K`-fixed point `z₀`. Suppose the action map `[g, z] ↦ g • ι z` of the balanced product
`G ×_K Z` (`TauCeti.BalancedProduct.liftRightTranslation`) is injective on a neighbourhood of
`[1, z₀]`, as it is when it is a local diffeomorphism there (the local half of the slice theorem).
Then it is injective on all of `G ×_K V` for some neighbourhood `V` of `z₀`
(`TauCeti.BalancedProduct.exists_mem_nhds_injOn_liftRightTranslation`).

Choose the neighbourhood of `[1, z₀]` of the form `[O × V₀]`. Since `K` is compact
(`ProperSMul.isCompact_stabilizer`) and fixes `z₀`, a smaller neighbourhood `V₁` of `z₀` has
`K • V₁ ⊆ V₀`. The set `O K` is a neighbourhood of `K`, so by properness some neighbourhood `W` of
`x` is moved to meet itself only by elements of `O K` (`ProperSMul.mem_nhdsSet_stabilizer_iff`).
Take `V = V₁ ∩ ι⁻¹ W`. If `g • ι z = g' • ι z'` with `z, z' ∈ V`, then `h = g'⁻¹ g` moves `ι z ∈ W`
to `ι z' ∈ W`, so `h = o k` with `o ∈ O` and `k ∈ K`, and `[h, z] = [o, k • z]` and `[1, z']` lie
in the neighbourhood where the map is injective and have the same image. So `[h, z] = [1, z']`,
and translating by `g'` gives `[g, z] = [g', z']`.

## Main results

* `TauCeti.BalancedProduct.exists_mem_nhds_injOn_liftRightTranslation`: injectivity on
  `G ×_K V` for a neighbourhood `V` of `z₀`.

## References

* E. Meinrenken, *Group actions on manifolds*, lecture notes, University of Toronto, 2003,
  Theorem 1.25 and its proof (injectivity after shrinking, by properness).
-/

public section

open Set Filter Topology
open scoped Pointwise

namespace TauCeti.BalancedProduct

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] {K : Subgroup G}
  {Z : Type*} [MulAction K Z] [TopologicalSpace Z] [ContinuousSMul K Z]
  {M : Type*} [MulAction G M] [TopologicalSpace M] [ProperSMul G M]
  {ι : Z →ₑ[((↑) : K → G)] M}

/-- **The slice map is injective after shrinking the slice.** Let `G` act properly on `M`, let `K`
be the stabilizer of `ι z₀` for a `K`-equivariant `ι : Z → M` continuous at the `K`-fixed point
`z₀`, and let `[g, z] ↦ g • ι z` be injective on a neighbourhood of `[1, z₀]` in `G ×_K Z`. Then it
is injective on the classes `[g, z]` with `z` in some neighbourhood `V` of `z₀`. -/
theorem exists_mem_nhds_injOn_liftRightTranslation {z₀ : Z} (hz₀ : ∀ k : K, k • z₀ = z₀)
    (hK : (K : Set G) = MulAction.stabilizer G (ι z₀)) (hι : ContinuousAt ι z₀)
    {U : Set (BalancedProduct K K.RightTranslation Z)}
    (hU : U ∈ 𝓝 (mk K (K.toRightTranslation 1) z₀)) (hinj : InjOn (liftRightTranslation ι) U) :
    ∃ V ∈ 𝓝 z₀, InjOn (liftRightTranslation ι)
      {y | ∃ g, ∃ z ∈ V, y = mk K (K.toRightTranslation g) z} := by
  -- A product neighbourhood `O × V₀` of `(1, z₀)` maps into `U`.
  have hp := (isOpenQuotientMap_mk_toRightTranslation (K := K) (Z := Z)).continuous
  obtain ⟨O, hO, V₀, hV₀, hOV⟩ := mem_nhds_prod_iff.mp (hp.continuousAt.preimage_mem_nhds hU)
  -- `K` is compact and fixes `z₀`, so some neighbourhood `V₁` of `z₀` has `K • V₁ ⊆ V₀`.
  have : CompactSpace K := isCompact_iff_compactSpace.mp
    (hK ▸ ProperSMul.isCompact_stabilizer (G := G) (ι z₀))
  have hV₁ : ∀ᶠ z in 𝓝 z₀, ∀ k ∈ (univ : Set K), k • z ∈ V₀ := by
    refine isCompact_univ.eventually_forall_of_forall_eventually fun k _ ↦ ?_
    have hc : ContinuousAt (fun p : Z × K ↦ p.2 • p.1) (z₀, k) :=
      (continuous_snd.smul continuous_fst).continuousAt
    exact hc.preimage_mem_nhds (by simpa [hz₀ k] using hV₀)
  -- `O K` is a neighbourhood of the stabilizer, so properness gives a neighbourhood `W` of `ι z₀`
  -- moved to meet itself only by elements of `O K`.
  have hOK : O * (K : Set G) ∈ 𝓝ˢ (MulAction.stabilizer G (ι z₀) : Set G) := by
    rw [← hK, mem_nhdsSet_iff_forall]
    intro s hs
    have hc : ContinuousAt (fun g : G ↦ g * s⁻¹) s :=
      (continuous_id.mul continuous_const).continuousAt
    filter_upwards [hc.preimage_mem_nhds (by simpa using hO)] with g hg
    exact ⟨g * s⁻¹, hg, s, hs, inv_mul_cancel_right g s⟩
  obtain ⟨W, hW, hWsub⟩ := ProperSMul.mem_nhdsSet_stabilizer_iff.mp hOK
  refine ⟨{z | ∀ k ∈ (univ : Set K), k • z ∈ V₀} ∩ ι ⁻¹' W,
    inter_mem hV₁ (hι.preimage_mem_nhds hW), ?_⟩
  rintro _ ⟨g, z, ⟨hz, hzW⟩, rfl⟩ _ ⟨g', z', ⟨hz', hzW'⟩, rfl⟩ heq
  rw [liftRightTranslation_mk, liftRightTranslation_mk] at heq
  have hh : (g'⁻¹ * g) • ι z = ι z' := by rw [mul_smul, heq, inv_smul_smul]
  obtain ⟨o, ho, k, hk, hok⟩ := hWsub ⟨ι z', by rw [← hh]; exact smul_mem_smul_set hzW, hzW'⟩
  have hok' : o * k = g'⁻¹ * g := hok
  have h₁ : mk K (K.toRightTranslation (g'⁻¹ * g)) z ∈ U := by
    rw [← hok', ← show ((⟨k, hk⟩ : K) : G) = k from rfl, mk_toRightTranslation_mul]
    exact hOV (show (o, (⟨k, hk⟩ : K) • z) ∈ O ×ˢ V₀ from ⟨ho, hz ⟨k, hk⟩ (mem_univ _)⟩)
  have h₂ : mk K (K.toRightTranslation 1) z' ∈ U :=
    hOV (show ((1 : G), z') ∈ O ×ˢ V₀ from ⟨mem_of_mem_nhds hO, by simpa using hz' 1 (mem_univ _)⟩)
  have h := hinj h₁ h₂ (by rw [liftRightTranslation_mk, liftRightTranslation_mk, one_smul, hh])
  have h' := congrArg (g' • ·) h
  simpa only [smul_mk_toRightTranslation, mul_inv_cancel_left, mul_one] using h'

end TauCeti.BalancedProduct
