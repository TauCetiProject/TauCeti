/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.TensorProduct.Map
public import TauCeti.Order.Filter.ZeroAndBoundedAtFilter

/-!
# Countable support for tensors with null-family modules

When a topological `A`-module `N` is `T₁` with countably generated neighbourhoods of `0`, every
family `f ∈ c₀(ι, N)` (`Filter.zeroAtFilterSubmodule (β := N) A Filter.cofinite`) has countable
support (`Filter.ZeroAtFilter.countable_support`). Since every element of `M ⊗[A] c₀(ι, N)` is a
finite sum of pure tensors, it lies in the image of extension-by-zero from `M ⊗[A] c₀(S, N)` for
some countable subset `S ⊆ ι` (`TensorProduct.exists_countable_lTensor_zeroAtFilterExtend_eq`).
Combined with `Filter.zeroAtFilterComap_comp_extend`, this reduces tensor-product properties of
`c₀(ι, N)` over arbitrary index types `ι` to countable index types.

## Main results

* `TensorProduct.exists_countable_lTensor_zeroAtFilterExtend_eq`: every tensor in
  `M ⊗[A] c₀(ι, N)` comes from `M ⊗[A] c₀(S, N)` for some countable `S : Set ι`.
-/

public section

open Filter
open scoped TensorProduct Topology

namespace TensorProduct

/-- Every tensor in `M ⊗[A] c₀(ι, N)` is supported on a countable subset of `ι`, whenever `N` is
`T₁` with countably generated neighbourhoods of `0`: it lies in the image of
`LinearMap.lTensor M (Filter.zeroAtFilterExtend A N Subtype.val)` for some countable `S : Set ι`. -/
theorem exists_countable_lTensor_zeroAtFilterExtend_eq {A M N ι : Type*} [CommSemiring A]
    [AddCommMonoid M] [Module A M] [AddCommMonoid N] [TopologicalSpace N] [Module A N]
    [ContinuousAdd N] [ContinuousConstSMul A N] [T1Space N] [(𝓝 (0 : N)).IsCountablyGenerated]
    (z : M ⊗[A] Filter.zeroAtFilterSubmodule (β := N) A (Filter.cofinite : Filter ι)) :
    ∃ (S : Set ι), S.Countable ∧
      ∃ w : M ⊗[A] Filter.zeroAtFilterSubmodule (β := N) A (Filter.cofinite : Filter S),
        LinearMap.lTensor M (zeroAtFilterExtend A N (Subtype.val : S → ι)) w = z := by
  induction z using TensorProduct.inductionOn with
  | tmul m f =>
    refine ⟨Function.support (f : ι → N), f.2.countable_support,
      m ⊗ₜ[A] zeroAtFilterComap A N Subtype.val_injective.tendsto_cofinite f, ?_⟩
    simp only [LinearMap.lTensor_tmul]
    congr 1
    refine Subtype.ext <| funext fun x ↦ ?_
    rw [congrFun (coe_zeroAtFilterExtend _ _) x, coe_zeroAtFilterComap]
    by_cases hx : (f : ι → N) x = 0
    · rw [Function.extend_apply' _ _ _ fun ⟨s, hs⟩ ↦ s.2 (hs.symm ▸ hx), Pi.zero_apply, hx]
    · exact Subtype.val_injective.extend_apply ((f : ι → N) ∘ Subtype.val) 0 ⟨x, hx⟩
  | add z₁ z₂ ih₁ ih₂ =>
    obtain ⟨S₁, hS₁, w₁, rfl⟩ := ih₁
    obtain ⟨S₂, hS₂, w₂, rfl⟩ := ih₂
    refine ⟨S₁ ∪ S₂, hS₁.union hS₂,
      LinearMap.lTensor M (zeroAtFilterExtend A N (Set.inclusion Set.subset_union_left)) w₁ +
        LinearMap.lTensor M (zeroAtFilterExtend A N (Set.inclusion Set.subset_union_right)) w₂,
      ?_⟩
    rw [map_add, ← LinearMap.comp_apply, ← LinearMap.comp_apply, ← LinearMap.lTensor_comp,
      ← LinearMap.lTensor_comp,
      zeroAtFilterExtend_comp A N (Set.inclusion_injective _) Subtype.val_injective,
      zeroAtFilterExtend_comp A N (Set.inclusion_injective _) Subtype.val_injective,
      Set.val_comp_inclusion, Set.val_comp_inclusion]

end TensorProduct
