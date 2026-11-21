/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Convex.Basic
public import Mathlib.Analysis.LocallyConvex.Basic
public import Mathlib.Tactic.Linarith

/-!
# Star-convex sets: dilates and complements of closed half-subspaces

The dilates of a set `s` star-convex about `0` increase with the factor: `p • s ⊆ q • s` for
`0 ≤ p ≤ q` (`StarConvex.smul_mono`), and in particular for a convex set containing `0`
(`Convex.smul_mono_of_zero_mem`). Thresholds defined by dilates, such as successive minima, are
monotone because of this.

For a subspace `W` of a vector space `E` over a linearly ordered field and a linear functional
`φ` on `E`, the set `{x ∈ W | φ x ≤ 0}` is a closed half of `W`. Its complement in `E` is
star-convex about any `v ∈ W` with `0 < φ v`
(`TauCeti.starConvex_compl_setOf_mem_and_nonpos`): a segment from `v` that ends outside `W`
leaves `W` at once, and one that ends in `W` stays where `φ` is positive. This is the
subspace analogue of Mathlib's `starConvex_compl_Iic`. Every neighbourhood of `0` in a real
topological vector space contains such a centre outside the closed half-subspace, a small
positive multiple of any `v ∈ W` with `0 < φ v`
(`TauCeti.exists_mem_starConvex_compl_setOf_mem_and_nonpos`).

## References

`Convex.smul_mono_of_zero_mem` follows the lemma of the same name in the successive-minima
proposal for Mathlib by Kevin H. Wilson, `Mathlib/Analysis/Convex/Basic.lean` at
<https://github.com/khwilson/mathlib4/blob/8423d1c878e50d8504a230ffd9b6ec76ce6a08eb/Mathlib/Analysis/Convex/Basic.lean>
(Apache 2.0).
-/

public section

namespace TauCeti

variable {𝕜 E : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] [AddCommGroup E]
  [Module 𝕜 E]

/-- The complement of the closed half-subspace `{x ∈ W | φ x ≤ 0}` is star-convex about any
`v ∈ W` with `0 < φ v`. -/
theorem starConvex_compl_setOf_mem_and_nonpos {W : Submodule 𝕜 E} {φ : E →ₗ[𝕜] 𝕜} {v : E}
    (hv : v ∈ W) (hφv : 0 < φ v) : StarConvex 𝕜 v {x | x ∈ W ∧ φ x ≤ 0}ᶜ := by
  rintro x hx a b ha hb hab ⟨hmem, hle⟩
  rw [map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul] at hle
  rcases hb.eq_or_lt with rfl | hb
  · rw [add_zero] at hab
    subst hab
    linarith
  · have hxW : x ∈ W := by
      have h : b • x ∈ W := by simpa using W.sub_mem hmem (W.smul_mem a hv)
      exact (W.smul_mem_iff hb.ne').1 h
    exact hx ⟨hxW, by nlinarith⟩

open Topology in
/-- A neighbourhood `K` of `0` in a real topological vector space contains a point `c` outside the
closed half-subspace `{x ∈ W | φ x ≤ 0}` about which its complement is star-convex, as soon as
`0 < φ v` for some `v ∈ W`: `K` is absorbent, so it contains a positive multiple of `v`. -/
theorem exists_mem_starConvex_compl_setOf_mem_and_nonpos {F : Type*} [AddCommGroup F]
    [Module ℝ F] [TopologicalSpace F] [ContinuousSMul ℝ F] {K : Set F} (hK : K ∈ 𝓝 (0 : F))
    {W : Submodule ℝ F} {φ : F →ₗ[ℝ] ℝ} {v : F} (hv : v ∈ W) (hφv : 0 < φ v) :
    ∃ c ∈ K, c ∉ {x | x ∈ W ∧ φ x ≤ 0} ∧ StarConvex ℝ c {x | x ∈ W ∧ φ x ≤ 0}ᶜ := by
  have hev : ∀ᶠ t in 𝓝[>] (0 : ℝ), t • v ∈ K :=
    ((absorbent_nhds_zero hK).eventually_nhdsNE_zero v).filter_mono
      (nhdsWithin_mono _ fun _ h ↦ ne_of_gt h)
  obtain ⟨t, htK, ht : 0 < t⟩ := (hev.and self_mem_nhdsWithin).exists
  have htv : 0 < φ (t • v) := by simpa using mul_pos ht hφv
  exact ⟨t • v, htK, fun h ↦ (not_le.2 htv) h.2,
    starConvex_compl_setOf_mem_and_nonpos (W.smul_mem t hv) htv⟩

end TauCeti

section Dilate

open scoped Pointwise

variable {𝕜 E : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] [AddCommGroup E]
  [Module 𝕜 E] {s : Set E} {p q : 𝕜}

/-- The dilates of a set star-convex about `0` increase with the factor: `p • s ⊆ q • s` whenever
`0 ≤ p ≤ q`. -/
theorem StarConvex.smul_mono (hs : StarConvex 𝕜 0 s) (hp : 0 ≤ p) (hpq : p ≤ q) :
    p • s ⊆ q • s := by
  rintro _ ⟨x, hx, rfl⟩
  rcases (hp.trans hpq).eq_or_lt with rfl | hq
  · obtain rfl := le_antisymm hpq hp
    exact Set.smul_mem_smul_set hx
  · -- `p • x = q • ((q⁻¹ * p) • x)`, and `(q⁻¹ * p) • x ∈ s` as `0 ≤ q⁻¹ * p ≤ 1`.
    rw [Set.mem_smul_set_iff_inv_smul_mem₀ hq.ne', smul_smul]
    exact hs.smul_mem hx (mul_nonneg (inv_nonneg.2 hq.le) hp) ((inv_mul_le_one₀ hq).2 hpq)

/-- The dilates of a convex set containing `0` increase with the factor: `p • s ⊆ q • s` whenever
`0 ≤ p ≤ q`. -/
theorem Convex.smul_mono_of_zero_mem (hs : Convex 𝕜 s) (h₀ : (0 : E) ∈ s) (hp : 0 ≤ p)
    (hpq : p ≤ q) : p • s ⊆ q • s :=
  (hs.starConvex h₀).smul_mono hp hpq

end Dilate
