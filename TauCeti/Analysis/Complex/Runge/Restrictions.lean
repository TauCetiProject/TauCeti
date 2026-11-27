/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Germ.HolomorphicRestrictions.Basic
public import TauCeti.Analysis.Complex.Runge.Approximation

/-!
# Runge density in the algebra of holomorphic restrictions

On a compact subset `K` of an open plane set `U`, the restrictions of functions holomorphic
on `U` are dense in the algebra of continuous functions on `K` that extend holomorphically
to a neighborhood of `K` exactly when `U \ K` has no relatively compact component in `U`.

On `K` the compact-open topology is the sup-norm topology.

## Main results

* `TauCeti.isFilledIn_iff_denseRange_restrictToHolomorphicRestrictions` characterizes dense
  range of the restriction homomorphism by `TauCeti.IsFilledIn`.

## References

* A. Rainer, *Advanced Complex Analysis*, §11.
-/

public section

open Set TopologicalSpace

namespace TauCeti

/-- Runge's theorem (Rainer, *Advanced Complex Analysis*, §11). For compact `K ⊆ U`,
restrictions of functions holomorphic on the open set `U` are dense in `O(K)` in the sup-norm
topology if and only if `K` is filled in `U`, meaning that no connected component of `U \\ K`
has compact closure contained in `U`. -/
theorem isFilledIn_iff_denseRange_restrictToHolomorphicRestrictions {U : Opens ℂ} {K : Set ℂ}
    (hK : IsCompact K) (hKU : K ⊆ U) :
    IsFilledIn K U ↔ DenseRange (HolomorphicFunctions.restrictToHolomorphicRestrictions hKU) := by
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  rw [Metric.denseRange_iff]
  constructor
  · intro hfill φ ε hε
    obtain ⟨V, f, hV, hKV, hf, hfφ⟩ :=
      mem_holomorphicRestrictions_iff_exists_open.mp φ.property
    have hRunge := isRungeCompactPair_iff.mpr ⟨U.isOpen, hK, hKU, hfill⟩
    obtain ⟨g, hg, hfg⟩ := hRunge.exists_differentiableOn_norm_sub_lt hV hKV hf hε
    refine ⟨HolomorphicFunctions.of U g hg, ?_⟩
    rw [Subtype.dist_eq, ContinuousMap.dist_lt_iff hε]
    intro x
    simpa only [HolomorphicFunctions.restrictToHolomorphicRestrictions_apply,
      HolomorphicFunctions.of_apply, ← hfφ x, dist_eq_norm] using hfg x x.property
  · intro hdense
    refine ((isRungeCompactPair_iff_approximation U.isOpen hK hKU).mpr ?_).isFilledIn
    intro V hV hKV f hf ε hε
    let F : C(K, ℂ) := ⟨f ∘ Subtype.val, (hf.continuousOn.mono hKV).domRestrict⟩
    let φ : holomorphicRestrictions K :=
      ⟨F, mem_holomorphicRestrictions_iff_exists_open.mpr ⟨V, f, hV, hKV, hf, fun _ ↦ rfl⟩⟩
    obtain ⟨g, hg⟩ := hdense φ ε hε
    rw [Subtype.dist_eq, ContinuousMap.dist_lt_iff hε] at hg
    refine ⟨HolomorphicFunctions.extend g, HolomorphicFunctions.differentiableOn_extend g,
      fun z hz ↦ ?_⟩
    have hφ : φ.val ⟨z, hz⟩ = f z := rfl
    simpa only [HolomorphicFunctions.restrictToHolomorphicRestrictions_apply,
      ← HolomorphicFunctions.extend_apply, dist_eq_norm, hφ] using hg ⟨z, hz⟩

end TauCeti
