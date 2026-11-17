/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Eigenspace.Basic

/-!
# Generalized eigenspaces for nonzero eigenvalues lie in the range

Let `f` be an endomorphism of a vector space and `μ ≠ 0`. A generalized eigenvector `w` for `μ`
satisfies `μ • w = f w - (f - μ) w`, so by induction on the exponent it lies in every submodule
containing the range of `f`. Thus the generalized eigenspaces of `f` for nonzero eigenvalues only
see the range of `f`, and `f` has the same nonzero eigenvalues as its restriction to any such
submodule.

## Main results

* `Module.End.genEigenspace_le_of_range_le`: for `μ ≠ 0`, every generalized eigenspace of `f` for
  `μ` lies in every submodule containing the range of `f`.
* `Module.End.hasEigenvalue_restrict_iff_of_range_le`: the restriction of `f` to a submodule
  containing its range has the same nonzero eigenvalues as `f`.
-/

public section

namespace Module.End

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

/-- For `μ ≠ 0`, the generalized eigenvectors for `μ` of an endomorphism `f` lie in every submodule
containing the range of `f`. -/
theorem genEigenspace_le_of_range_le {f : End K V} {S : Submodule K V}
    (hf : LinearMap.range f ≤ S) {μ : K} (hμ : μ ≠ 0) (k : ℕ∞) : f.genEigenspace μ k ≤ S :=
  fun w hw ↦ by
  obtain ⟨l, -, hl⟩ := mem_genEigenspace.1 hw
  suffices h : ∀ (l : ℕ) (w : V), ((f - μ • 1) ^ l) w ∈ S → w ∈ S from
    h l w ((LinearMap.mem_ker.1 hl).symm ▸ S.zero_mem)
  intro l
  induction l with
  | zero => simp
  | succ l ih =>
    intro w hw
    rw [pow_succ, mul_apply_eq_comp] at hw
    have h := S.sub_mem (hf (LinearMap.mem_range_self f w)) (ih _ hw)
    rw [LinearMap.sub_apply, sub_sub_cancel, LinearMap.smul_apply, one_apply_eq_self] at h
    exact (S.smul_mem_iff hμ).1 h

/-- The restriction of an endomorphism `f` to a submodule containing its range has the same nonzero
eigenvalues as `f`. -/
theorem hasEigenvalue_restrict_iff_of_range_le {f : End K V} {S : Submodule K V}
    (hf : LinearMap.range f ≤ S) {μ : K} (hμ : μ ≠ 0) :
    HasEigenvalue (f.restrict fun w _ ↦ hf (LinearMap.mem_range_self f w)) μ ↔
      f.HasEigenvalue μ := by
  rw [hasEigenvalue_iff, hasEigenvalue_iff,
    ← (Submodule.map_injective_of_injective S.injective_subtype).ne_iff, Submodule.map_bot,
    ← Submodule.inf_genEigenspace,
    inf_eq_right.2 (genEigenspace_le_of_range_le hf hμ 1)]

end Module.End
