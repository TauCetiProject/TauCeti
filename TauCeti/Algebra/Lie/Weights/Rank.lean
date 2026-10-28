/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Lie.Rank
import Mathlib.Algebra.Module.Submodule.Union
public import Mathlib.Algebra.Lie.Weights.Killing

/-!
# A Cartan subalgebra contains a generic element

Let `L` be a finite-dimensional Lie algebra over an infinite field, and let `H` be a Cartan
subalgebra whose action on `L` is triangularizable with linear weights. This file chooses an
element `h : H` on which no root vanishes and proves that its Engel subalgebra is exactly `H`.
Mathlib's lower bound on the dimension of each Engel subalgebra then gives

`LieAlgebra.rank K L ≤ Module.finrank K H`.

The construction has two ingredients. First, finitely many nonzero linear functionals cannot
cover a vector space over an infinite field, so there is an `h` outside every root hyperplane.
Second, the generalized Cartan weight spaces span `L`. The generalized zero eigenspace of `ad h`
therefore receives only the zero weight space: every nonzero weight is a root, and its value at `h`
is nonzero by construction. The zero root space is the Cartan subalgebra.

## Main results

* `LieSubalgebra.exists_forall_root_apply_ne_zero`: some element of `H` is nonzero under every root.
* `LieSubalgebra.engel_eq_cartan_iff_forall_root_apply_ne_zero`: an element has Engel
  subalgebra `H` exactly when every root is nonzero on it.
* `LieSubalgebra.exists_engel_eq_cartan`: a Cartan subalgebra is the Engel subalgebra of one of its
  elements.
* `LieSubalgebra.rank_le_finrank_cartan`: the rank of `L` is at most the dimension of `H`.

It supplies only the `rank ≤ dim H` direction; the reverse inequality, which needs a separate
minimal-centralizer or Cartan-dimension argument, is not asserted here.

## References

* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, Springer GTM 9
  (1972), §15.1--15.3.
-/

public section

namespace LieSubalgebra

open LieAlgebra LieModule Module

variable {K L : Type*} [Field K] [LieRing L] [LieAlgebra K L] [FiniteDimensional K L]
  (H : LieSubalgebra K L) [H.IsCartanSubalgebra]

/-- **A generic element of a Cartan subalgebra avoids every root hyperplane.** Since the root set
is finite and each root is a nonzero linear functional, finite hyperplane avoidance over the
infinite field `K` supplies one `h : H` on which every root is nonzero. -/
theorem exists_forall_root_apply_ne_zero [Infinite K] [LieModule.LinearWeights K H L] :
    ∃ h : H, ∀ α ∈ H.root, (α : H → K) h ≠ 0 := by
  let f : H.root → Module.Dual K H := fun α ↦ (α.1 : H →ₗ[K] K)
  obtain ⟨h, hh⟩ := Module.Dual.exists_forall_ne_zero_of_forall_exists f fun α ↦ by
    simpa [f] using DFunLike.ne_iff.mp
      (Weight.coe_toLinear_ne_zero_iff.mpr (H.isNonZero_coe_root α))
  exact ⟨h, fun α hα ↦ hh ⟨α, hα⟩⟩

/-- An element of a Cartan subalgebra has Engel subalgebra equal to the Cartan subalgebra
if and only if no root vanishes on it. The Cartan action is assumed triangularizable. -/
theorem engel_eq_cartan_iff_forall_root_apply_ne_zero {h : H}
    [LieModule.IsTriangularizable K H L] :
    LieSubalgebra.engel K (h : L) = H ↔ ∀ α ∈ H.root, (α : H → K) h ≠ 0 := by
  let N : LieSubmodule K H L := genWeightSpaceOf L 0 h
  have hEngel : (LieSubalgebra.engel K (h : L)).toSubmodule = N.toSubmodule := by
    ext x
    rw [LieSubalgebra.mem_toSubmodule, LieSubmodule.mem_toSubmodule,
      LieSubalgebra.mem_engel_iff, LieModule.mem_genWeightSpaceOf]
    simp only [zero_smul, sub_zero, LieAlgebra.ad, LieSubalgebra.toEnd_eq]
  rw [← LieSubalgebra.toSubmodule_inj, hEngel, ← H.coe_toLieSubmodule,
    LieSubmodule.toSubmodule_inj, ← rootSpace_zero_eq K L H]
  constructor
  · intro hN χ hχ hχh
    have hle : genWeightSpace L χ ≤ rootSpace H 0 := by
      rw [← hN]
      simpa only [hχh] using genWeightSpace_le_genWeightSpaceOf L h χ
    have hdisj : Disjoint (genWeightSpace L χ) (rootSpace H 0) :=
      disjoint_genWeightSpace K H L (H.isNonZero_coe_root ⟨χ, hχ⟩)
    exact χ.genWeightSpace_ne_bot L (disjoint_self.mp (hdisj.mono_right hle))
  · intro hh
    refine le_antisymm ?_ (genWeightSpace_le_genWeightSpaceOf L h 0)
    rw [eq_iSup_inf_genWeightSpace K H L N]
    refine iSup_le fun χ ↦ ?_
    by_cases hχ : χ.IsZero
    · rw [hχ.eq]
      exact inf_le_right
    · have hχroot : χ ∈ H.root := by
        simpa [LieSubalgebra.root] using hχ
      have hχh : χ h ≠ 0 := hh χ hχroot
      have hdisj : Disjoint N (genWeightSpace L χ) :=
        (disjoint_genWeightSpaceOf K H L hχh.symm).mono_right
          (genWeightSpace_le_genWeightSpaceOf L h χ)
      simp [hdisj.eq_bot]

/-- **Every Cartan subalgebra is the Engel subalgebra of one of its elements** when its action has
linear weights and is triangularizable over an infinite field. -/
theorem exists_engel_eq_cartan [Infinite K] [LieModule.LinearWeights K H L]
    [LieModule.IsTriangularizable K H L] :
    ∃ h : H, LieSubalgebra.engel K (h : L) = H := by
  obtain ⟨h, hh⟩ := exists_forall_root_apply_ne_zero H
  exact ⟨h, (H.engel_eq_cartan_iff_forall_root_apply_ne_zero).mpr hh⟩

/-- **The rank is at most the dimension of a Cartan subalgebra.** Choose a root-regular Cartan
element whose Engel subalgebra is `H`, then apply Mathlib's Engel-subalgebra dimension bound
`LieAlgebra.rank_le_finrank_engel`. -/
theorem rank_le_finrank_cartan [Infinite K] [LieModule.LinearWeights K H L]
    [LieModule.IsTriangularizable K H L] :
    LieAlgebra.rank K L ≤ finrank K H := by
  obtain ⟨h, hh⟩ := exists_engel_eq_cartan H
  rw [← hh]
  exact LieAlgebra.rank_le_finrank_engel K (h : L)

end LieSubalgebra
