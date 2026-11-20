/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.DifferentialForm.Smooth
public import Mathlib.Geometry.Manifold.PartitionOfUnity

/-!
# Cutting off a differential form that is regular on an open set

Let `φ` be a differential form on a finite-dimensional Hausdorff σ-compact manifold, which is a
`C^n` section of the bundle of forms at every point of an open set `U`, and let `K ⊆ U` be closed.
Multiplying `φ` by a smooth function equal to one near `K` and to zero near the complement of `U`
gives a globally `C^n` form that agrees with `φ` near `K` and vanishes near the complement of `U`
(`TauCeti.RoughForm.exists_isSmoothForm_eventuallyEq_nhdsSet`).

This applies for instance to a form only defined, or only regular, away from a closed set, such
as the logarithmic derivative `dlog u` of a function `u` away from its zeros.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, second edition, Chapter 2 (smooth bump
  functions).
-/

public section

noncomputable section

open Bundle Set Filter
open scoped Manifold Topology ContDiff

namespace TauCeti.RoughForm

variable {E H M F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M] [NormedAddCommGroup F] [NormedSpace ℝ F]
  {k : ℕ}

/-- **Cutting off a form.** A form `φ` which is a `C^n` section at every point of an open set `U`
agrees near a closed set `K ⊆ U` with a globally `C^n` form vanishing near the complement of
`U`. -/
theorem exists_isSmoothForm_eventuallyEq_nhdsSet {n : ℕ∞} {φ : RoughForm I M F k}
    {U K : Set M} (hU : IsOpen U) (hK : IsClosed K) (hKU : K ⊆ U)
    (hφ : ∀ x ∈ U, ContMDiffAt I (I.prod 𝓘(ℝ, E [⋀^Fin k]→L[ℝ] F)) n
      (fun y ↦ TotalSpace.mk' (E [⋀^Fin k]→L[ℝ] F) y (φ y)) x) :
    ∃ ψ : RoughForm I M F k, IsSmoothForm I n ψ ∧ (∀ᶠ x in 𝓝ˢ K, ψ x = φ x) ∧
      ∀ᶠ x in 𝓝ˢ Uᶜ, ψ x = 0 := by
  have : LocallyCompactSpace H := I.locallyCompactSpace
  have : LocallyCompactSpace M := ChartedSpace.locallyCompactSpace H M
  obtain ⟨b, hb0, hb1, -⟩ := exists_contMDiffMap_zero_one_nhds_of_isClosed I hU.isClosed_compl hK
    (disjoint_compl_left_iff_subset.mpr hKU) (n := ⊤)
  refine ⟨fun x ↦ b x • φ x, ?_, hb1.mono fun x hx ↦ by simp [hx],
    hb0.mono fun x hx ↦ by simp [hx]⟩
  rw [isSmoothForm_def]
  intro x
  by_cases hx : x ∈ U
  · exact (b.contMDiff.of_le (mod_cast le_top) x).smul_section (hφ x hx)
  · refine ((IsSmoothForm.zero (I := I) (M := M) (F := F) (k := k) n).contMDiff x)
      |>.congr_of_eventuallyEq ?_
    filter_upwards [(nhds_le_nhdsSet (show x ∈ Uᶜ from hx)) hb0] with y hy
    simp only [hy, zero_smul, Pi.zero_apply]

end TauCeti.RoughForm
