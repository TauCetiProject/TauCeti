/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Projection.Basic
public import TauCeti.Analysis.CStarAlgebra.Module.Complemented.Basic

/-!
# Comparison of C⋆-submodule orthogonal complementability with Hilbert spaces (`A = ℂ`)

When the coefficient C⋆-algebra is `A = ℂ`, a complex inner product space `E` is a Hilbert
C⋆-module over `ℂ`, and `TauCeti.CStarSubmodule.orthogonal` and
`TauCeti.CStarSubmodule.IsOrthogonallyComplemented` agree with Mathlib's `Submodule.orthogonal`,
`Submodule.HasOrthogonalProjection`, and `Submodule.starProjection`.

## Main declarations

* `TauCeti.CStarSubmodule.toSubmodule_orthogonal_complex`:
  `F.orthogonal.toSubmodule = F.toSubmoduleᗮ`.
* `TauCeti.CStarSubmodule.isOrthogonallyComplemented_complex_iff`:
  `F.IsOrthogonallyComplemented ↔ F.toSubmodule.HasOrthogonalProjection`.
* `TauCeti.CStarSubmodule.isOrthogonallyComplemented_of_isClosed_complex`: every closed complex
  submodule of a complete inner product space is orthogonally complemented.
* `TauCeti.CStarSubmodule.starProjection_complex`: agreement of
  `IsOrthogonallyComplemented.starProjection` with `Submodule.starProjection`.
* `Submodule.toSubmodule_orthogonal_toCStarSubmodule_complex` and
  `Submodule.isOrthogonallyComplemented_toCStarSubmodule_complex_iff`: the same comparisons for a
  `Submodule ℂ E` viewed via `Submodule.toCStarSubmodule`.

## References

* E. Christopher Lance, *Hilbert C⋆-Modules: A Toolkit for Operator Algebraists*, Chapter 1 and
  Chapter 3.
* Iain Raeburn and Dana P. Williams, *Morita Equivalence and Continuous-Trace C⋆-Algebras*,
  Chapter 2.
-/

public section

namespace TauCeti.CStarSubmodule

section ComplexComparison

open ComplexOrder

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- Over `A = ℂ`, `CStarSubmodule.orthogonal` agrees with Mathlib's `Submodule.orthogonal`. -/
theorem toSubmodule_orthogonal_complex (F : CStarSubmodule ℂ E) :
    F.orthogonal.toSubmodule = F.toSubmoduleᗮ := by
  ext y
  simp [Submodule.mem_orthogonal]

/-- Over `A = ℂ`, orthogonal complementability of a C⋆-submodule agrees with Mathlib's
`Submodule.HasOrthogonalProjection`. -/
theorem isOrthogonallyComplemented_complex_iff (F : CStarSubmodule ℂ E) :
    F.IsOrthogonallyComplemented ↔ F.toSubmodule.HasOrthogonalProjection := by
  rw [isOrthogonallyComplemented_iff_exists_add]
  constructor
  · intro h
    refine ⟨fun x ↦ ?_⟩
    obtain ⟨y, hy, z, hz, rfl⟩ := h x
    refine ⟨y, hy, ?_⟩
    rw [add_sub_cancel_left, ← toSubmodule_orthogonal_complex]
    exact hz
  · intro h x
    obtain ⟨y, hy, hsub⟩ := h.exists_orthogonal x
    refine ⟨y, hy, x - y, ?_, add_sub_cancel _ _⟩
    rw [← mem_toSubmodule, toSubmodule_orthogonal_complex]
    exact hsub

/-- Over `A = ℂ` in a complete inner product space, every closed submodule is orthogonally
complemented. -/
theorem isOrthogonallyComplemented_of_isClosed_complex [CompleteSpace E] (F : CStarSubmodule ℂ E)
    (hF : IsClosed (F : Set E)) : F.IsOrthogonallyComplemented := by
  have _ : CompleteSpace F.toSubmodule := hF.completeSpace_coe
  exact (isOrthogonallyComplemented_complex_iff F).mpr inferInstance

/-- Over `A = ℂ`, `IsOrthogonallyComplemented.starProjection` agrees with Mathlib's
`Submodule.starProjection`. -/
theorem starProjection_complex (F : CStarSubmodule ℂ E) [F.toSubmodule.HasOrthogonalProjection] :
    ((isOrthogonallyComplemented_complex_iff F).mpr inferInstance).starProjection =
      F.toSubmodule.starProjection := by
  ext x
  refine ((isOrthogonallyComplemented_complex_iff F).mpr
    inferInstance).eq_starProjection_of_mem_orthogonal
    (F.toSubmodule.starProjection_apply_mem x) ?_
  rw [← mem_toSubmodule, toSubmodule_orthogonal_complex]
  exact F.toSubmodule.sub_starProjection_mem_orthogonal x

end ComplexComparison

end TauCeti.CStarSubmodule

namespace Submodule

open ComplexOrder TauCeti.CStarSubmodule

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- Over `A = ℂ`, the orthogonal complement of a `Submodule ℂ E` viewed as a `CStarSubmodule ℂ E`
agrees with Mathlib's `Submodule.orthogonal`. -/
theorem toSubmodule_orthogonal_toCStarSubmodule_complex (K : Submodule ℂ E) :
    K.toCStarSubmodule.orthogonal.toSubmodule = Kᗮ := by
  rw [toSubmodule_orthogonal_complex, Submodule.toSubmodule_toCStarSubmodule,
    Submodule.restrictScalars_self]

/-- Over `A = ℂ`, a `Submodule ℂ E` is orthogonally complemented as a `CStarSubmodule ℂ E` if and
only if it satisfies `Submodule.HasOrthogonalProjection`. -/
theorem isOrthogonallyComplemented_toCStarSubmodule_complex_iff (K : Submodule ℂ E) :
    K.toCStarSubmodule.IsOrthogonallyComplemented ↔ K.HasOrthogonalProjection := by
  rw [isOrthogonallyComplemented_complex_iff, Submodule.toSubmodule_toCStarSubmodule,
    Submodule.restrictScalars_self]

end Submodule
