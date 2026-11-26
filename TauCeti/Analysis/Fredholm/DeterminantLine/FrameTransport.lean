/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Fredholm.DeterminantLine.Bundle
public import TauCeti.Topology.VectorBundle.FrameTransport
import TauCeti.Topology.UnitInterval.Contractible

/-!
# Linear transport of Fredholm determinant lines along paths

The determinant lines `det (ker T) ⊗ (det (F ⧸ range T))^*` of the real Fredholm operators form a
line bundle `TauCeti.FredholmDetLine ℝ E F` over the space of Fredholm operators. Along a path of
Fredholm operators, orientations of the determinant lines are transported canonically, by lifting
the path to the orientation double cover. A linear isomorphism between the determinant lines at the
two ends needs an additional choice. This file makes that choice a continuous frame of the
determinant lines along the path, using the linear transport of frames,
`TauCeti.frameTransport`.

Every continuous path `T` of real Fredholm operators carries such a frame, and its linear transport
`φ 1 ∘ (φ 0)⁻¹`, from the determinant line of `T 0` to that of `T 1`, carries every orientation to
its orientation transport along `T`
(`TauCeti.FredholmDetLine.exists_continuous_frame_and_orientationTransport_eq_map`). The linear
transport is not determined by the path: the transports of two continuous frames differ by a
positive scalar (`TauCeti.exists_pos_forall_frameTransport_eq_smul`), which is the change-of-choice
law, so their common orientation is the only canonical datum.

## Main results

* `TauCeti.FredholmDetLine.exists_continuous_frame_and_orientationTransport_eq_map`: along a
  continuous path of real Fredholm operators the determinant lines have a continuous frame, whose
  linear transport induces orientation transport.

## References

* D. McDuff, D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  AMS Colloquium Publications 52, 2012, Section A.2 (determinant line bundles).
* A. Zinger, *The determinant line bundle for Fredholm operators: construction, properties, and
  classification*, Math. Scand. 118 (2016), 203–268, arXiv:1304.6368.
-/

public section

noncomputable section

open Bundle
open scoped unitInterval

namespace TauCeti.FredholmDetLine

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

/-- **Linear transport of determinant lines.** Along a continuous path `T` of real Fredholm
operators the determinant lines have a continuous frame `φ`, linear isomorphisms
`φ t : ℝ ≃ det (T t)` depending continuously on `t` in the determinant line bundle. Its linear
transport `φ 1 ∘ (φ 0)⁻¹` carries every orientation of the determinant line of `T 0` to its
orientation transport along `T`, the monodromy of the orientation double cover. -/
theorem exists_continuous_frame_and_orientationTransport_eq_map
    (T : C(I, {T : E →L[ℝ] F // T.IsFredholm})) :
    ∃ φ : ∀ t : I, ℝ ≃L[ℝ] FredholmDetLine ℝ E F (T t),
      (Continuous fun q : I × ℝ ↦ TotalSpace.mk' ℝ (T q.1) (φ q.1 q.2)) ∧
      ∀ o, VectorBundleOrientationCover.orientationTransport (FredholmDetLine ℝ E F)
        (by simp : Fintype.card (Fin 1) = Module.finrank ℝ ℝ) ⟨T, rfl, rfl⟩ o =
          Orientation.map (Fin 1) (frameTransport φ 0 1).toLinearEquiv o := by
  obtain ⟨φ, hφ⟩ := exists_continuous_frame (𝕜 := ℝ) (F := ℝ) (E := FredholmDetLine ℝ E F)
    T.continuous
  exact ⟨φ, hφ, orientationTransport_eq_map_frameTransport _ T hφ⟩

end TauCeti.FredholmDetLine
