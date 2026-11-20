/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.Orthonormal.CalibratedFrame
public import TauCeti.Geometry.Manifold.Instances.Stiefel
import TauCeti.Geometry.Manifold.Instances.Stiefel.Comass
import TauCeti.Topology.Algebra.Module.Alternating.TopDegree

/-!
# Calibrated frames in the Stiefel manifold

The frames calibrated by a real alternating `k`-form `φ`, the orthonormal frames on which `φ`
takes the value one, form a closed subset of the Stiefel manifold of orthonormal `k`-frames, and a
compact one when the space is finite-dimensional. On a finite-dimensional space a form of comass
one in positive degree calibrates some frame: its comass is attained on an orthonormal frame, and
negating one vector of that frame turns the value `-1` into `1`. In degree zero this fails for
the constant `-1`, which has comass one and calibrates nothing.
-/

public section

open Module

namespace ContinuousAlternatingMap

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {k : ℕ}

/-- The frames calibrated by a form are a closed subset of the frames. -/
theorem isClosed_setOf_isCalibratedFrame (φ : E [⋀^Fin k]→L[ℝ] ℝ) :
    IsClosed {v | φ.IsCalibratedFrame v} := by
  have h : {v | φ.IsCalibratedFrame v} = TauCeti.stiefel E k ∩ {v | φ v = 1} := by
    ext v
    simp [isCalibratedFrame_iff, TauCeti.mem_stiefel_iff]
  rw [h]
  exact (TauCeti.isClosed_stiefel E k).inter (isClosed_eq φ.cont continuous_const)

variable [FiniteDimensional ℝ E]

/-- On a finite-dimensional space, the frames calibrated by a form are a compact subset of the
Stiefel manifold. -/
theorem isCompact_setOf_isCalibratedFrame (φ : E [⋀^Fin k]→L[ℝ] ℝ) :
    IsCompact {v | φ.IsCalibratedFrame v} :=
  (TauCeti.isCompact_stiefel E k).of_isClosed_subset φ.isClosed_setOf_isCalibratedFrame
    fun _ hv ↦ TauCeti.mem_stiefel_iff.2 hv.orthonormal

/-- On a finite-dimensional space, a form of comass one in positive degree calibrates some
frame. -/
theorem exists_isCalibratedFrame_of_norm_eq_one {φ : E [⋀^Fin k]→L[ℝ] ℝ} (hφ : ‖φ‖ = 1)
    (hk : k ≠ 0) : ∃ v, φ.IsCalibratedFrame v := by
  -- Above the dimension the form vanishes, so its comass would be zero.
  have hkE : k ≤ finrank ℝ E := by
    by_contra hlt
    simp [φ.eq_zero_of_finrank_lt (by simpa using hlt)] at hφ
  obtain ⟨v, hv, hnorm⟩ := φ.exists_orthonormal_norm_eq hkE
  rw [hφ, Real.norm_eq_abs] at hnorm
  rcases (abs_eq zero_le_one).1 hnorm with h | h
  · exact ⟨v, hv, h⟩
  · exact ⟨_, (isCalibratedFrame_neg_iff_update_neg ⟨0, Nat.pos_of_ne_zero hk⟩).1
      ⟨hv, by simp [h]⟩⟩

end ContinuousAlternatingMap
