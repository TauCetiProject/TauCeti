/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Algebra.CliffordAlgebra.Spin.Real.Stabilization.Basic
import TauCeti.Topology.Algebra.CliffordAlgebra.Spin.Covering.Obstruction

/-!
# Continuous lift obstructions for real Spin stabilization and one-block embeddings

In rank `n + 2 ≥ 2`, neither the left and right one-block embeddings
`g ↦ diag(g, I_m)` and `g ↦ diag(I_m, g)` nor first-coordinate stabilization `SO(n + 2) → SO(n + 3)`
admits a continuous lift to `Spin`. Each obstruction follows from
`TauCeti.not_exists_continuous_lift_of_spinLift_monoidHom` because the corresponding Spin-level map
is a continuous homomorphism sending `-1` to `-1`.

## Main results

* `TauCeti.not_exists_continuous_lift_realCliffordSpecialOrthogonalBlockSum_mk_one`: non-existence
  of a continuous Spin lift of `g ↦ diag(g, I_m)` in rank `≥ 2`.
* `TauCeti.not_exists_continuous_lift_realCliffordSpecialOrthogonalBlockSum_one_mk`: non-existence
  of a continuous Spin lift of `g ↦ diag(I_m, g)` in rank `≥ 2`.
* `TauCeti.not_exists_continuous_lift_realCliffordSpecialOrthogonalFirstInclusion`: non-existence
  of a continuous Spin lift of first-coordinate stabilization `SO(n + 2) → SO(n + 3)`.

## References

* H. B. Lawson and M.-L. Michelsohn, *Spin Geometry* (1989), Chapter I, §2 and Chapter II, §1.
-/

public section

namespace TauCeti

open _root_.CliffordAlgebra TauCeti.CliffordAlgebra TauCeti.QuadraticMap

noncomputable section

/-- **No continuous lift of the left one-block embedding `SO(n + 2) → SO((n + 2) + m)`,
`g ↦ diag(g, I_m)`, to `Spin((n + 2) + m)`.** -/
theorem not_exists_continuous_lift_realCliffordSpecialOrthogonalBlockSum_mk_one (n m : ℕ) :
    ¬ ∃ f : QuadraticMap.specialOrthogonalGroup (realCliffordForm (n + 2) 0) →
        realCliffordSpinGroupZero ((n + 2) + m),
      Continuous f ∧
        ∀ g, spinToSpecialOrthogonal (realCliffordForm ((n + 2) + m) 0) (f g) =
          realCliffordSpecialOrthogonalBlockSum (n + 2) m (g, 1) := by
  have : NeZero ((n + 2) + m) := ⟨by omega⟩
  exact not_exists_continuous_lift_of_spinLift_monoidHom
    ((realCliffordSpinBlockSum (n + 2) m).comp (MonoidHom.inl _ _))
    ((continuous_realCliffordSpinBlockSum (n + 2) m).comp (continuous_id.prodMk continuous_const))
    (fun x ↦ by simp)
    (by
      dsimp [MonoidHom.inl]
      rw [realCliffordSpinBlockSum_mk_one,
        (realCliffordSpinBlockInlIsometry (n + 2) m).spinGroupMap_negOne])

/-- **No continuous lift of the right one-block embedding `SO(n + 2) → SO(m + (n + 2))`,
`g ↦ diag(I_m, g)`, to `Spin(m + (n + 2))`.** -/
theorem not_exists_continuous_lift_realCliffordSpecialOrthogonalBlockSum_one_mk (m n : ℕ) :
    ¬ ∃ f : QuadraticMap.specialOrthogonalGroup (realCliffordForm (n + 2) 0) →
        realCliffordSpinGroupZero (m + (n + 2)),
      Continuous f ∧
        ∀ g, spinToSpecialOrthogonal (realCliffordForm (m + (n + 2)) 0) (f g) =
          realCliffordSpecialOrthogonalBlockSum m (n + 2) (1, g) := by
  have : NeZero (m + (n + 2)) := ⟨by omega⟩
  exact not_exists_continuous_lift_of_spinLift_monoidHom
    ((realCliffordSpinBlockSum m (n + 2)).comp (MonoidHom.inr _ _))
    ((continuous_realCliffordSpinBlockSum m (n + 2)).comp (continuous_const.prodMk continuous_id))
    (fun x ↦ by simp)
    (by
      dsimp [MonoidHom.inr]
      rw [realCliffordSpinBlockSum_one_mk,
        (realCliffordSpinBlockInrIsometry m (n + 2)).spinGroupMap_negOne])

/-- **No continuous lift of first-coordinate stabilization `SO(n + 2) → SO(n + 3)` to
`Spin(n + 3)`.** -/
theorem not_exists_continuous_lift_realCliffordSpecialOrthogonalFirstInclusion (n : ℕ) :
    ¬ ∃ f : QuadraticMap.specialOrthogonalGroup (realCliffordForm (n + 2) 0) →
        realCliffordSpinGroupZero ((n + 2) + 1),
      Continuous f ∧
        ∀ g, spinToSpecialOrthogonal (realCliffordForm ((n + 2) + 1) 0) (f g) =
          realCliffordSpecialOrthogonalFirstInclusion (n + 2) g :=
  not_exists_continuous_lift_of_spinLift_monoidHom
    (realCliffordSpinFirstInclusion (n + 2))
    (continuous_realCliffordSpinFirstInclusion (n + 2))
    (spinToSpecialOrthogonal_realCliffordSpinFirstInclusion (n + 2))
    (realCliffordSpinFirstInclusion_negOne (n + 2))

end

end TauCeti
