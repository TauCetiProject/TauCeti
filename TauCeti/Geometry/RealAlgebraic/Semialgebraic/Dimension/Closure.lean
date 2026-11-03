/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.RealAlgebraic.Semialgebraic.Dimension.Projection
import TauCeti.Geometry.RealAlgebraic.Semialgebraic.Topology

/-!
# Dimension of the closure of a semialgebraic set

The closure of a semialgebraic set has the same dimension as the set
(`TauCeti.IsSemialgebraic.semialgebraicDim_closure`).

The top-dimensional case is that a semialgebraic subset of `ℝ ^ n` with empty interior is nowhere
dense (`TauCeti.IsSemialgebraic.isNowhereDense_iff`), which fails for arbitrary sets, as the
rationals in `ℝ` show. The general case reduces to it through the characterization of dimension
by coordinate projections. If the closure of `s` has dimension `d`, some projection onto `d`
coordinates maps it onto a set with nonempty interior. That image lies in the closure of the
projection of `s`, which is semialgebraic, so the projection of `s` itself has nonempty interior
and `s` has dimension at least `d`.

## Main declarations

* `TauCeti.IsSemialgebraic.semialgebraicDim_closure`: the closure of a semialgebraic set has the
  same dimension.

## References

* J. Bochnak, M. Coste, M.-F. Roy, *Real Algebraic Geometry*, Ergebnisse der Mathematik und ihrer
  Grenzgebiete 36, Springer, 1998, Section 2.8.
-/

public section

open Set

namespace TauCeti

variable {n : ℕ} {s : Set (Fin n → ℝ)}

/-- **Dimension of the closure.** The closure of a semialgebraic set has the same dimension as
the set. -/
@[simp]
theorem IsSemialgebraic.semialgebraicDim_closure (hs : IsSemialgebraic s) :
    semialgebraicDim (closure s) = semialgebraicDim s := by
  refine le_antisymm ?_ (semialgebraicDim_mono subset_closure)
  rcases s.eq_empty_or_nonempty with rfl | hne
  · simp
  obtain ⟨-, -, -, -, d, hd, -⟩ := hs.closure.exists_isOpenEmbedding_semialgebraicDim_eq hne.closure
  -- A projection onto `d` coordinates maps `closure s` onto a set with nonempty interior.
  obtain ⟨ι, hι, hint⟩ := hs.closure.natCast_le_semialgebraicDim_iff.1 hd.ge
  rw [hd, hs.natCast_le_semialgebraicDim_iff]
  refine ⟨ι, hι, nonempty_iff_ne_empty.2 fun h0 ↦ hint.ne_empty ?_⟩
  -- That image lies in the closure of the projection of `s`, which is nowhere dense if the
  -- projection of `s` has empty interior.
  have hnd := (hs.image_comp ι).isNowhereDense_iff.2 h0
  rw [IsNowhereDense] at hnd
  exact subset_empty_iff.1 <| hnd ▸ interior_mono (image_closure_subset_closure_image (by fun_prop))

end TauCeti
