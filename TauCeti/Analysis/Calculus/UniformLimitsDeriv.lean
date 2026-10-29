/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.UniformLimitsDeriv
public import Mathlib.Topology.ContinuousMap.Bounded.Basic
public import Mathlib.Topology.Order.ProjIcc
import TauCeti.Analysis.Calculus.ContDiff.ClosedInterval

/-!
# Closed derivative graphs for bounded continuous functions

The Fréchet derivative identity is closed under uniform convergence of bounded continuous value
and derivative fields. The derivative field may be read through a uniformly continuous map.
These results supply the closed graph used to construct complete spaces of differentiable maps.
The corresponding one-dimensional graph on a closed interval includes the one-sided derivatives
at both endpoints.

The proofs use Mathlib's `hasFDerivAt_of_tendstoUniformly`.
-/

public section

namespace TauCeti

open Filter Topology
open scoped BoundedContinuousFunction

universe u v

/-- The set of bounded continuous fields satisfying a Fréchet derivative identity, with the
derivative read off the second field through a uniformly continuous map, is closed. -/
theorem isClosed_setOf_hasFDerivAt_comp {𝕜 : Type*} {E : Type u} {Y Z : Type*}
    [NontriviallyNormedField 𝕜] [IsRCLikeNormedField 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [NormedAddCommGroup Y] [NormedSpace 𝕜 Y] [PseudoMetricSpace Z]
    (L : Z → E →L[𝕜] Y) (hL : UniformContinuous L) :
    IsClosed {J : (E →ᵇ Y) × (E →ᵇ Z) | ∀ x, HasFDerivAt (J.1 : E → Y) (L (J.2 x)) x} := by
  rw [← isSeqClosed_iff_isClosed]
  intro J j hJ hjlim x
  apply hasFDerivAt_of_tendstoUniformly
      (f := fun n ↦ (J n).1) (f' := fun n y ↦ L ((J n).2 y))
      (g := j.1) (g' := fun y ↦ L (j.2 y)) (l := atTop)
  · exact hL.comp_tendstoUniformly
      (BoundedContinuousFunction.tendsto_iff_tendstoUniformly.mp
        ((continuous_snd.tendsto j).comp hjlim))
  · intro n y
    exact hJ n y
  · intro y
    exact (BoundedContinuousFunction.tendsto_iff_tendstoUniformly.mp
      ((continuous_fst.tendsto j).comp hjlim)).tendsto_at y

/-- The set of bounded continuous fields satisfying the Fréchet derivative identity is closed. -/
theorem isClosed_setOf_hasFDerivAt {𝕜 : Type*} {E : Type u} {Y : Type v}
    [NontriviallyNormedField 𝕜] [IsRCLikeNormedField 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [NormedAddCommGroup Y] [NormedSpace 𝕜 Y] :
    IsClosed {J : (E →ᵇ Y) × (E →ᵇ (E →L[𝕜] Y)) |
      ∀ x, HasFDerivAt (J.1 : E → Y) (J.2 x) x} :=
  isClosed_setOf_hasFDerivAt_comp id uniformContinuous_id

/-- The derivative graph of bounded continuous fields on a nondegenerate closed interval is
closed, including the one-sided derivative identities at its endpoints. The value field is
extended outside the interval by projection onto the interval. -/
theorem isClosed_setOf_hasDerivWithinAt_Icc {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F] {a b : ℝ} (hab : a < b) :
    IsClosed {J : (Set.Icc a b →ᵇ F) × (Set.Icc a b →ᵇ F) |
      ∀ t : Set.Icc a b,
        HasDerivWithinAt (fun s : ℝ ↦ J.1 (Set.projIcc a b hab.le s))
          (J.2 t) (Set.Icc a b) t} := by
  rw [← isSeqClosed_iff_isClosed]
  intro J j hJ hjlim t
  have hv := (BoundedContinuousFunction.tendsto_iff_tendstoUniformly.mp
    ((continuous_fst.tendsto j).comp hjlim)).comp (Set.projIcc a b hab.le)
  have hd := (BoundedContinuousFunction.tendsto_iff_tendstoUniformly.mp
    ((continuous_snd.tendsto j).comp hjlim)).comp (Set.projIcc a b hab.le)
  have hinter : ∀ x ∈ Set.Ioo a b,
      HasDerivAt (fun s : ℝ ↦ j.1 (Set.projIcc a b hab.le s))
        (j.2 (Set.projIcc a b hab.le x)) x := by
    intro x hx
    apply hasDerivAt_of_tendstoUniformlyOn
      (f := fun n s ↦ (J n).1 (Set.projIcc a b hab.le s))
      isOpen_Ioo hd.tendstoUniformlyOn _ _ hx
    · filter_upwards [] with n y hy
      have h := (hJ n ⟨y, Set.Ioo_subset_Icc_self hy⟩).hasDerivAt
        (Icc_mem_nhds hy.1 hy.2)
      simpa only [Function.comp_def, Set.projIcc_of_mem hab.le
        (Set.Ioo_subset_Icc_self hy)] using h
    · intro y _
      exact hv.tendsto_at y
  simpa only [Function.comp_def, Set.projIcc_val] using
    hasDerivWithinAt_Icc_of_continuousOn hab
      (j.1.continuous.comp continuous_projIcc).continuousOn
      (j.2.continuous.comp continuous_projIcc).continuousOn hinter t.property

end TauCeti
