/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Algebra.Module.ContinuousLinearMap.Index
public import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps
public import Mathlib.Analysis.Normed.Operator.Fredholm.Basic

import Mathlib.Analysis.Normed.Operator.Fredholm.Open

/-!
# Stability of Fredholm operators under small perturbations

This file records that Fredholm operators from a Banach space to a normed space are stable
under small perturbations and that their index is locally constant in the operator norm topology.
Equivalently, every Fredholm operator `T` has an `ε > 0` such that any operator `S` with
`‖S - T‖ < ε` is Fredholm and has the same index.

The stability itself is Mathlib's: `ContinuousLinearMap.IsFredholm.eventually_nhds` and
`ContinuousLinearMap.IsFredholm.eventually_nhds_index_eq` in
`Mathlib.Analysis.Normed.Operator.Fredholm.Open`, proved there from the block decomposition of a
`ContinuousLinearMap.FredholmPackage`. That file also shows that the Fredholm operators form an
open set (`ContinuousLinearMap.isOpen_setOfPred_isFredholm`). This file combines the two
neighbourhood statements and derives the operator-norm `ε` form and the openness of the set of
Fredholm operators of a fixed index.

## Main declarations

* `ContinuousLinearMap.IsFredholm.eventually_isFredholm_and_index_eq`: Fredholmness and the index
  are stable in a neighbourhood of a Fredholm operator.
* `ContinuousLinearMap.IsFredholm.exists_pos_isFredholm_and_index_eq_of_norm_sub_lt`: the
  corresponding operator-norm `ε` statement.
* `TauCeti.isOpen_setOf_isFredholm_index_eq`: Fredholm operators of a fixed index form an open
  set.

The statements follow McDuff--Salamon, *J-holomorphic Curves and Symplectic Topology*, Appendix
A.1.
-/

public section

namespace TauCeti

open Filter
open scoped Topology

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]

variable {E F : Type*}
variable [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
variable [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- Fredholmness and the Fredholm index are stable in a neighbourhood of a Fredholm operator. -/
theorem _root_.ContinuousLinearMap.IsFredholm.eventually_isFredholm_and_index_eq {T : E →L[𝕜] F}
    (hT : ContinuousLinearMap.IsFredholm T) :
    ∀ᶠ S : E →L[𝕜] F in 𝓝 T,
      ContinuousLinearMap.IsFredholm S ∧
        ContinuousLinearMap.index S = ContinuousLinearMap.index T := by
  simpa only [ContinuousLinearMap.index_def] using
    hT.eventually_nhds.and hT.eventually_nhds_index_eq

/-- A sufficiently small operator-norm perturbation of a Fredholm operator is Fredholm with the
same index. -/
theorem _root_.ContinuousLinearMap.IsFredholm.exists_pos_isFredholm_and_index_eq_of_norm_sub_lt
    {T : E →L[𝕜] F} (hT : ContinuousLinearMap.IsFredholm T) :
    ∃ ε > 0, ∀ S : E →L[𝕜] F, ‖S - T‖ < ε →
      ContinuousLinearMap.IsFredholm S ∧
        ContinuousLinearMap.index S = ContinuousLinearMap.index T := by
  obtain ⟨ε, hε, hball⟩ :=
    Metric.mem_nhds_iff.mp hT.eventually_isFredholm_and_index_eq
  exact ⟨ε, hε, fun S hS => hball (by simpa [dist_eq_norm] using hS)⟩

/-- For every integer `n`, the set of Fredholm operators of index `n` is open in the operator
norm topology. -/
theorem isOpen_setOf_isFredholm_index_eq (n : ℤ) :
    IsOpen {T : E →L[𝕜] F |
      ContinuousLinearMap.IsFredholm T ∧ ContinuousLinearMap.index T = n} := by
  rw [isOpen_iff_mem_nhds]
  rintro T ⟨hT, hindex⟩
  filter_upwards [hT.eventually_isFredholm_and_index_eq] with S hS
  exact ⟨hS.1, hS.2.trans hindex⟩

end TauCeti

end
