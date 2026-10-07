/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Group.Bounded

/-!
# Uniform local norm bounds over compact parameter spaces

This file records a uniform local boundedness consequence of continuity over a compact family.

## Main declarations

* `TauCeti.exists_eventually_norm_le_compact_family`: a continuous family indexed by a compact
  parameter space is uniformly bounded near any fiber contained in its open domain.
-/

public section

namespace TauCeti

open Filter Set
open scoped Topology

variable {X P α H : Type*} [TopologicalSpace X] [TopologicalSpace P] [TopologicalSpace α]
  [CompactSpace α] [NormedAddCommGroup H]

/-- A function continuous on an open set `W ⊆ X × P` is bounded on `{x} × ι(α)`, uniformly for
`x` near a point `x₀` with `{x₀} × ι(α) ⊆ W`, when `α` is compact and `ι` is continuous. -/
theorem exists_eventually_norm_le_compact_family {W : Set (X × P)} {F : X × P → H}
    {ι : α → P} (hι : Continuous ι) (hW : IsOpen W) (hF : ContinuousOn F W) {x₀ : X}
    (hx₀ : ∀ y, (x₀, ι y) ∈ W) :
    ∃ C, ∀ᶠ x in 𝓝 x₀, ∀ y, (x, ι y) ∈ W ∧ ‖F (x, ι y)‖ ≤ C := by
  obtain ⟨C, hC⟩ := isCompact_univ.exists_bound_of_continuousOn
    (hF.comp_continuous (continuous_const.prodMk hι) hx₀).continuousOn
  refine ⟨C + 1, ?_⟩
  have h := isCompact_univ.eventually_forall_of_forall_eventually (x₀ := x₀)
    (P := fun x y ↦ (x, ι y) ∈ W ∧ ‖F (x, ι y)‖ ≤ C + 1) fun y _ ↦ by
      have hmem : (x₀, ι y) ∈ W := hx₀ y
      have hlt : ∀ᶠ z in 𝓝 (x₀, ι y), ‖F z‖ < C + 1 :=
        (hF.continuousAt (hW.mem_nhds hmem)).norm.eventually_lt_const
          (lt_of_le_of_lt (hC y (mem_univ y)) (lt_add_one C))
      have hφ : Continuous fun z : X × α ↦ (z.1, ι z.2) := by fun_prop
      exact (hφ.tendsto (x₀, y)).eventually ((hW.eventually_mem hmem).and hlt) |>.mono
        fun z hz ↦ ⟨hz.1, hz.2.le⟩
  simpa only [mem_univ, true_imp_iff] using h

end TauCeti
