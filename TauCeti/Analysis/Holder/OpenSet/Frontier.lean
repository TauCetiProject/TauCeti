/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Holder.OpenSet.Basic

/-!
# Elements of `C^{k,α}(Ω)` vanishing on the frontier

Let `Ω` be an open set of a real normed space `E`. An element `f` of `C^{k,α}(Ω, F)` is a
function on `Ω` only, so its boundary values are limits: `f` *vanishes on the frontier* if
`f(y) → 0` as `y → x` within `Ω`, for every `x ∈ ∂Ω`. These elements form a closed submodule of
`C^{k,α}(Ω, F)` (`TauCeti.CkHolderSpaceOn.vanishingOnFrontierSubmodule`), hence a Banach space
when `F` is complete. It is the domain of the operators of the Dirichlet problem with zero
boundary values in the Hölder spaces of a domain: for a second-order operator `L`, the problem
`L u = f` in `Ω`, `u = 0` on `∂Ω`, with `u ∈ C^{2,α}(Ω)`, asks that `L` be surjective from this
submodule of `C^{2,α}(Ω)` onto `C^{0,α}(Ω)`.

Since `Ω` is open, its frontier does not meet `Ω`, and the extension by zero
`TauCeti.CkHolderSpaceOn.extend` vanishes there. So `f` vanishes on the frontier exactly when its
extension by zero is continuous on `closure Ω`
(`TauCeti.CkHolderSpaceOn.mem_vanishingOnFrontierSubmodule_iff_continuousOn_extend`). This is the
form in which maximum principles on `closure Ω` apply to `f`.

## Main declarations

* `TauCeti.CkHolderSpaceOn.vanishingOnFrontierSubmodule`: the submodule of elements of
  `C^{k,α}(Ω, F)` vanishing on the frontier of `Ω`.
* `TauCeti.CkHolderSpaceOn.isClosed_vanishingOnFrontierSubmodule`: it is closed, so it is a
  Banach space when `F` is complete.
* `TauCeti.CkHolderSpaceOn.mem_vanishingOnFrontierSubmodule_iff_continuousOn_extend`: vanishing
  on the frontier is continuity of the extension by zero on `closure Ω`.
-/

public section

noncomputable section

namespace TauCeti.CkHolderSpaceOn

open Filter Set TopologicalSpace
open scoped NNReal Topology

variable {k : ℕ} {α : ℝ≥0} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {Ω : Opens E}
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The extension by zero of an element of `C^{k,α}(Ω)` vanishes on the frontier of `Ω`. -/
theorem extend_apply_of_mem_frontier (f : CkHolderSpaceOn k α Ω F) {x : E}
    (hx : x ∈ frontier (Ω : Set E)) : f.extend x = 0 :=
  f.extend_apply_of_notMem fun hxΩ ↦ (Ω.isOpen.frontier_eq ▸ hx).2 hxΩ

variable (k α Ω F) in
/-- The elements of `C^{k,α}(Ω, F)` **vanishing on the frontier** of `Ω`: those `f` with
`f(y) → 0` as `y → x` within `Ω`, for every frontier point `x` of `Ω`. -/
def vanishingOnFrontierSubmodule : Submodule ℝ (CkHolderSpaceOn k α Ω F) where
  carrier := {f | ∀ x ∈ frontier (Ω : Set E), Tendsto f.extend (𝓝[Ω] x) (𝓝 0)}
  zero_mem' x _ := tendsto_const_nhds.congr' <| eventually_nhdsWithin_of_forall fun y hy ↦ by
    rw [← Subtype.coe_mk y hy, extend_apply, coe_zero, Pi.zero_apply]
  add_mem' {f g} hf hg x hx := by
    have h := (hf x hx).add (hg x hx)
    rw [add_zero] at h
    refine h.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with y hy
    rw [← Subtype.coe_mk y hy, extend_apply, extend_apply, extend_apply, coe_add]
    rfl
  smul_mem' c f hf x hx := by
    have h := (hf x hx).const_smul c
    rw [smul_zero] at h
    refine h.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with y hy
    rw [← Subtype.coe_mk y hy, extend_apply, extend_apply, coe_smul]
    rfl

theorem mem_vanishingOnFrontierSubmodule_iff {f : CkHolderSpaceOn k α Ω F} :
    f ∈ vanishingOnFrontierSubmodule k α Ω F ↔
      ∀ x ∈ frontier (Ω : Set E), Tendsto f.extend (𝓝[Ω] x) (𝓝 0) :=
  Iff.rfl

/-- An element of `C^{k,α}(Ω)` vanishes on the frontier of `Ω` if and only if its extension by
zero is continuous on `closure Ω`. -/
theorem mem_vanishingOnFrontierSubmodule_iff_continuousOn_extend {f : CkHolderSpaceOn k α Ω F} :
    f ∈ vanishingOnFrontierSubmodule k α Ω F ↔ ContinuousOn f.extend (closure (Ω : Set E)) := by
  refine ⟨fun hf x hx ↦ ?_, fun hf x hx ↦ ?_⟩
  · rcases (closure_eq_self_union_frontier (Ω : Set E) ▸ hx : x ∈ (Ω : Set E) ∪ _) with hxΩ | hxF
    · exact (f.contDiffOn_extend.continuousOn.continuousAt
        (Ω.isOpen.mem_nhds hxΩ)).continuousWithinAt
    -- At a frontier point, the extension vanishes nearby outside `Ω` and tends to `0` inside.
    refine ContinuousAt.continuousWithinAt ?_
    rw [ContinuousAt, f.extend_apply_of_mem_frontier hxF, ← nhdsWithin_univ,
      ← union_compl_self (Ω : Set E), nhdsWithin_union]
    exact (hf x hxF).sup <| tendsto_const_nhds.congr' <| eventually_nhdsWithin_of_forall
      fun y hy ↦ (f.extend_apply_of_notMem hy).symm
  · rw [← f.extend_apply_of_mem_frontier hx]
    exact (hf x (frontier_subset_closure hx)).tendsto.mono_left
      (nhdsWithin_mono x subset_closure)

/-- An element of `C^{k,α}(Ω)` vanishing on the frontier has extension by zero continuous on
`closure Ω`. -/
theorem continuousOn_extend_closure {f : CkHolderSpaceOn k α Ω F}
    (hf : f ∈ vanishingOnFrontierSubmodule k α Ω F) :
    ContinuousOn f.extend (closure (Ω : Set E)) :=
  mem_vanishingOnFrontierSubmodule_iff_continuousOn_extend.1 hf

/-- The elements of `C^{k,α}(Ω)` vanishing on the frontier form a closed set: a limit in
`C^{k,α}(Ω)` is in particular a uniform limit on `Ω`, which preserves boundary limits. -/
theorem isClosed_vanishingOnFrontierSubmodule :
    IsClosed (vanishingOnFrontierSubmodule k α Ω F : Set (CkHolderSpaceOn k α Ω F)) := by
  refine isClosed_of_closure_subset fun f hf x hx ↦ Metric.tendsto_nhds.2 fun ε hε ↦ ?_
  obtain ⟨g, hg, hfg⟩ := Metric.mem_closure_iff.1 hf (ε / 2) (half_pos hε)
  filter_upwards [Metric.tendsto_nhds.1 (hg x hx) (ε / 2) (half_pos hε), self_mem_nhdsWithin]
    with y hy hyΩ
  rw [← Subtype.coe_mk y hyΩ, extend_apply] at hy ⊢
  rw [dist_zero_right] at hy ⊢
  calc ‖f ⟨y, hyΩ⟩‖ ≤ ‖(f - g) ⟨y, hyΩ⟩‖ + ‖g ⟨y, hyΩ⟩‖ := by
        rw [coe_sub, Pi.sub_apply]
        exact norm_le_norm_sub_add _ _
    _ < ε / 2 + ε / 2 := add_lt_add_of_le_of_lt
        (((f - g).norm_apply_le _).trans (dist_eq_norm f g ▸ hfg.le)) hy
    _ = ε := add_halves ε

/-- The elements of `C^{k,α}(Ω, F)` vanishing on the frontier form a Banach space when `F` is
complete. -/
instance [CompleteSpace F] : CompleteSpace (vanishingOnFrontierSubmodule k α Ω F) :=
  isClosed_vanishingOnFrontierSubmodule.completeSpace_coe

end TauCeti.CkHolderSpaceOn
