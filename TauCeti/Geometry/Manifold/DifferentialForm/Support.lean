/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.DifferentialForm.Chart
public import TauCeti.Geometry.Manifold.Boundary.Basic
public import Mathlib.Topology.Maps.Proper.Basic
public import Mathlib.Topology.PartitionOfUnity
import Mathlib.Topology.Compactness.LocallyFinite

/-!
# Topological support of rough differential forms

This file establishes how the topological support of a rough differential form behaves under
scalar multiplication, pullback, exterior differentiation and finite partition localization.
Locality of the exterior derivative
preserves support and compact support without any regularity assumption. A rough form is a dependent
function whose fibre at `x` is
`TangentSpace I x [⋀^Fin k]→L[ℝ] F`, so Mathlib's `tsupport` is used with the model-space codomain
`E [⋀^Fin k]→L[ℝ] F` supplied explicitly.

A locally finite partition of unity has only finitely many terms meeting a compact form support.
The weights give a finite decomposition; containment in charts requires subordination separately.
Extension by zero in a chart preserves compact support when the form is supported inside that
chart; on its target the extension has the same germ within the model range.
-/

public section

noncomputable section

open Filter Set Function
open scoped Manifold Topology

namespace TauCeti

variable {E H X E' H' Y F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace X] [ChartedSpace H X]
  [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H']
  {I' : ModelWithCorners ℝ E' H'} [TopologicalSpace Y] [ChartedSpace H' Y]
  [AddCommGroup F] [Module ℝ F] [TopologicalSpace F] {k : ℕ}

namespace RoughForm

section SMul

variable [ContinuousConstSMul ℝ F]

-- Mathlib's `tsupport_smul_subset_right` at the codomain `E [⋀^Fin k]→L[ℝ] F` times out at `whnf`
-- matching the fibrewise scalar action on `TangentSpace I x [⋀^Fin k]→L[ℝ] F`, so this is proved
-- directly.
/-- Scalar multiplication does not enlarge the support of a rough form. -/
theorem tsupport_smul_subset (c : ℝ) (φ : RoughForm I X F k) :
    _root_.tsupport (α := E [⋀^Fin k]→L[ℝ] F) (c • φ) ⊆
      _root_.tsupport (α := E [⋀^Fin k]→L[ℝ] F) φ := by
  refine closure_minimal ?_ (_root_.isClosed_tsupport (α := E [⋀^Fin k]→L[ℝ] F) φ)
  intro x hx
  by_contra hxsupport
  have hφ : φ x = 0 := by
    by_contra h
    exact hxsupport (subset_tsupport (α := E [⋀^Fin k]→L[ℝ] F) φ h)
  apply hx
  ext v
  simp [hφ]
  rfl

/-- Multiplication by a nonzero constant preserves the support of a rough form. -/
theorem tsupport_smul (c : ℝ) (φ : RoughForm I X F k) (hc : c ≠ 0) :
    _root_.tsupport (α := E [⋀^Fin k]→L[ℝ] F) (c • φ) =
      _root_.tsupport (α := E [⋀^Fin k]→L[ℝ] F) φ := by
  simp only [_root_.tsupport]
  congr 1
  ext x
  -- Reduce set membership and the fibrewise scalar action; function-support lemmas expect
  -- a fixed codomain, whereas the form is a dependent section.
  change c • φ x ≠ 0 ↔ φ x ≠ 0
  apply not_congr
  constructor
  · intro h
    ext v
    exact (isUnit_iff_ne_zero.mpr hc).smul_eq_zero.mp
      (congrArg (fun L : TangentSpace I x [⋀^Fin k]→L[ℝ] F ↦ L v) h)
  · intro h
    ext v
    simp [h]

end SMul

/-- The zero form has compact topological support. -/
theorem isCompact_tsupport_zero :
    IsCompact (_root_.tsupport (α := E [⋀^Fin k]→L[ℝ] F) (0 : RoughForm I X F k)) := by
  -- Identify the dependent zero section with a fixed-codomain zero function so that
  -- the function `tsupport_zero` simplification applies.
  change IsCompact (_root_.tsupport (0 : X → E [⋀^Fin k]→L[ℝ] F))
  simp

/-- The sum of two forms with compact topological support has compact topological support. -/
theorem isCompact_tsupport_add [ContinuousAdd F] {φ ψ : RoughForm I X F k}
    (hφ : IsCompact (_root_.tsupport (α := E [⋀^Fin k]→L[ℝ] F) φ))
    (hψ : IsCompact (_root_.tsupport (α := E [⋀^Fin k]→L[ℝ] F) ψ)) :
    IsCompact (_root_.tsupport (α := E [⋀^Fin k]→L[ℝ] F) (φ + ψ)) :=
  -- The dependent tangent fibres are definitionally the model space `E`, so the form is a
  -- function with the fixed codomain from which `HasCompactSupport.add` infers its argument.
  HasCompactSupport.add (f := (show X → E [⋀^Fin k]→L[ℝ] F from φ)) hφ hψ

/-- The topological support of a pullback is contained in the preimage of the original support. -/
theorem tsupport_mpullback_subset_preimage {f : X → Y} (hf : Continuous f)
    (φ : RoughForm I' Y F k) :
    _root_.tsupport (α := E [⋀^Fin k]→L[ℝ] F) (mpullback I I' f φ) ⊆
      f ⁻¹' _root_.tsupport (α := E' [⋀^Fin k]→L[ℝ] F) φ := by
  refine closure_minimal ?_
    ((_root_.isClosed_tsupport (α := E' [⋀^Fin k]→L[ℝ] F) φ).preimage hf)
  intro x hx
  apply subset_tsupport (α := E' [⋀^Fin k]→L[ℝ] F) φ
  intro hφ
  apply hx
  ext v
  simp [mpullback_apply, hφ]
  rfl

/-- Pullback by a proper map preserves compact topological support. -/
theorem isCompact_tsupport_mpullback {f : X → Y} (hf : IsProperMap f)
    {φ : RoughForm I' Y F k}
    (hφ : IsCompact (_root_.tsupport (α := E' [⋀^Fin k]→L[ℝ] F) φ)) :
    IsCompact (_root_.tsupport (α := E [⋀^Fin k]→L[ℝ] F) (mpullback I I' f φ)) :=
  (hf.isCompact_preimage hφ).of_isClosed_subset
    (_root_.isClosed_tsupport (α := E [⋀^Fin k]→L[ℝ] F) _)
    (tsupport_mpullback_subset_preimage hf.continuous φ)

end RoughForm

end TauCeti

namespace TauCeti.RoughForm

variable {E H M F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [NormedAddCommGroup F] [NormedSpace ℝ F] {k : ℕ}

/-- Locality of the actual exterior derivative prevents enlargement of a form's support.
No regularity assumption is needed. -/
theorem tsupport_mextDeriv_subset (φ : RoughForm I M F k) :
    _root_.tsupport (α := E [⋀^Fin (k + 1)]→L[ℝ] F) (TauCeti.mextDeriv φ) ⊆
      _root_.tsupport (α := E [⋀^Fin k]→L[ℝ] F) φ := by
  -- Expose support as a closure: its dependent form fibres do not match function-support lemmas.
  change closure {x | TauCeti.mextDeriv φ x ≠ 0} ⊆ _
  apply closure_minimal _ (_root_.isClosed_tsupport (α := E [⋀^Fin _]→L[ℝ] F) φ)
  intro x hx
  by_contra hnot
  have hz : ∀ᶠ y in 𝓝 x, φ y = (0 : RoughForm I M F k) y := by
    have hn := (_root_.isClosed_tsupport (α := E [⋀^Fin _]→L[ℝ] F) φ).isOpen_compl
    filter_upwards [hn.mem_nhds hnot] with y hy
    exact _root_.image_eq_zero_of_notMem_tsupport (α := E [⋀^Fin _]→L[ℝ] F) hy
  have heq := mextDeriv_congr_of_eventuallyEq hz
  rw [mextDeriv_zero] at heq
  exact hx heq

/-- Compact support is preserved by the actual exterior derivative, without a regularity
assumption. -/
theorem isCompact_tsupport_mextDeriv {φ : RoughForm I M F k}
    (hφ : IsCompact (_root_.tsupport (α := E [⋀^Fin k]→L[ℝ] F) φ)) :
    IsCompact (_root_.tsupport (α := E [⋀^Fin (k + 1)]→L[ℝ] F) (TauCeti.mextDeriv φ)) :=
  hφ.of_isClosed_subset (_root_.isClosed_tsupport (α := E [⋀^Fin _]→L[ℝ] F) _)
    (φ.tsupport_mextDeriv_subset)

variable {ι : Type*}

/-- A partition of unity localizes any compactly supported rough form into finitely many
actual terms. All terms outside the chosen finite set vanish identically. -/
theorem exists_finset_partition_eq (φ : RoughForm I M F k) (hc : IsCompact
    (_root_.tsupport (α := E [⋀^Fin _]→L[ℝ] F) φ))
    (ρ : PartitionOfUnity ι M univ) :
    ∃ s : Finset ι,
      φ = (fun x ↦ ∑ i ∈ s, ρ i x • φ x) ∧
        ∀ i ∉ s, (fun x ↦ ρ i x • φ x : RoughForm I M F k) = 0 := by
  classical
  have hfin := ρ.locallyFinite_tsupport.finite_nonempty_inter_compact hc
  let s := hfin.toFinset
  have hmem (i : ι) (x : M) (hρ : ρ i x ≠ 0) (hφ : φ x ≠ 0) : i ∈ s := by
    exact hfin.mem_toFinset.mpr ⟨x, subset_tsupport (ρ i) hρ,
    _root_.subset_tsupport (α := E [⋀^Fin _]→L[ℝ] F) φ hφ⟩
  refine ⟨s, ?_, ?_⟩
  · funext x
    by_cases hx : φ x = 0
    · simp [hx]
    · have hs : ρ.finsupport x ⊆ s := by
        intro i hi
        exact hmem i x (by simpa only [PartitionOfUnity.mem_finsupport, mem_support] using hi) hx
      rw [← Finset.sum_smul, ρ.sum_finsupport' (mem_univ x) hs, one_smul]
  · intro i hi
    funext x
    by_cases hφ : φ x = 0
    · simp [hφ]
    · have hρ : ρ i x = 0 := by
        by_contra h
        exact hi (hmem i x h hφ)
      simp [hρ]

/-- Weights summing to one on the support give an actual finite form decomposition. -/
theorem eq_sum_fun_smul {n : ℕ} (φ : RoughForm I M F k) (ρ : Fin n → M → ℝ)
    (hρ : ∀ x ∈ (_root_.tsupport (α := E [⋀^Fin _]→L[ℝ] F) φ), ∑ i, ρ i x = 1) :
    φ = (fun x ↦ ∑ i, ρ i x • φ x) := by
  funext x
  by_cases hx : x ∈ (_root_.tsupport (α := E [⋀^Fin _]→L[ℝ] F) φ)
  · rw [← Finset.sum_smul, hρ x hx, one_smul]
  · have hz : φ x = 0 :=
      _root_.image_eq_zero_of_notMem_tsupport (α := E [⋀^Fin _]→L[ℝ] F) hx
    simp [hz]

end TauCeti.RoughForm

namespace TauCeti

variable {E H M F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [NormedAddCommGroup F] [NormedSpace ℝ F] {k : ℕ}

/-- The coordinate extension of a form supported inside a chart has support inside the compact
coordinate image of the original support. -/
theorem RoughForm.tsupport_indicator_inChartAt_subset (φ : RoughForm I M F k) (α : M)
    (hc : IsCompact (_root_.tsupport (α := E [⋀^Fin _]→L[ℝ] F) φ)) (hs :
    (_root_.tsupport (α := E [⋀^Fin _]→L[ℝ] F) φ) ⊆ (extChartAt I α).source) :
    _root_.tsupport ((extChartAt I α).target.indicator (φ.inChartAt α)) ⊆
      (extChartAt I α) '' (_root_.tsupport (α := E [⋀^Fin _]→L[ℝ] F) φ) := by
  classical
  have hK := hc.image_of_continuousOn ((continuousOn_extChartAt α).mono hs)
  apply closure_minimal _ hK.isClosed
  intro z hz
  have ht : z ∈ (extChartAt I α).target := by
    by_contra ht
    exact hz (indicator_of_notMem ht _)
  refine ⟨(extChartAt I α).symm z, ?_, (extChartAt I α).right_inv ht⟩
  apply _root_.subset_tsupport (α := E [⋀^Fin _]→L[ℝ] F) φ
  intro hzero
  apply hz
  rw [indicator_of_mem ht]
  ext v
  rw [RoughForm.inChartAt_apply, hzero]
  rfl

/-- The zero extension of a compact chart-supported form has no support outside the target. -/
theorem RoughForm.notMem_tsupport_indicator_inChartAt (φ : RoughForm I M F k) (α : M)
    (hc : IsCompact (_root_.tsupport (α := E [⋀^Fin _]→L[ℝ] F) φ)) (hs :
    (_root_.tsupport (α := E [⋀^Fin _]→L[ℝ] F) φ) ⊆ (extChartAt I α).source)
    {z : E} (hz : z ∉ (extChartAt I α).target) :
    z ∉ _root_.tsupport ((extChartAt I α).target.indicator (φ.inChartAt α)) := by
  intro ht
  obtain ⟨x, hx, rfl⟩ := φ.tsupport_indicator_inChartAt_subset α hc hs ht
  exact hz ((extChartAt I α).map_source (hs hx))

/-- Compact support survives extension by zero from a chart containing the form's support. -/
theorem RoughForm.hasCompactSupport_indicator_inChartAt (φ : RoughForm I M F k) (α : M)
    (hc : IsCompact (_root_.tsupport (α := E [⋀^Fin _]→L[ℝ] F) φ)) (hs :
    (_root_.tsupport (α := E [⋀^Fin _]→L[ℝ] F) φ) ⊆ (extChartAt I α).source) :
    HasCompactSupport ((extChartAt I α).target.indicator (φ.inChartAt α)) :=
  (hc.image_of_continuousOn ((continuousOn_extChartAt α).mono hs)).of_isClosed_subset
    (_root_.isClosed_tsupport _) (φ.tsupport_indicator_inChartAt_subset α hc hs)

/-- On the target, extension by zero has the same germ within the model range as the original
coordinate form. -/
theorem RoughForm.indicator_inChartAt_eventuallyEq (φ : RoughForm I M F k) (α : M)
    {z : E} (hz : z ∈ (extChartAt I α).target) :
    (extChartAt I α).target.indicator (φ.inChartAt α) =ᶠ[𝓝[range I] z] φ.inChartAt α := by
  classical
  filter_upwards [extChartAt_target_mem_nhdsWithin_of_mem hz] with y hy
  exact indicator_of_mem hy _

/-- The zero extension of a compact chart-supported form whose support avoids the boundary
is supported inside the interior of the coordinate target. -/
theorem RoughForm.tsupport_indicator_inChartAt_subset_interior [IsManifold I 1 M]
    (φ : RoughForm I M F k) (α : M) (hc : IsCompact (_root_.tsupport (α := E [⋀^Fin _]→L[ℝ] F) φ))
    (hs : (_root_.tsupport (α := E [⋀^Fin _]→L[ℝ] F) φ) ⊆ (extChartAt I α).source)
    (hd : Disjoint (_root_.tsupport (α := E [⋀^Fin _]→L[ℝ] F) φ) (I.boundary M)) :
    _root_.tsupport ((extChartAt I α).target.indicator (φ.inChartAt α)) ⊆
      interior (extChartAt I α).target := by
  intro y hy
  obtain ⟨x, hx, rfl⟩ := φ.tsupport_indicator_inChartAt_subset α hc hs hy
  apply mem_interior_iff_mem_nhds.mpr
  exact ModelWithCorners.extChartAt_target_mem_nhds_of_isInteriorPoint (k := 1)
    one_ne_zero α (hs hx)
    ((I.isInteriorPoint_iff_not_isBoundaryPoint x).mpr
      (fun hb ↦ Set.disjoint_left.mp hd hx hb))

end TauCeti
