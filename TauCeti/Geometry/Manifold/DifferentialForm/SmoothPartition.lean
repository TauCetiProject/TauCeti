/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.DifferentialForm.Support
public import TauCeti.Geometry.Manifold.DifferentialForm.Smooth
public import TauCeti.Geometry.Manifold.Orientation.Lift
public import Mathlib.Geometry.Manifold.PartitionOfUnity
public import Mathlib.Geometry.Manifold.IsManifold.InteriorBoundary

/-!
# Finite smooth localization in oriented charts

A compactly supported C1 form has a finite decomposition by an actual smooth partition of
unity. Each patch stays in one chart and one fiber of its locally constant orientation sign.
Patches centered away from the boundary avoid the boundary entirely. These refinements allow
the chartwise Stokes theorem to be assembled without changing its orientation conventions.
-/

public section

noncomputable section

open Set Function
open scoped Manifold ContDiff

namespace TauCeti.RoughForm

variable {E H M F ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [Fintype ι] {k : ℕ}

/-- An actual smooth partition gives a finite decomposition into compact C1 chart-supported
forms with constant chart signs. An interior-centered patch is disjoint from the boundary. -/
theorem exists_finset_smooth_partition_in_charts (φ : RoughForm I M F k)
    (l : Manifold.OrientationLift I M ι) (hφ : IsSmoothForm I 1 φ)
    (hc : IsCompact (_root_.tsupport (α := E [⋀^Fin k]→L[ℝ] F) φ)) :
    ∃ s : Finset M, ∃ ρ : SmoothPartitionOfUnity M I M univ,
      φ = ∑ i ∈ s, (fun x ↦ ρ i x • φ x : RoughForm I M F k) ∧
        ∀ i ∈ s,
          IsSmoothForm I 1 (fun x ↦ ρ i x • φ x) ∧
          IsCompact (_root_.tsupport (α := E [⋀^Fin _]→L[ℝ] F)
            (fun x ↦ ρ i x • φ x : RoughForm I M F k)) ∧
          _root_.tsupport (α := E [⋀^Fin _]→L[ℝ] F) (fun x ↦ ρ i x • φ x : RoughForm I M F k)
            ⊆ (chartAt H i).source ∧
          (∀ x ∈ _root_.tsupport (α := E [⋀^Fin _]→L[ℝ] F)
            (fun x ↦ ρ i x • φ x : RoughForm I M F k),
            l.signAt i x = l.signAt i i) ∧
          (i ∉ I.boundary M →
            Disjoint (_root_.tsupport (α := E [⋀^Fin _]→L[ℝ] F)
              (fun x ↦ ρ i x • φ x : RoughForm I M F k)) (I.boundary M)) := by
  classical
  let V : M → Set M := fun i ↦
    (chartAt H i).source ∩ (l.signAt i) ⁻¹' {l.signAt i i}
  let U : M → Set M := fun i ↦ V i ∩ if i ∈ I.boundary M then univ else (I.boundary M)ᶜ
  have hV : ∀ i, IsOpen (V i) := fun i ↦
    (l.continuousOn_signAt i).isOpen_inter_preimage (chartAt H i).open_source (isOpen_discrete _)
  have hboundary : IsClosed (I.boundary M) := I.isClosed_boundary (by simp : (∞ : ℕ∞ω) ≠ 0)
  have hU : ∀ i, IsOpen (U i) := by
    intro i
    dsimp only [U]
    split_ifs
    · exact (hV i).inter isOpen_univ
    · exact (hV i).inter hboundary.isOpen_compl
  have hcover : univ ⊆ ⋃ i, U i := by
    intro x _
    refine mem_iUnion.mpr ⟨x, ⟨⟨mem_chart_source H x, rfl⟩, ?_⟩⟩
    split_ifs with hx
    · exact mem_univ x
    · exact hx
  obtain ⟨ρ, hρ⟩ := SmoothPartitionOfUnity.exists_isSubordinate I isClosed_univ U hU hcover
  obtain ⟨s, heq, _⟩ := φ.exists_finset_partition_eq hc ρ.toPartitionOfUnity
  refine ⟨s, ρ, ?_, ?_⟩
  · exact heq.trans (by ext x; simp)
  · intro i _
    -- Fix the model-fibre view of φ for the ordinary function support lemmas; the form's
    -- tangent-fibre type otherwise leaves an expensive dependent-type identification implicit.
    have hs : _root_.tsupport (α := E [⋀^Fin k]→L[ℝ] F)
        (fun x ↦ ρ i x • φ x : RoughForm I M F k) ⊆ U i :=
      (_root_.tsupport_smul_subset_left (ρ i) (show M → E [⋀^Fin _]→L[ℝ] F from φ)).trans (hρ i)
    refine ⟨hφ.fun_smul ((ρ i).contMDiff.of_le (by simp)),
      hc.of_isClosed_subset (isClosed_tsupport _) (_root_.tsupport_smul_subset_right (ρ i)
        (show M → E [⋀^Fin _]→L[ℝ] F from φ)),
      fun x hx ↦ (hs hx).1.1, fun x hx ↦ (hs hx).1.2, ?_⟩
    intro hi
    apply disjoint_left.mpr
    intro x hx hxb
    have hh := (hs hx).2
    rw [ite_eq_right hi] at hh
    exact hh hxb

end TauCeti.RoughForm
