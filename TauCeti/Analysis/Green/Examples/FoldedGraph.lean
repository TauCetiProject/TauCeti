/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Green.BoundaryChain.Subdivision
import Mathlib.Analysis.Calculus.Deriv.Abs

/-!
# An unsplit folded boundary and its graph-piece subdivision

The upper boundary `y = 1 - |x|` is not a graph over `y`: it has two distinct points at every
height below its peak. Its actual unsplit path nevertheless has a geometric null-chain
comparison with its two graph pieces, and the genuine gauge integral is preserved.
-/

public section

noncomputable section

open Set MeasureTheory
open scoped Topology

namespace TauCeti.Green

/-- The original unsplit upper boundary of a triangular dome. -/
def foldedGraphPath : Path (-1 : ℂ) 1 :=
  Path.ofLine (f := fun t : ℝ ↦ (⟨2 * t - 1, 1 - |2 * t - 1|⟩ : ℂ))
    (Complex.equivRealProdCLM.symm.continuous.comp_continuousOn
      ((by fun_prop : ContinuousOn (fun t : ℝ ↦ 2 * t - 1) unitInterval).prodMk
        (by fun_prop)))
    (by apply Complex.ext <;> norm_num) (by apply Complex.ext <;> norm_num)

/-- The original parametrization traverses the whole fold in one arc. -/
theorem foldedGraphPath_apply (t : unitInterval) :
    foldedGraphPath t = (⟨2 * (t : ℝ) - 1, 1 - |2 * (t : ℝ) - 1|⟩ : ℂ) := (rfl)

private theorem left_graph : BoundaryChain.GraphArc .im (fun y ↦ y - 1) 0 1
    ⟨-1, Complex.I, Path.segment (-1 : ℂ) Complex.I⟩ where
  continuous_graph := by fun_prop
  differentiable_graph := ⟨∅, countable_empty, fun _ _ ↦ by fun_prop⟩
  on_graph t := by
    apply Complex.ext <;> simp [Path.segment_apply, AffineMap.lineMap_apply_module,
      Coordinate.graph_im_apply, Coordinate.proj_im]
  coordinate_mem t := by
    simp [Path.segment_apply, AffineMap.lineMap_apply_module, Coordinate.proj_im]
  differentiable_coordinate := by
    refine ⟨∅, countable_empty, ?_⟩
    intro t ht
    apply (differentiableAt_id : DifferentiableAt ℝ (fun t : ℝ ↦ t) t).congr_of_eventuallyEq
    filter_upwards [Icc_mem_nhds ht.1.1 ht.1.2] with x hx
    simp [Path.extend_apply _ hx, Path.segment_apply, AffineMap.lineMap_apply_module,
      Coordinate.proj_im]

private theorem right_graph : BoundaryChain.GraphArc .im (fun y ↦ 1 - y) 0 1
    ⟨Complex.I, 1, Path.segment Complex.I (1 : ℂ)⟩ where
  continuous_graph := by fun_prop
  differentiable_graph := ⟨∅, countable_empty, fun _ _ ↦ by fun_prop⟩
  on_graph t := by
    apply Complex.ext <;> simp [Path.segment_apply, AffineMap.lineMap_apply_module,
      Coordinate.graph_im_apply, Coordinate.proj_im]
  coordinate_mem t := by
    simp [Path.segment_apply, AffineMap.lineMap_apply_module, Coordinate.proj_im]
    constructor <;> linarith [t.property.1, t.property.2]
  differentiable_coordinate := by
    refine ⟨∅, countable_empty, ?_⟩
    intro t ht
    have hd : DifferentiableAt ℝ (fun t : ℝ ↦ 1 - t) t := by fun_prop
    apply hd.congr_of_eventuallyEq
    filter_upwards [Icc_mem_nhds ht.1.1 ht.1.2] with x hx
    simp [Path.extend_apply _ hx, Path.segment_apply, AffineMap.lineMap_apply_module,
      Coordinate.proj_im]

private theorem folded_join : foldedGraphPath =
    (Path.segment (-1 : ℂ) Complex.I).trans (Path.segment Complex.I (1 : ℂ)) := by
  ext t
  rw [foldedGraphPath_apply, Path.trans_apply]
  split_ifs with ht
  · apply Complex.ext <;>
      simp [Path.segment_apply, AffineMap.lineMap_apply_module,
        abs_of_nonpos (by linarith : 2 * (t : ℝ) - 1 ≤ 0)]
  · apply Complex.ext <;>
      simp [Path.segment_apply, AffineMap.lineMap_apply_module,
        abs_of_nonneg (by linarith : 0 ≤ 2 * (t : ℝ) - 1)]

private theorem folded_graph : BoundaryChain.GraphArc .re (fun x ↦ 1 - |x|) (-1) 1
    ⟨-1, 1, foldedGraphPath⟩ where
  continuous_graph := by fun_prop
  differentiable_graph := by
    refine ⟨{0}, countable_singleton _, ?_⟩
    intro t ht
    exact (differentiableAt_abs (by simpa only [mem_singleton_iff] using ht.2)).const_sub 1
  on_graph t := by
    simp [foldedGraphPath_apply, Coordinate.graph_re_apply, Coordinate.proj_re]
  coordinate_mem t := by
    rw [foldedGraphPath_apply, Coordinate.proj_re]
    -- Expose interval membership after evaluating the real coordinate of the complex path.
    change -1 ≤ 2 * (t : ℝ) - 1 ∧ 2 * (t : ℝ) - 1 ≤ 1
    constructor <;> linarith [t.property.1, t.property.2]
  differentiable_coordinate := by
    refine ⟨∅, countable_empty, ?_⟩
    intro t ht
    have hd : DifferentiableAt ℝ (fun t : ℝ ↦ 2 * t - 1) t := by fun_prop
    apply hd.congr_of_eventuallyEq
    filter_upwards [Icc_mem_nhds ht.1.1 ht.1.2] with x hx
    simp [Path.extend_apply _ hx, foldedGraphPath_apply, Coordinate.proj_re]

/-- In the other coordinate, the whole folded arc is graph-certified. Its two-piece
subdivision follows directly from that whole certificate, without recertifying either piece. -/
theorem foldedGraphPath_graph_subdivision {U : Set ℂ}
    (hU : Coordinate.re.graph (fun x ↦ 1 - |x|) '' Icc (-1) 1 ⊆ U) :
    BoundaryChain.GraphSubdivision .re U ⟨-1, 1, foldedGraphPath⟩
      (BoundaryChain.ofPath (Path.segment (-1 : ℂ) Complex.I) +
        BoundaryChain.ofPath (Path.segment Complex.I (1 : ℂ))) := by
  have h := folded_graph
  rw [folded_join] at h ⊢
  exact h.subdivision_trans hU

/-- The whole folded arc is not a graph over the selected `y` coordinate. -/
theorem not_graphArc_foldedGraphPath (g : ℝ → ℝ) (a b : ℝ) :
    ¬BoundaryChain.GraphArc .im g a b ⟨-1, 1, foldedGraphPath⟩ := by
  intro h
  have hL := h.on_graph ⟨1 / 4, by norm_num⟩
  have hR := h.on_graph ⟨3 / 4, by norm_num⟩
  -- Unpack the Arc projections in the two graph equations before evaluating the path.
  change foldedGraphPath _ = Coordinate.im.graph g (Coordinate.im.proj (foldedGraphPath _)) at hL hR
  rw [foldedGraphPath_apply, Coordinate.proj_im,
    Coordinate.graph_im_apply] at hL hR
  norm_num at hL hR
  have he := hL.trans hR.symm
  norm_num at he

/-- A constructive comparison retains the original unsplit, non-graph-over-y boundary.
Only containment of its two graph traces is required of the field domain. -/
theorem foldedGraphPath_subdivision {U : Set ℂ}
    (hL : Coordinate.im.graph (fun y ↦ y - 1) '' Icc 0 1 ⊆ U)
    (hR : Coordinate.im.graph (fun y ↦ 1 - y) '' Icc 0 1 ⊆ U) :
    BoundaryChain.GraphSubdivision .im U ⟨-1, 1, foldedGraphPath⟩
      (BoundaryChain.ofPath (Path.segment (-1 : ℂ) Complex.I) +
        BoundaryChain.ofPath (Path.segment Complex.I (1 : ℂ))) := by
  rw [folded_join]
  exact BoundaryChain.GraphSubdivision.join (.single (.graph left_graph hL))
    (.single (.graph right_graph hR))

/-- The original whole boundary is gauge integrable and its integral equals the sum on the
actual two pieces, without a Bochner integrability or integral identity premise. -/
theorem foldedGraphPath_integral {U : Set ℂ} {P : ℂ → ℝ}
    (hL : Coordinate.im.graph (fun y ↦ y - 1) '' Icc 0 1 ⊆ U)
    (hR : Coordinate.im.graph (fun y ↦ 1 - y) '' Icc 0 1 ⊆ U) (hP : ContinuousOn P U) :
    BoundaryChain.Integrable Complex.imCLM P (BoundaryChain.ofPath foldedGraphPath) ∧
      BoundaryChain.integral Complex.imCLM P (BoundaryChain.ofPath foldedGraphPath) =
        BoundaryChain.integral Complex.imCLM P
          (BoundaryChain.ofPath (Path.segment (-1 : ℂ) Complex.I) +
            BoundaryChain.ofPath (Path.segment Complex.I (1 : ℂ))) := by
  have h := (foldedGraphPath_subdivision hL hR).nullChain
  have hi := ((left_graph.integrable (hP.mono hL)).add (right_graph.integrable (hP.mono hR)))
  simpa only [Coordinate.proj_im] using
    And.intro ((h.integrable_iff hP).mpr hi) (h.integral_eq hP)

private theorem folded_regular : ∃ s : Set ℝ, s.Countable ∧
    ∀ t ∈ Ioo 0 1 \ s, DifferentiableAt ℝ foldedGraphPath.extend t := by
  refine ⟨{1 / 2}, countable_singleton _, ?_⟩
  intro t ht
  have hn : 2 * t - 1 ≠ 0 := fun he ↦ ht.2 (by simp only [mem_singleton_iff]; linarith)
  have hl : DifferentiableAt ℝ (fun t : ℝ ↦ 2 * t - 1) t := by fun_prop
  have ha := (differentiableAt_abs hn).comp t hl
  have hd := Complex.equivRealProdCLM.symm.differentiableAt.comp t (hl.prodMk (ha.const_sub 1))
  apply hd.congr_of_eventuallyEq
  filter_upwards [Icc_mem_nhds ht.1.1 ht.1.2] with x hx
  rw [Path.extend_apply _ hx, foldedGraphPath_apply]
  rfl

/-- A nonlinear reparametrization of the original unsplit folded arc. -/
def squaredFoldedGraphPath : Path (-1 : ℂ) 1 :=
  Path.ofLine (f := fun t : ℝ ↦ foldedGraphPath.extend (t ^ 2))
    (foldedGraphPath.continuous_extend.comp (by fun_prop)).continuousOn
    (by simp) (by simp)

/-- The squared parameter traverses the original fold with real coordinate `2t² - 1`. -/
@[simp]
theorem squaredFoldedGraphPath_apply (t : unitInterval) :
    squaredFoldedGraphPath t =
      (⟨2 * (t : ℝ) ^ 2 - 1, 1 - |2 * (t : ℝ) ^ 2 - 1|⟩ : ℂ) := by
  have ht : (t : ℝ) ^ 2 ∈ Icc (0 : ℝ) 1 :=
    ⟨sq_nonneg _, by nlinarith [t.property.1, t.property.2]⟩
  -- Evaluate the Path.ofLine definition before restricting its squared parameter to the interval.
  change foldedGraphPath.extend ((t : ℝ) ^ 2) = _
  rw [Path.extend_apply _ ht, foldedGraphPath_apply]

/-- A finite graph-piece comparison also retains an actual nonlinear parametrization of the
original whole arc. Its countable-fiber and derivative premises are proved from the square map. -/
theorem squaredFoldedGraphPath_subdivision {U : Set ℂ}
    (hL : Coordinate.im.graph (fun y ↦ y - 1) '' Icc 0 1 ⊆ U)
    (hR : Coordinate.im.graph (fun y ↦ 1 - y) '' Icc 0 1 ⊆ U) :
    BoundaryChain.GraphSubdivision .im U ⟨-1, 1, squaredFoldedGraphPath⟩
      (BoundaryChain.ofPath (Path.segment (-1 : ℂ) Complex.I) +
        BoundaryChain.ofPath (Path.segment Complex.I (1 : ℂ))) := by
  refine BoundaryChain.GraphSubdivision.reparam
    (foldedGraphPath_subdivision hL hR) (fun t ↦ t ^ 2)
    (by fun_prop) ⟨∅, countable_empty, fun _ _ ↦ by fun_prop⟩ folded_regular ?_ ?_
    (by norm_num) (by norm_num) (fun _ ↦ rfl)
  · intro y
    by_cases hn : ((fun t : ℝ ↦ t ^ 2) ⁻¹' {y}).Nonempty
    · obtain ⟨r, hr⟩ := hn
      apply (toFinite ({r, -r} : Set ℝ)).countable.mono
      intro t ht
      have he : t ^ 2 = r ^ 2 := ht.trans hr.symm
      simpa only [mem_insert_iff, mem_singleton_iff] using
        sq_eq_sq_iff_eq_or_eq_neg.mp he
    · simpa only [not_nonempty_iff_eq_empty.mp hn] using countable_empty
  · intro t ht
    constructor
    · exact sq_nonneg t
    · nlinarith [ht.1, ht.2, mul_nonneg ht.1 (sub_nonneg.mpr ht.2)]

/-- A common geometric refinement compares the nonlinear whole arc with the original arc. -/
theorem squaredFoldedGraphPath_nullChain {U : Set ℂ}
    (hL : Coordinate.im.graph (fun y ↦ y - 1) '' Icc 0 1 ⊆ U)
    (hR : Coordinate.im.graph (fun y ↦ 1 - y) '' Icc 0 1 ⊆ U) :
    BoundaryChain.NullChain .im U
      (BoundaryChain.ofPath squaredFoldedGraphPath - BoundaryChain.ofPath foldedGraphPath) :=
  (squaredFoldedGraphPath_subdivision hL hR).nullChain_of_common
    (foldedGraphPath_subdivision hL hR)

/-- The same common refinement retains negative orientation: both reversed original arcs
refine to the negative of their shared piece chain. -/
theorem squaredFoldedGraphPath_symm_nullChain {U : Set ℂ}
    (hL : Coordinate.im.graph (fun y ↦ y - 1) '' Icc 0 1 ⊆ U)
    (hR : Coordinate.im.graph (fun y ↦ 1 - y) '' Icc 0 1 ⊆ U) :
    BoundaryChain.NullChain .im U
      (BoundaryChain.ofPath squaredFoldedGraphPath.symm -
        BoundaryChain.ofPath foldedGraphPath.symm) :=
  (squaredFoldedGraphPath_subdivision hL hR).symm.nullChain_of_common
    (foldedGraphPath_subdivision hL hR).symm

/-- The folded arc traversed forward, backward, then forward again. -/
def backtrackingFoldedGraphPath : Path (-1 : ℂ) 1 :=
  foldedGraphPath.trans (foldedGraphPath.symm.trans foldedGraphPath)

/-- The backtracking path concatenates the forward fold, its reversal and the forward fold. -/
theorem backtrackingFoldedGraphPath_def : backtrackingFoldedGraphPath =
    foldedGraphPath.trans (foldedGraphPath.symm.trans foldedGraphPath) := by rfl

/-- Backtracking is present in the actual base coordinate, not just in an auxiliary
certificate: the path visits x=1 before returning to x=-1. -/
theorem not_monotone_re_backtrackingFoldedGraphPath :
    ¬Monotone (fun t : unitInterval ↦ (backtrackingFoldedGraphPath t).re) := by
  intro h
  have hle : (⟨1 / 2, by norm_num⟩ : unitInterval) ≤ ⟨3 / 4, by norm_num⟩ := by norm_num
  have hh := h hle
  norm_num [backtrackingFoldedGraphPath_def, Path.trans_apply, Path.symm_apply,
    foldedGraphPath_apply] at hh

/-- The three actual traversals have a geometric refinement with cancellation of the
reversed middle traversal. No field or integral identity is used to construct it. -/
theorem backtrackingFoldedGraphPath_subdivision {U : Set ℂ}
    (hL : Coordinate.im.graph (fun y ↦ y - 1) '' Icc 0 1 ⊆ U)
    (hR : Coordinate.im.graph (fun y ↦ 1 - y) '' Icc 0 1 ⊆ U) :
    BoundaryChain.GraphSubdivision .im U ⟨-1, 1, backtrackingFoldedGraphPath⟩
      (BoundaryChain.ofPath (Path.segment (-1 : ℂ) Complex.I) +
        BoundaryChain.ofPath (Path.segment Complex.I (1 : ℂ))) := by
  have h := foldedGraphPath_subdivision hL hR
  convert BoundaryChain.GraphSubdivision.join h (.join h.symm h) using 1
  · rfl
  · abel

/-- Gauge integrability and the coordinate integral are preserved by this backtracking
traversal under continuity on the graph traces alone. -/
theorem backtrackingFoldedGraphPath_integral {U : Set ℂ} {P : ℂ → ℝ}
    (hL : Coordinate.im.graph (fun y ↦ y - 1) '' Icc 0 1 ⊆ U)
    (hR : Coordinate.im.graph (fun y ↦ 1 - y) '' Icc 0 1 ⊆ U) (hP : ContinuousOn P U) :
    BoundaryChain.Integrable Complex.imCLM P (BoundaryChain.ofPath backtrackingFoldedGraphPath) ∧
      BoundaryChain.integral Complex.imCLM P (BoundaryChain.ofPath backtrackingFoldedGraphPath) =
        BoundaryChain.integral Complex.imCLM P (BoundaryChain.ofPath foldedGraphPath) := by
  have h := (backtrackingFoldedGraphPath_subdivision hL hR).nullChain_of_common
    (foldedGraphPath_subdivision hL hR)
  have hi : BoundaryChain.Integrable Coordinate.im.proj P
      (BoundaryChain.ofPath foldedGraphPath) := by
    simpa only [Coordinate.proj_im] using (foldedGraphPath_integral hL hR hP).1
  simpa only [Coordinate.proj_im] using
    And.intro ((h.integrable_iff hP).mpr hi) (h.integral_eq hP)

/-- A negatively weighted nonlinear whole arc and the positively weighted reversal of the
original arc have the same signed refinement. The arbitrary-chain common-refinement theorem
handles the coefficient -1 on the original arc and +1 on its reverse directly. -/
theorem squaredFoldedGraphPath_mixedSigned_nullChain {U : Set ℂ}
    (hL : Coordinate.im.graph (fun y ↦ y - 1) '' Icc 0 1 ⊆ U)
    (hR : Coordinate.im.graph (fun y ↦ 1 - y) '' Icc 0 1 ⊆ U) :
    BoundaryChain.NullChain .im U
      (-BoundaryChain.ofPath squaredFoldedGraphPath -
        BoundaryChain.ofPath foldedGraphPath.symm) := by
  classical
  let c := BoundaryChain.ofPath (Path.segment (-1 : ℂ) Complex.I) +
    BoundaryChain.ofPath (Path.segment Complex.I (1 : ℂ))
  apply BoundaryChain.NullChain.of_common_graphSubdivisions
    (-BoundaryChain.ofPath squaredFoldedGraphPath) (BoundaryChain.ofPath foldedGraphPath.symm)
    (fun _ ↦ c) (fun _ ↦ -c)
  · intro γ hγ
    have he : γ = ⟨-1, 1, squaredFoldedGraphPath⟩ := by
      simpa [BoundaryChain.ofPath_def] using hγ
    subst γ
    exact squaredFoldedGraphPath_subdivision hL hR
  · intro γ hγ
    have he : γ = ⟨1, -1, foldedGraphPath.symm⟩ := by
      simpa [BoundaryChain.ofPath_def] using hγ
    subst γ
    exact (foldedGraphPath_subdivision hL hR).symm
  · simp [BoundaryChain.ofPath_def, Finsupp.sum]

/-- The mixed signed common refinement preserves the whole-arc gauge integral under
continuity on the two graph traces, including its negatively weighted original arc. -/
theorem squaredFoldedGraphPath_mixedSigned_integral {U : Set ℂ} {P : ℂ → ℝ}
    (hL : Coordinate.im.graph (fun y ↦ y - 1) '' Icc 0 1 ⊆ U)
    (hR : Coordinate.im.graph (fun y ↦ 1 - y) '' Icc 0 1 ⊆ U) (hP : ContinuousOn P U) :
    BoundaryChain.Integrable Complex.imCLM P (-BoundaryChain.ofPath squaredFoldedGraphPath) ∧
      BoundaryChain.Integrable Complex.imCLM P (BoundaryChain.ofPath foldedGraphPath.symm) ∧
      BoundaryChain.integral Complex.imCLM P (-BoundaryChain.ofPath squaredFoldedGraphPath) =
        BoundaryChain.integral Complex.imCLM P (BoundaryChain.ofPath foldedGraphPath.symm) := by
  have h := squaredFoldedGraphPath_mixedSigned_nullChain hL hR
  have hi := BoundaryChain.integrable_neg_iff.mpr
    ((squaredFoldedGraphPath_subdivision hL hR).piecewiseGraphArc.integrable hP)
  rw [← Coordinate.proj_im]
  exact ⟨hi, (h.integrable_iff hP).mp hi, h.integral_eq hP⟩

end TauCeti.Green
