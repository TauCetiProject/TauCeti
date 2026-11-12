/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.Associated.Basic
public import TauCeti.Topology.VectorBundle.Associated.Metric
public import Mathlib.Geometry.Manifold.VectorBundle.Riemannian
import Mathlib.Analysis.InnerProductSpace.Calculus

/-!
# Smooth invariant metrics on associated bundles

For an isometric linear action, the associated metric is constant in every principal bundle
chart. Consequently its real Riemannian metric and its Hermitian pairings are smooth whenever
the existing associated vector bundle is smooth. No additional choice of metric, partition
of unity, or smooth structure on the base is made.

The real metric uses the native `Bundle.ContMDiffRiemannianMetric` carrier. Complex inner
products are smooth as maps over the real field, over an arbitrary real base manifold.

The local-constant metric argument follows the trivial-bundle construction of
`IsContMDiffRiemannianBundle` in Mathlib's
`Geometry/Manifold/VectorBundle/Riemannian`.

## References

* S. Kobayashi and K. Nomizu, *Foundations of Differential Geometry*, volume I, Chapter I, §5.
* I. Kolář, P. W. Michor, J. Slovák, *Natural Operations in Differential Geometry*, §10.7.
-/

public noncomputable section

open Bundle Filter MulOpposite Set
open scoped Manifold ContDiff InnerProductSpace Topology

namespace TauCeti.AssociatedBundle

variable {n : ℕ∞ω} {B G F EB HB : Type*}
  [NormedAddCommGroup EB] [NormedSpace ℝ EB] [TopologicalSpace HB]
  {IB : ModelWithCorners ℝ EB HB} [TopologicalSpace B] [ChartedSpace HB B]
  [Group G] [TopologicalSpace G]
  {P : B → Type*} [TopologicalSpace (TotalSpace G P)] [∀ b, TopologicalSpace (P b)]
  [FiberBundle G P] [∀ b, MulAction Gᵐᵒᵖ (P b)] [PrincipalBundle G P]
  [NormedAddCommGroup F] [DistribMulAction G F] [ContinuousSMul G F]
  [IsIsometricSMul G F]

section Real

variable [InnerProductSpace ℝ F] [SMulCommClass G ℝ F]

-- Name the dependent fibre carrier before forming its bilinear map: inference from `innerSL`
-- alone can select the model carrier and its scalar instances instead.
private def innerForm (b : B) :
    AssociatedBundle G P F b →L[ℝ] AssociatedBundle G P F b →L[ℝ] ℝ :=
  innerSL ℝ (E := AssociatedBundle G P F b)

private theorem innerForm_apply (b : B) (v w : AssociatedBundle G P F b) :
    innerForm b v w = ⟪v, w⟫_ℝ := innerSL_apply_apply ℝ v w

variable [VectorBundle ℝ F (AssociatedBundle G P F)]

private theorem contMDiff_innerSL :
    ContMDiff IB (IB.prod 𝓘(ℝ, F →L[ℝ] F →L[ℝ] ℝ)) n
      (fun b ↦ TotalSpace.mk' (F →L[ℝ] F →L[ℝ] ℝ) b
        (innerForm (G := G) (P := P) (F := F) b)) := by
  intro x
  rw [contMDiffAt_section]
  let C : F →L[ℝ] F →L[ℝ] ℝ := innerSL ℝ
  have hc : ContMDiffAt IB 𝓘(ℝ, F →L[ℝ] F →L[ℝ] ℝ) n (fun _ : B ↦ C) x :=
    contMDiffAt_const
  apply hc.congr_of_eventuallyEq
  filter_upwards [(trivializationAt G P x).open_baseSet.mem_nhds
    (mem_baseSet_trivializationAt G P x)] with y hy
  ext v w
  rw [hom_trivializationAt_apply]
  have hyA : y ∈ (trivializationAt F (AssociatedBundle G P F) x).baseSet := by
    simpa only [baseSet_trivializationAt] using hy
  rw [inCoordinates_apply_eq₂ hyA hyA (by simp)]
  let e := trivializationAt F (AssociatedBundle G P F) x
  have h := inner_trivializationAt (𝕜' := ℝ) hy (e.symm y v) (e.symm y w)
  simpa [C, innerForm_apply, e, Trivialization.apply_mk_symm _ hyA,
    innerSL_apply_apply ℝ (E := AssociatedBundle G P F y), innerSL_apply_apply ℝ (E := F)]
    using h.symm

/-- The canonical real metric of an associated bundle with an isometric linear action. -/
def contMDiffRiemannianMetric : ContMDiffRiemannianMetric IB n F (AssociatedBundle G P F) where
  inner := innerForm
  symm _ v w := real_inner_comm w v
  pos _ _ hv := real_inner_self_pos.mpr hv
  isVonNBounded b := by
    apply (NormedSpace.isVonNBounded_ball ℝ (AssociatedBundle G P F b) 1).subset
    intro v hv
    have hv' : ⟪v, v⟫_ℝ < 1 := hv
    rw [real_inner_self_eq_norm_sq] at hv'
    exact mem_ball_zero_iff.mpr ((sq_lt_one_iff₀ (norm_nonneg v)).mp hv')
  contMDiff := contMDiff_innerSL (G := G) (P := P) (F := F)

/-- The canonical real metric evaluates to the associated fibre's native inner product. -/
@[simp]
theorem contMDiffRiemannianMetric_inner (b : B) (v w : AssociatedBundle G P F b) :
    (contMDiffRiemannianMetric (G := G) (P := P) (F := F) (IB := IB) (n := n)).inner b
      v w = ⟪v, w⟫_ℝ := (rfl)

end Real

section Hermitian

variable {𝕜 : Type*} [RCLike 𝕜] [InnerProductSpace 𝕜 F] [NormedSpace ℝ F]
  [SMulCommClass G 𝕜 F]
  {EM HM M : Type*} [NormedAddCommGroup EM] [NormedSpace ℝ EM]
  [TopologicalSpace HM] {IM : ModelWithCorners ℝ EM HM}
  [TopologicalSpace M] [ChartedSpace HM M]
  {b : M → B} {v w : ∀ m, AssociatedBundle G P F (b m)} {s : Set M} {x : M}

/-- Hermitian pairings of smooth associated-bundle-valued maps with a common varying base
are smooth over the real base field, also within an arbitrary set. -/
theorem _root_.ContMDiffWithinAt.inner_associatedBundle
    (hv : ContMDiffWithinAt IM (IB.prod 𝓘(ℝ, F)) n
      (fun m ↦ (⟨b m, v m⟩ : TotalSpace F (AssociatedBundle G P F))) s x)
    (hw : ContMDiffWithinAt IM (IB.prod 𝓘(ℝ, F)) n
      (fun m ↦ (⟨b m, w m⟩ : TotalSpace F (AssociatedBundle G P F))) s x) :
    ContMDiffWithinAt IM 𝓘(ℝ, 𝕜) n (fun m ↦ ⟪v m, w m⟫_𝕜) s x := by
  obtain ⟨hb, hv'⟩ := (contMDiffWithinAt_totalSpace.mp hv)
  have hw' := (contMDiffWithinAt_totalSpace.mp hw).2
  have hx := mem_baseSet_trivializationAt G P (b x)
  have hmem := hb.continuousWithinAt.preimage_mem_nhdsWithin
    ((trivializationAt G P (b x)).open_baseSet.mem_nhds hx)
  apply ((contDiff_inner (𝕜 := 𝕜) (E := F)).contMDiff.contMDiffAt.comp_contMDiffWithinAt x
    (hv'.prodMk_space hw')).congr_of_eventuallyEq
  · filter_upwards [hmem] with y hy
    exact (inner_trivializationAt hy (v y) (w y)).symm
  · exact (inner_trivializationAt hx (v x) (w x)).symm

/-- The Hermitian pairing of two smooth maps into an associated bundle is smooth. -/
theorem _root_.ContMDiff.inner_associatedBundle
    (hv : ContMDiff IM (IB.prod 𝓘(ℝ, F)) n
      (fun m ↦ (⟨b m, v m⟩ : TotalSpace F (AssociatedBundle G P F))))
    (hw : ContMDiff IM (IB.prod 𝓘(ℝ, F)) n
      (fun m ↦ (⟨b m, w m⟩ : TotalSpace F (AssociatedBundle G P F)))) :
    ContMDiff IM 𝓘(ℝ, 𝕜) n (fun m ↦ ⟪v m, w m⟫_𝕜) := by
  intro x
  exact (hv x).inner_associatedBundle (hw x)

end Hermitian

end TauCeti.AssociatedBundle
