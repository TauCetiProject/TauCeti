/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.SmoothEmbedding.NormalSpace.VectorBundle.Riemannian
import TauCeti.Geometry.Manifold.VectorBundle.LocalFrame

/-!
# The induced metric on an intrinsic normal bundle

The intrinsic normal space is a quotient of the ambient tangent space. Its Riemannian metric
pairs the unique orthogonal representatives of two normal classes. This metric induces the
existing quotient topology and varies smoothly over the embedded submanifold. Consequently its
fibre lengths can be used for smooth radial compression and for normal disc and sphere bundles,
without choosing a global normal frame.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, second edition, Theorem 6.24.

The construction uses `SmoothEmbedding.normalSpaceOrthogonalComplementEquiv` and the total-space
regularity theorem `SmoothEmbedding.contMDiff_normalRepresentative`.
-/

public noncomputable section

open Bundle Manifold Set
open scoped ContDiff InnerProductSpace Manifold Topology

namespace TauCeti.SmoothEmbedding

variable {E V P H G M N : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
  [TopologicalSpace H] [TopologicalSpace G]
  {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ V G}
  [TopologicalSpace M] [ChartedSpace H M]
  [TopologicalSpace N] [ChartedSpace G N] {n : ℕ∞ω}
  [RiemannianBundle (fun y : N ↦ TangentSpace J y)]

/-- The metric on intrinsic normal classes obtained by pairing their orthogonal representatives.
It induces the existing quotient topology on each fibre. -/
def normalRiemannianMetric (f : SmoothEmbedding I J n M N) (hn : n ≠ 0) :
    RiemannianMetric (fun x => f.NormalSpace x hn) where
  inner x := (ContinuousLinearMap.precomp ℝ (f.normalRepresentative x hn)).comp
    ((innerSL ℝ).comp (f.normalRepresentative x hn))
  symm x v w := by
    simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.precomp_apply,
      innerSL_apply_apply] using real_inner_comm
        (f.normalRepresentative x hn w) (f.normalRepresentative x hn v)
  pos x v hv := by
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.precomp_apply,
      innerSL_apply_apply]
    apply real_inner_self_pos.mpr
    intro h
    apply hv
    simpa only [map_zero, normalClass_normalRepresentative] using
      congrArg (f.normalClass x hn) h
  isVonNBounded x := by
    let e := f.normalSpaceOrthogonalComplementEquiv x hn
    refine ((NormedSpace.isVonNBounded_ball ℝ ((f.tangentRange x hn)ᗮ) 1).image
      e.symm.toContinuousLinearMap).subset ?_
    intro v hv
    refine ⟨e v, ?_, e.symm_apply_apply v⟩
    rw [mem_ball_zero_iff]
    have hnorm : ‖e v‖ ^ 2 < 1 := by
      simpa only [← real_inner_self_eq_norm_sq, Submodule.coe_inner,
        e, ← normalRepresentative_apply, Set.mem_ofPred_eq,
        ContinuousLinearMap.comp_apply, ContinuousLinearMap.precomp_apply,
        innerSL_apply_apply] using hv
    nlinarith [norm_nonneg (e v)]
  continuousAt x := by
    exact ((f.normalRepresentative x hn).continuous.inner
      (f.normalRepresentative x hn).continuous).continuousAt

/-- The normal metric is the ambient inner product on orthogonal representatives. -/
@[simp]
theorem normalRiemannianMetric_inner (f : SmoothEmbedding I J n M N) (hn : n ≠ 0)
    (x : M) (v w : f.NormalSpace x hn) :
    (f.normalRiemannianMetric hn).inner x v w =
      inner ℝ (f.normalRepresentative x hn v) (f.normalRepresentative x hn w) :=
  by simp [normalRiemannianMetric]

variable [FiniteDimensional ℝ E] [IsManifold J 1 N] {m : ℕ∞ω}
  [IsManifold I (m + 1) M] [IsManifold J (m + 1) N]
  [IsContMDiffRiemannianBundle J m V (fun y : N ↦ TangentSpace J y)]

/-- The induced normal metric is `C^m` for a `C^n` embedding with `m + 1 ≤ n` into a manifold
with a `C^m` Riemannian metric. No compactness, boundarylessness or normal framing is required. -/
def normalContMDiffRiemannianMetric (f : SmoothEmbedding I J n M N)
    (hn : n ≠ 0) (hm : m + 1 ≤ n)
    (hdim : Module.finrank ℝ P = Module.finrank ℝ V - Module.finrank ℝ E) :
    haveI : IsManifold I 1 M := .of_le (n := m + 1) le_add_self
    letI := f.normalSpaceFiberBundle hn hdim
    letI := f.normalSpaceVectorBundle hn hdim
    ContMDiffRiemannianMetric I m P (fun x => f.NormalSpace x hn) := by
  have : IsManifold I 1 M := .of_le (n := m + 1) le_add_self
  have : IsManifold J 1 N := .of_le (n := m + 1) le_add_self
  let := f.normalSpaceFiberBundle hn hdim
  let := f.normalSpaceVectorBundle hn hdim
  let := f.normalSpaceContMDiffVectorBundle hn hm hdim
  refine { f.normalRiemannianMetric hn with contMDiff := ?_ }
  intro x
  let e := trivializationAt P (fun x => f.NormalSpace x hn) x
  let b := Module.Basis.ofVectorSpace ℝ P
  let e' := trivializationAt (P →L[ℝ] ℝ) (fun x => f.NormalSpace x hn →L[ℝ] ℝ) x
  let eℝ := trivializationAt ℝ (Bundle.Trivial M ℝ) x
  have he' : e'.baseSet = e.baseSet := by simp [e', e]
  let A (y : M) : f.NormalSpace y hn →L[ℝ] f.NormalSpace y hn →L[ℝ] ℝ :=
    (f.normalRiemannianMetric hn).inner y
  have : ∀ y, IsTopologicalAddGroup (f.NormalSpace y hn →L[ℝ] ℝ) := fun y => inferInstance
  have : ∀ y, ContinuousSMul ℝ (f.NormalSpace y hn →L[ℝ] ℝ) := fun y => inferInstance
  -- Test the bilinear field on two copies of a local normal frame.
  have hform : ContMDiffOn I (I.prod 𝓘(ℝ, P →L[ℝ] P →L[ℝ] ℝ)) m
      (fun y => (⟨y, A y⟩ : TotalSpace (P →L[ℝ] P →L[ℝ] ℝ)
        (fun y => f.NormalSpace y hn →L[ℝ] f.NormalSpace y hn →L[ℝ] ℝ))) e.baseSet := by
    apply TauCeti.Manifold.contMDiffOn_hom_of_localFrame
      (I := I) (n := m) (V := fun x => f.NormalSpace x hn)
      (V' := fun x => f.NormalSpace x hn →L[ℝ] ℝ) (F' := P →L[ℝ] ℝ)
      (e := e) (e' := e') b (J := I) (f := fun y => y) (u := e.baseSet)
      contMDiffOn_id (fun y hy => ⟨hy, he' ▸ hy⟩)
    intro i
    apply TauCeti.Manifold.contMDiffOn_hom_of_localFrame
      (I := I) (n := m) (V := fun x => f.NormalSpace x hn)
      (V' := Bundle.Trivial M ℝ) (F' := ℝ) (e := e) (e' := eℝ) b (J := I)
      (f := fun y => y) (u := e.baseSet) contMDiffOn_id (fun y hy => ⟨hy, by simp [eℝ]⟩)
    intro j
    -- Orthogonal representatives of the frame sections are smooth ambient tangent fields.
    have hi := (f.contMDiff_normalRepresentative hn hm hdim).comp_contMDiffOn
      (e.contMDiffOn_localFrame_baseSet m b i)
    have hj := (f.contMDiff_normalRepresentative hn hm hdim).comp_contMDiffOn
      (e.contMDiffOn_localFrame_baseSet m b j)
    have hpair : ContMDiffOn I 𝓘(ℝ) m
        (fun y => inner ℝ (f.normalRepresentative y hn (e.localFrame b i y))
          (f.normalRepresentative y hn (e.localFrame b j y))) e.baseSet :=
      ContMDiffOn.inner_bundle (IB := J) (E := fun y : N => TangentSpace J y)
        (F := V) (b := fun y => f y)
        (v := fun y => f.normalRepresentative y hn (e.localFrame b i y))
        (w := fun y => f.normalRepresentative y hn (e.localFrame b j y)) hi hj
    intro y hy
    apply Bundle.contMDiffWithinAt_totalSpace.mpr
    refine ⟨contMDiffWithinAt_id, ?_⟩
    simpa [A, Trivial.fiberBundle_trivializationAt'] using hpair y hy
  exact hform.contMDiffAt (e.open_baseSet.mem_nhds (mem_baseSet_trivializationAt _ _ x))

/-- The smooth normal metric has the same inner products as the fibrewise normal metric. -/
@[simp]
theorem normalContMDiffRiemannianMetric_inner (f : SmoothEmbedding I J n M N)
    (hn : n ≠ 0) (hm : m + 1 ≤ n)
    (hdim : Module.finrank ℝ P = Module.finrank ℝ V - Module.finrank ℝ E)
    (x : M) (v w : f.NormalSpace x hn) :
    haveI : IsManifold I 1 M := .of_le (n := m + 1) le_add_self
    letI := f.normalSpaceFiberBundle hn hdim
    letI := f.normalSpaceVectorBundle hn hdim
    (f.normalContMDiffRiemannianMetric hn hm hdim).inner x v w =
      inner ℝ (f.normalRepresentative x hn v) (f.normalRepresentative x hn w) :=
  by simp [normalContMDiffRiemannianMetric]

/-- Forgetting the normal metric's smoothness recovers the original fibrewise metric. -/
@[simp]
theorem toRiemannianMetric_normalContMDiffRiemannianMetric
    (f : SmoothEmbedding I J n M N) (hn : n ≠ 0) (hm : m + 1 ≤ n)
    (hdim : Module.finrank ℝ P = Module.finrank ℝ V - Module.finrank ℝ E) :
    haveI : IsManifold I 1 M := .of_le (n := m + 1) le_add_self
    letI := f.normalSpaceFiberBundle hn hdim
    letI := f.normalSpaceVectorBundle hn hdim
    (f.normalContMDiffRiemannianMetric hn hm hdim).toRiemannianMetric =
      f.normalRiemannianMetric hn :=
  (rfl)

end TauCeti.SmoothEmbedding
