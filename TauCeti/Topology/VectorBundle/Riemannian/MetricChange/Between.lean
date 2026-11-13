/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.Positive.MetricChange.Naturality
public import TauCeti.Topology.VectorBundle.Riemannian.MetricChange.Basic

/-!
# Canonical transport between continuous Riemannian metrics

Two continuous positive metrics `h` and `k` on a finite-dimensional real vector bundle determine
an intrinsic fibrewise linear transport from `h` to `k`. It is positive and self-adjoint for `h`,
and preserves the two metrics. The construction is the inverse square root of the relative Riesz
operator, expressed on the original fibres by `ContinuousLinearMap.metricChangeBetween`.

`Bundle.ContinuousRiemannianMetric.metricChangeBetweenHomeomorph` bundles this transport as a
homeomorphism of the original total space over the identity of the base. Its inverse is the
canonical transport with the metrics interchanged. Continuity is proved in ordinary linear
bundle charts, using coordinate independence of the canonical transport; the auxiliary fibre
inner products need not vary continuously.

## References

* R. Bhatia, *Positive Definite Matrices*, Princeton University Press, 2007, Chapter 1
  (positive square roots and congruences of inner products).
* J. Milnor and J. Stasheff, *Characteristic Classes*, Princeton University Press, 1974, §2
  (Euclidean vector bundles).
-/

public noncomputable section

open Bundle InnerProductSpace TauCeti
open scoped InnerProductSpace Topology

namespace Bundle.ContinuousRiemannianMetric

variable {B : Type*} [TopologicalSpace B] {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {E : B → Type*} [TopologicalSpace (TotalSpace F E)] [∀ b, NormedAddCommGroup (E b)]
  [∀ b, InnerProductSpace ℝ (E b)] [∀ b, FiniteDimensional ℝ (E b)] [FiberBundle F E]
  [VectorBundle ℝ F E] (h k : ContinuousRiemannianMetric F E)

/-- Canonical transport between two continuous positive metrics acts continuously on the original
bundle total space. The reference inner products on the fibres need not be continuous. -/
theorem continuous_metricChangeBetween :
    Continuous fun p : TotalSpace F E ↦
      (⟨p.proj, (h.inner p.proj).metricChangeBetween (k.inner p.proj) p.2⟩ : TotalSpace F E) := by
  refine continuous_iff_continuousAt.2 fun p₀ ↦ ?_
  let e := trivializationAt F E p₀.proj
  have hp₀ : p₀.proj ∈ e.baseSet := mem_baseSet_trivializationAt F E p₀.proj
  -- A single actual fibre supplies a Hilbert model; no reference metric continuity is needed.
  let e₀ := e.continuousLinearEquivAt ℝ p₀.proj hp₀
  let σ (y : e.baseSet) := e₀.trans (e.continuousLinearEquivAt ℝ y y.2).symm
  have hσ (w : E p₀.proj) :
      Continuous fun y : e.baseSet ↦ TotalSpace.mk' F (y : B) (σ y w) := by
    refine (e.continuousOn_symm.comp_continuous
      (continuous_subtype_val.prodMk (continuous_const (y := e₀ w)))
      fun y ↦ ⟨y.2, Set.mem_univ _⟩).congr fun y ↦ ?_
    simp [σ]
  let h' (y : e.baseSet) := (h.inner y).bilinearComp
    (σ y : E p₀.proj →L[ℝ] E y) (σ y : E p₀.proj →L[ℝ] E y)
  let k' (y : e.baseSet) := (k.inner y).bilinearComp
    (σ y : E p₀.proj →L[ℝ] E y) (σ y : E p₀.proj →L[ℝ] E y)
  have hT : Continuous fun y ↦ (h' y).metricChangeBetween (k' y) :=
    (h.continuous_inner_bilinearComp (f := fun y : e.baseSet ↦ (y : B))
      (fun y : e.baseSet ↦ (σ y : E p₀.proj →L[ℝ] E y))
      hσ).metricChangeBetween
      (k.continuous_inner_bilinearComp (f := fun y : e.baseSet ↦ (y : B))
        (fun y : e.baseSet ↦ (σ y : E p₀.proj →L[ℝ] E y))
        hσ)
      (fun y ↦ ContinuousLinearMap.isStrictlyPositive_continuousLinearMapOfBilin_bilinearComp_equiv
        (h.inner y) (σ y) (h.isStrictlyPositive_continuousLinearMapOfBilin_inner y))
      (fun y ↦ ContinuousLinearMap.isStrictlyPositive_continuousLinearMapOfBilin_bilinearComp_equiv
        (k.inner y) (σ y) (k.isStrictlyPositive_continuousLinearMapOfBilin_inner y))
  let U : Set (TotalSpace F E) := TotalSpace.proj ⁻¹' e.baseSet
  have hU : U ∈ 𝓝 p₀ := (e.open_baseSet.preimage (FiberBundle.continuous_proj F E)).mem_nhds hp₀
  refine ContinuousOn.continuousAt ?_ hU
  rw [continuousOn_iff_continuous_domRestrict]
  let y : U → e.baseSet := fun x ↦ ⟨x.1.proj, x.2⟩
  have hy : Continuous y :=
    ((FiberBundle.continuous_proj F E).comp continuous_subtype_val).subtype_mk _
  have hz : Continuous fun x : U ↦ (e x.1).2 :=
    continuous_snd.comp (e.continuousOn.comp_continuous continuous_subtype_val
      fun x ↦ e.mem_source.2 x.2)
  -- Express the output in the ordinary chart, then identify it by coordinate naturality.
  have hout := (e.continuousOn_symm.comp_continuous
    ((continuous_subtype_val.comp hy).prodMk
      (e₀.continuous.comp ((hT.comp hy).clm_apply (e₀.symm.continuous.comp hz))))
    fun x ↦ ⟨x.2, Set.mem_univ _⟩)
  refine hout.congr fun x ↦ ?_
  simp only [Function.comp_apply]
  have hcoord := ContinuousLinearMap.metricChangeBetween_bilinearComp
    (h.inner (y x)) (k.inner (y x)) (σ (y x))
    (h.isStrictlyPositive_continuousLinearMapOfBilin_inner (y x))
    (k.isStrictlyPositive_continuousLinearMapOfBilin_inner (y x)) (e₀.symm (e x.1).2)
  have hσx : σ (y x) (e₀.symm (e x.1).2) = x.1.2 := by
    simpa [σ, y] using e.symm_proj_apply x.1 x.2
  rw [hσx] at hcoord
  rw [hcoord]
  simpa [σ, y] using e.symm_apply_apply_mk x.2
    ((h.inner x.1.proj).metricChangeBetween (k.inner x.1.proj) x.1.2)

/-- The canonical positive source-self-adjoint transport between two continuous Riemannian
metrics, as a homeomorphism of the original total space. -/
def metricChangeBetweenHomeomorph : TotalSpace F E ≃ₜ TotalSpace F E where
  toFun p := ⟨p.proj, (h.inner p.proj).metricChangeBetween (k.inner p.proj) p.2⟩
  invFun p := ⟨p.proj, (k.inner p.proj).metricChangeBetween (h.inner p.proj) p.2⟩
  left_inv p := TotalSpace.ext rfl <| heq_of_eq <|
    ContinuousLinearMap.metricChangeBetween_apply_metricChangeBetween _ _
      (h.isStrictlyPositive_continuousLinearMapOfBilin_inner p.proj)
      (k.isStrictlyPositive_continuousLinearMapOfBilin_inner p.proj) p.2
  right_inv p := TotalSpace.ext rfl <| heq_of_eq <|
    ContinuousLinearMap.metricChangeBetween_apply_metricChangeBetween _ _
      (k.isStrictlyPositive_continuousLinearMapOfBilin_inner p.proj)
      (h.isStrictlyPositive_continuousLinearMapOfBilin_inner p.proj) p.2
  -- The generic bundle homeomorphism combinator requires a finite-dimensional model even when
  -- the base is empty. Here finite dimensionality is needed only on the actual fibres.
  continuous_toFun := h.continuous_metricChangeBetween k
  continuous_invFun := k.continuous_metricChangeBetween h

-- Evaluation and reversal remain named rewrites: simplifying them automatically can erase the
-- bundled homeomorphism before its generic inverse laws match.
/-- The canonical metric-change homeomorphism applies the intrinsic transport in each fibre. -/
theorem metricChangeBetweenHomeomorph_apply (p : TotalSpace F E) :
    h.metricChangeBetweenHomeomorph k p =
      ⟨p.proj, (h.inner p.proj).metricChangeBetween (k.inner p.proj) p.2⟩ := (rfl)

/-- The inverse applies the transport with the two metrics interchanged. -/
theorem metricChangeBetweenHomeomorph_symm_apply (p : TotalSpace F E) :
    (h.metricChangeBetweenHomeomorph k).symm p =
      ⟨p.proj, (k.inner p.proj).metricChangeBetween (h.inner p.proj) p.2⟩ := (rfl)

/-- Metric transport preserves the projection to the base. -/
@[simp]
theorem proj_metricChangeBetweenHomeomorph (p : TotalSpace F E) :
    (h.metricChangeBetweenHomeomorph k p).proj = p.proj := (rfl)

/-- The inverse metric transport also preserves the projection to the base. -/
@[simp]
theorem proj_metricChangeBetweenHomeomorph_symm (p : TotalSpace F E) :
    ((h.metricChangeBetweenHomeomorph k).symm p).proj = p.proj := by
  rw [metricChangeBetweenHomeomorph_symm_apply]

/-- Inverting metric transport interchanges its source and target metrics. -/
theorem metricChangeBetweenHomeomorph_symm :
    (h.metricChangeBetweenHomeomorph k).symm = k.metricChangeBetweenHomeomorph h := by
  apply Homeomorph.ext
  intro p
  rw [metricChangeBetweenHomeomorph_symm_apply, metricChangeBetweenHomeomorph_apply]

/-- Transport from a metric to itself is the identity. -/
@[simp]
theorem metricChangeBetweenHomeomorph_self :
    h.metricChangeBetweenHomeomorph h = Homeomorph.refl (TotalSpace F E) := by
  apply Homeomorph.ext
  intro p
  simp [metricChangeBetweenHomeomorph_apply, ContinuousLinearMap.metricChangeBetween_self _
    (h.isStrictlyPositive_continuousLinearMapOfBilin_inner p.proj)]

/-- Canonical transport is a fibrewise isometry from the source metric to the target metric. -/
@[simp]
theorem inner_metricChangeBetween_metricChangeBetween (b : B) (u v : E b) :
    k.inner b ((h.inner b).metricChangeBetween (k.inner b) u)
      ((h.inner b).metricChangeBetween (k.inner b) v) = h.inner b u v :=
  ContinuousLinearMap.apply_metricChangeBetween_metricChangeBetween _ _
    (h.isStrictlyPositive_continuousLinearMapOfBilin_inner b)
    (k.isStrictlyPositive_continuousLinearMapOfBilin_inner b) u v

/-- The successive changes from the reference metric to `h` and then to `k` agree with the
change directly to `k` after the canonical orthogonal correction in the reference metric.
In general the correction is nontrivial. -/
theorem metricChangeBetweenHomeomorph_apply_metricChangeHomeomorph
    [IsContinuousRiemannianBundle F E] (p : TotalSpace F E) :
    h.metricChangeBetweenHomeomorph k (h.metricChangeHomeomorph p) =
      k.metricChangeHomeomorph
        ⟨p.proj, (h.inner p.proj).metricChangeCompositionCorrection (k.inner p.proj)
          (h.isStrictlyPositive_continuousLinearMapOfBilin_inner p.proj)
          (k.isStrictlyPositive_continuousLinearMapOfBilin_inner p.proj) p.2⟩ := by
  rw [metricChangeBetweenHomeomorph_apply, metricChangeHomeomorph_apply,
    metricChangeHomeomorph_apply]
  apply congrArg (TotalSpace.mk' F p.proj)
  simpa only [mul_apply_eq_comp, LinearIsometryEquiv.coe_coe''] using
    congr($(ContinuousLinearMap.metricChangeBetween_mul_metricChangeTransport
      (h.inner p.proj) (k.inner p.proj)
      (h.isStrictlyPositive_continuousLinearMapOfBilin_inner p.proj)
      (k.isStrictlyPositive_continuousLinearMapOfBilin_inner p.proj)) p.2)

end Bundle.ContinuousRiemannianMetric
