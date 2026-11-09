/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Geodesic.Normal.Frame.Basic
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Hom
import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Metric.Hom
import Mathlib.LinearAlgebra.Matrix.ToLin

/-!
# Endomorphism frames induced by geodesic frames

A normal orthonormal tangent frame `eᵢ` induces the matrix-unit frame
`Eᵢⱼ(v) = ⟪eⱼ, v⟫ eᵢ` of the native tangent endomorphism bundle.
It is smooth on the normal neighbourhood and parallel at its centre for the
induced Hom connection. Thus differentiating endomorphism components at that
point computes their covariant derivatives without connection corrections.

The pointwise frame is Mathlib's `Basis.end`, transported to continuous linear
maps. No Hilbert space structure on the operator-norm endomorphism bundle is
asserted. In particular the construction applies in dimension zero as well.

## References

* J. M. Lee, *Introduction to Riemannian Manifolds*, second edition, Chapters 4–5
  (induced tensor frames and geodesic frames).
* `normalOrthonormalFrame` supplies the tangent frame and its central parallelism;
  `CovariantDerivative.hom` supplies the induced endomorphism connection, and the general
  metric comparisons `CovariantDerivative.IsMetricCompatible.inner_hom_apply_eq_mvfderiv_inner`
  and `CovariantDerivative.IsMetricCompatible.hom_rankOne_eq_zero` specialise to the centre.
-/

public noncomputable section

open Bundle CovariantDerivative InnerProductSpace Set
open scoped ContDiff Manifold RealInnerProductSpace Topology

namespace TauCeti.Manifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
  {ι : Type*} [Fintype ι] [LinearOrder ι] [LocallyFiniteOrderBot ι]
  {p : M} {U : Set (TangentSpace I p)}

/-- The matrix units of the normal orthonormal frame. The first index is the output
index and the second is the input index. -/
def normalEndomorphismFrame (I : ModelWithCorners ℝ E H) (M : Type*)
    [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
    (p : M) (U : Set (TangentSpace I p)) (b : OrthonormalBasis ι ℝ (TangentSpace I p))
    (ij : ι × ι) (q : M) : TangentSpace I q →L[ℝ] TangentSpace I q :=
  rankOne ℝ (normalOrthonormalFrame I M p U b ij.1 q)
    (normalOrthonormalFrame I M p U b ij.2 q)

/-- A normal matrix unit acts by the corresponding inner-product coordinate. -/
@[simp]
theorem normalEndomorphismFrame_apply (b : OrthonormalBasis ι ℝ (TangentSpace I p))
    (ij : ι × ι) (q : M) (v : TangentSpace I q) :
    normalEndomorphismFrame I M p U b ij q v =
      ⟪normalOrthonormalFrame I M p U b ij.2 q, v⟫ •
        normalOrthonormalFrame I M p U b ij.1 q := (rfl)

variable [I.Boundaryless] [T2Space M]

namespace IsNormalDomain

/-- Each normal matrix unit is a smooth section of the native endomorphism bundle
on the normal neighbourhood. -/
theorem contMDiffOn_normalEndomorphismFrame (h : IsNormalDomain I M p U)
    (b : OrthonormalBasis ι ℝ (TangentSpace I p)) (ij : ι × ι) :
    ContMDiffOn I (I.prod 𝓘(ℝ, E →L[ℝ] E)) ∞
      (fun q ↦ TotalSpace.mk' (E →L[ℝ] E)
        (E := fun q : M ↦ TangentSpace I q →L[ℝ] TangentSpace I q) q
        (normalEndomorphismFrame I M p U b ij q)) (riemannianExp I M p '' U) := by
  intro q hq
  have h₁ := (h.contMDiffOn_normalOrthonormalFrame b ij.1).contMDiffAt
    (h.isOpen_image.mem_nhds hq)
  have h₂ := (h.contMDiffOn_normalOrthonormalFrame b ij.2).contMDiffAt
    (h.isOpen_image.mem_nhds hq)
  exact (ContMDiffAt.rankOne_bundle (V := fun q : M ↦ TangentSpace I q) (F := E)
    (W := fun q : M ↦ TangentSpace I q) (F' := E)
    (fiberNorm := fun q ↦ inferInstanceAs (NormedAddCommGroup (TangentSpace I q)))
    (targetNorm := fun q ↦ inferInstanceAs (NormedAddCommGroup (TangentSpace I q)))
    h₁ h₂).contMDiffWithinAt

/-- The normal endomorphism frame is the basis of matrix units induced by the
normal tangent basis at each point of the normal neighbourhood. -/
theorem normalEndomorphismFrame_eq_basis_end (h : IsNormalDomain I M p U)
    (b : OrthonormalBasis ι ℝ (TangentSpace I p)) {q : M}
    (hq : q ∈ riemannianExp I M p '' U) (ij : ι × ι) :
    normalEndomorphismFrame I M p U b ij q =
      LinearMap.toContinuousLinearMap
        (((h.isLocalFrameOn_normalOrthonormalFrame b).toBasisAt hq).end ij) := by
  apply ContinuousLinearMap.coe_injective
  apply ((h.isLocalFrameOn_normalOrthonormalFrame b).toBasisAt hq).ext
  intro k
  have hright := Module.Basis.end_apply_apply
    ((h.isLocalFrameOn_normalOrthonormalFrame b).toBasisAt hq) ij k
  simpa only [ContinuousLinearMap.coe_coe, LinearMap.coe_toContinuousLinearMap,
    normalEndomorphismFrame_apply,
    IsLocalFrameOn.toBasisAt_coe,
    orthonormal_iff_ite.mp (h.orthonormal_normalOrthonormalFrame b hq),
    ite_smul, one_smul, zero_smul] using hright.symm

/-- The induced matrix units form a smooth local frame of the tangent endomorphism bundle. -/
theorem isLocalFrameOn_normalEndomorphismFrame (h : IsNormalDomain I M p U)
    (b : OrthonormalBasis ι ℝ (TangentSpace I p)) :
    IsLocalFrameOn I (E →L[ℝ] E) ∞ (normalEndomorphismFrame I M p U b)
      (riemannianExp I M p '' U) := by
  have hb {q : M} (hq : q ∈ riemannianExp I M p '' U) :
      ∃ B : Module.Basis (ι × ι) ℝ (TangentSpace I q →L[ℝ] TangentSpace I q),
        ⇑B = fun ij ↦ normalEndomorphismFrame I M p U b ij q := by
    refine ⟨(((h.isLocalFrameOn_normalOrthonormalFrame b).toBasisAt hq).end).map
      LinearMap.toContinuousLinearMap, ?_⟩
    funext ij
    exact (h.normalEndomorphismFrame_eq_basis_end b hq ij).symm
  exact {
    linearIndependent := fun hq ↦ by
      obtain ⟨B, hB⟩ := hb hq
      rw [← hB]
      exact B.linearIndependent
    generating := fun hq ↦ by
      obtain ⟨B, hB⟩ := hb hq
      rw [← hB, B.span_eq]
    contMDiffOn := h.contMDiffOn_normalEndomorphismFrame b }

/-- At the centre, the induced endomorphism frame is the prescribed matrix-unit basis. -/
@[simp]
theorem normalEndomorphismFrame_self (h : IsNormalDomain I M p U)
    (b : OrthonormalBasis ι ℝ (TangentSpace I p)) (ij : ι × ι) :
    normalEndomorphismFrame I M p U b ij p = rankOne ℝ (b ij.1) (b ij.2) := by
  ext v
  simp [h.normalOrthonormalFrame_self b]

/-- The coordinates of an endomorphism in the normal matrix-unit frame are its
usual matrix entries in the normal orthonormal tangent frame. -/
theorem coeff_normalEndomorphismFrame (h : IsNormalDomain I M p U)
    (b : OrthonormalBasis ι ℝ (TangentSpace I p)) {q : M}
    (hq : q ∈ riemannianExp I M p '' U)
    (A : Π q : M, TangentSpace I q →L[ℝ] TangentSpace I q) (ij : ι × ι) :
    (h.isLocalFrameOn_normalEndomorphismFrame b).coeff ij q (A q) =
      ⟪normalOrthonormalFrame I M p U b ij.1 q,
        A q (normalOrthonormalFrame I M p U b ij.2 q)⟫ := by
  have heq := (h.isLocalFrameOn_normalEndomorphismFrame b).coeff_sum_eq A hq
  have hentry := congrArg (fun B : TangentSpace I q →L[ℝ] TangentSpace I q ↦
    ⟪normalOrthonormalFrame I M p U b ij.1 q,
      B (normalOrthonormalFrame I M p U b ij.2 q)⟫) heq
  simpa [sum_apply, inner_sum, apply_ite, inner_smul_right, normalEndomorphismFrame_apply,
    orthonormal_iff_ite.mp (h.orthonormal_normalOrthonormalFrame b hq),
    Fintype.sum_prod_type] using hentry.symm

/-- At the centre of a geodesic frame, ordinary derivatives of the matrix entries
of an endomorphism are the entries of its induced covariant derivative.
Only differentiability of the endomorphism section at the centre is required. -/
theorem inner_hom_eq_mvfderiv_inner_normalOrthonormalFrame (h : IsNormalDomain I M p U)
    (b : OrthonormalBasis ι ℝ (TangentSpace I p))
    {A : Π q : M, TangentSpace I q →L[ℝ] TangentSpace I q}
    (hA : MDifferentiableAt I (I.prod 𝓘(ℝ, E →L[ℝ] E))
      (fun q ↦ TotalSpace.mk' (E →L[ℝ] E)
        (E := fun q : M ↦ TangentSpace I q →L[ℝ] TangentSpace I q) q (A q)) p)
    (v : TangentSpace I p) (i j : ι) :
    ⟪b i, ((leviCivitaConnection I M).hom (leviCivitaConnection I M) A p v) (b j)⟫ =
      mvfderiv I (fun q ↦ ⟪normalOrthonormalFrame I M p U b i q,
        A q (normalOrthonormalFrame I M p U b j q)⟫) p v := by
  have he (k : ι) : MDiffAt (T% (normalOrthonormalFrame I M p U b k)) p :=
    ((h.contMDiffOn_normalOrthonormalFrame b k).contMDiffAt
      (h.isOpen_image.mem_nhds h.self_mem_image)).mdifferentiableAt (by simp)
  simpa only [h.normalOrthonormalFrame_self b] using
    (isMetricCompatible_leviCivitaConnection I).inner_hom_apply_eq_mvfderiv_inner hA (he i)
      (he j) (h.leviCivitaConnection_normalOrthonormalFrame_self b i)
      (h.leviCivitaConnection_normalOrthonormalFrame_self b j) v

/-- The induced Hom connection of every normal matrix unit vanishes at the centre. -/
@[simp]
theorem hom_normalEndomorphismFrame_self (h : IsNormalDomain I M p U)
    (b : OrthonormalBasis ι ℝ (TangentSpace I p)) (ij : ι × ι) :
    ((leviCivitaConnection I M).hom (leviCivitaConnection I M))
      (normalEndomorphismFrame I M p U b ij) p = 0 := by
  have he (k : ι) : CMDiffAt 1 (T% (normalOrthonormalFrame I M p U b k)) p :=
    ((h.contMDiffOn_normalOrthonormalFrame b k).contMDiffAt
      (h.isOpen_image.mem_nhds h.self_mem_image)).of_le (by simp)
  exact (isMetricCompatible_leviCivitaConnection I).hom_rankOne_eq_zero
    (V := fun q : M ↦ TangentSpace I q) (F := E) (W := fun q : M ↦ TangentSpace I q) (G := E)
    (fiberNorm := fun q ↦ inferInstanceAs (NormedAddCommGroup (TangentSpace I q)))
    (targetNorm := fun q ↦ inferInstanceAs (NormedAddCommGroup (TangentSpace I q)))
    (he ij.1) (he ij.2)
    (h.leviCivitaConnection_normalOrthonormalFrame_self b ij.1)
    (h.leviCivitaConnection_normalOrthonormalFrame_self b ij.2)

end IsNormalDomain

end TauCeti.Manifold
