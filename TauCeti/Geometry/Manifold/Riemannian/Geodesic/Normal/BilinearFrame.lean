/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Geodesic.Normal.Frame
public import TauCeti.Geometry.Manifold.VectorBundle.Riemannian.Bilinear
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.BilinearTensor

/-!
# Geodesic frames for covariant two-tensors

The products of the duals of a normal orthonormal frame form a smooth local frame of the
native bilinear-form bundle. Their covariant derivatives vanish at the centre. The
coefficients of a bilinear tensor are its evaluations on the tangent frame, and at the
centre their ordinary differentials are the components of its covariant derivative.

This gives normal-frame computations for metrics, Ricci tensors and Hessians without
choosing another tensor bundle or assuming symmetry of the tensor.

The construction uses `normalOrthonormalFrame` and
`CovariantDerivative.derivBilinearTensor`. The convention follows J. M. Lee,
*Introduction to Riemannian Manifolds*, second edition, Chapters 4–5.
-/

public noncomputable section

open Bundle CovariantDerivative InnerProductSpace Set
open scoped ContDiff Manifold Topology

-- Keep the normed and algebraic structures on nested Hom bundles consistent.
attribute [local instance 1001] NormedAddCommGroup.toSeminormedAddCommGroup
  NormedAddCommGroup.toAddCommGroup AddCommGroup.toAddCommMonoid NormedSpace.toModule

namespace TauCeti.Manifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
  {ι : Type*} [Fintype ι] [LinearOrder ι] [LocallyFiniteOrderBot ι]
  {p : M} {U : Set (TangentSpace I p)}

/-- The covariant two-tensor `eᵢ♭ ⊗ eⱼ♭` induced by the normal orthonormal frame.
Its values outside the normal neighbourhood are immaterial. -/
def normalBilinearFrame (I : ModelWithCorners ℝ E H) (M : Type*)
    [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
    (p : M) (U : Set (TangentSpace I p)) (b : OrthonormalBasis ι ℝ (TangentSpace I p))
    (k : ι × ι) (q : M) : TangentSpace I q →L[ℝ] TangentSpace I q →L[ℝ] ℝ :=
  (innerSL ℝ (normalOrthonormalFrame I M p U b k.1 q)).smulRight
    (innerSL ℝ (normalOrthonormalFrame I M p U b k.2 q))

/-- Evaluation of an induced covariant frame tensor is the product of its two dual components. -/
@[simp]
theorem normalBilinearFrame_apply (b : OrthonormalBasis ι ℝ (TangentSpace I p))
    (k : ι × ι) (q : M) (u v : TangentSpace I q) :
    normalBilinearFrame I M p U b k q u v =
      inner ℝ (normalOrthonormalFrame I M p U b k.1 q) u *
        inner ℝ (normalOrthonormalFrame I M p U b k.2 q) v := (rfl)

namespace IsNormalDomain

-- Cache the nested operator norms: otherwise elaborating the local-frame type exceeds
-- the instance-search limit for the iterated Hom bundle.
private local instance (q : M) : NormedAddCommGroup (TangentSpace I q →L[ℝ] ℝ) := inferInstance
private local instance (q : M) : NormedSpace ℝ (TangentSpace I q →L[ℝ] ℝ) := inferInstance
private local instance (q : M) : NormedAddCommGroup
    (TangentSpace I q →L[ℝ] TangentSpace I q →L[ℝ] ℝ) := inferInstance
private local instance (q : M) : NormedSpace ℝ
    (TangentSpace I q →L[ℝ] TangentSpace I q →L[ℝ] ℝ) := inferInstance

/-- Evaluation on the tangent frame gives the Kronecker components of the induced tensor frame. -/
theorem normalBilinearFrame_apply_frame (h : IsNormalDomain I M p U)
    (b : OrthonormalBasis ι ℝ (TangentSpace I p)) {q : M}
    (hq : q ∈ riemannianExp I M p '' U) (k l : ι × ι) :
    normalBilinearFrame I M p U b k q
      (normalOrthonormalFrame I M p U b l.1 q)
      (normalOrthonormalFrame I M p U b l.2 q) = if k = l then 1 else 0 := by
  classical
  simp only [normalBilinearFrame_apply,
    (orthonormal_iff_ite.mp (h.orthonormal_normalOrthonormalFrame b hq))]
  split_ifs <;> simp_all [Prod.ext_iff]

/-- Every bilinear form expands in the induced frame with its tangent-frame evaluations
as coefficients. No symmetry of the form is required. -/
theorem eq_sum_normalBilinearFrame (h : IsNormalDomain I M p U)
    (b : OrthonormalBasis ι ℝ (TangentSpace I p)) {q : M}
    (hq : q ∈ riemannianExp I M p '' U)
    (B : TangentSpace I q →L[ℝ] TangentSpace I q →L[ℝ] ℝ) :
    B = ∑ k : ι × ι, B (normalOrthonormalFrame I M p U b k.1 q)
      (normalOrthonormalFrame I M p U b k.2 q) • normalBilinearFrame I M p U b k q := by
  let e := (h.isLocalFrameOn_normalOrthonormalFrame b).toBasisAt hq
  have he (i : ι) : e i = normalOrthonormalFrame I M p U b i q :=
    IsLocalFrameOn.toBasisAt_coe _ hq i
  -- Equality of continuous bilinear maps is tested on the underlying algebraic basis twice.
  apply ContinuousLinearMap.coe_injective
  apply e.ext
  intro i
  apply ContinuousLinearMap.coe_injective
  apply e.ext
  intro j
  simp only [ContinuousLinearMap.coe_coe, he, sum_apply, smul_apply, smul_eq_mul,
    normalBilinearFrame_apply]
  simp [Fintype.sum_prod_type,
    orthonormal_iff_ite.mp (h.orthonormal_normalOrthonormalFrame b hq)]

/-- The products of the normal dual coframe form a smooth local frame of covariant
two-tensors on the normal neighbourhood. -/
theorem isLocalFrameOn_normalBilinearFrame (h : IsNormalDomain I M p U)
    (b : OrthonormalBasis ι ℝ (TangentSpace I p)) :
    IsLocalFrameOn I (E →L[ℝ] E →L[ℝ] ℝ) ∞ (normalBilinearFrame I M p U b)
      (riemannianExp I M p '' U) where
  linearIndependent {q} hq := by
    classical
    apply Fintype.linearIndependent_iff.2
    intro c hc k
    have hv := congrArg (fun B ↦ B
      (normalOrthonormalFrame I M p U b k.1 q)
      (normalOrthonormalFrame I M p U b k.2 q)) hc
    simpa only [sum_apply, smul_apply, smul_eq_mul,
      h.normalBilinearFrame_apply_frame b hq, mul_ite, mul_one, mul_zero,
      Finset.sum_ite_eq', Finset.mem_univ, ite_true, zero_apply] using hv
  generating {q} hq := by
    intro B _
    rw [h.eq_sum_normalBilinearFrame b hq B]
    exact Submodule.sum_mem _ fun k _ ↦ Submodule.smul_mem _ _
      (Submodule.subset_span (mem_range_self k))
  contMDiffOn k := by
    intro q hq
    apply ContMDiffAt.contMDiffWithinAt
    exact ContMDiffAt.innerSL_smulRight_bundle
      (F := E) (V := fun x : M ↦ TangentSpace I x)
      (σ := normalOrthonormalFrame I M p U b k.1)
      (τ := normalOrthonormalFrame I M p U b k.2)
      ((h.contMDiffOn_normalOrthonormalFrame b k.1).contMDiffAt
        (h.isOpen_image.mem_nhds hq))
      ((h.contMDiffOn_normalOrthonormalFrame b k.2).contMDiffAt
        (h.isOpen_image.mem_nhds hq))

/-- The canonical frame coefficients of a bilinear tensor are its evaluations on the normal
tangent frame. -/
@[simp]
theorem coeff_normalBilinearFrame (h : IsNormalDomain I M p U)
    (b : OrthonormalBasis ι ℝ (TangentSpace I p)) {q : M}
    (hq : q ∈ riemannianExp I M p '' U)
    (B : TangentSpace I q →L[ℝ] TangentSpace I q →L[ℝ] ℝ) (k : ι × ι) :
    (h.isLocalFrameOn_normalBilinearFrame b).coeff k q B =
      B (normalOrthonormalFrame I M p U b k.1 q)
        (normalOrthonormalFrame I M p U b k.2 q) := by
  classical
  have hexp := (h.isLocalFrameOn_normalBilinearFrame b).coeff_sum_eq
    (FiberBundle.extend (E := fun x : M ↦
      TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) (E →L[ℝ] E →L[ℝ] ℝ) B) hq
  rw [FiberBundle.extend_apply_self] at hexp
  have hv := congrArg (fun C ↦ C
    (normalOrthonormalFrame I M p U b k.1 q)
    (normalOrthonormalFrame I M p U b k.2 q)) hexp
  simpa only [sum_apply, smul_apply, smul_eq_mul,
    h.normalBilinearFrame_apply_frame b hq, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true] using hv.symm

variable [I.Boundaryless] [T2Space M]

/-- At the centre of a normal frame, the differential of a bilinear tensor component equals
the corresponding component of its covariant derivative. Only differentiability at the
centre is required. -/
theorem mvfderiv_bilinear_normalOrthonormalFrame (h : IsNormalDomain I M p U)
    (b : OrthonormalBasis ι ℝ (TangentSpace I p))
    {B : Π q : M, TangentSpace I q →L[ℝ] TangentSpace I q →L[ℝ] ℝ}
    (hB : MDifferentiableAt I (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ))
      (fun q ↦ TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ) q (B q)) p)
    (i j : ι) (v : TangentSpace I p) :
    mvfderiv I (fun q ↦ B q (normalOrthonormalFrame I M p U b i q)
      (normalOrthonormalFrame I M p U b j q)) p v =
        (leviCivitaConnection I M).derivBilinearTensor B p (b i) (b j) v := by
  have hf (k : ι) : MDiffAt (T% (normalOrthonormalFrame I M p U b k)) p :=
    ((h.contMDiffOn_normalOrthonormalFrame b k).contMDiffAt
      (h.isOpen_image.mem_nhds h.self_mem_image)).mdifferentiableAt (by simp)
  have hb : ∀ ⦃σ τ : Π q : M, TangentSpace I q⦄, MDiffAt (T% σ) p →
      MDiffAt (T% τ) p → MDiffAt (fun q ↦ B q (σ q) (τ q)) p := by
    intro σ τ hσ hτ
    exact ((mdifferentiableAt_totalSpace I _).mp (hB.clm_bundle_apply₂ hσ hτ)).2
  have hd := (leviCivitaConnection I M).derivBilinearTensor_apply hb (hf i) (hf j) v
  simpa only [h.normalOrthonormalFrame_self,
    h.leviCivitaConnection_normalOrthonormalFrame_self, zero_apply,
    map_zero, sub_zero] using hd.symm

/-- Every induced covariant frame tensor is parallel at the centre, for the canonical
covariant derivative of bilinear tensors. -/
@[simp]
theorem derivBilinearTensor_normalBilinearFrame_self (h : IsNormalDomain I M p U)
    (b : OrthonormalBasis ι ℝ (TangentSpace I p)) (k : ι × ι) :
    (leviCivitaConnection I M).derivBilinearTensor
      (normalBilinearFrame I M p U b k) p = 0 := by
  have hF := ((h.isLocalFrameOn_normalBilinearFrame b).contMDiffAt
    h.isOpen_image h.self_mem_image k).mdifferentiableAt (by simp)
  -- Test the bilinear arguments on the original basis; the frame components are constant
  -- Kronecker symbols throughout the normal neighbourhood.
  apply ContinuousLinearMap.coe_injective
  apply b.toBasis.ext
  intro i
  apply ContinuousLinearMap.coe_injective
  apply b.toBasis.ext
  intro j
  ext v
  simp only [OrthonormalBasis.coe_toBasis, ContinuousLinearMap.coe_coe]
  rw [← h.mvfderiv_bilinear_normalOrthonormalFrame b hF]
  have hc : (fun q ↦ normalBilinearFrame I M p U b k q
      (normalOrthonormalFrame I M p U b i q)
      (normalOrthonormalFrame I M p U b j q)) =ᶠ[𝓝 p]
      fun _ ↦ if k = (i, j) then (1 : ℝ) else 0 := by
    filter_upwards [h.isOpen_image.mem_nhds h.self_mem_image] with q hq
    exact h.normalBilinearFrame_apply_frame b hq k (i, j)
  rw [hc.mvfderiv_eq, mvfderiv_const]
  rfl

end IsNormalDomain

end TauCeti.Manifold
