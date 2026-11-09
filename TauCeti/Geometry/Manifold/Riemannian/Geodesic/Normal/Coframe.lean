/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Geodesic.Normal.Frame.Basic
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Metric.Dual

/-!
# Geodesic coframes

The metric duals of the normal orthonormal tangent frame form a smooth coframe on the same
normal neighbourhood. They are parallel at its centre for the connection induced on the
cotangent bundle. The coefficient of a one-form in this coframe is its evaluation on the
corresponding tangent-frame vector. At the centre, differentiating that coefficient therefore
computes the corresponding component of the covariant derivative of the one-form.

The construction uses `normalOrthonormalFrame`, Mathlib's `IsLocalFrameOn`, and the induced
`CovariantDerivative.hom` connection to the trivial real line; it introduces no new cotangent
carrier or connection.

## References

* J. M. Lee, *Introduction to Riemannian Manifolds*, second edition, Chapters 4–5
  (dual connections and geodesic frames).
-/

public noncomputable section

open Bundle CovariantDerivative InnerProductSpace Set
open scoped ContDiff Manifold

namespace TauCeti.Manifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
  {ι : Type*} [Fintype ι] [LinearOrder ι] [LocallyFiniteOrderBot ι]
  {p : M} {U : Set (TangentSpace I p)}

/-- The metric-dual coframe of the normal orthonormal tangent frame. On a normal domain it
is smooth and parallel at the centre. Elsewhere it inherits the frame's junk values. -/
def normalCoframe (I : ModelWithCorners ℝ E H) (M : Type*)
    [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
    (p : M) (U : Set (TangentSpace I p)) (b : OrthonormalBasis ι ℝ (TangentSpace I p))
    (i : ι) (q : M) : TangentSpace I q →L[ℝ] ℝ :=
  innerSL ℝ (normalOrthonormalFrame I M p U b i q)

/-- The normal coframe consists of the metric duals of the normal tangent-frame vectors. -/
theorem normalCoframe_def (b : OrthonormalBasis ι ℝ (TangentSpace I p)) (i : ι) :
    normalCoframe I M p U b i = fun q ↦ innerSL ℝ (normalOrthonormalFrame I M p U b i q) := (rfl)

/-- Evaluation of the normal coframe is pairing with its tangent-frame vector. -/
@[simp]
theorem normalCoframe_apply (b : OrthonormalBasis ι ℝ (TangentSpace I p))
    (i : ι) (q : M) (v : TangentSpace I q) :
    normalCoframe I M p U b i q v = inner ℝ (normalOrthonormalFrame I M p U b i q) v := (rfl)

variable [I.Boundaryless] [T2Space M]

namespace IsNormalDomain

/-- Each covector in the normal coframe is smooth on the normal neighbourhood. -/
theorem contMDiffOn_normalCoframe (h : IsNormalDomain I M p U)
    (b : OrthonormalBasis ι ℝ (TangentSpace I p)) (i : ι) :
    ContMDiffOn I (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) ∞
      (fun q ↦ TotalSpace.mk' (E →L[ℝ] ℝ) q (normalCoframe I M p U b i q))
      (riemannianExp I M p '' U) := by
  intro q hq
  exact ContMDiffWithinAt.innerSL_bundle (I := I) (F := E)
    (V := fun x : M ↦ TangentSpace I x) (h.contMDiffOn_normalOrthonormalFrame b i q hq)

/-- The normal coframe and the normal tangent frame are dual on their common domain. -/
theorem normalCoframe_normalOrthonormalFrame (h : IsNormalDomain I M p U)
    (b : OrthonormalBasis ι ℝ (TangentSpace I p)) {q : M}
    (hq : q ∈ riemannianExp I M p '' U) (i j : ι) :
    normalCoframe I M p U b i q (normalOrthonormalFrame I M p U b j q) =
      if i = j then 1 else 0 := by
  rw [normalCoframe_apply]
  exact (orthonormal_iff_ite.mp (h.orthonormal_normalOrthonormalFrame b hq)) i j

/-- The metric-dual normal frame is a smooth local frame of the native cotangent bundle. -/
theorem isLocalFrameOn_normalCoframe (h : IsNormalDomain I M p U)
    (b : OrthonormalBasis ι ℝ (TangentSpace I p)) :
    IsLocalFrameOn I (E →L[ℝ] ℝ) ∞ (normalCoframe I M p U b)
      (riemannianExp I M p '' U) where
  linearIndependent {q} hq := by
    let B := (h.isLocalFrameOn_normalOrthonormalFrame b).toBasisAt hq
    let e := (InnerProductSpace.toDual ℝ (TangentSpace I q)).toLinearEquiv
    have heq : ⇑(B.map e) = fun i ↦ normalCoframe I M p U b i q := by
      ext i w
      simp only [B, e, Module.Basis.map_apply, IsLocalFrameOn.toBasisAt_coe,
        normalCoframe_apply, LinearIsometryEquiv.coe_toLinearEquiv, toDual_apply_apply]
    rw [← heq]
    exact (B.map e).linearIndependent
  generating {q} hq := by
    let B := (h.isLocalFrameOn_normalOrthonormalFrame b).toBasisAt hq
    let e := (InnerProductSpace.toDual ℝ (TangentSpace I q)).toLinearEquiv
    have heq : ⇑(B.map e) = fun i ↦ normalCoframe I M p U b i q := by
      ext i w
      simp only [B, e, Module.Basis.map_apply, IsLocalFrameOn.toBasisAt_coe,
        normalCoframe_apply, LinearIsometryEquiv.coe_toLinearEquiv, toDual_apply_apply]
    rw [← heq]
    exact (B.map e).span_eq.ge
  contMDiffOn := h.contMDiffOn_normalCoframe b

/-- At the centre the normal coframe is the metric dual of the prescribed basis. -/
@[simp]
theorem normalCoframe_self (h : IsNormalDomain I M p U)
    (b : OrthonormalBasis ι ℝ (TangentSpace I p)) (i : ι) :
    normalCoframe I M p U b i p = innerSL ℝ (b i) := by
  ext v
  simp [h.normalOrthonormalFrame_self]

/-- The normal coframe is parallel at its centre for the induced covector connection. -/
@[simp]
theorem hom_trivial_normalCoframe_self (h : IsNormalDomain I M p U)
    (b : OrthonormalBasis ι ℝ (TangentSpace I p)) (i : ι) :
    ((leviCivitaConnection I M).hom (CovariantDerivative.trivial (I := I) ℝ))
      (normalCoframe I M p U b i) p = 0 := by
  ext v w
  have hd := (h.contMDiffOn_normalOrthonormalFrame b i).contMDiffAt
    (h.isOpen_image.mem_nhds h.self_mem_image)
  rw [normalCoframe_def, (isMetricCompatible_leviCivitaConnection I).hom_trivial_innerSL
    (hd.mdifferentiableAt (by simp)), h.leviCivitaConnection_normalOrthonormalFrame_self]
  simp

/-- The coefficient of a one-form in the normal coframe is its evaluation on the corresponding
normal tangent-frame vector. -/
@[simp]
theorem repr_normalCoframe (h : IsNormalDomain I M p U)
    (b : OrthonormalBasis ι ℝ (TangentSpace I p))
    (α : Π q : M, TangentSpace I q →L[ℝ] ℝ) {q : M}
    (hq : q ∈ riemannianExp I M p '' U) (i : ι) :
    ((h.isLocalFrameOn_normalCoframe b).toBasisAt hq).repr (α q) i =
      α q (normalOrthonormalFrame I M p U b i q) := by
  rw [← (h.isLocalFrameOn_normalCoframe b).coeff_apply_of_mem hq α i]
  have hexp := (h.isLocalFrameOn_normalCoframe b).coeff_sum_eq α hq
  have heval := congrArg (fun β : TangentSpace I q →L[ℝ] ℝ ↦
    β (normalOrthonormalFrame I M p U b i q)) hexp
  simpa only [sum_apply, smul_apply,
    h.normalCoframe_normalOrthonormalFrame b hq, smul_eq_mul, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true] using heval.symm

/-- Expand a one-form in the normal coframe by evaluating it on the tangent frame. -/
theorem sum_normalCoframe (h : IsNormalDomain I M p U)
    (b : OrthonormalBasis ι ℝ (TangentSpace I p))
    (α : Π q : M, TangentSpace I q →L[ℝ] ℝ) {q : M}
    (hq : q ∈ riemannianExp I M p '' U) :
    ∑ i, α q (normalOrthonormalFrame I M p U b i q) • normalCoframe I M p U b i q =
      α q := by
  simpa only [(h.isLocalFrameOn_normalCoframe b).coeff_apply_of_mem hq α,
    h.repr_normalCoframe b α hq] using
    ((h.isLocalFrameOn_normalCoframe b).coeff_sum_eq α hq).symm

/-- At the centre of a normal coframe, differentiation of a one-form component equals the
corresponding component of its covariant derivative. Only pointwise differentiability of the
one-form is required. -/
theorem mvfderiv_normalCoframe_component (h : IsNormalDomain I M p U)
    (b : OrthonormalBasis ι ℝ (TangentSpace I p))
    {α : Π q : M, TangentSpace I q →L[ℝ] ℝ}
    (hα : MDifferentiableAt I (I.prod 𝓘(ℝ, E →L[ℝ] ℝ))
      (fun q ↦ TotalSpace.mk' (E →L[ℝ] ℝ) q (α q)) p)
    (i : ι) (v : TangentSpace I p) :
    mvfderiv I (fun q ↦ α q (normalOrthonormalFrame I M p U b i q)) p v =
      ((leviCivitaConnection I M).hom (CovariantDerivative.trivial (I := I) ℝ)) α p v (b i) := by
  have hX := (h.contMDiffOn_normalOrthonormalFrame b i).contMDiffAt
    (h.isOpen_image.mem_nhds h.self_mem_image)
  rw [← h.normalOrthonormalFrame_self b i,
    hom_apply _ _ hα (hX.mdifferentiableAt (by simp)),
    CovariantDerivative.trivial_apply, h.leviCivitaConnection_normalOrthonormalFrame_self]
  simp only [zero_apply, map_zero, sub_zero]

end IsNormalDomain

end TauCeti.Manifold
