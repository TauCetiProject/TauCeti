/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Geodesic.Normal.Coordinates
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.GramSchmidt
public import Mathlib.Geometry.Manifold.VectorBundle.LocalFrame
import TauCeti.Geometry.Manifold.IsManifold.Basic

/-!
# Orthonormal geodesic frames

An orthonormal basis at a point extends to a smooth orthonormal frame on any normal
neighbourhood, with zero covariant derivative at its centre. Apply Gram–Schmidt to the normal
coordinate fields. Since those fields are parallel at the centre, metric compatibility makes
the orthonormalized fields parallel there as well.

These frames allow tensor and curvature calculations in an orthonormal frame whose connection
coefficients vanish at the point of calculation. They are orthonormal throughout the normal
neighbourhood; they need not be coordinate fields or be parallel away from its centre.

`OrthonormalBasis.normalFrameExpansion` reconstructs an initial tangent vector at another point
from its orthonormal components in the frame; on the normal neighbourhood this preserves
components and inner products, and it is the identity at the centre.

## References

* J. M. Lee, *Introduction to Riemannian Manifolds*, second edition, Chapter 5
  (normal coordinates and geodesic frames).
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

/-- The orthonormalization of normal coordinate fields based on an orthonormal basis at `p`.
On a normal neighbourhood these are smooth orthonormal frame sections, parallel at `p`.
Outside that neighbourhood they carry the junk values of the normal coordinate fields. -/
def normalOrthonormalFrame (I : ModelWithCorners ℝ E H) (M : Type*)
    [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
    (p : M) (U : Set (TangentSpace I p)) (b : OrthonormalBasis ι ℝ (TangentSpace I p))
    (i : ι) (q : M) : TangentSpace I q :=
  gramSchmidtNormed ℝ (fun j ↦ normalCoordinateField I M p U (b j) q) i

/-- The normal orthonormal frame is normalized Gram–Schmidt on the normal coordinate fields. -/
theorem normalOrthonormalFrame_def (b : OrthonormalBasis ι ℝ (TangentSpace I p)) (i : ι) (q : M) :
    normalOrthonormalFrame I M p U b i q =
      gramSchmidtNormed ℝ (fun j ↦ normalCoordinateField I M p U (b j) q) i := (rfl)

/-- Reconstruct an initial tangent vector in the normal orthonormal frame at another point. -/
def _root_.OrthonormalBasis.normalFrameExpansion (b : OrthonormalBasis ι ℝ (TangentSpace I p))
    (q : M) (a : TangentSpace I p) : TangentSpace I q :=
  ∑ i, ⟪b i, a⟫_ℝ • normalOrthonormalFrame I M p U b i q

/-- Frame reconstruction uses the initial orthonormal components. -/
theorem _root_.OrthonormalBasis.normalFrameExpansion_apply
    (b : OrthonormalBasis ι ℝ (TangentSpace I p)) (q : M) (a : TangentSpace I p) :
    b.normalFrameExpansion (U := U) q a =
      ∑ i, ⟪b i, a⟫_ℝ • normalOrthonormalFrame I M p U b i q := by rfl

/-- Frame reconstruction sends zero to zero. -/
@[simp]
theorem _root_.OrthonormalBasis.normalFrameExpansion_zero
    (b : OrthonormalBasis ι ℝ (TangentSpace I p)) (q : M) :
    b.normalFrameExpansion (U := U) q 0 = 0 := by
  simp [OrthonormalBasis.normalFrameExpansion_apply]

/-- Frame reconstruction is additive. -/
@[simp]
theorem _root_.OrthonormalBasis.normalFrameExpansion_add
    (b : OrthonormalBasis ι ℝ (TangentSpace I p)) (q : M) (a a' : TangentSpace I p) :
    b.normalFrameExpansion (U := U) q (a + a') =
      b.normalFrameExpansion (U := U) q a + b.normalFrameExpansion (U := U) q a' := by
  simp [OrthonormalBasis.normalFrameExpansion_apply, inner_add_right, add_smul,
    Finset.sum_add_distrib]

/-- Frame reconstruction commutes with scalar multiplication. -/
@[simp]
theorem _root_.OrthonormalBasis.normalFrameExpansion_smul
    (b : OrthonormalBasis ι ℝ (TangentSpace I p)) (q : M) (c : ℝ) (a : TangentSpace I p) :
    b.normalFrameExpansion (U := U) q (c • a) = c • b.normalFrameExpansion (U := U) q a := by
  simp [OrthonormalBasis.normalFrameExpansion_apply, real_inner_smul_right, mul_smul,
    Finset.smul_sum]

namespace IsNormalDomain

/-- The normal orthonormal frame is orthonormal at every point of the normal neighbourhood. -/
theorem orthonormal_normalOrthonormalFrame (h : IsNormalDomain I M p U)
    (b : OrthonormalBasis ι ℝ (TangentSpace I p)) {q : M}
    (hq : q ∈ riemannianExp I M p '' U) :
    Orthonormal ℝ (fun i ↦ normalOrthonormalFrame I M p U b i q) := by
  simp only [normalOrthonormalFrame_def]
  exact gramSchmidtNormed_orthonormal
    (h.linearIndependent_normalCoordinateField b.orthonormal.linearIndependent hq)

/-- Each normal orthonormal frame section is smooth on the normal neighbourhood. -/
theorem contMDiffOn_normalOrthonormalFrame (h : IsNormalDomain I M p U)
    (b : OrthonormalBasis ι ℝ (TangentSpace I p)) (i : ι) :
    CMDiff[riemannianExp I M p '' U] ∞ (T% (normalOrthonormalFrame I M p U b i)) := by
  have heq : normalOrthonormalFrame I M p U b i =
      fun q ↦ gramSchmidtNormed ℝ (fun j ↦ normalCoordinateField I M p U (b j) q) i :=
    funext (normalOrthonormalFrame_def b i)
  rw [heq]
  intro q hq
  let v : ι → Π q : M, TangentSpace I q := fun j ↦ normalCoordinateField I M p U (b j)
  have hv (j : ι) : CMDiffAt ∞ (T% (v j)) q :=
    (h.contMDiffOn_normalCoordinateField (b j)).contMDiffAt (h.isOpen_image.mem_nhds hq)
  have hi : LinearIndependent ℝ (fun j ↦ v j q) :=
    h.linearIndependent_normalCoordinateField b.orthonormal.linearIndependent hq
  apply ContMDiffAt.contMDiffWithinAt
  apply ContMDiffAt.gramSchmidtNormed_bundle (I := I) (F := E) (v := v) (j := i)
  · exact hv
  · exact hi

/-- Normal orthonormal frame sections form a smooth local frame in Mathlib's sense. -/
theorem isLocalFrameOn_normalOrthonormalFrame (h : IsNormalDomain I M p U)
    (b : OrthonormalBasis ι ℝ (TangentSpace I p)) :
    IsLocalFrameOn I E ∞ (normalOrthonormalFrame I M p U b) (riemannianExp I M p '' U) where
  linearIndependent hq := (h.orthonormal_normalOrthonormalFrame b hq).linearIndependent
  generating {x} hq := by
    have hli := (h.orthonormal_normalOrthonormalFrame b hq).linearIndependent
    apply (hli.span_eq_top_of_card_eq_finrank' ?_).ge
    rw [← Module.finrank_eq_card_basis b.toBasis]
    exact (TauCeti.finrank_tangentSpace (I := I) p).trans
      (TauCeti.finrank_tangentSpace (I := I) x).symm
  contMDiffOn := h.contMDiffOn_normalOrthonormalFrame b

/-- The moving-frame components of a reconstructed vector are its original components. -/
@[simp]
theorem inner_normalFrameExpansion (h : IsNormalDomain I M p U)
    (b : OrthonormalBasis ι ℝ (TangentSpace I p)) {q : M}
    (hq : q ∈ riemannianExp I M p '' U) (a : TangentSpace I p) (k : ι) :
    ⟪normalOrthonormalFrame I M p U b k q, b.normalFrameExpansion (U := U) q a⟫_ℝ =
      ⟪b k, a⟫_ℝ := by
  simp [OrthonormalBasis.normalFrameExpansion_apply, inner_sum, real_inner_smul_right,
    orthonormal_iff_ite.mp (h.orthonormal_normalOrthonormalFrame b hq)]

/-- Reconstruction in a normal orthonormal frame preserves inner products. -/
@[simp]
theorem inner_normalFrameExpansion_pair (h : IsNormalDomain I M p U)
    (b : OrthonormalBasis ι ℝ (TangentSpace I p)) {q : M}
    (hq : q ∈ riemannianExp I M p '' U) (a a' : TangentSpace I p) :
    ⟪b.normalFrameExpansion (U := U) q a, b.normalFrameExpansion (U := U) q a'⟫_ℝ =
      ⟪a, a'⟫_ℝ := by
  rw [b.normalFrameExpansion_apply q a, sum_inner]
  simp only [real_inner_smul_left, h.inner_normalFrameExpansion b hq]
  simpa only [real_inner_comm a] using b.sum_inner_mul_inner a a'

variable [I.Boundaryless] [T2Space M]

/-- At its centre, the normal orthonormal frame recovers the prescribed orthonormal basis. -/
@[simp]
theorem normalOrthonormalFrame_self (h : IsNormalDomain I M p U)
    (b : OrthonormalBasis ι ℝ (TangentSpace I p)) (i : ι) :
    normalOrthonormalFrame I M p U b i p = b i := by
  simp only [normalOrthonormalFrame_def, h.normalCoordinateField_self,
    gramSchmidtNormed, gramSchmidt_of_orthogonal ℝ b.orthonormal.2,
    b.orthonormal.1 i, RCLike.ofReal_real_eq_id, id_eq, inv_one, one_smul]

/-- The normal orthonormal frame is parallel at its centre in every tangent direction. -/
@[simp]
theorem leviCivitaConnection_normalOrthonormalFrame_self (h : IsNormalDomain I M p U)
    (b : OrthonormalBasis ι ℝ (TangentSpace I p)) (i : ι) :
    leviCivitaConnection I M (normalOrthonormalFrame I M p U b i) p = 0 := by
  exact (isMetricCompatible_leviCivitaConnection I).apply_gramSchmidtNormed_eq_zero
    (fun j ↦ h.mdifferentiableAt_normalCoordinateField (b j) h.self_mem_image)
    (h.linearIndependent_normalCoordinateField b.orthonormal.linearIndependent h.self_mem_image)
    (fun j ↦ h.leviCivitaConnection_normalCoordinateField_self (b j)) i

/-- At the centre, frame reconstruction is the identity. -/
@[simp]
theorem normalFrameExpansion_self (h : IsNormalDomain I M p U)
    (b : OrthonormalBasis ι ℝ (TangentSpace I p)) (a : TangentSpace I p) :
    b.normalFrameExpansion (U := U) p a = a := by
  simp [OrthonormalBasis.normalFrameExpansion_apply, h.normalOrthonormalFrame_self, b.sum_repr']

end IsNormalDomain

end TauCeti.Manifold
