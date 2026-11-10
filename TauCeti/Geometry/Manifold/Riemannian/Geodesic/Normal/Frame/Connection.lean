/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Geodesic.Normal.Frame.Basic
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.LeviCivita.Regularity
public import Mathlib.Analysis.InnerProductSpace.LinearMap
public import TauCeti.Geometry.Manifold.MFDeriv.NormedSpace
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.ConnectionForm
import TauCeti.Geometry.Manifold.VectorBundle.LocalFrame.Orthonormal

/-!
# Connection operators in normal orthonormal frames

The Levi-Civita derivative of a normal orthonormal frame in a fixed normal-coordinate
vector field gives a smooth family of real connection coefficients. Their finite-rank
operator on the initial tangent space encodes the coefficient equation for parallel
transport along radial geodesics. Both the coefficients and the operator vanish at the
centre of the normal neighbourhood. On the normal neighbourhood the coefficients are the
connection one-forms `IsLocalFrameOn.connectionForm` of the normal orthonormal frame,
evaluated on the normal-coordinate field
(`IsNormalDomain.normalFrameConnectionCoefficient_eq_connectionForm`).
-/

public noncomputable section

open Bundle CovariantDerivative Filter Set
open scoped ContDiff InnerProductSpace Manifold Topology

section

open TauCeti.Manifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
  {ι : Type*} [Fintype ι] [LinearOrder ι] [LocallyFiniteOrderBot ι]
  {p : M} {U : Set (TangentSpace I p)}

namespace OrthonormalBasis

/-- The connection coefficient of a normal orthonormal frame in a normal-coordinate direction. -/
def normalFrameConnectionCoefficient (b : OrthonormalBasis ι ℝ (TangentSpace I p))
    (v : TangentSpace I p) (i j : ι) (q : M) : ℝ :=
  ⟪leviCivitaConnection I M (normalOrthonormalFrame I M p U b j) q
    (normalCoordinateField I M p U v q), normalOrthonormalFrame I M p U b i q⟫_ℝ

/-- Connection coefficients are the inner products of the covariant frame derivatives. -/
theorem normalFrameConnectionCoefficient_apply (b : OrthonormalBasis ι ℝ (TangentSpace I p))
    (v : TangentSpace I p) (i j : ι) (q : M) :
    normalFrameConnectionCoefficient (I := I) (U := U) b v i j q =
      ⟪leviCivitaConnection I M (normalOrthonormalFrame I M p U b j) q
        (normalCoordinateField I M p U v q), normalOrthonormalFrame I M p U b i q⟫_ℝ := by rfl

/-- Connection coefficients are additive in the normal-coordinate direction. -/
theorem normalFrameConnectionCoefficient_add (b : OrthonormalBasis ι ℝ (TangentSpace I p))
    (v w : TangentSpace I p) (i j : ι) (q : M) :
    normalFrameConnectionCoefficient (I := I) (U := U) b (v + w) i j q =
      normalFrameConnectionCoefficient (U := U) b v i j q +
        normalFrameConnectionCoefficient (U := U) b w i j q := by
  simp only [normalFrameConnectionCoefficient_apply, normalCoordinateField_add, Pi.add_apply,
    map_add, inner_add_left]

/-- Connection coefficients are homogeneous in the normal-coordinate direction. -/
theorem normalFrameConnectionCoefficient_smul (b : OrthonormalBasis ι ℝ (TangentSpace I p))
    (c : ℝ) (v : TangentSpace I p) (i j : ι) (q : M) :
    normalFrameConnectionCoefficient (I := I) (U := U) b (c • v) i j q =
      c * normalFrameConnectionCoefficient (U := U) b v i j q := by
  simp only [normalFrameConnectionCoefficient_apply, normalCoordinateField_smul, Pi.smul_apply,
    map_smul, real_inner_smul_left]

/-- Connection coefficients vanish in the zero direction. -/
@[simp]
theorem normalFrameConnectionCoefficient_zero (b : OrthonormalBasis ι ℝ (TangentSpace I p))
    (i j : ι) (q : M) :
    normalFrameConnectionCoefficient (I := I) (U := U) b 0 i j q = 0 := by
  simpa using normalFrameConnectionCoefficient_smul (U := U) b 0 0 i j q

/-- The normal-frame connection matrix, represented as an operator on the initial tangent space. -/
def normalFrameConnectionOperator (b : OrthonormalBasis ι ℝ (TangentSpace I p))
    (v : TangentSpace I p) (q : M) : TangentSpace I p →L[ℝ] TangentSpace I p :=
  ∑ i, ∑ j, normalFrameConnectionCoefficient (I := I) (U := U) b v i j q •
    InnerProductSpace.rankOne ℝ (b i) (b j)

/-- The connection operator is the finite-rank sum of its geometric frame coefficients. -/
theorem normalFrameConnectionOperator_apply (b : OrthonormalBasis ι ℝ (TangentSpace I p))
    (v : TangentSpace I p) (q : M) :
    normalFrameConnectionOperator (U := U) b v q =
      ∑ i, ∑ j, normalFrameConnectionCoefficient (I := I) (U := U) b v i j q •
        InnerProductSpace.rankOne ℝ (b i) (b j) := by rfl

/-- The connection operator is additive in the normal-coordinate direction. -/
theorem normalFrameConnectionOperator_add (b : OrthonormalBasis ι ℝ (TangentSpace I p))
    (v w : TangentSpace I p) (q : M) :
    normalFrameConnectionOperator (U := U) b (v + w) q =
      normalFrameConnectionOperator (U := U) b v q +
        normalFrameConnectionOperator (U := U) b w q := by
  simp only [normalFrameConnectionOperator_apply, normalFrameConnectionCoefficient_add, add_smul,
    Finset.sum_add_distrib]

/-- The connection operator is homogeneous in the normal-coordinate direction. -/
theorem normalFrameConnectionOperator_smul (b : OrthonormalBasis ι ℝ (TangentSpace I p))
    (c : ℝ) (v : TangentSpace I p) (q : M) :
    normalFrameConnectionOperator (U := U) b (c • v) q =
      c • normalFrameConnectionOperator (U := U) b v q := by
  simp only [normalFrameConnectionOperator_apply, normalFrameConnectionCoefficient_smul, mul_smul,
    Finset.smul_sum]

/-- The connection operator vanishes in the zero direction. -/
@[simp]
theorem normalFrameConnectionOperator_zero (b : OrthonormalBasis ι ℝ (TangentSpace I p))
    (q : M) : normalFrameConnectionOperator (U := U) b 0 q = 0 := by
  simp [normalFrameConnectionOperator_apply]

/-- The components of the connection operator recover the connection matrix acting on components. -/
theorem inner_normalFrameConnectionOperator (b : OrthonormalBasis ι ℝ (TangentSpace I p))
    (v : TangentSpace I p) (q : M) (k : ι) (a : TangentSpace I p) :
    ⟪b k, normalFrameConnectionOperator (U := U) b v q a⟫_ℝ =
      ∑ j, normalFrameConnectionCoefficient (U := U) b v k j q * ⟪b j, a⟫_ℝ := by
  simp [normalFrameConnectionOperator_apply, inner_sum, real_inner_smul_right,
    orthonormal_iff_ite.mp b.orthonormal]

end OrthonormalBasis

namespace TauCeti.Manifold

variable [I.Boundaryless] [T2Space M]

namespace IsNormalDomain

omit [I.Boundaryless] [T2Space M] in
/-- Normal-frame connection coefficients are smooth throughout a normal neighbourhood. -/
theorem contMDiffOn_normalFrameConnectionCoefficient (h : IsNormalDomain I M p U)
    (b : OrthonormalBasis ι ℝ (TangentSpace I p)) (v : TangentSpace I p) (i j : ι) :
    ContMDiffOn I 𝓘(ℝ) ∞ (b.normalFrameConnectionCoefficient (U := U) v i j)
      (riemannianExp I M p '' U) := by
  have : IsManifold I (∞ + 1) M := by simpa using (inferInstance : IsManifold I ∞ M)
  have hcov := contMDiffOn_leviCivitaConnection (I := I) (n := ∞) (m := ∞) (k := ∞)
    h.isOpen_image (by simp) (by simp) (by simpa using h.contMDiffOn_normalOrthonormalFrame b j)
  have hfield := hcov.clm_bundle_apply (h.contMDiffOn_normalCoordinateField v)
  exact ContMDiffOn.inner_bundle (IB := I) (F := E)
    (E := fun x : M ↦ TangentSpace I x) (b := id) hfield
    (h.contMDiffOn_normalOrthonormalFrame b i)

/-- Normal-frame connection coefficients vanish at the centre. -/
@[simp]
theorem normalFrameConnectionCoefficient_self (h : IsNormalDomain I M p U)
    (b : OrthonormalBasis ι ℝ (TangentSpace I p)) (v : TangentSpace I p) (i j : ι) :
    b.normalFrameConnectionCoefficient (U := U) v i j p = 0 := by
  rw [OrthonormalBasis.normalFrameConnectionCoefficient_apply,
    h.leviCivitaConnection_normalOrthonormalFrame_self b j, zero_apply, inner_zero_left]

omit [I.Boundaryless] [T2Space M] in
/-- The connection operator is smooth on the normal neighbourhood. -/
theorem contMDiffOn_normalFrameConnectionOperator (h : IsNormalDomain I M p U)
    (b : OrthonormalBasis ι ℝ (TangentSpace I p)) (v : TangentSpace I p) :
    ContMDiffOn I 𝓘(ℝ, TangentSpace I p →L[ℝ] TangentSpace I p) ∞
      (b.normalFrameConnectionOperator (U := U) v) (riemannianExp I M p '' U) := by
  rw [funext (b.normalFrameConnectionOperator_apply (U := U) v)]
  exact contMDiffOn_finsetSum fun i _ ↦ contMDiffOn_finsetSum fun j _ ↦
    (h.contMDiffOn_normalFrameConnectionCoefficient b v i j).smul contMDiffOn_const

/-- Along a radial geodesic, the normal-frame connection operator has smooth coefficients. -/
theorem contDiffOn_normalFrameConnectionOperator_radial (h : IsNormalDomain I M p U)
    (b : OrthonormalBasis ι ℝ (TangentSpace I p)) (v : TangentSpace I p) :
    ContDiffOn ℝ ∞
      (fun t : ℝ ↦ b.normalFrameConnectionOperator (U := U) v (riemannianExp I M p (t • v)))
      {t | t • v ∈ U} := by
  rw [← contMDiffOn_iff_contDiffOn]
  have hlin : ContMDiff 𝓘(ℝ) 𝓘(ℝ, TangentSpace I p) ∞ (fun t : ℝ ↦ t • v) :=
    (contDiff_id.smul contDiff_const).contMDiff
  exact (h.contMDiffOn_normalFrameConnectionOperator b v).comp
    ((contMDiffOn_riemannianExp p).comp hlin.contMDiffOn
      (fun t ht ↦ h.subset_expDomain ht)) (fun t ht ↦ mem_image_of_mem _ ht)

/-- The normal-frame connection operator vanishes at the centre. -/
@[simp]
theorem normalFrameConnectionOperator_self (h : IsNormalDomain I M p U)
    (b : OrthonormalBasis ι ℝ (TangentSpace I p)) (v : TangentSpace I p) :
    b.normalFrameConnectionOperator (U := U) v p = 0 := by
  simp [OrthonormalBasis.normalFrameConnectionOperator_apply, h]

omit [I.Boundaryless] [T2Space M] in
/-- On the normal neighbourhood, the normal-frame connection coefficient is the connection
one-form of the normal orthonormal frame, with input index `j` and output index `i`, evaluated on
the normal-coordinate field. -/
theorem normalFrameConnectionCoefficient_eq_connectionForm (h : IsNormalDomain I M p U)
    (b : OrthonormalBasis ι ℝ (TangentSpace I p))
    (hs : IsLocalFrameOn I E 2 (normalOrthonormalFrame I M p U b) (riemannianExp I M p '' U))
    (v : TangentSpace I p) (i j : ι) {q : M} (hq : q ∈ riemannianExp I M p '' U) :
    b.normalFrameConnectionCoefficient (U := U) v i j q =
      hs.connectionForm (leviCivitaConnection I M) j i q ![normalCoordinateField I M p U v q] := by
  rw [IsLocalFrameOn.connectionForm_apply,
    hs.coeff_eq_inner hq (h.orthonormal_normalOrthonormalFrame b hq),
    OrthonormalBasis.normalFrameConnectionCoefficient_apply, real_inner_comm]
  rfl

omit [I.Boundaryless] [T2Space M] in
/-- The connection matrix of an orthonormal frame is skew-symmetric. -/
theorem normalFrameConnectionCoefficient_add_swap (h : IsNormalDomain I M p U)
    (b : OrthonormalBasis ι ℝ (TangentSpace I p)) (v : TangentSpace I p) (i j : ι) {q : M}
    (hq : q ∈ riemannianExp I M p '' U) :
    b.normalFrameConnectionCoefficient (U := U) v i j q +
      b.normalFrameConnectionCoefficient (U := U) v j i q = 0 := by
  have hd (k : ι) : MDiffAt (T% (normalOrthonormalFrame I M p U b k)) q :=
    ((h.contMDiffOn_normalOrthonormalFrame b k).contMDiffAt
      (h.isOpen_image.mem_nhds hq)).mdifferentiableAt (by simp)
  have heq : (fun x ↦ ⟪normalOrthonormalFrame I M p U b j x,
      normalOrthonormalFrame I M p U b i x⟫_ℝ) =ᶠ[𝓝 q] fun _ ↦ if j = i then 1 else 0 := by
    filter_upwards [h.isOpen_image.mem_nhds hq] with x hx
    exact orthonormal_iff_ite.mp (h.orthonormal_normalOrthonormalFrame b hx) j i
  have hmetric := (isMetricCompatible_leviCivitaConnection I).mvfderiv_inner_eq
    (normalCoordinateField I M p U v) (hd j) (hd i)
  rw [heq.mvfderiv_eq, mvfderiv_const, zero_apply] at hmetric
  simpa only [OrthonormalBasis.normalFrameConnectionCoefficient_apply, real_inner_comm] using
    hmetric.symm

end IsNormalDomain

end TauCeti.Manifold

end
