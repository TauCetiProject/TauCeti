/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Dirac.DifferentialOperator
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Dirac.Split.Basic
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Dirac.Square
import TauCeti.Geometry.Manifold.Riemannian.Basic
import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Regularity
import TauCeti.LinearAlgebra.CliffordAlgebra.OrthonormalBasis

/-!
# The energy identity of the Dirac operator split along a parallel unit field

Let `V` be a Riemannian vector bundle over a Riemannian manifold `M` without boundary, with a
metric connection `∇` and a smooth Clifford multiplication `c` by skew-adjoint endomorphisms,
satisfying the Clifford relation `c(v)² = -‖v‖²` and compatible with `∇` and the Levi-Civita
connection. Along a unit vector field `T` the Dirac operator splits as `D = c(T) ∇_T + B_T`
(`CovariantDerivative.diracOperator_eq_add_transverseDiracOperator`), where the transverse Dirac
operator `B_T` (`CovariantDerivative.transverseDiracOperator`) differentiates only orthogonally to
`T`. This file integrates the square of this splitting.

* For a Killing field `T` of constant length, `B_T` is formally self-adjoint for the Riemannian
  volume: `∫ ⟪B_T σ, τ⟫ dV = ∫ ⟪σ, B_T τ⟫ dV` whenever `σ` or `τ` has compact support
  (`CovariantDerivative.IsMetricCompatible.integral_inner_transverseDiracOperator_left_eq_right`).
  It is the difference of the formally self-adjoint operators `D` and `c(T) ∇_T`. Consequently
  `∫ ⟪B_T² σ, σ⟫ dV = ∫ ‖B_T σ‖² dV` for compactly supported `σ`.
* For a parallel unit field `T`, such as the coordinate field `∂ₛ` of a product `S¹ × Y` with the
  product metric, every compactly supported smooth section `σ` satisfies

  `∫ ‖D σ‖² dV = ∫ ‖∇_T σ‖² dV + ∫ ‖B_T σ‖² dV + ∫ ⟪c(T) (∇_T B_T σ - B_T ∇_T σ), σ⟫ dV`

  (`CovariantDerivative.IsMetricCompatible.integral_norm_sq_diracOperator_eq`). This integrates
  the pointwise square `D² = -∇_T² + B_T² + c(T) [∇_T, B_T]`
  (`CovariantDerivative.diracOperator_diracOperator_eq`): `D` and `B_T` are formally self-adjoint
  and `∇_T` is formally skew-adjoint.
* If moreover vector fields `e₁, …, eₖ` complete `T` to an orthonormal frame at every point and
  commute with `T`, as fields lifted from an orthonormal frame of `Y` do on `S¹ × Y`, the
  commutator is the curvature term `∑ᵢ c(eᵢ) R(T, eᵢ)` and

  `∫ ‖D σ‖² dV = ∫ ‖∇_T σ‖² dV + ∫ ‖B_T σ‖² dV + ∫ ⟪c(T) ∑ᵢ c(eᵢ) R(T, eᵢ) σ, σ⟫ dV`

  (`IsMetricCompatible.integral_norm_sq_diracOperator_eq_sum_curvatureOperator`, in the namespace
  `CovariantDerivative`).

For a solution `D_A ψ = 0` of the unperturbed Seiberg–Witten equations on `S¹ × Y`, the left side
vanishes. For the spin connection of a unitary connection `A` on the determinant line the curvature
term is `(1 / 2) c₂(ds ∧ ι_T F_A)`, whose pairing with `ψ` is computed in
`TauCeti.SeibergWitten.re_inner_I_div_two_smul_ι_mul_ι_twoVectorContraction`; this gives the energy
identity `0 = ‖∇_T ψ‖² + ‖B_A ψ‖² + ‖ι_T F_A‖² + 2π² ⟨c₁(L)², [S¹ × Y]⟩`. Neither the
identification of the spin curvature nor that topological pairing is made here.

## Main results

* `CovariantDerivative.contMDiff_transverseDiracOperator`: `B_T` maps smooth sections to smooth
  sections.
* `CovariantDerivative.IsMetricCompatible.integral_inner_transverseDiracOperator_left_eq_right`:
  `B_T` is formally self-adjoint along a Killing field of constant length.
* `IsMetricCompatible.integral_inner_transverseDiracOperator_transverseDiracOperator_self`, in
  the namespace `CovariantDerivative`: `∫ ⟪B_T² σ, σ⟫ dV = ∫ ‖B_T σ‖² dV`.
* `CovariantDerivative.IsMetricCompatible.integral_norm_sq_diracOperator_eq`: the integrated split
  square along a parallel unit field.
* `IsMetricCompatible.integral_norm_sq_diracOperator_eq_sum_curvatureOperator`, in the namespace
  `CovariantDerivative`: its curvature form in a frame commuting with `T`.

## References

* H. B. Lawson and M.-L. Michelsohn, *Spin Geometry*, Princeton University Press, 1989,
  Chapter II, §5 and §8 (Dirac operators of Clifford bundles, their squares and their formal
  self-adjointness).
* J. W. Morgan, *The Seiberg–Witten equations and applications to the topology of smooth
  four-manifolds*, Mathematical Notes 44, Princeton University Press, 1996, §5.2.
* S. Baldridge, *Seiberg–Witten invariants, orbifolds, and circle actions*, Trans. Amer. Math.
  Soc. 355 (2003), 1669–1697, Theorem 15.
-/

public section

noncomputable section

open MeasureTheory Bundle Filter Set TauCeti TauCeti.Manifold
open scoped ContDiff Manifold RealInnerProductSpace Topology

namespace CovariantDerivative

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, NormedAddCommGroup (V x)] [∀ x, InnerProductSpace ℝ (V x)]
  [FiberBundle F V] [VectorBundle ℝ F V]
  {cov : _root_.CovariantDerivative I F V}
  {c : Π x : M, TangentSpace I x →L[ℝ] V x →L[ℝ] V x}

variable [IsManifold I ∞ M]
  (hc : ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] F →L[ℝ] F)) ∞
    (fun x ↦ TotalSpace.mk' (E →L[ℝ] F →L[ℝ] F)
      (E := fun y ↦ TangentSpace I y →L[ℝ] V y →L[ℝ] V y) x (c x)))

variable [FiniteDimensional ℝ E] [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
  [ContMDiffCovariantDerivative cov ∞]

variable (cov) in
include hc in
/-- **The transverse Dirac operator is smooth.** For a smooth connection, a smooth Clifford
multiplication and a smooth vector field `T`, the transverse Dirac operator `B_T σ` of a smooth
section `σ` is smooth. -/
theorem contMDiff_transverseDiracOperator {T : Π y : M, TangentSpace I y} (hT : CMDiff ∞ (T% T))
    {σ : Π y : M, V y} (hσ : CMDiff ∞ (T% σ)) :
    CMDiff ∞ (T% (cov.transverseDiracOperator c T σ)) := by
  have h : cov.transverseDiracOperator c T σ =
      cov.diracOperator c σ - fun y ↦ c y (T y) (cov σ y (T y)) :=
    funext fun y ↦ transverseDiracOperator_def cov c T σ y
  rw [h]
  exact (cov.contMDiff_diracOperator hc hσ).sub_section
    (contMDiff_clifford_apply hc hT (cov.contMDiff_apply hT (by simpa using hσ)))

variable [IsContMDiffRiemannianBundle I ∞ F V] [SigmaCompactSpace M] [MeasurableSpace M]
  [BorelSpace M]

local instance : IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x) :=
  IsContMDiffRiemannianBundle.toIsContinuousRiemannianBundle
    (IB := I) (n := ∞) (F := E) (V := fun x : M ↦ TangentSpace I x)

variable [T2Space M] [FiniteDimensional ℝ F] [ContMDiffVectorBundle ∞ F V I] [I.Boundaryless]
  (hskew : ∀ x (v : TangentSpace I x) (s t : V x), ⟪c x v s, t⟫ = -⟪s, c x v t⟫)
  (hcomp : ∀ (Y : Π y : M, TangentSpace I y) (τ : Π y : M, V y), CMDiff ∞ (T% Y) →
    CMDiff ∞ (T% τ) → ∀ x u, cov (fun y ↦ c y (Y y) (τ y)) x u =
      c x (leviCivitaConnection I M Y x u) (τ x) + c x (Y x) (cov τ x u))

omit [T2Space M] [FiniteDimensional ℝ F] [ContMDiffVectorBundle ∞ F V I]
  [IsContMDiffRiemannianBundle I ∞ F V] [SigmaCompactSpace M] [MeasurableSpace M] [BorelSpace M]
  [I.Boundaryless] in
include hc hcomp in
/-- The pointwise square `D² σ = -∇_T² σ + B_T² σ + c(T) [∇_T, B_T] σ` of the Dirac operator split
along a parallel unit field `T`, for a Clifford multiplication satisfying the Clifford relation and
compatible with `∇` and the Levi-Civita connection. -/
private theorem diracOperator_diracOperator_eq_of_forall_eq_zero
    (hcl : ∀ x (v : TangentSpace I x) (s : V x), c x v (c x v s) = -⟪v, v⟫ • s)
    {T : Π y : M, TangentSpace I y} (hT : CMDiff ∞ (T% T))
    (hTpar : ∀ x, leviCivitaConnection I M T x = 0) (hT1 : ∀ x, ‖T x‖ = 1)
    {σ : Π y : M, V y} (hσ : CMDiff ∞ (T% σ)) (x : M) :
    cov.diracOperator c (cov.diracOperator c σ) x =
      -cov (fun y ↦ cov σ y (T y)) x (T x) +
        cov.transverseDiracOperator c T (cov.transverseDiracOperator c T σ) x +
          c x (T x) (cov (cov.transverseDiracOperator c T σ) x (T x) -
            cov.transverseDiracOperator c T (fun y ↦ cov σ y (T y)) x) := by
  have hN : CMDiff ∞ (T% (fun y ↦ cov σ y (T y))) := cov.contMDiff_apply hT (by simpa using hσ)
  refine cov.diracOperator_diracOperator_eq c T (hT1 x) (fun u w ↦ ?_)
    (ContinuousLinearMap.ext fun u ↦ ?_)
    ((contMDiff_clifford_apply hc hT hN).mdifferentiableAt (by simp))
    ((cov.contMDiff_transverseDiracOperator hc hT hσ).mdifferentiableAt (by simp))
  · simpa using LinearMap.apply_apply_add_swap_eq_neg_two_inner
      ((ContinuousLinearMap.coeLM ℝ).comp (c x).toLinearMap) (by simpa using hcl x) u (T x) w
  · rw [ContinuousLinearMap.comp_apply, hcomp T _ hT hN x u, hTpar x]
    simp

namespace IsMetricCompatible

include hc hskew hcomp

/-- **The transverse Dirac operator is formally self-adjoint.** Let `∇` be a metric connection on
a Riemannian vector bundle over a Riemannian manifold without boundary, and let the Clifford
multiplication `c` be smooth, skew-adjoint and compatible with `∇` and the Levi-Civita connection.
For a Killing field `T` of constant length, such as the unit field `∂ₛ` on a product `S¹ × Y`, and
smooth sections `σ`, `τ` one of which has compact support,

`∫ ⟪B_T σ, τ⟫ dV = ∫ ⟪σ, B_T τ⟫ dV`

for the Riemannian volume `dV`. -/
theorem integral_inner_transverseDiracOperator_left_eq_right (hcov : cov.IsMetricCompatible)
    {T : Π y : M, TangentSpace I y} (hT : IsKillingField I T) {r : ℝ} (hTr : ∀ x, ‖T x‖ = r)
    {σ τ : Π y : M, V y} (hσ : CMDiff ∞ (T% σ)) (hτ : CMDiff ∞ (T% τ))
    (hστ : IsCompact (closure {x | σ x ≠ 0}) ∨ IsCompact (closure {x | τ x ≠ 0})) :
    ∫ x, ⟪cov.transverseDiracOperator c T σ x, τ x⟫ ∂riemannianVolume I M =
      ∫ x, ⟪σ x, cov.transverseDiracOperator c T τ x⟫ ∂riemannianVolume I M := by
  have := IsContMDiffRiemannianBundle.toIsContinuousRiemannianBundle (IB := I) (n := ∞) (F := F)
    (V := V)
  have hTs := hT.contMDiff
  let Tₛ : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ := ⟨T, hTs⟩
  -- Clifford multiplication by `T`, as an operator on the smooth sections.
  let A : Cₛ^∞⟮I; F, V⟯ →ₗ[ℝ] Cₛ^∞⟮I; F, V⟯ :=
    { toFun s := ⟨fun y ↦ c y (T y) (s y), contMDiff_clifford_apply hc hTs s.contMDiff⟩
      map_add' s t := ContMDiffSection.ext fun y ↦ by simp
      map_smul' a s := ContMDiffSection.ext fun y ↦ by simp }
  have hA (s : Cₛ^∞⟮I; F, V⟯) (y : M) : A s y = c y (T y) (s y) := (rfl)
  have hTₛ (y : M) : Tₛ y = T y := (rfl)
  -- `c(T) ∇_T = A ∘ ∇_T` and `D` are formally self-adjoint and do not enlarge supports.
  have hC : (A ∘ₗ cov.alongVectorField Tₛ).IsFormalAdjoint (A ∘ₗ cov.alongVectorField Tₛ)
      (riemannianVolume I M) := LinearMap.isFormalAdjoint_iff.2 fun s t hst ↦ by
    simpa only [LinearMap.comp_apply, hA, alongVectorField_apply, hTₛ] using
      hcov.integral_inner_clifford_covariantDerivative_left_eq_right hskew hcomp
        (fun _ _ hY hτ ↦ contMDiff_clifford_apply hc hY hτ) hT hTr s.contMDiff t.contMDiff
        (by simpa only [ContMDiffSection.tsupport_def] using hst)
  have hCs (s : Cₛ^∞⟮I; F, V⟯) : ((A ∘ₗ cov.alongVectorField Tₛ) s).tsupport ⊆ s.tsupport := by
    have h := tsupport_alongVectorField_apply_subset Tₛ cov s
    rw [ContMDiffSection.tsupport_def] at h ⊢
    refine subset_trans (closure_mono ?_) h
    intro x hx h0
    exact hx (by simp [hA, h0])
  have hDs := tsupport_differentialOperators_section_apply_subset
    (cov.smoothDiracOperator_mem_differentialOperators_one hc)
  have h := ((hcov.isFormalAdjoint_smoothDiracOperator hc hskew hcomp).sub hC hDs hCs hDs
    hCs).integral_inner_eq (s := ⟨σ, hσ⟩) (t := ⟨τ, hτ⟩)
    (by simpa only [ContMDiffSection.tsupport_def, ContMDiffSection.coeFn_mk] using hστ)
  simpa only [LinearMap.sub_apply, LinearMap.comp_apply, ContMDiffSection.coe_sub, Pi.sub_apply,
    smoothDiracOperator_apply, hA, alongVectorField_apply, hTₛ, ContMDiffSection.coeFn_mk,
    transverseDiracOperator_def] using h

/-- **The energy identity of the transverse Dirac operator.** Under the hypotheses of
`CovariantDerivative.IsMetricCompatible.integral_inner_transverseDiracOperator_left_eq_right`, for
a compactly supported smooth section `σ`, `∫ ⟪B_T² σ, σ⟫ dV = ∫ ‖B_T σ‖² dV`. -/
theorem integral_inner_transverseDiracOperator_transverseDiracOperator_self
    (hcov : cov.IsMetricCompatible) {T : Π y : M, TangentSpace I y} (hT : IsKillingField I T)
    {r : ℝ} (hTr : ∀ x, ‖T x‖ = r) {σ : Π y : M, V y} (hσ : CMDiff ∞ (T% σ))
    (hσc : IsCompact (closure {x | σ x ≠ 0})) :
    ∫ x, ⟪cov.transverseDiracOperator c T (cov.transverseDiracOperator c T σ) x, σ x⟫
        ∂riemannianVolume I M =
      ∫ x, ‖cov.transverseDiracOperator c T σ x‖ ^ 2 ∂riemannianVolume I M := by
  rw [hcov.integral_inner_transverseDiracOperator_left_eq_right hc hskew hcomp hT hTr
    (cov.contMDiff_transverseDiracOperator hc hT.contMDiff hσ) hσ (.inr hσc)]
  simp only [real_inner_self_eq_norm_sq]

variable (hcl : ∀ x (v : TangentSpace I x) (s : V x), c x v (c x v s) = -⟪v, v⟫ • s)

include hcl

/-- **The integrated square of the Dirac operator split along a parallel unit field.** Let `∇` be
a metric connection on a Riemannian vector bundle over a Riemannian manifold without boundary, and
let the Clifford multiplication `c` be smooth, skew-adjoint, satisfy the Clifford relation
`c(v)² = -‖v‖²` and be compatible with `∇` and the Levi-Civita connection. For a smooth unit
vector field `T` which is parallel for the Levi-Civita connection, such as `∂ₛ` on a product
`S¹ × Y` with the product metric, and a compactly supported smooth section `σ`,

`∫ ‖D σ‖² dV = ∫ ‖∇_T σ‖² dV + ∫ ‖B_T σ‖² dV + ∫ ⟪c(T) (∇_T B_T σ - B_T ∇_T σ), σ⟫ dV`

for the Riemannian volume `dV`, where `B_T = D - c(T) ∇_T` is the transverse Dirac operator. -/
theorem integral_norm_sq_diracOperator_eq (hcov : cov.IsMetricCompatible)
    {T : Π y : M, TangentSpace I y} (hT : CMDiff ∞ (T% T))
    (hTpar : ∀ x, leviCivitaConnection I M T x = 0) (hT1 : ∀ x, ‖T x‖ = 1)
    {σ : Π y : M, V y} (hσ : CMDiff ∞ (T% σ)) (hσc : IsCompact (closure {x | σ x ≠ 0})) :
    ∫ x, ‖cov.diracOperator c σ x‖ ^ 2 ∂riemannianVolume I M =
      ∫ x, ‖cov σ x (T x)‖ ^ 2 ∂riemannianVolume I M +
        ∫ x, ‖cov.transverseDiracOperator c T σ x‖ ^ 2 ∂riemannianVolume I M +
          ∫ x, ⟪c x (T x) (cov (cov.transverseDiracOperator c T σ) x (T x) -
            cov.transverseDiracOperator c T (fun y ↦ cov σ y (T y)) x), σ x⟫
              ∂riemannianVolume I M := by
  have hK : IsKillingField I T :=
    (isMetricCompatible_leviCivitaConnection I).isKillingField_of_forall_eq_zero
      (torsion_leviCivitaConnection_eq_zero I) hT hTpar
  have := IsContMDiffRiemannianBundle.toIsContinuousRiemannianBundle (IB := I) (n := ∞) (F := F)
    (V := V)
  -- Write `N = ∇_T σ` and `B = B_T`.
  have hN : CMDiff ∞ (T% (fun y ↦ cov σ y (T y))) := cov.contMDiff_apply hT (by simpa using hσ)
  have hB := cov.contMDiff_transverseDiracOperator hc hT hσ
  -- The three terms of `D² σ`, as smooth sections.
  have hNN : CMDiff ∞ (T% (fun y ↦ cov (fun y ↦ cov σ y (T y)) y (T y))) :=
    cov.contMDiff_apply hT (by simpa using hN)
  have hBB := cov.contMDiff_transverseDiracOperator hc hT hB
  have hcomm : CMDiff ∞ (T% (fun y ↦ c y (T y)
      (cov (cov.transverseDiracOperator c T σ) y (T y) -
        cov.transverseDiracOperator c T (fun y ↦ cov σ y (T y)) y))) :=
    contMDiff_clifford_apply hc hT
      ((cov.contMDiff_apply hT (by simpa using hB)).sub_section
        (cov.contMDiff_transverseDiracOperator hc hT hN))
  have h₁ : Integrable (fun x ↦ ⟪-cov (fun y ↦ cov σ y (T y)) x (T x), σ x⟫)
      (riemannianVolume I M) :=
    ContMDiff.integrable_inner_bundle hNN.neg_section hσ (.inr hσc)
  have h₂ : Integrable
      (fun x ↦ ⟪cov.transverseDiracOperator c T (cov.transverseDiracOperator c T σ) x, σ x⟫)
      (riemannianVolume I M) :=
    ContMDiff.integrable_inner_bundle hBB hσ (.inr hσc)
  have h₃ := ContMDiff.integrable_inner_bundle (μ := riemannianVolume I M) hcomm hσ (.inr hσc)
  have h₁₂ : Integrable (fun x ↦ ⟪-cov (fun y ↦ cov σ y (T y)) x (T x), σ x⟫ +
      ⟪cov.transverseDiracOperator c T (cov.transverseDiracOperator c T σ) x, σ x⟫)
      (riemannianVolume I M) :=
    h₁.add h₂
  -- `-∇_T²` is nonnegative since `T` is divergence-free.
  have hTT : ∫ x, ⟪-cov (fun y ↦ cov σ y (T y)) x (T x), σ x⟫ ∂riemannianVolume I M =
      ∫ x, ‖cov σ x (T x)‖ ^ 2 ∂riemannianVolume I M := by
    let Tₛ : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ := ⟨T, hT⟩
    let σₛ : Cₛ^∞⟮I; F, V⟯ := ⟨σ, hσ⟩
    have hcoe : ⇑(cov.alongVectorField Tₛ σₛ) = fun y ↦ cov σ y (T y) :=
      funext fun y ↦ alongVectorField_apply cov Tₛ σₛ y
    have h := hcov.integral_inner_alongVectorField_alongVectorField Tₛ hK.divergence_eq_zero
      (σ := σₛ) (by rw [ContMDiffSection.tsupport_def]; exact hσc)
    simp only [alongVectorField_apply, hcoe] at h
    simp only [inner_neg_left, integral_neg]
    exact neg_eq_iff_eq_neg.2 h
  rw [← hcov.integral_inner_diracOperator_diracOperator_self hc hskew hcomp hσ hσc]
  simp only [diracOperator_diracOperator_eq_of_forall_eq_zero hc hcomp hcl hT hTpar hT1 hσ,
    inner_add_left]
  rw [integral_add h₁₂ h₃, integral_add h₁ h₂, hTT,
    hcov.integral_inner_transverseDiracOperator_transverseDiracOperator_self hc hskew hcomp hK hT1
      hσ hσc]

/-- **The integrated square of the Dirac operator on a product.** Under the hypotheses of
`CovariantDerivative.IsMetricCompatible.integral_norm_sq_diracOperator_eq`, let `e₁, …, eₖ` be
smooth vector fields which at every point complete `T` to an orthonormal basis and whose brackets
`[T, eᵢ]` vanish, as for fields lifted from an orthonormal frame of `Y` on `S¹ × Y`. Then for a
compactly supported smooth section `σ`,

`∫ ‖D σ‖² dV = ∫ ‖∇_T σ‖² dV + ∫ ‖B_T σ‖² dV + ∫ ⟪c(T) ∑ᵢ c(eᵢ) R(T, eᵢ) σ, σ⟫ dV`,

where `R` is the curvature of `∇`. -/
theorem integral_norm_sq_diracOperator_eq_sum_curvatureOperator (hcov : cov.IsMetricCompatible)
    {T : Π y : M, TangentSpace I y} (hT : CMDiff ∞ (T% T))
    (hTpar : ∀ x, leviCivitaConnection I M T x = 0) (hT1 : ∀ x, ‖T x‖ = 1)
    {ι : Type*} [Fintype ι] (e : ι → Π y : M, TangentSpace I y) (he : ∀ i, CMDiff ∞ (T% (e i)))
    (hframe : ∀ x, ∃ b : OrthonormalBasis (Option ι) ℝ (TangentSpace I x),
      b none = T x ∧ ∀ i, b (some i) = e i x)
    (hbr : ∀ i x, VectorField.mlieBracket I T (e i) x = 0)
    {σ : Π y : M, V y} (hσ : CMDiff ∞ (T% σ)) (hσc : IsCompact (closure {x | σ x ≠ 0})) :
    ∫ x, ‖cov.diracOperator c σ x‖ ^ 2 ∂riemannianVolume I M =
      ∫ x, ‖cov σ x (T x)‖ ^ 2 ∂riemannianVolume I M +
        ∫ x, ‖cov.transverseDiracOperator c T σ x‖ ^ 2 ∂riemannianVolume I M +
          ∫ x, ⟪c x (T x) (∑ i, c x (e i x) (curvatureOperator cov T (e i) σ x)), σ x⟫
            ∂riemannianVolume I M := by
  rw [hcov.integral_norm_sq_diracOperator_eq hc hskew hcomp hcl hT hTpar hT1 hσ hσc]
  congr 1
  refine integral_congr_ae (.of_forall fun x ↦ ?_)
  -- Since `T` is parallel and `[T, eᵢ] = 0`, the torsion-free Levi-Civita connection has
  -- `∇_T eᵢ = ∇_{eᵢ} T + [T, eᵢ] = 0`, so each `c(eᵢ)` is parallel along `T`.
  have hTe (i : ι) : leviCivitaConnection I M (e i) x (T x) = 0 := by
    have h := (leviCivitaConnection I M).torsion_apply (x := x) (hT.mdifferentiableAt (by simp))
      ((he i).mdifferentiableAt (by simp))
    rw [torsion_leviCivitaConnection_eq_zero I, hTpar x, hbr i x] at h
    simpa [eq_comm] using h
  dsimp only
  have hEi (i : ι) : CMDiff ∞ (T% (fun y ↦ cov σ y (e i y))) :=
    cov.contMDiff_apply (he i) (by simpa using hσ)
  rw [cov.covariantDerivative_transverseDiracOperator_sub_eq_sum c T e (.of_forall hframe)
    (fun i ↦ by simp [hcomp (e i) _ (he i) (hEi i) x (T x), hTe i]) (fun i ↦ hbr i x)
    (fun i ↦ (contMDiff_clifford_apply hc (he i) (hEi i)).mdifferentiableAt (by simp))
    ((cov.contMDiff_transverseDiracOperator hc hT hσ).mdifferentiableAt (by simp))]

end IsMetricCompatible

end CovariantDerivative
