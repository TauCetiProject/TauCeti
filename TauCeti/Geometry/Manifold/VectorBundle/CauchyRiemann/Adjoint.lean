/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.CauchyRiemann.Connection
public import TauCeti.Geometry.Manifold.VectorBundle.CauchyRiemann.HilbertSchmidt
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.FormalAdjoint
import TauCeti.Analysis.InnerProductSpace.Dual
import TauCeti.Geometry.Manifold.Riemannian.Basic
import TauCeti.Geometry.Manifold.Riemannian.VolumeDensity.Support
import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.LeviCivita.Regularity
import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Regularity
import TauCeti.Geometry.Manifold.VectorBundle.Hom
import TauCeti.Geometry.Manifold.VectorBundle.Riemannian.Dual
import TauCeti.Geometry.Manifold.VectorBundle.Section.Inner
import TauCeti.Geometry.Manifold.VectorBundle.Trivial
import TauCeti.Geometry.Symplectic.Complex.InnerProductSpace

/-!
# The formal adjoint of a real Cauchy–Riemann operator

Let `M` be a manifold without boundary with an almost complex structure `j` and a Riemannian
metric for which `j` is orthogonal, and let `V → M` be a complex vector bundle with a Hermitian
metric, that is a real fibre metric for which multiplication by `i` is orthogonal. Let `D` be a
smooth real Cauchy–Riemann operator on `V` (`TauCeti.IsRealCauchyRiemannOperator`). The `L²`
pairing of sections uses the fibre metric and the Riemannian volume `dV`, and the pairing of
`V`-valued one-forms uses the Hilbert–Schmidt inner product
`ContinuousLinearMap.hilbertSchmidtInner`.

The **formal adjoint** `D*` of `D` (`TauCeti.IsRealCauchyRiemannOperator.formalAdjoint`) is built
from a metric connection `∇` on `V`. The operator `D` differs from the real Cauchy–Riemann operator
`(∇ξ)^{0,1}` by a zeroth-order term `a` (`TauCeti.IsRealCauchyRiemannOperator.difference`), and

`D* η = ∇* η + a* η`,

where `∇*` is the formal adjoint of `∇` for the Levi-Civita connection
(`CovariantDerivative.formalAdjoint`) and `a* η` is the fibrewise adjoint of `a` for the
Hilbert–Schmidt pairing, `⟪a* η, e⟫ = ⟪η, a e⟫_HS`. **Green's formula** (McDuff–Salamon,
Lemma C.1.9, for a surface without boundary) is

`∫ ⟪D* η, ξ⟫ dV = ∫ ⟪η, D ξ⟫_HS dV`

for a smooth compactly supported section `ξ` and a smooth `(0,1)`-form `η`. On a `(0,1)`-form the
pairings with `(∇ξ)^{0,1}` and with `∇ξ` agree, because the `(0,1)`-projection is self-adjoint for
compatible metrics
(`TauCeti.SmoothAlmostComplexStructure.IsZeroOneForm.hilbertSchmidtInner_zeroOnePart_right`), so
Green's formula follows from integration by parts for `∇`
(`CovariantDerivative.IsMetricCompatible.integral_inner_formalAdjoint`).

The adjoint `D*` sends smooth one-forms to smooth sections, it is characterized among smooth
sections by Green's formula, and so it does not depend on the metric connection. It is a first
order operator of `∂`-type: `D* (f η) = f D* η - η (grad f)`, and for a `(0,1)`-form `η` the term
`η (grad f)` only involves the complex linear part `∂f` of `df`.

## Main definitions

* `TauCeti.IsRealCauchyRiemannOperator.formalAdjoint`: the formal adjoint `D*`.

## Main results

* `TauCeti.IsRealCauchyRiemannOperator.inner_formalAdjoint`: `⟪D* η, e⟫ = ⟪∇* η, e⟫ + ⟪η, a e⟫_HS`.
* `TauCeti.IsRealCauchyRiemannOperator.contMDiff_formalAdjoint`: `D*` sends smooth one-forms to
  smooth sections.
* `TauCeti.IsRealCauchyRiemannOperator.integral_inner_formalAdjoint`: Green's formula
  `∫ ⟪D* η, ξ⟫ dV = ∫ ⟪η, D ξ⟫_HS dV` for compactly supported `ξ`, and
  `TauCeti.IsRealCauchyRiemannOperator.integral_inner_formalAdjoint_of_compactSpace` on a closed
  manifold.
* `TauCeti.IsRealCauchyRiemannOperator.eq_formalAdjoint_of_forall_integral_inner_eq`: a smooth
  section satisfying Green's formula is `D* η`, and
  `TauCeti.IsRealCauchyRiemannOperator.formalAdjoint_eq_of_isMetricCompatible`: `D*` does not
  depend on the metric connection.
* `TauCeti.IsRealCauchyRiemannOperator.formalAdjoint_smul`: the Leibniz rule
  `D* (f η) = f D* η - η (grad f)`.

## References

* D. McDuff, D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  Appendix C.1, Lemma C.1.9.
-/

public section

open Bundle FiberBundle MeasureTheory Set CovariantDerivative
open scoped ContDiff Manifold RealInnerProductSpace Topology

noncomputable section

namespace TauCeti

open SmoothAlmostComplexStructure

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, NormedAddCommGroup (V x)] [∀ x, InnerProductSpace ℝ (V x)]
  [∀ x, Module ℂ (V x)] [∀ x, IsScalarTower ℝ ℂ (V x)] [∀ x, ContinuousSMul ℂ (V x)]
  [FiberBundle F V] [VectorBundle ℝ F V] [ContMDiffVectorBundle ∞ F V I]
  [IsContMDiffRiemannianBundle I ∞ F V]
  {j : SmoothAlmostComplexStructure I M}
  {D : (Π x : M, V x) → Π x : M, TangentSpace I x →L[ℝ] V x}
  (hD : IsRealCauchyRiemannOperator F j D) (cov : _root_.CovariantDerivative I F V)
  {η : Π x : M, TangentSpace I x →L[ℝ] V x}

omit [T2Space M]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)] [FiniteDimensional ℝ F]
  [∀ x, IsScalarTower ℝ ℂ (V x)] [∀ x, ContinuousSMul ℂ (V x)] [ContMDiffVectorBundle ∞ F V I]
  [IsContMDiffRiemannianBundle I ∞ F V] in
/-- **The formal adjoint is of `∂`-type.** In real dimension two, for an orthogonal almost
complex structure `j`, a `(0,1)`-form `θ` at `x` and a unit tangent vector `v`, the term
`θ (grad f)` in the Leibniz rule of the formal adjoint
(`TauCeti.IsRealCauchyRiemannOperator.formalAdjoint_smul`) is
`df v • θ v - df (j v) • i • θ v`. So it only involves the complex linear part
`∂f = ½ (df - i • df ∘ j)` of `df`, where a real Cauchy–Riemann operator involves the complex
antilinear part `∂bar f`. -/
theorem SmoothAlmostComplexStructure.IsZeroOneForm.apply_mgradient {x : M}
    {θ : TangentSpace I x →L[ℝ] V x} (hθ : j.IsZeroOneForm θ)
    (hJ : ∀ u v : TangentSpace I x, ⟪j x u, j x v⟫ = ⟪u, v⟫)
    (hDim : Module.finrank ℝ (TangentSpace I x) = 2) {v : TangentSpace I x} (hv : ‖v‖ = 1)
    (f : M → ℝ) :
    θ (TauCeti.Manifold.mgradient I f x) =
      mvfderiv I f x v • θ v - mvfderiv I f x (j x v) • Complex.I • θ v := by
  have hJ' : ∀ u w, ⟪j.almostComplexStructureAt x u, j.almostComplexStructureAt x w⟫ = ⟪u, w⟫ := by
    simpa only [almostComplexStructureAt_apply] using hJ
  have hvself : ⟪v, v⟫ = 1 := by
    rw [real_inner_self_eq_norm_sq, hv]
    norm_num
  have hcross : ⟪v, j x v⟫ = 0 := by
    simpa only [almostComplexStructureAt_apply] using
      (real_inner_comm _ _).trans ((j.almostComplexStructureAt x).inner_apply_self hJ' v)
  have hon : Orthonormal ℝ ![v, j x v] := by
    rw [orthonormal_iff_ite]
    intro i k
    fin_cases i <;> fin_cases k
    · exact hvself
    · exact hcross
    · exact (real_inner_comm _ _).trans hcross
    · exact (hJ v v).trans hvself
  have hspan := hon.linearIndependent.span_eq_top_of_card_eq_finrank
    (by simpa only [Fintype.card_fin] using hDim.symm)
  let b := OrthonormalBasis.mk hon hspan.ge
  have hb0 : b 0 = v := by simp [b]
  have hb1 : b 1 = j x v := by simp [b]
  rw [← b.sum_repr' (TauCeti.Manifold.mgradient I f x), Fin.sum_univ_two, hb0, hb1, map_add,
    map_smul, map_smul, isZeroOneForm_iff.1 hθ v, TauCeti.Manifold.inner_mgradient_right,
    TauCeti.Manifold.inner_mgradient_right, smul_neg, sub_eq_add_neg]

namespace IsRealCauchyRiemannOperator

/-- The **formal adjoint** `D* η = ∇* η + a* η` of a real Cauchy–Riemann operator `D`, applied to
a `V`-valued one-form `η` at `x`. Here `∇*` is the formal adjoint of the connection `∇` for the
Levi-Civita connection, `a = D - (∇ ·)^{0,1}` is the zeroth-order term by which `D` differs from
the `(0,1)`-part of `∇`, and `a* η` is its fibrewise adjoint for the Hilbert–Schmidt pairing,
`⟪a* η, e⟫ = ⟪η, a e⟫_HS` (`TauCeti.IsRealCauchyRiemannOperator.inner_formalAdjoint`). For a metric
connection it is the formal adjoint of `D` on `(0,1)`-forms
(`TauCeti.IsRealCauchyRiemannOperator.integral_inner_formalAdjoint`) and does not depend on `∇`
(`TauCeti.IsRealCauchyRiemannOperator.formalAdjoint_eq_of_isMetricCompatible`). -/
def formalAdjoint (η : Π x : M, TangentSpace I x →L[ℝ] V x) (x : M) : V x :=
  cov.formalAdjoint (leviCivitaConnection I M) η x +
    (innerSL ℝ (E := V x)).inverse ((η x).hilbertSchmidtInnerL.comp
      (hD.difference (cov.isCovariantDerivativeOnUniv.isRealCauchyRiemannOperator_zeroOnePart j) x))

omit [T2Space M] [IsContMDiffRiemannianBundle I ∞ F V] in
/-- The defining property of the formal adjoint: `⟪D* η, e⟫ = ⟪∇* η, e⟫ + ⟪η, a e⟫_HS`, where
`a = D - (∇ ·)^{0,1}` is the zeroth-order term of `D` relative to `∇`. -/
theorem inner_formalAdjoint (η : Π x : M, TangentSpace I x →L[ℝ] V x) (x : M) (e : V x) :
    ⟪hD.formalAdjoint cov η x, e⟫ = ⟪cov.formalAdjoint (leviCivitaConnection I M) η x, e⟫ +
      (η x).hilbertSchmidtInner (hD.difference
        (cov.isCovariantDerivativeOnUniv.isRealCauchyRiemannOperator_zeroOnePart j) x e) := by
  let := VectorBundle.finiteDimensional ℝ F V x
  have hinv := InnerProductSpace.isInvertible_innerSL (E := V x)
  rw [formalAdjoint, inner_add_left]
  congr 1
  rw [← innerSL_apply_apply ℝ, hinv.self_apply_inverse, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.hilbertSchmidtInnerL_apply]

omit [T2Space M] [IsContMDiffRiemannianBundle I ∞ F V] in
/-- **Leibniz rule for the formal adjoint.** For a function `f` and a one-form `η` differentiable
at `x`, `D* (f η) = f D* η - η (grad f)`. So `D*` is a first-order operator whose symbol is
`-η (grad f)`; on a `(0,1)`-form `η` this only involves the complex linear part `∂f` of `df`. -/
theorem formalAdjoint_smul {f : M → ℝ} {x : M} (hf : MDiffAt f x)
    (hη : MDiffAt
      (fun y ↦ TotalSpace.mk' (E →L[ℝ] F) (E := fun z ↦ TangentSpace I z →L[ℝ] V z) y (η y)) x) :
    hD.formalAdjoint cov (f • η) x =
      f x • hD.formalAdjoint cov η x - η x (TauCeti.Manifold.mgradient I f x) := by
  refine ext_inner_right ℝ fun e ↦ ?_
  rw [inner_formalAdjoint, inner_sub_left, real_inner_smul_left, inner_formalAdjoint,
    CovariantDerivative.formalAdjoint_smul _ _ hf hη, inner_sub_left, real_inner_smul_left,
    Pi.smul_apply', ContinuousLinearMap.hilbertSchmidtInner_smul_left]
  ring

include hD in
omit [T2Space M] [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ F V] in
/-- At a section differentiable at `x`, the Hilbert–Schmidt pairing of a `(0,1)`-form with the
zeroth-order term is `⟪η, D ξ⟫_HS - ⟪η, ∇ξ⟫_HS`, for compatible metrics. -/
private theorem hilbertSchmidtInner_difference {x : M} (hηx : j.IsZeroOneForm (η x))
    (hJ : ∀ u v : TangentSpace I x, ⟪j x u, j x v⟫ = ⟪u, v⟫)
    (hV : ∀ u v : V x, ⟪Complex.I • u, Complex.I • v⟫ = ⟪u, v⟫)
    {ξ : Π x : M, V x} (hξ : MDiffAt (T% ξ) x) :
    (η x).hilbertSchmidtInner (hD.difference
        (cov.isCovariantDerivativeOnUniv.isRealCauchyRiemannOperator_zeroOnePart j) x (ξ x)) =
      (η x).hilbertSchmidtInner (D ξ x) - (η x).hilbertSchmidtInner (cov ξ x) := by
  rw [hD.difference_apply _ hξ, ContinuousLinearMap.hilbertSchmidtInner_sub_right,
    hηx.hilbertSchmidtInner_zeroOnePart_right hJ hV]

variable [ContMDiffCovariantDerivative cov ∞]

omit [∀ x, Module ℂ (V x)] [FiniteDimensional ℝ E] [T2Space M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)] [FiniteDimensional ℝ F]
  [∀ x, IsScalarTower ℝ ℂ (V x)] [∀ x, ContinuousSMul ℂ (V x)] [ContMDiffVectorBundle ∞ F V I]
  [IsContMDiffRiemannianBundle I ∞ F V] in
/-- A smooth real Cauchy–Riemann operator sends smooth sections to smooth one-forms. -/
private theorem contMDiff_apply (hDs : ContMDiffCovariantDerivativeOn F ∞ D univ)
    {σ : Π x : M, V x} (hσ : CMDiff ∞ (T% σ)) :
    ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] F)) ∞
      (fun x ↦ TotalSpace.mk' (E →L[ℝ] F) (E := fun y ↦ TangentSpace I y →L[ℝ] V y) x (D σ x)) :=
  contMDiffOn_univ.mp (hDs.contMDiff (by simpa using hσ.contMDiffOn))

/-- The formal adjoint of a smooth real Cauchy–Riemann operator sends smooth `(0,1)`-forms to
smooth sections, for compatible metrics and a smooth connection. -/
theorem contMDiff_formalAdjoint (hDs : ContMDiffCovariantDerivativeOn F ∞ D univ)
    (hJ : ∀ x (u v : TangentSpace I x), ⟪j x u, j x v⟫ = ⟪u, v⟫)
    (hV : ∀ x (u v : V x), ⟪Complex.I • u, Complex.I • v⟫ = ⟪u, v⟫)
    (hη : ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] F)) ∞
      (fun x ↦ TotalSpace.mk' (E →L[ℝ] F) (E := fun y ↦ TangentSpace I y →L[ℝ] V y) x (η x)))
    (hη01 : ∀ x, j.IsZeroOneForm (η x)) :
    CMDiff ∞ (T% (hD.formalAdjoint cov η)) := by
  -- The covector field `e ↦ ⟪η, a e⟫_HS` is smooth: on a smooth section `s` it is
  -- `⟪η, D s⟫_HS - ⟪η, ∇ s⟫_HS`.
  let ψ : Π x : M, V x →L[ℝ] Trivial M ℝ x := fun x ↦ (η x).hilbertSchmidtInnerL.comp
    (hD.difference (cov.isCovariantDerivativeOnUniv.isRealCauchyRiemannOperator_zeroOnePart j) x)
  have hψ : ContMDiff I (I.prod 𝓘(ℝ, F →L[ℝ] ℝ)) ∞
      (fun x ↦ TotalSpace.mk' (F →L[ℝ] ℝ) (E := fun y ↦ V y →L[ℝ] Trivial M ℝ y) x (ψ x)) := by
    refine (TauCeti.Manifold.contMDiff_hom_iff ψ).2 fun s hs ↦ ?_
    refine Bundle.Trivial.contMDiff_mk_iff.2 ⟨contMDiff_id, ?_⟩
    refine ((hη.hilbertSchmidtInner_bundle (contMDiff_apply hDs hs)).sub
      (hη.hilbertSchmidtInner_bundle (cov.contMDiff_covariantDerivative (by simpa using hs)))).congr
      fun x ↦ ?_
    simp only [ψ, ContinuousLinearMap.comp_apply, ContinuousLinearMap.hilbertSchmidtInnerL_apply]
    exact hilbertSchmidtInner_difference hD cov (hη01 x) (hJ x) (hV x)
      ((hs x).mdifferentiableAt (by simp))
  exact (cov.contMDiff_formalAdjoint (leviCivitaConnection I M) hη).add_section
    (IsContMDiffRiemannianBundle.contMDiff_innerSL_inverse.clm_bundle_apply hψ)

/-! ### Green's formula -/

variable [I.Boundaryless] [SigmaCompactSpace M] [MeasurableSpace M] [BorelSpace M]

local instance : IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x) :=
  IsContMDiffRiemannianBundle.toIsContinuousRiemannianBundle
    (IB := I) (n := ∞) (F := E) (V := fun x : M ↦ TangentSpace I x)

/-- **Green's formula for a real Cauchy–Riemann operator** (McDuff–Salamon, Lemma C.1.9, without
boundary). For compatible metrics, a smooth metric connection `∇`, a smooth `(0,1)`-form `η` and
a smooth compactly supported section `ξ`, `∫ ⟪D* η, ξ⟫ dV = ∫ ⟪η, D ξ⟫_HS dV`. -/
theorem integral_inner_formalAdjoint (hcov : cov.IsMetricCompatible)
    (hDs : ContMDiffCovariantDerivativeOn F ∞ D univ)
    (hJ : ∀ x (u v : TangentSpace I x), ⟪j x u, j x v⟫ = ⟪u, v⟫)
    (hV : ∀ x (u v : V x), ⟪Complex.I • u, Complex.I • v⟫ = ⟪u, v⟫)
    (hη : ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] F)) ∞
      (fun x ↦ TotalSpace.mk' (E →L[ℝ] F) (E := fun y ↦ TangentSpace I y →L[ℝ] V y) x (η x)))
    (hη01 : ∀ x, j.IsZeroOneForm (η x)) {ξ : Π x : M, V x} (hξ : CMDiff ∞ (T% ξ))
    (hξc : IsCompact (closure {x | ξ x ≠ 0})) :
    ∫ x, ⟪hD.formalAdjoint cov η x, ξ x⟫ ∂riemannianVolume I M =
      ∫ x, (η x).hilbertSchmidtInner (D ξ x) ∂riemannianVolume I M := by
  have hoff {y : M} (hy : y ∉ closure {x | ξ x ≠ 0}) : ξ y = 0 := by
    by_contra h
    exact hy (subset_closure h)
  have h1 : Integrable (fun x ↦ ⟪cov.formalAdjoint (leviCivitaConnection I M) η x, ξ x⟫)
      (riemannianVolume I M) :=
    ((cov.contMDiff_formalAdjoint _ hη).inner_bundle hξ).continuous.integrable_of_hasCompactSupport
      (.intro' hξc isClosed_closure fun y hy ↦ by simp [hoff hy])
  have h2 : Integrable (fun x ↦ (η x).hilbertSchmidtInner (D ξ x)) (riemannianVolume I M) :=
    (hη.hilbertSchmidtInner_bundle (contMDiff_apply hDs hξ)).continuous
      |>.integrable_of_hasCompactSupport
      (.intro' hξc isClosed_closure fun y hy ↦ by simp [hD.apply_eq_zero_of_notMem_closure hy])
  have h3 : Integrable (fun x ↦ (η x).hilbertSchmidtInner (cov ξ x)) (riemannianVolume I M) :=
    (hη.hilbertSchmidtInner_bundle
      (cov.contMDiff_covariantDerivative (by simpa using hξ))).continuous
      |>.integrable_of_hasCompactSupport
      (.intro' hξc isClosed_closure fun y hy ↦ by simp [cov.apply_eq_zero_of_notMem_closure hy])
  have hpt : (fun x ↦ ⟪hD.formalAdjoint cov η x, ξ x⟫) = fun x ↦
      ⟪cov.formalAdjoint (leviCivitaConnection I M) η x, ξ x⟫ +
        ((η x).hilbertSchmidtInner (D ξ x) - (η x).hilbertSchmidtInner (cov ξ x)) := by
    funext x
    rw [inner_formalAdjoint, hilbertSchmidtInner_difference hD cov (hη01 x) (hJ x) (hV x)
      ((hξ x).mdifferentiableAt (by simp))]
  have h23 : Integrable (fun x ↦ (η x).hilbertSchmidtInner (D ξ x) -
      (η x).hilbertSchmidtInner (cov ξ x)) (riemannianVolume I M) := h2.sub h3
  rw [hpt, integral_add h1 h23, integral_sub h2 h3,
    hcov.integral_inner_formalAdjoint hη hξ hξc]
  ring

/-- **Green's formula on a closed manifold**: `∫ ⟪D* η, ξ⟫ dV = ∫ ⟪η, D ξ⟫_HS dV` for smooth `ξ`
and a smooth `(0,1)`-form `η`. -/
theorem integral_inner_formalAdjoint_of_compactSpace [CompactSpace M]
    (hcov : cov.IsMetricCompatible) (hDs : ContMDiffCovariantDerivativeOn F ∞ D univ)
    (hJ : ∀ x (u v : TangentSpace I x), ⟪j x u, j x v⟫ = ⟪u, v⟫)
    (hV : ∀ x (u v : V x), ⟪Complex.I • u, Complex.I • v⟫ = ⟪u, v⟫)
    (hη : ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] F)) ∞
      (fun x ↦ TotalSpace.mk' (E →L[ℝ] F) (E := fun y ↦ TangentSpace I y →L[ℝ] V y) x (η x)))
    (hη01 : ∀ x, j.IsZeroOneForm (η x)) {ξ : Π x : M, V x} (hξ : CMDiff ∞ (T% ξ)) :
    ∫ x, ⟪hD.formalAdjoint cov η x, ξ x⟫ ∂riemannianVolume I M =
      ∫ x, (η x).hilbertSchmidtInner (D ξ x) ∂riemannianVolume I M :=
  hD.integral_inner_formalAdjoint cov hcov hDs hJ hV hη hη01 hξ isClosed_closure.isCompact

/-- **Uniqueness of the formal adjoint.** A smooth section `s` with
`∫ ⟪s, ξ⟫ dV = ∫ ⟪η, D ξ⟫_HS dV` for every smooth compactly supported section `ξ` is `D* η`. -/
theorem eq_formalAdjoint_of_forall_integral_inner_eq (hcov : cov.IsMetricCompatible)
    (hDs : ContMDiffCovariantDerivativeOn F ∞ D univ)
    (hJ : ∀ x (u v : TangentSpace I x), ⟪j x u, j x v⟫ = ⟪u, v⟫)
    (hV : ∀ x (u v : V x), ⟪Complex.I • u, Complex.I • v⟫ = ⟪u, v⟫)
    (hη : ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] F)) ∞
      (fun x ↦ TotalSpace.mk' (E →L[ℝ] F) (E := fun y ↦ TangentSpace I y →L[ℝ] V y) x (η x)))
    (hη01 : ∀ x, j.IsZeroOneForm (η x)) {s : Π x : M, V x} (hs : CMDiff ∞ (T% s))
    (h : ∀ ξ : Π x : M, V x, CMDiff ∞ (T% ξ) → IsCompact (closure {x | ξ x ≠ 0}) →
      ∫ x, ⟪s x, ξ x⟫ ∂riemannianVolume I M =
        ∫ x, (η x).hilbertSchmidtInner (D ξ x) ∂riemannianVolume I M) :
    s = hD.formalAdjoint cov η := by
  have : IsContinuousRiemannianBundle F V :=
    IsContMDiffRiemannianBundle.toIsContinuousRiemannianBundle (IB := I) (n := ∞)
  have hA := hD.contMDiff_formalAdjoint cov hDs hJ hV hη hη01
  let u : Cₛ^∞⟮I; F, V⟯ := ⟨s - hD.formalAdjoint cov η, hs.sub_section hA⟩
  have hu : u = 0 := by
    refine ContMDiffSection.eq_zero_of_forall_integral_inner_eq_zero
      (μ := riemannianVolume I M) fun t ht ↦ ?_
    rw [ContMDiffSection.tsupport_def] at ht
    have hoff {y : M} (hy : y ∉ closure {x | t x ≠ 0}) : t y = 0 := by
      by_contra h
      exact hy (subset_closure h)
    have hint {f : Π x : M, V x} (hf : CMDiff ∞ (T% f)) :
        Integrable (fun x ↦ ⟪f x, t x⟫) (riemannianVolume I M) :=
      (hf.inner_bundle t.contMDiff).continuous.integrable_of_hasCompactSupport
        (.intro' ht isClosed_closure fun y hy ↦ by simp [hoff hy])
    have hut (x : M) : ⟪t x, u x⟫ = ⟪s x, t x⟫ - ⟪hD.formalAdjoint cov η x, t x⟫ := by
      simp only [u, ContMDiffSection.coeFn_mk, Pi.sub_apply, inner_sub_right, real_inner_comm]
    simp only [hut]
    rw [integral_sub (hint hs) (hint hA), h t t.contMDiff ht,
      hD.integral_inner_formalAdjoint cov hcov hDs hJ hV hη hη01 t.contMDiff ht, sub_self]
  funext x
  simpa [u, sub_eq_zero] using congrArg (fun w : Cₛ^∞⟮I; F, V⟯ ↦ w x) hu

/-- The formal adjoint does not depend on the smooth metric connection used to build it. -/
theorem formalAdjoint_eq_of_isMetricCompatible {cov' : _root_.CovariantDerivative I F V}
    [ContMDiffCovariantDerivative cov' ∞] (hcov : cov.IsMetricCompatible)
    (hcov' : cov'.IsMetricCompatible) (hDs : ContMDiffCovariantDerivativeOn F ∞ D univ)
    (hJ : ∀ x (u v : TangentSpace I x), ⟪j x u, j x v⟫ = ⟪u, v⟫)
    (hV : ∀ x (u v : V x), ⟪Complex.I • u, Complex.I • v⟫ = ⟪u, v⟫)
    (hη : ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] F)) ∞
      (fun x ↦ TotalSpace.mk' (E →L[ℝ] F) (E := fun y ↦ TangentSpace I y →L[ℝ] V y) x (η x)))
    (hη01 : ∀ x, j.IsZeroOneForm (η x)) :
    hD.formalAdjoint cov η = hD.formalAdjoint cov' η :=
  hD.eq_formalAdjoint_of_forall_integral_inner_eq cov' hcov' hDs hJ hV hη hη01
    (hD.contMDiff_formalAdjoint cov hDs hJ hV hη hη01)
    fun _ hξ hξc ↦ hD.integral_inner_formalAdjoint cov hcov hDs hJ hV hη hη01 hξ hξc

end IsRealCauchyRiemannOperator

end TauCeti
