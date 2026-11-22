/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.DifferentialOperator.FormalAdjoint.Connection
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.RoughLaplacian.DifferentialOperator
import TauCeti.Geometry.Manifold.DifferentialOperator.LaplaceType.Basic
import TauCeti.Geometry.Manifold.MFDeriv.Localized
import TauCeti.Geometry.Manifold.Riemannian.Basic
import TauCeti.Geometry.Manifold.Riemannian.Gradient.Basic
import TauCeti.Geometry.Manifold.Riemannian.VolumeDensity.Support
import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Basic
import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.DifferentialOperator
import TauCeti.Geometry.Manifold.VectorBundle.Section.Extension

/-!
# Bochner connections of operators on vector bundles

Let `V` be a smooth vector bundle with a fibre metric over a Riemannian manifold `M`, and let
`c ≠ 0`. An operator `D : Γ(V) → Γ(V)` of Laplace type with constant `c` can be written as

`D = c ∇*∇ + P`,

where `∇*∇` is the rough Laplacian (`CovariantDerivative.smoothRoughLaplacian`) of a connection `∇`
on `V`, built with the Levi-Civita connection on the tangent bundle, and `P` is an operator of
order zero, that is a `C^∞(M)`-linear map, in Grothendieck's sense
(`TauCeti.differentialOperators`). The connection `∇` is the **Bochner connection** of `D`, and `P`
its zeroth-order remainder (Gilkey, Lemma 2.1, applied to `c⁻¹ D`). This file proves the two
statements about this decomposition that do not depend on how it was found.

* **Uniqueness.** The connection and the remainder are determined by `D`
  (`CovariantDerivative.eq_of_smul_smoothRoughLaplacian_add_eq`). Indeed the commutator of
  `D` with multiplication by a smooth function `f` is
  `[D, f] σ = c [∇*∇, f] σ = -c (2 ∇_{grad f} σ + (Δ f) σ)`
  (`CovariantDerivative.smulCommutator_smoothRoughLaplacian_apply`), since `P` commutes with `f`.
  So `D` determines `∇_{grad f}` for every `f`, and gradients of smooth functions take every value
  in each tangent space.
* **Formal self-adjointness.** For the Riemannian volume `dV` (`TauCeti.riemannianVolume`) and the
  given fibre metric, `D` is formally self-adjoint if and only if its Bochner connection is
  compatible with the metric and its remainder is fibrewise self-adjoint
  (`CovariantDerivative.isFormalAdjoint_smul_smoothRoughLaplacian_add_iff`); this is the remark
  following Gilkey's Lemma 2.1. If `D` is formally self-adjoint, so is each commutator `[D, f]`
  up to sign, so the operators `∇_{grad f} + ½ Δ f` are formally skew-adjoint; by
  `CovariantDerivative.isMetricCompatible_of_forall_integral_inner_apply_mgradient_eq` this forces
  `∇` to be metric. Then `∇*∇` is formally self-adjoint
  (`CovariantDerivative.IsMetricCompatible.isFormalAdjoint_smoothRoughLaplacian`), hence so is `P`,
  and a formally self-adjoint operator of order zero is fibrewise self-adjoint.

The density matters: for a weighted volume `e^w dV`, a formally self-adjoint operator of Laplace
type can have a Bochner connection that is not metric. On the trivial line over the real line this
already happens for `-∂ₓ² - cos x ∂ₓ`, formally self-adjoint for `e^(sin x) dx`: its Bochner
connection `d + ½ cos x dx` is not metric, since `d + ⟪Y, ·⟫` is metric only for `Y = 0`
(`CovariantDerivative.isMetricCompatible_trivialAddInner_iff`).

The existence of the Bochner connection of an operator of Laplace type on a vector bundle is not
proved here; for the trivial line bundle it is
`LinearMap.existsUnique_eq_mul_roughLaplacian_trivialAddInner_add_mul`.

## Main results

* `CovariantDerivative.eq_of_smul_smoothRoughLaplacian_add_eq`: if
  `c ∇*∇ + P = c ∇'*∇' + P'` with `c ≠ 0` and `P`, `P'` of order zero, then `∇` and `∇'` agree on
  every section differentiable at a point, and `P = P'`.
* `CovariantDerivative.isMetricCompatible_of_isFormalAdjoint_smul_smoothRoughLaplacian_add`: if
  `c ∇*∇ + P`, with `c ≠ 0` and `P` of order zero, is formally self-adjoint for the Riemannian
  volume, then `∇` is a metric connection.
* `CovariantDerivative.isFormalAdjoint_smul_smoothRoughLaplacian_add_iff`: `c ∇*∇ + P` is formally
  self-adjoint for the Riemannian volume if and only if `∇` is a metric connection and `P` is
  fibrewise self-adjoint.

## References

* P. B. Gilkey, *The spectral geometry of operators of Dirac and Laplace type*, in Handbook of
  Global Analysis, Elsevier, 2008, §2, Lemma 2.1 and the paragraph following it.
* N. Berline, E. Getzler, M. Vergne, *Heat Kernels and Dirac Operators*, Springer, 1992, §2.1
  (the connection and potential of a generalized Laplacian).
-/

public section

noncomputable section

open Bundle MeasureTheory TauCeti TauCeti.Manifold
open scoped ContDiff Manifold RealInnerProductSpace

namespace CovariantDerivative

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]

/-! ### Uniqueness of the Bochner connection -/

section Uniqueness

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)]
  [∀ x, TopologicalSpace (V x)] [∀ x, IsTopologicalAddGroup (V x)]
  [∀ x, ContinuousSMul ℝ (V x)]
  [FiberBundle F V] [VectorBundle ℝ F V] [ContMDiffVectorBundle ∞ F V I]

omit [FiniteDimensional ℝ F] in
/-- The commutator of `c ∇*∇ + P` with multiplication by `f`, for `P` of order zero, is
`c [∇*∇, f]`. -/
private theorem smulCommutator_smul_smoothRoughLaplacian_add
    (cov : _root_.CovariantDerivative I F V) [ContMDiffCovariantDerivative cov ∞] (c : ℝ)
    {P : Cₛ^∞⟮I; F, V⟯ →ₗ[ℝ] Cₛ^∞⟮I; F, V⟯}
    (hP : P ∈ differentialOperators ℝ C^∞⟮I, M; ℝ⟯ Cₛ^∞⟮I; F, V⟯ Cₛ^∞⟮I; F, V⟯ 0)
    (f : C^∞⟮I, M; ℝ⟯) :
    smulCommutator ℝ f (c • cov.smoothRoughLaplacian (leviCivitaConnection I M) + P) =
      c • smulCommutator ℝ f (cov.smoothRoughLaplacian (leviCivitaConnection I M)) := by
  rw [map_add, map_smul, smulCommutator_eq_zero_of_mem_differentialOperators_zero hP, add_zero]

/-- **Uniqueness of the Bochner connection.** If two smooth connections `∇`, `∇'` on `V` and two
operators `P`, `P'` of order zero give the same operator, `c ∇*∇ + P = c ∇'*∇' + P'` with
`c ≠ 0`, the rough Laplacians being built with the Levi-Civita connection, then the connections
agree on every section differentiable at a point, and `P = P'`. -/
theorem eq_of_smul_smoothRoughLaplacian_add_eq
    (cov cov' : _root_.CovariantDerivative I F V)
    [ContMDiffCovariantDerivative cov ∞] [ContMDiffCovariantDerivative cov' ∞]
    {c : ℝ} (hc : c ≠ 0) {P P' : Cₛ^∞⟮I; F, V⟯ →ₗ[ℝ] Cₛ^∞⟮I; F, V⟯}
    (hP : P ∈ differentialOperators ℝ C^∞⟮I, M; ℝ⟯ Cₛ^∞⟮I; F, V⟯ Cₛ^∞⟮I; F, V⟯ 0)
    (hP' : P' ∈ differentialOperators ℝ C^∞⟮I, M; ℝ⟯ Cₛ^∞⟮I; F, V⟯ Cₛ^∞⟮I; F, V⟯ 0)
    (h : c • cov.smoothRoughLaplacian (leviCivitaConnection I M) + P =
      c • cov'.smoothRoughLaplacian (leviCivitaConnection I M) + P') :
    (∀ (σ : Π x : M, V x) (x : M), MDiffAt (T% σ) x → cov σ x = cov' σ x) ∧ P = P' := by
  -- The connections agree on smooth sections: test the commutators `[D, f]` against a function
  -- with a prescribed gradient at `x`.
  have hsmooth (σ : Cₛ^∞⟮I; F, V⟯) (x : M) : cov σ x = cov' σ x := by
    ext v
    obtain ⟨f, -, hfx⟩ := TauCeti.exists_contMDiffMap_mvfderiv_eq (I := I) x (0 : ℝ) (innerSL ℝ v)
    have hgrad : mgradient I f x = v := by
      refine (eq_mgradient_iff.2 fun w ↦ ?_).symm
      rw [hfx, innerSL_apply_apply]
    have hf := congr(smulCommutator ℝ f $h σ x)
    rw [smulCommutator_smul_smoothRoughLaplacian_add cov c hP,
      smulCommutator_smul_smoothRoughLaplacian_add cov' c hP'] at hf
    simp only [LinearMap.smul_apply, ContMDiffSection.coe_smul, Pi.smul_apply,
      smulCommutator_smoothRoughLaplacian_apply, hgrad] at hf
    have hf' := sub_left_injective (smul_right_injective _ hc hf)
    exact smul_right_injective _ (by norm_num : -(2 : ℝ) ≠ 0) hf'
  -- Their difference tensor vanishes, so they agree on every differentiable section.
  have hdiff (σ : Π x : M, V x) (x : M) (hσ : MDiffAt (T% σ) x) : cov σ x = cov' σ x := by
    obtain ⟨τ, hτ⟩ := ContMDiffSection.evalLinearMap_surjective (I := I) (F := F) (V := V) ∞ x
      (σ x)
    rw [ContMDiffSection.evalLinearMap_apply] at hτ
    rw [← sub_eq_zero, ← difference_apply cov cov' hσ, ← hτ,
      difference_apply cov cov' τ.mdifferentiableAt, hsmooth, sub_self]
  refine ⟨hdiff, ?_⟩
  -- The rough Laplacians agree, hence so do the remainders.
  have hrough : cov.smoothRoughLaplacian (leviCivitaConnection I M) =
      cov'.smoothRoughLaplacian (leviCivitaConnection I M) := by
    refine LinearMap.ext fun σ ↦ ContMDiffSection.ext fun x ↦ ?_
    rw [smoothRoughLaplacian_apply, smoothRoughLaplacian_apply,
      roughLaplacian_congr cov _ cov' fun τ hτ ↦ funext fun y ↦ hdiff τ y
        (hτ.mdifferentiableAt (by simp))]
  rw [hrough] at h
  exact add_left_cancel h

end Uniqueness

/-! ### Formally self-adjoint operators and metric Bochner connections -/

section FormalAdjoint

variable [I.Boundaryless] [SigmaCompactSpace M] [MeasurableSpace M] [BorelSpace M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, NormedAddCommGroup (V x)] [∀ x, InnerProductSpace ℝ (V x)]
  [FiberBundle F V] [VectorBundle ℝ F V] [ContMDiffVectorBundle ∞ F V I]
  [IsContMDiffRiemannianBundle I ∞ F V]
  {cov : _root_.CovariantDerivative I F V} [ContMDiffCovariantDerivative cov ∞]

local instance instIsContinuousRiemannianBundleTangentSpaceBochner :
    IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x) :=
  IsContMDiffRiemannianBundle.toIsContinuousRiemannianBundle
    (IB := I) (n := ∞) (F := E) (V := fun x : M ↦ TangentSpace I x)

omit [I.Boundaryless] [FiniteDimensional ℝ F] in
/-- If `[∇*∇, f]` is formally skew-adjoint, then `∇_{grad f} + ½ Δ f` is, in the form of the
hypothesis of `CovariantDerivative.isMetricCompatible_of_forall_integral_inner_apply_mgradient_eq`.
-/
private theorem integral_inner_apply_mgradient_eq_of_isFormalAdjoint (f : C^∞⟮I, M; ℝ⟯)
    (h : (smulCommutator ℝ f (cov.smoothRoughLaplacian (leviCivitaConnection I M))).IsFormalAdjoint
      (-smulCommutator ℝ f (cov.smoothRoughLaplacian (leviCivitaConnection I M)))
      (riemannianVolume I M))
    {σ τ : Cₛ^∞⟮I; F, V⟯} (hσ : IsCompact σ.tsupport) :
    ∫ x, ⟪cov σ x (mgradient I f x), τ x⟫ ∂riemannianVolume I M =
      -∫ x, ⟪σ x, cov τ x (mgradient I f x) + laplaceBeltrami I f x • τ x⟫
        ∂riemannianVolume I M := by
  have := IsContMDiffRiemannianBundle.toIsContinuousRiemannianBundle (IB := I) (n := ∞) (F := F)
    (V := V)
  have h1 := h.integral_inner_eq (s := σ) (t := τ) (.inl hσ)
  let Y : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ :=
    ⟨mgradient I (f : M → ℝ), contMDiff_mgradient_infty f.contMDiff⟩
  set Δf := smoothLaplaceBeltrami I M f
  have hΔf (y : M) : Δf y = laplaceBeltrami I f y := smoothLaplaceBeltrami_apply f y
  set u : M → ℝ := fun y ↦ ⟪cov σ y (mgradient I f y), τ y⟫
  set v : M → ℝ := fun y ↦ ⟪σ y, cov τ y (mgradient I f y) + laplaceBeltrami I f y • τ y⟫
  set w : M → ℝ := fun y ↦ laplaceBeltrami I f y * ⟪σ y, τ y⟫
  have hu : Integrable u (riemannianVolume I M) :=
    (LinearMap.integrable_inner_apply_left (cov.tsupport_alongVectorField_apply_subset Y)
      (s := σ) (t := τ) (.inl hσ)).congr (.of_forall fun y ↦ by simp [u, Y])
  have hv : Integrable v (riemannianVolume I M) := by
    refine (ContMDiffSection.integrable_inner (μ := riemannianVolume I M) (s := σ)
      (t := cov.alongVectorField Y τ + Δf • τ) (.inl hσ)).congr (.of_forall fun y ↦ ?_)
    simp only [v, ContMDiffSection.coe_add, Pi.add_apply, alongVectorField_apply]
    rw [ContMDiffSection.smul_apply Δf τ y, hΔf]
    rfl
  have hw : Integrable w (riemannianVolume I M) :=
    (Δf.contMDiff.continuous.mul (ContMDiffSection.continuous_inner σ τ)
      |>.integrable_of_hasCompactSupport
        (ContMDiffSection.hasCompactSupport_inner (.inl hσ)).mul_left).congr
      (.of_forall fun y ↦ by simp [w, hΔf])
  -- `[∇*∇, f] = -2 ∇_{grad f} - Δ f`, paired with `τ` and with `σ`.
  have hleft (y : M) :
      ⟪smulCommutator ℝ f (cov.smoothRoughLaplacian (leviCivitaConnection I M)) σ y, τ y⟫ =
        -2 * u y + -1 * w y := by
    rw [smulCommutator_smoothRoughLaplacian_apply]
    simp only [u, w, inner_sub_left, real_inner_smul_left]
    ring
  have hright (y : M) :
      ⟪σ y, (-smulCommutator ℝ f (cov.smoothRoughLaplacian (leviCivitaConnection I M))) τ y⟫ =
        2 * v y + -1 * w y := by
    rw [LinearMap.neg_apply, ContMDiffSection.coe_neg, Pi.neg_apply,
      smulCommutator_smoothRoughLaplacian_apply]
    simp only [v, w, inner_neg_right, real_inner_smul_right, inner_sub_right, inner_add_right]
    ring
  rw [integral_congr_ae (.of_forall hleft), integral_congr_ae (.of_forall hright),
    integral_add (hu.const_mul _) (hw.const_mul _), integral_add (hv.const_mul _) (hw.const_mul _),
    integral_const_mul, integral_const_mul, integral_const_mul] at h1
  linarith

/-- **Formally self-adjoint operators have metric Bochner connections.** Let `c ≠ 0` and let `P`
be an operator of order zero on the smooth sections of a Riemannian bundle over a Riemannian
manifold without boundary. If `c ∇*∇ + P` is formally self-adjoint for the Riemannian volume, then
the connection `∇` is compatible with the fibre metric. -/
theorem isMetricCompatible_of_isFormalAdjoint_smul_smoothRoughLaplacian_add {c : ℝ} (hc : c ≠ 0)
    {P : Cₛ^∞⟮I; F, V⟯ →ₗ[ℝ] Cₛ^∞⟮I; F, V⟯}
    (hP : P ∈ differentialOperators ℝ C^∞⟮I, M; ℝ⟯ Cₛ^∞⟮I; F, V⟯ Cₛ^∞⟮I; F, V⟯ 0)
    (hD : (c • cov.smoothRoughLaplacian (leviCivitaConnection I M) + P).IsFormalAdjoint
      (c • cov.smoothRoughLaplacian (leviCivitaConnection I M) + P) (riemannianVolume I M)) :
    cov.IsMetricCompatible := by
  have := IsContMDiffRiemannianBundle.toIsContinuousRiemannianBundle (IB := I) (n := ∞) (F := F)
    (V := V)
  have hDs := tsupport_differentialOperators_section_apply_subset (add_mem
    (Submodule.smul_mem _ c
      (cov.smoothRoughLaplacian_mem_differentialOperators_two (leviCivitaConnection I M)))
    (differentialOperators_mono (by norm_num : 0 ≤ 2) hP))
  refine isMetricCompatible_of_forall_integral_inner_apply_mgradient_eq fun f σ τ hσ ↦ ?_
  -- The commutator `[D, f] = c [∇*∇, f]` is formally skew-adjoint, hence so is `[∇*∇, f]`.
  have h := (hD.smulCommutator hDs hDs f).smul c⁻¹
  rw [smulCommutator_smul_smoothRoughLaplacian_add cov c hP, smul_neg, smul_smul,
    inv_mul_cancel₀ hc, one_smul] at h
  exact integral_inner_apply_mgradient_eq_of_isFormalAdjoint f h hσ

/-- **Formally self-adjoint operators and their Bochner connections.** Let `c ≠ 0` and let `P`
be an operator of order zero on the smooth sections of a Riemannian bundle over a Riemannian
manifold without boundary. Then `c ∇*∇ + P` is formally self-adjoint for the Riemannian volume if
and only if the connection `∇` is compatible with the fibre metric and `P` is fibrewise
self-adjoint: `⟪P s x, t x⟫ = ⟪s x, P t x⟫` for all smooth sections `s`, `t` and every point `x`.
-/
theorem isFormalAdjoint_smul_smoothRoughLaplacian_add_iff {c : ℝ} (hc : c ≠ 0)
    {P : Cₛ^∞⟮I; F, V⟯ →ₗ[ℝ] Cₛ^∞⟮I; F, V⟯}
    (hP : P ∈ differentialOperators ℝ C^∞⟮I, M; ℝ⟯ Cₛ^∞⟮I; F, V⟯ Cₛ^∞⟮I; F, V⟯ 0) :
    (c • cov.smoothRoughLaplacian (leviCivitaConnection I M) + P).IsFormalAdjoint
        (c • cov.smoothRoughLaplacian (leviCivitaConnection I M) + P) (riemannianVolume I M) ↔
      cov.IsMetricCompatible ∧ ∀ s t x, ⟪P s x, t x⟫ = ⟪s x, P t x⟫ := by
  have := IsContMDiffRiemannianBundle.toIsContinuousRiemannianBundle (IB := I) (n := ∞) (F := F)
    (V := V)
  set L := cov.smoothRoughLaplacian (leviCivitaConnection I M)
  have hL2 := cov.smoothRoughLaplacian_mem_differentialOperators_two (leviCivitaConnection I M)
  have hPs := tsupport_differentialOperators_section_apply_subset hP
  have hcLs := tsupport_differentialOperators_section_apply_subset (Submodule.smul_mem _ c hL2)
  have hDs := tsupport_differentialOperators_section_apply_subset
    (add_mem (Submodule.smul_mem _ c hL2) (differentialOperators_mono (by norm_num : 0 ≤ 2) hP))
  have hLsa (hcov : cov.IsMetricCompatible) :
      (c • L).IsFormalAdjoint (c • L) (riemannianVolume I M) :=
    hcov.isFormalAdjoint_smoothRoughLaplacian.smul c
  refine ⟨fun hD ↦ ?_, fun ⟨hcov, hPsa⟩ ↦ (hLsa hcov).add
    (LinearMap.isFormalAdjoint_of_forall_inner_eq hPsa) hcLs hPs hcLs hPs⟩
  have hcov := isMetricCompatible_of_isFormalAdjoint_smul_smoothRoughLaplacian_add hc hP hD
  -- `P = D - c ∇*∇` is formally self-adjoint and of order zero, hence fibrewise self-adjoint.
  have hP' : P.IsFormalAdjoint P (riemannianVolume I M) := by
    simpa using hD.sub (hLsa hcov) hDs hcLs hDs hcLs
  exact ⟨hcov, hP'.inner_apply_eq_of_mem_differentialOperators_zero hP⟩

end FormalAdjoint

end CovariantDerivative
