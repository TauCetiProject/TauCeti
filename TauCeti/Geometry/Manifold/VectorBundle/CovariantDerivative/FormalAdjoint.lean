/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.DivergenceTheorem
public import TauCeti.Geometry.Manifold.Riemannian.Gradient.Basic
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Hom
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.RoughLaplacian
public import TauCeti.Geometry.Manifold.VectorBundle.Riemannian.HilbertSchmidt
import TauCeti.Geometry.Manifold.Riemannian.Basic
import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Regularity
import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.SecondCovariantDerivative.Hom
import TauCeti.Geometry.Manifold.VectorBundle.Riemannian.Riesz
import TauCeti.Geometry.Manifold.VectorBundle.Section.Extension
import TauCeti.Topology.Algebra.Module.Spaces.ContinuousLinearMap

/-!
# The formal adjoint of a connection

Let `∇` be a connection on a vector bundle `V` over a Riemannian manifold `M`, and `∇ᵀ` a
connection on the tangent bundle. The connection is an operator `∇ : Γ(V) → Γ(T*M ⊗ V)` from
sections of `V` to `V`-valued one-forms, here sections `α` of the bundle `Hom(TM, V)`. Its
**formal adjoint** is the negative metric trace of the covariant derivative of a one-form,

`∇*α = -tr_g ∇α = -∑ᵢ (∇_{eᵢ} α)(eᵢ)`,

for any orthonormal basis `eᵢ` of the tangent space, where `∇α` is the covariant derivative of
`α` for the connection induced by `∇ᵀ` and `∇` on `Hom(TM, V)` (`CovariantDerivative.hom`).

This file proves that `∇*` is the formal adjoint of `∇` and that the rough Laplacian factors
through it:

* the rough Laplacian is the composite `∇*∇ σ = ∇*(∇σ)`, since the covariant derivative of the
  one-form `∇σ` is the second covariant derivative `∇²σ`;
* for a metric connection `∇` and the Levi-Civita connection `∇ᵀ` on a manifold without boundary,
  **integration by parts** holds for the Riemannian volume `dV`:

  `∫ ⟪∇*α, τ⟫ dV = ∫ ⟪α, ∇τ⟫ dV`

  for a smooth one-form `α` and a smooth section `τ`, one of which has compact support. Here
  `⟪α, ∇τ⟫ = ∑ᵢ ⟪α(eᵢ), ∇_{eᵢ} τ⟫` is the pointwise inner product of `V`-valued one-forms, the
  Hilbert–Schmidt inner product `ContinuousLinearMap.hilbertSchmidtInner`.

For `α = ∇σ` the integration by parts is the energy identity `∫ ⟪∇*∇ σ, τ⟫ dV = ∫ ⟪∇σ, ∇τ⟫ dV`
of the rough Laplacian, in `RoughLaplacian/Energy.lean`.

The integration by parts comes from the divergence theorem. The vector field `X` metric-dual to
the one-form `w ↦ ⟪α(w), τ⟫` has divergence `div X = ⟪α, ∇τ⟫ - ⟪∇*α, τ⟫`: at a point, with a
smooth vector field `W`, metric compatibility of the two connections gives
`⟪∇_u X, W⟫ = ⟪(∇_u α)(W), τ⟫ + ⟪α(W), ∇_u τ⟫`, and tracing over an orthonormal basis gives the
divergence.

## Main definitions and results

* `CovariantDerivative.formalAdjoint`: the formal adjoint `∇*α` of a `V`-valued one-form at a
  point.
* `CovariantDerivative.formalAdjoint_def`: it is the negative metric trace of `∇α`.
* `CovariantDerivative.formalAdjoint_eq_sum`: its value in an orthonormal basis.
* `CovariantDerivative.formalAdjoint_smul`: the Leibniz rule `∇*(f α) = f ∇*α - α(grad f)`.
* `CovariantDerivative.roughLaplacian_eq_formalAdjoint`: `∇*∇ σ = ∇*(∇σ)` for a smooth section.
* `CovariantDerivative.IsMetricCompatible.integral_inner_formalAdjoint` and
  `CovariantDerivative.IsMetricCompatible.integral_inner_formalAdjoint_of_isCompact_left`:
  **integration by parts**, `∫ ⟪∇*α, τ⟫ dV = ∫ ⟪α, ∇τ⟫ dV`, when `τ`, respectively `α`, has
  compact support.

## References

* H. B. Lawson and M.-L. Michelsohn, *Spin Geometry*, Princeton University Press (1989),
  Chapter II, §8 (the connection Laplacian `∇*∇` as the composite of `∇` and its adjoint).
* P. Gilkey, *The spectral geometry of operators of Dirac and Laplace type*, §2 (the rough
  Laplacian and operators of Laplace type).
* J. M. Lee, *Introduction to Riemannian Manifolds*, 2nd ed., Springer GTM 176 (2018),
  Chapter 2 (the divergence theorem) and Chapter 4 (covariant derivatives of tensor fields).
-/

public section

open Bundle FiberBundle MeasureTheory Riemannian.Tensor Set
open TauCeti (riemannianVolume)
open scoped ContDiff Manifold RealInnerProductSpace Topology

noncomputable section

namespace CovariantDerivative

section Definition

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 2 M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)]
  [∀ x, TopologicalSpace (V x)] [∀ x, IsTopologicalAddGroup (V x)]
  [∀ x, ContinuousSMul ℝ (V x)]
  [FiberBundle F V] [VectorBundle ℝ F V]
  (cov : _root_.CovariantDerivative I F V)
  (covT : _root_.CovariantDerivative I E (TangentSpace I : M → Type _))
  {α : Π x : M, TangentSpace I x →L[ℝ] V x}

variable [RiemannianBundle (fun x : M ↦ TangentSpace I x)]

/-- The **formal adjoint** `∇*α = -tr_g ∇α` of the connection `∇`, applied to a `V`-valued
one-form `α` at `x`: the negative metric trace (`LinearMap.BilinMap.metricTrace`) of the
covariant derivative of `α` for the connection induced by `∇ᵀ` and `∇` on `Hom(TM, V)`. In an
orthonormal basis it is `-∑ᵢ (∇_{eᵢ} α)(eᵢ)` (`formalAdjoint_eq_sum`). For a metric connection
and the Levi-Civita connection it is the formal adjoint of `∇` for the Riemannian volume
(`IsMetricCompatible.integral_inner_formalAdjoint`), and `∇*(∇σ)` is the rough Laplacian
(`roughLaplacian_eq_formalAdjoint`). It is zero at points where `α` is not differentiable. -/
def formalAdjoint (α : Π x : M, TangentSpace I x →L[ℝ] V x) (x : M) : V x :=
  -LinearMap.BilinMap.metricTrace (ContinuousLinearMap.toLinearMap₁₂ (covT.hom cov α x))

/-- The formal adjoint is the negative metric trace of the covariant derivative of the one-form. -/
theorem formalAdjoint_def (α : Π x : M, TangentSpace I x →L[ℝ] V x) (x : M) :
    cov.formalAdjoint covT α x =
      -LinearMap.BilinMap.metricTrace (ContinuousLinearMap.toLinearMap₁₂ (covT.hom cov α x)) :=
  (rfl)

/-- The formal adjoint of a connection in an orthonormal basis: `∇*α = -∑ᵢ (∇_{eᵢ} α)(eᵢ)`. -/
theorem formalAdjoint_eq_sum (α : Π x : M, TangentSpace I x →L[ℝ] V x) (x : M) {ι : Type*}
    [Fintype ι] (b : OrthonormalBasis ι ℝ (TangentSpace I x)) :
    cov.formalAdjoint covT α x = -∑ i, covT.hom cov α x (b i) (b i) := by
  simp only [formalAdjoint_def, LinearMap.BilinMap.metricTrace_eq_sum _ b,
    ContinuousLinearMap.toLinearMap₁₂_apply_apply_apply]

/-- The formal adjoint vanishes at a point where the one-form is not differentiable. -/
@[simp]
theorem formalAdjoint_eq_zero_of_not_mdifferentiableAt {x : M}
    (hα : ¬MDiffAt
      (fun y ↦ TotalSpace.mk' (E →L[ℝ] F) (E := fun z ↦ TangentSpace I z →L[ℝ] V z) y (α y)) x) :
    cov.formalAdjoint covT α x = 0 := by
  simp [formalAdjoint_def, hom_eq_zero_of_not_mdifferentiableAt covT cov hα]

/-- The formal adjoint of the zero one-form is zero. -/
@[simp]
theorem formalAdjoint_zero (x : M) :
    cov.formalAdjoint covT (0 : Π x : M, TangentSpace I x →L[ℝ] V x) x = 0 := by
  rw [formalAdjoint_def, (covT.hom cov).isCovariantDerivativeOnUniv.zero, map_zero, map_zero,
    neg_zero]

/-- The formal adjoint is additive on one-forms differentiable at the point. -/
theorem formalAdjoint_add {β : Π x : M, TangentSpace I x →L[ℝ] V x} {x : M}
    (hα : MDiffAt
      (fun y ↦ TotalSpace.mk' (E →L[ℝ] F) (E := fun z ↦ TangentSpace I z →L[ℝ] V z) y (α y)) x)
    (hβ : MDiffAt
      (fun y ↦ TotalSpace.mk' (E →L[ℝ] F) (E := fun z ↦ TangentSpace I z →L[ℝ] V z) y (β y)) x) :
    cov.formalAdjoint covT (α + β) x = cov.formalAdjoint covT α x + cov.formalAdjoint covT β x := by
  simp only [formalAdjoint_def, (covT.hom cov).isCovariantDerivativeOnUniv.add hα hβ, map_add,
    neg_add]

/-- The formal adjoint commutes with multiplication of the one-form by a constant. -/
@[simp]
theorem formalAdjoint_const_smul (c : ℝ) (x : M) :
    cov.formalAdjoint covT (c • α) x = c • cov.formalAdjoint covT α x := by
  by_cases hα : MDiffAt
      (fun y ↦ TotalSpace.mk' (E →L[ℝ] F) (E := fun z ↦ TangentSpace I z →L[ℝ] V z) y (α y)) x
  · simp only [formalAdjoint_def, (covT.hom cov).isCovariantDerivativeOnUniv.smul_const c hα,
      map_smul, smul_neg]
  · rcases eq_or_ne c 0 with rfl | hc
    · simp
    · have hcα : ¬MDiffAt (fun y ↦ TotalSpace.mk' (E →L[ℝ] F)
          (E := fun z ↦ TangentSpace I z →L[ℝ] V z) y ((c • α) y)) x := fun h ↦ hα (by
        simpa [smul_smul, inv_mul_cancel₀ hc] using
          (mdifferentiableAt_const (c := c⁻¹)).smul_section h)
      simp [formalAdjoint_eq_zero_of_not_mdifferentiableAt cov covT hα,
        formalAdjoint_eq_zero_of_not_mdifferentiableAt cov covT hcα]

/-- The formal adjoint commutes with negation of the one-form. -/
@[simp]
theorem formalAdjoint_neg (x : M) :
    cov.formalAdjoint covT (-α) x = -cov.formalAdjoint covT α x := by
  rw [← neg_one_smul ℝ α, formalAdjoint_const_smul, neg_one_smul]

/-- The formal adjoint commutes with differences of one-forms differentiable at the point. -/
theorem formalAdjoint_sub {β : Π x : M, TangentSpace I x →L[ℝ] V x} {x : M}
    (hα : MDiffAt
      (fun y ↦ TotalSpace.mk' (E →L[ℝ] F) (E := fun z ↦ TangentSpace I z →L[ℝ] V z) y (α y)) x)
    (hβ : MDiffAt
      (fun y ↦ TotalSpace.mk' (E →L[ℝ] F) (E := fun z ↦ TangentSpace I z →L[ℝ] V z) y (β y)) x) :
    cov.formalAdjoint covT (α - β) x = cov.formalAdjoint covT α x - cov.formalAdjoint covT β x := by
  have hβ' : MDiffAt (fun y ↦ TotalSpace.mk' (E →L[ℝ] F)
      (E := fun z ↦ TangentSpace I z →L[ℝ] V z) y ((-β) y)) x := by
    simpa using (mdifferentiableAt_const (c := (-1 : ℝ))).smul_section hβ
  rw [sub_eq_add_neg, formalAdjoint_add cov covT hα hβ', formalAdjoint_neg, sub_eq_add_neg]

/-- **Leibniz rule for the formal adjoint.** For a function `f` and a one-form `α` differentiable
at `x`, `∇*(f α) = f ∇*α - α(grad f)`. -/
theorem formalAdjoint_smul {f : M → ℝ} {x : M} (hf : MDiffAt f x)
    (hα : MDiffAt
      (fun y ↦ TotalSpace.mk' (E →L[ℝ] F) (E := fun z ↦ TangentSpace I z →L[ℝ] V z) y (α y)) x) :
    cov.formalAdjoint covT (f • α) x =
      f x • cov.formalAdjoint covT α x - α x (TauCeti.Manifold.mgradient I f x) := by
  -- The Leibniz term is the rank-one map `(v, w) ↦ ⟪grad f, v⟫ • α w`, whose trace is
  -- `α (grad f)`.
  rw [formalAdjoint_def, formalAdjoint_def,
    (covT.hom cov).isCovariantDerivativeOnUniv.leibniz hα hf, map_add, map_smul,
    ContinuousLinearMap.toLinearMap₁₂_smulRight,
    TauCeti.Manifold.toLinearMap_mvfderiv_eq_innerₗ_mgradient, map_add, map_smul,
    LinearMap.BilinMap.metricTrace_innerₗ_smulRight, ContinuousLinearMap.coe_coe, neg_add,
    smul_neg, sub_eq_add_neg]

end Definition

section RoughLaplacian

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)]
  [∀ x, TopologicalSpace (V x)] [∀ x, IsTopologicalAddGroup (V x)]
  [∀ x, ContinuousSMul ℝ (V x)]
  [FiberBundle F V] [VectorBundle ℝ F V]
  (cov : _root_.CovariantDerivative I F V) [ContMDiffCovariantDerivative cov ∞]
  (covT : _root_.CovariantDerivative I E (TangentSpace I : M → Type _))
  {σ : Π x : M, V x}

/-- **The rough Laplacian is the composite of the connection and its formal adjoint**:
`∇*∇ σ = ∇*(∇σ)` for a smooth section `σ`. -/
theorem roughLaplacian_eq_formalAdjoint (hσ : CMDiff ∞ (T% σ)) :
    cov.roughLaplacian covT σ = cov.formalAdjoint covT (cov σ) := by
  funext x
  rw [roughLaplacian_def, formalAdjoint_def,
    secondCovariantDerivative_eq_toLinearMap₁₂_hom cov covT hσ x]

end RoughLaplacian

/-! ### Integration by parts -/

section Pairing

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, NormedAddCommGroup (V x)] [∀ x, InnerProductSpace ℝ (V x)]
  [FiberBundle F V] [VectorBundle ℝ F V] [ContMDiffVectorBundle ∞ F V I]
  [IsContMDiffRiemannianBundle I ∞ F V]
  {cov : _root_.CovariantDerivative I F V} [ContMDiffCovariantDerivative cov ∞]
  {α : Π x : M, TangentSpace I x →L[ℝ] V x} {τ : Π x : M, V x}

/-- The vector field metric-dual to the one-form `w ↦ ⟪α(w), τ⟫`. -/
private def pairingField (α : Π x : M, TangentSpace I x →L[ℝ] V x) (τ : Π x : M, V x) (y : M) :
    TangentSpace I y :=
  rieszDual y ((innerSL ℝ (τ y)).comp (α y))

omit [T2Space M] [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)] in
private theorem inner_pairingField (y : M) (w : TangentSpace I y) :
    ⟪pairingField α τ y, w⟫ = ⟪α y w, τ y⟫ := by
  rw [pairingField, inner_rieszDual]
  simp [real_inner_comm]

omit [T2Space M] [FiniteDimensional ℝ F] [ContMDiffVectorBundle ∞ F V I] in
private theorem contMDiff_pairingField
    (hα : ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] F)) ∞
      (fun x ↦ TotalSpace.mk' (E →L[ℝ] F) (E := fun y ↦ TangentSpace I y →L[ℝ] V y) x (α x)))
    (hτ : CMDiff ∞ (T% τ)) :
    ContMDiff I I.tangent ∞ (T% (pairingField α τ)) := by
  intro x
  have : IsManifold I (∞ + 1) M := by simpa using (inferInstance : IsManifold I ∞ M)
  refine contMDiffAt_rieszDual (n := ∞) x (mem_chart_source H x) fun j ↦ ?_
  have hframe : CMDiffAt ∞ (T% (chartLocalFrame (I := I) x j)) x :=
    contMDiffAt_chartLocalFrame (I := I) (n := ∞) x j
  simpa only [ContinuousLinearMap.comp_apply, innerSL_apply_apply, real_inner_comm] using
    (ContMDiffAt.clm_bundle_apply (hα x) hframe).inner_bundle (hτ x)

omit [ContMDiffCovariantDerivative cov ∞] in
/-- The divergence of the vector field dual to `⟪α, τ⟫` is `⟪α, ∇τ⟫ - ⟪∇*α, τ⟫`. -/
private theorem divergence_pairingField (hcov : cov.IsMetricCompatible)
    (hα : ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] F)) ∞
      (fun x ↦ TotalSpace.mk' (E →L[ℝ] F) (E := fun y ↦ TangentSpace I y →L[ℝ] V y) x (α x)))
    (hτ : CMDiff ∞ (T% τ)) (x : M) :
    TauCeti.Manifold.divergence I (pairingField α τ) x =
      (α x).hilbertSchmidtInner (cov τ x) -
        ⟪cov.formalAdjoint (leviCivitaConnection I M) α x, τ x⟫ := by
  set covT := leviCivitaConnection I M
  set b := stdOrthonormalBasis ℝ (TangentSpace I x)
  have hXd : MDiffAt (T% (pairingField α τ)) x :=
    (contMDiff_pairingField hα hτ).mdifferentiableAt (by simp)
  have hαd := hα.mdifferentiableAt (x := x) (by simp)
  have hτd : MDiffAt (T% τ) x := hτ.mdifferentiable (by simp) x
  -- Each diagonal term of the divergence is `⟪(∇_{eᵢ} α)(eᵢ), τ⟫ + ⟪α(eᵢ), ∇_{eᵢ} τ⟫`.
  have hterm (i) : ⟪leviCivitaConnection I M (pairingField α τ) x (b i), b i⟫ =
      ⟪covT.hom cov α x (b i) (b i), τ x⟫ + ⟪α x (b i), cov τ x (b i)⟫ := by
    obtain ⟨W, hW, hWx⟩ := exists_contMDiff_section_eq I E ∞ (b i)
    have hWd : MDiffAt (T% W) x := hW.mdifferentiable (by simp) x
    have hαWd : MDiffAt (T% (fun y ↦ α y (W y))) x := hαd.clm_bundle_apply hWd
    have hLC := (isMetricCompatible_leviCivitaConnection I).mvfderiv_inner_eq
      (FiberBundle.extend E (b i)) hXd hWd
    have hV := hcov.mvfderiv_inner_eq (FiberBundle.extend E (b i)) hαWd hτd
    have hfun : (fun y ↦ ⟪pairingField α τ y, W y⟫) = fun y ↦ ⟪α y (W y), τ y⟫ :=
      funext fun y ↦ inner_pairingField y (W y)
    have hS := hom_apply covT cov hαd hWd (b i)
    simp only [FiberBundle.extend_apply_self] at hLC hV
    rw [hfun, hV, inner_pairingField] at hLC
    rw [hWx] at hLC hS
    rw [hS, inner_sub_left]
    linarith
  rw [TauCeti.Manifold.divergence_eq_sum_inner I _ x b,
    ContinuousLinearMap.hilbertSchmidtInner_eq_sum _ _ b, formalAdjoint_eq_sum cov covT α x b]
  simp only [hterm, Finset.sum_add_distrib, inner_neg_left, sum_inner]
  ring

namespace IsMetricCompatible

variable [I.Boundaryless] [SigmaCompactSpace M] [MeasurableSpace M] [BorelSpace M]

local instance : IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x) :=
  IsContMDiffRiemannianBundle.toIsContinuousRiemannianBundle
    (IB := I) (n := ∞) (F := E) (V := fun x : M ↦ TangentSpace I x)

/-- Integration by parts for the formal adjoint, when the vector field dual to `⟪α, τ⟫` and the
function `⟪α, ∇τ⟫` both vanish off a compact set. -/
private theorem integral_inner_formalAdjoint_of_subset (hcov : cov.IsMetricCompatible)
    (hα : ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] F)) ∞
      (fun x ↦ TotalSpace.mk' (E →L[ℝ] F) (E := fun y ↦ TangentSpace I y →L[ℝ] V y) x (α x)))
    (hτ : CMDiff ∞ (T% τ)) {K : Set M} (hK : IsCompact K) (hKc : IsClosed K)
    (hX : ∀ y ∉ K, pairingField α τ y = 0)
    (hB : ∀ y ∉ K, (α y).hilbertSchmidtInner (cov τ y) = 0) :
    ∫ x, ⟪cov.formalAdjoint (leviCivitaConnection I M) α x, τ x⟫ ∂riemannianVolume I M =
      ∫ x, (α x).hilbertSchmidtInner (cov τ x) ∂riemannianVolume I M := by
  have : IsManifold I (∞ + 1) M := by simpa using (inferInstance : IsManifold I ∞ M)
  have hXc : HasCompactSupport (β := E) (pairingField α τ) := .intro' hK hKc hX
  have hBc : HasCompactSupport fun x ↦ (α x).hilbertSchmidtInner (cov τ x) := .intro' hK hKc hB
  have hX1 : ContMDiff I I.tangent 1 (T% (pairingField α τ)) :=
    (contMDiff_pairingField hα hτ).of_le (by simp)
  have hBi : Integrable (fun x ↦ (α x).hilbertSchmidtInner (cov τ x)) (riemannianVolume I M) :=
    (hα.hilbertSchmidtInner_bundle (cov.contMDiff_covariantDerivative hτ)).continuous
      |>.integrable_of_hasCompactSupport hBc
  have hdiv := TauCeti.Manifold.integral_divergence_eq_zero hX1 hXc
  simp_rw [divergence_pairingField hcov hα hτ] at hdiv
  rw [integral_sub hBi] at hdiv
  · linarith
  · refine (hBi.sub (TauCeti.Manifold.integrable_divergence hX1 hXc)).congr
      (Filter.Eventually.of_forall fun x ↦ ?_)
    simp only [Pi.sub_apply, divergence_pairingField hcov hα hτ]
    ring

/-- **Integration by parts for the formal adjoint of a connection.** For a metric connection `∇`
on a Riemannian vector bundle over a manifold without boundary, a smooth `V`-valued one-form `α`
and a smooth section `τ` with compact support, `∫ ⟪∇*α, τ⟫ dV = ∫ ⟪α, ∇τ⟫ dV`, where
`⟪α, ∇τ⟫ = ∑ᵢ ⟪α(eᵢ), ∇_{eᵢ} τ⟫`: `∇*` is the formal adjoint of `∇` for the Riemannian
volume. -/
theorem integral_inner_formalAdjoint (hcov : cov.IsMetricCompatible)
    (hα : ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] F)) ∞
      (fun x ↦ TotalSpace.mk' (E →L[ℝ] F) (E := fun y ↦ TangentSpace I y →L[ℝ] V y) x (α x)))
    (hτ : CMDiff ∞ (T% τ)) (hτc : IsCompact (closure {x | τ x ≠ 0})) :
    ∫ x, ⟪cov.formalAdjoint (leviCivitaConnection I M) α x, τ x⟫ ∂riemannianVolume I M =
      ∫ x, (α x).hilbertSchmidtInner (cov τ x) ∂riemannianVolume I M := by
  refine integral_inner_formalAdjoint_of_subset hcov hα hτ hτc isClosed_closure
    (fun y hy ↦ ?_) (fun y hy ↦ ?_)
  · have hτy : τ y = 0 := by
      by_contra h
      exact hy (subset_closure h)
    simp [pairingField, hτy, LinearIsometryEquiv.map_zero]
  · simp [cov.apply_eq_zero_of_notMem_closure hy]

/-- **Integration by parts for the formal adjoint of a connection**, when the one-form has
compact support: `∫ ⟪∇*α, τ⟫ dV = ∫ ⟪α, ∇τ⟫ dV`. -/
theorem integral_inner_formalAdjoint_of_isCompact_left (hcov : cov.IsMetricCompatible)
    (hα : ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] F)) ∞
      (fun x ↦ TotalSpace.mk' (E →L[ℝ] F) (E := fun y ↦ TangentSpace I y →L[ℝ] V y) x (α x)))
    (hτ : CMDiff ∞ (T% τ)) (hαc : IsCompact (closure {x | α x ≠ 0})) :
    ∫ x, ⟪cov.formalAdjoint (leviCivitaConnection I M) α x, τ x⟫ ∂riemannianVolume I M =
      ∫ x, (α x).hilbertSchmidtInner (cov τ x) ∂riemannianVolume I M := by
  have hαy {y : M} (hy : y ∉ closure {x | α x ≠ 0}) : α y = 0 := by
    by_contra h
    exact hy (subset_closure h)
  refine integral_inner_formalAdjoint_of_subset hcov hα hτ hαc isClosed_closure
    (fun y hy ↦ ?_) (fun y hy ↦ ?_)
  · simp [pairingField, hαy hy, LinearIsometryEquiv.map_zero]
  · simp [hαy hy]

end IsMetricCompatible

end Pairing

end CovariantDerivative
