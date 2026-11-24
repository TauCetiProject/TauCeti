/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.DifferentialOperator.DiracType
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Dirac.Basic
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.FormalAdjoint
import TauCeti.Geometry.Manifold.Riemannian.Basic
import TauCeti.Geometry.Manifold.Riemannian.VolumeDensity.Support
import TauCeti.Geometry.Manifold.VectorBundle.Bilinear.Section
import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Regularity
import TauCeti.Geometry.Manifold.VectorBundle.Riemannian.ChartGram
import TauCeti.Geometry.Manifold.VectorBundle.Section.Extension

/-!
# The Dirac operator as a formally self-adjoint operator of Dirac type

Let `V` be a smooth vector bundle over a Riemannian manifold `M`, with a smooth connection `∇` and
a smooth Clifford multiplication `c`, a smooth section of `Hom(TM, End V)`. The Dirac operator
`D σ = ∑ᵢ c(eᵢ) ∇_{eᵢ} σ` (`CovariantDerivative.diracOperator`) sends smooth sections to smooth
sections (`CovariantDerivative.contMDiff_diracOperator`): near a point it is the finite sum
`∑ᵢ c(Fᵢ) ∇_{Dᵢ} σ` over the chart frame `Fᵢ` and its metric-dual frame `Dᵢ`, which depend smoothly
on the point. So `D` is a real-linear endomorphism of the smooth sections
(`CovariantDerivative.smoothDiracOperator`), on the carrier of differential operators, principal
symbols and formal adjoints used for the rough Laplacian in
`TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.RoughLaplacian.DifferentialOperator`.

**Order and symbol.** The commutator of `D` with multiplication by a smooth function `f` is
Clifford multiplication by the gradient, `[D, f] = c(grad f)`
(`CovariantDerivative.smulCommutator_smoothDiracOperator_apply`), an operator of order zero. So
`D` is a differential operator of order at most one
(`CovariantDerivative.smoothDiracOperator_mem_differentialOperators_one`) with geometric principal
symbol `σ_geom(D)(ξ) = c(ξ♯)` (`CovariantDerivative.sectionPrincipalSymbol_smoothDiracOperator`).
If `c` satisfies the Clifford relation `c(v)² = -‖v‖²`, then `D²` is of Laplace type with constant
`1` (`CovariantDerivative.isSectionLaplaceType_smoothDiracOperator_comp`). When `V` carries a
fibre metric for which each `c(v)` is skew-adjoint and `c` satisfies the Clifford relation, the
symbol satisfies `σ(ξ)* σ(ξ) = ‖ξ‖² Id`, so `D` is of Dirac type
(`CovariantDerivative.isDiracType_smoothDiracOperator`); in particular it is elliptic.

**Formal self-adjointness.** Suppose that the connection is metric, each `c(v)` is skew-adjoint,
and `∇` is compatible with `c` and the Levi-Civita connection `∇ᵀ`,
`∇_u (c(Y) τ) = c(∇ᵀ_u Y) τ + c(Y) ∇_u τ`. Then for every section `τ` the `V`-valued one-form
`c(·) τ : w ↦ c(w) τ` has formal adjoint

`∇*(c(·) τ) = -D τ`

(`CovariantDerivative.formalAdjoint_flip_eq_neg_diracOperator`), while skew-adjointness gives
`⟪D σ, τ⟫ = -⟪∇σ, c(·) τ⟫` pointwise
(`CovariantDerivative.inner_diracOperator_eq_neg_hilbertSchmidtInner`). Integrating by parts with
the formal adjoint of the connection
(`CovariantDerivative.IsMetricCompatible.integral_inner_formalAdjoint`) gives, on a manifold
without boundary with its Riemannian volume,

`∫ ⟪D σ, τ⟫ dV = ∫ ⟪σ, D τ⟫ dV`

for smooth sections one of which has compact support
(`CovariantDerivative.IsMetricCompatible.integral_inner_diracOperator_left_eq_right` and its
variant `integral_inner_diracOperator_left_eq_right_of_isCompact_left`):
the Dirac operator is its own formal adjoint
(`CovariantDerivative.IsMetricCompatible.isFormalAdjoint_smoothDiracOperator`). Consequently
`∫ ⟪D² σ, σ⟫ dV = ∫ ‖D σ‖² dV` for every compactly supported smooth section `σ`
(`CovariantDerivative.IsMetricCompatible.integral_inner_diracOperator_diracOperator_self`), the
identity through which the Weitzenböck formula for `D²` becomes an integral energy identity.

## Main definitions

* `CovariantDerivative.smoothDiracOperator`: the Dirac operator as a real-linear endomorphism of
  the smooth sections.

## Main results

* `CovariantDerivative.contMDiff_diracOperator`: the Dirac operator of a smooth section is smooth.
* `CovariantDerivative.smoothDiracOperator_mem_differentialOperators_one`: `D` has order at most
  one.
* `CovariantDerivative.sectionPrincipalSymbol_smoothDiracOperator`: its principal symbol is
  `ξ ↦ c(ξ♯)`.
* `CovariantDerivative.isSectionLaplaceType_smoothDiracOperator_comp`: under the Clifford relation,
  `D²` is of Laplace type.
* `CovariantDerivative.isDiracType_smoothDiracOperator`: under the Clifford relation and
  skew-adjointness, `D` is of Dirac type.
* `CovariantDerivative.formalAdjoint_flip_eq_neg_diracOperator`: `∇*(c(·) τ) = -D τ`.
* `CovariantDerivative.IsMetricCompatible.integral_inner_diracOperator_left_eq_right`: integration
  by parts, `∫ ⟪D σ, τ⟫ dV = ∫ ⟪σ, D τ⟫ dV`.
* `CovariantDerivative.IsMetricCompatible.isFormalAdjoint_smoothDiracOperator`: `D` is formally
  self-adjoint.
* `CovariantDerivative.IsMetricCompatible.integral_inner_diracOperator_diracOperator_self`: the
  energy identity `∫ ⟪D² σ, σ⟫ dV = ∫ ‖D σ‖² dV`.

## References

* L. I. Nicolaescu, *Lectures on the Geometry of Manifolds*, 2nd ed., World Scientific, 2007,
  §12.1.4 (Proposition 12.1.66: Dirac operators of Clifford bundles are formally self-adjoint).
* H. B. Lawson and M.-L. Michelsohn, *Spin Geometry*, Princeton University Press, 1989,
  Chapter II, §5 (Proposition 5.3).
* P. B. Gilkey, *The spectral geometry of operators of Dirac and Laplace type*, in Handbook of
  Global Analysis, Elsevier, 2008, §2.
-/

public section

open Bundle FiberBundle MeasureTheory Riemannian.Tensor TauCeti
open scoped ContDiff Manifold RealInnerProductSpace Topology

noncomputable section

namespace CovariantDerivative

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]

/-! ### The Dirac operator as a differential operator -/

section Operator

variable [IsManifold I ∞ M] [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)]
  [∀ x, TopologicalSpace (V x)] [∀ x, IsTopologicalAddGroup (V x)]
  [∀ x, ContinuousSMul ℝ (V x)]
  [FiberBundle F V] [VectorBundle ℝ F V]
  (cov : _root_.CovariantDerivative I F V) [ContMDiffCovariantDerivative cov ∞]
  {c : Π x : M, TangentSpace I x →L[ℝ] V x →L[ℝ] V x}

/-- **The Dirac operator is smooth.** For a smooth connection `∇` and a Clifford multiplication `c`
which is a smooth section of `Hom(TM, End V)`, the Dirac operator `D σ` of a smooth section `σ` is
smooth. -/
theorem contMDiff_diracOperator
    (hc : ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] F →L[ℝ] F)) ∞
      (fun x ↦ TotalSpace.mk' (E →L[ℝ] F →L[ℝ] F)
        (E := fun y ↦ TangentSpace I y →L[ℝ] V y →L[ℝ] V y) x (c x)))
    {σ : Π y : M, V y} (hσ : CMDiff ∞ (T% σ)) :
    CMDiff ∞ (T% (cov.diracOperator c σ)) := by
  have : IsManifold I (∞ + 1) M := by simpa using (inferInstance : IsManifold I ∞ M)
  have h1 := cov.contMDiff_covariantDerivative (n := ∞) (by simpa using hσ)
  intro x
  have hx : x ∈ (trivializationAt E (TangentSpace I) x).baseSet :=
    mem_baseSet_trivializationAt E _ x
  -- Near `x`, `D σ = ∑ᵢ c(Fᵢ) ∇_{Dᵢ} σ` with the smooth chart frame `Fᵢ` and its dual frame `Dᵢ`.
  have hsum : CMDiffAt ∞ (T% (fun y ↦ ∑ i, c y (chartLocalFrame (I := I) x i y)
      (cov σ y (chartDualFrame (I := I) x i y)))) x :=
    ContMDiffAt.sum_section fun i _ ↦
      ((hc x).clm_bundle_apply (contMDiffAt_chartLocalFrame (n := ∞) x i)).clm_bundle_apply
        ((h1 x).clm_bundle_apply (contMDiffAt_chartDualFrame (n := ∞) x hx i))
  refine hsum.congr_of_eventuallyEq ?_
  filter_upwards [eventually_metricTrace_eq_sum_chartDualFrame (I := I) x (mem_chart_source H x)
    fun y ↦ (ContinuousLinearMap.toLinearMap₁₂ (c y)).compl₂ (cov σ y).toLinearMap] with y hy
  rw [diracOperator_def, LinearMap.metricTraceCompl₂_apply, hy]
  simp

/-- The Dirac operator `D σ = ∑ᵢ c(eᵢ) ∇_{eᵢ} σ` (`CovariantDerivative.diracOperator`) of a smooth
connection `∇` and a smooth Clifford multiplication `c`, as a real-linear endomorphism of the smooth
sections of `V`. -/
def smoothDiracOperator
    (hc : ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] F →L[ℝ] F)) ∞
      (fun x ↦ TotalSpace.mk' (E →L[ℝ] F →L[ℝ] F)
        (E := fun y ↦ TangentSpace I y →L[ℝ] V y →L[ℝ] V y) x (c x))) :
    Cₛ^∞⟮I; F, V⟯ →ₗ[ℝ] Cₛ^∞⟮I; F, V⟯ where
  toFun σ := ⟨cov.diracOperator c σ, cov.contMDiff_diracOperator hc σ.contMDiff⟩
  map_add' σ τ := ContMDiffSection.ext fun x ↦ by
    simpa using cov.diracOperator_add c (σ.contMDiff.mdifferentiableAt (by simp))
      (τ.contMDiff.mdifferentiableAt (by simp)) (x := x)
  map_smul' a σ := ContMDiffSection.ext fun x ↦ by
    simpa using cov.diracOperator_const_smul c a (σ.contMDiff.mdifferentiableAt (by simp)) (x := x)

variable (hc : ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] F →L[ℝ] F)) ∞
  (fun x ↦ TotalSpace.mk' (E →L[ℝ] F →L[ℝ] F)
    (E := fun y ↦ TangentSpace I y →L[ℝ] V y →L[ℝ] V y) x (c x)))

/-- The smooth Dirac operator evaluates pointwise to the Dirac operator of the section. -/
@[simp]
theorem smoothDiracOperator_apply (σ : Cₛ^∞⟮I; F, V⟯) (x : M) :
    cov.smoothDiracOperator hc σ x = cov.diracOperator c σ x :=
  (rfl)

/-- **The commutator of the Dirac operator with multiplication** by a smooth function `f` is
Clifford multiplication by the gradient of `f`: `[D, f] σ = D (f σ) - f D σ = c(grad f) σ`. -/
theorem smulCommutator_smoothDiracOperator_apply (f : C^∞⟮I, M; ℝ⟯) (σ : Cₛ^∞⟮I; F, V⟯) (x : M) :
    smulCommutator ℝ f (cov.smoothDiracOperator hc) σ x =
      c x (TauCeti.Manifold.mgradient I f x) (σ x) := by
  have hfun : ⇑(f • σ) = ⇑f • ⇑σ := funext fun y ↦ ContMDiffSection.smul_apply f σ y
  simp only [smulCommutator_apply_apply, ContMDiffSection.coe_sub, Pi.sub_apply,
    smoothDiracOperator_apply, hfun, ContMDiffSection.smul_apply]
  exact cov.diracOperator_smul_sub c (f.contMDiff.mdifferentiableAt (by simp))
    (σ.contMDiff.mdifferentiableAt (by simp))

/-- **The Dirac operator has order one**: it is a differential operator of order at most one on the
smooth sections, since its commutators with multiplication by smooth functions are of order zero. -/
theorem smoothDiracOperator_mem_differentialOperators_one :
    cov.smoothDiracOperator hc ∈
      differentialOperators ℝ C^∞⟮I, M; ℝ⟯ Cₛ^∞⟮I; F, V⟯ Cₛ^∞⟮I; F, V⟯ 1 := by
  refine mem_differentialOperators_succ_iff.2 fun f ↦ mem_differentialOperators_zero_iff.2
    fun a σ ↦ ContMDiffSection.ext fun x ↦ ?_
  simp only [smulCommutator_smoothDiracOperator_apply, ContMDiffSection.smul_apply, map_smul]

/-- **The principal symbol of the Dirac operator.** The geometric principal symbol of `D` at a
covector `ξ` is Clifford multiplication by its metric dual vector, `σ_geom(D)(ξ) = c(ξ♯)`. -/
@[simp]
theorem sectionPrincipalSymbol_smoothDiracOperator [T2Space M] [FiniteDimensional ℝ F]
    [ContMDiffVectorBundle ∞ F V I] {x : M}
    (hx : I.IsInteriorPoint x) (ξ : TangentSpace I x →L[ℝ] ℝ) :
    sectionPrincipalSymbol I hx
      ⟨cov.smoothDiracOperator hc, cov.smoothDiracOperator_mem_differentialOperators_one hc⟩ ξ =
        (c x (rieszDual x ξ) : V x →ₗ[ℝ] V x) := by
  obtain ⟨f, rfl⟩ : ∃ f : C^∞⟮I, M; ℝ⟯, mvfderiv I f x = ξ := ⟨_, mvfderiv_covectorLift hx ξ⟩
  refine LinearMap.ext fun v ↦ ?_
  obtain ⟨σ, rfl⟩ := ContMDiffSection.evalLinearMap_surjective (I := I) (F := F) (V := V) ∞ x v
  rw [ContMDiffSection.evalLinearMap_apply, sectionPrincipalSymbol_mvfderiv, pow_one,
    Nat.factorial_one, Nat.cast_one, inv_one, one_smul, ContinuousLinearMap.coe_coe,
    ← TauCeti.Manifold.mgradient_def]
  exact cov.smulCommutator_smoothDiracOperator_apply hc f σ x

/-- **The square of the Dirac operator is of Laplace type.** If `c` satisfies the Clifford relation
`c(v) c(v) = -⟪v, v⟫`, then `D² = D ∘ D` is of Laplace type with constant `1`: its principal
symbol is `c(ξ♯) c(ξ♯) = -‖ξ‖² Id`. -/
theorem isSectionLaplaceType_smoothDiracOperator_comp [T2Space M] [FiniteDimensional ℝ F]
    [ContMDiffVectorBundle ∞ F V I]
    (hcl : ∀ x (v : TangentSpace I x) (s : V x), c x v (c x v s) = -⟪v, v⟫ • s) :
    IsSectionLaplaceType ⟨cov.smoothDiracOperator hc ∘ₗ cov.smoothDiracOperator hc,
      comp_mem_differentialOperators (cov.smoothDiracOperator_mem_differentialOperators_one hc)
        (cov.smoothDiracOperator_mem_differentialOperators_one hc)⟩ 1 := by
  refine isSectionLaplaceType_iff.2 ⟨one_pos, fun x hx ξ ↦ LinearMap.ext fun v ↦ ?_⟩
  rw [sectionPrincipalSymbol_comp hx
    ⟨_, cov.smoothDiracOperator_mem_differentialOperators_one hc⟩
    ⟨_, cov.smoothDiracOperator_mem_differentialOperators_one hc⟩ ξ,
    sectionPrincipalSymbol_smoothDiracOperator, LinearMap.comp_apply, ContinuousLinearMap.coe_coe,
    hcl, real_inner_self_eq_norm_sq, LinearIsometryEquiv.norm_map, LinearMap.smul_apply,
    LinearMap.id_apply, one_mul]

end Operator

/-! ### Pointwise identities for a Clifford multiplication by skew-adjoint maps -/

section Pointwise

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, NormedAddCommGroup (V x)] [∀ x, InnerProductSpace ℝ (V x)] [FiberBundle F V]
  (cov : _root_.CovariantDerivative I F V)
  {c : Π x : M, TangentSpace I x →L[ℝ] V x →L[ℝ] V x}

/-- Pointwise, `⟪D σ, τ⟫ = -⟪∇σ, c(·) τ⟫` when each `c(v)` is skew-adjoint, where `c(·) τ` is the
`V`-valued one-form `w ↦ c(w) τ` and the pairing of one-forms is the Hilbert–Schmidt inner
product `ContinuousLinearMap.hilbertSchmidtInner`. -/
theorem inner_diracOperator_eq_neg_hilbertSchmidtInner
    (hskew : ∀ x (v : TangentSpace I x) (s t : V x), ⟪c x v s, t⟫ = -⟪s, c x v t⟫)
    (σ τ : Π y : M, V y) (x : M) :
    ⟪cov.diracOperator c σ x, τ x⟫ = -((c x).flip (τ x)).hilbertSchmidtInner (cov σ x) := by
  set b := stdOrthonormalBasis ℝ (TangentSpace I x)
  rw [diracOperator_eq_sum cov c σ x b, ContinuousLinearMap.hilbertSchmidtInner_eq_sum _ _ b,
    sum_inner, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [hskew, ContinuousLinearMap.flip_apply, real_inner_comm]

variable [T2Space M] [IsManifold I ∞ M] [VectorBundle ℝ F V]

/-- **The formal adjoint of Clifford multiplication.** If `∇` is compatible at `x` with `c` and a
connection `∇ᵀ` on the tangent bundle, `∇_u (c(Y) τ) = c(∇ᵀ_u Y) τ + c(Y) ∇_u τ` for smooth vector
fields `Y`, then for a section `τ` the `V`-valued one-form `c(·) τ : w ↦ c(w) τ`, if it is
differentiable at `x`, has formal adjoint `∇*(c(·) τ) = -D τ` at `x`. -/
theorem formalAdjoint_flip_eq_neg_diracOperator
    (covT : _root_.CovariantDerivative I E (TangentSpace I : M → Type _))
    {τ : Π y : M, V y} {x : M}
    (hcomp : ∀ Y : Π y : M, TangentSpace I y, CMDiff ∞ (T% Y) →
      ∀ u, cov (fun y ↦ c y (Y y) (τ y)) x u = c x (covT Y x u) (τ x) + c x (Y x) (cov τ x u))
    (hα : MDiffAt (fun y ↦ TotalSpace.mk' (E →L[ℝ] F)
      (E := fun z ↦ TangentSpace I z →L[ℝ] V z) y ((c y).flip (τ y))) x) :
    cov.formalAdjoint covT (fun y ↦ (c y).flip (τ y)) x = -cov.diracOperator c τ x := by
  set b := stdOrthonormalBasis ℝ (TangentSpace I x)
  rw [formalAdjoint_eq_sum cov covT _ x b, diracOperator_eq_sum cov c τ x b]
  congr 1
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  -- Evaluate `∇(c(·) τ)` on a smooth extension `W` of the basis vector.
  obtain ⟨W, hW, hWx⟩ := exists_contMDiff_section_eq I E ∞ (b i)
  have h := hom_apply covT cov hα (hW.mdifferentiable (by simp) x) (b i)
  simp only [ContinuousLinearMap.flip_apply, hWx] at h
  rw [h, hcomp W hW, ← hWx, add_sub_cancel_left]

end Pointwise

/-! ### Dirac type and formal self-adjointness -/

section FormalAdjoint

variable [T2Space M] [IsManifold I ∞ M]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, NormedAddCommGroup (V x)] [∀ x, InnerProductSpace ℝ (V x)]
  [FiberBundle F V] [VectorBundle ℝ F V] [ContMDiffVectorBundle ∞ F V I]
  {cov : _root_.CovariantDerivative I F V} [ContMDiffCovariantDerivative cov ∞]
  {c : Π x : M, TangentSpace I x →L[ℝ] V x →L[ℝ] V x}
  (hc : ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] F →L[ℝ] F)) ∞
    (fun x ↦ TotalSpace.mk' (E →L[ℝ] F →L[ℝ] F)
      (E := fun y ↦ TangentSpace I y →L[ℝ] V y →L[ℝ] V y) x (c x)))

/-- **The Dirac operator of a Clifford module is of Dirac type.** If each `c(v)` is skew-adjoint and
`c` satisfies the Clifford relation `c(v) c(v) = -⟪v, v⟫`, then the principal symbol `c(ξ♯)` of
the Dirac operator satisfies `σ(ξ)* σ(ξ) = ‖ξ‖² Id`. -/
theorem isDiracType_smoothDiracOperator
    (hskew : ∀ x (v : TangentSpace I x) (s t : V x), ⟪c x v s, t⟫ = -⟪s, c x v t⟫)
    (hcl : ∀ x (v : TangentSpace I x) (s : V x), c x v (c x v s) = -⟪v, v⟫ • s) :
    IsDiracType
      ⟨cov.smoothDiracOperator hc, cov.smoothDiracOperator_mem_differentialOperators_one hc⟩ := by
  refine isDiracType_iff.2 fun x hx ξ v w ↦ ?_
  rw [sectionPrincipalSymbol_smoothDiracOperator, ContinuousLinearMap.coe_coe, hskew, hcl,
    inner_smul_right, real_inner_self_eq_norm_sq, LinearIsometryEquiv.norm_map]
  ring

variable [IsContMDiffRiemannianBundle I ∞ F V]
  [I.Boundaryless] [SigmaCompactSpace M] [MeasurableSpace M] [BorelSpace M]
  (hskew : ∀ x (v : TangentSpace I x) (s t : V x), ⟪c x v s, t⟫ = -⟪s, c x v t⟫)
  (hcomp : ∀ (Y : Π y : M, TangentSpace I y) (τ : Π y : M, V y), CMDiff ∞ (T% Y) →
    CMDiff ∞ (T% τ) → ∀ x u, cov (fun y ↦ c y (Y y) (τ y)) x u =
      c x (leviCivitaConnection I M Y x u) (τ x) + c x (Y x) (cov τ x u))

local instance instIsContinuousRiemannianBundleTangentSpaceDirac :
    IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x) :=
  IsContMDiffRiemannianBundle.toIsContinuousRiemannianBundle
    (IB := I) (n := ∞) (F := E) (V := fun x : M ↦ TangentSpace I x)

namespace IsMetricCompatible

include hc hskew hcomp

/-- **Integration by parts for the Dirac operator**, when the first section has compact support.
Let `∇` be a metric connection on a Riemannian vector bundle over a manifold without boundary, and
`c` a smooth Clifford multiplication by skew-adjoint endomorphisms with which `∇` is compatible
together with the Levi-Civita connection `∇ᵀ`: `∇_u (c(Y) τ) = c(∇ᵀ_u Y) τ + c(Y) ∇_u τ` for smooth
vector fields `Y` and sections `τ`. Then for smooth sections `σ` and `τ`, with `σ` compactly
supported, `∫ ⟪D σ, τ⟫ dV = ∫ ⟪σ, D τ⟫ dV` for the Riemannian volume. -/
theorem integral_inner_diracOperator_left_eq_right_of_isCompact_left
    (hcov : cov.IsMetricCompatible) {σ τ : Π y : M, V y} (hσ : CMDiff ∞ (T% σ))
    (hτ : CMDiff ∞ (T% τ)) (hσc : IsCompact (closure {x | σ x ≠ 0})) :
    ∫ x, ⟪cov.diracOperator c σ x, τ x⟫ ∂riemannianVolume I M =
      ∫ x, ⟪σ x, cov.diracOperator c τ x⟫ ∂riemannianVolume I M := by
  have hα := hc.clm_bundle_flip.clm_bundle_apply hτ
  have hadj (x : M) : cov.formalAdjoint (leviCivitaConnection I M)
      (fun y ↦ (c y).flip (τ y)) x = -cov.diracOperator c τ x :=
    formalAdjoint_flip_eq_neg_diracOperator cov (leviCivitaConnection I M)
      (fun Y hY u ↦ hcomp Y τ hY hτ x u) (hα.mdifferentiableAt (by simp))
  -- `⟪D σ, τ⟫ = -⟪∇σ, c(·) τ⟫` pointwise, and `∇*(c(·) τ) = -D τ`.
  calc ∫ x, ⟪cov.diracOperator c σ x, τ x⟫ ∂riemannianVolume I M
      = -∫ x, ((c x).flip (τ x)).hilbertSchmidtInner (cov σ x) ∂riemannianVolume I M := by
        rw [← integral_neg]
        exact integral_congr_ae (.of_forall fun x ↦
          inner_diracOperator_eq_neg_hilbertSchmidtInner cov hskew σ τ x)
    _ = ∫ x, ⟪cov.diracOperator c τ x, σ x⟫ ∂riemannianVolume I M := by
        rw [← hcov.integral_inner_formalAdjoint hα hσ hσc]
        simp only [hadj, inner_neg_left, integral_neg, neg_neg]
    _ = ∫ x, ⟪σ x, cov.diracOperator c τ x⟫ ∂riemannianVolume I M :=
        integral_congr_ae (.of_forall fun x ↦ real_inner_comm _ _)

/-- **Integration by parts for the Dirac operator.** Under the same hypotheses on `∇` and `c`, for
smooth sections `σ` and `τ` with `τ` compactly supported, `∫ ⟪D σ, τ⟫ dV = ∫ ⟪σ, D τ⟫ dV`. -/
theorem integral_inner_diracOperator_left_eq_right (hcov : cov.IsMetricCompatible)
    {σ τ : Π y : M, V y} (hσ : CMDiff ∞ (T% σ)) (hτ : CMDiff ∞ (T% τ))
    (hτc : IsCompact (closure {x | τ x ≠ 0})) :
    ∫ x, ⟪cov.diracOperator c σ x, τ x⟫ ∂riemannianVolume I M =
      ∫ x, ⟪σ x, cov.diracOperator c τ x⟫ ∂riemannianVolume I M := by
  rw [integral_congr_ae (.of_forall fun x ↦ real_inner_comm _ _),
    ← hcov.integral_inner_diracOperator_left_eq_right_of_isCompact_left hc hskew hcomp hτ hσ hτc]
  exact integral_congr_ae (.of_forall fun x ↦ real_inner_comm _ _)

/-- **The Dirac operator is formally self-adjoint.** If `∇` is a metric connection compatible with a
smooth Clifford multiplication `c` by skew-adjoint endomorphisms and with the Levi-Civita
connection, then `D` is its own formal adjoint for the Riemannian volume:
`∫ ⟪D σ, τ⟫ dV = ∫ ⟪σ, D τ⟫ dV` whenever `σ` or `τ` has compact support. -/
theorem isFormalAdjoint_smoothDiracOperator (hcov : cov.IsMetricCompatible) :
    (cov.smoothDiracOperator hc).IsFormalAdjoint (cov.smoothDiracOperator hc)
      (riemannianVolume I M) := by
  refine LinearMap.isFormalAdjoint_iff.2 fun σ τ hστ ↦ ?_
  simp only [smoothDiracOperator_apply, ContMDiffSection.tsupport_def] at hστ ⊢
  rcases hστ with hσc | hτc
  · exact hcov.integral_inner_diracOperator_left_eq_right_of_isCompact_left hc hskew hcomp
      σ.contMDiff τ.contMDiff hσc
  · exact hcov.integral_inner_diracOperator_left_eq_right hc hskew hcomp σ.contMDiff τ.contMDiff hτc

/-- **The energy identity of the Dirac operator.** Under the hypotheses of
`CovariantDerivative.IsMetricCompatible.integral_inner_diracOperator_left_eq_right`, for a
compactly supported smooth section `σ`, `∫ ⟪D² σ, σ⟫ dV = ∫ ‖D σ‖² dV`. -/
theorem integral_inner_diracOperator_diracOperator_self (hcov : cov.IsMetricCompatible)
    {σ : Π y : M, V y} (hσ : CMDiff ∞ (T% σ)) (hσc : IsCompact (closure {x | σ x ≠ 0})) :
    ∫ x, ⟪cov.diracOperator c (cov.diracOperator c σ) x, σ x⟫ ∂riemannianVolume I M =
      ∫ x, ‖cov.diracOperator c σ x‖ ^ 2 ∂riemannianVolume I M := by
  rw [hcov.integral_inner_diracOperator_left_eq_right hc hskew hcomp
    (cov.contMDiff_diracOperator hc hσ) hσ hσc]
  simp only [real_inner_self_eq_norm_sq]

end IsMetricCompatible

end FormalAdjoint

end CovariantDerivative
