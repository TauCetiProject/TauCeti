/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.DifferentialOperator.FormalAdjoint.Basic
public import TauCeti.Geometry.Manifold.DifferentialOperator.LaplaceType.Section
public import TauCeti.Geometry.Manifold.DifferentialOperator.PrincipalSymbol.Section
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.RoughLaplacian.Energy
import TauCeti.Geometry.Manifold.Riemannian.Basic
import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.LeviCivita.Regularity
import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.RoughLaplacian.Commutator
import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.SecondCovariantDerivative.Hom
import TauCeti.Geometry.Manifold.VectorBundle.Riemannian.ChartGram
import TauCeti.Geometry.Manifold.VectorBundle.Section.Extension

/-!
# The rough Laplacian as a differential operator on smooth sections

Let `∇` be a smooth connection on a smooth vector bundle `V` over a manifold `M` with a smooth
Riemannian metric, and `∇ᵀ` a smooth connection on the tangent bundle. The rough Laplacian
`∇*∇ σ = -tr_g ∇²σ` (`CovariantDerivative.roughLaplacian`) of a smooth section `σ` is again a
smooth section (`CovariantDerivative.contMDiff_roughLaplacian`): near a point `x` it is the finite
sum `-∑ᵢ ∇²σ(Fᵢ, Dᵢ)` over the chart frame `Fᵢ` and its metric-dual frame `Dᵢ`, which depend
smoothly on the point. So `∇*∇` is a real-linear endomorphism of the smooth sections
(`CovariantDerivative.smoothRoughLaplacian`), the operator on the carrier
`Γ(V) →ₗ[ℝ] Γ(V)` of differential operators between sections, principal symbols and formal
adjoints.

On this carrier it is a differential operator of order at most two in Grothendieck's sense
(`TauCeti.differentialOperators`): its double commutators with multiplication by smooth
functions `f` and `g` are multiplication by `-2 ⟪grad f, grad g⟫`
(`CovariantDerivative.roughLaplacian_smul_smul_sub`), an operator of order zero. Hence its
geometric principal symbol (`TauCeti.sectionPrincipalSymbol`) is

`σ_geom(∇*∇)(ξ) = -‖ξ‖² Id`,

equivalently `σ_F(∇*∇)(ξ) = ‖ξ‖² Id` in the Fourier convention, where `∂ⱼ` has symbol `i ξⱼ`.
This is the symbol of an operator of Laplace type with constant `1`
(`CovariantDerivative.isSectionLaplaceType_smoothRoughLaplacian`). For a metric connection
`∇`, the Levi-Civita connection `∇ᵀ` and a manifold without boundary, the energy identity makes
`∇*∇` its own formal adjoint for the Riemannian volume
(`CovariantDerivative.IsMetricCompatible.isFormalAdjoint_smoothRoughLaplacian`).

## Main definitions and results

* `CovariantDerivative.contMDiff_roughLaplacian`: the rough Laplacian of every section is smooth.
* `CovariantDerivative.smoothRoughLaplacian`: the rough Laplacian as a real-linear endomorphism of
  the smooth sections.
* `CovariantDerivative.smulCommutator_smoothRoughLaplacian_apply`: with the Levi-Civita
  connection on the tangent bundle, the commutators `[∇*∇, f] σ = -2 ∇_{grad f} σ - (Δ f) σ`.
* `CovariantDerivative.smulCommutator_smulCommutator_smoothRoughLaplacian_apply`: the double
  commutators `[[∇*∇, f], g] σ = -2 ⟪grad f, grad g⟫ σ`.
* `CovariantDerivative.smoothRoughLaplacian_mem_differentialOperators_two`: `∇*∇` has order at
  most two.
* `CovariantDerivative.sectionPrincipalSymbol_smoothRoughLaplacian`: its geometric principal
  symbol is `ξ ↦ -‖ξ‖² Id`.
* `CovariantDerivative.isSectionLaplaceType_smoothRoughLaplacian`: `∇*∇` is of Laplace type with
  constant `1`.
* `CovariantDerivative.IsMetricCompatible.isFormalAdjoint_smoothRoughLaplacian`: for a metric
  connection, `∇*∇` is formally self-adjoint for the Riemannian volume.

## References

* P. B. Gilkey, *The spectral geometry of operators of Dirac and Laplace type*, in Handbook of
  Global Analysis, Elsevier, 2008, §2 (the rough Laplacian is of Laplace type).
* N. Berline, E. Getzler, M. Vergne, *Heat Kernels and Dirac Operators*, Springer, 1992, §2.1
  (generalized Laplacians and connection Laplacians).
-/

public section

open Bundle FiberBundle MeasureTheory Riemannian.Tensor TauCeti
open scoped ContDiff Manifold RealInnerProductSpace

noncomputable section

namespace CovariantDerivative

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [T2Space M] [IsManifold I ∞ M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]

section Operator

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)]
  [∀ x, TopologicalSpace (V x)] [∀ x, IsTopologicalAddGroup (V x)]
  [∀ x, ContinuousSMul ℝ (V x)]
  [FiberBundle F V] [VectorBundle ℝ F V] [ContMDiffVectorBundle ∞ F V I]
  (cov : _root_.CovariantDerivative I F V) [ContMDiffCovariantDerivative cov ∞]
  (covT : _root_.CovariantDerivative I E (TangentSpace I : M → Type _))
  [ContMDiffCovariantDerivative covT ∞]

/-- **The rough Laplacian is smooth.** For a smooth connection `∇` on `V`, a smooth connection
`∇ᵀ` on the tangent bundle and a smooth metric, the rough Laplacian `∇*∇ σ` of every section `σ`
is a smooth section; it is zero when `σ` is not smooth. -/
theorem contMDiff_roughLaplacian (σ : Π y : M, V y) :
    CMDiff ∞ (T% (cov.roughLaplacian covT σ)) := by
  by_cases hσ : CMDiff ∞ (T% σ)
  swap
  · have h0 : cov.roughLaplacian covT σ = 0 :=
      funext (roughLaplacian_of_not_contMDiff cov covT hσ)
    rw [h0]
    exact contMDiff_zeroSection ℝ V
  have : IsManifold I (∞ + 1) M := by simpa using (inferInstance : IsManifold I ∞ M)
  intro x
  set Fr := chartLocalFrame (I := I) x
  set D := chartDualFrame (I := I) x
  have hx : x ∈ (trivializationAt E (TangentSpace I) x).baseSet :=
    mem_baseSet_trivializationAt E _ x
  have hF (i : Fin (Module.finrank ℝ E)) : CMDiffAt ∞ (T% (Fr i)) x :=
    contMDiffAt_chartLocalFrame (n := ∞) x i
  have hD (i : Fin (Module.finrank ℝ E)) : CMDiffAt ∞ (T% (D i)) x :=
    contMDiffAt_chartDualFrame (n := ∞) x hx i
  have h2 := contMDiff_hom_covariantDerivative cov (covT := covT) hσ x
  -- Near `x`, `∇*∇ σ = -∑ᵢ ∇²σ(Fᵢ, Dᵢ)` with smooth frames `Fᵢ` and `Dᵢ`.
  have hsum : CMDiffAt ∞
      (T% (-fun y ↦ ∑ i, covT.hom cov (cov σ) y (Fr i y) (D i y))) x :=
    (ContMDiffAt.sum_section fun i _ ↦
      (h2.clm_bundle_apply (hF i)).clm_bundle_apply (hD i)).neg_section
  refine hsum.congr_of_eventuallyEq ?_
  filter_upwards [(trivializationAt E (TangentSpace I) x).open_baseSet.mem_nhds hx] with y hy
  rw [roughLaplacian_eq_neg_sum_chartDualFrame cov covT x (by simpa using hy)]
  simp [secondCovariantDerivative_eq_hom_apply cov covT hσ, Fr, D]

/-- The rough Laplacian `∇*∇ σ = -tr_g ∇²σ` (`CovariantDerivative.roughLaplacian`) of a smooth
connection `∇` on `V`, built with a smooth connection `∇ᵀ` on the tangent bundle, as a real-linear
endomorphism of the smooth sections of `V`. -/
def smoothRoughLaplacian : Cₛ^∞⟮I; F, V⟯ →ₗ[ℝ] Cₛ^∞⟮I; F, V⟯ where
  toFun σ := ⟨cov.roughLaplacian covT σ, cov.contMDiff_roughLaplacian covT σ⟩
  map_add' σ τ := ContMDiffSection.ext fun x ↦ by
    simpa using cov.roughLaplacian_add covT σ.contMDiff τ.contMDiff x
  map_smul' c σ := ContMDiffSection.ext fun x ↦ by simp

@[simp]
theorem smoothRoughLaplacian_apply (σ : Cₛ^∞⟮I; F, V⟯) (x : M) :
    cov.smoothRoughLaplacian covT σ x = cov.roughLaplacian covT σ x :=
  (rfl)

/-- **The commutator of the rough Laplacian with multiplication.** With the Levi-Civita connection
on the tangent bundle, `[∇*∇, f] σ = ∇*∇(f σ) - f ∇*∇ σ = -2 ∇_{grad f} σ - (Δ f) σ`, where
`Δ = div ∘ grad` is the Laplace–Beltrami operator. The leading part `-2 ∇_{grad f}` of this
first-order operator is where the connection `∇` enters. -/
theorem smulCommutator_smoothRoughLaplacian_apply (f : C^∞⟮I, M; ℝ⟯) (σ : Cₛ^∞⟮I; F, V⟯) (x : M) :
    smulCommutator ℝ f (cov.smoothRoughLaplacian (leviCivitaConnection I M)) σ x =
      -(2 : ℝ) • cov σ x (TauCeti.Manifold.mgradient I f x) -
        TauCeti.Manifold.laplaceBeltrami I f x • σ x := by
  have hfun : ⇑(f • σ) = ⇑f • ⇑σ := funext fun y ↦ ContMDiffSection.smul_apply f σ y
  simp only [smulCommutator_apply_apply, ContMDiffSection.coe_sub, Pi.sub_apply,
    smoothRoughLaplacian_apply, hfun, ContMDiffSection.smul_apply,
    roughLaplacian_smul cov f.contMDiff σ.contMDiff x]
  module

/-- The double commutator of the rough Laplacian with multiplication by smooth functions is
multiplication by `-2` times the inner product of their gradients:
`[[∇*∇, f], g] σ = -2 ⟪grad f, grad g⟫ σ`. -/
theorem smulCommutator_smulCommutator_smoothRoughLaplacian_apply (f g : C^∞⟮I, M; ℝ⟯)
    (σ : Cₛ^∞⟮I; F, V⟯) (x : M) :
    smulCommutator ℝ g (smulCommutator ℝ f (cov.smoothRoughLaplacian covT)) σ x =
      -(2 * ⟪TauCeti.Manifold.mgradient I f x, TauCeti.Manifold.mgradient I g x⟫) • σ x := by
  have hfun (a : C^∞⟮I, M; ℝ⟯) (τ : Cₛ^∞⟮I; F, V⟯) : ⇑(a • τ) = ⇑a • ⇑τ :=
    funext fun y ↦ ContMDiffSection.smul_apply a τ y
  rw [← roughLaplacian_smul_smul_sub cov covT f.contMDiff g.contMDiff σ.contMDiff x]
  simp only [smulCommutator_apply_apply, ContMDiffSection.coe_sub, hfun, Pi.sub_apply,
    Pi.smul_apply', smoothRoughLaplacian_apply]
  module

/-- The rough Laplacian is a differential operator of order at most two on the smooth sections. -/
theorem smoothRoughLaplacian_mem_differentialOperators_two :
    cov.smoothRoughLaplacian covT ∈
      differentialOperators ℝ C^∞⟮I, M; ℝ⟯ Cₛ^∞⟮I; F, V⟯ Cₛ^∞⟮I; F, V⟯ 2 := by
  refine mem_differentialOperators_succ_iff.2 fun f ↦ mem_differentialOperators_succ_iff.2
    fun g ↦ mem_differentialOperators_zero_iff.2 fun a σ ↦ ContMDiffSection.ext fun x ↦ ?_
  simp only [smulCommutator_smulCommutator_smoothRoughLaplacian_apply,
    ContMDiffSection.smul_apply, smul_comm (a x)]

/-- **The principal symbol of the rough Laplacian.** The geometric principal symbol of `∇*∇` is
`ξ ↦ -‖ξ‖² Id`, the norm being the one the metric induces on `T_x*M`; in the Fourier convention
it is `‖ξ‖² Id`, the symbol of an operator of Laplace type with constant `1`. -/
@[simp]
theorem sectionPrincipalSymbol_smoothRoughLaplacian [FiniteDimensional ℝ F] {x : M}
    (hx : I.IsInteriorPoint x) (ξ : TangentSpace I x →L[ℝ] ℝ) :
    sectionPrincipalSymbol I hx
      ⟨cov.smoothRoughLaplacian covT, cov.smoothRoughLaplacian_mem_differentialOperators_two covT⟩
        ξ = -(‖ξ‖ ^ 2) • LinearMap.id := by
  obtain ⟨f, rfl⟩ : ∃ f : C^∞⟮I, M; ℝ⟯, mvfderiv I f x = ξ := ⟨_, mvfderiv_covectorLift hx ξ⟩
  refine LinearMap.ext fun v ↦ ?_
  obtain ⟨σ, rfl⟩ := ContMDiffSection.evalLinearMap_surjective (I := I) (F := F) (V := V) ∞ x v
  rw [ContMDiffSection.evalLinearMap_apply, sectionPrincipalSymbol_mvfderiv, pow_two,
    mul_apply_eq_comp, smulCommutator_smulCommutator_smoothRoughLaplacian_apply,
    real_inner_self_eq_norm_sq, TauCeti.Manifold.norm_mgradient_eq_norm_mvfderiv,
    Nat.factorial_two, LinearMap.smul_apply, LinearMap.id_apply]
  module

/-- **The rough Laplacian is of Laplace type** with constant `1`: its geometric principal symbol
is `-‖ξ‖² Id`. In particular it is elliptic (`TauCeti.IsSectionLaplaceType.isSectionElliptic`). -/
theorem isSectionLaplaceType_smoothRoughLaplacian [FiniteDimensional ℝ F] :
    TauCeti.IsSectionLaplaceType
      ⟨cov.smoothRoughLaplacian covT, cov.smoothRoughLaplacian_mem_differentialOperators_two covT⟩
        1 :=
  TauCeti.isSectionLaplaceType_iff.2
    ⟨one_pos, fun _ hx ξ ↦ by rw [sectionPrincipalSymbol_smoothRoughLaplacian, one_mul]⟩

end Operator

/-! ### Formal self-adjointness -/

section FormalAdjoint

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, NormedAddCommGroup (V x)] [∀ x, InnerProductSpace ℝ (V x)]
  [FiberBundle F V] [VectorBundle ℝ F V] [ContMDiffVectorBundle ∞ F V I]
  [IsContMDiffRiemannianBundle I ∞ F V]
  {cov : _root_.CovariantDerivative I F V} [ContMDiffCovariantDerivative cov ∞]
  [I.Boundaryless] [SigmaCompactSpace M] [MeasurableSpace M] [BorelSpace M]

local instance instIsContinuousRiemannianBundleTangentSpaceRoughLaplacian :
    IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x) :=
  IsContMDiffRiemannianBundle.toIsContinuousRiemannianBundle
    (IB := I) (n := ∞) (F := E) (V := fun x : M ↦ TangentSpace I x)

/-- **The rough Laplacian is formally self-adjoint.** For a metric connection `∇` on a Riemannian
vector bundle over a Riemannian manifold without boundary, with the Levi-Civita connection on the
tangent bundle, `∇*∇` is its own formal adjoint for the Riemannian volume:
`∫ ⟪∇*∇ σ, τ⟫ dV = ∫ ⟪σ, ∇*∇ τ⟫ dV` whenever `σ` or `τ` has compact support. -/
theorem IsMetricCompatible.isFormalAdjoint_smoothRoughLaplacian (hcov : cov.IsMetricCompatible) :
    (cov.smoothRoughLaplacian (leviCivitaConnection I M)).IsFormalAdjoint
      (cov.smoothRoughLaplacian (leviCivitaConnection I M)) (riemannianVolume I M) := by
  refine LinearMap.isFormalAdjoint_iff.2 fun σ τ hστ ↦ ?_
  simp only [smoothRoughLaplacian_apply, ContMDiffSection.tsupport_def] at hστ ⊢
  rcases hστ with hσc | hτc
  · rw [integral_congr_ae (.of_forall fun x ↦ real_inner_comm _ _),
      ← hcov.integral_inner_roughLaplacian_left_eq_right τ.contMDiff σ.contMDiff hσc]
    exact integral_congr_ae (.of_forall fun x ↦ real_inner_comm _ _)
  · exact hcov.integral_inner_roughLaplacian_left_eq_right σ.contMDiff τ.contMDiff hτc

end FormalAdjoint

end CovariantDerivative
