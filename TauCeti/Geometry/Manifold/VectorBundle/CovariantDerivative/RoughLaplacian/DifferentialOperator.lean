/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.DifferentialOperator.FormalAdjoint.Basic
public import TauCeti.Geometry.Manifold.DifferentialOperator.LaplaceType.Section
public import TauCeti.Geometry.Manifold.DifferentialOperator.PrincipalSymbol.Section
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.DifferentialOperator
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.RoughLaplacian.Energy
import TauCeti.Geometry.Manifold.Riemannian.Basic
import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.LeviCivita.Regularity
import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.RoughLaplacian.Commutator
import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.SecondCovariantDerivative.Hom
import TauCeti.Geometry.Manifold.VectorBundle.Riemannian.ChartGram
import TauCeti.Geometry.Manifold.VectorBundle.Section.Extension

/-!
# The formal adjoint and rough Laplacian as differential operators on smooth sections

Let `∇` be a smooth connection on a smooth vector bundle `V` over a manifold `M` with a smooth
Riemannian metric, and `∇ᵀ` a smooth connection on the tangent bundle. Both the formal adjoint
`∇* η = -tr_g ∇η` (`CovariantDerivative.formalAdjoint`) on smooth `V`-valued one-forms and the
rough Laplacian `∇*∇ σ = -tr_g ∇²σ` (`CovariantDerivative.roughLaplacian`) on smooth sections of
`V` preserve smoothness (`CovariantDerivative.contMDiff_formalAdjoint`,
`CovariantDerivative.contMDiff_roughLaplacian`): near a point `x` they are finite sums over the
chart frame `Fᵢ` and its metric-dual frame `Dᵢ`. Hence they bundle as real-linear operators
`CovariantDerivative.smoothFormalAdjoint` and `CovariantDerivative.smoothRoughLaplacian` on
`ContMDiffSection`, related by the operator factorization

`(∇*) ∘ ∇ = ∇*∇`

(`CovariantDerivative.smoothFormalAdjoint_comp_smoothCovariantDerivative`).

In Grothendieck's order filtration (`TauCeti.differentialOperators`), `∇*` has order at most `1`
with commutator `[∇*, f] η = -η(grad f)`, and `∇*∇ = ∇* ∘ ∇` has order at most `2` with double
commutator `[[∇*∇, f], g] σ = -2 ⟪grad f, grad g⟫ σ`. Hence its geometric principal symbol
(`TauCeti.sectionPrincipalSymbol`) is

`σ_geom(∇*∇)(ξ) = -‖ξ‖² Id`,

equivalently `σ_F(∇*∇)(ξ) = ‖ξ‖² Id` in the Fourier convention, making `∇*∇` an operator of
Laplace type with constant `1` (`CovariantDerivative.isSectionLaplaceType_smoothRoughLaplacian`).
For a metric connection `∇`, the Levi-Civita connection `∇ᵀ` and a manifold without boundary,
`smoothFormalAdjoint` is formally adjoint to `smoothCovariantDerivative` and `smoothRoughLaplacian`
is formally self-adjoint for the Riemannian volume.

## Main definitions and results

* `CovariantDerivative.contMDiff_formalAdjoint` and `CovariantDerivative.contMDiff_roughLaplacian`:
  smoothness of `∇*` and `∇*∇`.
* `CovariantDerivative.smoothFormalAdjoint` and `CovariantDerivative.smoothRoughLaplacian`: `∇*`
  and `∇*∇` as real-linear maps on smooth sections, with
  `CovariantDerivative.smoothFormalAdjoint_comp_smoothCovariantDerivative` (`∇* ∘ ∇ = ∇*∇`) and
  support bounds (`tsupport_smoothFormalAdjoint_subset`, `tsupport_smoothRoughLaplacian_subset`).
* `CovariantDerivative.smulCommutator_smoothFormalAdjoint_apply` and
  `CovariantDerivative.smoothFormalAdjoint_mem_differentialOperators_one`: `[∇*, f] η = -η(grad f)`
  and first-order bound for `∇*`.
* `CovariantDerivative.smulCommutator_smoothRoughLaplacian_apply`,
  `CovariantDerivative.smulCommutator_smulCommutator_smoothRoughLaplacian_apply`, and
  `CovariantDerivative.smoothRoughLaplacian_mem_differentialOperators_two`: commutators and
  second-order bound for `∇*∇`.
* `CovariantDerivative.sectionPrincipalSymbol_smoothRoughLaplacian` and
  `CovariantDerivative.isSectionLaplaceType_smoothRoughLaplacian`: principal symbol `-‖ξ‖² Id` and
  Laplace-type property.
* `CovariantDerivative.IsMetricCompatible.integral_inner_smoothFormalAdjoint`,
  `CovariantDerivative.IsMetricCompatible.isFormalAdjoint_smoothRoughLaplacian`, and
  `CovariantDerivative.IsMetricCompatible.smoothRoughLaplacian_eq_zero_iff`: bundled formal
  adjunction, self-adjointness, and harmonic-section characterizations.

## References

* P. B. Gilkey, *The spectral geometry of operators of Dirac and Laplace type*, in Handbook of
  Global Analysis, Elsevier, 2008, §2 (the rough Laplacian is of Laplace type).
* N. Berline, E. Getzler, M. Vergne, *Heat Kernels and Dirac Operators*, Springer, 1992, §2.1
  (generalized Laplacians and connection Laplacians).
-/

public section

open Bundle FiberBundle MeasureTheory Riemannian.Tensor Set TauCeti
open scoped ContDiff Manifold RealInnerProductSpace Topology

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

/-- **The formal adjoint of a smooth connection is smooth.** For smooth connections `∇` on `V` and
`∇ᵀ` on `TM` and a smooth metric, `∇* η` is smooth for every smooth `V`-valued one-form `η`. -/
theorem contMDiff_formalAdjoint {η : Π x : M, TangentSpace I x →L[ℝ] V x}
    (hη : ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] F)) ∞
      (fun x ↦ TotalSpace.mk' (E →L[ℝ] F) (E := fun y ↦ TangentSpace I y →L[ℝ] V y) x (η x))) :
    CMDiff ∞ (T% (cov.formalAdjoint covT η)) := by
  have : IsManifold I (∞ + 1) M := by simpa using (inferInstance : IsManifold I ∞ M)
  have hhom := contMDiff_hom covT cov hη
  intro x
  set Fr := chartLocalFrame (I := I) x
  set D := chartDualFrame (I := I) x
  have hx : x ∈ (trivializationAt E (TangentSpace I) x).baseSet :=
    mem_baseSet_trivializationAt E _ x
  have hF (i : Fin (Module.finrank ℝ E)) : CMDiffAt ∞ (T% (Fr i)) x :=
    contMDiffAt_chartLocalFrame (n := ∞) x i
  have hD (i : Fin (Module.finrank ℝ E)) : CMDiffAt ∞ (T% (D i)) x :=
    contMDiffAt_chartDualFrame (n := ∞) x hx i
  have hsum : CMDiffAt ∞ (T% (-fun y ↦ ∑ i, covT.hom cov η y (Fr i y) (D i y))) x :=
    (ContMDiffAt.sum_section fun i _ ↦
      ((hhom x).clm_bundle_apply (hF i)).clm_bundle_apply (hD i)).neg_section
  refine hsum.congr_of_eventuallyEq ?_
  filter_upwards [(trivializationAt E (TangentSpace I) x).open_baseSet.mem_nhds hx] with y hy
  simp [formalAdjoint_eq_neg_sum_chartDualFrame cov covT x (by simpa using hy), Fr, D]

/-- **The rough Laplacian is smooth.** For a smooth connection `∇` on `V`, a smooth connection
`∇ᵀ` on the tangent bundle and a smooth metric, the rough Laplacian `∇*∇ σ` of every section `σ`
is a smooth section; it is zero when `σ` is not smooth. -/
theorem contMDiff_roughLaplacian (σ : Π y : M, V y) :
    CMDiff ∞ (T% (cov.roughLaplacian covT σ)) := by
  by_cases hσ : CMDiff ∞ (T% σ)
  · rw [roughLaplacian_eq_formalAdjoint cov covT hσ]
    exact cov.contMDiff_formalAdjoint covT (cov.contMDiff_covariantDerivative (by simpa using hσ))
  · have h0 : cov.roughLaplacian covT σ = 0 :=
      funext (roughLaplacian_of_not_contMDiff cov covT hσ)
    rw [h0]
    exact contMDiff_zeroSection ℝ V

/-- The formal adjoint `∇* η = -tr_g ∇η` (`CovariantDerivative.formalAdjoint`) as a real-linear map
from smooth sections of `Hom(TM, V)` to smooth sections of `V`. -/
def smoothFormalAdjoint :
    Cₛ^∞⟮I; E →L[ℝ] F, fun x ↦ TangentSpace I x →L[ℝ] V x⟯ →ₗ[ℝ] Cₛ^∞⟮I; F, V⟯ where
  toFun η := ⟨cov.formalAdjoint covT η, cov.contMDiff_formalAdjoint covT η.contMDiff⟩
  map_add' η₁ η₂ := ContMDiffSection.ext fun _ ↦
    formalAdjoint_add cov covT η₁.mdifferentiableAt η₂.mdifferentiableAt
  map_smul' c _ := ContMDiffSection.ext fun x ↦ formalAdjoint_const_smul cov covT c x

@[simp]
theorem smoothFormalAdjoint_apply
    (η : Cₛ^∞⟮I; E →L[ℝ] F, fun x ↦ TangentSpace I x →L[ℝ] V x⟯) (x : M) :
    cov.smoothFormalAdjoint covT η x = cov.formalAdjoint covT η x :=
  (rfl)

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

/-- **Operator factorization `∇* ∘ ∇ = ∇*∇`** on smooth sections. -/
@[simp]
theorem smoothFormalAdjoint_comp_smoothCovariantDerivative :
    (cov.smoothFormalAdjoint covT).comp cov.smoothCovariantDerivative =
      cov.smoothRoughLaplacian covT := by
  ext σ x
  have hcoe : (⇑(cov.smoothCovariantDerivative σ) : Π y, TangentSpace I y →L[ℝ] V y) = cov σ :=
    funext fun y ↦ cov.smoothCovariantDerivative_apply σ y
  simp only [LinearMap.comp_apply, smoothFormalAdjoint_apply, hcoe, smoothRoughLaplacian_apply,
    roughLaplacian_eq_formalAdjoint cov covT σ.contMDiff]

/-- The formal adjoint does not enlarge the closed support of a smooth one-form. -/
theorem tsupport_smoothFormalAdjoint_subset
    (η : Cₛ^∞⟮I; E →L[ℝ] F, fun x ↦ TangentSpace I x →L[ℝ] V x⟯) :
    (cov.smoothFormalAdjoint covT η).tsupport ⊆ η.tsupport := by
  refine (ContMDiffSection.tsupport_subset_iff η.isClosed_tsupport).2 fun x hx ↦ ?_
  rw [ContMDiffSection.tsupport_def] at hx
  rw [smoothFormalAdjoint_apply]
  exact cov.formalAdjoint_eq_zero_of_notMem_closure covT hx

/-- The rough Laplacian does not enlarge the closed support of a smooth section. -/
theorem tsupport_smoothRoughLaplacian_subset (σ : Cₛ^∞⟮I; F, V⟯) :
    (cov.smoothRoughLaplacian covT σ).tsupport ⊆ σ.tsupport := by
  rw [← smoothFormalAdjoint_comp_smoothCovariantDerivative, LinearMap.comp_apply]
  exact (cov.tsupport_smoothFormalAdjoint_subset covT _).trans
    (cov.tsupport_smoothCovariantDerivative_subset σ)

/-- The formal adjoint preserves compactly supported smooth one-forms. -/
theorem smoothFormalAdjoint_mem_compactlySupported
    {η : Cₛ^∞⟮I; E →L[ℝ] F, fun x ↦ TangentSpace I x →L[ℝ] V x⟯}
    (hη : η ∈
      ContMDiffSection.compactlySupported I (E →L[ℝ] F) ∞ (fun x ↦ TangentSpace I x →L[ℝ] V x)) :
    cov.smoothFormalAdjoint covT η ∈ ContMDiffSection.compactlySupported I F ∞ V := by
  rw [ContMDiffSection.mem_compactlySupported] at hη ⊢
  exact hη.of_isClosed_subset (ContMDiffSection.isClosed_tsupport _)
    (cov.tsupport_smoothFormalAdjoint_subset covT η)

/-- The rough Laplacian preserves compactly supported smooth sections. -/
theorem smoothRoughLaplacian_mem_compactlySupported {σ : Cₛ^∞⟮I; F, V⟯}
    (hσ : σ ∈ ContMDiffSection.compactlySupported I F ∞ V) :
    cov.smoothRoughLaplacian covT σ ∈ ContMDiffSection.compactlySupported I F ∞ V := by
  rw [ContMDiffSection.mem_compactlySupported] at hσ ⊢
  exact hσ.of_isClosed_subset (ContMDiffSection.isClosed_tsupport _)
    (cov.tsupport_smoothRoughLaplacian_subset covT σ)

/-- The commutator `[∇*, f] η` is `-η(grad f)`: the principal symbol `-ι_{ξ♯}` of `∇*`. -/
theorem smulCommutator_smoothFormalAdjoint_apply (f : C^∞⟮I, M; ℝ⟯)
    (η : Cₛ^∞⟮I; E →L[ℝ] F, fun x ↦ TangentSpace I x →L[ℝ] V x⟯) (x : M) :
    smulCommutator ℝ f (cov.smoothFormalAdjoint covT) η x =
      -η x (TauCeti.Manifold.mgradient I f x) := by
  have hcoe : (⇑(f • η) : Π y, TangentSpace I y →L[ℝ] V y) =
      (f : M → ℝ) • (η : Π y, TangentSpace I y →L[ℝ] V y) :=
    funext fun y ↦ ContMDiffSection.smul_apply f η y
  simp only [smulCommutator_apply_apply, ContMDiffSection.coe_sub, Pi.sub_apply,
    ContMDiffSection.smul_apply, smoothFormalAdjoint_apply, hcoe,
    formalAdjoint_smul cov covT (f.contMDiff.mdifferentiableAt (by simp)) η.mdifferentiableAt,
    sub_sub_cancel_left]

/-- The formal adjoint `∇*` has differential-operator order at most `1`. -/
theorem smoothFormalAdjoint_mem_differentialOperators_one :
    cov.smoothFormalAdjoint covT ∈
      differentialOperators ℝ C^∞⟮I, M; ℝ⟯
        Cₛ^∞⟮I; E →L[ℝ] F, fun x ↦ TangentSpace I x →L[ℝ] V x⟯ Cₛ^∞⟮I; F, V⟯ 1 := by
  refine mem_differentialOperators_succ_iff.2 fun f ↦
    mem_differentialOperators_zero_iff.2 fun g η ↦ ContMDiffSection.ext fun x ↦ ?_
  simp only [ContMDiffSection.smul_apply, smulCommutator_smoothFormalAdjoint_apply,
    smul_apply, smul_neg]

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

/-- The rough Laplacian `∇*∇ = ∇* ∘ ∇` is a differential operator of order at most two on the
smooth sections, as the composite of the first-order operators `∇*` and `∇`. -/
theorem smoothRoughLaplacian_mem_differentialOperators_two :
    cov.smoothRoughLaplacian covT ∈
      differentialOperators ℝ C^∞⟮I, M; ℝ⟯ Cₛ^∞⟮I; F, V⟯ Cₛ^∞⟮I; F, V⟯ 2 := by
  rw [← smoothFormalAdjoint_comp_smoothCovariantDerivative]
  exact comp_mem_differentialOperators
    (cov.smoothFormalAdjoint_mem_differentialOperators_one covT)
    cov.smoothCovariantDerivative_mem_differentialOperators_one

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

/-! ### Formal adjunction and self-adjointness -/

section FormalAdjoint

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, NormedAddCommGroup (V x)] [∀ x, InnerProductSpace ℝ (V x)]
  [FiberBundle F V] [VectorBundle ℝ F V] [ContMDiffVectorBundle ∞ F V I]
  [IsContMDiffRiemannianBundle I ∞ F V]
  {cov : _root_.CovariantDerivative I F V} [ContMDiffCovariantDerivative cov ∞]
  [I.Boundaryless]

local instance instIsContinuousRiemannianBundleTangentSpaceRoughLaplacian :
    IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x) :=
  IsContMDiffRiemannianBundle.toIsContinuousRiemannianBundle
    (IB := I) (n := ∞) (F := E) (V := fun x : M ↦ TangentSpace I x)

/-- **Formal adjunction of `smoothFormalAdjoint` and `smoothCovariantDerivative`** on bundled
smooth sections when at least one section is compactly supported. -/
theorem IsMetricCompatible.integral_inner_smoothFormalAdjoint
    [SigmaCompactSpace M] [MeasurableSpace M] [BorelSpace M]
    (hcov : cov.IsMetricCompatible)
    (η : Cₛ^∞⟮I; E →L[ℝ] F, fun x ↦ TangentSpace I x →L[ℝ] V x⟯)
    (τ : Cₛ^∞⟮I; F, V⟯)
    (hsupp : η ∈ ContMDiffSection.compactlySupported I (E →L[ℝ] F) ∞
        (fun x ↦ TangentSpace I x →L[ℝ] V x) ∨
      τ ∈ ContMDiffSection.compactlySupported I F ∞ V) :
    ∫ x, ⟪cov.smoothFormalAdjoint (leviCivitaConnection I M) η x, τ x⟫
        ∂riemannianVolume I M =
      ∫ x, (η x).hilbertSchmidtInner (cov.smoothCovariantDerivative τ x)
        ∂riemannianVolume I M := by
  simp only [ContMDiffSection.mem_compactlySupported, ContMDiffSection.tsupport_def] at hsupp
  simp only [smoothFormalAdjoint_apply, smoothCovariantDerivative_apply]
  exact hcov.integral_inner_formalAdjoint_of_or η.contMDiff τ.contMDiff hsupp

/-- **The rough Laplacian is formally self-adjoint.** For a metric connection `∇` on a Riemannian
vector bundle over a Riemannian manifold without boundary, with the Levi-Civita connection on the
tangent bundle, `∇*∇` is its own formal adjoint for the Riemannian volume:
`∫ ⟪∇*∇ σ, τ⟫ dV = ∫ ⟪σ, ∇*∇ τ⟫ dV` whenever `σ` or `τ` has compact support. -/
theorem IsMetricCompatible.isFormalAdjoint_smoothRoughLaplacian
    [SigmaCompactSpace M] [MeasurableSpace M] [BorelSpace M]
    (hcov : cov.IsMetricCompatible) :
    (cov.smoothRoughLaplacian (leviCivitaConnection I M)).IsFormalAdjoint
      (cov.smoothRoughLaplacian (leviCivitaConnection I M)) (riemannianVolume I M) := by
  refine LinearMap.isFormalAdjoint_iff.2 fun σ τ hστ ↦ ?_
  simp only [smoothRoughLaplacian_apply, ContMDiffSection.tsupport_def] at hστ ⊢
  exact hcov.integral_inner_roughLaplacian_left_eq_right_of_or σ.contMDiff τ.contMDiff hστ

/-- **Bundled characterization of compactly supported rough-harmonic smooth sections.** -/
theorem IsMetricCompatible.smoothRoughLaplacian_eq_zero_iff
    [SigmaCompactSpace M] [MeasurableSpace M] [BorelSpace M]
    (hcov : cov.IsMetricCompatible) (σ : Cₛ^∞⟮I; F, V⟯)
    (hσc : σ ∈ ContMDiffSection.compactlySupported I F ∞ V) :
    cov.smoothRoughLaplacian (leviCivitaConnection I M) σ = 0 ↔
      cov.smoothCovariantDerivative σ = 0 := by
  simp only [ContMDiffSection.mem_compactlySupported, ContMDiffSection.tsupport_def] at hσc
  simpa only [ContMDiffSection.ext_iff, smoothRoughLaplacian_apply,
    smoothCovariantDerivative_apply, ContMDiffSection.coe_zero, Pi.zero_apply, funext_iff] using
    hcov.roughLaplacian_eq_zero_iff σ.contMDiff hσc

/-- **Bundled characterization of rough-harmonic smooth sections on a closed manifold.** -/
theorem IsMetricCompatible.smoothRoughLaplacian_eq_zero_iff_of_compactSpace
    [CompactSpace M] [MeasurableSpace M] [BorelSpace M]
    (hcov : cov.IsMetricCompatible) (σ : Cₛ^∞⟮I; F, V⟯) :
    cov.smoothRoughLaplacian (leviCivitaConnection I M) σ = 0 ↔
      cov.smoothCovariantDerivative σ = 0 :=
  hcov.smoothRoughLaplacian_eq_zero_iff σ (by simp)

end FormalAdjoint

end CovariantDerivative
