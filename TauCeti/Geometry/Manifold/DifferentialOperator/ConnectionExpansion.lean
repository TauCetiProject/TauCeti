/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.DifferentialOperator.PrincipalSymbol.Section
public import TauCeti.Geometry.Manifold.DifferentialOperator.Section
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Basic
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Regularity
import TauCeti.Geometry.Manifold.MFDeriv.Localized
import TauCeti.Geometry.Manifold.VectorBundle.Section.Extension
import TauCeti.Geometry.Manifold.VectorField.CoordinateFrame
import TauCeti.Topology.Algebra.Module.FiniteDimension

/-!
# First-order operators through a connection

Let `V` and `W` be smooth real vector bundles over a boundaryless finite-dimensional manifold `M`,
with `V` of finite rank, and let `∇` be a smooth connection on `V`. This file proves that the
differential operators `P : Γ(V) → Γ(W)` of order at most one, in Grothendieck's sense
(`TauCeti.differentialOperators`), are exactly the operators

`P σ = A(∇σ) + B σ`

for a bundle map `A : Hom(TM, V) → W`, sending smooth `V`-valued one-forms to smooth sections of
`W`, and a smooth bundle map `B : V → W`, and that `A` and `B` are unique. The leading
coefficient `A` does not depend on the connection: it is determined by the principal symbol of
`P`,

`A(ξ ⊗ v) = σ(P)(ξ) v`,

where `ξ ⊗ v` is the rank-one map `w ↦ ξ(w) v` (`ContinuousLinearMap.smulRight`). This is the
first-order case of the expansion of a differential operator of order `m` in the symmetrized
covariant derivatives `∇ʲ`, `j ≤ m`.

* At each point `x`, `A_x` is the contraction of the principal symbol with a one-form:
  `A_x(L) = ∑ₖ σ(P)(eᵏ)(L eₖ)` for dual bases `(eₖ)`, `(eᵏ)` of `T_xM` and `T_x*M`
  (`TauCeti.sectionPrincipalCoefficient`). It is the unique linear map with
  `A_x(ξ ⊗ v) = σ(P)(ξ) v` (`TauCeti.eq_sectionPrincipalCoefficient_iff`), since rank-one maps
  span `Hom(T_xM, V_x)`. Near each point it is given by commutators of `P`: for functions `u_j` and
  vector fields `X_j` whose values are dual bases nearby (cut-off coordinate functions and the
  coordinate frame of a chart), `A(θ) = ∑ⱼ [P, u_j] (θ(X_j))`. So `A` sends smooth one-forms to
  smooth sections (`TauCeti.contMDiff_sectionPrincipalCoefficient`).
* The operator `σ ↦ A(∇σ)` (`CovariantDerivative.principalPart`) has the same commutators with
  multiplication by functions as `P`, by the Leibniz rule `∇(fσ) = f ∇σ + df ⊗ σ`. Hence
  `P - A ∘ ∇` is linear over the smooth functions
  (`CovariantDerivative.sub_principalPart_mem_differentialOperators_zero`): it is the bundle map
  `B` (`CovariantDerivative.zerothCoefficient`), which is smooth
  (`CovariantDerivative.contMDiff_zerothCoefficient`).
* Changing the connection to `∇'` keeps `A` and changes `B` to `B + A ∘ (∇ - ∇')`
  (`CovariantDerivative.zerothCoefficient_apply_eq_add`).

## Main definitions

* `TauCeti.sectionPrincipalCoefficient I hx P`: the leading coefficient `A_x`, a linear map from
  `Hom(T_xM, V_x)` to `W_x`.
* `CovariantDerivative.principalPart cov P`: the operator `σ ↦ A(∇σ)`.
* `CovariantDerivative.zerothCoefficient cov P x`: the coefficient `B_x : V_x → W_x`.

## Main results

* `TauCeti.sectionPrincipalCoefficient_smulRight`: `A_x(ξ ⊗ v) = σ(P)(ξ) v`.
* `CovariantDerivative.apply_eq_sectionPrincipalCoefficient_add_zerothCoefficient`: the
  expansion `(P σ)(x) = A_x((∇σ)(x)) + B_x(σ(x))`.
* `CovariantDerivative.forall_apply_eq_add_iff`: uniqueness of the coefficients.
* `CovariantDerivative.mem_differentialOperators_one_of_forall_apply_eq_add`,
  `CovariantDerivative.sectionPrincipalSymbol_eq_of_forall_apply_eq_add`: conversely, an operator
  of the form `A ∘ ∇ + B` has order at most one and principal symbol `ξ ↦ A(ξ ⊗ ·)`.

## References

* I. Kolář, P. W. Michor, J. Slovák, *Natural Operations in Differential Geometry*, Springer,
  1993, §§12, 19 (jets and linear differential operators between vector bundles).
* R. O. Wells, *Differential Analysis on Complex Manifolds*, 3rd ed., Springer GTM 65 (2008),
  Chapter IV, §2 (differential operators and their symbols).
-/

public section

noncomputable section

open Bundle Filter
open scoped ContDiff Manifold Topology

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)] [∀ x, TopologicalSpace (V x)]
  [∀ x, IsTopologicalAddGroup (V x)] [∀ x, ContinuousSMul ℝ (V x)]
  [FiberBundle F V] [VectorBundle ℝ F V] [ContMDiffVectorBundle ∞ F V I]
  {F' : Type*} [NormedAddCommGroup F'] [NormedSpace ℝ F']
  {W : M → Type*} [TopologicalSpace (TotalSpace F' W)]
  [∀ x, AddCommGroup (W x)] [∀ x, Module ℝ (W x)] [∀ x, TopologicalSpace (W x)]
  [FiberBundle F' W] [VectorBundle ℝ F' W]
  {x : M}

/-! ### The leading coefficient at a point -/

variable (I) in
/-- **The leading coefficient of a first-order operator** at an interior point `x`: the linear
map `A_x : Hom(T_xM, V_x) → W_x`, `A_x(L) = ∑ₖ σ(P)(eᵏ)(L eₖ)`, contracting a `V_x`-valued
one-form `L` with the principal symbol `σ(P)` of an operator `P : Γ(V) → Γ(W)` of order at most
one, for a basis `(eₖ)` of `T_xM` with dual basis `(eᵏ)`. It does not depend on the basis: it is
the unique linear map with `A_x(ξ ⊗ v) = σ(P)(ξ) v` (`TauCeti.eq_sectionPrincipalCoefficient_iff`),
and for any smooth connection `∇` on `V` over a boundaryless manifold, `P σ = A(∇σ) + B σ` for a
bundle map `B`
(`CovariantDerivative.apply_eq_sectionPrincipalCoefficient_add_zerothCoefficient`). -/
def sectionPrincipalCoefficient (hx : I.IsInteriorPoint x)
    (P : differentialOperators ℝ C^∞⟮I, M; ℝ⟯ Cₛ^∞⟮I; F, V⟯ Cₛ^∞⟮I; F', W⟯ 1) :
    (TangentSpace I x →L[ℝ] V x) →ₗ[ℝ] W x where
  toFun L :=
    let b := Module.finBasis ℝ (TangentSpace I x)
    ∑ k, sectionPrincipalSymbol I hx P (LinearMap.toContinuousLinearMap (b.coord k)) (L (b k))
  map_add' L L' := by simp [Finset.sum_add_distrib]
  map_smul' a L := by simp [Finset.smul_sum]

omit [∀ x, IsTopologicalAddGroup (V x)] [∀ x, ContinuousSMul ℝ (V x)] in
/-- For a family of covectors `cⱼ` and vectors `eⱼ` with `∑ⱼ ξ(eⱼ) cⱼ = ξ` for every covector
`ξ`, the contraction `∑ⱼ σ(P)(cⱼ)(eⱼ ⬝)` sends `ξ ⊗ v` to `σ(P)(ξ) v`. -/
private theorem sum_sectionPrincipalSymbol_smul (hx : I.IsInteriorPoint x)
    (P : differentialOperators ℝ C^∞⟮I, M; ℝ⟯ Cₛ^∞⟮I; F, V⟯ Cₛ^∞⟮I; F', W⟯ 1)
    {ι : Type*} [Fintype ι] (c : ι → TangentSpace I x →L[ℝ] ℝ) (e : ι → TangentSpace I x)
    (hce : ∀ ξ : TangentSpace I x →L[ℝ] ℝ, ∑ j, ξ (e j) • c j = ξ)
    (ξ : TangentSpace I x →L[ℝ] ℝ) (v : V x) :
    ∑ j, sectionPrincipalSymbol I hx P (c j) (ξ (e j) • v) =
      sectionPrincipalSymbol I hx P ξ v := by
  conv_rhs => rw [← hce ξ]
  simp only [map_smul, ← sectionPrincipalSymbolₗ_apply, map_sum, LinearMap.sum_apply,
    LinearMap.smul_apply]

/-- **The leading coefficient on rank-one maps** is the principal symbol:
`A_x(ξ ⊗ v) = σ(P)(ξ) v`. -/
@[simp]
theorem sectionPrincipalCoefficient_smulRight (hx : I.IsInteriorPoint x)
    (P : differentialOperators ℝ C^∞⟮I, M; ℝ⟯ Cₛ^∞⟮I; F, V⟯ Cₛ^∞⟮I; F', W⟯ 1)
    (ξ : TangentSpace I x →L[ℝ] ℝ) (v : V x) :
    sectionPrincipalCoefficient I hx P (ξ.smulRight v) = sectionPrincipalSymbol I hx P ξ v := by
  set b := Module.finBasis ℝ (TangentSpace I x)
  rw [← sum_sectionPrincipalSymbol_smul hx P (fun k ↦ LinearMap.toContinuousLinearMap (b.coord k))
    b (fun ζ ↦ ?_) ξ v]
  · simp [sectionPrincipalCoefficient, b]
  · ext w
    simpa using LinearMap.congr_fun (b.sum_dual_apply_smul_coord ζ.toLinearMap) w

/-- **Characterization of the leading coefficient.** It is the unique linear map on
`Hom(T_xM, V_x)` sending each rank-one map `ξ ⊗ v` to `σ(P)(ξ) v`. -/
theorem eq_sectionPrincipalCoefficient_iff (hx : I.IsInteriorPoint x)
    (P : differentialOperators ℝ C^∞⟮I, M; ℝ⟯ Cₛ^∞⟮I; F, V⟯ Cₛ^∞⟮I; F', W⟯ 1)
    (T : (TangentSpace I x →L[ℝ] V x) →ₗ[ℝ] W x) :
    T = sectionPrincipalCoefficient I hx P ↔
      ∀ (ξ : TangentSpace I x →L[ℝ] ℝ) (v : V x),
        T (ξ.smulRight v) = sectionPrincipalSymbol I hx P ξ v :=
  ⟨fun h ξ v ↦ h ▸ sectionPrincipalCoefficient_smulRight hx P ξ v, fun h ↦
    LinearMap.ext_smulRight fun ξ v ↦ by rw [h, sectionPrincipalCoefficient_smulRight]⟩

/-- For finitely many covectors `cⱼ` and vectors `eⱼ` at `x` with `∑ⱼ ξ(eⱼ) cⱼ = ξ` for every
covector `ξ`, for instance dual bases, the leading coefficient is
`A_x(L) = ∑ⱼ σ(P)(cⱼ)(L eⱼ)`. -/
theorem sectionPrincipalCoefficient_apply_eq_sum (hx : I.IsInteriorPoint x)
    (P : differentialOperators ℝ C^∞⟮I, M; ℝ⟯ Cₛ^∞⟮I; F, V⟯ Cₛ^∞⟮I; F', W⟯ 1)
    {ι : Type*} [Fintype ι] (c : ι → TangentSpace I x →L[ℝ] ℝ) (e : ι → TangentSpace I x)
    (hce : ∀ ξ : TangentSpace I x →L[ℝ] ℝ, ∑ j, ξ (e j) • c j = ξ)
    (L : TangentSpace I x →L[ℝ] V x) :
    sectionPrincipalCoefficient I hx P L = ∑ j, sectionPrincipalSymbol I hx P (c j) (L (e j)) := by
  let T : (TangentSpace I x →L[ℝ] V x) →ₗ[ℝ] W x :=
    { toFun L := ∑ j, sectionPrincipalSymbol I hx P (c j) (L (e j))
      map_add' L L' := by simp [Finset.sum_add_distrib]
      map_smul' a L := by simp [Finset.smul_sum] }
  have hT : T = sectionPrincipalCoefficient I hx P :=
    (eq_sectionPrincipalCoefficient_iff hx P T).2 fun ξ v ↦ by
      simpa [T] using sum_sectionPrincipalSymbol_smul hx P c e hce ξ v
  simp [← hT, T]

/-! ### Smoothness of the leading coefficient -/

/-- **The leading coefficient sends smooth one-forms to smooth sections.** On a boundaryless
manifold, the leading coefficient of an operator of order at most one sends a smooth `V`-valued
one-form `θ` to the smooth section `x ↦ A_x(θ x)` of `W`. -/
theorem contMDiff_sectionPrincipalCoefficient [BoundarylessManifold I M]
    (P : differentialOperators ℝ C^∞⟮I, M; ℝ⟯ Cₛ^∞⟮I; F, V⟯ Cₛ^∞⟮I; F', W⟯ 1)
    {θ : Π x : M, TangentSpace I x →L[ℝ] V x}
    (hθ : ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] F)) ∞
      (fun x ↦ TotalSpace.mk' (E →L[ℝ] F) (E := fun y ↦ TangentSpace I y →L[ℝ] V y) x (θ x))) :
    ContMDiff I (I.prod 𝓘(ℝ, F')) ∞
      (fun x ↦ TotalSpace.mk' F' x
        (sectionPrincipalCoefficient I BoundarylessManifold.isInteriorPoint P (θ x))) := by
  -- Near each point, `A(θ)` is the sum of the commutators `[P, u_j] (θ(X_j))`, for cut-off
  -- coordinate functions `u_j` and the coordinate frame `X_j` of a chart, dual bases there.
  intro x₀
  obtain ⟨u, X, hu⟩ := Manifold.exists_eventually_sum_smul_mvfderiv_eq (I := I) x₀
  -- The smooth sections `θ(X_j)` of `V`, and the sum of the commutators of `P` applied to them.
  let τ (j : Fin (Module.finrank ℝ E)) : Cₛ^∞⟮I; F, V⟯ :=
    ⟨fun y ↦ θ y (X j y), hθ.clm_bundle_apply (X j).contMDiff⟩
  let S : Cₛ^∞⟮I; F', W⟯ := ∑ j, ((P : Cₛ^∞⟮I; F, V⟯ →ₗ[ℝ] Cₛ^∞⟮I; F', W⟯) (u j • τ j) -
    u j • (P : Cₛ^∞⟮I; F, V⟯ →ₗ[ℝ] Cₛ^∞⟮I; F', W⟯) (τ j))
  refine (S.contMDiff x₀).congr_of_eventuallyEq ?_
  filter_upwards [hu] with y hy
  refine congrArg (TotalSpace.mk' F' y) ?_
  rw [sectionPrincipalCoefficient_apply_eq_sum _ P (fun j ↦ mvfderiv I (u j) y)
    (fun j ↦ X j y) hy]
  simp only [S, ContMDiffSection.coe_sum, Finset.sum_apply, ContMDiffSection.coe_sub,
    Pi.sub_apply, ContMDiffSection.smul_apply]
  exact Finset.sum_congr rfl fun j _ ↦ sectionPrincipalSymbol_mvfderiv_of_order_one _ P (u j) (τ j)

end TauCeti

/-! ### The expansion through a connection -/

namespace CovariantDerivative

open TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  [BoundarylessManifold I M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)] [∀ x, TopologicalSpace (V x)]
  [∀ x, IsTopologicalAddGroup (V x)] [∀ x, ContinuousSMul ℝ (V x)]
  [FiberBundle F V] [VectorBundle ℝ F V] [ContMDiffVectorBundle ∞ F V I]
  {F' : Type*} [NormedAddCommGroup F'] [NormedSpace ℝ F']
  {W : M → Type*} [TopologicalSpace (TotalSpace F' W)]
  [∀ x, AddCommGroup (W x)] [∀ x, Module ℝ (W x)] [∀ x, TopologicalSpace (W x)]
  [FiberBundle F' W] [VectorBundle ℝ F' W]
  (cov : CovariantDerivative I F V) [ContMDiffCovariantDerivative cov ∞]

/-- **The principal part of a first-order operator relative to a connection**: the operator
`σ ↦ A(∇σ)` on smooth sections, where `A` is the leading coefficient
`TauCeti.sectionPrincipalCoefficient` of an operator `P : Γ(V) → Γ(W)` of order at most one. Its
commutators with multiplication by functions are those of `P`
(`CovariantDerivative.principalPart_smul_apply`), so `P` minus it is a bundle map
(`CovariantDerivative.sub_principalPart_mem_differentialOperators_zero`). -/
def principalPart (P : differentialOperators ℝ C^∞⟮I, M; ℝ⟯ Cₛ^∞⟮I; F, V⟯ Cₛ^∞⟮I; F', W⟯ 1) :
    Cₛ^∞⟮I; F, V⟯ →ₗ[ℝ] Cₛ^∞⟮I; F', W⟯ where
  toFun σ := ⟨fun x ↦ sectionPrincipalCoefficient I BoundarylessManifold.isInteriorPoint P
      (cov σ x),
    contMDiff_sectionPrincipalCoefficient P
      (cov.contMDiff_covariantDerivative (by simpa using σ.contMDiff))⟩
  map_add' σ τ := ContMDiffSection.ext fun x ↦ by
    simp [cov.isCovariantDerivativeOnUniv.add σ.mdifferentiableAt τ.mdifferentiableAt]
  map_smul' c σ := ContMDiffSection.ext fun x ↦ by
    simp [cov.isCovariantDerivativeOnUniv.smul_const c σ.mdifferentiableAt]

@[simp]
theorem principalPart_apply
    (P : differentialOperators ℝ C^∞⟮I, M; ℝ⟯ Cₛ^∞⟮I; F, V⟯ Cₛ^∞⟮I; F', W⟯ 1)
    (σ : Cₛ^∞⟮I; F, V⟯) (x : M) :
    cov.principalPart P σ x =
      sectionPrincipalCoefficient I BoundarylessManifold.isInteriorPoint P (cov σ x) :=
  (rfl)

/-- The commutator of the principal part with multiplication by `f` is the principal symbol of
`P` at `df`: `A(∇(f σ)) = f A(∇σ) + σ(P)(df) σ`. -/
theorem principalPart_smul_apply
    (P : differentialOperators ℝ C^∞⟮I, M; ℝ⟯ Cₛ^∞⟮I; F, V⟯ Cₛ^∞⟮I; F', W⟯ 1)
    (f : C^∞⟮I, M; ℝ⟯) (σ : Cₛ^∞⟮I; F, V⟯) (x : M) :
    cov.principalPart P (f • σ) x = f x • cov.principalPart P σ x +
      sectionPrincipalSymbol I BoundarylessManifold.isInteriorPoint P (mvfderiv I f x) (σ x) := by
  simp [cov.apply_smul]

/-- **A first-order operator minus its principal part is a bundle map.** For an operator `P` of
order at most one and a smooth connection `∇`, the operator `σ ↦ P σ - A(∇σ)` is linear over the
smooth functions. -/
theorem sub_principalPart_mem_differentialOperators_zero
    (P : differentialOperators ℝ C^∞⟮I, M; ℝ⟯ Cₛ^∞⟮I; F, V⟯ Cₛ^∞⟮I; F', W⟯ 1) :
    (P : Cₛ^∞⟮I; F, V⟯ →ₗ[ℝ] Cₛ^∞⟮I; F', W⟯) - cov.principalPart P ∈
      differentialOperators ℝ C^∞⟮I, M; ℝ⟯ Cₛ^∞⟮I; F, V⟯ Cₛ^∞⟮I; F', W⟯ 0 := by
  refine mem_differentialOperators_zero_iff.2 fun f σ ↦ ContMDiffSection.ext fun x ↦ ?_
  have hP := sectionPrincipalSymbol_mvfderiv_of_order_one
    (BoundarylessManifold.isInteriorPoint (I := I) (x := x)) P f σ
  simp only [LinearMap.sub_apply, ContMDiffSection.coe_sub, Pi.sub_apply,
    ContMDiffSection.smul_apply, principalPart_smul_apply, hP]
  module

/-- **The zeroth-order coefficient of a first-order operator relative to a connection**: the
fibre map `B_x : V_x → W_x` of the bundle map `P - A ∘ ∇`, so that
`(P σ)(x) = A_x((∇σ)(x)) + B_x(σ(x))`
(`CovariantDerivative.apply_eq_sectionPrincipalCoefficient_add_zerothCoefficient`). -/
def zerothCoefficient
    (P : differentialOperators ℝ C^∞⟮I, M; ℝ⟯ Cₛ^∞⟮I; F, V⟯ Cₛ^∞⟮I; F', W⟯ 1) (x : M) :
    V x →ₗ[ℝ] W x :=
  smoothSectionFiberMap x
    { toFun := (P : Cₛ^∞⟮I; F, V⟯ →ₗ[ℝ] Cₛ^∞⟮I; F', W⟯) - cov.principalPart P
      map_add' := map_add _
      map_smul' := mem_differentialOperators_zero_iff.1
        (cov.sub_principalPart_mem_differentialOperators_zero P) }

/-- The zeroth-order coefficient at `x`, on the value of a smooth section `σ`, is the value of
`P σ - A(∇σ)` at `x`. -/
theorem zerothCoefficient_apply
    (P : differentialOperators ℝ C^∞⟮I, M; ℝ⟯ Cₛ^∞⟮I; F, V⟯ Cₛ^∞⟮I; F', W⟯ 1)
    (σ : Cₛ^∞⟮I; F, V⟯) (x : M) :
    cov.zerothCoefficient P x (σ x) =
      (P : Cₛ^∞⟮I; F, V⟯ →ₗ[ℝ] Cₛ^∞⟮I; F', W⟯) σ x - cov.principalPart P σ x :=
  smoothSectionFiberMap_apply x _ σ

/-- **The expansion of a first-order operator through a connection.** For an operator `P` of order
at most one and a smooth connection `∇`,

`(P σ)(x) = A_x((∇σ)(x)) + B_x(σ(x))`,

where the leading coefficient `A` (`TauCeti.sectionPrincipalCoefficient`) is determined by the
principal symbol of `P` and does not depend on `∇`, and `B` is the zeroth-order coefficient. -/
theorem apply_eq_sectionPrincipalCoefficient_add_zerothCoefficient
    (P : differentialOperators ℝ C^∞⟮I, M; ℝ⟯ Cₛ^∞⟮I; F, V⟯ Cₛ^∞⟮I; F', W⟯ 1)
    (σ : Cₛ^∞⟮I; F, V⟯) (x : M) :
    (P : Cₛ^∞⟮I; F, V⟯ →ₗ[ℝ] Cₛ^∞⟮I; F', W⟯) σ x =
      sectionPrincipalCoefficient I BoundarylessManifold.isInteriorPoint P (cov σ x) +
        cov.zerothCoefficient P x (σ x) := by
  rw [zerothCoefficient_apply, principalPart_apply, add_sub_cancel]

/-- **The zeroth-order coefficient is a smooth bundle map**: its map of total spaces
`TotalSpace F V → TotalSpace F' W` is smooth. -/
theorem contMDiff_zerothCoefficient [ContMDiffVectorBundle ∞ F' W I]
    (P : differentialOperators ℝ C^∞⟮I, M; ℝ⟯ Cₛ^∞⟮I; F, V⟯ Cₛ^∞⟮I; F', W⟯ 1) :
    ContMDiff (I.prod 𝓘(ℝ, F)) (I.prod 𝓘(ℝ, F')) ∞
      (fun p : TotalSpace F V ↦ (⟨p.proj, cov.zerothCoefficient P p.proj p.snd⟩ :
        TotalSpace F' W)) := by
  obtain ⟨ϕ, hϕ, h⟩ := mem_differentialOperators_zero_iff_exists_eq_mapLinearMap.1
    (cov.sub_principalPart_mem_differentialOperators_zero P)
  have hB (x : M) : cov.zerothCoefficient P x = ϕ x :=
    (smoothSectionFiberMap_eq_iff x _ _).2 fun σ ↦ by
      simp [h, ContMDiffSection.mapLinearMap_apply]
  simpa only [hB] using hϕ

/-- **The expansion as operators**: a first-order operator is the principal part relative to a
connection plus the action of its smooth zeroth-order coefficient. -/
theorem eq_principalPart_add_mapLinearMap [ContMDiffVectorBundle ∞ F' W I]
    (P : differentialOperators ℝ C^∞⟮I, M; ℝ⟯ Cₛ^∞⟮I; F, V⟯ Cₛ^∞⟮I; F', W⟯ 1) :
    (P : Cₛ^∞⟮I; F, V⟯ →ₗ[ℝ] Cₛ^∞⟮I; F', W⟯) = cov.principalPart P +
      ContMDiffSection.mapLinearMap (cov.zerothCoefficient P) (cov.contMDiff_zerothCoefficient P) :=
  LinearMap.ext fun σ ↦ ContMDiffSection.ext fun x ↦ by
    simp [ContMDiffSection.mapLinearMap_apply, zerothCoefficient_apply]

/-! ### Uniqueness, the converse and changes of connection -/

omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] [T2Space M] [BoundarylessManifold I M]
  [FiniteDimensional ℝ F] [ContMDiffVectorBundle ∞ F V I] [ContMDiffCovariantDerivative cov ∞] in
/-- For an operator of the form `A ∘ ∇ + B`, the commutator with multiplication by `f` is
`σ ↦ A(df ⊗ σ)`. -/
private theorem apply_smul_sub_of_forall_apply_eq_add {Q : Cₛ^∞⟮I; F, V⟯ →ₗ[ℝ] Cₛ^∞⟮I; F', W⟯}
    (A : ∀ x, (TangentSpace I x →L[ℝ] V x) →ₗ[ℝ] W x) (B : ∀ x, V x →ₗ[ℝ] W x)
    (h : ∀ σ x, Q σ x = A x (cov σ x) + B x (σ x)) (f : C^∞⟮I, M; ℝ⟯) (σ : Cₛ^∞⟮I; F, V⟯)
    (x : M) : Q (f • σ) x - f x • Q σ x = A x ((mvfderiv I f x).smulRight (σ x)) := by
  rw [h, h, cov.apply_smul, ContMDiffSection.smul_apply]
  simp only [map_add, map_smul]
  module

omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] [T2Space M] [BoundarylessManifold I M]
  [FiniteDimensional ℝ F] [ContMDiffVectorBundle ∞ F V I] [ContMDiffCovariantDerivative cov ∞] in
/-- **Operators of the form `A ∘ ∇ + B` have order at most one.** If `(Q σ)(x) = A_x((∇σ)(x)) +
B_x(σ(x))` for all smooth sections `σ`, for any fibrewise linear maps `A_x` and `B_x`, then `Q`
is a differential operator of order at most one. -/
theorem mem_differentialOperators_one_of_forall_apply_eq_add
    {Q : Cₛ^∞⟮I; F, V⟯ →ₗ[ℝ] Cₛ^∞⟮I; F', W⟯}
    (A : ∀ x, (TangentSpace I x →L[ℝ] V x) →ₗ[ℝ] W x) (B : ∀ x, V x →ₗ[ℝ] W x)
    (h : ∀ σ x, Q σ x = A x (cov σ x) + B x (σ x)) :
    Q ∈ differentialOperators ℝ C^∞⟮I, M; ℝ⟯ Cₛ^∞⟮I; F, V⟯ Cₛ^∞⟮I; F', W⟯ 1 := by
  refine mem_differentialOperators_succ_iff.2 fun a ↦ mem_differentialOperators_zero_iff.2
    fun f σ ↦ ContMDiffSection.ext fun x ↦ ?_
  have hsmul : (mvfderiv I a x).smulRight (f x • σ x) =
      f x • (mvfderiv I a x).smulRight (σ x) := by
    ext w
    simp only [ContinuousLinearMap.smulRight_apply, FunLike.coe_smul, Pi.smul_apply]
    exact smul_comm _ _ _
  simp only [smulCommutator_apply_apply, ContMDiffSection.coe_sub, Pi.sub_apply,
    ContMDiffSection.smul_apply, apply_smul_sub_of_forall_apply_eq_add cov A B h, hsmul, map_smul]

/-- **Uniqueness of the coefficients.** An operator `P` of order at most one satisfies
`(P σ)(x) = A_x((∇σ)(x)) + B_x(σ(x))` for all smooth sections `σ` exactly when `A` is its leading
coefficient and `B` its zeroth-order coefficient relative to `∇`. -/
theorem forall_apply_eq_add_iff
    (P : differentialOperators ℝ C^∞⟮I, M; ℝ⟯ Cₛ^∞⟮I; F, V⟯ Cₛ^∞⟮I; F', W⟯ 1)
    (A : ∀ x, (TangentSpace I x →L[ℝ] V x) →ₗ[ℝ] W x) (B : ∀ x, V x →ₗ[ℝ] W x) :
    (∀ σ x, (P : Cₛ^∞⟮I; F, V⟯ →ₗ[ℝ] Cₛ^∞⟮I; F', W⟯) σ x = A x (cov σ x) + B x (σ x)) ↔
      (∀ x, A x = sectionPrincipalCoefficient I BoundarylessManifold.isInteriorPoint P) ∧
        ∀ x, B x = cov.zerothCoefficient P x := by
  refine ⟨fun h ↦ ?_, fun ⟨hA, hB⟩ σ x ↦ by
    rw [hA, hB, cov.apply_eq_sectionPrincipalCoefficient_add_zerothCoefficient]⟩
  -- The commutators of `P` with functions determine `A` on rank-one maps.
  have hA (x : M) : A x = sectionPrincipalCoefficient I BoundarylessManifold.isInteriorPoint P :=
    (eq_sectionPrincipalCoefficient_iff _ P (A x)).2 fun ξ v ↦ by
      obtain ⟨f, -, rfl⟩ := exists_contMDiffMap_mvfderiv_eq (I := I) x (0 : ℝ) ξ
      obtain ⟨σ, rfl⟩ := ContMDiffSection.evalLinearMap_surjective (I := I) (F := F) ∞ x v
      rw [ContMDiffSection.evalLinearMap_apply,
        ← apply_smul_sub_of_forall_apply_eq_add cov A B h,
        sectionPrincipalSymbol_mvfderiv_of_order_one]
  refine ⟨hA, fun x ↦ LinearMap.ext fun v ↦ ?_⟩
  obtain ⟨σ, rfl⟩ := ContMDiffSection.evalLinearMap_surjective (I := I) (F := F) ∞ x v
  rw [ContMDiffSection.evalLinearMap_apply]
  have hσ := h σ x
  rw [apply_eq_sectionPrincipalCoefficient_add_zerothCoefficient cov P σ x, hA] at hσ
  exact (add_left_cancel hσ).symm

/-- **The principal symbol of `A ∘ ∇ + B`.** If an operator `P` of order at most one is
`(P σ)(x) = A_x((∇σ)(x)) + B_x(σ(x))`, then its principal symbol is `σ(P)(ξ) v = A_x(ξ ⊗ v)`. -/
theorem sectionPrincipalSymbol_eq_of_forall_apply_eq_add
    (P : differentialOperators ℝ C^∞⟮I, M; ℝ⟯ Cₛ^∞⟮I; F, V⟯ Cₛ^∞⟮I; F', W⟯ 1)
    (A : ∀ x, (TangentSpace I x →L[ℝ] V x) →ₗ[ℝ] W x) (B : ∀ x, V x →ₗ[ℝ] W x)
    (h : ∀ σ x, (P : Cₛ^∞⟮I; F, V⟯ →ₗ[ℝ] Cₛ^∞⟮I; F', W⟯) σ x = A x (cov σ x) + B x (σ x))
    {x : M} (ξ : TangentSpace I x →L[ℝ] ℝ) (v : V x) :
    sectionPrincipalSymbol I BoundarylessManifold.isInteriorPoint P ξ v = A x (ξ.smulRight v) := by
  rw [((cov.forall_apply_eq_add_iff P A B).1 h).1 x, sectionPrincipalCoefficient_smulRight]

/-- **Changing the connection.** The leading coefficient does not depend on the connection, and
replacing `∇` by `∇'` changes the zeroth-order coefficient by the leading coefficient applied to
the difference `∇ - ∇'`: `B' = B + A ∘ (∇ - ∇')`. -/
theorem zerothCoefficient_apply_eq_add (cov' : CovariantDerivative I F V)
    [ContMDiffCovariantDerivative cov' ∞]
    (P : differentialOperators ℝ C^∞⟮I, M; ℝ⟯ Cₛ^∞⟮I; F, V⟯ Cₛ^∞⟮I; F', W⟯ 1) (x : M)
    (v : V x) :
    cov'.zerothCoefficient P x v = cov.zerothCoefficient P x v +
      sectionPrincipalCoefficient I BoundarylessManifold.isInteriorPoint P
        (cov.difference cov' x v) := by
  obtain ⟨σ, rfl⟩ := ContMDiffSection.evalLinearMap_surjective (I := I) (F := F) ∞ x v
  rw [ContMDiffSection.evalLinearMap_apply, cov.difference_apply cov' σ.mdifferentiableAt,
    map_sub, zerothCoefficient_apply, zerothCoefficient_apply, principalPart_apply,
    principalPart_apply]
  abel

end CovariantDerivative
