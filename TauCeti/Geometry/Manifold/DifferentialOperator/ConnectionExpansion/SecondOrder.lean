/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.DifferentialOperator.ConnectionExpansion
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.SecondCovariantDerivative.Hom
import TauCeti.Geometry.Manifold.MFDeriv.Localized
import TauCeti.Geometry.Manifold.VectorField.CoordinateFrame
import TauCeti.Topology.Algebra.Module.FiniteDimension

/-!
# Second-order operators through a connection

Let `V` and `W` be smooth real vector bundles over a boundaryless finite-dimensional manifold `M`,
with `V` of finite rank, let `∇` be a smooth connection on `V` and `∇ᵀ` a smooth connection on the
tangent bundle. This file proves that every differential operator `P : Γ(V) → Γ(W)` of order at
most two, in Grothendieck's sense (`TauCeti.differentialOperators`), is

`(P σ)(x) = A₂((∇²σ)(x)) + A₁((∇σ)(x)) + A₀(σ(x))`,

where `∇²σ = ∇(∇σ)` is the covariant derivative of the section `∇σ` of `Hom(TM, V)` for the
connection induced by `∇ᵀ` and `∇` (equal to the second covariant derivative
`CovariantDerivative.secondCovariantDerivative`, by
`CovariantDerivative.secondCovariantDerivative_eq_hom_apply`), and `A₂`, `A₁`, `A₀` are bundle
maps on `Hom(TM, Hom(TM, V))`, `Hom(TM, V)` and `V`. This is the second-order case of the
expansion of a differential operator of order `m` in the covariant derivatives `∇ʲ`, `j ≤ m`; for
the first-order case see
`CovariantDerivative.apply_eq_sectionPrincipalCoefficient_add_zerothCoefficient`.

* The leading coefficient `A₂` (`TauCeti.sectionSecondOrderCoefficient`) does not depend on the
  connections: it is determined by the commutator symbol of `P`, the symmetric bilinear map
  `(df, dg) ↦ [[P, f], g]` (`TauCeti.sectionCommutatorSymbol`), through
  `A₂(ξ ⊗ η ⊗ v) = ½ [[P, ξ], η] v`, where `ξ ⊗ η ⊗ v` is the bilinear map `(u, w) ↦ ξ(u) η(w) v`
  (`TauCeti.sectionSecondOrderCoefficient_smulRight_smulRight`). It is symmetric, so it only sees
  the symmetrization of `∇²σ` (`TauCeti.sectionSecondOrderCoefficient_eq_of_apply_swap`), and on
  the symmetric tensors `ξ ⊗ ξ ⊗ v` it is the principal symbol, `A₂(ξ ⊗ ξ ⊗ v) = σ(P)(ξ) v`
  (`TauCeti.sectionSecondOrderCoefficient_smulRight_smulRight_self`). Near each point it is given
  by double commutators of `P` with cut-off coordinate functions, so it sends smooth sections of
  `Hom(TM, Hom(TM, V))` to smooth sections of `W`
  (`TauCeti.contMDiff_sectionSecondOrderCoefficient`).
* By the Leibniz rule, the double commutator of `∇²` with multiplication by `f` and `g` is
  `(df ⊗ dg + dg ⊗ df) σ` (`CovariantDerivative.secondCovariantDerivative_smul_smul_sub`), so the
  operator `σ ↦ A₂(∇²σ)` (`CovariantDerivative.secondOrderPart`) has the same double commutators
  as `P` (`CovariantDerivative.secondOrderPart_smul_smul_sub`). Hence `P - A₂ ∘ ∇²`
  (`CovariantDerivative.firstOrderRemainder`) has order at most one, and the first-order expansion
  applies to it: `A₁` is its leading coefficient `TauCeti.sectionPrincipalCoefficient` and `A₀` its
  zeroth-order coefficient `CovariantDerivative.zerothCoefficient`.

## Main definitions

* `TauCeti.sectionSecondOrderCoefficient I hx P`: the leading coefficient `A₂` at `x`, a linear
  map from `Hom(T_xM, Hom(T_xM, V_x))` to `W_x`.
* `CovariantDerivative.secondOrderPart cov covT P`: the operator `σ ↦ A₂(∇²σ)`.
* `CovariantDerivative.firstOrderRemainder cov covT P`: the operator `P - A₂ ∘ ∇²`, of order at most
  one.

## Main results

* `TauCeti.eq_sectionSecondOrderCoefficient_iff`: `A₂` is the unique linear map with
  `A₂(ξ ⊗ η ⊗ v) = ½ [[P, ξ], η] v`.
* `CovariantDerivative.apply_eq_sectionSecondOrderCoefficient_add`: the expansion
  `(P σ)(x) = A₂((∇²σ)(x)) + A₁((∇σ)(x)) + A₀(σ(x))`.
* `CovariantDerivative.eq_secondOrderPart_add_principalPart_add_mapLinearMap`: the same expansion
  as operators, with `A₀` a smooth bundle map.
* `CovariantDerivative.forall_apply_eq_add_add_iff`: uniqueness of the coefficients, among
  fibrewise linear families with `A₂` symmetric.
* `CovariantDerivative.mem_differentialOperators_two_of_forall_apply_eq_add_add`,
  `CovariantDerivative.sectionPrincipalSymbol_eq_of_forall_apply_eq_add_add`: conversely, an
  operator of the form `A ∘ ∇² + B ∘ ∇ + C` has order at most two and principal symbol
  `ξ ↦ A(ξ ⊗ ξ ⊗ ·)`.

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

/-! ### The commutator symbol in two covectors -/

omit [∀ x, IsTopologicalAddGroup (V x)] [∀ x, ContinuousSMul ℝ (V x)] in
/-- The commutator symbol of an operator of order at most two, as a bilinear map in the two
covectors. -/
private def sectionCommutatorSymbolBilin (hx : I.IsInteriorPoint x)
    (P : differentialOperators ℝ C^∞⟮I, M; ℝ⟯ Cₛ^∞⟮I; F, V⟯ Cₛ^∞⟮I; F', W⟯ 2) :
    (TangentSpace I x →L[ℝ] ℝ) →ₗ[ℝ] (TangentSpace I x →L[ℝ] ℝ) →ₗ[ℝ] V x →ₗ[ℝ] W x :=
  LinearMap.mk₂ ℝ (fun ξ η ↦ sectionCommutatorSymbol I hx P ![ξ, η])
    (fun ξ ξ' η ↦ (sectionCommutatorSymbol I hx P).cons_add ![η] ξ ξ')
    (fun c ξ η ↦ (sectionCommutatorSymbol I hx P).cons_smul ![η] c ξ)
    (fun ξ η η' ↦ by
      simp only [sectionCommutatorSymbol_comm hx P ξ]
      exact (sectionCommutatorSymbol I hx P).cons_add ![ξ] η η')
    (fun c ξ η ↦ by
      simp only [sectionCommutatorSymbol_comm hx P ξ]
      exact (sectionCommutatorSymbol I hx P).cons_smul ![ξ] c η)

omit [∀ x, IsTopologicalAddGroup (V x)] [∀ x, ContinuousSMul ℝ (V x)] in
private theorem sectionCommutatorSymbolBilin_apply (hx : I.IsInteriorPoint x)
    (P : differentialOperators ℝ C^∞⟮I, M; ℝ⟯ Cₛ^∞⟮I; F, V⟯ Cₛ^∞⟮I; F', W⟯ 2)
    (ξ η : TangentSpace I x →L[ℝ] ℝ) :
    sectionCommutatorSymbolBilin hx P ξ η = sectionCommutatorSymbol I hx P ![ξ, η] :=
  (rfl)

omit [∀ x, IsTopologicalAddGroup (V x)] [∀ x, ContinuousSMul ℝ (V x)] in
/-- For a family of covectors `cⱼ` and vectors `eⱼ` with `∑ⱼ ξ(eⱼ) cⱼ = ξ` for every covector `ξ`,
the contraction `∑ⱼₖ [[P, cⱼ], cₖ] (ξ(eⱼ) η(eₖ) v)` is `[[P, ξ], η] v`. -/
private theorem sum_sum_sectionCommutatorSymbol_smul (hx : I.IsInteriorPoint x)
    (P : differentialOperators ℝ C^∞⟮I, M; ℝ⟯ Cₛ^∞⟮I; F, V⟯ Cₛ^∞⟮I; F', W⟯ 2)
    {ι : Type*} [Fintype ι] (c : ι → TangentSpace I x →L[ℝ] ℝ) (e : ι → TangentSpace I x)
    (hce : ∀ ξ : TangentSpace I x →L[ℝ] ℝ, ∑ j, ξ (e j) • c j = ξ)
    (ξ η : TangentSpace I x →L[ℝ] ℝ) (v : V x) :
    ∑ j, ∑ k, sectionCommutatorSymbol I hx P ![c j, c k] (ξ (e j) • η (e k) • v) =
      sectionCommutatorSymbol I hx P ![ξ, η] v := by
  conv_rhs => rw [← sectionCommutatorSymbolBilin_apply, ← hce ξ, ← hce η]
  simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, Finset.smul_sum,
    sectionCommutatorSymbolBilin_apply]
  conv_rhs => rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun j _ ↦ Finset.sum_congr rfl fun k _ ↦ smul_comm _ _ _

/-! ### The leading coefficient at a point -/

/-- The linear map `B ↦ ½ ∑ⱼₖ [[P, cⱼ], cₖ](B(eⱼ, eₖ))` attached to a family of covectors `cⱼ` and
vectors `eⱼ`. -/
private def sectionSecondOrderContraction (hx : I.IsInteriorPoint x)
    (P : differentialOperators ℝ C^∞⟮I, M; ℝ⟯ Cₛ^∞⟮I; F, V⟯ Cₛ^∞⟮I; F', W⟯ 2)
    {ι : Type*} [Fintype ι] (c : ι → TangentSpace I x →L[ℝ] ℝ) (e : ι → TangentSpace I x) :
    (TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] V x) →ₗ[ℝ] W x where
  toFun B := (2 : ℝ)⁻¹ • ∑ j, ∑ k, sectionCommutatorSymbol I hx P ![c j, c k] (B (e j) (e k))
  map_add' B B' := by simp [Finset.sum_add_distrib, smul_add]
  map_smul' a B := by simp [Finset.smul_sum, smul_comm _ a]

variable (I) in
/-- **The leading coefficient of a second-order operator** at an interior point `x`: the linear
map `A_x : Hom(T_xM, Hom(T_xM, V_x)) → W_x`, `A_x(B) = ½ ∑ₖₗ [[P, eᵏ], eˡ](B(eₖ, eₗ))`,
contracting a `V_x`-valued bilinear form `B` with the commutator symbol of an operator
`P : Γ(V) → Γ(W)` of order at most two, for a basis `(eₖ)` of `T_xM` with dual basis `(eᵏ)`. It does
not depend on the basis: it is the unique linear map with `A_x(ξ ⊗ η ⊗ v) = ½ [[P, ξ], η] v`
(`TauCeti.eq_sectionSecondOrderCoefficient_iff`). For smooth connections `∇` on `V` and `∇ᵀ` on
the tangent bundle over a boundaryless manifold, `P σ = A(∇²σ) + A₁(∇σ) + A₀ σ`
(`CovariantDerivative.apply_eq_sectionSecondOrderCoefficient_add`). -/
def sectionSecondOrderCoefficient (hx : I.IsInteriorPoint x)
    (P : differentialOperators ℝ C^∞⟮I, M; ℝ⟯ Cₛ^∞⟮I; F, V⟯ Cₛ^∞⟮I; F', W⟯ 2) :
    (TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] V x) →ₗ[ℝ] W x :=
  let b := Module.finBasis ℝ (TangentSpace I x)
  sectionSecondOrderContraction hx P (fun k ↦ LinearMap.toContinuousLinearMap (b.coord k)) b

/-- The contraction along a family with `∑ⱼ ξ(eⱼ) cⱼ = ξ` sends `ξ ⊗ η ⊗ v` to
`½ [[P, ξ], η] v`. -/
private theorem sectionSecondOrderContraction_smulRight_smulRight (hx : I.IsInteriorPoint x)
    (P : differentialOperators ℝ C^∞⟮I, M; ℝ⟯ Cₛ^∞⟮I; F, V⟯ Cₛ^∞⟮I; F', W⟯ 2)
    {ι : Type*} [Fintype ι] (c : ι → TangentSpace I x →L[ℝ] ℝ) (e : ι → TangentSpace I x)
    (hce : ∀ ξ : TangentSpace I x →L[ℝ] ℝ, ∑ j, ξ (e j) • c j = ξ)
    (ξ η : TangentSpace I x →L[ℝ] ℝ) (v : V x) :
    sectionSecondOrderContraction hx P c e (ξ.smulRight (η.smulRight v)) =
      (2 : ℝ)⁻¹ • sectionCommutatorSymbol I hx P ![ξ, η] v := by
  rw [← sum_sum_sectionCommutatorSymbol_smul hx P c e hce ξ η v]
  simp [sectionSecondOrderContraction]

/-- **The leading coefficient on rank-one maps** is half the commutator symbol:
`A_x(ξ ⊗ η ⊗ v) = ½ [[P, ξ], η] v`. -/
@[simp]
theorem sectionSecondOrderCoefficient_smulRight_smulRight (hx : I.IsInteriorPoint x)
    (P : differentialOperators ℝ C^∞⟮I, M; ℝ⟯ Cₛ^∞⟮I; F, V⟯ Cₛ^∞⟮I; F', W⟯ 2)
    (ξ η : TangentSpace I x →L[ℝ] ℝ) (v : V x) :
    sectionSecondOrderCoefficient I hx P (ξ.smulRight (η.smulRight v)) =
      (2 : ℝ)⁻¹ • sectionCommutatorSymbol I hx P ![ξ, η] v :=
  sectionSecondOrderContraction_smulRight_smulRight hx P _ _
    (Module.finBasis ℝ _).sum_apply_smul_coord_toContinuousLinearMap ξ η v

/-- **Characterization of the leading coefficient.** It is the unique linear map on
`Hom(T_xM, Hom(T_xM, V_x))` sending each rank-one map `ξ ⊗ η ⊗ v` to `½ [[P, ξ], η] v`. -/
theorem eq_sectionSecondOrderCoefficient_iff (hx : I.IsInteriorPoint x)
    (P : differentialOperators ℝ C^∞⟮I, M; ℝ⟯ Cₛ^∞⟮I; F, V⟯ Cₛ^∞⟮I; F', W⟯ 2)
    (T : (TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] V x) →ₗ[ℝ] W x) :
    T = sectionSecondOrderCoefficient I hx P ↔
      ∀ (ξ η : TangentSpace I x →L[ℝ] ℝ) (v : V x),
        T (ξ.smulRight (η.smulRight v)) = (2 : ℝ)⁻¹ • sectionCommutatorSymbol I hx P ![ξ, η] v :=
  ⟨fun h ξ η v ↦ h ▸ sectionSecondOrderCoefficient_smulRight_smulRight hx P ξ η v,
    fun h ↦ LinearMap.ext_smulRight_smulRight fun ξ η v ↦ by
      rw [h, sectionSecondOrderCoefficient_smulRight_smulRight]⟩

/-- For finitely many covectors `cⱼ` and vectors `eⱼ` at `x` with `∑ⱼ ξ(eⱼ) cⱼ = ξ` for every
covector `ξ`, for instance dual bases, the leading coefficient is
`A_x(B) = ½ ∑ⱼₖ [[P, cⱼ], cₖ](B(eⱼ, eₖ))`. -/
theorem sectionSecondOrderCoefficient_apply_eq_sum (hx : I.IsInteriorPoint x)
    (P : differentialOperators ℝ C^∞⟮I, M; ℝ⟯ Cₛ^∞⟮I; F, V⟯ Cₛ^∞⟮I; F', W⟯ 2)
    {ι : Type*} [Fintype ι] (c : ι → TangentSpace I x →L[ℝ] ℝ) (e : ι → TangentSpace I x)
    (hce : ∀ ξ : TangentSpace I x →L[ℝ] ℝ, ∑ j, ξ (e j) • c j = ξ)
    (B : TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] V x) :
    sectionSecondOrderCoefficient I hx P B =
      (2 : ℝ)⁻¹ • ∑ j, ∑ k, sectionCommutatorSymbol I hx P ![c j, c k] (B (e j) (e k)) := by
  have h : sectionSecondOrderContraction hx P c e = sectionSecondOrderCoefficient I hx P :=
    (eq_sectionSecondOrderCoefficient_iff hx P _).2
      (sectionSecondOrderContraction_smulRight_smulRight hx P c e hce)
  simp only [← h, sectionSecondOrderContraction, LinearMap.coe_mk, AddHom.coe_mk]

/-- **The leading coefficient is symmetric**: it takes the same value on a bilinear map `B` and on
its transpose `(u, w) ↦ B(w, u)`. So it only depends on the symmetric part of `B`. -/
theorem sectionSecondOrderCoefficient_eq_of_apply_swap (hx : I.IsInteriorPoint x)
    (P : differentialOperators ℝ C^∞⟮I, M; ℝ⟯ Cₛ^∞⟮I; F, V⟯ Cₛ^∞⟮I; F', W⟯ 2)
    {B B' : TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] V x} (h : ∀ u w, B' u w = B w u) :
    sectionSecondOrderCoefficient I hx P B' = sectionSecondOrderCoefficient I hx P B := by
  set b := Module.finBasis ℝ (TangentSpace I x)
  set c := fun k ↦ LinearMap.toContinuousLinearMap (b.coord k)
  have hc := b.sum_apply_smul_coord_toContinuousLinearMap
  rw [sectionSecondOrderCoefficient_apply_eq_sum hx P c b hc,
    sectionSecondOrderCoefficient_apply_eq_sum hx P c b hc, Finset.sum_comm]
  congr 1
  refine Finset.sum_congr rfl fun k _ ↦ Finset.sum_congr rfl fun j _ ↦ ?_
  rw [h, sectionCommutatorSymbol_comm hx P (c j)]

/-- **On symmetric rank-one maps the leading coefficient is the principal symbol**:
`A_x(ξ ⊗ ξ ⊗ v) = σ(P)(ξ) v`. -/
theorem sectionSecondOrderCoefficient_smulRight_smulRight_self (hx : I.IsInteriorPoint x)
    (P : differentialOperators ℝ C^∞⟮I, M; ℝ⟯ Cₛ^∞⟮I; F, V⟯ Cₛ^∞⟮I; F', W⟯ 2)
    (ξ : TangentSpace I x →L[ℝ] ℝ) (v : V x) :
    sectionSecondOrderCoefficient I hx P (ξ.smulRight (ξ.smulRight v)) =
      sectionPrincipalSymbol I hx P ξ v := by
  rw [sectionSecondOrderCoefficient_smulRight_smulRight,
    sectionPrincipalSymbol_eq_inv_two_smul_sectionCommutatorSymbol, LinearMap.smul_apply]

/-! ### Smoothness of the leading coefficient -/

/-- **The leading coefficient sends smooth sections to smooth sections.** On a boundaryless
manifold, the leading coefficient of an operator of order at most two sends a smooth section `θ`
of `Hom(TM, Hom(TM, V))` to the smooth section `x ↦ A_x(θ x)` of `W`. -/
theorem contMDiff_sectionSecondOrderCoefficient [BoundarylessManifold I M]
    (P : differentialOperators ℝ C^∞⟮I, M; ℝ⟯ Cₛ^∞⟮I; F, V⟯ Cₛ^∞⟮I; F', W⟯ 2)
    {θ : Π x : M, TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] V x}
    (hθ : ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] F)) ∞
      (fun x ↦ TotalSpace.mk' (E →L[ℝ] E →L[ℝ] F)
        (E := fun y ↦ TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] V y) x (θ x))) :
    ContMDiff I (I.prod 𝓘(ℝ, F')) ∞
      (fun x ↦ TotalSpace.mk' F' x
        (sectionSecondOrderCoefficient I BoundarylessManifold.isInteriorPoint P (θ x))) := by
  -- Near each point, `A(θ)` is half the sum of the double commutators
  -- `[[P, u_j], u_k] (θ(X_j, X_k))`, for cut-off coordinate functions `u_j` and the coordinate
  -- frame `X_j` of a chart.
  intro x₀
  obtain ⟨u, X, hu⟩ := Manifold.exists_eventually_sum_smul_mvfderiv_eq (I := I) x₀
  let τ (j k : Fin (Module.finrank ℝ E)) : Cₛ^∞⟮I; F, V⟯ :=
    ⟨fun y ↦ θ y (X j y) (X k y),
      (hθ.clm_bundle_apply (X j).contMDiff).clm_bundle_apply (X k).contMDiff⟩
  let S : Cₛ^∞⟮I; F', W⟯ := (2 : ℝ)⁻¹ • ∑ j, ∑ k,
    commutatorSymbol ℝ C^∞⟮I, M; ℝ⟯ Cₛ^∞⟮I; F, V⟯ Cₛ^∞⟮I; F', W⟯ 2 P ![u j, u k] (τ j k)
  refine (S.contMDiff x₀).congr_of_eventuallyEq ?_
  filter_upwards [hu] with y hy
  refine congrArg (TotalSpace.mk' F' y) ?_
  rw [sectionSecondOrderCoefficient_apply_eq_sum _ P (fun j ↦ mvfderiv I (u j) y)
    (fun j ↦ X j y) hy]
  simp only [S, ContMDiffSection.coe_smul, ContMDiffSection.coe_sum, Pi.smul_apply,
    Finset.sum_apply]
  congr 1
  refine Finset.sum_congr rfl fun j _ ↦ Finset.sum_congr rfl fun k _ ↦ ?_
  -- The section `τ j k` is built from the values `θ y (X j y) (X k y)`.
  have hτ : τ j k y = θ y (X j y) (X k y) := rfl
  rw [← hτ, sectionCommutatorSymbol_mvfderiv_pair]

end TauCeti

/-! ### The expansion through connections -/

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
  (covT : CovariantDerivative I E (TangentSpace I : M → Type _))
  [ContMDiffCovariantDerivative covT ∞]

omit [BoundarylessManifold I M] [FiniteDimensional ℝ F] [ContMDiffVectorBundle ∞ F V I]
  [ContMDiffCovariantDerivative covT ∞] in
/-- For an operator of the form `A ∘ ∇² + B ∘ ∇ + C`, the double commutator with multiplication by
`f` and `g` is `σ ↦ A((df ⊗ dg + dg ⊗ df) σ)`. -/
private theorem apply_smul_smul_sub_of_forall_apply_eq_add
    {Q : Cₛ^∞⟮I; F, V⟯ →ₗ[ℝ] Cₛ^∞⟮I; F', W⟯}
    (A : ∀ x, (TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] V x) →ₗ[ℝ] W x)
    (B : ∀ x, (TangentSpace I x →L[ℝ] V x) →ₗ[ℝ] W x) (C : ∀ x, V x →ₗ[ℝ] W x)
    (h : ∀ σ x, Q σ x = A x (covT.hom cov (cov σ) x) + B x (cov σ x) + C x (σ x))
    (f g : C^∞⟮I, M; ℝ⟯) (σ : Cₛ^∞⟮I; F, V⟯) (x : M) :
    Q (f • g • σ) x - f x • Q (g • σ) x - g x • Q (f • σ) x + (f x * g x) • Q σ x =
      A x ((mvfderiv I f x).smulRight ((mvfderiv I g x).smulRight (σ x)) +
        (mvfderiv I g x).smulRight ((mvfderiv I f x).smulRight (σ x))) := by
  have hA := congrArg (A x) (hom_covariantDerivative_smul_smul_sub cov covT f.contMDiff
    g.contMDiff σ.contMDiff x)
  rw [← ContMDiffSection.coe_smul_contMDiffMap g σ, ← ContMDiffSection.coe_smul_contMDiffMap f,
    ← ContMDiffSection.coe_smul_contMDiffMap f σ] at hA
  have hB := congrArg (B x) (cov.apply_smul_smul_sub f g σ x)
  simp only [map_add, map_sub, map_smul, map_zero] at hA hB
  rw [map_add, ← hA, h, h, h, h]
  simp only [ContMDiffSection.smul_apply, map_smul]
  linear_combination (norm := module) hB

/-! ### The second-order part -/

/-- **The second-order part of an operator relative to connections**: the operator
`σ ↦ A(∇²σ)` on smooth sections, where `A` is the leading coefficient
`TauCeti.sectionSecondOrderCoefficient` of an operator `P : Γ(V) → Γ(W)` of order at most two and
`∇²σ` is the covariant derivative of `∇σ` for the connection induced on `Hom(TM, V)` by `∇ᵀ` and
`∇`. Its double commutators with multiplication by functions are those of `P`
(`CovariantDerivative.secondOrderPart_smul_smul_sub`), so `P` minus it has order at most one
(`CovariantDerivative.sub_secondOrderPart_mem_differentialOperators_one`). -/
def secondOrderPart (P : differentialOperators ℝ C^∞⟮I, M; ℝ⟯ Cₛ^∞⟮I; F, V⟯ Cₛ^∞⟮I; F', W⟯ 2) :
    Cₛ^∞⟮I; F, V⟯ →ₗ[ℝ] Cₛ^∞⟮I; F', W⟯ where
  toFun σ := ⟨fun x ↦ sectionSecondOrderCoefficient I BoundarylessManifold.isInteriorPoint P
      (covT.hom cov (cov σ) x),
    contMDiff_sectionSecondOrderCoefficient P
      (contMDiff_hom_covariantDerivative cov (covT := covT) σ.contMDiff)⟩
  map_add' σ τ := ContMDiffSection.ext fun x ↦ by
    simp [hom_covariantDerivative_add cov covT σ.contMDiff τ.contMDiff]
  map_smul' c σ := ContMDiffSection.ext fun x ↦ by
    simp [hom_covariantDerivative_const_smul cov covT c σ.contMDiff]

@[simp]
theorem secondOrderPart_apply
    (P : differentialOperators ℝ C^∞⟮I, M; ℝ⟯ Cₛ^∞⟮I; F, V⟯ Cₛ^∞⟮I; F', W⟯ 2)
    (σ : Cₛ^∞⟮I; F, V⟯) (x : M) :
    cov.secondOrderPart covT P σ x =
      sectionSecondOrderCoefficient I BoundarylessManifold.isInteriorPoint P
        (covT.hom cov (cov σ) x) :=
  (rfl)

/-- The double commutators of the second-order part with multiplication by functions are those of
`P`: `A(∇²(f g σ)) - f A(∇²(g σ)) - g A(∇²(f σ)) + f g A(∇²σ) = [[P, df], dg] σ`. -/
theorem secondOrderPart_smul_smul_sub
    (P : differentialOperators ℝ C^∞⟮I, M; ℝ⟯ Cₛ^∞⟮I; F, V⟯ Cₛ^∞⟮I; F', W⟯ 2)
    (f g : C^∞⟮I, M; ℝ⟯) (σ : Cₛ^∞⟮I; F, V⟯) (x : M) :
    cov.secondOrderPart covT P (f • g • σ) x - f x • cov.secondOrderPart covT P (g • σ) x -
        g x • cov.secondOrderPart covT P (f • σ) x +
          (f x * g x) • cov.secondOrderPart covT P σ x =
      sectionCommutatorSymbol I BoundarylessManifold.isInteriorPoint P
        ![mvfderiv I f x, mvfderiv I g x] (σ x) := by
  rw [apply_smul_smul_sub_of_forall_apply_eq_add cov covT
    (fun x ↦ sectionSecondOrderCoefficient I BoundarylessManifold.isInteriorPoint P) 0 0
    (fun σ x ↦ by simp) f g σ x, map_add, sectionSecondOrderCoefficient_smulRight_smulRight,
    sectionSecondOrderCoefficient_smulRight_smulRight,
    sectionCommutatorSymbol_comm _ P (mvfderiv I g x), ← add_smul]
  norm_num

/-- **A second-order operator minus its second-order part has order at most one.** For an operator
`P` of order at most two and smooth connections `∇` and `∇ᵀ`, the operator
`σ ↦ P σ - A(∇²σ)` is a differential operator of order at most one. -/
theorem sub_secondOrderPart_mem_differentialOperators_one
    (P : differentialOperators ℝ C^∞⟮I, M; ℝ⟯ Cₛ^∞⟮I; F, V⟯ Cₛ^∞⟮I; F', W⟯ 2) :
    (P : Cₛ^∞⟮I; F, V⟯ →ₗ[ℝ] Cₛ^∞⟮I; F', W⟯) - cov.secondOrderPart covT P ∈
      differentialOperators ℝ C^∞⟮I, M; ℝ⟯ Cₛ^∞⟮I; F, V⟯ Cₛ^∞⟮I; F', W⟯ 1 := by
  refine mem_differentialOperators_succ_iff.2 fun f ↦ mem_differentialOperators_zero_iff.2
    fun g σ ↦ ContMDiffSection.ext fun x ↦ ?_
  have hP := sectionCommutatorSymbol_mvfderiv_of_order_two
    (BoundarylessManifold.isInteriorPoint (I := I) (x := x)) P f g σ
  have hQ := cov.secondOrderPart_smul_smul_sub covT P f g σ x
  simp only [smulCommutator_apply_apply, LinearMap.sub_apply, ContMDiffSection.coe_sub,
    Pi.sub_apply, ContMDiffSection.smul_apply]
  linear_combination (norm := module) -hP - hQ

/-- **The first-order remainder of a second-order operator relative to connections**: the
operator `P - A ∘ ∇²` of order at most one, where `A ∘ ∇²` is the second-order part
`CovariantDerivative.secondOrderPart`. Its leading and zeroth-order coefficients
(`TauCeti.sectionPrincipalCoefficient`, `CovariantDerivative.zerothCoefficient`) are the remaining
coefficients of the expansion of `P`. -/
def firstOrderRemainder
    (P : differentialOperators ℝ C^∞⟮I, M; ℝ⟯ Cₛ^∞⟮I; F, V⟯ Cₛ^∞⟮I; F', W⟯ 2) :
    differentialOperators ℝ C^∞⟮I, M; ℝ⟯ Cₛ^∞⟮I; F, V⟯ Cₛ^∞⟮I; F', W⟯ 1 :=
  ⟨P - cov.secondOrderPart covT P, cov.sub_secondOrderPart_mem_differentialOperators_one covT P⟩

@[simp]
theorem coe_firstOrderRemainder
    (P : differentialOperators ℝ C^∞⟮I, M; ℝ⟯ Cₛ^∞⟮I; F, V⟯ Cₛ^∞⟮I; F', W⟯ 2) :
    (cov.firstOrderRemainder covT P : Cₛ^∞⟮I; F, V⟯ →ₗ[ℝ] Cₛ^∞⟮I; F', W⟯) =
      P - cov.secondOrderPart covT P :=
  (rfl)

/-- **The expansion of a second-order operator through connections.** For an operator `P` of order
at most two and smooth connections `∇` on `V` and `∇ᵀ` on the tangent bundle,

`(P σ)(x) = A₂((∇²σ)(x)) + A₁((∇σ)(x)) + A₀(σ(x))`,

where `∇²σ` is the covariant derivative of `∇σ` for the connection induced on `Hom(TM, V)`, the
leading coefficient `A₂` (`TauCeti.sectionSecondOrderCoefficient`) is determined by the commutator
symbol of `P` and does not depend on the connections, and `A₁` and `A₀` are the leading and
zeroth-order coefficients of the first-order remainder `P - A₂ ∘ ∇²`. -/
theorem apply_eq_sectionSecondOrderCoefficient_add
    (P : differentialOperators ℝ C^∞⟮I, M; ℝ⟯ Cₛ^∞⟮I; F, V⟯ Cₛ^∞⟮I; F', W⟯ 2)
    (σ : Cₛ^∞⟮I; F, V⟯) (x : M) :
    (P : Cₛ^∞⟮I; F, V⟯ →ₗ[ℝ] Cₛ^∞⟮I; F', W⟯) σ x =
      sectionSecondOrderCoefficient I BoundarylessManifold.isInteriorPoint P
          (covT.hom cov (cov σ) x) +
        sectionPrincipalCoefficient I BoundarylessManifold.isInteriorPoint
          (cov.firstOrderRemainder covT P) (cov σ x) +
        cov.zerothCoefficient (cov.firstOrderRemainder covT P) x (σ x) := by
  rw [add_assoc, ← cov.apply_eq_sectionPrincipalCoefficient_add_zerothCoefficient]
  simp

/-- **The expansion as operators**: a second-order operator is its second-order part, plus the
principal part of its first-order remainder, plus the action of the smooth zeroth-order
coefficient of that remainder. -/
theorem eq_secondOrderPart_add_principalPart_add_mapLinearMap [ContMDiffVectorBundle ∞ F' W I]
    (P : differentialOperators ℝ C^∞⟮I, M; ℝ⟯ Cₛ^∞⟮I; F, V⟯ Cₛ^∞⟮I; F', W⟯ 2) :
    (P : Cₛ^∞⟮I; F, V⟯ →ₗ[ℝ] Cₛ^∞⟮I; F', W⟯) = cov.secondOrderPart covT P +
      cov.principalPart (cov.firstOrderRemainder covT P) +
        ContMDiffSection.mapLinearMap (cov.zerothCoefficient (cov.firstOrderRemainder covT P))
          (cov.contMDiff_zerothCoefficient (cov.firstOrderRemainder covT P)) := by
  rw [add_assoc, ← cov.eq_principalPart_add_mapLinearMap, coe_firstOrderRemainder,
    add_sub_cancel]

/-! ### The converse and uniqueness -/

omit [BoundarylessManifold I M] [FiniteDimensional ℝ F] [ContMDiffVectorBundle ∞ F V I]
  [ContMDiffCovariantDerivative covT ∞] in
/-- **Operators of the form `A ∘ ∇² + B ∘ ∇ + C` have order at most two.** If
`(Q σ)(x) = A_x((∇²σ)(x)) + B_x((∇σ)(x)) + C_x(σ(x))` for all smooth sections `σ`, for any
fibrewise linear maps `A_x`, `B_x` and `C_x`, then `Q` is a differential operator of order at most
two. -/
theorem mem_differentialOperators_two_of_forall_apply_eq_add_add
    {Q : Cₛ^∞⟮I; F, V⟯ →ₗ[ℝ] Cₛ^∞⟮I; F', W⟯}
    (A : ∀ x, (TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] V x) →ₗ[ℝ] W x)
    (B : ∀ x, (TangentSpace I x →L[ℝ] V x) →ₗ[ℝ] W x) (C : ∀ x, V x →ₗ[ℝ] W x)
    (h : ∀ σ x, Q σ x = A x (covT.hom cov (cov σ) x) + B x (cov σ x) + C x (σ x)) :
    Q ∈ differentialOperators ℝ C^∞⟮I, M; ℝ⟯ Cₛ^∞⟮I; F, V⟯ Cₛ^∞⟮I; F', W⟯ 2 := by
  refine mem_differentialOperators_succ_iff.2 fun f ↦ mem_differentialOperators_succ_iff.2
    fun g ↦ mem_differentialOperators_zero_iff.2 fun a σ ↦ ContMDiffSection.ext fun x ↦ ?_
  have hσ := apply_smul_smul_sub_of_forall_apply_eq_add cov covT A B C h f g σ x
  have haσ := apply_smul_smul_sub_of_forall_apply_eq_add cov covT A B C h f g (a • σ) x
  have hsmul (ξ η : TangentSpace I x →L[ℝ] ℝ) :
      ξ.smulRight (η.smulRight ((a • σ) x)) = a x • ξ.smulRight (η.smulRight (σ x)) := by
    ext u w
    simp only [ContMDiffSection.smul_apply, ContinuousLinearMap.smulRight_apply, smul_apply]
    module
  have hA : A x ((mvfderiv I f x).smulRight ((mvfderiv I g x).smulRight ((a • σ) x)) +
      (mvfderiv I g x).smulRight ((mvfderiv I f x).smulRight ((a • σ) x))) =
      a x • A x ((mvfderiv I f x).smulRight ((mvfderiv I g x).smulRight (σ x)) +
        (mvfderiv I g x).smulRight ((mvfderiv I f x).smulRight (σ x))) := by
    simp only [hsmul, map_add, map_smul, smul_add]
  rw [hA, ← hσ] at haσ
  simp only [smulCommutator_apply_apply, ContMDiffSection.coe_sub, Pi.sub_apply,
    ContMDiffSection.smul_apply]
  linear_combination (norm := module) haσ

omit [BoundarylessManifold I M] [ContMDiffCovariantDerivative covT ∞] in
/-- **The principal symbol of `A ∘ ∇² + B ∘ ∇ + C`.** If an operator `P` of order at most two is
`(P σ)(x) = A_x((∇²σ)(x)) + B_x((∇σ)(x)) + C_x(σ(x))`, then its principal symbol is
`σ(P)(ξ) v = A_x(ξ ⊗ ξ ⊗ v)`. -/
theorem sectionPrincipalSymbol_eq_of_forall_apply_eq_add_add
    (P : differentialOperators ℝ C^∞⟮I, M; ℝ⟯ Cₛ^∞⟮I; F, V⟯ Cₛ^∞⟮I; F', W⟯ 2)
    (A : ∀ x, (TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] V x) →ₗ[ℝ] W x)
    (B : ∀ x, (TangentSpace I x →L[ℝ] V x) →ₗ[ℝ] W x) (C : ∀ x, V x →ₗ[ℝ] W x)
    (h : ∀ σ x, (P : Cₛ^∞⟮I; F, V⟯ →ₗ[ℝ] Cₛ^∞⟮I; F', W⟯) σ x =
      A x (covT.hom cov (cov σ) x) + B x (cov σ x) + C x (σ x))
    {x : M} (hx : I.IsInteriorPoint x) (ξ : TangentSpace I x →L[ℝ] ℝ) (v : V x) :
    sectionPrincipalSymbol I hx P ξ v = A x (ξ.smulRight (ξ.smulRight v)) := by
  obtain ⟨f, rfl⟩ : ∃ f : C^∞⟮I, M; ℝ⟯, mvfderiv I f x = ξ := ⟨_, mvfderiv_covectorLift hx ξ⟩
  obtain ⟨σ, rfl⟩ := ContMDiffSection.evalLinearMap_surjective (I := I) (F := F) ∞ x v
  rw [ContMDiffSection.evalLinearMap_apply,
    sectionPrincipalSymbol_eq_inv_two_smul_sectionCommutatorSymbol, LinearMap.smul_apply,
    sectionCommutatorSymbol_mvfderiv_of_order_two,
    apply_smul_smul_sub_of_forall_apply_eq_add cov covT A B C h f f σ x, map_add]
  module

/-- **Uniqueness of the coefficients.** An operator `P` of order at most two satisfies
`(P σ)(x) = A_x((∇²σ)(x)) + B_x((∇σ)(x)) + C_x(σ(x))` for all smooth sections `σ`, with `A_x`
symmetric, exactly when `A`, `B` and `C` are the coefficients of its expansion: `A` its leading
coefficient, and `B` and `C` the leading and zeroth-order coefficients of its first-order
remainder. The symmetry of `A_x` cannot be dropped, since an antisymmetric map composed with `∇²`
only sees the curvature and torsion terms, of order zero and one. -/
theorem forall_apply_eq_add_add_iff
    (P : differentialOperators ℝ C^∞⟮I, M; ℝ⟯ Cₛ^∞⟮I; F, V⟯ Cₛ^∞⟮I; F', W⟯ 2)
    (A : ∀ x, (TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] V x) →ₗ[ℝ] W x)
    (hA : ∀ x (L L' : TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] V x),
      (∀ u w, L' u w = L w u) → A x L' = A x L)
    (B : ∀ x, (TangentSpace I x →L[ℝ] V x) →ₗ[ℝ] W x) (C : ∀ x, V x →ₗ[ℝ] W x) :
    (∀ σ x, (P : Cₛ^∞⟮I; F, V⟯ →ₗ[ℝ] Cₛ^∞⟮I; F', W⟯) σ x =
        A x (covT.hom cov (cov σ) x) + B x (cov σ x) + C x (σ x)) ↔
      (∀ x, A x = sectionSecondOrderCoefficient I BoundarylessManifold.isInteriorPoint P) ∧
        (∀ x, B x = sectionPrincipalCoefficient I BoundarylessManifold.isInteriorPoint
          (cov.firstOrderRemainder covT P)) ∧
        ∀ x, C x = cov.zerothCoefficient (cov.firstOrderRemainder covT P) x := by
  refine ⟨fun h ↦ ?_, fun ⟨hA, hB, hC⟩ σ x ↦ by
    rw [hA, hB, hC, cov.apply_eq_sectionSecondOrderCoefficient_add covT]⟩
  -- The double commutators of `P` with functions determine `A` on rank-one maps.
  have hA₂ (x : M) : A x = sectionSecondOrderCoefficient I BoundarylessManifold.isInteriorPoint P :=
    (eq_sectionSecondOrderCoefficient_iff _ P (A x)).2 fun ξ η v ↦ by
      obtain ⟨f, -, rfl⟩ := exists_contMDiffMap_mvfderiv_eq (I := I) x (0 : ℝ) ξ
      obtain ⟨g, -, rfl⟩ := exists_contMDiffMap_mvfderiv_eq (I := I) x (0 : ℝ) η
      obtain ⟨σ, rfl⟩ := ContMDiffSection.evalLinearMap_surjective (I := I) (F := F) ∞ x v
      have hc := apply_smul_smul_sub_of_forall_apply_eq_add cov covT A B C h f g σ x
      have hswap : A x ((mvfderiv I g x).smulRight ((mvfderiv I f x).smulRight (σ x))) =
          A x ((mvfderiv I f x).smulRight ((mvfderiv I g x).smulRight (σ x))) :=
        hA x _ _ fun u w ↦ by
          simp only [ContinuousLinearMap.smulRight_apply]
          exact smul_comm _ _ _
      rw [map_add, hswap,
        ← sectionCommutatorSymbol_mvfderiv_of_order_two BoundarylessManifold.isInteriorPoint] at hc
      rw [ContMDiffSection.evalLinearMap_apply, hc]
      module
  -- The remaining coefficients are those of the first-order remainder.
  have h₁ : ∀ σ x, (cov.firstOrderRemainder covT P : Cₛ^∞⟮I; F, V⟯ →ₗ[ℝ] Cₛ^∞⟮I; F', W⟯) σ x =
      B x (cov σ x) + C x (σ x) := fun σ x ↦ by
    simp [h, hA₂, add_assoc]
  exact ⟨hA₂, ((cov.forall_apply_eq_add_iff _ B C).1 h₁)⟩

end CovariantDerivative
