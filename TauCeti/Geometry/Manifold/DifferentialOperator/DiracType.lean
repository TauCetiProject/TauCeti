/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.DifferentialOperator.FormalAdjoint.PrincipalSymbol
public import TauCeti.Geometry.Manifold.DifferentialOperator.LaplaceType.Section
public import TauCeti.Geometry.Manifold.VectorBundle.Riemannian.Riesz

/-!
# Operators of Dirac type

Let `V` and `W` be smooth real vector bundles of finite rank with fibre metrics over a manifold `M`
with a Riemannian metric `g`. A first-order differential operator `D : Γ(V) → Γ(W)`, in
Grothendieck's sense (`TauCeti.differentialOperators`), is of *Dirac type* (`TauCeti.IsDiracType`)
if its geometric principal symbol `σ(ξ) = σ_geom(D)(ξ) : V_x → W_x`
(`TauCeti.sectionPrincipalSymbol`) satisfies

`⟪σ(ξ) v, σ(ξ) w⟫ = ‖ξ‖² ⟪v, w⟫`,

that is `σ(ξ)* σ(ξ) = ‖ξ‖² Id`, for every covector `ξ` at an interior point. Since `σ` is linear in
`ξ` for a first-order operator, this is equivalent to the polarized Clifford relation

`σ(α)* σ(β) + σ(β)* σ(α) = 2 g*(α, β) Id`,

where `g*(α, β) = ⟪α♯, β♯⟫` is the dual metric on covectors
(`TauCeti.isDiracType_iff_inner_add_inner`). The basic examples are the Dirac operators of
Clifford modules; for instance the symbol of the de Rham operator `d + d*` on families of forms
satisfies this relation
(`TauCeti.SmoothForm.coe_lie_deRhamOperator_piMap_funSMulₗ_mul_add_mul_apply`).

If `D*` is a formal adjoint of `D` for a measure `μ` and the fibre metrics, then `D* D` is of
Laplace type with constant `1` (`TauCeti.IsDiracType.isSectionLaplaceType_comp`). Indeed principal
symbols multiply under composition, and the principal symbol of the formal adjoint is minus the
fibrewise adjoint of that of `D` (`LinearMap.IsFormalAdjoint.inner_sectionPrincipalSymbol_apply`),
so `σ_geom(D* D)(ξ) = -σ(ξ)* σ(ξ) = -‖ξ‖² Id`. In particular the principal symbol of an operator of
Dirac type is injective at every nonzero covector
(`TauCeti.IsDiracType.injective_sectionPrincipalSymbol`).

## Main definitions

* `TauCeti.IsDiracType D`: `D` is of Dirac type.

## Main results

* `TauCeti.isDiracType_iff_inner_add_inner`: the polarized form of the Clifford relation.
* `TauCeti.IsDiracType.injective_sectionPrincipalSymbol`: the principal symbol of an operator of
  Dirac type is injective at every nonzero covector.
* `TauCeti.IsDiracType.isSectionLaplaceType_comp`: if `D` is of Dirac type and the first-order
  operator `Q` is a formal adjoint of `D`, then `Q ∘ D` is of Laplace type with constant `1`.

## References

* P. B. Gilkey, *The spectral geometry of operators of Dirac and Laplace type*, in Handbook of
  Global Analysis, Elsevier, 2008, §2 (operators of Dirac type and their squares).
* N. Berline, E. Getzler, M. Vergne, *Heat Kernels and Dirac Operators*, Springer, 1992,
  Chapter 3 (Dirac operators, whose squares are generalized Laplacians).
-/

public section

noncomputable section

open MeasureTheory Bundle Riemannian.Tensor
open scoped ContDiff Manifold RealInnerProductSpace

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, NormedAddCommGroup (V x)] [∀ x, InnerProductSpace ℝ (V x)]
  [FiberBundle F V] [VectorBundle ℝ F V] [ContMDiffVectorBundle ∞ F V I]
  {F' : Type*} [NormedAddCommGroup F'] [NormedSpace ℝ F']
  {W : M → Type*} [TopologicalSpace (TotalSpace F' W)]
  [∀ x, NormedAddCommGroup (W x)] [∀ x, InnerProductSpace ℝ (W x)]
  [FiberBundle F' W] [VectorBundle ℝ F' W]

/-- A first-order differential operator `D : Γ(V) → Γ(W)` between the smooth sections of bundles
with fibre metrics, over a Riemannian manifold, is of **Dirac type** if at every interior point `x`
and every covector `ξ ∈ T_x*M` its geometric principal symbol `σ(ξ) : V_x → W_x` satisfies
`⟪σ(ξ) v, σ(ξ) w⟫ = ‖ξ‖² ⟪v, w⟫`, that is `σ(ξ)* σ(ξ) = ‖ξ‖² Id`. The polarized form of this
condition is the Clifford relation `σ(α)* σ(β) + σ(β)* σ(α) = 2 g*(α, β) Id`
(`TauCeti.isDiracType_iff_inner_add_inner`). -/
def IsDiracType (D : differentialOperators ℝ C^∞⟮I, M; ℝ⟯ Cₛ^∞⟮I; F, V⟯ Cₛ^∞⟮I; F', W⟯ 1) :
    Prop :=
  ∀ (x : M) (hx : I.IsInteriorPoint x) (ξ : TangentSpace I x →L[ℝ] ℝ) (v w : V x),
    ⟪sectionPrincipalSymbol I hx D ξ v, sectionPrincipalSymbol I hx D ξ w⟫ = ‖ξ‖ ^ 2 * ⟪v, w⟫

variable {D : differentialOperators ℝ C^∞⟮I, M; ℝ⟯ Cₛ^∞⟮I; F, V⟯ Cₛ^∞⟮I; F', W⟯ 1}

theorem isDiracType_iff : IsDiracType D ↔
    ∀ (x : M) (hx : I.IsInteriorPoint x) (ξ : TangentSpace I x →L[ℝ] ℝ) (v w : V x),
      ⟪sectionPrincipalSymbol I hx D ξ v, sectionPrincipalSymbol I hx D ξ w⟫ =
        ‖ξ‖ ^ 2 * ⟪v, w⟫ :=
  Iff.rfl

/-- The Clifford relation `σ(ξ)* σ(ξ) = ‖ξ‖² Id` of an operator of Dirac type, evaluated on two
vectors. -/
theorem IsDiracType.inner_sectionPrincipalSymbol (hD : IsDiracType D) {x : M}
    (hx : I.IsInteriorPoint x) (ξ : TangentSpace I x →L[ℝ] ℝ) (v w : V x) :
    ⟪sectionPrincipalSymbol I hx D ξ v, sectionPrincipalSymbol I hx D ξ w⟫ = ‖ξ‖ ^ 2 * ⟪v, w⟫ :=
  hD x hx ξ v w

/-- **The polarized Clifford relation.** A first-order operator `D` is of Dirac type if and only
if its geometric principal symbol satisfies `σ(α)* σ(β) + σ(β)* σ(α) = 2 g*(α, β) Id` for all
covectors `α` and `β` at every interior point, where `g*(α, β) = ⟪α♯, β♯⟫` is the inner product of
the dual tangent vectors (`Riemannian.Tensor.rieszDual`). -/
theorem isDiracType_iff_inner_add_inner : IsDiracType D ↔
    ∀ (x : M) (hx : I.IsInteriorPoint x) (α β : TangentSpace I x →L[ℝ] ℝ) (v w : V x),
      ⟪sectionPrincipalSymbol I hx D α v, sectionPrincipalSymbol I hx D β w⟫ +
          ⟪sectionPrincipalSymbol I hx D β v, sectionPrincipalSymbol I hx D α w⟫ =
        2 * ⟪rieszDual x α, rieszDual x β⟫ * ⟪v, w⟫ := by
  refine ⟨fun hD x hx α β v w ↦ ?_, fun h x hx ξ v w ↦ ?_⟩
  · -- Expand the Clifford relation at `α + β`, using that the symbol is additive in the covector
    -- and that `rieszDual` is a linear isometry.
    have hαβ := hD x hx (α + β) v w
    rw [sectionPrincipalSymbol_add_covector, LinearMap.add_apply, LinearMap.add_apply,
      inner_add_left, inner_add_right, inner_add_right, hD x hx α v w, hD x hx β v w] at hαβ
    have hn : ‖α + β‖ ^ 2 = ‖α‖ ^ 2 + 2 * ⟪rieszDual x α, rieszDual x β⟫ + ‖β‖ ^ 2 := by
      rw [← (rieszDual (I := I) x).norm_map (α + β), map_add, norm_add_sq_real,
        (rieszDual (I := I) x).norm_map, (rieszDual (I := I) x).norm_map]
    rw [hn] at hαβ
    linear_combination hαβ
  · have hξ := h x hx ξ ξ v w
    rw [real_inner_self_eq_norm_sq, (rieszDual (I := I) x).norm_map] at hξ
    linear_combination hξ / 2

/-- **The symbol of an operator of Dirac type is injective** at every nonzero covector at an
interior point: `‖σ(ξ) v‖ = ‖ξ‖ ‖v‖`. -/
theorem IsDiracType.injective_sectionPrincipalSymbol (hD : IsDiracType D) {x : M}
    (hx : I.IsInteriorPoint x) {ξ : TangentSpace I x →L[ℝ] ℝ} (hξ : ξ ≠ 0) :
    Function.Injective (sectionPrincipalSymbol I hx D ξ) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro v hv
  have h := hD.inner_sectionPrincipalSymbol hx ξ v v
  rw [hv, inner_zero_left, eq_comm, mul_eq_zero] at h
  have hξ := (norm_pos_iff (E := TangentSpace I x →L[ℝ] ℝ)).2 hξ
  exact inner_self_eq_zero.1 (h.resolve_left (pow_pos hξ 2).ne')

section Adjoint

variable [FiniteDimensional ℝ F'] [ContMDiffVectorBundle ∞ F' W I]
  [SigmaCompactSpace M] [MeasurableSpace M] [BorelSpace M]
  [IsContinuousRiemannianBundle F V] [IsContinuousRiemannianBundle F' W]
  {μ : Measure M} [IsLocallyFiniteMeasure μ] [μ.IsOpenPosMeasure]

/-- **`D* D` is of Laplace type.** If `D : Γ(V) → Γ(W)` is of Dirac type and the first-order
operator `Q : Γ(W) → Γ(V)` is a formal adjoint of `D` with respect to a locally finite measure `μ`
that is positive on open sets, then `Q ∘ D` is of Laplace type with constant `1`: its geometric
principal symbol is `-σ(ξ)* σ(ξ) = -‖ξ‖² Id`. -/
theorem IsDiracType.isSectionLaplaceType_comp (hD : IsDiracType D)
    {Q : differentialOperators ℝ C^∞⟮I, M; ℝ⟯ Cₛ^∞⟮I; F', W⟯ Cₛ^∞⟮I; F, V⟯ 1}
    (hQ : (D : Cₛ^∞⟮I; F, V⟯ →ₗ[ℝ] Cₛ^∞⟮I; F', W⟯).IsFormalAdjoint
      (Q : Cₛ^∞⟮I; F', W⟯ →ₗ[ℝ] Cₛ^∞⟮I; F, V⟯) μ) :
    IsSectionLaplaceType
      ⟨(Q : Cₛ^∞⟮I; F', W⟯ →ₗ[ℝ] Cₛ^∞⟮I; F, V⟯) ∘ₗ (D : Cₛ^∞⟮I; F, V⟯ →ₗ[ℝ] Cₛ^∞⟮I; F', W⟯),
        comp_mem_differentialOperators Q.property D.property⟩ 1 := by
  refine isSectionLaplaceType_iff.2
    ⟨one_pos, fun x hx ξ ↦ LinearMap.ext fun v ↦ ext_inner_right ℝ fun w ↦ ?_⟩
  -- `⟪σ(Q)(ξ) σ(D)(ξ) v, w⟫ = -⟪σ(D)(ξ) w, σ(D)(ξ) v⟫ = -‖ξ‖² ⟪w, v⟫`.
  have h := hQ.inner_sectionPrincipalSymbol_apply hx ξ w (sectionPrincipalSymbol I hx D ξ v)
  rw [hD.inner_sectionPrincipalSymbol] at h
  rw [sectionPrincipalSymbol_comp, LinearMap.comp_apply, LinearMap.smul_apply, LinearMap.id_apply,
    real_inner_smul_left, real_inner_comm]
  linear_combination h - ‖ξ‖ ^ 2 * real_inner_comm v w

end Adjoint

end TauCeti
