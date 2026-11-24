/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.DifferentialOperator.PrincipalSymbol.Section
public import TauCeti.Geometry.Manifold.DifferentialOperator.Restrict.Section
public import TauCeti.Geometry.Manifold.Riemannian.Restriction.Basic
public import Mathlib.Topology.VectorBundle.Riemannian

/-!
# Laplace-type operators between sections of a vector bundle

Let `V` be a smooth real vector bundle of finite rank over a finite-dimensional Hausdorff manifold
`M` with a Riemannian metric. A differential operator `P : Γ(V) → Γ(V)` of order at most two, in
Grothendieck's sense (`TauCeti.differentialOperators`), is of *Laplace type* with constant `c > 0`
if its principal symbol in the Fourier convention is `ξ ↦ c ‖ξ‖² Id`, where `‖ξ‖` is the norm the
metric induces on the cotangent space. Since `∂ⱼ` has Fourier symbol `i ξⱼ`, for an operator of
order two this is the condition `σ_geom(P)(ξ) = -(c ‖ξ‖²) Id` on the geometric principal symbol
`TauCeti.sectionPrincipalSymbol`, defined by iterated commutators with multiplication operators.
This is the vector bundle version of `TauCeti.IsLaplaceType`, which treats operators on the smooth
functions. The products `D* D` of operators of Dirac type with their formal adjoints are of Laplace
type with constant `1` (`TauCeti.IsDiracType.isSectionLaplaceType_comp`). Connection Laplacians
`∇*∇` have the same principal symbol: their double commutators with multiplication by `f` are
`-2 ‖df‖²` (`CovariantDerivative.roughLaplacian_smul_smul_sub_self`).

An operator of Laplace type is elliptic: its principal symbol is invertible at every nonzero
covector.

## Main definitions

* `TauCeti.IsSectionLaplaceType P c`: `P` is of Laplace type with constant `c`.

## Main results

* `TauCeti.IsSectionLaplaceType.smul`: positive rescaling multiplies the constant.
* `TauCeti.IsSectionLaplaceType.add_of_mem_differentialOperators_one`: perturbations of order at
  most one keep the Laplace type.
* `TauCeti.IsSectionLaplaceType.unique`: over a manifold of positive dimension, the constant is
  determined by the operator as soon as some fibre over an interior point is nonzero.
* `TauCeti.IsSectionLaplaceType.sectionPrincipalSymbol_bijective`: operators of Laplace type are
  elliptic.
* `TauCeti.IsSectionLaplaceType.restrictSectionDifferentialOperators`: the restriction of an
  operator of Laplace type to an open subset, with the inherited metric, is of Laplace type with the
  same constant.

## References

* N. Berline, E. Getzler, M. Vergne, *Heat Kernels and Dirac Operators*, Springer, 1992, §2.1
  (generalized Laplacians, Definition 2.2).
* P. B. Gilkey, *The spectral geometry of operators of Dirac and Laplace type*, in Handbook of
  Global Analysis, Elsevier, 2008, §2 (operators of Laplace type).
-/

public section

open Bundle TopologicalSpace
open scoped ContDiff Manifold

noncomputable section

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)] [∀ x, TopologicalSpace (V x)]
  [FiberBundle F V] [VectorBundle ℝ F V] [ContMDiffVectorBundle ∞ F V I]

/-- A differential operator `P : Γ(V) → Γ(V)` of order at most two between the smooth sections of
a vector bundle over a Riemannian manifold is of **Laplace type** with constant `c` if `0 < c` and,
at every interior point `x`, its principal symbol in the Fourier convention is `ξ ↦ c ‖ξ‖² Id`, the
norm being the one the metric induces on `T_x*M`. The Fourier symbol of `∂ⱼ` is `i ξⱼ`, so for
operators of order two the Fourier principal symbol is `-1` times the geometric one
`TauCeti.sectionPrincipalSymbol`, and the condition reads `σ_geom(P)(ξ) = -(c ‖ξ‖²) Id`. -/
def IsSectionLaplaceType
    (P : differentialOperators ℝ C^∞⟮I, M; ℝ⟯ Cₛ^∞⟮I; F, V⟯ Cₛ^∞⟮I; F, V⟯ 2) (c : ℝ) : Prop :=
  0 < c ∧ ∀ (x : M) (hx : I.IsInteriorPoint x) (ξ : TangentSpace I x →L[ℝ] ℝ),
    sectionPrincipalSymbol I hx P ξ = -(c * ‖ξ‖ ^ 2) • LinearMap.id

variable {P Q : differentialOperators ℝ C^∞⟮I, M; ℝ⟯ Cₛ^∞⟮I; F, V⟯ Cₛ^∞⟮I; F, V⟯ 2} {c c' : ℝ}

theorem isSectionLaplaceType_iff : IsSectionLaplaceType P c ↔
    0 < c ∧ ∀ (x : M) (hx : I.IsInteriorPoint x) (ξ : TangentSpace I x →L[ℝ] ℝ),
      sectionPrincipalSymbol I hx P ξ = -(c * ‖ξ‖ ^ 2) • LinearMap.id :=
  Iff.rfl

/-- The constant of an operator of Laplace type is positive. -/
theorem IsSectionLaplaceType.pos (hP : IsSectionLaplaceType P c) : 0 < c :=
  hP.1

/-- The geometric principal symbol of an operator of Laplace type with constant `c` is
`ξ ↦ -(c ‖ξ‖²) Id` at every interior point. -/
theorem IsSectionLaplaceType.sectionPrincipalSymbol_eq (hP : IsSectionLaplaceType P c) {x : M}
    (hx : I.IsInteriorPoint x) (ξ : TangentSpace I x →L[ℝ] ℝ) :
    sectionPrincipalSymbol I hx P ξ = -(c * ‖ξ‖ ^ 2) • LinearMap.id :=
  hP.2 x hx ξ

/-- The geometric principal symbol of an operator of Laplace type with constant `c` multiplies
every vector by `-(c ‖ξ‖²)`. -/
theorem IsSectionLaplaceType.sectionPrincipalSymbol_apply (hP : IsSectionLaplaceType P c) {x : M}
    (hx : I.IsInteriorPoint x) (ξ : TangentSpace I x →L[ℝ] ℝ) (v : V x) :
    sectionPrincipalSymbol I hx P ξ v = -(c * ‖ξ‖ ^ 2) • v := by
  rw [hP.sectionPrincipalSymbol_eq hx, LinearMap.smul_apply, LinearMap.id_apply]

/-- A positive multiple of an operator of Laplace type is of Laplace type, with the constant
multiplied accordingly. -/
theorem IsSectionLaplaceType.smul (hP : IsSectionLaplaceType P c) {t : ℝ} (ht : 0 < t) :
    IsSectionLaplaceType (t • P) (t * c) :=
  ⟨mul_pos ht hP.pos, fun x hx ξ ↦ by
    rw [sectionPrincipalSymbol_smul, hP.sectionPrincipalSymbol_eq, smul_smul]
    congr 1
    ring⟩

/-- Adding an operator of order at most one does not change the Laplace type. -/
theorem IsSectionLaplaceType.add_of_mem_differentialOperators_one (hP : IsSectionLaplaceType P c)
    (hQ : (Q : Cₛ^∞⟮I; F, V⟯ →ₗ[ℝ] Cₛ^∞⟮I; F, V⟯) ∈
      differentialOperators ℝ C^∞⟮I, M; ℝ⟯ Cₛ^∞⟮I; F, V⟯ Cₛ^∞⟮I; F, V⟯ 1) :
    IsSectionLaplaceType (P + Q) c :=
  ⟨hP.pos, fun x hx ξ ↦ by
    rw [sectionPrincipalSymbol_add, hP.sectionPrincipalSymbol_eq,
      sectionPrincipalSymbol_eq_zero_of_mem_differentialOperators hx Q hQ, add_zero]⟩

/-- **Uniqueness of the constant.** On a manifold of positive dimension, the constant of an
operator of Laplace type is determined by the operator as soon as the fibre over some interior
point is nonzero. Over a zero fibre every principal symbol vanishes, and the constant is not
determined. -/
theorem IsSectionLaplaceType.unique [Nontrivial E] {x : M} (hx : I.IsInteriorPoint x) {v : V x}
    (hv : v ≠ 0) (hP : IsSectionLaplaceType P c) (hP' : IsSectionLaplaceType P c') : c = c' := by
  -- `TangentSpace I x` is `E`, so it is nontrivial and carries a nonzero covector.
  have : Nontrivial (TangentSpace I x) := inferInstanceAs (Nontrivial E)
  obtain ⟨ξ, hξ⟩ := exists_ne (0 : TangentSpace I x →L[ℝ] ℝ)
  have hξ := (norm_pos_iff (E := TangentSpace I x →L[ℝ] ℝ)).2 hξ
  have h := (hP.sectionPrincipalSymbol_apply hx ξ v).symm.trans
    (hP'.sectionPrincipalSymbol_apply hx ξ v)
  exact mul_right_cancel₀ (pow_pos hξ 2).ne' (neg_inj.1 (smul_left_injective ℝ hv h))

/-- **Operators of Laplace type are elliptic**: at every nonzero covector `ξ` at an interior point,
the principal symbol `-(c ‖ξ‖²) Id` is bijective. -/
theorem IsSectionLaplaceType.sectionPrincipalSymbol_bijective (hP : IsSectionLaplaceType P c)
    {x : M} (hx : I.IsInteriorPoint x) {ξ : TangentSpace I x →L[ℝ] ℝ} (hξ : ξ ≠ 0) :
    Function.Bijective (sectionPrincipalSymbol I hx P ξ) := by
  have hξ := (norm_pos_iff (E := TangentSpace I x →L[ℝ] ℝ)).2 hξ
  have hc : -(c * ‖ξ‖ ^ 2) ≠ 0 := neg_ne_zero.2 (mul_pos hP.pos (pow_pos hξ 2)).ne'
  rw [hP.sectionPrincipalSymbol_eq hx]
  exact ⟨fun v w h ↦ smul_right_injective (V x) hc h, fun v ↦ ⟨(-(c * ‖ξ‖ ^ 2))⁻¹ • v, by
    rw [LinearMap.smul_apply, LinearMap.id_apply, smul_smul, mul_inv_cancel₀ hc, one_smul]⟩⟩

/-- **Restriction to open subsets.** For the Riemannian metric that an open subset `U` inherits
from `M`, the restriction to `U` of an operator of Laplace type with constant `c` is of Laplace type
with constant `c`. -/
theorem IsSectionLaplaceType.restrictSectionDifferentialOperators (hP : IsSectionLaplaceType P c)
    (U : Opens M) : IsSectionLaplaceType (U.restrictSectionDifferentialOperators 2 P) c := by
  refine ⟨hP.pos, fun x hx ξ ↦ ?_⟩
  have hx' : I.IsInteriorPoint (x : M) := I.isInteriorPoint_iff_isInteriorPoint_val.mp hx
  -- Write `ξ` as `η ∘ ι` for the identification `ι : T_x U ≃ T_x M` of the tangent spaces, which
  -- is a linear isometric equivalence for the inherited metric, so `η` has the norm of `ξ`.
  have hξ : ξ = (ξ.comp ((Manifold.tangentSpaceOpenLinearIsometryEquiv (I := I) U x).symm :
      TangentSpace I (x : M) →L[ℝ] TangentSpace I x)).comp
      (Manifold.tangentSpaceOpenEquiv (I := I) x).toContinuousLinearMap := by
    ext v
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
      LinearIsometryEquiv.coe_coe, ← Manifold.coe_tangentSpaceOpenLinearIsometryEquiv,
      LinearIsometryEquiv.symm_apply_apply]
  conv_lhs => rw [hξ]
  rw [sectionPrincipalSymbol_restrictSectionDifferentialOperators hx',
    hP.sectionPrincipalSymbol_eq hx', ContinuousLinearMap.opNorm_comp_linearIsometryEquiv]
  -- The identity of the fibre of `V` over `x` is that of the fibre of `V|_U`.
  rfl

end TauCeti
