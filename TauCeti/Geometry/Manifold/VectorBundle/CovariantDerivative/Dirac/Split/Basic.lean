/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.DifferentialOperator.FormalAdjoint.Connection
public import TauCeti.Geometry.Manifold.Riemannian.Killing.Basic
import TauCeti.Geometry.Manifold.Riemannian.Basic

/-!
# Integration by parts along a Killing field for Clifford multiplication

Let `V` be a Riemannian vector bundle over a Riemannian manifold `M` without boundary, with a
metric connection `∇` and a Clifford multiplication `c x : T_x M → End (V x)` which is
skew-adjoint, `⟪c(v) s, t⟫ = -⟪s, c(v) t⟫`, and compatible with `∇` and the Levi-Civita
connection: `∇_u (c(Y) τ) = c(∇_u Y) τ + c(Y) ∇_u τ`. For a unit vector field `T`, the Dirac
operator `D σ = ∑ᵢ c(eᵢ) ∇_{eᵢ} σ` (`CovariantDerivative.diracOperator`) splits as

`D σ = c(T) ∇_T σ + B_T σ`,

where the transverse Dirac operator `B_T` (`CovariantDerivative.transverseDiracOperator`)
differentiates only in the directions orthogonal to `T`. On a product `S¹ × Y` with the product
metric and `T = ∂ₛ`, this is the splitting `D = c(ds) ∇_T + B_A` of the Seiberg–Witten Dirac
operator, whose square is `-∇_T² + B_A² + (1 / 2) c₂(ds ∧ ι_T F_A)`.

This file proves that the summand `c(T) ∇_T` is formally self-adjoint for the Riemannian volume
`dV` whenever `T` is a Killing field of constant length, such as the parallel field `∂ₛ` on a
product:

`∫ ⟪c(T) ∇_T σ, τ⟫ dV = ∫ ⟪σ, c(T) ∇_T τ⟫ dV`

for smooth sections `σ` and `τ`, one of which has compact support. This is the theorem
`CovariantDerivative.IsMetricCompatible.integral_inner_clifford_covariantDerivative_left_eq_right`
below. A Killing field is divergence-free (`TauCeti.Manifold.IsKillingField.divergence_eq_zero`), so
`∇_T` is formally skew-adjoint
(`CovariantDerivative.IsMetricCompatible.isFormalAdjoint_alongVectorField_neg`).
A Killing field of constant length satisfies `∇_T T = 0`
(`TauCeti.Manifold.IsKillingField.covariantDerivative_self_eq_zero`), so compatibility gives
`∇_T (c(T) τ) = c(T) ∇_T τ`. The formal adjoint of `c(T) ∇_T` is therefore
`(-∇_T)(-c(T)) = c(T) ∇_T`
(`CovariantDerivative.IsMetricCompatible.isFormalAdjoint_comp_alongVectorField`).

Together with the formal skew-adjointness of `∇_T`, which gives
`-∫ ⟪∇_T ∇_T ψ, ψ⟫ dV = ∫ ‖∇_T ψ‖² dV`
(`CovariantDerivative.IsMetricCompatible.integral_inner_alongVectorField_alongVectorField`), this is
the integration by parts in the direction of `T` behind the energy identity
`0 = ‖∇_T ψ‖² + ‖B_A ψ‖² + ‖ι_T F_A‖² + 2π² ⟨c₁(L)², [S¹ × Y]⟩` for the unperturbed
Seiberg–Witten equations on a product.

## Main results

* `CovariantDerivative.IsMetricCompatible.integral_inner_clifford_covariantDerivative_left_eq_right`
  : `c(T) ∇_T` is formally self-adjoint along a Killing field `T` of constant length.

## References

* H. B. Lawson and M.-L. Michelsohn, *Spin Geometry*, Princeton University Press, 1989,
  Chapter II, §5 (Dirac operators of Clifford bundles and their formal self-adjointness).
* J. W. Morgan, *The Seiberg–Witten equations and applications to the topology of smooth
  four-manifolds*, Mathematical Notes 44, Princeton University Press, 1996, §5.2.
* C. H. Taubes, *The Seiberg–Witten invariants and symplectic forms*, Math. Res. Lett. 1 (1994),
  809–822.
-/

public section

noncomputable section

open MeasureTheory Bundle TauCeti TauCeti.Manifold
open scoped ContDiff Manifold RealInnerProductSpace

namespace CovariantDerivative

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
  {c : Π x : M, TangentSpace I x →L[ℝ] V x →L[ℝ] V x}
  [I.Boundaryless] [SigmaCompactSpace M] [MeasurableSpace M] [BorelSpace M]

local instance : IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x) :=
  IsContMDiffRiemannianBundle.toIsContinuousRiemannianBundle
    (IB := I) (n := ∞) (F := E) (V := fun x : M ↦ TangentSpace I x)

/-- **Formal self-adjointness of `c(T) ∇_T` along a Killing field.** Let `∇` be a metric
connection on a Riemannian vector bundle over a Riemannian manifold without boundary, and let the
Clifford multiplication `c` be skew-adjoint, compatible with `∇` and the Levi-Civita connection,
and smooth on smooth fields and sections. For a Killing field `T` of constant length, such as the
unit field `∂ₛ` on a product `S¹ × Y`, and smooth sections `σ`, `τ` one of which has compact
support,

`∫ ⟪c(T) ∇_T σ, τ⟫ dV = ∫ ⟪σ, c(T) ∇_T τ⟫ dV`

for the Riemannian volume `dV`: the summand `c(T) ∇_T` of the split Dirac operator
`D = c(T) ∇_T + B_T` is formally self-adjoint. -/
theorem IsMetricCompatible.integral_inner_clifford_covariantDerivative_left_eq_right
    (hcov : cov.IsMetricCompatible)
    (hskew : ∀ (x : M) (v : TangentSpace I x) (s t : V x), ⟪c x v s, t⟫ = -⟪s, c x v t⟫)
    (hcomp : ∀ (Y : Π y : M, TangentSpace I y) (τ : Π y : M, V y), CMDiff ∞ (T% Y) →
      CMDiff ∞ (T% τ) → ∀ x u, cov (fun y ↦ c y (Y y) (τ y)) x u =
        c x (leviCivitaConnection I M Y x u) (τ x) + c x (Y x) (cov τ x u))
    (hdiff : ∀ (Y : Π y : M, TangentSpace I y) (τ : Π y : M, V y), CMDiff ∞ (T% Y) →
      CMDiff ∞ (T% τ) → CMDiff ∞ (T% (fun y ↦ c y (Y y) (τ y))))
    {T : Π y : M, TangentSpace I y} (hT : IsKillingField I T) {r : ℝ} (hTr : ∀ x, ‖T x‖ = r)
    {σ τ : Π y : M, V y} (hσ : CMDiff ∞ (T% σ)) (hτ : CMDiff ∞ (T% τ))
    (hστ : IsCompact (closure {x | σ x ≠ 0}) ∨ IsCompact (closure {x | τ x ≠ 0})) :
    ∫ x, ⟪c x (T x) (cov σ x (T x)), τ x⟫ ∂riemannianVolume I M =
      ∫ x, ⟪σ x, c x (T x) (cov τ x (T x))⟫ ∂riemannianVolume I M := by
  -- Clifford multiplication by `T`, as an operator on the smooth sections.
  let A : Cₛ^∞⟮I; F, V⟯ →ₗ[ℝ] Cₛ^∞⟮I; F, V⟯ :=
    { toFun s := ⟨fun y ↦ c y (T y) (s y), hdiff T s hT.contMDiff s.contMDiff⟩
      map_add' s t := ContMDiffSection.ext fun y ↦ by simp
      map_smul' a s := ContMDiffSection.ext fun y ↦ by simp }
  have hA (s : Cₛ^∞⟮I; F, V⟯) (y : M) : A s y = c y (T y) (s y) := (rfl)
  let Tₛ : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ := ⟨T, hT.contMDiff⟩
  have hTₛ (y : M) : Tₛ y = T y := (rfl)
  -- Since `∇_T T = 0`, compatibility makes `c(T)` commute with `∇_T`.
  have hTT := hT.covariantDerivative_self_eq_zero (isMetricCompatible_leviCivitaConnection I)
    (torsion_leviCivitaConnection_eq_zero I) hTr
  have hAX (s : Cₛ^∞⟮I; F, V⟯) : cov.alongVectorField Tₛ (A s) = A (cov.alongVectorField Tₛ s) :=
    ContMDiffSection.ext fun y ↦ by
      -- `hcomp` is stated for the section `fun y ↦ c y (T y) (s y)`, so unfold `A s` to it.
      have hAs : ⇑(A s) = fun y ↦ c y (T y) (s y) := funext (hA s)
      simp [alongVectorField_apply, hA, hAs, hTₛ, hcomp T s hT.contMDiff s.contMDiff, hTT]
  have h := hcov.isFormalAdjoint_comp_alongVectorField Tₛ hT.divergence_eq_zero
    (fun y ↦ c y (T y)) hA (fun y ↦ hskew y (T y)) hAX
  have h' := h.integral_inner_eq (s := ⟨σ, hσ⟩) (t := ⟨τ, hτ⟩)
    (by simpa only [ContMDiffSection.tsupport_def, ContMDiffSection.coeFn_mk] using hστ)
  simpa only [LinearMap.comp_apply, hA, alongVectorField_apply, ContMDiffSection.coeFn_mk, hTₛ]
    using h'

end CovariantDerivative
