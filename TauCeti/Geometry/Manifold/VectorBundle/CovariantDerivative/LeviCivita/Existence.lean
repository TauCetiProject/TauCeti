/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.LeviCivita.Nondegenerate
public import TauCeti.Geometry.Manifold.VectorBundle.NondegenerateMetric.Musical

/-!
# Existence of the Levi-Civita connection for a nondegenerate metric

The Koszul expression of a smooth symmetric nondegenerate metric is tensorial in its first
and third arguments. Raising its third index produces a covariant derivative, without any
positivity assumption. The resulting `leviCivitaConnection` is metric compatible and torsion
free. Its positive-definite specialization agrees with Mathlib's connection on differentiable
vector fields.

The value on a vector field not differentiable at the evaluation point is chosen to be zero;
connection laws and uniqueness only concern differentiable fields.

## References

* B. O'Neill, *Semi-Riemannian Geometry with Applications to Relativity*, Ch. 3, Thm. 11.
* J. M. Lee, *Introduction to Riemannian Manifolds*, 2nd ed., Thm. 5.10.
* `TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.LeviCivita.Basic`: the
  shared bilinear Koszul tensoriality and Leibniz identities used in the construction.
* `Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.LeviCivita`: the construction
  using `TensorialAt.mkHom₂`, adapted here by replacing the Riesz isomorphism with the
  nondegenerate metric's sharp isomorphism.
-/

public section

open Bundle FiberBundle VectorField
open scoped ContDiff Manifold

noncomputable section

namespace TauCeti.Manifold.ContMDiffNondegenerateMetric

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  (g : ContMDiffNondegenerateMetric (I := I) (M := M))
  {X Y Z : Π x : M, TangentSpace I x} {x : M}

variable [FiniteDimensional ℝ E]

private def connectionOfMDiffAt (hY : MDiffAt (T% Y) x) :
    TangentSpace I x →L[ℝ] TangentSpace I x :=
  (1 / 2 : ℝ) • ((g x).inverse ∘L
    TensorialAt.mkHom₂ (fun X Z ↦ g.koszul X Y Z x) x
      (fun _ hZ ↦ g.tensorialAt_koszul_first hY hZ)
      (fun _ hX ↦ g.tensorialAt_koszul_third hX hY))

private theorem two_apply_connectionOfMDiffAt
    (hX : MDiffAt (T% X) x) (hY : MDiffAt (T% Y) x) (hZ : MDiffAt (T% Z) x) :
    2 * g x (g.connectionOfMDiffAt hY (X x)) (Z x) = g.koszul X Y Z x := by
  simp [connectionOfMDiffAt, TensorialAt.mkHom₂_apply _ _ hX hZ]

open scoped Classical in
private def connection (Y : Π x : M, TangentSpace I x) (x : M) :
    TangentSpace I x →L[ℝ] TangentSpace I x :=
  if hY : MDiffAt (T% Y) x then g.connectionOfMDiffAt hY else 0

private theorem two_apply_connection
    (hX : MDiffAt (T% X) x) (hY : MDiffAt (T% Y) x) (hZ : MDiffAt (T% Z) x) :
    2 * g x (g.connection Y x (X x)) (Z x) = g.koszul X Y Z x := by
  simpa only [connection, dite_eq_left hY] using g.two_apply_connectionOfMDiffAt hX hY hZ

private theorem isCovariantDerivativeOn_connection :
    IsCovariantDerivativeOn E g.connection where
  add {Y Y'} x hY hY' _ := by
    ext v
    apply g.injective_apply_mdifferentiableAt_vectorField x
    ext Z hZ
    have hv := mdifferentiableAt_extend I E v
    have hsum := g.two_apply_connection hv (mdifferentiableAt_add_section hY hY') hZ
    have h₁ := g.two_apply_connection hv hY hZ
    have h₂ := g.two_apply_connection hv hY' hZ
    rw [g.koszul_add_second hv hY hY' hZ] at hsum
    simp only [extend_apply_self] at hsum h₁ h₂
    simp only [add_apply, map_add]
    linarith
  leibniz {Y f x} hY hf _ := by
    ext v
    apply g.injective_apply_mdifferentiableAt_vectorField x
    ext Z hZ
    have hv := mdifferentiableAt_extend I E v
    have hsmul := g.two_apply_connection hv (hf.smul_section hY) hZ
    have hbase := g.two_apply_connection hv hY hZ
    rw [g.koszul_smul_second hf hv hY hZ] at hsmul
    simp only [extend_apply_self] at hsmul hbase
    simp only [add_apply, smul_apply,
      ContinuousLinearMap.smulRight_apply, map_add, map_smul, smul_eq_mul]
    linear_combination hsmul / 2 - f x * hbase / 2

/-- The Levi-Civita connection of a smooth symmetric nondegenerate metric. It is chosen to
vanish on vector fields that are not differentiable at the evaluation point. -/
def leviCivitaConnection : CovariantDerivative I E (fun x : M ↦ TangentSpace I x) where
  toFun := g.connection
  isCovariantDerivativeOnUniv := g.isCovariantDerivativeOn_connection

/-- The Levi-Civita connection vanishes on a vector field not differentiable at the point. -/
@[simp] theorem leviCivitaConnection_eq_zero_of_not_mdifferentiableAt (hY : ¬ MDiffAt (T% Y) x) :
    g.leviCivitaConnection Y x = 0 := by
  simp only [leviCivitaConnection, connection, dite_eq_right hY]

/-- The connection constructed from a nondegenerate metric satisfies the Koszul formula. -/
theorem two_apply_leviCivitaConnection_eq_koszul
    (hX : MDiffAt (T% X) x) (hY : MDiffAt (T% Y) x) (hZ : MDiffAt (T% Z) x) :
    2 * g x (g.leviCivitaConnection Y x (X x)) (Z x) = g.koszul X Y Z x :=
  g.two_apply_connection hX hY hZ

/-- The connection constructed from the Koszul formula is metric compatible and torsion free. -/
theorem isLeviCivitaConnection_leviCivitaConnection :
    g.IsLeviCivitaConnection g.leviCivitaConnection :=
  g.isLeviCivitaConnection_iff.mpr fun _ _ _ _ hX hY hZ ↦
    g.two_apply_leviCivitaConnection_eq_koszul hX hY hZ

/-- For a positive metric, the nondegenerate Koszul construction agrees with Mathlib's
Riemannian Levi-Civita connection on differentiable vector fields. -/
theorem leviCivitaConnection_apply_eq_of_apply_eq_inner
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x)]
    (hg : ∀ x (v w : TangentSpace I x), g x v w = inner ℝ v w)
    (hY : MDiffAt (T% Y) x) (v : TangentSpace I x) :
    g.leviCivitaConnection Y x v = CovariantDerivative.leviCivitaConnection I M Y x v :=
  g.isLeviCivitaConnection_leviCivitaConnection.uniqueness
    ((isLeviCivitaConnection_iff_of_apply_eq_inner hg).mpr
      (CovariantDerivative.isLeviCivitaConnection_leviCivitaConnection I)) hY v

end TauCeti.Manifold.ContMDiffNondegenerateMetric
