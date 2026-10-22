/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.LeviCivita.Basic
public import TauCeti.Geometry.Manifold.VectorBundle.NondegenerateMetric.Basic

/-!
# Levi-Civita connections of nondegenerate metrics

Let `g` be a smooth field of symmetric nondegenerate bilinear forms on the tangent bundle of `M`,
as bundled by `TauCeti.Manifold.ContMDiffNondegenerateMetric`; no positivity is assumed, so this
covers pseudo-Riemannian metrics of every signature. This file states what it means for a
covariant derivative `∇` on `TM` to be compatible with `g`,

`X (g (Y, Z)) = g (∇_X Y, Z) + g (Y, ∇_X Z)`,

and to be a Levi-Civita connection of `g`, that is, torsion free and compatible with `g`.

The Koszul formula

`2 g (∇_X Y, Z) = X g(Y, Z) + Y g(Z, X) - Z g(X, Y) + g([X, Y], Z) - g([X, Z], Y) - g([Y, Z], X)`

holds for every Levi-Civita connection of `g`, and conversely characterizes them. Since `g` is
nondegenerate, a tangent vector is determined by its pairings with differentiable vector fields,
so the Koszul formula determines `∇_X Y` for every `Y` differentiable at the base point: a
Levi-Civita connection of a nondegenerate metric is unique on differentiable vector fields. This is
the uniqueness half of the fundamental theorem of pseudo-Riemannian geometry.

For the metric of a Riemannian bundle instance, these notions agree with Mathlib's
`CovariantDerivative.IsMetricCompatible` and `CovariantDerivative.IsLeviCivitaConnection`, and
Mathlib's `CovariantDerivative.leviCivitaConnection` is a Levi-Civita connection of
the nondegenerate metric obtained from the bundled Riemannian metric.

## Main definitions and results

* `TauCeti.Manifold.ContMDiffNondegenerateMetric.koszul`: the Koszul expression of `g`.
* `TauCeti.Manifold.ContMDiffNondegenerateMetric.IsMetricCompatible`: compatibility of a covariant
  derivative on `TM` with `g`.
* `TauCeti.Manifold.ContMDiffNondegenerateMetric.isMetricCompatible_iff_derivBilinearTensor_eq_zero`
  characterizes compatibility with `g` as the vanishing of the covariant derivative `∇g` of `g`.
* `TauCeti.Manifold.ContMDiffNondegenerateMetric.IsLeviCivitaConnection`: a torsion-free covariant
  derivative compatible with `g`.
* `TauCeti.Manifold.ContMDiffNondegenerateMetric.IsLeviCivitaConnection.two_apply_eq_koszul` and
  `TauCeti.Manifold.ContMDiffNondegenerateMetric.isLeviCivitaConnection_iff`: the Koszul formula,
  and its characterization of the Levi-Civita connections of `g`.
* `TauCeti.Manifold.ContMDiffNondegenerateMetric.IsLeviCivitaConnection.uniqueness` and
  `TauCeti.Manifold.ContMDiffNondegenerateMetric.IsLeviCivitaConnection.difference_eq_zero`:
  uniqueness of the Levi-Civita connection of `g` on differentiable vector fields.
* `TauCeti.Manifold.ContMDiffNondegenerateMetric.isLeviCivitaConnection_iff_of_apply_eq_inner`:
  for a metric given by a Riemannian bundle instance, the comparison with
  `CovariantDerivative.IsLeviCivitaConnection`.

## References

* B. O'Neill, *Semi-Riemannian Geometry with Applications to Relativity*, Academic Press, 1983,
  Ch. 3, Thm. 11.
* J. M. Lee, *Introduction to Riemannian Manifolds*, 2nd ed., Springer GTM 176 (2018),
  Thm. 5.10.
* `Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.LeviCivita`: the
  `injective_inner_mdifferentiableAt_vectorField`, `IsLeviCivitaConnection.apply_eq_extend`, and
  `IsLeviCivitaConnection.uniqueness` arguments adapted here, with the inner product replaced by
  `g` and positivity by nondegeneracy.
* `TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.LeviCivita.Basic`: the
  positive-definite Koszul development generalized here to `g`.
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
  {cov cov' : CovariantDerivative I E (fun x : M ↦ TangentSpace I x)}
  {X Y Z : Π x : M, TangentSpace I x} {x : M}

/-! ### Nondegeneracy along differentiable vector fields -/

/-- A tangent vector is determined by its pairings under a nondegenerate metric with the values of
vector fields that are differentiable at its base point. -/
theorem injective_apply_mdifferentiableAt_vectorField (x : M) :
    Function.Injective fun u : TangentSpace I x ↦
      fun (Z : Π x : M, TangentSpace I x) (_ : MDiffAt (T% Z) x) ↦ g x u (Z x) := by
  intro u u' h
  rw [← sub_eq_zero]
  refine (g.nondegenerate x).1 _ fun w ↦ ?_
  have hw := congr_fun₂ h (extend E w) (mdifferentiableAt_extend I E w)
  simp only [extend_apply_self] at hw
  simp [hw]

/-! ### The Koszul expression -/

/-- The right-hand side of the Koszul formula for the metric `g`,

`X g(Y, Z) + Y g(Z, X) - Z g(X, Y) + g([X, Y], Z) - g([X, Z], Y) - g([Y, Z], X)`,

evaluated at `x`. For a Levi-Civita connection `∇` of `g` it computes `2 g(∇_X Y, Z)`, by
`TauCeti.Manifold.ContMDiffNondegenerateMetric.IsLeviCivitaConnection.two_apply_eq_koszul`. -/
def koszul (X Y Z : Π x : M, TangentSpace I x) (x : M) : ℝ :=
  TauCeti.Manifold.koszulBilinear I g X Y Z x

/-- The defining formula for the Koszul expression of a nondegenerate metric. -/
theorem koszul_apply (X Y Z : Π x : M, TangentSpace I x) (x : M) :
    g.koszul X Y Z x =
      mvfderiv I (fun y ↦ g y (Y y) (Z y)) x (X x)
        + mvfderiv I (fun y ↦ g y (Z y) (X y)) x (Y x)
        - mvfderiv I (fun y ↦ g y (X y) (Y y)) x (Z x)
        + g x (mlieBracket I X Y x) (Z x)
        - g x (mlieBracket I X Z x) (Y x)
        - g x (mlieBracket I Y Z x) (X x) :=
  TauCeti.Manifold.koszulBilinear_apply g X Y Z x

/-- Antisymmetrizing the Koszul expression in its first two arguments returns twice the pairing
of the Lie bracket with the third argument. -/
theorem koszul_sub_koszul_swap_first_two :
    g.koszul X Y Z x - g.koszul Y X Z x = 2 * g x (mlieBracket I X Y x) (Z x) :=
  TauCeti.Manifold.koszulBilinear_sub_koszulBilinear_swap_first_two g.apply_comm

/-- Symmetrizing the Koszul expression in its last two arguments returns twice the derivative of
their pairing along the first argument. -/
theorem koszul_add_koszul_swap_last_two :
    g.koszul Z X Y x + g.koszul Z Y X x =
      2 * mvfderiv I (fun y ↦ g y (X y) (Y y)) x (Z x) :=
  TauCeti.Manifold.koszulBilinear_add_koszulBilinear_swap_last_two g.apply_comm

/-- For a metric whose pairing is the inner product of a Riemannian bundle instance, the Koszul
expression is `TauCeti.Manifold.koszul`. -/
theorem koszul_eq_of_apply_eq_inner [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    (hg : ∀ x (v w : TangentSpace I x), g x v w = inner ℝ v w) :
    g.koszul X Y Z x = TauCeti.Manifold.koszul I X Y Z x := by
  simp only [koszul_apply, TauCeti.Manifold.koszul_apply, hg]

/-! ### Compatibility with the metric -/

/-- A covariant derivative `∇` on the tangent bundle is compatible with the nondegenerate metric
`g` when `v (g(Y, Z)) = g(∇_v Y, Z) + g(Y, ∇_v Z)` for every tangent vector `v` at `x` and all
vector fields `Y`, `Z` differentiable at `x`. -/
def IsMetricCompatible (cov : CovariantDerivative I E (fun x : M ↦ TangentSpace I x)) : Prop :=
  ∀ ⦃x : M⦄ ⦃Y Z : Π x : M, TangentSpace I x⦄, MDiffAt (T% Y) x → MDiffAt (T% Z) x →
    ∀ v : TangentSpace I x,
      mvfderiv I (fun y ↦ g y (Y y) (Z y)) x v = g x (cov Y x v) (Z x) + g x (Y x) (cov Z x v)

/-- Compatibility with a nondegenerate metric, in its defining arbitrary-tangent-vector form. -/
theorem isMetricCompatible_def :
    g.IsMetricCompatible cov ↔
      ∀ ⦃x : M⦄ ⦃Y Z : Π x : M, TangentSpace I x⦄,
        MDiffAt (T% Y) x → MDiffAt (T% Z) x → ∀ v : TangentSpace I x,
          mvfderiv I (fun y ↦ g y (Y y) (Z y)) x v =
            g x (cov Y x v) (Z x) + g x (Y x) (cov Z x v) :=
  Iff.rfl

variable {g}

/-- The product rule satisfied by a covariant derivative compatible with a nondegenerate metric. -/
theorem IsMetricCompatible.mvfderiv_eq (h : g.IsMetricCompatible cov) (hY : MDiffAt (T% Y) x)
    (hZ : MDiffAt (T% Z) x) (v : TangentSpace I x) :
    mvfderiv I (fun y ↦ g y (Y y) (Z y)) x v = g x (cov Y x v) (Z x) + g x (Y x) (cov Z x v) :=
  h hY hZ v

/-- Compatibility with a nondegenerate metric may be tested along differentiable vector fields
`X` rather than along arbitrary tangent vectors. -/
theorem isMetricCompatible_iff :
    g.IsMetricCompatible cov ↔ ∀ ⦃x : M⦄ ⦃X Y Z : Π x : M, TangentSpace I x⦄,
      MDiffAt (T% X) x → MDiffAt (T% Y) x → MDiffAt (T% Z) x →
      mvfderiv I (fun y ↦ g y (Y y) (Z y)) x (X x) =
        g x (cov Y x (X x)) (Z x) + g x (Y x) (cov Z x (X x)) := by
  refine ⟨fun h _ X _ _ _ hY hZ ↦ h.mvfderiv_eq hY hZ (X _), fun h x Y Z hY hZ v ↦ ?_⟩
  simpa only [extend_apply_self] using h (mdifferentiableAt_extend I E v) hY hZ

/-- For a metric whose pairing is the inner product of a Riemannian bundle instance,
compatibility with the metric is Mathlib's `CovariantDerivative.IsMetricCompatible`. -/
theorem isMetricCompatible_iff_of_apply_eq_inner [FiniteDimensional ℝ E]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x)]
    (hg : ∀ x (v w : TangentSpace I x), g x v w = inner ℝ v w) :
    g.IsMetricCompatible cov ↔ cov.IsMetricCompatible (M := M) (V := TangentSpace I) := by
  simp only [isMetricCompatible_iff, CovariantDerivative.isMetricCompatible_iff, hg]

/-! ### Levi-Civita connections -/

variable [FiniteDimensional ℝ E]

/-- A covariant derivative on the tangent bundle is compatible with a nondegenerate metric `g`
exactly when the covariant derivative `∇g` of `g`, as a field of bilinear forms, vanishes. -/
theorem isMetricCompatible_iff_derivBilinearTensor_eq_zero :
    g.IsMetricCompatible cov ↔ ∀ x, cov.derivBilinearTensor g x = 0 :=
  (cov.derivBilinearTensor_eq_zero_iff fun _ _ _ ↦ g.mdifferentiableAt_apply).symm

variable (g) in
/-- A covariant derivative on the tangent bundle is a **Levi-Civita connection** of the
nondegenerate metric `g` when it is torsion free and compatible with `g`. -/
structure IsLeviCivitaConnection (cov : CovariantDerivative I E (fun x : M ↦ TangentSpace I x)) :
    Prop where
  /-- A Levi-Civita connection is compatible with the metric. -/
  isMetricCompatible : g.IsMetricCompatible cov
  /-- A Levi-Civita connection is torsion free. -/
  torsion : cov.torsion = 0

/-- The covariant derivative of a nondegenerate metric along one of its Levi-Civita connections
vanishes. -/
theorem IsLeviCivitaConnection.derivBilinearTensor_eq_zero (h : g.IsLeviCivitaConnection cov)
    (x : M) : cov.derivBilinearTensor g x = 0 :=
  isMetricCompatible_iff_derivBilinearTensor_eq_zero.mp h.isMetricCompatible x

/-- **The Koszul formula**: for a Levi-Civita connection `∇` of a nondegenerate metric `g`,
`2 g(∇_X Y, Z)` is the Koszul expression of `g`. -/
theorem IsLeviCivitaConnection.two_apply_eq_koszul (h : g.IsLeviCivitaConnection cov)
    (hX : MDiffAt (T% X) x) (hY : MDiffAt (T% Y) x) (hZ : MDiffAt (T% Z) x) :
    2 * g x (cov Y x (X x)) (Z x) = g.koszul X Y Z x := by
  have := TauCeti.Manifold.koszulBilinear_sub_two_mul_apply_eq_derivBilinearTensor h.torsion
    g.apply_comm (fun _ _ ↦ g.mdifferentiableAt_apply) hX hY hZ
  simp only [h.derivBilinearTensor_eq_zero, zero_apply] at this
  rw [koszul]
  linarith

/-- A covariant derivative on the tangent bundle is a Levi-Civita connection of a nondegenerate
metric exactly when it satisfies the Koszul formula. -/
theorem isLeviCivitaConnection_iff :
    g.IsLeviCivitaConnection cov ↔ ∀ ⦃x : M⦄ ⦃X Y Z : Π x : M, TangentSpace I x⦄,
      MDiffAt (T% X) x → MDiffAt (T% Y) x → MDiffAt (T% Z) x →
      2 * g x (cov Y x (X x)) (Z x) = g.koszul X Y Z x := by
  refine ⟨fun h _ _ _ _ hX hY hZ ↦ h.two_apply_eq_koszul hX hY hZ, fun h ↦ ⟨?_, ?_⟩⟩
  · exact isMetricCompatible_iff.mpr
      (TauCeti.Manifold.metricProductRule_of_two_apply_eq_koszulBilinear g.apply_comm h)
  · exact TauCeti.Manifold.torsion_eq_zero_of_two_apply_eq_koszulBilinear g.apply_comm
      g.injective_apply_mdifferentiableAt_vectorField h

/-- **Uniqueness of the Levi-Civita connection** of a nondegenerate metric: two Levi-Civita
connections of `g` agree on every vector field differentiable at the base point.

The differentiability hypothesis on `Y` is needed, since a `CovariantDerivative` is unconstrained
on vector fields that are not differentiable. -/
theorem IsLeviCivitaConnection.uniqueness (h : g.IsLeviCivitaConnection cov)
    (h' : g.IsLeviCivitaConnection cov') (hY : MDiffAt (T% Y) x) (v : TangentSpace I x) :
    cov Y x v = cov' Y x v := by
  refine g.injective_apply_mdifferentiableAt_vectorField x ?_
  ext Z hZ
  have hv := mdifferentiableAt_extend I E v
  have hk := h.two_apply_eq_koszul hv hY hZ
  have hk' := h'.two_apply_eq_koszul hv hY hZ
  rw [extend_apply_self] at hk hk'
  linarith

/-- Uniqueness of the Levi-Civita connection of a nondegenerate metric, as the vanishing of the
endomorphism-valued one-form `CovariantDerivative.difference` of two of them. -/
theorem IsLeviCivitaConnection.difference_eq_zero (h : g.IsLeviCivitaConnection cov)
    (h' : g.IsLeviCivitaConnection cov') : cov.difference cov' = 0 :=
  CovariantDerivative.difference_eq_zero_of_forall fun _ _ hY ↦
    ContinuousLinearMap.ext (h.uniqueness h' hY)

/-! ### The positive-definite specialization -/

/-- For a metric whose pairing is the inner product of a Riemannian bundle instance, its
Levi-Civita connections are those of Mathlib's `CovariantDerivative.IsLeviCivitaConnection`. -/
theorem isLeviCivitaConnection_iff_of_apply_eq_inner
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x)]
    (hg : ∀ x (v w : TangentSpace I x), g x v w = inner ℝ v w) :
    g.IsLeviCivitaConnection cov ↔ cov.IsLeviCivitaConnection :=
  ⟨fun h ↦ ⟨(isMetricCompatible_iff_of_apply_eq_inner hg).mp h.isMetricCompatible, h.torsion⟩,
    fun h ↦ ⟨(isMetricCompatible_iff_of_apply_eq_inner hg).mpr h.isMetricCompatible, h.torsion⟩⟩

variable (I M) in
/-- Mathlib's Levi-Civita connection of a smooth Riemannian manifold is a Levi-Civita connection of
its metric, viewed as a nondegenerate metric. -/
theorem isLeviCivitaConnection_ofRiemannianBundle_leviCivitaConnection
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)] :
    (ofRiemannianBundle I M).IsLeviCivitaConnection
      (CovariantDerivative.leviCivitaConnection I M) :=
  (isLeviCivitaConnection_iff_of_apply_eq_inner (ofRiemannianBundle_apply I M)).mpr
    (CovariantDerivative.isLeviCivitaConnection_leviCivitaConnection I)

end TauCeti.Manifold.ContMDiffNondegenerateMetric
