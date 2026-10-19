/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.LeviCivita.Basic
public import TauCeti.Geometry.Manifold.VectorBundle.NondegenerateMetric

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
`TauCeti.Manifold.ContMDiffNondegenerateMetric.ofRiemannianBundle`.

## Main definitions and results

* `TauCeti.Manifold.ContMDiffNondegenerateMetric.koszul`: the Koszul expression of `g`.
* `TauCeti.Manifold.ContMDiffNondegenerateMetric.IsMetricCompatible`: compatibility of a covariant
  derivative on `TM` with `g`.
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
  mvfderiv I (fun y ↦ g y (Y y) (Z y)) x (X x)
    + mvfderiv I (fun y ↦ g y (Z y) (X y)) x (Y x)
    - mvfderiv I (fun y ↦ g y (X y) (Y y)) x (Z x)
    + g x (mlieBracket I X Y x) (Z x)
    - g x (mlieBracket I X Z x) (Y x)
    - g x (mlieBracket I Y Z x) (X x)

/-- The defining formula for the Koszul expression of a nondegenerate metric. -/
theorem koszul_apply (X Y Z : Π x : M, TangentSpace I x) (x : M) :
    g.koszul X Y Z x =
      mvfderiv I (fun y ↦ g y (Y y) (Z y)) x (X x)
        + mvfderiv I (fun y ↦ g y (Z y) (X y)) x (Y x)
        - mvfderiv I (fun y ↦ g y (X y) (Y y)) x (Z x)
        + g x (mlieBracket I X Y x) (Z x)
        - g x (mlieBracket I X Z x) (Y x)
        - g x (mlieBracket I Y Z x) (X x) := (rfl)

/-- Swapping the two tangent arguments of the pointwise pairing of two vector fields. -/
private theorem apply_section_comm (Y Z : Π x : M, TangentSpace I x) :
    (fun y ↦ g y (Y y) (Z y)) = fun y ↦ g y (Z y) (Y y) :=
  funext fun y ↦ g.apply_comm y _ _

/-- Antisymmetrizing the Koszul expression in its first two arguments returns twice the pairing
of the Lie bracket with the third argument. -/
theorem koszul_sub_koszul_swap_first_two :
    g.koszul X Y Z x - g.koszul Y X Z x = 2 * g x (mlieBracket I X Y x) (Z x) := by
  rw [koszul, koszul, g.apply_section_comm Z Y, g.apply_section_comm Y X,
    g.apply_section_comm X Z, mlieBracket_swap_apply (V := Y) (W := X)]
  simp only [map_neg, neg_apply]
  ring

/-- Symmetrizing the Koszul expression in its last two arguments returns twice the derivative of
their pairing along the first argument. -/
theorem koszul_add_koszul_swap_last_two :
    g.koszul Z X Y x + g.koszul Z Y X x = 2 * mvfderiv I (fun y ↦ g y (X y) (Y y)) x (Z x) := by
  rw [koszul, koszul, g.apply_section_comm Y X, g.apply_section_comm Y Z,
    g.apply_section_comm X Z, mlieBracket_swap_apply (V := Y) (W := X)]
  simp only [map_neg, neg_apply]
  ring

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

variable (g) in
/-- A covariant derivative on the tangent bundle is a **Levi-Civita connection** of the
nondegenerate metric `g` when it is torsion free and compatible with `g`. -/
structure IsLeviCivitaConnection (cov : CovariantDerivative I E (fun x : M ↦ TangentSpace I x)) :
    Prop where
  /-- A Levi-Civita connection is compatible with the metric. -/
  isMetricCompatible : g.IsMetricCompatible cov
  /-- A Levi-Civita connection is torsion free. -/
  torsion : cov.torsion = 0

/-- **The Koszul formula**: for a Levi-Civita connection `∇` of a nondegenerate metric `g`,
`2 g(∇_X Y, Z)` is the Koszul expression of `g`. -/
theorem IsLeviCivitaConnection.two_apply_eq_koszul (h : g.IsLeviCivitaConnection cov)
    (hX : MDiffAt (T% X) x) (hY : MDiffAt (T% Y) x) (hZ : MDiffAt (T% Z) x) :
    2 * g x (cov Y x (X x)) (Z x) = g.koszul X Y Z x := by
  have hm₁ := h.isMetricCompatible.mvfderiv_eq hY hZ (X x)
  have hm₂ := h.isMetricCompatible.mvfderiv_eq hZ hX (Y x)
  have hm₃ := h.isMetricCompatible.mvfderiv_eq hX hY (Z x)
  have ht {X Y : Π x : M, TangentSpace I x} (hX : MDiffAt (T% X) x) (hY : MDiffAt (T% Y) x) :=
    (cov.torsion_eq_zero_iff.mp h.torsion) hX hY
  rw [koszul_apply, ← ht hX hY, ← ht hX hZ, ← ht hY hZ, hm₁, hm₂, hm₃]
  simp only [map_sub, sub_apply]
  rw [g.apply_comm x (Y x) (cov Z x (X x)), g.apply_comm x (Z x) (cov X x (Y x)),
    g.apply_comm x (X x) (cov Y x (Z x))]
  ring

/-- A covariant derivative on the tangent bundle is a Levi-Civita connection of a nondegenerate
metric exactly when it satisfies the Koszul formula. -/
theorem isLeviCivitaConnection_iff :
    g.IsLeviCivitaConnection cov ↔ ∀ ⦃x : M⦄ ⦃X Y Z : Π x : M, TangentSpace I x⦄,
      MDiffAt (T% X) x → MDiffAt (T% Y) x → MDiffAt (T% Z) x →
      2 * g x (cov Y x (X x)) (Z x) = g.koszul X Y Z x := by
  refine ⟨fun h _ _ _ _ hX hY hZ ↦ h.two_apply_eq_koszul hX hY hZ, fun h ↦ ⟨?_, ?_⟩⟩
  · refine isMetricCompatible_iff.mpr fun x X Y Z hX hY hZ ↦ ?_
    have hXY := h hX hY hZ
    have hYX := h hX hZ hY
    have key := g.koszul_add_koszul_swap_last_two (X := Y) (Y := Z) (Z := X) (x := x)
    rw [g.apply_comm x (Y x) (cov Z x (X x))]
    linarith
  · refine cov.torsion_eq_zero_iff.mpr fun {X Y x} hX hY ↦ ?_
    refine g.injective_apply_mdifferentiableAt_vectorField x ?_
    ext Z hZ
    have hXY := h hX hY hZ
    have hYX := h hY hX hZ
    have key := g.koszul_sub_koszul_swap_first_two (X := X) (Y := Y) (Z := Z) (x := x)
    simp only [map_sub, sub_apply]
    linarith

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
    (h' : g.IsLeviCivitaConnection cov') : cov.difference cov' = 0 := by
  ext x v
  have hv := mdifferentiableAt_extend I E v
  have hd := IsCovariantDerivativeOn.difference_apply cov.isCovariantDerivativeOnUniv
    cov'.isCovariantDerivativeOnUniv (x := x) (Set.mem_univ x) hv
  rw [extend_apply_self] at hd
  have hu : cov (extend E v) x = cov' (extend E v) x :=
    ContinuousLinearMap.ext (h.uniqueness h' hv)
  simp [CovariantDerivative.difference, hd, hu]

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
its metric, viewed as a nondegenerate metric. The order-one instance
`IsContMDiffRiemannianBundle I 1` required by `CovariantDerivative.leviCivitaConnection` is carried
alongside the smooth one, since instance search does not derive it. -/
theorem isLeviCivitaConnection_ofRiemannianBundle_leviCivitaConnection
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x)] :
    (ofRiemannianBundle I M).IsLeviCivitaConnection
      (CovariantDerivative.leviCivitaConnection I M) :=
  (isLeviCivitaConnection_iff_of_apply_eq_inner (ofRiemannianBundle_apply I M)).mpr
    (CovariantDerivative.isLeviCivitaConnection_leviCivitaConnection I)

end TauCeti.Manifold.ContMDiffNondegenerateMetric
