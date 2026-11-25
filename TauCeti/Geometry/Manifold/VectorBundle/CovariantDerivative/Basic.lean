/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.Basic
import TauCeti.Geometry.Manifold.VectorBundle.Section.Support

/-!
# Covariant derivatives of sections and evaluation of connection operations

Mathlib's `IsCovariantDerivativeOn` is additive on pairs of sections differentiable at a point of
the set it is a covariant derivative on. This file derives the corresponding statements for
negatives and differences, and iterates additivity to finite sums of sections. It also evaluates
Mathlib's `CovariantDerivative.addOneForm` on sections and `CovariantDerivative.difference` on
section values and fibre vectors.

## Main results

* `IsCovariantDerivativeOn.neg` and `IsCovariantDerivativeOn.sub`: a covariant derivative over
  `u` commutes with negation and subtraction of sections differentiable at a point of `u`.
* `IsCovariantDerivativeOn.sum`: a covariant derivative over `u` commutes with finite sums of
  sections differentiable at a point of `u`.
* `IsCovariantDerivativeOn.leibniz_apply` and
  `CovariantDerivative.covariantDerivative_smul_section_vectorField`: the Leibniz rule for the
  covariant derivative of a function multiple of a section at a tangent vector and along a
  vector field.
* `CovariantDerivative.apply_eq_zero_of_notMem_closure`: a covariant derivative of a section
  vanishes off the closure of its nonzero locus.
* `CovariantDerivative.addOneForm_apply`: evaluate a connection perturbed by an
  endomorphism-valued one-form on a section.
* `CovariantDerivative.difference_apply`: evaluate the difference of two connections on the value
  of a section differentiable at the base point.
* `CovariantDerivative.difference_apply_eq_extend`: evaluate the difference of two connections on
  a fibre vector using a local extension.
* `CovariantDerivative.difference_self`: the difference of a connection with itself vanishes.
-/

public section

open Bundle Set
open scoped Manifold ContDiff Topology

noncomputable section

namespace IsCovariantDerivativeOn

variable
  {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, AddCommGroup (V x)] [∀ x, Module 𝕜 (V x)] [∀ x, TopologicalSpace (V x)]
  [∀ x, IsTopologicalAddGroup (V x)] [∀ x, ContinuousSMul 𝕜 (V x)]
  [FiberBundle F V] [VectorBundle 𝕜 F V]
  {cov : (Π x : M, V x) → (Π x : M, TangentSpace I x →L[𝕜] V x)} {u : Set M}
  {σ σ' : Π x : M, V x} {x : M}

omit [VectorBundle 𝕜 F V] in
/-- A covariant derivative over `u` sends the negative of a section differentiable at a point of
`u` to the negative of its covariant derivative there. -/
theorem neg (hcov : IsCovariantDerivativeOn F cov u) (hσ : MDiffAt (T% σ) x)
    (hx : x ∈ u := by trivial) :
    cov (-σ) x = -cov σ x := by
  rw [← neg_one_smul 𝕜 σ, hcov.smul_const (-1) hσ hx, neg_one_smul]

/-- A covariant derivative over `u` sends the difference of two sections differentiable at a point
of `u` to the difference of their covariant derivatives there. -/
theorem sub (hcov : IsCovariantDerivativeOn F cov u) (hσ : MDiffAt (T% σ) x)
    (hσ' : MDiffAt (T% σ') x) (hx : x ∈ u := by trivial) :
    cov (σ - σ') x = cov σ x - cov σ' x := by
  rw [sub_eq_add_neg, hcov.add hσ (mdifferentiableAt_neg_section hσ') hx, hcov.neg hσ' hx,
    ← sub_eq_add_neg]

/-- A covariant derivative over `u` commutes with finite sums of sections differentiable at a
point of `u`. -/
theorem sum (hcov : IsCovariantDerivativeOn F cov u) {κ : Type*} {s : Finset κ}
    {τ : κ → Π x : M, V x} (hτ : ∀ i ∈ s, MDiffAt (T% (τ i)) x) (hx : x ∈ u := by trivial) :
    cov (∑ i ∈ s, τ i) x = ∑ i ∈ s, cov (τ i) x := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using hcov.zero hx
  | insert i s hi ih =>
    simp only [Finset.mem_insert, forall_eq_or_imp] at hτ
    have hsum : MDiffAt (T% (∑ j ∈ s, τ j)) x := by
      simpa [Finset.sum_apply] using
        MDifferentiableAt.sum_section (t := fun j (y : M) ↦ τ j y) (s := s) hτ.2
    rw [Finset.sum_insert hi, hcov.add hτ.1 hsum hx, ih hτ.2, Finset.sum_insert hi]

omit [VectorBundle 𝕜 F V] in
/-- **Leibniz rule at a tangent vector.** The covariant derivative over `u` of `f • σ` at a point
`x` of `u` along `v` is `f x • ∇_v σ + df_x(v) • σ x`, for `f` and `σ` differentiable at `x`. -/
theorem leibniz_apply (hcov : IsCovariantDerivativeOn F cov u) {f : M → 𝕜}
    (hσ : MDiffAt (T% σ) x) (hf : MDiffAt f x) (v : TangentSpace I x)
    (hx : x ∈ u := by trivial) :
    cov (f • σ) x v = f x • cov σ x v + d% f x v • σ x := by
  rw [hcov.leibniz hσ hf hx]
  simp [add_apply, ContinuousLinearMap.smulRight_apply]

end IsCovariantDerivativeOn

namespace CovariantDerivative

variable
  {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, AddCommGroup (V x)] [∀ x, Module 𝕜 (V x)] [∀ x, TopologicalSpace (V x)]
  [∀ x, IsTopologicalAddGroup (V x)] [∀ x, ContinuousSMul 𝕜 (V x)]
  [FiberBundle F V] [VectorBundle 𝕜 F V]

omit [VectorBundle 𝕜 F V] in
/-- Adding an endomorphism-valued one-form, evaluated on a section. -/
@[simp]
theorem addOneForm_apply (cov : CovariantDerivative I F V)
    (A : Π x : M, V x →L[𝕜] TangentSpace I x →L[𝕜] V x)
    (σ : Π x : M, V x) (x : M) :
    cov.addOneForm A σ x = cov σ x + A x (σ x) := (rfl)

omit [VectorBundle 𝕜 F V] in
/-- **Leibniz rule along a vector field.** The covariant derivative of `f • σ` along a vector
field `Z` is `f` times the covariant derivative of `σ` along `Z`, plus the derivative of `f` along
`Z` times `σ`, for a differentiable function `f` and a differentiable section `σ`. -/
theorem covariantDerivative_smul_section_vectorField (cov : CovariantDerivative I F V)
    {f : M → 𝕜} {σ : Π x : M, V x} {Z : Π x : M, TangentSpace I x}
    (hf : MDiff f) (hσ : MDiff (T% σ)) :
    (fun y ↦ cov (f • σ) y (Z y)) =
      f • (fun y ↦ cov σ y (Z y)) + (fun y ↦ d% f y (Z y)) • σ := by
  funext y
  rw [cov.isCovariantDerivativeOnUniv.leibniz_apply (hσ y) (hf y)]
  simp only [Pi.add_apply, Pi.smul_apply']

/-- **Locality.** A covariant derivative of a section vanishes off the closure of the nonzero
locus of the section. -/
theorem apply_eq_zero_of_notMem_closure (cov : CovariantDerivative I F V) {σ : Π x : M, V x}
    {x : M} (hx : x ∉ closure {y | σ y ≠ 0}) : cov σ x = 0 := by
  have hev : ∀ᶠ y in 𝓝 x, σ y = (0 : Π y : M, V y) y := by
    filter_upwards [isClosed_closure.isOpen_compl.mem_nhds hx] with y hy
    exact Bundle.apply_eq_zero_of_notMem_closure hy
  have h0 : MDiffAt (T% (0 : Π y : M, V y)) x := mdifferentiableAt_zeroSection ..
  have hσ : MDiffAt (T% σ) x := h0.congr_of_eventuallyEq (hev.mono fun y hy ↦ by simp [hy])
  rw [cov.isCovariantDerivativeOnUniv.congr_of_eventuallyEq hσ h0 Filter.univ_mem hev]
  exact congrFun cov.zero x

variable [CompleteSpace 𝕜] [FiniteDimensional 𝕜 F] [ContMDiffVectorBundle 1 F V I]

/-- The difference of two connections evaluated on a section differentiable at the base point. -/
theorem difference_apply (cov cov' : CovariantDerivative I F V)
    {σ : Π x : M, V x} {x : M} (hσ : MDiffAt (T% σ) x) :
    cov.difference cov' x (σ x) = cov σ x - cov' σ x :=
  IsCovariantDerivativeOn.difference_apply cov.isCovariantDerivativeOnUniv
    cov'.isCovariantDerivativeOnUniv (hσ := hσ)

/-- Evaluate the difference of two connections through a local extension of a fibre vector. -/
theorem difference_apply_eq_extend (cov cov' : CovariantDerivative I F V)
    (x : M) (w : V x) :
    cov.difference cov' x w = cov (FiberBundle.extend F w) x - cov' (FiberBundle.extend F w) x := by
  simpa only [FiberBundle.extend_apply_self] using
    cov.difference_apply cov' (FiberBundle.mdifferentiableAt_extend I F w)

/-- The difference of a connection with itself vanishes. -/
@[simp]
theorem difference_self (cov : CovariantDerivative I F V) : cov.difference cov = 0 := by
  ext x w
  simp [difference_apply_eq_extend]

end CovariantDerivative
