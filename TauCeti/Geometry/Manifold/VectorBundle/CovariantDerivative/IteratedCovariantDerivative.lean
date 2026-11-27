/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.DifferentialOperator.PrincipalSymbol.Section
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.ContinuousMultilinearMap
public import TauCeti.Topology.Algebra.Module.FiniteDimension
import TauCeti.Geometry.Manifold.VectorBundle.ContinuousMultilinearMap.LocalFrame
import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Regularity
import TauCeti.Geometry.Manifold.VectorBundle.Hom.Basic
import TauCeti.Geometry.Manifold.VectorBundle.Section.Extension

/-!
# Iterated covariant derivatives

Let `V` be a smooth real vector bundle over a manifold `M`, with a connection `∇` on `V` and a
connection `∇ᵀ` on the tangent bundle. The **`j`-th covariant derivative** `∇ʲσ` of a section
`σ` of `V` is the section of the bundle `Mult^j(TM, V)` of `V`-valued covariant tensors of rank
`j`, with fibres the continuous multilinear maps `(T_xM)^j → V_x`, defined by

`∇⁰σ = σ`, `(∇ʲ⁺¹σ)(u₀, u₁, …, u_j) = (∇_{u₀} ∇ʲσ)(u₁, …, u_j)`,

where `∇ʲσ` is differentiated with the connection induced on `Mult^j(TM, V)` by `∇ᵀ` and `∇`
(`CovariantDerivative.continuousMultilinearMap`). So `∇¹σ` is the covariant derivative `∇σ`
(`CovariantDerivative.iteratedCovariantDerivative_one_apply`), and in general the first slot of
`∇ʲσ` carries the outermost derivative.

The iterated covariant derivatives are the building blocks of the expansion of a differential
operator `P : Γ(V) → Γ(W)` of order `m` through connections, `P σ = ∑_{j ≤ m} A_j(∇ʲσ)` with
bundle maps `A_j`. This file proves the facts about `∇ʲ` that such an expansion rests on:

* `∇ʲ` sends smooth sections to smooth sections
  (`CovariantDerivative.contMDiff_iteratedCovariantDerivative`), and is linear on them
  (`CovariantDerivative.iteratedCovariantDerivativeLinearMap`);
* it is a differential operator of order at most `j` in Grothendieck's sense
  (`CovariantDerivative.iteratedCovariantDerivativeLinearMap_mem_differentialOperators`): by the
  Leibniz rule, the commutator of one step `A ↦ ∇A` with multiplication by a function `f` is
  `A ↦ df ⊗ A`, which is linear over the smooth functions;
* its principal symbol is the `j`-th tensor power of the covector,
  `σ(∇ʲ)(ξ) v = ξ ⊗ ⋯ ⊗ ξ ⊗ v`, the multilinear map `(u₁, …, u_j) ↦ ξ(u₁) ⋯ ξ(u_j) v`
  (`CovariantDerivative.sectionPrincipalSymbol_iteratedCovariantDerivativeLinearMap`). In
  particular it does not depend on the connections.

## Main definitions

* `CovariantDerivative.totalCovariantDerivative covT cov j A`: the total covariant derivative of
  a section `A` of `Mult^j(TM, V)`, the section `(u₀, …, u_j) ↦ (∇_{u₀} A)(u₁, …, u_j)` of
  `Mult^(j+1)(TM, V)`; `CovariantDerivative.totalCovariantDerivativeLinearMap` is the same on smooth
  sections, a first-order operator with principal symbol `A ↦ ξ ⊗ A`.
* `CovariantDerivative.iteratedCovariantDerivative covT cov j σ`: the section `∇ʲσ` of
  `Mult^j(TM, V)`.
* `CovariantDerivative.iteratedCovariantDerivativeLinearMap covT cov j`: `∇ʲ` as a linear map
  between the spaces of smooth sections.

## Implementation notes

The fibres `V x` carry no norm, so Mathlib's `ContinuousLinearMap.uncurryLeft` does not apply to
`∇A : T_xM →L Mult^j(T_xM, V_x)`. Since `T_xM` is finite-dimensional, the uncurried multilinear
map is continuous anyway (`MultilinearMap.continuous_of_finiteDimensional`).

## References

* J. M. Lee, *Introduction to Riemannian Manifolds*, second edition, Springer GTM 176 (2018),
  Chapter 4 (total covariant derivatives).
* I. Kolář, P. W. Michor, J. Slovák, *Natural Operations in Differential Geometry*, Springer,
  1993, §§12, 19 (jets and linear differential operators between vector bundles).
-/

public section

noncomputable section

open Bundle Function TauCeti
open scoped ContDiff Manifold

namespace CovariantDerivative

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)] [∀ x, TopologicalSpace (V x)]
  [∀ x, IsTopologicalAddGroup (V x)] [∀ x, ContinuousSMul ℝ (V x)]
  [FiberBundle F V] [VectorBundle ℝ F V]
  (covT : CovariantDerivative I E (TangentSpace I : M → Type _))
  (cov : CovariantDerivative I F V)

/-- **The total covariant derivative** of a section `A` of the bundle `Mult^j(TM, V)` of
`V`-valued covariant tensors of rank `j`: the section `∇A` of `Mult^(j+1)(TM, V)` given by
`(∇A)(u₀, u₁, …, u_j) = (∇_{u₀} A)(u₁, …, u_j)`, where `A` is differentiated with the connection
induced on `Mult^j(TM, V)` by `covT` on `TM` and `cov` on `V`. -/
def totalCovariantDerivative (j : ℕ)
    (A : Π x : M, ContinuousMultilinearMap ℝ (fun _ : Fin j ↦ TangentSpace I x) (V x)) (x : M) :
    ContinuousMultilinearMap ℝ (fun _ : Fin (j + 1) ↦ TangentSpace I x) (V x) :=
  ⟨LinearMap.uncurryLeft <| ContinuousMultilinearMap.toMultilinearMapLinear ∘ₗ
      (covT.continuousMultilinearMap (Fin j) cov A x).toLinearMap,
    MultilinearMap.continuous_of_finiteDimensional _⟩

@[simp]
theorem totalCovariantDerivative_apply (j : ℕ)
    (A : Π x : M, ContinuousMultilinearMap ℝ (fun _ : Fin j ↦ TangentSpace I x) (V x)) (x : M)
    (u : Fin (j + 1) → TangentSpace I x) :
    totalCovariantDerivative covT cov j A x u =
      covT.continuousMultilinearMap (Fin j) cov A x (u 0) (Fin.tail u) := by
  rw [totalCovariantDerivative]
  -- A continuous multilinear map built from a multilinear map `f` evaluates as `f`.
  exact LinearMap.uncurryLeft_apply _ u

/-- **The `j`-th covariant derivative** `∇ʲσ` of a section `σ` of `V`, a section of the bundle of
continuous multilinear maps `(T_xM)^j → V_x`: `∇⁰σ = σ` and `∇ʲ⁺¹σ` is the total covariant
derivative of `∇ʲσ` (`CovariantDerivative.totalCovariantDerivative`), so that
`(∇ʲ⁺¹σ)(u₀, u₁, …, u_j) = (∇_{u₀} ∇ʲσ)(u₁, …, u_j)`. -/
def iteratedCovariantDerivative : (j : ℕ) → (Π x : M, V x) →
    Π x : M, ContinuousMultilinearMap ℝ (fun _ : Fin j ↦ TangentSpace I x) (V x)
  | 0, σ, x => ContinuousMultilinearMap.constOfIsEmpty ℝ _ (σ x)
  | j + 1, σ, x => totalCovariantDerivative covT cov j (iteratedCovariantDerivative j σ) x

@[simp]
theorem iteratedCovariantDerivative_zero_apply (σ : Π x : M, V x) (x : M)
    (u : Fin 0 → TangentSpace I x) :
    iteratedCovariantDerivative covT cov 0 σ x u = σ x := by
  simp [iteratedCovariantDerivative]

theorem iteratedCovariantDerivative_succ (j : ℕ) (σ : Π x : M, V x) :
    iteratedCovariantDerivative covT cov (j + 1) σ =
      totalCovariantDerivative covT cov j (iteratedCovariantDerivative covT cov j σ) := by
  funext x
  simp [iteratedCovariantDerivative]

/-- The defining recursion of the iterated covariant derivatives, evaluated:
`(∇ʲ⁺¹σ)(u₀, u₁, …, u_j) = (∇_{u₀} ∇ʲσ)(u₁, …, u_j)`. -/
theorem iteratedCovariantDerivative_succ_apply (j : ℕ) (σ : Π x : M, V x) (x : M)
    (u : Fin (j + 1) → TangentSpace I x) :
    iteratedCovariantDerivative covT cov (j + 1) σ x u =
      covT.continuousMultilinearMap (Fin j) cov (iteratedCovariantDerivative covT cov j σ) x
        (u 0) (Fin.tail u) := by
  rw [iteratedCovariantDerivative_succ, totalCovariantDerivative_apply]

section Smooth

variable [T2Space M] [ContMDiffVectorBundle ∞ F V I]
  [ContMDiffCovariantDerivative covT ∞] [ContMDiffCovariantDerivative cov ∞]

/-- **The total covariant derivative of a smooth tensor field is smooth.** -/
theorem contMDiff_totalCovariantDerivative {j : ℕ}
    {A : Π x : M, ContinuousMultilinearMap ℝ (fun _ : Fin j ↦ TangentSpace I x) (V x)}
    (hA : ContMDiff I (I.prod 𝓘(ℝ, ContinuousMultilinearMap ℝ (fun _ : Fin j ↦ E) F)) ∞
      (fun x ↦ TotalSpace.mk' (ContinuousMultilinearMap ℝ (fun _ : Fin j ↦ E) F)
        (E := fun y ↦ ContinuousMultilinearMap ℝ (fun _ : Fin j ↦ TangentSpace I y) (V y)) x
        (A x))) :
    ContMDiff I (I.prod 𝓘(ℝ, ContinuousMultilinearMap ℝ (fun _ : Fin (j + 1) ↦ E) F)) ∞
      (fun x ↦ TotalSpace.mk' (ContinuousMultilinearMap ℝ (fun _ : Fin (j + 1) ↦ E) F)
        (E := fun y ↦ ContinuousMultilinearMap ℝ (fun _ : Fin (j + 1) ↦ TangentSpace I y) (V y))
        x (totalCovariantDerivative covT cov j A x)) := by
  refine (TauCeti.Manifold.contMDiff_continuousMultilinearMap_iff _).2 fun s hs ↦ ?_
  have h := ((contMDiff_continuousMultilinearMap covT cov hA).clm_bundle_apply
    (hs 0)).continuousMultilinearMap_bundle_apply fun i ↦ hs i.succ
  simpa [Fin.tail_def] using h

/-- **The iterated covariant derivatives of a smooth section are smooth**, as sections of the
bundle `Mult^j(TM, V)`. -/
theorem contMDiff_iteratedCovariantDerivative {σ : Π x : M, V x} (hσ : CMDiff ∞ (T% σ))
    (j : ℕ) :
    ContMDiff I (I.prod 𝓘(ℝ, ContinuousMultilinearMap ℝ (fun _ : Fin j ↦ E) F)) ∞
      (fun x ↦ TotalSpace.mk' (ContinuousMultilinearMap ℝ (fun _ : Fin j ↦ E) F)
        (E := fun y ↦ ContinuousMultilinearMap ℝ (fun _ : Fin j ↦ TangentSpace I y) (V y)) x
        (iteratedCovariantDerivative covT cov j σ x)) := by
  induction j with
  | zero =>
    exact (TauCeti.Manifold.contMDiff_continuousMultilinearMap_iff _).2 fun _ _ ↦ by simpa using hσ
  | succ j ih =>
    rw [iteratedCovariantDerivative_succ]
    exact contMDiff_totalCovariantDerivative covT cov ih

/-- **The first covariant derivative is the covariant derivative**: `(∇¹σ)(u) = ∇_u σ`. -/
theorem iteratedCovariantDerivative_one_apply {σ : Π x : M, V x} (hσ : CMDiff ∞ (T% σ)) (x : M)
    (u : Fin 1 → TangentSpace I x) :
    iteratedCovariantDerivative covT cov 1 σ x u = cov σ x (u 0) := by
  have h := continuousMultilinearMap_apply covT cov
    ((contMDiff_iteratedCovariantDerivative covT cov hσ 0 x).mdifferentiableAt (by simp))
    (s := fun i ↦ i.elim0) (fun i ↦ i.elim0) (u 0)
  rw [iteratedCovariantDerivative_succ_apply, Subsingleton.elim (Fin.tail u) _, h]
  simp

/-! ### The iterated covariant derivatives as operators on smooth sections -/

/-- The total covariant derivative `A ↦ ∇A`, as a linear map from the smooth sections of
`Mult^j(TM, V)` to those of `Mult^(j+1)(TM, V)`. -/
def totalCovariantDerivativeLinearMap (j : ℕ) :
    Cₛ^∞⟮I; ContinuousMultilinearMap ℝ (fun _ : Fin j ↦ E) F,
        fun x ↦ ContinuousMultilinearMap ℝ (fun _ : Fin j ↦ TangentSpace I x) (V x)⟯ →ₗ[ℝ]
      Cₛ^∞⟮I; ContinuousMultilinearMap ℝ (fun _ : Fin (j + 1) ↦ E) F,
        fun x ↦ ContinuousMultilinearMap ℝ (fun _ : Fin (j + 1) ↦ TangentSpace I x) (V x)⟯ where
  toFun A := ⟨totalCovariantDerivative covT cov j A,
    contMDiff_totalCovariantDerivative covT cov A.contMDiff⟩
  map_add' A B := ContMDiffSection.ext fun x ↦ by
    ext u
    simp [(covT.continuousMultilinearMap (Fin j) cov).isCovariantDerivativeOnUniv.add
      A.mdifferentiableAt B.mdifferentiableAt]
  map_smul' c A := ContMDiffSection.ext fun x ↦ by
    ext u
    simp [(covT.continuousMultilinearMap (Fin j) cov).isCovariantDerivativeOnUniv.smul_const c
      A.mdifferentiableAt]

@[simp]
theorem totalCovariantDerivativeLinearMap_apply (j : ℕ)
    (A : Cₛ^∞⟮I; ContinuousMultilinearMap ℝ (fun _ : Fin j ↦ E) F,
      fun x ↦ ContinuousMultilinearMap ℝ (fun _ : Fin j ↦ TangentSpace I x) (V x)⟯) (x : M) :
    totalCovariantDerivativeLinearMap covT cov j A x = totalCovariantDerivative covT cov j A x :=
  (rfl)

omit [T2Space M] [ContMDiffVectorBundle ∞ F V I] [ContMDiffCovariantDerivative covT ∞]
  [ContMDiffCovariantDerivative cov ∞] in
/-- **The Leibniz rule for the total covariant derivative**:
`∇(f A)(u₀, u₁, …, u_j) = f ∇A(u₀, u₁, …, u_j) + df(u₀) A(u₁, …, u_j)`. -/
theorem totalCovariantDerivative_smul_apply {j : ℕ} (f : C^∞⟮I, M; ℝ⟯)
    (A : Cₛ^∞⟮I; ContinuousMultilinearMap ℝ (fun _ : Fin j ↦ E) F,
      fun x ↦ ContinuousMultilinearMap ℝ (fun _ : Fin j ↦ TangentSpace I x) (V x)⟯) (x : M)
    (u : Fin (j + 1) → TangentSpace I x) :
    totalCovariantDerivative covT cov j ⇑(f • A) x u =
      f x • totalCovariantDerivative covT cov j A x u +
        mvfderiv I f x (u 0) • A x (Fin.tail u) := by
  simp only [totalCovariantDerivative_apply,
    (covT.continuousMultilinearMap (Fin j) cov).apply_smul f A x, add_apply, smul_apply,
    ContinuousLinearMap.smulRight_apply]

/-- **The total covariant derivative is a first-order operator**: its commutator with
multiplication by `f` is `A ↦ df ⊗ A`, which is linear over the smooth functions. -/
theorem totalCovariantDerivativeLinearMap_mem_differentialOperators_one (j : ℕ) :
    totalCovariantDerivativeLinearMap covT cov j ∈
      differentialOperators ℝ C^∞⟮I, M; ℝ⟯
        Cₛ^∞⟮I; ContinuousMultilinearMap ℝ (fun _ : Fin j ↦ E) F,
          fun x ↦ ContinuousMultilinearMap ℝ (fun _ : Fin j ↦ TangentSpace I x) (V x)⟯
        Cₛ^∞⟮I; ContinuousMultilinearMap ℝ (fun _ : Fin (j + 1) ↦ E) F,
          fun x ↦ ContinuousMultilinearMap ℝ (fun _ : Fin (j + 1) ↦ TangentSpace I x) (V x)⟯ 1 := by
  refine mem_differentialOperators_succ_iff.2 fun f ↦
    mem_differentialOperators_zero_iff.2 fun g A ↦ ContMDiffSection.ext fun x ↦ ?_
  ext u
  simp only [smulCommutator_apply_apply, ContMDiffSection.coe_sub, Pi.sub_apply,
    ContMDiffSection.smul_apply, totalCovariantDerivativeLinearMap_apply,
    totalCovariantDerivative_smul_apply, sub_apply, smul_apply, smul_comm f g A]
  module

/-- The iterated covariant derivative `σ ↦ ∇ʲσ`, as a linear map from the smooth sections of `V`
to those of `Mult^j(TM, V)`: `∇⁰σ = σ` and `∇ʲ⁺¹ = ∇ ∘ ∇ʲ` with the total covariant derivative
`CovariantDerivative.totalCovariantDerivativeLinearMap`. -/
def iteratedCovariantDerivativeLinearMap : (j : ℕ) →
    Cₛ^∞⟮I; F, V⟯ →ₗ[ℝ] Cₛ^∞⟮I; ContinuousMultilinearMap ℝ (fun _ : Fin j ↦ E) F,
      fun x ↦ ContinuousMultilinearMap ℝ (fun _ : Fin j ↦ TangentSpace I x) (V x)⟯
  | 0 => {
      toFun σ := ⟨iteratedCovariantDerivative covT cov 0 σ,
        contMDiff_iteratedCovariantDerivative covT cov (by simpa using σ.contMDiff) 0⟩
      map_add' σ τ := ContMDiffSection.ext fun x ↦ by ext u; simp
      map_smul' c σ := ContMDiffSection.ext fun x ↦ by ext u; simp }
  | j + 1 => totalCovariantDerivativeLinearMap covT cov j ∘ₗ iteratedCovariantDerivativeLinearMap j

theorem iteratedCovariantDerivativeLinearMap_succ (j : ℕ) :
    iteratedCovariantDerivativeLinearMap covT cov (j + 1) =
      totalCovariantDerivativeLinearMap covT cov j ∘ₗ
        iteratedCovariantDerivativeLinearMap covT cov j :=
  (rfl)

@[simp]
theorem iteratedCovariantDerivativeLinearMap_apply (j : ℕ) (σ : Cₛ^∞⟮I; F, V⟯) (x : M) :
    iteratedCovariantDerivativeLinearMap covT cov j σ x =
      iteratedCovariantDerivative covT cov j σ x := by
  induction j generalizing x with
  | zero => rfl
  | succ j ih =>
    rw [iteratedCovariantDerivativeLinearMap_succ, LinearMap.comp_apply,
      totalCovariantDerivativeLinearMap_apply, iteratedCovariantDerivative_succ]
    exact congrArg (totalCovariantDerivative covT cov j · x) (funext ih)

/-- **The `j`-th covariant derivative is a differential operator of order at most `j`.** -/
theorem iteratedCovariantDerivativeLinearMap_mem_differentialOperators (j : ℕ) :
    iteratedCovariantDerivativeLinearMap covT cov j ∈
      differentialOperators ℝ C^∞⟮I, M; ℝ⟯ Cₛ^∞⟮I; F, V⟯
        Cₛ^∞⟮I; ContinuousMultilinearMap ℝ (fun _ : Fin j ↦ E) F,
          fun x ↦ ContinuousMultilinearMap ℝ (fun _ : Fin j ↦ TangentSpace I x) (V x)⟯ j := by
  induction j with
  | zero =>
    exact mem_differentialOperators_zero_iff.2 fun f σ ↦ ContMDiffSection.ext fun x ↦ by
      ext u
      simp
  | succ j ih =>
    rw [iteratedCovariantDerivativeLinearMap_succ]
    exact differentialOperators_mono (add_comm 1 j).le (comp_mem_differentialOperators
      (totalCovariantDerivativeLinearMap_mem_differentialOperators_one covT cov j) ih)

/-! ### Principal symbols -/

variable [FiniteDimensional ℝ F] {x : M}

/-- **The principal symbol of the total covariant derivative** is `σ(∇)(ξ) A = ξ ⊗ A`, the tensor
`(u₀, u₁, …, u_j) ↦ ξ(u₀) A(u₁, …, u_j)`. -/
@[simp]
theorem sectionPrincipalSymbol_totalCovariantDerivativeLinearMap (hx : I.IsInteriorPoint x)
    (j : ℕ) (ξ : TangentSpace I x →L[ℝ] ℝ)
    (a : ContinuousMultilinearMap ℝ (fun _ : Fin j ↦ TangentSpace I x) (V x))
    (u : Fin (j + 1) → TangentSpace I x) :
    sectionPrincipalSymbol I hx ⟨totalCovariantDerivativeLinearMap covT cov j,
      totalCovariantDerivativeLinearMap_mem_differentialOperators_one covT cov j⟩ ξ a u =
      ξ (u 0) • a (Fin.tail u) := by
  obtain ⟨f, rfl⟩ : ∃ f : C^∞⟮I, M; ℝ⟯, mvfderiv I f x = ξ := ⟨_, mvfderiv_covectorLift hx ξ⟩
  obtain ⟨A, rfl⟩ := ContMDiffSection.evalLinearMap_surjective (I := I)
    (F := ContinuousMultilinearMap ℝ (fun _ : Fin j ↦ E) F)
    (V := fun x ↦ ContinuousMultilinearMap ℝ (fun _ : Fin j ↦ TangentSpace I x) (V x)) ∞ x a
  rw [ContMDiffSection.evalLinearMap_apply, sectionPrincipalSymbol_mvfderiv_of_order_one,
    totalCovariantDerivativeLinearMap_apply, totalCovariantDerivativeLinearMap_apply, sub_apply,
    smul_apply, totalCovariantDerivative_smul_apply, add_sub_cancel_left]

/-- **The principal symbol of the `j`-th covariant derivative** is the `j`-th tensor power of the
covector: `σ(∇ʲ)(ξ) v = ξ ⊗ ⋯ ⊗ ξ ⊗ v`, the multilinear map `(u₁, …, u_j) ↦ ξ(u₁) ⋯ ξ(u_j) v`. In
particular it does not depend on the connections. -/
theorem sectionPrincipalSymbol_iteratedCovariantDerivativeLinearMap (hx : I.IsInteriorPoint x)
    (j : ℕ) (ξ : TangentSpace I x →L[ℝ] ℝ) (v : V x) :
    sectionPrincipalSymbol I hx ⟨iteratedCovariantDerivativeLinearMap covT cov j,
      iteratedCovariantDerivativeLinearMap_mem_differentialOperators covT cov j⟩ ξ v =
      (ContinuousMultilinearMap.mkPiRing ℝ (Fin j) v).compContinuousLinearMap fun _ ↦ ξ := by
  induction j generalizing v with
  | zero =>
    obtain ⟨f, rfl⟩ : ∃ f : C^∞⟮I, M; ℝ⟯, mvfderiv I f x = ξ := ⟨_, mvfderiv_covectorLift hx ξ⟩
    obtain ⟨σ, rfl⟩ := ContMDiffSection.evalLinearMap_surjective (I := I) (F := F) (V := V) ∞ x v
    ext u
    rw [ContMDiffSection.evalLinearMap_apply, sectionPrincipalSymbol_mvfderiv]
    simp only [ContinuousMultilinearMap.compContinuousLinearMap_apply,
      ContinuousMultilinearMap.mkPiRing_apply, Finset.univ_eq_empty, Finset.prod_empty, one_smul]
    simp
  | succ j ih =>
    have h := sectionPrincipalSymbol_comp hx
      ⟨_, totalCovariantDerivativeLinearMap_mem_differentialOperators_one covT cov j⟩
      ⟨_, iteratedCovariantDerivativeLinearMap_mem_differentialOperators covT cov j⟩ ξ
    dsimp only at h
    rw [sectionPrincipalSymbol_congr hx (add_comm j 1) (P' := ⟨_, comp_mem_differentialOperators
      (totalCovariantDerivativeLinearMap_mem_differentialOperators_one covT cov j)
      (iteratedCovariantDerivativeLinearMap_mem_differentialOperators covT cov j)⟩)
      (iteratedCovariantDerivativeLinearMap_succ covT cov j), h, LinearMap.comp_apply, ih]
    ext u
    simp [Fin.prod_univ_succ, mul_smul, Fin.tail_def]

/-- The principal symbol of the `j`-th covariant derivative, evaluated:
`σ(∇ʲ)(ξ) v (u₁, …, u_j) = ξ(u₁) ⋯ ξ(u_j) v`. -/
@[simp]
theorem sectionPrincipalSymbol_iteratedCovariantDerivativeLinearMap_apply
    (hx : I.IsInteriorPoint x) (j : ℕ) (ξ : TangentSpace I x →L[ℝ] ℝ) (v : V x)
    (u : Fin j → TangentSpace I x) :
    sectionPrincipalSymbol I hx ⟨iteratedCovariantDerivativeLinearMap covT cov j,
      iteratedCovariantDerivativeLinearMap_mem_differentialOperators covT cov j⟩ ξ v u =
      (∏ i, ξ (u i)) • v := by
  simp [sectionPrincipalSymbol_iteratedCovariantDerivativeLinearMap]

end Smooth

end CovariantDerivative
