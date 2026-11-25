/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Distribution.SchwartzKernel.Basic
public import Mathlib.Topology.Algebra.Module.FiniteDimension
import TauCeti.Analysis.Distribution.TestFunction.Basic
import TauCeti.Analysis.Distribution.TestFunction.TensorDensity

/-!
# The Schwartz kernel theorem with finite-rank coefficients

Let `Ω ⊆ ℝ^a` and `O ⊆ ℝ^b` be open sets, `W` a finite-dimensional real normed space and `F` a
real Banach space. An operator from the `W`-valued test functions on `O` to the `F`-valued
distributions on `Ω` has a kernel with values in `W →L[ℝ] F`: on trivial bundles with fibres `W`
and `F` over open subsets of Euclidean space, this is the kernel theorem with coefficients in the
bundle `F ⊠ W*`, the local form of the Schwartz kernel theorem on vector bundles.

A distribution `K` on an open set `V ⊇ Ω ×ˢ O` with values in `W →L[ℝ] F` defines the operator
`Distribution.vectorKernelOperator hV K : 𝓓(O, W) →ₗ[ℝ] 𝓓'(Ω, F)`. On the test function
`g • w : y ↦ g y • w`, for a real test function `g` and a vector `w ∈ W`, it is

`⟨vectorKernelOperator hV K (g • w), φ⟩ = K (φ ⊗ g) w`

(`Distribution.vectorKernelOperator_postcompCLM_toSpanSingleton`), where
`(φ ⊗ g)(x, y) = g y • φ x` is `TestFunction.prodSMulCLM g hV φ`. Every `W`-valued test function
is a finite sum of such products (`TestFunction.sum_postcompCLM_toSpanSingleton_coord`), so this
determines the operator; in coordinates in any basis `b` of `W` it reads
`⟨vectorKernelOperator hV K ψ, φ⟩ = ∑ i, K (φ ⊗ (b.coord i ∘ ψ)) (b i)`
(`Distribution.vectorKernelOperator_apply_eq_sum`). The operator determines `K` when
`V = Ω ×ˢ O` (`Distribution.vectorKernelOperator_injective`).

**The Schwartz kernel theorem** (`LinearMap.existsUnique_vectorKernelOperator_eq`): a linear map
`A : 𝓓(O, W) → 𝓓'(Ω, F)` which is continuous for the weak topology of distributions is
`vectorKernelOperator hV K` for exactly one `K ∈ 𝓓'(Ω × O, W →L[ℝ] F)`. Its kernel is the kernel,
supplied by the scalar theorem `LinearMap.existsUnique_kernelOperator_eq` with values in the
Banach space `W →L[ℝ] F`, of the operator `g ↦ (w ↦ A (g • w))` on real test functions.

## Main declarations

* `Distribution.vectorKernelOperator`: the operator `𝓓(O, W) → 𝓓'(Ω, F)` with kernel `K`.
* `Distribution.vectorKernelOperator_postcompCLM_toSpanSingleton`,
  `Distribution.vectorKernelOperator_apply_eq_sum`: its values.
* `Distribution.continuous_vectorKernelOperator_apply`: it is weakly continuous.
* `Distribution.vectorKernelOperator_injective`: it determines its kernel.
* `LinearMap.existsUnique_vectorKernelOperator_eq`,
  `ContinuousLinearMap.existsUnique_vectorKernelOperator_eq`: the Schwartz kernel theorem for
  weakly continuous and for continuous linear maps `𝓓(O, W) → 𝓓'(Ω, F)`.
* `LinearMap.exists_vectorKernelOperator_eq_iff`: the operators with a kernel are exactly the
  weakly continuous ones.

## References

* L. Hörmander, *The Analysis of Linear Partial Differential Operators I*, second edition,
  Springer, 1990, Theorem 5.2.1 (the Schwartz kernel theorem).
-/

public section

noncomputable section

open TopologicalSpace TestFunction
open scoped Distributions

namespace Distribution

variable {E D : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup D]
  [NormedSpace ℝ D] {Ω : Opens E} {O : Opens D} {V : Opens (E × D)}
  {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The **operator with `W →L[ℝ] F`-valued Schwartz kernel** `K`: a distribution `K` on an open set
`V ⊇ Ω ×ˢ O` with values in `W →L[ℝ] F` defines a linear map `𝓓(O, W) → 𝓓'(Ω, F)`. It sends the
test function `y ↦ g y • w` to the distribution `φ ↦ K (φ ⊗ g) w`
(`Distribution.vectorKernelOperator_postcompCLM_toSpanSingleton`); it is defined through the
coordinates in `Module.finBasis ℝ W`, and in any basis it is given by
`Distribution.vectorKernelOperator_apply_eq_sum`. It is linear in `K`. -/
def vectorKernelOperator (hV : (Ω : Set E) ×ˢ (O : Set D) ⊆ V) :
    𝓓'(V, W →L[ℝ] F) →ₗ[ℝ] 𝓓(O, W) →ₗ[ℝ] 𝓓'(Ω, F) :=
  ∑ i, ((kernelOperator hV).comp
      (mapCLM (ContinuousLinearMap.apply ℝ F (Module.finBasis ℝ W i))).toLinearMap).compl₂
    (postcompCLM (((Module.finBasis ℝ W).coord i).toContinuousLinearMap)).toLinearMap

/-- The operator with kernel `K` pairs the test function `y ↦ g y • w` with `φ` to
`K (φ ⊗ g) w`. -/
@[simp]
theorem vectorKernelOperator_postcompCLM_toSpanSingleton
    (hV : (Ω : Set E) ×ˢ (O : Set D) ⊆ V) (K : 𝓓'(V, W →L[ℝ] F)) (g : 𝓓(O, ℝ)) (w : W)
    (φ : 𝓓(Ω, ℝ)) :
    vectorKernelOperator hV K (postcompCLM (ContinuousLinearMap.toSpanSingleton ℝ w) g) φ =
      K (prodSMulCLM g hV φ) w := by
  -- The `i`-th coordinate function of `y ↦ g y • w` is `(Module.finBasis ℝ W).coord i w • g`;
  -- expand `w` in the same basis on the right.
  conv_rhs => rw [← (Module.finBasis ℝ W).sum_repr w, map_sum]
  simp [vectorKernelOperator]

/-- **The operator with kernel `K` in coordinates.** For any basis `b` of `W`, the operator with
kernel `K` pairs `ψ` with `φ` to `∑ i, K (φ ⊗ (b.coord i ∘ ψ)) (b i)`. -/
theorem vectorKernelOperator_apply_eq_sum {ι : Type*} [Fintype ι] (b : Module.Basis ι ℝ W)
    (hV : (Ω : Set E) ×ˢ (O : Set D) ⊆ V) (K : 𝓓'(V, W →L[ℝ] F)) (ψ : 𝓓(O, W))
    (φ : 𝓓(Ω, ℝ)) :
    vectorKernelOperator hV K ψ φ = ∑ i, K (prodSMulCLM
      (postcompCLM ((b.coord i).toContinuousLinearMap) ψ) hV φ) (b i) := by
  conv_lhs => rw [← sum_postcompCLM_toSpanSingleton_coord b ψ]
  simp

/-- The operator with kernel `K` is continuous for the weak topology of distributions:
`ψ ↦ ⟨vectorKernelOperator hV K ψ, φ⟩` is continuous for every test function `φ`. -/
theorem continuous_vectorKernelOperator_apply (hV : (Ω : Set E) ×ˢ (O : Set D) ⊆ V)
    (K : 𝓓'(V, W →L[ℝ] F)) (φ : 𝓓(Ω, ℝ)) :
    Continuous fun ψ ↦ vectorKernelOperator hV K ψ φ := by
  simp only [vectorKernelOperator_apply_eq_sum (Module.finBasis ℝ W)]
  refine continuous_finsetSum _ fun i _ ↦ ?_
  exact (ContinuousLinearMap.apply ℝ F _).continuous.comp <| K.continuous.comp <|
    (continuous_prodSMulCLM_apply hV φ).comp (postcompCLM _).continuous

/-- A distribution on `Ω ×ˢ O` with values in `W →L[ℝ] F` is determined by its operator. -/
theorem vectorKernelOperator_injective (hV : (V : Set (E × D)) = (Ω : Set E) ×ˢ (O : Set D)) :
    Function.Injective (vectorKernelOperator (W := W) (F := F) hV.symm.subset) := fun K K' h ↦
  kernelOperator_injective hV <| by
    ext g φ w
    simpa using congr($h (postcompCLM (ContinuousLinearMap.toSpanSingleton ℝ w) g) φ)

end Distribution

namespace LinearMap

open Distribution

variable {a b : Type*} [Fintype a] [Fintype b] {Ω : Opens (a → ℝ)} {O : Opens (b → ℝ)}
  {V : Opens ((a → ℝ) × (b → ℝ))}
  {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

/-- **The Schwartz kernel theorem with finite-rank coefficients.** Let `Ω ⊆ ℝ^a` and `O ⊆ ℝ^b` be
open sets, `W` a finite-dimensional real normed space and `F` a real Banach space, and let
`A : 𝓓(O, W) → 𝓓'(Ω, F)` be a linear map which is continuous for the weak topology of
distributions: `ψ ↦ ⟨A ψ, φ⟩` is continuous for every test function `φ` on `Ω`. Then there is a
unique distribution `K` on `V = Ω × O` with values in `W →L[ℝ] F` such that
`A = vectorKernelOperator hV K`, that is, `⟨A (g • w), φ⟩ = K (φ ⊗ g) w` for real test functions
`φ` and `g` and vectors `w ∈ W`. -/
theorem existsUnique_vectorKernelOperator_eq (A : 𝓓(O, W) →ₗ[ℝ] 𝓓'(Ω, F))
    (hA : ∀ φ, Continuous fun ψ ↦ A ψ φ)
    (hV : (V : Set ((a → ℝ) × (b → ℝ))) = (Ω : Set (a → ℝ)) ×ˢ (O : Set (b → ℝ))) :
    ∃! K : 𝓓'(V, W →L[ℝ] F), vectorKernelOperator hV.symm.subset K = A := by
  set e := Module.finBasis ℝ W
  -- The operator `g ↦ (w ↦ A (g • w))` on real test functions, with values in the distributions
  -- with values in `W →L[ℝ] F`, written in the coordinates of the basis `e`.
  let B : 𝓓(O, ℝ) →ₗ[ℝ] 𝓓'(Ω, W →L[ℝ] F) := ∑ i,
    (mapCLM (ContinuousLinearMap.smulRightL ℝ ℝ ℝ W F
        ((e.coord i).toContinuousLinearMap))).toLinearMap ∘ₗ A ∘ₗ
      (postcompCLM (ContinuousLinearMap.toSpanSingleton ℝ (e i))).toLinearMap
  have hB (g : 𝓓(O, ℝ)) (φ : 𝓓(Ω, ℝ)) (w : W) :
      B g φ w = A (postcompCLM (ContinuousLinearMap.toSpanSingleton ℝ w) g) φ := by
    -- Expand `y ↦ g y • w` in the basis `e` inside `A`, and use linearity of `A`.
    conv_rhs => rw [← sum_postcompCLM_toSpanSingleton_coord e
      (postcompCLM (ContinuousLinearMap.toSpanSingleton ℝ w) g)]
    simp [B]
  have hBc (φ : 𝓓(Ω, ℝ)) : Continuous fun g ↦ B g φ :=
    continuous_clm_apply.2 fun w ↦ by
      simpa only [hB, Function.comp_def] using (hA φ).comp (postcompCLM _).continuous
  obtain ⟨K, hK, -⟩ := existsUnique_kernelOperator_eq B hBc hV
  have hKA : vectorKernelOperator hV.symm.subset K = A := by
    ext ψ φ
    rw [vectorKernelOperator_apply_eq_sum e]
    conv_rhs => rw [← sum_postcompCLM_toSpanSingleton_coord e ψ]
    simp only [← kernelOperator_apply, hK, hB, map_sum, sum_apply]
  exact ⟨K, hKA, fun K' hK' ↦ vectorKernelOperator_injective hV (hK'.trans hKA.symm)⟩

/-- **The operators with a `W →L[ℝ] F`-valued Schwartz kernel** are exactly the linear maps
`𝓓(O, W) → 𝓓'(Ω, F)` that are continuous for the weak topology of distributions. -/
theorem exists_vectorKernelOperator_eq_iff (A : 𝓓(O, W) →ₗ[ℝ] 𝓓'(Ω, F))
    (hV : (V : Set ((a → ℝ) × (b → ℝ))) = (Ω : Set (a → ℝ)) ×ˢ (O : Set (b → ℝ))) :
    (∃ K : 𝓓'(V, W →L[ℝ] F), vectorKernelOperator hV.symm.subset K = A) ↔
      ∀ φ, Continuous fun ψ ↦ A ψ φ := by
  refine ⟨?_, fun hA ↦ (existsUnique_vectorKernelOperator_eq A hA hV).exists⟩
  rintro ⟨K, rfl⟩ φ
  exact continuous_vectorKernelOperator_apply _ K φ

end LinearMap

namespace ContinuousLinearMap

open Distribution

variable {a b : Type*} [Fintype a] [Fintype b] {Ω : Opens (a → ℝ)} {O : Opens (b → ℝ)}
  {V : Opens ((a → ℝ) × (b → ℝ))}
  {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

/-- **The Schwartz kernel theorem with finite-rank coefficients, for continuous operators.** Every
continuous linear map `A : 𝓓(O, W) → 𝓓'(Ω, F)`, for the topology of compact convergence on
distributions, is the operator `vectorKernelOperator hV K` of a unique distribution `K` on
`V = Ω × O` with values in `W →L[ℝ] F`. -/
theorem existsUnique_vectorKernelOperator_eq (A : 𝓓(O, W) →L[ℝ] 𝓓'(Ω, F))
    (hV : (V : Set ((a → ℝ) × (b → ℝ))) = (Ω : Set (a → ℝ)) ×ˢ (O : Set (b → ℝ))) :
    ∃! K : 𝓓'(V, W →L[ℝ] F), vectorKernelOperator hV.symm.subset K = A :=
  LinearMap.existsUnique_vectorKernelOperator_eq _
    (fun φ ↦ (continuous_eval_const φ).comp A.continuous) hV

end ContinuousLinearMap
