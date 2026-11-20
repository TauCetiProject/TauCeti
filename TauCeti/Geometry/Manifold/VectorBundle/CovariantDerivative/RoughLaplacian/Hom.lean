/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.RoughLaplacian
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.SecondCovariantDerivative.Hom
import TauCeti.Geometry.Manifold.IsManifold.Basic

/-!
# The rough Laplacian of a homomorphism applied to a section

Let `∇'` and `∇` be smooth connections on vector bundles `V'` and `V` over a Riemannian manifold,
with `V'` of finite rank, and give `Hom(V', V)` the induced connection
(`CovariantDerivative.hom`). For a smooth homomorphism `A : V' → V` and a smooth section `s` of
`V'`, tracing the Leibniz rule for the second covariant derivative
(`CovariantDerivative.secondCovariantDerivative_clm_apply`) gives

`∇*∇(A s) = (∇*∇A) s - 2 ∑ᵢ (∇_{eᵢ} A)(∇'_{eᵢ} s) + A (∇'*∇' s)`

for every orthonormal basis `eᵢ` of the tangent space
(`CovariantDerivative.roughLaplacian_clm_apply`). So the commutator of the rough Laplacian with a
bundle map is a first-order operator whose coefficients are the first two covariant derivatives of
the map. For normed fibres this bounds it pointwise
(`CovariantDerivative.norm_roughLaplacian_clm_apply_sub_le`):

`|∇*∇(A s) - A (∇'*∇' s)| ≤ |∇*∇A| |s| + 2 n |∇A| |∇'s|`,  `n = dim M`.

For instance, if `A` is a field of projections that is not parallel, the rough Laplacian of a
section of its image need not lie in the image; this estimate controls the defect by `|s|` and
`|∇'s|` alone.

## References

* J. M. Lee, *Introduction to Riemannian Manifolds*, 2nd ed., Springer GTM 176 (2018),
  Chapter 4 (induced connections and the second covariant derivative).
-/

public section

open Bundle FiberBundle Module
open scoped ContDiff Manifold

noncomputable section

namespace CovariantDerivative

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  (covT : _root_.CovariantDerivative I E (TangentSpace I : M → Type _))

section Algebraic

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)]
  [∀ x, TopologicalSpace (V x)] [∀ x, IsTopologicalAddGroup (V x)]
  [∀ x, ContinuousSMul ℝ (V x)] [FiberBundle F V] [VectorBundle ℝ F V]
  [ContMDiffVectorBundle ∞ F V I]
  {F' : Type*} [NormedAddCommGroup F'] [NormedSpace ℝ F'] [FiniteDimensional ℝ F']
  {V' : M → Type*} [TopologicalSpace (TotalSpace F' V')]
  [∀ x, AddCommGroup (V' x)] [∀ x, Module ℝ (V' x)]
  [∀ x, TopologicalSpace (V' x)] [∀ x, IsTopologicalAddGroup (V' x)]
  [∀ x, ContinuousSMul ℝ (V' x)] [FiberBundle F' V'] [VectorBundle ℝ F' V']
  [ContMDiffVectorBundle ∞ F' V' I]
  (cov : _root_.CovariantDerivative I F V) [ContMDiffCovariantDerivative cov ∞]
  (cov' : _root_.CovariantDerivative I F' V') [ContMDiffCovariantDerivative cov' ∞]
  {A : Π x : M, V' x →L[ℝ] V x} {s : Π x : M, V' x}

/-- **Leibniz rule for the rough Laplacian of a homomorphism applied to a section.** For a smooth
homomorphism `A : V' → V`, a smooth section `s` of `V'` and an orthonormal basis `eᵢ` of the
tangent space at `x`,
`∇*∇(A s) = (∇*∇A) s - 2 ∑ᵢ (∇_{eᵢ} A)(∇'_{eᵢ} s) + A (∇'*∇' s)`, where `∇*∇A` is the rough
Laplacian for the induced connection on `Hom(V', V)`. -/
theorem roughLaplacian_clm_apply
    (hA : ContMDiff I (I.prod 𝓘(ℝ, F' →L[ℝ] F)) ∞
      (fun y ↦ TotalSpace.mk' (F' →L[ℝ] F) (E := fun z ↦ V' z →L[ℝ] V z) y (A y)))
    (hs : CMDiff ∞ (T% s)) (x : M) {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℝ (TangentSpace I x)) :
    cov.roughLaplacian covT (fun y ↦ A y (s y)) x =
      (cov'.hom cov).roughLaplacian covT A x (s x) -
        (2 : ℝ) • ∑ i, cov'.hom cov A x (b i) (cov' s x (b i)) +
          A x (cov'.roughLaplacian covT s x) := by
  rw [roughLaplacian_eq_sum cov covT _ x b, roughLaplacian_eq_sum (cov'.hom cov) covT _ x b,
    roughLaplacian_eq_sum cov' covT _ x b]
  simp only [secondCovariantDerivative_clm_apply cov covT cov' hA hs, Finset.sum_add_distrib,
    neg_apply, sum_apply, map_neg, map_sum]
  module

end Algebraic

section Normed

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, NormedAddCommGroup (V x)] [∀ x, NormedSpace ℝ (V x)]
  [FiberBundle F V] [VectorBundle ℝ F V] [ContMDiffVectorBundle ∞ F V I]
  {F' : Type*} [NormedAddCommGroup F'] [NormedSpace ℝ F'] [FiniteDimensional ℝ F']
  {V' : M → Type*} [TopologicalSpace (TotalSpace F' V')]
  [∀ x, NormedAddCommGroup (V' x)] [∀ x, NormedSpace ℝ (V' x)]
  [FiberBundle F' V'] [VectorBundle ℝ F' V'] [ContMDiffVectorBundle ∞ F' V' I]
  (cov : _root_.CovariantDerivative I F V) [ContMDiffCovariantDerivative cov ∞]
  (cov' : _root_.CovariantDerivative I F' V') [ContMDiffCovariantDerivative cov' ∞]
  {A : Π x : M, V' x →L[ℝ] V x} {s : Π x : M, V' x}

/-- **The commutator of the rough Laplacian with a homomorphism.** For a smooth homomorphism
`A : V' → V` and a smooth section `s` of `V'` over a Riemannian manifold of dimension `n`,
`|∇*∇(A s) - A (∇'*∇' s)| ≤ |∇*∇A| |s| + 2 n |∇A| |∇'s|`, with operator norms on the right. -/
theorem norm_roughLaplacian_clm_apply_sub_le
    (hA : ContMDiff I (I.prod 𝓘(ℝ, F' →L[ℝ] F)) ∞
      (fun y ↦ TotalSpace.mk' (F' →L[ℝ] F) (E := fun z ↦ V' z →L[ℝ] V z) y (A y)))
    (hs : CMDiff ∞ (T% s)) (x : M) :
    ‖cov.roughLaplacian covT (fun y ↦ A y (s y)) x - A x (cov'.roughLaplacian covT s x)‖ ≤
      ‖(cov'.hom cov).roughLaplacian covT A x‖ * ‖s x‖ +
        2 * finrank ℝ E * ‖cov'.hom cov A x‖ * ‖cov' s x‖ := by
  set b := stdOrthonormalBasis ℝ (TangentSpace I x)
  rw [roughLaplacian_clm_apply covT cov cov' hA hs x b, add_sub_cancel_right]
  -- Each term of the sum has norm at most `|∇A| |∇'s|`, as the `eᵢ` are unit vectors.
  have hterm (i) : ‖cov'.hom cov A x (b i) (cov' s x (b i))‖ ≤
      ‖cov'.hom cov A x‖ * ‖cov' s x‖ := by
    calc _ ≤ ‖cov'.hom cov A x (b i)‖ * ‖cov' s x (b i)‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ (‖cov'.hom cov A x‖ * ‖b i‖) * (‖cov' s x‖ * ‖b i‖) := by
          gcongr
          · exact ContinuousLinearMap.le_opNorm _ _
          · exact ContinuousLinearMap.le_opNorm _ _
      _ = _ := by rw [b.orthonormal.1 i]; ring
  have hsum : ‖∑ i, cov'.hom cov A x (b i) (cov' s x (b i))‖ ≤
      finrank ℝ E * (‖cov'.hom cov A x‖ * ‖cov' s x‖) := by
    refine (norm_sum_le _ _).trans ((Finset.sum_le_sum fun i _ ↦ hterm i).trans ?_)
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
      TauCeti.finrank_tangentSpace]
  calc _ ≤ ‖(cov'.hom cov).roughLaplacian covT A x (s x)‖ +
        ‖(2 : ℝ) • ∑ i, cov'.hom cov A x (b i) (cov' s x (b i))‖ := norm_sub_le _ _
    _ ≤ _ := by
        rw [norm_smul, Real.norm_two]
        have := ContinuousLinearMap.le_opNorm ((cov'.hom cov).roughLaplacian covT A x) (s x)
        nlinarith

end Normed

end CovariantDerivative
