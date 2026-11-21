/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.SecondCovariantDerivative
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Hom
public import TauCeti.Geometry.Manifold.VectorBundle.Section.Extension
import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Regularity

/-!
# The second covariant derivative as an induced Hom derivative

For a smooth section `σ`, the second covariant derivative `∇²σ` equals the covariant derivative
of `∇σ`, regarded as a section of `Hom(TM, V)` with the connection induced by `∇ᵀ` and `∇`. This
identification connects the tensor `∇²σ` with the product rule for a bundle map acting on a
field along a curve. The bundle `V` need not have finite rank or a norm.

For a smooth section `A` of `Hom(V, W)` and a smooth section `s` of `V`, the second covariant
derivative of `A s` obeys the Leibniz rule
`∇²(A s)(u, w) = (∇²A)(u, w) s + (∇_u A)(∇_w s) + (∇_w A)(∇_u s) + A ∇²s(u, w)`
(`CovariantDerivative.secondCovariantDerivative_clm_apply`).

## References

* J. M. Lee, *Introduction to Riemannian Manifolds*, second edition, Chapter 4.
-/

public noncomputable section

open Bundle CovariantDerivative FiberBundle
open scoped ContDiff Manifold

namespace CovariantDerivative

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [T2Space M] [IsManifold I ∞ M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)]
  [∀ x, TopologicalSpace (V x)] [∀ x, IsTopologicalAddGroup (V x)]
  [∀ x, ContinuousSMul ℝ (V x)]
  [FiberBundle F V] [VectorBundle ℝ F V]
  (cov : _root_.CovariantDerivative I F V) [ContMDiffCovariantDerivative cov ∞]
  (covT : _root_.CovariantDerivative I E (TangentSpace I : M → Type _))
  {σ : Π y : M, V y}

/-- The second covariant derivative of a smooth section is the covariant derivative of its first
covariant derivative, regarded as a section of `Hom(TM, V)` with the induced connection. -/
theorem secondCovariantDerivative_eq_hom_apply (hσ : CMDiff ∞ (T% σ))
    (x : M) (u v : TangentSpace I x) :
    cov.secondCovariantDerivative covT σ x u v = covT.hom cov (cov σ) x u v := by
  have hD : ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] F)) ∞
      (fun x ↦ TotalSpace.mk' (E →L[ℝ] F)
        (E := fun x : M ↦ TangentSpace I x →L[ℝ] V x) x (cov σ x)) :=
    contMDiffOn_univ.mp (ContMDiffCovariantDerivative.contMDiff.contMDiff
      (by simpa using hσ.contMDiffOn))
  obtain ⟨Y, hY, rfl⟩ := exists_contMDiff_section_eq I E ∞ v
  rw [secondCovariantDerivative_apply cov covT hσ x hY,
    hom_apply covT cov (hD.mdifferentiable (by simp) x) (hY.mdifferentiable (by simp) x)]

end CovariantDerivative

namespace CovariantDerivative

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [T2Space M] [IsManifold I ∞ M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)]
  [∀ x, TopologicalSpace (V x)] [∀ x, IsTopologicalAddGroup (V x)]
  [∀ x, ContinuousSMul ℝ (V x)] [FiberBundle F V] [VectorBundle ℝ F V]
  [ContMDiffVectorBundle ∞ F V I]
  {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
  {W : M → Type*} [TopologicalSpace (TotalSpace G W)]
  [∀ x, AddCommGroup (W x)] [∀ x, Module ℝ (W x)]
  [∀ x, TopologicalSpace (W x)] [∀ x, IsTopologicalAddGroup (W x)]
  [∀ x, ContinuousSMul ℝ (W x)] [FiberBundle G W] [VectorBundle ℝ G W]
  [ContMDiffVectorBundle ∞ G W I]
  (covV : _root_.CovariantDerivative I F V) (covW : _root_.CovariantDerivative I G W)
  [ContMDiffCovariantDerivative covV ∞] [ContMDiffCovariantDerivative covW ∞]
  (covT : _root_.CovariantDerivative I E (TangentSpace I : M → Type _))
  {A : Π x : M, V x →L[ℝ] W x} {s : Π x : M, V x}

/-- **The Leibniz rule for the second covariant derivative of a bundle map applied to a
section.** For a smooth section `A` of `Hom(V, W)` and a smooth section `s` of `V`,
`∇²(A s)(u, w) = (∇²A)(u, w) s + (∇_u A)(∇_w s) + (∇_w A)(∇_u s) + A ∇²s(u, w)`, where `A` is
differentiated with the induced connection on `Hom(V, W)`. The connection `∇ᵀ` on the tangent
bundle is arbitrary. -/
theorem secondCovariantDerivative_clm_apply
    (hA : ContMDiff I (I.prod 𝓘(ℝ, F →L[ℝ] G)) ∞
      (fun x ↦ TotalSpace.mk' (F →L[ℝ] G) (E := fun y ↦ V y →L[ℝ] W y) x (A x)))
    (hs : CMDiff ∞ (T% s)) (x : M) (u w : TangentSpace I x) :
    covW.secondCovariantDerivative covT (fun y ↦ A y (s y)) x u w =
      (covV.hom covW).secondCovariantDerivative covT A x u w (s x) +
        covV.hom covW A x u (covV s x w) + covV.hom covW A x w (covV s x u) +
        A x (covV.secondCovariantDerivative covT s x u w) := by
  obtain ⟨Y, hY, rfl⟩ := exists_contMDiff_section_eq I E ∞ w
  have hAs : CMDiff ∞ (T% (fun y ↦ A y (s y))) := hA.clm_bundle_apply hs
  have hs' : CMDiff (∞ + 1) (T% s) := by simpa using hs
  have hA' : ContMDiff I (I.prod 𝓘(ℝ, F →L[ℝ] G)) (∞ + 1)
      (fun x ↦ TotalSpace.mk' (F →L[ℝ] G) (E := fun y ↦ V y →L[ℝ] W y) x (A x)) := by
    simpa using hA
  -- The covariant derivative of `A` along `Y`, and that of `s` along `Y`.
  have hB : ContMDiff I (I.prod 𝓘(ℝ, F →L[ℝ] G)) ∞
      (fun x ↦ TotalSpace.mk' (F →L[ℝ] G) (E := fun y ↦ V y →L[ℝ] W y) x
        (covV.hom covW A x (Y x))) :=
    (covV.hom covW).contMDiff_apply hY hA'
  have ht : CMDiff ∞ (T% (fun y ↦ covV s y (Y y))) := covV.contMDiff_apply hY hs'
  have hsplit : (fun y ↦ covW (fun z ↦ A z (s z)) y (Y y)) =
      (fun y ↦ covV.hom covW A y (Y y) (s y)) + fun y ↦ A y (covV s y (Y y)) := by
    funext y
    simp only [Pi.add_apply]
    rw [hom_apply covV covW ((hA y).mdifferentiableAt (by simp))
      ((hs y).mdifferentiableAt (by simp))]
    abel
  have h1 := hom_apply covV covW ((hB x).mdifferentiableAt (by simp))
    ((hs x).mdifferentiableAt (by simp)) u
  have h2 := hom_apply covV covW ((hA x).mdifferentiableAt (by simp))
    ((ht x).mdifferentiableAt (by simp)) u
  have h3 := hom_apply covV covW ((hA x).mdifferentiableAt (by simp))
    ((hs x).mdifferentiableAt (by simp)) (covT Y x u)
  rw [secondCovariantDerivative_apply covW covT hAs x hY u,
    secondCovariantDerivative_apply (covV.hom covW) covT hA x hY u,
    secondCovariantDerivative_apply covV covT hs x hY u, hsplit,
    covW.isCovariantDerivativeOnUniv.add
      (((hB.clm_bundle_apply hs) x).mdifferentiableAt (by simp))
      (((hA.clm_bundle_apply ht) x).mdifferentiableAt (by simp))]
  simp only [add_apply, sub_apply, map_sub]
  rw [h1, h2, h3]
  abel

end CovariantDerivative
