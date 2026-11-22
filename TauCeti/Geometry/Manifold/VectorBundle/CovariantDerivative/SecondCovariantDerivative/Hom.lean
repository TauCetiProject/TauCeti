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

Applied to the section `∇σ` of `Hom(TM, V)`, the identification gives `∇²(∇σ) = ∇³σ`, the
covariant derivative of `∇²σ` (`CovariantDerivative.secondCovariantDerivative_covariantDerivative`).

For a smooth homomorphism `A` from a finite-rank bundle `V'` to `V` and a smooth section `s` of
`V'`, the second covariant derivative of `A s` obeys the Leibniz rule
(`CovariantDerivative.secondCovariantDerivative_clm_apply`)

`∇²(A s)(u, v) = (∇²A)(u, v) s + (∇_v A)(∇_u s) + (∇_u A)(∇_v s) + A (∇²s(u, v))`,

where `∇²A` is the second covariant derivative for the induced connection on `Hom(V', V)`.

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

section Third

variable [ContMDiffVectorBundle ∞ F V I] [ContMDiffCovariantDerivative covT ∞] {covT}

/-- The second covariant derivative of the section `∇σ` of `Hom(TM, V)` is the third covariant
derivative of `σ`: `∇²(∇σ)(u, w) = ∇³σ(u, w, ·)`, where `∇³σ` is the covariant derivative of the
section `∇²σ` of `Hom(TM, Hom(TM, V))`. -/
theorem secondCovariantDerivative_covariantDerivative (hσ : CMDiff ∞ (T% σ)) (x : M)
    (u w : TangentSpace I x) :
    (covT.hom cov).secondCovariantDerivative covT (cov σ) x u w =
      covT.hom (covT.hom cov) (covT.hom cov (cov σ)) x u w :=
  secondCovariantDerivative_eq_hom_apply (covT.hom cov) covT
    (contMDiffOn_univ.mp ((ContMDiffCovariantDerivative.contMDiff (cov := cov) (k := ∞)).contMDiff
      (by simpa using hσ.contMDiffOn))) x u w

end Third

section Leibniz

variable
  {F' : Type*} [NormedAddCommGroup F'] [NormedSpace ℝ F'] [FiniteDimensional ℝ F']
  {V' : M → Type*} [TopologicalSpace (TotalSpace F' V')]
  [∀ x, AddCommGroup (V' x)] [∀ x, Module ℝ (V' x)]
  [∀ x, TopologicalSpace (V' x)] [∀ x, IsTopologicalAddGroup (V' x)]
  [∀ x, ContinuousSMul ℝ (V' x)] [FiberBundle F' V'] [VectorBundle ℝ F' V']
  [ContMDiffVectorBundle ∞ F' V' I] [ContMDiffVectorBundle ∞ F V I]
  (cov' : _root_.CovariantDerivative I F' V') [ContMDiffCovariantDerivative cov' ∞]
  {A : Π x : M, V' x →L[ℝ] V x} {s : Π x : M, V' x}

/-- **Leibniz rule for the second covariant derivative of a homomorphism applied to a section.**
For a smooth homomorphism `A : V' → V` and a smooth section `s` of `V'`,
`∇²(A s)(u, v) = (∇²A)(u, v) s + (∇_v A)(∇_u s) + (∇_u A)(∇_v s) + A (∇²s(u, v))`, where `∇²A`
is the second covariant derivative for the induced connection on `Hom(V', V)`. -/
theorem secondCovariantDerivative_clm_apply
    (hA : ContMDiff I (I.prod 𝓘(ℝ, F' →L[ℝ] F)) ∞
      (fun y ↦ TotalSpace.mk' (F' →L[ℝ] F) (E := fun z ↦ V' z →L[ℝ] V z) y (A y)))
    (hs : CMDiff ∞ (T% s)) (x : M) (u v : TangentSpace I x) :
    cov.secondCovariantDerivative covT (fun y ↦ A y (s y)) x u v =
      (cov'.hom cov).secondCovariantDerivative covT A x u v (s x) +
        cov'.hom cov A x v (cov' s x u) + cov'.hom cov A x u (cov' s x v) +
          A x (cov'.secondCovariantDerivative covT s x u v) := by
  obtain ⟨Y, hY, rfl⟩ := exists_contMDiff_section_eq I E ∞ v
  have hAs : CMDiff ∞ (T% fun y ↦ A y (s y)) := hA.clm_bundle_apply hs
  -- The homomorphism `∇_Y A` and the section `∇_Y s` are smooth.
  have hB : ContMDiff I (I.prod 𝓘(ℝ, F' →L[ℝ] F)) ∞ (fun y ↦ TotalSpace.mk' (F' →L[ℝ] F)
      (E := fun z ↦ V' z →L[ℝ] V z) y (cov'.hom cov A y (Y y))) :=
    (contMDiff_hom cov' cov hA).clm_bundle_apply hY
  have hτ : CMDiff ∞ (T% fun y ↦ cov' s y (Y y)) := cov'.contMDiff_apply hY hs
  have hsum : (fun y ↦ cov (fun z ↦ A z (s z)) y (Y y)) =
      (fun y ↦ cov'.hom cov A y (Y y) (s y)) + fun y ↦ A y (cov' s y (Y y)) := by
    funext y
    exact covariantDerivative_clm_apply cov' cov (hA.mdifferentiable (by simp) y)
      (hs.mdifferentiable (by simp) y) (Y y)
  rw [secondCovariantDerivative_apply cov covT hAs x hY,
    secondCovariantDerivative_apply (cov'.hom cov) covT hA x hY,
    secondCovariantDerivative_apply cov' covT hs x hY, hsum,
    cov.isCovariantDerivativeOnUniv.add
      ((hB.clm_bundle_apply hs).mdifferentiable (by simp) x)
      ((hA.clm_bundle_apply hτ).mdifferentiable (by simp) x),
    add_apply, covariantDerivative_clm_apply cov' cov (hB.mdifferentiable (by simp) x)
      (hs.mdifferentiable (by simp) x),
    covariantDerivative_clm_apply cov' cov (hA.mdifferentiable (by simp) x)
      (hτ.mdifferentiable (by simp) x),
    covariantDerivative_clm_apply cov' cov (hA.mdifferentiable (by simp) x)
      (hs.mdifferentiable (by simp) x)]
  simp only [map_sub, sub_apply]
  abel

end Leibniz

end CovariantDerivative
