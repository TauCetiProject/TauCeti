/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.Basic
public import Mathlib.Geometry.Manifold.VectorBundle.Hom
public import TauCeti.Geometry.Manifold.VectorBundle.Section.Module
public import TauCeti.RingTheory.Derivation.DifferentialOperator
import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Basic

/-!
# Bundled smooth covariant derivatives as first-order differential operators

Let `∇` (`cov : CovariantDerivative I F V`) be a smooth covariant derivative on a `𝕜`-vector bundle
`V` over a `C¹` manifold `M` (`[ContMDiffCovariantDerivative cov ∞]`). Mathlib defines `cov` on bare
dependent sections `Π x, V x` and records smoothness via `ContMDiffCovariantDerivative`.

This file bundles `cov` as a `𝕜`-linear map `CovariantDerivative.smoothCovariantDerivative` from
Mathlib's `ContMDiffSection` space `Cₛ^∞⟮I; F, V⟯` to
`Cₛ^∞⟮I; E →L[𝕜] F, fun x ↦ TangentSpace I x →L[𝕜] V x⟯`, with no Riemannian, Hausdorff,
finite-dimensionality, or boundary assumptions. Using locality off the closed support
(`CovariantDerivative.covariantDerivative_eq_zero_of_notMem_closure`) and the Leibniz rule
(`CovariantDerivative.covariantDerivative_smul_section_apply`), it shows that bundled covariant
differentiation shrinks closed supports, preserves compactly supported smooth sections, satisfies
the commutator identity `[∇, f] σ = df • σ` (`TauCeti.smulCommutator`), and therefore lies in
Grothendieck's filtration `TauCeti.differentialOperators` of differential operators of order at
most `1`.

## Main definitions

* `CovariantDerivative.smoothCovariantDerivative`: a smooth connection `∇` bundled as a `𝕜`-linear
  map from smooth sections of `V` to smooth sections of `Hom(TM, V)`.

## Main results

* `CovariantDerivative.tsupport_smoothCovariantDerivative_subset` and
  `CovariantDerivative.smoothCovariantDerivative_mem_compactlySupported`: `∇` does not enlarge
  closed supports and preserves `ContMDiffSection.compactlySupported`.
* `CovariantDerivative.smulCommutator_smoothCovariantDerivative_apply`:
  `[∇, f] σ x v = df_x(v) • σ x`, computing the principal symbol of `∇`.
* `CovariantDerivative.smoothCovariantDerivative_mem_differentialOperators_one`: `∇` has
  differential-operator order at most `1` in `TauCeti.differentialOperators`.

## References

* A. Grothendieck, *Éléments de géométrie algébrique IV*, Quatrième partie, §16.8.
* N. Berline, E. Getzler, M. Vergne, *Heat Kernels and Dirac Operators*, Springer, 1992, §2.1.
-/

public section

open Bundle
open scoped ContDiff Manifold

noncomputable section

namespace CovariantDerivative

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, AddCommGroup (V x)] [∀ x, Module 𝕜 (V x)]
  [∀ x, TopologicalSpace (V x)] [∀ x, IsTopologicalAddGroup (V x)]
  [∀ x, ContinuousSMul 𝕜 (V x)]
  [FiberBundle F V] [VectorBundle 𝕜 F V]
  (cov : CovariantDerivative I F V) [ContMDiffCovariantDerivative cov ∞]

/-- The covariant derivative `∇` as a `𝕜`-linear map from smooth sections of `V` to smooth
sections of `Hom(TM, V)`. -/
def smoothCovariantDerivative :
    Cₛ^∞⟮I; F, V⟯ →ₗ[𝕜] Cₛ^∞⟮I; E →L[𝕜] F, fun x ↦ TangentSpace I x →L[𝕜] V x⟯ where
  toFun σ := ⟨cov σ, contMDiffOn_univ.mp
    (ContMDiffCovariantDerivative.contMDiff.contMDiff (by simpa using σ.contMDiff.contMDiffOn))⟩
  map_add' σ τ := ContMDiffSection.ext fun x ↦
    cov.isCovariantDerivativeOnUniv.add
      (σ.contMDiff.mdifferentiableAt (by simp)) (τ.contMDiff.mdifferentiableAt (by simp))
  map_smul' c σ := ContMDiffSection.ext fun x ↦
    cov.isCovariantDerivativeOnUniv.smul_const c
      (σ.contMDiff.mdifferentiableAt (by simp))

@[simp]
theorem smoothCovariantDerivative_apply (σ : Cₛ^∞⟮I; F, V⟯) (x : M) :
    cov.smoothCovariantDerivative σ x = cov σ x :=
  (rfl)

/-- Covariant differentiation does not enlarge the closed support of a smooth section. -/
theorem tsupport_smoothCovariantDerivative_subset (σ : Cₛ^∞⟮I; F, V⟯) :
    (cov.smoothCovariantDerivative σ).tsupport ⊆ σ.tsupport := by
  refine (ContMDiffSection.tsupport_subset_iff σ.isClosed_tsupport).2 fun x hx ↦ ?_
  rw [ContMDiffSection.tsupport_def] at hx
  rw [smoothCovariantDerivative_apply]
  exact cov.covariantDerivative_eq_zero_of_notMem_closure hx

/-- Covariant differentiation preserves compactly supported smooth sections. -/
theorem smoothCovariantDerivative_mem_compactlySupported {σ : Cₛ^∞⟮I; F, V⟯}
    (hσ : σ ∈ ContMDiffSection.compactlySupported I F ∞ V) :
    cov.smoothCovariantDerivative σ ∈
      ContMDiffSection.compactlySupported I (E →L[𝕜] F) ∞ (fun x ↦ TangentSpace I x →L[𝕜] V x) := by
  rw [ContMDiffSection.mem_compactlySupported] at hσ ⊢
  exact hσ.of_isClosed_subset (ContMDiffSection.isClosed_tsupport _)
    (cov.tsupport_smoothCovariantDerivative_subset σ)

/-- The commutator `[∇, f] σ` acts on `v` by `df(v) • σ x`: the principal symbol of `∇`. -/
theorem smulCommutator_smoothCovariantDerivative_apply
    (f : C^∞⟮I, M; 𝕜⟯) (σ : Cₛ^∞⟮I; F, V⟯) (x : M) (v : TangentSpace I x) :
    TauCeti.smulCommutator 𝕜 f cov.smoothCovariantDerivative σ x v = d% f x v • σ x := by
  have hcoe : (⇑(f • σ) : Π y, V y) = (f : M → 𝕜) • (σ : Π y, V y) :=
    funext fun y ↦ ContMDiffSection.smul_apply f σ y
  simp only [TauCeti.smulCommutator_apply_apply, ContMDiffSection.coe_sub, Pi.sub_apply,
    sub_apply, ContMDiffSection.smul_apply, smul_apply,
    smoothCovariantDerivative_apply, hcoe,
    cov.covariantDerivative_smul_section_apply (f.contMDiff.mdifferentiableAt (by simp))
      (σ.contMDiff.mdifferentiableAt (by simp)), add_sub_cancel_left]

/-- A smooth covariant derivative has differential-operator order at most `1`. -/
theorem smoothCovariantDerivative_mem_differentialOperators_one :
    cov.smoothCovariantDerivative ∈
      TauCeti.differentialOperators 𝕜 C^∞⟮I, M; 𝕜⟯ Cₛ^∞⟮I; F, V⟯
        Cₛ^∞⟮I; E →L[𝕜] F, fun x ↦ TangentSpace I x →L[𝕜] V x⟯ 1 := by
  refine TauCeti.mem_differentialOperators_succ_iff.2 fun f ↦
    TauCeti.mem_differentialOperators_zero_iff.2 fun g σ ↦ ContMDiffSection.ext fun x ↦ ?_
  ext v
  simp only [ContMDiffSection.smul_apply, smul_apply,
    smulCommutator_smoothCovariantDerivative_apply, smul_comm (d% f x v) (g x)]

end CovariantDerivative

end
