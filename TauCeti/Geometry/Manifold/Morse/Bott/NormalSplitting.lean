/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.Spectral.Inertia
public import TauCeti.Analysis.InnerProductSpace.Spectral.Projection
public import TauCeti.Geometry.Manifold.Morse.Bott.Coordinates
import TauCeti.Analysis.InnerProductSpace.Dual

/-!
# Smooth spectral splitting of the normal Hessian

Let `i : S → M` be a Morse–Bott critical submanifold of `f`. Read in a local trivialization of
the normal bundle with fibre model a finite-dimensional real inner product space `P`, the normal
Hessian becomes a family `Q s` of symmetric nondegenerate bilinear forms on `P`
(`IsNondegenerateCriticalSubmanifold.exists_contMDiffOn_normalHessian_normalSpaceTrivialization`
in the namespace `TauCeti.SmoothEmbedding`).
Through the inner product of `P`, each `Q s` is represented by an invertible self-adjoint
operator, its Riesz operator `(Q s)♯`, with `⟪(Q s)♯ u, v⟫ = Q s u v`. The negative and positive
spectral subspaces of `(Q s)♯` split `P` into a subspace on which `Q s` is negative definite and
one on which it is positive definite.

This file shows that this splitting is as regular as the normal Hessian and has the dimensions
predicted by the index: when `f` is `C^{k+2}` along the submanifold, the orthogonal projections
onto the negative and positive spectral subspaces of `(Q s)♯` are `C^k` in `s` over the base set
of the trivialization, and the two subspaces have dimensions the Morse indices of `f` and `-f` at
`i s`. Transported back along the trivialization, they are local `C^k` families of negative and
positive definite subspaces of the normal spaces: the local form of the splitting of the normal
bundle into negative and positive normal subbundles. The subspaces themselves depend on the
inner product chosen on `P` and on the trivialization; their dimensions do not.

The pointwise statements need only some linear equivalence `L : P ≃ₗ[ℝ] NormalSpace s` with
`Q (u, v) = Hess (L u, L v)`, such as `(e.linearEquivAt ℝ s hs).symm` for a normal-bundle
trivialization `e`.

## Main results

In the namespace `TauCeti.SmoothEmbedding`:

* `IsCriticalSubmanifold.isSelfAdjoint_continuousLinearMapOfBilin`: a form representing the normal
  Hessian has a self-adjoint Riesz operator.
* `IsNondegenerateCriticalSubmanifold.isUnit_continuousLinearMapOfBilin`: for a Morse–Bott
  submanifold, that Riesz operator is invertible.
* `IsNondegenerateCriticalSubmanifold.finrank_pointSpectralSubspace_Iio_continuousLinearMapOfBilin`,
  `IsNondegenerateCriticalSubmanifold.finrank_pointSpectralSubspace_Ioi_continuousLinearMapOfBilin`:
  the negative and positive spectral subspaces of the Riesz operator have dimensions the Morse
  index of `f` and the Morse index of `-f`.
* `IsNondegenerateCriticalSubmanifold.exists_contMDiffOn_starProjection_pointSpectralSubspace`:
  in each normal-bundle trivialization, the negative and positive spectral projections of the
  normal Hessian are `C^k`.

## References

* R. Bott, *Nondegenerate critical manifolds*, Annals of Mathematics 60 (1954), 248–261.
-/

public section

open Bundle Function InnerProductSpace Set
open scoped ContDiff Manifold

noncomputable section

namespace TauCeti.SmoothEmbedding

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  {E' H' S : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H']
  {J : ModelWithCorners ℝ E' H'} [TopologicalSpace S] [ChartedSpace H' S]
  {f : M → ℝ} {n : ℕ∞ω} {i : SmoothEmbedding J I n S M} (hn : n ≠ 0)
  {P : Type*} [NormedAddCommGroup P] [InnerProductSpace ℝ P] [FiniteDimensional ℝ P]

local postfix:1024 "♯" => continuousLinearMapOfBilin (𝕜 := ℝ)

namespace IsCriticalSubmanifold

variable [I.Boundaryless] [IsManifold I 2 M]

/-- A bilinear form on an inner product space `P` representing the normal Hessian of a critical
submanifold through a linear equivalence `L` has a self-adjoint Riesz operator. -/
theorem isSelfAdjoint_continuousLinearMapOfBilin (h : i.IsCriticalSubmanifold f) {s : S}
    (L : P ≃ₗ[ℝ] i.NormalSpace s hn) {Q : P →L[ℝ] P →L[ℝ] ℝ}
    (hQ : ∀ u v, h.normalHessian hn s (L u) (L v) = Q u v) : IsSelfAdjoint Q♯ := by
  refine ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr fun u v ↦ ?_
  rw [ContinuousLinearMap.coe_coe, continuousLinearMapOfBilin_apply, real_inner_comm,
    continuousLinearMapOfBilin_apply, ← hQ, ← hQ,
    (h.isSymm_normalHessian hn s).eq]

end IsCriticalSubmanifold

namespace IsNondegenerateCriticalSubmanifold

variable [I.Boundaryless] [IsManifold I 2 M]

/-- A bilinear form on an inner product space `P` representing the normal Hessian of a Morse–Bott
critical submanifold through a linear equivalence `L` has an invertible Riesz operator. -/
theorem isUnit_continuousLinearMapOfBilin (h : i.IsNondegenerateCriticalSubmanifold f) {s : S}
    (L : P ≃ₗ[ℝ] i.NormalSpace s hn) {Q : P →L[ℝ] P →L[ℝ] ℝ}
    (hQ : ∀ u v, h.normalHessian hn s (L u) (L v) = Q u v) : IsUnit Q♯ := by
  refine ContinuousLinearMap.isUnit_iff_isUnit_toLinearMap.mpr
    ((LinearMap.isUnit_iff_ker_eq_bot _).mpr (LinearMap.ker_eq_bot'.mpr fun u hu ↦ ?_))
  -- `L u` pairs to zero with every normal vector, so it lies in the trivial kernel.
  have hker : L u ∈ LinearMap.ker (h.normalHessian hn s) := by
    rw [LinearMap.mem_ker]
    ext p
    obtain ⟨v, rfl⟩ := L.surjective p
    rw [hQ, ← continuousLinearMapOfBilin_apply, ← ContinuousLinearMap.coe_coe, hu,
      inner_zero_left, LinearMap.zero_apply]
  rwa [h.ker_normalHessian hn s, Submodule.mem_bot, map_eq_zero_iff _ L.injective] at hker

omit [FiniteDimensional ℝ P] in
/-- The quadratic form of a bilinear form representing the normal Hessian through `L` is
isometric to the quadratic form of the normal Hessian. -/
private theorem equivalent_toQuadraticMap (h : i.IsNondegenerateCriticalSubmanifold f) {s : S}
    (L : P ≃ₗ[ℝ] i.NormalSpace s hn) {Q : P →L[ℝ] P →L[ℝ] ℝ}
    (hQ : ∀ u v, h.normalHessian hn s (L u) (L v) = Q u v) :
    Q.toBilinForm.toQuadraticMap.Equivalent (h.normalHessian hn s).toQuadraticMap :=
  ⟨{ L with map_app' := fun u ↦ by simp [hQ] }⟩

variable [FiniteDimensional ℝ E]

/-- **The negative normal subspace has the dimension of the index.** If a bilinear form `Q` on an
inner product space `P` represents the normal Hessian of a Morse–Bott critical submanifold at `s`
through a linear equivalence, the negative spectral subspace of its Riesz operator, on which `Q`
is negative definite, has dimension the Morse index of `f` at `i s`. -/
theorem finrank_pointSpectralSubspace_Iio_continuousLinearMapOfBilin
    (h : i.IsNondegenerateCriticalSubmanifold f) {s : S} (L : P ≃ₗ[ℝ] i.NormalSpace s hn)
    {Q : P →L[ℝ] P →L[ℝ] ℝ} (hQ : ∀ u v, h.normalHessian hn s (L u) (L v) = Q u v) :
    Module.finrank ℝ (Module.End.pointSpectralSubspace Q♯.toLinearMap (Iio 0)) =
      manifoldMorseIndex I f (i s) := by
  have hA := ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp
    (h.isSelfAdjoint_continuousLinearMapOfBilin hn L hQ)
  rw [← h.sigNeg_normalHessian hn s, ← (h.equivalent_toQuadraticMap hn L hQ).sigNeg_eq,
    hA.sigNeg_eq_finrank_pointSpectralSubspace_Iio fun u ↦ by
      simp [continuousLinearMapOfBilin_apply]]

/-- **The positive normal subspace has the dimension of the coindex.** If a bilinear form `Q` on
an inner product space `P` represents the normal Hessian of a Morse–Bott critical submanifold at
`s` through a linear equivalence, the positive spectral subspace of its Riesz operator, on which
`Q` is positive definite, has dimension the Morse index of `-f` at `i s`. -/
theorem finrank_pointSpectralSubspace_Ioi_continuousLinearMapOfBilin
    (h : i.IsNondegenerateCriticalSubmanifold f) {s : S} (L : P ≃ₗ[ℝ] i.NormalSpace s hn)
    {Q : P →L[ℝ] P →L[ℝ] ℝ} (hQ : ∀ u v, h.normalHessian hn s (L u) (L v) = Q u v) :
    Module.finrank ℝ (Module.End.pointSpectralSubspace Q♯.toLinearMap (Ioi 0)) =
      manifoldMorseIndex I (-f) (i s) := by
  have hA := ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp
    (h.isSelfAdjoint_continuousLinearMapOfBilin hn L hQ)
  rw [← h.sigPos_normalHessian hn s, ← (h.equivalent_toQuadraticMap hn L hQ).sigPos_eq,
    hA.sigPos_eq_finrank_pointSpectralSubspace_Ioi fun u ↦ by
      simp [continuousLinearMapOfBilin_apply]]

end IsNondegenerateCriticalSubmanifold

namespace IsNondegenerateCriticalSubmanifold

variable [I.Boundaryless] [FiniteDimensional ℝ E] [FiniteDimensional ℝ E'] [IsManifold J 1 S]

/-- **The spectral splitting of the normal Hessian is `C^k`.** Let `i` be a Morse–Bott critical
submanifold of `f`, with `f` of class `C^{k+2}` at every point of the submanifold and `k ≤ n`.
In the preferred normal-bundle trivialization at any point `s₀`, with fibre model a
finite-dimensional real inner product space `P`, the normal Hessian is given over the base set by
a `C^k` family `Q` of bilinear forms on `P`, and the orthogonal projections onto the negative and
positive spectral subspaces of the Riesz operators `(Q s)♯` are `C^k` on the base set.

The ranges of these projections are the spectral subspaces themselves, on which `Q s` is negative,
respectively positive, definite
(`LinearMap.IsSymmetric.re_inner_apply_self_neg_of_mem_pointSpectralSubspace_Iio`). Their
dimensions are the Morse indices of `f` and `-f` at `i s`
(`finrank_pointSpectralSubspace_Iio_continuousLinearMapOfBilin` and
`finrank_pointSpectralSubspace_Ioi_continuousLinearMapOfBilin`, applied to the linear equivalence
`((i.normalSpaceTrivialization hn hdim s₀).linearEquivAt ℝ s hs).symm`). -/
theorem exists_contMDiffOn_starProjection_pointSpectralSubspace {k : ℕ∞ω}
    [IsManifold I (k + 2) M] (h : i.IsNondegenerateCriticalSubmanifold f) (hk : k ≤ n)
    (hf : ∀ s, ContMDiffAt I 𝓘(ℝ) (k + 2) f (i s))
    (hdim : Module.finrank ℝ P = Module.finrank ℝ E - Module.finrank ℝ E') (s₀ : S) :
    haveI : IsManifold I 2 M := .of_le (n := k + 2) le_add_self
    ∃ Q : S → P →L[ℝ] P →L[ℝ] ℝ,
      ContMDiffOn J 𝓘(ℝ, P →L[ℝ] P →L[ℝ] ℝ) k Q
        (i.normalSpaceTrivialization hn hdim s₀).baseSet ∧
      (∀ s ∈ (i.normalSpaceTrivialization hn hdim s₀).baseSet, ∀ u v : P,
        h.normalHessian hn s ((i.normalSpaceTrivialization hn hdim s₀).symm s u)
          ((i.normalSpaceTrivialization hn hdim s₀).symm s v) = Q s u v) ∧
      ContMDiffOn J 𝓘(ℝ, P →L[ℝ] P) k
        (fun s ↦ (Module.End.pointSpectralSubspace (Q s)♯.toLinearMap (Iio 0)).starProjection)
        (i.normalSpaceTrivialization hn hdim s₀).baseSet ∧
      ContMDiffOn J 𝓘(ℝ, P →L[ℝ] P) k
        (fun s ↦ (Module.End.pointSpectralSubspace (Q s)♯.toLinearMap (Ioi 0)).starProjection)
        (i.normalSpaceTrivialization hn hdim s₀).baseSet := by
  have : IsManifold I 2 M := .of_le (n := k + 2) le_add_self
  set e := i.normalSpaceTrivialization hn hdim s₀
  obtain ⟨Q, hQ, hrep⟩ :=
    h.exists_contMDiffOn_normalHessian_normalSpaceTrivialization hn hk hf hdim s₀
  have hrep' (s : S) (hs : s ∈ e.baseSet) (u v : P) :
      h.normalHessian hn s ((e.linearEquivAt ℝ s hs).symm u) ((e.linearEquivAt ℝ s hs).symm v) =
        Q s u v := by
    simpa only [Trivialization.linearEquivAt_symm_apply] using ((hrep s hs).1 u v).1
  -- Over the base set the Riesz operators are `C^k`, self-adjoint and invertible.
  set T : Set (P →L[ℝ] P) := {A | IsSelfAdjoint A ∧ IsUnit A}
  have hT (s : S) (hs : s ∈ e.baseSet) : (Q s)♯ ∈ T :=
    ⟨h.isSelfAdjoint_continuousLinearMapOfBilin hn _ (hrep' s hs),
      h.isUnit_continuousLinearMapOfBilin hn _ (hrep' s hs)⟩
  have hsharp : ContMDiffOn J 𝓘(ℝ, P →L[ℝ] P) k (fun s ↦ (Q s)♯) e.baseSet := fun s hs ↦
    contDiff_continuousLinearMapOfBilin.comp_contMDiffWithinAt (hQ s hs)
  have hneg := (contDiffOn_id (n := k) (s := T)).starProjection_pointSpectralSubspace_Iio_zero
    (fun _ hA ↦ hA.1) (fun _ hA ↦ hA.2)
  have hpos := (contDiffOn_id (n := k) (s := T)).starProjection_pointSpectralSubspace_Ioi_zero
    (fun _ hA ↦ hA.1) (fun _ hA ↦ hA.2)
  refine ⟨Q, hQ, fun s hs u v ↦ ((hrep s hs).1 u v).1, fun s hs ↦ ?_, fun s hs ↦ ?_⟩
  · exact ContDiffWithinAt.comp_contMDiffWithinAt (f := fun s ↦ (Q s)♯) (hneg _ (hT s hs))
      (hsharp s hs) hT
  · exact ContDiffWithinAt.comp_contMDiffWithinAt (f := fun s ↦ (Q s)♯) (hpos _ (hT s hs))
      (hsharp s hs) hT

end IsNondegenerateCriticalSubmanifold

end TauCeti.SmoothEmbedding
