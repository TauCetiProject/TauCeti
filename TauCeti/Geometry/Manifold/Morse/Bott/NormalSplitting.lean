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
import TauCeti.Analysis.InnerProductSpace.Spectral.SignatureNormalForm

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

The same data put half the normal Hessian in the standard form of the Morse–Bott lemma: with
`T s` the square root of the absolute value of `(Q s)♯ / 2`, a `C^k` family of invertible operators
preserving the two spectral subspaces, `½ Q s (u, u) = ‖P₊ (T s u)‖ ^ 2 - ‖P₋ (T s u)‖ ^ 2`, where
`P₋` and `P₊` are the negative and positive spectral projections. This is the fibrewise linear
change of variables that turns a quadratic normal form `c + ½ Hess (w, w)` along the submanifold
into `c - ‖w₋‖ ^ 2 + ‖w₊‖ ^ 2`.

The pointwise statements need only some linear equivalence `L : P ≃ₗ[ℝ] NormalSpace s` with
`Q (u, v) = Hess (L u, L v)`, such as `(e.linearEquivAt ℝ s hs).symm` for a normal-bundle
trivialization `e`. Such a form is negative definite on the negative spectral subspace of its
Riesz operator and positive definite on the positive one: apply
`InnerProductSpace.apply_self_neg_of_mem_pointSpectralSubspace_Iio_continuousLinearMapOfBilin` and
`InnerProductSpace.apply_self_pos_of_mem_pointSpectralSubspace_Ioi_continuousLinearMapOfBilin` to
`IsCriticalSubmanifold.isSelfAdjoint_continuousLinearMapOfBilin`. For a Morse–Bott submanifold
the form is injective (`IsNondegenerateCriticalSubmanifold.injective_of_normalHessian_eq`), so its
Riesz operator is invertible by `InnerProductSpace.isUnit_continuousLinearMapOfBilin`.

## Main results

In the namespace `TauCeti.SmoothEmbedding.IsCriticalSubmanifold`:

* `isSelfAdjoint_continuousLinearMapOfBilin`: a form representing the normal Hessian has a
  self-adjoint Riesz operator.

In the namespace `TauCeti.SmoothEmbedding.IsNondegenerateCriticalSubmanifold`:

* `isCompl_pointSpectralSubspace_Iio_Ioi_continuousLinearMapOfBilin`: for a Morse–Bott
  submanifold, the negative and positive spectral subspaces of the Riesz operator are
  complementary.
* `finrank_pointSpectralSubspace_Iio_continuousLinearMapOfBilin`,
  `finrank_pointSpectralSubspace_Ioi_continuousLinearMapOfBilin`: the negative and positive
  spectral subspaces of the Riesz operator have dimensions the Morse index of `f` and the Morse
  index of `-f`.
* `exists_contMDiffOn_starProjection_pointSpectralSubspace`: in each normal-bundle trivialization,
  the negative and positive spectral projections of the normal Hessian are `C^k`.
* `exists_contMDiffOn_normalHessian_div_two_eq_norm_sq_sub_norm_sq`: in each normal-bundle
  trivialization, a `C^k` family of invertible operators preserving the spectral splitting carries
  half the normal Hessian to the difference of the squared norms of its positive and negative
  components.

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

omit [FiniteDimensional ℝ P] in
/-- A bilinear form representing the normal Hessian through a linear equivalence is symmetric. -/
private theorem symm_of_normalHessian_eq (h : i.IsCriticalSubmanifold f) {s : S}
    (L : P ≃ₗ[ℝ] i.NormalSpace s hn) {Q : P →L[ℝ] P →L[ℝ] ℝ}
    (hQ : ∀ u v, h.normalHessian hn s (L u) (L v) = Q u v) (u v : P) :
    Q u v = Q v u := by
  rw [← hQ, ← hQ, (h.isSymm_normalHessian hn s).eq]

/-- A bilinear form on an inner product space `P` representing the normal Hessian of a critical
submanifold through a linear equivalence `L` has a self-adjoint Riesz operator. -/
theorem isSelfAdjoint_continuousLinearMapOfBilin (h : i.IsCriticalSubmanifold f) {s : S}
    (L : P ≃ₗ[ℝ] i.NormalSpace s hn) {Q : P →L[ℝ] P →L[ℝ] ℝ}
    (hQ : ∀ u v, h.normalHessian hn s (L u) (L v) = Q u v) : IsSelfAdjoint Q♯ :=
  InnerProductSpace.isSelfAdjoint_continuousLinearMapOfBilin <|
    h.symm_of_normalHessian_eq hn L hQ

end IsCriticalSubmanifold

namespace IsNondegenerateCriticalSubmanifold

variable [I.Boundaryless] [IsManifold I 2 M]

/-- **The normal splitting.** For a bilinear form `Q` representing the normal Hessian of a
Morse–Bott critical submanifold through a linear equivalence `L`, the negative and positive
spectral subspaces of its Riesz operator are complementary, so `P` is their direct sum. -/
theorem isCompl_pointSpectralSubspace_Iio_Ioi_continuousLinearMapOfBilin
    (h : i.IsNondegenerateCriticalSubmanifold f) {s : S} (L : P ≃ₗ[ℝ] i.NormalSpace s hn)
    {Q : P →L[ℝ] P →L[ℝ] ℝ} (hQ : ∀ u v, h.normalHessian hn s (L u) (L v) = Q u v) :
    IsCompl (Module.End.pointSpectralSubspace Q♯.toLinearMap (Iio 0))
      (Module.End.pointSpectralSubspace Q♯.toLinearMap (Ioi 0)) :=
  (h.isSelfAdjoint_continuousLinearMapOfBilin hn L hQ).isSymmetric
    |>.isCompl_pointSpectralSubspace_Iio_zero_Ioi_zero <| (ker_continuousLinearMapOfBilin Q).trans
      (LinearMap.ker_eq_bot.mpr (h.injective_of_normalHessian_eq hn L hQ))

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
  rw [InnerProductSpace.finrank_pointSpectralSubspace_Iio_continuousLinearMapOfBilin
    (h.symm_of_normalHessian_eq hn L hQ), (h.equivalent_toQuadraticMap hn L hQ).sigNeg_eq,
    h.sigNeg_normalHessian hn s]

/-- **The positive normal subspace has the dimension of the coindex.** If a bilinear form `Q` on
an inner product space `P` represents the normal Hessian of a Morse–Bott critical submanifold at
`s` through a linear equivalence, the positive spectral subspace of its Riesz operator, on which
`Q` is positive definite, has dimension the Morse index of `-f` at `i s`. -/
theorem finrank_pointSpectralSubspace_Ioi_continuousLinearMapOfBilin
    (h : i.IsNondegenerateCriticalSubmanifold f) {s : S} (L : P ≃ₗ[ℝ] i.NormalSpace s hn)
    {Q : P →L[ℝ] P →L[ℝ] ℝ} (hQ : ∀ u v, h.normalHessian hn s (L u) (L v) = Q u v) :
    Module.finrank ℝ (Module.End.pointSpectralSubspace Q♯.toLinearMap (Ioi 0)) =
      manifoldMorseIndex I (-f) (i s) := by
  rw [InnerProductSpace.finrank_pointSpectralSubspace_Ioi_continuousLinearMapOfBilin
    (h.symm_of_normalHessian_eq hn L hQ), (h.equivalent_toQuadraticMap hn L hQ).sigPos_eq,
    h.sigPos_normalHessian hn s]

end IsNondegenerateCriticalSubmanifold

namespace IsNondegenerateCriticalSubmanifold

variable [I.Boundaryless] [FiniteDimensional ℝ E] [FiniteDimensional ℝ E'] [IsManifold J 1 S]

/-- In the preferred normal-bundle trivialization at `s₀`, the normal Hessian of a Morse–Bott
critical submanifold is given over the base set by a `C^k` family `Q` of bilinear forms on `P`,
whose Riesz operators `(Q s)♯` form a `C^k` family of invertible self-adjoint operators there. -/
private theorem exists_contMDiffOn_continuousLinearMapOfBilin {k : ℕ∞ω}
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
      ContMDiffOn J 𝓘(ℝ, P →L[ℝ] P) k (fun s ↦ (Q s)♯)
        (i.normalSpaceTrivialization hn hdim s₀).baseSet ∧
      ∀ s ∈ (i.normalSpaceTrivialization hn hdim s₀).baseSet,
        IsSelfAdjoint (Q s)♯ ∧ IsUnit (Q s)♯ := by
  obtain ⟨Q, hQ, hrep⟩ :=
    h.exists_contMDiffOn_normalHessian_normalSpaceTrivialization hn hk hf hdim s₀
  exact ⟨Q, hQ, fun s hs u v ↦ ((hrep s hs).1 u v).1, fun s hs ↦
    contDiff_continuousLinearMapOfBilin.comp_contMDiffWithinAt (hQ s hs), fun s hs ↦
    ⟨InnerProductSpace.isSelfAdjoint_continuousLinearMapOfBilin fun u v ↦ ((hrep s hs).1 u v).2,
      InnerProductSpace.isUnit_continuousLinearMapOfBilin (hrep s hs).2⟩⟩

/-- **The spectral splitting of the normal Hessian is `C^k`.** Let `i` be a Morse–Bott critical
submanifold of `f`, with `f` of class `C^{k+2}` at every point of the submanifold and `k ≤ n`.
In the preferred normal-bundle trivialization at any point `s₀`, with fibre model a
finite-dimensional real inner product space `P`, the normal Hessian is given over the base set by
a `C^k` family `Q` of bilinear forms on `P`, and the orthogonal projections onto the negative and
positive spectral subspaces of the Riesz operators `(Q s)♯` are `C^k` on the base set.

The ranges of these projections are the spectral subspaces themselves. They are complementary
(`isCompl_pointSpectralSubspace_Iio_Ioi_continuousLinearMapOfBilin`), `Q s` is negative,
respectively positive, definite on them
(`InnerProductSpace.apply_self_neg_of_mem_pointSpectralSubspace_Iio_continuousLinearMapOfBilin`
and `InnerProductSpace.apply_self_pos_of_mem_pointSpectralSubspace_Ioi_continuousLinearMapOfBilin`,
applied to `IsCriticalSubmanifold.isSelfAdjoint_continuousLinearMapOfBilin`), and their dimensions
are the Morse indices of `f` and `-f` at `i s`
(`finrank_pointSpectralSubspace_Iio_continuousLinearMapOfBilin` and
`finrank_pointSpectralSubspace_Ioi_continuousLinearMapOfBilin`). Each of these applies to the
linear equivalence `((i.normalSpaceTrivialization hn hdim s₀).linearEquivAt ℝ s hs).symm`. -/
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
  obtain ⟨Q, hQ, hrep, hsharp, hT⟩ :=
    h.exists_contMDiffOn_continuousLinearMapOfBilin hn hk hf hdim s₀
  -- Over the base set the Riesz operators lie in the set of invertible self-adjoint operators.
  set T : Set (P →L[ℝ] P) := {A | IsSelfAdjoint A ∧ IsUnit A}
  have hneg := (contDiffOn_id (n := k) (s := T)).starProjection_pointSpectralSubspace_Iio_zero
    (fun _ hA ↦ hA.1) (fun _ hA ↦ hA.2)
  have hpos := (contDiffOn_id (n := k) (s := T)).starProjection_pointSpectralSubspace_Ioi_zero
    (fun _ hA ↦ hA.1) (fun _ hA ↦ hA.2)
  refine ⟨Q, hQ, hrep, fun s hs ↦ ?_, fun s hs ↦ ?_⟩
  · exact ContDiffWithinAt.comp_contMDiffWithinAt (f := fun s ↦ (Q s)♯) (hneg _ (hT s hs))
      (hsharp s hs) hT
  · exact ContDiffWithinAt.comp_contMDiffWithinAt (f := fun s ↦ (Q s)♯) (hpos _ (hT s hs))
      (hsharp s hs) hT

/-- **Half the normal Hessian as a difference of squared norms.** Let `i` be a Morse–Bott critical
submanifold of `f`, with `f` of class `C^{k+2}` at every point of the submanifold and `k ≤ n`. In
the preferred normal-bundle trivialization `e` at any point `s₀`, with fibre model a
finite-dimensional real inner product space `P`, the normal Hessian is given over the base set by
a `C^k` family `Q` of bilinear forms on `P`. Write `P₋ s` and `P₊ s` for the orthogonal
projections onto the negative and positive spectral subspaces of the Riesz operator `(Q s)♯`.
Then there is a `C^k` family `T` of invertible operators on `P`, commuting with every spectral
projection of `(Q s)♯`, such that for every `u : P`

  `½ Hess (e.symm s u, e.symm s u) = ‖P₊ s (T s u)‖ ^ 2 - ‖P₋ s (T s u)‖ ^ 2`.

So the fibrewise linear change of variables `u ↦ T s u`, which maps the negative and positive
spectral subspaces into themselves, carries half the normal Hessian to the standard quadratic
form `-‖u₋‖ ^ 2 + ‖u₊‖ ^ 2` of the Morse–Bott lemma; the projections `P₋` and `P₊` are `C^k` by
`exists_contMDiffOn_starProjection_pointSpectralSubspace`. One such family is
`2^{-1/2} |(Q s)♯|^{1/2}`, a multiple of the square root of the absolute value of the Riesz
operator, which involves no choice of eigenbasis
(`ContinuousLinearMap.inner_apply_self_eq_norm_sq_sub_norm_sq`). -/
theorem exists_contMDiffOn_normalHessian_div_two_eq_norm_sq_sub_norm_sq {k : ℕ∞ω}
    [IsManifold I (k + 2) M] (h : i.IsNondegenerateCriticalSubmanifold f) (hk : k ≤ n)
    (hf : ∀ s, ContMDiffAt I 𝓘(ℝ) (k + 2) f (i s))
    (hdim : Module.finrank ℝ P = Module.finrank ℝ E - Module.finrank ℝ E') (s₀ : S) :
    haveI : IsManifold I 2 M := .of_le (n := k + 2) le_add_self
    ∃ (Q : S → P →L[ℝ] P →L[ℝ] ℝ) (T : S → P →L[ℝ] P),
      ContMDiffOn J 𝓘(ℝ, P →L[ℝ] P →L[ℝ] ℝ) k Q
        (i.normalSpaceTrivialization hn hdim s₀).baseSet ∧
      (∀ s ∈ (i.normalSpaceTrivialization hn hdim s₀).baseSet, ∀ u v : P,
        h.normalHessian hn s ((i.normalSpaceTrivialization hn hdim s₀).symm s u)
          ((i.normalSpaceTrivialization hn hdim s₀).symm s v) = Q s u v) ∧
      ContMDiffOn J 𝓘(ℝ, P →L[ℝ] P) k T (i.normalSpaceTrivialization hn hdim s₀).baseSet ∧
      ∀ s ∈ (i.normalSpaceTrivialization hn hdim s₀).baseSet, IsUnit (T s) ∧
        (∀ Ω : Set ℝ,
          Commute (T s) (Module.End.pointSpectralSubspace (Q s)♯.toLinearMap Ω).starProjection) ∧
        ∀ u : P, h.normalHessian hn s ((i.normalSpaceTrivialization hn hdim s₀).symm s u)
            ((i.normalSpaceTrivialization hn hdim s₀).symm s u) / 2 =
          ‖(Module.End.pointSpectralSubspace (Q s)♯.toLinearMap (Ioi 0)).starProjection
              (T s u)‖ ^ 2 -
            ‖(Module.End.pointSpectralSubspace (Q s)♯.toLinearMap (Iio 0)).starProjection
              (T s u)‖ ^ 2 := by
  obtain ⟨Q, hQ, hrep, hsharp, hT⟩ :=
    h.exists_contMDiffOn_continuousLinearMapOfBilin hn hk hf hdim s₀
  set c : ℝ := (√2)⁻¹
  have hc : c ^ 2 = 1 / 2 := by simp [c, inv_pow]
  -- `T s = c • ((Q s)♯ * (Q s)♯) ^ (1 / 4)` is a smooth function of the Riesz operator.
  set T : Set (P →L[ℝ] P) := {A | IsSelfAdjoint A ∧ IsUnit A}
  have hroot := ((contDiffOn_id (n := k) (s := T)).rpow_mul_self (1 / 4) (fun _ hA ↦ hA.1)
    (fun _ hA ↦ hA.2)).const_smul c
  refine ⟨Q, fun s ↦ c • ((Q s)♯ * (Q s)♯) ^ (1 / 4 : ℝ), hQ, hrep, fun s hs ↦
    ContDiffWithinAt.comp_contMDiffWithinAt (f := fun s ↦ (Q s)♯) (hroot _ (hT s hs))
      (hsharp s hs) hT, fun s hs ↦ ⟨?_, fun Ω ↦ ?_, fun u ↦ ?_⟩⟩
  · have hpos : 0 ≤ (Q s)♯ * (Q s)♯ := by
      simpa only [(hT s hs).1.star_eq] using star_mul_self_nonneg (Q s)♯
    exact ((hT s hs).2.mul (hT s hs).2).cfcRpow _ hpos |>.smul
      (Units.mk0 c (by positivity))
  · exact (ContinuousLinearMap.commute_rpow_mul_self_starProjection_pointSpectralSubspace
      (hT s hs).1 _ Ω).smul_left c
  · rw [hrep s hs, ← InnerProductSpace.continuousLinearMapOfBilin_apply,
      ContinuousLinearMap.inner_apply_self_eq_norm_sq_sub_norm_sq (hT s hs).1]
    simp only [smul_apply, map_smul, norm_smul, mul_pow, Real.norm_eq_abs,
      sq_abs, hc]
    ring

end IsNondegenerateCriticalSubmanifold

end TauCeti.SmoothEmbedding
