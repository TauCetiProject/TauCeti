/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.Spectral.RelativeProjection
public import TauCeti.Geometry.Manifold.Morse.Bott.Coordinates

/-!
# Local negative normal projections of a Morse–Bott submanifold

Let `i : S → M` be a nondegenerate critical submanifold of a function `f`. At each point of `S`
the normal Hessian is a nondegenerate symmetric bilinear form on the normal space, whose negative
index of inertia is the Morse index of `f` at `i s`
(`TauCeti.SmoothEmbedding.IsNondegenerateCriticalSubmanifold.sigNeg_normalHessian`). Given a fibre
metric on the normal bundle, the normal space therefore splits, orthogonally for the metric and for
the normal Hessian, into a **negative normal space**, on which the normal Hessian is negative
definite, and a positive normal space, on which it is positive definite. The negative normal
spaces are the fibres of the negative normal bundle along which the negative disc bundle of the
critical submanifold is attached.

This file shows that these splittings vary smoothly. In the preferred normal-bundle trivialization
at any point `s₀`, with Euclidean fibre model `P`, write the fibre metric as a `C^k` family `G` of
positive definite bilinear forms on `P`. Then the projections onto the negative normal spaces
along the positive ones form a `C^k` family of operators on `P` over the base set of the
trivialization (or the part of it where `G` is given). Their ranks are the Morse indices of `f`
and their nullities those of `-f`. The projection at `s` is the negative spectral projection of
the normal Hessian relative to the fibre metric (`ContinuousLinearMap.negativeSpectralProjection`),
read in the trivialization. It is smooth because the normal Hessian is a `C^k` family of
nondegenerate forms in these coordinates
(`exists_contMDiffOn_normalHessian_normalSpaceTrivialization`, in the namespace
`TauCeti.SmoothEmbedding.IsNondegenerateCriticalSubmanifold`).
No eigenbasis of the normal Hessian is chosen, so no smoothly varying eigenvectors are needed.

The inner product of `P` only serves as a reference for the construction: the stated properties
involve the normal Hessian and the fibre metric alone, and they determine the projections
(`ContinuousLinearMap.eq_negativeSpectralProjection_iff`).

## Main results

In the namespace `TauCeti.SmoothEmbedding`:

* `IsNondegenerateCriticalSubmanifold.exists_contMDiffOn_negativeNormalProjection`: in each
  normal-bundle trivialization, the projections onto the negative normal spaces of a Morse–Bott
  submanifold relative to a `C^k` fibre metric form a `C^k` family, of rank the Morse index.

## References

* R. Bott, *Nondegenerate critical manifolds*, Annals of Mathematics 60 (1954), 248–261.
* A. Banyaga and D. E. Hurtubise, *Lectures on Morse Homology*, Kluwer, 2004, Section 3.5.
-/

public section

open Bundle Function Set InnerProductSpace
open scoped ContDiff Manifold

noncomputable section

namespace TauCeti.SmoothEmbedding.IsNondegenerateCriticalSubmanifold

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  {E' H' S : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H']
  {J : ModelWithCorners ℝ E' H'} [TopologicalSpace S] [ChartedSpace H' S]
  {f : M → ℝ} {n : ℕ∞ω} {i : SmoothEmbedding J I n S M} (hn : n ≠ 0)
  [I.Boundaryless] [FiniteDimensional ℝ E] [FiniteDimensional ℝ E'] [IsManifold J 1 S]
  {P : Type*} [NormedAddCommGroup P] [InnerProductSpace ℝ P] [FiniteDimensional ℝ P]

/-- **The negative normal projections of a Morse–Bott submanifold are smooth.** Let `i` be a
nondegenerate critical submanifold of `f`, with `f` of class `C^{k+2}` along it and `k ≤ n`, and
let `G` be a `C^k` family of symmetric positive definite bilinear forms on the fibre model `P` over
a set `U`, for instance a fibre metric on the normal bundle read in the preferred normal-bundle
trivialization `e` at `s₀`. Write `N s u v` for the normal Hessian at `s` of the normal vectors
with coordinates `u` and `v`. Then there is a `C^k` family `p` of operators on `P` over the
intersection of `U` with the base set of `e` such that each `p s` is a projection whose range and
kernel are orthogonal for both `G s` and `N s`, with `N s` negative definite on the range and
positive definite on the kernel. The rank of `p s` is the Morse index of `f` at `i s`, and its
nullity is the Morse index of `-f`. -/
theorem exists_contMDiffOn_negativeNormalProjection {k : ℕ∞ω} [IsManifold I (k + 2) M]
    (h : i.IsNondegenerateCriticalSubmanifold f) (hk : k ≤ n)
    (hf : ∀ s, ContMDiffAt I 𝓘(ℝ) (k + 2) f (i s))
    (hdim : Module.finrank ℝ P = Module.finrank ℝ E - Module.finrank ℝ E') (s₀ : S)
    {U : Set S} {G : S → P →L[ℝ] P →L[ℝ] ℝ} (hG : ContMDiffOn J 𝓘(ℝ, P →L[ℝ] P →L[ℝ] ℝ) k G U)
    (hGsymm : ∀ s ∈ U, ∀ u v, G s u v = G s v u) (hGpos : ∀ s ∈ U, ∀ u, u ≠ 0 → 0 < G s u u) :
    haveI : IsManifold I 2 M := .of_le (n := k + 2) le_add_self
    ∃ p : S → P →L[ℝ] P,
      ContMDiffOn J 𝓘(ℝ, P →L[ℝ] P) k p (U ∩ (i.normalSpaceTrivialization hn hdim s₀).baseSet) ∧
      ∀ s ∈ U ∩ (i.normalSpaceTrivialization hn hdim s₀).baseSet,
        let e := i.normalSpaceTrivialization hn hdim s₀
        IsIdempotentElem (p s) ∧
        (∀ u v, G s (p s u) (v - p s v) = 0) ∧
        (∀ u v, h.normalHessian hn s (e.symm s (p s u)) (e.symm s (v - p s v)) = 0) ∧
        (∀ u, p s u ≠ 0 → h.normalHessian hn s (e.symm s (p s u)) (e.symm s (p s u)) < 0) ∧
        (∀ u, u - p s u ≠ 0 →
          0 < h.normalHessian hn s (e.symm s (u - p s u)) (e.symm s (u - p s u))) ∧
        Module.finrank ℝ (p s).range = manifoldMorseIndex I f (i s) ∧
        Module.finrank ℝ (p s).ker = manifoldMorseIndex I (-f) (i s) := by
  have : IsManifold I 2 M := .of_le (n := k + 2) le_add_self
  set e := i.normalSpaceTrivialization hn hdim s₀
  obtain ⟨Q, hQ, hrep⟩ :=
    h.exists_contMDiffOn_normalHessian_normalSpaceTrivialization hn hk hf hdim s₀
  have hGH (s : S) (hs : s ∈ U) :
      IsStrictlyPositive (continuousLinearMapOfBilin (𝕜 := ℝ) (G s)) :=
    isStrictlyPositive_continuousLinearMapOfBilin_iff.mpr ⟨hGsymm s hs, hGpos s hs⟩
  have hmaps (s : S) (hs : s ∈ U ∩ e.baseSet) :
      (Q s, G s) ∈ {p : (P →L[ℝ] P →L[ℝ] ℝ) × (P →L[ℝ] P →L[ℝ] ℝ) |
        (∀ u v, p.1 u v = p.1 v u) ∧ Function.Injective p.1 ∧
          IsStrictlyPositive (continuousLinearMapOfBilin (𝕜 := ℝ) p.2)} :=
    ⟨fun u v ↦ ((hrep s hs.2).1 u v).2, (hrep s hs.2).2, hGH s hs.1⟩
  refine ⟨fun s ↦ (Q s).negativeSpectralProjection (G s), fun s hs ↦ ?_, fun s hs ↦ ?_⟩
  · -- Smoothness: compose the smooth dependence on the pair of forms with the pair of families.
    have hpair := ((hQ s hs.2).mono inter_subset_right).prodMk_space
      ((hG s hs.1).mono inter_subset_left)
    exact (ContinuousLinearMap.contDiffOn_negativeSpectralProjection.contDiffWithinAt
      (hmaps s hs)).comp_contMDiffWithinAt (f := fun s' ↦ (Q s', G s')) hpair
        fun s' hs' ↦ hmaps s' hs'
  -- In the trivialization the normal Hessian is `Q s`.
  obtain ⟨hQrep, hinj⟩ := hrep s hs.2
  replace hs : s ∈ e.baseSet ∧ IsStrictlyPositive (continuousLinearMapOfBilin (𝕜 := ℝ) (G s)) :=
    ⟨hs.2, hGH s hs.1⟩
  have hsymm (u v : P) : Q s u v = Q s v u := (hQrep u v).2
  have hN (u v : P) : h.normalHessian hn s (e.symm s u) (e.symm s v) = Q s u v := (hQrep u v).1
  -- The inverse trivialization at `s` is an isometry from `Q s` to the normal Hessian.
  let L : QuadraticMap.IsometryEquiv (Q s).toBilinForm.toQuadraticMap
      (h.normalHessian hn s).toQuadraticMap :=
    { (e.linearEquivAt ℝ s hs.1).symm with
      map_app' := fun u ↦ by
        simp only [LinearEquiv.toFun_eq_coe, Trivialization.linearEquivAt_symm_apply,
          LinearMap.BilinMap.toQuadraticMap_apply, ContinuousLinearMap.toBilinForm_apply, hN] }
  refine ⟨ContinuousLinearMap.isIdempotentElem_negativeSpectralProjection hs.2,
    ContinuousLinearMap.metric_apply_negativeSpectralProjection_apply_sub_eq_zero hs.2,
    fun u v ↦ ?_, fun u hu ↦ ?_, fun u hu ↦ ?_, ?_, ?_⟩
  · rw [hN]
    exact ContinuousLinearMap.apply_negativeSpectralProjection_apply_sub_eq_zero hs.2 u v
  · rw [hN]
    exact ContinuousLinearMap.apply_negativeSpectralProjection_apply_self_lt_zero hsymm hu
  · rw [hN]
    exact ContinuousLinearMap.apply_sub_negativeSpectralProjection_apply_self_pos hs.2
      hsymm hinj hu
  · rw [ContinuousLinearMap.finrank_range_negativeSpectralProjection hs.2 hsymm,
      QuadraticMap.Equivalent.sigNeg_eq ⟨L⟩, h.sigNeg_normalHessian hn s]
  · rw [ContinuousLinearMap.finrank_ker_negativeSpectralProjection hs.2 hsymm hinj,
      QuadraticMap.Equivalent.sigPos_eq ⟨L⟩, h.sigPos_normalHessian hn s]

end TauCeti.SmoothEmbedding.IsNondegenerateCriticalSubmanifold
