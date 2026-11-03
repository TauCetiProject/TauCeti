/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Morse.Cell.Homology
public import TauCeti.Geometry.Manifold.RegularValue.Polynomial

/-!
# Sublevel homology of pseudoconvex Morse functions

On a complex manifold of complex dimension `n`, a real Morse function which is strongly
`q`-pseudoconvex at its critical points has Morse index at most `n + q` at each of them
(`TauCeti.IsManifoldStronglyPseudoconvexAt.manifoldMorseIndex_le`). Crossing a critical level `c`
therefore attaches only cells of dimension at most `n + q`, so the relative singular homology
`Hⱼ({f ≤ c + ε}, {f ≤ c - ε})` vanishes for `j > n + q`, with coefficients in any abelian category
with coproducts
(`TauCeti.IsMorse.exists_isZero_singularHomology_sublevelPair_of_isManifoldStronglyPseudoconvexAt`).

The strictly plurisubharmonic case `q = 0` applies to the squared distance `‖i x - a‖²` along a
holomorphic immersion `i` into a complex inner product space
(`TauCeti.exists_isZero_singularHomology_sublevelPair_norm_sq_sub_comp`), and in particular to the
Euclidean squared distance on a smooth affine complete intersection in `ℂ^σ`, where every band is
compact because the squared distance is proper
(`TauCeti.exists_isZero_singularHomology_sublevelPair_norm_sq_sub_toLp_affineZeroLocus`). These
single-level statements are the steps from which, along a proper Morse exhaustion, one obtains
that a manifold with a strongly `q`-pseudoconvex exhaustion has no homology above degree `n + q`,
and a smooth affine variety of complex dimension `n` none above degree `n`; that assembly is not
carried out here.

## Main results

* `TauCeti.IsMorse.exists_isZero_singularHomology_sublevelPair_of_isManifoldStronglyPseudoconvexAt`:
  across a critical level of a strongly `q`-pseudoconvex Morse function, the relative homology of
  the sublevel pair vanishes above degree `n + q`.
* `TauCeti.exists_isZero_singularHomology_sublevelPair_norm_sq_sub_comp`: across a critical level
  of a Morse squared distance along a holomorphic immersion, it vanishes above degree `n`.
* `TauCeti.exists_isZero_singularHomology_sublevelPair_norm_sq_sub_toLp_affineZeroLocus`: the same
  on a smooth affine complete intersection, at every level.

## References

* J. Milnor, *Morse Theory*, Annals of Mathematics Studies 51, Princeton University Press, 1963,
  Section 7.
* R. Hain, *Notes on the Morse theory of complex manifolds*, Section 2.
-/

public section

noncomputable section

open CategoryTheory Limits Module Set
open scoped ContDiff Manifold

universe u v w

namespace TauCeti

variable {E : Type*} {M : Type u} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℂ, E) ∞ M] [T2Space M] {c δ : ℝ}

/-- **Relative homology across a critical level of a strongly `q`-pseudoconvex Morse function.**
Let `f` be a real Morse function on a complex manifold of complex dimension `n`, strongly
`q`-pseudoconvex at the critical points on the level `c`, and suppose the band
`f⁻¹[c - δ, c + δ]` is compact. For some `0 < ε ≤ δ`, the relative singular homology
`Hⱼ({f ≤ c + ε}, {f ≤ c - ε}; R)` vanishes for every `j > n + q` and every coefficient object `R`
of an abelian category with coproducts. -/
theorem IsMorse.exists_isZero_singularHomology_sublevelPair_of_isManifoldStronglyPseudoconvexAt
    {f : M → ℝ} {q : ℕ} (hf : IsMorse 𝓘(ℝ, E) f)
    (hq : ∀ x ∈ criticalPoints 𝓘(ℝ, E) f ∩ f ⁻¹' {c}, IsManifoldStronglyPseudoconvexAt E q f x)
    (hδ : 0 < δ) (hcompact : IsCompact (f ⁻¹' Icc (c - δ) (c + δ))) :
    ∃ ε, ∃ hε : 0 < ε, ε ≤ δ ∧
      ∀ {A : Type v} [Category.{w} A] [Abelian A] [HasCoproducts.{u} A] (R : A) (n : ℕ),
        finrank ℂ E + q < n → IsZero
          ((sublevelPair f (a := c - ε) (b := c + ε) (by linarith)).singularHomology R n) := by
  have : IsManifold 𝓘(ℝ, E) ∞ M :=
    IsManifold.restrictScalars ℝ (inferInstance : IsManifold 𝓘(ℂ, E) ∞ M)
  exact hf.exists_isZero_singularHomology_sublevelPair_of_manifoldMorseIndex_le
    (fun x hx ↦ (hq x hx).manifoldMorseIndex_le (hf.contMDiff x |>.of_le (by norm_cast))
      (mem_criticalPoints.1 hx.1)) hδ hcompact

/-- **Relative homology across a critical level of squared distance along a holomorphic
immersion.** Let `i` be a holomorphic immersion of a complex manifold of complex dimension `n` into
a complex inner product space, such that `x ↦ ‖i x - a‖²` is a Morse function with a compact band
around the level `c`. For some `0 < ε ≤ δ`, the relative singular homology of the sublevel pair
`({‖i - a‖² ≤ c + ε}, {‖i - a‖² ≤ c - ε})` vanishes above degree `n`, for coefficients in any
abelian category with coproducts. -/
theorem exists_isZero_singularHomology_sublevelPair_norm_sq_sub_comp {F : Type*}
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] {i : M → F} {a : F}
    (hi : ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, F) 2 i) (hinj : ∀ x, Function.Injective (mvfderiv 𝓘(ℂ, E) i x))
    (hf : IsMorse 𝓘(ℝ, E) fun x ↦ ‖i x - a‖ ^ 2) (hδ : 0 < δ)
    (hcompact : IsCompact ((fun x ↦ ‖i x - a‖ ^ 2) ⁻¹' Icc (c - δ) (c + δ))) :
    ∃ ε, ∃ hε : 0 < ε, ε ≤ δ ∧
      ∀ {A : Type v} [Category.{w} A] [Abelian A] [HasCoproducts.{u} A] (R : A) (n : ℕ),
        finrank ℂ E < n →
          IsZero ((sublevelPair (fun x ↦ ‖i x - a‖ ^ 2) (a := c - ε) (b := c + ε)
            (by linarith)).singularHomology R n) := by
  simpa using hf.exists_isZero_singularHomology_sublevelPair_of_isManifoldStronglyPseudoconvexAt
    (q := 0) (fun x _ ↦ (((isManifoldStrictlyPlurisubharmonicAt_norm_sq_sub_comp_iff (hi x)).2
      (hinj x)).isManifoldStronglyPseudoconvexAt 0)) hδ hcompact

/-- **Relative homology across a critical level of squared distance on a smooth affine complete
intersection.** Let `X ⊆ ℂ^σ` be the common zero set of a polynomial family with surjective
Jacobian at every common zero, a complex manifold of dimension `|σ| - |ι|`, and suppose the
Euclidean squared distance from `a` is a Morse function on `X`. Then at every level `c`, for some
`0 < ε ≤ δ`, the relative singular homology of the sublevel pair of the squared distance across `c`
vanishes above degree `|σ| - |ι|`, for coefficients in any abelian category with coproducts. -/
theorem exists_isZero_singularHomology_sublevelPair_norm_sq_sub_toLp_affineZeroLocus
    {σ : Type u} {ι : Type*} [Fintype σ] [Fintype ι] {p : ι → MvPolynomial σ ℂ}
    (hp : ∀ x ∈ affineZeroLocus p, Function.Surjective (jacobiMatrixAt p x).mulVec)
    (a : EuclideanSpace ℂ σ)
    (hf : letI := affineZeroLocusChartedSpace hp
      IsMorse 𝓘(ℝ, Fin (Fintype.card σ - Fintype.card ι) → ℂ)
        fun y : affineZeroLocus p ↦ ‖WithLp.toLp 2 (y : σ → ℂ) - a‖ ^ 2) (c : ℝ) (hδ : 0 < δ) :
    ∃ ε, ∃ hε : 0 < ε, ε ≤ δ ∧
      ∀ {A : Type v} [Category.{w} A] [Abelian A] [HasCoproducts.{u} A] (R : A) (n : ℕ),
        Fintype.card σ - Fintype.card ι < n →
          IsZero ((sublevelPair (fun y : affineZeroLocus p ↦ ‖WithLp.toLp 2 (y : σ → ℂ) - a‖ ^ 2)
            (a := c - ε) (b := c + ε) (by linarith)).singularHomology R n) := by
  let _ := affineZeroLocusChartedSpace hp
  have : IsManifold 𝓘(ℝ, Fin (Fintype.card σ - Fintype.card ι) → ℂ) ∞ (affineZeroLocus p) :=
    IsManifold.restrictScalars ℝ (isManifold_affineZeroLocus hp ∞)
  exact hf.exists_isZero_singularHomology_sublevelPair_of_manifoldMorseIndex_le
    (fun x hx ↦ manifoldMorseIndex_norm_sq_sub_toLp_affineZeroLocus_le hp a x
      (mem_criticalPoints.1 hx.1)) hδ
    ((isProperMap_norm_sq_sub_toLp_affineZeroLocus p a).isCompact_preimage isCompact_Icc)

end TauCeti
