/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Morse.TopHomology
public import TauCeti.Geometry.Manifold.RegularValue.Polynomial
public import TauCeti.Topology.Maps.Proper.Metric

/-!
# Homology and cohomology of pseudoconvex Morse functions and of affine complete intersections

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
(`TauCeti.exists_isZero_singularHomology_sublevelPair_norm_sq_sub_toLp_affineZeroLocus`).

Assembled across a compact band between regular values
(`TauCeti.IsMorse.isZero_singularHomology_sublevelPair_of_isManifoldStronglyPseudoconvexAt`) and
along a proper Morse exhaustion
(`TauCeti.IsMorse.isZero_singularHomology_of_manifoldMorseIndex_le`), these single-level
statements show that a manifold with a proper, bounded below, strongly `q`-pseudoconvex Morse
function has no homology above degree `n + q`
(`TauCeti.IsMorse.isZero_singularHomology_of_isManifoldStronglyPseudoconvexAt`); the extension to
arbitrary smooth strongly `q`-pseudoconvex exhaustions via Morse approximation is carried out in
`TauCeti/Geometry/Manifold/Complex/ExhaustionHomology.lean`. For a proper holomorphic immersion into
a proper complex inner product space (and in particular a closed holomorphic embedding into a
finite-dimensional complex inner product space), the squared distance from almost every point is
such a function with `q = 0`, so a complex `n`-manifold admitting a proper holomorphic immersion has
no homology above degree `n`
(`TauCeti.isZero_singularHomology_of_isProperMap_holomorphic_immersion`,
`TauCeti.isZero_singularHomology_of_isClosedEmbedding`). This applies in particular to a smooth
affine complete intersection (`TauCeti.isZero_singularHomology_affineZeroLocus`). The same
proper Morse function, of index at most `n`
(`TauCeti.exists_isMorse_isProperMap_bddBelow_and_manifoldMorseIndex_norm_sq_sub_comp_le`),
makes the top homology `Hₙ(M; V)` free for every free module `V` over a principal ideal ring
without zero divisors and kills the cohomology `Hᵏ(M; V, N)` for `k > n`
(`TauCeti.free_singularHomology_of_isProperMap_holomorphic_immersion`,
`TauCeti.isZero_singularCohomology_of_isProperMap_holomorphic_immersion`, and their
closed-embedding and affine complete intersection forms). These are the
homological forms of the theorem of Andreotti and Frankel, in Milnor's Morse-theoretic proof, that
a closed complex submanifold of `ℂᴺ` of complex dimension `n` has the homotopy type of a CW complex
of dimension at most `n`, and of its extension to strongly `q`-pseudoconvex exhaustions, with
dimension at most `n + q`.

## Main results

* `TauCeti.IsMorse.exists_isZero_singularHomology_sublevelPair_of_isManifoldStronglyPseudoconvexAt`:
  across a critical level of a strongly `q`-pseudoconvex Morse function, the relative homology of
  the sublevel pair vanishes above degree `n + q`.
* `TauCeti.exists_isZero_singularHomology_sublevelPair_norm_sq_sub_comp`: across a critical level
  of a Morse squared distance along a holomorphic immersion, it vanishes above degree `n`.
* `TauCeti.exists_isZero_singularHomology_sublevelPair_norm_sq_sub_toLp_affineZeroLocus`: the same
  on a smooth affine complete intersection, at every level.
* `TauCeti.IsMorse.isZero_singularHomology_sublevelPair_of_isManifoldStronglyPseudoconvexAt`:
  across a compact band between regular values of a strongly `q`-pseudoconvex Morse function, the
  relative homology of the sublevel pair vanishes above degree `n + q`.
* `TauCeti.IsMorse.isZero_singularHomology_of_isManifoldStronglyPseudoconvexAt`: a manifold with a
  proper, bounded below, strongly `q`-pseudoconvex Morse function has no homology above degree
  `n + q`.
* `TauCeti.isZero_singularHomology_of_isProperMap_holomorphic_immersion`: Andreotti–Frankel
  homology vanishing above the complex dimension along a proper holomorphic immersion into a proper
  complex inner product space.
* `TauCeti.isZero_singularHomology_of_isClosedEmbedding`: a closed complex submanifold of a
  finite-dimensional complex inner product space has no homology above its complex dimension.
* `TauCeti.isZero_singularHomology_affineZeroLocus`: a smooth affine complete intersection has no
  homology above its complex dimension.
* `TauCeti.free_singularHomology_of_isProperMap_holomorphic_immersion`,
  `TauCeti.free_singularHomology_of_isClosedEmbedding`,
  `TauCeti.free_singularHomology_affineZeroLocus`: the homology in the complex dimension is free.
* `TauCeti.isZero_singularCohomology_of_isProperMap_holomorphic_immersion`,
  `TauCeti.isZero_singularCohomology_of_isClosedEmbedding`,
  `TauCeti.isZero_singularCohomology_affineZeroLocus`: the cohomology vanishes above the complex
  dimension.

## References

* J. Milnor, *Morse Theory*, Annals of Mathematics Studies 51, Princeton University Press, 1963,
  Section 7, Theorems 7.1 and 7.2.
* A. Andreotti and T. Frankel, *The Lefschetz theorem on hyperplane sections*, Annals of
  Mathematics 69 (1959), 713–717.
* R. Hain, *Notes on the Morse theory of complex manifolds*, Section 2.
-/

public section

noncomputable section

open AlgebraicTopology CategoryTheory Limits Module Set Topology
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
    (fun x hx ↦ (hq x hx).manifoldMorseIndex_le_of_mem_criticalPoints (hf.contMDiff x) hx.1)
    hδ hcompact

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

/-- **Relative homology vanishing across a compact regular band of a strongly `q`-pseudoconvex
Morse function.** Let `f` be a real Morse function on a complex manifold of complex dimension `n`,
`a ≤ b` regular values with compact band `f⁻¹[a, b]`, and suppose `f` is strongly `q`-pseudoconvex
at every critical point in `f⁻¹[a, b]`. Then `Hₖ({f ≤ b}, {f ≤ a}; R)` vanishes for every
`k > n + q` and every coefficient object `R` of an abelian category with coproducts. -/
theorem IsMorse.isZero_singularHomology_sublevelPair_of_isManifoldStronglyPseudoconvexAt
    {A : Type v} [Category.{w} A] [Abelian A] [HasCoproducts.{u} A] {f : M → ℝ} {q : ℕ}
    (hf : IsMorse 𝓘(ℝ, E) f) {a b : ℝ} (hab : a ≤ b) (hcompact : IsCompact (f ⁻¹' Icc a b))
    (ha : IsRegularValue 𝓘(ℝ, E) 𝓘(ℝ) f a) (hb : IsRegularValue 𝓘(ℝ, E) 𝓘(ℝ) f b)
    (hq : ∀ x ∈ criticalPoints 𝓘(ℝ, E) f ∩ f ⁻¹' Icc a b,
      IsManifoldStronglyPseudoconvexAt E q f x) (R : A) {k : ℕ}
    (hk : finrank ℂ E + q < k) :
    IsZero ((sublevelPair f hab).singularHomology R k) := by
  have : IsManifold 𝓘(ℝ, E) ∞ M :=
    IsManifold.restrictScalars ℝ (inferInstance : IsManifold 𝓘(ℂ, E) ∞ M)
  exact hf.isZero_singularHomology_sublevelPair_of_manifoldMorseIndex_le hab hcompact ha hb
    (fun x hx ↦ (hq x hx).manifoldMorseIndex_le_of_mem_criticalPoints (hf.contMDiff x) hx.1) R hk

/-- **A manifold with a strongly `q`-pseudoconvex Morse exhaustion has no homology above degree
`n + q`.** Let `f` be a proper real Morse function, bounded below, on a complex manifold of complex
dimension `n`, which is strongly `q`-pseudoconvex at each of its critical points. Then the singular
homology `Hₖ(M; R)` vanishes for every `k > n + q`, with coefficients in any abelian category with
coproducts in which colimits of sequences are exact. -/
theorem IsMorse.isZero_singularHomology_of_isManifoldStronglyPseudoconvexAt
    {A : Type v} [Category.{w} A] [Abelian A] [HasCoproducts.{u} A] [HasColimitsOfShape ℕ A]
    [HasExactColimitsOfShape ℕ A] {f : M → ℝ} {q : ℕ} (hf : IsMorse 𝓘(ℝ, E) f)
    (hp : IsProperMap f) (hbdd : BddBelow (range f))
    (hq : ∀ x ∈ criticalPoints 𝓘(ℝ, E) f, IsManifoldStronglyPseudoconvexAt E q f x) (R : A)
    {k : ℕ} (hk : finrank ℂ E + q < k) :
    IsZero (((singularHomologyFunctor A k).obj R).obj (TopCat.of M)) := by
  have : IsManifold 𝓘(ℝ, E) ∞ M :=
    IsManifold.restrictScalars ℝ (inferInstance : IsManifold 𝓘(ℂ, E) ∞ M)
  exact hf.isZero_singularHomology_of_manifoldMorseIndex_le hp hbdd
    (fun x hx ↦ (hq x hx).manifoldMorseIndex_le_of_mem_criticalPoints (hf.contMDiff x) hx) R hk

/-- **Andreotti–Frankel theorem for proper holomorphic immersions.** If a complex manifold `M` of
complex dimension `n` admits a smooth proper holomorphic immersion into a proper complex inner
product space `F`, then `Hₖ(M; R) = 0` for `k > n` and every coefficient object `R` of an abelian
category with coproducts and exact sequential colimits. -/
theorem isZero_singularHomology_of_isProperMap_holomorphic_immersion {A : Type v} [Category.{w} A]
    [Abelian A] [HasCoproducts.{u} A] [HasColimitsOfShape ℕ A] [HasExactColimitsOfShape ℕ A]
    {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [ProperSpace F]
    {i : M → F} (hi : ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, F) ∞ i)
    (hinj : ∀ x, Function.Injective (mvfderiv 𝓘(ℂ, E) i x)) (hip : IsProperMap i)
    (R : A) {k : ℕ} (hk : finrank ℂ E < k) :
    IsZero (((singularHomologyFunctor A k).obj R).obj (TopCat.of M)) := by
  have : FiniteDimensional ℝ E := Module.Finite.trans ℂ E
  have : IsManifold 𝓘(ℝ, E) ∞ M :=
    IsManifold.restrictScalars ℝ (inferInstance : IsManifold 𝓘(ℂ, E) ∞ M)
  obtain ⟨a, ha, hap, hbdd, hidx⟩ :=
    exists_isMorse_isProperMap_bddBelow_and_manifoldMorseIndex_norm_sq_sub_comp_le hi hinj hip
  exact ha.isZero_singularHomology_of_manifoldMorseIndex_le hap hbdd hidx R hk

/-- **Free top homology along a proper holomorphic immersion.** If a complex manifold `M` of
complex dimension `n` admits a smooth proper holomorphic immersion into a proper complex inner
product space, then `Hₙ(M; V)` is free for every free module `V` over a principal ideal ring
without zero divisors. With integral coefficients it is free abelian, even when it is not finitely
generated. -/
theorem free_singularHomology_of_isProperMap_holomorphic_immersion {F : Type*}
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] [ProperSpace F]
    {i : M → F} (hi : ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, F) ∞ i)
    (hinj : ∀ x, Function.Injective (mvfderiv 𝓘(ℂ, E) i x)) (hip : IsProperMap i)
    {k : Type u} [CommRing k] [NoZeroDivisors k] [IsPrincipalIdealRing k] (V : ModuleCat.{u} k)
    [Module.Free k V] :
    Module.Free k (((singularHomologyFunctor (ModuleCat.{u} k) (finrank ℂ E)).obj V).obj
      (TopCat.of M)) := by
  have : FiniteDimensional ℝ E := Module.Finite.trans ℂ E
  have : IsManifold 𝓘(ℝ, E) ∞ M :=
    IsManifold.restrictScalars ℝ (inferInstance : IsManifold 𝓘(ℂ, E) ∞ M)
  obtain ⟨a, ha, hap, hbdd, hidx⟩ :=
    exists_isMorse_isProperMap_bddBelow_and_manifoldMorseIndex_norm_sq_sub_comp_le hi hinj hip
  exact ha.free_singularHomology_of_manifoldMorseIndex_le hap hbdd hidx V

/-- **Cohomology vanishing along a proper holomorphic immersion.** If a complex manifold `M` of
complex dimension `n` admits a smooth proper holomorphic immersion into a proper complex inner
product space, then `Hᵏ(M; V, N) = 0` for every `k > n`, every free module `V` over a principal
ideal ring `R` without zero divisors and every `R`-module `N`; for instance `Hᵏ(M; ℤ) = 0` for
`k > n`. -/
theorem isZero_singularCohomology_of_isProperMap_holomorphic_immersion {F : Type*}
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] [ProperSpace F]
    {i : M → F} (hi : ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, F) ∞ i)
    (hinj : ∀ x, Function.Injective (mvfderiv 𝓘(ℂ, E) i x)) (hip : IsProperMap i)
    {R : Type u} [CommRing R] [NoZeroDivisors R] [IsPrincipalIdealRing R] (V N : ModuleCat.{u} R)
    [Module.Free R V] {k : ℕ} (hk : finrank ℂ E < k) :
    IsZero ((TopCat.of M).singularCohomology V R N k) := by
  have : FiniteDimensional ℝ E := Module.Finite.trans ℂ E
  have : IsManifold 𝓘(ℝ, E) ∞ M :=
    IsManifold.restrictScalars ℝ (inferInstance : IsManifold 𝓘(ℂ, E) ∞ M)
  obtain ⟨a, ha, hap, hbdd, hidx⟩ :=
    exists_isMorse_isProperMap_bddBelow_and_manifoldMorseIndex_norm_sq_sub_comp_le hi hinj hip
  exact ha.isZero_singularCohomology_of_manifoldMorseIndex_le hap hbdd hidx V N hk

/-- **A closed complex submanifold of a complex inner product space has no homology above its
complex dimension.** Let `i` be a holomorphic immersion of a complex manifold of complex
dimension `n` into a finite-dimensional complex inner product space, which is a closed embedding.
Then the singular homology `Hₖ(M; R)` vanishes for every `k > n`, with coefficients in
any abelian category with coproducts in which colimits of sequences are exact. -/
theorem isZero_singularHomology_of_isClosedEmbedding {A : Type v} [Category.{w} A] [Abelian A]
    [HasCoproducts.{u} A] [HasColimitsOfShape ℕ A] [HasExactColimitsOfShape ℕ A] {F : Type*}
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] [FiniteDimensional ℂ F] {i : M → F}
    (hi : ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, F) ∞ i)
    (hinj : ∀ x, Function.Injective (mvfderiv 𝓘(ℂ, E) i x)) (hclosed : IsClosedEmbedding i)
    (R : A) {k : ℕ} (hk : finrank ℂ E < k) :
    IsZero (((singularHomologyFunctor A k).obj R).obj (TopCat.of M)) := by
  have : FiniteDimensional ℝ F := Module.Finite.trans ℂ F
  exact isZero_singularHomology_of_isProperMap_holomorphic_immersion hi hinj hclosed.isProperMap
    R hk

/-- **A closed complex submanifold of a complex inner product space has free top homology.** Let
`i` be a holomorphic immersion of a complex manifold of complex dimension `n` into a
finite-dimensional complex inner product space, which is a closed embedding. Then `Hₙ(M; V)` is
free for every free module `V` over a principal ideal ring without zero divisors. -/
theorem free_singularHomology_of_isClosedEmbedding {F : Type*} [NormedAddCommGroup F]
    [InnerProductSpace ℂ F] [FiniteDimensional ℂ F] {i : M → F}
    (hi : ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, F) ∞ i)
    (hinj : ∀ x, Function.Injective (mvfderiv 𝓘(ℂ, E) i x)) (hclosed : IsClosedEmbedding i)
    {k : Type u} [CommRing k] [NoZeroDivisors k] [IsPrincipalIdealRing k] (V : ModuleCat.{u} k)
    [Module.Free k V] :
    Module.Free k (((singularHomologyFunctor (ModuleCat.{u} k) (finrank ℂ E)).obj V).obj
      (TopCat.of M)) := by
  have : FiniteDimensional ℝ F := Module.Finite.trans ℂ F
  exact free_singularHomology_of_isProperMap_holomorphic_immersion hi hinj hclosed.isProperMap V

/-- **A closed complex submanifold of a complex inner product space has no cohomology above its
complex dimension.** Let `i` be a holomorphic immersion of a complex manifold of complex
dimension `n` into a finite-dimensional complex inner product space, which is a closed embedding.
Then `Hᵏ(M; V, N) = 0` for every `k > n`, every free module `V` over a principal ideal ring `R`
without zero divisors and every `R`-module `N`. -/
theorem isZero_singularCohomology_of_isClosedEmbedding {F : Type*} [NormedAddCommGroup F]
    [InnerProductSpace ℂ F] [FiniteDimensional ℂ F] {i : M → F}
    (hi : ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, F) ∞ i)
    (hinj : ∀ x, Function.Injective (mvfderiv 𝓘(ℂ, E) i x)) (hclosed : IsClosedEmbedding i)
    {R : Type u} [CommRing R] [NoZeroDivisors R] [IsPrincipalIdealRing R] (V N : ModuleCat.{u} R)
    [Module.Free R V] {k : ℕ} (hk : finrank ℂ E < k) :
    IsZero ((TopCat.of M).singularCohomology V R N k) := by
  have : FiniteDimensional ℝ F := Module.Finite.trans ℂ F
  exact isZero_singularCohomology_of_isProperMap_holomorphic_immersion hi hinj hclosed.isProperMap
    V N hk

/-- **A smooth affine complete intersection has no homology above its complex dimension.** Let
`X ⊆ ℂ^σ` be the common zero set of a polynomial family `p : ι → ℂ[X_σ]` whose Jacobian is
surjective at every common zero, a complex manifold of dimension `|σ| - |ι|`. Then the singular
homology `Hₖ(X; R)` vanishes for every `k > |σ| - |ι|`, with coefficients in any abelian category
with coproducts in which colimits of sequences are exact. -/
theorem isZero_singularHomology_affineZeroLocus {σ : Type u} {ι : Type*} [Fintype σ] [Fintype ι]
    {p : ι → MvPolynomial σ ℂ}
    (hp : ∀ x ∈ affineZeroLocus p, Function.Surjective (jacobiMatrixAt p x).mulVec)
    {A : Type v} [Category.{w} A] [Abelian A] [HasCoproducts.{u} A] [HasColimitsOfShape ℕ A]
    [HasExactColimitsOfShape ℕ A] (R : A) {k : ℕ} (hk : Fintype.card σ - Fintype.card ι < k) :
    IsZero (((singularHomologyFunctor A k).obj R).obj (TopCat.of (affineZeroLocus p))) := by
  let _ := affineZeroLocusChartedSpace hp
  have := isManifold_affineZeroLocus hp ∞
  have hdim : Module.finrank ℂ (Fin (Fintype.card σ - Fintype.card ι) → ℂ) =
      Fintype.card σ - Fintype.card ι := Module.finrank_fin_fun ℂ
  exact isZero_singularHomology_of_isClosedEmbedding (contMDiff_toLp_coe_affineZeroLocus hp ∞)
    (injective_mvfderiv_toLp_coe_affineZeroLocus hp)
    ((EuclideanSpace.equiv σ ℂ).symm.toHomeomorph.isClosedEmbedding.comp
      (isClosed_affineZeroLocus p).isClosedEmbedding_subtypeVal) R (by rw [hdim]; exact hk)

/-- **A smooth affine complete intersection has free top homology.** Let `X ⊆ ℂ^σ` be the common
zero set of a polynomial family `p : ι → ℂ[X_σ]` whose Jacobian is surjective at every common zero,
a complex manifold of dimension `|σ| - |ι|`. Then `H_{|σ| - |ι|}(X; V)` is free for every free
module `V` over a principal ideal ring without zero divisors; with integral coefficients it is free
abelian. -/
theorem free_singularHomology_affineZeroLocus {σ : Type u} {ι : Type*} [Fintype σ] [Fintype ι]
    {p : ι → MvPolynomial σ ℂ}
    (hp : ∀ x ∈ affineZeroLocus p, Function.Surjective (jacobiMatrixAt p x).mulVec)
    {k : Type u} [CommRing k] [NoZeroDivisors k] [IsPrincipalIdealRing k] (V : ModuleCat.{u} k)
    [Module.Free k V] :
    Module.Free k (((singularHomologyFunctor (ModuleCat.{u} k)
      (Fintype.card σ - Fintype.card ι)).obj V).obj (TopCat.of (affineZeroLocus p))) := by
  let _ := affineZeroLocusChartedSpace hp
  have := isManifold_affineZeroLocus hp ∞
  have := free_singularHomology_of_isClosedEmbedding (contMDiff_toLp_coe_affineZeroLocus hp ∞)
    (injective_mvfderiv_toLp_coe_affineZeroLocus hp)
    ((EuclideanSpace.equiv σ ℂ).symm.toHomeomorph.isClosedEmbedding.comp
      (isClosed_affineZeroLocus p).isClosedEmbedding_subtypeVal) V
  rwa [Module.finrank_fin_fun] at this

/-- **A smooth affine complete intersection has no cohomology above its complex dimension.** Let
`X ⊆ ℂ^σ` be the common zero set of a polynomial family `p : ι → ℂ[X_σ]` whose Jacobian is
surjective at every common zero, a complex manifold of dimension `|σ| - |ι|`. Then
`Hᵏ(X; V, N) = 0` for every `k > |σ| - |ι|`, every free module `V` over a principal ideal ring `R`
without zero divisors and every `R`-module `N`; for instance `Hᵏ(X; ℤ) = 0` for `k > |σ| - |ι|`. -/
theorem isZero_singularCohomology_affineZeroLocus {σ : Type u} {ι : Type*} [Fintype σ] [Fintype ι]
    {p : ι → MvPolynomial σ ℂ}
    (hp : ∀ x ∈ affineZeroLocus p, Function.Surjective (jacobiMatrixAt p x).mulVec)
    {R : Type u} [CommRing R] [NoZeroDivisors R] [IsPrincipalIdealRing R] (V N : ModuleCat.{u} R)
    [Module.Free R V] {k : ℕ} (hk : Fintype.card σ - Fintype.card ι < k) :
    IsZero ((TopCat.of (affineZeroLocus p)).singularCohomology V R N k) := by
  let _ := affineZeroLocusChartedSpace hp
  have := isManifold_affineZeroLocus hp ∞
  exact isZero_singularCohomology_of_isClosedEmbedding (contMDiff_toLp_coe_affineZeroLocus hp ∞)
    (injective_mvfderiv_toLp_coe_affineZeroLocus hp)
    ((EuclideanSpace.equiv σ ℂ).symm.toHomeomorph.isClosedEmbedding.comp
      (isClosed_affineZeroLocus p).isClosedEmbedding_subtypeVal) V N
    (by rwa [Module.finrank_fin_fun])

end TauCeti
