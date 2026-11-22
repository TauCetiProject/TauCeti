/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.BettiNumber
public import TauCeti.Geometry.Manifold.Morse.Bott.Thom.Class
public import TauCeti.Geometry.Manifold.Morse.Generic.Inequalities
import Mathlib.Order.Interval.Set.Union
import TauCeti.Algebra.Category.ModuleCat.Biproducts
import TauCeti.Algebra.Category.ModuleCat.Finrank
import TauCeti.Geometry.Manifold.Morse.Bott.NormalSubbundle
import TauCeti.Geometry.Manifold.Morse.Bott.Thom.Pair
import TauCeti.Geometry.Manifold.SmoothEmbedding.NormalSpace.Metric
import TauCeti.Topology.VectorBundle.MayerVietoris.DirectedUnion

/-!
# The Morse–Bott inequalities

Let `f` be a Morse–Bott function on a compact boundaryless manifold `M`, exhibited by a family
`i a : S a → M` of critical submanifolds (`TauCeti.IsMorseBottFamily`), and let `K` be a field.
Suppose that the negative normal bundle of each piece `S a`, relative to some smooth fibre metric
on its normal bundle, has rank `r a` (the index of the piece) and a Thom class with coefficients
in `K`. This holds for every field when the negative normal bundles are oriented
(`TauCeti.VectorBundleOrientation.exists_isThomClass`), and for every bundle when `K` has
characteristic two, for instance over `𝔽₂` (`TauCeti.exists_isThomClass_of_two_eq_zero`). Write
`bⱼ = dim Hⱼ(M; K)` and let

`cⱼ = ∑ₐ b_{j - r a}(S a; K)`,

the sum running over the pieces with `r a ≤ j`: `cⱼ` is the coefficient of `tʲ` in the
Morse–Bott polynomial `∑ₐ t^{r a} P_{S a}(t)`. This file proves the **Morse–Bott inequalities**
for `b` and `c`: the weak inequalities `bⱼ ≤ cⱼ`, the strong inequalities
`bₙ - bₙ₋₁ + ⋯ ± b₀ ≤ cₙ - cₙ₋₁ + ⋯ ± c₀`, Euler's equality in degrees at least `dim M`, and the
polynomial identity `∑ⱼ cⱼ tʲ = ∑ⱼ bⱼ tʲ + (1 + t) Q(t)` with `Q` having natural number
coefficients. Over a field of characteristic two they hold for every Morse–Bott function, the index
of each piece being given as its Morse index. Over every field `K`, for instance `ℚ`, they hold when
the negative normal bundles of the pieces relative to given smooth fibre metrics are oriented (the
`_of_orientation` versions), as for a Morse–Bott function whose negative normal bundles carry
complex structures, and when the pieces are simply connected, over which every vector bundle is
orientable (the `_of_simplyConnectedSpace` versions). In characteristic two, when no two
consecutive `cⱼ` are both nonzero the inequalities force `bⱼ = cⱼ`, the lacunary principle: the
function is perfect over `K`. For a Morse function every piece is a point of index the Morse index,
so `cⱼ` is the number of critical points of index `j`
(`TauCeti.IsMorseBottFamily.morseBottCount_eq_criticalCount`). A point is simply connected, so the
`_of_simplyConnectedSpace` versions apply to the family of critical points of a Morse function
(`TauCeti.IsMorse.exists_isMorseBottFamily`) over every field, where they are the Morse
inequalities.

Without a Thom class the untwisted statement can fail: over a field of characteristic other than
`2`, the contribution of a piece whose negative normal bundle is not orientable is its homology
twisted by the orientation local system of that bundle, not its ordinary homology. Those
inequalities, over fields in which `2` is invertible, are in
`TauCeti.Geometry.Manifold.Morse.Bott.TwistedInequalities`.

The proof follows Bott. Cut the values of `f` at regular values `s 0 < ⋯ < s (N + 1)` so that each
band `f⁻¹[s j, s (j + 1)]` contains at most one critical value. The Morse–Bott inequalities are then
the inequalities of this filtration by sublevels
(`TauCeti.sum_range_neg_one_pow_mul_finrank_singularHomology_le_sum_sublevelPair_of_contMDiff` and
its companions), once the homology of each band is computed:

* crossing a critical level `c` deformation retracts the upper sublevel onto the lower one with the
  negative disc bundles of the pieces on that level attached, so the homology of the band is the
  direct sum of the homologies of the Thom pairs of the negative normal bundles `ν⁻ a` of those
  pieces, vector bundles of ranks `r a`
  (`TauCeti.IsMorseBottFamily.nonempty_singularHomology_sublevelPair_iso_sigma_thomPair`). So over
  any field `K`, `dim Hₙ({f ≤ b}, {f ≤ a}; K) = ∑ dim Hₙ(ν⁻ a, (ν⁻ a)₀; K)` over the pieces on the
  only critical level `c ∈ (a, b)` of the band
  (`TauCeti.IsMorseBottFamily.finrank_singularHomology_sublevelPair_eq_sum_finrank_thomPair`), and
  if `dim H_{r a + p}(ν⁻ a, (ν⁻ a)₀; K) = d a p` for every `p`, this is `∑ d a (n - r a)` over
  those pieces with `r a ≤ n`
  (`TauCeti.IsMorseBottFamily.finrank_singularHomology_sublevelPair_eq_sum_of_finrank_thomPair`);
* when `ν⁻ a` has a Thom class with coefficients in `K`, its Thom pair has the homology of `S a`
  shifted by `r a` (`TauCeti.homologyThomIso`), so
  `dim Hₙ({f ≤ b}, {f ≤ a}; K) = ∑ b_{n - r a}(S a; K)` over those pieces with `r a ≤ n`
  (`TauCeti.IsMorseBottFamily.finrank_singularHomology_sublevelPair_eq_sum_of_isThomClass`).

Summing over the bands counts every piece once.

The homology Thom isomorphism (`TauCeti.homologyThomIso`) needs the model fibre
`Fin r → ℝ` of the negative normal bundle in the universe of its base, so the manifolds, their
models and the coefficient field here live in `Type`.

## Main results

In the namespace `TauCeti.SmoothEmbedding`:

* `IsCriticalSubmanifold.finrank_singularHomology_negativeDiscSpherePair_of_isThomClass`: if the
  negative normal bundle has rank `r` and a Thom class over a nontrivial commutative ring `K`, then
  `dim Hₙ(D_ε, S_ε; K) = b_{n - r}(S; K)` if `r ≤ n`, and `0` otherwise.
* `IsNondegenerateCriticalSubmanifold.finrank_singularHomology_negativeDiscSpherePair`: the same
  over a field of characteristic two for a Morse–Bott submanifold of index `r`.

In the namespace `TauCeti.IsMorseBottFamily`:

* `exists_cut_sum_finrank_sublevelPair_eq_sum`: a cut of the values of `f` whose bands, summed,
  count the contribution of every piece once, for any coefficient field and any contributions of
  the pieces that compute the homology of the bands.
* `finrank_singularHomology_sublevelPair_eq_sum_finrank_thomPair`: over any field, the dimension of
  the homology of a band with a single critical value is the sum of the dimensions of the homology
  of the Thom pairs of the pieces on its level.
* `finrank_singularHomology_sublevelPair_eq_sum_of_finrank_thomPair`: the same dimension from the
  dimensions of the homology of those Thom pairs in degrees at least their ranks.
* `finrank_singularHomology_sublevelPair_eq_sum_of_isThomClass`: the dimension of the homology of
  a band with a single critical value, when the negative normal bundles have Thom classes over `K`.
* `bettiNumber_le_sum_of_isThomClass`,
  `sum_range_neg_one_pow_mul_bettiNumber_le_sum_of_isThomClass`,
  `sum_range_neg_one_pow_mul_bettiNumber_eq_sum_of_isThomClass` and
  `exists_sum_range_monomial_sum_eq_add_mul_of_isThomClass`: the weak and strong Morse–Bott
  inequalities, Euler's equality and the Morse–Bott polynomial identity over `K`, under the same
  hypothesis.
* `finrank_singularHomology_sublevelPair_eq_sum`, `bettiNumber_le_sum`,
  `sum_range_neg_one_pow_mul_bettiNumber_le_sum`, `sum_range_neg_one_pow_mul_bettiNumber_eq_sum` and
  `exists_sum_range_monomial_sum_eq_add_mul`: the same over a field of characteristic two, such as
  `𝔽₂`, for every Morse–Bott function.
* `bettiNumber_eq_sum_of_forall_eq_zero_or_eq_zero`: the lacunary principle in characteristic two,
  `bₙ = cₙ` when no two consecutive `cₙ` are both nonzero.
* `finrank_singularHomology_sublevelPair_eq_sum_of_orientation`,
  `bettiNumber_le_sum_of_orientation`,
  `sum_range_neg_one_pow_mul_bettiNumber_le_sum_of_orientation`,
  `sum_range_neg_one_pow_mul_bettiNumber_eq_sum_of_orientation` and
  `exists_sum_range_monomial_sum_eq_add_mul_of_orientation`: the same over every field, when the
  negative normal bundles are oriented
  (`SmoothEmbedding.IsNondegenerateCriticalSubmanifold.NegativeNormalBundleOrientation`).
* `finrank_singularHomology_sublevelPair_eq_sum_of_simplyConnectedSpace`,
  `bettiNumber_le_sum_of_simplyConnectedSpace`,
  `sum_range_neg_one_pow_mul_bettiNumber_le_sum_of_simplyConnectedSpace`,
  `sum_range_neg_one_pow_mul_bettiNumber_eq_sum_of_simplyConnectedSpace` and
  `exists_sum_range_monomial_sum_eq_add_mul_of_simplyConnectedSpace`: the same over every field,
  when the pieces are simply connected, for instance points.

## References

* R. Bott, *Nondegenerate critical manifolds*, Annals of Mathematics 60 (1954), 248–261.
* R. Bott, *Lectures on Morse theory, old and new*, Bulletin of the American Mathematical
  Society 7 (1982), 331–358, Section 1.
* R. L. Cohen, K. Iga and P. Norbury, *Topics in Morse theory: lecture notes*, 2006,
  Theorems 15.4 and 15.6.
-/

public section

noncomputable section

open Bundle CategoryTheory Function Limits Module Set Topology
open Polynomial (monomial)
open scoped ContDiff Manifold Polynomial

namespace TauCeti

/-! ### The contribution of one Morse–Bott submanifold -/

namespace SmoothEmbedding.IsCriticalSubmanifold

variable {E : Type} {H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  {E' H' : Type*} {S : Type} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
  [TopologicalSpace H'] {J : ModelWithCorners ℝ E' H'} [TopologicalSpace S] [ChartedSpace H' S]
  [IsManifold J 1 S] {f : M → ℝ} {n : ℕ∞ω} {i : SmoothEmbedding J I n S M} (hn : n ≠ 0)
  [I.Boundaryless] [IsManifold I 2 M] (h : i.IsCriticalSubmanifold f)
  {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
  (g : RiemannianMetric fun s ↦ i.NormalSpace s hn)
  (hdim : finrank ℝ P = finrank ℝ E - finrank ℝ E') {r : ℕ}

/-- **The homology of the negative disc bundle from a Thom class, in dimensions.** Let `i` be a
critical submanifold of `f` and `g` a fibre metric on its normal bundle, and suppose that the
negative normal spaces have continuous local frames of size `r`, so that they form a vector bundle
`ν⁻` of rank `r`. If `ν⁻` has a Thom class with coefficients in a nontrivial commutative ring
`K`, then for `ε > 0` the
negative disc bundle `D_ε`, relative to the negative sphere bundle `S_ε`, has
`dim Hₖ(D_ε, S_ε; K) = b_{k - r}(S; K)` when `r ≤ k`, and `0` when `k < r`. -/
theorem finrank_singularHomology_negativeDiscSpherePair_of_isThomClass
    (hV : letI := i.normalSpaceFiberBundle hn hdim
      HasLocalSubbundleFrames P (Fin r) (h.negativeNormalSpace hn g))
    {ε : ℝ} (hε : 0 < ε) {K : Type} [CommRing K] [Nontrivial K]
    (u : letI := i.normalSpaceFiberBundle hn hdim
      haveI := i.normalSpaceVectorBundle hn hdim
      letI := subbundleTopology P (F' := Fin r → ℝ) (h.negativeNormalSpace hn g)
      letI := hV.fiberBundle
      (thomPair (Fin r → ℝ) fun s ↦ h.negativeNormalSpace hn g s).singularCohomology
        (ModuleCat.of K K) K (ModuleCat.of K K) (finrank ℝ (Fin r → ℝ)))
    (hu : letI := i.normalSpaceFiberBundle hn hdim
      haveI := i.normalSpaceVectorBundle hn hdim
      letI := subbundleTopology P (F' := Fin r → ℝ) (h.negativeNormalSpace hn g)
      letI := hV.fiberBundle
      IsThomClass (Fin r → ℝ) (fun s ↦ h.negativeNormalSpace hn g s) u) (k : ℕ) :
    finrank K ((h.negativeDiscSpherePair hn P g ε).singularHomology (ModuleCat.of K K) k :
        ModuleCat K) =
      if r ≤ k then bettiNumber K S (k - r) else 0 := by
  let := i.normalSpaceFiberBundle hn hdim
  have := i.normalSpaceVectorBundle hn hdim
  let := subbundleTopology P (F' := Fin r → ℝ) (h.negativeNormalSpace hn g)
  let := hV.fiberBundle
  have := hV.vectorBundle
  -- The negative disc-sphere pair has the homology of the Thom pair of `ν⁻`, which the Thom class
  -- identifies with that of `S` shifted by `r`.
  rw [(@asIso _ _ _ _ _ (h.isIso_singularHomologyMap_negativeDiscThomPairMap hn g r hdim hV hε
    (ModuleCat.of K K) k)).toLinearEquiv.finrank_eq]
  exact finrank_singularHomology_thomPair_eq_ite _ _ (finrank_fin_fun ℝ) _
    (fun p ↦ finrank_singularHomology_thomPair_of_isThomClass _ _ p _ (by rw [finrank_fin_fun]) hu)
    k

end SmoothEmbedding.IsCriticalSubmanifold

namespace SmoothEmbedding.IsNondegenerateCriticalSubmanifold

variable {E : Type} {H M E' H' P : Type*} {S : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [NormedAddCommGroup E']
  [NormedSpace ℝ E'] [FiniteDimensional ℝ E'] [TopologicalSpace H'] {J : ModelWithCorners ℝ E' H'}
  [TopologicalSpace S] [ChartedSpace H' S] [IsManifold J ∞ S] [NormedAddCommGroup P]
  [NormedSpace ℝ P] [FiniteDimensional ℝ P] {f : M → ℝ} {i : SmoothEmbedding J I ∞ S M}
  (hn : (∞ : ℕ∞ω) ≠ 0)

/-- **The homology in characteristic two of the negative disc bundle of a Morse–Bott
submanifold.** Let `i` be a nondegenerate critical submanifold of a smooth function `f`, with Morse
index `r` at every point, and let `g` be a smooth fibre metric on its normal bundle. Let `K` be a
nontrivial commutative ring of characteristic two, such as `ZMod 2`. For `ε > 0`, the negative disc
bundle `D_ε` relative to `g`, taken relative to its boundary `S_ε`, has
`dim Hₙ(D_ε, S_ε; K) = b_{n - r}(S; K)` when `r ≤ n`, and `0` when `n < r`: it has the homology
of the Thom pair of the negative normal bundle, a vector bundle of rank `r`, which has a Thom
class over `K` with no orientation needed. -/
theorem finrank_singularHomology_negativeDiscSpherePair
    (h : i.IsNondegenerateCriticalSubmanifold f) (hfs : ContMDiff I 𝓘(ℝ) ∞ f)
    (hdim : finrank ℝ P = finrank ℝ E - finrank ℝ E')
    (g : letI := i.normalSpaceFiberBundle hn hdim
      letI := i.normalSpaceVectorBundle hn hdim
      ContMDiffRiemannianMetric J ∞ P fun s ↦ i.NormalSpace s hn) {r : ℕ}
    (hr : ∀ s, manifoldMorseIndex I f (i s) = r) {ε : ℝ} (hε : 0 < ε) (K : Type) [CommRing K]
    [Nontrivial K] (h2 : (2 : K) = 0) (n : ℕ) :
    letI := i.normalSpaceFiberBundle hn hdim
    letI := i.normalSpaceVectorBundle hn hdim
    finrank K ((h.negativeDiscSpherePair hn P g.toRiemannianMetric ε).singularHomology
        (ModuleCat.of K K) n : ModuleCat K) =
      if r ≤ n then bettiNumber K S (n - r) else 0 := by
  let := i.normalSpaceFiberBundle hn hdim
  let := i.normalSpaceVectorBundle hn hdim
  have hV := h.hasLocalSubbundleFrames_negativeNormalSpace hn hfs hdim g hr
  let := subbundleTopology P (F' := Fin r → ℝ) (h.negativeNormalSpace hn g.toRiemannianMetric)
  let := hV.fiberBundle
  have := hV.vectorBundle
  obtain ⟨u, hu⟩ := exists_isThomClass_of_two_eq_zero (F := Fin r → ℝ)
    (E := fun s ↦ h.negativeNormalSpace hn g.toRiemannianMetric s) K h2
  exact h.finrank_singularHomology_negativeDiscSpherePair_of_isThomClass hn
    g.toRiemannianMetric hdim hV hε u hu n

/-- For a Morse–Bott submanifold of constant index `r` and a field `K` of characteristic two, the
negative normal bundle relative to some smooth fibre metric has a Thom class with coefficients in
`K`. -/
private theorem exists_isThomClass_negativeNormalSpace_of_two_eq_zero
    (h : i.IsNondegenerateCriticalSubmanifold f) (hfs : ContMDiff I 𝓘(ℝ) ∞ f)
    [T2Space M] [SigmaCompactSpace S] (hdim : finrank ℝ P = finrank ℝ E - finrank ℝ E')
    {r : ℕ} (hr : ∀ s, manifoldMorseIndex I f (i s) = r) (K : Type) [Field K]
    (h2 : (2 : K) = 0) :
    letI := i.normalSpaceFiberBundle hn hdim
    letI := i.normalSpaceVectorBundle hn hdim
    ∃ (g : ContMDiffRiemannianMetric J ∞ P fun s ↦ i.NormalSpace s hn)
      (hV : HasLocalSubbundleFrames P (Fin r) (h.negativeNormalSpace hn g.toRiemannianMetric)),
      letI := subbundleTopology P (F' := Fin r → ℝ)
        (h.negativeNormalSpace hn g.toRiemannianMetric)
      letI := hV.fiberBundle
      ∃ u, IsThomClass (R := ModuleCat.of K K) (k := K) (M := ModuleCat.of K K) (Fin r → ℝ)
        (fun s ↦ h.negativeNormalSpace hn g.toRiemannianMetric s) u := by
  let := i.normalSpaceFiberBundle hn hdim
  let := i.normalSpaceVectorBundle hn hdim
  obtain ⟨g⟩ := i.nonempty_contMDiffRiemannianMetric_normalSpace hn hdim
  have hV := h.hasLocalSubbundleFrames_negativeNormalSpace hn hfs hdim g hr
  let := subbundleTopology P (F' := Fin r → ℝ) (h.negativeNormalSpace hn g.toRiemannianMetric)
  let := hV.fiberBundle
  have := hV.vectorBundle
  exact ⟨g, hV, exists_isThomClass_of_two_eq_zero K h2⟩

end SmoothEmbedding.IsNondegenerateCriticalSubmanifold

/-! ### The homology of a band with a single critical value -/

section Level

variable {E : Type} {H : Type*} {M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {ι : Type*} {E' H' P : ι → Type*} {S : ι → Type}
  [∀ j, NormedAddCommGroup (E' j)] [∀ j, NormedSpace ℝ (E' j)] [∀ j, FiniteDimensional ℝ (E' j)]
  [∀ j, TopologicalSpace (H' j)] {J : ∀ j, ModelWithCorners ℝ (E' j) (H' j)}
  [∀ j, TopologicalSpace (S j)] [∀ j, ChartedSpace (H' j) (S j)] [∀ j, IsManifold (J j) ∞ (S j)]
  [∀ j, NormedAddCommGroup (P j)] [∀ j, NormedSpace ℝ (P j)] [∀ j, FiniteDimensional ℝ (P j)]
  {f : M → ℝ} {i : ∀ j, SmoothEmbedding (J j) I ∞ (S j) M} (hn : (∞ : ℕ∞ω) ≠ 0)

namespace IsMorseBottFamily

variable [T2Space M] [SecondCountableTopology M] [CompactSpace M] [Fintype ι]
  [∀ j, (J j).Boundaryless] (h : IsMorseBottFamily i f) {r : ι → ℕ} (K : Type) [Field K]

omit [FiniteDimensional ℝ E] [I.Boundaryless] [IsManifold I ∞ M]
  [∀ j, FiniteDimensional ℝ (E' j)] [T2Space M] [SecondCountableTopology M]
  [∀ j, (J j).Boundaryless] in
include h in
open scoped Classical in
/-- **A cut of the values of a Morse–Bott function.** Let the family `i j : S j → M` exhibit `f`
as a Morse–Bott function on a compact boundaryless manifold, and let `K` be a field. Suppose that
the piece `S j` contributes `d j (n - r j)` to the dimension of the relative homology in degree `n`
of a band with a single critical value, for the pieces on that level with `r j ≤ n`. Then the
values of `f` can be cut at values `s 0 ≤ s 1 ≤ ⋯ ≤ s (N + 1)`, regular from `s 1` on, with
`s 0 < f ≤ s (N + 1)`, such that summing the dimensions of the relative homologies of the bands
`[s j, s (j + 1)]` counts the contribution of every piece once:
`∑ⱼ dim Hₙ({f ≤ s (j + 1)}, {f ≤ s j}; K) = ∑ d p (n - r p)` over the pieces with `r p ≤ n`. -/
theorem exists_cut_sum_finrank_sublevelPair_eq_sum (d : ι → ℕ → ℕ)
    (hband : ∀ {a b c : ℝ} (hac : a < c) (hcb : c < b),
      (∀ x ∈ criticalPoints I f, f x ∈ Icc a b → f x = c) → ∀ n,
        finrank K ((sublevelPair f (hac.trans hcb).le).singularHomology (ModuleCat.of K K) n :
            ModuleCat K) =
          ∑ j with (∀ s, f (i j s) = c) ∧ r j ≤ n, d j (n - r j)) :
    ∃ (s : ℕ → ℝ) (hs : Monotone s) (N : ℕ), (∀ x, s 0 < f x) ∧ (∀ x, f x ≤ s (N + 1)) ∧
      (∀ j ≤ N, IsRegularValue I 𝓘(ℝ) f (s (j + 1))) ∧
      ∀ n, ∑ j ∈ Finset.range (N + 1),
          finrank K ((sublevelPair f (hs j.le_succ)).singularHomology (ModuleCat.of K K) n :
            ModuleCat K) =
        ∑ p with r p ≤ n, d p (n - r p) := by
  classical
  have hn : (∞ : ℕ∞ω) ≠ 0 := by simp
  obtain ⟨s, N, hs, hs₀, hsN, hcut, hreg⟩ :=
    exists_monotone_isCriticalBand_of_finite_image_criticalPoints h.contMDiff.continuous
      (h.finite_image_criticalPoints hn)
  choose c hc hcrit using fun j ↦ (hcut j).exists_mem_Ioo_forall_eq
  refine ⟨s, hs, N, hs₀, hsN, fun j _ ↦ hreg (j + 1), fun n ↦ ?_⟩
  rw [Finset.sum_congr rfl fun j _ ↦ hband (hc j).1 (hc j).2 (hcrit j) n]
  simp_rw [Finset.sum_filter]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun p _ ↦ ?_
  -- The piece `p` lies on the critical level of exactly one band, `j₀`.
  obtain ⟨t₀⟩ := h.nonempty p
  have hv := (h.isNondegenerateCriticalSubmanifold p).mem_criticalPoints t₀
  have hfp (t : S p) : f (i p t) = f (i p t₀) := h.subsingleton_image_range hn p
    (mem_image_of_mem f (mem_range_self t)) (mem_image_of_mem f (mem_range_self t₀))
  obtain ⟨j₀, hj₀, hlt, hle⟩ := mem_iUnion₂.1
    (Ioc_subset_biUnion_Ioc (N + 1) s ⟨hs₀ (i p t₀), hsN (i p t₀)⟩)
  have hcj₀ : f (i p t₀) = c j₀ := hcrit j₀ _ hv ⟨hlt.le, hle⟩
  have hlevel (j : ℕ) : (∀ t, f (i p t) = c j) ↔ j = j₀ := by
    refine ⟨fun hj ↦ ?_, fun hj t ↦ hj ▸ (hfp t).trans hcj₀⟩
    have hcj := (hj t₀).symm.trans hcj₀
    rcases Nat.lt_trichotomy j j₀ with hlt' | rfl | hlt'
    · linarith [hs (Nat.succ_le_of_lt hlt'), (hc j).2, (hc j₀).1]
    · rfl
    · linarith [hs (Nat.succ_le_of_lt hlt'), (hc j).1, (hc j₀).2]
  rw [Finset.sum_eq_single_of_mem j₀ hj₀
    fun j _ hj ↦ ite_eq_right fun hpj ↦ hj ((hlevel j).1 hpj.1)]
  simp [(hlevel j₀).2 rfl]

/-! #### The homology of a band from the Thom pairs of its pieces -/

section ThomPair

variable (hdim : ∀ j, finrank ℝ (P j) = finrank ℝ E - finrank ℝ (E' j))
  (g : letI : ∀ j, FiberBundle (P j) fun s ↦ (i j).NormalSpace s hn :=
      fun j ↦ (i j).normalSpaceFiberBundle hn (hdim j)
    letI : ∀ j, VectorBundle ℝ (P j) fun s ↦ (i j).NormalSpace s hn :=
      fun j ↦ (i j).normalSpaceVectorBundle hn (hdim j)
    ∀ j, ContMDiffRiemannianMetric (J j) ∞ (P j) fun s ↦ (i j).NormalSpace s hn)

include h

open scoped Classical in
/-- **The dimension of the homology of a critical band of a Morse–Bott function is the sum over the
pieces on its level of the dimensions of the homology of their Thom pairs.** Let the family
`i j : S j → M` exhibit `f` as a Morse–Bott function on a compact boundaryless manifold, with Morse
index `r j` along the piece `S j`, let `g j` be smooth fibre metrics on the normal bundles of the
pieces, and let `ν⁻ j` be the negative normal bundle of `S j` relative to `g j`. Let `K` be a field
and let `a < c < b` be such that `c` is the only critical value of `f` in `[a, b]`. Then
`dim Hₙ({f ≤ b}, {f ≤ a}; K) = ∑ dim Hₙ(ν⁻ j, (ν⁻ j)₀; K)`, the sum running over the pieces on the
level `f = c`. -/
theorem finrank_singularHomology_sublevelPair_eq_sum_finrank_thomPair
    (hr : ∀ j s, manifoldMorseIndex I f (i j s) = r j) {a b c : ℝ} (hac : a < c)
    (hcb : c < b) (hcrit : ∀ x ∈ criticalPoints I f, f x ∈ Icc a b → f x = c) (n : ℕ) :
    letI : ∀ j, FiberBundle (P j) fun s ↦ (i j).NormalSpace s hn :=
      fun j ↦ (i j).normalSpaceFiberBundle hn (hdim j)
    letI : ∀ j, VectorBundle ℝ (P j) fun s ↦ (i j).NormalSpace s hn :=
      fun j ↦ (i j).normalSpaceVectorBundle hn (hdim j)
    letI : ∀ j, TopologicalSpace (TotalSpace (Fin (r j) → ℝ)
        fun s ↦ (h.isNondegenerateCriticalSubmanifold j).negativeNormalSpace hn
          (g j).toRiemannianMetric s) :=
      fun j ↦ subbundleTopology (P j)
        ((h.isNondegenerateCriticalSubmanifold j).negativeNormalSpace hn (g j).toRiemannianMetric)
    finrank K ((sublevelPair f (hac.trans hcb).le).singularHomology (ModuleCat.of K K) n :
        ModuleCat K) =
      ∑ j : {j // ∀ s, f (i j s) = c}, finrank K ((thomPair (Fin (r j) → ℝ) fun s ↦
        (h.isNondegenerateCriticalSubmanifold j).negativeNormalSpace hn (g j).toRiemannianMetric s
        ).singularHomology (ModuleCat.of K K) n : ModuleCat K) := by
  let _ : ∀ j, FiberBundle (P j) fun s ↦ (i j).NormalSpace s hn :=
    fun j ↦ (i j).normalSpaceFiberBundle hn (hdim j)
  let _ : ∀ j, VectorBundle ℝ (P j) fun s ↦ (i j).NormalSpace s hn :=
    fun j ↦ (i j).normalSpaceVectorBundle hn (hdim j)
  let _ : ∀ j, TopologicalSpace (TotalSpace (Fin (r j) → ℝ)
      fun s ↦ (h.isNondegenerateCriticalSubmanifold j).negativeNormalSpace hn
        (g j).toRiemannianMetric s) :=
    fun j ↦ subbundleTopology (P j)
      ((h.isNondegenerateCriticalSubmanifold j).negativeNormalSpace hn (g j).toRiemannianMetric)
  -- The band has the homology of the sum of the Thom pairs of the pieces on the level `c`, a
  -- finite-dimensional space, so each summand is finite-dimensional.
  obtain ⟨e⟩ := h.nonempty_singularHomology_sublevelPair_iso_sigma_thomPair hn hac hcb hcrit hdim g
    hr (ModuleCat.of K K) n
  let V (j : {j // ∀ s, f (i j s) = c}) : ModuleCat K := (thomPair (Fin (r j) → ℝ) fun s ↦
    (h.isNondegenerateCriticalSubmanifold j).negativeNormalSpace hn (g j).toRiemannianMetric s
    ).singularHomology (ModuleCat.of K K) n
  let e' := e ≪≫ (biproduct.isoCoproduct V).symm
  have := finite_singularHomology_sublevelPair_of_criticalValue (ModuleCat.of K K) h.contMDiff
    h.contMDiff.continuous.isProperMap hac hcb hcrit n
  have := Module.Finite.equiv e'.toLinearEquiv
  have := ModuleCat.finite_of_finite_biproduct V
  rw [e'.toLinearEquiv.finrank_eq, ModuleCat.finrank_biproduct]

variable (hV : letI : ∀ j, FiberBundle (P j) fun s ↦ (i j).NormalSpace s hn :=
      fun j ↦ (i j).normalSpaceFiberBundle hn (hdim j)
    letI : ∀ j, VectorBundle ℝ (P j) fun s ↦ (i j).NormalSpace s hn :=
      fun j ↦ (i j).normalSpaceVectorBundle hn (hdim j)
    ∀ j, HasLocalSubbundleFrames (P j) (Fin (r j))
      ((h.isNondegenerateCriticalSubmanifold j).negativeNormalSpace hn (g j).toRiemannianMetric))

include hV in
open scoped Classical in
/-- **The homology of a critical band from the homology of the Thom pairs of its pieces.** Under
the hypotheses of
`TauCeti.IsMorseBottFamily.finrank_singularHomology_sublevelPair_eq_sum_finrank_thomPair`, with the
negative normal bundles `ν⁻ j` of ranks `r j` given by the local frames `hV j`, suppose
`dim H_{r j + p}(ν⁻ j, (ν⁻ j)₀; K) = d j p` for every piece `j` and every `p`. Then
`dim Hₙ({f ≤ b}, {f ≤ a}; K) = ∑ d j (n - r j)`, the sum running over the pieces on the level
`f = c` of index at most `n`. -/
theorem finrank_singularHomology_sublevelPair_eq_sum_of_finrank_thomPair (d : ι → ℕ → ℕ)
    (hd : letI : ∀ j, FiberBundle (P j) fun s ↦ (i j).NormalSpace s hn :=
        fun j ↦ (i j).normalSpaceFiberBundle hn (hdim j)
      letI : ∀ j, VectorBundle ℝ (P j) fun s ↦ (i j).NormalSpace s hn :=
        fun j ↦ (i j).normalSpaceVectorBundle hn (hdim j)
      letI : ∀ j, TopologicalSpace (TotalSpace (Fin (r j) → ℝ)
          fun s ↦ (h.isNondegenerateCriticalSubmanifold j).negativeNormalSpace hn
            (g j).toRiemannianMetric s) :=
        fun j ↦ subbundleTopology (P j)
          ((h.isNondegenerateCriticalSubmanifold j).negativeNormalSpace hn (g j).toRiemannianMetric)
      ∀ j p, finrank K ((thomPair (Fin (r j) → ℝ) fun s ↦
        (h.isNondegenerateCriticalSubmanifold j).negativeNormalSpace hn (g j).toRiemannianMetric s
        ).singularHomology (ModuleCat.of K K) (r j + p) : ModuleCat K) = d j p)
    {a b c : ℝ} (hac : a < c) (hcb : c < b)
    (hcrit : ∀ x ∈ criticalPoints I f, f x ∈ Icc a b → f x = c) (n : ℕ) :
    finrank K ((sublevelPair f (hac.trans hcb).le).singularHomology (ModuleCat.of K K) n :
        ModuleCat K) =
      ∑ j with (∀ s, f (i j s) = c) ∧ r j ≤ n, d j (n - r j) := by
  let _ : ∀ j, FiberBundle (P j) fun s ↦ (i j).NormalSpace s hn :=
    fun j ↦ (i j).normalSpaceFiberBundle hn (hdim j)
  let _ : ∀ j, VectorBundle ℝ (P j) fun s ↦ (i j).NormalSpace s hn :=
    fun j ↦ (i j).normalSpaceVectorBundle hn (hdim j)
  let _ : ∀ j, TopologicalSpace (TotalSpace (Fin (r j) → ℝ)
      fun s ↦ (h.isNondegenerateCriticalSubmanifold j).negativeNormalSpace hn
        (g j).toRiemannianMetric s) :=
    fun j ↦ subbundleTopology (P j)
      ((h.isNondegenerateCriticalSubmanifold j).negativeNormalSpace hn (g j).toRiemannianMetric)
  let _ (j : ι) := (hV j).fiberBundle
  have (j : ι) := (hV j).vectorBundle
  -- The frames have size the dimension of the negative normal spaces, which is the index.
  have hr (j : ι) (s : S j) : manifoldMorseIndex I f (i j s) = r j := by
    rw [← (h.isNondegenerateCriticalSubmanifold j).finrank_negativeNormalSpace hn
      (g j).toRiemannianMetric, (hV j).finrank_eq, Fintype.card_fin]
  rw [h.finrank_singularHomology_sublevelPair_eq_sum_finrank_thomPair hn K hdim g hr hac hcb hcrit
    n]
  -- Each Thom pair has the homology `d j` shifted by the index, and none below the index.
  have hV' (j : {j // ∀ s, f (i j s) = c}) := finrank_singularHomology_thomPair_eq_ite _ _
    (finrank_fin_fun ℝ) (d j) (hd j) n
  simp only [hV']
  rw [← Finset.filter_filter, Finset.sum_filter]
  exact (Finset.sum_subtype _ (fun j ↦ by simp) fun j ↦ if r j ≤ n then d j (n - r j) else 0).symm

end ThomPair


/-! #### Negative normal bundles with Thom classes -/

section ThomClass

variable (hdim : ∀ j, finrank ℝ (P j) = finrank ℝ E - finrank ℝ (E' j))
  (hK : ∀ j, letI := (i j).normalSpaceFiberBundle hn (hdim j)
    letI := (i j).normalSpaceVectorBundle hn (hdim j)
    ∃ (g : ContMDiffRiemannianMetric (J j) ∞ (P j) fun s ↦ (i j).NormalSpace s hn)
      (hV : HasLocalSubbundleFrames (P j) (Fin (r j))
        ((h.isNondegenerateCriticalSubmanifold j).negativeNormalSpace hn g.toRiemannianMetric)),
      letI := subbundleTopology (P j) (F' := Fin (r j) → ℝ)
        ((h.isNondegenerateCriticalSubmanifold j).negativeNormalSpace hn g.toRiemannianMetric)
      letI := hV.fiberBundle
      ∃ u, IsThomClass (R := ModuleCat.of K K) (k := K) (M := ModuleCat.of K K) (Fin (r j) → ℝ)
        (fun s ↦ (h.isNondegenerateCriticalSubmanifold j).negativeNormalSpace hn
          g.toRiemannianMetric s) u)

include h hK

open scoped Classical in
/-- **The homology of a critical band of a Morse–Bott function.** Let the family `i j : S j → M`
exhibit `f` as a Morse–Bott function on a compact boundaryless manifold, and let `K` be a field.
Suppose that for each piece `S j` the negative normal bundle, relative to some smooth fibre metric,
has rank `r j` and a Thom class with coefficients in `K`. Let `a < c < b` be such that `c` is the
only critical value of `f` in `[a, b]`. Then `dim Hₙ({f ≤ b}, {f ≤ a}; K) = ∑ b_{n - r j}(S j; K)`,
the sum running over the pieces on the level `f = c` with `r j ≤ n`. If `c` is not a critical
value, the sum is empty. -/
theorem finrank_singularHomology_sublevelPair_eq_sum_of_isThomClass {a b c : ℝ} (hac : a < c)
    (hcb : c < b) (hcrit : ∀ x ∈ criticalPoints I f, f x ∈ Icc a b → f x = c) (n : ℕ) :
    finrank K ((sublevelPair f (hac.trans hcb).le).singularHomology (ModuleCat.of K K) n :
        ModuleCat K) =
      ∑ j with (∀ s, f (i j s) = c) ∧ r j ≤ n, bettiNumber K (S j) (n - r j) := by
  -- Fix the smooth fibre metrics, local frames and Thom classes given by `hK`.
  let _ (j : ι) := (i j).normalSpaceFiberBundle hn (hdim j)
  let _ (j : ι) := (i j).normalSpaceVectorBundle hn (hdim j)
  choose g hV u hu using hK
  let _ (j : ι) := subbundleTopology (P j) (F' := Fin (r j) → ℝ)
    ((h.isNondegenerateCriticalSubmanifold j).negativeNormalSpace hn (g j).toRiemannianMetric)
  let _ (j : ι) := (hV j).fiberBundle
  have (j : ι) := (hV j).vectorBundle
  -- By the Thom isomorphism, each Thom pair has the homology of its piece shifted by the index.
  refine h.finrank_singularHomology_sublevelPair_eq_sum_of_finrank_thomPair hn K hdim g hV
    (fun j ↦ bettiNumber K (S j)) (fun j p ↦ ?_) hac hcb hcrit n
  exact finrank_singularHomology_thomPair_of_isThomClass _ _ p _ (by rw [finrank_fin_fun]) (hu j)

/-- **A cut of the values of a Morse–Bott function.** When the negative normal bundles have Thom
classes with coefficients in `K`, the cut of `exists_cut_sum_finrank_sublevelPair_eq_sum` counts,
summing over the bands the dimensions of their homology, the shifted Betti numbers of every piece
once. -/
private theorem exists_cut_sum_finrank_sublevelPair :
    ∃ (s : ℕ → ℝ) (hs : Monotone s) (N : ℕ), (∀ x, s 0 < f x) ∧ (∀ x, f x ≤ s (N + 1)) ∧
      (∀ j ≤ N, IsRegularValue I 𝓘(ℝ) f (s (j + 1))) ∧
      ∀ n, ∑ j ∈ Finset.range (N + 1),
          finrank K ((sublevelPair f (hs j.le_succ)).singularHomology (ModuleCat.of K K) n :
            ModuleCat K) =
        ∑ p with r p ≤ n, bettiNumber K (S p) (n - r p) :=
  h.exists_cut_sum_finrank_sublevelPair_eq_sum K (fun j ↦ bettiNumber K (S j))
    (h.finrank_singularHomology_sublevelPair_eq_sum_of_isThomClass hn K hdim hK)

/-- **The weak Morse–Bott inequalities.** Let the family `i j : S j → M` exhibit `f` as a
Morse–Bott function on a compact boundaryless manifold, and let `K` be a field. Suppose that for
each piece `S j` the negative normal bundle, relative to some smooth fibre metric, has rank `r j`
and a Thom class with coefficients in `K`, as it does when it is oriented. Then
`bₙ(M; K) ≤ ∑ b_{n - r j}(S j; K)`, the sum running over the pieces with `r j ≤ n`. -/
theorem bettiNumber_le_sum_of_isThomClass (n : ℕ) :
    bettiNumber K M n ≤ ∑ p with r p ≤ n, bettiNumber K (S p) (n - r p) := by
  obtain ⟨s, hs, N, hs₀, hsN, hreg, hsum⟩ := h.exists_cut_sum_finrank_sublevelPair hn K hdim hK
  rw [bettiNumber_def, ← hsum]
  exact finrank_singularHomology_le_sum_sublevelPair_of_contMDiff (ModuleCat.of K K) h.contMDiff
    hs hs₀ hsN hreg n

/-- **The strong Morse–Bott inequalities.** Let the family `i j : S j → M` exhibit `f` as a
Morse–Bott function on a compact boundaryless manifold, and let `K` be a field. Suppose that for
each piece `S j` the negative normal bundle, relative to some smooth fibre metric, has rank `r j`
and a Thom class with coefficients in `K`, as it does when it is oriented. Write `bₖ = bₖ(M; K)`
and `cₖ = ∑ b_{k - r j}(S j; K)` over the pieces with `r j ≤ k`, the coefficient of `tᵏ` in the
Morse–Bott polynomial `∑ⱼ t^{r j} P_{S j}(t)`. Then `bₙ - bₙ₋₁ + ⋯ ± b₀ ≤ cₙ - cₙ₋₁ + ⋯ ± c₀`. -/
theorem sum_range_neg_one_pow_mul_bettiNumber_le_sum_of_isThomClass (n : ℕ) :
    ∑ k ∈ Finset.range (n + 1), (-1 : ℤ) ^ (n - k) * bettiNumber K M k ≤
      ∑ k ∈ Finset.range (n + 1), (-1 : ℤ) ^ (n - k) *
        ((∑ p with r p ≤ k, bettiNumber K (S p) (k - r p) : ℕ) : ℤ) := by
  obtain ⟨s, hs, N, hs₀, hsN, hreg, hsum⟩ := h.exists_cut_sum_finrank_sublevelPair hn K hdim hK
  simpa only [← bettiNumber_def, hsum] using
    sum_range_neg_one_pow_mul_finrank_singularHomology_le_sum_sublevelPair_of_contMDiff
      (ModuleCat.of K K) h.contMDiff hs hs₀ hsN hreg n

/-- **Euler's equality for a Morse–Bott function.** Under the hypotheses of
`TauCeti.IsMorseBottFamily.sum_range_neg_one_pow_mul_bettiNumber_le_sum_of_isThomClass`, for every
`n` at least the dimension of `M`, `∑ₖ₌₀ⁿ (-1)ᵏ bₖ = ∑ₖ₌₀ⁿ (-1)ᵏ cₖ`. -/
theorem sum_range_neg_one_pow_mul_bettiNumber_eq_sum_of_isThomClass {n : ℕ}
    (hdimn : finrank ℝ E ≤ n) :
    ∑ k ∈ Finset.range (n + 1), (-1 : ℤ) ^ k * bettiNumber K M k =
      ∑ k ∈ Finset.range (n + 1), (-1 : ℤ) ^ k *
        ((∑ p with r p ≤ k, bettiNumber K (S p) (k - r p) : ℕ) : ℤ) := by
  obtain ⟨s, hs, N, hs₀, hsN, hreg, hsum⟩ := h.exists_cut_sum_finrank_sublevelPair hn K hdim hK
  simpa only [← bettiNumber_def, hsum] using
    sum_range_neg_one_pow_mul_finrank_singularHomology_eq_sum_sublevelPair_of_contMDiff
      (ModuleCat.of K K) h.contMDiff hs hs₀ hsN hreg hdimn

/-- **The Morse–Bott polynomial identity.** Under the hypotheses of
`TauCeti.IsMorseBottFamily.sum_range_neg_one_pow_mul_bettiNumber_le_sum_of_isThomClass`, for every
`n` at least the dimension of `M`, `∑ₖ₌₀ⁿ cₖ tᵏ = ∑ₖ₌₀ⁿ bₖ tᵏ + (1 + t) Q(t)` for a polynomial `Q`
with natural number coefficients: the Morse–Bott polynomial `∑ⱼ t^{r j} P_{S j}(t)` exceeds the
Poincaré polynomial of `M` by `(1 + t) Q(t)`. -/
theorem exists_sum_range_monomial_sum_eq_add_mul_of_isThomClass {n : ℕ}
    (hdimn : finrank ℝ E ≤ n) :
    ∃ Q : ℕ[X], ∑ k ∈ Finset.range (n + 1),
        monomial k (∑ p with r p ≤ k, bettiNumber K (S p) (k - r p)) =
      ∑ k ∈ Finset.range (n + 1), monomial k (bettiNumber K M k) + (1 + Polynomial.X) * Q := by
  obtain ⟨s, hs, N, hs₀, hsN, hreg, hsum⟩ := h.exists_cut_sum_finrank_sublevelPair hn K hdim hK
  obtain ⟨Q, hQ, -⟩ := exists_sum_range_monomial_sum_sublevelPair_eq_add_mul_of_contMDiff
    (ModuleCat.of K K) h.contMDiff hs hs₀ hsN hreg hdimn
  simp only [← bettiNumber_def, hsum] at hQ
  exact ⟨Q, hQ⟩

end ThomClass

/-! #### Coefficients of characteristic two -/

section TwoEqZero

variable (h2 : (2 : K) = 0) (hr : ∀ j s, manifoldMorseIndex I f (i j s) = r j)

include h h2 hr

omit [SecondCountableTopology M] [Fintype ι] [∀ j, (J j).Boundaryless] in
/-- Over a field of characteristic two, the negative normal bundle of every piece of a Morse–Bott
family, of rank its index, has a Thom class relative to some smooth fibre metric. -/
private theorem exists_isThomClass_of_two_eq_zero (j : ι) :
    letI := (i j).normalSpaceFiberBundle hn (finrank_euclideanSpace_fin (𝕜 := ℝ)
      (n := finrank ℝ E - finrank ℝ (E' j)))
    letI := (i j).normalSpaceVectorBundle hn (finrank_euclideanSpace_fin (𝕜 := ℝ)
      (n := finrank ℝ E - finrank ℝ (E' j)))
    ∃ (g : ContMDiffRiemannianMetric (J j) ∞
        (EuclideanSpace ℝ (Fin (finrank ℝ E - finrank ℝ (E' j)))) fun s ↦ (i j).NormalSpace s hn)
      (hV : HasLocalSubbundleFrames (EuclideanSpace ℝ (Fin (finrank ℝ E - finrank ℝ (E' j))))
        (Fin (r j))
        ((h.isNondegenerateCriticalSubmanifold j).negativeNormalSpace hn g.toRiemannianMetric)),
      letI := subbundleTopology (EuclideanSpace ℝ (Fin (finrank ℝ E - finrank ℝ (E' j))))
        (F' := Fin (r j) → ℝ)
        ((h.isNondegenerateCriticalSubmanifold j).negativeNormalSpace hn g.toRiemannianMetric)
      letI := hV.fiberBundle
      ∃ u, IsThomClass (R := ModuleCat.of K K) (k := K) (M := ModuleCat.of K K) (Fin (r j) → ℝ)
        (fun s ↦ (h.isNondegenerateCriticalSubmanifold j).negativeNormalSpace hn
          g.toRiemannianMetric s) u :=
  have : CompactSpace (S j) := h.compactSpace_of_range_subset isCompact_univ (subset_univ _)
  have hN := h.isNondegenerateCriticalSubmanifold j
  hN.exists_isThomClass_negativeNormalSpace_of_two_eq_zero hn h.contMDiff _ (hr j) K h2

open scoped Classical in
/-- **The homology in characteristic two of a critical band of a Morse–Bott function.** Let the
family `i j : S j → M` exhibit `f` as a Morse–Bott function on a compact boundaryless manifold, the
piece `S j` having index `r j`, and let `K` be a field of characteristic two, such as `ZMod 2`. Let
`a < c < b` be such that `c` is the only critical value of `f` in `[a, b]`. Then
`dim Hₙ({f ≤ b}, {f ≤ a}; K) = ∑ b_{n - r j}(S j; K)`, the sum running over the pieces on the
level `f = c` of index at most `n`. If `c` is not a critical value, the sum is empty. -/
theorem finrank_singularHomology_sublevelPair_eq_sum {a b c : ℝ} (hac : a < c) (hcb : c < b)
    (hcrit : ∀ x ∈ criticalPoints I f, f x ∈ Icc a b → f x = c) (n : ℕ) :
    finrank K ((sublevelPair f (hac.trans hcb).le).singularHomology (ModuleCat.of K K) n :
        ModuleCat K) =
      ∑ j with (∀ s, f (i j s) = c) ∧ r j ≤ n, bettiNumber K (S j) (n - r j) :=
  h.finrank_singularHomology_sublevelPair_eq_sum_of_isThomClass (by simp) K
    (fun _ ↦ finrank_euclideanSpace_fin) (h.exists_isThomClass_of_two_eq_zero _ K h2 hr) hac
    hcb hcrit n

/-- **The weak Morse–Bott inequalities in characteristic two.** Let the family `i j : S j → M`
exhibit `f` as a Morse–Bott function on a compact boundaryless manifold, the piece `S j` having
index `r j`, and let `K` be a field of characteristic two, such as `ZMod 2`. Then
`bₙ(M; K) ≤ ∑ b_{n - r j}(S j; K)`, the sum running over the pieces of index at most `n`. -/
theorem bettiNumber_le_sum (n : ℕ) :
    bettiNumber K M n ≤ ∑ p with r p ≤ n, bettiNumber K (S p) (n - r p) :=
  h.bettiNumber_le_sum_of_isThomClass (by simp) K (fun _ ↦ finrank_euclideanSpace_fin)
    (h.exists_isThomClass_of_two_eq_zero _ K h2 hr) n

/-- **The strong Morse–Bott inequalities in characteristic two.** Let the family `i j : S j → M`
exhibit `f` as a Morse–Bott function on a compact boundaryless manifold, the piece `S j` having
index `r j`, and let `K` be a field of characteristic two, such as `ZMod 2`. Write
`bₖ = bₖ(M; K)` and `cₖ = ∑ b_{k - r j}(S j; K)` over the pieces of index at most `k`, the
coefficient of `tᵏ` in the Morse–Bott polynomial `∑ⱼ t^{r j} P_{S j}(t)`. Then
`bₙ - bₙ₋₁ + ⋯ ± b₀ ≤ cₙ - cₙ₋₁ + ⋯ ± c₀`. -/
theorem sum_range_neg_one_pow_mul_bettiNumber_le_sum (n : ℕ) :
    ∑ k ∈ Finset.range (n + 1), (-1 : ℤ) ^ (n - k) * bettiNumber K M k ≤
      ∑ k ∈ Finset.range (n + 1), (-1 : ℤ) ^ (n - k) *
        ((∑ p with r p ≤ k, bettiNumber K (S p) (k - r p) : ℕ) : ℤ) :=
  h.sum_range_neg_one_pow_mul_bettiNumber_le_sum_of_isThomClass (by simp) K
    (fun _ ↦ finrank_euclideanSpace_fin) (h.exists_isThomClass_of_two_eq_zero _ K h2 hr) n

/-- **Euler's equality for a Morse–Bott function in characteristic two.** Under the hypotheses of
`TauCeti.IsMorseBottFamily.sum_range_neg_one_pow_mul_bettiNumber_le_sum`, for every `n` at least the
dimension of `M`, `∑ₖ₌₀ⁿ (-1)ᵏ bₖ = ∑ₖ₌₀ⁿ (-1)ᵏ cₖ`. -/
theorem sum_range_neg_one_pow_mul_bettiNumber_eq_sum {n : ℕ} (hdimn : finrank ℝ E ≤ n) :
    ∑ k ∈ Finset.range (n + 1), (-1 : ℤ) ^ k * bettiNumber K M k =
      ∑ k ∈ Finset.range (n + 1), (-1 : ℤ) ^ k *
        ((∑ p with r p ≤ k, bettiNumber K (S p) (k - r p) : ℕ) : ℤ) :=
  h.sum_range_neg_one_pow_mul_bettiNumber_eq_sum_of_isThomClass (by simp) K
    (fun _ ↦ finrank_euclideanSpace_fin) (h.exists_isThomClass_of_two_eq_zero _ K h2 hr) hdimn

/-- **The Morse–Bott polynomial identity in characteristic two.** Under the hypotheses of
`TauCeti.IsMorseBottFamily.sum_range_neg_one_pow_mul_bettiNumber_le_sum`, for every `n` at least the
dimension of `M`, `∑ₖ₌₀ⁿ cₖ tᵏ = ∑ₖ₌₀ⁿ bₖ tᵏ + (1 + t) Q(t)` for a polynomial `Q` with natural
number coefficients: the Morse–Bott polynomial `∑ⱼ t^{r j} P_{S j}(t)` exceeds the Poincaré
polynomial of `M` by `(1 + t) Q(t)`. -/
theorem exists_sum_range_monomial_sum_eq_add_mul {n : ℕ} (hdimn : finrank ℝ E ≤ n) :
    ∃ Q : ℕ[X], ∑ k ∈ Finset.range (n + 1),
        monomial k (∑ p with r p ≤ k, bettiNumber K (S p) (k - r p)) =
      ∑ k ∈ Finset.range (n + 1), monomial k (bettiNumber K M k) + (1 + Polynomial.X) * Q :=
  h.exists_sum_range_monomial_sum_eq_add_mul_of_isThomClass (by simp) K
    (fun _ ↦ finrank_euclideanSpace_fin) (h.exists_isThomClass_of_two_eq_zero _ K h2 hr) hdimn

/-- **The lacunary principle for a Morse–Bott function in characteristic two.** Under the
hypotheses of `TauCeti.IsMorseBottFamily.sum_range_neg_one_pow_mul_bettiNumber_le_sum`, write
`cₖ = ∑ b_{k - r j}(S j; K)` over the pieces of index at most `k`. If of any two consecutive counts
`cₖ` and `cₖ₊₁` one vanishes, then `bₙ(M; K) = cₙ` for every `n`: the Morse–Bott function is
perfect over `K`. -/
theorem bettiNumber_eq_sum_of_forall_eq_zero_or_eq_zero
    (hlac : ∀ k, ∑ p with r p ≤ k, bettiNumber K (S p) (k - r p) = 0 ∨
      ∑ p with r p ≤ k + 1, bettiNumber K (S p) (k + 1 - r p) = 0) (n : ℕ) :
    bettiNumber K M n = ∑ p with r p ≤ n, bettiNumber K (S p) (n - r p) :=
  congrFun (eq_of_forall_sum_range_neg_one_pow_mul_le
    (h.sum_range_neg_one_pow_mul_bettiNumber_le_sum K h2 hr) hlac) n

end TwoEqZero

/-! #### Oriented negative normal bundles -/

section Orientation

variable (hdim : ∀ j, finrank ℝ (P j) = finrank ℝ E - finrank ℝ (E' j))
  (g : letI : ∀ j, FiberBundle (P j) fun s ↦ (i j).NormalSpace s hn :=
      fun j ↦ (i j).normalSpaceFiberBundle hn (hdim j)
    letI : ∀ j, VectorBundle ℝ (P j) fun s ↦ (i j).NormalSpace s hn :=
      fun j ↦ (i j).normalSpaceVectorBundle hn (hdim j)
    ∀ j, ContMDiffRiemannianMetric (J j) ∞ (P j) fun s ↦ (i j).NormalSpace s hn)
  (hr : ∀ j s, manifoldMorseIndex I f (i j s) = r j)
  (o : ∀ j, (h.isNondegenerateCriticalSubmanifold j).NegativeNormalBundleOrientation hn
    h.contMDiff (hdim j) (g j) (hr j))

include h o

omit [T2Space M] [SecondCountableTopology M] [CompactSpace M] [Fintype ι]
  [∀ j, (J j).Boundaryless] in
/-- When the negative normal bundles of the pieces relative to the metrics `g j` are oriented, they
have Thom classes with coefficients in every field `K`. -/
private theorem exists_isThomClass_of_orientation (j : ι) :
    letI := (i j).normalSpaceFiberBundle hn (hdim j)
    letI := (i j).normalSpaceVectorBundle hn (hdim j)
    ∃ (g' : ContMDiffRiemannianMetric (J j) ∞ (P j) fun s ↦ (i j).NormalSpace s hn)
      (hV : HasLocalSubbundleFrames (P j) (Fin (r j))
        ((h.isNondegenerateCriticalSubmanifold j).negativeNormalSpace hn g'.toRiemannianMetric)),
      letI := subbundleTopology (P j) (F' := Fin (r j) → ℝ)
        ((h.isNondegenerateCriticalSubmanifold j).negativeNormalSpace hn g'.toRiemannianMetric)
      letI := hV.fiberBundle
      ∃ u, IsThomClass (R := ModuleCat.of K K) (k := K) (M := ModuleCat.of K K) (Fin (r j) → ℝ)
        (fun s ↦ (h.isNondegenerateCriticalSubmanifold j).negativeNormalSpace hn
          g'.toRiemannianMetric s) u :=
  have hN := h.isNondegenerateCriticalSubmanifold j
  ⟨g j, _, (hN.hasNegativeNormalThomClass_iff hn h.contMDiff (hdim j) (g j) (hr j) K).1
    (hN.hasNegativeNormalThomClass_of_orientation hn h.contMDiff (hdim j) (g j) (hr j) (o j) K)⟩

open scoped Classical in
/-- **The homology of a critical band of a Morse–Bott function with oriented negative normal
bundles.** Let the family `i j : S j → M` exhibit `f` as a Morse–Bott function on a compact
boundaryless manifold, the piece `S j` having index `r j`, let `g j` be smooth fibre metrics on the
normal bundles of the pieces, and suppose that the negative normal bundle of every piece relative
to `g j` is oriented. Let `K` be any field, such as `ℚ`. Let `a < c < b` be such that `c` is the
only critical value of `f` in `[a, b]`. Then `dim Hₙ({f ≤ b}, {f ≤ a}; K) = ∑ b_{n - r j}(S j; K)`,
the sum running over the pieces on the level `f = c` of index at most `n`. -/
theorem finrank_singularHomology_sublevelPair_eq_sum_of_orientation {a b c : ℝ} (hac : a < c)
    (hcb : c < b) (hcrit : ∀ x ∈ criticalPoints I f, f x ∈ Icc a b → f x = c) (n : ℕ) :
    finrank K ((sublevelPair f (hac.trans hcb).le).singularHomology (ModuleCat.of K K) n :
        ModuleCat K) =
      ∑ j with (∀ s, f (i j s) = c) ∧ r j ≤ n, bettiNumber K (S j) (n - r j) :=
  h.finrank_singularHomology_sublevelPair_eq_sum_of_isThomClass hn K hdim
    (h.exists_isThomClass_of_orientation hn K hdim g hr o) hac hcb hcrit n

/-- **The weak Morse–Bott inequalities with oriented negative normal bundles.** Let the family
`i j : S j → M` exhibit `f` as a Morse–Bott function on a compact boundaryless manifold, the piece
`S j` having index `r j`, let `g j` be smooth fibre metrics on the normal bundles of the pieces,
and suppose that the negative normal bundle of every piece relative to `g j` is oriented. Then for
every field `K`, such as `ℚ`, `bₙ(M; K) ≤ ∑ b_{n - r j}(S j; K)`, the sum running over the pieces
of index at most `n`. -/
theorem bettiNumber_le_sum_of_orientation (n : ℕ) :
    bettiNumber K M n ≤ ∑ p with r p ≤ n, bettiNumber K (S p) (n - r p) :=
  h.bettiNumber_le_sum_of_isThomClass hn K hdim
    (h.exists_isThomClass_of_orientation hn K hdim g hr o) n

/-- **The strong Morse–Bott inequalities with oriented negative normal bundles.** Let the family
`i j : S j → M` exhibit `f` as a Morse–Bott function on a compact boundaryless manifold, the piece
`S j` having index `r j`, let `g j` be smooth fibre metrics on the normal bundles of the pieces,
and suppose that the negative normal bundle of every piece relative to `g j` is oriented. Let `K`
be any field, such as `ℚ`. Write `bₖ = bₖ(M; K)` and `cₖ = ∑ b_{k - r j}(S j; K)` over the pieces
of index at most `k`, the coefficient of `tᵏ` in the Morse–Bott polynomial
`∑ⱼ t^{r j} P_{S j}(t)`. Then `bₙ - bₙ₋₁ + ⋯ ± b₀ ≤ cₙ - cₙ₋₁ + ⋯ ± c₀`. -/
theorem sum_range_neg_one_pow_mul_bettiNumber_le_sum_of_orientation (n : ℕ) :
    ∑ k ∈ Finset.range (n + 1), (-1 : ℤ) ^ (n - k) * bettiNumber K M k ≤
      ∑ k ∈ Finset.range (n + 1), (-1 : ℤ) ^ (n - k) *
        ((∑ p with r p ≤ k, bettiNumber K (S p) (k - r p) : ℕ) : ℤ) :=
  h.sum_range_neg_one_pow_mul_bettiNumber_le_sum_of_isThomClass hn K hdim
    (h.exists_isThomClass_of_orientation hn K hdim g hr o) n

/-- **Euler's equality for a Morse–Bott function with oriented negative normal bundles.** Under the
hypotheses of
`TauCeti.IsMorseBottFamily.sum_range_neg_one_pow_mul_bettiNumber_le_sum_of_orientation`, for every
`n` at least the dimension of `M`, `∑ₖ₌₀ⁿ (-1)ᵏ bₖ = ∑ₖ₌₀ⁿ (-1)ᵏ cₖ`. -/
theorem sum_range_neg_one_pow_mul_bettiNumber_eq_sum_of_orientation {n : ℕ}
    (hdimn : finrank ℝ E ≤ n) :
    ∑ k ∈ Finset.range (n + 1), (-1 : ℤ) ^ k * bettiNumber K M k =
      ∑ k ∈ Finset.range (n + 1), (-1 : ℤ) ^ k *
        ((∑ p with r p ≤ k, bettiNumber K (S p) (k - r p) : ℕ) : ℤ) :=
  h.sum_range_neg_one_pow_mul_bettiNumber_eq_sum_of_isThomClass hn K hdim
    (h.exists_isThomClass_of_orientation hn K hdim g hr o) hdimn

/-- **The Morse–Bott polynomial identity with oriented negative normal bundles.** Under the
hypotheses of
`TauCeti.IsMorseBottFamily.sum_range_neg_one_pow_mul_bettiNumber_le_sum_of_orientation`, for every
`n` at least the dimension of `M`, `∑ₖ₌₀ⁿ cₖ tᵏ = ∑ₖ₌₀ⁿ bₖ tᵏ + (1 + t) Q(t)` for a polynomial `Q`
with natural number coefficients: over every field, the Morse–Bott polynomial
`∑ⱼ t^{r j} P_{S j}(t)` exceeds the Poincaré polynomial of `M` by `(1 + t) Q(t)`. -/
theorem exists_sum_range_monomial_sum_eq_add_mul_of_orientation {n : ℕ}
    (hdimn : finrank ℝ E ≤ n) :
    ∃ Q : ℕ[X], ∑ k ∈ Finset.range (n + 1),
        monomial k (∑ p with r p ≤ k, bettiNumber K (S p) (k - r p)) =
      ∑ k ∈ Finset.range (n + 1), monomial k (bettiNumber K M k) + (1 + Polynomial.X) * Q :=
  h.exists_sum_range_monomial_sum_eq_add_mul_of_isThomClass hn K hdim
    (h.exists_isThomClass_of_orientation hn K hdim g hr o) hdimn

end Orientation

/-! #### Simply connected critical submanifolds -/

section SimplyConnected

variable [∀ j, SimplyConnectedSpace (S j)] (hr : ∀ j s, manifoldMorseIndex I f (i j s) = r j)

include h hr

omit [SecondCountableTopology M] [Fintype ι] [∀ j, (J j).Boundaryless] in
/-- The negative normal bundle of a simply connected piece of a Morse–Bott family, of rank its
index, has a Thom class with coefficients in every field relative to some smooth fibre metric. -/
private theorem exists_isThomClass_of_simplyConnectedSpace (j : ι) :
    letI := (i j).normalSpaceFiberBundle hn (finrank_euclideanSpace_fin (𝕜 := ℝ)
      (n := finrank ℝ E - finrank ℝ (E' j)))
    letI := (i j).normalSpaceVectorBundle hn (finrank_euclideanSpace_fin (𝕜 := ℝ)
      (n := finrank ℝ E - finrank ℝ (E' j)))
    ∃ (g : ContMDiffRiemannianMetric (J j) ∞
        (EuclideanSpace ℝ (Fin (finrank ℝ E - finrank ℝ (E' j)))) fun s ↦ (i j).NormalSpace s hn)
      (hV : HasLocalSubbundleFrames (EuclideanSpace ℝ (Fin (finrank ℝ E - finrank ℝ (E' j))))
        (Fin (r j))
        ((h.isNondegenerateCriticalSubmanifold j).negativeNormalSpace hn g.toRiemannianMetric)),
      letI := subbundleTopology (EuclideanSpace ℝ (Fin (finrank ℝ E - finrank ℝ (E' j))))
        (F' := Fin (r j) → ℝ)
        ((h.isNondegenerateCriticalSubmanifold j).negativeNormalSpace hn g.toRiemannianMetric)
      letI := hV.fiberBundle
      ∃ u, IsThomClass (R := ModuleCat.of K K) (k := K) (M := ModuleCat.of K K) (Fin (r j) → ℝ)
        (fun s ↦ (h.isNondegenerateCriticalSubmanifold j).negativeNormalSpace hn
          g.toRiemannianMetric s) u := by
  have : CompactSpace (S j) := h.compactSpace_of_range_subset isCompact_univ (subset_univ _)
  have hN := h.isNondegenerateCriticalSubmanifold j
  have hdim := finrank_euclideanSpace_fin (𝕜 := ℝ) (n := finrank ℝ E - finrank ℝ (E' j))
  let := (i j).normalSpaceFiberBundle hn hdim
  let := (i j).normalSpaceVectorBundle hn hdim
  obtain ⟨g⟩ := (i j).nonempty_contMDiffRiemannianMetric_normalSpace hn hdim
  exact ⟨g, _, (hN.hasNegativeNormalThomClass_iff hn h.contMDiff hdim g (hr j) K).1
    (hN.hasNegativeNormalThomClass_of_simplyConnectedSpace hn h.contMDiff hdim g (hr j) K)⟩

open scoped Classical in
/-- **The homology of a critical band of a Morse–Bott function with simply connected critical
submanifolds.** Let the family `i j : S j → M` exhibit `f` as a Morse–Bott function on a compact
boundaryless manifold, the piece `S j` being simply connected of index `r j`, and let `K` be any
field, such as `ℚ`. Let `a < c < b` be such that `c` is the only critical value of `f` in `[a, b]`.
Then `dim Hₙ({f ≤ b}, {f ≤ a}; K) = ∑ b_{n - r j}(S j; K)`, the sum running over the pieces on the
level `f = c` of index at most `n`. -/
theorem finrank_singularHomology_sublevelPair_eq_sum_of_simplyConnectedSpace {a b c : ℝ}
    (hac : a < c) (hcb : c < b) (hcrit : ∀ x ∈ criticalPoints I f, f x ∈ Icc a b → f x = c)
    (n : ℕ) :
    finrank K ((sublevelPair f (hac.trans hcb).le).singularHomology (ModuleCat.of K K) n :
        ModuleCat K) =
      ∑ j with (∀ s, f (i j s) = c) ∧ r j ≤ n, bettiNumber K (S j) (n - r j) :=
  h.finrank_singularHomology_sublevelPair_eq_sum_of_isThomClass (by simp) K
    (fun _ ↦ finrank_euclideanSpace_fin) (h.exists_isThomClass_of_simplyConnectedSpace _ K hr)
    hac hcb hcrit n

/-- **The weak Morse–Bott inequalities with simply connected critical submanifolds.** Let the
family `i j : S j → M` exhibit `f` as a Morse–Bott function on a compact boundaryless manifold, the
piece `S j` being simply connected of index `r j`. Then for every field `K`, such as `ℚ`,
`bₙ(M; K) ≤ ∑ b_{n - r j}(S j; K)`, the sum running over the pieces of index at most `n`. -/
theorem bettiNumber_le_sum_of_simplyConnectedSpace (n : ℕ) :
    bettiNumber K M n ≤ ∑ p with r p ≤ n, bettiNumber K (S p) (n - r p) :=
  h.bettiNumber_le_sum_of_isThomClass (by simp) K (fun _ ↦ finrank_euclideanSpace_fin)
    (h.exists_isThomClass_of_simplyConnectedSpace _ K hr) n

/-- **The strong Morse–Bott inequalities with simply connected critical submanifolds.** Let the
family `i j : S j → M` exhibit `f` as a Morse–Bott function on a compact boundaryless manifold, the
piece `S j` being simply connected of index `r j`, and let `K` be any field, such as `ℚ`. Write
`bₖ = bₖ(M; K)` and `cₖ = ∑ b_{k - r j}(S j; K)` over the pieces of index at most `k`, the
coefficient of `tᵏ` in the Morse–Bott polynomial `∑ⱼ t^{r j} P_{S j}(t)`. Then
`bₙ - bₙ₋₁ + ⋯ ± b₀ ≤ cₙ - cₙ₋₁ + ⋯ ± c₀`. -/
theorem sum_range_neg_one_pow_mul_bettiNumber_le_sum_of_simplyConnectedSpace (n : ℕ) :
    ∑ k ∈ Finset.range (n + 1), (-1 : ℤ) ^ (n - k) * bettiNumber K M k ≤
      ∑ k ∈ Finset.range (n + 1), (-1 : ℤ) ^ (n - k) *
        ((∑ p with r p ≤ k, bettiNumber K (S p) (k - r p) : ℕ) : ℤ) :=
  h.sum_range_neg_one_pow_mul_bettiNumber_le_sum_of_isThomClass (by simp) K
    (fun _ ↦ finrank_euclideanSpace_fin) (h.exists_isThomClass_of_simplyConnectedSpace _ K hr) n

/-- **Euler's equality for a Morse–Bott function with simply connected critical submanifolds.**
Under the hypotheses of
`TauCeti.IsMorseBottFamily.sum_range_neg_one_pow_mul_bettiNumber_le_sum_of_simplyConnectedSpace`,
for every `n` at least the dimension of `M`, `∑ₖ₌₀ⁿ (-1)ᵏ bₖ = ∑ₖ₌₀ⁿ (-1)ᵏ cₖ`. -/
theorem sum_range_neg_one_pow_mul_bettiNumber_eq_sum_of_simplyConnectedSpace {n : ℕ}
    (hdimn : finrank ℝ E ≤ n) :
    ∑ k ∈ Finset.range (n + 1), (-1 : ℤ) ^ k * bettiNumber K M k =
      ∑ k ∈ Finset.range (n + 1), (-1 : ℤ) ^ k *
        ((∑ p with r p ≤ k, bettiNumber K (S p) (k - r p) : ℕ) : ℤ) :=
  h.sum_range_neg_one_pow_mul_bettiNumber_eq_sum_of_isThomClass (by simp) K
    (fun _ ↦ finrank_euclideanSpace_fin) (h.exists_isThomClass_of_simplyConnectedSpace _ K hr)
    hdimn

/-- **The Morse–Bott polynomial identity with simply connected critical submanifolds.** Under the
hypotheses of
`TauCeti.IsMorseBottFamily.sum_range_neg_one_pow_mul_bettiNumber_le_sum_of_simplyConnectedSpace`,
for every `n` at least the dimension of `M`, `∑ₖ₌₀ⁿ cₖ tᵏ = ∑ₖ₌₀ⁿ bₖ tᵏ + (1 + t) Q(t)` for a
polynomial `Q` with natural number coefficients: over every field, the Morse–Bott polynomial
`∑ⱼ t^{r j} P_{S j}(t)` exceeds the Poincaré polynomial of `M` by `(1 + t) Q(t)`. -/
theorem exists_sum_range_monomial_sum_eq_add_mul_of_simplyConnectedSpace {n : ℕ}
    (hdimn : finrank ℝ E ≤ n) :
    ∃ Q : ℕ[X], ∑ k ∈ Finset.range (n + 1),
        monomial k (∑ p with r p ≤ k, bettiNumber K (S p) (k - r p)) =
      ∑ k ∈ Finset.range (n + 1), monomial k (bettiNumber K M k) + (1 + Polynomial.X) * Q :=
  h.exists_sum_range_monomial_sum_eq_add_mul_of_isThomClass (by simp) K
    (fun _ ↦ finrank_euclideanSpace_fin) (h.exists_isThomClass_of_simplyConnectedSpace _ K hr)
    hdimn

end SimplyConnected

end IsMorseBottFamily

end Level

end TauCeti
