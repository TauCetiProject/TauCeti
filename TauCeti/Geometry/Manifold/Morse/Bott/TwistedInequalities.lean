/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Morse.Bott.Count
public import TauCeti.Geometry.Manifold.Morse.Bott.Inequalities
public import TauCeti.Topology.VectorBundle.Orientation.BettiNumber
public import TauCeti.Topology.VectorBundle.Thom.TwistedHomology
import TauCeti.Geometry.Manifold.Topology

/-!
# The Morse–Bott inequalities with coefficients twisted by the negative orientation

Let `f` be a Morse–Bott function on a compact boundaryless manifold `M`, exhibited by a family
`i j : S j → M` of critical submanifolds (`TauCeti.IsMorseBottFamily`), and let `g j` be smooth
fibre metrics on their normal bundles. The negative normal spaces of `S j` relative to `g j` form
a real vector bundle `ν⁻ j` of rank `r j`, the index of the piece, with orientation local system
`o(ν⁻ j)` (`TauCeti.VectorBundleOrientationCover.signLocalSystem`). Let `K` be any field. Write
`bₙ = dim Hₙ(M; K)` and

`cₙ = ∑ⱼ dim H_{n - r j}(S j; o(ν⁻ j) ⊗ K)`,

the sum running over the pieces of index `r j ≤ n`. This file proves the **Morse–Bott
inequalities** for `b` and `c`: the weak inequalities `bₙ ≤ cₙ`, the strong inequalities
`bₙ - bₙ₋₁ + ⋯ ± b₀ ≤ cₙ - cₙ₋₁ + ⋯ ± c₀`, Euler's equality in degrees at least `dim M`, the
polynomial identity `∑ₙ cₙ tⁿ = ∑ₙ bₙ tⁿ + (1 + t) Q(t)` with `Q` having natural number
coefficients, and the lacunary principle: if no two consecutive `cₙ` are both nonzero, then
`bₙ = cₙ` for every `n`. No orientation of the negative normal bundles is assumed: the contribution
of a piece is its homology twisted by the orientation of its negative normal bundle, which is its
ordinary homology when that bundle is orientable. For instance, on the real projective plane the
function `[x : y : z] ↦ (x² + y²) / (x² + y² + z²)` has a minimum at `[0 : 0 : 1]` and a critical
circle of index `1` on which it is maximal, whose negative normal bundle is a Möbius line. Over `ℚ`
the circle contributes nothing, as its homology with coefficients in the orientation system of the
Möbius line vanishes, so `c = (1, 0, 0)` is the sequence of Betti numbers of the plane over `ℚ`;
its untwisted homology would contribute `t + t²`. Over a field of characteristic two, such as
`𝔽₂`, the twist disappears: the twisted Betti numbers are the ordinary ones
(`TauCeti.IsMorseBottFamily.twistedBettiNumber_eq_bettiNumber_of_two_eq_zero`), and the
inequalities are those of `TauCeti.Geometry.Manifold.Morse.Bott.Inequalities`.

The proof is that of the mod `2` inequalities. The homology of a band with one critical value `c`
is the direct sum of the homologies of the Thom pairs of the negative normal bundles of the pieces
on the level `c`
(`TauCeti.IsMorseBottFamily.nonempty_singularHomology_sublevelPair_iso_sigma_thomPair`), so its
dimension is the sum of their contributions
(`TauCeti.IsMorseBottFamily.finrank_singularHomology_sublevelPair_eq_sum_of_finrank_thomPair`, here
`TauCeti.IsMorseBottFamily.finrank_singularHomology_sublevelPair_eq_sum_twistedBettiNumber`).
Over a field, the Thom pair of a bundle of rank `r` has the twisted homology of its base shifted by
`r`. A field either has characteristic two or has `2` invertible. In the first case the twist
disappears and the mod `2` Thom isomorphism applies
(`TauCeti.finrank_singularHomology_thomPair_of_two_eq_zero`); in the second the twisted Thom
isomorphism does
(`VectorBundleOrientationCover.finrank_singularHomology_thomPair_eq_finrank_twistedHomology`).
The inequalities of the filtration of `M` by sublevels at a cut of the values of `f`
(`TauCeti.IsMorseBottFamily.exists_cut_sum_finrank_sublevelPair_eq_sum`) then give the result.

The twisted counts `cₙ` reduce to the untwisted ones where the twist is invisible. The twisted Betti
numbers of a piece are its ordinary Betti numbers over `K` when its negative normal bundle is
oriented, when the piece is simply connected, and when `2 = 0` in `K`
(`twistedBettiNumber_eq_bettiNumber_of_orientation`,
`twistedBettiNumber_eq_bettiNumber_of_simplyConnectedSpace` and
`twistedBettiNumber_eq_bettiNumber_of_two_eq_zero`). So with oriented negative normal bundles
`cₙ` is the Morse–Bott count `∑ⱼ b_{n - r j}(S j; K)`
(`TauCeti.IsMorseBottFamily.morseBottCount`), and the inequalities here are those of
`TauCeti.Geometry.Manifold.Morse.Bott.Inequalities` for oriented negative normal bundles. For a
Morse function every piece is a point, so `cₙ` is the number of critical points of index `n`
(`sum_twistedBettiNumber_eq_criticalCount`) and the inequalities are the Morse inequalities.
Otherwise the twist is visible already in degree zero: if `2 ≠ 0` in `K`, the zeroth twisted Betti
number of a piece is `1` or `0` according as its negative normal bundle is orientable or not
(`twistedBettiNumber_zero`).

The hypothesis `hV` gives the negative normal spaces local frames of size `r j`, which makes them a
vector bundle of rank `r j`; such frames exist exactly when `r j` is the Morse index of `f` along
`S j` (in the namespace `TauCeti.SmoothEmbedding`,
`IsNondegenerateCriticalSubmanifold.hasLocalContMDiffSubbundleFrames_negativeNormalSpace`).
The manifolds and the coefficient field here live in `Type`, as in the untwisted inequalities
(`TauCeti.Geometry.Manifold.Morse.Bott.Inequalities`) and the Thom classes of oriented negative
normal bundles (`TauCeti.Geometry.Manifold.Morse.Bott.Thom.Class`) that this file compares with.

## Main results

In the namespace `TauCeti.IsMorseBottFamily`:

* `twistedBettiNumber`: the twisted Betti numbers `dim Hₖ(S j; o(ν⁻ j) ⊗ K)` of the pieces.
* `finrank_singularHomology_sublevelPair_eq_sum_twistedBettiNumber`: the dimension of the
  homology of a band with a single critical value.
* `bettiNumber_le_sum_twistedBettiNumber`,
  `sum_range_neg_one_pow_mul_bettiNumber_le_sum_twistedBettiNumber`,
  `sum_range_neg_one_pow_mul_bettiNumber_eq_sum_twistedBettiNumber` and
  `exists_sum_range_monomial_sum_twistedBettiNumber_eq_add_mul`: the weak and strong
  Morse–Bott inequalities, Euler's equality and the Morse–Bott polynomial identity with
  coefficients twisted by the orientation local systems of the negative normal bundles, over every
  field.
* `twistedBettiNumber_eq_bettiNumber_of_orientation`,
  `twistedBettiNumber_eq_bettiNumber_of_simplyConnectedSpace` and
  `twistedBettiNumber_eq_bettiNumber_of_two_eq_zero`: the twisted Betti numbers of a piece are its
  ordinary Betti numbers when its negative normal bundle is oriented, when it is simply connected,
  and in characteristic two.
* `twistedBettiNumber_zero`: away from characteristic two, the zeroth twisted Betti number of a
  piece detects the orientability of its negative normal bundle.
* `sum_twistedBettiNumber_eq_morseBottCount_of_orientation` and
  `sum_twistedBettiNumber_eq_criticalCount`: with oriented negative normal bundles the twisted
  counts are the Morse–Bott counts, and for a Morse function they are the critical counts.
* `bettiNumber_eq_sum_twistedBettiNumber_of_forall_eq_zero_or_eq_zero`: the lacunary principle
  with twisted coefficients.

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
open TauCeti.VectorBundleOrientationCover TauCeti.LocalCoefficientSystem
open Polynomial (monomial)
open scoped ContDiff Manifold Polynomial

namespace TauCeti.IsMorseBottFamily

variable {E : Type} {H : Type*} {M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  [SecondCountableTopology M] [CompactSpace M]
  {ι : Type*} [Fintype ι] {E' H' P : ι → Type*} {S : ι → Type}
  [∀ j, NormedAddCommGroup (E' j)] [∀ j, NormedSpace ℝ (E' j)] [∀ j, FiniteDimensional ℝ (E' j)]
  [∀ j, TopologicalSpace (H' j)] {J : ∀ j, ModelWithCorners ℝ (E' j) (H' j)}
  [∀ j, (J j).Boundaryless] [∀ j, TopologicalSpace (S j)] [∀ j, ChartedSpace (H' j) (S j)]
  [∀ j, IsManifold (J j) ∞ (S j)] [∀ j, NormedAddCommGroup (P j)] [∀ j, NormedSpace ℝ (P j)]
  [∀ j, FiniteDimensional ℝ (P j)] {f : M → ℝ} {i : ∀ j, SmoothEmbedding (J j) I ∞ (S j) M}
  (hn : (∞ : ℕ∞ω) ≠ 0) (h : IsMorseBottFamily i f)
  (hdim : ∀ j, finrank ℝ (P j) = finrank ℝ E - finrank ℝ (E' j))
  (g : letI : ∀ j, FiberBundle (P j) fun s ↦ (i j).isImmersion.NormalSpace s hn :=
      fun j ↦ (i j).normalSpaceFiberBundle hn (hdim j)
    letI : ∀ j, VectorBundle ℝ (P j) fun s ↦ (i j).isImmersion.NormalSpace s hn :=
      fun j ↦ (i j).normalSpaceVectorBundle hn (hdim j)
    ∀ j, ContMDiffRiemannianMetric (J j) ∞ (P j) fun s ↦ (i j).isImmersion.NormalSpace s hn)
  {r : ι → ℕ}
  (hV : letI : ∀ j, FiberBundle (P j) fun s ↦ (i j).isImmersion.NormalSpace s hn :=
      fun j ↦ (i j).normalSpaceFiberBundle hn (hdim j)
    letI : ∀ j, VectorBundle ℝ (P j) fun s ↦ (i j).isImmersion.NormalSpace s hn :=
      fun j ↦ (i j).normalSpaceVectorBundle hn (hdim j)
    ∀ j, HasLocalSubbundleFrames (P j) (Fin (r j))
      ((h.isNondegenerateCriticalSubmanifold j).negativeNormalSpace hn (g j).toRiemannianMetric))
  (K : Type) [Field K]

include hV

omit [T2Space M] [SecondCountableTopology M] [CompactSpace M] [Fintype ι]
  [∀ j, (J j).Boundaryless] in
/-- **The twisted Betti numbers of a piece of a Morse–Bott function.** Let the family
`i j : S j → M` exhibit `f` as a Morse–Bott function, let `g j` be smooth fibre metrics on the
normal bundles of the pieces, and let the negative normal spaces relative to `g j` have local frames
of size `r j`, so that they form the negative normal bundle `ν⁻ j` of rank `r j`. This is
`dim Hₖ(S j; o(ν⁻ j) ⊗ K)`, the dimension of the homology of `S j` with coefficients in the
orientation local system `o(ν⁻ j)` of `ν⁻ j`. -/
def twistedBettiNumber (j : ι) (k : ℕ) : ℕ :=
  letI : ∀ j, FiberBundle (P j) fun s ↦ (i j).isImmersion.NormalSpace s hn :=
    fun j ↦ (i j).normalSpaceFiberBundle hn (hdim j)
  letI : ∀ j, VectorBundle ℝ (P j) fun s ↦ (i j).isImmersion.NormalSpace s hn :=
    fun j ↦ (i j).normalSpaceVectorBundle hn (hdim j)
  letI : TopologicalSpace (TotalSpace (Fin (r j) → ℝ)
      fun s ↦ (h.isNondegenerateCriticalSubmanifold j).negativeNormalSpace hn
        (g j).toRiemannianMetric s) :=
    subbundleTopology (P j)
      ((h.isNondegenerateCriticalSubmanifold j).negativeNormalSpace hn (g j).toRiemannianMetric)
  letI : FiberBundle (Fin (r j) → ℝ) fun s ↦
      (h.isNondegenerateCriticalSubmanifold j).negativeNormalSpace hn (g j).toRiemannianMetric s :=
    (hV j).fiberBundle
  haveI : VectorBundle ℝ (Fin (r j) → ℝ) fun s ↦
      (h.isNondegenerateCriticalSubmanifold j).negativeNormalSpace hn (g j).toRiemannianMetric s :=
    (hV j).vectorBundle
  finrank K (twistedHomology (signLocalSystem (Fin (r j) → ℝ)
    (fun s ↦ (h.isNondegenerateCriticalSubmanifold j).negativeNormalSpace hn
      (g j).toRiemannianMetric s) K ((Fintype.card_fin _).trans (finrank_fin_fun ℝ).symm)) k)

omit [T2Space M] [SecondCountableTopology M] [CompactSpace M] [Fintype ι]
  [∀ j, (J j).Boundaryless] in
/-- The twisted Betti number `dim Hₖ(S j; o(ν⁻ j) ⊗ K)` is the dimension of the twisted homology
of `S j` with coefficients in the orientation local system of `ν⁻ j`. -/
theorem twistedBettiNumber_def (j : ι) (k : ℕ) :
    h.twistedBettiNumber hn hdim g hV K j k =
    letI : ∀ j, FiberBundle (P j) fun s ↦ (i j).isImmersion.NormalSpace s hn :=
      fun j ↦ (i j).normalSpaceFiberBundle hn (hdim j)
    letI : ∀ j, VectorBundle ℝ (P j) fun s ↦ (i j).isImmersion.NormalSpace s hn :=
      fun j ↦ (i j).normalSpaceVectorBundle hn (hdim j)
    letI : TopologicalSpace (TotalSpace (Fin (r j) → ℝ)
        fun s ↦ (h.isNondegenerateCriticalSubmanifold j).negativeNormalSpace hn
          (g j).toRiemannianMetric s) :=
      subbundleTopology (P j)
        ((h.isNondegenerateCriticalSubmanifold j).negativeNormalSpace hn (g j).toRiemannianMetric)
    letI : FiberBundle (Fin (r j) → ℝ) fun s ↦
        (h.isNondegenerateCriticalSubmanifold j).negativeNormalSpace hn
          (g j).toRiemannianMetric s :=
      (hV j).fiberBundle
    haveI : VectorBundle ℝ (Fin (r j) → ℝ) fun s ↦
        (h.isNondegenerateCriticalSubmanifold j).negativeNormalSpace hn
          (g j).toRiemannianMetric s :=
      (hV j).vectorBundle
    finrank K (twistedHomology (signLocalSystem (Fin (r j) → ℝ)
      (fun s ↦ (h.isNondegenerateCriticalSubmanifold j).negativeNormalSpace hn
        (g j).toRiemannianMetric s) K ((Fintype.card_fin _).trans (finrank_fin_fun ℝ).symm)) k) :=
  (rfl)

omit [T2Space M] [SecondCountableTopology M] [CompactSpace M] [Fintype ι]
  [∀ j, (J j).Boundaryless] in
/-- **The twisted Betti numbers in characteristic two.** If `2 = 0` in `K`, as for `K = 𝔽₂`, the
orientation local system of every bundle is constant, so
`dim Hₖ(S j; o(ν⁻ j) ⊗ K) = bₖ(S j; K)` for every piece, oriented or not. -/
theorem twistedBettiNumber_eq_bettiNumber_of_two_eq_zero (h2 : (2 : K) = 0) (j : ι) (k : ℕ) :
    h.twistedBettiNumber hn hdim g hV K j k = bettiNumber K (S j) k := by
  let _ : ∀ j, FiberBundle (P j) fun s ↦ (i j).isImmersion.NormalSpace s hn :=
    fun j ↦ (i j).normalSpaceFiberBundle hn (hdim j)
  let _ : ∀ j, VectorBundle ℝ (P j) fun s ↦ (i j).isImmersion.NormalSpace s hn :=
    fun j ↦ (i j).normalSpaceVectorBundle hn (hdim j)
  let _ := subbundleTopology (P j) (F' := Fin (r j) → ℝ)
    ((h.isNondegenerateCriticalSubmanifold j).negativeNormalSpace hn (g j).toRiemannianMetric)
  let _ := (hV j).fiberBundle
  have := (hV j).vectorBundle
  rw [twistedBettiNumber_def]
  exact VectorBundleOrientationCover.finrank_twistedHomology_signLocalSystem_of_two_eq_zero _ h2 k

open scoped Classical in
/-- **The homology of a critical band of a Morse–Bott function, with twisted coefficients.** Let
the family `i j : S j → M` exhibit `f` as a Morse–Bott function on a compact boundaryless manifold,
let `g j` be smooth fibre metrics on the normal bundles of the pieces, and let the negative normal
spaces relative to `g j` have local frames of size `r j`, so that they form the negative normal
bundle `ν⁻ j` of rank `r j`. Let `K` be any field, and let `a < c < b` be such that `c` is the
only critical value of `f` in `[a, b]`. Then
`dim Hₙ({f ≤ b}, {f ≤ a}; K) = ∑ dim H_{n - r j}(S j; o(ν⁻ j) ⊗ K)`, the sum running over the
pieces on the level `f = c` with `r j ≤ n`, where `o(ν⁻ j)` is the orientation local system of
`ν⁻ j`. If `c` is not a critical value, the sum is empty. -/
theorem finrank_singularHomology_sublevelPair_eq_sum_twistedBettiNumber {a b c : ℝ}
    (hac : a < c) (hcb : c < b) (hcrit : ∀ x ∈ criticalPoints I f, f x ∈ Icc a b → f x = c)
    (n : ℕ) :
    finrank K ((sublevelPair f (hac.trans hcb).le).singularHomology (ModuleCat.of K K) n :
        ModuleCat K) =
      ∑ j with (∀ s, f (i j s) = c) ∧ r j ≤ n, h.twistedBettiNumber hn hdim g hV K j (n - r j) := by
  let _ : ∀ j, FiberBundle (P j) fun s ↦ (i j).isImmersion.NormalSpace s hn :=
    fun j ↦ (i j).normalSpaceFiberBundle hn (hdim j)
  let _ : ∀ j, VectorBundle ℝ (P j) fun s ↦ (i j).isImmersion.NormalSpace s hn :=
    fun j ↦ (i j).normalSpaceVectorBundle hn (hdim j)
  let _ : ∀ j, TopologicalSpace (TotalSpace (Fin (r j) → ℝ) fun s ↦
      (h.isNondegenerateCriticalSubmanifold j).negativeNormalSpace hn (g j).toRiemannianMetric s) :=
    fun j ↦ subbundleTopology (P j)
      ((h.isNondegenerateCriticalSubmanifold j).negativeNormalSpace hn (g j).toRiemannianMetric)
  let _ (j : ι) := (hV j).fiberBundle
  have (j : ι) := (hV j).vectorBundle
  -- Each Thom pair has the twisted homology of its piece shifted by the index.
  refine h.finrank_singularHomology_sublevelPair_eq_sum_of_finrank_thomPair hn K hdim g hV
    (h.twistedBettiNumber hn hdim g hV K) (fun j p ↦ ?_) hac hcb hcrit n
  rcases eq_or_ne (2 : K) 0 with h2 | h2
  · -- In characteristic two the twist disappears, and the mod `2` Thom isomorphism applies.
    rw [h.twistedBettiNumber_eq_bettiNumber_of_two_eq_zero hn hdim g hV K h2]
    exact finrank_singularHomology_thomPair_of_two_eq_zero _ _ h2 _ _ (by rw [finrank_fin_fun])
  · -- Otherwise `2` is invertible, and the twisted Thom isomorphism applies.
    let _ : Invertible (2 : K) := invertibleOfNonzero h2
    rw [twistedBettiNumber_def]
    exact finrank_singularHomology_thomPair_eq_finrank_twistedHomology _ _ _ K
      (by rw [finrank_fin_fun])

open scoped Classical in
/-- **A cut of the values of a Morse–Bott function, with twisted coefficients.** Under the
hypotheses of `finrank_singularHomology_sublevelPair_eq_sum_twistedBettiNumber`, the values of `f`
can be cut at values `s 0 ≤ s 1 ≤ ⋯ ≤ s (N + 1)`, regular from `s 1` on, with
`s 0 < f ≤ s (N + 1)`, such that summing over the bands the dimensions of their homology counts the
twisted homology of every piece once, shifted by its index. -/
private theorem exists_cut_sum_finrank_sublevelPair_eq_sum_twistedBettiNumber :
    ∃ (s : ℕ → ℝ) (hs : Monotone s) (N : ℕ), (∀ x, s 0 < f x) ∧ (∀ x, f x ≤ s (N + 1)) ∧
      (∀ j ≤ N, IsRegularValue I 𝓘(ℝ) f (s (j + 1))) ∧
      ∀ n, ∑ j ∈ Finset.range (N + 1),
          finrank K ((sublevelPair f (hs j.le_succ)).singularHomology (ModuleCat.of K K) n :
            ModuleCat K) =
        ∑ p with r p ≤ n, h.twistedBettiNumber hn hdim g hV K p (n - r p) :=
  h.exists_cut_sum_finrank_sublevelPair_eq_sum K (h.twistedBettiNumber hn hdim g hV K)
    (h.finrank_singularHomology_sublevelPair_eq_sum_twistedBettiNumber hn hdim g hV K)

/-- **The weak Morse–Bott inequalities with twisted coefficients.** Let the family `i j : S j → M`
exhibit `f` as a Morse–Bott function on a compact boundaryless manifold, let `g j` be smooth fibre
metrics on the normal bundles of the pieces, and let the negative normal spaces relative to `g j`
have local frames of size `r j`, so that they form the negative normal bundle `ν⁻ j` of rank `r j`.
Let `K` be any field, such as `ℚ`. Then
`bₙ(M; K) ≤ ∑ dim H_{n - r j}(S j; o(ν⁻ j) ⊗ K)`, the sum running over the pieces with `r j ≤ n`,
where `o(ν⁻ j)` is the orientation local system of `ν⁻ j`. -/
theorem bettiNumber_le_sum_twistedBettiNumber (n : ℕ) :
    bettiNumber K M n ≤ ∑ p with r p ≤ n, h.twistedBettiNumber hn hdim g hV K p (n - r p) := by
  obtain ⟨s, hs, N, hs₀, hsN, hreg, hsum⟩ :=
    exists_cut_sum_finrank_sublevelPair_eq_sum_twistedBettiNumber hn h hdim g hV K
  rw [bettiNumber_def, ← hsum]
  exact finrank_singularHomology_le_sum_sublevelPair_of_contMDiff (ModuleCat.of K K) h.contMDiff
    hs hs₀ hsN hreg n

/-- **The strong Morse–Bott inequalities with twisted coefficients.** Under the hypotheses of
`TauCeti.IsMorseBottFamily.bettiNumber_le_sum_twistedBettiNumber`, write `bₖ = bₖ(M; K)` and
`cₖ = ∑ dim H_{k - r j}(S j; o(ν⁻ j) ⊗ K)` over the pieces with `r j ≤ k`, the coefficient of `tᵏ`
in the twisted Morse–Bott polynomial `∑ⱼ t^{r j} P_{S j; o(ν⁻ j)}(t)`. Then
`bₙ - bₙ₋₁ + ⋯ ± b₀ ≤ cₙ - cₙ₋₁ + ⋯ ± c₀`. -/
theorem sum_range_neg_one_pow_mul_bettiNumber_le_sum_twistedBettiNumber (n : ℕ) :
    ∑ k ∈ Finset.range (n + 1), (-1 : ℤ) ^ (n - k) * bettiNumber K M k ≤
      ∑ k ∈ Finset.range (n + 1), (-1 : ℤ) ^ (n - k) *
        ((∑ p with r p ≤ k, h.twistedBettiNumber hn hdim g hV K p (k - r p) : ℕ) : ℤ) := by
  obtain ⟨s, hs, N, hs₀, hsN, hreg, hsum⟩ :=
    exists_cut_sum_finrank_sublevelPair_eq_sum_twistedBettiNumber hn h hdim g hV K
  simpa only [← bettiNumber_def, hsum] using
    sum_range_neg_one_pow_mul_finrank_singularHomology_le_sum_sublevelPair_of_contMDiff
      (ModuleCat.of K K) h.contMDiff hs hs₀ hsN hreg n

/-- **Euler's equality for a Morse–Bott function with twisted coefficients.** Under the hypotheses
of `TauCeti.IsMorseBottFamily.bettiNumber_le_sum_twistedBettiNumber`, for every `n` at least the
dimension of `M`, `∑ₖ₌₀ⁿ (-1)ᵏ bₖ = ∑ₖ₌₀ⁿ (-1)ᵏ cₖ`, where
`cₖ = ∑ dim H_{k - r j}(S j; o(ν⁻ j) ⊗ K)` over the pieces with `r j ≤ k`. -/
theorem sum_range_neg_one_pow_mul_bettiNumber_eq_sum_twistedBettiNumber {n : ℕ}
    (hdimn : finrank ℝ E ≤ n) :
    ∑ k ∈ Finset.range (n + 1), (-1 : ℤ) ^ k * bettiNumber K M k =
      ∑ k ∈ Finset.range (n + 1), (-1 : ℤ) ^ k *
        ((∑ p with r p ≤ k, h.twistedBettiNumber hn hdim g hV K p (k - r p) : ℕ) : ℤ) := by
  obtain ⟨s, hs, N, hs₀, hsN, hreg, hsum⟩ :=
    exists_cut_sum_finrank_sublevelPair_eq_sum_twistedBettiNumber hn h hdim g hV K
  simpa only [← bettiNumber_def, hsum] using
    sum_range_neg_one_pow_mul_finrank_singularHomology_eq_sum_sublevelPair_of_contMDiff
      (ModuleCat.of K K) h.contMDiff hs hs₀ hsN hreg hdimn

/-- **The Morse–Bott polynomial identity with twisted coefficients.** Under the hypotheses of
`TauCeti.IsMorseBottFamily.bettiNumber_le_sum_twistedBettiNumber`, for every `n` at least the
dimension of `M`, `∑ₖ₌₀ⁿ cₖ tᵏ = ∑ₖ₌₀ⁿ bₖ tᵏ + (1 + t) Q(t)` for a polynomial `Q` with natural
number coefficients, where `cₖ = ∑ dim H_{k - r j}(S j; o(ν⁻ j) ⊗ K)` over the pieces with
`r j ≤ k`: the twisted Morse–Bott polynomial `∑ⱼ t^{r j} P_{S j; o(ν⁻ j)}(t)` exceeds the Poincaré
polynomial of `M` by `(1 + t) Q(t)`. -/
theorem exists_sum_range_monomial_sum_twistedBettiNumber_eq_add_mul {n : ℕ}
    (hdimn : finrank ℝ E ≤ n) :
    ∃ Q : ℕ[X], ∑ k ∈ Finset.range (n + 1),
        monomial k (∑ p with r p ≤ k, h.twistedBettiNumber hn hdim g hV K p (k - r p)) =
      ∑ k ∈ Finset.range (n + 1), monomial k (bettiNumber K M k) + (1 + Polynomial.X) * Q := by
  obtain ⟨s, hs, N, hs₀, hsN, hreg, hsum⟩ :=
    exists_cut_sum_finrank_sublevelPair_eq_sum_twistedBettiNumber hn h hdim g hV K
  obtain ⟨Q, hQ, -⟩ := exists_sum_range_monomial_sum_sublevelPair_eq_add_mul_of_contMDiff
    (ModuleCat.of K K) h.contMDiff hs hs₀ hsN hreg hdimn
  simp only [← bettiNumber_def, hsum] at hQ
  exact ⟨Q, hQ⟩

/-- **The lacunary principle for a Morse–Bott function with twisted coefficients.** Under the
hypotheses of `TauCeti.IsMorseBottFamily.bettiNumber_le_sum_twistedBettiNumber`, write
`cₖ = ∑ dim H_{k - r j}(S j; o(ν⁻ j) ⊗ K)` over the pieces with `r j ≤ k`. If of any two
consecutive counts `cₖ` and `cₖ₊₁` one vanishes, then `bₙ(M; K) = cₙ` for every `n`: the
Morse–Bott function is perfect over `K`. -/
theorem bettiNumber_eq_sum_twistedBettiNumber_of_forall_eq_zero_or_eq_zero
    (hlac : ∀ k, ∑ p with r p ≤ k, h.twistedBettiNumber hn hdim g hV K p (k - r p) = 0 ∨
      ∑ p with r p ≤ k + 1, h.twistedBettiNumber hn hdim g hV K p (k + 1 - r p) = 0) (n : ℕ) :
    bettiNumber K M n = ∑ p with r p ≤ n, h.twistedBettiNumber hn hdim g hV K p (n - r p) :=
  congrFun (eq_of_forall_sum_range_neg_one_pow_mul_le
    (h.sum_range_neg_one_pow_mul_bettiNumber_le_sum_twistedBettiNumber hn hdim g hV K) hlac) n

/-! ### Comparison with the untwisted counts -/

omit [T2Space M] [SecondCountableTopology M] [CompactSpace M] [Fintype ι]
  [∀ j, (J j).Boundaryless] in
/-- **The twisted Betti numbers of a piece with an oriented negative normal bundle.** If the
negative normal bundle `ν⁻ j` of the piece `S j` is oriented, then
`dim Hₖ(S j; o(ν⁻ j) ⊗ K) = bₖ(S j; K)`: the orientation trivializes the orientation local
system. -/
theorem twistedBettiNumber_eq_bettiNumber_of_orientation (j : ι)
    (o : (h.isNondegenerateCriticalSubmanifold j).NegativeNormalBundleOrientation hn h.contMDiff
      (hdim j) (g j)
      ((h.isNondegenerateCriticalSubmanifold j).manifoldMorseIndex_eq_of_hasLocalSubbundleFrames hn
        _ (hV j)))
    (k : ℕ) :
    h.twistedBettiNumber hn hdim g hV K j k = bettiNumber K (S j) k := by
  let _ : ∀ j, FiberBundle (P j) fun s ↦ (i j).isImmersion.NormalSpace s hn :=
    fun j ↦ (i j).normalSpaceFiberBundle hn (hdim j)
  let _ : ∀ j, VectorBundle ℝ (P j) fun s ↦ (i j).isImmersion.NormalSpace s hn :=
    fun j ↦ (i j).normalSpaceVectorBundle hn (hdim j)
  let _ := subbundleTopology (P j) (F' := Fin (r j) → ℝ)
    ((h.isNondegenerateCriticalSubmanifold j).negativeNormalSpace hn (g j).toRiemannianMetric)
  let _ := (hV j).fiberBundle
  have := (hV j).vectorBundle
  rw [twistedBettiNumber_def]
  exact VectorBundleOrientation.finrank_twistedHomology_signLocalSystem _ o k

omit [T2Space M] [SecondCountableTopology M] [CompactSpace M] [Fintype ι]
  [∀ j, (J j).Boundaryless] in
/-- **The twisted Betti numbers of a simply connected piece.** Over a simply connected piece
`S j`, for instance a point, the negative normal bundle is orientable, so
`dim Hₖ(S j; o(ν⁻ j) ⊗ K) = bₖ(S j; K)`. -/
theorem twistedBettiNumber_eq_bettiNumber_of_simplyConnectedSpace (j : ι)
    [SimplyConnectedSpace (S j)] (k : ℕ) :
    h.twistedBettiNumber hn hdim g hV K j k = bettiNumber K (S j) k :=
  h.twistedBettiNumber_eq_bettiNumber_of_orientation hn hdim g hV K j
    ((h.isNondegenerateCriticalSubmanifold j).nonempty_negativeNormalBundleOrientation hn
      h.contMDiff (hdim j) (g j) _).some k

open scoped Classical in
omit [T2Space M] [SecondCountableTopology M] [CompactSpace M] [Fintype ι]
  [∀ j, (J j).Boundaryless] in
/-- **The twist in degree zero.** If `2 ≠ 0` in `K`, the zeroth twisted Betti number
`dim H₀(S j; o(ν⁻ j) ⊗ K)` of a piece is `1` when its negative normal bundle `ν⁻ j` is orientable
and `0` when it is not, whereas its ordinary zeroth Betti number is `1`, the piece being connected.
So over `ℚ` a piece of index `r j` whose negative normal bundle is not orientable, such as a
critical circle with a Möbius negative line, contributes nothing in degree `r j`. -/
theorem twistedBettiNumber_zero (h2 : (2 : K) ≠ 0) (j : ι) :
    h.twistedBettiNumber hn hdim g hV K j 0 =
      if Nonempty ((h.isNondegenerateCriticalSubmanifold j).NegativeNormalBundleOrientation hn
          h.contMDiff (hdim j) (g j)
          ((h.isNondegenerateCriticalSubmanifold j).manifoldMorseIndex_eq_of_hasLocalSubbundleFrames
            hn _ (hV j))) then 1 else 0 := by
  let _ : ∀ j, FiberBundle (P j) fun s ↦ (i j).isImmersion.NormalSpace s hn :=
    fun j ↦ (i j).normalSpaceFiberBundle hn (hdim j)
  let _ : ∀ j, VectorBundle ℝ (P j) fun s ↦ (i j).isImmersion.NormalSpace s hn :=
    fun j ↦ (i j).normalSpaceVectorBundle hn (hdim j)
  let _ := subbundleTopology (P j) (F' := Fin (r j) → ℝ)
    ((h.isNondegenerateCriticalSubmanifold j).negativeNormalSpace hn (g j).toRiemannianMetric)
  let _ := (hV j).fiberBundle
  have := (hV j).vectorBundle
  have := h.preconnectedSpace j
  have : ConnectedSpace (S j) := ⟨h.nonempty j⟩
  have := (J j).locallyPathConnectedSpace_of_chartedSpace (S j)
  rw [twistedBettiNumber_def]
  exact VectorBundleOrientationCover.finrank_twistedHomology_zero_signLocalSystem _ h2

omit [T2Space M] [SecondCountableTopology M] [CompactSpace M] [∀ j, (J j).Boundaryless] in
/-- **The twisted count of oriented negative normal bundles is the Morse–Bott count.** If the
negative normal bundle of every piece is oriented, then the coefficient
`∑ dim H_{n - r j}(S j; o(ν⁻ j) ⊗ K)` of `tⁿ` in the twisted Morse–Bott polynomial, the sum running
over the pieces with `r j ≤ n`, is the Morse–Bott count `∑ b_{n - r j}(S j; K)`
(`TauCeti.IsMorseBottFamily.morseBottCount`), the index of each piece being the rank `r j` of its
negative normal bundle. -/
theorem sum_twistedBettiNumber_eq_morseBottCount_of_orientation
    (o : ∀ j, (h.isNondegenerateCriticalSubmanifold j).NegativeNormalBundleOrientation hn
      h.contMDiff (hdim j) (g j)
      ((h.isNondegenerateCriticalSubmanifold j).manifoldMorseIndex_eq_of_hasLocalSubbundleFrames hn
        _ (hV j)))
    (n : ℕ) :
    (∑ p with r p ≤ n, h.twistedBettiNumber hn hdim g hV K p (n - r p) : ℕ∞) =
      h.morseBottCount K n := by
  have hr (p : ι) : h.index p = r p :=
    (h.index_def p).trans <|
      (h.isNondegenerateCriticalSubmanifold p).manifoldMorseIndex_eq_of_hasLocalSubbundleFrames hn _
        (hV p) _
  simp only [h.morseBottCount_eq_sum, hr, Nat.cast_sum,
    h.twistedBettiNumber_eq_bettiNumber_of_orientation hn hdim g hV K _ (o _)]

omit [T2Space M] [SecondCountableTopology M] [CompactSpace M] [∀ j, (J j).Boundaryless] in
/-- **The twisted count of a Morse function is its critical count.** If the Morse–Bott function
`f` is a Morse function, every piece is a point, whose negative normal bundle is orientable, so the
coefficient `∑ dim H_{n - r j}(S j; o(ν⁻ j) ⊗ K)` of `tⁿ` in the twisted Morse–Bott polynomial is
the number of critical points of `f` of index `n`: the twisted Morse–Bott inequalities specialize to
the Morse inequalities. -/
theorem sum_twistedBettiNumber_eq_criticalCount (hf : IsMorse I f) (n : ℕ) :
    (∑ p with r p ≤ n, h.twistedBettiNumber hn hdim g hV K p (n - r p) : ℕ∞) =
      criticalCount I f n := by
  have (p : ι) : SimplyConnectedSpace (S p) := by
    have := h.subsingleton_of_isMorse hf p
    have := h.nonempty p
    infer_instance
  rw [← h.morseBottCount_eq_criticalCount K hf n]
  exact h.sum_twistedBettiNumber_eq_morseBottCount_of_orientation hn hdim g hV K
    (fun p ↦ ((h.isNondegenerateCriticalSubmanifold p).nonempty_negativeNormalBundleOrientation hn
      h.contMDiff (hdim p) (g p) _).some) n

end TauCeti.IsMorseBottFamily
