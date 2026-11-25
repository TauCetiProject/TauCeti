/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Morse.Cell.Band
public import TauCeti.Geometry.Manifold.Morse.Generic.Strong
public import TauCeti.Geometry.Manifold.Morse.Inequalities
import TauCeti.Geometry.Manifold.MFDeriv.NormedSpace
import TauCeti.Topology.Maps.Proper.Basic
import TauCeti.Topology.Maps.Proper.Metric

/-!
# The band inequalities of a smooth function

Let `f` be a smooth proper function on a boundaryless manifold `M`, with no assumption on its
critical points, and write `M_a = {f ≤ a}`. This file shows that the relative homology of the
sublevels at two regular values behaves as if `f` were a Morse function.

Let `c` range over finitely many regular values of `f`. Since `f` is proper, its critical values
form a closed set, so there is `δ > 0` such that the bands `f⁻¹[c - δ, c + δ]` contain no critical
point of `f`. Then there is a Morse function `g` within `δ` of `f` that equals `f` near these
bands (`ContMDiffMap.exists_isMorse_mem_ball_sub_compl`). The values `c` are regular for `g` and
`g` has the same sublevels `{g ≤ c} = {f ≤ c}`
(`TauCeti.exists_isMorse_isRegularValue_sublevel_eq`). The Morse inequalities for `g` then give,
for regular values `a ≤ b` of `f` and a finite-dimensional module `V` over a division ring:

* `Hₙ(M_b, M_a; V)` is finite-dimensional
  (`TauCeti.finite_singularHomology_sublevelPair_of_contMDiff`), for instance whenever
  `a < c < b` and `c` is the only possible critical value of `f` in `[a, b]`
  (`TauCeti.finite_singularHomology_sublevelPair_of_criticalValue`);
* `Hₙ(M_b, M_a)` vanishes above the dimension of `M`, for any coefficients
  (`TauCeti.isZero_singularHomology_sublevelPair_of_contMDiff`), since the Morse index of every
  critical point of `g` is at most that dimension.

Applied to the constant function `0` on a compact manifold, whose sublevels at the regular values
`-1` and `1` are `∅` and `M`, the first statement shows that the homology `Hₙ(M; V)` of a compact
boundaryless manifold is finite-dimensional (`TauCeti.finite_singularHomology_of_compactSpace`).

These are the hypotheses of the Morse inequalities of a filtration
(`TauCeti.AlgebraicTopology.Singular.Sublevel`). Let `M` be compact, so that every smooth `f` is
proper and bounded. Cut the values of `f` at regular values
`s 0 ≤ s 1 ≤ ⋯ ≤ s (N + 1)` with `s 0 < f ≤ s (N + 1)`, write `bᵢ = dim Hᵢ(M; V)` and let
`cᵢ = ∑ⱼ dim Hᵢ(M_{s (j + 1)}, M_{s j}; V)` collect the homology of the bands. Then `b` and `c`
satisfy the weak and strong Morse inequalities, Euler's equality, the Morse polynomial identity
`∑ᵢ cᵢ tⁱ = ∑ᵢ bᵢ tⁱ + (1 + t) Q(t)` with `Q` having natural number coefficients, and the
lacunary principle.

For a Morse–Bott function the critical values are finite in number
(`TauCeti.IsMorseBottFamily.finite_image_criticalPoints`), so there is a `ℤ`-indexed cut with one
critical level in each band (`TauCeti.exists_isCriticalBandCut_of_finite_image_criticalPoints`);
reindexed, it is a cut as above with each band a critical band
(`TauCeti.exists_monotone_isCriticalBand_of_finite_image_criticalPoints`). Once the homology of
each band is identified with the homology of the critical submanifolds of its level shifted by
their indices, with coefficients twisted by the orientations of their negative normal bundles, the
statements here give the Morse–Bott inequalities. The module
`TauCeti.Geometry.Manifold.Morse.Bott.Inequalities` does this when the negative normal bundles
have Thom classes, for instance when they are oriented, and
`TauCeti.Geometry.Manifold.Morse.Bott.TwistedInequalities` does it with twisted coefficients over
every field.

## Main results

* `TauCeti.exists_isMorse_isRegularValue_sublevel_eq`: a Morse function close to a proper `f`,
  with the same sublevels as `f` at finitely many regular values of `f`.
* `TauCeti.finite_singularHomology_sublevelPair_of_contMDiff`,
  `TauCeti.finite_singularHomology_sublevelPair_of_criticalValue` and
  `TauCeti.isZero_singularHomology_sublevelPair_of_contMDiff`: finiteness of the relative
  homology of regular sublevels, and its vanishing above the dimension.
* `TauCeti.finite_singularHomology_of_compactSpace`: finiteness of the homology of a compact
  boundaryless manifold.
* `TauCeti.finrank_singularHomology_le_sum_sublevelPair_of_contMDiff`,
  `TauCeti.sum_range_neg_one_pow_mul_finrank_singularHomology_le_sum_sublevelPair_of_contMDiff`,
  `TauCeti.sum_range_neg_one_pow_mul_finrank_singularHomology_eq_sum_sublevelPair_of_contMDiff`,
  `TauCeti.exists_sum_range_monomial_sum_sublevelPair_eq_add_mul_of_contMDiff` and
  `TauCeti.finrank_singularHomology_eq_sum_sublevelPair_of_contMDiff`: the weak and strong
  inequalities, Euler's equality, the polynomial identity and the lacunary principle for the bands
  of a smooth function cut at regular values.

## References

* R. Bott, *Nondegenerate critical manifolds*, Annals of Mathematics 60 (1954), 248–261.
* R. Bott, *Lectures on Morse theory, old and new*, Bulletin of the American Mathematical
  Society 7 (1982), 331–358, Section 1.
* J. Milnor, *Morse Theory*, Annals of Mathematics Studies 51, Princeton University Press, 1963,
  Section 5.
-/

public section

open CategoryTheory Limits Module Set Topology
open Polynomial (monomial)
open scoped ContDiff Manifold Polynomial

universe u v w

namespace TauCeti

variable {E H : Type*} {M : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] [FiniteDimensional ℝ E]
  [I.Boundaryless] [IsManifold I ∞ M] [T2Space M] {f : M → ℝ}

omit [FiniteDimensional ℝ E] [I.Boundaryless] [IsManifold I ∞ M] [T2Space M] in
/-- If `g` stays within `δ` of a continuous `f` and agrees with `f` on the band
`f⁻¹[c - δ, c + δ]`, which contains no critical point of `f`, then `c` is a regular value of `g`
and `{g ≤ c} = {f ≤ c}`. -/
private theorem isRegularValue_and_sublevel_eq_of_eqOn {g : M → ℝ} {c δ : ℝ} (hf : Continuous f)
    (hgf : ∀ x, |g x - f x| < δ) (hgC : EqOn g f (f ⁻¹' Icc (c - δ) (c + δ)))
    (hreg : ∀ x, |f x - c| ≤ δ → x ∉ criticalPoints I f) :
    IsRegularValue I 𝓘(ℝ) g c ∧ {x | g x ≤ c} = {x | f x ≤ c} := by
  refine ⟨isRegularValue_iff_notMem_image_criticalPoints.2 ?_, ?_⟩
  · rintro ⟨x, hcrit, rfl⟩
    -- A critical point of `g` on the level lies in the open band `|f - c| < δ`, where `g = f`.
    obtain ⟨h₁, h₂⟩ := abs_sub_lt_iff.1 (hgf x)
    have hgf' : g =ᶠ[𝓝 x] f := Filter.eventuallyEq_of_mem
      ((isOpen_Ioo.preimage hf).mem_nhds (show f x ∈ Ioo (g x - δ) (g x + δ) from
        ⟨by linarith, by linarith⟩)) fun y hy ↦ hgC (Ioo_subset_Icc_self hy)
    refine hreg x (abs_sub_le_iff.2 ⟨by linarith, by linarith⟩) ?_
    rw [mem_criticalPoints, ← Filter.EventuallyEq.mvfderiv_eq hgf']
    exact mem_criticalPoints.1 hcrit
  · ext x
    obtain ⟨h₁, h₂⟩ := abs_sub_lt_iff.1 (hgf x)
    simp only [mem_ofPred_eq]
    by_cases hx : f x ∈ Icc (c - δ) (c + δ)
    · rw [hgC hx]
    · -- Outside the band, `f` is more than `δ` away from `c`, so `g` stays on the same side.
      rcases not_and_or.1 hx with h | h <;> constructor <;> intro <;> push Not at h <;> linarith

/-- **A Morse function with the sublevels of `f` at regular values.** Let `f` be a smooth proper
function on a boundaryless manifold, `δ > 0` and `S` a finite set of regular values of `f`. There
is a Morse function `g` within `δ` of `f` for which every `c ∈ S` is again a regular value, with
the same sublevel `{g ≤ c} = {f ≤ c}`. -/
theorem exists_isMorse_isRegularValue_sublevel_eq (hf : ContMDiff I 𝓘(ℝ) ∞ f)
    (hp : IsProperMap f) {δ : ℝ} (hδ : 0 < δ) (S : Finset ℝ)
    (hS : ∀ c ∈ S, IsRegularValue I 𝓘(ℝ) f c) :
    ∃ g : M → ℝ, IsMorse I g ∧ (∀ x, |g x - f x| < δ) ∧
      ∀ c ∈ S, IsRegularValue I 𝓘(ℝ) g c ∧ {x | g x ≤ c} = {x | f x ≤ c} := by
  have : SigmaCompactSpace M := hp.sigmaCompactSpace
  -- The critical values form a closed set missing `S`, so it misses an `ε`-thickening of `S`,
  -- and we may take `ε ≤ δ`.
  have hT : IsClosed (f '' criticalPoints I f) :=
    hp.isClosedMap _ (isClosed_criticalPoints (hf.of_le (by simp)))
  obtain ⟨ε₀, hε₀, hε₀S⟩ := S.finite_toSet.isCompact.exists_thickening_subset_open
    hT.isOpen_compl fun c hc ↦ isRegularValue_iff_notMem_image_criticalPoints.1 (hS c hc)
  obtain ⟨ε, hε, hεδ, hεS⟩ : ∃ ε > 0, ε ≤ δ ∧ Metric.thickening ε (S : Set ℝ) ⊆
      (f '' criticalPoints I f)ᶜ :=
    ⟨min ε₀ δ, lt_min hε₀ hδ, min_le_right _ _,
      (Metric.thickening_mono (min_le_left _ _) _).trans hε₀S⟩
  have hnotcrit : ∀ c ∈ S, ∀ x, |f x - c| ≤ ε / 2 → x ∉ criticalPoints I f :=
    fun c hc x hx hcrit ↦ hεS (Metric.mem_thickening_iff.2 ⟨c, hc,
      by rw [Real.dist_eq]; linarith⟩) ⟨x, hcrit, rfl⟩
  -- So `f` is Morse on the closed bands `f⁻¹[c - ε/2, c + ε/2]`, having no critical point there.
  let C : Set M := ⋃ c ∈ S, f ⁻¹' Icc (c - ε / 2) (c + ε / 2)
  have hfC : IsMorseOn I f C := by
    refine isMorseOn_iff_criticalPoints.2 ⟨hf.contMDiffOn, fun x hx hcrit ↦ ?_⟩
    obtain ⟨c, hc, hx⟩ := mem_iUnion₂.1 hx
    exact absurd hcrit (hnotcrit c hc x (abs_sub_le_iff.2 ⟨by linarith [hx.2], by linarith [hx.1]⟩))
  -- A Morse approximation within `ε/2` of `f` which agrees with `f` near the bands.
  obtain ⟨g, -, hg, hgf, hgs⟩ := ContMDiffMap.exists_isMorse_mem_ball_sub_compl ⟨f, hf⟩
    ContMDiffMap.StrongCkControl.empty continuous_const (fun _ ↦ half_pos hε)
    (isClosed_biUnion_finset fun c _ ↦ isClosed_Icc.preimage hf.continuous) hfC
  have hgC : EqOn g f C := fun x hx ↦
    sub_eq_zero.1 (image_eq_zero_of_notMem_tsupport (f := fun y ↦ g y - f y) fun h ↦ hgs h hx)
  exact ⟨g, hg, fun x ↦ (hgf x).trans_le (by linarith),
    fun c hc ↦ isRegularValue_and_sublevel_eq_of_eqOn hf.continuous hgf
    (hgC.mono (subset_biUnion_of_mem (u := fun c ↦ f ⁻¹' Icc (c - ε / 2) (c + ε / 2)) hc))
    (hnotcrit c hc)⟩

/-- A Morse function with compact band `g⁻¹[a, b]` and the sublevels of a proper `f` at two
regular values `a ≤ b`. -/
private theorem exists_isMorse_sublevelPair_eq (hf : ContMDiff I 𝓘(ℝ) ∞ f) (hp : IsProperMap f)
    {a b : ℝ} (hab : a ≤ b) (ha : IsRegularValue I 𝓘(ℝ) f a) (hb : IsRegularValue I 𝓘(ℝ) f b) :
    ∃ g : M → ℝ, IsMorse I g ∧ IsCompact (g ⁻¹' Icc a b) ∧ IsRegularValue I 𝓘(ℝ) g a ∧
      IsRegularValue I 𝓘(ℝ) g b ∧ sublevelPair g hab = sublevelPair f hab := by
  classical
  obtain ⟨g, hg, hgf, hgS⟩ := exists_isMorse_isRegularValue_sublevel_eq hf hp one_pos {a, b}
    (by simp [ha, hb])
  obtain ⟨hga, hla⟩ := hgS a (by simp)
  obtain ⟨hgb, hlb⟩ := hgS b (by simp)
  -- `g` is proper, being within distance `1` of `f`.
  have hcompact : IsCompact (g ⁻¹' Icc a b) :=
    (hp.of_dist_le hg.contMDiff.continuous (C := 1) fun x ↦ by
      rw [Real.dist_eq, abs_sub_comm]; exact (hgf x).le).isCompact_preimage isCompact_Icc
  exact ⟨g, hg, hcompact, hga, hgb, TopPair.ofInclusion_congr (X := TopCat.of M) _ _ hla hlb⟩

/-- **Finiteness of the homology of regular sublevels.** Let `f` be a smooth proper function on a
boundaryless manifold and `a ≤ b` regular values of `f`. Then the relative singular homology
`Hₙ({f ≤ b}, {f ≤ a}; V)` with coefficients in a finite-dimensional module `V` is
finite-dimensional. -/
theorem finite_singularHomology_sublevelPair_of_contMDiff {k : Type u} [DivisionRing k]
    (V : ModuleCat.{u} k) [Module.Finite k V] (hf : ContMDiff I 𝓘(ℝ) ∞ f) (hp : IsProperMap f)
    {a b : ℝ} (hab : a ≤ b) (ha : IsRegularValue I 𝓘(ℝ) f a) (hb : IsRegularValue I 𝓘(ℝ) f b)
    (n : ℕ) : Module.Finite k ((sublevelPair f hab).singularHomology V n : ModuleCat k) := by
  obtain ⟨g, hg, hcompact, hga, hgb, hgf⟩ := exists_isMorse_sublevelPair_eq hf hp hab ha hb
  rw [← hgf]
  exact hg.finite_singularHomology_sublevelPair V hab hcompact hga hgb n

variable (I M) in
include I in
/-- **Finiteness of the homology of a compact manifold.** The singular homology of a compact
boundaryless manifold, with coefficients in a finite-dimensional module `V` over a division ring,
is finite-dimensional in every degree. -/
theorem finite_singularHomology_of_compactSpace [CompactSpace M] {k : Type u} [DivisionRing k]
    (V : ModuleCat.{u} k) [Module.Finite k V] (n : ℕ) :
    Module.Finite k (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} k) n).obj V).obj
      (TopCat.of M)) :=
  -- Apply the finiteness of the homology of regular sublevels to the constant function `0`,
  -- whose sublevels `{0 ≤ -1} = ∅` and `{0 ≤ 1} = M` are cut at the regular values `±1`.
  have hreg (c : ℝ) (hc : c ≠ 0) : IsRegularValue I 𝓘(ℝ) (fun _ : M ↦ (0 : ℝ)) c :=
    isRegularValue_of_notMem_range fun ⟨_, hx⟩ ↦ hc hx.symm
  have := finite_singularHomology_sublevelPair_of_contMDiff V contMDiff_const
    continuous_const.isProperMap (neg_one_lt_zero.trans zero_lt_one).le
    (hreg _ (neg_ne_zero.2 one_ne_zero)) (hreg _ one_ne_zero) n
  Module.Finite.equiv (singularHomologyIsoSublevelPair (f := fun _ : M ↦ (0 : ℝ))
    (neg_one_lt_zero.trans zero_lt_one).le (fun _ ↦ neg_one_lt_zero) (fun _ ↦ zero_le_one) V
    n).symm.toLinearEquiv

/-- **Finiteness of the homology of a band with one critical value.** Let `f` be a smooth proper
function on a boundaryless manifold and `a < c < b` such that `c` is the only possible critical
value of `f` in `[a, b]`. Then `a` and `b` are regular values, so the relative singular homology
`Hₙ({f ≤ b}, {f ≤ a}; V)` with coefficients in a finite-dimensional module `V` is
finite-dimensional. -/
theorem finite_singularHomology_sublevelPair_of_criticalValue {k : Type u} [DivisionRing k]
    (V : ModuleCat.{u} k) [Module.Finite k V] (hf : ContMDiff I 𝓘(ℝ) ∞ f) (hp : IsProperMap f)
    {a b c : ℝ} (hac : a < c) (hcb : c < b)
    (hcrit : ∀ x ∈ criticalPoints I f, f x ∈ Icc a b → f x = c) (n : ℕ) :
    Module.Finite k ((sublevelPair f (hac.trans hcb).le).singularHomology V n : ModuleCat k) := by
  have hreg {t : ℝ} (ht : t ∈ ({a, b} : Set ℝ)) : IsRegularValue I 𝓘(ℝ) f t :=
    isRegularValue_iff_notMem_image_criticalPoints.2 fun ⟨x, hx, hxt⟩ ↦ by
      have := hcrit x hx (by rcases ht with rfl | rfl <;> simp [hxt, (hac.trans hcb).le])
      rcases ht with rfl | rfl <;> linarith
  exact finite_singularHomology_sublevelPair_of_contMDiff V hf hp (hac.trans hcb).le
    (hreg (by simp)) (hreg (by simp)) n

/-- **Vanishing of the homology of regular sublevels above the dimension.** Let `f` be a smooth
proper function on a boundaryless manifold and `a ≤ b` regular values of `f`. Then the relative
singular homology `Hₙ({f ≤ b}, {f ≤ a}; R)` vanishes for `n > dim M`, for every coefficient object
`R` of an abelian category with coproducts. -/
theorem isZero_singularHomology_sublevelPair_of_contMDiff {C : Type v} [Category.{w} C]
    [HasCoproducts.{u} C] [Abelian C] (hf : ContMDiff I 𝓘(ℝ) ∞ f) (hp : IsProperMap f) {a b : ℝ}
    (hab : a ≤ b) (ha : IsRegularValue I 𝓘(ℝ) f a) (hb : IsRegularValue I 𝓘(ℝ) f b) (R : C)
    {n : ℕ} (hn : finrank ℝ E < n) : IsZero ((sublevelPair f hab).singularHomology R n) := by
  obtain ⟨g, hg, hcompact, hga, hgb, hgf⟩ := exists_isMorse_sublevelPair_eq hf hp hab ha hb
  rw [← hgf]
  exact hg.isZero_singularHomology_sublevelPair_of_manifoldMorseIndex_le hab hcompact hga hgb
    (fun _ _ ↦ manifoldMorseIndex_le_finrank) R hn

/-! ### The inequalities for the bands of a smooth function -/

section Filtration

variable [CompactSpace M] {k : Type u} [DivisionRing k] (V : ModuleCat.{u} k) [Module.Finite k V]
  (hf : ContMDiff I 𝓘(ℝ) ∞ f) {s : ℕ → ℝ} (hs : Monotone s) {N : ℕ}
  (hs₀ : ∀ x, s 0 < f x) (hsN : ∀ x, f x ≤ s (N + 1))
  (hreg : ∀ j ≤ N, IsRegularValue I 𝓘(ℝ) f (s (j + 1)))

omit [FiniteDimensional ℝ E] [I.Boundaryless] [IsManifold I ∞ M] [T2Space M] [CompactSpace M] in
include hs₀ hreg in
/-- Every cut value `s j` is regular: `s 0` is below all values of `f`. -/
private theorem isRegularValue_cut {j : ℕ} (hj : j ≤ N + 1) : IsRegularValue I 𝓘(ℝ) f (s j) := by
  rcases j with _ | j
  · exact isRegularValue_of_notMem_range fun ⟨x, hx⟩ ↦ (hs₀ x).ne' hx
  · exact hreg j (by lia)

include hf hs₀ hreg in
/-- The bands of `f` cut at regular values have finite-dimensional homology. -/
private theorem finite_band (j : ℕ) (hj : j ≤ N) (i : ℕ) :
    Module.Finite k ((sublevelPair f (hs j.le_succ)).singularHomology V i : ModuleCat k) :=
  finite_singularHomology_sublevelPair_of_contMDiff V hf hf.continuous.isProperMap
    (hs j.le_succ) (isRegularValue_cut hs₀ hreg (by lia)) (isRegularValue_cut hs₀ hreg (by lia)) i

omit [Module.Finite k V] in
include hf hs₀ hreg in
/-- The bands of `f` cut at regular values have no homology above the dimension of `M`. -/
private theorem isZero_band (j : ℕ) (hj : j ≤ N) {i : ℕ} (hi : finrank ℝ E < i) :
    IsZero ((sublevelPair f (hs j.le_succ)).singularHomology V i) :=
  isZero_singularHomology_sublevelPair_of_contMDiff hf hf.continuous.isProperMap (hs j.le_succ)
    (isRegularValue_cut hs₀ hreg (by lia)) (isRegularValue_cut hs₀ hreg (by lia)) V hi

include hf hs₀ hsN hreg

/-- **The weak inequalities for the bands of a smooth function.** Let `f` be a smooth function on
a compact boundaryless manifold, and cut its values at regular values
`s 0 ≤ s 1 ≤ ⋯ ≤ s (N + 1)` with `s 0 < f ≤ s (N + 1)`. Then `dim Hᵢ(M; V)` is at most the sum
of the dimensions of the homology `Hᵢ({f ≤ s (j + 1)}, {f ≤ s j}; V)` of the bands. -/
theorem finrank_singularHomology_le_sum_sublevelPair_of_contMDiff (i : ℕ) :
    finrank k (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} k) i).obj V).obj
        (TopCat.of M)) ≤
      ∑ j ∈ Finset.range (N + 1),
        finrank k ((sublevelPair f (hs j.le_succ)).singularHomology V i : ModuleCat k) :=
  finrank_singularHomology_le_sum_sublevelPair hs hs₀ hsN V i
    fun j hj ↦ finite_band V hf hs hs₀ hreg j hj i

/-- **The strong inequalities for the bands of a smooth function.** Let `f` be a smooth function
on a compact boundaryless manifold, and cut its values at regular values
`s 0 ≤ s 1 ≤ ⋯ ≤ s (N + 1)` with `s 0 < f ≤ s (N + 1)`. Write `bᵢ = dim Hᵢ(M; V)` and `cᵢ` for the
sum of the dimensions of the homology `Hᵢ({f ≤ s (j + 1)}, {f ≤ s j}; V)` of the bands. Then
`bₙ - bₙ₋₁ + ⋯ ± b₀ ≤ cₙ - cₙ₋₁ + ⋯ ± c₀`. -/
theorem sum_range_neg_one_pow_mul_finrank_singularHomology_le_sum_sublevelPair_of_contMDiff
    (n : ℕ) :
    ∑ i ∈ Finset.range (n + 1), (-1 : ℤ) ^ (n - i) *
        finrank k (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} k) i).obj V).obj
          (TopCat.of M)) ≤
      ∑ i ∈ Finset.range (n + 1), (-1 : ℤ) ^ (n - i) * ((∑ j ∈ Finset.range (N + 1),
        finrank k ((sublevelPair f (hs j.le_succ)).singularHomology V i : ModuleCat k) : ℕ) :
          ℤ) :=
  sum_range_neg_one_pow_mul_finrank_singularHomology_le_sum_sublevelPair hs hs₀ hsN V
    (fun j hj ↦ finite_band V hf hs hs₀ hreg j hj) n

/-- **Euler's equality for the bands of a smooth function.** Let `f` be a smooth function on a
compact boundaryless manifold, and cut its values at regular values `s 0 ≤ s 1 ≤ ⋯ ≤ s (N + 1)`
with `s 0 < f ≤ s (N + 1)`. Write `bᵢ = dim Hᵢ(M; V)` and `cᵢ` for the sum of the dimensions of the
homology `Hᵢ({f ≤ s (j + 1)}, {f ≤ s j}; V)` of the bands. Then
`∑ᵢ₌₀ⁿ (-1)ⁱ bᵢ = ∑ᵢ₌₀ⁿ (-1)ⁱ cᵢ` for every `n ≥ dim M`. -/
theorem sum_range_neg_one_pow_mul_finrank_singularHomology_eq_sum_sublevelPair_of_contMDiff
    {n : ℕ} (hn : finrank ℝ E ≤ n) :
    ∑ i ∈ Finset.range (n + 1), (-1 : ℤ) ^ i *
        finrank k (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} k) i).obj V).obj
          (TopCat.of M)) =
      ∑ i ∈ Finset.range (n + 1), (-1 : ℤ) ^ i * ((∑ j ∈ Finset.range (N + 1),
        finrank k ((sublevelPair f (hs j.le_succ)).singularHomology V i : ModuleCat k) : ℕ) :
          ℤ) :=
  sum_range_neg_one_pow_mul_finrank_singularHomology_eq_sum_sublevelPair hs hs₀ hsN V
    (fun j hj ↦ finite_band V hf hs hs₀ hreg j hj) fun j hj ↦
      isZero_band V hf hs hs₀ hreg j hj (by lia)

/-- **The Morse polynomial identity for the bands of a smooth function.** Let `f` be a smooth
function on a compact boundaryless manifold, and cut its values at regular values
`s 0 ≤ s 1 ≤ ⋯ ≤ s (N + 1)` with `s 0 < f ≤ s (N + 1)`. Write `bᵢ = dim Hᵢ(M; V)` and `cᵢ` for the
sum of the dimensions of the homology `Hᵢ({f ≤ s (j + 1)}, {f ≤ s j}; V)` of the bands. For every
`n ≥ dim M`, `∑ᵢ₌₀ⁿ cᵢ tⁱ = ∑ᵢ₌₀ⁿ bᵢ tⁱ + (1 + t) Q(t)` for a polynomial `Q` with natural number
coefficients. For `i < n` the coefficient of `tⁱ` in `Q` is the sum over `j < N` of the ranks of
the connecting maps `Hᵢ₊₁({f ≤ s (j + 2)}, {f ≤ s (j + 1)}) ⟶ Hᵢ({f ≤ s (j + 1)}, {f ≤ s 0})` of
the triples of sublevels, and for `i ≥ n` it is zero. -/
theorem exists_sum_range_monomial_sum_sublevelPair_eq_add_mul_of_contMDiff {n : ℕ}
    (hn : finrank ℝ E ≤ n) :
    ∃ Q : ℕ[X], ∑ i ∈ Finset.range (n + 1), monomial i (∑ j ∈ Finset.range (N + 1),
          finrank k ((sublevelPair f (hs j.le_succ)).singularHomology V i : ModuleCat k)) =
        ∑ i ∈ Finset.range (n + 1), monomial i
          (finrank k (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} k) i).obj V).obj
            (TopCat.of M))) + (1 + Polynomial.X) * Q ∧
      (∀ i < n, Q.coeff i = ∑ j ∈ Finset.range N, finrank k (LinearMap.range
        ((TopTriple.ofInclusions (X := TopCat.of M) (sublevel_mono f (hs (Nat.zero_le (j + 1))))
          (sublevel_mono f (hs (j + 1).le_succ))).singularHomologyδ V (i + 1) i rfl).hom)) ∧
      ∀ i, n ≤ i → Q.coeff i = 0 :=
  exists_sum_range_monomial_sum_sublevelPair_eq_add_mul hs hs₀ hsN V
    (fun j hj ↦ finite_band V hf hs hs₀ hreg j hj) fun j hj ↦
      isZero_band V hf hs hs₀ hreg j hj (by lia)

/-- **The lacunary principle for the bands of a smooth function.** Let `f` be a smooth function on
a compact boundaryless manifold, and cut its values at regular values
`s 0 ≤ s 1 ≤ ⋯ ≤ s (N + 1)` with `s 0 < f ≤ s (N + 1)`. Write `cᵢ` for the sum of the dimensions of
the homology `Hᵢ({f ≤ s (j + 1)}, {f ≤ s j}; V)` of the bands. If of any two consecutive `cᵢ` one
vanishes, then `dim Hₙ(M; V) = cₙ` for every `n`. -/
theorem finrank_singularHomology_eq_sum_sublevelPair_of_contMDiff
    (hc : ∀ i, ∑ j ∈ Finset.range (N + 1),
        finrank k ((sublevelPair f (hs j.le_succ)).singularHomology V i : ModuleCat k) = 0 ∨
      ∑ j ∈ Finset.range (N + 1),
        finrank k ((sublevelPair f (hs j.le_succ)).singularHomology V (i + 1) : ModuleCat k) = 0)
    (n : ℕ) :
    finrank k (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} k) n).obj V).obj
        (TopCat.of M)) =
      ∑ j ∈ Finset.range (N + 1),
        finrank k ((sublevelPair f (hs j.le_succ)).singularHomology V n : ModuleCat k) :=
  finrank_singularHomology_eq_sum_sublevelPair hs hs₀ hsN V
    (fun j hj ↦ finite_band V hf hs hs₀ hreg j hj) hc n

end Filtration

end TauCeti
