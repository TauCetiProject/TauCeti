/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.Empty
public import TauCeti.AlgebraicTopology.Singular.Excision
public import TauCeti.Geometry.Manifold.Morse.Bott.Homology
import TauCeti.Geometry.Manifold.SmoothEmbedding.NormalSpace.Metric

/-!
# Crossing the level of a Morse–Bott submanifold of index zero

Let `i : S → M` be a nondegenerate critical submanifold of a smooth function `f`, on the level
`f = c`, along which the Morse index of `f` is `0`: the normal Hessian is positive definite, so
`f` has a local minimum along the submanifold. Let `a < c < b` be such that the band `f⁻¹[a, b]` is
compact and all its critical points lie on `i`. Write `M_t = {f ≤ t}`. Then the inclusion of pairs
`(i(S), ∅) ⟶ (M_b, M_a)` induces isomorphisms on relative singular homology, in every degree and
for every coefficient object of an abelian category with coproducts, so that
`Hₙ(M_b, M_a) ≅ Hₙ(S)`: crossing the level adds a disjoint copy of the critical submanifold to the
lower sublevel.

This is the index-zero case of Bott's identification of the relative homology across a critical
level with the homology of the critical submanifold, shifted by the index and twisted by the
orientation of the negative normal bundle. In index zero the negative normal bundle has rank `0`, so
there is neither a shift nor a twist, and no Thom isomorphism is needed. For a function which is
constant on a connected component of a manifold, the component is a critical submanifold of index
zero; for an isolated nondegenerate local minimum the submanifold is a point.

## Main results

In the namespace `TauCeti.SmoothEmbedding.IsNondegenerateCriticalSubmanifold`:

* `image_negativeDiscBundle_eq_range_of_manifoldMorseIndex_eq_zero`: in index zero a Morse–Bott
  normal form carries the negative disc bundle onto the critical submanifold.
* `exists_isIso_singularHomologyMap_range_of_manifoldMorseIndex_eq_zero`: for all small `ε > 0`,
  the inclusion `(i(S), ∅) ⟶ (M_{c+ε}, M_{c-ε})` induces isomorphisms on relative homology.
* `isIso_singularHomologyMap_range_sublevelPair_of_manifoldMorseIndex_eq_zero`: the same for
  `(i(S), ∅) ⟶ (M_b, M_a)`, for any band `f⁻¹[a, b]` around the level as above.
* `singularHomologyIsoSublevelPairOfManifoldMorseIndexEqZero`: `Hₙ(S) ≅ Hₙ(M_b, M_a)`, induced by
  `i` and the inclusion of pairs.

## The proof

Choose a smooth fibre metric on the normal bundle
(`TauCeti.SmoothEmbedding.nonempty_contMDiffRiemannianMetric_normalSpace`). For small `ε > 0` the
inclusion of pairs `(M_{c-ε} ∪ Θ(D_ε), M_{c-ε}) ⟶ (M_{c+ε}, M_{c-ε})` induces isomorphisms on
relative homology, where `D_ε` is the negative disc bundle and `Θ` a Morse–Bott normal form
(`IsNondegenerateCriticalSubmanifold.exists_isIso_singularHomologyMap_negativeDiscBundle`). The
negative normal spaces have dimension the Morse index
(`IsNondegenerateCriticalSubmanifold.finrank_negativeNormalSpace`), so in index zero `D_ε` is the
zero section and `Θ(D_ε)` is the image of `i`, a compact set on the level `c`, disjoint from the
closed set `M_{c-ε}`. Excising `M_{c-ε}`
(`TopPair.isIso_singularHomologyMap_ofInclusionMap_union_of_disjoint`) leaves the homology of the
image of `i`, which is homeomorphic to `S`. Finally the regular collars `f⁻¹[a, c - ε]` and
`f⁻¹[c + ε, b]` carry no relative homology, so they can be cut off
(`TauCeti.isIso_singularHomologyMap_ofInclusionMap_sublevelPair_iff`).

## References

* R. Bott, *Nondegenerate critical manifolds*, Annals of Mathematics 60 (1954), 248–261.
* R. L. Cohen, K. Iga and P. Norbury, *Topics in Morse theory: lecture notes*, 2006,
  Theorem 15.4.
-/

public section

noncomputable section

open Bundle CategoryTheory Limits Module Set Topology
open scoped ContDiff Manifold

universe u v w

namespace TauCeti

namespace SmoothEmbedding

variable {E H : Type*} {M : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless] [TopologicalSpace M]
  [ChartedSpace H M] [IsManifold I ∞ M] {E' H' S : Type*} [NormedAddCommGroup E']
  [NormedSpace ℝ E'] [FiniteDimensional ℝ E'] [TopologicalSpace H'] {J : ModelWithCorners ℝ E' H'}
  [TopologicalSpace S] [ChartedSpace H' S] [IsManifold J ∞ S] {f : M → ℝ}
  {i : SmoothEmbedding J I ∞ S M}

namespace IsNondegenerateCriticalSubmanifold

omit [FiniteDimensional ℝ E'] [IsManifold J ∞ S] in
/-- **The negative disc bundle in index zero is the zero section.** If the Morse index of `f`
vanishes along a nondegenerate critical submanifold `i`, the negative normal spaces are `0`, so for
`ε ≥ 0` a Morse–Bott normal form `Θ` sending the zero section to `i` carries the negative disc
bundle of size `ε` onto the image of `i`. -/
theorem image_negativeDiscBundle_eq_range_of_manifoldMorseIndex_eq_zero {P : Type*}
    (hn : (∞ : ℕ∞ω) ≠ 0) (h : i.IsNondegenerateCriticalSubmanifold f)
    (hidx : ∀ s, manifoldMorseIndex I f (i s) = 0)
    (g : RiemannianMetric fun s ↦ i.NormalSpace s hn)
    {Θ : TotalSpace P (fun s ↦ i.NormalSpace s hn) → M}
    (hΘi : ∀ s, Θ (zeroSection P (fun s ↦ i.NormalSpace s hn) s) = i s) {ε : ℝ} (hε : 0 ≤ ε) :
    Θ '' h.negativeDiscBundle hn P g ε = range i := by
  refine Subset.antisymm ?_ (range_subset_iff.2 fun s ↦
    ⟨_, h.zeroSection_mem_negativeDiscBundle hn P g hε s, hΘi s⟩)
  rintro _ ⟨⟨s, v⟩, hv, rfl⟩
  -- The negative normal space at `s` has dimension the Morse index `0`, so `v = 0`.
  have hbot : h.negativeNormalSpace hn g s = ⊥ := by
    rw [← Submodule.finrank_eq_zero, h.finrank_negativeNormalSpace hn g s, hidx s]
  have hv0 : v = 0 := by
    simpa [hbot] using (h.toIsCriticalSubmanifold.mem_negativeDiscBundle hn).1 hv |>.1
  subst hv0
  exact ⟨s, (hΘi s).symm⟩

/-- In index zero, crossing the level attaches the image of `i` to the lower sublevel: for a fibre
metric chosen on the normal bundle, the negative disc bundle of
`exists_isIso_singularHomologyMap_negativeDiscBundle` is the zero section. -/
private theorem exists_isIso_singularHomologyMap_union_range [T2Space M]
    [SecondCountableTopology M] [J.Boundaryless]
    (h : i.IsNondegenerateCriticalSubmanifold f) (hfs : ContMDiff I 𝓘(ℝ) ∞ f) {c : ℝ}
    (hc : ∀ s, f (i s) = c) (hidx : ∀ s, manifoldMorseIndex I f (i s) = 0) :
    ∃ ε₀ > 0, ∀ ε (hε : 0 < ε), ε < ε₀ → IsCompact (f ⁻¹' Icc (c - ε) (c + ε)) →
      criticalPoints I f ∩ f ⁻¹' Icc (c - ε) (c + ε) ⊆ range i →
      ∃ hA : {y | f y ≤ c - ε} ∪ range i ⊆ {y | f y ≤ c + ε},
        ∀ {A : Type v} [Category.{w} A] [Abelian A] [HasCoproducts.{u} A] (R : A) (n : ℕ),
          IsIso (TopPair.singularHomologyMap (TopPair.ofInclusionMap (X := TopCat.of M)
            (Y := TopCat.of M) (subset_union_left :
              {y | f y ≤ c - ε} ⊆ {y | f y ≤ c - ε} ∪ range i)
            (sublevel_mono f (a := c - ε) (b := c + ε) (by linarith))
            (ContinuousMap.inclusion hA) fun _ hx ↦ hx) R n) := by
  rcases isEmpty_or_nonempty S with hS | hS
  · refine ⟨1, one_pos, fun ε hε _ hcompact hcrit ↦ ?_⟩
    have hle : c - ε ≤ c + ε := by linarith
    have hreg : ∀ x, c - ε ≤ f x → f x ≤ c + ε → mfderiv I 𝓘(ℝ) f x ≠ 0 := fun x h₁ h₂ hx ↦ by
      obtain ⟨s, -⟩ := hcrit ⟨mem_criticalPoints_iff_mfderiv_eq_zero.2 hx, h₁, h₂⟩
      exact isEmptyElim s
    obtain ⟨rdef, -, ⟨G⟩⟩ := exists_sublevelDeformation hfs hle hcompact hreg
    have hAeq : {y | f y ≤ c - ε} ∪ range i = {y | f y ≤ c - ε} := by
      rw [range_eq_empty, union_empty]
    have hA : {y | f y ≤ c - ε} ∪ range i ⊆ {y | f y ≤ c + ε} := fun y hy ↦ by
      rcases hy with hy | ⟨s, -⟩
      · exact sublevel_mono f hle hy
      · exact isEmptyElim s
    have hset : {x : {y | f y ≤ c + ε} | (x : M) ∈ {y | f y ≤ c - ε}} =
        {x : {y | f y ≤ c + ε} | (x : M) ∈ {y | f y ≤ c - ε} ∪ range i} := by
      rw [hAeq]
    have hincl : sublevelInclusion f (c - ε) (c + ε) hle =
        (ContinuousMap.inclusion hA).comp (ContinuousMap.inclusion subset_union_left) := by
      ext; simp
    rw [hincl] at G
    let r' : C({y | f y ≤ c + ε}, ↥({y | f y ≤ c - ε} ∪ range i)) :=
      (ContinuousMap.inclusion subset_union_left).comp rdef
    have G' : ((ContinuousMap.inclusion hA).comp r').HomotopyRel (ContinuousMap.id _)
        {x | (x : M) ∈ {y | f y ≤ c - ε} ∪ range i} := hset ▸ G
    exact ⟨hA, fun R n ↦ TopPair.isIso_singularHomologyMap_ofInclusionMap_inclusion_of_homotopyRel
      (X := TopCat.of M) subset_union_left hA r' G' R n⟩
  have hn : (∞ : ℕ∞ω) ≠ 0 := by simp
  by_cases hS : CompactSpace S
  swap
  · -- If `S` is not compact, no `ε` satisfies the hypotheses.
    refine ⟨1, one_pos, fun ε hε _ hcompact hcrit ↦ (hS ?_).elim⟩
    exact h.toIsCriticalSubmanifold.compactSpace_of_isCompact_preimage_Icc (hfs.of_le (by simp))
      hc (by linarith) (by linarith) hcompact hcrit
  let P := EuclideanSpace ℝ (Fin (finrank ℝ E - finrank ℝ E'))
  have hdim : finrank ℝ P = finrank ℝ E - finrank ℝ E' := finrank_euclideanSpace_fin
  let := i.normalSpaceFiberBundle hn hdim
  let := i.normalSpaceVectorBundle hn hdim
  obtain ⟨g⟩ := i.nonempty_contMDiffRiemannianMetric_normalSpace hn hdim
  obtain ⟨Θ, -, hΘi, -, ε₀, hε₀, hmain⟩ :=
    h.exists_isIso_singularHomologyMap_negativeDiscBundle hn hfs hc hdim g
  refine ⟨ε₀, hε₀, fun ε hε hεε₀ hcompact hcrit ↦ ?_⟩
  have hmε := hmain ε hε hεε₀ hcompact hcrit
  rw [image_negativeDiscBundle_eq_range_of_manifoldMorseIndex_eq_zero hn h hidx
    g.toRiemannianMetric hΘi hε.le] at hmε
  exact ⟨hmε.2.1, fun R n ↦ hmε.2.2 R n⟩

/-- **The relative homology across the level of a Morse–Bott submanifold of index zero.** Let
`i : S → M` be a nondegenerate critical submanifold of a smooth function `f` on a Hausdorff,
second-countable, finite-dimensional, boundaryless manifold, with `f = c` along `i` and Morse index
`0` at every point of `i`. Then there is an `ε₀ > 0` such that for `0 < ε < ε₀` with the band
`f⁻¹[c - ε, c + ε]` compact and all its critical points on `i`, the inclusion of pairs
`(i(S), ∅) ⟶ ({f ≤ c + ε}, {f ≤ c - ε})` induces isomorphisms on relative singular homology, in
every degree and for every coefficient object of an abelian category with coproducts. -/
theorem exists_isIso_singularHomologyMap_range_of_manifoldMorseIndex_eq_zero [T2Space M]
    [SecondCountableTopology M] [J.Boundaryless]
    (h : i.IsNondegenerateCriticalSubmanifold f) (hfs : ContMDiff I 𝓘(ℝ) ∞ f) {c : ℝ}
    (hc : ∀ s, f (i s) = c) (hidx : ∀ s, manifoldMorseIndex I f (i s) = 0) :
    ∃ ε₀ > 0, ∀ ε (hε : 0 < ε), ε < ε₀ → IsCompact (f ⁻¹' Icc (c - ε) (c + ε)) →
      criticalPoints I f ∩ f ⁻¹' Icc (c - ε) (c + ε) ⊆ range i →
      ∀ {A : Type v} [Category.{w} A] [Abelian A] [HasCoproducts.{u} A] (R : A) (n : ℕ),
        IsIso (TopPair.singularHomologyMap (TopPair.ofInclusionMap (X := TopCat.of M)
          (Y := TopCat.of M) (empty_subset (range i))
          (sublevel_mono f (a := c - ε) (b := c + ε) (by linarith))
          (ContinuousMap.inclusion (range_subset_iff.2 fun s ↦
            (hc s).trans_le (by linarith : c ≤ c + ε)))
          fun _ hx ↦ hx.elim) R n) := by
  obtain ⟨ε₀, hε₀, hmain⟩ := exists_isIso_singularHomologyMap_union_range h hfs hc hidx
  refine ⟨ε₀, hε₀, fun ε hε hεε₀ hcompact hcrit A _ _ _ R n ↦ ?_⟩
  obtain ⟨hA, hiso⟩ := hmain ε hε hεε₀ hcompact hcrit
  have : CompactSpace S := h.toIsCriticalSubmanifold.compactSpace_of_isCompact_preimage_Icc
    (hfs.of_le (by simp)) hc (by linarith) (by linarith) hcompact hcrit
  -- Relative to `{f ≤ c - ε}`, the image of `i` contributes its own homology.
  have hexc := TopPair.isIso_singularHomologyMap_ofInclusionMap_union_of_disjoint R
    (X := TopCat.of M) (s := {y | f y ≤ c - ε}) (t := range i)
    (isClosed_le hfs.continuous continuous_const)
    (isCompact_range i.isEmbedding.continuous).isClosed
    (Set.disjoint_left.2 fun y (hy : f y ≤ c - ε) ⟨s', hs'⟩ ↦ by
      rw [← hs', hc] at hy
      linarith) n
  -- The inclusion factors through `({f ≤ c - ε} ∪ i(S), {f ≤ c - ε})`. The inclusion `hsl` of
  -- sublevels is a local hypothesis, so that the maps of pairs built from it can be rewritten.
  have hsl : {y | f y ≤ c - ε} ⊆ {y | f y ≤ c + ε} := sublevel_mono f (by linarith)
  have hfac := TopPair.ofInclusionMap_comp (X := TopCat.of M) (Y := TopCat.of M)
    (Z := TopCat.of M) (hst := empty_subset (range i))
    (hst' := (subset_union_left : {y | f y ≤ c - ε} ⊆ {y | f y ≤ c - ε} ∪ range i)) hsl
    (ContinuousMap.inclusion subset_union_right) (ContinuousMap.inclusion hA)
    (fun _ hx ↦ hx.elim) fun _ hx ↦ hx
  exact (congrArg IsIso ((congrArg (TopPair.singularHomologyMap · R n) hfac).trans
    (TopPair.singularHomologyMap_comp _ R _ n))).mpr (IsIso.comp_isIso' hexc (hiso R n))

/-- **Crossing the level of a Morse–Bott submanifold of index zero adds a copy of the
submanifold.** Let `i : S → M` be a nondegenerate critical submanifold of a smooth function `f` on
a Hausdorff, second-countable, finite-dimensional, boundaryless manifold, with `f = c` along `i`
and Morse index `0` at every point of `i`. Let `a < c < b` be such that the band `f⁻¹[a, b]` is
compact and all its critical points lie on `i`.

Then the inclusion of pairs `(i(S), ∅) ⟶ ({f ≤ b}, {f ≤ a})` induces isomorphisms on relative
singular homology, in every degree and for every coefficient object of an abelian category with
coproducts: `Hₙ({f ≤ b}, {f ≤ a})` is the singular homology of the image of `i`. -/
theorem isIso_singularHomologyMap_range_sublevelPair_of_manifoldMorseIndex_eq_zero
    [T2Space M] [SecondCountableTopology M] [J.Boundaryless]
    (h : i.IsNondegenerateCriticalSubmanifold f) (hfs : ContMDiff I 𝓘(ℝ) ∞ f) {a b c : ℝ}
    (hc : ∀ s, f (i s) = c) (hidx : ∀ s, manifoldMorseIndex I f (i s) = 0) (hac : a < c)
    (hcb : c < b) (hcompact : IsCompact (f ⁻¹' Icc a b))
    (hcrit : criticalPoints I f ∩ f ⁻¹' Icc a b ⊆ range i)
    {A : Type v} [Category.{w} A] [Abelian A] [HasCoproducts.{u} A] (R : A) (n : ℕ) :
    IsIso (TopPair.singularHomologyMap (TopPair.ofInclusionMap (X := TopCat.of M)
      (Y := TopCat.of M) (empty_subset (range i)) (sublevel_mono f (hac.trans hcb).le)
      (ContinuousMap.inclusion (range_subset_iff.2 fun s ↦ (hc s).trans_le hcb.le))
      fun _ hx ↦ hx.elim) R n) := by
  obtain ⟨ε₀, hε₀, hmain⟩ :=
    h.exists_isIso_singularHomologyMap_range_of_manifoldMorseIndex_eq_zero hfs hc hidx
  -- Fix a width `0 < ε < ε₀` with `[c - ε, c + ε] ⊆ (a, b)`.
  have hm : 0 < min ε₀ (min (c - a) (b - c)) := lt_min hε₀ (lt_min (by linarith) (by linarith))
  set ε := min ε₀ (min (c - a) (b - c)) / 2
  have hε : 0 < ε := half_pos hm
  have hεm : ε < min ε₀ (min (c - a) (b - c)) := half_lt_self hm
  have hεa : ε < c - a := hεm.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hεb : ε < b - c := hεm.trans_le ((min_le_right _ _).trans (min_le_right _ _))
  have hsub {a₁ b₁ : ℝ} (h₁ : a ≤ a₁) (h₂ : b₁ ≤ b) : IsCompact (f ⁻¹' Icc a₁ b₁) :=
    hcompact.of_isClosed_subset (isClosed_Icc.preimage hfs.continuous)
      (preimage_mono (Icc_subset_Icc h₁ h₂))
  -- A critical point of the band lies on `i`, hence on the level `c`.
  have hlev {x : M} (hx : mfderiv I 𝓘(ℝ) f x = 0) (h₁ : a ≤ f x) (h₂ : f x ≤ b) : f x = c := by
    obtain ⟨s, rfl⟩ := hcrit ⟨mem_criticalPoints_iff_mfderiv_eq_zero.2 hx, h₁, h₂⟩
    exact hc s
  -- The regular collars `f⁻¹[a, c - ε]` and `f⁻¹[c + ε, b]` can be cut off.
  refine (isIso_singularHomologyMap_ofInclusionMap_sublevelPair_iff hfs (s := c - ε) (t := c + ε)
    (by linarith) (by linarith) (by linarith) (hsub le_rfl (by linarith))
    (hsub (by linarith) le_rfl) (fun x h₁ h₂ h₀ ↦ by linarith [hlev h₀ h₁ (by linarith)])
    (fun x h₁ h₂ h₀ ↦ by linarith [hlev h₀ (by linarith) h₂]) (empty_subset (range i))
    (range_subset_iff.2 fun s ↦ (hc s).trans_le (by linarith : c ≤ c + ε)) (empty_subset _)
    R n).2 ?_
  exact hmain ε hε (hεm.trans_le (min_le_left _ _)) (hsub (by linarith) (by linarith))
    (fun x hx ↦ hcrit ⟨hx.1, (by linarith [hx.2.1] : a ≤ f x), (by linarith [hx.2.2] : f x ≤ b)⟩)
    R n

/-- **The relative homology across the level of a Morse–Bott submanifold of index zero is the
homology of the submanifold.** Under the hypotheses of
`isIso_singularHomologyMap_range_sublevelPair_of_manifoldMorseIndex_eq_zero`, for `S` in the
universe of `M`, `Hₙ(S) ≅ Hₙ({f ≤ b}, {f ≤ a})`, in every degree and for every coefficient object
of an abelian category with coproducts. The forward map is induced by `i`, followed by the quotient
map from absolute to relative homology of `(i(S), ∅)` and by the inclusion of pairs
`(i(S), ∅) ⟶ ({f ≤ b}, {f ≤ a})`
(`singularHomologyIsoSublevelPairOfManifoldMorseIndexEqZero_hom`). -/
def singularHomologyIsoSublevelPairOfManifoldMorseIndexEqZero {S : Type u}
    [TopologicalSpace S] [ChartedSpace H' S] [IsManifold J ∞ S] {i : SmoothEmbedding J I ∞ S M}
    [T2Space M] [SecondCountableTopology M] [J.Boundaryless]
    (h : i.IsNondegenerateCriticalSubmanifold f) (hfs : ContMDiff I 𝓘(ℝ) ∞ f) {a b c : ℝ}
    (hc : ∀ s, f (i s) = c) (hidx : ∀ s, manifoldMorseIndex I f (i s) = 0) (hac : a < c)
    (hcb : c < b) (hcompact : IsCompact (f ⁻¹' Icc a b))
    (hcrit : criticalPoints I f ∩ f ⁻¹' Icc a b ⊆ range i)
    {A : Type v} [Category.{w} A] [Abelian A] [HasCoproducts.{u} A] (R : A) (n : ℕ) :
    ((AlgebraicTopology.singularHomologyFunctor A n).obj R).obj (TopCat.of S) ≅
      (sublevelPair f (hac.trans hcb).le).singularHomology R n :=
  have : IsEmpty (TopPair.ofInclusion (X := TopCat.of M) (empty_subset (range i))).snd :=
    inferInstanceAs (IsEmpty (∅ : Set M))
  have := h.isIso_singularHomologyMap_range_sublevelPair_of_manifoldMorseIndex_eq_zero hfs hc hidx
    hac hcb hcompact hcrit R n
  -- Each `asIso` is elaborated without the expected type, so that instance search sees the objects
  -- of the pairs rather than the homology of `S` they unfold to.
  ((AlgebraicTopology.singularHomologyFunctor A n).obj R).mapIso
      (TopCat.isoOfHomeo i.isEmbedding.toHomeomorph) ≪≫
    (asIso ((TopPair.ofInclusion (X := TopCat.of M) (empty_subset (range i))).singularHomologyπ
      R n) :) ≪≫
    (asIso (TopPair.singularHomologyMap (TopPair.ofInclusionMap (X := TopCat.of M)
      (Y := TopCat.of M) (empty_subset (range i)) (sublevel_mono f (hac.trans hcb).le)
      (ContinuousMap.inclusion (range_subset_iff.2 fun s ↦ (hc s).trans_le hcb.le))
      fun _ hx ↦ hx.elim) R n) :)

/-- The forward map of `singularHomologyIsoSublevelPairOfManifoldMorseIndexEqZero` is induced by
`i : S → i(S)`, followed by the quotient map from absolute to relative homology of `(i(S), ∅)` and
by the inclusion of pairs `(i(S), ∅) ⟶ ({f ≤ b}, {f ≤ a})`. -/
@[reassoc]
theorem singularHomologyIsoSublevelPairOfManifoldMorseIndexEqZero_hom {S : Type u}
    [TopologicalSpace S] [ChartedSpace H' S] [IsManifold J ∞ S] {i : SmoothEmbedding J I ∞ S M}
    [T2Space M] [SecondCountableTopology M] [J.Boundaryless]
    (h : i.IsNondegenerateCriticalSubmanifold f) (hfs : ContMDiff I 𝓘(ℝ) ∞ f) {a b c : ℝ}
    (hc : ∀ s, f (i s) = c) (hidx : ∀ s, manifoldMorseIndex I f (i s) = 0) (hac : a < c)
    (hcb : c < b) (hcompact : IsCompact (f ⁻¹' Icc a b))
    (hcrit : criticalPoints I f ∩ f ⁻¹' Icc a b ⊆ range i)
    {A : Type v} [Category.{w} A] [Abelian A] [HasCoproducts.{u} A] (R : A) (n : ℕ) :
    (h.singularHomologyIsoSublevelPairOfManifoldMorseIndexEqZero hfs hc hidx hac hcb hcompact
        hcrit R n).hom =
      ((AlgebraicTopology.singularHomologyFunctor A n).obj R).map
          (TopCat.ofHom ⟨rangeFactorization i, i.isEmbedding.continuous.rangeFactorization⟩) ≫
        (TopPair.ofInclusion (X := TopCat.of M) (empty_subset (range i))).singularHomologyπ R n ≫
        TopPair.singularHomologyMap (TopPair.ofInclusionMap (X := TopCat.of M)
          (Y := TopCat.of M) (empty_subset (range i)) (sublevel_mono f (hac.trans hcb).le)
          (ContinuousMap.inclusion (range_subset_iff.2 fun s ↦ (hc s).trans_le hcb.le))
          fun _ hx ↦ hx.elim) R n := by
  rw [singularHomologyIsoSublevelPairOfManifoldMorseIndexEqZero]
  -- `Iso.trans_hom`, `Functor.mapIso_hom`, `asIso_hom` and `TopCat.isoOfHomeo_hom` are all `rfl`,
  -- and so is `IsEmbedding.toHomeomorph_apply_coe`, which says that `i.isEmbedding.toHomeomorph`
  -- is `rangeFactorization i` pointwise. They cannot be used with `rw` or `simp` here: `i(S)` and
  -- the first space of `TopPair.ofInclusion` agree only after unfolding the pair, so the motive is
  -- not type-correct at the transparency `rw` checks. Hence the goal is closed by `rfl`.
  rfl

end IsNondegenerateCriticalSubmanifold

end SmoothEmbedding

end TauCeti
