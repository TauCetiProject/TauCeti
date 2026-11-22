/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.FilteredSpace.Basic
public import TauCeti.Geometry.Manifold.Morse.Bott.ThomPair

/-!
# The first page of the critical-band spectral sequence of a Morse–Bott function

Let the family `i j : S j → M` exhibit `f` as a Morse–Bott function (`TauCeti.IsMorseBottFamily`)
on a compact boundaryless manifold `M`, and let `a : ℤ → ℝ` be monotone. The sublevels
`M_{a q} = {f ≤ a q}` filter `M`, and the spectral sequence of this filtered space
(`TauCeti.filteredSpaceSpectralSequence`) has on its first page (numbered `2` in the cohomological
indexing used there) at `(p, q)` the relative homology `Hₙ(M_{a (q + 1)}, M_{a q})` of the `q`th
band, where `p + q = -n`. Such a function has finitely many critical values
(`TauCeti.IsMorseBottFamily.finite_image_criticalPoints`), so it has a critical-band cut
(`TauCeti.exists_isCriticalBandCut_of_finite_image_criticalPoints`): a sequence `a` whose bands
each contain at most one critical value, starting below and ending above all values of `f`, so
that the filtration is finite and its spectral sequence converges to the singular homology of `M`
(`TauCeti.filteredSpaceSpectralSequencePageXIsoGradedOfFinite`).

This file identifies the first page with the attachments of Bott's theorem. If every critical value
of `f` in `[a q, a (q + 1)]` equals `c`, with `a q < c < a (q + 1)`, then crossing the level `c`
attaches the negative disc bundles `D j ε` of the critical submanifolds on that level, through
Morse–Bott normal forms `Θ j` of `f` on their normal bundles
(`TauCeti.IsMorseBottFamily.exists_sublevel_union_iUnion_negativeDiscBundle_deformation`). So the
object at `(p, q)` is the relative homology
`Hₙ(M_{c - ε} ∪ ⋃ j, Θ j (D j ε), M_{c - ε})` of the lower sublevel with these disc bundles
attached, for all small `ε > 0`
(`nonempty_filteredSpaceSpectralSequence_page_two_X_iso_iUnion_negativeDiscBundle`, in the
namespace `TauCeti.IsMorseBottFamily`). When the band contains no critical value there are no
pieces on the level `c`, nothing is attached, and the object is zero, as for any smooth function
(`TauCeti.isZero_filteredSpaceSpectralSequence_page_two_X_of_forall_notMem`). When every piece is
a point, each disc bundle is a disc of dimension the Morse index, as in Milnor's cell attachment
theorem, through which the first page of a Morse function is free on its critical points
(`TauCeti.IsMorse.nonempty_filteredSpaceSpectralSequence_page_two_X_iso_sigma`).

The attachments split over the critical submanifolds, and each contributes the homology of the Thom
pair of its negative normal bundle. If the pieces `i j` have Morse indices `r j`, so that their
negative normal spaces form vector bundles `ν⁻ j` of rank `r j`, the object at `(p, q)` is the
coproduct of the groups `Hₙ(ν⁻ j, (ν⁻ j)₀)` over the pieces on the level `c`
(`nonempty_filteredSpaceSpectralSequence_page_two_X_iso_sigma_thomPair`, in the namespace
`TauCeti.IsMorseBottFamily`). This is the form in which the Thom isomorphism computes the first
page from the homology of the critical submanifolds, shifted by their indices.

The identification of one band needs neither a global Morse–Bott family nor a compact manifold:
it holds whenever the band `f⁻¹[a q, a (q + 1)]` is compact and its critical points lie on finitely
many disjoint compact nondegenerate critical submanifolds on a level `c` inside it
(`nonempty_filteredSpaceSpectralSequence_page_two_X_iso_iUnion_negativeDiscBundle`, in the
namespace `TauCeti.SmoothEmbedding`).

## Main results

In the namespace `TauCeti.SmoothEmbedding`:

* `nonempty_filteredSpaceSpectralSequence_page_two_X_iso_iUnion_negativeDiscBundle`: at a compact
  band whose critical points lie on finitely many compact Morse–Bott submanifolds on one level, the
  first page of the spectral sequence of the sublevel filtration is the relative homology of the
  lower sublevel with their negative disc bundles attached.

In the namespace `TauCeti.IsMorseBottFamily`:

* `nonempty_filteredSpaceSpectralSequence_page_two_X_iso_iUnion_negativeDiscBundle`: at a band of
  a Morse–Bott function with one critical value `c`, the first page of the spectral sequence of the
  sublevel filtration is the relative homology of the lower sublevel with the negative disc bundles
  of the critical submanifolds on the level `c` attached.
* `nonempty_filteredSpaceSpectralSequence_page_two_X_iso_sigma_thomPair`: at such a band, the first
  page is the coproduct over the critical submanifolds on the level `c` of the homologies of the
  Thom pairs of their negative normal bundles.

## References

* R. Bott, *Nondegenerate critical manifolds*, Annals of Mathematics 60 (1954), 248–261.
* R. L. Cohen, K. Iga and P. Norbury, *Topics in Morse theory: lecture notes*, 2006,
  Theorems 15.4 and 15.6.
-/

public section

noncomputable section

open Bundle CategoryTheory Function Limits Set
open scoped ContDiff Manifold

universe u v w

namespace TauCeti

variable {E H : Type*} {M : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless] [TopologicalSpace M]
  [ChartedSpace H M] [IsManifold I ∞ M] {ι : Type*} {E' H' S P : ι → Type*}
  [∀ j, NormedAddCommGroup (E' j)] [∀ j, NormedSpace ℝ (E' j)] [∀ j, FiniteDimensional ℝ (E' j)]
  [∀ j, TopologicalSpace (H' j)] {J : ∀ j, ModelWithCorners ℝ (E' j) (H' j)}
  [∀ j, TopologicalSpace (S j)] [∀ j, ChartedSpace (H' j) (S j)] [∀ j, IsManifold (J j) ∞ (S j)]
  [∀ j, NormedAddCommGroup (P j)] [∀ j, NormedSpace ℝ (P j)] [∀ j, FiniteDimensional ℝ (P j)]
  {f : M → ℝ} {i : ∀ j, SmoothEmbedding (J j) I ∞ (S j) M} (hn : (∞ : ℕ∞ω) ≠ 0)

namespace SmoothEmbedding

/-- **The first page of the critical-band spectral sequence at a band of finitely many compact
Morse–Bott submanifolds.** Let `i j : S j → M`, for `j` in a finite index type, be nondegenerate
critical submanifolds of a smooth function `f` on a Hausdorff, second-countable,
finite-dimensional, boundaryless manifold, each modelled on its own boundaryless model, with `S j`
compact and nonempty, pairwise disjoint images and `f = c` along each of them. Let `g j` be a
smooth fibre metric on the normal bundle of `i j`. Let `a : ℤ → ℝ` be monotone, with
`a q < c < a (q + 1)`, such that the band `f⁻¹[a q, a (q + 1)]` is compact and all its critical
points lie on the submanifolds.

Then there are smooth partial diffeomorphisms `Θ j` from the total spaces of the normal bundles to
`M`, each defined on a neighbourhood of the zero section and sending it to `i j`, which put `f` in
the Morse–Bott normal form `f (Θ j v) = c + ½ Hessₛ (v, v)`, and an `ε₀ > 0` with the following
property. For every `0 < ε < ε₀` each negative disc bundle `D j ε` relative to `g j` lies in the
source of `Θ j`, and on the first page of the spectral sequence of the filtration
`q ↦ {f ≤ a q}`, the object at `(p, q)` with `p + q = -n` is the relative singular homology
`Hₙ({f ≤ c - ε} ∪ ⋃ j, Θ j (D j ε), {f ≤ c - ε})`, for every coefficient object. -/
theorem nonempty_filteredSpaceSpectralSequence_page_two_X_iso_iUnion_negativeDiscBundle
    [T2Space M] [SecondCountableTopology M] [Finite ι] [∀ j, (J j).Boundaryless]
    [∀ j, CompactSpace (S j)] [∀ j, Nonempty (S j)]
    (h : ∀ j, (i j).IsNondegenerateCriticalSubmanifold f) (hfs : ContMDiff I 𝓘(ℝ) ∞ f)
    {a : ℤ → ℝ} (ha : Monotone a) {q : ℤ} {c : ℝ} (hc : ∀ j s, f (i j s) = c)
    (hd : Pairwise (Disjoint on fun j ↦ range (i j))) (hcq : c ∈ Ioo (a q) (a (q + 1)))
    (hcompact : IsCompact (f ⁻¹' Icc (a q) (a (q + 1))))
    (hcrit : criticalPoints I f ∩ f ⁻¹' Icc (a q) (a (q + 1)) ⊆ ⋃ j, range (i j))
    (hdim : ∀ j, Module.finrank ℝ (P j) = Module.finrank ℝ E - Module.finrank ℝ (E' j))
    (g : letI : ∀ j, FiberBundle (P j) fun s ↦ (i j).NormalSpace s hn :=
        fun j ↦ (i j).normalSpaceFiberBundle hn (hdim j)
      letI : ∀ j, VectorBundle ℝ (P j) fun s ↦ (i j).NormalSpace s hn :=
        fun j ↦ (i j).normalSpaceVectorBundle hn (hdim j)
      ∀ j, ContMDiffRiemannianMetric (J j) ∞ (P j) fun s ↦ (i j).NormalSpace s hn) :
    letI : ∀ j, FiberBundle (P j) fun s ↦ (i j).NormalSpace s hn :=
      fun j ↦ (i j).normalSpaceFiberBundle hn (hdim j)
    letI : ∀ j, VectorBundle ℝ (P j) fun s ↦ (i j).NormalSpace s hn :=
      fun j ↦ (i j).normalSpaceVectorBundle hn (hdim j)
    ∃ Θ : ∀ j, PartialDiffeomorph ((J j).prod 𝓘(ℝ, P j)) I
        (TotalSpace (P j) fun s ↦ (i j).NormalSpace s hn) M ∞,
      (∀ j s, zeroSection (P j) (fun s ↦ (i j).NormalSpace s hn) s ∈ (Θ j).source) ∧
      (∀ j s, Θ j (zeroSection (P j) (fun s ↦ (i j).NormalSpace s hn) s) = i j s) ∧
      (∀ j, ∀ x ∈ (Θ j).source, f (Θ j x) = c + 2⁻¹ * (h j).normalHessian hn x.proj x.snd x.snd) ∧
      ∃ ε₀ > 0, ∀ ε ∈ Ioo 0 ε₀,
        (∀ j, (h j).negativeDiscBundle hn (P j) (g j).toRiemannianMetric ε ⊆ (Θ j).source) ∧
        ∀ {A : Type v} [Category.{w} A] [Abelian A] [HasCoproducts.{u} A] (R : A) (pq : ℤ × ℤ),
          pq.2 = q → ∀ n : ℕ, pq.1 + pq.2 = -n →
            Nonempty (((filteredSpaceSpectralSequence (Y := TopCat.of M) R
                ((sublevel_mono f).comp ha)).page 2).X pq ≅
              (TopPair.ofInclusion (X := TopCat.of M) (subset_union_left :
                {y | f y ≤ c - ε} ⊆ {y | f y ≤ c - ε} ∪
                  ⋃ j, Θ j '' (h j).negativeDiscBundle hn (P j) (g j).toRiemannianMetric ε)
                ).singularHomology R n) := by
  obtain ⟨Θ, hΘz, hΘi, hΘf, ε₀, hε₀, hmain⟩ :=
    nonempty_singularHomology_sublevelPair_iso_iUnion_negativeDiscBundle hn h hfs hc hd hcq.1
      hcq.2 hcompact hcrit hdim g
  refine ⟨Θ, hΘz, hΘi, hΘf, ε₀, hε₀, fun ε hε ↦ ?_⟩
  obtain ⟨hD, hiso⟩ := hmain ε hε
  refine ⟨hD, fun {A} _ _ _ R pq hq n hpq ↦ ?_⟩
  subst hq
  obtain ⟨e⟩ := hiso R n
  exact ⟨filteredSpaceSpectralSequenceFirstPageXIso (Y := TopCat.of M) R
    ((sublevel_mono f).comp ha) pq pq.2 (pq.2 + 1) rfl rfl _ rfl n hpq ≪≫ e⟩

end SmoothEmbedding

namespace IsMorseBottFamily

/-- **The first page of the critical-band spectral sequence of a Morse–Bott function.** Let the
family `i j : S j → M` exhibit `f` as a Morse–Bott function (`TauCeti.IsMorseBottFamily`) on a
compact Hausdorff second-countable boundaryless manifold, with pieces modelled on boundaryless
models, and let `g j` be a smooth fibre metric on the normal bundle of `i j`. Let `a : ℤ → ℝ` be
monotone, and let `a q < c < a (q + 1)` be such that every critical point of `f` with value in
`[a q, a (q + 1)]` lies on the level `c`. Index the pieces on that level by
`{j // ∀ s, f (i j s) = c}`.

Then there are smooth partial diffeomorphisms `Θ j` from the total spaces of the normal bundles of
these pieces to `M`, each defined on a neighbourhood of the zero section and sending it to `i j`,
which put `f` in the Morse–Bott normal form `f (Θ j v) = c + ½ Hessₛ (v, v)`, and an `ε₀ > 0` with
the following property. For every `0 < ε < ε₀` each negative disc bundle `D j ε` relative to `g j`
lies in the source of `Θ j`, and on the first page of the spectral sequence of the filtration
`q ↦ {f ≤ a q}`, the object at `(p, q)` with `p + q = -n` is the relative singular homology
`Hₙ({f ≤ c - ε} ∪ ⋃ j, Θ j (D j ε), {f ≤ c - ε})`, for every coefficient object. -/
theorem nonempty_filteredSpaceSpectralSequence_page_two_X_iso_iUnion_negativeDiscBundle
    [T2Space M] [SecondCountableTopology M] [CompactSpace M] [∀ j, (J j).Boundaryless]
    (h : IsMorseBottFamily i f) {a : ℤ → ℝ} (ha : Monotone a) {q : ℤ} {c : ℝ}
    (hc : c ∈ Ioo (a q) (a (q + 1)))
    (hcrit : ∀ x ∈ criticalPoints I f, f x ∈ Icc (a q) (a (q + 1)) → f x = c)
    (hdim : ∀ j, Module.finrank ℝ (P j) = Module.finrank ℝ E - Module.finrank ℝ (E' j))
    (g : letI : ∀ j, FiberBundle (P j) fun s ↦ (i j).NormalSpace s hn :=
        fun j ↦ (i j).normalSpaceFiberBundle hn (hdim j)
      letI : ∀ j, VectorBundle ℝ (P j) fun s ↦ (i j).NormalSpace s hn :=
        fun j ↦ (i j).normalSpaceVectorBundle hn (hdim j)
      ∀ j, ContMDiffRiemannianMetric (J j) ∞ (P j) fun s ↦ (i j).NormalSpace s hn) :
    letI : ∀ j, FiberBundle (P j) fun s ↦ (i j).NormalSpace s hn :=
      fun j ↦ (i j).normalSpaceFiberBundle hn (hdim j)
    letI : ∀ j, VectorBundle ℝ (P j) fun s ↦ (i j).NormalSpace s hn :=
      fun j ↦ (i j).normalSpaceVectorBundle hn (hdim j)
    ∃ Θ : ∀ j : {j // ∀ s, f (i j s) = c}, PartialDiffeomorph ((J j).prod 𝓘(ℝ, P j)) I
        (TotalSpace (P j) fun s ↦ (i j).NormalSpace s hn) M ∞,
      (∀ (j : {j // ∀ s, f (i j s) = c}) s,
        zeroSection (P j) (fun s ↦ (i j).NormalSpace s hn) s ∈ (Θ j).source) ∧
      (∀ (j : {j // ∀ s, f (i j s) = c}) s,
        Θ j (zeroSection (P j) (fun s ↦ (i j).NormalSpace s hn) s) = i j s) ∧
      (∀ j : {j // ∀ s, f (i j s) = c}, ∀ x ∈ (Θ j).source, f (Θ j x) =
        c + 2⁻¹ * (h.isNondegenerateCriticalSubmanifold j).normalHessian hn x.proj x.snd x.snd) ∧
      ∃ ε₀ > 0, ∀ ε ∈ Ioo 0 ε₀,
        (∀ j : {j // ∀ s, f (i j s) = c},
          (h.isNondegenerateCriticalSubmanifold j).negativeDiscBundle hn (P j)
            (g j).toRiemannianMetric ε ⊆ (Θ j).source) ∧
        ∀ {A : Type v} [Category.{w} A] [Abelian A] [HasCoproducts.{u} A] (R : A) (pq : ℤ × ℤ),
          pq.2 = q → ∀ n : ℕ, pq.1 + pq.2 = -n →
            Nonempty (((filteredSpaceSpectralSequence (Y := TopCat.of M) R
                ((sublevel_mono f).comp ha)).page 2).X pq ≅
              (TopPair.ofInclusion (X := TopCat.of M) (subset_union_left :
                {y | f y ≤ c - ε} ⊆ {y | f y ≤ c - ε} ∪
                  ⋃ j, Θ j '' (h.isNondegenerateCriticalSubmanifold j).negativeDiscBundle hn
                    (P j) (g j).toRiemannianMetric ε)).singularHomology R n) := by
  obtain ⟨Θ, hΘz, hΘi, hΘf, ε₀, hε₀, hmain⟩ :=
    h.nonempty_singularHomology_sublevelPair_iso_iUnion_negativeDiscBundle hn hc.1 hc.2 hcrit
      hdim g
  refine ⟨Θ, hΘz, hΘi, hΘf, ε₀, hε₀, fun ε hε ↦ ?_⟩
  obtain ⟨hD, hiso⟩ := hmain ε hε
  refine ⟨hD, fun {A} _ _ _ R pq hq n hpq ↦ ?_⟩
  subst hq
  obtain ⟨e⟩ := hiso R n
  exact ⟨filteredSpaceSpectralSequenceFirstPageXIso (Y := TopCat.of M) R
    ((sublevel_mono f).comp ha) pq pq.2 (pq.2 + 1) rfl rfl _ rfl n hpq ≪≫ e⟩

end IsMorseBottFamily

section ThomPair

variable {E M : Type u} {H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] {ι : Type*} {E' H' P : ι → Type*}
  {S : ι → Type u} [∀ j, NormedAddCommGroup (E' j)] [∀ j, NormedSpace ℝ (E' j)]
  [∀ j, FiniteDimensional ℝ (E' j)] [∀ j, TopologicalSpace (H' j)]
  {J : ∀ j, ModelWithCorners ℝ (E' j) (H' j)} [∀ j, TopologicalSpace (S j)]
  [∀ j, ChartedSpace (H' j) (S j)] [∀ j, IsManifold (J j) ∞ (S j)]
  [∀ j, NormedAddCommGroup (P j)] [∀ j, NormedSpace ℝ (P j)] [∀ j, FiniteDimensional ℝ (P j)]
  {f : M → ℝ} {i : ∀ j, SmoothEmbedding (J j) I ∞ (S j) M} (hn : (∞ : ℕ∞ω) ≠ 0)

/-- **The first page of the critical-band spectral sequence of a Morse–Bott function is the sum of
the homologies of the Thom pairs of the negative normal bundles.** Let the family `i j : S j → M`
exhibit `f` as a Morse–Bott function (`TauCeti.IsMorseBottFamily`) on a compact Hausdorff
second-countable boundaryless manifold, with pieces modelled on boundaryless models and Morse index
`r j` at every point of `i j`, and let `g j` be a smooth fibre metric on the normal bundle of
`i j`. Give the total space of the negative normal spaces relative to `g j` the topology of a
subspace of the normal bundle, so that they form a vector bundle `ν⁻ j` of rank `r j` over `S j`.
Let `a : ℤ → ℝ` be monotone, and let `a q < c < a (q + 1)` be such that every critical point of `f`
with value in `[a q, a (q + 1)]` lies on the level `c`.

Then on the first page of the spectral sequence of the filtration `q ↦ {f ≤ a q}`, the object at
`(p, q)` with `p + q = -n` is the coproduct, over the pieces on the level `c`, of the relative
homologies `Hₙ(ν⁻ j, (ν⁻ j)₀)` of their Thom pairs, for every coefficient object. -/
theorem IsMorseBottFamily.nonempty_filteredSpaceSpectralSequence_page_two_X_iso_sigma_thomPair
    [T2Space M] [SecondCountableTopology M] [CompactSpace M] [∀ j, (J j).Boundaryless]
    (h : IsMorseBottFamily i f) {a : ℤ → ℝ} (ha : Monotone a) {q : ℤ} {c : ℝ}
    (hc : c ∈ Ioo (a q) (a (q + 1)))
    (hcrit : ∀ x ∈ criticalPoints I f, f x ∈ Icc (a q) (a (q + 1)) → f x = c)
    (hdim : ∀ j, Module.finrank ℝ (P j) = Module.finrank ℝ E - Module.finrank ℝ (E' j))
    (g : letI : ∀ j, FiberBundle (P j) fun s ↦ (i j).NormalSpace s hn :=
        fun j ↦ (i j).normalSpaceFiberBundle hn (hdim j)
      letI : ∀ j, VectorBundle ℝ (P j) fun s ↦ (i j).NormalSpace s hn :=
        fun j ↦ (i j).normalSpaceVectorBundle hn (hdim j)
      ∀ j, ContMDiffRiemannianMetric (J j) ∞ (P j) fun s ↦ (i j).NormalSpace s hn)
    {r : ι → ℕ} (hr : ∀ j s, manifoldMorseIndex I f (i j s) = r j)
    {A : Type v} [Category.{w} A] [Abelian A] [HasCoproducts.{u} A] (R : A) (pq : ℤ × ℤ)
    (hq : pq.2 = q) (n : ℕ) (hpq : pq.1 + pq.2 = -n) :
    letI : ∀ j, FiberBundle (P j) fun s ↦ (i j).NormalSpace s hn :=
      fun j ↦ (i j).normalSpaceFiberBundle hn (hdim j)
    letI : ∀ j, VectorBundle ℝ (P j) fun s ↦ (i j).NormalSpace s hn :=
      fun j ↦ (i j).normalSpaceVectorBundle hn (hdim j)
    letI : ∀ j, TopologicalSpace (TotalSpace (Fin (r j) → ℝ)
        fun s ↦ (h.isNondegenerateCriticalSubmanifold j).negativeNormalSpace hn
          (g j).toRiemannianMetric s) :=
      fun j ↦ subbundleTopology (P j)
        ((h.isNondegenerateCriticalSubmanifold j).negativeNormalSpace hn (g j).toRiemannianMetric)
    -- The pieces are finitely many, so the coproduct exists in the abelian category `A`.
    haveI := h.finite
    Nonempty (((filteredSpaceSpectralSequence (Y := TopCat.of M) R
        ((sublevel_mono f).comp ha)).page 2).X pq ≅
      ∐ fun j : {j // ∀ s, f (i j s) = c} ↦ (thomPair (Fin (r j) → ℝ)
        fun s ↦ (h.isNondegenerateCriticalSubmanifold j).negativeNormalSpace hn
          (g j).toRiemannianMetric s).singularHomology R n) := by
  subst hq
  obtain ⟨e⟩ := h.nonempty_singularHomology_sublevelPair_iso_sigma_thomPair hn hc.1 hc.2 hcrit
    hdim g hr R n
  exact ⟨filteredSpaceSpectralSequenceFirstPageXIso (Y := TopCat.of M) R
    ((sublevel_mono f).comp ha) pq pq.2 (pq.2 + 1) rfl rfl _ rfl n hpq ≪≫ e⟩

end ThomPair

end TauCeti
