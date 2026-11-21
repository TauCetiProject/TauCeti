/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.FilteredSpace.Basic
public import TauCeti.Geometry.Manifold.Morse.Bott.Homology
public import TauCeti.Geometry.Manifold.Morse.Bott.Homology.ThomPair

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

In the namespace `TauCeti.SmoothEmbedding.IsNondegenerateCriticalSubmanifold`:

* `nonempty_filteredSpaceSpectralSequence_page_two_X_iso_thomPair` and
  `isZero_filteredSpaceSpectralSequence_page_two_X_of_lt_index`: across a single compact
  Morse–Bott submanifold of constant index `r`, the first page is the homology of the Thom pair
  `(ν⁻, ν⁻₀)` and vanishes below `r`.

In the namespace `TauCeti.IsMorseBottFamily`:

* `nonempty_filteredSpaceSpectralSequence_page_two_X_iso_iUnion_negativeDiscBundle`: at a band of
  a Morse–Bott function with one critical value `c`, the first page of the spectral sequence of the
  sublevel filtration is the relative homology of the lower sublevel with the negative disc bundles
  of the critical submanifolds on the level `c` attached.

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

namespace SmoothEmbedding.IsNondegenerateCriticalSubmanifold

section ThomPair

open Module Topology

variable {E : Type u} {H : Type*} {M : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  [SecondCountableTopology M]
  {E' H' : Type*} {S : Type u} [NormedAddCommGroup E'] [NormedSpace ℝ E']
  [FiniteDimensional ℝ E'] [TopologicalSpace H'] {J : ModelWithCorners ℝ E' H'} [J.Boundaryless]
  [TopologicalSpace S] [ChartedSpace H' S] [IsManifold J ∞ S] [CompactSpace S]
  {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
  {f : M → ℝ} {i : SmoothEmbedding J I ∞ S M} (hn : (∞ : ℕ∞ω) ≠ 0)

/-- **The first page of the sublevel filtration spectral sequence across a Morse–Bott submanifold.**
Let `a : ℤ → ℝ` be monotone, and suppose the `q`-th band `f⁻¹[a q, a (q + 1)]` is compact,
contains the critical level `c` strictly between `a q` and `a (q + 1)`, and all its critical points
lie on the compact Morse–Bott submanifold `i : S → M` of constant index `r`. Then on the first
page (`page 2` in the cohomological indexing) of `TauCeti.filteredSpaceSpectralSequence`, the
object at `(p, q)` with `p + q = -n` is isomorphic to `Hₙ(ν⁻, ν⁻₀; R)`. -/
theorem nonempty_filteredSpaceSpectralSequence_page_two_X_iso_thomPair
    (h : i.IsNondegenerateCriticalSubmanifold f) (hfs : ContMDiff I 𝓘(ℝ) ∞ f)
    {a : ℤ → ℝ} (ha : Monotone a) {c : ℝ} (hc : ∀ s, f (i s) = c)
    (hdim : finrank ℝ P = finrank ℝ E - finrank ℝ E')
    (g : letI := i.normalSpaceFiberBundle hn hdim
      letI := i.normalSpaceVectorBundle hn hdim
      ContMDiffRiemannianMetric J ∞ P fun s ↦ i.NormalSpace s hn) {r : ℕ}
    (hr : ∀ s, manifoldMorseIndex I f (i s) = r)
    (pq : ℤ × ℤ) (m : ℕ) (hdeg : pq.1 + pq.2 = -m)
    (hac : a pq.2 < c) (hcb : c < a (pq.2 + 1))
    (hcomp : IsCompact (f ⁻¹' Icc (a pq.2) (a (pq.2 + 1))))
    (hcrit : criticalPoints I f ∩ f ⁻¹' Icc (a pq.2) (a (pq.2 + 1)) ⊆ range i)
    {A : Type v} [Category.{w} A] [HasCoproducts.{u} A] [Abelian A] (R : A) :
    letI := i.normalSpaceFiberBundle hn hdim
    letI := i.normalSpaceVectorBundle hn hdim
    letI := subbundleTopology P (F' := Fin r → ℝ) (h.negativeNormalSpace hn g.toRiemannianMetric)
    Nonempty (((filteredSpaceSpectralSequence (Y := TopCat.of M) R
        ((sublevel_mono f).comp ha)).page 2).X pq ≅
      (thomPair (Fin r → ℝ)
        (fun s ↦ h.negativeNormalSpace hn g.toRiemannianMetric s)).singularHomology R m) := by
  let := i.normalSpaceFiberBundle hn hdim
  let := i.normalSpaceVectorBundle hn hdim
  let := subbundleTopology P (F' := Fin r → ℝ) (h.negativeNormalSpace hn g.toRiemannianMetric)
  obtain ⟨e⟩ := h.nonempty_singularHomology_sublevelPair_iso_thomPair hn hfs hc hdim g hr hac hcb
    hcomp hcrit R m
  exact ⟨filteredSpaceSpectralSequenceFirstPageXIso (Y := TopCat.of M) R
    ((sublevel_mono f).comp ha) pq pq.2 (pq.2 + 1) rfl rfl _ rfl m hdeg ≪≫ e⟩

/-- **Vanishing below the index on the first page of the sublevel filtration spectral sequence.**
Under the hypotheses of `nonempty_filteredSpaceSpectralSequence_page_two_X_iso_thomPair`, if
`m < r` (with `pq.1 + pq.2 = -m`), the object at `pq` on the first page vanishes. -/
theorem isZero_filteredSpaceSpectralSequence_page_two_X_of_lt_index
    (h : i.IsNondegenerateCriticalSubmanifold f) (hfs : ContMDiff I 𝓘(ℝ) ∞ f)
    {a : ℤ → ℝ} (ha : Monotone a) {c : ℝ} (hc : ∀ s, f (i s) = c)
    {r : ℕ} (hr : ∀ s, manifoldMorseIndex I f (i s) = r)
    (pq : ℤ × ℤ) {m : ℕ} (hdeg : pq.1 + pq.2 = -m) (hmr : m < r)
    (hac : a pq.2 < c) (hcb : c < a (pq.2 + 1))
    (hcomp : IsCompact (f ⁻¹' Icc (a pq.2) (a (pq.2 + 1))))
    (hcrit : criticalPoints I f ∩ f ⁻¹' Icc (a pq.2) (a (pq.2 + 1)) ⊆ range i)
    {A : Type v} [Category.{w} A] [HasCoproducts.{u} A] [Abelian A] (R : A) :
    IsZero (((filteredSpaceSpectralSequence (Y := TopCat.of M) R
      ((sublevel_mono f).comp ha)).page 2).X pq) :=
  (h.isZero_singularHomology_sublevelPair_of_lt_index hfs hc hr hac hcb hcomp hcrit R hmr).of_iso
    (filteredSpaceSpectralSequenceFirstPageXIso (Y := TopCat.of M) R
      ((sublevel_mono f).comp ha) pq pq.2 (pq.2 + 1) rfl rfl _ rfl m hdeg)

end ThomPair

end SmoothEmbedding.IsNondegenerateCriticalSubmanifold

end TauCeti
