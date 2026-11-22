/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.FilteredSpace.Basic
public import TauCeti.Geometry.Manifold.Morse.Bott.Inequalities
public import TauCeti.Geometry.Manifold.Morse.Bott.Thom.Class
import TauCeti.Algebra.Homology.SpectralSequence.Degeneration

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
page from the homology of the critical submanifolds, shifted by their indices. When each `ν⁻ j`
has a Thom class with coefficients in a commutative ring `K`, for instance when it is oriented, the
object at `(p, q)` with coefficients in `K` is `∐ H_{n - r j}(S j; K)` over the pieces on the level
`c` with `r j ≤ n` (`nonempty_filteredSpaceSpectralSequence_page_two_X_iso_sigma_of_isThomClass`,
in the namespace `TauCeti.IsMorseBottFamily`). An oriented bundle has a Thom class over every `K`
(`TauCeti.VectorBundleOrientation.exists_isThomClass`), so for oriented negative normal bundles
this computes the first page over `ℤ`, as in Cohen, Iga and Norbury, Theorem 15.6.

The identification of one band needs neither a global Morse–Bott family nor a compact manifold:
it holds whenever the band `f⁻¹[a q, a (q + 1)]` is compact and its critical points lie on finitely
many disjoint compact nondegenerate critical submanifolds on a level `c` inside it
(`nonempty_filteredSpaceSpectralSequence_page_two_X_iso_iUnion_negativeDiscBundle`, in the
namespace `TauCeti.SmoothEmbedding`).

With coefficients in a field `K` of characteristic two, such as `𝔽₂`, the first page is computed
by the critical submanifolds themselves. If the piece `S j` has index `r j`, the object at `(p, q)`
with `p + q = -n` has dimension `∑ b_{n - r j}(S j; K)` over the pieces in the `q`th band of index
at most `n` (`TauCeti.IsMorseBottFamily.finrank_filteredSpaceSpectralSequence_page_two_X`): each
negative disc bundle contributes the homology of its Thom pair, which over `K` is that of its base
shifted by its rank. So the first page records the Morse–Bott counts `cₙ = ∑ⱼ b_{n - r j}(S j; K)`
band by band. If of any two consecutive counts `cₙ` and `cₙ₊₁` one vanishes, every differential on
every page of the spectral sequence of a critical-band cut vanishes
(`IsMorseBottFamily.filteredSpaceSpectralSequence_page_d_eq_zero_of_forall_eq_zero_or_eq_zero`),
since a differential raises the total degree by one. The first page then survives unchanged to the
homology of `M`: the graded piece `F_{q+1} Hₙ(M) / F_q Hₙ(M)` of the filtration of `Hₙ(M; K)` by
the images of the homology of the sublevels has the dimension of the contribution of the pieces in
the `q`th band
(`TauCeti.IsMorseBottFamily.finrank_cokernel_abutmentFiltrationMap_of_forall_eq_zero_or_eq_zero`).
This refines the lacunary principle
`TauCeti.IsMorseBottFamily.bettiNumber_eq_sum_of_forall_eq_zero_or_eq_zero`, which records only the
total dimensions `bₙ(M; K) = cₙ`. For a Morse function every piece is a point and these are the
corresponding statements `TauCeti.IsMorse.finrank_filteredSpaceSpectralSequence_page_two_X`,
`TauCeti.IsMorse.filteredSpaceSpectralSequence_page_d_eq_zero_of_forall_ne_add_one` and
`TauCeti.IsMorse.nonempty_cokernel_abutmentFiltrationMap_iso_sigma_of_forall_ne_add_one` over
`𝔽₂`. The degeneration and the graded pieces are deduced, in both cases, from the statements for
any cohomological spectral sequence
(`CategoryTheory.SpectralSequence.page_d_eq_zero_of_isZero_or_isZero`) and for any finite
filtration of a space
(`TauCeti.nonempty_cokernel_abutmentFiltrationMap_iso_page_two_X_of_isZero_or_isZero`).

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
* `finrank_filteredSpaceSpectralSequence_page_two_X`: in characteristic two, the dimension of the
  first page at a critical band is the sum of the shifted Betti numbers of the pieces in the band.
* `filteredSpaceSpectralSequence_page_d_eq_zero_of_forall_eq_zero_or_eq_zero`: degeneration when
  no two consecutive Morse–Bott counts in characteristic two are both nonzero.
* `finrank_cokernel_abutmentFiltrationMap_of_forall_eq_zero_or_eq_zero`: in that case, the
  dimensions of the graded pieces of the homology of `M`.
* `nonempty_filteredSpaceSpectralSequence_page_two_X_iso_sigma_of_isThomClass`: when the negative
  normal bundles have Thom classes over a commutative ring `K`, the first page with coefficients in
  `K` is the coproduct of the homologies `H_{n - r j}(S j; K)` of the pieces on the level `c`.

## References

* R. Bott, *Nondegenerate critical manifolds*, Annals of Mathematics 60 (1954), 248–261.
* R. L. Cohen, K. Iga and P. Norbury, *Topics in Morse theory: lecture notes*, 2006,
  Theorems 15.4 and 15.6.
* R. Bott, *Lectures on Morse theory, old and new*, Bulletin of the American Mathematical
  Society 7 (1982), 331–358, Section 1.
-/

public section

noncomputable section

open AlgebraicTopology Bundle CategoryTheory Function Limits Set
open scoped ContDiff Manifold

universe u v w

namespace TauCeti

section Attachment

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

end Attachment

/-! ### The first page with coefficients of characteristic two -/

section ModTwo

open _root_.Module (finrank)

variable {E : Type} {H : Type*} {M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  [SecondCountableTopology M] [CompactSpace M]
  {ι : Type*} [Fintype ι] {E' H' : ι → Type*} {S : ι → Type}
  [∀ j, NormedAddCommGroup (E' j)] [∀ j, NormedSpace ℝ (E' j)] [∀ j, FiniteDimensional ℝ (E' j)]
  [∀ j, TopologicalSpace (H' j)] {J : ∀ j, ModelWithCorners ℝ (E' j) (H' j)}
  [∀ j, TopologicalSpace (S j)] [∀ j, ChartedSpace (H' j) (S j)] [∀ j, IsManifold (J j) ∞ (S j)]
  [∀ j, (J j).Boundaryless] {f : M → ℝ} {i : ∀ j, SmoothEmbedding (J j) I ∞ (S j) M}
  {a : ℤ → ℝ}

namespace IsMorseBottFamily

omit [FiniteDimensional ℝ E] [I.Boundaryless] [IsManifold I ∞ M] [T2Space M]
  [SecondCountableTopology M] [CompactSpace M] [Fintype ι] [∀ j, FiniteDimensional ℝ (E' j)]
  [∀ j, IsManifold (J j) ∞ (S j)] [∀ j, (J j).Boundaryless] in
/-- In a band `f⁻¹[s, t]` whose only critical value is `c`, strictly between `s` and `t`, a piece
of a Morse–Bott family lies in `f⁻¹(s, t]` exactly when it lies on the level `c`. -/
private theorem forall_mem_Ioc_iff_forall_eq (h : IsMorseBottFamily i f) {s t c : ℝ}
    (hc : c ∈ Ioo s t) (hcrit : ∀ x ∈ criticalPoints I f, f x ∈ Icc s t → f x = c) (j : ι) :
    (∀ x, f (i j x) ∈ Ioc s t) ↔ ∀ x, f (i j x) = c :=
  ⟨fun hj x ↦ hcrit _ ((h.isNondegenerateCriticalSubmanifold j).mem_criticalPoints x)
    (Ioc_subset_Icc_self (hj x)), fun hj x ↦ hj x ▸ Ioo_subset_Ioc_self hc⟩

variable (h : IsMorseBottFamily i f) {r : ι → ℕ} (hr : ∀ j s, manifoldMorseIndex I f (i j s) = r j)
  (K : Type) [Field K] (h2 : (2 : K) = 0)

include h hr h2

open scoped Classical in
/-- **The first page of the critical-band spectral sequence of a Morse–Bott function in
characteristic two.** Let the family `i j : S j → M` exhibit `f` as a Morse–Bott function on a
compact boundaryless manifold, the piece `S j` having index `r j`, and let `K` be a field of
characteristic two, such as `ZMod 2`. Let `a : ℤ → ℝ` be monotone and let
`f⁻¹[a q, a (q + 1)]` be a critical band of `f`. On the first page of the spectral sequence of the
filtration `q ↦ {f ≤ a q}` with coefficients in `K`, the object at `(p, q)` with `p + q = -n` has
dimension `∑ b_{n - r j}(S j; K)`, the sum running over the pieces with values in
`(a q, a (q + 1)]` of index at most `n`. -/
theorem finrank_filteredSpaceSpectralSequence_page_two_X (ha : Monotone a) {q : ℤ}
    (hband : IsCriticalBand I f (a q) (a (q + 1))) (pq : ℤ × ℤ) (hq : pq.2 = q) (n : ℕ)
    (hpq : pq.1 + pq.2 = -n) :
    finrank K (((filteredSpaceSpectralSequence (Y := TopCat.of M) (ModuleCat.of K K)
        ((sublevel_mono f).comp ha)).page 2).X pq : ModuleCat K) =
      ∑ j with (∀ s, f (i j s) ∈ Ioc (a q) (a (q + 1))) ∧ r j ≤ n,
        bettiNumber K (S j) (n - r j) := by
  obtain ⟨c, hc, hcrit⟩ := hband.exists_mem_Ioo_forall_eq
  subst hq
  rw [(filteredSpaceSpectralSequenceFirstPageXIso (Y := TopCat.of M) (ModuleCat.of K K)
    ((sublevel_mono f).comp ha) pq pq.2 (pq.2 + 1) rfl rfl _ rfl n hpq).toLinearEquiv.finrank_eq,
    h.finrank_singularHomology_sublevelPair_eq_sum K h2 hr hc.1 hc.2 hcrit n]
  simp only [h.forall_mem_Ioc_iff_forall_eq hc hcrit]

open scoped Classical in
/-- A nonzero object on the first page at `(p, q)` lies in a total degree `p + q = -n` whose
Morse–Bott count `cₙ = ∑ b_{n - r j}(S j; K)` is nonzero. -/
private theorem exists_sum_ne_zero_of_not_isZero_page_two_X (ha : Monotone a) {pq : ℤ × ℤ}
    (hband : IsCriticalBand I f (a pq.2) (a (pq.2 + 1)))
    (hne : ¬IsZero (((filteredSpaceSpectralSequence (Y := TopCat.of M) (ModuleCat.of K K)
      ((sublevel_mono f).comp ha)).page 2).X pq)) :
    ∃ n : ℕ, pq.1 + pq.2 = -n ∧ ∑ j with r j ≤ n, bettiNumber K (S j) (n - r j) ≠ 0 := by
  by_cases hpos : 0 < pq.1 + pq.2
  · exact absurd (isZero_filteredSpaceSpectralSequence_page_two_X _ _ pq hpos) hne
  obtain ⟨n, hn⟩ := Int.exists_eq_neg_ofNat (not_lt.1 hpos)
  refine ⟨n, hn, fun hzero ↦ hne ?_⟩
  obtain ⟨c, hc, hcrit⟩ := hband.exists_mem_Ioo_forall_eq
  -- The first page is the homology of the band, which is finite-dimensional.
  let e := filteredSpaceSpectralSequenceFirstPageXIso (Y := TopCat.of M) (ModuleCat.of K K)
    ((sublevel_mono f).comp ha) pq pq.2 (pq.2 + 1) rfl rfl _ rfl n hn
  have := finite_singularHomology_sublevelPair_of_criticalValue (ModuleCat.of K K) h.contMDiff
    h.contMDiff.continuous.isProperMap hc.1 hc.2 hcrit n
  have := Module.Finite.equiv e.symm.toLinearEquiv
  -- Its dimension is a part of the vanishing count.
  have hle : finrank K (((filteredSpaceSpectralSequence (Y := TopCat.of M) (ModuleCat.of K K)
      ((sublevel_mono f).comp ha)).page 2).X pq : ModuleCat K) ≤
        ∑ j with r j ≤ n, bettiNumber K (S j) (n - r j) := by
    rw [h.finrank_filteredSpaceSpectralSequence_page_two_X hr K h2 ha hband pq rfl n hn]
    refine Finset.sum_le_sum_of_subset fun j hj ↦ ?_
    simp only [Finset.mem_filter] at hj ⊢
    exact ⟨hj.1, hj.2.2⟩
  rw [hzero, Nat.le_zero, Module.finrank_zero_iff] at hle
  exact ModuleCat.isZero_of_subsingleton _

variable (hlac : ∀ n, ∑ j with r j ≤ n, bettiNumber K (S j) (n - r j) = 0 ∨
  ∑ j with r j ≤ n + 1, bettiNumber K (S j) (n + 1 - r j) = 0)
include hlac

/-- If of any two consecutive Morse–Bott counts in characteristic two one vanishes, of two
positions of the first page whose total degrees differ by one, at least one carries the zero
object. -/
private theorem isZero_or_isZero_page_two_X (ha : IsCriticalBandCut I f a) {pq pq' : ℤ × ℤ}
    (hdeg : pq.1 + pq.2 + 1 = pq'.1 + pq'.2) :
    IsZero (((filteredSpaceSpectralSequence (Y := TopCat.of M) (ModuleCat.of K K)
        ((sublevel_mono f).comp ha.monotone)).page 2).X pq) ∨
      IsZero (((filteredSpaceSpectralSequence (Y := TopCat.of M) (ModuleCat.of K K)
        ((sublevel_mono f).comp ha.monotone)).page 2).X pq') := by
  by_contra hne
  rw [not_or] at hne
  obtain ⟨n, hn, hcn⟩ := h.exists_sum_ne_zero_of_not_isZero_page_two_X hr K h2 ha.monotone
    (ha.isCriticalBand _) hne.1
  obtain ⟨n', hn', hcn'⟩ := h.exists_sum_ne_zero_of_not_isZero_page_two_X hr K h2 ha.monotone
    (ha.isCriticalBand _) hne.2
  obtain rfl : n = n' + 1 := by lia
  exact (hlac n').elim hcn' hcn

/-- **Lacunary degeneration in characteristic two.** Let the family `i j : S j → M` exhibit `f` as a
Morse–Bott function on a compact boundaryless manifold, the piece `S j` having index `r j`, let
`K` be a field of characteristic two, such as `ZMod 2`, and let `a : ℤ → ℝ` be a critical-band
cut of `f`. Write `cₙ = ∑ b_{n - r j}(S j; K)` over the pieces of index at most `n`. If of any two
consecutive counts `cₙ` and `cₙ₊₁` one vanishes, every differential on every page of the spectral
sequence of the filtration `q ↦ {f ≤ a q}` with coefficients in `K` vanishes. -/
theorem filteredSpaceSpectralSequence_page_d_eq_zero_of_forall_eq_zero_or_eq_zero
    (ha : IsCriticalBandCut I f a) (r' : ℤ) (hr' : 2 ≤ r') (pq pq' : ℤ × ℤ) :
    ((filteredSpaceSpectralSequence (Y := TopCat.of M) (ModuleCat.of K K)
      ((sublevel_mono f).comp ha.monotone)).page r').d pq pq' = 0 :=
  SpectralSequence.page_d_eq_zero_of_isZero_or_isZero _
    (fun _ _ ↦ h.isZero_or_isZero_page_two_X hr K h2 hlac ha) r' hr' pq pq'

open scoped Classical in
/-- **The graded homology of a lacunary Morse–Bott function in characteristic two.** Let the family
`i j : S j → M` exhibit `f` as a Morse–Bott function on a compact boundaryless manifold, the piece
`S j` having index `r j`, let `K` be a field of characteristic two, such as `ZMod 2`, and let
`a : ℤ → ℝ` be a critical-band cut of `f` starting below and ending above all values of `f`.
Filter `Hₙ(M; K)` by the images `F_q Hₙ` of the homology of the sublevels `{f ≤ a q}`. If of any
two consecutive counts `cₙ = ∑ b_{n - r j}(S j; K)` one vanishes, the graded piece
`F_{q+1} Hₙ / F_q Hₙ` has dimension `∑ b_{n - r j}(S j; K)` over the pieces with values in
`(a q, a (q + 1)]` of index at most `n`. The graded piece is written as the cokernel of the
inclusion `F_q Hₙ ⟶ F_{q+1} Hₙ` of the filtration of the abutment of the spectral sequence, which
is `Hₙ(M)` in total degree `p + q = -n` (`TauCeti.chainFiltrationAbutmentIso`). -/
theorem finrank_cokernel_abutmentFiltrationMap_of_forall_eq_zero_or_eq_zero
    (ha : IsCriticalBandCut I f a) {q₀ q₁ : ℤ} (hq₀ : ∀ x, a q₀ < f x) (hq₁ : ∀ x, f x ≤ a q₁)
    (pq : ℤ × ℤ) (n : ℕ) (hn : pq.1 + pq.2 = -n) :
    finrank K (cokernel ((filteredSpaceSpectralObject (Y := TopCat.of M) (ModuleCat.of K K)
        ((sublevel_mono f).comp ha.monotone)).abutmentFiltrationMap pq.2 (pq.1 + pq.2)) :
        ModuleCat K) =
      ∑ j with (∀ s, f (i j s) ∈ Ioc (a pq.2) (a (pq.2 + 1))) ∧ r j ≤ n,
        bettiNumber K (S j) (n - r j) := by
  rw [← h.finrank_filteredSpaceSpectralSequence_page_two_X hr K h2 ha.monotone
    (ha.isCriticalBand _) pq rfl n hn]
  obtain ⟨e⟩ := nonempty_cokernel_abutmentFiltrationMap_iso_page_two_X_of_isZero_or_isZero
    (Y := TopCat.of M) (ModuleCat.of K K) ((sublevel_mono f).comp ha.monotone)
    (eq_empty_of_forall_notMem fun x hx ↦ (hq₀ x).not_ge hx) (eq_univ_of_forall hq₁)
    (fun _ hpq' ↦ hpq'.elim (h.isZero_or_isZero_page_two_X hr K h2 hlac ha)
      fun h' ↦ (h.isZero_or_isZero_page_two_X hr K h2 hlac ha h').symm)
  exact e.toLinearEquiv.finrank_eq

end IsMorseBottFamily

end ModTwo

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

section ThomClass

variable {E M : Type} {H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] {ι : Type*} {E' H' P : ι → Type*}
  {S : ι → Type} [∀ j, NormedAddCommGroup (E' j)] [∀ j, NormedSpace ℝ (E' j)]
  [∀ j, FiniteDimensional ℝ (E' j)] [∀ j, TopologicalSpace (H' j)]
  {J : ∀ j, ModelWithCorners ℝ (E' j) (H' j)} [∀ j, TopologicalSpace (S j)]
  [∀ j, ChartedSpace (H' j) (S j)] [∀ j, IsManifold (J j) ∞ (S j)]
  [∀ j, NormedAddCommGroup (P j)] [∀ j, NormedSpace ℝ (P j)] [∀ j, FiniteDimensional ℝ (P j)]
  {f : M → ℝ} {i : ∀ j, SmoothEmbedding (J j) I ∞ (S j) M} (hn : (∞ : ℕ∞ω) ≠ 0)

/-- **The first page of the critical-band spectral sequence of a Morse–Bott function from Thom
classes of the negative normal bundles.** Let the family `i j : S j → M` exhibit `f` as a
Morse–Bott function (`TauCeti.IsMorseBottFamily`) on a compact Hausdorff second-countable
boundaryless manifold, with pieces modelled on boundaryless models, and let `K` be a commutative
ring. Suppose that for each piece `S j` the negative normal bundle, relative to some smooth fibre
metric on the normal bundle, has rank `r j` and a Thom class with coefficients in `K`, as it does
over every `K`, for instance `ℤ`, when it is oriented
(`TauCeti.VectorBundleOrientation.exists_isThomClass`). Let `a : ℤ → ℝ` be monotone, and let
`a q < c < a (q + 1)` be such that every critical point of `f` with value in `[a q, a (q + 1)]`
lies on the level `c`.

Then on the first page of the spectral sequence of the filtration `q ↦ {f ≤ a q}` with
coefficients in `K`, the object at `(p, q)` with `p + q = -n` is `∐ H_{n - r j}(S j; K)`, the
coproduct running over the pieces on the level `c` with `r j ≤ n`. -/
theorem
    IsMorseBottFamily.nonempty_filteredSpaceSpectralSequence_page_two_X_iso_sigma_of_isThomClass
    [T2Space M] [SecondCountableTopology M] [CompactSpace M] [∀ j, (J j).Boundaryless]
    (h : IsMorseBottFamily i f) {a : ℤ → ℝ} (ha : Monotone a) {q : ℤ} {c : ℝ}
    (hc : c ∈ Ioo (a q) (a (q + 1)))
    (hcrit : ∀ x ∈ criticalPoints I f, f x ∈ Icc (a q) (a (q + 1)) → f x = c)
    (hdim : ∀ j, Module.finrank ℝ (P j) = Module.finrank ℝ E - Module.finrank ℝ (E' j))
    {r : ι → ℕ} {K : Type} [CommRing K]
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
    (pq : ℤ × ℤ) (hq : pq.2 = q) (n : ℕ) (hpq : pq.1 + pq.2 = -n) :
    -- The pieces are finitely many, so the coproduct exists.
    haveI := h.finite
    Nonempty (((filteredSpaceSpectralSequence (Y := TopCat.of M) (ModuleCat.of K K)
        ((sublevel_mono f).comp ha)).page 2).X pq ≅
      ∐ fun j : {j // (∀ s, f (i j s) = c) ∧ r j ≤ n} ↦
        ((singularHomologyFunctor (ModuleCat.{0} K) (n - r j)).obj (ModuleCat.of K K)).obj
          (TopCat.of (S j))) := by
  subst hq
  obtain ⟨e⟩ := h.nonempty_singularHomology_sublevelPair_iso_sigma_of_isThomClass hn hdim hK
    hc.1 hc.2 hcrit n
  exact ⟨filteredSpaceSpectralSequenceFirstPageXIso (Y := TopCat.of M) (ModuleCat.of K K)
    ((sublevel_mono f).comp ha) pq pq.2 (pq.2 + 1) rfl rfl _ rfl n hpq ≪≫ e⟩

end ThomClass

end TauCeti
