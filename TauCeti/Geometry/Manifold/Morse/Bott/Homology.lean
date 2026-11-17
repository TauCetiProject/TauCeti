/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Morse.Bott.DiscBundle
public import TauCeti.Geometry.Manifold.Morse.Deformation.Homology

/-!
# Relative homology across the level of a compact Morse–Bott submanifold

Let `i : S → M` be a compact nondegenerate critical submanifold of a smooth function `f`, on the
level `f = c`, and let `g` be a smooth fibre metric on its normal bundle. Write `M_t = {f ≤ t}`.
Crossing the level attaches the negative disc bundle: for a Morse–Bott normal form `Θ` near the
zero section of the normal bundle and all small `ε > 0` such that the band `f⁻¹[c-ε, c+ε]` is
compact and all its critical points lie on `i`, the sublevel `M_{c+ε}` strong deformation
retracts onto `M_{c-ε} ∪ Θ(D_ε)`, where `D_ε` is the negative disc bundle of size `ε`
(`IsNondegenerateCriticalSubmanifold.exists_sublevel_union_negativeDiscBundle_deformation`, in
the namespace `TauCeti.SmoothEmbedding`).

This file reads that attachment in relative singular homology. The image `Θ(D_ε)` lies in the
critical sublevel `M_c`, since the normal Hessian is negative on the negative normal spaces, and
the deformation fixes `M_{c-ε} ∪ Θ(D_ε)`. So, for the same `ε`, the inclusion of pairs

`(M_{c-ε} ∪ Θ(D_ε), M_{c-ε}) ⟶ (M_{c+ε}, M_{c-ε})`

induces isomorphisms on relative singular homology, with coefficients in any preadditive category
with coproducts and homology (`exists_isIso_singularHomologyMap_negativeDiscBundle`).

The width `ε` can be replaced by arbitrary regular levels: if `a < c < b`, the band `f⁻¹[a, b]` is
compact and its critical points lie on the submanifold, then `c` is its only critical value, so
`Hₙ(M_b, M_a)` is isomorphic to `Hₙ(M_{c+ε}, M_{c-ε})`
(`TauCeti.singularHomologySublevelPairIsoOfCriticalValue`), hence to the relative homology of the
lower sublevel with the negative disc bundle attached
(`nonempty_singularHomology_sublevelPair_iso_negativeDiscBundle`). Groups `Hₙ(M_b, M_a)` of this
kind, between consecutive regular levels, are the first-page terms of the spectral sequence of the
filtration of a manifold by the sublevels of `f`; this identifies the contribution of a compact
Morse–Bott critical submanifold through its negative disc bundle. For an isolated nondegenerate
critical point the base is a point and the disc bundle is a cell of dimension the Morse index.

A level may hold finitely many compact critical submanifolds `i j` with disjoint images, and
crossing it attaches all their negative disc bundles at once
(`TauCeti.SmoothEmbedding.exists_sublevel_union_iUnion_negativeDiscBundle_deformation`). Both
statements are proved for such a family: the inclusion of
`({f ≤ c - ε} ∪ ⋃ j, Θ j (D j ε), {f ≤ c - ε})` into `({f ≤ c + ε}, {f ≤ c - ε})` induces
isomorphisms on relative singular homology, and `Hₙ(M_b, M_a)` is the relative homology of this
attachment when the band `f⁻¹[a, b]` is compact and its critical points lie on the family. The
statements for one submanifold are the case of a single index. For a Morse–Bott function on a
compact manifold (`TauCeti.IsMorseBottFamily`) the family is that of its critical submanifolds on
the level `c`, and the band condition holds as soon as `c` is the only critical value in `[a, b]`.

## Main results

In the namespace `TauCeti.SmoothEmbedding`:

* `exists_isIso_singularHomologyMap_iUnion_negativeDiscBundle`: for finitely many compact
  Morse–Bott submanifolds on a level, the inclusion of the lower sublevel with their negative disc
  bundles attached into the upper sublevel, relative to the lower sublevel, induces isomorphisms
  on relative singular homology.
* `nonempty_singularHomology_sublevelPair_iso_iUnion_negativeDiscBundle`: the relative homology of
  a compact band whose critical points lie on such a family is that of the lower sublevel with
  their negative disc bundles attached.

In the namespace `TauCeti.SmoothEmbedding.IsNondegenerateCriticalSubmanifold`:

* `exists_isIso_singularHomologyMap_negativeDiscBundle`: the inclusion of the lower sublevel with
  the negative disc bundle attached into the upper sublevel, relative to the lower sublevel,
  induces isomorphisms on relative singular homology.
* `nonempty_singularHomology_sublevelPair_iso_negativeDiscBundle`: the relative homology of the
  sublevels at two regular levels around the critical level is the relative homology of the lower
  sublevel with the negative disc bundle attached.

In the namespace `TauCeti.IsMorseBottFamily`:

* `nonempty_singularHomology_sublevelPair_iso_iUnion_negativeDiscBundle`: the relative homology of
  a band of a Morse–Bott function with one critical value is that of the lower sublevel with the
  negative disc bundles of the critical submanifolds on that level attached.

## References

* R. Bott, *Nondegenerate critical manifolds*, Annals of Mathematics 60 (1954), 248–261.
* R. L. Cohen, K. Iga and P. Norbury, *Topics in Morse theory: lecture notes*, 2006,
  Theorem 15.4.
-/

public section

noncomputable section

open Bundle CategoryTheory Function Limits Set
open scoped ContDiff Manifold

universe u v w

namespace TauCeti

namespace SmoothEmbedding

section Family

variable {E H : Type*} {M : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless] [TopologicalSpace M]
  [ChartedSpace H M] [IsManifold I ∞ M] {ι : Type*} {E' H' S P : ι → Type*}
  [∀ j, NormedAddCommGroup (E' j)] [∀ j, NormedSpace ℝ (E' j)] [∀ j, FiniteDimensional ℝ (E' j)]
  [∀ j, TopologicalSpace (H' j)] {J : ∀ j, ModelWithCorners ℝ (E' j) (H' j)}
  [∀ j, TopologicalSpace (S j)] [∀ j, ChartedSpace (H' j) (S j)] [∀ j, IsManifold (J j) ∞ (S j)]
  [∀ j, NormedAddCommGroup (P j)] [∀ j, NormedSpace ℝ (P j)] [∀ j, FiniteDimensional ℝ (P j)]
  {f : M → ℝ} {i : ∀ j, SmoothEmbedding (J j) I ∞ (S j) M} (hn : (∞ : ℕ∞ω) ≠ 0)

/-- **The relative homology across a level of finitely many compact Morse–Bott submanifolds is
carried by their negative disc bundles.** Let `i j : S j → M`, for `j` in a finite index type, be
nondegenerate critical submanifolds of a smooth function `f` on a Hausdorff, second-countable,
finite-dimensional, boundaryless manifold, each modelled on its own boundaryless model, with `S j`
compact and nonempty, pairwise disjoint images and `f = c` along each of them. Let `g j` be a
smooth fibre metric on the normal bundle of `i j`.

Then there are smooth partial diffeomorphisms `Θ j` from the total spaces of the normal bundles to
`M`, each defined on a neighbourhood of the zero section and sending it to `i j`, which put `f` in
the Morse–Bott normal form `f (Θ j v) = c + ½ Hessₛ (v, v)`, and an `ε₀ > 0` with the following
property. Let `0 < ε < ε₀` be such that the band `f⁻¹[c - ε, c + ε]` is compact and all its
critical points lie on the submanifolds. Then each negative disc bundle `D j ε` relative to `g j`
lies in the source of `Θ j`, the set `{f ≤ c - ε} ∪ ⋃ j, Θ j (D j ε)` lies in `{f ≤ c + ε}`, and
the inclusion of pairs `({f ≤ c - ε} ∪ ⋃ j, Θ j (D j ε), {f ≤ c - ε}) ⟶ ({f ≤ c + ε}, {f ≤ c - ε})`
induces isomorphisms on relative singular homology, in every degree and for every coefficient
object. -/
theorem exists_isIso_singularHomologyMap_iUnion_negativeDiscBundle [T2Space M]
    [SecondCountableTopology M] [Finite ι] [∀ j, (J j).Boundaryless] [∀ j, CompactSpace (S j)]
    [∀ j, Nonempty (S j)] (h : ∀ j, (i j).IsNondegenerateCriticalSubmanifold f)
    (hfs : ContMDiff I 𝓘(ℝ) ∞ f) {c : ℝ} (hc : ∀ j s, f (i j s) = c)
    (hd : Pairwise (Disjoint on fun j ↦ range (i j)))
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
      (∀ j, ∀ x ∈ (Θ j).source, f (Θ j x) = c + 2⁻¹ * (h j).normalHessian hn x.proj x.2 x.2) ∧
      ∃ ε₀ > 0, ∀ ε ∈ Ioo 0 ε₀, IsCompact (f ⁻¹' Icc (c - ε) (c + ε)) →
        criticalPoints I f ∩ f ⁻¹' Icc (c - ε) (c + ε) ⊆ ⋃ j, range (i j) →
        (∀ j, (h j).negativeDiscBundle hn (P j) (g j).toRiemannianMetric ε ⊆ (Θ j).source) ∧
        ∃ hA : {y | f y ≤ c - ε} ∪
            ⋃ j, Θ j '' (h j).negativeDiscBundle hn (P j) (g j).toRiemannianMetric ε ⊆
              {y | f y ≤ c + ε},
          ∀ {A : Type v} [Category.{w} A] [HasCoproducts.{u} A] [Preadditive A]
            [CategoryWithHomology A] (R : A) (n : ℕ),
            IsIso ((TopPair.ofInclusion (X := TopCat.of M) (subset_union_left :
                {y | f y ≤ c - ε} ⊆ {y | f y ≤ c - ε} ∪
                  ⋃ j, Θ j '' (h j).negativeDiscBundle hn (P j) (g j).toRiemannianMetric ε)
              ).singularHomologyMap (TopPair.ofInclusionMap (Y := TopCat.of M) _
                (subset_union_left.trans hA) (ContinuousMap.inclusion hA) fun _ hx ↦ hx) R n) := by
  let : ∀ j, FiberBundle (P j) fun s ↦ (i j).NormalSpace s hn :=
    fun j ↦ (i j).normalSpaceFiberBundle hn (hdim j)
  let : ∀ j, VectorBundle ℝ (P j) fun s ↦ (i j).NormalSpace s hn :=
    fun j ↦ (i j).normalSpaceVectorBundle hn (hdim j)
  obtain ⟨Θ, hΘz, hΘi, hΘf, ε₀, hε₀, hmain⟩ :=
    exists_sublevel_union_iUnion_negativeDiscBundle_deformation hn h hfs hc hd hdim g
  refine ⟨Θ, hΘz, hΘi, hΘf, ε₀, hε₀, fun ε hε hcompact hcrit ↦ ?_⟩
  obtain ⟨hD, r, -, ⟨G⟩⟩ := hmain ε hε hcompact hcrit
  -- The disc bundles lie in the critical sublevel, since the normal Hessian is negative on the
  -- negative normal spaces.
  have hA : {y | f y ≤ c - ε} ∪
      ⋃ j, Θ j '' (h j).negativeDiscBundle hn (P j) (g j).toRiemannianMetric ε ⊆
        {y | f y ≤ c + ε} := by
    rintro y (hy | hy)
    · exact sublevel_mono f (by linarith [hε.1]) hy
    · obtain ⟨j, x, hx, rfl⟩ := mem_iUnion.1 hy
      have hneg := ((h j).mem_negativeDiscBundle hn).1 hx |>.1
      have hle : (h j).normalHessian hn x.proj x.2 x.2 ≤ 0 := by
        rcases eq_or_ne x.2 0 with h0 | h0
        · simp [h0]
        · exact ((h j).normalHessian_apply_self_neg_of_mem_negativeNormalSpace hn _ hneg h0).le
      rw [mem_ofPred_eq, hΘf j x (hD j hx)]
      linarith [hε.1]
  -- The deformation retracts `{f ≤ c + ε}` onto `{f ≤ c - ε} ∪ ⋃ j, Θ j (D j ε)`, fixing it
  -- pointwise.
  exact ⟨hD, hA, fun {A} _ _ _ _ R n ↦
    TopPair.isIso_singularHomologyMap_ofInclusionMap_inclusion_of_homotopyRel (X := TopCat.of M)
      subset_union_left hA ((ContinuousMap.inclusion inter_subset_right).comp r)
      (G.cast (ContinuousMap.ext fun _ ↦ rfl) rfl) R n⟩

/-- **The relative homology of a critical band of finitely many compact Morse–Bott
submanifolds.** Let `i j : S j → M`, for `j` in a finite index type, be nondegenerate critical
submanifolds of a smooth function `f` on a Hausdorff, second-countable, finite-dimensional,
boundaryless manifold, each modelled on its own boundaryless model, with `S j` compact and
nonempty, pairwise disjoint images and `f = c` along each of them. Let `g j` be a smooth fibre
metric on the normal bundle of `i j`. Let `a < c < b` be such that the band `f⁻¹[a, b]` is compact
and all its critical points lie on the submanifolds.

Then there are smooth partial diffeomorphisms `Θ j` from the total spaces of the normal bundles to
`M`, each defined on a neighbourhood of the zero section and sending it to `i j`, which put `f` in
the Morse–Bott normal form `f (Θ j v) = c + ½ Hessₛ (v, v)`, and an `ε₀ > 0` such that for every
`0 < ε < ε₀` each negative disc bundle `D j ε` relative to `g j` lies in the source of `Θ j` and
the relative singular homology `Hₙ({f ≤ b}, {f ≤ a})` is isomorphic to
`Hₙ({f ≤ c - ε} ∪ ⋃ j, Θ j (D j ε), {f ≤ c - ε})`, in every degree and for every coefficient
object. -/
theorem nonempty_singularHomology_sublevelPair_iso_iUnion_negativeDiscBundle [T2Space M]
    [SecondCountableTopology M] [Finite ι] [∀ j, (J j).Boundaryless] [∀ j, CompactSpace (S j)]
    [∀ j, Nonempty (S j)] (h : ∀ j, (i j).IsNondegenerateCriticalSubmanifold f)
    (hfs : ContMDiff I 𝓘(ℝ) ∞ f) {a b c : ℝ} (hc : ∀ j s, f (i j s) = c)
    (hd : Pairwise (Disjoint on fun j ↦ range (i j))) (hac : a < c) (hcb : c < b)
    (hcompact : IsCompact (f ⁻¹' Icc a b))
    (hcrit : criticalPoints I f ∩ f ⁻¹' Icc a b ⊆ ⋃ j, range (i j))
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
      (∀ j, ∀ x ∈ (Θ j).source, f (Θ j x) = c + 2⁻¹ * (h j).normalHessian hn x.proj x.2 x.2) ∧
      ∃ ε₀ > 0, ∀ ε ∈ Ioo 0 ε₀,
        (∀ j, (h j).negativeDiscBundle hn (P j) (g j).toRiemannianMetric ε ⊆ (Θ j).source) ∧
        ∀ {A : Type v} [Category.{w} A] [Abelian A] [HasCoproducts.{u} A] (R : A) (n : ℕ),
          Nonempty ((sublevelPair f (hac.trans hcb).le).singularHomology R n ≅
            (TopPair.ofInclusion (X := TopCat.of M) (subset_union_left :
              {y | f y ≤ c - ε} ⊆ {y | f y ≤ c - ε} ∪
                ⋃ j, Θ j '' (h j).negativeDiscBundle hn (P j) (g j).toRiemannianMetric ε)
              ).singularHomology R n) := by
  let : ∀ j, FiberBundle (P j) fun s ↦ (i j).NormalSpace s hn :=
    fun j ↦ (i j).normalSpaceFiberBundle hn (hdim j)
  let : ∀ j, VectorBundle ℝ (P j) fun s ↦ (i j).NormalSpace s hn :=
    fun j ↦ (i j).normalSpaceVectorBundle hn (hdim j)
  obtain ⟨Θ, hΘz, hΘi, hΘf, ε₀, hε₀, hmain⟩ :=
    exists_isIso_singularHomologyMap_iUnion_negativeDiscBundle hn h hfs hc hd hdim g
  refine ⟨Θ, hΘz, hΘi, hΘf, min ε₀ (min (c - a) (b - c)),
    lt_min hε₀ (lt_min (by linarith) (by linarith)), fun ε hε ↦ ?_⟩
  obtain ⟨hε0, hεm⟩ := hε
  have hε₁ : ε < ε₀ := hεm.trans_le (min_le_left _ _)
  have hεa : ε < c - a := hεm.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hεb : ε < b - c := hεm.trans_le ((min_le_right _ _).trans (min_le_right _ _))
  have hε' : Icc (c - ε) (c + ε) ⊆ Icc a b := Icc_subset_Icc (by linarith) (by linarith)
  have hcompact' : IsCompact (f ⁻¹' Icc (c - ε) (c + ε)) :=
    hcompact.of_isClosed_subset (isClosed_Icc.preimage hfs.continuous) (preimage_mono hε')
  -- Every critical point of the band lies on a submanifold, hence on the level `c`.
  have hlev : ∀ x ∈ criticalPoints I f, f x ∈ Icc a b → f x = c := fun x hx hfx ↦ by
    obtain ⟨j, s, rfl⟩ := mem_iUnion.1 (hcrit ⟨hx, hfx⟩)
    exact hc j s
  obtain ⟨hD, _, hiso⟩ := hmain ε ⟨hε0, hε₁⟩ hcompact' fun x hx ↦ hcrit ⟨hx.1, hε' hx.2⟩
  refine ⟨hD, fun {A} _ _ _ R n ↦ ⟨singularHomologySublevelPairIsoOfCriticalValue hfs hac hcb
    (by linarith : c - ε < c) (by linarith : c < c + ε) hcompact hcompact' hlev
    (fun x hx hfx ↦ hlev x hx (hε' hfx)) R n ≪≫ (@asIso _ _ _ _ _ (hiso R n)).symm⟩⟩

end Family

variable {E H : Type*} {M : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless] [TopologicalSpace M]
  [ChartedSpace H M] [IsManifold I ∞ M] {E' H' S P : Type*} [NormedAddCommGroup E']
  [NormedSpace ℝ E'] [FiniteDimensional ℝ E'] [TopologicalSpace H'] {J : ModelWithCorners ℝ E' H'}
  [TopologicalSpace S] [ChartedSpace H' S] [IsManifold J ∞ S] [NormedAddCommGroup P]
  [NormedSpace ℝ P] [FiniteDimensional ℝ P] {f : M → ℝ} {i : SmoothEmbedding J I ∞ S M}
  (hn : (∞ : ℕ∞ω) ≠ 0)

namespace IsNondegenerateCriticalSubmanifold

/-- **The relative homology across the level of a Morse–Bott submanifold is carried by its
negative disc bundle.** Let `i : S → M` be a nondegenerate critical submanifold of a smooth
function `f` on a Hausdorff, second-countable, finite-dimensional, boundaryless manifold, with `S`
nonempty and `f = c` along `i`, and let `g` be a smooth fibre metric on its normal bundle.

Then there is a smooth partial diffeomorphism `Θ` from the total space of the normal bundle to
`M`, defined on a neighbourhood of the zero section and sending it to `i`, which puts `f` in the
Morse–Bott normal form `f (Θ v) = c + ½ Hessₛ (v, v)`, and an `ε₀ > 0` with the following
property. Let `0 < ε < ε₀` be such that the band `f⁻¹[c - ε, c + ε]` is compact and all its
critical points lie on `i`. Then the negative disc bundle `D_ε` relative to `g` lies in the source
of `Θ`, the set `{f ≤ c - ε} ∪ Θ(D_ε)` lies in `{f ≤ c + ε}`, and the inclusion of pairs
`({f ≤ c - ε} ∪ Θ(D_ε), {f ≤ c - ε}) ⟶ ({f ≤ c + ε}, {f ≤ c - ε})` induces isomorphisms on
relative singular homology, in every degree and for every coefficient object. Such an `ε` exists
only when `S` is compact, since the image of `i` is then the closed set of critical points of the
compact band. -/
theorem exists_isIso_singularHomologyMap_negativeDiscBundle [T2Space M]
    [SecondCountableTopology M] [J.Boundaryless] [Nonempty S]
    (h : i.IsNondegenerateCriticalSubmanifold f) (hfs : ContMDiff I 𝓘(ℝ) ∞ f) {c : ℝ}
    (hc : ∀ s, f (i s) = c) (hdim : Module.finrank ℝ P = Module.finrank ℝ E - Module.finrank ℝ E')
    (g : letI := i.normalSpaceFiberBundle hn hdim
      letI := i.normalSpaceVectorBundle hn hdim
      ContMDiffRiemannianMetric J ∞ P fun s ↦ i.NormalSpace s hn) :
    letI := i.normalSpaceFiberBundle hn hdim
    letI := i.normalSpaceVectorBundle hn hdim
    ∃ Θ : PartialDiffeomorph (J.prod 𝓘(ℝ, P)) I (TotalSpace P fun s ↦ i.NormalSpace s hn) M ∞,
      (∀ s, zeroSection P (fun s ↦ i.NormalSpace s hn) s ∈ Θ.source) ∧
      (∀ s, Θ (zeroSection P (fun s ↦ i.NormalSpace s hn) s) = i s) ∧
      (∀ x ∈ Θ.source, f (Θ x) = c + 2⁻¹ * h.normalHessian hn x.proj x.2 x.2) ∧
      ∃ ε₀ > 0, ∀ ε (hε : 0 < ε), ε < ε₀ → IsCompact (f ⁻¹' Icc (c - ε) (c + ε)) →
        criticalPoints I f ∩ f ⁻¹' Icc (c - ε) (c + ε) ⊆ range i →
        h.negativeDiscBundle hn P g.toRiemannianMetric ε ⊆ Θ.source ∧
        ∃ hA : {y | f y ≤ c - ε} ∪ Θ '' h.negativeDiscBundle hn P g.toRiemannianMetric ε ⊆
            {y | f y ≤ c + ε},
          ∀ {A : Type v} [Category.{w} A] [HasCoproducts.{u} A] [Preadditive A]
            [CategoryWithHomology A] (R : A) (n : ℕ),
            IsIso ((TopPair.ofInclusion (X := TopCat.of M) (subset_union_left :
                {y | f y ≤ c - ε} ⊆
                  {y | f y ≤ c - ε} ∪ Θ '' h.negativeDiscBundle hn P g.toRiemannianMetric ε)
              ).singularHomologyMap (TopPair.ofInclusionMap (Y := TopCat.of M) _
                (sublevel_mono f (a := c - ε) (b := c + ε) (by linarith))
                (ContinuousMap.inclusion hA) fun _ hx ↦ hx) R n) := by
  let := i.normalSpaceFiberBundle hn hdim
  let := i.normalSpaceVectorBundle hn hdim
  by_cases hS : CompactSpace S
  swap
  · -- If `S` is not compact, no `ε` satisfies the hypotheses, and only the normal form remains.
    obtain ⟨Θ, hΘz, hΘi, -, hΘf⟩ := h.exists_morseBott_partialDiffeomorph_normalBundle hn
      (k := ⊤) (by simp) hdim isOpen_univ (subset_univ _) (hfs.contMDiffOn.of_le (by simp))
    refine ⟨Θ, hΘz, hΘi, fun x hx ↦ by rw [hΘf x hx, hc], 1, one_pos,
      fun ε hε _ hcompact hcrit ↦ ?_⟩
    exact (hS (h.toIsCriticalSubmanifold.compactSpace_of_isCompact_preimage_Icc
      (hfs.of_le (by simp)) hc (by linarith) (by linarith) hcompact hcrit)).elim
  obtain ⟨Θ, hΘz, hΘi, hΘf, ε₀, hε₀, hmain⟩ :=
    exists_isIso_singularHomologyMap_iUnion_negativeDiscBundle (ι := Unit) (S := fun _ ↦ S)
      (P := fun _ ↦ P) (J := fun _ ↦ J) (i := fun _ ↦ i) hn (fun _ ↦ h) hfs (fun _ ↦ hc)
      Subsingleton.pairwise (fun _ ↦ hdim) (fun _ ↦ g)
  refine ⟨Θ (), hΘz (), hΘi (), hΘf (), ε₀, hε₀, fun ε hε hεε₀ hcompact hcrit ↦ ?_⟩
  obtain ⟨hD, hiso⟩ := hmain ε ⟨hε, hεε₀⟩ hcompact (by rwa [iUnion_const])
  rw [show (⋃ j, Θ j '' h.negativeDiscBundle hn P g.toRiemannianMetric ε) =
    Θ () '' h.negativeDiscBundle hn P g.toRiemannianMetric ε from
      Set.ext fun _ ↦ by simp only [mem_iUnion, Unique.exists_iff]] at hiso
  exact ⟨hD (), hiso⟩

/-- **The relative homology of a critical band of a Morse–Bott submanifold.** Let `i : S → M` be
a nondegenerate critical submanifold of a smooth function `f` on a Hausdorff, second-countable,
finite-dimensional, boundaryless manifold, with `S` nonempty and `f = c` along `i`, and let `g`
be a smooth fibre metric on its normal bundle. Let `a < c < b` be such that the band `f⁻¹[a, b]`
is compact and all its critical points lie on `i`; then `S` is compact.

Then there is a smooth partial diffeomorphism `Θ` from the total space of the normal bundle to
`M`, defined on a neighbourhood of the zero section and sending it to `i`, which puts `f` in the
Morse–Bott normal form `f (Θ v) = c + ½ Hessₛ (v, v)`, and an `ε₀ > 0` such that for every
`0 < ε < ε₀` the negative disc bundle `D_ε` relative to `g` lies in the source of `Θ` and the
relative singular homology `Hₙ({f ≤ b}, {f ≤ a})` is isomorphic to
`Hₙ({f ≤ c - ε} ∪ Θ(D_ε), {f ≤ c - ε})`, in every degree and for every coefficient object. -/
theorem nonempty_singularHomology_sublevelPair_iso_negativeDiscBundle [T2Space M]
    [SecondCountableTopology M] [J.Boundaryless] [Nonempty S]
    (h : i.IsNondegenerateCriticalSubmanifold f) (hfs : ContMDiff I 𝓘(ℝ) ∞ f) {a b c : ℝ}
    (hc : ∀ s, f (i s) = c) (hac : a < c) (hcb : c < b) (hcompact : IsCompact (f ⁻¹' Icc a b))
    (hcrit : criticalPoints I f ∩ f ⁻¹' Icc a b ⊆ range i)
    (hdim : Module.finrank ℝ P = Module.finrank ℝ E - Module.finrank ℝ E')
    (g : letI := i.normalSpaceFiberBundle hn hdim
      letI := i.normalSpaceVectorBundle hn hdim
      ContMDiffRiemannianMetric J ∞ P fun s ↦ i.NormalSpace s hn) :
    letI := i.normalSpaceFiberBundle hn hdim
    letI := i.normalSpaceVectorBundle hn hdim
    ∃ Θ : PartialDiffeomorph (J.prod 𝓘(ℝ, P)) I (TotalSpace P fun s ↦ i.NormalSpace s hn) M ∞,
      (∀ s, zeroSection P (fun s ↦ i.NormalSpace s hn) s ∈ Θ.source) ∧
      (∀ s, Θ (zeroSection P (fun s ↦ i.NormalSpace s hn) s) = i s) ∧
      (∀ x ∈ Θ.source, f (Θ x) = c + 2⁻¹ * h.normalHessian hn x.proj x.2 x.2) ∧
      ∃ ε₀ > 0, ∀ ε ∈ Ioo 0 ε₀,
        h.negativeDiscBundle hn P g.toRiemannianMetric ε ⊆ Θ.source ∧
        ∀ {A : Type v} [Category.{w} A] [Abelian A] [HasCoproducts.{u} A] (R : A) (n : ℕ),
          Nonempty ((sublevelPair f (hac.trans hcb).le).singularHomology R n ≅
            (TopPair.ofInclusion (X := TopCat.of M) (subset_union_left :
              {y | f y ≤ c - ε} ⊆
                {y | f y ≤ c - ε} ∪ Θ '' h.negativeDiscBundle hn P g.toRiemannianMetric ε)
              ).singularHomology R n) := by
  let := i.normalSpaceFiberBundle hn hdim
  let := i.normalSpaceVectorBundle hn hdim
  have : CompactSpace S := h.toIsCriticalSubmanifold.compactSpace_of_isCompact_preimage_Icc
    (hfs.of_le (by simp)) hc hac.le hcb.le hcompact hcrit
  obtain ⟨Θ, hΘz, hΘi, hΘf, ε₀, hε₀, hmain⟩ :=
    nonempty_singularHomology_sublevelPair_iso_iUnion_negativeDiscBundle (ι := Unit)
      (S := fun _ ↦ S) (P := fun _ ↦ P) (J := fun _ ↦ J) (i := fun _ ↦ i) hn (fun _ ↦ h) hfs
      (fun _ ↦ hc) Subsingleton.pairwise hac hcb hcompact (by rwa [iUnion_const]) (fun _ ↦ hdim)
      (fun _ ↦ g)
  refine ⟨Θ (), hΘz (), hΘi (), hΘf (), ε₀, hε₀, fun ε hε ↦ ?_⟩
  obtain ⟨hD, hiso⟩ := hmain ε hε
  rw [show (⋃ j, Θ j '' h.negativeDiscBundle hn P g.toRiemannianMetric ε) =
    Θ () '' h.negativeDiscBundle hn P g.toRiemannianMetric ε from
      Set.ext fun _ ↦ by simp only [mem_iUnion, Unique.exists_iff]] at hiso
  exact ⟨hD (), hiso⟩

end IsNondegenerateCriticalSubmanifold

end SmoothEmbedding

namespace IsMorseBottFamily

variable {E H : Type*} {M : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless] [TopologicalSpace M]
  [ChartedSpace H M] [IsManifold I ∞ M] {ι : Type*} {E' H' S P : ι → Type*}
  [∀ j, NormedAddCommGroup (E' j)] [∀ j, NormedSpace ℝ (E' j)] [∀ j, FiniteDimensional ℝ (E' j)]
  [∀ j, TopologicalSpace (H' j)] {J : ∀ j, ModelWithCorners ℝ (E' j) (H' j)}
  [∀ j, TopologicalSpace (S j)] [∀ j, ChartedSpace (H' j) (S j)] [∀ j, IsManifold (J j) ∞ (S j)]
  [∀ j, NormedAddCommGroup (P j)] [∀ j, NormedSpace ℝ (P j)] [∀ j, FiniteDimensional ℝ (P j)]
  {f : M → ℝ} {i : ∀ j, SmoothEmbedding (J j) I ∞ (S j) M} (hn : (∞ : ℕ∞ω) ≠ 0)


/-- **The relative homology of a critical band of a Morse–Bott function.** Let the family
`i j : S j → M` exhibit `f` as a Morse–Bott function (`TauCeti.IsMorseBottFamily`) on a compact
Hausdorff second-countable boundaryless manifold, with pieces modelled on boundaryless models, and
let `g j` be a smooth fibre metric on the normal bundle of `i j`. Let `a < c < b` be such that
every critical point of `f` with value in `[a, b]` lies on the level `c`, and index the pieces on
that level by `{j // ∀ s, f (i j s) = c}`.

Then there are smooth partial diffeomorphisms `Θ j` from the total spaces of the normal bundles of
these pieces to `M`, each defined on a neighbourhood of the zero section and sending it to `i j`,
which put `f` in the Morse–Bott normal form `f (Θ j v) = c + ½ Hessₛ (v, v)`, and an `ε₀ > 0` such
that for every `0 < ε < ε₀` each negative disc bundle `D j ε` relative to `g j` lies in the source
of `Θ j` and the relative singular homology `Hₙ({f ≤ b}, {f ≤ a})` is isomorphic to
`Hₙ({f ≤ c - ε} ∪ ⋃ j, Θ j (D j ε), {f ≤ c - ε})`, in every degree and for every coefficient
object. -/
theorem nonempty_singularHomology_sublevelPair_iso_iUnion_negativeDiscBundle [T2Space M]
    [SecondCountableTopology M] [CompactSpace M] [∀ j, (J j).Boundaryless]
    (h : IsMorseBottFamily i f) {a b c : ℝ} (hac : a < c) (hcb : c < b)
    (hcrit : ∀ x ∈ criticalPoints I f, f x ∈ Icc a b → f x = c)
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
        c + 2⁻¹ * (h.isNondegenerateCriticalSubmanifold j).normalHessian hn x.proj x.2 x.2) ∧
      ∃ ε₀ > 0, ∀ ε ∈ Ioo 0 ε₀,
        (∀ j : {j // ∀ s, f (i j s) = c},
          (h.isNondegenerateCriticalSubmanifold j).negativeDiscBundle hn (P j)
            (g j).toRiemannianMetric ε ⊆ (Θ j).source) ∧
        ∀ {A : Type v} [Category.{w} A] [Abelian A] [HasCoproducts.{u} A] (R : A) (n : ℕ),
          Nonempty ((sublevelPair f (hac.trans hcb).le).singularHomology R n ≅
            (TopPair.ofInclusion (X := TopCat.of M) (subset_union_left :
              {y | f y ≤ c - ε} ⊆ {y | f y ≤ c - ε} ∪
                ⋃ j, Θ j '' (h.isNondegenerateCriticalSubmanifold j).negativeDiscBundle hn
                  (P j) (g j).toRiemannianMetric ε)).singularHomology R n) := by
  have := h.finite
  have (j : ι) : Nonempty (S j) := h.nonempty j
  have (j : ι) : CompactSpace (S j) :=
    (Topology.IsClosedEmbedding.mk (i j).isEmbedding (h.isClosed_range j)).compactSpace
  refine SmoothEmbedding.nonempty_singularHomology_sublevelPair_iso_iUnion_negativeDiscBundle
    (ι := {j // ∀ s, f (i j s) = c}) (S := fun j ↦ S j) (P := fun j ↦ P j) (J := fun j ↦ J j)
    (i := fun j ↦ i j) hn (fun j ↦ h.isNondegenerateCriticalSubmanifold j) h.contMDiff
    (fun j ↦ j.2) (fun j k hjk ↦ h.pairwise_disjoint_range fun he ↦ hjk (Subtype.ext he)) hac hcb
    (isClosed_Icc.preimage h.contMDiff.continuous).isCompact (fun x ⟨hx, hxb⟩ ↦ ?_)
    (fun j ↦ hdim j) (fun j ↦ g j)
  -- A critical point in the band has value `c`, so its piece lies on the level `c`.
  obtain ⟨j, s, rfl⟩ := mem_iUnion.1 (h.criticalPoints_subset_iUnion_range hx)
  exact mem_iUnion.2 ⟨⟨j, fun s' ↦ (h.subsingleton_image_range hn j (mem_image_of_mem f
    (mem_range_self s')) (mem_image_of_mem f (mem_range_self s))).trans (hcrit _ hx hxb)⟩, s, rfl⟩

end IsMorseBottFamily

end TauCeti
