/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.FilteredSpace.Basic
public import TauCeti.Geometry.Manifold.Morse.Bott.Attachment
public import TauCeti.Geometry.Manifold.Morse.Bott.DiscBundle
public import TauCeti.Geometry.Manifold.Morse.Bott.HessianMetric
public import TauCeti.Geometry.Manifold.Morse.Deformation.Homology
public import TauCeti.Topology.VectorBundle.Attachment
public import TauCeti.Topology.VectorBundle.SphereBundle.Basic
import TauCeti.AlgebraicTopology.Cohomology.HomotopyInvariance
import TauCeti.AlgebraicTopology.Singular.Empty
import TauCeti.Geometry.Manifold.VectorBundle.Riemannian.Existence
import TauCeti.Topology.Maps.IsEmpty
import TauCeti.Topology.VectorBundle.DiscSphere
import TauCeti.Topology.VectorBundle.MayerVietoris.Basic
import TauCeti.Topology.VectorBundle.Riemannian.Basic
import TauCeti.Topology.VectorBundle.Smul
import TauCeti.Topology.VectorBundle.Subbundle
import TauCeti.Topology.VectorBundle.Thom.FiberwiseEquiv
import TauCeti.Topology.VectorBundle.Thom.RankDegreeHomology
import TauCeti.Topology.VectorBundle.Thom.RankZero

/-!
# Relative homology and cohomology across the level of compact Morse–Bott submanifolds

Let `i : S → M` be a compact nondegenerate critical submanifold of a smooth function `f` on a
boundaryless finite-dimensional manifold, on the level `f = c`, and let `g` be a smooth fibre
metric on its normal bundle. Write `M_t = {f ≤ t}`. Crossing the level attaches the negative disc
bundle: for a Morse–Bott normal form `Θ` near the zero section of the normal bundle and all small
`ε > 0` such that the band `f⁻¹[c-ε, c+ε]` is compact and all its critical points lie on `i`, the
sublevel `M_{c+ε}` strong deformation retracts onto `M_{c-ε} ∪ Θ(D_ε)`, where `D_ε` is the negative
disc bundle of size `ε`
(`IsNondegenerateCriticalSubmanifold.exists_sublevel_union_negativeDiscBundle_deformation`, in
the namespace `TauCeti.SmoothEmbedding`).

First, reading that attachment directly in relative singular homology gives an isomorphism induced
by the inclusion of pairs

`(M_{c-ε} ∪ Θ(D_ε), M_{c-ε}) ⟶ (M_{c+ε}, M_{c-ε})`

with coefficients in any preadditive category with coproducts and homology
(`exists_isIso_singularHomologyMap_negativeDiscBundle`), and regular-collar removal replaces `ε`
by arbitrary regular levels `a < c < b`
(`nonempty_singularHomology_sublevelPair_iso_negativeDiscBundle`). Groups `Hₙ(M_b, M_a)` of this
kind, between consecutive regular levels, are the first-page terms of the spectral sequence of the
filtration of a manifold by the sublevels of `f`; this identifies the contribution of a compact
Morse–Bott critical submanifold through its negative disc bundle. For an isolated nondegenerate
critical point the base is a point and the disc bundle is a cell of dimension the Morse index.

Next, assuming constant Morse index `r`, we equip the negative normal subbundle `ν⁻` with the
continuous Hessian fibre metric `-½ Hessₛ` (`TauCeti.Geometry.Manifold.Morse.Bott.HessianMetric`).
Rescaling the unit disc bundle `D(ν⁻)` by `√ε` yields `f (Θ (√ε • v)) = c - ε ‖v‖²`, so `D(ν⁻)`
attaches along `S(ν⁻)` to `{f ≤ c - ε}` as a closed embedding; disc-bundle attachment
(`TauCeti.isIso_singularHomologyMap_of_attach_gaugeDiscBundle`,
`TauCeti.isIso_singularCohomologyMap_of_attach_gaugeDiscBundle`) and the deformation retraction give
isomorphisms `(D(ν⁻), S(ν⁻)) ⟶ ({f ≤ c + ε}, {f ≤ c - ε})` and hence with the Thom pair
`(ν⁻, ν⁻₀)` in both homology and cohomology (`exists_discSpherePairMap_isIso_sublevelPair`).
Regular-collar removal (`TauCeti.singularHomologySublevelPairIsoOfCriticalValue`) extends the
homology identification to any compact isolated band `[a, b]` around `c`, yielding vanishing below
`r`, the `Subsingleton Kˣ` index-degree isomorphism `Hᵣ({f ≤ b}, {f ≤ a}; K) ≅ H₀(S; K)`, the
index-`0` isomorphism `Hₙ({f ≤ b}, {f ≤ a}; R) ≅ Hₙ(S; R)`, and the first page of
`TauCeti.filteredSpaceSpectralSequence`.

A level of a Morse–Bott function generally carries several critical submanifolds, of different
dimensions and indices. For finitely many compact ones `i j : S j → M` with pairwise disjoint
images on the level `c`, crossing the level attaches all their negative disc bundles at once
(`TauCeti.SmoothEmbedding.exists_sublevel_union_iUnion_negativeDiscBundle_deformation`), and the
same argument identifies `Hₙ(M_{c+ε}, M_{c-ε})`, and `Hₙ(M_b, M_a)` for regular levels
`a < c < b`, with `Hₙ(M_{c-ε} ∪ ⋃ j, Θ j (D j ε), M_{c-ε})`. For a Morse–Bott function on a compact
manifold (`TauCeti.IsMorseBottFamily`) the pieces on a level are finite in number, compact and
disjoint, so this applies to every band `[a, b]` whose only critical value is `c`, with the pieces
on the level `c` as the family.

The relative homology across the critical level can also be read off a parametrization of the
negative disc bundle. Write the normal form as `f = c - s + t` on a tube `W`, and suppose that the
negative disc bundle `{x ∈ W | t x = 0, s x ≤ ε}` is parametrized by the disc bundle `D_ρ(V)` of a
fibre gauge `ρ` on a real vector bundle `V → B`, for instance the negative normal bundle with a
fibre metric: a map `g` restricting to a closed embedding of `D_ρ(V)` onto the negative disc bundle,
and of the sphere bundle `S_ρ(V)` onto its boundary `{t = 0, s = ε}`. Then `g` induces a map of
pairs `(D_ρ(V), S_ρ(V)) ⟶ (M_{c+ε}, M_{c-ε})` which is an isomorphism on relative singular
homology in every degree
(`TauCeti.exists_isIso_singularHomologyMap_sublevelPair_of_negativeDiscBundle`), so
`Hₙ(M_{c+ε}, M_{c-ε})` is the relative homology `Hₙ(V, V₀)` of the Thom pair of `V`
(`TauCeti.nonempty_singularHomology_sublevelPair_iso_thomPair`). The Thom isomorphism, which this
file does not use, identifies the homology of the Thom pair with the homology of the base `B`,
shifted by the rank of `V` and with coefficients twisted by the orientation of `V`.

## Main results

In the namespace `TauCeti.SmoothEmbedding.IsNondegenerateCriticalSubmanifold`:

* `exists_isIso_singularHomologyMap_negativeDiscBundle`: the inclusion of the lower sublevel with
  the negative disc bundle attached into the upper sublevel, relative to the lower sublevel,
  induces isomorphisms on relative singular homology.
* `nonempty_singularHomology_sublevelPair_iso_negativeDiscBundle`: the relative homology of the
  sublevels at two regular levels around the critical level is the relative homology of the lower
  sublevel with the negative disc bundle attached.
* `exists_discSpherePairMap_isIso_sublevelPair`: for small `ε > 0`, the attaching map
  `(D(ν⁻), S(ν⁻)) ⟶ ({f ≤ c + ε}, {f ≤ c - ε})` induces isomorphisms on both relative singular
  homology and cohomology.
* `exists_singularHomology_sublevelPair_iso_thomPair` and
  `exists_singularCohomology_sublevelPair_iso_thomPair`: identification with the relative homology
  and cohomology of the Thom pair `(ν⁻, ν⁻₀)` across `[c - ε, c + ε]`.
* `nonempty_singularHomology_sublevelPair_iso_thomPair`,
  `nonempty_singularHomology_sublevelPair_iso_thomPair_of_preconnectedSpace`, and
  `nonempty_singularHomology_bandPair_iso_thomPair`: identification with `Hₙ(ν⁻, ν⁻₀; R)` on an
  arbitrary compact isolated band `[a, b]`.
* `isZero_singularHomology_sublevelPair_of_lt_index` and
  `isZero_singularCohomology_sublevelPair_of_lt_index`: vanishing below the Morse index.
* `nonempty_singularHomology_sublevelPair_iso_singularHomology_zero`: in the index degree,
  `Hᵣ({f ≤ b}, {f ≤ a}; K) ≅ H₀(S; K)` for a ring with `Subsingleton Kˣ`.
* `nonempty_singularHomology_sublevelPair_iso_singularHomology_of_index_eq_zero`: for index `0`,
  `Hₙ({f ≤ b}, {f ≤ a}; R) ≅ Hₙ(S; R)`.
* `nonempty_filteredSpaceSpectralSequence_page_two_X_iso_thomPair` and
  `isZero_filteredSpaceSpectralSequence_page_two_X_of_lt_index`: the first page of the sublevel
  filtration spectral sequence across a Morse–Bott critical submanifold.

In the namespace `TauCeti.SmoothEmbedding`:

* `exists_isIso_singularHomologyMap_iUnion_negativeDiscBundle` and
  `nonempty_singularHomology_sublevelPair_iso_iUnion_negativeDiscBundle`: the same for finitely
  many disjoint compact Morse–Bott submanifolds on one level, each with its own model, with all
  their negative disc bundles attached.

In the namespace `TauCeti.IsMorseBottFamily`:

* `nonempty_singularHomology_sublevelPair_iso_iUnion_negativeDiscBundle`: the relative homology of
  a band of a Morse–Bott function on a compact manifold with a single critical value `c` is that of
  the lower sublevel with the negative disc bundles of all the critical submanifolds on the level
  `c` attached.

In the namespace `TauCeti`:

* `exists_isIso_singularHomologyMap_sublevelPair_of_negativeDiscBundle`: a parametrization of
  the negative disc bundle induces isomorphisms `Hₙ(D_ρ(V), S_ρ(V)) ≅ Hₙ(M_{c+ε}, M_{c-ε})`.
* `nonempty_singularHomology_sublevelPair_iso_thomPair`: the relative homology across the
  critical level is that of the Thom pair, `Hₙ(M_{c+ε}, M_{c-ε}) ≅ Hₙ(V, V₀)`.

## References

* R. Bott, *Nondegenerate critical manifolds*, Annals of Mathematics 60 (1954), 248–261.
* J. Milnor, *Morse Theory*, Annals of Mathematics Studies 51, Princeton University Press, 1963,
  Theorem 3.2 and §5.
* R. L. Cohen, K. Iga and P. Norbury, *Topics in Morse theory: lecture notes*, 2006,
  Theorems 15.1 and 15.4.
-/

public section

noncomputable section

open AlgebraicTopology Bundle CategoryTheory Filter Function Limits Module Set Topology
open scoped ContDiff Manifold Bundle

universe u v w w'

namespace TauCeti

section Family

variable {E H : Type*} {M : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless] [TopologicalSpace M]
  [ChartedSpace H M] [IsManifold I ∞ M] {ι : Type*} {E' H' S P : ι → Type*}
  [∀ j, NormedAddCommGroup (E' j)] [∀ j, NormedSpace ℝ (E' j)] [∀ j, FiniteDimensional ℝ (E' j)]
  [∀ j, TopologicalSpace (H' j)] {J : ∀ j, ModelWithCorners ℝ (E' j) (H' j)}
  [∀ j, TopologicalSpace (S j)] [∀ j, ChartedSpace (H' j) (S j)] [∀ j, IsManifold (J j) ∞ (S j)]
  [∀ j, NormedAddCommGroup (P j)] [∀ j, NormedSpace ℝ (P j)] [∀ j, FiniteDimensional ℝ (P j)]
  {f : M → ℝ} {i : ∀ j, SmoothEmbedding (J j) I ∞ (S j) M} (hn : (∞ : ℕ∞ω) ≠ 0)

/-- **The relative homology across a level of finitely many Morse–Bott submanifolds is carried by
their negative disc bundles.** Let `i j : S j → M`, for `j` in a finite index type, be
nondegenerate critical submanifolds of a smooth function `f` on a Hausdorff, second-countable,
finite-dimensional, boundaryless manifold, each modelled on its own space, with `S j` compact and
nonempty, pairwise disjoint images and `f = c` along each of them. Let `g j` be a smooth fibre
metric on the normal bundle of `i j`.

Then there are smooth partial diffeomorphisms `Θ j` from the total spaces of the normal bundles to
`M`, each defined on a neighbourhood of the zero section and sending it to `i j`, which put `f` in
the Morse–Bott normal form `f (Θ j v) = c + ½ Hessₛ (v, v)`, and an `ε₀ > 0` with the following
property. Let `0 < ε < ε₀` be such that the band `f⁻¹[c - ε, c + ε]` is compact and all its
critical points lie on the submanifolds. Then each negative disc bundle `D j ε` relative to `g j`
lies in the source of `Θ j`, the set `{f ≤ c - ε} ∪ ⋃ j, Θ j (D j ε)` lies in `{f ≤ c + ε}`, and
the inclusion of pairs `({f ≤ c - ε} ∪ ⋃ j, Θ j (D j ε), {f ≤ c - ε}) ⟶
({f ≤ c + ε}, {f ≤ c - ε})` induces isomorphisms on relative singular homology, in every degree
and for every coefficient object. -/
theorem SmoothEmbedding.exists_isIso_singularHomologyMap_iUnion_negativeDiscBundle [T2Space M]
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
      (∀ j, ∀ x ∈ (Θ j).source, f (Θ j x) = c + 2⁻¹ * (h j).normalHessian hn x.proj x.snd x.snd) ∧
      ∃ ε₀ > 0, ∀ ε (hε : 0 < ε), ε < ε₀ → IsCompact (f ⁻¹' Icc (c - ε) (c + ε)) →
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
                (sublevel_mono f (a := c - ε) (b := c + ε) (by linarith))
                (ContinuousMap.inclusion hA) fun _ hx ↦ hx) R n) := by
  let : ∀ j, FiberBundle (P j) fun s ↦ (i j).NormalSpace s hn :=
    fun j ↦ (i j).normalSpaceFiberBundle hn (hdim j)
  let : ∀ j, VectorBundle ℝ (P j) fun s ↦ (i j).NormalSpace s hn :=
    fun j ↦ (i j).normalSpaceVectorBundle hn (hdim j)
  obtain ⟨Θ, hΘz, hΘi, hΘf, ε₀, hε₀, hmain⟩ :=
    exists_sublevel_union_iUnion_negativeDiscBundle_deformation hn h hfs hc hd hdim g
  refine ⟨Θ, hΘz, hΘi, hΘf, ε₀, hε₀, fun ε hε hεε₀ hcompact hcrit ↦ ?_⟩
  obtain ⟨hD, -, r, -, ⟨G⟩⟩ := hmain ε ⟨hε, hεε₀⟩ hcompact hcrit
  -- Each disc bundle lies in the critical sublevel, since the normal Hessian is negative on the
  -- negative normal spaces.
  have hA : {y | f y ≤ c - ε} ∪
      ⋃ j, Θ j '' (h j).negativeDiscBundle hn (P j) (g j).toRiemannianMetric ε ⊆
        {y | f y ≤ c + ε} := by
    refine union_subset (sublevel_mono f (by linarith)) <| iUnion_subset fun j ↦ ?_
    rintro _ ⟨x, hx, rfl⟩
    have hle : (h j).normalHessian hn x.proj x.snd x.snd ≤ 0 := by
      rcases eq_or_ne x.snd 0 with h0 | h0
      · simp [h0]
      · exact ((h j).normalHessian_apply_self_neg_of_mem_negativeNormalSpace hn _
          (IsCriticalSubmanifold.mem_negativeNormalSpace_of_mem_negativeDiscBundle hn hx) h0).le
    rw [mem_ofPred_eq, hΘf j x (hD j hx)]
    linarith
  -- The deformation retracts `{f ≤ c + ε}` onto `{f ≤ c - ε} ∪ ⋃ j, Θ j (D j ε)`, fixing it
  -- pointwise.
  refine ⟨hD, hA, fun {A} _ _ _ _ R n ↦
    TopPair.isIso_singularHomologyMap_ofInclusionMap_inclusion_of_homotopyRel (X := TopCat.of M)
      subset_union_left hA ((ContinuousMap.inclusion inter_subset_right).comp r)
      (G.cast (ContinuousMap.ext fun _ ↦ rfl) rfl) R n⟩

/-- **The relative homology of a critical band of finitely many Morse–Bott submanifolds.** Let
`i j : S j → M`, for `j` in a finite index type, be nondegenerate critical submanifolds of a
smooth function `f` on a Hausdorff, second-countable, finite-dimensional, boundaryless manifold,
each modelled on its own space, with `S j` compact and nonempty, pairwise disjoint images and
`f = c` along each of them, and let `g j` be a smooth fibre metric on the normal bundle of `i j`.
Let `a < c < b` be such that the band `f⁻¹[a, b]` is compact and all its critical points lie on
the submanifolds.

Then there are smooth partial diffeomorphisms `Θ j` from the total spaces of the normal bundles to
`M`, each defined on a neighbourhood of the zero section and sending it to `i j`, which put `f` in
the Morse–Bott normal form `f (Θ j v) = c + ½ Hessₛ (v, v)`, and an `ε₀ > 0` such that for every
`0 < ε < ε₀` each negative disc bundle `D j ε` relative to `g j` lies in the source of `Θ j` and
the relative singular homology `Hₙ({f ≤ b}, {f ≤ a})` is isomorphic to
`Hₙ({f ≤ c - ε} ∪ ⋃ j, Θ j (D j ε), {f ≤ c - ε})`, in every degree and for every coefficient
object. -/
theorem SmoothEmbedding.nonempty_singularHomology_sublevelPair_iso_iUnion_negativeDiscBundle
    [T2Space M] [SecondCountableTopology M] [Finite ι] [∀ j, (J j).Boundaryless]
    [∀ j, CompactSpace (S j)] [∀ j, Nonempty (S j)]
    (h : ∀ j, (i j).IsNondegenerateCriticalSubmanifold f) (hfs : ContMDiff I 𝓘(ℝ) ∞ f)
    {a b c : ℝ} (hc : ∀ j s, f (i j s) = c) (hd : Pairwise (Disjoint on fun j ↦ range (i j)))
    (hac : a < c) (hcb : c < b) (hcompact : IsCompact (f ⁻¹' Icc a b))
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
      (∀ j, ∀ x ∈ (Θ j).source, f (Θ j x) = c + 2⁻¹ * (h j).normalHessian hn x.proj x.snd x.snd) ∧
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
  -- Every critical point of the band lies on one of the submanifolds, hence on the level `c`.
  have hlev : ∀ x ∈ criticalPoints I f, f x ∈ Icc a b → f x = c := fun x hx hfx ↦ by
    obtain ⟨j, s, rfl⟩ := mem_iUnion.1 (hcrit ⟨hx, hfx⟩)
    exact hc j s
  obtain ⟨hD, _, hiso⟩ := hmain ε hε0 hε₁ hcompact' fun x hx ↦ hcrit ⟨hx.1, hε' hx.2⟩
  refine ⟨hD, fun {A} _ _ _ R n ↦ ⟨singularHomologySublevelPairIsoOfCriticalValue hfs hac hcb
    (by linarith : c - ε < c) (by linarith : c < c + ε) hcompact hcompact' hlev
    (fun x hx hfx ↦ hlev x hx (hε' hfx)) R n ≪≫ (@asIso _ _ _ _ _ (hiso R n)).symm⟩⟩

/-- **The relative homology across a critical level of a Morse–Bott function is carried by the
negative disc bundles of its critical submanifolds on that level.** Let the family
`i j : S j → M` exhibit `f` as a Morse–Bott function (`TauCeti.IsMorseBottFamily`) on a compact
Hausdorff second-countable boundaryless manifold, with pieces modelled on boundaryless models,
and let `g j` be a smooth fibre metric on the normal bundle of `i j`. Let `a < c < b` be such that
`c` is the only critical value of `f` in `[a, b]`, and index the pieces on the level `f = c` by
`{j // ∀ s, f (i j s) = c}`.

Then there are smooth partial diffeomorphisms `Θ j` from the total spaces of the normal bundles of
these pieces to `M`, each defined on a neighbourhood of the zero section and sending it to `i j`,
which put `f` in the Morse–Bott normal form `f (Θ j v) = c + ½ Hessₛ (v, v)`, and an `ε₀ > 0` such
that for every `0 < ε < ε₀` each negative disc bundle `D j ε` relative to `g j` lies in the source
of `Θ j` and the relative singular homology `Hₙ({f ≤ b}, {f ≤ a})` is isomorphic to
`Hₙ({f ≤ c - ε} ∪ ⋃ j, Θ j (D j ε), {f ≤ c - ε})`, in every degree and for every coefficient
object. If `c` is not a critical value there are no such pieces, and the second pair is
`({f ≤ c - ε}, {f ≤ c - ε})`. -/
theorem IsMorseBottFamily.nonempty_singularHomology_sublevelPair_iso_iUnion_negativeDiscBundle
    [T2Space M] [SecondCountableTopology M] [CompactSpace M] [∀ j, (J j).Boundaryless]
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
        c + 2⁻¹ * (h.isNondegenerateCriticalSubmanifold j).normalHessian hn x.proj x.snd x.snd) ∧
      ∃ ε₀ > 0, ∀ ε ∈ Ioo 0 ε₀,
        (∀ j : {j // ∀ s, f (i j s) = c},
          (h.isNondegenerateCriticalSubmanifold j).negativeDiscBundle hn (P j)
            (g j).toRiemannianMetric ε ⊆ (Θ j).source) ∧
        ∀ {A : Type v} [Category.{w} A] [Abelian A] [HasCoproducts.{u} A] (R : A) (n : ℕ),
          Nonempty ((sublevelPair f (hac.trans hcb).le).singularHomology R n ≅
            (TopPair.ofInclusion (X := TopCat.of M) (subset_union_left :
              {y | f y ≤ c - ε} ⊆ {y | f y ≤ c - ε} ∪
                ⋃ j, Θ j '' (h.isNondegenerateCriticalSubmanifold j).negativeDiscBundle hn (P j)
                  (g j).toRiemannianMetric ε)
              ).singularHomology R n) := by
  have := h.finite
  have (j : ι) : Nonempty (S j) := h.nonempty j
  have (j : ι) : CompactSpace (S j) :=
    (Topology.IsClosedEmbedding.mk (i j).isEmbedding (h.isClosed_range j)).compactSpace
  refine SmoothEmbedding.nonempty_singularHomology_sublevelPair_iso_iUnion_negativeDiscBundle
    (ι := {j // ∀ s, f (i j s) = c}) (S := fun j ↦ S j) (P := fun j ↦ P j) (J := fun j ↦ J j)
    (i := fun j ↦ i j) hn (fun j ↦ h.isNondegenerateCriticalSubmanifold j) h.contMDiff
    (fun j ↦ j.property) (fun j k hjk ↦ h.pairwise_disjoint_range fun he ↦ hjk
        (Subtype.ext he)) hac hcb
    (isClosed_Icc.preimage h.contMDiff.continuous).isCompact (fun x ⟨hx, hfx⟩ ↦ ?_)
    (fun j ↦ hdim j) (fun j ↦ g j)
  -- A critical point in the band has value `c`, so its piece lies on the level `c`.
  exact h.mem_iUnion_range_of_apply_eq hn hx (hcrit _ hx hfx)

end Family

namespace SmoothEmbedding

section Submanifold

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
      (∀ x ∈ Θ.source, f (Θ x) = c + 2⁻¹ * h.normalHessian hn x.proj x.snd x.snd) ∧
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
  have hmain := hmain ε hε hεε₀ hcompact (by rwa [iUnion_const])
  rw [show (⋃ a, Θ a '' h.negativeDiscBundle hn P g.toRiemannianMetric ε) =
    Θ () '' h.negativeDiscBundle hn P g.toRiemannianMetric ε from
      Set.ext fun _ ↦ by simp only [mem_iUnion, Unique.exists_iff]] at hmain
  exact ⟨hmain.1 (), hmain.2⟩

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
      (∀ x ∈ Θ.source, f (Θ x) = c + 2⁻¹ * h.normalHessian hn x.proj x.snd x.snd) ∧
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
  have := h.toIsCriticalSubmanifold.compactSpace_of_isCompact_preimage_Icc (hfs.of_le (by simp))
    hc hac.le hcb.le hcompact hcrit
  obtain ⟨Θ, hΘz, hΘi, hΘf, ε₀, hε₀, hmain⟩ :=
    nonempty_singularHomology_sublevelPair_iso_iUnion_negativeDiscBundle (ι := Unit)
      (S := fun _ ↦ S) (P := fun _ ↦ P) (J := fun _ ↦ J) (i := fun _ ↦ i) hn (fun _ ↦ h) hfs
      (fun _ ↦ hc) Subsingleton.pairwise hac hcb hcompact (by rwa [iUnion_const])
      (fun _ ↦ hdim) (fun _ ↦ g)
  refine ⟨Θ (), hΘz (), hΘi (), hΘf (), ε₀, hε₀, fun ε hε ↦ ?_⟩
  have hmain := hmain ε hε
  rw [show (⋃ a, Θ a '' h.negativeDiscBundle hn P g.toRiemannianMetric ε) =
    Θ () '' h.negativeDiscBundle hn P g.toRiemannianMetric ε from
      Set.ext fun _ ↦ by simp only [mem_iUnion, Unique.exists_iff]] at hmain
  exact ⟨hmain.1 (), hmain.2⟩

end IsNondegenerateCriticalSubmanifold

end Submanifold

namespace IsNondegenerateCriticalSubmanifold

/-! ### Disc-bundle attachment and Thom-pair comparison in homology and cohomology -/

section HomologyAttachment

variable {E : Type u} {H : Type*} {M : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  [SecondCountableTopology M]
  {E' H' : Type*} {S : Type u} [NormedAddCommGroup E'] [NormedSpace ℝ E']
  [FiniteDimensional ℝ E'] [TopologicalSpace H'] {J : ModelWithCorners ℝ E' H'} [J.Boundaryless]
  [TopologicalSpace S] [ChartedSpace H' S] [IsManifold J ∞ S] [CompactSpace S]
  {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
  {f : M → ℝ} {i : SmoothEmbedding J I ∞ S M} (hn : (∞ : ℕ∞ω) ≠ 0)

omit [SecondCountableTopology M] [J.Boundaryless] [CompactSpace S] in
/-- In the empty-submanifold case, the band contains no critical points, so the empty attaching map
from the empty disc-sphere pair into the sublevel pair induces isomorphisms on both relative
singular homology and cohomology. -/
private theorem exists_discSpherePairMap_isIso_sublevelPair_of_isEmpty [IsEmpty S]
    (h : i.IsNondegenerateCriticalSubmanifold f) (hfs : ContMDiff I 𝓘(ℝ) ∞ f) {c : ℝ}
    (hdim : finrank ℝ P = finrank ℝ E - finrank ℝ E')
    (g : letI := i.normalSpaceFiberBundle hn hdim
      letI := i.normalSpaceVectorBundle hn hdim
      ContMDiffRiemannianMetric J ∞ P fun s ↦ i.NormalSpace s hn) {r : ℕ}
    (hr : ∀ s, manifoldMorseIndex I f (i s) = r) :
    haveI : IsManifold I (∞ + 2) M := .of_le (n := ∞) (by simp)
    haveI : IsManifold J (∞ + 1) S := .of_le (n := ∞) (by simp)
    letI := i.normalSpaceFiberBundle hn hdim
    letI := i.normalSpaceVectorBundle hn hdim
    letI hV := h.hasLocalContMDiffSubbundleFrames_negativeNormalSpace hn (by simp)
      (fun s ↦ (hfs (i s)).of_le (by simp)) hdim g hr
    letI ν : S → Type u := fun s ↦ h.negativeNormalSpace hn g.toRiemannianMetric s
    letI : TopologicalSpace (TotalSpace (Fin r → ℝ) ν) :=
      subbundleTopology P (F' := Fin r → ℝ) (h.negativeNormalSpace hn g.toRiemannianMetric)
    letI : FiberBundle (Fin r → ℝ) ν := hV.fiberBundle
    letI : VectorBundle ℝ (Fin r → ℝ) ν := hV.vectorBundle
    letI : RiemannianBundle ν :=
      ⟨(h.negativeNormalHessianMetric hn (by simp) (fun s ↦ (hfs (i s)).of_le (by simp)) hdim g
        hr).toRiemannianMetric⟩
    letI : ∀ s, NormedAddCommGroup (ν s) := fun s ↦ inferInstance
    ∃ ε₀ > 0, ∀ ε (hε : ε ∈ Ioo 0 ε₀), IsCompact (f ⁻¹' Icc (c - ε) (c + ε)) →
      criticalPoints I f ∩ f ⁻¹' Icc (c - ε) (c + ε) ⊆ range i →
      ∃ ψ : gaugeDiscSpherePair (fun v : TotalSpace (Fin r → ℝ) ν ↦ ‖v.snd‖) ⟶
          sublevelPair f (a := c - ε) (b := c + ε) (by linarith [hε.1]),
        (∀ {A : Type v} [Category.{w} A] [HasCoproducts.{u} A] [Abelian A] (R : A) (n : ℕ),
          IsIso (TopPair.singularHomologyMap ψ R n)) ∧
        (∀ {A : Type v} [Category.{w} A] [HasCoproducts.{u} A] [Abelian A] (R : A)
          (k : Type w') [Ring k] [Linear k A] (M' : A) (n : ℕ),
          IsIso (TopPair.singularCohomologyMap (R := R) (k := k) (M := M') ψ n)) := by
  have : IsManifold I (∞ + 2) M := .of_le (n := ∞) (by simp)
  have : IsManifold J (∞ + 1) S := .of_le (n := ∞) (by simp)
  let := i.normalSpaceFiberBundle hn hdim
  let := i.normalSpaceVectorBundle hn hdim
  let hV := h.hasLocalContMDiffSubbundleFrames_negativeNormalSpace hn (by simp)
    (fun s ↦ (hfs (i s)).of_le (by simp)) hdim g hr
  let ν : S → Type u := fun s ↦ h.negativeNormalSpace hn g.toRiemannianMetric s
  let := subbundleTopology P (F' := Fin r → ℝ) (h.negativeNormalSpace hn g.toRiemannianMetric)
  let := hV.fiberBundle
  let := hV.vectorBundle
  let : RiemannianBundle ν := ⟨(h.negativeNormalHessianMetric hn (by simp)
    (fun s ↦ (hfs (i s)).of_le (by simp)) hdim g hr).toRiemannianMetric⟩
  let : ∀ s, NormedAddCommGroup (ν s) := fun s ↦ inferInstance
  let : ∀ s, InnerProductSpace ℝ (ν s) := fun s ↦ inferInstance
  let := Bundle.instIsContinuousRiemannianBundle
    (h.negativeNormalHessianMetric hn (by simp) (fun s ↦ (hfs (i s)).of_le (by simp)) hdim g hr)
  refine ⟨1, one_pos, fun ε hε hcomp hcrit ↦ ?_⟩
  have hle : c - ε ≤ c + ε := by linarith [hε.1]
  have hreg : ∀ x, c - ε ≤ f x → f x ≤ c + ε → mfderiv I 𝓘(ℝ) f x ≠ 0 := fun x h₁ h₂ hx ↦ by
    obtain ⟨s, -⟩ := hcrit ⟨mem_criticalPoints_iff_mfderiv_eq_zero.2 hx, h₁, h₂⟩
    exact isEmptyElim s
  obtain ⟨rdef, -, ⟨G⟩⟩ := exists_sublevelDeformation hfs hle hcomp hreg
  have hdeq : sublevelInclusion f (c - ε) (c + ε) hle =
      ContinuousMap.inclusion (sublevel_mono f hle) := by ext; simp
  rw [hdeq] at G
  let ρ : TotalSpace (Fin r → ℝ) ν → ℝ := fun v ↦ ‖v.snd‖
  have : IsEmpty (gaugeDiscBundle ρ) := ⟨fun v ↦ isEmptyElim v.val.proj⟩
  have : IsEmpty (gaugeSphereBundle ρ) := ⟨fun v ↦ isEmptyElim v.val.proj⟩
  have : IsEmpty (gaugeDiscSpherePair ρ).fst := ⟨fun v ↦ isEmptyElim v.val.proj⟩
  have : IsEmpty (gaugeDiscSpherePair ρ).snd := ⟨fun v ↦ isEmptyElim v.val.proj⟩
  let Z := {y : M | f y ≤ c - ε}
  let φ_pair : gaugeDiscSpherePair ρ ⟶
      TopPair.ofSubset (X := TopCat.of Z) (Subtype.val ⁻¹' {y | f y ≤ c - ε}) :=
    TopPair.ofHom (TopCat.ofHom ⟨isEmptyElim, continuous_of_discreteTopology⟩)
      (TopCat.ofHom ⟨isEmptyElim, continuous_of_discreteTopology⟩) (TopCat.ext isEmptyElim)
  let eZ := TopPair.ofSubsetPreimageValIso (X := TopCat.of M) (subset_refl Z)
  let ι : TopPair.ofInclusion (X := TopCat.of M) (subset_refl Z) ⟶ sublevelPair f hle :=
    TopPair.ofInclusionMap (subset_refl Z) (sublevel_mono f hle)
      (ContinuousMap.inclusion (sublevel_mono f hle)) fun _ hx ↦ hx
  have hXeq : (Subtype.val ⁻¹' {y : M | f y ≤ c - ε} : Set Z) = univ :=
    eq_univ_of_forall fun z ↦ z.property
  have hρ : IsFiberGauge ρ := isFiberGauge_norm (TauCeti.continuous_norm_bundle (Fin r → ℝ) ν)
  refine ⟨φ_pair ≫ eZ.hom ≫ ι, fun {A} _ _ _ R m ↦ ?_, fun {A} _ _ _ R k _ _ M' m ↦ ?_⟩
  · have : IsIso (TopPair.singularHomologyMap φ_pair R m) :=
      isIso_singularHomologyMap_of_attach_gaugeDiscBundle hρ (hXeq ▸ isClosed_univ) R m
        (IsClosedEmbedding.of_isEmpty _) (fun v ↦ isEmptyElim v) (by simp [hXeq])
    have : IsIso (TopPair.singularHomologyMap eZ.hom R m) :=
      (TopPair.singularHomologyMapIso R eZ m).isIso_hom
    have : IsIso (TopPair.singularHomologyMap ι R m) :=
      TopPair.isIso_singularHomologyMap_ofInclusionMap_inclusion_of_homotopyRel
        (X := TopCat.of M) (subset_refl Z) (sublevel_mono f hle) rdef G R m
    rw [TopPair.singularHomologyMap_comp, TopPair.singularHomologyMap_comp]
    infer_instance
  · have : IsIso (TopPair.singularCohomologyMap (R := R) (k := k) (M := M') φ_pair m) :=
      isIso_singularCohomologyMap_of_attach_gaugeDiscBundle hρ (hXeq ▸ isClosed_univ) R m k M'
        (IsClosedEmbedding.of_isEmpty _) (fun v ↦ isEmptyElim v) (by simp [hXeq])
    have : IsIso (TopPair.singularCohomologyMap (R := R) (k := k) (M := M') eZ.hom m) :=
      ⟨⟨TopPair.singularCohomologyMap eZ.inv m,
        by rw [← TopPair.singularCohomologyMap_comp, eZ.inv_hom_id,
          TopPair.singularCohomologyMap_id],
        by rw [← TopPair.singularCohomologyMap_comp, eZ.hom_inv_id,
          TopPair.singularCohomologyMap_id]⟩⟩
    have : IsIso (TopPair.singularCohomologyMap (R := R) (k := k) (M := M') ι m) :=
      TopPair.isIso_singularCohomologyMap_ofInclusionMap_inclusion_of_homotopyRel
        (X := TopCat.of M) (subset_refl Z) (sublevel_mono f hle) rdef G R k M' m
    rw [TopPair.singularCohomologyMap_comp, TopPair.singularCohomologyMap_comp]
    infer_instance

omit [T2Space M] [SecondCountableTopology M] [J.Boundaryless] [CompactSpace S] in
/-- Rescaling vectors in the negative normal bundle by `√ε` sends the unit disc bundle `D(ν⁻)`
for the Hessian fibre metric continuously and injectively onto the negative disc bundle `D_ε`,
with `-½ Hess(scale v, scale v) = ε ‖v‖²`. -/
private theorem exists_rescale_negativeDiscBundle
    (h : i.IsNondegenerateCriticalSubmanifold f) (hfs : ContMDiff I 𝓘(ℝ) ∞ f)
    (hdim : finrank ℝ P = finrank ℝ E - finrank ℝ E')
    (g : letI := i.normalSpaceFiberBundle hn hdim
      letI := i.normalSpaceVectorBundle hn hdim
      ContMDiffRiemannianMetric J ∞ P fun s ↦ i.NormalSpace s hn) {r : ℕ}
    (hr : ∀ s, manifoldMorseIndex I f (i s) = r) {ε : ℝ} (hε : 0 < ε) :
    haveI : IsManifold I (∞ + 2) M := .of_le (n := ∞) (by simp)
    haveI : IsManifold J (∞ + 1) S := .of_le (n := ∞) (by simp)
    letI := i.normalSpaceFiberBundle hn hdim
    letI := i.normalSpaceVectorBundle hn hdim
    letI hV := h.hasLocalContMDiffSubbundleFrames_negativeNormalSpace hn (by simp)
      (fun s ↦ (hfs (i s)).of_le (by simp)) hdim g hr
    letI ν : S → Type u := fun s ↦ h.negativeNormalSpace hn g.toRiemannianMetric s
    letI : TopologicalSpace (TotalSpace (Fin r → ℝ) ν) :=
      subbundleTopology P (F' := Fin r → ℝ) (h.negativeNormalSpace hn g.toRiemannianMetric)
    letI : FiberBundle (Fin r → ℝ) ν := hV.fiberBundle
    letI : VectorBundle ℝ (Fin r → ℝ) ν := hV.vectorBundle
    letI : RiemannianBundle ν :=
      ⟨(h.negativeNormalHessianMetric hn (by simp) (fun s ↦ (hfs (i s)).of_le (by simp)) hdim g
        hr).toRiemannianMetric⟩
    letI : ∀ s, NormedAddCommGroup (ν s) := fun s ↦ inferInstance
    ∃ scale : TotalSpace (Fin r → ℝ) ν → TotalSpace P (fun s ↦ i.NormalSpace s hn),
      Continuous scale ∧ Injective scale ∧
      (∀ v, -(2⁻¹ * h.normalHessian hn (scale v).proj (scale v).snd (scale v).snd) =
        ε * ‖v.snd‖ ^ 2) ∧
      scale '' discBundle (Fin r → ℝ) ν = h.negativeDiscBundle hn P g.toRiemannianMetric ε := by
  have : IsManifold I (∞ + 2) M := .of_le (n := ∞) (by simp)
  have : IsManifold J (∞ + 1) S := .of_le (n := ∞) (by simp)
  let := i.normalSpaceFiberBundle hn hdim
  let := i.normalSpaceVectorBundle hn hdim
  let hV := h.hasLocalContMDiffSubbundleFrames_negativeNormalSpace hn (by simp)
    (fun s ↦ (hfs (i s)).of_le (by simp)) hdim g hr
  let ν : S → Type u := fun s ↦ h.negativeNormalSpace hn g.toRiemannianMetric s
  let := subbundleTopology P (F' := Fin r → ℝ) (h.negativeNormalSpace hn g.toRiemannianMetric)
  let := hV.fiberBundle
  let := hV.vectorBundle
  let : RiemannianBundle ν := ⟨(h.negativeNormalHessianMetric hn (by simp)
    (fun s ↦ (hfs (i s)).of_le (by simp)) hdim g hr).toRiemannianMetric⟩
  let : ∀ s, NormedAddCommGroup (ν s) := fun s ↦ inferInstance
  have hsq : Real.sqrt ε ≠ 0 := Real.sqrt_ne_zero'.mpr hε
  let scale : TotalSpace (Fin r → ℝ) ν → TotalSpace P (fun s ↦ i.NormalSpace s hn) :=
    fun v ↦ TotalSpace.mk' P v.proj (Real.sqrt ε • v.snd.val)
  have hcont : Continuous scale :=
    (Continuous.smul_totalSpace continuous_const continuous_id).comp
      (isEmbedding_totalSpace_subbundle P (Fin r → ℝ)
        (h.negativeNormalSpace hn g.toRiemannianMetric)).continuous
  have hinj : Injective scale := by
    intro ⟨s₁, v₁⟩ ⟨s₂, v₂⟩ hEq
    obtain rfl : s₁ = s₂ := congrArg TotalSpace.proj hEq
    dsimp only [scale, TotalSpace.mk'] at hEq
    have h2 : Real.sqrt ε • v₁.val = Real.sqrt ε • v₂.val :=
      (TotalSpace.mk_inj (E := fun s ↦ i.NormalSpace s hn)).mp hEq
    exact congrArg (TotalSpace.mk s₁) (Subtype.ext (smul_right_injective _ hsq h2))
  have hhess (v : TotalSpace (Fin r → ℝ) ν) :
      -(2⁻¹ * h.normalHessian hn (scale v).proj (scale v).snd (scale v).snd) = ε * ‖v.snd‖ ^ 2 := by
    have hnorm := h.norm_sq_eq_of_negativeNormalHessianMetric hn (by simp)
      (fun s ↦ (hfs (i s)).of_le (by simp)) hdim g hr v.proj v.snd
    simp only [scale, TotalSpace.mk', map_smul, LinearMap.smul_apply, smul_eq_mul]
    rw [hnorm]
    have : Real.sqrt ε * (Real.sqrt ε * h.normalHessian hn v.proj v.snd.val v.snd.val) =
        Real.sqrt ε ^ 2 * h.normalHessian hn v.proj v.snd.val v.snd.val := by ring
    rw [this, Real.sq_sqrt hε.le]
    ring
  refine ⟨scale, hcont, hinj, hhess, Subset.antisymm ?_ ?_⟩
  · rintro _ ⟨v, hv, rfl⟩
    refine (IsCriticalSubmanifold.mem_negativeDiscBundle hn).2
      ⟨Submodule.smul_mem _ _ v.snd.property, ?_⟩
    rw [hhess v]
    have hle : ‖v.snd‖ ^ 2 ≤ 1 := by nlinarith [mem_discBundle.1 hv, norm_nonneg v.snd]
    nlinarith
  · intro x hx
    obtain ⟨hxmem, hxle⟩ := (IsCriticalSubmanifold.mem_negativeDiscBundle hn).1 hx
    let v : TotalSpace (Fin r → ℝ) ν :=
      ⟨x.proj, ⟨(Real.sqrt ε)⁻¹ • x.snd, Submodule.smul_mem _ _ hxmem⟩⟩
    have hsv : scale v = x := by
      cases x
      simp [scale, v, TotalSpace.mk', smul_inv_smul₀ hsq]
    refine ⟨v, mem_discBundle.2 ?_, hsv⟩
    have hsqle : ε * ‖v.snd‖ ^ 2 ≤ ε := by
      rw [← hhess v, hsv]
      exact hxle
    have hle1 : ‖v.snd‖ ^ 2 ≤ 1 := by nlinarith
    nlinarith [norm_nonneg v.snd]

omit [SecondCountableTopology M] [J.Boundaryless] in
/-- Given a Morse–Bott normal form `Θ` and `ε > 0` with `D_ε ⊆ Θ.source`, the rescaled map
`v ↦ Θ (√ε • v)` attaches the unit disc bundle `D(ν⁻)` along `S(ν⁻)` to `{f ≤ c - ε}` to form
`{f ≤ c + ε} ∩ ({f ≤ c - ε} ∪ Θ(D_ε))`, inducing isomorphisms on relative homology and
cohomology. -/
private theorem exists_attach_discSpherePair_isIso
    (h : i.IsNondegenerateCriticalSubmanifold f) (hfs : ContMDiff I 𝓘(ℝ) ∞ f) {c : ℝ}
    (hdim : finrank ℝ P = finrank ℝ E - finrank ℝ E')
    (g : letI := i.normalSpaceFiberBundle hn hdim
      letI := i.normalSpaceVectorBundle hn hdim
      ContMDiffRiemannianMetric J ∞ P fun s ↦ i.NormalSpace s hn) {r : ℕ}
    (hr : ∀ s, manifoldMorseIndex I f (i s) = r)
    (Θ : letI := i.normalSpaceFiberBundle hn hdim
      letI := i.normalSpaceVectorBundle hn hdim
      PartialDiffeomorph (J.prod 𝓘(ℝ, P)) I (TotalSpace P fun s ↦ i.NormalSpace s hn) M ∞)
    (hΘf : ∀ x ∈ Θ.source, f (Θ x) = c + 2⁻¹ * h.normalHessian hn x.proj x.snd x.snd)
    {ε : ℝ} (hε : 0 < ε)
    (hDsub : letI := i.normalSpaceFiberBundle hn hdim
      letI := i.normalSpaceVectorBundle hn hdim
      h.negativeDiscBundle hn P g.toRiemannianMetric ε ⊆ Θ.source) :
    haveI : IsManifold I (∞ + 2) M := .of_le (n := ∞) (by simp)
    haveI : IsManifold J (∞ + 1) S := .of_le (n := ∞) (by simp)
    letI := i.normalSpaceFiberBundle hn hdim
    letI := i.normalSpaceVectorBundle hn hdim
    letI hV := h.hasLocalContMDiffSubbundleFrames_negativeNormalSpace hn (by simp)
      (fun s ↦ (hfs (i s)).of_le (by simp)) hdim g hr
    letI ν : S → Type u := fun s ↦ h.negativeNormalSpace hn g.toRiemannianMetric s
    letI : TopologicalSpace (TotalSpace (Fin r → ℝ) ν) :=
      subbundleTopology P (F' := Fin r → ℝ) (h.negativeNormalSpace hn g.toRiemannianMetric)
    letI : FiberBundle (Fin r → ℝ) ν := hV.fiberBundle
    letI : VectorBundle ℝ (Fin r → ℝ) ν := hV.vectorBundle
    letI : RiemannianBundle ν :=
      ⟨(h.negativeNormalHessianMetric hn (by simp) (fun s ↦ (hfs (i s)).of_le (by simp)) hdim g
        hr).toRiemannianMetric⟩
    letI : ∀ s, NormedAddCommGroup (ν s) := fun s ↦ inferInstance
    let Z : Set M := {y | f y ≤ c + ε} ∩
      ({y | f y ≤ c - ε} ∪ Θ '' h.negativeDiscBundle hn P g.toRiemannianMetric ε)
    ∃ φ : gaugeDiscSpherePair (fun v : TotalSpace (Fin r → ℝ) ν ↦ ‖v.snd‖) ⟶
        TopPair.ofSubset (X := TopCat.of Z) (Subtype.val ⁻¹' {y | f y ≤ c - ε}),
      (∀ {A : Type v} [Category.{w} A] [HasCoproducts.{u} A] [Abelian A] (R : A) (m : ℕ),
        IsIso (TopPair.singularHomologyMap φ R m)) ∧
      (∀ {A : Type v} [Category.{w} A] [HasCoproducts.{u} A] [Abelian A] (R : A)
        (k : Type w') [Ring k] [Linear k A] (M' : A) (m : ℕ),
        IsIso (TopPair.singularCohomologyMap (R := R) (k := k) (M := M') φ m)) := by
  have : IsManifold I (∞ + 2) M := .of_le (n := ∞) (by simp)
  have : IsManifold J (∞ + 1) S := .of_le (n := ∞) (by simp)
  let := i.normalSpaceFiberBundle hn hdim
  let := i.normalSpaceVectorBundle hn hdim
  let hV := h.hasLocalContMDiffSubbundleFrames_negativeNormalSpace hn (by simp)
    (fun s ↦ (hfs (i s)).of_le (by simp)) hdim g hr
  let ν : S → Type u := fun s ↦ h.negativeNormalSpace hn g.toRiemannianMetric s
  let := subbundleTopology P (F' := Fin r → ℝ) (h.negativeNormalSpace hn g.toRiemannianMetric)
  let := hV.fiberBundle
  let := hV.vectorBundle
  let : RiemannianBundle ν := ⟨(h.negativeNormalHessianMetric hn (by simp)
    (fun s ↦ (hfs (i s)).of_le (by simp)) hdim g hr).toRiemannianMetric⟩
  let : ∀ s, NormedAddCommGroup (ν s) := fun s ↦ inferInstance
  let : ∀ s, InnerProductSpace ℝ (ν s) := fun s ↦ inferInstance
  let := Bundle.instIsContinuousRiemannianBundle
    (h.negativeNormalHessianMetric hn (by simp) (fun s ↦ (hfs (i s)).of_le (by simp)) hdim g hr)
  let Dε := h.negativeDiscBundle hn P g.toRiemannianMetric ε
  let Z : Set M := {y | f y ≤ c + ε} ∩ ({y | f y ≤ c - ε} ∪ Θ '' Dε)
  let ρ : TotalSpace (Fin r → ℝ) ν → ℝ := fun v ↦ ‖v.snd‖
  obtain ⟨scale, hscale_cont, hscale_inj, hscale_hess, hscale_img⟩ :=
    h.exists_rescale_negativeDiscBundle hn hfs hdim g hr hε
  rw [discBundle_def] at hscale_img
  have hscale_mem {v : TotalSpace (Fin r → ℝ) ν} (hv : v ∈ gaugeDiscBundle ρ) :
      scale v ∈ Dε := by
    dsimp only [Dε]
    rw [← hscale_img]
    exact mem_image_of_mem scale hv
  have hf_val {v : TotalSpace (Fin r → ℝ) ν} (hv : v ∈ gaugeDiscBundle ρ) :
      f (Θ (scale v)) = c - ε * ‖v.snd‖ ^ 2 := by
    rw [hΘf (scale v) (hDsub (hscale_mem hv))]
    linarith [hscale_hess v]
  have hf_le_iff {v : TotalSpace (Fin r → ℝ) ν} (hv : v ∈ gaugeDiscBundle ρ) :
      f (Θ (scale v)) ≤ c - ε ↔ v ∈ gaugeSphereBundle ρ := by
    rw [hf_val hv, mem_gaugeSphereBundle]
    have hv1 : ‖v.snd‖ ≤ 1 := mem_gaugeDiscBundle.1 hv
    have hv0 : 0 ≤ ‖v.snd‖ := norm_nonneg v.snd
    exact ⟨fun hle ↦ by
        dsimp only [ρ]
        have hsq_ge : 1 ≤ ‖v.snd‖ ^ 2 := by nlinarith
        nlinarith,
      fun heq ↦ by dsimp only [ρ] at heq; rw [heq]; linarith⟩
  -- The attaching map `φ : D(ν⁻) → Z` sends `v` to `Θ (√ε • v)`.
  have hφ_le (v : gaugeDiscBundle ρ) : f (Θ (scale v.val)) ≤ c + ε := by
    rw [hf_val v.property]
    nlinarith [sq_nonneg ‖v.val.snd‖]
  let φ : C(gaugeDiscBundle ρ, Z) :=
    { toFun := fun v ↦ ⟨Θ (scale v.val),
        ⟨hφ_le v, Or.inr ⟨scale v.val, hscale_mem v.property, rfl⟩⟩⟩
      continuous_toFun := Continuous.subtype_mk
        (Θ.toOpenPartialHomeomorph.continuousOn.comp_continuous
          (hscale_cont.comp continuous_subtypeVal) fun v ↦ hDsub (hscale_mem v.property)) _ }
  have hφ_emb : IsClosedEmbedding φ := by
    have hD_eq : gaugeDiscBundle ρ = {p : TotalSpace (Fin r → ℝ) ν | ‖p.snd‖ ≤ 1} :=
      Set.ext fun _ ↦ mem_gaugeDiscBundle
    have : CompactSpace (gaugeDiscBundle ρ) :=
      isCompact_iff_compactSpace.mp (hD_eq ▸
        TauCeti.isCompact_setOf_norm_le_bundle (F := Fin r → ℝ) (V := ν) (r := fun _ ↦ 1)
          continuous_const)
    refine φ.continuous.isClosedEmbedding fun v w hvw ↦ ?_
    have hΘeq : Θ (scale v.val) = Θ (scale w.val) := congrArg Subtype.val hvw
    exact Subtype.ext
      (hscale_inj (Θ.injOn (hDsub (hscale_mem v.property)) (hDsub (hscale_mem w.property)) hΘeq))
  have hX : IsClosed (Subtype.val ⁻¹' {y : M | f y ≤ c - ε} : Set Z) :=
    isClosed_le (hfs.continuous.comp continuous_subtypeVal) continuous_const
  have hcover : (Subtype.val ⁻¹' {y : M | f y ≤ c - ε} : Set Z) ∪ range φ = univ := by
    refine eq_univ_of_forall fun z ↦ ?_
    rcases z.property.2 with hz | ⟨x, hx, hxz⟩
    · exact Or.inl hz
    · obtain ⟨v, hv, rfl⟩ := hscale_img.symm.subset hx
      exact Or.inr ⟨⟨v, hv⟩, Subtype.ext hxz⟩
  let φ_pair : gaugeDiscSpherePair ρ ⟶
      TopPair.ofSubset (X := TopCat.of Z) (Subtype.val ⁻¹' {y | f y ≤ c - ε}) :=
    TopPair.ofHom (TopCat.ofHom φ)
      (TopCat.ofHom ⟨fun v ↦ ⟨φ ⟨v.val, gaugeSphereBundle_subset_gaugeDiscBundle ρ v.property⟩,
        (hf_le_iff (gaugeSphereBundle_subset_gaugeDiscBundle ρ v.property)).2 v.property⟩,
        (φ.continuous.comp (continuous_subtypeVal.subtype_mk _)).subtype_mk _⟩)
      (TopCat.ext fun _ ↦ rfl)
  have hφ_pre (v : gaugeDiscBundle ρ)
      (hv : TopPair.Hom.fst φ_pair v ∈ (Subtype.val ⁻¹' {y : M | f y ≤ c - ε} : Set Z)) :
      v.val ∈ gaugeSphereBundle ρ :=
    (hf_le_iff v.property).1 hv
  have hρ : IsFiberGauge ρ := isFiberGauge_norm (TauCeti.continuous_norm_bundle (Fin r → ℝ) ν)
  exact ⟨φ_pair,
    fun {A} _ _ _ R m ↦ isIso_singularHomologyMap_of_attach_gaugeDiscBundle hρ hX R m hφ_emb
      hφ_pre hcover,
    fun {A} _ _ _ R k _ _ M' m ↦
      isIso_singularCohomologyMap_of_attach_gaugeDiscBundle hρ hX R m k M' hφ_emb hφ_pre hcover⟩

/-- **Attaching the disc-sphere pair across a compact Morse–Bott submanifold.** Let `i : S → M`
be a compact nondegenerate critical submanifold of a smooth function `f` on a boundaryless
manifold, on the level `f = c` with constant Morse index `r`, and let `g` be a smooth fibre metric
on its normal bundle. Equip the negative normal bundle `ν⁻` with the Hessian fibre metric
`negativeNormalHessianMetric`. Then there is `ε₀ > 0` such that for every `ε ∈ (0, ε₀)` whose band
`f⁻¹[c - ε, c + ε]` is compact with all its critical points on `i`, there is a map of pairs
`(D(ν⁻), S(ν⁻)) ⟶ ({f ≤ c + ε}, {f ≤ c - ε})` inducing isomorphisms on both relative singular
homology and relative singular cohomology, with arbitrary coefficients, in every degree. -/
theorem exists_discSpherePairMap_isIso_sublevelPair
    (h : i.IsNondegenerateCriticalSubmanifold f) (hfs : ContMDiff I 𝓘(ℝ) ∞ f) {c : ℝ}
    (hc : ∀ s, f (i s) = c) (hdim : finrank ℝ P = finrank ℝ E - finrank ℝ E')
    (g : letI := i.normalSpaceFiberBundle hn hdim
      letI := i.normalSpaceVectorBundle hn hdim
      ContMDiffRiemannianMetric J ∞ P fun s ↦ i.NormalSpace s hn) {r : ℕ}
    (hr : ∀ s, manifoldMorseIndex I f (i s) = r) :
    haveI : IsManifold I (∞ + 2) M := .of_le (n := ∞) (by simp)
    haveI : IsManifold J (∞ + 1) S := .of_le (n := ∞) (by simp)
    letI := i.normalSpaceFiberBundle hn hdim
    letI := i.normalSpaceVectorBundle hn hdim
    letI hV := h.hasLocalContMDiffSubbundleFrames_negativeNormalSpace hn (by simp)
      (fun s ↦ (hfs (i s)).of_le (by simp)) hdim g hr
    letI ν : S → Type u := fun s ↦ h.negativeNormalSpace hn g.toRiemannianMetric s
    letI : TopologicalSpace (TotalSpace (Fin r → ℝ) ν) :=
      subbundleTopology P (F' := Fin r → ℝ) (h.negativeNormalSpace hn g.toRiemannianMetric)
    letI : FiberBundle (Fin r → ℝ) ν := hV.fiberBundle
    letI : VectorBundle ℝ (Fin r → ℝ) ν := hV.vectorBundle
    letI : RiemannianBundle ν :=
      ⟨(h.negativeNormalHessianMetric hn (by simp) (fun s ↦ (hfs (i s)).of_le (by simp)) hdim g
        hr).toRiemannianMetric⟩
    letI : ∀ s, NormedAddCommGroup (ν s) := fun s ↦ inferInstance
    ∃ ε₀ > 0, ∀ ε (hε : ε ∈ Ioo 0 ε₀), IsCompact (f ⁻¹' Icc (c - ε) (c + ε)) →
      criticalPoints I f ∩ f ⁻¹' Icc (c - ε) (c + ε) ⊆ range i →
      ∃ ψ : gaugeDiscSpherePair (fun v : TotalSpace (Fin r → ℝ) ν ↦ ‖v.snd‖) ⟶
          sublevelPair f (a := c - ε) (b := c + ε) (by linarith [hε.1]),
        (∀ {A : Type v} [Category.{w} A] [HasCoproducts.{u} A] [Abelian A] (R : A) (m : ℕ),
          IsIso (TopPair.singularHomologyMap ψ R m)) ∧
        (∀ {A : Type v} [Category.{w} A] [HasCoproducts.{u} A] [Abelian A] (R : A)
          (k : Type w') [Ring k] [Linear k A] (M' : A) (m : ℕ),
          IsIso (TopPair.singularCohomologyMap (R := R) (k := k) (M := M') ψ m)) := by
  rcases isEmpty_or_nonempty S with hS | hS
  · exact h.exists_discSpherePairMap_isIso_sublevelPair_of_isEmpty hn hfs hdim g hr
  have : Nonempty S := hS
  have : IsManifold I (∞ + 2) M := .of_le (n := ∞) (by simp)
  have : IsManifold J (∞ + 1) S := .of_le (n := ∞) (by simp)
  let := i.normalSpaceFiberBundle hn hdim
  let := i.normalSpaceVectorBundle hn hdim
  let hV := h.hasLocalContMDiffSubbundleFrames_negativeNormalSpace hn (by simp)
    (fun s ↦ (hfs (i s)).of_le (by simp)) hdim g hr
  let ν : S → Type u := fun s ↦ h.negativeNormalSpace hn g.toRiemannianMetric s
  let : TopologicalSpace (TotalSpace (Fin r → ℝ) ν) :=
    subbundleTopology P (F' := Fin r → ℝ) (h.negativeNormalSpace hn g.toRiemannianMetric)
  let : FiberBundle (Fin r → ℝ) ν := hV.fiberBundle
  let : VectorBundle ℝ (Fin r → ℝ) ν := hV.vectorBundle
  let : RiemannianBundle ν :=
    ⟨(h.negativeNormalHessianMetric hn (by simp) (fun s ↦ (hfs (i s)).of_le (by simp)) hdim g
      hr).toRiemannianMetric⟩
  let : ∀ s, NormedAddCommGroup (ν s) := fun s ↦ inferInstance
  obtain ⟨Θ, -, -, hΘf, ε₀, hε₀, hdef⟩ :=
    h.exists_sublevel_union_negativeDiscBundle_deformation hn hfs hc hdim g
  refine ⟨ε₀, hε₀, fun ε hε hcomp hcrit ↦ ?_⟩
  have hle : c - ε ≤ c + ε := by linarith [hε.1]
  obtain ⟨hDsub, rdef, -, ⟨G⟩⟩ := hdef ε hε hcomp hcrit
  obtain ⟨φ_pair, hφH, hφC⟩ := h.exists_attach_discSpherePair_isIso hn hfs hdim g hr Θ hΘf hε.1
    hDsub
  let Z : Set M := {y | f y ≤ c + ε} ∩
    ({y | f y ≤ c - ε} ∪ Θ '' h.negativeDiscBundle hn P g.toRiemannianMetric ε)
  have hsubZ : {y | f y ≤ c - ε} ⊆ Z := fun y hy ↦ by
    have hfy : f y ≤ c - ε := hy
    have hle_add : f y ≤ c + ε := by linarith [hε.1]
    exact ⟨hle_add, Or.inl hy⟩
  have hrel : {y : {y | f y ≤ c + ε} | (y : M) ∈
      {y | f y ≤ c - ε} ∪ Θ '' h.negativeDiscBundle hn P g.toRiemannianMetric ε} =
      {y : {y | f y ≤ c + ε} | (y : M) ∈ Z} :=
    Set.ext fun y ↦ ⟨fun hy ↦ ⟨y.property, hy⟩, fun hy ↦ hy.2⟩
  rw [hrel] at G
  let eZ := TopPair.ofSubsetPreimageValIso (X := TopCat.of M) hsubZ
  let ι : TopPair.ofInclusion (X := TopCat.of M) hsubZ ⟶ sublevelPair f hle :=
    TopPair.ofInclusionMap hsubZ (sublevel_mono f hle)
      (ContinuousMap.inclusion inter_subset_left) fun _ hx ↦ hx
  refine ⟨φ_pair ≫ eZ.hom ≫ ι, fun {A} _ _ _ R m ↦ ?_, fun {A} _ _ _ R k _ _ M' m ↦ ?_⟩
  · have := hφH R m
    have : IsIso (TopPair.singularHomologyMap eZ.hom R m) :=
      (TopPair.singularHomologyMapIso R eZ m).isIso_hom
    have : IsIso (TopPair.singularHomologyMap ι R m) :=
      TopPair.isIso_singularHomologyMap_ofInclusionMap_inclusion_of_homotopyRel
        (X := TopCat.of M) hsubZ inter_subset_left rdef G R m
    rw [TopPair.singularHomologyMap_comp, TopPair.singularHomologyMap_comp]
    infer_instance
  · have := hφC R k M' m
    have : IsIso (TopPair.singularCohomologyMap (R := R) (k := k) (M := M') eZ.hom m) :=
      ⟨⟨TopPair.singularCohomologyMap eZ.inv m,
        by rw [← TopPair.singularCohomologyMap_comp, eZ.inv_hom_id,
          TopPair.singularCohomologyMap_id],
        by rw [← TopPair.singularCohomologyMap_comp, eZ.hom_inv_id,
          TopPair.singularCohomologyMap_id]⟩⟩
    have : IsIso (TopPair.singularCohomologyMap (R := R) (k := k) (M := M') ι m) :=
      TopPair.isIso_singularCohomologyMap_ofInclusionMap_inclusion_of_homotopyRel
        (X := TopCat.of M) hsubZ inter_subset_left rdef G R k M' m
    rw [TopPair.singularCohomologyMap_comp, TopPair.singularCohomologyMap_comp]
    infer_instance

/-- **Relative homology across a compact Morse–Bott submanifold equals that of the Thom pair
(small band).** For small `ε > 0` with compact band `f⁻¹[c - ε, c + ε]` whose critical points lie
on `i`, `Hₙ({f ≤ c + ε}, {f ≤ c - ε}; R) ≅ Hₙ(ν⁻, ν⁻₀; R)` in every degree, with coefficients in
any abelian category with coproducts. -/
theorem exists_singularHomology_sublevelPair_iso_thomPair
    (h : i.IsNondegenerateCriticalSubmanifold f) (hfs : ContMDiff I 𝓘(ℝ) ∞ f) {c : ℝ}
    (hc : ∀ s, f (i s) = c) (hdim : finrank ℝ P = finrank ℝ E - finrank ℝ E')
    (g : letI := i.normalSpaceFiberBundle hn hdim
      letI := i.normalSpaceVectorBundle hn hdim
      ContMDiffRiemannianMetric J ∞ P fun s ↦ i.NormalSpace s hn) {r : ℕ}
    (hr : ∀ s, manifoldMorseIndex I f (i s) = r) :
    letI := i.normalSpaceFiberBundle hn hdim
    letI := i.normalSpaceVectorBundle hn hdim
    letI := subbundleTopology P (F' := Fin r → ℝ) (h.negativeNormalSpace hn g.toRiemannianMetric)
    ∃ ε₀ > 0, ∀ ε (hε : ε ∈ Ioo 0 ε₀), IsCompact (f ⁻¹' Icc (c - ε) (c + ε)) →
      criticalPoints I f ∩ f ⁻¹' Icc (c - ε) (c + ε) ⊆ range i →
      ∀ {A : Type v} [Category.{w} A] [HasCoproducts.{u} A] [Abelian A] (R : A) (m : ℕ),
        Nonempty ((sublevelPair f (a := c - ε) (b := c + ε) (by linarith [hε.1])).singularHomology
            R m ≅
          (thomPair (Fin r → ℝ)
            (fun s ↦ h.negativeNormalSpace hn g.toRiemannianMetric s)).singularHomology R m) := by
  have : IsManifold I (∞ + 2) M := .of_le (n := ∞) (by simp)
  have : IsManifold J (∞ + 1) S := .of_le (n := ∞) (by simp)
  let := i.normalSpaceFiberBundle hn hdim
  let := i.normalSpaceVectorBundle hn hdim
  let hV := h.hasLocalContMDiffSubbundleFrames_negativeNormalSpace hn (by simp)
    (fun s ↦ (hfs (i s)).of_le (by simp)) hdim g hr
  let ν : S → Type u := fun s ↦ h.negativeNormalSpace hn g.toRiemannianMetric s
  let := subbundleTopology P (F' := Fin r → ℝ) (h.negativeNormalSpace hn g.toRiemannianMetric)
  let := hV.fiberBundle
  let := hV.vectorBundle
  let : RiemannianBundle ν := ⟨(h.negativeNormalHessianMetric hn (by simp)
    (fun s ↦ (hfs (i s)).of_le (by simp)) hdim g hr).toRiemannianMetric⟩
  let : ∀ s, NormedAddCommGroup (ν s) := fun s ↦ inferInstance
  let : ∀ s, InnerProductSpace ℝ (ν s) := fun s ↦ inferInstance
  let := Bundle.instIsContinuousRiemannianBundle
    (h.negativeNormalHessianMetric hn (by simp) (fun s ↦ (hfs (i s)).of_le (by simp)) hdim g hr)
  obtain ⟨ε₀, hε₀, hψ⟩ :=
    h.exists_discSpherePairMap_isIso_sublevelPair.{u, v, w, 0, _, _, _, _} hn hfs hc hdim g hr
  refine ⟨ε₀, hε₀, fun ε hε hcomp hcrit {A} _ _ _ R m ↦ ?_⟩
  obtain ⟨ψ, hψH, -⟩ := hψ ε hε hcomp hcrit
  have hρ := isFiberGauge_norm (TauCeti.continuous_norm_bundle (Fin r → ℝ) ν)
  have := hψH R m
  have := isIso_singularHomologyMap_gaugeDiscSpherePairMap hρ R m
  exact ⟨(asIso (TopPair.singularHomologyMap ψ R m)).symm ≪≫
    asIso (TopPair.singularHomologyMap (gaugeDiscSpherePairMap hρ) R m)⟩

/-- **Relative cohomology across a compact Morse–Bott submanifold equals that of the Thom pair.**
For small `ε > 0` with compact band `f⁻¹[c - ε, c + ε]` whose critical points lie on `i`,
`Hⁿ({f ≤ c + ε}, {f ≤ c - ε}; R, M') ≅ Hⁿ(ν⁻, ν⁻₀; R, M')` in every degree, with arbitrary
coefficients in any `k`-linear abelian category with coproducts. -/
theorem exists_singularCohomology_sublevelPair_iso_thomPair
    (h : i.IsNondegenerateCriticalSubmanifold f) (hfs : ContMDiff I 𝓘(ℝ) ∞ f) {c : ℝ}
    (hc : ∀ s, f (i s) = c) (hdim : finrank ℝ P = finrank ℝ E - finrank ℝ E')
    (g : letI := i.normalSpaceFiberBundle hn hdim
      letI := i.normalSpaceVectorBundle hn hdim
      ContMDiffRiemannianMetric J ∞ P fun s ↦ i.NormalSpace s hn) {r : ℕ}
    (hr : ∀ s, manifoldMorseIndex I f (i s) = r) :
    letI := i.normalSpaceFiberBundle hn hdim
    letI := i.normalSpaceVectorBundle hn hdim
    letI := subbundleTopology P (F' := Fin r → ℝ) (h.negativeNormalSpace hn g.toRiemannianMetric)
    ∃ ε₀ > 0, ∀ ε (hε : ε ∈ Ioo 0 ε₀), IsCompact (f ⁻¹' Icc (c - ε) (c + ε)) →
      criticalPoints I f ∩ f ⁻¹' Icc (c - ε) (c + ε) ⊆ range i →
      ∀ {A : Type v} [Category.{w} A] [HasCoproducts.{u} A] [Abelian A] (R : A)
        (k : Type w') [Ring k] [Linear k A] (M' : A) (m : ℕ),
        Nonempty ((sublevelPair f (a := c - ε) (b := c + ε) (by linarith [hε.1])).singularCohomology
            R k M' m ≅
          (thomPair (Fin r → ℝ)
            (fun s ↦ h.negativeNormalSpace hn g.toRiemannianMetric s)).singularCohomology
            R k M' m) := by
  have : IsManifold I (∞ + 2) M := .of_le (n := ∞) (by simp)
  have : IsManifold J (∞ + 1) S := .of_le (n := ∞) (by simp)
  let := i.normalSpaceFiberBundle hn hdim
  let := i.normalSpaceVectorBundle hn hdim
  let hV := h.hasLocalContMDiffSubbundleFrames_negativeNormalSpace hn (by simp)
    (fun s ↦ (hfs (i s)).of_le (by simp)) hdim g hr
  let ν : S → Type u := fun s ↦ h.negativeNormalSpace hn g.toRiemannianMetric s
  let := subbundleTopology P (F' := Fin r → ℝ) (h.negativeNormalSpace hn g.toRiemannianMetric)
  let := hV.fiberBundle
  let := hV.vectorBundle
  let : RiemannianBundle ν := ⟨(h.negativeNormalHessianMetric hn (by simp)
    (fun s ↦ (hfs (i s)).of_le (by simp)) hdim g hr).toRiemannianMetric⟩
  let : ∀ s, NormedAddCommGroup (ν s) := fun s ↦ inferInstance
  let : ∀ s, InnerProductSpace ℝ (ν s) := fun s ↦ inferInstance
  let := Bundle.instIsContinuousRiemannianBundle
    (h.negativeNormalHessianMetric hn (by simp) (fun s ↦ (hfs (i s)).of_le (by simp)) hdim g hr)
  obtain ⟨ε₀, hε₀, hψ⟩ := h.exists_discSpherePairMap_isIso_sublevelPair hn hfs hc hdim g hr
  refine ⟨ε₀, hε₀, fun ε hε hcomp hcrit {A} _ _ _ R k _ _ M' m ↦ ?_⟩
  obtain ⟨ψ, -, hψC⟩ := hψ ε hε hcomp hcrit
  have hρ := isFiberGauge_norm (TauCeti.continuous_norm_bundle (Fin r → ℝ) ν)
  have := hψC R k M' m
  have := isIso_singularCohomologyMap_gaugeDiscSpherePairMap hρ R k M' m
  exact ⟨asIso (TopPair.singularCohomologyMap (R := R) (k := k) (M := M') ψ m) ≪≫
    (asIso (TopPair.singularCohomologyMap (R := R) (k := k) (M := M')
      (gaugeDiscSpherePairMap hρ) m)).symm⟩

/-! ### Arbitrary compact isolated bands and consequences -/

/-- **Relative homology across a compact Morse–Bott submanifold equals that of the Thom pair.**
Let `i : S → M` be a compact nondegenerate critical submanifold of a smooth function `f` on a
boundaryless manifold, on the level `f = c` with constant Morse index `r`, and let `g` be a smooth
fibre metric on its normal bundle. For any compact band `f⁻¹[a, b]` with `a < c < b` whose
critical points all lie on `i`, `Hₙ({f ≤ b}, {f ≤ a}; R) ≅ Hₙ(ν⁻, ν⁻₀; R)` in every degree, with
coefficients in any abelian category with coproducts. -/
theorem nonempty_singularHomology_sublevelPair_iso_thomPair
    (h : i.IsNondegenerateCriticalSubmanifold f) (hfs : ContMDiff I 𝓘(ℝ) ∞ f) {c a b : ℝ}
    (hc : ∀ s, f (i s) = c) (hdim : finrank ℝ P = finrank ℝ E - finrank ℝ E')
    (g : letI := i.normalSpaceFiberBundle hn hdim
      letI := i.normalSpaceVectorBundle hn hdim
      ContMDiffRiemannianMetric J ∞ P fun s ↦ i.NormalSpace s hn) {r : ℕ}
    (hr : ∀ s, manifoldMorseIndex I f (i s) = r) (hac : a < c) (hcb : c < b)
    (hcomp : IsCompact (f ⁻¹' Icc a b)) (hcrit : criticalPoints I f ∩ f ⁻¹' Icc a b ⊆ range i)
    {A : Type v} [Category.{w} A] [HasCoproducts.{u} A] [Abelian A] (R : A) (m : ℕ) :
    letI := i.normalSpaceFiberBundle hn hdim
    letI := i.normalSpaceVectorBundle hn hdim
    letI := subbundleTopology P (F' := Fin r → ℝ) (h.negativeNormalSpace hn g.toRiemannianMetric)
    Nonempty ((sublevelPair f (hac.trans hcb).le).singularHomology R m ≅
      (thomPair (Fin r → ℝ)
        (fun s ↦ h.negativeNormalSpace hn g.toRiemannianMetric s)).singularHomology R m) := by
  let := i.normalSpaceFiberBundle hn hdim
  let := i.normalSpaceVectorBundle hn hdim
  let := subbundleTopology P (F' := Fin r → ℝ) (h.negativeNormalSpace hn g.toRiemannianMetric)
  obtain ⟨ε₀, hε₀, hsmall⟩ :=
    h.exists_singularHomology_sublevelPair_iso_thomPair hn hfs hc hdim g hr
  set ε := min (ε₀ / 2) (min ((c - a) / 2) ((b - c) / 2))
  have hε_pos : 0 < ε := lt_min (by linarith) (lt_min (by linarith) (by linarith))
  have hε_lt : ε < ε₀ := (min_le_left _ _).trans_lt (by linarith)
  have haε : a ≤ c - ε := by
    linarith [min_le_right (ε₀ / 2) (min ((c - a) / 2) ((b - c) / 2)),
      min_le_left ((c - a) / 2) ((b - c) / 2)]
  have hεb : c + ε ≤ b := by
    linarith [min_le_right (ε₀ / 2) (min ((c - a) / 2) ((b - c) / 2)),
      min_le_right ((c - a) / 2) ((b - c) / 2)]
  have hsubIcc : Icc (c - ε) (c + ε) ⊆ Icc a b := Icc_subset_Icc haε hεb
  have hcompε : IsCompact (f ⁻¹' Icc (c - ε) (c + ε)) :=
    hcomp.of_isClosed_subset (isClosed_Icc.preimage hfs.continuous) (preimage_mono hsubIcc)
  have hcritε : criticalPoints I f ∩ f ⁻¹' Icc (c - ε) (c + ε) ⊆ range i :=
    (inter_subset_inter_right _ (preimage_mono hsubIcc)).trans hcrit
  obtain ⟨eThom⟩ := hsmall ε ⟨hε_pos, hε_lt⟩ hcompε hcritε R m
  have hval {s t : ℝ} (hcr : criticalPoints I f ∩ f ⁻¹' Icc s t ⊆ range i) :
      ∀ x ∈ criticalPoints I f, f x ∈ Icc s t → f x = c := fun x hx hfx ↦ by
    obtain ⟨p, rfl⟩ := hcr ⟨hx, hfx⟩
    exact hc p
  exact ⟨singularHomologySublevelPairIsoOfCriticalValue hfs hac hcb (by linarith) (by linarith)
    hcomp hcompε (hval hcrit) (hval hcritε) R m ≪≫ eThom⟩

/-- **Relative homology across a connected compact Morse–Bott submanifold.** On a connected
compact Morse–Bott submanifold the Morse index is constant, so the relative homology of any
compact isolated band around its level is that of the Thom pair of its negative normal bundle of
rank `manifoldMorseIndex I f (i s₀)`. -/
theorem nonempty_singularHomology_sublevelPair_iso_thomPair_of_preconnectedSpace
    [PreconnectedSpace S] (h : i.IsNondegenerateCriticalSubmanifold f) (hfs : ContMDiff I 𝓘(ℝ) ∞ f)
    {c a b : ℝ} (hc : ∀ s, f (i s) = c) (hdim : finrank ℝ P = finrank ℝ E - finrank ℝ E')
    (g : letI := i.normalSpaceFiberBundle hn hdim
      letI := i.normalSpaceVectorBundle hn hdim
      ContMDiffRiemannianMetric J ∞ P fun s ↦ i.NormalSpace s hn)
    (s₀ : S) (hac : a < c) (hcb : c < b) (hcomp : IsCompact (f ⁻¹' Icc a b))
    (hcrit : criticalPoints I f ∩ f ⁻¹' Icc a b ⊆ range i)
    {A : Type v} [Category.{w} A] [HasCoproducts.{u} A] [Abelian A] (R : A) (m : ℕ) :
    letI := i.normalSpaceFiberBundle hn hdim
    letI := i.normalSpaceVectorBundle hn hdim
    letI := subbundleTopology P (F' := Fin (manifoldMorseIndex I f (i s₀)) → ℝ)
      (h.negativeNormalSpace hn g.toRiemannianMetric)
    Nonempty ((sublevelPair f (hac.trans hcb).le).singularHomology R m ≅
      (thomPair (Fin (manifoldMorseIndex I f (i s₀)) → ℝ)
        (fun s ↦ h.negativeNormalSpace hn g.toRiemannianMetric s)).singularHomology R m) :=
  h.nonempty_singularHomology_sublevelPair_iso_thomPair hn hfs hc hdim g
    (fun s ↦ (h.isLocallyConstant_manifoldMorseIndex hn).apply_eq_of_preconnectedSpace s s₀)
    hac hcb hcomp hcrit R m

/-- **Relative homology of a compact cobordism across a Morse–Bott submanifold.** Under the
hypotheses of `nonempty_singularHomology_sublevelPair_iso_thomPair`, the lower level `a` is
regular, so the band pair `(f⁻¹[a, b], f⁻¹(a))` also has the relative homology of the Thom pair
`(ν⁻, ν⁻₀)`. -/
theorem nonempty_singularHomology_bandPair_iso_thomPair
    (h : i.IsNondegenerateCriticalSubmanifold f) (hfs : ContMDiff I 𝓘(ℝ) ∞ f) {c a b : ℝ}
    (hc : ∀ s, f (i s) = c) (hdim : finrank ℝ P = finrank ℝ E - finrank ℝ E')
    (g : letI := i.normalSpaceFiberBundle hn hdim
      letI := i.normalSpaceVectorBundle hn hdim
      ContMDiffRiemannianMetric J ∞ P fun s ↦ i.NormalSpace s hn) {r : ℕ}
    (hr : ∀ s, manifoldMorseIndex I f (i s) = r) (hac : a < c) (hcb : c < b)
    (hcomp : IsCompact (f ⁻¹' Icc a b)) (hcrit : criticalPoints I f ∩ f ⁻¹' Icc a b ⊆ range i)
    {A : Type v} [Category.{w} A] [HasCoproducts.{u} A] [Abelian A] (R : A) (m : ℕ) :
    letI := i.normalSpaceFiberBundle hn hdim
    letI := i.normalSpaceVectorBundle hn hdim
    letI := subbundleTopology P (F' := Fin r → ℝ) (h.negativeNormalSpace hn g.toRiemannianMetric)
    Nonempty ((bandPair f (hac.trans hcb).le).singularHomology R m ≅
      (thomPair (Fin r → ℝ)
        (fun s ↦ h.negativeNormalSpace hn g.toRiemannianMetric s)).singularHomology R m) := by
  let := i.normalSpaceFiberBundle hn hdim
  let := i.normalSpaceVectorBundle hn hdim
  let := subbundleTopology P (F' := Fin r → ℝ) (h.negativeNormalSpace hn g.toRiemannianMetric)
  have ha : IsRegularValue I 𝓘(ℝ) f a :=
    isRegularValue_iff_notMem_image_criticalPoints.2 fun ⟨x, hxc, hx⟩ ↦ by
      obtain ⟨s, rfl⟩ := hcrit ⟨hxc, le_of_eq hx.symm, hx.le.trans (hac.trans hcb).le⟩
      exact hac.ne (hx.symm.trans (hc s))
  have := isIso_singularHomologyMap_bandPairInclusion hfs (hac.trans hcb).le hcomp ha R m
  obtain ⟨e⟩ := h.nonempty_singularHomology_sublevelPair_iso_thomPair hn hfs hc hdim g hr hac hcb
    hcomp hcrit R m
  exact ⟨asIso (TopPair.singularHomologyMap (bandPairInclusion f (hac.trans hcb).le) R m) ≪≫ e⟩

/-! ### Metric-free consequences: vanishing below the index, index degree, and index zero -/

omit [I.Boundaryless] [SecondCountableTopology M] [J.Boundaryless] in
/-- Auxiliary existence of a smooth fibre metric on the normal bundle over a compact submanifold,
using `Fin (finrank ℝ E - finrank ℝ E') → ℝ` as fibre model. -/
private theorem exists_normalSpaceMetric :
    let P₀ := Fin (finrank ℝ E - finrank ℝ E') → ℝ
    have hdim : finrank ℝ P₀ = finrank ℝ E - finrank ℝ E' := Module.finrank_fin_fun ℝ
    letI := i.normalSpaceFiberBundle hn hdim
    letI := i.normalSpaceVectorBundle hn hdim
    Nonempty (ContMDiffRiemannianMetric J ∞ P₀ fun s ↦ i.NormalSpace s hn) := by
  have : IsManifold I (∞ + 1) M := .of_le (n := ∞) (by simp)
  have : IsManifold J (∞ + 1) S := .of_le (n := ∞) (by simp)
  let P₀ := Fin (finrank ℝ E - finrank ℝ E') → ℝ
  have hdim : finrank ℝ P₀ = finrank ℝ E - finrank ℝ E' := Module.finrank_fin_fun ℝ
  have : T2Space S := i.isEmbedding.t2Space
  let := i.normalSpaceFiberBundle hn hdim
  let := i.normalSpaceVectorBundle hn hdim
  let := i.normalSpaceContMDiffVectorBundle (m := ∞) hn (by simp) hdim
  exact nonempty_contMDiffRiemannianMetric (IB := J) (n := ⊤) (F := P₀)
    (E := fun s ↦ i.NormalSpace s hn)

/-- **Vanishing below the Morse index in homology.** Across a compact Morse–Bott submanifold of
constant index `r`, the relative singular homology `Hₙ({f ≤ b}, {f ≤ a}; R)` vanishes for every
`n < r`, with coefficients in any abelian category with coproducts. -/
theorem isZero_singularHomology_sublevelPair_of_lt_index
    (h : i.IsNondegenerateCriticalSubmanifold f) (hfs : ContMDiff I 𝓘(ℝ) ∞ f) {c a b : ℝ}
    (hc : ∀ s, f (i s) = c) {r : ℕ} (hr : ∀ s, manifoldMorseIndex I f (i s) = r)
    (hac : a < c) (hcb : c < b) (hcomp : IsCompact (f ⁻¹' Icc a b))
    (hcrit : criticalPoints I f ∩ f ⁻¹' Icc a b ⊆ range i)
    {A : Type v} [Category.{w} A] [HasCoproducts.{u} A] [Abelian A] (R : A)
    {m : ℕ} (hmr : m < r) :
    IsZero ((sublevelPair f (hac.trans hcb).le).singularHomology R m) := by
  have hn : (∞ : ℕ∞ω) ≠ 0 := by simp
  have : IsManifold I (∞ + 2) M := .of_le (n := ∞) (by simp)
  have : IsManifold J (∞ + 1) S := .of_le (n := ∞) (by simp)
  let P₀ := Fin (finrank ℝ E - finrank ℝ E') → ℝ
  have hdim : finrank ℝ P₀ = finrank ℝ E - finrank ℝ E' := Module.finrank_fin_fun ℝ
  let := i.normalSpaceFiberBundle hn hdim
  let := i.normalSpaceVectorBundle hn hdim
  obtain ⟨g⟩ := exists_normalSpaceMetric (i := i) hn
  obtain ⟨e⟩ := h.nonempty_singularHomology_sublevelPair_iso_thomPair hn hfs hc hdim g hr hac hcb
    hcomp hcrit R m
  let hV := h.hasLocalContMDiffSubbundleFrames_negativeNormalSpace hn (by simp)
    (fun s ↦ (hfs (i s)).of_le (by simp)) hdim g hr
  let hVu := hV.hasLocalSubbundleFrames.comp_equiv Equiv.ulift
  let := subbundleTopology P₀ (F' := Fin r → ℝ) (h.negativeNormalSpace hn g.toRiemannianMetric)
  let := subbundleTopology P₀ (F' := ULift.{u} (Fin r) → ℝ)
    (h.negativeNormalSpace hn g.toRiemannianMetric)
  let := hVu.fiberBundle
  let := hVu.vectorBundle
  have hrank : finrank ℝ (ULift.{u} (Fin r) → ℝ) = r := by
    rw [Module.finrank_pi, Fintype.card_ulift, Fintype.card_fin]
  let ν : S → Type u := fun s ↦ h.negativeNormalSpace hn g.toRiemannianMetric s
  have hzero : IsZero ((thomPair (ULift.{u} (Fin r) → ℝ) ν).singularHomology R m) :=
    isZero_singularHomology_thomPair_of_compactSpace R (hrank.symm ▸ hmr)
  have h₁ : Continuous fun v : TotalSpace (Fin r → ℝ) ν ↦
      TotalSpace.mk' (E := ν) (ULift.{u} (Fin r) → ℝ) v.proj v.snd := by
    rw [(isEmbedding_totalSpace_subbundle P₀ (ULift.{u} (Fin r) → ℝ) _).continuous_iff]
    exact (isEmbedding_totalSpace_subbundle P₀ (Fin r → ℝ) _).continuous
  have h₂ : Continuous fun v : TotalSpace (ULift.{u} (Fin r) → ℝ) ν ↦
      TotalSpace.mk' (E := ν) (Fin r → ℝ) v.proj v.snd := by
    rw [(isEmbedding_totalSpace_subbundle P₀ (Fin r → ℝ) _).continuous_iff]
    exact (isEmbedding_totalSpace_subbundle P₀ (ULift.{u} (Fin r) → ℝ) _).continuous
  exact hzero.of_iso (e ≪≫ TopPair.singularHomologyMapIso R (thomPairModelIso h₁ h₂) m)

/-- **Vanishing below the Morse index in cohomology.** Across a compact Morse–Bott submanifold of
constant index `r`, the relative singular cohomology `Hⁿ({f ≤ b}, {f ≤ a}; R, M')` vanishes for
every `n < r` whenever the chain coefficient object `R` is projective. -/
theorem isZero_singularCohomology_sublevelPair_of_lt_index
    (h : i.IsNondegenerateCriticalSubmanifold f) (hfs : ContMDiff I 𝓘(ℝ) ∞ f) {c a b : ℝ}
    (hc : ∀ s, f (i s) = c) {r : ℕ} (hr : ∀ s, manifoldMorseIndex I f (i s) = r)
    (hac : a < c) (hcb : c < b) (hcomp : IsCompact (f ⁻¹' Icc a b))
    (hcrit : criticalPoints I f ∩ f ⁻¹' Icc a b ⊆ range i)
    {A : Type v} [Category.{w} A] [HasCoproducts.{u} A] [Abelian A] (R : A) [Projective R]
    (k : Type*) [Ring k] [Linear k A] (M' : A) {m : ℕ} (hmr : m < r) :
    IsZero ((sublevelPair f (hac.trans hcb).le).singularCohomology R k M' m) :=
  TopPair.isZero_singularCohomology_of_isZero_singularHomology _ R M' m fun _ hj ↦
    h.isZero_singularHomology_sublevelPair_of_lt_index hfs hc hr hac hcb hcomp hcrit R
      (hj.trans_lt hmr)

/-- **The index-degree relative homology with `Subsingleton Kˣ` coefficients.** Across a compact
Morse–Bott submanifold `i : S → M` of constant index `r`, for any commutative ring `K` whose only
unit is `1` (such as `ZMod 2`), `Hᵣ({f ≤ b}, {f ≤ a}; K) ≅ H₀(S; K)`, without any orientability
assumption on the negative normal bundle. -/
theorem nonempty_singularHomology_sublevelPair_iso_singularHomology_zero
    (h : i.IsNondegenerateCriticalSubmanifold f) (hfs : ContMDiff I 𝓘(ℝ) ∞ f) {c a b : ℝ}
    (hc : ∀ s, f (i s) = c) {r : ℕ} (hr : ∀ s, manifoldMorseIndex I f (i s) = r)
    (hac : a < c) (hcb : c < b) (hcomp : IsCompact (f ⁻¹' Icc a b))
    (hcrit : criticalPoints I f ∩ f ⁻¹' Icc a b ⊆ range i)
    (K : Type u) [CommRing K] [Subsingleton Kˣ] :
    Nonempty ((sublevelPair f (hac.trans hcb).le).singularHomology (ModuleCat.of K K) r ≅
      ((singularHomologyFunctor (ModuleCat.{u} K) 0).obj (ModuleCat.of K K)).obj
        (TopCat.of S)) := by
  have hn : (∞ : ℕ∞ω) ≠ 0 := by simp
  have : IsManifold I (∞ + 2) M := .of_le (n := ∞) (by simp)
  have : IsManifold J (∞ + 1) S := .of_le (n := ∞) (by simp)
  let P₀ := Fin (finrank ℝ E - finrank ℝ E') → ℝ
  have hdim : finrank ℝ P₀ = finrank ℝ E - finrank ℝ E' := Module.finrank_fin_fun ℝ
  let := i.normalSpaceFiberBundle hn hdim
  let := i.normalSpaceVectorBundle hn hdim
  obtain ⟨g⟩ := exists_normalSpaceMetric (i := i) hn
  obtain ⟨e⟩ := h.nonempty_singularHomology_sublevelPair_iso_thomPair hn hfs hc hdim g hr hac hcb
    hcomp hcrit (ModuleCat.of K K) r
  let hV := h.hasLocalContMDiffSubbundleFrames_negativeNormalSpace hn (by simp)
    (fun s ↦ (hfs (i s)).of_le (by simp)) hdim g hr
  let hVu := hV.hasLocalSubbundleFrames.comp_equiv Equiv.ulift
  let := subbundleTopology P₀ (F' := Fin r → ℝ) (h.negativeNormalSpace hn g.toRiemannianMetric)
  let := subbundleTopology P₀ (F' := ULift.{u} (Fin r) → ℝ)
    (h.negativeNormalSpace hn g.toRiemannianMetric)
  let := hVu.fiberBundle
  let := hVu.vectorBundle
  have hrank : finrank ℝ (ULift.{u} (Fin r) → ℝ) = r := by
    rw [Module.finrank_pi, Fintype.card_ulift, Fintype.card_fin]
  let ν : S → Type u := fun s ↦ h.negativeNormalSpace hn g.toRiemannianMetric s
  have h₁ : Continuous fun v : TotalSpace (Fin r → ℝ) ν ↦
      TotalSpace.mk' (E := ν) (ULift.{u} (Fin r) → ℝ) v.proj v.snd := by
    rw [(isEmbedding_totalSpace_subbundle P₀ (ULift.{u} (Fin r) → ℝ) _).continuous_iff]
    exact (isEmbedding_totalSpace_subbundle P₀ (Fin r → ℝ) _).continuous
  have h₂ : Continuous fun v : TotalSpace (ULift.{u} (Fin r) → ℝ) ν ↦
      TotalSpace.mk' (E := ν) (Fin r → ℝ) v.proj v.snd := by
    rw [(isEmbedding_totalSpace_subbundle P₀ (Fin r → ℝ) _).continuous_iff]
    exact (isEmbedding_totalSpace_subbundle P₀ (ULift.{u} (Fin r) → ℝ) _).continuous
  let eLift := TopPair.singularHomologyMapIso (ModuleCat.of K K) (thomPairModelIso h₁ h₂) r
  let eThom := eqToIso (congrArg
    ((thomPair (ULift.{u} (Fin r) → ℝ) ν).singularHomology (ModuleCat.of K K)) hrank.symm) ≪≫
    thomPairSingularHomologyFinrankIso K (ULift.{u} (Fin r) → ℝ) ν
  exact ⟨e ≪≫ eLift ≪≫ eThom⟩

/-- **Relative homology across a local-minimum Morse–Bott submanifold.** When the Morse index is
identically `0`, the negative normal bundle has rank `0`, so its Thom pair is `(S, ∅)` and
`Hₙ({f ≤ b}, {f ≤ a}; R) ≅ Hₙ(S; R)` in every degree `n`, with coefficients in any abelian
category with coproducts. -/
theorem nonempty_singularHomology_sublevelPair_iso_singularHomology_of_index_eq_zero
    (h : i.IsNondegenerateCriticalSubmanifold f) (hfs : ContMDiff I 𝓘(ℝ) ∞ f) {c a b : ℝ}
    (hc : ∀ s, f (i s) = c) (hr : ∀ s, manifoldMorseIndex I f (i s) = 0)
    (hac : a < c) (hcb : c < b) (hcomp : IsCompact (f ⁻¹' Icc a b))
    (hcrit : criticalPoints I f ∩ f ⁻¹' Icc a b ⊆ range i)
    {A : Type v} [Category.{w} A] [HasCoproducts.{u} A] [Abelian A] (R : A) (m : ℕ) :
    Nonempty ((sublevelPair f (hac.trans hcb).le).singularHomology R m ≅
      ((singularHomologyFunctor A m).obj R).obj (TopCat.of S)) := by
  have hn : (∞ : ℕ∞ω) ≠ 0 := by simp
  have : IsManifold I (∞ + 2) M := .of_le (n := ∞) (by simp)
  have : IsManifold J (∞ + 1) S := .of_le (n := ∞) (by simp)
  let P₀ := Fin (finrank ℝ E - finrank ℝ E') → ℝ
  have hdim : finrank ℝ P₀ = finrank ℝ E - finrank ℝ E' := Module.finrank_fin_fun ℝ
  let := i.normalSpaceFiberBundle hn hdim
  let := i.normalSpaceVectorBundle hn hdim
  obtain ⟨g⟩ := exists_normalSpaceMetric (i := i) hn
  obtain ⟨e⟩ := h.nonempty_singularHomology_sublevelPair_iso_thomPair hn hfs hc hdim g hr hac hcb
    hcomp hcrit R m
  let hV := h.hasLocalContMDiffSubbundleFrames_negativeNormalSpace hn (by simp)
    (fun s ↦ (hfs (i s)).of_le (by simp)) hdim g hr
  let ν : S → Type u := fun s ↦ h.negativeNormalSpace hn g.toRiemannianMetric s
  let := subbundleTopology P₀ (F' := Fin 0 → ℝ) (h.negativeNormalSpace hn g.toRiemannianMetric)
  let := hV.fiberBundle
  let := hV.vectorBundle
  have : IsEmpty (thomPair (Fin 0 → ℝ) ν).snd :=
    isEmpty_thomPair_snd_of_subsingleton (Fin 0 → ℝ) ν
  have : IsIso (thomPairProj (Fin 0 → ℝ) ν) :=
    isIso_thomPairProj_of_subsingleton (Fin 0 → ℝ) ν
  let eπ := (asIso ((thomPair (Fin 0 → ℝ) ν).singularHomologyπ R m)).symm ≪≫
    (eqToIso (singularHomologyFunctor_obj_obj_eq_toSSet_homology R m
      (thomPair (Fin 0 → ℝ) ν).fst)).symm ≪≫
    ((singularHomologyFunctor A m).obj R).mapIso (asIso (thomPairProj (Fin 0 → ℝ) ν))
  exact ⟨e ≪≫ eπ⟩

/-! ### The first page of the sublevel filtration spectral sequence -/

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

end HomologyAttachment

end IsNondegenerateCriticalSubmanifold

end SmoothEmbedding

/-! ### The negative disc bundle parametrized by a vector bundle -/

section ThomPair

variable {E H : Type*} {M : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless] [TopologicalSpace M]
  [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M] {f s t : M → ℝ} {c ε : ℝ} {W : Set M}
  {B : Type u} [TopologicalSpace B] {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {V : B → Type u} [∀ b, AddCommGroup (V b)] [∀ b, Module ℝ (V b)] [∀ b, TopologicalSpace (V b)]
  [TopologicalSpace (TotalSpace F V)] [FiberBundle F V] [VectorBundle ℝ F V]
  {ρ : TotalSpace F V → ℝ} {g : TotalSpace F V → M}

/-- **The relative homology across a Morse–Bott critical level is that of the disc-sphere pair of
the negative bundle.** Let `f` be smooth, with the quadratic normal form `f = c - s + t` on a tube
`W` and the scaling `φ` of the positive directions of
`TauCeti.exists_sublevel_union_negativeDiscBundle_deformation`, whose hypotheses are repeated here.
Let `ρ` be a fibre gauge on a real vector bundle `V → B`, for instance a fibre norm which is
continuous on the total space, and let `g` restrict to a closed embedding of the disc bundle
`D_ρ(V)` onto the negative disc bundle `{x ∈ W | t x = 0, s x ≤ ε}`, carrying the sphere bundle
`S_ρ(V)` onto `{x ∈ W | t x = 0, s x = ε}`. Then `g` induces a map of pairs
`(D_ρ(V), S_ρ(V)) ⟶ ({f ≤ c + ε}, {f ≤ c - ε})` which is an isomorphism on relative singular
homology, with coefficients in any abelian category with coproducts, in every degree. -/
theorem exists_isIso_singularHomologyMap_sublevelPair_of_negativeDiscBundle
    (hfs : ContMDiff I 𝓘(ℝ) ∞ f) (hW : IsOpen W) (hs : ContMDiffOn I 𝓘(ℝ) ∞ s W)
    (ht : ContMDiffOn I 𝓘(ℝ) ∞ t W) (hs₀ : ∀ x ∈ W, 0 ≤ s x) (ht₀ : ∀ x ∈ W, 0 ≤ t x)
    (hf : ∀ x ∈ W, f x = c - s x + t x)
    (hdir : ∀ x ∈ W, t x ≠ 0 → ∃ v : TangentSpace I x,
      mfderiv I 𝓘(ℝ) s x v = 0 ∧ mfderiv I 𝓘(ℝ) t x v ≠ 0)
    (φ : C(unitInterval × W, W)) (hφs : ∀ τ x, s (φ (τ, x)) = s x)
    (hφt : ∀ τ x, t (φ (τ, x)) = τ ^ 2 * t x) (hφ₁ : ∀ x, φ (1, x) = x)
    (hφ₀ : ∀ τ (x : W), t x = 0 → φ (τ, x) = x) (hε : 0 < ε)
    (hK : IsCompact {x | x ∈ W ∧ s x + 2 * t x ≤ 2 * ε})
    (hcompact : IsCompact (f ⁻¹' Icc (c - ε) (c + ε)))
    (hcrit : criticalPoints I f ∩ f ⁻¹' Icc (c - ε) (c + ε) ⊆ W)
    (hρ : IsFiberGauge ρ)
    (hg : IsClosedEmbedding ((gaugeDiscBundle ρ).domRestrict g))
    (hgD : g '' gaugeDiscBundle ρ = {x | x ∈ W ∧ t x = 0 ∧ s x ≤ ε})
    (hgS : g '' gaugeSphereBundle ρ = {x | x ∈ W ∧ t x = 0 ∧ s x = ε}) :
    ∃ ψ : gaugeDiscSpherePair ρ ⟶ sublevelPair f (a := c - ε) (b := c + ε) (by linarith),
      (∀ v : gaugeDiscBundle ρ, Subtype.val (TopPair.Hom.fst ψ v) = g v) ∧
      ∀ {C : Type w} [Category.{v} C] [HasCoproducts.{u} C] [Abelian C] (R : C) (n : ℕ),
        IsIso (TopPair.singularHomologyMap ψ R n) := by
  obtain ⟨r, -, ⟨G⟩⟩ := exists_sublevel_union_negativeDiscBundle_deformation hfs hW hs ht hs₀ ht₀
    hf hdir φ hφs hφt hφ₁ hφ₀ hε hK hcompact hcrit
  refine exists_isIso_singularHomologyMap_of_homotopyRel_attach_discBundle hρ
    (sublevel_mono f (by linarith)) (isClosed_le hfs.continuous continuous_const) hg hgD
    (fun x ⟨hxW, htx, _⟩ ↦ ?_) (fun v hv ↦ ?_) r G
  · -- On the negative disc bundle `f = c - s ≤ c`.
    rw [mem_ofPred_eq, hf x hxW, htx]
    linarith [hs₀ x hxW]
  · -- A point of the disc bundle lies in `{f ≤ c - ε}` exactly when `s = ε` there, that is, when
    -- it is the image of a point of the sphere bundle.
    obtain ⟨hxW, htx, hsx⟩ : g v ∈ {x | x ∈ W ∧ t x = 0 ∧ s x ≤ ε} := hgD ▸ mem_image_of_mem g hv
    rw [mem_ofPred_eq, hf _ hxW, htx]
    refine ⟨fun hle ↦ ?_, fun hvS ↦ ?_⟩
    · obtain ⟨w, hw, hwv⟩ : g v ∈ g '' gaugeSphereBundle ρ := hgS ▸ ⟨hxW, htx, by linarith⟩
      obtain rfl : w = v :=
        congrArg Subtype.val
          (@hg.injective ⟨w, gaugeSphereBundle_subset_gaugeDiscBundle ρ hw⟩ ⟨v, hv⟩ hwv)
      exact hw
    · have : g v ∈ {x | x ∈ W ∧ t x = 0 ∧ s x = ε} := hgS ▸ mem_image_of_mem g hvS
      linarith [this.2.2]

/-- **The relative homology across a Morse–Bott critical level is that of the Thom pair of the
negative bundle.** Under the hypotheses of
`TauCeti.exists_isIso_singularHomologyMap_sublevelPair_of_negativeDiscBundle`, the relative singular
homology `Hₙ({f ≤ c + ε}, {f ≤ c - ε}; R)` is isomorphic to the relative homology `Hₙ(V, V₀; R)`
of the Thom pair of `V`, `V₀` the complement of the zero section, for coefficients in any abelian
category with coproducts. -/
theorem nonempty_singularHomology_sublevelPair_iso_thomPair
    (hfs : ContMDiff I 𝓘(ℝ) ∞ f) (hW : IsOpen W) (hs : ContMDiffOn I 𝓘(ℝ) ∞ s W)
    (ht : ContMDiffOn I 𝓘(ℝ) ∞ t W) (hs₀ : ∀ x ∈ W, 0 ≤ s x) (ht₀ : ∀ x ∈ W, 0 ≤ t x)
    (hf : ∀ x ∈ W, f x = c - s x + t x)
    (hdir : ∀ x ∈ W, t x ≠ 0 → ∃ v : TangentSpace I x,
      mfderiv I 𝓘(ℝ) s x v = 0 ∧ mfderiv I 𝓘(ℝ) t x v ≠ 0)
    (φ : C(unitInterval × W, W)) (hφs : ∀ τ x, s (φ (τ, x)) = s x)
    (hφt : ∀ τ x, t (φ (τ, x)) = τ ^ 2 * t x) (hφ₁ : ∀ x, φ (1, x) = x)
    (hφ₀ : ∀ τ (x : W), t x = 0 → φ (τ, x) = x) (hε : 0 < ε)
    (hK : IsCompact {x | x ∈ W ∧ s x + 2 * t x ≤ 2 * ε})
    (hcompact : IsCompact (f ⁻¹' Icc (c - ε) (c + ε)))
    (hcrit : criticalPoints I f ∩ f ⁻¹' Icc (c - ε) (c + ε) ⊆ W)
    (hρ : IsFiberGauge ρ)
    (hg : IsClosedEmbedding ((gaugeDiscBundle ρ).domRestrict g))
    (hgD : g '' gaugeDiscBundle ρ = {x | x ∈ W ∧ t x = 0 ∧ s x ≤ ε})
    (hgS : g '' gaugeSphereBundle ρ = {x | x ∈ W ∧ t x = 0 ∧ s x = ε})
    {C : Type w} [Category.{v} C] [HasCoproducts.{u} C] [Abelian C] (R : C) (n : ℕ) :
    Nonempty ((sublevelPair f (a := c - ε) (b := c + ε) (by linarith)).singularHomology R n ≅
      (thomPair F V).singularHomology R n) := by
  obtain ⟨ψ, -, hψ⟩ := exists_isIso_singularHomologyMap_sublevelPair_of_negativeDiscBundle hfs hW
    hs ht hs₀ ht₀ hf hdir φ hφs hφt hφ₁ hφ₀ hε hK hcompact hcrit hρ hg hgD hgS
  have := hψ R n
  have := isIso_singularHomologyMap_gaugeDiscSpherePairMap hρ R n
  exact ⟨(asIso (TopPair.singularHomologyMap ψ R n)).symm ≪≫
    asIso (TopPair.singularHomologyMap (gaugeDiscSpherePairMap hρ) R n)⟩

end ThomPair

end TauCeti
