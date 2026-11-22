/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.DisjointClosed
public import TauCeti.Geometry.Manifold.Morse.Bott.Attachment
public import TauCeti.Geometry.Manifold.Morse.Bott.DiscBundle
public import TauCeti.Geometry.Manifold.Morse.Deformation.Homology
public import TauCeti.Topology.VectorBundle.Attachment
public import TauCeti.Topology.VectorBundle.Thom.LineBundle

/-!
# Relative homology across the level of compact Morse–Bott submanifolds

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

A level of a Morse–Bott function generally carries several critical submanifolds, of different
dimensions and indices. For finitely many compact ones `i j : S j → M` with pairwise disjoint
images on the level `c`, crossing the level attaches all their negative disc bundles at once
(`TauCeti.SmoothEmbedding.exists_sublevel_union_iUnion_negativeDiscBundle_deformation`), and the
same argument identifies `Hₙ(M_{c+ε}, M_{c-ε})`, and `Hₙ(M_b, M_a)` for regular levels
`a < c < b`, with `Hₙ(M_{c-ε} ∪ ⋃ j, Θ j (D j ε), M_{c-ε})`. For a Morse–Bott function on a compact
manifold (`TauCeti.IsMorseBottFamily`) the pieces on a level are finite in number, compact and
disjoint, so this applies to every band `[a, b]` whose only critical value is `c`, with the pieces
on the level `c` as the family.

This relative homology splits over the submanifolds. For small `ε` the sets `Θ j (D j ε)` are
compact and pairwise disjoint, since the disc bundles shrink to the zero sections
(`TauCeti.SmoothEmbedding.IsNondegenerateCriticalSubmanifold.exists_pos_negativeDiscBundle_subset`)
and the submanifolds have disjoint neighbourhoods. The relative homology of a union of disjoint
closed sets is the coproduct of the contributions of the sets
(`TopPair.isColimitCofanSingularHomologyOfDisjointClosed`), so `Hₙ(M_b, M_a)` is the coproduct over
`j` of `Hₙ(M_{c-ε} ∪ Θ j (D j ε), M_{c-ε})`, the relative homology of attaching the negative disc
bundle of `i j` alone
(`TauCeti.SmoothEmbedding.nonempty_singularHomology_sublevelPair_iso_sigma_negativeDiscBundle`).
For a Morse–Bott function on a compact manifold this splits each band with a single critical value
over the critical submanifolds on that level
(`TauCeti.IsMorseBottFamily.nonempty_singularHomology_sublevelPair_iso_sigma_negativeDiscBundle`).

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
(`TauCeti.nonempty_singularHomology_sublevelPair_iso_thomPair`). The Thom isomorphism identifies
the homology of the Thom pair with the homology of the base `B`, shifted by the rank of `V` and
with coefficients twisted by the orientation of `V`. In index one, where `V` is a line bundle, and
with coefficients in a ring of characteristic two, such as `ZMod 2`, the twist disappears
(`TauCeti.thomPairSingularHomologySuccIsoSingularHomology`), so crossing the level shifts the
homology of the base by one: `Hₙ₊₁(M_{c+ε}, M_{c-ε}; R) ≅ Hₙ(B; R)`
(`TauCeti.nonempty_singularHomology_sublevelPair_succ_iso_singularHomology_of_finrank_eq_one`).

## Main results

In the namespace `TauCeti.SmoothEmbedding.IsNondegenerateCriticalSubmanifold`:

* `exists_isIso_singularHomologyMap_negativeDiscBundle`: the inclusion of the lower sublevel with
  the negative disc bundle attached into the upper sublevel, relative to the lower sublevel,
  induces isomorphisms on relative singular homology.
* `nonempty_singularHomology_sublevelPair_iso_negativeDiscBundle`: the relative homology of the
  sublevels at two regular levels around the critical level is the relative homology of the lower
  sublevel with the negative disc bundle attached.

In the namespace `TauCeti.SmoothEmbedding`:

* `exists_isIso_singularHomologyMap_iUnion_negativeDiscBundle` and
  `nonempty_singularHomology_sublevelPair_iso_iUnion_negativeDiscBundle`: the same for finitely
  many disjoint compact Morse–Bott submanifolds on one level, each with its own model, with all
  their negative disc bundles attached.

* `nonempty_singularHomology_sublevelPair_iso_sigma_negativeDiscBundle`: this relative homology is
  the coproduct over the submanifolds of the relative homology of attaching each negative disc
  bundle alone.

In the namespace `TauCeti.IsMorseBottFamily`:

* `nonempty_singularHomology_sublevelPair_iso_iUnion_negativeDiscBundle`: the relative homology of
  a band of a Morse–Bott function on a compact manifold with a single critical value `c` is that of
  the lower sublevel with the negative disc bundles of all the critical submanifolds on the level
  `c` attached.
* `nonempty_singularHomology_sublevelPair_iso_sigma_negativeDiscBundle`: it is the coproduct over
  the critical submanifolds on the level `c` of the relative homology of attaching each negative
  disc bundle alone.

In the namespace `TauCeti`:

* `exists_isIso_singularHomologyMap_sublevelPair_of_negativeDiscBundle`: a parametrization of
  the negative disc bundle induces isomorphisms `Hₙ(D_ρ(V), S_ρ(V)) ≅ Hₙ(M_{c+ε}, M_{c-ε})`.
* `nonempty_singularHomology_sublevelPair_iso_thomPair`: the relative homology across the
  critical level is that of the Thom pair, `Hₙ(M_{c+ε}, M_{c-ε}) ≅ Hₙ(V, V₀)`.
* `nonempty_singularHomology_sublevelPair_succ_iso_singularHomology_of_finrank_eq_one`: in index
  one and characteristic two, `Hₙ₊₁(M_{c+ε}, M_{c-ε}; R) ≅ Hₙ(B; R)`.

## References

* R. Bott, *Nondegenerate critical manifolds*, Annals of Mathematics 60 (1954), 248–261.
* R. L. Cohen, K. Iga and P. Norbury, *Topics in Morse theory: lecture notes*, 2006,
  Theorem 15.4.
* J. Milnor, *Morse Theory*, Annals of Mathematics Studies 51, Princeton University Press, 1963,
  Theorem 3.2.
-/

public section

noncomputable section

open Bundle CategoryTheory Function Limits Set Topology
open scoped ContDiff Manifold

universe u v w

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
    lt_min hε₀ (lt_min (by linarith) (by linarith)), fun ε ⟨hε0, hεm⟩ ↦ ?_⟩
  -- Every critical point of the band lies on one of the submanifolds, hence on the level `c`.
  have hlev : ∀ x ∈ criticalPoints I f, f x ∈ Icc a b → f x = c := fun x hx hfx ↦ by
    obtain ⟨j, s, rfl⟩ := mem_iUnion.1 (hcrit ⟨hx, hfx⟩)
    exact hc j s
  obtain ⟨hε', hcompact'⟩ :=
    Icc_subset_and_isCompact_preimage_Icc hfs.continuous hcompact
      (hεm.trans_le (min_le_right _ _)).le
  obtain ⟨hD, _, hiso⟩ := hmain ε hε0 (hεm.trans_le (min_le_left _ _)) hcompact'
    fun x hx ↦ hcrit ⟨hx.1, hε' hx.2⟩
  exact ⟨hD, fun {A} _ _ _ R n ↦ ⟨singularHomologySublevelPairIsoSymmetricBand hfs hac hcb
    hcompact hlev hε0 (hεm.trans_le (min_le_right _ _)).le R n ≪≫
      (@asIso _ _ _ _ _ (hiso R n)).symm⟩⟩

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

/-- For finitely many disjoint compact Morse–Bott submanifolds with Morse–Bott normal forms `Θ j`
defined near their zero sections, the images `Θ j (D j ε)` of small negative disc bundles are
pairwise disjoint. -/
private theorem exists_pos_pairwise_disjoint_image_negativeDiscBundle [T2Space M] [Finite ι]
    [∀ j, CompactSpace (S j)] (h : ∀ j, (i j).IsNondegenerateCriticalSubmanifold f)
    (hfs : ContMDiff I 𝓘(ℝ) ∞ f) (hd : Pairwise (Disjoint on fun j ↦ range (i j)))
    (hdim : ∀ j, Module.finrank ℝ (P j) = Module.finrank ℝ E - Module.finrank ℝ (E' j))
    (g : letI : ∀ j, FiberBundle (P j) fun s ↦ (i j).NormalSpace s hn :=
        fun j ↦ (i j).normalSpaceFiberBundle hn (hdim j)
      letI : ∀ j, VectorBundle ℝ (P j) fun s ↦ (i j).NormalSpace s hn :=
        fun j ↦ (i j).normalSpaceVectorBundle hn (hdim j)
      ∀ j, ContMDiffRiemannianMetric (J j) ∞ (P j) fun s ↦ (i j).NormalSpace s hn)
    (Θ : letI : ∀ j, FiberBundle (P j) fun s ↦ (i j).NormalSpace s hn :=
        fun j ↦ (i j).normalSpaceFiberBundle hn (hdim j)
      ∀ j, PartialDiffeomorph ((J j).prod 𝓘(ℝ, P j)) I
        (TotalSpace (P j) fun s ↦ (i j).NormalSpace s hn) M ∞)
    (hΘz : ∀ j s, zeroSection (P j) (fun s ↦ (i j).NormalSpace s hn) s ∈ (Θ j).source)
    (hΘi : ∀ j s, Θ j (zeroSection (P j) (fun s ↦ (i j).NormalSpace s hn) s) = i j s) :
    letI : ∀ j, FiberBundle (P j) fun s ↦ (i j).NormalSpace s hn :=
      fun j ↦ (i j).normalSpaceFiberBundle hn (hdim j)
    letI : ∀ j, VectorBundle ℝ (P j) fun s ↦ (i j).NormalSpace s hn :=
      fun j ↦ (i j).normalSpaceVectorBundle hn (hdim j)
    ∃ δ > 0, ∀ ε ≤ δ, Pairwise (Disjoint on fun j ↦
      Θ j '' (h j).negativeDiscBundle hn (P j) (g j).toRiemannianMetric ε) := by
  let : ∀ j, FiberBundle (P j) fun s ↦ (i j).NormalSpace s hn :=
    fun j ↦ (i j).normalSpaceFiberBundle hn (hdim j)
  let : ∀ j, VectorBundle ℝ (P j) fun s ↦ (i j).NormalSpace s hn :=
    fun j ↦ (i j).normalSpaceVectorBundle hn (hdim j)
  have (j : ι) : T2Space (S j) := (i j).isEmbedding.t2Space
  -- A small negative disc bundle is carried into any given neighbourhood of the submanifold.
  have hsmall (l : ι) {O : Set M} (hO : IsOpen O) (hlO : range (i l) ⊆ O) :
      ∃ δ > 0, Θ l '' (h l).negativeDiscBundle hn (P l) (g l).toRiemannianMetric δ ⊆ O := by
    obtain ⟨δ, hδ, hδO⟩ := (h l).exists_pos_negativeDiscBundle_subset hn hfs (hdim l) (g l)
      ((Θ l).contMDiffOn_toFun.continuousOn.isOpen_inter_preimage (Θ l).open_source hO)
      fun s ↦ ⟨hΘz l s, by rw [mem_preimage, hΘi]; exact hlO ⟨s, rfl⟩⟩
    exact ⟨δ, hδ, image_subset_iff.2 fun x hx ↦ (hδO hx).2⟩
  -- The submanifolds have pairwise disjoint neighbourhoods, since their images are compact.
  obtain ⟨U, hU, hUd⟩ := Pairwise.exists_mem_filter_of_disjoint fun j k hjk ↦
    separatedNhds_iff_disjoint.1 (SeparatedNhds.of_isCompact_isCompact
      (isCompact_range (i j).isEmbedding.continuous)
      (isCompact_range (i k).isEmbedding.continuous) (hd hjk))
  choose δ hδ hδU using fun j ↦ hsmall j isOpen_interior (subset_interior_iff_mem_nhdsSet.2 (hU j))
  -- A size below the sizes for the finitely many submanifolds.
  obtain ⟨δ₀, hδ₀, hδ₀le⟩ : ∃ δ₀ > 0, ∀ j, δ₀ ≤ δ j := by
    rcases isEmpty_or_nonempty ι with hι | hι
    · exact ⟨1, one_pos, fun j ↦ isEmptyElim j⟩
    obtain ⟨l, hl⟩ := Finite.exists_min δ
    exact ⟨δ l, hδ l, hl⟩
  have hsub (j : ι) {ε : ℝ} (hε : ε ≤ δ₀) :
      Θ j '' (h j).negativeDiscBundle hn (P j) (g j).toRiemannianMetric ε ⊆ U j :=
    ((image_mono ((h j).negativeDiscBundle_mono hn (P j) _ (hε.trans (hδ₀le j)))).trans
      (hδU j)).trans interior_subset
  exact ⟨δ₀, hδ₀, fun ε hε j k hjk ↦ (hUd hjk).mono (hsub j hε) (hsub k hε)⟩

/-- **The relative homology across a level of finitely many Morse–Bott submanifolds splits over
the submanifolds.** Let `i j : S j → M`, for `j` in a finite index type, be nondegenerate critical
submanifolds of a smooth function `f` on a Hausdorff, second-countable, finite-dimensional,
boundaryless manifold, each modelled on its own space, with `S j` compact and nonempty, pairwise
disjoint images and `f = c` along each of them, and let `g j` be a smooth fibre metric on the
normal bundle of `i j`. Let `a < c < b` be such that the band `f⁻¹[a, b]` is compact and all its
critical points lie on the submanifolds.

Then there are smooth partial diffeomorphisms `Θ j` from the total spaces of the normal bundles to
`M`, each defined on a neighbourhood of the zero section and sending it to `i j`, which put `f` in
the Morse–Bott normal form `f (Θ j v) = c + ½ Hessₛ (v, v)`, and an `ε₀ > 0` such that for every
`0 < ε < ε₀` each negative disc bundle `D j ε` relative to `g j` lies in the source of `Θ j`, the
sets `Θ j (D j ε)` are pairwise disjoint, and the relative singular homology
`Hₙ({f ≤ b}, {f ≤ a})` is isomorphic to the coproduct over `j` of the groups
`Hₙ({f ≤ c - ε} ∪ Θ j (D j ε), {f ≤ c - ε})`, in every degree and for every coefficient object.
Each summand is the contribution of one submanifold, the relative homology of attaching its
negative disc bundle alone. -/
theorem SmoothEmbedding.nonempty_singularHomology_sublevelPair_iso_sigma_negativeDiscBundle
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
        Pairwise (Disjoint on fun j ↦
          Θ j '' (h j).negativeDiscBundle hn (P j) (g j).toRiemannianMetric ε) ∧
        ∀ {A : Type v} [Category.{w} A] [Abelian A] [HasCoproducts.{u} A] (R : A) (n : ℕ),
          Nonempty ((sublevelPair f (hac.trans hcb).le).singularHomology R n ≅
            ∐ fun j ↦ (TopPair.ofInclusion (X := TopCat.of M) (subset_union_left :
              {y | f y ≤ c - ε} ⊆ {y | f y ≤ c - ε} ∪
                Θ j '' (h j).negativeDiscBundle hn (P j) (g j).toRiemannianMetric ε)
              ).singularHomology R n) := by
  let : ∀ j, FiberBundle (P j) fun s ↦ (i j).NormalSpace s hn :=
    fun j ↦ (i j).normalSpaceFiberBundle hn (hdim j)
  let : ∀ j, VectorBundle ℝ (P j) fun s ↦ (i j).NormalSpace s hn :=
    fun j ↦ (i j).normalSpaceVectorBundle hn (hdim j)
  have (j : ι) : T2Space (S j) := (i j).isEmbedding.t2Space
  obtain ⟨Θ, hΘz, hΘi, hΘf, ε₀, hε₀, hmain⟩ :=
    nonempty_singularHomology_sublevelPair_iso_iUnion_negativeDiscBundle hn h hfs hc hd hac hcb
      hcompact hcrit hdim g
  obtain ⟨δ, hδ, hδd⟩ :=
    exists_pos_pairwise_disjoint_image_negativeDiscBundle hn h hfs hd hdim g Θ hΘz hΘi
  refine ⟨Θ, hΘz, hΘi, hΘf, min ε₀ δ, lt_min hε₀ hδ, fun ε hε ↦ ?_⟩
  obtain ⟨hD, hiso⟩ := hmain ε ⟨hε.1, hε.2.trans_le (min_le_left _ _)⟩
  have hdisj := hδd ε (hε.2.le.trans (min_le_right _ _))
  refine ⟨hD, hdisj, fun {A} _ _ _ R n ↦ ?_⟩
  -- The images of the compact disc bundles are compact, hence closed, and they are disjoint.
  have hclosed (j : ι) :
      IsClosed (Θ j '' (h j).negativeDiscBundle hn (P j) (g j).toRiemannianMetric ε) :=
    (((h j).isCompact_negativeDiscBundle hn hfs (hdim j) (g j) ε).image_of_continuousOn
      ((Θ j).contMDiffOn_toFun.continuousOn.mono (hD j))).isClosed
  obtain ⟨e⟩ := hiso R n
  exact ⟨e ≪≫ (TopPair.isColimitCofanSingularHomologyOfDisjointClosed (Y := TopCat.of M) R
    hclosed hdisj n).coconePointUniqueUpToIso (colimit.isColimit _)⟩

/-- **The relative homology across a critical level of a Morse–Bott function splits over its
critical submanifolds on that level.** Let the family `i j : S j → M` exhibit `f` as a Morse–Bott
function (`TauCeti.IsMorseBottFamily`) on a compact Hausdorff second-countable boundaryless
manifold, with pieces modelled on boundaryless models, and let `g j` be a smooth fibre metric on
the normal bundle of `i j`. Let `a < c < b` be such that `c` is the only critical value of `f` in
`[a, b]`, and index the pieces on the level `f = c` by `{j // ∀ s, f (i j s) = c}`.

Then there are smooth partial diffeomorphisms `Θ j` from the total spaces of the normal bundles of
these pieces to `M`, each defined on a neighbourhood of the zero section and sending it to `i j`,
which put `f` in the Morse–Bott normal form `f (Θ j v) = c + ½ Hessₛ (v, v)`, and an `ε₀ > 0` such
that for every `0 < ε < ε₀` each negative disc bundle `D j ε` relative to `g j` lies in the source
of `Θ j`, the sets `Θ j (D j ε)` are pairwise disjoint, and the relative singular homology
`Hₙ({f ≤ b}, {f ≤ a})` is isomorphic to the coproduct over the pieces on the level of the groups
`Hₙ({f ≤ c - ε} ∪ Θ j (D j ε), {f ≤ c - ε})`, in every degree and for every coefficient object.
If `c` is not a critical value there are no such pieces, and the coproduct is zero. -/
theorem IsMorseBottFamily.nonempty_singularHomology_sublevelPair_iso_sigma_negativeDiscBundle
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
        Pairwise (Disjoint on fun j : {j // ∀ s, f (i j s) = c} ↦
          Θ j '' (h.isNondegenerateCriticalSubmanifold j).negativeDiscBundle hn (P j)
            (g j).toRiemannianMetric ε) ∧
        ∀ {A : Type v} [Category.{w} A] [Abelian A] [HasCoproducts.{u} A] (R : A) (n : ℕ),
          -- The pieces are finitely many, so the coproduct exists in the abelian category `A`.
          haveI := h.finite
          Nonempty ((sublevelPair f (hac.trans hcb).le).singularHomology R n ≅
            ∐ fun j : {j // ∀ s, f (i j s) = c} ↦
              (TopPair.ofInclusion (X := TopCat.of M) (subset_union_left :
                {y | f y ≤ c - ε} ⊆ {y | f y ≤ c - ε} ∪
                  Θ j '' (h.isNondegenerateCriticalSubmanifold j).negativeDiscBundle hn (P j)
                    (g j).toRiemannianMetric ε)).singularHomology R n) := by
  have := h.finite
  have (j : ι) : Nonempty (S j) := h.nonempty j
  have (j : ι) : CompactSpace (S j) :=
    (Topology.IsClosedEmbedding.mk (i j).isEmbedding (h.isClosed_range j)).compactSpace
  refine SmoothEmbedding.nonempty_singularHomology_sublevelPair_iso_sigma_negativeDiscBundle
    (ι := {j // ∀ s, f (i j s) = c}) (S := fun j ↦ S j) (P := fun j ↦ P j) (J := fun j ↦ J j)
    (i := fun j ↦ i j) hn (fun j ↦ h.isNondegenerateCriticalSubmanifold j) h.contMDiff
    (fun j ↦ j.property) (fun j k hjk ↦ h.pairwise_disjoint_range fun he ↦ hjk (Subtype.ext he))
    hac hcb
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

section LineBundle

variable {E H : Type*} {M : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless] [TopologicalSpace M]
  [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M] {f s t : M → ℝ} {c ε : ℝ} {W : Set M}
  {B : Type u} [TopologicalSpace B] {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {V : B → Type u} [∀ b, NormedAddCommGroup (V b)] [∀ b, NormedSpace ℝ (V b)]
  [TopologicalSpace (TotalSpace F V)] [FiberBundle F V] [VectorBundle ℝ F V]
  {ρ : TotalSpace F V → ℝ} {g : TotalSpace F V → M}

/-- **Crossing a Morse–Bott level of index one shifts the homology of the base by one, in
characteristic two.** Under the hypotheses of
`TauCeti.nonempty_singularHomology_sublevelPair_iso_thomPair`, suppose that the vector bundle
`V → B` parametrizing the negative disc bundle has rank one, and that its fibre norm is continuous
on the total space. Then for every ring `R` of characteristic two, such as `ZMod 2`,
`Hₙ₊₁({f ≤ c + ε}, {f ≤ c - ε}; R) ≅ Hₙ(B; R)` in every degree `n`, with no orientation
hypothesis on `V`. -/
theorem nonempty_singularHomology_sublevelPair_succ_iso_singularHomology_of_finrank_eq_one
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
    (hnorm : Continuous fun v : TotalSpace F V ↦ ‖v.snd‖) (hF : Module.finrank ℝ F = 1)
    (R : Type u) [Ring R] [CharP R 2] (n : ℕ) :
    Nonempty ((sublevelPair f (a := c - ε) (b := c + ε) (by linarith)).singularHomology
        (ModuleCat.of R R) (n + 1) ≅
      ((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} R) n).obj
        (ModuleCat.of R R)).obj (TopCat.of B)) := by
  obtain ⟨e⟩ := nonempty_singularHomology_sublevelPair_iso_thomPair hfs hW hs ht hs₀ ht₀ hf hdir
    φ hφs hφt hφ₁ hφ₀ hε hK hcompact hcrit hρ hg hgD hgS (ModuleCat.of R R) (n + 1)
  exact ⟨e ≪≫ thomPairSingularHomologySuccIsoSingularHomology hnorm hF R n⟩

end LineBundle

end TauCeti
