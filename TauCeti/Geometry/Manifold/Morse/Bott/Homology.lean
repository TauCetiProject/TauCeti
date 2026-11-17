/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.FilteredSpace.Basic
public import TauCeti.Geometry.Manifold.Morse.Bott.DiscBundle
public import TauCeti.Geometry.Manifold.Morse.Bott.HessianMetric
public import TauCeti.Geometry.Manifold.Morse.Deformation.Homology
public import TauCeti.Topology.VectorBundle.SphereBundle.Basic
import TauCeti.AlgebraicTopology.Cohomology.HomotopyInvariance
import TauCeti.AlgebraicTopology.Singular.Empty
import TauCeti.Geometry.Manifold.VectorBundle.Riemannian.Existence
import TauCeti.Topology.Maps.IsEmpty
import TauCeti.Topology.VectorBundle.Attachment
import TauCeti.Topology.VectorBundle.DiscSphere
import TauCeti.Topology.VectorBundle.MayerVietoris.Basic
import TauCeti.Topology.VectorBundle.Riemannian.Basic
import TauCeti.Topology.VectorBundle.Smul
import TauCeti.Topology.VectorBundle.Thom.RankDegreeHomology

/-!
# Relative homology and cohomology across a compact Morse–Bott critical submanifold

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
(`nonempty_singularHomology_sublevelPair_iso_negativeDiscBundle`).

Next, assuming constant Morse index `r`, we equip the negative normal subbundle `ν⁻` with the
continuous Hessian fibre metric `-½ Hessₛ` (`negativeNormalHessianMetric` from
`TauCeti.Geometry.Manifold.Morse.Bott.HessianMetric`) and compute the relative singular homology
and cohomology of sublevel pairs across `c` in terms of the Thom pair `(ν⁻, ν⁻₀)`. Rescaling each
vector of the unit disc bundle `D(ν⁻)` for the Hessian metric by `√ε` identifies `D(ν⁻)`
homeomorphically with `D_ε` so that `f (Θ (√ε • v)) = c - ε ‖v‖²`; hence a point of `D(ν⁻)` lands
in `{f ≤ c - ε}` precisely when `‖v‖ = 1`, i.e., on the unit sphere bundle `S(ν⁻)`. The
compactness of `D(ν⁻)` makes `v ↦ Θ (√ε • v)` a closed embedding into `{f ≤ c - ε} ∪ Θ(D_ε)`, so
disc-bundle attachment (`TauCeti.isIso_singularHomologyMap_of_attach_gaugeDiscBundle`,
`TauCeti.isIso_singularCohomologyMap_of_attach_gaugeDiscBundle`) and the strong deformation
retraction of `{f ≤ c + ε}` onto `{f ≤ c - ε} ∪ Θ(D_ε)` show that the attaching map
`(D(ν⁻), S(ν⁻)) ⟶ ({f ≤ c + ε}, {f ≤ c - ε})` induces isomorphisms on both relative singular
homology and cohomology in every degree (`exists_discSpherePairMap_isIso_sublevelPair`). Composing
with `(D(ν⁻), S(ν⁻)) ⟶ (ν⁻, ν⁻₀)` (`TauCeti.isIso_singularHomologyMap_gaugeDiscSpherePairMap`,
`TauCeti.isIso_singularCohomologyMap_gaugeDiscSpherePairMap`) identifies both the relative homology
and the relative cohomology across `c` with those of the Thom pair `(ν⁻, ν⁻₀)`.

In homology, regular-collar removal (`TauCeti.singularHomologySublevelPairIsoOfCriticalValue`)
removes the width `ε` and applies to any compact band `f⁻¹[a, b]` with `a < c < b` whose critical
points lie on `i` (`nonempty_singularHomology_sublevelPair_iso_thomPair`, and the cobordism form
`nonempty_singularHomology_bandPair_iso_thomPair`). Several metric-free consequences follow by
choosing an auxiliary normal metric internally:

* relative singular homology vanishes in degrees below the Morse index `r`
  (`isZero_singularHomology_sublevelPair_of_lt_index`), and relative singular cohomology with
  projective chain coefficients likewise vanishes below `r`
  (`isZero_singularCohomology_sublevelPair_of_lt_index`);
* in the index degree `r`, for any commutative ring `K` whose only unit is `1` (such as `ZMod 2`),
  `Hᵣ({f ≤ b}, {f ≤ a}; K) ≅ H₀(S; K)` without any orientability assumption
  (`nonempty_singularHomology_sublevelPair_iso_singularHomology_zero`);
* for a local-minimum critical submanifold (`r = 0`), `Hₙ({f ≤ b}, {f ≤ a}; R) ≅ Hₙ(S; R)` in
  every degree `n` (`nonempty_singularHomology_sublevelPair_iso_singularHomology_of_index_eq_zero`);
* in the spectral sequence of a monotone sublevel filtration
  (`TauCeti.filteredSpaceSpectralSequence`), a compact band containing `i` as its only critical
  locus contributes `Hₙ(ν⁻, ν⁻₀; R)` to the first page
  (`nonempty_filteredSpaceSpectralSequence_page_two_X_iso_thomPair`), and vanishes below the index
  (`isZero_filteredSpaceSpectralSequence_page_two_X_of_lt_index`).

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

namespace SmoothEmbedding

section NegativeDiscBundle

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
    h.exists_sublevel_union_negativeDiscBundle_deformation hn hfs hc hdim g
  refine ⟨Θ, hΘz, hΘi, hΘf, ε₀, hε₀, fun ε hε hεε₀ hcompact hcrit ↦ ?_⟩
  set D := h.negativeDiscBundle hn P g.toRiemannianMetric ε
  obtain ⟨hD, r, -, ⟨G⟩⟩ := hmain ε ⟨hε, hεε₀⟩ hcompact hcrit
  -- The disc bundle lies in the critical sublevel, since the normal Hessian is negative on the
  -- negative normal spaces.
  have hA : {y | f y ≤ c - ε} ∪ Θ '' D ⊆ {y | f y ≤ c + ε} := by
    rintro y (hy | ⟨x, hx, rfl⟩)
    · exact sublevel_mono f (by linarith) hy
    · have hneg := (h.toIsCriticalSubmanifold.mem_negativeDiscBundle hn).1 hx |>.1
      have hle : h.normalHessian hn x.proj x.2 x.2 ≤ 0 := by
        rcases eq_or_ne x.2 0 with h0 | h0
        · simp [h0]
        · exact (h.normalHessian_apply_self_neg_of_mem_negativeNormalSpace hn _ hneg h0).le
      rw [mem_ofPred_eq, hΘf x (hD hx)]
      linarith
  -- The deformation retracts `{f ≤ c + ε}` onto `{f ≤ c - ε} ∪ Θ(D_ε)`, fixing it pointwise.
  refine ⟨hD, hA, fun {A} _ _ _ _ R n ↦
    TopPair.isIso_singularHomologyMap_ofInclusionMap_inclusion_of_homotopyRel (X := TopCat.of M)
      subset_union_left hA ((ContinuousMap.inclusion inter_subset_right).comp r)
      (G.cast (ContinuousMap.ext fun _ ↦ rfl) rfl) R n⟩

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
  obtain ⟨Θ, hΘz, hΘi, hΘf, ε₀, hε₀, hmain⟩ :=
    h.exists_isIso_singularHomologyMap_negativeDiscBundle hn hfs hc hdim g
  refine ⟨Θ, hΘz, hΘi, hΘf, min ε₀ (min (c - a) (b - c)),
    lt_min hε₀ (lt_min (by linarith) (by linarith)), fun ε hε ↦ ?_⟩
  obtain ⟨hε0, hεm⟩ := hε
  have hε₁ : ε < ε₀ := hεm.trans_le (min_le_left _ _)
  have hεa : ε < c - a := hεm.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hεb : ε < b - c := hεm.trans_le ((min_le_right _ _).trans (min_le_right _ _))
  have hε' : Icc (c - ε) (c + ε) ⊆ Icc a b := Icc_subset_Icc (by linarith) (by linarith)
  have hcompact' : IsCompact (f ⁻¹' Icc (c - ε) (c + ε)) :=
    hcompact.of_isClosed_subset (isClosed_Icc.preimage hfs.continuous) (preimage_mono hε')
  -- Every critical point of the band lies on the submanifold, hence on the level `c`.
  have hlev : ∀ x ∈ criticalPoints I f, f x ∈ Icc a b → f x = c := fun x hx hfx ↦ by
    obtain ⟨s, rfl⟩ := hcrit ⟨hx, hfx⟩
    exact hc s
  obtain ⟨hD, _, hiso⟩ := hmain ε hε0 hε₁ hcompact' fun x hx ↦ hcrit ⟨hx.1, hε' hx.2⟩
  refine ⟨hD, fun {A} _ _ _ R n ↦ ⟨singularHomologySublevelPairIsoOfCriticalValue hfs hac hcb
    (by linarith : c - ε < c) (by linarith : c < c + ε) hcompact hcompact' hlev
    (fun x hx hfx ↦ hlev x hx (hε' hfx)) R n ≪≫ (@asIso _ _ _ _ _ (hiso R n)).symm⟩⟩

end IsNondegenerateCriticalSubmanifold

end NegativeDiscBundle

namespace IsNondegenerateCriticalSubmanifold

/-! ### Universe-lifting of subbundle frames and Thom pairs -/

section ULiftHelper

/-- Reindexing local subbundle frames from `Fin r` to `ULift.{u} (Fin r)` lifts the model fibre
into universe `u` without changing the subbundle fibres or topology. -/
private theorem hasLocalSubbundleFrames_ulift {B : Type u} [TopologicalSpace B]
    {F : Type*} {E : B → Type u} [TopologicalSpace (TotalSpace F E)]
    [∀ b, AddCommMonoid (E b)] [∀ b, Module ℝ (E b)] {V : ∀ b, Submodule ℝ (E b)} {r : ℕ}
    (hV : HasLocalSubbundleFrames F (Fin r) V) :
    HasLocalSubbundleFrames F (ULift.{u} (Fin r)) V := by
  rw [hasLocalSubbundleFrames_iff] at hV ⊢
  intro b
  obtain ⟨U, hU, hbU, X, hX⟩ := hV b
  refine ⟨U, hU, hbU, fun j ↦ X j.down,
    ⟨fun j ↦ hX.continuousOn j.down,
     fun hy ↦ (hX.linearIndependent hy).comp ULift.down ULift.down_injective,
     fun {y} hy ↦ ?_⟩⟩
  have hrange : (range fun j : ULift.{u} (Fin r) ↦ X j.down y) = range (fun j ↦ X j y) :=
    ULift.down_surjective.range_comp (fun j ↦ X j y)
  rw [hrange]
  exact hX.span_eq hy

/-- Changing the phantom model-fibre parameter from `Fin r → ℝ` to `ULift.{u} (Fin r) → ℝ` yields
an isomorphic Thom pair in `TopPair.{u}`. -/
private def thomPairULiftIso {B : Type u} {F : Type*} {E : B → Type u}
    [TopologicalSpace (TotalSpace F E)] [∀ b, AddCommMonoid (E b)] [∀ b, Module ℝ (E b)]
    (V : ∀ b, Submodule ℝ (E b)) (r : ℕ) :
    letI := subbundleTopology F (F' := Fin r → ℝ) V
    letI := subbundleTopology F (F' := ULift.{u} (Fin r) → ℝ) V
    thomPair (Fin r → ℝ) (fun b ↦ V b) ≅ thomPair (ULift.{u} (Fin r) → ℝ) (fun b ↦ V b) :=
  letI := subbundleTopology F (F' := Fin r → ℝ) V
  letI := subbundleTopology F (F' := ULift.{u} (Fin r) → ℝ) V
  let f : C(TotalSpace (Fin r → ℝ) (fun b ↦ V b),
      TotalSpace (ULift.{u} (Fin r) → ℝ) (fun b ↦ V b)) :=
    ⟨fun v ↦ ⟨v.proj, v.2⟩,
      (isEmbedding_totalSpace_subbundle F (ULift.{u} (Fin r) → ℝ) V).continuous_iff.2
        (isEmbedding_totalSpace_subbundle F (Fin r → ℝ) V).continuous⟩
  let g : C(TotalSpace (ULift.{u} (Fin r) → ℝ) (fun b ↦ V b),
      TotalSpace (Fin r → ℝ) (fun b ↦ V b)) :=
    ⟨fun v ↦ ⟨v.proj, v.2⟩,
      (isEmbedding_totalSpace_subbundle F (Fin r → ℝ) V).continuous_iff.2
        (isEmbedding_totalSpace_subbundle F (ULift.{u} (Fin r) → ℝ) V).continuous⟩
  { hom := TopPair.ofSubsetMap (TopCat.ofHom f) fun _ hv ↦
      (mem_zeroSectionCompl (F := ULift.{u} (Fin r) → ℝ)).2
        ((mem_zeroSectionCompl (F := Fin r → ℝ)).1 hv)
    inv := TopPair.ofSubsetMap (TopCat.ofHom g) fun _ hv ↦
      (mem_zeroSectionCompl (F := Fin r → ℝ)).2
        ((mem_zeroSectionCompl (F := ULift.{u} (Fin r) → ℝ)).1 hv)
    hom_inv_id :=
      (TopPair.ofSubsetMap_comp_ofSubsetMap_of_comp_eq _ _ (fun _ hv ↦ hv)
        (TopCat.ext fun _ ↦ rfl)).trans (TopPair.ofSubsetMap_id _)
    inv_hom_id :=
      (TopPair.ofSubsetMap_comp_ofSubsetMap_of_comp_eq _ _ (fun _ hv ↦ hv)
        (TopCat.ext fun _ ↦ rfl)).trans (TopPair.ofSubsetMap_id _) }

/-- For a rank-`0` real vector bundle, every fibre is trivial, so the Thom pair `(E, ∅)` is
isomorphic to `TopPair.incl.obj (TopCat.of B)` and has the singular homology of the base. -/
private def thomPairZeroRankIsoIncl {B : Type u} [TopologicalSpace B] {E : B → Type u}
    [TopologicalSpace (TotalSpace (Fin 0 → ℝ) E)] [∀ b, AddCommGroup (E b)]
    [∀ b, Module ℝ (E b)] [∀ b, TopologicalSpace (E b)]
    [FiberBundle (Fin 0 → ℝ) E] [VectorBundle ℝ (Fin 0 → ℝ) E]
    (hsub : ∀ b, Subsingleton (E b)) :
    thomPair (Fin 0 → ℝ) E ≅ TopPair.incl.obj (TopCat.of B) := by
  haveI hempty : IsEmpty (zeroSectionCompl (Fin 0 → ℝ) E) :=
    ⟨fun ⟨v, hv⟩ ↦ (mem_zeroSectionCompl.1 hv) (Subsingleton.elim v.2 0)⟩
  let f : C(TotalSpace (Fin 0 → ℝ) E, B) := ⟨TotalSpace.proj, FiberBundle.continuous_proj _ _⟩
  let g : C(B, TotalSpace (Fin 0 → ℝ) E) :=
    ⟨zeroSection (Fin 0 → ℝ) E, Trivialization.continuous_zeroSection ℝ (F := Fin 0 → ℝ) (E := E)⟩
  let e1 : C(zeroSectionCompl (Fin 0 → ℝ) E, PEmpty.{u + 1}) :=
    ⟨isEmptyElim, continuous_of_discreteTopology⟩
  let e2 : C(PEmpty.{u + 1}, zeroSectionCompl (Fin 0 → ℝ) E) :=
    ⟨isEmptyElim, continuous_of_discreteTopology⟩
  refine
    { hom := TopPair.ofHom (TopCat.ofHom f) (TopCat.ofHom e1) (TopCat.ext fun x ↦ hempty.elim x)
      inv := TopPair.ofHom (TopCat.ofHom g) (TopCat.ofHom e2) (TopCat.ext fun x ↦ isEmptyElim x)
      hom_inv_id := TopPair.hom_ext_of_fst _ (TopCat.ext fun v ↦
        TotalSpace.ext rfl (heq_of_eq (Subsingleton.elim _ _)))
      inv_hom_id := TopPair.hom_ext_of_fst _ (TopCat.ext fun _ ↦ rfl) }

end ULiftHelper

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
      ∃ ψ : gaugeDiscSpherePair (fun v : TotalSpace (Fin r → ℝ) ν ↦ ‖v.2‖) ⟶
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
  let : TopologicalSpace (TotalSpace (Fin r → ℝ) ν) :=
    subbundleTopology P (F' := Fin r → ℝ) (h.negativeNormalSpace hn g.toRiemannianMetric)
  let : FiberBundle (Fin r → ℝ) ν := hV.fiberBundle
  let : VectorBundle ℝ (Fin r → ℝ) ν := hV.vectorBundle
  let : RiemannianBundle ν :=
    ⟨(h.negativeNormalHessianMetric hn (by simp) (fun s ↦ (hfs (i s)).of_le (by simp)) hdim g
      hr).toRiemannianMetric⟩
  let : ∀ s, NormedAddCommGroup (ν s) := fun s ↦ inferInstance
  let : ∀ s, InnerProductSpace ℝ (ν s) := fun s ↦ inferInstance
  let : IsContinuousRiemannianBundle (Fin r → ℝ) ν :=
    Bundle.instIsContinuousRiemannianBundle
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
  let ρ : TotalSpace (Fin r → ℝ) ν → ℝ := fun v ↦ ‖v.2‖
  have : IsEmpty (gaugeDiscBundle ρ) := ⟨fun v ↦ isEmptyElim v.1.proj⟩
  have : IsEmpty (gaugeSphereBundle ρ) := ⟨fun v ↦ isEmptyElim v.1.proj⟩
  have : IsEmpty (gaugeDiscSpherePair ρ).fst := ⟨fun v ↦ isEmptyElim v.1.proj⟩
  have : IsEmpty (gaugeDiscSpherePair ρ).snd := ⟨fun v ↦ isEmptyElim v.1.proj⟩
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
    eq_univ_of_forall fun z ↦ z.2
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
      (∀ v, -(2⁻¹ * h.normalHessian hn (scale v).proj (scale v).2 (scale v).2) = ε * ‖v.2‖ ^ 2) ∧
      scale '' discBundle (Fin r → ℝ) ν = h.negativeDiscBundle hn P g.toRiemannianMetric ε := by
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
  have hsq : Real.sqrt ε ≠ 0 := Real.sqrt_ne_zero'.mpr hε
  let scale : TotalSpace (Fin r → ℝ) ν → TotalSpace P (fun s ↦ i.NormalSpace s hn) :=
    fun v ↦ TotalSpace.mk' P v.proj (Real.sqrt ε • v.2.1)
  have hcont : Continuous scale :=
    (Continuous.smul_totalSpace continuous_const continuous_id).comp
      (isEmbedding_totalSpace_subbundle P (Fin r → ℝ)
        (h.negativeNormalSpace hn g.toRiemannianMetric)).continuous
  have hinj : Injective scale := by
    intro ⟨s₁, v₁⟩ ⟨s₂, v₂⟩ hEq
    obtain rfl : s₁ = s₂ := congrArg TotalSpace.proj hEq
    dsimp only [scale, TotalSpace.mk'] at hEq
    have h2 : Real.sqrt ε • v₁.1 = Real.sqrt ε • v₂.1 :=
      (TotalSpace.mk_inj (E := fun s ↦ i.NormalSpace s hn)).mp hEq
    exact congrArg (TotalSpace.mk s₁) (Subtype.ext (smul_right_injective _ hsq h2))
  have hhess (v : TotalSpace (Fin r → ℝ) ν) :
      -(2⁻¹ * h.normalHessian hn (scale v).proj (scale v).2 (scale v).2) = ε * ‖v.2‖ ^ 2 := by
    have hnorm := h.norm_sq_eq_of_negativeNormalHessianMetric hn (by simp)
      (fun s ↦ (hfs (i s)).of_le (by simp)) hdim g hr v.proj v.2
    simp only [scale, TotalSpace.mk', map_smul, LinearMap.smul_apply, smul_eq_mul]
    rw [hnorm]
    have : Real.sqrt ε * (Real.sqrt ε * h.normalHessian hn v.proj v.2.1 v.2.1) =
        Real.sqrt ε ^ 2 * h.normalHessian hn v.proj v.2.1 v.2.1 := by ring
    rw [this, Real.sq_sqrt hε.le]
    ring
  refine ⟨scale, hcont, hinj, hhess, Subset.antisymm ?_ ?_⟩
  · rintro _ ⟨v, hv, rfl⟩
    refine (IsCriticalSubmanifold.mem_negativeDiscBundle hn).2
      ⟨Submodule.smul_mem _ _ v.2.2, ?_⟩
    rw [hhess v]
    have hle : ‖v.2‖ ^ 2 ≤ 1 := by nlinarith [mem_discBundle.1 hv, norm_nonneg v.2]
    nlinarith
  · intro x hx
    obtain ⟨hxmem, hxle⟩ := (IsCriticalSubmanifold.mem_negativeDiscBundle hn).1 hx
    let v : TotalSpace (Fin r → ℝ) ν :=
      ⟨x.proj, ⟨(Real.sqrt ε)⁻¹ • x.2, Submodule.smul_mem _ _ hxmem⟩⟩
    have hsv : scale v = x := by
      cases x
      simp [scale, v, TotalSpace.mk', smul_inv_smul₀ hsq]
    refine ⟨v, mem_discBundle.2 ?_, hsv⟩
    have hsqle : ε * ‖v.2‖ ^ 2 ≤ ε := by
      rw [← hhess v, hsv]
      exact hxle
    have hle1 : ‖v.2‖ ^ 2 ≤ 1 := by nlinarith
    nlinarith [norm_nonneg v.2]

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
    (hΘf : ∀ x ∈ Θ.source, f (Θ x) = c + 2⁻¹ * h.normalHessian hn x.proj x.2 x.2)
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
    ∃ φ : gaugeDiscSpherePair (fun v : TotalSpace (Fin r → ℝ) ν ↦ ‖v.2‖) ⟶
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
  let : TopologicalSpace (TotalSpace (Fin r → ℝ) ν) :=
    subbundleTopology P (F' := Fin r → ℝ) (h.negativeNormalSpace hn g.toRiemannianMetric)
  let : FiberBundle (Fin r → ℝ) ν := hV.fiberBundle
  let : VectorBundle ℝ (Fin r → ℝ) ν := hV.vectorBundle
  let : RiemannianBundle ν :=
    ⟨(h.negativeNormalHessianMetric hn (by simp) (fun s ↦ (hfs (i s)).of_le (by simp)) hdim g
      hr).toRiemannianMetric⟩
  let : ∀ s, NormedAddCommGroup (ν s) := fun s ↦ inferInstance
  let : ∀ s, InnerProductSpace ℝ (ν s) := fun s ↦ inferInstance
  let : IsContinuousRiemannianBundle (Fin r → ℝ) ν :=
    Bundle.instIsContinuousRiemannianBundle
      (h.negativeNormalHessianMetric hn (by simp) (fun s ↦ (hfs (i s)).of_le (by simp)) hdim g hr)
  let Dε := h.negativeDiscBundle hn P g.toRiemannianMetric ε
  let Z : Set M := {y | f y ≤ c + ε} ∩ ({y | f y ≤ c - ε} ∪ Θ '' Dε)
  let ρ : TotalSpace (Fin r → ℝ) ν → ℝ := fun v ↦ ‖v.2‖
  obtain ⟨scale, hscale_cont, hscale_inj, hscale_hess, hscale_img⟩ :=
    h.exists_rescale_negativeDiscBundle hn hfs hdim g hr hε
  rw [discBundle_def] at hscale_img
  have hscale_mem {v : TotalSpace (Fin r → ℝ) ν} (hv : v ∈ gaugeDiscBundle ρ) :
      scale v ∈ Dε := by
    dsimp only [Dε]
    rw [← hscale_img]
    exact mem_image_of_mem scale hv
  have hf_val {v : TotalSpace (Fin r → ℝ) ν} (hv : v ∈ gaugeDiscBundle ρ) :
      f (Θ (scale v)) = c - ε * ‖v.2‖ ^ 2 := by
    rw [hΘf (scale v) (hDsub (hscale_mem hv))]
    linarith [hscale_hess v]
  have hf_le_iff {v : TotalSpace (Fin r → ℝ) ν} (hv : v ∈ gaugeDiscBundle ρ) :
      f (Θ (scale v)) ≤ c - ε ↔ v ∈ gaugeSphereBundle ρ := by
    rw [hf_val hv, mem_gaugeSphereBundle]
    have hv1 : ‖v.2‖ ≤ 1 := mem_gaugeDiscBundle.1 hv
    have hv0 : 0 ≤ ‖v.2‖ := norm_nonneg v.2
    exact ⟨fun hle ↦ by dsimp only [ρ]; nlinarith [show 1 ≤ ‖v.2‖ ^ 2 by nlinarith],
      fun heq ↦ by dsimp only [ρ] at heq; rw [heq]; linarith⟩
  -- The attaching map `φ : D(ν⁻) → Z` sends `v` to `Θ (√ε • v)`.
  let φ : C(gaugeDiscBundle ρ, Z) :=
    { toFun := fun v ↦ ⟨Θ (scale v.1),
        ⟨show f (Θ (scale v.1)) ≤ c + ε by rw [hf_val v.2]; nlinarith [sq_nonneg ‖v.1.2‖],
         Or.inr ⟨scale v.1, hscale_mem v.2, rfl⟩⟩⟩
      continuous_toFun := Continuous.subtype_mk
        (Θ.toOpenPartialHomeomorph.continuousOn.comp_continuous
          (hscale_cont.comp continuous_subtype_val) fun v ↦ hDsub (hscale_mem v.2)) _ }
  have hφ_emb : IsClosedEmbedding φ := by
    have hD_eq : gaugeDiscBundle ρ = {p : TotalSpace (Fin r → ℝ) ν | ‖p.2‖ ≤ 1} :=
      Set.ext fun _ ↦ mem_gaugeDiscBundle
    have : CompactSpace (gaugeDiscBundle ρ) :=
      isCompact_iff_compactSpace.mp (hD_eq ▸
        TauCeti.isCompact_setOf_norm_le_bundle (F := Fin r → ℝ) (V := ν) (r := fun _ ↦ 1)
          continuous_const)
    refine φ.continuous.isClosedEmbedding fun v w hvw ↦ ?_
    have hΘeq : Θ (scale v.1) = Θ (scale w.1) := congrArg Subtype.val hvw
    exact Subtype.ext (hscale_inj (Θ.injOn (hDsub (hscale_mem v.2)) (hDsub (hscale_mem w.2)) hΘeq))
  have hX : IsClosed (Subtype.val ⁻¹' {y : M | f y ≤ c - ε} : Set Z) :=
    isClosed_le (hfs.continuous.comp continuous_subtype_val) continuous_const
  have hcover : (Subtype.val ⁻¹' {y : M | f y ≤ c - ε} : Set Z) ∪ range φ = univ := by
    refine eq_univ_of_forall fun z ↦ ?_
    rcases z.2.2 with hz | ⟨x, hx, hxz⟩
    · exact Or.inl hz
    · obtain ⟨v, hv, rfl⟩ := hscale_img.symm.subset hx
      exact Or.inr ⟨⟨v, hv⟩, Subtype.ext hxz⟩
  let φ_pair : gaugeDiscSpherePair ρ ⟶
      TopPair.ofSubset (X := TopCat.of Z) (Subtype.val ⁻¹' {y | f y ≤ c - ε}) :=
    TopPair.ofHom (TopCat.ofHom φ)
      (TopCat.ofHom ⟨fun v ↦ ⟨φ ⟨v.1, gaugeSphereBundle_subset_gaugeDiscBundle ρ v.2⟩,
        (hf_le_iff (gaugeSphereBundle_subset_gaugeDiscBundle ρ v.2)).2 v.2⟩,
        (φ.continuous.comp (continuous_subtype_val.subtype_mk _)).subtype_mk _⟩)
      (TopCat.ext fun _ ↦ rfl)
  have hφ_pre (v : gaugeDiscBundle ρ)
      (hv : TopPair.Hom.fst φ_pair v ∈ (Subtype.val ⁻¹' {y : M | f y ≤ c - ε} : Set Z)) :
      v.1 ∈ gaugeSphereBundle ρ :=
    (hf_le_iff v.2).1 hv
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
      ∃ ψ : gaugeDiscSpherePair (fun v : TotalSpace (Fin r → ℝ) ν ↦ ‖v.2‖) ⟶
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
  have hsubZ : {y | f y ≤ c - ε} ⊆ Z := fun y hy ↦
    ⟨show f y ≤ c + ε by have : f y ≤ c - ε := hy; linarith [hε.1], Or.inl hy⟩
  have hrel : {y : {y | f y ≤ c + ε} | (y : M) ∈
      {y | f y ≤ c - ε} ∪ Θ '' h.negativeDiscBundle hn P g.toRiemannianMetric ε} =
      {y : {y | f y ≤ c + ε} | (y : M) ∈ Z} :=
    Set.ext fun y ↦ ⟨fun hy ↦ ⟨y.2, hy⟩, fun hy ↦ hy.2⟩
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
  let : TopologicalSpace (TotalSpace (Fin r → ℝ) ν) :=
    subbundleTopology P (F' := Fin r → ℝ) (h.negativeNormalSpace hn g.toRiemannianMetric)
  let : FiberBundle (Fin r → ℝ) ν := hV.fiberBundle
  let : VectorBundle ℝ (Fin r → ℝ) ν := hV.vectorBundle
  let : RiemannianBundle ν :=
    ⟨(h.negativeNormalHessianMetric hn (by simp) (fun s ↦ (hfs (i s)).of_le (by simp)) hdim g
      hr).toRiemannianMetric⟩
  let : ∀ s, NormedAddCommGroup (ν s) := fun s ↦ inferInstance
  let : ∀ s, InnerProductSpace ℝ (ν s) := fun s ↦ inferInstance
  let : IsContinuousRiemannianBundle (Fin r → ℝ) ν :=
    Bundle.instIsContinuousRiemannianBundle
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
  let : TopologicalSpace (TotalSpace (Fin r → ℝ) ν) :=
    subbundleTopology P (F' := Fin r → ℝ) (h.negativeNormalSpace hn g.toRiemannianMetric)
  let : FiberBundle (Fin r → ℝ) ν := hV.fiberBundle
  let : VectorBundle ℝ (Fin r → ℝ) ν := hV.vectorBundle
  let : RiemannianBundle ν :=
    ⟨(h.negativeNormalHessianMetric hn (by simp) (fun s ↦ (hfs (i s)).of_le (by simp)) hdim g
      hr).toRiemannianMetric⟩
  let : ∀ s, NormedAddCommGroup (ν s) := fun s ↦ inferInstance
  let : ∀ s, InnerProductSpace ℝ (ν s) := fun s ↦ inferInstance
  let : IsContinuousRiemannianBundle (Fin r → ℝ) ν :=
    Bundle.instIsContinuousRiemannianBundle
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
    have : ε ≤ (c - a) / 2 := (min_le_right _ _).trans (min_le_left _ _)
    linarith
  have hεb : c + ε ≤ b := by
    have : ε ≤ (b - c) / 2 := (min_le_right _ _).trans (min_le_right _ _)
    linarith
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
  let hVu := hasLocalSubbundleFrames_ulift.{u} hV.hasLocalSubbundleFrames
  let := subbundleTopology P₀ (F' := Fin r → ℝ) (h.negativeNormalSpace hn g.toRiemannianMetric)
  let := subbundleTopology P₀ (F' := ULift.{u} (Fin r) → ℝ)
    (h.negativeNormalSpace hn g.toRiemannianMetric)
  let := hVu.fiberBundle
  let := hVu.vectorBundle
  have hrank : finrank ℝ (ULift.{u} (Fin r) → ℝ) = r := by
    rw [Module.finrank_pi, Fintype.card_ulift, Fintype.card_fin]
  have hzero : IsZero ((thomPair (ULift.{u} (Fin r) → ℝ)
      (fun s ↦ h.negativeNormalSpace hn g.toRiemannianMetric s)).singularHomology R m) :=
    isZero_singularHomology_thomPair_of_compactSpace R (hrank.symm ▸ hmr)
  exact hzero.of_iso (e ≪≫ TopPair.singularHomologyMapIso R
    (thomPairULiftIso (F := P₀) (h.negativeNormalSpace hn g.toRiemannianMetric) r) m)

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
  let hVu := hasLocalSubbundleFrames_ulift.{u} hV.hasLocalSubbundleFrames
  let := subbundleTopology P₀ (F' := Fin r → ℝ) (h.negativeNormalSpace hn g.toRiemannianMetric)
  let := subbundleTopology P₀ (F' := ULift.{u} (Fin r) → ℝ)
    (h.negativeNormalSpace hn g.toRiemannianMetric)
  let := hVu.fiberBundle
  let := hVu.vectorBundle
  have hrank : finrank ℝ (ULift.{u} (Fin r) → ℝ) = r := by
    rw [Module.finrank_pi, Fintype.card_ulift, Fintype.card_fin]
  let eLift := TopPair.singularHomologyMapIso (ModuleCat.of K K)
    (thomPairULiftIso (F := P₀) (h.negativeNormalSpace hn g.toRiemannianMetric) r) r
  let eThom := eqToIso (congrArg
    ((thomPair (ULift.{u} (Fin r) → ℝ)
      (fun s ↦ h.negativeNormalSpace hn g.toRiemannianMetric s)).singularHomology
      (ModuleCat.of K K)) hrank.symm) ≪≫
    thomPairSingularHomologyFinrankIso K (ULift.{u} (Fin r) → ℝ)
      (fun s ↦ h.negativeNormalSpace hn g.toRiemannianMetric s)
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
  let := subbundleTopology P₀ (F' := Fin 0 → ℝ) (h.negativeNormalSpace hn g.toRiemannianMetric)
  let := hV.fiberBundle
  let := hV.vectorBundle
  have hsub : ∀ s, Subsingleton (h.negativeNormalSpace hn g.toRiemannianMetric s) := fun s ↦ by
    rw [← Module.finrank_zero_iff (R := ℝ)]
    simpa using hV.hasLocalSubbundleFrames.finrank_eq s
  let e0 := TopPair.singularHomologyMapIso R
    (thomPairZeroRankIsoIncl (E := fun s ↦ h.negativeNormalSpace hn g.toRiemannianMetric s) hsub) m
  let eEmpty :=
    eqToIso (TopPair.singularHomologyFunctor_obj (TopPair.incl.obj (TopCat.of S)) R m).symm ≪≫
      ((TopPair.singularHomologyInclIso A R m).app (TopCat.of S)).symm
  exact ⟨e ≪≫ e0 ≪≫ eEmpty⟩

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

end TauCeti
