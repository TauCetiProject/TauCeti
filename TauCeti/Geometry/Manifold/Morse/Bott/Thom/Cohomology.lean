/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Morse.Bott.Thom.Pair
public import TauCeti.Topology.VectorBundle.MayerVietoris.DirectedUnion
public import TauCeti.Topology.VectorBundle.Orientation.ThomClass
public import TauCeti.Topology.VectorBundle.Thom.Isomorphism

/-!
# The cohomology across a Morse–Bott level from a Thom class of the negative normal bundle

Let `i : S → M` be a nondegenerate critical submanifold of a smooth function `f` on a Hausdorff,
second-countable, finite-dimensional, boundaryless manifold, on the level `f = c`, and let `g` be a
smooth fibre metric on its normal bundle. When the negative normal spaces relative to `g` have
continuous local frames of size `r`, they form a vector bundle `ν⁻ → S` of rank `r`, the negative
normal bundle, and `r` is the Morse index of `f` along `i`. Let `a < c < b` be such that the band
`f⁻¹[a, b]` is compact and all its critical points lie on `i`. Then the relative cohomology
`Hⁿ({f ≤ b}, {f ≤ a})` is that of the Thom pair `(ν⁻, ν⁻₀)`, with arbitrary coefficients
(`nonempty_singularCohomology_sublevelPair_iso_thomPair` in
`TauCeti.Geometry.Manifold.Morse.Bott.Thom.Pair`). This file applies the cohomology Thom
isomorphism `a ↦ π^*a ⌣ u` over the compact base `S` (`TauCeti.thomEquivOfCompactSpace`) to it,
which gives Bott's description of the contribution of a critical submanifold of index `r`: the
cohomology of `S`, shifted up by the index.

* Given a Thom class `u` of `ν⁻` with coefficients in a commutative ring `K`,
  `Hᵣ₊ₚ({f ≤ b}, {f ≤ a}; K, N) ≅ Hᵖ(S; K, N)` for every `K`-module `N` and every degree `p`
  (`nonempty_singularCohomology_sublevelPair_iso_singularCohomology_of_isThomClass`).
* Such a Thom class exists for every commutative ring `K` when `ν⁻` is oriented
  (`nonempty_singularCohomology_sublevelPair_iso_singularCohomology_of_orientation`), for instance
  `K = ℤ`, and with no orientation when `2 = 0` in `K`, as for `K = ZMod 2`
  (`nonempty_singularCohomology_sublevelPair_iso_singularCohomology_of_two_eq_zero`).

These are the cohomology forms of the homology statements in
`TauCeti.Geometry.Manifold.Morse.Bott.Thom.Class`, and the actual-negative-bundle forms of
`TauCeti.nonempty_singularCohomology_sublevelPair_iso_singularCohomology_of_isThomClass` and its
corollaries, which assume that `f` is already in a quadratic normal form on a tube and that the
negative disc bundle is parametrized by the disc bundle of some vector bundle. For a non-orientable
negative normal bundle and a ring in which `-1 ≠ 1`, the cohomology of `S` must be twisted by the
orientation local system of `ν⁻`, which this file does not treat.

The Thom isomorphism needs the model fibre `Fin r → ℝ` of `ν⁻` in the universe of its base, so the
manifolds, their models and the coefficient ring here live in `Type`.

## Main results

In the namespace `TauCeti.SmoothEmbedding.IsNondegenerateCriticalSubmanifold`:

* `nonempty_singularCohomology_sublevelPair_iso_singularCohomology_of_isThomClass`: a Thom class of
  `ν⁻` identifies `Hᵣ₊ₚ({f ≤ b}, {f ≤ a}; K, N)` with `Hᵖ(S; K, N)`.
* `nonempty_singularCohomology_sublevelPair_iso_singularCohomology_of_orientation`: the same for an
  oriented `ν⁻` and every commutative ring `K`.
* `nonempty_singularCohomology_sublevelPair_iso_singularCohomology_of_two_eq_zero`: the same for
  every `ν⁻` when `2 = 0` in `K`.

## References

* R. Bott, *Nondegenerate critical manifolds*, Annals of Mathematics 60 (1954), 248–261.
* R. L. Cohen, K. Iga and P. Norbury, *Topics in Morse theory: lecture notes*, 2006,
  Theorem 15.4.
* J. W. Milnor, J. D. Stasheff, *Characteristic Classes*, Annals of Mathematics Studies 76,
  Princeton (1974), Theorem 10.4.
-/

public section

noncomputable section

open Bundle CategoryTheory Function Limits Module Set Topology
open scoped ContDiff Manifold

namespace TauCeti.SmoothEmbedding.IsNondegenerateCriticalSubmanifold

/-! ### The shifted cohomology of the critical submanifold -/

section ThomClass

variable {E : Type} {H : Type*} {M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  [SecondCountableTopology M] {E' H' P : Type*} {S : Type} [NormedAddCommGroup E']
  [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
  [TopologicalSpace H'] {J : ModelWithCorners ℝ E' H'} [J.Boundaryless] [TopologicalSpace S]
  [ChartedSpace H' S] [IsManifold J ∞ S] [Nonempty S] [NormedAddCommGroup P] [NormedSpace ℝ P]
  [FiniteDimensional ℝ P] {f : M → ℝ} {i : SmoothEmbedding J I ∞ S M} (hn : (∞ : ℕ∞ω) ≠ 0)
  (h : i.IsNondegenerateCriticalSubmanifold f) (hfs : ContMDiff I 𝓘(ℝ) ∞ f) {a b c : ℝ}
  (hc : ∀ s, f (i s) = c) (hac : a < c) (hcb : c < b) (hcompact : IsCompact (f ⁻¹' Icc a b))
  (hcrit : criticalPoints I f ∩ f ⁻¹' Icc a b ⊆ range i)
  (hdim : finrank ℝ P = finrank ℝ E - finrank ℝ E')
  (g : letI := i.normalSpaceFiberBundle hn hdim
    letI := i.normalSpaceVectorBundle hn hdim
    ContMDiffRiemannianMetric J ∞ P fun s ↦ i.NormalSpace s hn) {r : ℕ}
  (hV : letI := i.normalSpaceFiberBundle hn hdim
    letI := i.normalSpaceVectorBundle hn hdim
    HasLocalSubbundleFrames P (Fin r) (h.negativeNormalSpace hn g.toRiemannianMetric))

include h hfs hc hac hcb hcompact hcrit in
/-- **A Thom class of the negative normal bundle computes the cohomology across a Morse–Bott
level.** Let `i : S → M` be a nondegenerate critical submanifold of a smooth function `f` on a
Hausdorff, second-countable, finite-dimensional, boundaryless manifold, with `S` nonempty and
`f = c` along `i`, and let `g` be a smooth fibre metric on its normal bundle. Let `a < c < b` be
such that the band `f⁻¹[a, b]` is compact and all its critical points lie on `i`. Suppose that the
negative normal spaces relative to `g` have continuous local frames of size `r`, so that they form
the negative normal bundle `ν⁻` of rank `r`, and let `u` be a Thom class of `ν⁻` with coefficients
in a commutative ring `K`. Then `Hᵣ₊ₚ({f ≤ b}, {f ≤ a}; K, N) ≅ Hᵖ(S; K, N)` for every `K`-module
`N` and every degree `p`. This is the cohomology form of
`nonempty_singularHomology_sublevelPair_iso_singularHomology_of_isThomClass`. -/
theorem nonempty_singularCohomology_sublevelPair_iso_singularCohomology_of_isThomClass
    {K : Type} [CommRing K]
    (u : letI := i.normalSpaceFiberBundle hn hdim
      haveI := i.normalSpaceVectorBundle hn hdim
      letI := subbundleTopology P (F' := Fin r → ℝ) (h.negativeNormalSpace hn g.toRiemannianMetric)
      letI := hV.fiberBundle
      (thomPair (Fin r → ℝ) fun s ↦
        h.negativeNormalSpace hn g.toRiemannianMetric s).singularCohomology
        (ModuleCat.of K K) K (ModuleCat.of K K) (finrank ℝ (Fin r → ℝ)))
    (hu : letI := i.normalSpaceFiberBundle hn hdim
      haveI := i.normalSpaceVectorBundle hn hdim
      letI := subbundleTopology P (F' := Fin r → ℝ) (h.negativeNormalSpace hn g.toRiemannianMetric)
      letI := hV.fiberBundle
      IsThomClass (Fin r → ℝ) (fun s ↦ h.negativeNormalSpace hn g.toRiemannianMetric s) u)
    (N : ModuleCat.{0} K) {p m : ℕ} (hm : r + p = m) :
    Nonempty ((sublevelPair f (hac.trans hcb).le).singularCohomology (ModuleCat.of K K) K N m ≅
      (TopCat.of S).singularCohomology (ModuleCat.of K K) K N p) := by
  let := i.normalSpaceFiberBundle hn hdim
  let := i.normalSpaceVectorBundle hn hdim
  let := subbundleTopology P (F' := Fin r → ℝ) (h.negativeNormalSpace hn g.toRiemannianMetric)
  let := hV.fiberBundle
  have := hV.vectorBundle
  have := h.toIsCriticalSubmanifold.compactSpace_of_isCompact_preimage_Icc (hfs.of_le (by simp))
    hc hac.le hcb.le hcompact hcrit
  -- The negative normal spaces have the dimension of the Morse index.
  have hr (s : S) : manifoldMorseIndex I f (i s) = r := by
    rw [← h.finrank_negativeNormalSpace hn g.toRiemannianMetric s, hV.finrank_eq s,
      Fintype.card_fin]
  -- The band has the cohomology of the Thom pair of `ν⁻`, which the Thom class computes.
  obtain ⟨e⟩ := h.nonempty_singularCohomology_sublevelPair_iso_thomPair hn hfs hc hac hcb hcompact
    hcrit hdim g hr (ModuleCat.of K K) K N m
  exact ⟨e ≪≫ (thomEquivOfCompactSpace (Fin r → ℝ) _ N p m (by rw [finrank_fin_fun]; omega) u
    hu).toModuleIso.symm⟩

include h hfs hc hac hcb hcompact hcrit in
/-- **The cohomology across the level of a Morse–Bott submanifold with an oriented negative normal
bundle.** Under the hypotheses of
`nonempty_singularCohomology_sublevelPair_iso_singularCohomology_of_isThomClass`, suppose that the
negative normal bundle `ν⁻` of rank `r` is oriented. Then for every commutative ring `K`, for
instance `ℤ`, and every `K`-module `N`, `Hᵣ₊ₚ({f ≤ b}, {f ≤ a}; K, N) ≅ Hᵖ(S; K, N)` in every
degree `p`. -/
theorem nonempty_singularCohomology_sublevelPair_iso_singularCohomology_of_orientation
    (o : letI := i.normalSpaceFiberBundle hn hdim
      haveI := i.normalSpaceVectorBundle hn hdim
      letI := subbundleTopology P (F' := Fin r → ℝ) (h.negativeNormalSpace hn g.toRiemannianMetric)
      letI := hV.fiberBundle
      haveI := hV.vectorBundle
      VectorBundleOrientation (Fin r → ℝ) (fun s ↦ h.negativeNormalSpace hn g.toRiemannianMetric s)
        (Fin r))
    (K : Type) [CommRing K] (N : ModuleCat.{0} K) {p m : ℕ} (hm : r + p = m) :
    Nonempty ((sublevelPair f (hac.trans hcb).le).singularCohomology (ModuleCat.of K K) K N m ≅
      (TopCat.of S).singularCohomology (ModuleCat.of K K) K N p) := by
  let := i.normalSpaceFiberBundle hn hdim
  have := i.normalSpaceVectorBundle hn hdim
  let := subbundleTopology P (F' := Fin r → ℝ) (h.negativeNormalSpace hn g.toRiemannianMetric)
  let := hV.fiberBundle
  have := hV.vectorBundle
  obtain ⟨u, hu⟩ := VectorBundleOrientation.exists_isThomClass (by simp) o K
  exact h.nonempty_singularCohomology_sublevelPair_iso_singularCohomology_of_isThomClass hn hfs hc
    hac hcb hcompact hcrit hdim g hV u hu N hm

include h hfs hc hac hcb hcompact hcrit in
/-- **The cohomology across a Morse–Bott level in characteristic two.** Let `i : S → M` be a
nondegenerate critical submanifold of a smooth function `f` on a Hausdorff, second-countable,
finite-dimensional, boundaryless manifold, with `S` nonempty, `f = c` along `i` and Morse index `r`
at every point of `i`. Let `a < c < b` be such that the band `f⁻¹[a, b]` is compact and all its
critical points lie on `i`, and let `K` be a commutative ring in which `2 = 0`, such as `ZMod 2`.
Then with no orientation of the negative normal bundle, `Hᵣ₊ₚ({f ≤ b}, {f ≤ a}; K, N) ≅ Hᵖ(S; K, N)`
for every `K`-module `N` and every degree `p`. -/
theorem nonempty_singularCohomology_sublevelPair_iso_singularCohomology_of_two_eq_zero
    (hr : ∀ s, manifoldMorseIndex I f (i s) = r) (K : Type) [CommRing K] (h2 : (2 : K) = 0)
    (N : ModuleCat.{0} K) {p m : ℕ} (hm : r + p = m) :
    Nonempty ((sublevelPair f (hac.trans hcb).le).singularCohomology (ModuleCat.of K K) K N m ≅
      (TopCat.of S).singularCohomology (ModuleCat.of K K) K N p) := by
  have hn : (∞ : ℕ∞ω) ≠ 0 := by simp
  have := h.toIsCriticalSubmanifold.compactSpace_of_isCompact_preimage_Icc (hfs.of_le (by simp))
    hc hac.le hcb.le hcompact hcrit
  have : T2Space S := i.isEmbedding.t2Space
  -- Choose a smooth fibre metric on the normal bundle; its negative normal spaces form `ν⁻`.
  let P := EuclideanSpace ℝ (Fin (finrank ℝ E - finrank ℝ E'))
  have hdim : finrank ℝ P = finrank ℝ E - finrank ℝ E' := finrank_euclideanSpace_fin
  let := i.normalSpaceFiberBundle hn hdim
  let := i.normalSpaceVectorBundle hn hdim
  have : IsManifold I (∞ + 1) M := by simpa using (inferInstance : IsManifold I ∞ M)
  have : IsManifold I (∞ + 2) M := .of_le (n := ∞) (by simp)
  have : IsManifold J (∞ + 1) S := by simpa using (inferInstance : IsManifold J ∞ S)
  let := i.normalSpaceContMDiffVectorBundle (m := ∞) hn (by simp) hdim
  obtain ⟨g⟩ := nonempty_contMDiffRiemannianMetric (IB := J) (n := ⊤) (F := P)
    (E := fun s ↦ i.NormalSpace s hn)
  have hV := (h.hasLocalContMDiffSubbundleFrames_negativeNormalSpace hn (k := ∞) (by simp)
    (fun s ↦ (hfs (i s)).of_le (by simp)) hdim g hr).hasLocalSubbundleFrames
  let := subbundleTopology P (F' := Fin r → ℝ) (h.negativeNormalSpace hn g.toRiemannianMetric)
  let := hV.fiberBundle
  have := hV.vectorBundle
  -- Every vector bundle has a Thom class with coefficients in `K`.
  obtain ⟨u, hu⟩ := exists_isThomClass_of_two_eq_zero (F := Fin r → ℝ)
    (E := fun s ↦ h.negativeNormalSpace hn g.toRiemannianMetric s) K h2
  exact h.nonempty_singularCohomology_sublevelPair_iso_singularCohomology_of_isThomClass hn hfs hc
    hac hcb hcompact hcrit hdim g hV u hu N hm

end ThomClass

end TauCeti.SmoothEmbedding.IsNondegenerateCriticalSubmanifold
