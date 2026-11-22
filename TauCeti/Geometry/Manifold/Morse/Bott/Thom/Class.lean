/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Morse.Bott.Thom.Pair
public import TauCeti.Topology.VectorBundle.Orientation.ThomClass
public import TauCeti.Topology.VectorBundle.Thom.Homology

/-!
# The homology across a Morse–Bott level from a Thom class of the negative normal bundle

Let `i : S → M` be a nondegenerate critical submanifold of a smooth function `f`, on the level
`f = c`, and let `g` be a fibre metric on its normal bundle. The metric selects the negative normal
spaces `ν⁻`, on which the normal Hessian is negative definite; when they have continuous local
frames of size `r` they form a real vector bundle `ν⁻ → S` of rank `r`, the negative normal bundle.
For `ε > 0` the pair `(D_ε, S_ε)` of the negative disc and sphere bundles has the homology of the
Thom pair `(ν⁻, ν⁻₀)`
(`TauCeti.SmoothEmbedding.IsCriticalSubmanifold.isIso_singularHomologyMap_negativeDiscThomPairMap`),
and when the band `f⁻¹[a, b]` around the level is compact with all its critical points on `i`, the
relative homology across the level is that of `(D_ε, S_ε)` for all small `ε > 0`
(`nonempty_singularHomology_sublevelPair_iso_negativeDiscSpherePair` in
`TauCeti.Geometry.Manifold.Morse.Bott.Thom.Pair`). This file applies the homology Thom
isomorphism `Hᵣ₊ₚ(ν⁻, ν⁻₀; K) ≅ Hₚ(S; K)` (`TauCeti.homologyThomIso`) to these pairs:

* given a Thom class `u` of `ν⁻` with coefficients in a commutative ring `K`, the pair `(D_ε, S_ε)`
  has the homology of `S` shifted by the rank, `Hᵣ₊ₚ(D_ε, S_ε; K) ≅ Hₚ(S; K)`
  (`nonempty_singularHomology_negativeDiscSpherePair_iso_singularHomology_of_isThomClass`);
* given such a `u`, if `a < c < b`, the band `f⁻¹[a, b]` is compact and all its critical points lie
  on `i`, then crossing the level shifts the homology of `S` by the rank,
  `Hᵣ₊ₚ({f ≤ b}, {f ≤ a}; K) ≅ Hₚ(S; K)`
  (`nonempty_singularHomology_sublevelPair_iso_singularHomology_of_isThomClass`).

An orientation of `ν⁻` provides a Thom class with coefficients in every commutative ring
(`TauCeti.VectorBundleOrientation.exists_isThomClass`), so for an oriented negative normal bundle
both isomorphisms hold over every commutative ring, for instance `ℤ`
(`nonempty_singularHomology_negativeDiscSpherePair_iso_singularHomology_of_orientation` and
`nonempty_singularHomology_sublevelPair_iso_singularHomology_of_orientation`).
This is the untwisted case of Bott's identification of the relative homology across a critical
level with the homology of the critical submanifold, shifted by the index and twisted by the
orientation local system of `ν⁻`, which an orientation trivializes
(`TauCeti.VectorBundleOrientation.signLocalSystemIso`). Without an orientation the integral
statement fails: for a critical circle of index one whose negative normal bundle is a Möbius line,
`H₁(D_ε, S_ε; ℤ)` is `ℤ/2`, not `H₀(S¹; ℤ) = ℤ`.

A level generally carries several critical submanifolds `i j : S j → M`, whose negative normal
bundles `ν⁻ j` have ranks `r j`, and the relative homology across it is the coproduct of the
homologies of their Thom pairs
(`TauCeti.SmoothEmbedding.nonempty_singularHomology_sublevelPair_iso_sigma_thomPair`). Given a Thom
class of each `ν⁻ j` over `K`, the Thom pairs of rank above `n` have no homology in degree `n` and
the others have the homology of their bases shifted by the rank, so

`Hₙ({f ≤ b}, {f ≤ a}; K) ≅ ∐_{r j ≤ n} H_{n - r j}(S j; K)`

(`TauCeti.SmoothEmbedding.nonempty_singularHomology_sublevelPair_iso_sigma_of_isThomClass`), and
the same holds across a critical level of a Morse–Bott function on a compact manifold, the
coproduct running over the pieces on that level
(`TauCeti.IsMorseBottFamily.nonempty_singularHomology_sublevelPair_iso_sigma_of_isThomClass`).
This is the form of Bott's computation that produces the first page of the critical-band spectral
sequence (`TauCeti.Geometry.Manifold.Morse.Bott.SpectralSequence`).

The Thom isomorphism needs the model fibre `Fin r → ℝ` of `ν⁻` in the universe of its base, so in
all statements below the base `S`, the model space `E` of `M` and the coefficient ring `K` live in
`Type`, and in the band statements so does `M`.

## Main results

In the namespace `TauCeti.SmoothEmbedding.IsCriticalSubmanifold`:

* `nonempty_singularHomology_negativeDiscSpherePair_iso_singularHomology_of_isThomClass`: a Thom
  class of `ν⁻` identifies `Hᵣ₊ₚ(D_ε, S_ε; K)` with `Hₚ(S; K)`.
* `nonempty_singularHomology_negativeDiscSpherePair_iso_singularHomology_of_orientation`: the same
  for an oriented `ν⁻` and every commutative ring `K`.

In the namespace `TauCeti.SmoothEmbedding.IsNondegenerateCriticalSubmanifold`:

* `nonempty_singularHomology_sublevelPair_iso_singularHomology_of_isThomClass`: a Thom class of
  `ν⁻` identifies the relative homology `Hᵣ₊ₚ({f ≤ b}, {f ≤ a}; K)` of a critical band with
  `Hₚ(S; K)`.
* `nonempty_singularHomology_sublevelPair_iso_singularHomology_of_orientation`: the same for an
  oriented `ν⁻` and every commutative ring `K`.

In the namespaces `TauCeti.SmoothEmbedding` and `TauCeti.IsMorseBottFamily`:

* `nonempty_singularHomology_sublevelPair_iso_sigma_of_isThomClass`: Thom classes of the negative
  normal bundles of the critical submanifolds on a level identify the relative homology across it
  with `∐_{r j ≤ n} H_{n - r j}(S j; K)`.

## References

* R. Bott, *Nondegenerate critical manifolds*, Annals of Mathematics 60 (1954), 248–261.
* R. L. Cohen, K. Iga and P. Norbury, *Topics in Morse theory: lecture notes*, 2006,
  Theorems 15.4 and 15.6.
* J. W. Milnor, J. D. Stasheff, *Characteristic Classes*, Annals of Mathematics Studies 76,
  Princeton (1974), §10 (the Thom isomorphism).
-/

public section

noncomputable section

open AlgebraicTopology Bundle CategoryTheory Function Limits Module Set Topology
open scoped ContDiff Manifold

namespace TauCeti.SmoothEmbedding

/-! ### The negative disc-sphere pair -/

namespace IsCriticalSubmanifold

variable {E : Type} {H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  {E' H' : Type*} {S : Type} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
  [TopologicalSpace H'] {J : ModelWithCorners ℝ E' H'} [TopologicalSpace S] [ChartedSpace H' S]
  [IsManifold J 1 S] {f : M → ℝ} {n : ℕ∞ω} {i : SmoothEmbedding J I n S M} (hn : n ≠ 0)
  [I.Boundaryless] [IsManifold I 2 M] (h : i.IsCriticalSubmanifold f)
  {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
  (g : RiemannianMetric fun s ↦ i.NormalSpace s hn) {ε : ℝ}
  (hdim : finrank ℝ P = finrank ℝ E - finrank ℝ E') {r : ℕ}

/-- **A Thom class of the negative normal bundle computes the homology of the negative disc
bundle.** Let `i` be a critical submanifold of `f`, let `g` be a fibre metric on its normal bundle,
and suppose that the negative normal spaces have continuous local frames of size `r`, so that they
form a vector bundle `ν⁻` of rank `r`. Let `u` be a Thom class of `ν⁻` with coefficients in a
commutative ring `K`. Then for `ε > 0` the negative disc bundle `D_ε`, relative to the negative
sphere bundle `S_ε`, has the homology of `S` shifted by `r`: `Hᵣ₊ₚ(D_ε, S_ε; K) ≅ Hₚ(S; K)` in
every degree `p`. -/
theorem nonempty_singularHomology_negativeDiscSpherePair_iso_singularHomology_of_isThomClass
    (hV : letI := i.normalSpaceFiberBundle hn hdim
      HasLocalSubbundleFrames P (Fin r) (h.negativeNormalSpace hn g))
    (hε : 0 < ε) {K : Type} [CommRing K]
    (u : letI := i.normalSpaceFiberBundle hn hdim
      haveI := i.normalSpaceVectorBundle hn hdim
      letI := subbundleTopology P (F' := Fin r → ℝ) (h.negativeNormalSpace hn g)
      letI := hV.fiberBundle
      (thomPair (Fin r → ℝ) fun s ↦ h.negativeNormalSpace hn g s).singularCohomology
        (ModuleCat.of K K) K (ModuleCat.of K K) (finrank ℝ (Fin r → ℝ)))
    (hu : letI := i.normalSpaceFiberBundle hn hdim
      haveI := i.normalSpaceVectorBundle hn hdim
      letI := subbundleTopology P (F' := Fin r → ℝ) (h.negativeNormalSpace hn g)
      letI := hV.fiberBundle
      IsThomClass (Fin r → ℝ) (fun s ↦ h.negativeNormalSpace hn g s) u)
    {p m : ℕ} (hm : r + p = m) :
    Nonempty ((h.negativeDiscSpherePair hn P g ε).singularHomology (ModuleCat.of K K) m ≅
      ((singularHomologyFunctor (ModuleCat.{0} K) p).obj (ModuleCat.of K K)).obj
        (TopCat.of S)) := by
  let := i.normalSpaceFiberBundle hn hdim
  have := i.normalSpaceVectorBundle hn hdim
  let := subbundleTopology P (F' := Fin r → ℝ) (h.negativeNormalSpace hn g)
  let := hV.fiberBundle
  have := hV.vectorBundle
  have := h.isIso_singularHomologyMap_negativeDiscThomPairMap hn g r hdim hV hε
    (ModuleCat.of K K) m
  exact ⟨asIso (TopPair.singularHomologyMap (h.negativeDiscThomPairMap hn P g r hε)
      (ModuleCat.of K K) m) ≪≫
    homologyThomIso (Fin r → ℝ) _ p m (by rwa [finrank_fin_fun]) u hu⟩

/-- **The homology of the negative disc bundle of an oriented negative normal bundle.** Under the
hypotheses of
`nonempty_singularHomology_negativeDiscSpherePair_iso_singularHomology_of_isThomClass`, suppose
that the negative normal bundle `ν⁻` of rank `r` is oriented. Then for `ε > 0` and every
commutative ring `K`, for instance `ℤ`, `Hᵣ₊ₚ(D_ε, S_ε; K) ≅ Hₚ(S; K)` in every degree `p`. -/
theorem nonempty_singularHomology_negativeDiscSpherePair_iso_singularHomology_of_orientation
    (hV : letI := i.normalSpaceFiberBundle hn hdim
      HasLocalSubbundleFrames P (Fin r) (h.negativeNormalSpace hn g))
    (o : letI := i.normalSpaceFiberBundle hn hdim
      haveI := i.normalSpaceVectorBundle hn hdim
      letI := subbundleTopology P (F' := Fin r → ℝ) (h.negativeNormalSpace hn g)
      letI := hV.fiberBundle
      haveI := hV.vectorBundle
      VectorBundleOrientation (Fin r → ℝ) (fun s ↦ h.negativeNormalSpace hn g s) (Fin r))
    (hε : 0 < ε) (K : Type) [CommRing K] {p m : ℕ} (hm : r + p = m) :
    Nonempty ((h.negativeDiscSpherePair hn P g ε).singularHomology (ModuleCat.of K K) m ≅
      ((singularHomologyFunctor (ModuleCat.{0} K) p).obj (ModuleCat.of K K)).obj
        (TopCat.of S)) := by
  let := i.normalSpaceFiberBundle hn hdim
  have := i.normalSpaceVectorBundle hn hdim
  let := subbundleTopology P (F' := Fin r → ℝ) (h.negativeNormalSpace hn g)
  let := hV.fiberBundle
  have := hV.vectorBundle
  obtain ⟨u, hu⟩ := VectorBundleOrientation.exists_isThomClass (by simp) o K
  exact h.nonempty_singularHomology_negativeDiscSpherePair_iso_singularHomology_of_isThomClass hn g
    hdim hV hε u hu hm

end IsCriticalSubmanifold

/-! ### The homology of a critical band -/

namespace IsNondegenerateCriticalSubmanifold

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
/-- **A Thom class of the negative normal bundle computes the homology across a Morse–Bott
level.** Let `i : S → M` be a nondegenerate critical submanifold of a smooth function `f` on a
Hausdorff, second-countable, finite-dimensional, boundaryless manifold, with `S` nonempty and
`f = c` along `i`, and let `g` be a smooth fibre metric on its normal bundle. Let `a < c < b` be
such that the band `f⁻¹[a, b]` is compact and all its critical points lie on `i`. Suppose that the
negative normal spaces relative to `g` have continuous local frames of size `r`, so that they form
the negative normal bundle `ν⁻` of rank `r`, and let `u` be a Thom class of `ν⁻` with coefficients
in a commutative ring `K`. Then `Hᵣ₊ₚ({f ≤ b}, {f ≤ a}; K) ≅ Hₚ(S; K)` in every degree `p`. -/
theorem nonempty_singularHomology_sublevelPair_iso_singularHomology_of_isThomClass
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
    {p m : ℕ} (hm : r + p = m) :
    Nonempty ((sublevelPair f (hac.trans hcb).le).singularHomology (ModuleCat.of K K) m ≅
      ((singularHomologyFunctor (ModuleCat.{0} K) p).obj (ModuleCat.of K K)).obj
        (TopCat.of S)) := by
  let := i.normalSpaceFiberBundle hn hdim
  let := i.normalSpaceVectorBundle hn hdim
  -- The band has the homology of `(D_ε, S_ε)`, which the Thom class computes.
  obtain ⟨ε₀, hε₀, hband⟩ :=
    h.nonempty_singularHomology_sublevelPair_iso_negativeDiscSpherePair hn hfs hc hac hcb hcompact
      hcrit hdim g hV
  have hε : ε₀ / 2 ∈ Ioo 0 ε₀ := ⟨half_pos hε₀, half_lt_self hε₀⟩
  obtain ⟨e₁⟩ := hband (ε₀ / 2) hε (ModuleCat.of K K) m
  have h' := h.toIsCriticalSubmanifold
  obtain ⟨e₂⟩ :=
    h'.nonempty_singularHomology_negativeDiscSpherePair_iso_singularHomology_of_isThomClass hn
      g.toRiemannianMetric hdim hV hε.1 u hu hm
  exact ⟨e₁ ≪≫ e₂⟩

include h hfs hc hac hcb hcompact hcrit in
/-- **The homology across the level of a Morse–Bott submanifold with an oriented negative normal
bundle.** Under the hypotheses of
`nonempty_singularHomology_sublevelPair_iso_singularHomology_of_isThomClass`,
suppose that the negative normal bundle `ν⁻` of rank `r` is oriented. Then for every commutative
ring `K`, for instance `ℤ`, `Hᵣ₊ₚ({f ≤ b}, {f ≤ a}; K) ≅ Hₚ(S; K)` in every degree `p`. -/
theorem nonempty_singularHomology_sublevelPair_iso_singularHomology_of_orientation
    (o : letI := i.normalSpaceFiberBundle hn hdim
      haveI := i.normalSpaceVectorBundle hn hdim
      letI := subbundleTopology P (F' := Fin r → ℝ) (h.negativeNormalSpace hn g.toRiemannianMetric)
      letI := hV.fiberBundle
      haveI := hV.vectorBundle
      VectorBundleOrientation (Fin r → ℝ) (fun s ↦ h.negativeNormalSpace hn g.toRiemannianMetric s)
        (Fin r))
    (K : Type) [CommRing K] {p m : ℕ} (hm : r + p = m) :
    Nonempty ((sublevelPair f (hac.trans hcb).le).singularHomology (ModuleCat.of K K) m ≅
      ((singularHomologyFunctor (ModuleCat.{0} K) p).obj (ModuleCat.of K K)).obj
        (TopCat.of S)) := by
  let := i.normalSpaceFiberBundle hn hdim
  have := i.normalSpaceVectorBundle hn hdim
  let := subbundleTopology P (F' := Fin r → ℝ) (h.negativeNormalSpace hn g.toRiemannianMetric)
  let := hV.fiberBundle
  have := hV.vectorBundle
  obtain ⟨u, hu⟩ := VectorBundleOrientation.exists_isThomClass (by simp) o K
  exact h.nonempty_singularHomology_sublevelPair_iso_singularHomology_of_isThomClass hn hfs hc hac
    hcb hcompact hcrit hdim g hV u hu hm

end IsNondegenerateCriticalSubmanifold

end TauCeti.SmoothEmbedding

/-! ### A critical level carrying several submanifolds -/

namespace TauCeti

variable {E M : Type} {H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] {ι : Type*} {E' H' P : ι → Type*}
  {S : ι → Type} [∀ j, NormedAddCommGroup (E' j)] [∀ j, NormedSpace ℝ (E' j)]
  [∀ j, FiniteDimensional ℝ (E' j)] [∀ j, TopologicalSpace (H' j)]
  {J : ∀ j, ModelWithCorners ℝ (E' j) (H' j)} [∀ j, TopologicalSpace (S j)]
  [∀ j, ChartedSpace (H' j) (S j)] [∀ j, IsManifold (J j) ∞ (S j)]
  [∀ j, NormedAddCommGroup (P j)] [∀ j, NormedSpace ℝ (P j)] [∀ j, FiniteDimensional ℝ (P j)]
  {f : M → ℝ} {i : ∀ j, SmoothEmbedding (J j) I ∞ (S j) M} (hn : (∞ : ℕ∞ω) ≠ 0)

/-- **Thom classes of the negative normal bundles compute the homology across a level of finitely
many Morse–Bott submanifolds.** Let `i j : S j → M`, for `j` in a finite index type, be
nondegenerate critical submanifolds of a smooth function `f` on a Hausdorff, second-countable,
finite-dimensional, boundaryless manifold, each modelled on its own boundaryless model, with `S j`
compact and nonempty, pairwise disjoint images and `f = c` along each of them. Let `g j` be a
smooth fibre metric on the normal bundle of `i j`, and suppose that the negative normal spaces
relative to `g j` have continuous local frames of size `r j`, so that they form the negative normal
bundle `ν⁻ j` of rank `r j`. Let `u j` be a Thom class of `ν⁻ j` with coefficients in a commutative
ring `K`. Let `a < c < b` be such that the band `f⁻¹[a, b]` is compact and all its critical points
lie on the submanifolds.

Then `Hₙ({f ≤ b}, {f ≤ a}; K) ≅ ∐ H_{n - r j}(S j; K)`, the coproduct running over the
submanifolds with `r j ≤ n`, in every degree `n`. -/
theorem
    SmoothEmbedding.nonempty_singularHomology_sublevelPair_iso_sigma_of_isThomClass
    [T2Space M] [SecondCountableTopology M] [Finite ι] [∀ j, (J j).Boundaryless]
    [∀ j, CompactSpace (S j)] [∀ j, Nonempty (S j)]
    (h : ∀ j, (i j).IsNondegenerateCriticalSubmanifold f) (hfs : ContMDiff I 𝓘(ℝ) ∞ f)
    {a b c : ℝ} (hc : ∀ j s, f (i j s) = c) (hd : Pairwise (Disjoint on fun j ↦ range (i j)))
    (hac : a < c) (hcb : c < b) (hcompact : IsCompact (f ⁻¹' Icc a b))
    (hcrit : criticalPoints I f ∩ f ⁻¹' Icc a b ⊆ ⋃ j, range (i j))
    (hdim : ∀ j, finrank ℝ (P j) = finrank ℝ E - finrank ℝ (E' j))
    (g : letI : ∀ j, FiberBundle (P j) fun s ↦ (i j).NormalSpace s hn :=
        fun j ↦ (i j).normalSpaceFiberBundle hn (hdim j)
      letI : ∀ j, VectorBundle ℝ (P j) fun s ↦ (i j).NormalSpace s hn :=
        fun j ↦ (i j).normalSpaceVectorBundle hn (hdim j)
      ∀ j, ContMDiffRiemannianMetric (J j) ∞ (P j) fun s ↦ (i j).NormalSpace s hn)
    {r : ι → ℕ}
    (hV : letI : ∀ j, FiberBundle (P j) fun s ↦ (i j).NormalSpace s hn :=
        fun j ↦ (i j).normalSpaceFiberBundle hn (hdim j)
      letI : ∀ j, VectorBundle ℝ (P j) fun s ↦ (i j).NormalSpace s hn :=
        fun j ↦ (i j).normalSpaceVectorBundle hn (hdim j)
      ∀ j, HasLocalSubbundleFrames (P j) (Fin (r j))
        ((h j).negativeNormalSpace hn (g j).toRiemannianMetric))
    {K : Type} [CommRing K]
    (u : letI : ∀ j, FiberBundle (P j) fun s ↦ (i j).NormalSpace s hn :=
        fun j ↦ (i j).normalSpaceFiberBundle hn (hdim j)
      letI : ∀ j, VectorBundle ℝ (P j) fun s ↦ (i j).NormalSpace s hn :=
        fun j ↦ (i j).normalSpaceVectorBundle hn (hdim j)
      letI : ∀ j, TopologicalSpace (TotalSpace (Fin (r j) → ℝ)
          fun s ↦ (h j).negativeNormalSpace hn (g j).toRiemannianMetric s) :=
        fun j ↦ subbundleTopology (P j) ((h j).negativeNormalSpace hn (g j).toRiemannianMetric)
      letI : ∀ j, FiberBundle (Fin (r j) → ℝ)
          fun s ↦ (h j).negativeNormalSpace hn (g j).toRiemannianMetric s :=
        fun j ↦ (hV j).fiberBundle
      ∀ j, (thomPair (Fin (r j) → ℝ)
        fun s ↦ (h j).negativeNormalSpace hn (g j).toRiemannianMetric s).singularCohomology
          (ModuleCat.of K K) K (ModuleCat.of K K) (finrank ℝ (Fin (r j) → ℝ)))
    (hu : letI : ∀ j, FiberBundle (P j) fun s ↦ (i j).NormalSpace s hn :=
        fun j ↦ (i j).normalSpaceFiberBundle hn (hdim j)
      letI : ∀ j, VectorBundle ℝ (P j) fun s ↦ (i j).NormalSpace s hn :=
        fun j ↦ (i j).normalSpaceVectorBundle hn (hdim j)
      letI : ∀ j, TopologicalSpace (TotalSpace (Fin (r j) → ℝ)
          fun s ↦ (h j).negativeNormalSpace hn (g j).toRiemannianMetric s) :=
        fun j ↦ subbundleTopology (P j) ((h j).negativeNormalSpace hn (g j).toRiemannianMetric)
      letI : ∀ j, FiberBundle (Fin (r j) → ℝ)
          fun s ↦ (h j).negativeNormalSpace hn (g j).toRiemannianMetric s :=
        fun j ↦ (hV j).fiberBundle
      ∀ j, IsThomClass (Fin (r j) → ℝ)
        (fun s ↦ (h j).negativeNormalSpace hn (g j).toRiemannianMetric s) (u j))
    (n : ℕ) :
    Nonempty ((sublevelPair f (hac.trans hcb).le).singularHomology (ModuleCat.of K K) n ≅
      ∐ fun j : {j // r j ≤ n} ↦ ((singularHomologyFunctor (ModuleCat.{0} K) (n - r j)).obj
        (ModuleCat.of K K)).obj (TopCat.of (S j))) := by
  let _ : ∀ j, FiberBundle (P j) fun s ↦ (i j).NormalSpace s hn :=
    fun j ↦ (i j).normalSpaceFiberBundle hn (hdim j)
  have _ : ∀ j, VectorBundle ℝ (P j) fun s ↦ (i j).NormalSpace s hn :=
    fun j ↦ (i j).normalSpaceVectorBundle hn (hdim j)
  let _ : ∀ j, TopologicalSpace (TotalSpace (Fin (r j) → ℝ)
      fun s ↦ (h j).negativeNormalSpace hn (g j).toRiemannianMetric s) :=
    fun j ↦ subbundleTopology (P j) ((h j).negativeNormalSpace hn (g j).toRiemannianMetric)
  let _ : ∀ j, FiberBundle (Fin (r j) → ℝ)
      fun s ↦ (h j).negativeNormalSpace hn (g j).toRiemannianMetric s :=
    fun j ↦ (hV j).fiberBundle
  have _ : ∀ j, VectorBundle ℝ (Fin (r j) → ℝ)
      fun s ↦ (h j).negativeNormalSpace hn (g j).toRiemannianMetric s :=
    fun j ↦ (hV j).vectorBundle
  -- The Morse index along `i j` is the rank `r j` of the negative normal bundle.
  have hr (j : ι) (s : S j) : manifoldMorseIndex I f (i j s) = r j := by
    rw [← (h j).finrank_negativeNormalSpace hn (g j).toRiemannianMetric s, (hV j).finrank_eq s,
      Fintype.card_fin]
  obtain ⟨e⟩ := SmoothEmbedding.nonempty_singularHomology_sublevelPair_iso_sigma_thomPair hn h hfs
    hc hd hac hcb hcompact hcrit hdim g hr (ModuleCat.of K K) n
  -- The Thom pairs of the bundles of rank above `n` have no homology in degree `n`.
  have hzero (j : ι) (hj : ¬ r j ≤ n) : IsZero ((thomPair (Fin (r j) → ℝ)
      fun s ↦ (h j).negativeNormalSpace hn (g j).toRiemannianMetric s).singularHomology
        (ModuleCat.of K K) n) :=
    isZero_singularHomology_thomPair _ (by simpa using hj)
  -- Drop those summands, and apply the Thom isomorphism to the others.
  exact ⟨e ≪≫ (biproduct.isoCoproduct _).symm ≪≫
    (biproductSubtypeIsoOfIsZero _ (fun j ↦ r j ≤ n) hzero).symm ≪≫ biproduct.isoCoproduct _ ≪≫
    Sigma.mapIso fun j ↦
      homologyThomIso (Fin (r j) → ℝ) _ (n - r j) n (by simp [j.property]) (u j) (hu j)⟩

/-- **Thom classes of the negative normal bundles compute the homology across a critical level of a
Morse–Bott function.** Let the family `i j : S j → M` exhibit `f` as a Morse–Bott function
(`TauCeti.IsMorseBottFamily`) on a compact Hausdorff second-countable boundaryless manifold, with
pieces modelled on boundaryless models, and let `K` be a commutative ring. Suppose that for each
piece `S j` the negative normal bundle, relative to some smooth fibre metric on the normal bundle,
has rank `r j` and a Thom class with coefficients in `K`, as it does over every `K` when it is
oriented (`TauCeti.VectorBundleOrientation.exists_isThomClass`). Let `a < c < b` be such that `c`
is the only critical value of `f` in `[a, b]`.

Then `Hₙ({f ≤ b}, {f ≤ a}; K) ≅ ∐ H_{n - r j}(S j; K)`, the coproduct running over the pieces on
the level `f = c` with `r j ≤ n`, in every degree `n`. -/
theorem
    IsMorseBottFamily.nonempty_singularHomology_sublevelPair_iso_sigma_of_isThomClass
    [T2Space M] [SecondCountableTopology M] [CompactSpace M] [∀ j, (J j).Boundaryless]
    (h : IsMorseBottFamily i f)
    (hdim : ∀ j, finrank ℝ (P j) = finrank ℝ E - finrank ℝ (E' j)) {r : ι → ℕ}
    {K : Type} [CommRing K]
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
    {a b c : ℝ} (hac : a < c) (hcb : c < b)
    (hcrit : ∀ x ∈ criticalPoints I f, f x ∈ Icc a b → f x = c) (n : ℕ) :
    -- The pieces are finitely many, so the coproduct exists.
    haveI := h.finite
    Nonempty ((sublevelPair f (hac.trans hcb).le).singularHomology (ModuleCat.of K K) n ≅
      ∐ fun j : {j // (∀ s, f (i j s) = c) ∧ r j ≤ n} ↦
        ((singularHomologyFunctor (ModuleCat.{0} K) (n - r j)).obj (ModuleCat.of K K)).obj
          (TopCat.of (S j))) := by
  have := h.finite
  have (j : ι) : Nonempty (S j) := h.nonempty j
  have (j : ι) : CompactSpace (S j) :=
    (Topology.IsClosedEmbedding.mk (i j).isEmbedding (h.isClosed_range j)).compactSpace
  let _ (j : ι) := (i j).normalSpaceFiberBundle hn (hdim j)
  let _ (j : ι) := (i j).normalSpaceVectorBundle hn (hdim j)
  choose g hV u hu using hK
  obtain ⟨e⟩ :=
    SmoothEmbedding.nonempty_singularHomology_sublevelPair_iso_sigma_of_isThomClass
      (ι := {j // ∀ s, f (i j s) = c}) (S := fun j ↦ S j) (P := fun j ↦ P j) (J := fun j ↦ J j)
      (i := fun j ↦ i j) hn (fun j ↦ h.isNondegenerateCriticalSubmanifold j) h.contMDiff
      (fun j ↦ j.property) (fun j k hjk ↦ h.pairwise_disjoint_range fun he ↦ hjk (Subtype.ext he))
      hac hcb (isClosed_Icc.preimage h.contMDiff.continuous).isCompact
      (fun x ⟨hx, hfx⟩ ↦ h.mem_iUnion_range_of_apply_eq hn hx (hcrit _ hx hfx)) (fun j ↦ hdim j)
      (fun j ↦ g j) (fun j ↦ hV j) (fun j ↦ u j) (fun j ↦ hu j) n
  -- Reindex the pieces of rank at most `n` among those on the level `c`.
  exact ⟨e ≪≫ Sigma.whiskerEquiv (Equiv.subtypeSubtypeEquivSubtypeInter _ _)
    (g := fun j : {j // (∀ s, f (i j s) = c) ∧ r j ≤ n} ↦
      ((singularHomologyFunctor (ModuleCat.{0} K) (n - r j)).obj (ModuleCat.of K K)).obj
        (TopCat.of (S j))) fun _ ↦ Iso.refl _⟩

end TauCeti
