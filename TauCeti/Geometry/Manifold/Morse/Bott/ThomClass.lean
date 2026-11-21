/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Morse.Bott.Homology
public import TauCeti.Geometry.Manifold.Morse.Bott.ThomPair
public import TauCeti.Topology.VectorBundle.Orientation.ThomClass
public import TauCeti.Topology.VectorBundle.Thom.Homology
import TauCeti.Geometry.Manifold.Morse.Bott.Adjunction

/-!
# The homology across a Morse–Bott level from a Thom class of the negative normal bundle

Let `i : S → M` be a nondegenerate critical submanifold of a smooth function `f`, on the level
`f = c`, and let `g` be a fibre metric on its normal bundle. The metric selects the negative normal
spaces `ν⁻`, on which the normal Hessian is negative definite; when they have continuous local
frames of size `r` they form a real vector bundle `ν⁻ → S` of rank `r`, the negative normal bundle.
For `ε > 0` the pair `(D_ε, S_ε)` of the negative disc and sphere bundles has the homology of the
Thom pair `(ν⁻, ν⁻₀)`
(`TauCeti.SmoothEmbedding.IsCriticalSubmanifold.isIso_singularHomologyMap_negativeDiscThomPairMap`),
and crossing the level attaches `D_ε` along `S_ε` to the lower sublevel `{f ≤ c - ε}` through a
Morse–Bott normal form `Θ`. This file reads that attachment in homology and applies the homology
Thom isomorphism `Hᵣ₊ₚ(ν⁻, ν⁻₀; K) ≅ Hₚ(S; K)` (`TauCeti.homologyThomIso`) to it:

* `(D_ε, S_ε)` has the homology of the lower sublevel with `Θ(D_ε)` attached,
  `Hₖ(D_ε, S_ε) ≅ Hₖ({f ≤ c - ε} ∪ Θ(D_ε), {f ≤ c - ε})`, whenever `D_ε` is compact and `Θ` is
  continuous and injective on it
  (`IsCriticalSubmanifold.nonempty_singularHomology_negativeDiscSpherePair_iso_union`);
* given a Thom class `u` of `ν⁻` with coefficients in a commutative ring `K`, the pair `(D_ε, S_ε)`
  has the homology of `S` shifted by the rank, `Hᵣ₊ₚ(D_ε, S_ε; K) ≅ Hₚ(S; K)`
  (`IsCriticalSubmanifold.nonempty_singularHomology_negativeDiscSpherePair_iso_of_isThomClass`);
* given such a `u`, if `a < c < b`, the band `f⁻¹[a, b]` is compact and all its critical points lie
  on `i`, then crossing the level shifts the homology of `S` by the rank,
  `Hᵣ₊ₚ({f ≤ b}, {f ≤ a}; K) ≅ Hₚ(S; K)`
  (`IsNondegenerateCriticalSubmanifold.nonempty_singularHomology_sublevelPair_iso_of_isThomClass`).

An orientation of `ν⁻` provides a Thom class with coefficients in every commutative ring
(`TauCeti.VectorBundleOrientation.exists_isThomClass`), so for an oriented negative normal bundle
the last two isomorphisms hold over every commutative ring, for instance `ℤ`
(`IsCriticalSubmanifold.nonempty_singularHomology_negativeDiscSpherePair_iso_of_orientation` and
`IsNondegenerateCriticalSubmanifold.nonempty_singularHomology_sublevelPair_iso_of_orientation`).
This is the untwisted case of Bott's identification of the relative homology across a critical
level with the homology of the critical submanifold, shifted by the index and twisted by the
orientation local system of `ν⁻`, which an orientation trivializes
(`TauCeti.VectorBundleOrientation.signLocalSystemIso`). Without an orientation the integral
statement fails: for a critical circle of index one whose negative normal bundle is a Möbius line,
`H₁(D_ε, S_ε; ℤ)` is `ℤ/2`, not `H₀(S¹; ℤ) = ℤ`.

The Thom isomorphism needs the model fibre `Fin r → ℝ` of `ν⁻` in the universe of its base, so the
manifolds, their models and the coefficient ring of the Thom-class statements live in `Type`.

## Main results

In the namespace `TauCeti.SmoothEmbedding.IsCriticalSubmanifold`:

* `nonempty_singularHomology_negativeDiscSpherePair_iso_union`: `(D_ε, S_ε)` has the homology of
  its attachment `({f ≤ c - ε} ∪ Θ(D_ε), {f ≤ c - ε})`.
* `nonempty_singularHomology_negativeDiscSpherePair_iso_of_isThomClass`: a Thom class of `ν⁻`
  identifies `Hᵣ₊ₚ(D_ε, S_ε; K)` with `Hₚ(S; K)`.
* `nonempty_singularHomology_negativeDiscSpherePair_iso_of_orientation`: the same for an oriented
  `ν⁻` and every commutative ring `K`.

In the namespace `TauCeti.SmoothEmbedding.IsNondegenerateCriticalSubmanifold`:

* `nonempty_singularHomology_sublevelPair_iso_of_isThomClass`: a Thom class of `ν⁻` identifies the
  relative homology `Hᵣ₊ₚ({f ≤ b}, {f ≤ a}; K)` of a critical band with `Hₚ(S; K)`.
* `nonempty_singularHomology_sublevelPair_iso_of_orientation`: the same for an oriented `ν⁻` and
  every commutative ring `K`.

## References

* R. Bott, *Nondegenerate critical manifolds*, Annals of Mathematics 60 (1954), 248–261.
* R. L. Cohen, K. Iga and P. Norbury, *Topics in Morse theory: lecture notes*, 2006,
  Theorem 15.4.
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
theorem nonempty_singularHomology_negativeDiscSpherePair_iso_of_isThomClass
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
hypotheses of `nonempty_singularHomology_negativeDiscSpherePair_iso_of_isThomClass`, suppose that
the negative normal bundle `ν⁻` of rank `r` is oriented. Then for `ε > 0` and every commutative ring
`K`, for instance `ℤ`, `Hᵣ₊ₚ(D_ε, S_ε; K) ≅ Hₚ(S; K)` in every degree `p`. -/
theorem nonempty_singularHomology_negativeDiscSpherePair_iso_of_orientation
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
  exact h.nonempty_singularHomology_negativeDiscSpherePair_iso_of_isThomClass hn g hdim hV hε u hu
    hm

end IsCriticalSubmanifold

/-! ### The negative disc-sphere pair and the attachment across the level -/

section Attachment

universe u

variable {E M S : Type u} {H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 2 M] [T2Space M] {E' H' : Type*}
  [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E'] [TopologicalSpace H']
  {J : ModelWithCorners ℝ E' H'} [TopologicalSpace S] [ChartedSpace H' S] [IsManifold J 1 S]
  {f : M → ℝ} {n : ℕ∞ω} {i : SmoothEmbedding J I n S M} (hn : n ≠ 0)
  {h : i.IsCriticalSubmanifold f} {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [FiniteDimensional ℝ P] (g : RiemannianMetric fun s ↦ i.NormalSpace s hn)
  {Θ : TotalSpace P (fun s ↦ i.NormalSpace s hn) → M} {c ε : ℝ}

namespace IsCriticalSubmanifold

/-- **The negative disc-sphere pair has the homology of its attachment across the level.** Let `i`
be a critical submanifold of a continuous function `f` on a Hausdorff manifold, let `g` be a fibre
metric on its normal bundle, and suppose that the negative normal spaces have continuous local
frames of size `r` and that the negative disc bundle `D_ε`, `ε > 0`, is compact. Let `Θ` be
continuous and injective on `D_ε` and put `f` there in the Morse–Bott normal form
`f (Θ v) = c + ½ Hessₛ (v, v)`. Then `(D_ε, S_ε)` has the relative homology of the lower sublevel
`L = {f ≤ c - ε}` with `Θ(D_ε)` attached: `Hₖ(D_ε, S_ε) ≅ Hₖ(L ∪ Θ(D_ε), L)`, with coefficients in
any abelian category with coproducts, in every degree. -/
theorem nonempty_singularHomology_negativeDiscSpherePair_iso_union (hf : Continuous f)
    (hdim : finrank ℝ P = finrank ℝ E - finrank ℝ E') {r : ℕ}
    (hV : letI := i.normalSpaceFiberBundle hn hdim
      HasLocalSubbundleFrames P (Fin r) (h.negativeNormalSpace hn g))
    (hε : 0 < ε) (hD : IsCompact (h.negativeDiscBundle hn P g ε))
    (hΘc : ContinuousOn Θ (h.negativeDiscBundle hn P g ε))
    (hΘi : InjOn Θ (h.negativeDiscBundle hn P g ε))
    (hΘ : ∀ x ∈ h.negativeDiscBundle hn P g ε,
      f (Θ x) = c + 2⁻¹ * h.normalHessian hn x.proj x.snd x.snd)
    {C : Type*} [Category C] [HasCoproducts.{u} C] [Abelian C] (R : C) (k : ℕ) :
    Nonempty ((h.negativeDiscSpherePair hn P g ε).singularHomology R k ≅
      (TopPair.ofInclusion (X := TopCat.of M) (subset_union_left :
        {y | f y ≤ c - ε} ⊆ {y | f y ≤ c - ε} ∪ Θ '' h.negativeDiscBundle hn P g ε)
        ).singularHomology R k) := by
  set D := h.negativeDiscBundle hn P g ε
  set L : Set M := {y | f y ≤ c - ε}
  -- `Θ` restricts to a map of pairs `(D_ε, S_ε) ⟶ (L ∪ Θ(D_ε), L)` attaching `D_ε` along `S_ε`.
  have hχ : MapsTo Θ D (L ∪ Θ '' D) := fun x hx ↦ Or.inr (mem_image_of_mem Θ hx)
  let χ : C(D, (L ∪ Θ '' D : Set M)) := ⟨hχ.restrict, hΘc.mapsToRestrict hχ⟩
  have hS (x : ↥(D ∩ {x | -(2⁻¹ * h.normalHessian hn x.proj x.snd x.snd) = ε})) :
      f (Θ x) ≤ c - ε :=
    (mem_negativeSphereBundle_iff_apply_le hΘ x.property.left).1
      ((mem_negativeSphereBundle hn).2
        ⟨((mem_negativeDiscBundle hn).1 x.property.left).left, x.property.right⟩)
  let φ : h.negativeDiscSpherePair hn P g ε ⟶
      TopPair.ofSubset (X := TopCat.of (L ∪ Θ '' D : Set M)) (Subtype.val ⁻¹' L) :=
    TopPair.ofHom (TopCat.ofHom χ)
      (TopCat.ofHom ⟨fun x ↦ ⟨χ (inclusion inter_subset_left x), hS x⟩,
        ((χ.continuous.comp (continuous_inclusion inter_subset_left)).subtype_mk _)⟩)
      (by ext; rfl)
  have hφ : IsClosedEmbedding χ := by
    have := isCompact_iff_compactSpace.1 hD
    exact χ.continuous.isClosedEmbedding fun x y hxy ↦
      Subtype.ext (hΘi x.property y.property (congrArg Subtype.val hxy))
  have := h.isIso_singularHomologyMap_of_attach_negativeDiscBundle hn g r hdim hV hε
    ((isClosed_le hf continuous_const).preimage continuous_subtypeVal) φ hφ
    (fun x hx ↦ ((mem_negativeSphereBundle hn).1
      ((mem_negativeSphereBundle_iff_apply_le hΘ x.property).2 hx)).right)
    (eq_univ_of_forall fun ⟨y, hy⟩ ↦ by
      rcases hy with hy | ⟨x, hx, rfl⟩
      · exact Or.inl hy
      · exact Or.inr ⟨⟨x, hx⟩, rfl⟩)
    R k
  exact ⟨asIso (TopPair.singularHomologyMap φ R k) ≪≫ TopPair.singularHomologyMapIso R
    (TopPair.ofSubsetPreimageValIso (X := TopCat.of M) (subset_union_left : L ⊆ L ∪ Θ '' D)) k⟩

end IsCriticalSubmanifold

end Attachment

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
theorem nonempty_singularHomology_sublevelPair_iso_of_isThomClass {K : Type} [CommRing K]
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
  have : CompactSpace S := h.toIsCriticalSubmanifold.compactSpace_of_isCompact_preimage_Icc
    (hfs.of_le (by simp)) hc hac.le hcb.le hcompact hcrit
  have : T2Space S := i.isEmbedding.t2Space
  -- Crossing the level attaches `Θ(D_ε)` to `L = {f ≤ c - ε}`, for a normal form `Θ`.
  obtain ⟨Θ, -, -, hΘf, ε₀, hε₀, hmain⟩ :=
    h.nonempty_singularHomology_sublevelPair_iso_negativeDiscBundle hn hfs hc hac hcb hcompact
      hcrit hdim g
  have hε : 0 < ε₀ / 2 := half_pos hε₀
  obtain ⟨hsrc, hband⟩ := hmain (ε₀ / 2) ⟨hε, half_lt_self hε₀⟩
  obtain ⟨e₁⟩ := hband (ModuleCat.of K K) m
  -- `(D_ε, S_ε)` has the homology of this attachment, and the Thom class computes it.
  obtain ⟨e₂⟩ :=
    h.toIsCriticalSubmanifold.nonempty_singularHomology_negativeDiscSpherePair_iso_union hn
      g.toRiemannianMetric hfs.continuous hdim hV hε
      (h.isCompact_negativeDiscBundle hn hfs hdim g (ε₀ / 2))
      (Θ.contMDiffOn.continuousOn.mono hsrc) (Θ.toPartialEquiv.injOn.mono hsrc)
      (fun x hx ↦ hΘf x (hsrc hx)) (ModuleCat.of K K) m
  obtain ⟨e₃⟩ :=
    h.toIsCriticalSubmanifold.nonempty_singularHomology_negativeDiscSpherePair_iso_of_isThomClass
      hn g.toRiemannianMetric hdim hV hε u hu hm
  exact ⟨e₁ ≪≫ e₂.symm ≪≫ e₃⟩

include h hfs hc hac hcb hcompact hcrit in
/-- **The homology across the level of a Morse–Bott submanifold with an oriented negative normal
bundle.** Under the hypotheses of `nonempty_singularHomology_sublevelPair_iso_of_isThomClass`,
suppose that the negative normal bundle `ν⁻` of rank `r` is oriented. Then for every commutative
ring `K`, for instance `ℤ`, `Hᵣ₊ₚ({f ≤ b}, {f ≤ a}; K) ≅ Hₚ(S; K)` in every degree `p`. -/
theorem nonempty_singularHomology_sublevelPair_iso_of_orientation
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
  exact h.nonempty_singularHomology_sublevelPair_iso_of_isThomClass hn hfs hc hac hcb hcompact hcrit
    hdim g hV u hu hm

end IsNondegenerateCriticalSubmanifold

end TauCeti.SmoothEmbedding
