/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Morse.Bott.Thom.Pair

/-!
# The homology across a Morse–Bott level is that of the negative disc-sphere pair

Let `i : S → M` be a critical submanifold of a function `f` on a boundaryless manifold, let `g` be
a fibre metric on its normal bundle, and let `(D_ε, S_ε)` be the negative disc-sphere pair
(`TauCeti.SmoothEmbedding.IsCriticalSubmanifold.negativeDiscSpherePair`).

* Let `f` be continuous on a Hausdorff manifold, suppose that the negative normal spaces have
  continuous local frames, and let `ε > 0` be such that `D_ε` is compact. If a map `Θ` is
  continuous and injective on `D_ε` and puts `f` there in the Morse–Bott normal form
  `f (Θ v) = c + ½ Hessₛ (v, v)`, then `(D_ε, S_ε)` has the homology of the lower sublevel with
  `Θ(D_ε)` attached, `Hₖ(D_ε, S_ε) ≅ Hₖ({f ≤ c - ε} ∪ Θ(D_ε), {f ≤ c - ε})`
  (`IsCriticalSubmanifold.nonempty_singularHomology_negativeDiscSpherePair_iso_union`).
* If `i` is a nondegenerate critical submanifold of a smooth `f` on the level `f = c`, `a < c < b`,
  the band `f⁻¹[a, b]` is compact and all its critical points lie on `i`, then for all small
  `ε > 0` the relative homology across the level is that of the negative disc-sphere pair,
  `Hₖ({f ≤ b}, {f ≤ a}) ≅ Hₖ(D_ε, S_ε)`, with coefficients in any abelian category with
  coproducts (`nonempty_singularHomology_sublevelPair_iso_negativeDiscSpherePair`, in the namespace
  `TauCeti.SmoothEmbedding.IsNondegenerateCriticalSubmanifold`).
-/

public section

noncomputable section

open Bundle CategoryTheory Limits Set Topology
open scoped ContDiff Manifold

universe u v w

namespace TauCeti.SmoothEmbedding

/-! ### The attachment across the level -/

section Attachment

variable {E M S : Type u} {H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [T2Space M] {E' H' P : Type*}
  [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E'] [TopologicalSpace H']
  {J : ModelWithCorners ℝ E' H'} [TopologicalSpace S] [ChartedSpace H' S]
  [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P] {f : M → ℝ}

namespace IsCriticalSubmanifold

variable [IsManifold I 2 M] [IsManifold J 1 S] {n : ℕ∞ω} {i : SmoothEmbedding J I n S M}
  (hn : n ≠ 0) {h : i.IsCriticalSubmanifold f} (g : RiemannianMetric fun s ↦ i.NormalSpace s hn)
  {Θ : TotalSpace P (fun s ↦ i.NormalSpace s hn) → M} {c ε : ℝ}

/-- **The negative disc-sphere pair has the homology of its attachment across the level.** Let `i`
be a critical submanifold of a continuous function `f` on a Hausdorff manifold, let `g` be a fibre
metric on its normal bundle, and suppose that the negative normal spaces have continuous local
frames of size `r` and that the negative disc bundle `D_ε`, `ε > 0`, is compact. Let `Θ` be
continuous and injective on `D_ε` and put `f` there in the Morse–Bott normal form
`f (Θ v) = c + ½ Hessₛ (v, v)`. Then `(D_ε, S_ε)` has the relative homology of the lower sublevel
`L = {f ≤ c - ε}` with `Θ(D_ε)` attached: `Hₖ(D_ε, S_ε) ≅ Hₖ(L ∪ Θ(D_ε), L)`, with coefficients in
any abelian category with coproducts, in every degree. -/
theorem nonempty_singularHomology_negativeDiscSpherePair_iso_union (hf : Continuous f)
    (hdim : Module.finrank ℝ P = Module.finrank ℝ E - Module.finrank ℝ E') {r : ℕ}
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

namespace IsNondegenerateCriticalSubmanifold

variable [IsManifold I ∞ M] [SecondCountableTopology M] [J.Boundaryless] [IsManifold J ∞ S]
  [Nonempty S] {i : SmoothEmbedding J I ∞ S M} (hn : (∞ : ℕ∞ω) ≠ 0)

/-- **The relative homology across a Morse–Bott level is that of the negative disc-sphere pair.**
Let `i : S → M` be a nondegenerate critical submanifold of a smooth function `f` on a Hausdorff,
second-countable, finite-dimensional, boundaryless manifold, with `S` nonempty and `f = c` along
`i`, and let `g` be a smooth fibre metric on its normal bundle. Let `a < c < b` be such that the
band `f⁻¹[a, b]` is compact and all its critical points lie on `i`, and suppose that the negative
normal spaces relative to `g` have continuous local frames of size `r`. Then there is an `ε₀ > 0`
such that for every `0 < ε < ε₀` the relative homology `Hₖ({f ≤ b}, {f ≤ a})` is isomorphic to
the homology `Hₖ(D_ε, S_ε)` of the negative disc-sphere pair, with coefficients in any abelian
category with coproducts, in every degree. -/
theorem nonempty_singularHomology_sublevelPair_iso_negativeDiscSpherePair
    (h : i.IsNondegenerateCriticalSubmanifold f) (hfs : ContMDiff I 𝓘(ℝ) ∞ f) {a b c : ℝ}
    (hc : ∀ s, f (i s) = c) (hac : a < c) (hcb : c < b) (hcompact : IsCompact (f ⁻¹' Icc a b))
    (hcrit : criticalPoints I f ∩ f ⁻¹' Icc a b ⊆ range i)
    (hdim : Module.finrank ℝ P = Module.finrank ℝ E - Module.finrank ℝ E')
    (g : letI := i.normalSpaceFiberBundle hn hdim
      letI := i.normalSpaceVectorBundle hn hdim
      ContMDiffRiemannianMetric J ∞ P fun s ↦ i.NormalSpace s hn) {r : ℕ}
    (hV : letI := i.normalSpaceFiberBundle hn hdim
      letI := i.normalSpaceVectorBundle hn hdim
      HasLocalSubbundleFrames P (Fin r) (h.negativeNormalSpace hn g.toRiemannianMetric)) :
    letI := i.normalSpaceFiberBundle hn hdim
    letI := i.normalSpaceVectorBundle hn hdim
    ∃ ε₀ > 0, ∀ ε ∈ Ioo 0 ε₀, ∀ {C : Type v} [Category.{w} C] [Abelian C] [HasCoproducts.{u} C]
      (R : C) (k : ℕ),
      Nonempty ((sublevelPair f (hac.trans hcb).le).singularHomology R k ≅
        (h.negativeDiscSpherePair hn P g.toRiemannianMetric ε).singularHomology R k) := by
  let := i.normalSpaceFiberBundle hn hdim
  let := i.normalSpaceVectorBundle hn hdim
  have : CompactSpace S := h.toIsCriticalSubmanifold.compactSpace_of_isCompact_preimage_Icc
    (hfs.of_le (by simp)) hc hac.le hcb.le hcompact hcrit
  have : T2Space S := i.isEmbedding.t2Space
  -- Crossing the level attaches `Θ(D_ε)` to `L = {f ≤ c - ε}`, for a normal form `Θ`, and
  -- `(D_ε, S_ε)` has the homology of this attachment.
  obtain ⟨Θ, -, -, hΘf, ε₀, hε₀, hmain⟩ :=
    h.nonempty_singularHomology_sublevelPair_iso_negativeDiscBundle hn hfs hc hac hcb hcompact
      hcrit hdim g
  refine ⟨ε₀, hε₀, fun ε hε C _ _ _ R k ↦ ?_⟩
  obtain ⟨hsrc, hband⟩ := hmain ε hε
  obtain ⟨e₁⟩ := hband R k
  obtain ⟨e₂⟩ :=
    h.toIsCriticalSubmanifold.nonempty_singularHomology_negativeDiscSpherePair_iso_union hn
      g.toRiemannianMetric hfs.continuous hdim hV hε.1
      (h.isCompact_negativeDiscBundle hn hfs hdim g ε)
      (Θ.contMDiffOn.continuousOn.mono hsrc) (Θ.toPartialEquiv.injOn.mono hsrc)
      (fun x hx ↦ hΘf x (hsrc hx)) R k
  exact ⟨e₁ ≪≫ e₂.symm⟩

end IsNondegenerateCriticalSubmanifold

end Attachment

end TauCeti.SmoothEmbedding
