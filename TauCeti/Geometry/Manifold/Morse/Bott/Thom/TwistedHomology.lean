/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Limits.Shapes.Biproduct.Basic
public import TauCeti.Geometry.Manifold.Morse.Bott.Thom.Pair
public import TauCeti.Topology.VectorBundle.Thom.Orientation.Cover.Descent

/-!
# The homology across a Morse–Bott level with orientation-twisted coefficients

Let `i j : S j → M` be finitely many disjoint compact nondegenerate critical submanifolds of a
smooth function `f` on the level `f = c`, with negative normal bundles `ν⁻ j` of ranks `r j`, the
Morse indices of the pieces, and let `a < c < b` be such that the band `f⁻¹[a, b]` is compact and
all its critical points lie on the pieces. Crossing the level attaches the negative disc bundles of
the pieces, so the relative homology across the level is the direct sum of the homologies of the
Thom pairs `(ν⁻ j, (ν⁻ j)₀)`
(`TauCeti.SmoothEmbedding.nonempty_singularHomology_sublevelPair_iso_sigma_thomPair`). This file
applies the Thom isomorphism with orientation-twisted coefficients
(`nonempty_singularHomology_thomPair_iso_twistedHomology_signLocalSystem`, in the namespace
`TauCeti.VectorBundleOrientationCover`) to every summand. For every commutative ring `K`, `ℤ`
included, this gives Bott's description of the homology across the level with no orientation of the
negative normal bundles:

`Hₙ({f ≤ b}, {f ≤ a}; K) ≅ ⨁_{r j ≤ n} H_{n - r j}(S j; o(ν⁻ j) ⊗ K)`,

where `o(ν⁻ j)` is the orientation local system of `ν⁻ j`
(`TauCeti.VectorBundleOrientationCover.signLocalSystem`). A piece of index `r j > n` contributes
nothing in degree `n`, because the homology of a Thom pair vanishes below the rank
(`TauCeti.isZero_singularHomology_thomPair`). An orientation of `ν⁻ j` trivializes `o(ν⁻ j)`
(`TauCeti.VectorBundleOrientation.signLocalSystemIso`); without one the twist matters. For a
critical circle whose negative normal bundle is a Möbius line, `H₀(S¹; o(ν⁻)) ≅ ℤ/2` with integral
coefficients and `H₀(S¹; o(ν⁻) ⊗ ℚ) = 0`, so in degree `r j` the circle contributes `ℤ/2` over `ℤ`
and nothing over `ℚ`, where constant coefficients would give `ℤ` and `ℚ`.

This is the identification of the first page of the critical-band spectral sequence of a
Morse–Bott function with the twisted homology of its critical submanifolds
(`nonempty_filteredSpaceSpectralSequence_page_two_X_iso_sigma_twistedHomology`, in the namespace
`TauCeti.IsMorseBottFamily`, in `TauCeti.Geometry.Manifold.Morse.Bott.SpectralSequence`).

The statements hold in every universe `u` containing the manifolds, their model spaces and the
ring. The twisted Thom isomorphism needs the base, the model fibre of `ν⁻ j` and the ring in one
universe, so the negative normal bundle is given its model fibre `κ j → ℝ` from local frames indexed
by a finite type `κ j` in that universe, and its rank is `r j = |κ j|`. Frames indexed by
`Fin (r j)`, which exist when `r j` is the index
(`IsNondegenerateCriticalSubmanifold.hasLocalSubbundleFrames_negativeNormalSpace`, in the namespace
`TauCeti.SmoothEmbedding`), give frames indexed by `ULift (Fin (r j))`
(`TauCeti.HasLocalSubbundleFrames.of_equiv`). The Thom pairs of the attachment theorem carry the
model fibres `Fin (r j) → ℝ`; relabelling the model fibre of the same subspaces
(`TauCeti.subbundleTotalSpaceModelHomeomorph`) identifies them with the Thom pairs used here.

## Main results

* `TauCeti.SmoothEmbedding.nonempty_singularHomology_sublevelPair_iso_sigma_twistedHomology`: at a
  compact band whose critical points lie on finitely many compact Morse–Bott submanifolds on one
  level, the relative homology across the level is the direct sum of the twisted homologies of the
  submanifolds of index at most `n`, shifted by their indices.
* `TauCeti.IsMorseBottFamily.nonempty_singularHomology_sublevelPair_iso_sigma_twistedHomology`: the
  same for the pieces on a critical level of a Morse–Bott function inside a compact band.

## References

* R. Bott, *Nondegenerate critical manifolds*, Annals of Mathematics 60 (1954), 248–261.
* R. L. Cohen, K. Iga and P. Norbury, *Topics in Morse theory: lecture notes*, 2006,
  Theorem 15.4.
* J. W. Milnor, J. D. Stasheff, *Characteristic Classes*, Annals of Mathematics Studies 76,
  Princeton (1974), §10 and §12.
-/

public section

noncomputable section

open Bundle CategoryTheory Function Limits Module Set
open TauCeti.LocalCoefficientSystem TauCeti.VectorBundleOrientationCover
open scoped ContDiff Manifold

namespace TauCeti

universe u

/-- The Thom pairs of a family `V` of subspaces of the fibres of `E` for two model-fibre parameters
`F₁` and `F₂`, both with the topology of a subspace of the total space of `E`, are isomorphic by the
identity on vectors (`subbundleTotalSpaceModelHomeomorph`). -/
private def subbundleThomPairModelIso {𝕜 : Type*} {B : Type u} [Semiring 𝕜] (F : Type*)
    {E : B → Type u} [∀ x, AddCommMonoid (E x)] [∀ x, Module 𝕜 (E x)]
    [TopologicalSpace (TotalSpace F E)] (F₁ F₂ : Type*) (V : Π x, Submodule 𝕜 (E x)) :
    letI := subbundleTopology F (F' := F₁) V
    letI := subbundleTopology F (F' := F₂) V
    thomPair F₁ (fun x ↦ V x) ≅ thomPair F₂ (fun x ↦ V x) :=
  letI := subbundleTopology F (F' := F₁) V
  letI := subbundleTopology F (F' := F₂) V
  TopPair.ofSubsetIso (subbundleTotalSpaceModelHomeomorph F F₁ F₂ V) fun _ ↦ by simp

/-- **The Thom pairs of finitely many bundles, with orientation-twisted coefficients.** For
finitely many vector bundles `V j` over bases `S j`, with model fibres `κ j → ℝ` for finite
types `κ j`, so of ranks `|κ j|`, and a commutative ring `K`, the coproduct of the homologies
`Hₙ(V j, (V j)₀; K)` of the Thom pairs is the coproduct, over the bundles of rank `|κ j| ≤ n`, of
the homologies `H_{n - |κ j|}(S j; o(V j) ⊗ K)` with coefficients in the orientation local
systems. -/
private theorem nonempty_sigma_singularHomology_thomPair_iso_sigma_twistedHomology
    {ι : Type*} [Finite ι] {S : ι → Type u} [∀ j, TopologicalSpace (S j)]
    {κ : ι → Type u} [∀ j, Fintype (κ j)] {V : ∀ j, S j → Type u}
    [∀ j, TopologicalSpace (TotalSpace (κ j → ℝ) (V j))] [∀ j s, AddCommMonoid (V j s)]
    [∀ j s, Module ℝ (V j s)] [∀ j s, TopologicalSpace (V j s)]
    [∀ j, FiberBundle (κ j → ℝ) (V j)] [∀ j, VectorBundle ℝ (κ j → ℝ) (V j)]
    (K : Type u) [CommRing K] (n : ℕ) :
    Nonempty ((∐ fun j ↦ (thomPair (κ j → ℝ) (V j)).singularHomology (ModuleCat.of K K) n) ≅
      ∐ fun j : {j // Fintype.card (κ j) ≤ n} ↦ twistedHomology (signLocalSystem (κ j → ℝ) (V j) K
        ((Fintype.card_fin _).trans (finrank_fintype_fun_eq_card ℝ).symm))
        (n - Fintype.card (κ j))) := by
  let W (j : ι) : ModuleCat K :=
    (thomPair (κ j → ℝ) (V j)).singularHomology (ModuleCat.of K K) n
  -- Below the rank the homology of a Thom pair vanishes, so only the bundles of rank `|κ j| ≤ n`
  -- contribute.
  have hW (j : ι) (hj : ¬Fintype.card (κ j) ≤ n) : IsZero (W j) :=
    isZero_singularHomology_thomPair _ (by rw [finrank_fintype_fun_eq_card]; omega)
  -- From rank `|κ j|` on, the twisted Thom isomorphism shifts the twisted homology of the base up
  -- by the rank.
  have T (j : {j // Fintype.card (κ j) ≤ n}) : W j ≅ twistedHomology (signLocalSystem (κ j → ℝ)
      (V j) K ((Fintype.card_fin _).trans (finrank_fintype_fun_eq_card ℝ).symm))
      (n - Fintype.card (κ j)) :=
    eqToIso (by rw [finrank_fintype_fun_eq_card, Nat.sub_add_cancel j.property]) ≪≫
      (nonempty_singularHomology_thomPair_iso_twistedHomology_signLocalSystem (F := κ j → ℝ)
        (E := V j) ((Fintype.card_fin _).trans (finrank_fintype_fun_eq_card ℝ).symm) K
        (n - Fintype.card (κ j))).some
  exact ⟨(biproduct.isoCoproduct W).symm ≪≫
    (biproductSubtypeIsoOfIsZero W (fun j ↦ Fintype.card (κ j) ≤ n) hW).symm ≪≫
    biproduct.mapIso T ≪≫ biproduct.isoCoproduct _⟩

variable {E M : Type u} {H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] {ι : Type*} {E' H' P : ι → Type*}
  {S : ι → Type u} [∀ j, NormedAddCommGroup (E' j)] [∀ j, NormedSpace ℝ (E' j)]
  [∀ j, FiniteDimensional ℝ (E' j)] [∀ j, TopologicalSpace (H' j)]
  {J : ∀ j, ModelWithCorners ℝ (E' j) (H' j)} [∀ j, TopologicalSpace (S j)]
  [∀ j, ChartedSpace (H' j) (S j)] [∀ j, IsManifold (J j) ∞ (S j)]
  [∀ j, NormedAddCommGroup (P j)] [∀ j, NormedSpace ℝ (P j)] [∀ j, FiniteDimensional ℝ (P j)]
  {f : M → ℝ} {i : ∀ j, SmoothEmbedding (J j) I ∞ (S j) M} (hn : (∞ : ℕ∞ω) ≠ 0)

/-- **The relative homology across a level of finitely many Morse–Bott submanifolds, with
orientation-twisted coefficients.** Let `i j : S j → M`, for `j` in a finite index type, be
nondegenerate critical submanifolds of a smooth function `f` on a Hausdorff, second-countable,
finite-dimensional, boundaryless manifold, each modelled on its own boundaryless model, with `S j`
compact and nonempty, pairwise disjoint images and `f = c` along each of them. Let `g j` be a
smooth fibre metric on the normal bundle of `i j`, and suppose that the negative normal spaces
relative to `g j` have continuous local frames indexed by a finite type `κ j`, so that they form the
negative normal bundle `ν⁻ j` of rank `|κ j|`. Let `a < c < b` be such that the band `f⁻¹[a, b]` is
compact and all its critical points lie on the submanifolds, and let `K` be a commutative ring, for
instance `ℤ`. The manifolds, the frame index types and the ring lie in one universe.

Then `Hₙ({f ≤ b}, {f ≤ a}; K)` is isomorphic to the coproduct, over the submanifolds of index
`|κ j| ≤ n`, of the homologies `H_{n - |κ j|}(S j; o(ν⁻ j) ⊗ K)` with coefficients in the
orientation local systems `o(ν⁻ j)`. No orientation of the bundles `ν⁻ j` is assumed. -/
theorem SmoothEmbedding.nonempty_singularHomology_sublevelPair_iso_sigma_twistedHomology
    [T2Space M] [SecondCountableTopology M] [Finite ι] [∀ j, (J j).Boundaryless]
    [∀ j, CompactSpace (S j)] [∀ j, Nonempty (S j)]
    (h : ∀ j, (i j).IsNondegenerateCriticalSubmanifold f) (hfs : ContMDiff I 𝓘(ℝ) ∞ f)
    {a b c : ℝ} (hc : ∀ j s, f (i j s) = c) (hd : Pairwise (Disjoint on fun j ↦ range (i j)))
    (hac : a < c) (hcb : c < b) (hcompact : IsCompact (f ⁻¹' Icc a b))
    (hcrit : criticalPoints I f ∩ f ⁻¹' Icc a b ⊆ ⋃ j, range (i j))
    (hdim : ∀ j, finrank ℝ (P j) = finrank ℝ E - finrank ℝ (E' j))
    (g : letI : ∀ j, FiberBundle (P j) fun s ↦ (i j).isImmersion.NormalSpace s hn :=
        fun j ↦ (i j).normalSpaceFiberBundle hn (hdim j)
      letI : ∀ j, VectorBundle ℝ (P j) fun s ↦ (i j).isImmersion.NormalSpace s hn :=
        fun j ↦ (i j).normalSpaceVectorBundle hn (hdim j)
      ∀ j, ContMDiffRiemannianMetric (J j) ∞ (P j) fun s ↦ (i j).isImmersion.NormalSpace s hn)
    {κ : ι → Type u} [∀ j, Fintype (κ j)]
    (hV : letI : ∀ j, FiberBundle (P j) fun s ↦ (i j).isImmersion.NormalSpace s hn :=
        fun j ↦ (i j).normalSpaceFiberBundle hn (hdim j)
      letI : ∀ j, VectorBundle ℝ (P j) fun s ↦ (i j).isImmersion.NormalSpace s hn :=
        fun j ↦ (i j).normalSpaceVectorBundle hn (hdim j)
      ∀ j, HasLocalSubbundleFrames (P j) (κ j)
        ((h j).negativeNormalSpace hn (g j).toRiemannianMetric))
    (K : Type u) [CommRing K] (n : ℕ) :
    letI : ∀ j, FiberBundle (P j) fun s ↦ (i j).isImmersion.NormalSpace s hn :=
      fun j ↦ (i j).normalSpaceFiberBundle hn (hdim j)
    letI : ∀ j, VectorBundle ℝ (P j) fun s ↦ (i j).isImmersion.NormalSpace s hn :=
      fun j ↦ (i j).normalSpaceVectorBundle hn (hdim j)
    letI : ∀ j, TopologicalSpace (TotalSpace (κ j → ℝ)
        fun s ↦ (h j).negativeNormalSpace hn (g j).toRiemannianMetric s) :=
      fun j ↦ subbundleTopology (P j) ((h j).negativeNormalSpace hn (g j).toRiemannianMetric)
    letI : ∀ j, FiberBundle (κ j → ℝ)
        fun s ↦ (h j).negativeNormalSpace hn (g j).toRiemannianMetric s :=
      fun j ↦ (hV j).fiberBundle
    haveI : ∀ j, VectorBundle ℝ (κ j → ℝ)
        fun s ↦ (h j).negativeNormalSpace hn (g j).toRiemannianMetric s :=
      fun j ↦ (hV j).vectorBundle
    Nonempty ((sublevelPair f (hac.trans hcb).le).singularHomology (ModuleCat.of K K) n ≅
      ∐ fun j : {j // Fintype.card (κ j) ≤ n} ↦ twistedHomology (signLocalSystem (κ j → ℝ)
        (fun s ↦ (h j).negativeNormalSpace hn (g j).toRiemannianMetric s) K
        ((Fintype.card_fin _).trans (finrank_fintype_fun_eq_card ℝ).symm))
        (n - Fintype.card (κ j))) := by
  let _ : ∀ j, FiberBundle (P j) fun s ↦ (i j).isImmersion.NormalSpace s hn :=
    fun j ↦ (i j).normalSpaceFiberBundle hn (hdim j)
  let _ : ∀ j, VectorBundle ℝ (P j) fun s ↦ (i j).isImmersion.NormalSpace s hn :=
    fun j ↦ (i j).normalSpaceVectorBundle hn (hdim j)
  set V : ∀ j, S j → Type u := fun j s ↦ (h j).negativeNormalSpace hn (g j).toRiemannianMetric s
  let _ : ∀ j, TopologicalSpace (TotalSpace (κ j → ℝ) (V j)) :=
    fun j ↦ subbundleTopology (P j) ((h j).negativeNormalSpace hn (g j).toRiemannianMetric)
  let _ : ∀ j, TopologicalSpace (TotalSpace (Fin (Fintype.card (κ j)) → ℝ) (V j)) :=
    fun j ↦ subbundleTopology (P j) ((h j).negativeNormalSpace hn (g j).toRiemannianMetric)
  let _ : ∀ j, FiberBundle (κ j → ℝ) (V j) := fun j ↦ (hV j).fiberBundle
  have (j : ι) : VectorBundle ℝ (κ j → ℝ) (V j) := (hV j).vectorBundle
  -- The band has the homology of the direct sum of the Thom pairs of the submanifolds, whose
  -- ranks are the indices. Those pairs carry the model fibres `Fin |κ j| → ℝ`, which differ from
  -- `κ j → ℝ` only as labels of the same subspaces.
  obtain ⟨e⟩ := nonempty_singularHomology_sublevelPair_iso_sigma_thomPair hn h hfs hc hd hac hcb
    hcompact hcrit hdim g (fun j ↦ (h j).manifoldMorseIndex_eq_of_hasLocalSubbundleFrames hn _
      ((hV j).of_equiv (Fintype.equivFin (κ j))))
    (ModuleCat.of K K) n
  let R (j : ι) : thomPair (Fin (Fintype.card (κ j)) → ℝ) (V j) ≅ thomPair (κ j → ℝ) (V j) :=
    subbundleThomPairModelIso (P j) _ _ ((h j).negativeNormalSpace hn (g j).toRiemannianMetric)
  exact ⟨e ≪≫ Sigma.mapIso (fun j ↦ TopPair.singularHomologyMapIso _ (R j) n) ≪≫
    (nonempty_sigma_singularHomology_thomPair_iso_sigma_twistedHomology K n).some⟩

/-- **The relative homology across a critical level of a Morse–Bott function, with
orientation-twisted coefficients.** Let the family `i j : S j → M` exhibit `f` as a Morse–Bott
function (`TauCeti.IsMorseBottFamily`) on a Hausdorff second-countable boundaryless manifold, not
necessarily compact, with pieces modelled on boundaryless models, and let `g j` be a smooth fibre
metric on the normal bundle of `i j`. Suppose that the negative normal spaces relative to `g j` have
continuous local frames indexed by a finite type `κ j`, so that they form the negative normal bundle
`ν⁻ j` of rank `|κ j|`, the index of the piece. Let `a < c < b` be such that the band `f⁻¹[a, b]` is
compact and `c` is its only critical value, and let `K` be a commutative ring, for instance `ℤ`. The
manifolds, the frame index types and the ring lie in one universe.

Then `Hₙ({f ≤ b}, {f ≤ a}; K)` is isomorphic to the coproduct, over the pieces on the level `f = c`
of index `|κ j| ≤ n`, of the homologies `H_{n - |κ j|}(S j; o(ν⁻ j) ⊗ K)` with coefficients in the
orientation local systems `o(ν⁻ j)`. No orientation of the bundles `ν⁻ j` is assumed. If `c` is not
a critical value there are no such pieces, and the coproduct is zero. -/
theorem IsMorseBottFamily.nonempty_singularHomology_sublevelPair_iso_sigma_twistedHomology
    [T2Space M] [SecondCountableTopology M] [∀ j, (J j).Boundaryless]
    (h : IsMorseBottFamily i f) {a b c : ℝ} (hac : a < c) (hcb : c < b)
    (hcompact : IsCompact (f ⁻¹' Icc a b))
    (hcrit : ∀ x ∈ criticalPoints I f, f x ∈ Icc a b → f x = c)
    (hdim : ∀ j, finrank ℝ (P j) = finrank ℝ E - finrank ℝ (E' j))
    (g : letI : ∀ j, FiberBundle (P j) fun s ↦ (i j).isImmersion.NormalSpace s hn :=
        fun j ↦ (i j).normalSpaceFiberBundle hn (hdim j)
      letI : ∀ j, VectorBundle ℝ (P j) fun s ↦ (i j).isImmersion.NormalSpace s hn :=
        fun j ↦ (i j).normalSpaceVectorBundle hn (hdim j)
      ∀ j, ContMDiffRiemannianMetric (J j) ∞ (P j) fun s ↦ (i j).isImmersion.NormalSpace s hn)
    {κ : ι → Type u} [∀ j, Fintype (κ j)]
    (hV : letI : ∀ j, FiberBundle (P j) fun s ↦ (i j).isImmersion.NormalSpace s hn :=
        fun j ↦ (i j).normalSpaceFiberBundle hn (hdim j)
      letI : ∀ j, VectorBundle ℝ (P j) fun s ↦ (i j).isImmersion.NormalSpace s hn :=
        fun j ↦ (i j).normalSpaceVectorBundle hn (hdim j)
      ∀ j, HasLocalSubbundleFrames (P j) (κ j)
        ((h.isNondegenerateCriticalSubmanifold j).negativeNormalSpace hn (g j).toRiemannianMetric))
    (K : Type u) [CommRing K] (n : ℕ) :
    letI : ∀ j, FiberBundle (P j) fun s ↦ (i j).isImmersion.NormalSpace s hn :=
      fun j ↦ (i j).normalSpaceFiberBundle hn (hdim j)
    letI : ∀ j, VectorBundle ℝ (P j) fun s ↦ (i j).isImmersion.NormalSpace s hn :=
      fun j ↦ (i j).normalSpaceVectorBundle hn (hdim j)
    letI : ∀ j, TopologicalSpace (TotalSpace (κ j → ℝ)
        fun s ↦ (h.isNondegenerateCriticalSubmanifold j).negativeNormalSpace hn
          (g j).toRiemannianMetric s) :=
      fun j ↦ subbundleTopology (P j)
        ((h.isNondegenerateCriticalSubmanifold j).negativeNormalSpace hn (g j).toRiemannianMetric)
    letI : ∀ j, FiberBundle (κ j → ℝ) fun s ↦
        (h.isNondegenerateCriticalSubmanifold j).negativeNormalSpace hn
          (g j).toRiemannianMetric s :=
      fun j ↦ (hV j).fiberBundle
    haveI : ∀ j, VectorBundle ℝ (κ j → ℝ) fun s ↦
        (h.isNondegenerateCriticalSubmanifold j).negativeNormalSpace hn
          (g j).toRiemannianMetric s :=
      fun j ↦ (hV j).vectorBundle
    -- The pieces on the level `c` are finitely many, so the coproduct exists.
    haveI : Finite {j // (∀ s, f (i j s) = c) ∧ Fintype.card (κ j) ≤ n} :=
      h.finite_subtype_of_forall_apply_eq hcompact ⟨hac.le, hcb.le⟩ fun _ ↦ And.left
    Nonempty ((sublevelPair f (hac.trans hcb).le).singularHomology (ModuleCat.of K K) n ≅
      ∐ fun j : {j // (∀ s, f (i j s) = c) ∧ Fintype.card (κ j) ≤ n} ↦
        twistedHomology (signLocalSystem (κ j → ℝ)
          (fun s ↦ (h.isNondegenerateCriticalSubmanifold j).negativeNormalSpace hn
            (g j).toRiemannianMetric s) K
          ((Fintype.card_fin _).trans (finrank_fintype_fun_eq_card ℝ).symm))
          (n - Fintype.card (κ j))) := by
  let _ : ∀ j, FiberBundle (P j) fun s ↦ (i j).isImmersion.NormalSpace s hn :=
    fun j ↦ (i j).normalSpaceFiberBundle hn (hdim j)
  let _ : ∀ j, VectorBundle ℝ (P j) fun s ↦ (i j).isImmersion.NormalSpace s hn :=
    fun j ↦ (i j).normalSpaceVectorBundle hn (hdim j)
  set V : ∀ j, S j → Type u := fun j s ↦
    (h.isNondegenerateCriticalSubmanifold j).negativeNormalSpace hn (g j).toRiemannianMetric s
  let _ : ∀ j, TopologicalSpace (TotalSpace (κ j → ℝ) (V j)) :=
    fun j ↦ subbundleTopology (P j)
      ((h.isNondegenerateCriticalSubmanifold j).negativeNormalSpace hn (g j).toRiemannianMetric)
  let _ : ∀ j, TopologicalSpace (TotalSpace (Fin (Fintype.card (κ j)) → ℝ) (V j)) :=
    fun j ↦ subbundleTopology (P j)
      ((h.isNondegenerateCriticalSubmanifold j).negativeNormalSpace hn (g j).toRiemannianMetric)
  let _ : ∀ j, FiberBundle (κ j → ℝ) (V j) := fun j ↦ (hV j).fiberBundle
  have (j : ι) : VectorBundle ℝ (κ j → ℝ) (V j) := (hV j).vectorBundle
  -- The pieces on the level `c` lie in the compact band, so they are finitely many.
  have := h.finite_subtype_of_forall_apply_eq hcompact ⟨hac.le, hcb.le⟩ fun _ ↦ id
  have : Finite {j // (∀ s, f (i j s) = c) ∧ Fintype.card (κ j) ≤ n} :=
    h.finite_subtype_of_forall_apply_eq hcompact ⟨hac.le, hcb.le⟩ fun _ ↦ And.left
  -- The band has the homology of the direct sum of the Thom pairs of the pieces on the level `c`,
  -- whose ranks are the indices. Those pairs carry the model fibres `Fin |κ j| → ℝ`, which differ
  -- from `κ j → ℝ` only as labels of the same subspaces.
  obtain ⟨e⟩ := h.nonempty_singularHomology_sublevelPair_iso_sigma_thomPair hn hac hcb hcompact
    hcrit hdim g
    (fun j ↦ (h.isNondegenerateCriticalSubmanifold j)
      |>.manifoldMorseIndex_eq_of_hasLocalSubbundleFrames hn _
        ((hV j).of_equiv (Fintype.equivFin (κ j))))
    (ModuleCat.of K K) n
  let R (j : ι) : thomPair (Fin (Fintype.card (κ j)) → ℝ) (V j) ≅ thomPair (κ j → ℝ) (V j) :=
    subbundleThomPairModelIso (P j) _ _
      ((h.isNondegenerateCriticalSubmanifold j).negativeNormalSpace hn (g j).toRiemannianMetric)
  -- Reindex the pieces of index at most `n` among those on the level `c`.
  exact ⟨e ≪≫ Sigma.mapIso (fun j ↦ TopPair.singularHomologyMapIso _ (R j) n) ≪≫
    (nonempty_sigma_singularHomology_thomPair_iso_sigma_twistedHomology
      (V := fun j : {j // ∀ s, f (i j s) = c} ↦ V j) K n).some ≪≫
    Sigma.reindex (C := ModuleCat.{u} K)
      (Equiv.subtypeSubtypeEquivSubtypeInter _ fun j ↦ Fintype.card (κ j) ≤ n)
      fun j ↦ twistedHomology (signLocalSystem (κ j → ℝ) (V j) K
        ((Fintype.card_fin _).trans (finrank_fintype_fun_eq_card ℝ).symm))
        (n - Fintype.card (κ j))⟩

end TauCeti
