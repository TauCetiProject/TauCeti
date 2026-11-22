/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.BettiNumber
public import TauCeti.Geometry.Manifold.Morse.Bott.Thom.Pair
public import TauCeti.Geometry.Manifold.Morse.Generic.Inequalities
import Mathlib.Order.Interval.Set.Union
import TauCeti.Algebra.Category.ModuleCat.Biproducts
import TauCeti.Algebra.Category.ModuleCat.Finrank
import TauCeti.Geometry.Manifold.Morse.Bott.Adjunction
import TauCeti.Geometry.Manifold.Morse.Bott.NormalSubbundle
import TauCeti.Geometry.Manifold.SmoothEmbedding.NormalSpace.Metric
import TauCeti.Topology.VectorBundle.MayerVietoris.DirectedUnion
import TauCeti.Topology.VectorBundle.Thom.Homology

/-!
# The Morse–Bott inequalities with coefficients in `𝔽₂`

Let `f` be a Morse–Bott function on a compact boundaryless manifold `M`, exhibited by a family
`i a : S a → M` of critical submanifolds (`TauCeti.IsMorseBottFamily`), and let `r a` be the index
of the piece `S a`, the Morse index of `f` at its points. Let `K` be a field whose only unit is `1`,
that is `𝔽₂`. Write `bⱼ = dim Hⱼ(M; K)` and let

`cⱼ = ∑ₐ b_{j - r a}(S a; K)`,

the sum running over the pieces of index `r a ≤ j`: `cⱼ` is the coefficient of `tʲ` in the
Morse–Bott polynomial `∑ₐ t^{r a} P_{S a}(t)`. This file proves the **Morse–Bott inequalities**
for `b` and `c`: the weak inequalities `bⱼ ≤ cⱼ`, the strong inequalities
`bₙ - bₙ₋₁ + ⋯ ± b₀ ≤ cₙ - cₙ₋₁ + ⋯ ± c₀`, Euler's equality in degrees at least `dim M`, and the
polynomial identity `∑ⱼ cⱼ tʲ = ∑ⱼ bⱼ tʲ + (1 + t) Q(t)` with `Q` having natural number
coefficients. When no two consecutive `cⱼ` are both nonzero the inequalities force `bⱼ = cⱼ`, the
lacunary principle: the function is perfect over `𝔽₂`. For a Morse function every piece is a point
of index the Morse index, so `cⱼ` is the number of critical points of index `j`, and these are the
Morse inequalities over `𝔽₂`.

Over `𝔽₂` no orientation of the negative normal bundles is needed. Over another field the
contribution of a piece is its homology twisted by the orientation local system of its negative
normal bundle; it agrees with the untwisted one when that bundle is orientable.

The proof follows Bott. Cut the values of `f` at regular values `s 0 < ⋯ < s (N + 1)` so that each
band `f⁻¹[s j, s (j + 1)]` contains at most one critical value. The Morse–Bott inequalities are then
the inequalities of this filtration by sublevels
(`TauCeti.sum_range_neg_one_pow_mul_finrank_singularHomology_le_sum_sublevelPair_of_contMDiff` and
its companions), once the homology of each band is computed:

* crossing a critical level `c` deformation retracts the upper sublevel onto the lower one with the
  negative disc bundles `D a ε` of the pieces on that level attached
  (`TauCeti.IsMorseBottFamily.exists_sublevel_union_iUnion_negativeDiscBundle_deformation`), so the
  homology of the band is the direct sum of the homologies of the pairs `(D a ε, S a ε)`
  (`TauCeti.isIso_biproductDesc_singularHomologyMap_of_attach_negativeDiscBundles`);
* each `(D a ε, S a ε)` has the homology of the Thom pair of the negative normal bundle of `S a`
  (`SmoothEmbedding.IsCriticalSubmanifold.isIso_singularHomologyMap_negativeDiscThomPairMap`),
  a vector bundle of rank `r a`, whose homology with coefficients in `𝔽₂` is that of `S a` shifted
  by `r a` (`TauCeti.finrank_singularHomology_thomPair_of_subsingleton_units`).

So `dim Hₙ({f ≤ b}, {f ≤ a}; K) = ∑ b_{n - r a}(S a; K)` over the pieces on the only critical level
`c ∈ (a, b)` of the band, of index at most `n`
(`TauCeti.IsMorseBottFamily.finrank_singularHomology_sublevelPair_eq_sum`), and summing over the
bands counts every piece once.

The homology Thom isomorphism (`TauCeti.homologyThomIso`) needs the model fibre
`Fin r → ℝ` of the negative normal bundle in the universe of its base, so the manifolds, their
models and the coefficient field here live in `Type`.

## Main results

* `finrank_singularHomology_negativeDiscSpherePair`, in the namespace
  `TauCeti.SmoothEmbedding.IsNondegenerateCriticalSubmanifold`: for a Morse–Bott submanifold of
  index `r`, `dim Hₙ(D_ε, S_ε; 𝔽₂) = b_{n - r}(S; 𝔽₂)` if `r ≤ n`, and `0` otherwise.
* `TauCeti.IsMorseBottFamily.finrank_singularHomology_sublevelPair_eq_sum`: the dimension of the
  homology of a band with a single critical value.
* `TauCeti.IsMorseBottFamily.bettiNumber_le_sum`,
  `TauCeti.IsMorseBottFamily.sum_range_neg_one_pow_mul_bettiNumber_le_sum`,
  `TauCeti.IsMorseBottFamily.sum_range_neg_one_pow_mul_bettiNumber_eq_sum` and
  `TauCeti.IsMorseBottFamily.exists_sum_range_monomial_sum_eq_add_mul`: the weak and strong
  Morse–Bott inequalities, Euler's equality and the Morse–Bott polynomial identity over `𝔽₂`.
* `TauCeti.IsMorseBottFamily.bettiNumber_eq_sum`: the lacunary principle over `𝔽₂`, `bₙ = cₙ` when
  no two consecutive `cₙ` are both nonzero.

## References

* R. Bott, *Nondegenerate critical manifolds*, Annals of Mathematics 60 (1954), 248–261.
* R. Bott, *Lectures on Morse theory, old and new*, Bulletin of the American Mathematical
  Society 7 (1982), 331–358, Section 1.
* R. L. Cohen, K. Iga and P. Norbury, *Topics in Morse theory: lecture notes*, 2006,
  Theorems 15.4 and 15.6.
-/

public section

noncomputable section

open Bundle CategoryTheory Function Limits Module Set Topology
open Polynomial (monomial)
open scoped ContDiff Manifold Polynomial

namespace TauCeti

/-! ### The contribution of one Morse–Bott submanifold -/

namespace SmoothEmbedding.IsNondegenerateCriticalSubmanifold

variable {E : Type} {H M E' H' P : Type*} {S : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [NormedAddCommGroup E']
  [NormedSpace ℝ E'] [FiniteDimensional ℝ E'] [TopologicalSpace H'] {J : ModelWithCorners ℝ E' H'}
  [TopologicalSpace S] [ChartedSpace H' S] [IsManifold J ∞ S] [NormedAddCommGroup P]
  [NormedSpace ℝ P] [FiniteDimensional ℝ P] {f : M → ℝ} {i : SmoothEmbedding J I ∞ S M}
  (hn : (∞ : ℕ∞ω) ≠ 0)

/-- The negative normal spaces of a Morse–Bott submanifold of constant index `r`, relative to a
smooth fibre metric, have continuous local frames of size `r`. -/
private theorem hasLocalSubbundleFrames_negativeNormalSpace
    (h : i.IsNondegenerateCriticalSubmanifold f) (hfs : ContMDiff I 𝓘(ℝ) ∞ f)
    (hdim : finrank ℝ P = finrank ℝ E - finrank ℝ E')
    (g : letI := i.normalSpaceFiberBundle hn hdim
      letI := i.normalSpaceVectorBundle hn hdim
      ContMDiffRiemannianMetric J ∞ P fun s ↦ i.NormalSpace s hn) {r : ℕ}
    (hr : ∀ s, manifoldMorseIndex I f (i s) = r) :
    letI := i.normalSpaceFiberBundle hn hdim
    letI := i.normalSpaceVectorBundle hn hdim
    HasLocalSubbundleFrames P (Fin r) (h.negativeNormalSpace hn g.toRiemannianMetric) := by
  have : IsManifold I (∞ + 2) M := .of_le (n := ∞) (by simp)
  have : IsManifold J (∞ + 1) S := by simpa using (inferInstance : IsManifold J ∞ S)
  let := i.normalSpaceFiberBundle hn hdim
  let := i.normalSpaceVectorBundle hn hdim
  exact (h.hasLocalContMDiffSubbundleFrames_negativeNormalSpace hn (k := ∞) (by simp)
    (fun s ↦ hfs.contMDiffAt.of_le (by simp)) hdim g hr).hasLocalSubbundleFrames

/-- **The mod `2` homology of the negative disc bundle of a Morse–Bott submanifold.** Let `i` be a
nondegenerate critical submanifold of a smooth function `f`, with Morse index `r` at every point,
and let `g` be a smooth fibre metric on its normal bundle. Let `K` be a field whose only unit is
`1`, such as `ZMod 2`. For `ε > 0`, the negative disc bundle `D_ε` relative to `g`, taken
relative to its boundary `S_ε`, has `dim Hₙ(D_ε, S_ε; K) = b_{n - r}(S; K)` when `r ≤ n`, and `0`
when `n < r`: it has the homology of the Thom pair of the negative normal bundle, a vector bundle of
rank `r`, whose mod `2` homology is that of `S` shifted by `r`, with no orientation needed. -/
theorem finrank_singularHomology_negativeDiscSpherePair
    (h : i.IsNondegenerateCriticalSubmanifold f) (hfs : ContMDiff I 𝓘(ℝ) ∞ f)
    (hdim : finrank ℝ P = finrank ℝ E - finrank ℝ E')
    (g : letI := i.normalSpaceFiberBundle hn hdim
      letI := i.normalSpaceVectorBundle hn hdim
      ContMDiffRiemannianMetric J ∞ P fun s ↦ i.NormalSpace s hn) {r : ℕ}
    (hr : ∀ s, manifoldMorseIndex I f (i s) = r) {ε : ℝ} (hε : 0 < ε) (K : Type) [Field K]
    [Subsingleton Kˣ] (n : ℕ) :
    letI := i.normalSpaceFiberBundle hn hdim
    letI := i.normalSpaceVectorBundle hn hdim
    finrank K ((h.negativeDiscSpherePair hn P g.toRiemannianMetric ε).singularHomology
        (ModuleCat.of K K) n : ModuleCat K) =
      if r ≤ n then bettiNumber K S (n - r) else 0 := by
  let := i.normalSpaceFiberBundle hn hdim
  let := i.normalSpaceVectorBundle hn hdim
  have hV := h.hasLocalSubbundleFrames_negativeNormalSpace hn hfs hdim g hr
  let := subbundleTopology P (F' := Fin r → ℝ) (h.negativeNormalSpace hn g.toRiemannianMetric)
  let := hV.fiberBundle
  have := hV.vectorBundle
  -- The negative disc-sphere pair has the homology of the Thom pair of the negative normal bundle.
  rw [(@asIso _ _ _ _ _ (h.isIso_singularHomologyMap_negativeDiscThomPairMap hn
    g.toRiemannianMetric r hdim hV hε (ModuleCat.of K K) n)).toLinearEquiv.finrank_eq]
  split_ifs with hrn
  · exact finrank_singularHomology_thomPair_of_subsingleton_units (Fin r → ℝ) _ (n - r) n
      (by rw [Module.finrank_fin_fun]; omega)
  · have hz := isZero_singularHomology_thomPair (F := Fin r → ℝ)
      (E := fun s ↦ h.negativeNormalSpace hn g.toRiemannianMetric s) (ModuleCat.of K K)
      (n := n) (by rw [Module.finrank_fin_fun]; omega)
    have := ModuleCat.isZero_iff_subsingleton.1 hz
    exact Module.finrank_zero_of_subsingleton

end SmoothEmbedding.IsNondegenerateCriticalSubmanifold

/-! ### The homology of a band with a single critical value -/

section Level

variable {E : Type} {H : Type*} {M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {ι : Type*} {E' H' P : ι → Type*} {S : ι → Type}
  [∀ j, NormedAddCommGroup (E' j)] [∀ j, NormedSpace ℝ (E' j)] [∀ j, FiniteDimensional ℝ (E' j)]
  [∀ j, TopologicalSpace (H' j)] {J : ∀ j, ModelWithCorners ℝ (E' j) (H' j)}
  [∀ j, TopologicalSpace (S j)] [∀ j, ChartedSpace (H' j) (S j)] [∀ j, IsManifold (J j) ∞ (S j)]
  [∀ j, NormedAddCommGroup (P j)] [∀ j, NormedSpace ℝ (P j)] [∀ j, FiniteDimensional ℝ (P j)]
  {f : M → ℝ} {i : ∀ j, SmoothEmbedding (J j) I ∞ (S j) M} (hn : (∞ : ℕ∞ω) ≠ 0)

/-- **The homology of an attachment of negative disc bundles across a level.** Let `Θ j` be
Morse–Bott normal forms `f (Θ j v) = c + ½ Hessₛ (v, v)` for finitely many compact Morse–Bott
submanifolds of constant indices, defined on the negative disc bundles `D j ε`, `ε > 0`, with
pairwise disjoint images. Then the relative homology of `{f ≤ c - ε} ∪ ⋃ j, Θ j (D j ε)` relative
to `{f ≤ c - ε}` is the direct sum of the homologies of the pairs `(D j ε, S j ε)`. -/
private theorem nonempty_biproduct_iso_singularHomology_union_iUnion_image_negativeDiscBundle
    [T2Space M] [Finite ι] [∀ j, CompactSpace (S j)]
    (h : ∀ j, (i j).IsNondegenerateCriticalSubmanifold f) (hfs : ContMDiff I 𝓘(ℝ) ∞ f)
    (hdim : ∀ j, finrank ℝ (P j) = finrank ℝ E - finrank ℝ (E' j))
    (g : letI : ∀ j, FiberBundle (P j) fun s ↦ (i j).NormalSpace s hn :=
        fun j ↦ (i j).normalSpaceFiberBundle hn (hdim j)
      letI : ∀ j, VectorBundle ℝ (P j) fun s ↦ (i j).NormalSpace s hn :=
        fun j ↦ (i j).normalSpaceVectorBundle hn (hdim j)
      ∀ j, ContMDiffRiemannianMetric (J j) ∞ (P j) fun s ↦ (i j).NormalSpace s hn)
    {r : ι → ℕ} (hr : ∀ j s, manifoldMorseIndex I f (i j s) = r j)
    (Θ : letI : ∀ j, FiberBundle (P j) fun s ↦ (i j).NormalSpace s hn :=
        fun j ↦ (i j).normalSpaceFiberBundle hn (hdim j)
      letI : ∀ j, VectorBundle ℝ (P j) fun s ↦ (i j).NormalSpace s hn :=
        fun j ↦ (i j).normalSpaceVectorBundle hn (hdim j)
      ∀ j, PartialDiffeomorph ((J j).prod 𝓘(ℝ, P j)) I
        (TotalSpace (P j) fun s ↦ (i j).NormalSpace s hn) M ∞) {c ε : ℝ} (hε : 0 < ε)
    (hΘf : letI : ∀ j, FiberBundle (P j) fun s ↦ (i j).NormalSpace s hn :=
        fun j ↦ (i j).normalSpaceFiberBundle hn (hdim j)
      letI : ∀ j, VectorBundle ℝ (P j) fun s ↦ (i j).NormalSpace s hn :=
        fun j ↦ (i j).normalSpaceVectorBundle hn (hdim j)
      ∀ j, ∀ x ∈ (Θ j).source,
        f (Θ j x) = c + 2⁻¹ * (h j).normalHessian hn x.proj x.snd x.snd)
    (hD : letI : ∀ j, FiberBundle (P j) fun s ↦ (i j).NormalSpace s hn :=
        fun j ↦ (i j).normalSpaceFiberBundle hn (hdim j)
      letI : ∀ j, VectorBundle ℝ (P j) fun s ↦ (i j).NormalSpace s hn :=
        fun j ↦ (i j).normalSpaceVectorBundle hn (hdim j)
      ∀ j, (h j).negativeDiscBundle hn (P j) (g j).toRiemannianMetric ε ⊆ (Θ j).source)
    (hdisj : letI : ∀ j, FiberBundle (P j) fun s ↦ (i j).NormalSpace s hn :=
        fun j ↦ (i j).normalSpaceFiberBundle hn (hdim j)
      letI : ∀ j, VectorBundle ℝ (P j) fun s ↦ (i j).NormalSpace s hn :=
        fun j ↦ (i j).normalSpaceVectorBundle hn (hdim j)
      Pairwise (Disjoint on fun j ↦
        Θ j '' (h j).negativeDiscBundle hn (P j) (g j).toRiemannianMetric ε))
    (K : Type) [Field K] (n : ℕ) :
    letI : ∀ j, FiberBundle (P j) fun s ↦ (i j).NormalSpace s hn :=
      fun j ↦ (i j).normalSpaceFiberBundle hn (hdim j)
    letI : ∀ j, VectorBundle ℝ (P j) fun s ↦ (i j).NormalSpace s hn :=
      fun j ↦ (i j).normalSpaceVectorBundle hn (hdim j)
    Nonempty ((⨁ fun j ↦ ((h j).negativeDiscSpherePair hn (P j) (g j).toRiemannianMetric ε
        ).singularHomology (ModuleCat.of K K) n) ≅
      (TopPair.ofInclusion (X := TopCat.of M) (subset_union_left :
        {y | f y ≤ c - ε} ⊆ {y | f y ≤ c - ε} ∪
          ⋃ j, Θ j '' (h j).negativeDiscBundle hn (P j) (g j).toRiemannianMetric ε)
        ).singularHomology (ModuleCat.of K K) n) := by
  let _ : ∀ j, FiberBundle (P j) fun s ↦ (i j).NormalSpace s hn :=
    fun j ↦ (i j).normalSpaceFiberBundle hn (hdim j)
  let _ : ∀ j, VectorBundle ℝ (P j) fun s ↦ (i j).NormalSpace s hn :=
    fun j ↦ (i j).normalSpaceVectorBundle hn (hdim j)
  have (j : ι) : T2Space (S j) := (i j).isEmbedding.t2Space
  set D := fun j ↦ (h j).negativeDiscBundle hn (P j) (g j).toRiemannianMetric ε
  set X : Set M := {y | f y ≤ c - ε}
  have hXZ : X ⊆ X ∪ ⋃ j, Θ j '' D j := subset_union_left
  -- The attaching map of `D j`: the normal form `Θ j`, read in `X ∪ ⋃ j, Θ j (D j)`.
  let θ (j : ι) : C(D j, ↥(X ∪ ⋃ j, Θ j '' D j)) :=
    ⟨fun x ↦ ⟨Θ j x, Or.inr (mem_iUnion.2 ⟨j, x, x.property, rfl⟩)⟩,
      ((Θ j).contMDiffOn_toFun.continuousOn.comp_continuous continuous_subtypeVal
        fun x ↦ hD j x.property).subtype_mk _⟩
  -- A point of `D j` is sent into `{f ≤ c - ε}` exactly when it lies on the sphere `S j ε`.
  have hΘX (j : ι) (x : D j) : Θ j x ∈ X ↔ -(2⁻¹ * (h j).normalHessian hn x.val.proj x.val.snd
      x.val.snd) = ε := by
    have h₂ := ((SmoothEmbedding.IsCriticalSubmanifold.mem_negativeDiscBundle hn).1 x.property).2
    simp only [X, mem_ofPred_eq, hΘf j x (hD j x.property)]
    constructor <;> intro h₃ <;> linarith
  let φ (j : ι) : (h j).negativeDiscSpherePair hn (P j) (g j).toRiemannianMetric ε ⟶
      TopPair.ofSubset (X := TopCat.of ↥(X ∪ ⋃ j, Θ j '' D j)) (Subtype.val ⁻¹' X) :=
    TopPair.ofHom (TopCat.ofHom (θ j))
      (TopCat.ofHom ⟨fun x ↦ ⟨θ j (inclusion inter_subset_left x), (hΘX j _).2 x.property.right⟩,
        ((θ j).continuous.comp (continuous_inclusion inter_subset_left)).subtype_mk _⟩)
      (by ext; rfl)
  -- The ambient component of `φ j` is `θ j`, by construction.
  have hφ (j : ι) : ⇑(TopPair.Hom.fst (φ j)) = θ j := rfl
  have hemb (j : ι) : IsClosedEmbedding (TopPair.Hom.fst (φ j)) := by
    have : CompactSpace (D j) := isCompact_iff_compactSpace.1
      ((h j).isCompact_negativeDiscBundle hn hfs (hdim j) (g j) ε)
    rw [hφ]
    exact (θ j).continuous.isClosedEmbedding fun x y hxy ↦ Subtype.ext
      ((Θ j).toPartialEquiv.injOn (hD j x.property) (hD j y.property)
        (congrArg Subtype.val hxy))
  have hrange (j : ι) : range (TopPair.Hom.fst (φ j)) ⊆ Subtype.val ⁻¹' (Θ j '' D j) :=
    range_subset_iff.2 fun x ↦ ⟨_, x.property, rfl⟩
  have hcover : Subtype.val ⁻¹' X ∪ ⋃ j, range (TopPair.Hom.fst (φ j)) = univ := by
    refine eq_univ_of_forall fun z ↦ (z.property.imp id) fun hz ↦ ?_
    obtain ⟨j, x, hx, hxz⟩ := mem_iUnion.1 hz
    exact mem_iUnion.2 ⟨j, ⟨x, hx⟩, Subtype.ext hxz⟩
  have hiso := isIso_biproductDesc_singularHomologyMap_of_attach_negativeDiscBundles hn
    (h := fun j ↦ (h j).toIsCriticalSubmanifold) hdim
    (fun j ↦ (h j).hasLocalSubbundleFrames_negativeNormalSpace hn hfs (hdim j) (g j) (hr j)) hε
    ((isClosed_le hfs.continuous continuous_const).preimage continuous_subtypeVal) hemb
    (fun j x hx ↦ (hΘX j x).1 hx) (fun a b hab ↦ ((hdisj hab).preimage Subtype.val).mono
      (sdiff_subset.trans (hrange a)) (sdiff_subset.trans (hrange b))) hcover (ModuleCat.of K K) n
  exact ⟨@asIso _ _ _ _ _ hiso ≪≫
    TopPair.singularHomologyMapIso _ (TopPair.ofSubsetPreimageValIso (X := TopCat.of M) hXZ) n⟩

namespace IsMorseBottFamily

variable [T2Space M] [SecondCountableTopology M] [CompactSpace M] [Fintype ι]
  [∀ j, (J j).Boundaryless] (h : IsMorseBottFamily i f) {r : ι → ℕ}
  (hr : ∀ j s, manifoldMorseIndex I f (i j s) = r j) (K : Type) [Field K] [Subsingleton Kˣ]

include h hr

open scoped Classical in
/-- **The mod `2` homology of a critical band of a Morse–Bott function.** Let the family
`i j : S j → M` exhibit `f` as a Morse–Bott function on a compact boundaryless manifold, the piece
`S j` having index `r j`, and let `K` be a field whose only unit is `1`, such as `ZMod 2`. Let
`a < c < b` be such that `c` is the only critical value of `f` in `[a, b]`. Then
`dim Hₙ({f ≤ b}, {f ≤ a}; K) = ∑ b_{n - r j}(S j; K)`, the sum running over the pieces on the
level `f = c` of index at most `n`. If `c` is not a critical value, the sum is empty. -/
theorem finrank_singularHomology_sublevelPair_eq_sum {a b c : ℝ} (hac : a < c) (hcb : c < b)
    (hcrit : ∀ x ∈ criticalPoints I f, f x ∈ Icc a b → f x = c) (n : ℕ) :
    finrank K ((sublevelPair f (hac.trans hcb).le).singularHomology (ModuleCat.of K K) n :
        ModuleCat K) =
      ∑ j with (∀ s, f (i j s) = c) ∧ r j ≤ n, bettiNumber K (S j) (n - r j) := by
  have hn : (∞ : ℕ∞ω) ≠ 0 := by simp
  have (j : ι) : CompactSpace (S j) :=
    h.compactSpace_of_range_subset isCompact_univ (subset_univ _)
  -- Fix the model fibres of the normal bundles and smooth fibre metrics on them.
  have hdim (j : ι) : finrank ℝ (EuclideanSpace ℝ (Fin (finrank ℝ E - finrank ℝ (E' j)))) =
      finrank ℝ E - finrank ℝ (E' j) := finrank_euclideanSpace_fin
  let g (j : ι) := ((i j).nonempty_contMDiffRiemannianMetric_normalSpace hn (hdim j)).some
  -- Crossing the level `c` attaches the negative disc bundles of the pieces on it.
  obtain ⟨Θ, -, -, hΘf, ε₀, hε₀, hmain⟩ :=
    h.exists_sublevel_union_iUnion_negativeDiscBundle_deformation hn c hdim g
  obtain ⟨ε, hε0, hε⟩ := exists_between (lt_min hε₀ (lt_min (sub_pos.2 hac) (sub_pos.2 hcb)))
  obtain ⟨hεε₀, hεa, hεb⟩ : ε < ε₀ ∧ ε < c - a ∧ ε < b - c := by simpa only [lt_min_iff] using hε
  obtain ⟨hD, hdisj, ret, -, ⟨G⟩⟩ := hmain ε ⟨hε0, hεε₀⟩
  let _ (j : {j // ∀ s, f (i j s) = c}) := (i j).normalSpaceFiberBundle hn (hdim j)
  let _ (j : {j // ∀ s, f (i j s) = c}) := (i j).normalSpaceVectorBundle hn (hdim j)
  -- The band has the homology of `[c - ε, c + ε]`, and `{f ≤ c + ε}` deformation retracts onto
  -- `{f ≤ c - ε}` with the negative disc bundles attached.
  have e₁ := singularHomologySublevelPairIsoOfCriticalValue h.contMDiff hac hcb
    (by linarith : c - ε < c) (by linarith : c < c + ε)
    (isClosed_Icc.preimage h.contMDiff.continuous).isCompact
    (isClosed_Icc.preimage h.contMDiff.continuous).isCompact hcrit
    (fun x hx hfx ↦ hcrit x hx ⟨by linarith [hfx.1], by linarith [hfx.2]⟩) (ModuleCat.of K K) n
  have hA : {y | f y ≤ c - ε} ∪ ⋃ j, Θ j '' (h.isNondegenerateCriticalSubmanifold j
      ).negativeDiscBundle hn _ (g j).toRiemannianMetric ε ⊆ {y | f y ≤ c + ε} :=
    union_subset (sublevel_mono f (by linarith)) <| iUnion_subset fun j ↦ by
      rintro _ ⟨x, hx, rfl⟩
      exact (SmoothEmbedding.IsCriticalSubmanifold.apply_le_of_mem_negativeDiscBundle
        (fun x hx ↦ hΘf j x (hD j hx)) hx).trans (by linarith)
  have hiso := TopPair.isIso_singularHomologyMap_ofInclusionMap_inclusion_of_homotopyRel
    (X := TopCat.of M) subset_union_left hA ((ContinuousMap.inclusion inter_subset_right).comp ret)
    (G.cast (ContinuousMap.ext fun _ ↦ rfl) rfl) (ModuleCat.of K K) n
  obtain ⟨e₂⟩ := nonempty_biproduct_iso_singularHomology_union_iUnion_image_negativeDiscBundle
    (ι := {j // ∀ s, f (i j s) = c}) hn (fun j ↦ h.isNondegenerateCriticalSubmanifold j)
    h.contMDiff (fun j ↦ hdim j) (fun j ↦ g j) (fun j ↦ hr j) Θ hε0 hΘf hD hdisj K n
  -- So the band homology is the direct sum of the homologies of the negative disc bundles.
  let e := e₁ ≪≫ (@asIso _ _ _ _ _ hiso).symm ≪≫ e₂.symm
  have := finite_singularHomology_sublevelPair_of_criticalValue (ModuleCat.of K K) h.contMDiff
    h.contMDiff.continuous.isProperMap hac hcb hcrit n
  have := Module.Finite.equiv e.toLinearEquiv
  have := ModuleCat.finite_of_finite_biproduct (R := K) (fun j : {j // ∀ s, f (i j s) = c} ↦
    ((h.isNondegenerateCriticalSubmanifold j).negativeDiscSpherePair hn
      (EuclideanSpace ℝ (Fin (finrank ℝ E - finrank ℝ (E' j)))) (g j).toRiemannianMetric ε
      ).singularHomology (ModuleCat.of K K) n)
  rw [e.toLinearEquiv.finrank_eq, ModuleCat.finrank_biproduct]
  simp only [fun j : {j // ∀ s, f (i j s) = c} ↦
    (h.isNondegenerateCriticalSubmanifold j).finrank_singularHomology_negativeDiscSpherePair hn
      h.contMDiff (hdim j) (g j) (hr j) hε0 K n]
  rw [← Finset.filter_filter, Finset.sum_filter]
  exact (Finset.sum_subtype _ (fun j ↦ by simp)
    fun j ↦ if r j ≤ n then bettiNumber K (S j) (n - r j) else 0).symm

/-- **A cut of the values of a Morse–Bott function.** On a compact manifold the values of a
Morse–Bott function can be cut at values `s 0 ≤ s 1 ≤ ⋯ ≤ s (N + 1)`, regular from `s 1` on, with
`s 0 < f ≤ s (N + 1)`, such that each band `[s j, s (j + 1)]` has at most one critical value, lying
strictly inside it. Summing over the bands the dimensions of their mod `2` homology then counts
the shifted Betti numbers of every piece once. -/
private theorem exists_cut_sum_finrank_sublevelPair :
    ∃ (s : ℕ → ℝ) (hs : Monotone s) (N : ℕ), (∀ x, s 0 < f x) ∧ (∀ x, f x ≤ s (N + 1)) ∧
      (∀ j ≤ N, IsRegularValue I 𝓘(ℝ) f (s (j + 1))) ∧
      ∀ n, ∑ j ∈ Finset.range (N + 1),
          finrank K ((sublevelPair f (hs j.le_succ)).singularHomology (ModuleCat.of K K) n :
            ModuleCat K) =
        ∑ p with r p ≤ n, bettiNumber K (S p) (n - r p) := by
  classical
  have hn : (∞ : ℕ∞ω) ≠ 0 := by simp
  obtain ⟨a, ha, ⟨q₀, hq₀⟩, ⟨q₁, hq₁⟩⟩ := exists_isCriticalBandCut_of_finite_image_criticalPoints
    h.contMDiff.continuous (h.finite_image_criticalPoints hn)
  -- Reindex the cut by `ℕ`, starting at `q₀`.
  let s (j : ℕ) : ℝ := a (q₀ + j)
  have hs : Monotone s := fun j k hjk ↦ ha.monotone (by simpa using hjk)
  have hband (j : ℕ) : ∃ c ∈ Ioo (s j) (s (j + 1)),
      ∀ x ∈ criticalPoints I f, f x ∈ Icc (s j) (s (j + 1)) → f x = c := by
    simpa [s, ← add_assoc] using (ha.isCriticalBand (q₀ + j)).exists_mem_Ioo_forall_eq
  choose c hc hcrit using hband
  set N := (max q₁ (q₀ + 1) - q₀ - 1).toNat
  have hs₀ (x : M) : s 0 < f x := by simpa [s] using hq₀ x
  have hsN (x : M) : f x ≤ s (N + 1) := (hq₁ x).trans (ha.monotone (by simp only [N]; omega))
  refine ⟨s, hs, N, hs₀, hsN, fun j _ ↦ ?_, fun n ↦ ?_⟩
  · -- A cut value is not a critical value, since the critical value of its band is inside it.
    refine isRegularValue_iff_notMem_image_criticalPoints.2 fun ⟨x, hx, hxs⟩ ↦ ?_
    have := hcrit j x hx ⟨hxs ▸ hs j.le_succ, hxs.le⟩
    linarith [(hc j).2]
  rw [Finset.sum_congr rfl fun j _ ↦
    h.finrank_singularHomology_sublevelPair_eq_sum hr K (hc j).1 (hc j).2 (hcrit j) n]
  simp_rw [Finset.sum_filter]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun p _ ↦ ?_
  -- The piece `p` lies on the critical level of exactly one band, `j₀`.
  obtain ⟨t₀⟩ := h.nonempty p
  have hv := (h.isNondegenerateCriticalSubmanifold p).mem_criticalPoints t₀
  have hfp (t : S p) : f (i p t) = f (i p t₀) := h.subsingleton_image_range hn p
    (mem_image_of_mem f (mem_range_self t)) (mem_image_of_mem f (mem_range_self t₀))
  obtain ⟨j₀, hj₀, hlt, hle⟩ := mem_iUnion₂.1
    (Ioc_subset_biUnion_Ioc (N + 1) s ⟨hs₀ (i p t₀), hsN (i p t₀)⟩)
  have hcj₀ : f (i p t₀) = c j₀ := hcrit j₀ _ hv ⟨hlt.le, hle⟩
  have hlevel (j : ℕ) : (∀ t, f (i p t) = c j) ↔ j = j₀ := by
    refine ⟨fun hj ↦ ?_, fun hj t ↦ hj ▸ (hfp t).trans hcj₀⟩
    have hcj := (hj t₀).symm.trans hcj₀
    rcases Nat.lt_trichotomy j j₀ with hlt' | rfl | hlt'
    · linarith [hs (Nat.succ_le_of_lt hlt'), (hc j).2, (hc j₀).1]
    · rfl
    · linarith [hs (Nat.succ_le_of_lt hlt'), (hc j).1, (hc j₀).2]
  rw [Finset.sum_eq_single_of_mem j₀ hj₀
    fun j _ hj ↦ ite_eq_right fun hpj ↦ hj ((hlevel j).1 hpj.1)]
  simp [(hlevel j₀).2 rfl]

/-- **The weak Morse–Bott inequalities over `𝔽₂`.** Let the family `i j : S j → M` exhibit `f` as
a Morse–Bott function on a compact boundaryless manifold, the piece `S j` having index `r j`, and
let `K` be a field whose only unit is `1`, such as `ZMod 2`. Then
`bₙ(M; K) ≤ ∑ b_{n - r j}(S j; K)`, the sum running over the pieces of index at most `n`. -/
theorem bettiNumber_le_sum (n : ℕ) :
    bettiNumber K M n ≤ ∑ p with r p ≤ n, bettiNumber K (S p) (n - r p) := by
  obtain ⟨s, hs, N, hs₀, hsN, hreg, hsum⟩ := h.exists_cut_sum_finrank_sublevelPair hr K
  rw [bettiNumber_def, ← hsum]
  exact finrank_singularHomology_le_sum_sublevelPair_of_contMDiff (ModuleCat.of K K) h.contMDiff
    hs hs₀ hsN hreg n

/-- **The strong Morse–Bott inequalities over `𝔽₂`.** Let the family `i j : S j → M` exhibit `f`
as a Morse–Bott function on a compact boundaryless manifold, the piece `S j` having index `r j`,
and let `K` be a field whose only unit is `1`, such as `ZMod 2`. Write `bₖ = bₖ(M; K)` and
`cₖ = ∑ b_{k - r j}(S j; K)` over the pieces of index at most `k`, the coefficient of `tᵏ` in the
Morse–Bott polynomial `∑ⱼ t^{r j} P_{S j}(t)`. Then `bₙ - bₙ₋₁ + ⋯ ± b₀ ≤ cₙ - cₙ₋₁ + ⋯ ± c₀`. -/
theorem sum_range_neg_one_pow_mul_bettiNumber_le_sum (n : ℕ) :
    ∑ k ∈ Finset.range (n + 1), (-1 : ℤ) ^ (n - k) * bettiNumber K M k ≤
      ∑ k ∈ Finset.range (n + 1), (-1 : ℤ) ^ (n - k) *
        ((∑ p with r p ≤ k, bettiNumber K (S p) (k - r p) : ℕ) : ℤ) := by
  obtain ⟨s, hs, N, hs₀, hsN, hreg, hsum⟩ := h.exists_cut_sum_finrank_sublevelPair hr K
  simpa only [← bettiNumber_def, hsum] using
    sum_range_neg_one_pow_mul_finrank_singularHomology_le_sum_sublevelPair_of_contMDiff
      (ModuleCat.of K K) h.contMDiff hs hs₀ hsN hreg n

/-- **Euler's equality for a Morse–Bott function over `𝔽₂`.** Under the hypotheses of
`TauCeti.IsMorseBottFamily.sum_range_neg_one_pow_mul_bettiNumber_le_sum`, for every `n` at least the
dimension of `M`, `∑ₖ₌₀ⁿ (-1)ᵏ bₖ = ∑ₖ₌₀ⁿ (-1)ᵏ cₖ`. -/
theorem sum_range_neg_one_pow_mul_bettiNumber_eq_sum {n : ℕ} (hdimn : finrank ℝ E ≤ n) :
    ∑ k ∈ Finset.range (n + 1), (-1 : ℤ) ^ k * bettiNumber K M k =
      ∑ k ∈ Finset.range (n + 1), (-1 : ℤ) ^ k *
        ((∑ p with r p ≤ k, bettiNumber K (S p) (k - r p) : ℕ) : ℤ) := by
  obtain ⟨s, hs, N, hs₀, hsN, hreg, hsum⟩ := h.exists_cut_sum_finrank_sublevelPair hr K
  simpa only [← bettiNumber_def, hsum] using
    sum_range_neg_one_pow_mul_finrank_singularHomology_eq_sum_sublevelPair_of_contMDiff
      (ModuleCat.of K K) h.contMDiff hs hs₀ hsN hreg hdimn

/-- **The Morse–Bott polynomial identity over `𝔽₂`.** Under the hypotheses of
`TauCeti.IsMorseBottFamily.sum_range_neg_one_pow_mul_bettiNumber_le_sum`, for every `n` at least the
dimension of `M`, `∑ₖ₌₀ⁿ cₖ tᵏ = ∑ₖ₌₀ⁿ bₖ tᵏ + (1 + t) Q(t)` for a polynomial `Q` with natural
number coefficients: the Morse–Bott polynomial `∑ⱼ t^{r j} P_{S j}(t)` exceeds the Poincaré
polynomial of `M` by `(1 + t) Q(t)`. -/
theorem exists_sum_range_monomial_sum_eq_add_mul {n : ℕ} (hdimn : finrank ℝ E ≤ n) :
    ∃ Q : ℕ[X], ∑ k ∈ Finset.range (n + 1),
        monomial k (∑ p with r p ≤ k, bettiNumber K (S p) (k - r p)) =
      ∑ k ∈ Finset.range (n + 1), monomial k (bettiNumber K M k) + (1 + Polynomial.X) * Q := by
  obtain ⟨s, hs, N, hs₀, hsN, hreg, hsum⟩ := h.exists_cut_sum_finrank_sublevelPair hr K
  obtain ⟨Q, hQ, -⟩ := exists_sum_range_monomial_sum_sublevelPair_eq_add_mul_of_contMDiff
    (ModuleCat.of K K) h.contMDiff hs hs₀ hsN hreg hdimn
  simp only [← bettiNumber_def, hsum] at hQ
  exact ⟨Q, hQ⟩

/-- **The lacunary principle for a Morse–Bott function over `𝔽₂`.** Under the hypotheses of
`TauCeti.IsMorseBottFamily.sum_range_neg_one_pow_mul_bettiNumber_le_sum`, write
`cₖ = ∑ b_{k - r j}(S j; K)` over the pieces of index at most `k`. If of any two consecutive counts
`cₖ` and `cₖ₊₁` one vanishes, then `bₙ(M; K) = cₙ` for every `n`: the Morse–Bott function is
perfect over `K`. -/
theorem bettiNumber_eq_sum
    (hlac : ∀ k, ∑ p with r p ≤ k, bettiNumber K (S p) (k - r p) = 0 ∨
      ∑ p with r p ≤ k + 1, bettiNumber K (S p) (k + 1 - r p) = 0) (n : ℕ) :
    bettiNumber K M n = ∑ p with r p ≤ n, bettiNumber K (S p) (n - r p) :=
  congrFun (eq_of_forall_sum_range_neg_one_pow_mul_le
    (h.sum_range_neg_one_pow_mul_bettiNumber_le_sum hr K) hlac) n

end IsMorseBottFamily

end Level

end TauCeti
