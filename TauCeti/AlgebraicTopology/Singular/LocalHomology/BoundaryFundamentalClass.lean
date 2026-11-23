/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.LocalHomology.IsFundamentalClass
public import TauCeti.AlgebraicTopology.Singular.LocalHomology.RelativeFundamentalClass
public import TauCeti.AlgebraicTopology.Singular.Triple
import TauCeti.Algebra.Category.ModuleCat.SpanSingleton
import TauCeti.AlgebraicTopology.Singular.Excision
import TauCeti.AlgebraicTopology.Singular.Homotopy.Invariance
import TauCeti.AlgebraicTopology.Singular.LocalHomology.OpenEmbedding

/-!
# The boundary of the relative fundamental class

Let `X` be a compact Hausdorff space and `ι : M → X` an open embedding of an oriented
`(n + 1)`-manifold `M`, whose complement `∂X = X ∖ ι(M)` is the image of a collared map, as for a
compact topological manifold with boundary or with corners. The connecting morphism of the pair
`(X, ∂X)` sends the relative fundamental class `[X, ∂X] ∈ Hₙ₊₁(X, ∂X; ℤ)`
(`TauCeti.HomologicalOrientation.fundamentalClassRel`) to a fundamental class of `∂X`: its image in
the local homology `Hₙ(∂X, ∂X ∖ {z}; ℤ)` generates that group at every point `z` of `∂X`
(`TauCeti.HomologicalOrientation.isFundamentalClass_singularHomologyδ_fundamentalClassRel`). No
manifold structure is assumed on `∂X`: the collar identifies its local homology at `z` with the
local homology of `M` at an interior point one dimension up. Through the cubical–singular
comparison, `TopPair.exists_boundary_eq_of_singularHomologyδ_eq` therefore gives a normalized
cubical fundamental chain of `X` relative to `∂X` whose boundary is any prescribed normalized
cubical cycle of `∂X` representing `∂[X, ∂X]`, and such a cycle is a fundamental cycle of `∂X`;
this is the homological input of fundamental chains of manifolds with corners.

The argument uses neither the orientation nor the integral coefficients, only that the class
generates the local homology at the interior points. With coefficients in any module `R` over a
ring `Λ`, a class of `Hₙ₊₁(X, ∂X; R)` whose local images at the points of `ι(M)` generate is sent
to a fundamental class of `∂X` with coefficients in `R`
(`TauCeti.isFundamentalClass_singularHomologyδ_of_forall_span_eq_top`). With coefficients in a
Dedekind-finite ring whose only unit is `1`, such as `ZMod 2`, this applies to the fundamental class
relative to the boundary of an unoriented `X`
(`TauCeti.existsUnique_span_localHomologyRestriction_range_eq_top`);
when `∂X` is moreover a compact manifold, its image is the unique fundamental class of `∂X`
(`TauCeti.IsFundamentalClass.eq_of_subsingleton_units`). This is the homological input of the
fundamental chains of manifolds with corners over `ℤ/2` of Barraud and Cornea.

## Proof

Fix `z ∈ ∂X` and a collar `c : ∂X × [0, 1) → X` with `c (z, 0) = z`. Let `p = c (z, 1 / 2)` and
let `σ = c ({z} × [0, 1 / 2])` be the segment from `z` to `p`. The identity of `X` is a map of
triples `(X, ∂X, ∂X ∖ {z}) ⟶ (X, X ∖ {p}, X ∖ σ)`, so by naturality of connecting morphisms the
image of `∂[X, ∂X]` in `Hₙ(∂X, ∂X ∖ {z})` maps to the image under the connecting morphism of the
second triple of the restriction of `[X, ∂X]` to the local homology at `p`, which is the local
orientation at `p`. The comparison is made in the model `B × [0, 1)`, which the collar carries
onto an open subset of `X`:

* the local homology of `B × [0, 1)` along `{b} × [0, 1 / 2]` vanishes, since pushing the depth
  coordinate up deforms the product into the complement of the segment; so the connecting morphism
  `Hₙ₊₁(P, P ∖ {(b, 1 / 2)}) ⟶ Hₙ(P ∖ {(b, 1 / 2)}, P ∖ {b} × [0, 1 / 2])` of the model triple is an
  isomorphism;
* excising the points of depth at least `1 / 2` and contracting the depth coordinate show that
  `m ↦ (m, 0)` induces isomorphisms from `Hₙ(B, B ∖ {b})` to the homology of the inner pair of the
  model triple.

The collar is an open embedding, so by excision it induces isomorphisms on local homology, and the
two isomorphisms above transport to the triple in `X`. The composite of these isomorphisms carries
the local class of `[X, ∂X]` at `p`, a generator, to the image of `∂[X, ∂X]` at `z`, which is
therefore a generator.

## Main results

* `TauCeti.isFundamentalClass_singularHomologyδ_of_forall_span_eq_top`: the connecting morphism
  `Hₙ₊₁(X, ∂X; R) ⟶ Hₙ(∂X; R)` carries a class generating the local homology at every interior
  point to a fundamental class of `∂X`.
* `TauCeti.HomologicalOrientation.isFundamentalClass_singularHomologyδ_fundamentalClassRel`: the
  connecting morphism `Hₙ₊₁(X, ∂X; ℤ) ⟶ Hₙ(∂X; ℤ)` carries the relative fundamental class to a
  fundamental class of `∂X`.

## References

* A. Hatcher, *Algebraic Topology*, Cambridge University Press, 2002, Section 3.3: fundamental
  classes of compact manifolds with boundary and Lefschetz duality.
* J.-F. Barraud, O. Cornea, *Lagrangian intersections and the Serre spectral sequence*, Annals of
  Mathematics 166 (2007), Lemma 2.2 and Appendix A, where fundamental chains relative to the
  boundary, with boundary the fundamental cycle of the boundary, form the representing chain
  systems.
-/

public section

noncomputable section

open CategoryTheory Limits Set Topology Module

universe w v u

namespace TauCeti

namespace CollarModel

/-! ### The model `B × [0, 1)` -/

section Model

variable {A : Type u} [Category.{v} A] [HasCoproducts.{w} A] [Abelian A] (R : A)
  {B : Type w} [TopologicalSpace B] (b : B)

/-- The depth `1 / 2` of the collar coordinate. -/
private def half : Ico (0 : ℝ) 1 := ⟨1 / 2, by norm_num, by norm_num⟩

/-- The segment `{b} × [0, 1 / 2]` of `B × [0, 1)`. -/
private def segment : Set (B × Ico (0 : ℝ) 1) := {q | q.1 = b ∧ (q.2 : ℝ) ≤ 1 / 2}

private lemma isClosed_segment [T1Space B] : IsClosed (segment b) :=
  (isClosed_singleton.preimage continuous_fst).inter
    (isClosed_le (continuous_subtypeVal.comp continuous_snd) continuous_const)

private lemma isCompact_segment : IsCompact (segment b) := by
  have hI : IsCompact {t : Ico (0 : ℝ) 1 | (t : ℝ) ≤ 1 / 2} := by
    rw [IsEmbedding.subtypeVal.isCompact_iff]
    convert isCompact_Icc (a := (0 : ℝ)) (b := 1 / 2) using 1
    ext t
    refine ⟨?_, fun ht ↦ ⟨⟨t, ht.1, by linarith [ht.2]⟩, ht.2, rfl⟩⟩
    rintro ⟨t, ht, rfl⟩
    exact ⟨t.property.1, ht⟩
  exact isCompact_singleton.prod hI

/-- Pushing the depth coordinate up to at least `3τ / 4` at time `τ`. -/
private def pushUp (τ : unitInterval) (q : B × Ico (0 : ℝ) 1) : B × Ico (0 : ℝ) 1 :=
  (q.1, ⟨max q.2 (τ * (3 / 4)), le_max_of_le_left q.2.property.1,
    max_lt q.2.property.2 (by nlinarith [τ.property.1, τ.property.2])⟩)

private lemma continuous_pushUp : Continuous fun x : unitInterval × (B × Ico (0 : ℝ) 1) ↦
    pushUp x.1 x.2 := by
  unfold pushUp; fun_prop

omit [TopologicalSpace B] in
private lemma pushUp_zero (q : B × Ico (0 : ℝ) 1) : pushUp 0 q = q :=
  Prod.ext rfl (Subtype.ext (by simp [pushUp, q.2.property.1]))

omit [TopologicalSpace B] in
private lemma pushUp_one_notMem (q : B × Ico (0 : ℝ) 1) : pushUp 1 q ∉ segment b := fun h ↦ by
  have := h.2
  simp only [pushUp, Set.Icc.coe_one, one_mul] at this
  exact absurd ((le_max_right _ _).trans this) (by norm_num)

omit [TopologicalSpace B] in
private lemma pushUp_notMem {τ : unitInterval} {q : B × Ico (0 : ℝ) 1} (hq : q ∉ segment b) :
    pushUp τ q ∉ segment b :=
  fun h ↦ hq ⟨h.1, (le_max_left _ _).trans h.2⟩

/-- **The local homology of `B × [0, 1)` along the segment `{b} × [0, 1 / 2]` vanishes**: pushing
the depth coordinate up deforms the whole product into the complement of the segment, keeping that
complement in place. -/
private lemma isZero_localHomology_segment (k : ℕ) :
    IsZero (localHomology R (segment b) k) :=
  TopPair.isZero_singularHomology_ofSubset_of_homotopy (ρ := TopCat.ofHom
      ⟨pushUp 1, continuous_pushUp.comp (Continuous.prodMk_right 1)⟩)
    { toFun := fun x ↦ pushUp x.1 x.2
      continuous_toFun := continuous_pushUp
      map_zero_left := pushUp_zero
      map_one_left := fun _ ↦ rfl }
    (fun _ _ hq ↦ pushUp_notMem b hq) (pushUp_one_notMem b) R k

omit [TopologicalSpace B] in
private lemma mem_segment_half : (b, half) ∈ segment b :=
  ⟨rfl, le_of_eq (rfl : ((half : Ico (0 : ℝ) 1) : ℝ) = 1 / 2)⟩

omit [TopologicalSpace B] in
private lemma compl_segment_subset :
    (segment b)ᶜ ⊆ ({(b, half)}ᶜ : Set (B × Ico (0 : ℝ) 1)) :=
  compl_subset_compl.2 (singleton_subset_iff.2 (mem_segment_half b))

/-- The triple `(B × [0, 1), B × [0, 1) ∖ {(b, 1 / 2)}, B × [0, 1) ∖ {b} × [0, 1 / 2])`. -/
private abbrev triple : TopTriple.{w} :=
  TopTriple.ofSubset (X := TopCat.of (B × Ico (0 : ℝ) 1)) (compl_segment_subset b)

/-- The connecting morphism of the triple is an isomorphism, since the local homology along the
segment vanishes. -/
private instance isIso_singularHomologyδ_triple (k : ℕ) :
    IsIso ((triple b).singularHomologyδ R (k + 1) k) :=
  isIso_singularHomologyδ_ofSubset_compl R (singleton_subset_iff.2 (mem_segment_half b)) k
    (isZero_localHomology_segment R b _)
    (isZero_localHomology_segment R b _)

variable (B) in
/-- The points of `B × [0, 1)` of depth less than `1 / 2`. -/
private def lower : Set (B × Ico (0 : ℝ) 1) := {q | (q.2 : ℝ) < 1 / 2}

omit [TopologicalSpace B] in
private lemma lower_subset : lower B ⊆ ({(b, half)}ᶜ : Set (B × Ico (0 : ℝ) 1)) := by
  rintro q hq rfl
  exact lt_irrefl (1 / 2 : ℝ) hq

/-- The pair `(B × [0, 1 / 2), (B ∖ {b}) × [0, 1 / 2))`. -/
private abbrev lowerPair : TopPair.{w} :=
  TopPair.ofInclusion (X := TopCat.of (B × Ico (0 : ℝ) 1))
    (inter_subset_left : lower B ∩ (segment b)ᶜ ⊆ lower B)

/-- The inclusion of `lowerPair b` into the inner pair of the triple. -/
private def lowerPairMap : lowerPair b ⟶ TopTriple.innerPair.obj (triple b) :=
  TopPair.ofInclusionMap _ (compl_segment_subset b) (ContinuousMap.inclusion (lower_subset b))
    -- The ascription unfolds the coercion of `ContinuousMap.inclusion` to `Subtype.val`, where
    -- `hx.2` applies.
    fun x hx ↦ show ((ContinuousMap.inclusion (lower_subset b) x : B × Ico (0 : ℝ) 1)) ∈
      (segment b)ᶜ from hx.2

private lemma lowerPairMap_fst :
    TopPair.Hom.fst (lowerPairMap b) = TopCat.ofHom (ContinuousMap.inclusion (lower_subset b)) :=
  TopPair.ofInclusionMap_fst _ _

/-- **Excision of the points of depth at least `1 / 2`**: they form a closed subset of
`B × [0, 1) ∖ {(b, 1 / 2)}` inside the open complement of the segment. -/
private lemma isIso_singularHomologyMap_lowerPairMap [T1Space B] (k : ℕ) :
    IsIso (TopPair.singularHomologyMap (lowerPairMap b) R k) := by
  refine TopPair.isIso_singularHomologyMap_of_open_cover R (lowerPairMap b) ?_ ?_
    (fun i : Bool ↦ bif i then Subtype.val ⁻¹' lower B else Subtype.val ⁻¹' (segment b)ᶜ) ?_ ?_
    ?_ k
  · rw [lowerPairMap_fst]
    exact IsEmbedding.inclusion (lower_subset b)
  · rintro (x : lower B) ⟨(y : ((segment b)ᶜ : Set (B × Ico (0 : ℝ) 1))), hy⟩
    rw [lowerPairMap_fst] at hy
    have hyx : (y : B × Ico (0 : ℝ) 1) = x := congrArg Subtype.val hy
    exact ⟨⟨x, x.property, hyx ▸ y.property⟩, rfl⟩
  · rintro (_ | _)
    · exact (isClosed_segment b).isOpen_compl.preimage continuous_subtypeVal
    · exact (isOpen_lt (continuous_subtypeVal.comp continuous_snd) continuous_const).preimage
        continuous_subtypeVal
  · refine eq_univ_of_forall fun (w : ({(b, half)}ᶜ : Set (B × Ico (0 : ℝ) 1))) ↦
      mem_iUnion.2 ?_
    by_cases hw : ((w : B × Ico (0 : ℝ) 1).2 : ℝ) < 1 / 2
    · exact ⟨true, hw⟩
    · refine ⟨false, fun hs ↦ w.property (Prod.ext hs.1 (Subtype.ext ?_))⟩
      exact le_antisymm hs.2 (not_lt.1 hw)
  · rintro (_ | _)
    · exact Or.inl fun (w : ({(b, half)}ᶜ : Set (B × Ico (0 : ℝ) 1))) hw ↦ ⟨⟨w, hw⟩, rfl⟩
    · refine Or.inr fun (w : ({(b, half)}ᶜ : Set (B × Ico (0 : ℝ) 1))) hw ↦ ⟨⟨w, hw⟩, ?_⟩
      rw [lowerPairMap_fst]
      rfl

/-- The depth `0` of the collar coordinate. -/
private def bottom : Ico (0 : ℝ) 1 := ⟨0, le_rfl, by norm_num⟩

private lemma bottom_lt_half : ((bottom : Ico (0 : ℝ) 1) : ℝ) < 1 / 2 := by
  norm_num [bottom]

/-- The inclusion `m ↦ (m, 0)` of `(B, B ∖ {b})` into `lowerPair b`. -/
private def toLower : TopPair.ofSubset ({b}ᶜ : Set (TopCat.of B)) ⟶ lowerPair b :=
  TopPair.ofHom
    (TopCat.ofHom ⟨fun m ↦ ⟨(m, bottom), bottom_lt_half⟩,
      (continuous_id.prodMk continuous_const).subtype_mk _⟩)
    (TopCat.ofHom ⟨fun m ↦ ⟨(m.val, bottom), bottom_lt_half, fun h ↦ m.property h.1⟩,
      (continuous_subtypeVal.prodMk continuous_const).subtype_mk _⟩) rfl

/-- The projection `(m, t) ↦ m` of `lowerPair b` onto `(B, B ∖ {b})`. -/
private def fromLower : lowerPair b ⟶ TopPair.ofSubset ({b}ᶜ : Set (TopCat.of B)) :=
  TopPair.ofHom
    (TopCat.ofHom ⟨fun q : lower B ↦ (q : B × Ico (0 : ℝ) 1).1, by fun_prop⟩)
    (TopCat.ofHom ⟨fun q : ↥(lower B ∩ (segment b)ᶜ) ↦
      ⟨(q : B × Ico (0 : ℝ) 1).1, fun h ↦ q.property.2 ⟨h, q.property.1.le⟩⟩,
      (continuous_fst.comp continuous_subtypeVal).subtype_mk _⟩) rfl

private lemma toLower_comp_fromLower : toLower b ≫ fromLower b = 𝟙 _ :=
  TopPair.hom_ext_of_fst _ rfl

variable (B) in
/-- Contracting the depth coordinate of `B × [0, 1 / 2)` to `0`. -/
private def lowerContraction : C(lower B, lower B) :=
  ⟨fun q ↦ ⟨((q : B × Ico (0 : ℝ) 1).1, bottom), bottom_lt_half⟩,
    ((continuous_fst.comp continuous_subtypeVal).prodMk continuous_const).subtype_mk _⟩

variable (B) in
/-- Scaling the depth coordinate deforms `lowerContraction B` into the identity of `lower B`. -/
private def lowerHomotopy :
    (lowerContraction B).Homotopy (ContinuousMap.id (lower B)) where
  toFun x := ⟨((x.2 : B × Ico (0 : ℝ) 1).1, ⟨x.1 * ((x.2 : B × Ico (0 : ℝ) 1).2 : ℝ),
      mul_nonneg x.1.property.1 (x.2 : B × Ico (0 : ℝ) 1).2.property.1,
      (mul_le_of_le_one_left (x.2 : B × Ico (0 : ℝ) 1).2.property.1 x.1.property.2).trans_lt
        (x.2 : B × Ico (0 : ℝ) 1).2.property.2⟩),
    (mul_le_of_le_one_left (x.2 : B × Ico (0 : ℝ) 1).2.property.1 x.1.property.2).trans_lt
        x.2.property⟩
  continuous_toFun := by fun_prop
  map_zero_left q := by
    refine Subtype.ext (Prod.ext rfl (Subtype.ext ?_))
    simp [lowerContraction, bottom]
  map_one_left q := by
    refine Subtype.ext (Prod.ext rfl (Subtype.ext ?_))
    simp

private lemma fromLower_comp_toLower :
    fromLower b ≫ toLower b =
      TopPair.ofInclusionMap inter_subset_left inter_subset_left (lowerContraction B)
        -- The ascription unfolds the point `lowerContraction B q` to its underlying pair, whose
        -- first coordinate is that of `q`.
        fun q (hq : (q : B × Ico (0 : ℝ) 1) ∈ lower B ∩ (segment b)ᶜ) ↦
          show ((lowerContraction B q : lower B) : B × Ico (0 : ℝ) 1) ∈ lower B ∩ (segment b)ᶜ
            from ⟨(lowerContraction B q).property, fun h ↦ hq.2 ⟨h.1, hq.1.le⟩⟩ :=
  TopPair.hom_ext_of_fst _ (by rw [TopPair.ofInclusionMap_fst]; rfl)

/-- `(B, B ∖ {b}) ⟶ lowerPair b` induces isomorphisms on relative homology: the projection is a
homotopy inverse. -/
private lemma isIso_singularHomologyMap_toLower (k : ℕ) :
    IsIso (TopPair.singularHomologyMap (toLower b) R k) := by
  refine TopPair.isIso_singularHomologyMap _ (fromLower b)
    (toLower_comp_fromLower b ▸ TopPair.Homotopy.refl _) ?_ R k
  rw [fromLower_comp_toLower, ← TopPair.ofInclusionMap_id]
  exact TopPair.ofInclusionHomotopy (hst := inter_subset_left) (hst' := inter_subset_left)
    -- As in `fromLower_comp_toLower`, the ascription unfolds the point to its underlying pair.
    (lowerHomotopy B) fun τ q (hq : (q : B × Ico (0 : ℝ) 1) ∈ lower B ∩ (segment b)ᶜ) ↦
      (⟨(lowerHomotopy B (τ, q)).property, fun h ↦ hq.2 ⟨h.1, hq.1.le⟩⟩ :
        ((lowerHomotopy B (τ, q) : lower B) : B × Ico (0 : ℝ) 1) ∈ lower B ∩ (segment b)ᶜ)

/-- The inclusion `m ↦ (m, 0)` of `(B, B ∖ {b})` into the inner pair of the model triple. -/
private def boundaryMap :
    TopPair.ofSubset ({b}ᶜ : Set (TopCat.of B)) ⟶ TopTriple.innerPair.obj (triple b) :=
  toLower b ≫ lowerPairMap b

omit [TopologicalSpace B] in
private lemma bottom_notMem_singleton (m : B) :
    (m, bottom) ∈ ({(b, half)}ᶜ : Set (B × Ico (0 : ℝ) 1)) :=
  lower_subset b bottom_lt_half

private lemma boundaryMap_fst :
    TopPair.Hom.fst (boundaryMap b) =
      TopCat.ofHom ⟨fun m ↦ ⟨(m, bottom), bottom_notMem_singleton b m⟩,
        (continuous_id.prodMk continuous_const).subtype_mk _⟩ := by
  rw [boundaryMap, TopPair.Hom.fst_comp, lowerPairMap_fst]
  rfl

private lemma isIso_singularHomologyMap_boundaryMap [T1Space B] (k : ℕ) :
    IsIso (TopPair.singularHomologyMap (boundaryMap b) R k) := by
  have := isIso_singularHomologyMap_toLower R b k
  have := isIso_singularHomologyMap_lowerPairMap R b k
  rw [boundaryMap, TopPair.singularHomologyMap_comp]
  infer_instance

end Model

/-! ### The comparison in a space with a collared subset -/

section Collar

variable {A : Type u} [Category.{v} A] [HasCoproducts.{w} A] [Abelian A] (R : A)
  {X : Type w} [TopologicalSpace X] [T2Space X] {D : Set X}
  {c : D × Ico (0 : ℝ) 1 → X} (hc : IsCollar (Subtype.val : D → X) c) (z : D)

include hc in
omit [T2Space X] in
private lemma apply_mem_iff (q : D × Ico (0 : ℝ) 1) :
    c q ∈ D ↔ q.2 = ⟨0, by norm_num⟩ := by
  have h := congrArg (q ∈ ·) hc.preimage_range
  simp only [Subtype.range_coe_subtype, ofPred_mem_eq, mem_preimage, mem_prod, mem_univ,
    mem_singleton_iff, true_and, eq_iff_iff] at h
  exact h

include hc in
omit [T2Space X] in
private lemma apply_half_notMem : c (z, half) ∉ D := fun h ↦ by
  have := congrArg Subtype.val ((apply_mem_iff hc _).1 h)
  norm_num [half] at this

include hc in
omit [T2Space X] in
private lemma notMem_image_segment {w : D} (hw : w ≠ z) : (w : X) ∉ c '' segment z := by
  rintro ⟨q, hq, hqw⟩
  have h0 := (apply_mem_iff hc q).1 (hqw ▸ w.property)
  refine hw (Subtype.ext ?_)
  rw [← hqw, ← hc.apply_zero z, ← hq.1, ← h0]

include hc in
private lemma isClosed_image_segment : IsClosed (c '' segment z) :=
  ((isCompact_segment z).image hc.isOpenEmbedding.continuous).isClosed

include hc in
omit [T2Space X] in
private lemma preimage_image_segment : c ⁻¹' (c '' segment z) = segment z :=
  hc.isOpenEmbedding.injective.preimage_image _

omit [TopologicalSpace X] [T2Space X] in
private lemma compl_image_segment_subset : (c '' segment z)ᶜ ⊆ {c (z, half)}ᶜ :=
  compl_subset_compl.2 (singleton_subset_iff.2 (mem_image_of_mem c (mem_segment_half z)))

/-- The triple `(X, X ∖ {p}, X ∖ σ)` for the point `p = c (z, 1 / 2)` and the segment
`σ = c ({z} × [0, 1 / 2])` from `z` to `p`. -/
private abbrev spaceTriple : TopTriple.{w} :=
  TopTriple.ofSubset (X := TopCat.of X) (compl_image_segment_subset (c := c) z)

/-- The collar as a map of triples from the model triple to `spaceTriple z`. -/
private def collarTripleMap : triple z ⟶ spaceTriple (c := c) z :=
  ⟨ComposableArrows.homMk₂
    (TopCat.ofHom ⟨fun q : ↥(segment z)ᶜ ↦ ⟨c q, fun h ↦
      q.property (hc.isOpenEmbedding.injective.mem_set_image.1 h)⟩, by
        have := hc.isOpenEmbedding.continuous; fun_prop⟩)
    (TopCat.ofHom ⟨fun q : ↥({(z, half)}ᶜ : Set (D × Ico (0 : ℝ) 1)) ↦ ⟨c q, fun h ↦
      q.property (hc.isOpenEmbedding.injective h)⟩, by
        have := hc.isOpenEmbedding.continuous; fun_prop⟩)
    (TopCat.ofHom ⟨c, hc.isOpenEmbedding.continuous⟩) rfl rfl⟩

/-- The triple `(X, D, D ∖ {z})`. -/
private abbrev boundaryTriple : TopTriple.{w} :=
  TopTriple.of (TopCat.ofHom ⟨Subtype.val, continuous_subtypeVal⟩ :
      TopCat.of ↥({z}ᶜ : Set D) ⟶ TopCat.of D)
    (TopCat.ofHom ⟨Subtype.val, continuous_subtypeVal⟩ : TopCat.of D ⟶ TopCat.of X)
    IsEmbedding.subtypeVal IsEmbedding.subtypeVal

/-- The identity of `X` as a map of triples `(X, D, D ∖ {z}) ⟶ (X, X ∖ {p}, X ∖ σ)`. -/
private def boundaryTripleMap : boundaryTriple z ⟶ spaceTriple (c := c) z :=
  ⟨ComposableArrows.homMk₂
    (TopCat.ofHom ⟨fun w : ↥({z}ᶜ : Set D) ↦ ⟨(w : D), notMem_image_segment hc z w.property⟩, by
      fun_prop⟩)
    (TopCat.ofHom ⟨fun w : D ↦ ⟨w, fun h ↦ apply_half_notMem hc z (h ▸ w.property)⟩, by fun_prop⟩)
    (𝟙 _) rfl rfl⟩

/-- The inclusion `m ↦ (m, 0)` of the model, as a map out of the inner pair of
`boundaryTriple z`. -/
-- `boundaryMap z` has this type because `TopTriple.innerPair.obj (boundaryTriple z)` unfolds, by
-- the `abbrev`s `TopTriple.innerPair` and `TopTriple.of`, to the pair of the inclusion
-- `Subtype.val : D ∖ {z} → D`, which is `TopPair.ofSubset ({z}ᶜ : Set D)` by definition.
private def boundaryTripleInnerMap :
    TopTriple.innerPair.obj (boundaryTriple z) ⟶ TopTriple.innerPair.obj (triple z) :=
  boundaryMap z

private instance isIso_singularHomologyMap_boundaryTripleInnerMap (k : ℕ) :
    IsIso (TopPair.singularHomologyMap (boundaryTripleInnerMap z) R k) :=
  isIso_singularHomologyMap_boundaryMap R z k

include hc in
private instance isIso_singularHomologyMap_outerPair_collarTripleMap (k : ℕ) :
    IsIso (TopPair.singularHomologyMap (TopTriple.outerPair.map (collarTripleMap hc z)) R k) := by
  have h : c ⁻¹' {c (z, half)} = {(z, half)} := by
    rw [← image_singleton, hc.isOpenEmbedding.injective.preimage_image]
  have hiso := isIso_localHomologyMap R ⟨c, hc.isOpenEmbedding.continuous⟩ hc.isOpenEmbedding h
    isClosed_singleton (singleton_subset_iff.2 (mem_range_self _)) k
  rw [localHomologyMap_def] at hiso
  have e : TopTriple.outerPair.map (collarTripleMap hc z) =
      TopPair.ofSubsetMap (X := TopCat.of (D × Ico (0 : ℝ) 1)) (Y := TopCat.of X)
        (B := ({(z, half)}ᶜ : Set (D × Ico (0 : ℝ) 1))) (B' := {c (z, half)}ᶜ)
        (TopCat.ofHom ⟨c, hc.isOpenEmbedding.continuous⟩)
        ((mapsTo_preimage _ _).mono_left (compl_subset_compl.2 h.subset)) :=
    TopPair.hom_ext_of_fst _ (TopPair.ofSubsetMap_fst _ _).symm
  rw [e]
  exact hiso

include hc in
private lemma isZero_localHomology_image_segment (k : ℕ) :
    IsZero (localHomology R (c '' segment z) k) :=
  have := isIso_localHomologyMap R ⟨c, hc.isOpenEmbedding.continuous⟩ hc.isOpenEmbedding
    (preimage_image_segment hc z) (isClosed_image_segment hc z) (image_subset_range _ _) k
  (isZero_localHomology_segment R z k).of_iso
    (asIso (localHomologyMap R ⟨c, hc.isOpenEmbedding.continuous⟩
      (preimage_image_segment hc z).subset k)).symm

include hc in
private lemma isIso_singularHomologyδ_spaceTriple (k : ℕ) :
    IsIso ((spaceTriple (c := c) z).singularHomologyδ R (k + 1) k) :=
  isIso_singularHomologyδ_ofSubset_compl R
    (singleton_subset_iff.2 (mem_image_of_mem c (mem_segment_half z))) k
    (isZero_localHomology_image_segment R hc z _) (isZero_localHomology_image_segment R hc z _)

include hc in
omit [T2Space X] in
private lemma innerPair_map_boundaryTripleMap :
    TopTriple.innerPair.map (boundaryTripleMap hc z) =
      boundaryTripleInnerMap z ≫ TopTriple.innerPair.map (collarTripleMap hc z) := by
  refine TopPair.hom_ext_of_fst _ ?_
  rw [TopPair.Hom.fst_comp, boundaryTripleInnerMap, boundaryMap_fst]
  ext w
  exact Subtype.ext (hc.apply_zero w).symm

/-- The isomorphism `Hₖ₊₁(X, X ∖ {p}) ≅ Hₖ(D, D ∖ {z})` read off the collar: the inverse of the
collar on local homology at `p = c (z, 1 / 2)`, the connecting morphism of the model triple, and
the inverse of the inclusion `m ↦ (m, 0)`. -/
private def localHomologyIso (k : ℕ) :
    (TopTriple.outerPair.obj (spaceTriple (c := c) z)).singularHomology R (k + 1) ≅
      (TopTriple.innerPair.obj (boundaryTriple z)).singularHomology R k :=
  (asIso (TopPair.singularHomologyMap (TopTriple.outerPair.map (collarTripleMap hc z)) R
      (k + 1))).symm ≪≫ asIso ((triple z).singularHomologyδ R (k + 1) k rfl) ≪≫
    (asIso (TopPair.singularHomologyMap (boundaryTripleInnerMap z) R k)).symm

/-- **The connecting morphism of `(X, D, D ∖ {z})` at a collared point** is restriction to the
local homology of `X` at `p = c (z, 1 / 2)` followed by `localHomologyIso`. -/
private lemma singularHomologyδ_boundaryTriple (k : ℕ) :
    (boundaryTriple z).singularHomologyδ R (k + 1) k =
      TopPair.singularHomologyMap (TopTriple.outerPair.map (boundaryTripleMap hc z)) R (k + 1) ≫
        (localHomologyIso R hc z k).hom := by
  have hΨ := TopTriple.singularHomologyδ_naturality (boundaryTripleMap hc z) R (k + 1) k
  have hΦ := TopTriple.singularHomologyδ_naturality (collarTripleMap hc z) R (k + 1) k
  have hinner : TopPair.singularHomologyMap (TopTriple.innerPair.map (boundaryTripleMap hc z)) R k =
      TopPair.singularHomologyMap (boundaryTripleInnerMap z) R k ≫
        TopPair.singularHomologyMap (TopTriple.innerPair.map (collarTripleMap hc z)) R k := by
    rw [innerPair_map_boundaryTripleMap hc z, TopPair.singularHomologyMap_comp]
  have := isIso_singularHomologyδ_spaceTriple R hc z k
  have : IsIso ((triple z).singularHomologyδ R (k + 1) k rfl ≫
      TopPair.singularHomologyMap (TopTriple.innerPair.map (collarTripleMap hc z)) R k) := by
    rw [hΦ]
    infer_instance
  have := IsIso.of_isIso_comp_left ((triple z).singularHomologyδ R (k + 1) k rfl)
    (TopPair.singularHomologyMap (TopTriple.innerPair.map (collarTripleMap hc z)) R k)
  rw [← cancel_mono (TopPair.singularHomologyMap (boundaryTripleInnerMap z) R k ≫
    TopPair.singularHomologyMap (TopTriple.innerPair.map (collarTripleMap hc z)) R k)]
  simp only [localHomologyIso, Iso.trans_hom, Iso.symm_hom, asIso_hom, asIso_inv, Category.assoc,
    IsIso.inv_hom_id_assoc]
  rw [hΦ, IsIso.inv_hom_id_assoc, ← hinner, hΨ]

end Collar

end CollarModel

/-! ### The boundary of a relative class with generating interior local classes -/

section Coefficients

variable {X M : Type w} {N : Type*} [TopologicalSpace X] [TopologicalSpace N] [T2Space X]
  {ι : M → X} {f : N → X} {Λ : Type w} [Ring Λ] (R : ModuleCat.{w} Λ) {n : ℕ}
  (hιf : range ι = (range f)ᶜ) (hf : IsCollared f)

include hιf hf in
/-- **The boundary of a relative class generating at every interior point is a fundamental class
of the boundary.** Let `X` be a Hausdorff space and `∂X = X ∖ ι(M)` the collared image of
`f : N → X`, and let `R` be a module over a ring `Λ`. If the image of `γ ∈ Hₙ₊₁(X, ∂X; R)` in the
local homology `Hₙ₊₁(X, X ∖ {p}; R)` generates that `Λ`-module at every point `p` of `ι(M)`, then
the connecting morphism `Hₙ₊₁(X, ∂X; R) ⟶ Hₙ(∂X; R)` sends `γ` to a fundamental class of `∂X`.

No manifold structure is used, on `M` or on `∂X`: the collar identifies the local homology of
`∂X` at `z` with that of `X` at an interior point one dimension up. For integral coefficients this
gives `TauCeti.HomologicalOrientation.isFundamentalClass_singularHomologyδ_fundamentalClassRel`.
With coefficients in a Dedekind-finite ring whose only unit is `1`, such as `ZMod 2`, it applies to
the fundamental class relative to the boundary of
`TauCeti.existsUnique_span_localHomologyRestriction_range_eq_top`, with no orientation. -/
theorem isFundamentalClass_singularHomologyδ_of_forall_span_eq_top
    {γ : (localHomology R (range ι) (n + 1) : ModuleCat.{w} Λ)}
    (hγ : ∀ p (hp : p ∈ range ι),
      Submodule.span Λ {localHomologyRestriction R (singleton_subset_iff.2 hp) (n + 1) γ} = ⊤) :
    IsFundamentalClass (M := ↥((range ι)ᶜ : Set X)) (n := n)
      ((TopPair.ofSubset (X := TopCat.of X) (range ι)ᶜ).singularHomologyδ R (n + 1) n rfl γ) := by
  refine (isFundamentalClass_iff _).2 fun z ↦ ?_
  -- A collar of the inclusion of the boundary `∂X = f(N)`.
  have hD : range f = (range ι)ᶜ := by rw [hιf, compl_compl]
  obtain ⟨c, hc⟩ := isCollared_iff.1
    (hD ▸ hf.subtypeVal_range : IsCollared (Subtype.val : ↥((range ι)ᶜ : Set X) → X))
  -- The interior point `p = c (z, 1 / 2)` of the collar.
  have hp : c (z, CollarModel.half) ∈ range ι := by
    simpa using CollarModel.apply_half_notMem hc z
  have houter : TopPair.singularHomologyMap
      (TopTriple.outerPair.map (CollarModel.boundaryTripleMap hc z)) R (n + 1) =
      localHomologyRestriction R (singleton_subset_iff.2 hp) (n + 1) := by
    rw [localHomologyRestriction_def]
    exact congrArg (TopPair.singularHomologyMap · _ _)
      (TopPair.hom_ext_of_fst _ (TopPair.ofSubsetMap_fst _ _).symm)
  have key := (TopTriple.singularHomologyδ_eq_comp_singularHomologyπ
    (CollarModel.boundaryTriple z) R (n + 1) n).symm.trans
      (CollarModel.singularHomologyδ_boundaryTriple R hc z n)
  rw [houter] at key
  -- So the image of `∂γ` at `z` is the image of the local class of `γ` at `p` under
  -- `localHomologyIso`. The final step is up to definitional unfolding: the inner pair of
  -- `boundaryTriple z` is `TopPair.ofSubset ({z}ᶜ : Set ∂X)`, so its homology is the local homology
  -- of `∂X` at `z` (see `boundaryTripleInnerMap`), and the outer pair of `spaceTriple z` is
  -- `TopPair.ofSubset {p}ᶜ`, whose homology is the abbreviation `localHomology` at `p`.
  exact (congrArg (fun v ↦ Submodule.span Λ {v} = ⊤)
    ((singularHomologyToLocalHomology_eq_singularHomologyπ _ z _).trans
      (congrArg (fun φ ↦ φ.hom γ) key))).mpr
    ((ModuleCat.span_singleton_apply_eq_top_iff (CollarModel.localHomologyIso R hc z n).hom).2
      (hγ _ hp))

end Coefficients

/-! ### The boundary of the relative fundamental class -/

namespace HomologicalOrientation

variable {X M : Type} {N : Type*} [TopologicalSpace X] [TopologicalSpace N] {ι : M → X}
  {f : N → X} [TopologicalSpace M] [T2Space X] [CompactSpace X] [T2Space M] {E : Type}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [ChartedSpace E M] {n : ℕ}
  (o : HomologicalOrientation M E (n + 1)) (hn : finrank ℝ E = n + 1) (hι : IsOpenEmbedding ι)
  (hιf : range ι = (range f)ᶜ) (hf : IsCollared f)

/-- **The boundary of the relative fundamental class is a fundamental class of the boundary.**
Let `X` be a compact Hausdorff space containing an oriented `(n + 1)`-manifold `M` as an open
subset `ι(M)`, whose complement `∂X` is collared. The connecting morphism
`Hₙ₊₁(X, ∂X; ℤ) ⟶ Hₙ(∂X; ℤ)` sends the relative fundamental class `[X, ∂X]` to a fundamental class
of `∂X`: its image in the local homology `Hₙ(∂X, ∂X ∖ {z}; ℤ)` generates that group at every point
`z` of the boundary. -/
theorem isFundamentalClass_singularHomologyδ_fundamentalClassRel :
    IsFundamentalClass (M := ↥((range ι)ᶜ : Set X)) (n := n)
      ((TopPair.ofSubset (X := TopCat.of X) (range ι)ᶜ).singularHomologyδ
        (ModuleCat.of ℤ (ULift.{0} ℤ)) (n + 1) n rfl (o.fundamentalClassRel hn hι hιf hf)) :=
  isFundamentalClass_singularHomologyδ_of_forall_span_eq_top _ hιf hf fun _ hp ↦
    (isLocalOrientation_iff_span_eq_top _ _ _).1
      (o.isLocalOrientation_localHomologyRestriction_fundamentalClassRel hn hι hιf hf hp)

end HomologicalOrientation

end TauCeti
