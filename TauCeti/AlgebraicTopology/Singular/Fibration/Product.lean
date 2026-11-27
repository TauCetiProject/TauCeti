/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.ModuleCat.Flat.Homology
public import TauCeti.Algebra.Homology.Semisimple
public import TauCeti.AlgebraicTopology.Singular.Fibration.BaseRow
public import TauCeti.AlgebraicTopology.Singular.Kunneth.Relative

/-!
# The Serre spectral sequence of a product

Let `B` and `F` be topological spaces, `C ⊆ B` a relative CW complex with skeleta
`Xᵏ = skeletonLT C (k + 1)`, and `K` a field. The first projection `p : B × F ⟶ B`
(`CartesianMonoidalCategory.fst B F`) is the trivial fibration with fibre `F`. Its Serre spectral
sequence `TauCeti.TopCat.serreSpectralSequence C p K` is computed from that of the identity of `B`,
the spectral sequence of the skeletal filtration of `C`, by tensoring with the homology of `F`.

* **The cross product on the first page.** The preimages of the skeleta are `p⁻¹(Xᵏ) = Xᵏ × F`,
  and the relative cross product
  `H_k(Xᵏ, Xᵏ⁻¹; K) ⊗ H_q(F; K) ⟶ H_{k+q}(p⁻¹(Xᵏ), p⁻¹(Xᵏ⁻¹); K)`
  (`TauCeti.TopCat.singularHomologyCrossPreimageSkeletonPair`) is an isomorphism
  (`TauCeti.TopCat.isIso_singularHomologyCrossPreimageSkeletonPair`). By the relative Künneth
  theorem over a field (`TopCat.isIso_singularHomologyKunnethRel`) the relative Künneth map
  `⨁_{a + b = k + q} H_a(Xᵏ, Xᵏ⁻¹; K) ⊗ H_b(F; K) ⟶ H_{k+q}(Xᵏ × F, Xᵏ⁻¹ × F; K ⊗ K)` is an
  isomorphism, and only the summand `a = k` survives, since `H_a(Xᵏ, Xᵏ⁻¹; K) = 0` for `a ≠ k`
  (`TauCeti.isZero_singularHomology_skeletonPair_of_ne`,
  `TopCat.isIso_singularHomologyCrossRel_of_isZero`). The cross product on the skeleta is the
  relative cross product of nested subspaces `TopCat.singularHomologyCrossRelOfInclusion`.
* **The first page.** In the classical indexing, `E¹_{k,q}(p) ≅ E¹_{k,0}(𝟙 B) ⊗ H_q(F; K)`, where
  `E¹_{k,0}(𝟙 B) = H_k(Xᵏ, Xᵏ⁻¹; K)` is the `k`-th cellular chain group of `C`
  (`TauCeti.TopCat.serreSpectralSequenceFstFirstPageXIsoTensor`); its inverse is induced by the
  cross product (`TauCeti.TopCat.serreSpectralSequenceFstFirstPageXIsoTensor_inv`).
* **The first differential.** The first differential of the spectral sequence of a filtered space
  is the connecting map of the triple of three consecutive stages
  (`TauCeti.filteredSpaceSpectralSequence_first_page_d_eq`), which factors through the connecting
  map of a pair. The connecting map of the pair `(Xᵏ, Xᵏ⁻¹) × F` sends `a × b` to `∂a × b`, without
  a sign since the pair is the first factor
  (`TopCat.singularHomologyCrossRel_comp_singularHomologyδ`).
  So under the identifications of the first pages, `d¹(p) = d¹(𝟙 B) ⊗ H_q(F; K)`
  (`TauCeti.TopCat.d_comp_serreSpectralSequenceFstFirstPageXIsoTensor_hom`).
* **The second page.** Tensoring with the vector space `H_q(F; K)` is exact, so it commutes with the
  homology of the first page (`TauCeti.ModuleCat.preservesHomology_tensorRight`). For a CW
  complex `B` this gives
  `E²_{k,q}(p) ≅ E²_{k,0}(𝟙 B) ⊗ H_q(F; K) ≅ H_k(B; K) ⊗ H_q(F; K)`
  (`TauCeti.TopCat.serreSpectralSequenceFstSecondPageXIsoTensor`), the row `q = 0` of the spectral
  sequence of the skeletal filtration being the homology of `B`
  (`TauCeti.TopCat.serreSpectralSequenceIdSecondPageXIsoSingularHomology`).

The cross product takes values in homology with coefficients in `K ⊗ K`. The two spectral sequences
of `p` with coefficients in `K ⊗ K` and in `K` are identified by the isomorphism of spectral
sequences induced by the unitor `K ⊗ K ≅ K`
(`TauCeti.filteredSpaceSpectralSequenceCoefficientIso`), which commutes with the differentials.

The spectral sequences are indexed as in `TauCeti.filteredSpaceSpectralSequence`: the first page
is the page numbered `2`, the second page is the page numbered `3`, and the classical position
`(k, q)` is `(a, b) = (1 - q - 2k, k - 1)`.

## Main definitions

* `TauCeti.TopCat.singularHomologyCrossPreimageSkeletonPair`: the relative cross product
  `H_k(Xᵏ, Xᵏ⁻¹; K) ⊗ H_q(F; K) ⟶ H_{k+q}(p⁻¹(Xᵏ), p⁻¹(Xᵏ⁻¹); K)`.
* `TauCeti.TopCat.serreSpectralSequenceFstFirstPageXIsoTensor`:
  `E¹_{k,q}(p) ≅ E¹_{k,0}(𝟙 B) ⊗ H_q(F; K)`.
* `TauCeti.TopCat.serreSpectralSequenceFstSecondPageXIsoTensor`:
  `E²_{k,q}(p) ≅ H_k(B; K) ⊗ H_q(F; K)` for a CW complex `B`.

## Main results

* `TauCeti.TopCat.isIso_singularHomologyCrossPreimageSkeletonPair`: the cross product on the first
  page is an isomorphism.
* `TauCeti.TopCat.whiskerRight_singularHomologyπ_comp_singularHomologyCrossPreimageSkeletonPair`:
  on the image of an absolute class, the cross product on the first page is the absolute cross
  product.
* `TauCeti.TopCat.d_comp_serreSpectralSequenceFstFirstPageXIsoTensor_hom`: the first differential
  of the spectral sequence of `p` is that of the skeletal filtration of `B` tensored with
  `H_q(F; K)`.
* `TauCeti.TopCat.homologyπ_comp_serreSpectralSequenceFstSecondPageXIsoTensor_hom`: the second
  page identification sends the class of a cycle to the class of the corresponding cycle of the
  skeletal filtration of `B`, tensored with `H_q(F; K)`.

## References

* J.-P. Serre, *Homologie singulière des espaces fibrés. Applications*, Ann. of Math. 54 (1951),
  425–505, Chapter II.
* A. Hatcher,
  [*Spectral Sequences in Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/SSAT/SSch1.pdf),
  Chapter 1, Section 1.1 (the homology spectral sequence, and the product of a CW complex with a
  space).
* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 3.B, the relative cross product and the relative Künneth formula.
* E. H. Spanier, *Algebraic Topology*, Chapter 5, Section 3.
-/

public section

noncomputable section

universe u

open CategoryTheory Limits Set Topology Topology.RelCWComplex MonoidalCategory
  CartesianMonoidalCategory AlgebraicTopology

namespace TauCeti

namespace TopCat

/-! ### The relative cross product for nested subspaces over a field

Facts about the relative cross product `TopCat.singularHomologyCrossRelOfInclusion` of nested
subspaces with coefficients in a field `K`. -/

section Cross

variable {Y F : _root_.TopCat.{u}} {s t : Set Y} {s' t' : Set ↑(Y ⊗ F)} (K : Type u) [Field K]

/-- Over a field, the relative cross product of `(t, s)` with `F` in degree `k` is an isomorphism
when `(t, s)` has no relative homology outside degree `k`. -/
private lemma isIso_crossRelOfInclusion (hst : s ⊆ t) (hst' : s' ⊆ t')
    (hs : ∀ x, x ∈ s' ↔ fst Y F x ∈ s) (ht : ∀ x, x ∈ t' ↔ fst Y F x ∈ t) (k q n : ℕ)
    (h : k + q = n)
    (hz : ∀ a, a ≠ k → IsZero ((TopPair.ofInclusion hst).singularHomology (ModuleCat.of K K) a)) :
    IsIso (_root_.TopCat.singularHomologyCrossRelOfInclusion (ModuleCat.of K K) (ModuleCat.of K K)
      hst hst' hs ht k q n h) := by
  have := _root_.TopCat.isIso_singularHomologyCrossRel_of_isZero (_root_.TopCat.of t) F
    (Subtype.val ⁻¹' s) (ModuleCat.of K K) (ModuleCat.of K K) k q n h fun a ha ↦ (hz a ha).of_iso
      (TopPair.singularHomologyMapIso _ (TopPair.ofSubsetPreimageValIso hst) a)
  rw [_root_.TopCat.singularHomologyCrossRelOfInclusion_def]
  infer_instance

/-- The map induced on relative homology by the unitor `K ⊗ K ≅ K` of the coefficients. -/
private abbrev unitorHomologyMap (P : TopPair.{u}) (n : ℕ) :
    P.singularHomology (ModuleCat.of K K ⊗ ModuleCat.of K K) n ⟶
      P.singularHomology (ModuleCat.of K K) n :=
  HomologicalComplex.homologyMap (((SSetPair.chainComplexFunctor _).map
    (λ_ (ModuleCat.of K K)).hom).app (TopPair.toSSetPair.obj P)) n

/-- The relative cross product followed by the unitor of the coefficients only depends on the
subsets, not on how they are written. -/
private lemma crossRelOfInclusion_comp_unitorHomologyMap_congr {s₁ t₁ : Set Y}
    {s₁' t₁' : Set ↑(Y ⊗ F)} (hst : s ⊆ t) (hst' : s' ⊆ t') (hs : ∀ x, x ∈ s' ↔ fst Y F x ∈ s)
    (ht : ∀ x, x ∈ t' ↔ fst Y F x ∈ t) (hst₁ : s₁ ⊆ t₁) (hst₁' : s₁' ⊆ t₁')
    (hs₁ : ∀ x, x ∈ s₁' ↔ fst Y F x ∈ s₁) (ht₁ : ∀ x, x ∈ t₁' ↔ fst Y F x ∈ t₁) (e₁ : s = s₁)
    (e₂ : t = t₁) (e₁' : s' = s₁') (e₂' : t' = t₁') (a b n : ℕ) (h : a + b = n) :
    _root_.TopCat.singularHomologyCrossRelOfInclusion (ModuleCat.of K K) (ModuleCat.of K K) hst
        hst' hs ht a b n h ≫ unitorHomologyMap K (TopPair.ofInclusion hst') n =
      (eqToHom (congrArg (fun P : TopPair.{u} ↦ P.singularHomology (ModuleCat.of K K) a)
          (TopPair.ofInclusion_congr hst hst₁ e₁ e₂)) ▷ _) ≫
        _root_.TopCat.singularHomologyCrossRelOfInclusion (ModuleCat.of K K) (ModuleCat.of K K)
            hst₁ hst₁' hs₁ ht₁ a b n h ≫
          unitorHomologyMap K (TopPair.ofInclusion hst₁') n ≫
            eqToHom (congrArg (fun P : TopPair.{u} ↦ P.singularHomology (ModuleCat.of K K) n)
              (TopPair.ofInclusion_congr hst' hst₁' e₁' e₂')).symm := by
  subst e₁ e₂ e₁' e₂'
  simp

end Cross

/-! ### Change of coefficients -/

section Coefficients

variable (K : Type u) [Field K] {Y : _root_.TopCat.{u}} {X : ℤ → Set Y} (hX : Monotone X)

/-- The isomorphism of spectral sequences of a filtered space induced by the unitor `K ⊗ K ≅ K` of
the coefficients, with its source written with coefficients in `K ⊗ K`. -/
private abbrev unitorSpectralSequenceIso :
    filteredSpaceSpectralSequence (ModuleCat.of K K ⊗ ModuleCat.of K K) hX ≅
      filteredSpaceSpectralSequence (ModuleCat.of K K) hX :=
  filteredSpaceSpectralSequenceCoefficientIso hX (λ_ (ModuleCat.of K K))

/-- The component on the first page of `unitorSpectralSequenceIso`. -/
private def unitorPageTwoXIso (pq : ℤ × ℤ) :
    ((filteredSpaceSpectralSequence (ModuleCat.of K K ⊗ ModuleCat.of K K) hX).page 2).X pq ≅
      ((filteredSpaceSpectralSequence (ModuleCat.of K K) hX).page 2).X pq :=
  (HomologicalComplex.eval _ _ pq).mapIso
    ((SpectralSequence.pageFunctor _ _ _ 2).mapIso (unitorSpectralSequenceIso K hX))

/-- `unitorPageTwoXIso` is the component of the morphism of spectral sequences induced by the
unitor. -/
private lemma unitorPageTwoXIso_hom (pq : ℤ × ℤ) :
    (unitorPageTwoXIso K hX pq).hom =
      ((filteredSpaceSpectralSequenceCoefficientMap hX (λ_ (ModuleCat.of K K)).hom).hom 2).f
        pq := by
  simp [unitorPageTwoXIso]

/-- The inverse of `unitorPageTwoXIso` is the component of the morphism of spectral sequences
induced by the inverse unitor. -/
private lemma unitorPageTwoXIso_inv (pq : ℤ × ℤ) :
    (unitorPageTwoXIso K hX pq).inv = ((unitorSpectralSequenceIso K hX).inv.hom 2).f pq := by
  simp [unitorPageTwoXIso]

end Coefficients

/-! ### The first page -/

section SpectralSequence

variable {B : _root_.TopCat.{u}} [T2Space B] {C D : Set B} [RelCWComplex C D]
  (F : _root_.TopCat.{u}) (K : Type u) [Field K]

/-- A point of `B × F` lies over the `b`-skeleton exactly when its first coordinate does. -/
private lemma mem_preimageSkeleton_fst_iff (b : ℤ) (x : ↑(B ⊗ F)) :
    x ∈ preimageSkeleton C (fst B F) b ↔ fst B F x ∈ preimageSkeleton C (𝟙 B) b :=
  (mem_preimageSkeleton_iff _ _ _).trans (mem_preimageSkeleton_iff (C := C) (𝟙 B) b _).symm

/-- The relative homology `Hₙ(Xᵇ, Xᵇ⁻¹; K)` of consecutive stages of the skeletal filtration of the
base vanishes for `n ≠ b`. -/
private lemma isZero_singularHomology_preimageSkeleton_id (a b : ℤ) (hab : b = a + 1) (n : ℕ)
    (hn : (n : ℤ) ≠ b) :
    IsZero ((TopPair.ofInclusion (monotone_preimageSkeleton (C := C) (𝟙 B)
      (by lia : a ≤ b))).singularHomology (ModuleCat.of K K) n) := by
  subst hab
  exact (isZero_serreSpectralSequence_id_page_two_X K (-(n : ℤ) - a, a) (by dsimp; lia)).of_iso
    (filteredSpaceSpectralSequenceFirstPageXIso _ _ (-(n : ℤ) - a, a) a (a + 1) rfl rfl _ rfl n
      (by dsimp; lia)).symm

variable (C) in
/-- **The cross product on the first page of the Serre spectral sequence of a product.** For the
first projection `p : B × F ⟶ B` and a relative CW complex `C ⊆ B` with skeleta `Xᵏ`, the relative
cross product `H_k(Xᵏ, Xᵏ⁻¹; K) ⊗ H_q(F; K) ⟶ Hₙ(p⁻¹(Xᵏ), p⁻¹(Xᵏ⁻¹); K)`, for `k + q = n`: the
relative cross product `TopCat.singularHomologyCrossRel` of the pair `(Xᵏ, Xᵏ⁻¹)` with `F`, read on
`p⁻¹(Xᵏ) = Xᵏ × F`, followed by the unitor `K ⊗ K ≅ K` of the coefficients. Its source is the
first page of the Serre spectral sequence of the identity of `B` at the classical position `(k, 0)`,
tensored with `H_q(F; K)`, and its target that of `p` at `(k, q)`. -/
def singularHomologyCrossPreimageSkeletonPair (k q n : ℕ) (h : k + q = n) :
    (preimageSkeletonPair (𝟙 B) C k).singularHomology (ModuleCat.of K K) k ⊗
        ((singularHomologyFunctor _ q).obj (ModuleCat.of K K)).obj F ⟶
      (preimageSkeletonPair (fst B F) C k).singularHomology (ModuleCat.of K K) n :=
  _root_.TopCat.singularHomologyCrossRelOfInclusion (ModuleCat.of K K) (ModuleCat.of K K)
      (preimage_mono (f := 𝟙 B) (skeletonLT_subset_skeletonLT_succ C k))
      (preimage_mono (f := fst B F) (skeletonLT_subset_skeletonLT_succ C k)) (fun _ ↦ Iff.rfl)
      (fun _ ↦ Iff.rfl) k q n h ≫
    unitorHomologyMap K (preimageSkeletonPair (fst B F) C k) n

/-- **The cross product on the first page is an isomorphism.** Over a field, the relative cross
product `H_k(Xᵏ, Xᵏ⁻¹; K) ⊗ H_q(F; K) ⟶ H_{k+q}(p⁻¹(Xᵏ), p⁻¹(Xᵏ⁻¹); K)` is an isomorphism: it is a
summand of the relative Künneth isomorphism, whose other summands vanish since
`H_a(Xᵏ, Xᵏ⁻¹; K) = 0` for `a ≠ k`. -/
instance isIso_singularHomologyCrossPreimageSkeletonPair (k q n : ℕ) (h : k + q = n) :
    IsIso (singularHomologyCrossPreimageSkeletonPair C F K k q n h) := by
  have := isIso_crossRelOfInclusion K
    (preimage_mono (f := 𝟙 B) (skeletonLT_subset_skeletonLT_succ C k))
    (preimage_mono (f := fst B F) (skeletonLT_subset_skeletonLT_succ C k)) (fun _ ↦ Iff.rfl)
    (fun _ ↦ Iff.rfl) k q n h fun a ha ↦
      isZero_singularHomology_skeletonPair_of_ne C (ModuleCat.of K K) ha
  unfold singularHomologyCrossPreimageSkeletonPair
  infer_instance

/-- **The cross product on the first page of an absolute class.** The relative cross product
`H_k(Xᵏ, Xᵏ⁻¹; K) ⊗ H_q(F; K) ⟶ Hₙ(p⁻¹(Xᵏ), p⁻¹(Xᵏ⁻¹); K)` of the image of a class of `H_k(Xᵏ; K)`
is the absolute cross product, carried to `p⁻¹(Xᵏ)` by `Xᵏ × F ≅ p⁻¹(Xᵏ)`, mapped to relative
homology, and followed by the unitor `K ⊗ K ≅ K` of the coefficients. -/
@[reassoc]
lemma whiskerRight_singularHomologyπ_comp_singularHomologyCrossPreimageSkeletonPair (k q n : ℕ)
    (h : k + q = n) :
    ((preimageSkeletonPair (𝟙 B) C k).singularHomologyπ (ModuleCat.of K K) k ▷
        ((singularHomologyFunctor _ q).obj (ModuleCat.of K K)).obj F) ≫
      singularHomologyCrossPreimageSkeletonPair C F K k q n h =
    _root_.TopCat.singularHomologyCross (preimageSkeletonPair (𝟙 B) C k).fst F (ModuleCat.of K K)
        (ModuleCat.of K K) k q n h ≫
      ((singularHomologyFunctor _ n).obj _).map
        (_root_.TopCat.prodPreimageFstIso B F (skeletonLT C ((k + 1 : ℕ) : ℕ∞))).hom ≫
        (preimageSkeletonPair (fst B F) C k).singularHomologyπ _ n ≫
          HomologicalComplex.homologyMap (((SSetPair.chainComplexFunctor _).map
            (λ_ (ModuleCat.of K K)).hom).app
              (TopPair.toSSetPair.obj (preimageSkeletonPair (fst B F) C k))) n := by
  -- `TopCat.singularHomologyCrossRelOfInclusion` carries `Xᵏ × F` to `p⁻¹(Xᵏ)` by
  -- `(x, y) ↦ (x, y)`, which is `prodPreimageFstIso` as both have the same coordinates.
  have he : _root_.TopCat.prodSubspaceMap F (t := skeletonLT C ((k + 1 : ℕ) : ℕ∞))
      (t' := fst B F ⁻¹' skeletonLT C ((k + 1 : ℕ) : ℕ∞)) (fun _ ↦ Iff.rfl) =
        (_root_.TopCat.prodPreimageFstIso B F (skeletonLT C ((k + 1 : ℕ) : ℕ∞))).hom := by
    ext x
    rw [_root_.TopCat.prodSubspaceMap_apply]
    exact (ConcreteCategory.congr_hom
      (_root_.TopCat.prodPreimageFstIso_hom_comp_map B F (skeletonLT C ((k + 1 : ℕ) : ℕ∞))) x).symm
  rw [← he]
  -- The proofs of membership carried by the subspaces have types that differ up to unfolding of
  -- `𝟙 B`, so the lemma for the cross product is applied with `exact` rather than `rw`.
  exact (_root_.TopCat.whiskerRight_singularHomologyπ_comp_singularHomologyCrossRelOfInclusion_assoc
    (ModuleCat.of K K) (ModuleCat.of K K)
    (preimage_mono (f := 𝟙 B) (skeletonLT_subset_skeletonLT_succ C k))
    (preimage_mono (f := fst B F) (skeletonLT_subset_skeletonLT_succ C k)) (fun _ ↦ Iff.rfl)
    (fun _ ↦ Iff.rfl) k q n h _)

/-- The cross product on the stages `a ≤ b = a + 1` of the skeletal filtrations is an isomorphism
in degree `b`. -/
private lemma isIso_crossRelOfInclusion_preimageSkeleton (a b : ℤ) (hab : a ≤ b) (k q n : ℕ)
    (hk : b = k) (hb : b = a + 1) (hn : k + q = n) :
    IsIso (_root_.TopCat.singularHomologyCrossRelOfInclusion (ModuleCat.of K K) (ModuleCat.of K K)
      (monotone_preimageSkeleton (C := C) (𝟙 B) hab)
      (monotone_preimageSkeleton (C := C) (fst B F) hab) (mem_preimageSkeleton_fst_iff F a)
      (mem_preimageSkeleton_fst_iff F b) k q n hn) :=
  isIso_crossRelOfInclusion K _ _ _ _ k q n hn fun m hm ↦
    isZero_singularHomology_preimageSkeleton_id (C := C) K a b hb m (by lia)

/-- The first-page identification `E¹_{k,q}(fst; K ⊗ K) ≅ E¹_{k,0}(𝟙; K) ⊗ H_q(F; K)` through the
first-page identifications of both filtered spaces and the inverse of the cross product, with all
indices given together with equations. -/
private def auxIso (k q n : ℕ) (hn : k + q = n) (pq pq₀ : ℤ × ℤ) (a b : ℤ) (ha : a = pq.2)
    (hb : b = pq.2 + 1) (hk : b = k) (hm : pq.1 + pq.2 = -n) (ha₀ : a = pq₀.2)
    (hb₀ : b = pq₀.2 + 1) (hm₀ : pq₀.1 + pq₀.2 = -k) :
    ((filteredSpaceSpectralSequence (ModuleCat.of K K ⊗ ModuleCat.of K K)
        (monotone_preimageSkeleton (C := C) (fst B F))).page 2).X pq ≅
      ((serreSpectralSequence C (𝟙 B) K).page 2).X pq₀ ⊗
        ((singularHomologyFunctor _ q).obj (ModuleCat.of K K)).obj F :=
  filteredSpaceSpectralSequenceFirstPageXIso _ _ pq a b ha hb _ rfl n hm ≪≫
    (@asIso _ _ _ _ (_root_.TopCat.singularHomologyCrossRelOfInclusion (ModuleCat.of K K)
        (ModuleCat.of K K) (monotone_preimageSkeleton (C := C) (𝟙 B) (by lia))
        (monotone_preimageSkeleton (C := C) (fst B F) (by lia : a ≤ b))
        (mem_preimageSkeleton_fst_iff F a) (mem_preimageSkeleton_fst_iff F b) k q n hn)
      (isIso_crossRelOfInclusion_preimageSkeleton F K a b (by lia) k q n hk (by lia) hn)).symm ≪≫
    whiskerRightIso (filteredSpaceSpectralSequenceFirstPageXIso _ _ pq₀ a b ha₀ hb₀ _ rfl k
      hm₀).symm _

/-- `auxIso` only depends on the values of the indices. -/
private lemma auxIso_congr (k q n n' : ℕ) (hn : k + q = n) (hn' : k + q = n') (pq pq₀ : ℤ × ℤ)
    (a b a' b' : ℤ) (ha : a = pq.2) (hb : b = pq.2 + 1) (hk : b = k) (hm : pq.1 + pq.2 = -n)
    (ha₀ : a = pq₀.2) (hb₀ : b = pq₀.2 + 1) (hm₀ : pq₀.1 + pq₀.2 = -k) (ha' : a' = pq.2)
    (hb' : b' = pq.2 + 1) (hk' : b' = k) (hm' : pq.1 + pq.2 = -n') (ha₀' : a' = pq₀.2)
    (hb₀' : b' = pq₀.2 + 1) :
    auxIso (C := C) F K k q n hn pq pq₀ a b ha hb hk hm ha₀ hb₀ hm₀ =
      auxIso F K k q n' hn' pq pq₀ a' b' ha' hb' hk' hm' ha₀' hb₀' hm₀ := by
  obtain rfl : n = n' := by lia
  obtain rfl : a = a' := by lia
  obtain rfl : b = b' := by lia
  rfl

/-- The first-page identification of a filtered space only depends on the value of the total
degree `m`. -/
private lemma filteredSpaceSpectralSequenceFirstPageXIso_congr {Y : _root_.TopCat.{u}}
    {X : ℤ → Set Y} (R : ModuleCat.{u} K) (hX : Monotone X) (pq : ℤ × ℤ) (a b : ℤ)
    (ha : a = pq.2) (hb : b = pq.2 + 1) (m m' : ℤ) (hm : m = pq.1 + pq.2)
    (hm' : m' = pq.1 + pq.2) (n : ℕ) (hn : m = -n) (hn' : m' = -n) :
    filteredSpaceSpectralSequenceFirstPageXIso R hX pq a b ha hb m hm n hn =
      filteredSpaceSpectralSequenceFirstPageXIso R hX pq a b ha hb m' hm' n hn' := by
  subst hm hm'
  rfl

/-- With coefficients in `K ⊗ K`, the first differential of the spectral sequence of the product
corresponds under `auxIso` to the first differential of the skeletal filtration of the base,
tensored with `H_q(F; K)`. -/
private lemma auxIso_hom_d (k q : ℕ) (p b p₀ : ℤ) (hb : b = k) (hm : p + b = -(k + q + 1 : ℕ))
    (hm₀ : p₀ + b = -(k + 1 : ℕ)) :
    ((filteredSpaceSpectralSequence (ModuleCat.of K K ⊗ ModuleCat.of K K)
        (monotone_preimageSkeleton (C := C) (fst B F))).page 2).d (p, b) (p + 2, b - 1) ≫
      (auxIso F K k q (k + q) rfl (p + 2, b - 1) (p₀ + 2, b - 1) (b - 1) b rfl
        (by dsimp only; lia) hb (by dsimp only; lia) rfl (by dsimp only; lia)
        (by dsimp only; lia)).hom =
    (auxIso F K (k + 1) q (k + q + 1) (by lia) (p, b) (p₀, b) b (b + 1) rfl rfl (by lia)
        (by dsimp only; lia) rfl rfl (by dsimp only; lia)).hom ≫
      (((serreSpectralSequence C (𝟙 B) K).page 2).d (p₀, b) (p₀ + 2, b - 1) ▷ _) := by
  -- Both first differentials are connecting maps of triples, which the cross product intertwines.
  rw [filteredSpaceSpectralSequence_first_page_d_eq _ _ b p (k + q) hm,
    filteredSpaceSpectralSequence_first_page_d_eq _ _ b p₀ k hm₀]
  simp only [auxIso, Iso.trans_hom, Iso.symm_hom, asIso_inv, whiskerRightIso_hom, Category.assoc]
  rw [filteredSpaceSpectralSequenceFirstPageXIso_congr K _ _ (p + 2, b - 1) (b - 1) b _ _
      (p + 2 + (b - 1)) (p + b + 1) _ (by dsimp only; lia) _ _ (by lia),
    filteredSpaceSpectralSequenceFirstPageXIso_congr K _ _ (p₀ + 2, b - 1) (b - 1) b _ _
      (p₀ + 2 + (b - 1)) (p₀ + b + 1) _ (by dsimp only; lia) _ _ (by lia)]
  have hC := _root_.TopCat.whiskerRight_singularHomologyδ_comp_singularHomologyCrossRelOfInclusion
    (ModuleCat.of K K) (ModuleCat.of K K)
    (monotone_preimageSkeleton (C := C) (𝟙 B) (by lia : b - 1 ≤ b))
    (monotone_preimageSkeleton (C := C) (𝟙 B) (by lia : b ≤ b + 1))
    (monotone_preimageSkeleton (C := C) (fst B F) (by lia : b - 1 ≤ b))
    (monotone_preimageSkeleton (C := C) (fst B F) (by lia : b ≤ b + 1))
    (mem_preimageSkeleton_fst_iff F (b - 1)) (mem_preimageSkeleton_fst_iff F b)
    (mem_preimageSkeleton_fst_iff F (b + 1)) k q (k + q) rfl
  have i₁ := isIso_crossRelOfInclusion_preimageSkeleton (C := C) F K (b - 1) b (by lia) k q (k + q)
    hb (by lia) rfl
  have i₂ := isIso_crossRelOfInclusion_preimageSkeleton (C := C) F K b (b + 1) (by lia) (k + 1) q
    (k + q + 1) (by lia) rfl (by lia)
  have key := (Iso.eq_inv_comp (@asIso _ _ _ _ _ i₂)).2 ((Category.assoc _ _ _).symm.trans
    ((Iso.comp_inv_eq (@asIso _ _ _ _ _ i₁)).2 hC.symm))
  -- The first-page identifications and the cross products are indexed through equations between
  -- the indices, so their intermediate objects agree only up to unfolding: `simp` cannot apply
  -- `Category.assoc` to these composites and `rw [key]` finds no occurrence, so the steps are
  -- composed as terms.
  refine congrArg (_ ≫ ·) ?_
  refine ((Category.assoc _ _ _).trans (congrArg (_ ≫ ·) (Iso.inv_hom_id_assoc _ _))).trans ?_
  refine (Category.assoc _ _ _).symm.trans (((congrArg (· ≫ _) key).trans
    (Category.assoc _ _ _)).trans (congrArg (_ ≫ ·) ?_))
  exact (comp_whiskerRight (C := ModuleCat.{u} K) _ _ _).symm.trans
    ((congrArg (MonoidalCategory.whiskerRight (C := ModuleCat.{u} K) · _)
      (Iso.inv_hom_id_assoc _ _).symm).trans (comp_whiskerRight _ _ _))

variable (C) in
/-- **The first page of the Serre spectral sequence of a product.** For the first projection
`p : B × F ⟶ B` and a relative CW complex `C ⊆ B`, over a field `K`, the object of the first page
(numbered `2`) of the Serre spectral sequence of `p` at `pq = (a, b)`, with `b = k - 1` and
`a + b = -(q + k)`, is the object of the first page of the spectral sequence of the skeletal
filtration of `C` at `pq₀ = (a₀, b)`, with `a₀ + b = -k`, tensored with `H_q(F; K)`. In the
classical indexing this is `E¹_{k,q}(p) ≅ E¹_{k,0}(𝟙 B) ⊗ H_q(F; K)`; the inverse is induced by the
cross product (`TauCeti.TopCat.serreSpectralSequenceFstFirstPageXIsoTensor_inv`). -/
def serreSpectralSequenceFstFirstPageXIsoTensor (k q : ℕ) (pq : ℤ × ℤ) (hb : pq.2 = k - 1)
    (ha : pq.1 + pq.2 = -(q + k : ℕ)) (pq₀ : ℤ × ℤ) (hb₀ : pq₀.2 = k - 1)
    (ha₀ : pq₀.1 + pq₀.2 = -k) :
    ((serreSpectralSequence C (fst B F) K).page 2).X pq ≅
      ((serreSpectralSequence C (𝟙 B) K).page 2).X pq₀ ⊗
        ((singularHomologyFunctor _ q).obj (ModuleCat.of K K)).obj F :=
  (unitorPageTwoXIso K _ pq).symm ≪≫
    auxIso F K k q (k + q) rfl pq pq₀ pq.2 (pq.2 + 1) rfl rfl (by lia) (by lia) (by lia) (by lia)
      ha₀

/-- The inverse of the identification `E¹_{k,q}(p) ≅ E¹_{k,0}(𝟙 B) ⊗ H_q(F; K)` is the relative
cross product `TauCeti.TopCat.singularHomologyCrossPreimageSkeletonPair`, read through the
first-page identifications of both spectral sequences with the relative homology of consecutive
(preimages of) skeleta. -/
lemma serreSpectralSequenceFstFirstPageXIsoTensor_inv (k q : ℕ) (pq : ℤ × ℤ) (hb : pq.2 = k - 1)
    (ha : pq.1 + pq.2 = -(q + k : ℕ)) (pq₀ : ℤ × ℤ) (hb₀ : pq₀.2 = k - 1)
    (ha₀ : pq₀.1 + pq₀.2 = -k) :
    (serreSpectralSequenceFstFirstPageXIsoTensor C F K k q pq hb ha pq₀ hb₀ ha₀).inv =
      (((filteredSpaceSpectralSequenceFirstPageXIso (ModuleCat.of K K)
          (monotone_preimageSkeleton (C := C) (𝟙 B)) pq₀ pq₀.2 (pq₀.2 + 1) rfl rfl _ rfl k
            ha₀).hom ≫
          eqToHom (congrArg (fun P : TopPair.{u} ↦ P.singularHomology (ModuleCat.of K K) k)
            (ofInclusion_preimageSkeleton_eq_preimageSkeletonPair k pq₀.2 hb₀))) ▷ _) ≫
        singularHomologyCrossPreimageSkeletonPair C F K k q (k + q) rfl ≫
          eqToHom (congrArg (fun P : TopPair.{u} ↦ P.singularHomology (ModuleCat.of K K) (k + q))
            (ofInclusion_preimageSkeleton_eq_preimageSkeletonPair k pq.2 hb)).symm ≫
          (filteredSpaceSpectralSequenceFirstPageXIso (ModuleCat.of K K)
            (monotone_preimageSkeleton (C := C) (fst B F)) pq pq.2 (pq.2 + 1) rfl rfl _ rfl
              (k + q) (by lia)).inv := by
  obtain ⟨p, b⟩ := pq
  obtain ⟨p₀, b₀⟩ := pq₀
  dsimp only at hb ha hb₀ ha₀
  obtain rfl : b = b₀ := by lia
  have hN := filteredSpaceSpectralSequenceFirstPageXIso_hom_coefficient_naturality
    (monotone_preimageSkeleton (C := C) (fst B F)) (λ_ (ModuleCat.of K K)).hom (p, b) b (b + 1)
    rfl rfl _ rfl (k + q) (by dsimp only; lia)
  dsimp only at hN
  have key := (Iso.inv_comp_eq _).2 (((Iso.eq_comp_inv _).2 hN).trans (Category.assoc _ _ _))
  have hc := crossRelOfInclusion_comp_unitorHomologyMap_congr K
    (monotone_preimageSkeleton (C := C) (𝟙 B) (Int.le_add_one le_rfl : b ≤ b + 1))
    (monotone_preimageSkeleton (C := C) (fst B F) (Int.le_add_one le_rfl : b ≤ b + 1))
    (mem_preimageSkeleton_fst_iff F b) (mem_preimageSkeleton_fst_iff F (b + 1))
    (preimage_mono (f := 𝟙 B) (skeletonLT_subset_skeletonLT_succ C k))
    (preimage_mono (f := fst B F) (skeletonLT_subset_skeletonLT_succ C k)) (fun _ ↦ Iff.rfl)
    (fun _ ↦ Iff.rfl) (preimageSkeleton_eq_preimage_skeletonLT _ k b hb)
    (preimageSkeleton_add_one_eq_preimage_skeletonLT _ k b hb)
    (preimageSkeleton_eq_preimage_skeletonLT _ k b hb)
    (preimageSkeleton_add_one_eq_preimage_skeletonLT _ k b hb) k q (k + q) rfl
  simp only [serreSpectralSequenceFstFirstPageXIsoTensor, auxIso, Iso.trans_inv, Iso.symm_inv,
    whiskerRightIso_inv, asIso_hom, Category.assoc, unitorPageTwoXIso_hom]
  -- `key` comes from the coefficient naturality of the first-page identification, stated for the
  -- source `𝟙_ (ModuleCat K) ⊗ K` of the unitor, which is `K ⊗ K` only up to unfolding, so
  -- `rw [key]` finds no occurrence and the steps are composed as terms.
  refine Eq.trans ?_ (comp_whiskerRight_assoc (C := ModuleCat.{u} K) _ _ _ _).symm
  refine congrArg (_ ≫ ·) ?_
  refine (congrArg (_ ≫ ·) key).trans ?_
  -- `singularHomologyCrossPreimageSkeletonPair` is by definition the cross product followed by
  -- the unitor of the coefficients, so the two sides agree after reassociating.
  exact ((reassoc_of% hc) _).trans (congrArg (_ ≫ ·) (Category.assoc _ _ _).symm)

/-- **The first differential of the Serre spectral sequence of a product.** Under the
identifications `E¹_{k,q}(p) ≅ E¹_{k,0}(𝟙 B) ⊗ H_q(F; K)`, the first differential
`E¹_{k+1,q}(p) ⟶ E¹_{k,q}(p)` of the Serre spectral sequence of `p : B × F ⟶ B` is the first
differential of the spectral sequence of the skeletal filtration of `C`, the cellular boundary
map, tensored with `H_q(F; K)`. Here `pq = (a, k)` is the classical position `(k + 1, q)`. -/
@[reassoc]
theorem d_comp_serreSpectralSequenceFstFirstPageXIsoTensor_hom (k q : ℕ)
    (pq pq' pq₀ pq₀' : ℤ × ℤ) (hb : pq.2 = k) (ha : pq.1 + pq.2 = -(q + (k + 1) : ℕ))
    (hb₀ : pq₀.2 = k) (ha₀ : pq₀.1 + pq₀.2 = -(k + 1 : ℕ)) (h' : pq' = (pq.1 + 2, pq.2 - 1))
    (h₀' : pq₀' = (pq₀.1 + 2, pq₀.2 - 1)) :
    ((serreSpectralSequence C (fst B F) K).page 2).d pq pq' ≫
        (serreSpectralSequenceFstFirstPageXIsoTensor C F K k q pq' (by rw [h']; dsimp only; lia)
          (by rw [h']; dsimp only; lia) pq₀' (by rw [h₀']; dsimp only; lia)
          (by rw [h₀']; dsimp only; lia)).hom =
      (serreSpectralSequenceFstFirstPageXIsoTensor C F K (k + 1) q pq (by lia) ha pq₀ (by lia)
          ha₀).hom ≫
        (((serreSpectralSequence C (𝟙 B) K).page 2).d pq₀ pq₀' ▷ _) := by
  obtain ⟨p, b⟩ := pq
  obtain ⟨p₀, b₀⟩ := pq₀
  dsimp only at hb ha hb₀ ha₀ h' h₀'
  subst h' h₀'
  obtain rfl : b = b₀ := by lia
  -- The identification passes to coefficients in `K ⊗ K` by an isomorphism of spectral
  -- sequences, which commutes with the differentials, and then is `auxIso`.
  have hφ := ((unitorSpectralSequenceIso K (monotone_preimageSkeleton (C := C)
    (fst B F))).inv.hom 2).comm (p, b) (p + 2, b - 1)
  have hA := auxIso_hom_d (C := C) F K k q p b p₀ hb (by lia) (by lia)
  simp only [serreSpectralSequenceFstFirstPageXIsoTensor, Iso.trans_hom, Iso.symm_hom,
    unitorPageTwoXIso_inv]
  rw [auxIso_congr F K k q (k + q) (k + q) rfl rfl _ _ (b - 1) (b - 1 + 1) (b - 1) b _ _ _ _ _ _ _
      rfl (by dsimp only; lia) (by lia) (by dsimp only; lia) rfl (by dsimp only; lia),
    auxIso_congr F K (k + 1) q (k + 1 + q) (k + q + 1) _ (by lia) _ _ b (b + 1) b (b + 1) _ _ _ _ _
      _ _ rfl rfl (by lia) (by dsimp only; lia) rfl rfl,
    ← reassoc_of% hφ, hA, Category.assoc]

end SpectralSequence

/-! ### The second page -/

section SecondPage

variable {B : _root_.TopCat.{u}} [T2Space B] [CWComplex (univ : Set B)] (F : _root_.TopCat.{u})
  (K : Type u) [Field K]

/-- The differential of the first page into `pq` starts at `(a - 2, b + 1)`. -/
private lemma up'_rel_two (pq : ℤ × ℤ) :
    (ComplexShape.up' ((2, 1 - 2) : ℤ × ℤ)).Rel (pq.1 - 2, pq.2 + 1) pq :=
  Prod.ext (by simp only [Prod.fst_add]; lia) (by simp only [Prod.snd_add]; lia)

/-- The differential of the first page out of `pq` ends at `(a + 2, b - 1)`. -/
private lemma up'_rel_two' (pq : ℤ × ℤ) :
    (ComplexShape.up' ((2, 1 - 2) : ℤ × ℤ)).Rel pq (pq.1 + 2, pq.2 - 1) :=
  Prod.ext (by simp only [Prod.fst_add]) (by simp only [Prod.snd_add]; lia)

/-- The identification of the first page at the target of the first differential out of the
column `k`; for `k = 0` both sides vanish. -/
private def thirdIso (q : ℕ) : (k : ℕ) → (pq pq₀ : ℤ × ℤ) → pq.2 = k - 1 → pq₀.2 = k - 1 →
    pq.1 + pq.2 = -(q + k : ℕ) → pq₀.1 + pq₀.2 = -k →
    (((serreSpectralSequence univ (fst B F) K).page 2).X (pq.1 + 2, pq.2 - 1) ≅
      ((serreSpectralSequence univ (𝟙 B) K).page 2).X (pq₀.1 + 2, pq₀.2 - 1) ⊗
        ((singularHomologyFunctor _ q).obj (ModuleCat.of K K)).obj F)
  | 0, _, _, hb, hb₀, _, _ =>
    IsZero.iso (isZero_serreSpectralSequence_page_two_X_of_snd_le_neg_two K univ _
      (by dsimp only; lia)) ((tensorRight _).map_isZero
        (isZero_serreSpectralSequence_page_two_X_of_snd_le_neg_two K univ _ (by dsimp only; lia)))
  | k + 1, _, _, hb, hb₀, ha, ha₀ =>
    serreSpectralSequenceFstFirstPageXIsoTensor univ F K k q _ (by dsimp only; lia)
      (by dsimp only; lia) _ (by dsimp only; lia) (by dsimp only; lia)

/-- The identification of the first page commutes with the first differential out of the column
`k`, including for `k = 0`. -/
private lemma d_comp_thirdIso_hom (q k : ℕ) (pq pq₀ : ℤ × ℤ) (hb : pq.2 = k - 1)
    (hb₀ : pq₀.2 = k - 1) (ha : pq.1 + pq.2 = -(q + k : ℕ)) (ha₀ : pq₀.1 + pq₀.2 = -k) :
    ((serreSpectralSequence univ (fst B F) K).page 2).d pq (pq.1 + 2, pq.2 - 1) ≫
        (thirdIso F K q k pq pq₀ hb hb₀ ha ha₀).hom =
      (serreSpectralSequenceFstFirstPageXIsoTensor univ F K k q pq hb ha pq₀ hb₀ ha₀).hom ≫
        (((serreSpectralSequence univ (𝟙 B) K).page 2).d pq₀ (pq₀.1 + 2, pq₀.2 - 1) ▷ _) := by
  cases k with
  | zero =>
    exact ((tensorRight _).map_isZero
      (isZero_serreSpectralSequence_page_two_X_of_snd_le_neg_two K univ _
        (by dsimp only; lia))).eq_of_tgt _ _
  | succ k =>
    exact d_comp_serreSpectralSequenceFstFirstPageXIsoTensor_hom (C := univ) (D := ∅) F K
      k q pq _ pq₀ _ (by lia) (by lia) (by lia) (by lia) rfl rfl

/-- The homology of the first page of the Serre spectral sequence of the product projection at
`(k, q)` is the homology of the first page of the skeletal filtration of `B` at `(k, 0)`, tensored
with `H_q(F; K)`. -/
private def pageTwoHomologyIso (k q : ℕ) (pq pq₀ : ℤ × ℤ) (hb : pq.2 = k - 1)
    (hb₀ : pq₀.2 = k - 1) (ha : pq.1 + pq.2 = -(q + k : ℕ)) (ha₀ : pq₀.1 + pq₀.2 = -k) :
    ((serreSpectralSequence univ (fst B F) K).page 2).homology pq ≅
      ((serreSpectralSequence univ (𝟙 B) K).page 2).homology pq₀ ⊗
        ((singularHomologyFunctor _ q).obj (ModuleCat.of K K)).obj F :=
  ((serreSpectralSequence univ (fst B F) K).page 2).homologyIsoSc' _ pq _
      ((ComplexShape.up' _).prev_eq' (up'_rel_two pq))
      ((ComplexShape.up' _).next_eq' (up'_rel_two' pq)) ≪≫
    ShortComplex.homologyMapIso (ShortComplex.isoMk
      (S₂ := (((serreSpectralSequence univ (𝟙 B) K).page 2).sc' (pq₀.1 - 2, pq₀.2 + 1) pq₀
        (pq₀.1 + 2, pq₀.2 - 1)).map (tensorRight _))
      (serreSpectralSequenceFstFirstPageXIsoTensor univ F K (k + 1) q (pq.1 - 2, pq.2 + 1)
        (by dsimp only; lia) (by dsimp only; lia) (pq₀.1 - 2, pq₀.2 + 1) (by dsimp only; lia)
        (by dsimp only; lia))
      (serreSpectralSequenceFstFirstPageXIsoTensor univ F K k q pq hb ha pq₀ hb₀ ha₀)
      (thirdIso F K q k pq pq₀ hb hb₀ ha ha₀)
      (d_comp_serreSpectralSequenceFstFirstPageXIsoTensor_hom (C := univ) (D := ∅) F K k q
        _ pq _ pq₀ (by dsimp only; lia) (by dsimp only; lia) (by dsimp only; lia)
        (by dsimp only; lia) (Prod.ext (by simp) (by simp)) (Prod.ext (by simp) (by simp))).symm
      (d_comp_thirdIso_hom F K q k pq pq₀ hb hb₀ ha ha₀).symm) ≪≫
    ShortComplex.mapHomologyIso _ (tensorRight _) ≪≫
    whiskerRightIso (((serreSpectralSequence univ (𝟙 B) K).page 2).homologyIsoSc' _ pq₀ _
      ((ComplexShape.up' _).prev_eq' (up'_rel_two pq₀))
      ((ComplexShape.up' _).next_eq' (up'_rel_two' pq₀))).symm _

/-- On the class of a cycle, `pageTwoHomologyIso` is the class of the corresponding cycle of the
first page of the skeletal filtration of `B`, tensored with `H_q(F; K)`. -/
private lemma homologyπ_comp_pageTwoHomologyIso_hom (k q : ℕ) (pq pq₀ : ℤ × ℤ)
    (hb : pq.2 = k - 1) (hb₀ : pq₀.2 = k - 1) (ha : pq.1 + pq.2 = -(q + k : ℕ))
    (ha₀ : pq₀.1 + pq₀.2 = -k)
    (c : ((serreSpectralSequence univ (fst B F) K).page 2).cycles pq ⟶
      ((serreSpectralSequence univ (𝟙 B) K).page 2).cycles pq₀ ⊗
        ((singularHomologyFunctor _ q).obj (ModuleCat.of K K)).obj F)
    (hc : c ≫ (((serreSpectralSequence univ (𝟙 B) K).page 2).iCycles pq₀ ▷ _) =
      ((serreSpectralSequence univ (fst B F) K).page 2).iCycles pq ≫
        (serreSpectralSequenceFstFirstPageXIsoTensor univ F K k q pq hb ha pq₀ hb₀ ha₀).hom) :
    ((serreSpectralSequence univ (fst B F) K).page 2).homologyπ pq ≫
        (pageTwoHomologyIso F K k q pq pq₀ hb hb₀ ha ha₀).hom =
      c ≫ (((serreSpectralSequence univ (𝟙 B) K).page 2).homologyπ pq₀ ▷ _) := by
  simp only [pageTwoHomologyIso, Iso.trans_hom, Iso.symm_hom, whiskerRightIso_hom,
    HomologicalComplex.π_homologyIsoSc'_hom_assoc, ShortComplex.homologyMapIso_hom,
    ShortComplex.homologyπ_naturality_assoc, ShortComplex.homologyπ_comp_mapHomologyIso_hom_assoc,
    Functor.flip_obj_map, curriedTensor_map_app]
  rw [← comp_whiskerRight, HomologicalComplex.π_homologyIsoSc'_inv, comp_whiskerRight]
  simp only [← Category.assoc]
  refine congrArg (· ≫ _) ?_
  -- Tensoring with `H_q(F; K)` preserves monomorphisms, so the cycles are compared after the
  -- inclusion into the first page.
  have : Mono (((serreSpectralSequence univ (𝟙 B) K).page 2).iCycles pq₀ ▷
      ((singularHomologyFunctor _ q).obj (ModuleCat.of K K)).obj F) :=
    (tensorRight _).map_mono _
  have hi := ShortComplex.mapCyclesIso_hom_iCycles
    (((serreSpectralSequence univ (𝟙 B) K).page 2).sc' (pq₀.1 - 2, pq₀.2 + 1) pq₀
      (pq₀.1 + 2, pq₀.2 - 1))
    (tensorRight (((singularHomologyFunctor (ModuleCat.{u} K) q).obj (ModuleCat.of K K)).obj F))
  simp only [Functor.flip_obj_map, curriedTensor_map_app] at hi
  -- The page index `2 ≤ 2` is given explicitly, as its default argument fails inside `rw`.
  rw [← cancel_mono (((serreSpectralSequence univ (𝟙 B) K).page 2 le_rfl).iCycles pq₀ ▷ _), hc]
  simp only [Category.assoc, ← comp_whiskerRight, HomologicalComplex.cyclesIsoSc'_inv_iCycles, hi,
    ShortComplex.cyclesMap_i, ShortComplex.isoMk_hom_τ₂,
    HomologicalComplex.cyclesIsoSc'_hom_iCycles_assoc]

variable (B) in
/-- **The second page of the Serre spectral sequence of a product.** For the first projection
`p : B × F ⟶ B` over a CW complex `B` and a field `K`, the object at `pq = (a, b)`, with
`b = k - 1` and `a + b = -(q + k)`, of the second page (numbered `3`) of the Serre spectral
sequence of `p` is `H_k(B; K) ⊗ H_q(F; K)`. In the classical indexing this is
`E²_{k,q} ≅ H_k(B; K) ⊗ H_q(F; K)`. The first page of `p` is that of the skeletal filtration of
`B` tensored with `H_q(F; K)`, differentials included
(`TauCeti.TopCat.d_comp_serreSpectralSequenceFstFirstPageXIsoTensor_hom`); tensoring with a vector
space is exact, and the second page of the skeletal filtration is the homology of `B`
(`TauCeti.TopCat.serreSpectralSequenceIdSecondPageXIsoSingularHomology`). -/
def serreSpectralSequenceFstSecondPageXIsoTensor (k q : ℕ) (pq : ℤ × ℤ) (hb : pq.2 = k - 1)
    (ha : pq.1 + pq.2 = -(q + k : ℕ)) :
    ((serreSpectralSequence univ (fst B F) K).page 3).X pq ≅
      ((singularHomologyFunctor (ModuleCat.{u} K) k).obj (ModuleCat.of K K)).obj B ⊗
        ((singularHomologyFunctor _ q).obj (ModuleCat.of K K)).obj F :=
  ((serreSpectralSequence univ (fst B F) K).iso 2 3 pq).symm ≪≫
    pageTwoHomologyIso F K k q pq (pq.1 + q, pq.2) hb hb ha (by dsimp only; lia) ≪≫
    whiskerRightIso (((serreSpectralSequence univ (𝟙 B) K).iso 2 3 (pq.1 + q, pq.2)) ≪≫
      serreSpectralSequenceIdSecondPageXIsoSingularHomology K k (pq.1 + q, pq.2) hb
        (by dsimp only; lia)) _

variable (B) in
/-- **The second page of a product on the class of a cycle.** Let `z` be a cycle of the first page
of the Serre spectral sequence of `p : B × F ⟶ B` at the classical position `(k, q)`, and `c` the
map on cycles induced by `TauCeti.TopCat.serreSpectralSequenceFstFirstPageXIsoTensor`, landing in
the cycles of the first page of the skeletal filtration of `B` tensored with `H_q(F; K)`. Then
`TauCeti.TopCat.serreSpectralSequenceFstSecondPageXIsoTensor` sends the class of `z` on the second
page to the class of `c z` in `H_k(B; K) ⊗ H_q(F; K)`, through
`TauCeti.TopCat.serreSpectralSequenceIdSecondPageXIsoSingularHomology`. -/
lemma homologyπ_comp_serreSpectralSequenceFstSecondPageXIsoTensor_hom (k q : ℕ) (pq : ℤ × ℤ)
    (hb : pq.2 = k - 1) (ha : pq.1 + pq.2 = -(q + k : ℕ))
    (c : ((serreSpectralSequence univ (fst B F) K).page 2).cycles pq ⟶
      ((serreSpectralSequence univ (𝟙 B) K).page 2).cycles (pq.1 + q, pq.2) ⊗
        ((singularHomologyFunctor _ q).obj (ModuleCat.of K K)).obj F)
    (hc : c ≫ (((serreSpectralSequence univ (𝟙 B) K).page 2).iCycles (pq.1 + q, pq.2) ▷ _) =
      ((serreSpectralSequence univ (fst B F) K).page 2).iCycles pq ≫
        (serreSpectralSequenceFstFirstPageXIsoTensor univ F K k q pq hb ha (pq.1 + q, pq.2) hb
          (by dsimp only; lia)).hom) :
    ((serreSpectralSequence univ (fst B F) K).page 2).homologyπ pq ≫
        ((serreSpectralSequence univ (fst B F) K).iso 2 3 pq).hom ≫
          (serreSpectralSequenceFstSecondPageXIsoTensor B F K k q pq hb ha).hom =
      c ≫ ((((serreSpectralSequence univ (𝟙 B) K).page 2).homologyπ (pq.1 + q, pq.2) ≫
        ((serreSpectralSequence univ (𝟙 B) K).iso 2 3 (pq.1 + q, pq.2)).hom ≫
          (serreSpectralSequenceIdSecondPageXIsoSingularHomology K k (pq.1 + q, pq.2) hb
            (by dsimp only; lia)).hom) ▷ _) := by
  rw [serreSpectralSequenceFstSecondPageXIsoTensor, Iso.trans_hom, Iso.trans_hom, Iso.symm_hom,
    Iso.hom_inv_id_assoc, reassoc_of% homologyπ_comp_pageTwoHomologyIso_hom F K k q pq
      (pq.1 + q, pq.2) hb hb ha (by dsimp only; lia) c hc, whiskerRightIso_hom, Iso.trans_hom,
    comp_whiskerRight, comp_whiskerRight, comp_whiskerRight]

end SecondPage

end TopCat

end TauCeti
