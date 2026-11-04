/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Cohomology.UniversalCoefficient
public import TauCeti.AlgebraicTopology.Singular.ProdThomPair
public import TauCeti.Topology.VectorBundle.ThomClass
import TauCeti.Algebra.Category.ModuleCat.Biproducts
import TauCeti.AlgebraicTopology.Cohomology.MayerVietoris.Pair

/-!
# The Thom pair over finite unions of trivializing open sets

Let `E → B` be a real vector bundle with model fibre `F` of finite dimension `r`, and `E₀` the
complement of its zero section. For a subset `W` of the base, the Thom pair of the restriction of
`E` to `W` is the pair `(E|_W, E₀|_W)` of subspaces of the total space
(`TauCeti.thomPairOver`). Over the whole base it is the Thom pair `(E, E₀)`
(`TauCeti.thomPairOverUnivIso`).

Over a subset of the base set of a linear trivialization `e`, the trivialization identifies this
pair with the Thom pair `(W × F, W × (F ∖ {0}))` of the product bundle
(`Bundle.Trivialization.thomPairOverIso`, in `TauCeti.Topology.VectorBundle.ThomClass`), whose
relative homology vanishes below the rank. The
Mayer–Vietoris sequence of the two pairs over open sets `U` and `V`
(`TopCat.isZero_singularHomology_ofInclusion_union`) propagates this vanishing from `U`, `V` and
`U ∩ V` to `U ∪ V`. Since the intersection of an open set with a finite union of open sets is again
a finite union of open sets, induction on the number of sets shows that
`Hₙ(E|_W, E₀|_W) = 0` for `n < r` whenever `W` is a finite union of open sets each lying in the base
set of a linear trivialization (`TauCeti.isZero_singularHomology_thomPairOver_biUnion`). In
particular the relative homology of the Thom pair `(E, E₀)` vanishes below the rank over a compact
base (`TauCeti.isZero_singularHomology_thomPair_of_compactSpace`). The extension to arbitrary
bases, with exact filtered colimits of coefficients, is in
`TauCeti.Topology.VectorBundle.MayerVietoris.DirectedUnion`.

By the universal coefficient theorem, the finite-union vanishing also holds for relative
cohomology with projective chain coefficients
(`TauCeti.isZero_singularCohomology_thomPairOver_biUnion`). The arbitrary-base cohomology form is
in `TauCeti.Topology.VectorBundle.MayerVietoris.DirectedUnion`.

This vanishing drives the construction of Thom classes by Mayer–Vietoris over a finite
trivializing cover. For open sets `U` and `V` of the base, the Mayer–Vietoris sequence of the pairs
over `U` and over `V` in cohomology shows that a class over `U ∪ V` is determined by its
restrictions to `U` and `V` when `Hⁿ⁻¹(E|_{U ∩ V}, E₀|_{U ∩ V}) = 0`
(`TauCeti.singularCohomology_thomPairOver_union_ext`), and that classes over `U` and over `V`
which agree over `U ∩ V` glue to a class over `U ∪ V`
(`TauCeti.exists_singularCohomology_thomPairOver_union`). Over a single trivializing set, a class
in the top degree `r` is determined by its restrictions to the fibre pairs `(E_b, E_b ∖ {0})`
(`Bundle.Trivialization.singularCohomology_thomPairOver_ext`, in
`TauCeti.Topology.VectorBundle.ThomClass`). Since `Hʳ⁻¹` vanishes over finite
unions of trivializing open sets, induction on the number of sets gives the same over such a union
(`TauCeti.singularCohomology_thomPairOver_biUnion_ext`), and shows that classes over the sets
with the same restrictions to the fibres where two sets meet glue to a class over the union
(`TauCeti.exists_singularCohomology_thomPairOver_biUnion`).

These finite-union results are the input for Thom classes over an arbitrary base: the gluing over
arbitrary trivializing covers, and the Thom classes it produces, are in
`TauCeti.Topology.VectorBundle.MayerVietoris.DirectedUnion` and
`TauCeti.Topology.VectorBundle.Orientation.ThomClass`.

## Main results

* `TauCeti.isZero_singularHomology_thomPairOver_union`: the Mayer–Vietoris step from open sets
  `U` and `V` to `U ∪ V`.
* `TauCeti.isZero_singularHomology_thomPairOver_biUnion`: `Hₙ(E|_W, E₀|_W) = 0` for `n < r` over a
  finite union `W` of trivializing open sets.
* `TauCeti.isZero_singularHomology_thomPair_of_compactSpace`: `Hₙ(E, E₀) = 0` for `n < r` over a
  compact base, without a filtered-colimit hypothesis on coefficients.
* `TauCeti.isZero_singularCohomology_thomPairOver_biUnion`: `Hⁿ(E|_W, E₀|_W) = 0` for `n < r`
  over a finite union `W` of trivializing open sets, with projective chain coefficients.
* `TauCeti.singularCohomology_thomPairOver_union_ext`,
  `TauCeti.exists_singularCohomology_thomPairOver_union`: uniqueness and existence of classes over
  `U ∪ V` with given restrictions to the open sets `U` and `V`.
* `TauCeti.singularCohomology_thomPairOver_biUnion_ext`: over a finite union of trivializing open
  sets, a class in the top degree is determined on the fibres.
* `TauCeti.exists_singularCohomology_thomPairOver_biUnion`: classes over finitely many
  trivializing open sets agreeing on the fibres glue to a class over their union.

## References

* J. W. Milnor, J. D. Stasheff, *Characteristic Classes*, Annals of Mathematics Studies 76,
  Princeton (1974), §10, Lemma 10.3 and the proof of Theorem 10.4.
* A. Hatcher, *Algebraic Topology*, Section 4.D, Theorem 4D.10 and its proof.
-/

public section

noncomputable section

open Bundle CategoryTheory Limits Set Module

universe w v u

namespace Bundle.Trivialization

open TauCeti

variable {B : Type w} [TopologicalSpace B] {F : Type w} [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F] {E : B → Type w} [TopologicalSpace (TotalSpace F E)]
  [∀ b, AddCommMonoid (E b)] [∀ b, Module ℝ (E b)] (e : Trivialization F (π F E)) [e.IsLinear ℝ]
  {W : Set B} (hW : W ⊆ e.baseSet)
  {C : Type u} [Category.{v} C] [HasCoproducts.{w} C] [Abelian C] (R : C)

include hW in
/-- **The relative homology of the Thom pair over a trivializing set vanishes below the rank**:
for `W` contained in the base set of a linear trivialization, `Hₙ(E|_W, E₀|_W) = 0` for
`n < dim F`. -/
theorem isZero_singularHomology_thomPairOver {n : ℕ} (hn : n < finrank ℝ F) :
    IsZero ((thomPairOver F E W).singularHomology R n) :=
  (isZero_singularHomology_prodThomPair R W F hn).of_iso
    (asIso (TopPair.singularHomologyMap (e.thomPairOverIso ℝ hW).hom R n))

end Bundle.Trivialization

namespace TauCeti

variable {C : Type u} [Category.{v} C] [HasCoproducts.{w} C] [Abelian C] (R : C)

section Empty

variable {B : Type w} {F : Type*} {E : B → Type w} [∀ b, Zero (E b)]
  [TopologicalSpace (TotalSpace F E)]

/-- The relative homology of the Thom pair over the empty set vanishes. -/
private theorem isZero_singularHomology_thomPairOver_empty (n : ℕ) :
    IsZero ((thomPairOver F E ∅).singularHomology R n) := by
  rw [IsZero.iff_id_eq_zero, ← TopPair.singularHomologyMap_id]
  exact TopPair.singularHomologyMap_eq_zero_of_fac _ R
    (TopCat.ofHom (X := π F E ⁻¹' (∅ : Set B))
      (Y := ↥(π F E ⁻¹' (∅ : Set B) ∩ zeroSectionCompl F E))
      ⟨fun v ↦ v.2.elim, continuous_of_const fun v ↦ v.2.elim⟩) (by ext v; exact v.2.elim) n

end Empty

section Union

variable {B : Type w} [TopologicalSpace B] {F : Type*} [TopologicalSpace F] {E : B → Type w}
  [TopologicalSpace (TotalSpace F E)] [∀ b, Zero (E b)] [∀ b, TopologicalSpace (E b)]
  [FiberBundle F E] {U V : Set B}

/-- The four subspaces of the total space which the Mayer–Vietoris sequences of the Thom pairs over
open sets `U` and `V` of the base need to be open: the preimages of `U` and `V` are open in the
total space, hence in any subspace, and their traces on a subspace of nonzero vectors are the traces
of the preimages themselves. -/
private theorem isOpen_thomPairOver_mayerVietoris (hU : IsOpen U) (hV : IsOpen V) :
    IsOpen (((↑) : ↥(π F E ⁻¹' U ∪ π F E ⁻¹' V) → TotalSpace F E) ⁻¹' (π F E ⁻¹' U)) ∧
    IsOpen (((↑) : ↥(π F E ⁻¹' U ∪ π F E ⁻¹' V) → TotalSpace F E) ⁻¹' (π F E ⁻¹' V)) ∧
    IsOpen (((↑) : ↥(π F E ⁻¹' U ∩ zeroSectionCompl F E ∪ π F E ⁻¹' V ∩ zeroSectionCompl F E) →
      TotalSpace F E) ⁻¹' (π F E ⁻¹' U ∩ zeroSectionCompl F E)) ∧
    IsOpen (((↑) : ↥(π F E ⁻¹' U ∩ zeroSectionCompl F E ∪ π F E ⁻¹' V ∩ zeroSectionCompl F E) →
      TotalSpace F E) ⁻¹' (π F E ⁻¹' V ∩ zeroSectionCompl F E)) := by
  have hopen {W : Set B} (hW : IsOpen W) (T : Set (TotalSpace F E)) :
      IsOpen (((↑) : T → TotalSpace F E) ⁻¹' (π F E ⁻¹' W)) :=
    (hW.preimage (FiberBundle.continuous_proj F E)).preimage continuous_subtype_val
  have hopen₀ {W : Set B} (hW : IsOpen W) {T : Set (TotalSpace F E)}
      (hT : T ⊆ zeroSectionCompl F E) :
      IsOpen (((↑) : T → TotalSpace F E) ⁻¹' (π F E ⁻¹' W ∩ zeroSectionCompl F E)) := by
    convert hopen hW T using 1
    ext x
    simp [hT x.2]
  have hT : π F E ⁻¹' U ∩ zeroSectionCompl F E ∪ π F E ⁻¹' V ∩ zeroSectionCompl F E ⊆
      zeroSectionCompl F E := union_subset inter_subset_right inter_subset_right
  exact ⟨hopen hU _, hopen hV _, hopen₀ hU hT, hopen₀ hV hT⟩

/-- **The Mayer–Vietoris step for the Thom pair**: for open sets `U` and `V` of the base, if
`Hₙ(E|_U, E₀|_U)` and `Hₙ(E|_V, E₀|_V)` vanish, and so does `Hₙ₋₁(E|_{U ∩ V}, E₀|_{U ∩ V})` when
`n` is positive, then `Hₙ(E|_{U ∪ V}, E₀|_{U ∪ V})` vanishes. -/
theorem isZero_singularHomology_thomPairOver_union (hU : IsOpen U) (hV : IsOpen V) {n : ℕ}
    (hUn : IsZero ((thomPairOver F E U).singularHomology R n))
    (hVn : IsZero ((thomPairOver F E V).singularHomology R n))
    (hUVn : ∀ m, m + 1 = n → IsZero ((thomPairOver F E (U ∩ V)).singularHomology R m)) :
    IsZero ((thomPairOver F E (U ∪ V)).singularHomology R n) := by
  obtain ⟨hA, hB, hC, hD⟩ := isOpen_thomPairOver_mayerVietoris (F := F) (E := E) hU hV
  have h := TopCat.isZero_singularHomology_ofInclusion_union R (X := TopCat.of (TotalSpace F E))
    (inter_subset_left : π F E ⁻¹' U ∩ zeroSectionCompl F E ⊆ π F E ⁻¹' U)
    (inter_subset_left : π F E ⁻¹' V ∩ zeroSectionCompl F E ⊆ π F E ⁻¹' V)
    hA hB hC hD (n := n) hUn hVn fun m hm ↦
      (TopPair.isZero_singularHomology_ofInclusion_congr R
        (inter_subset_left : π F E ⁻¹' (U ∩ V) ∩ zeroSectionCompl F E ⊆ π F E ⁻¹' (U ∩ V))
        (inter_subset_inter inter_subset_left inter_subset_left) preimage_inter
        (inter_inter_distrib_right _ _ _) m).1 (hUVn m hm)
  exact (TopPair.isZero_singularHomology_ofInclusion_congr R
    (union_subset_union inter_subset_left inter_subset_left)
    (inter_subset_left : π F E ⁻¹' (U ∪ V) ∩ zeroSectionCompl F E ⊆ π F E ⁻¹' (U ∪ V))
    preimage_union.symm (union_inter_distrib_right _ _ _).symm n).1 h

end Union

section Gluing

/-! ### Gluing classes over two open sets

The Mayer–Vietoris sequence of the pairs `(E|_U, E₀|_U)` and `(E|_V, E₀|_V)` in singular
cohomology (`TopCat.singularCohomologyPairMayerVietoris_exact₁` and
`TopCat.singularCohomologyPairMayerVietoris_exact₂`) is stated for the pairs
`(E|_U ∪ E|_V, E₀|_U ∪ E₀|_V)` and `(E|_U ∩ E|_V, E₀|_U ∩ E₀|_V)`, which are the Thom pairs over
`U ∪ V` and over `U ∩ V` written differently. -/

variable {B : Type w} {F : Type*} {E : B → Type w} [TopologicalSpace (TotalSpace F E)]
  [∀ b, Zero (E b)] {U V : Set B}

variable (F E U V) in
/-- The Thom pair over `U ∪ V`, as the union pair of the Mayer–Vietoris sequence of the Thom pairs
over `U` and over `V`. -/
private def thomPairOverUnionIso :
    TopPair.ofInclusion (X := TopCat.of (TotalSpace F E))
        (union_subset_union (inter_subset_left : π F E ⁻¹' U ∩ zeroSectionCompl F E ⊆ π F E ⁻¹' U)
          (inter_subset_left : π F E ⁻¹' V ∩ zeroSectionCompl F E ⊆ π F E ⁻¹' V)) ≅
      thomPairOver F E (U ∪ V) where
  hom := TopPair.ofHom (TopCat.ofHom (ContinuousMap.inclusion fun _ h ↦ h))
    (TopCat.ofHom (ContinuousMap.inclusion fun _ h ↦
      h.elim (fun h ↦ ⟨Or.inl h.1, h.2⟩) fun h ↦ ⟨Or.inr h.1, h.2⟩)) (by ext; rfl)
  inv := TopPair.ofHom (TopCat.ofHom (ContinuousMap.inclusion fun _ h ↦ h))
    (TopCat.ofHom (ContinuousMap.inclusion fun _ h ↦
      h.1.elim (fun h' ↦ Or.inl ⟨h', h.2⟩) fun h' ↦ Or.inr ⟨h', h.2⟩)) (by ext; rfl)
  hom_inv_id := TopPair.hom_ext_of_fst _ (TopCat.ext fun _ ↦ rfl)
  inv_hom_id := TopPair.hom_ext_of_fst _ (TopCat.ext fun _ ↦ rfl)

variable (F E U V) in
/-- The Thom pair over `U ∩ V`, as the intersection pair of the Mayer–Vietoris sequence of the Thom
pairs over `U` and over `V`. -/
private def thomPairOverInterIso :
    thomPairOver F E (U ∩ V) ≅
      TopPair.ofInclusion (X := TopCat.of (TotalSpace F E))
        (inter_subset_inter (inter_subset_left : π F E ⁻¹' U ∩ zeroSectionCompl F E ⊆ π F E ⁻¹' U)
          (inter_subset_left : π F E ⁻¹' V ∩ zeroSectionCompl F E ⊆ π F E ⁻¹' V)) where
  hom := TopPair.ofHom (TopCat.ofHom (ContinuousMap.inclusion fun _ h ↦ h))
    (TopCat.ofHom (ContinuousMap.inclusion fun _ h ↦ ⟨⟨h.1.1, h.2⟩, h.1.2, h.2⟩)) (by ext; rfl)
  inv := TopPair.ofHom (TopCat.ofHom (ContinuousMap.inclusion fun _ h ↦ h))
    (TopCat.ofHom (ContinuousMap.inclusion fun _ h ↦ ⟨⟨h.1.1, h.2.1⟩, h.1.2⟩)) (by ext; rfl)
  hom_inv_id := TopPair.hom_ext_of_fst _ (TopCat.ext fun _ ↦ rfl)
  inv_hom_id := TopPair.hom_ext_of_fst _ (TopCat.ext fun _ ↦ rfl)

/-- The restriction from the union pair of the Mayer–Vietoris sequence to the pair over `U` is the
restriction from `U ∪ V` to `U`. -/
private theorem ofInclusionMap_comp_thomPairOverUnionIso_hom_left :
    TopPair.ofInclusionMap _ _ (ContinuousMap.inclusion subset_union_left)
        (fun _ hx ↦ subset_union_left hx) ≫ (thomPairOverUnionIso F E U V).hom =
      thomPairOverMap F E (subset_union_left : U ⊆ U ∪ V) :=
  TopPair.hom_ext_of_fst _ (TopCat.ext fun v ↦ by
    -- `TopPair.Hom.fst` of a composite is the composite of the `fst` maps only up to unfolding.
    erw [CategoryTheory.comp_apply, TopPair.ofInclusionMap_fst_apply, thomPairOverMap_fst_apply]
    rfl)

/-- The restriction from the union pair of the Mayer–Vietoris sequence to the pair over `V` is the
restriction from `U ∪ V` to `V`. -/
private theorem ofInclusionMap_comp_thomPairOverUnionIso_hom_right :
    TopPair.ofInclusionMap _ _ (ContinuousMap.inclusion subset_union_right)
        (fun _ hx ↦ subset_union_right hx) ≫ (thomPairOverUnionIso F E U V).hom =
      thomPairOverMap F E (subset_union_right : V ⊆ U ∪ V) :=
  TopPair.hom_ext_of_fst _ (TopCat.ext fun v ↦ by
    -- `TopPair.Hom.fst` of a composite is the composite of the `fst` maps only up to unfolding.
    erw [CategoryTheory.comp_apply, TopPair.ofInclusionMap_fst_apply, thomPairOverMap_fst_apply]
    rfl)

/-- The restriction from the pair over `U ∩ V` to the pair over `U`, through the intersection pair
of the Mayer–Vietoris sequence. -/
private theorem thomPairOverInterIso_hom_comp_ofInclusionMap_left :
    (thomPairOverInterIso F E U V).hom ≫ TopPair.ofInclusionMap _ _
        (ContinuousMap.inclusion inter_subset_left) (fun _ hx ↦ inter_subset_left hx) =
      thomPairOverMap F E (inter_subset_left : U ∩ V ⊆ U) :=
  TopPair.hom_ext_of_fst _ (TopCat.ext fun v ↦ by
    -- `TopPair.Hom.fst` of a composite is the composite of the `fst` maps only up to unfolding.
    erw [CategoryTheory.comp_apply, TopPair.ofInclusionMap_fst_apply, thomPairOverMap_fst_apply]
    rfl)

/-- The restriction from the pair over `U ∩ V` to the pair over `V`, through the intersection pair
of the Mayer–Vietoris sequence. -/
private theorem thomPairOverInterIso_hom_comp_ofInclusionMap_right :
    (thomPairOverInterIso F E U V).hom ≫ TopPair.ofInclusionMap _ _
        (ContinuousMap.inclusion inter_subset_right) (fun _ hx ↦ inter_subset_right hx) =
      thomPairOverMap F E (inter_subset_right : U ∩ V ⊆ V) :=
  TopPair.hom_ext_of_fst _ (TopCat.ext fun v ↦ by
    -- `TopPair.Hom.fst` of a composite is the composite of the `fst` maps only up to unfolding.
    erw [CategoryTheory.comp_apply, TopPair.ofInclusionMap_fst_apply, thomPairOverMap_fst_apply]
    rfl)

variable {R} {k : Type*} [Ring k] [Linear k C] {M : C}

variable (R k M F E U V) in
/-- The first map of the Mayer–Vietoris sequence of the Thom pairs over `U` and over `V`, from the
cohomology of the Thom pair over `U ∪ V`. -/
private abbrev thomPairOverToBiprod (n : ℕ) :
    (thomPairOver F E (U ∪ V)).singularCohomology R k M n ⟶
      (thomPairOver F E U).singularCohomology R k M n ⊞
        (thomPairOver F E V).singularCohomology R k M n :=
  TopPair.singularCohomologyMap (thomPairOverUnionIso F E U V).hom n ≫
    TopCat.singularCohomologyPairMayerVietorisToBiprod R k M (X := TopCat.of (TotalSpace F E))
      (inter_subset_left : π F E ⁻¹' U ∩ zeroSectionCompl F E ⊆ π F E ⁻¹' U)
      (inter_subset_left : π F E ⁻¹' V ∩ zeroSectionCompl F E ⊆ π F E ⁻¹' V) n

/-- The first component of the Mayer–Vietoris map is the restriction from `U ∪ V` to `U`. -/
private theorem thomPairOverToBiprod_fst (n : ℕ) :
    thomPairOverToBiprod R F E U V k M n ≫ biprod.fst =
      TopPair.singularCohomologyMap (thomPairOverMap F E subset_union_left) n := by
  rw [Category.assoc, TopCat.singularCohomologyPairMayerVietorisToBiprod_fst,
    ← TopPair.singularCohomologyMap_comp, ofInclusionMap_comp_thomPairOverUnionIso_hom_left]

/-- The second component of the Mayer–Vietoris map is the restriction from `U ∪ V` to `V`. -/
private theorem thomPairOverToBiprod_snd (n : ℕ) :
    thomPairOverToBiprod R F E U V k M n ≫ biprod.snd =
      TopPair.singularCohomologyMap (thomPairOverMap F E subset_union_right) n := by
  rw [Category.assoc, TopCat.singularCohomologyPairMayerVietorisToBiprod_snd,
    ← TopPair.singularCohomologyMap_comp, ofInclusionMap_comp_thomPairOverUnionIso_hom_right]

/-- The second map of the Mayer–Vietoris sequence of the Thom pairs over `U` and over `V`, read in
the cohomology of the Thom pair over `U ∩ V`, sends `(a, b)` to the difference of the restrictions
of `a` and `b` to `U ∩ V`. -/
private theorem singularCohomologyPairMayerVietorisFromBiprod_thomPairOverInterIso (n : ℕ) :
    TopCat.singularCohomologyPairMayerVietorisFromBiprod R k M (X := TopCat.of (TotalSpace F E))
        (inter_subset_left : π F E ⁻¹' U ∩ zeroSectionCompl F E ⊆ π F E ⁻¹' U)
        (inter_subset_left : π F E ⁻¹' V ∩ zeroSectionCompl F E ⊆ π F E ⁻¹' V) n ≫
          TopPair.singularCohomologyMap (thomPairOverInterIso F E U V).hom n =
      biprod.desc (TopPair.singularCohomologyMap (thomPairOverMap F E inter_subset_left) n)
        (-TopPair.singularCohomologyMap (thomPairOverMap F E inter_subset_right) n) := by
  refine biprod.hom_ext' _ _ ?_ ?_
  · rw [TopCat.inl_singularCohomologyPairMayerVietorisFromBiprod_assoc,
      ← TopPair.singularCohomologyMap_comp, thomPairOverInterIso_hom_comp_ofInclusionMap_left,
      biprod.inl_desc]
  · rw [TopCat.inr_singularCohomologyPairMayerVietorisFromBiprod_assoc, Preadditive.neg_comp,
      ← TopPair.singularCohomologyMap_comp, thomPairOverInterIso_hom_comp_ofInclusionMap_right,
      biprod.inr_desc]

variable [TopologicalSpace B] [∀ b, TopologicalSpace (E b)] [TopologicalSpace F] [FiberBundle F E]

/-- **Classes over `U ∪ V` are determined by their restrictions to `U` and to `V`** when
`Hⁿ⁻¹(E|_{U ∩ V}, E₀|_{U ∩ V})` vanishes (or `n = 0`): this is exactness of the Mayer–Vietoris
sequence of the Thom pairs over the open sets `U` and `V` at `Hⁿ(E|_{U ∪ V}, E₀|_{U ∪ V})`. -/
theorem singularCohomology_thomPairOver_union_ext (hU : IsOpen U) (hV : IsOpen V) {n : ℕ}
    (hUV : ∀ m, m + 1 = n → IsZero ((thomPairOver F E (U ∩ V)).singularCohomology R k M m))
    {x y : (thomPairOver F E (U ∪ V)).singularCohomology R k M n}
    (hxyU : TopPair.singularCohomologyMap (thomPairOverMap F E subset_union_left) n x =
      TopPair.singularCohomologyMap (thomPairOverMap F E subset_union_left) n y)
    (hxyV : TopPair.singularCohomologyMap (thomPairOverMap F E subset_union_right) n x =
      TopPair.singularCohomologyMap (thomPairOverMap F E subset_union_right) n y) : x = y := by
  obtain ⟨hA, hB, hC, hD⟩ := isOpen_thomPairOver_mayerVietoris (F := F) (E := E) hU hV
  -- The first map of the Mayer–Vietoris sequence is injective in degree `n`.
  have hmono : Mono (thomPairOverToBiprod R F E U V k M n) := by
    have : IsIso (TopPair.singularCohomologyMap (R := R) (k := k) (M := M)
        (thomPairOverUnionIso F E U V).hom n) :=
      (TopPair.singularCohomologyFunctor R k M n).map_isIso (thomPairOverUnionIso F E U V).hom.op
    have : Mono (TopCat.singularCohomologyPairMayerVietorisToBiprod R k M
        (X := TopCat.of (TotalSpace F E))
        (inter_subset_left : π F E ⁻¹' U ∩ zeroSectionCompl F E ⊆ π F E ⁻¹' U)
        (inter_subset_left : π F E ⁻¹' V ∩ zeroSectionCompl F E ⊆ π F E ⁻¹' V) n) := by
      cases n with
      | zero =>
        exact TopCat.mono_singularCohomologyPairMayerVietorisToBiprod_zero R k M _ _ hA hB hC hD
      | succ m =>
        refine (TopCat.singularCohomologyPairMayerVietoris_exact₁ R k M _ _ hA hB hC hD m
          (m + 1)).mono_g (IsZero.eq_of_src ?_ _ _)
        exact (hUV m rfl).of_iso ((TopPair.singularCohomologyFunctor R k M m).mapIso
          (thomPairOverInterIso F E U V).op)
    exact mono_comp _ _
  -- Its two components are the restrictions to `U` and to `V`.
  refine (ModuleCat.mono_iff_injective _).1 hmono
    ((ModuleCat.mono_iff_injective (ModuleCat.biprodIsoProd _ _).hom).1 inferInstance ?_)
  rw [ModuleCat.biprodIsoProd_hom_apply, ModuleCat.biprodIsoProd_hom_apply]
  simp only [← ConcreteCategory.comp_apply, thomPairOverToBiprod_fst, thomPairOverToBiprod_snd,
    hxyU, hxyV]

/-- **Classes over `U` and over `V` that agree over `U ∩ V` glue to a class over `U ∪ V`**: this is
exactness of the Mayer–Vietoris sequence of the Thom pairs over the open sets `U` and `V` at
`Hⁿ(E|_U, E₀|_U) ⊞ Hⁿ(E|_V, E₀|_V)`. -/
theorem exists_singularCohomology_thomPairOver_union (hU : IsOpen U) (hV : IsOpen V) {n : ℕ}
    (a : (thomPairOver F E U).singularCohomology R k M n)
    (b : (thomPairOver F E V).singularCohomology R k M n)
    (hab : TopPair.singularCohomologyMap (thomPairOverMap F E inter_subset_left) n a =
      TopPair.singularCohomologyMap (thomPairOverMap F E inter_subset_right) n b) :
    ∃ x : (thomPairOver F E (U ∪ V)).singularCohomology R k M n,
      TopPair.singularCohomologyMap (thomPairOverMap F E subset_union_left) n x = a ∧
        TopPair.singularCohomologyMap (thomPairOverMap F E subset_union_right) n x = b := by
  obtain ⟨hA, hB, hC, hD⟩ := isOpen_thomPairOver_mayerVietoris (F := F) (E := E) hU hV
  let hCA : π F E ⁻¹' U ∩ zeroSectionCompl F E ⊆ π F E ⁻¹' U := inter_subset_left
  let hDB : π F E ⁻¹' V ∩ zeroSectionCompl F E ⊆ π F E ⁻¹' V := inter_subset_left
  let z := (biprod.inl : _ ⟶ _ ⊞ (thomPairOver F E V).singularCohomology R k M n) a +
    (biprod.inr : _ ⟶ (thomPairOver F E U).singularCohomology R k M n ⊞ _) b
  -- The pair `(a, b)` is in the kernel of the second map of the Mayer–Vietoris sequence, since its
  -- image there is the difference of the restrictions of `a` and `b` to `U ∩ V`.
  have hz : TopCat.singularCohomologyPairMayerVietorisFromBiprod R k M hCA hDB n z = 0 := by
    have : IsIso (TopPair.singularCohomologyMap (R := R) (k := k) (M := M)
        (thomPairOverInterIso F E U V).hom n) :=
      (TopPair.singularCohomologyFunctor R k M n).map_isIso (thomPairOverInterIso F E U V).hom.op
    refine (ModuleCat.mono_iff_injective (TopPair.singularCohomologyMap
      (thomPairOverInterIso F E U V).hom n)).1 inferInstance ?_
    rw [← ConcreteCategory.comp_apply,
      singularCohomologyPairMayerVietorisFromBiprod_thomPairOverInterIso]
    simp [z, ← ConcreteCategory.comp_apply, hab]
  obtain ⟨x, hx⟩ := (ShortComplex.moduleCat_exact_iff _).1
    (TopCat.singularCohomologyPairMayerVietoris_exact₂ R k M hCA hDB hA hB hC hD n) z hz
  -- A preimage of `(a, b)` under the first map of the Mayer–Vietoris sequence.
  have hι : thomPairOverToBiprod R F E U V k M n
      (TopPair.singularCohomologyMap (thomPairOverUnionIso F E U V).inv n x) = z := by
    simpa [← TopPair.singularCohomologyMap_comp_apply] using hx
  refine ⟨TopPair.singularCohomologyMap (thomPairOverUnionIso F E U V).inv n x, ?_, ?_⟩
  · rw [← thomPairOverToBiprod_fst, ConcreteCategory.comp_apply, hι]
    simp [z, ← ConcreteCategory.comp_apply]
  · rw [← thomPairOverToBiprod_snd, ConcreteCategory.comp_apply, hι]
    simp [z, ← ConcreteCategory.comp_apply]

end Gluing

variable {B : Type w} [TopologicalSpace B] {F : Type w} [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F] {E : B → Type w} [TopologicalSpace (TotalSpace F E)]
  [∀ b, AddCommMonoid (E b)] [∀ b, Module ℝ (E b)] [∀ b, TopologicalSpace (E b)] [FiberBundle F E]

/-- **The relative homology of the Thom pair over a finite union of trivializing open sets
vanishes below the rank**: if each of the finitely many open sets `W i`, `i ∈ s`, lies in the base
set of a linear trivialization, then `Hₙ(E|_W, E₀|_W) = 0` for `n < dim F`, where `W` is their
union. -/
theorem isZero_singularHomology_thomPairOver_biUnion {ι : Type*} (s : Finset ι) {W : ι → Set B}
    (hWo : ∀ i ∈ s, IsOpen (W i))
    (hWe : ∀ i ∈ s, ∃ (e : Trivialization F (π F E)) (_ : e.IsLinear ℝ), W i ⊆ e.baseSet)
    {n : ℕ} (hn : n < finrank ℝ F) :
    IsZero ((thomPairOver F E (⋃ i ∈ s, W i)).singularHomology R n) := by
  classical
  induction s using Finset.induction_on generalizing W n with
  | empty => simpa using isZero_singularHomology_thomPairOver_empty R n
  | insert a s ha ih =>
    rw [Finset.set_biUnion_insert]
    obtain ⟨e, _, he⟩ := hWe a (Finset.mem_insert_self a s)
    refine isZero_singularHomology_thomPairOver_union R (hWo a (Finset.mem_insert_self a s))
      (isOpen_iUnion fun i ↦ isOpen_iUnion fun hi ↦ hWo i (Finset.mem_insert_of_mem hi))
      (e.isZero_singularHomology_thomPairOver he R hn)
      (ih (fun i hi ↦ hWo i (Finset.mem_insert_of_mem hi))
        (fun i hi ↦ hWe i (Finset.mem_insert_of_mem hi)) hn) fun m hm ↦ ?_
    -- `W a ∩ ⋃ i ∈ s, W i` is the union of the trivializing open sets `W a ∩ W i`, `i ∈ s`.
    rw [inter_iUnion₂]
    refine ih (fun i hi ↦ (hWo a (Finset.mem_insert_self a s)).inter
      (hWo i (Finset.mem_insert_of_mem hi))) (fun i hi ↦ ?_) (by omega)
    obtain ⟨e', he', hi'⟩ := hWe i (Finset.mem_insert_of_mem hi)
    exact ⟨e', he', inter_subset_right.trans hi'⟩

/-- **The relative homology of the Thom pair of a vector bundle over a compact base vanishes below
the rank**: `Hₙ(E, E₀) = 0` for `n < dim F`. -/
theorem isZero_singularHomology_thomPair_of_compactSpace [CompactSpace B] [VectorBundle ℝ F E]
    {n : ℕ} (hn : n < finrank ℝ F) : IsZero ((thomPair F E).singularHomology R n) := by
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover
    (fun b : B ↦ (trivializationAt F E b).baseSet) (fun b ↦ (trivializationAt F E b).open_baseSet)
    fun b _ ↦ mem_iUnion.2 ⟨b, mem_baseSet_trivializationAt F E b⟩
  have h := isZero_singularHomology_thomPairOver_biUnion R t
    (fun b _ ↦ (trivializationAt F E b).open_baseSet)
    (fun b _ ↦ ⟨trivializationAt F E b, inferInstance, subset_rfl⟩) hn
  rw [univ_subset_iff.1 ht] at h
  exact h.of_iso (asIso (TopPair.singularHomologyMap (thomPairOverUnivIso F E).inv R n))

section Cohomology

variable {k : Type*} [CommRing k] (R' M' : ModuleCat.{w} k) [Module.Projective k R']

/-- **The relative cohomology of the Thom pair over a finite union of trivializing open sets
vanishes below the rank**: if each of the finitely many open sets `W i`, `i ∈ s`, lies in the base
set of a linear trivialization, then `Hⁿ(E|_W, E₀|_W; R, M) = 0` for `n < dim F`, where `W` is
their union and `R` is projective. -/
theorem isZero_singularCohomology_thomPairOver_biUnion {ι : Type*} (s : Finset ι)
    {W : ι → Set B} (hWo : ∀ i ∈ s, IsOpen (W i))
    (hWe : ∀ i ∈ s, ∃ (e : Trivialization F (π F E)) (_ : e.IsLinear ℝ), W i ⊆ e.baseSet)
    {n : ℕ} (hn : n < finrank ℝ F) :
    IsZero ((thomPairOver F E (⋃ i ∈ s, W i)).singularCohomology R' k M' n) :=
  TopPair.isZero_singularCohomology_of_isZero_singularHomology _ R' M' n fun _ hj ↦
    isZero_singularHomology_thomPairOver_biUnion R' s hWo hWe (hj.trans_lt hn)

end Cohomology

section TopDegree

variable {K : Type*} [CommRing K] {R' M' : ModuleCat.{w} K}

omit [NormedSpace ℝ F] [FiniteDimensional ℝ F] [∀ b, Module ℝ (E b)] in
/-- Restricting a class to a smaller set and then to a fibre is restricting it to the fibre. -/
private theorem singularCohomologyMap_fiberThomPairOverMap_thomPairOverMap {W W' : Set B}
    (h : W ⊆ W') {b : B} (hb : b ∈ W) {n : ℕ}
    (x : (thomPairOver F E W').singularCohomology R' K M' n) :
    TopPair.singularCohomologyMap (fiberThomPairOverMap F E hb) n
        (TopPair.singularCohomologyMap (thomPairOverMap F E h) n x) =
      TopPair.singularCohomologyMap (fiberThomPairOverMap F E (h hb)) n x := by
  rw [← TopPair.singularCohomologyMap_comp_apply, fiberThomPairOverMap_comp_thomPairOverMap]

omit [TopologicalSpace B] [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [∀ b, Module ℝ (E b)] [∀ b, TopologicalSpace (E b)] [FiberBundle F E] in
/-- Restricting a class to a smaller set and then to a still smaller one is restricting it to the
smallest set. -/
private theorem singularCohomologyMap_thomPairOverMap_thomPairOverMap {W W' W'' : Set B}
    (h : W ⊆ W') (h' : W' ⊆ W'') {n : ℕ}
    (x : (thomPairOver F E W'').singularCohomology R' K M' n) :
    TopPair.singularCohomologyMap (thomPairOverMap F E h) n
        (TopPair.singularCohomologyMap (thomPairOverMap F E h') n x) =
      TopPair.singularCohomologyMap (thomPairOverMap F E (h.trans h')) n x := by
  rw [← TopPair.singularCohomologyMap_comp_apply, thomPairOverMap_comp_thomPairOverMap]

omit [TopologicalSpace B] [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [∀ b, Module ℝ (E b)] [∀ b, TopologicalSpace (E b)] [FiberBundle F E] in
/-- Over two equal sets of the base, classes can be compared through the restriction map. -/
private theorem singularCohomology_thomPairOver_eq_of_eq {W W' : Set B} (hW : W = W') {n : ℕ}
    {x y : (thomPairOver F E W).singularCohomology R' K M' n}
    (h : TopPair.singularCohomologyMap (thomPairOverMap F E hW.ge) n x =
      TopPair.singularCohomologyMap (thomPairOverMap F E hW.ge) n y) : x = y := by
  subst hW
  simpa using h

variable [Module.Projective K R']

/-- **Classes over a finite union of trivializing open sets in the top degree are determined on
the fibres**: if each of the finitely many open sets `W i`, `i ∈ s`, lies in the base set of a
linear trivialization, then two classes of `Hʳ(E|_W, E₀|_W; R, M)`, where `W` is their union,
`r = dim F` and `R` is projective, whose restrictions to the fibre pair `(E_b, E_b ∖ {0})` over
every point `b ∈ W` agree, are equal. -/
theorem singularCohomology_thomPairOver_biUnion_ext {ι : Type*} (s : Finset ι) {W : ι → Set B}
    (hWo : ∀ i ∈ s, IsOpen (W i))
    (hWe : ∀ i ∈ s, ∃ (e : Trivialization F (π F E)) (_ : e.IsLinear ℝ), W i ⊆ e.baseSet)
    {u v : (thomPairOver F E (⋃ i ∈ s, W i)).singularCohomology R' K M' (finrank ℝ F)}
    (h : ∀ b (hb : b ∈ ⋃ i ∈ s, W i),
      TopPair.singularCohomologyMap (fiberThomPairOverMap F E hb) _ u =
        TopPair.singularCohomologyMap (fiberThomPairOverMap F E hb) _ v) : u = v := by
  classical
  induction s using Finset.induction_on generalizing W with
  | empty =>
    -- Over the empty set the Thom pair has no cohomology.
    refine (ModuleCat.subsingleton_of_isZero ?_).elim u v
    refine TopPair.isZero_singularCohomology_of_isZero_singularHomology _ R' M' _ fun j _ ↦ ?_
    simpa using isZero_singularHomology_thomPairOver_empty (E := E) R' j
  | insert a s ha ih =>
    revert u v
    rw [Finset.set_biUnion_insert]
    intro u v h
    have hs (i : ι) (hi : i ∈ s) : i ∈ insert a s := Finset.mem_insert_of_mem hi
    obtain ⟨e, _, he⟩ := hWe a (Finset.mem_insert_self a s)
    refine singularCohomology_thomPairOver_union_ext (hWo a (Finset.mem_insert_self a s))
      (isOpen_iUnion fun i ↦ isOpen_iUnion fun hi ↦ hWo i (hs i hi)) (fun m hm ↦ ?_) ?_ ?_
    · -- `W a ∩ ⋃ i ∈ s, W i` is the union of the trivializing open sets `W a ∩ W i`, `i ∈ s`.
      rw [inter_iUnion₂]
      refine isZero_singularCohomology_thomPairOver_biUnion R' M' s
        (fun i hi ↦ (hWo a (Finset.mem_insert_self a s)).inter (hWo i (hs i hi)))
        (fun i hi ↦ ?_) (by omega)
      obtain ⟨e', he', hi'⟩ := hWe i (hs i hi)
      exact ⟨e', he', inter_subset_right.trans hi'⟩
    · refine e.singularCohomology_thomPairOver_ext he fun b hb ↦ ?_
      rw [singularCohomologyMap_fiberThomPairOverMap_thomPairOverMap,
        singularCohomologyMap_fiberThomPairOverMap_thomPairOverMap, h]
    · refine ih (fun i hi ↦ hWo i (hs i hi)) (fun i hi ↦ hWe i (hs i hi)) fun b hb ↦ ?_
      rw [singularCohomologyMap_fiberThomPairOverMap_thomPairOverMap,
        singularCohomologyMap_fiberThomPairOverMap_thomPairOverMap, h]

/-- **Local classes agreeing on the fibres glue over a finite union of trivializing open sets**:
if each of the finitely many open sets `W i`, `i ∈ s`, lies in the base set of a linear
trivialization, and classes `u i ∈ Hʳ(E|_{W i}, E₀|_{W i}; R, M)`, `r = dim F` and `R` projective,
have the same restriction to the fibre pair `(E_b, E_b ∖ {0})` over every point `b` lying in two of
the sets, then there is a class over the union `W` of the `W i` restricting to each `u i`. By
`TauCeti.singularCohomology_thomPairOver_biUnion_ext` it is unique. -/
theorem exists_singularCohomology_thomPairOver_biUnion {ι : Type*} (s : Finset ι) {W : ι → Set B}
    (hWo : ∀ i ∈ s, IsOpen (W i))
    (hWe : ∀ i ∈ s, ∃ (e : Trivialization F (π F E)) (_ : e.IsLinear ℝ), W i ⊆ e.baseSet)
    (u : ∀ i, (thomPairOver F E (W i)).singularCohomology R' K M' (finrank ℝ F))
    (hu : ∀ i ∈ s, ∀ j ∈ s, ∀ b (hi : b ∈ W i) (hj : b ∈ W j),
      TopPair.singularCohomologyMap (fiberThomPairOverMap F E hi) _ (u i) =
        TopPair.singularCohomologyMap (fiberThomPairOverMap F E hj) _ (u j)) :
    ∃ x : (thomPairOver F E (⋃ i ∈ s, W i)).singularCohomology R' K M' (finrank ℝ F),
      ∀ i (hi : i ∈ s), TopPair.singularCohomologyMap
        (thomPairOverMap F E (Finset.subset_set_biUnion_of_mem hi)) _ x = u i := by
  classical
  induction s using Finset.induction_on generalizing W with
  | empty => exact ⟨0, fun i hi ↦ absurd hi (Finset.notMem_empty i)⟩
  | insert a s ha ih =>
    have ha' : a ∈ insert a s := Finset.mem_insert_self a s
    have hs (i : ι) (hi : i ∈ s) : i ∈ insert a s := Finset.mem_insert_of_mem hi
    have hSo : IsOpen (⋃ i ∈ s, W i) := isOpen_iUnion fun i ↦ isOpen_iUnion fun hi ↦ hWo i (hs i hi)
    obtain ⟨y, hy⟩ := ih (fun i hi ↦ hWo i (hs i hi)) (fun i hi ↦ hWe i (hs i hi)) u
      fun i hi j hj ↦ hu i (hs i hi) j (hs j hj)
    -- `u a` and `y` agree over `W a ∩ ⋃ i ∈ s, W i`, the union of the trivializing sets
    -- `W a ∩ W i`, since they agree on every fibre there.
    have hagree : TopPair.singularCohomologyMap (thomPairOverMap F E inter_subset_left) _ (u a) =
        TopPair.singularCohomologyMap (thomPairOverMap F E inter_subset_right) _ y := by
      refine singularCohomology_thomPairOver_eq_of_eq (inter_iUnion₂ _ _)
        (singularCohomology_thomPairOver_biUnion_ext s
          (fun i hi ↦ (hWo a ha').inter (hWo i (hs i hi))) (fun i hi ↦ ?_) fun b hb ↦ ?_)
      · obtain ⟨e', he', hi'⟩ := hWe i (hs i hi)
        exact ⟨e', he', inter_subset_right.trans hi'⟩
      · obtain ⟨j, hj, hbj⟩ := mem_iUnion₂.1 hb
        -- On the fibre over `b ∈ W j`, `y` restricts as its restriction `u j` to `W j` does.
        have hyb := singularCohomologyMap_fiberThomPairOverMap_thomPairOverMap
          (Finset.subset_set_biUnion_of_mem hj) hbj.2 y
        rw [hy j hj] at hyb
        simp only [singularCohomologyMap_fiberThomPairOverMap_thomPairOverMap, ← hyb]
        exact hu a ha' j (hs j hj) b hbj.1 hbj.2
    obtain ⟨z, hza, hzs⟩ := exists_singularCohomology_thomPairOver_union (hWo a ha') hSo (u a) y
      hagree
    refine ⟨TopPair.singularCohomologyMap
      (thomPairOverMap F E (Finset.set_biUnion_insert a s W).le) _ z, fun i hi ↦ ?_⟩
    rw [singularCohomologyMap_thomPairOverMap_thomPairOverMap]
    rcases Finset.mem_insert.1 hi with rfl | hi
    · exact hza
    · rw [← hy i hi, ← hzs, singularCohomologyMap_thomPairOverMap_thomPairOverMap]

end TopDegree

end TauCeti
