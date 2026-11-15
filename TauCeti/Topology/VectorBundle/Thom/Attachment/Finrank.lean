/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.VectorBundle.Thom.Attachment.Basic
public import TauCeti.Topology.VectorBundle.Thom.RankDegreeHomology
import Mathlib.Topology.Algebra.Module.FiniteDimension
import TauCeti.AlgebraicTopology.Singular.LocalHomology.Basic
import TauCeti.AlgebraicTopology.Singular.Triple.Finrank

/-!
# Dimensions, rank bounds and point-base specialization for disc-bundle attachments

From the direct-sum Thom-pair decompositions established in
`TauCeti.Topology.VectorBundle.Thom.Attachment.Basic`, this file derives quantitative and
rank-filtered consequences for spaces `Z` obtained from a closed subset `X` by attaching a finite
family of closed disc bundles `D_{rᵢ}(Eᵢ)` along their sphere bundles `S_{rᵢ}(Eᵢ)`:

* **Dimension additivity** (`TauCeti.finite_singularHomology_of_attach_discBundlesOfRadius`,
  `TauCeti.finrank_singularHomology_of_attach_discBundlesOfRadius_eq_sum`): over a division ring
  `k`, `dim Hₙ(Z, X; V) = ∑ᵢ dim Hₙ(Eᵢ, (Eᵢ)₀; V)`.
* **Vanishing below all ranks**
  (`TauCeti.isZero_singularHomology_of_attach_discBundlesOfRadius_of_lt_finrank`,
  `TauCeti.isZero_singularCohomology_of_attach_discBundlesOfRadius_of_lt_finrank`): `Hₙ(Z, X)` and
  `Hⁿ(Z, X)` vanish whenever `n < finrank ℝ (F i)` for all `i`.
* **Bottom nonvanishing degree without orientation**
  (`TauCeti.singularHomologyAttachDiscBundlesOfRadiusIsoH0OfLeFinrank`): when
  `d ≤ finrank ℝ (F i)` for all `i` and `K` is a commutative ring with `Subsingleton Kˣ` (such as
  `ZMod 2`), `H_d(Z, X; K) ≅ ⨁_{finrank ℝ (F i) = d} H₀(Bᵢ; K)` over arbitrary bases and without
  any orientability assumption.
* **Subsingleton and point bases (classical Morse specialization)**
  (`TauCeti.isIso_fiberThomPairMap_of_subsingleton`,
  `TauCeti.isZero_singularHomology_thomPair_of_subsingleton_of_ne`,
  `TauCeti.singularHomologyThomPairIsoOfUnique`,
  `TauCeti.singularHomologyIsoOfAttachDiscBundlesOfRadiusOfUniqueBase`,
  `TauCeti.finrank_singularHomology_of_attach_discBundlesOfRadius_of_unique_base`): when each `Bᵢ`
  is a point (`Unique (Bᵢ)`), `Hₙ(Z, X; R) ≅ ⨁_{finrank ℝ (F i) = n} R` and
  `dim Hₙ(Z, X; V) = #{i | finrank ℝ (F i) = n} · dim V`.

## References

* R. Bott, *Nondegenerate critical manifolds*, Annals of Mathematics 60 (1954), 248–261.
* J. Milnor, *Morse Theory*, Annals of Mathematics Studies 51, Princeton University Press (1963),
  §3 and §5.
-/

public section

noncomputable section

open Bundle CategoryTheory Limits Module Set Topology

universe uF w v u

namespace TauCeti

section Helpers

private def biproductSubtypeIsoOfIsZero {C : Type u} [Category.{v} C] [HasZeroMorphisms C]
    [HasFiniteBiproducts C] {ι : Type*} [Finite ι] (M : ι → C) (P : ι → Prop)
    [DecidablePred P] (hzero : ∀ i, ¬ P i → IsZero (M i)) :
    (⨁ fun x : {i : ι // P i} ↦ M x.1) ≅ ⨁ M where
  hom := biproduct.fromSubtype M P
  inv := biproduct.toSubtype M P
  hom_inv_id := biproduct.fromSubtype_toSubtype M P
  inv_hom_id := by
    rw [biproduct.toSubtype_fromSubtype]
    refine biproduct.hom_ext' _ _ fun i ↦ ?_
    rw [biproduct.ι_map, Category.comp_id]
    split_ifs with hi
    · exact Category.id_comp _
    · exact (hzero i hi).eq_of_src _ _

@[reassoc (attr := simp)]
private lemma ι_biproductSubtypeIsoOfIsZero_hom {C : Type u} [Category.{v} C]
    [HasZeroMorphisms C] [HasFiniteBiproducts C] {ι : Type*} [Finite ι] (M : ι → C)
    (P : ι → Prop) [DecidablePred P] (hzero : ∀ i, ¬ P i → IsZero (M i))
    (x : {i : ι // P i}) :
    biproduct.ι (fun y : {i : ι // P i} ↦ M y.1) x ≫
      (biproductSubtypeIsoOfIsZero M P hzero).hom = biproduct.ι M x.1 :=
  biproduct.ι_desc _ _

@[simps]
private def singularHomologyMapIso {C : Type u} [Category.{v} C] [Abelian C]
    [HasCoproducts.{w} C] {P Q : TopPair.{w}} (e : P ≅ Q) (R : C) (n : ℕ) :
    P.singularHomology R n ≅ Q.singularHomology R n where
  hom := TopPair.singularHomologyMap e.hom R n
  inv := TopPair.singularHomologyMap e.inv R n
  hom_inv_id := by
    rw [← TopPair.singularHomologyMap_comp, e.hom_inv_id, TopPair.singularHomologyMap_id]
  inv_hom_id := by
    rw [← TopPair.singularHomologyMap_comp, e.inv_hom_id, TopPair.singularHomologyMap_id]

private def singularHomologyCongrDegreeIso {C : Type u} [Category.{v} C] [Abelian C]
    [HasCoproducts.{w} C] (P : TopPair.{w}) (R : C) {m n : ℕ} (h : m = n) :
    P.singularHomology R m ≅ P.singularHomology R n :=
  eqToIso (by subst h; rfl)

@[simp]
private lemma singularHomologyCongrDegreeIso_inv {C : Type u} [Category.{v} C] [Abelian C]
    [HasCoproducts.{w} C] (P : TopPair.{w}) (R : C) {m n : ℕ} (h : m = n) :
    (singularHomologyCongrDegreeIso P R h).inv = eqToHom (by subst h; rfl) := by
  subst h; rfl

end Helpers

/-! ### Dimension additivity over a division ring -/

section ModuleCatBiproduct

variable {k : Type*} [DivisionRing k]

private lemma finite_biproduct_moduleCat {ι : Type*} [Finite ι] (V : ι → ModuleCat.{w} k)
    (hV : ∀ i, Module.Finite k (V i)) : Module.Finite k (⨁ V : ModuleCat.{w} k) := by
  obtain ⟨m, ⟨e⟩⟩ := Finite.exists_equiv_fin ι
  let iso := (biproduct.whiskerEquiv e.symm fun _ ↦ Iso.refl _).symm ≪≫
    ModuleCat.biproductIsoPi (fun j : Fin m ↦ V (e.symm j))
  exact Module.Finite.equiv iso.symm.toLinearEquiv

private lemma finrank_biproduct_moduleCat {ι : Type*} [Fintype ι] (V : ι → ModuleCat.{w} k)
    (hV : ∀ i, Module.Finite k (V i)) :
    finrank k (⨁ V : ModuleCat.{w} k) = ∑ i, finrank k (V i) := by
  obtain ⟨m, ⟨e⟩⟩ := Finite.exists_equiv_fin ι
  let iso := (biproduct.whiskerEquiv e.symm fun _ ↦ Iso.refl _).symm ≪≫
    ModuleCat.biproductIsoPi (fun j : Fin m ↦ V (e.symm j))
  rw [iso.toLinearEquiv.finrank_eq, Module.finrank_pi_fintype,
    ← Equiv.sum_comp e.symm (fun i ↦ finrank k (V i))]

end ModuleCatBiproduct

section Finrank

variable {ι : Type*} [Finite ι]
  {B : ι → Type w} {F : ι → Type uF} {E : ∀ i, B i → Type w}
  [∀ i, TopologicalSpace (B i)] [∀ i, NormedAddCommGroup (F i)] [∀ i, NormedSpace ℝ (F i)]
  [∀ i b, NormedAddCommGroup (E i b)] [∀ i b, NormedSpace ℝ (E i b)]
  [∀ i, TopologicalSpace (TotalSpace (F i) (E i))] [∀ i, FiberBundle (F i) (E i)]
  [∀ i, VectorBundle ℝ (F i) (E i)]
  (hnorm : ∀ i, Continuous fun v : TotalSpace (F i) (E i) ↦ ‖v.2‖)
  {r : ∀ i, B i → ℝ} (hr : ∀ i, Continuous (r i)) (hrpos : ∀ i b, 0 < r i b)
  {Z : Type w} [TopologicalSpace Z] {X : Set Z}
  {f : ∀ i, discSpherePairOfRadius (F i) (E i) (r i) ⟶ TopPair.ofSubset (X := TopCat.of Z) X}
  (hf : ∀ i, IsClosedEmbedding (TopPair.Hom.fst (f i))) (hX : IsClosed X)
  (hfX : ∀ i (v : discBundleOfRadius (F i) (E i) (r i)),
    TopPair.Hom.fst (f i) v ∈ X →
      (v : TotalSpace (F i) (E i)) ∈ sphereBundleOfRadius (F i) (E i) (r i))
  (hdisj : Pairwise fun i j ↦
    Disjoint (range (TopPair.Hom.fst (f i)) \ X) (range (TopPair.Hom.fst (f j)) \ X))
  (hfcover : X ∪ ⋃ i, range (TopPair.Hom.fst (f i)) = univ)

include hnorm hr hrpos hf hX hfX hdisj hfcover in
/-- **Finite-dimensionality of relative homology for a finite disc-bundle attachment.** Over a
division ring `k`, if each Thom-pair homology `Hₙ(Eᵢ, (Eᵢ)₀; V)` is finite-dimensional, then so is
`Hₙ(Z, X; V)`. -/
theorem finite_singularHomology_of_attach_discBundlesOfRadius
    {k : Type*} [DivisionRing k] (V : ModuleCat.{w} k) (n : ℕ)
    (hfin : ∀ i, Module.Finite k ((thomPair (F i) (E i)).singularHomology V n : ModuleCat k)) :
    Module.Finite k ((TopPair.ofSubset (X := TopCat.of Z) X).singularHomology V n : ModuleCat k) :=
  have := finite_biproduct_moduleCat (fun i ↦ (thomPair (F i) (E i)).singularHomology V n) hfin
  Module.Finite.equiv (singularHomologyIsoThomPairsOfAttachDiscBundlesOfRadius
    hnorm hr hrpos hf hX hfX hdisj hfcover V n).toLinearEquiv

end Finrank

/-- **Dimension additivity for a finite disc-bundle attachment.** Over a division ring `k`, if each
Thom-pair homology `Hₙ(Eᵢ, (Eᵢ)₀; V)` is finite-dimensional, then
`dim Hₙ(Z, X; V) = ∑ᵢ dim Hₙ(Eᵢ, (Eᵢ)₀; V)`. -/
theorem finrank_singularHomology_of_attach_discBundlesOfRadius_eq_sum
    {ι : Type*} [Fintype ι]
    {B : ι → Type w} {F : ι → Type uF} {E : ∀ i, B i → Type w}
    [∀ i, TopologicalSpace (B i)] [∀ i, NormedAddCommGroup (F i)] [∀ i, NormedSpace ℝ (F i)]
    [∀ i b, NormedAddCommGroup (E i b)] [∀ i b, NormedSpace ℝ (E i b)]
    [∀ i, TopologicalSpace (TotalSpace (F i) (E i))] [∀ i, FiberBundle (F i) (E i)]
    [∀ i, VectorBundle ℝ (F i) (E i)]
    (hnorm : ∀ i, Continuous fun v : TotalSpace (F i) (E i) ↦ ‖v.2‖)
    {r : ∀ i, B i → ℝ} (hr : ∀ i, Continuous (r i)) (hrpos : ∀ i b, 0 < r i b)
    {Z : Type w} [TopologicalSpace Z] {X : Set Z}
    {f : ∀ i, discSpherePairOfRadius (F i) (E i) (r i) ⟶ TopPair.ofSubset (X := TopCat.of Z) X}
    (hf : ∀ i, IsClosedEmbedding (TopPair.Hom.fst (f i))) (hX : IsClosed X)
    (hfX : ∀ i (v : discBundleOfRadius (F i) (E i) (r i)),
      TopPair.Hom.fst (f i) v ∈ X →
        (v : TotalSpace (F i) (E i)) ∈ sphereBundleOfRadius (F i) (E i) (r i))
    (hdisj : Pairwise fun i j ↦
      Disjoint (range (TopPair.Hom.fst (f i)) \ X) (range (TopPair.Hom.fst (f j)) \ X))
    (hfcover : X ∪ ⋃ i, range (TopPair.Hom.fst (f i)) = univ)
    {k : Type*} [DivisionRing k] (V : ModuleCat.{w} k) (n : ℕ)
    (hfin : ∀ i, Module.Finite k ((thomPair (F i) (E i)).singularHomology V n : ModuleCat k)) :
    finrank k ((TopPair.ofSubset (X := TopCat.of Z) X).singularHomology V n : ModuleCat k) =
      ∑ i, finrank k ((thomPair (F i) (E i)).singularHomology V n : ModuleCat k) := by
  rw [← (singularHomologyIsoThomPairsOfAttachDiscBundlesOfRadius
    hnorm hr hrpos hf hX hfX hdisj hfcover V n).toLinearEquiv.finrank_eq]
  exact finrank_biproduct_moduleCat _ hfin

/-! ### Below-rank vanishing and rank-degree `H₀` without orientation -/

section RankBounds

variable {ι : Type*} [Finite ι]
  {B : ι → Type w} {F : ι → Type w} {E : ∀ i, B i → Type w}
  [∀ i, TopologicalSpace (B i)] [∀ i, NormedAddCommGroup (F i)] [∀ i, NormedSpace ℝ (F i)]
  [∀ i, FiniteDimensional ℝ (F i)]
  [∀ i b, NormedAddCommGroup (E i b)] [∀ i b, NormedSpace ℝ (E i b)]
  [∀ i, TopologicalSpace (TotalSpace (F i) (E i))] [∀ i, FiberBundle (F i) (E i)]
  [∀ i, VectorBundle ℝ (F i) (E i)]
  (hnorm : ∀ i, Continuous fun v : TotalSpace (F i) (E i) ↦ ‖v.2‖)
  {r : ∀ i, B i → ℝ} (hr : ∀ i, Continuous (r i)) (hrpos : ∀ i b, 0 < r i b)
  {Z : Type w} [TopologicalSpace Z] {X : Set Z}
  {f : ∀ i, discSpherePairOfRadius (F i) (E i) (r i) ⟶ TopPair.ofSubset (X := TopCat.of Z) X}
  (hf : ∀ i, IsClosedEmbedding (TopPair.Hom.fst (f i))) (hX : IsClosed X)
  (hfX : ∀ i (v : discBundleOfRadius (F i) (E i) (r i)),
    TopPair.Hom.fst (f i) v ∈ X →
      (v : TotalSpace (F i) (E i)) ∈ sphereBundleOfRadius (F i) (E i) (r i))
  (hdisj : Pairwise fun i j ↦
    Disjoint (range (TopPair.Hom.fst (f i)) \ X) (range (TopPair.Hom.fst (f j)) \ X))
  (hfcover : X ∪ ⋃ i, range (TopPair.Hom.fst (f i)) = univ)

include hnorm hr hrpos hf hX hfX hdisj hfcover in
/-- **Vanishing below the ranks in relative homology.** When `Z` is obtained from `X` by attaching
finite-rank real disc bundles `D_{rᵢ}(Eᵢ)` along `S_{rᵢ}(Eᵢ)`, `Hₙ(Z, X; R)` vanishes in every
degree `n` strictly below all ranks `finrank ℝ (F i)`. -/
theorem isZero_singularHomology_of_attach_discBundlesOfRadius_of_lt_finrank
    {C : Type u} [Category.{v} C] [HasCoproducts.{w} C] [Abelian C]
    [HasFilteredColimitsOfSize.{w, w} C] [AB5OfSize.{w, w} C]
    (R : C) {n : ℕ} (hn : ∀ i, n < finrank ℝ (F i)) :
    IsZero ((TopPair.ofSubset (X := TopCat.of Z) X).singularHomology R n) := by
  have := Abelian.hasFiniteBiproducts (C := C)
  refine IsZero.of_iso ?_
    (singularHomologyIsoThomPairsOfAttachDiscBundlesOfRadius
      hnorm hr hrpos hf hX hfX hdisj hfcover R n).symm
  exact (IsZero.iff_id_eq_zero _).2 (biproduct.hom_ext' _ _ fun i ↦
    (isZero_singularHomology_thomPair R (hn i)).eq_of_src _ _)

include hnorm hr hrpos hf hX hfX hdisj hfcover in
/-- **Vanishing below the ranks in relative cohomology.** With projective chain coefficients,
`Hⁿ(Z, X; R, M)` vanishes in every degree `n` strictly below all ranks `finrank ℝ (F i)`. -/
theorem isZero_singularCohomology_of_attach_discBundlesOfRadius_of_lt_finrank
    {k : Type*} [CommRing k] [Linear k (ModuleCat.{w} k)] (R M : ModuleCat.{w} k)
    [Module.Projective k R] {n : ℕ} (hn : ∀ i, n < finrank ℝ (F i)) :
    IsZero ((TopPair.ofSubset (X := TopCat.of Z) X).singularCohomology R k M n) := by
  refine IsZero.of_iso ?_
    (singularCohomologyIsoThomPairsOfAttachDiscBundlesOfRadius
      hnorm hr hrpos hf hX hfX hdisj hfcover R k M n)
  exact (IsZero.iff_id_eq_zero _).2 (biproduct.hom_ext _ _ fun i ↦
    (isZero_singularCohomology_thomPair R M (hn i)).eq_of_tgt _ _)

/-- **Bottom nonvanishing degree without orientation.** Suppose every attached bundle has rank at
least `d`, and let `K` be a commutative ring whose only unit is `1` (such as `ZMod 2`). Then the
bundles of rank strictly above `d` contribute zero in degree `d`, while each bundle of rank `d`
contributes `H₀(Bᵢ; K)` (`TauCeti.thomPairSingularHomologyFinrankIso`), giving
`H_d(Z, X; K) ≅ ⨁_{dim Fᵢ = d} H₀(Bᵢ; K)` over arbitrary bases and without orientability. -/
def singularHomologyAttachDiscBundlesOfRadiusIsoH0OfLeFinrank
    (K : Type w) [CommRing K] [Subsingleton Kˣ] {d : ℕ} (hd : ∀ i, d ≤ finrank ℝ (F i)) :
    (TopPair.ofSubset (X := TopCat.of Z) X).singularHomology (ModuleCat.of K K) d ≅
      ⨁ fun x : {i : ι // finrank ℝ (F i) = d} ↦
        ((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{w} K) 0).obj
          (ModuleCat.of K K)).obj (TopCat.of (B x.1)) :=
  (singularHomologyIsoThomPairsOfAttachDiscBundlesOfRadius
      hnorm hr hrpos hf hX hfX hdisj hfcover (ModuleCat.of K K) d).symm ≪≫
    (biproductSubtypeIsoOfIsZero
      (fun i ↦ (thomPair (F i) (E i)).singularHomology (ModuleCat.of K K) d)
      (fun i ↦ finrank ℝ (F i) = d) fun i hi ↦
        isZero_singularHomology_thomPair (ModuleCat.of K K)
          (lt_of_le_of_ne (hd i) (Ne.symm hi))).symm ≪≫
    biproduct.mapIso fun x ↦
      singularHomologyCongrDegreeIso (thomPair (F x.1) (E x.1)) (ModuleCat.of K K) x.2.symm ≪≫
        thomPairSingularHomologyFinrankIso K (F x.1) (E x.1)

@[reassoc (attr := simp)]
theorem ι_singularHomologyAttachDiscBundlesOfRadiusIsoH0OfLeFinrank_inv
    (K : Type w) [CommRing K] [Subsingleton Kˣ] {d : ℕ} (hd : ∀ i, d ≤ finrank ℝ (F i))
    (x : {i : ι // finrank ℝ (F i) = d}) :
    biproduct.ι
        (fun y : {i : ι // finrank ℝ (F i) = d} ↦
          ((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{w} K) 0).obj
            (ModuleCat.of K K)).obj (TopCat.of (B y.1))) x ≫
      (singularHomologyAttachDiscBundlesOfRadiusIsoH0OfLeFinrank
        hnorm hr hrpos hf hX hfX hdisj hfcover K hd).inv =
      (thomPairSingularHomologyFinrankIso K (F x.1) (E x.1)).inv ≫
        eqToHom (by rw [x.2]) ≫
        biproduct.ι (fun i ↦ (thomPair (F i) (E i)).singularHomology (ModuleCat.of K K) d) x.1 ≫
        (singularHomologyIsoThomPairsOfAttachDiscBundlesOfRadius
          hnorm hr hrpos hf hX hfX hdisj hfcover (ModuleCat.of K K) d).hom := by
  simp only [singularHomologyAttachDiscBundlesOfRadiusIsoH0OfLeFinrank, Iso.trans_inv,
    Iso.symm_inv, biproduct.mapIso_inv, singularHomologyCongrDegreeIso_inv, Category.assoc,
    biproduct.ι_map_assoc]
  rw [ι_biproductSubtypeIsoOfIsZero_hom_assoc
    (M := fun i ↦ (thomPair (F i) (E i)).singularHomology (ModuleCat.of K K) d)]

end RankBounds

/-! ### Bundles over subsingleton and point bases (classical Morse specialization) -/

section PointBase

/-- Over a subsingleton base `B`, the inclusion `(E_b, E_b ∖ {0}) ⟶ (E, E₀)` of the fibre over `b`
into the Thom pair is an isomorphism in `TopPair`. -/
instance isIso_fiberThomPairMap_of_subsingleton
    {B : Type w} [TopologicalSpace B] [Subsingleton B]
    (F : Type uF) [TopologicalSpace F] (E : B → Type w)
    [TopologicalSpace (TotalSpace F E)] [∀ b, TopologicalSpace (E b)] [FiberBundle F E]
    [∀ b, Zero (E b)] (b : B) :
    IsIso (fiberThomPairMap F E b) := by
  let e : E b ≃ₜ TotalSpace F E :=
    (Equiv.ofBijective (TotalSpace.mk b) ⟨TotalSpace.mk_injective b,
      fun ⟨b', x⟩ ↦ by cases Subsingleton.elim b b'; exact ⟨x, rfl⟩⟩).toHomeomorphOfIsInducing
        (FiberBundle.totalSpaceMk_isInducing F E b)
  have : IsIso (TopPair.Hom.fst (fiberThomPairMap F E b)) := by
    rw [fiberThomPairMap_fst]
    exact (TopCat.isoOfHomeo (X := TopCat.of (E b)) (Y := TopCat.of (TotalSpace F E)) e).isIso_hom
  exact TopPair.isIso_of_isIso_fst_of_surjective_snd _ fun ⟨⟨b', x⟩, hx⟩ ↦ by
    cases Subsingleton.elim b b'
    refine ⟨⟨x, mem_zeroSectionCompl.1 hx⟩, ?_⟩
    rw [fiberThomPairMap_eq_ofSubsetMap]
    exact Subtype.ext (TopPair.ofSubsetMap_snd_apply _ _ _)

/-- Over a subsingleton base, the relative singular homology of the Thom pair `(E, E₀)` vanishes
in every degree `n ≠ finrank ℝ F`, for arbitrary abelian coefficients with coproducts (without
filtered-colimit hypotheses). -/
theorem isZero_singularHomology_thomPair_of_subsingleton_of_ne
    {B : Type w} [TopologicalSpace B] [Subsingleton B]
    {F : Type uF} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    {E : B → Type w} [TopologicalSpace (TotalSpace F E)]
    [∀ b, AddCommMonoid (E b)] [∀ b, Module ℝ (E b)] [∀ b, TopologicalSpace (E b)]
    [FiberBundle F E] [VectorBundle ℝ F E]
    {C : Type u} [Category.{v} C] [HasCoproducts.{w} C] [Abelian C]
    (R : C) {n : ℕ} (hn : n ≠ finrank ℝ F) :
    IsZero ((thomPair F E).singularHomology R n) := by
  by_cases hB : Nonempty B
  · obtain ⟨b⟩ := hB
    let F' := EuclideanSpace ℝ (ULift.{w} (Fin (finrank ℝ F)))
    let L₁ := (trivializationAt F E b).continuousLinearEquivAt ℝ b
      (mem_baseSet_trivializationAt F E b)
    let L₂ : F ≃L[ℝ] F' :=
      (LinearEquiv.ofFinrankEq F F'
        (finrank_euclideanSpace_ulift_fin _).symm).toContinuousLinearEquiv
    let isoPair : TopPair.ofSubset (X := TopCat.of F') ({0}ᶜ : Set F') ≅ thomPair F E :=
      (L₁.trans L₂).complZeroPairIso.symm ≪≫ asIso (fiberThomPairMap F E b)
    exact (isZero_singularHomology_complSingleton_of_ne R (OpenPartialHomeomorph.refl F')
      (mem_univ (0 : F')) (finrank_euclideanSpace_ulift_fin (finrank ℝ F)) hn).of_iso
        (singularHomologyMapIso isoPair.symm R n)
  · have : IsEmpty B := not_nonempty_iff.1 hB
    have hsurj : Function.Surjective (thomPair F E).map := fun v ↦ isEmptyElim v.proj
    exact TopPair.isZero_singularHomology_of_surjective_map (thomPair F E) R hsurj n

/-- Over a one-point base (`Unique B`), the relative singular homology of the Thom pair `(E, E₀)`
in the rank degree `finrank ℝ F` is isomorphic to one copy of the coefficients `R`, obtained by
choosing a linear equivalence of the unique fibre with `ℝ^(dim F)` (`LinearEquiv.ofFinrankEq`) and
applying `TauCeti.singularHomologyComplSingletonFinrankIso`. Because no orientation is assumed on
`E`, this isomorphism depends up to sign on that choice of coordinates; invariants such as
`Module.finrank` are independent of the choice. -/
def singularHomologyThomPairIsoOfUnique
    {B : Type w} [TopologicalSpace B] [Unique B]
    (F : Type uF) [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    (E : B → Type w) [TopologicalSpace (TotalSpace F E)]
    [∀ b, AddCommMonoid (E b)] [∀ b, Module ℝ (E b)] [∀ b, TopologicalSpace (E b)]
    [FiberBundle F E] [VectorBundle ℝ F E]
    {C : Type u} [Category.{v} C] [HasCoproducts.{w} C] [Abelian C] (R : C) :
    (thomPair F E).singularHomology R (finrank ℝ F) ≅ R :=
  let b : B := default
  let F' := EuclideanSpace ℝ (ULift.{w} (Fin (finrank ℝ F)))
  let L₁ := (trivializationAt F E b).continuousLinearEquivAt ℝ b
    (mem_baseSet_trivializationAt F E b)
  let L₂ : F ≃L[ℝ] F' :=
    (LinearEquiv.ofFinrankEq F F'
      (finrank_euclideanSpace_ulift_fin _).symm).toContinuousLinearEquiv
  (singularHomologyMapIso
      ((L₁.trans L₂).complZeroPairIso.symm ≪≫ asIso (fiberThomPairMap F E b)) R
      (finrank ℝ F)).symm ≪≫
    singularHomologyCongrDegreeIso
      (TopPair.ofSubset (X := TopCat.of F') ({0}ᶜ : Set F')) R
      (finrank_euclideanSpace_ulift_fin (finrank ℝ F)).symm ≪≫
    singularHomologyComplSingletonFinrankIso R (OpenPartialHomeomorph.refl F') (mem_univ (0 : F'))

section PointAttachment

variable {ι : Type*} [Finite ι]
  {B : ι → Type w} [∀ i, TopologicalSpace (B i)] [∀ i, Unique (B i)]
  {F : ι → Type uF} [∀ i, NormedAddCommGroup (F i)] [∀ i, NormedSpace ℝ (F i)]
  [∀ i, FiniteDimensional ℝ (F i)]
  {E : ∀ i, B i → Type w}
  [∀ i b, NormedAddCommGroup (E i b)] [∀ i b, NormedSpace ℝ (E i b)]
  [∀ i, TopologicalSpace (TotalSpace (F i) (E i))] [∀ i, FiberBundle (F i) (E i)]
  [∀ i, VectorBundle ℝ (F i) (E i)]
  (hnorm : ∀ i, Continuous fun v : TotalSpace (F i) (E i) ↦ ‖v.2‖)
  {r : ∀ i, B i → ℝ} (hr : ∀ i, Continuous (r i)) (hrpos : ∀ i b, 0 < r i b)
  {Z : Type w} [TopologicalSpace Z] {X : Set Z}
  {f : ∀ i, discSpherePairOfRadius (F i) (E i) (r i) ⟶ TopPair.ofSubset (X := TopCat.of Z) X}
  (hf : ∀ i, IsClosedEmbedding (TopPair.Hom.fst (f i))) (hX : IsClosed X)
  (hfX : ∀ i (v : discBundleOfRadius (F i) (E i) (r i)),
    TopPair.Hom.fst (f i) v ∈ X →
      (v : TotalSpace (F i) (E i)) ∈ sphereBundleOfRadius (F i) (E i) (r i))
  (hdisj : Pairwise fun i j ↦
    Disjoint (range (TopPair.Hom.fst (f i)) \ X) (range (TopPair.Hom.fst (f j)) \ X))
  (hfcover : X ∪ ⋃ i, range (TopPair.Hom.fst (f i)) = univ)

/-- **Point-base specialization (classical Morse handle attachment)**: when each attached bundle has
a one-point base `Bᵢ`, `Hₙ(Z, X; R)` is isomorphic to one copy of `R` for each index `i` of rank
`finrank ℝ (F i) = n`. -/
def singularHomologyIsoOfAttachDiscBundlesOfRadiusOfUniqueBase
    {C : Type u} [Category.{v} C] [HasCoproducts.{w} C] [Abelian C] [HasFiniteBiproducts C]
    (R : C) (n : ℕ) :
    (TopPair.ofSubset (X := TopCat.of Z) X).singularHomology R n ≅
      ⨁ fun _ : {i : ι // finrank ℝ (F i) = n} ↦ R :=
  (singularHomologyIsoThomPairsOfAttachDiscBundlesOfRadius
      hnorm hr hrpos hf hX hfX hdisj hfcover R n).symm ≪≫
    (biproductSubtypeIsoOfIsZero
      (fun i ↦ (thomPair (F i) (E i)).singularHomology R n)
      (fun i ↦ finrank ℝ (F i) = n) fun _ hi ↦
        isZero_singularHomology_thomPair_of_subsingleton_of_ne R (Ne.symm hi)).symm ≪≫
    biproduct.mapIso fun x ↦
      singularHomologyCongrDegreeIso (thomPair (F x.1) (E x.1)) R x.2.symm ≪≫
        singularHomologyThomPairIsoOfUnique (F x.1) (E x.1) R

@[reassoc (attr := simp)]
theorem ι_singularHomologyIsoOfAttachDiscBundlesOfRadiusOfUniqueBase_inv
    {C : Type u} [Category.{v} C] [HasCoproducts.{w} C] [Abelian C] [HasFiniteBiproducts C]
    (R : C) (n : ℕ) (x : {i : ι // finrank ℝ (F i) = n}) :
    biproduct.ι (fun _ : {i : ι // finrank ℝ (F i) = n} ↦ R) x ≫
      (singularHomologyIsoOfAttachDiscBundlesOfRadiusOfUniqueBase
        hnorm hr hrpos hf hX hfX hdisj hfcover R n).inv =
      (singularHomologyThomPairIsoOfUnique (F x.1) (E x.1) R).inv ≫
        eqToHom (by rw [x.2]) ≫
        biproduct.ι (fun i ↦ (thomPair (F i) (E i)).singularHomology R n) x.1 ≫
        (singularHomologyIsoThomPairsOfAttachDiscBundlesOfRadius
          hnorm hr hrpos hf hX hfX hdisj hfcover R n).hom := by
  simp only [singularHomologyIsoOfAttachDiscBundlesOfRadiusOfUniqueBase, Iso.trans_inv,
    Iso.symm_inv, biproduct.mapIso_inv, singularHomologyCongrDegreeIso_inv, Category.assoc,
    biproduct.ι_map_assoc]
  rw [ι_biproductSubtypeIsoOfIsZero_hom_assoc
    (M := fun i ↦ (thomPair (F i) (E i)).singularHomology R n)]

include hnorm hr hrpos hf hX hfX hdisj hfcover in
/-- **Dimension count in the point-base specialization**: over a division ring `k` with a
finite-dimensional coefficient module `V`, `dim Hₙ(Z, X; V) = #{i | dim Fᵢ = n} · dim V`. -/
theorem finrank_singularHomology_of_attach_discBundlesOfRadius_of_unique_base
    {k : Type*} [DivisionRing k] (V : ModuleCat.{w} k) [Module.Finite k V] (n : ℕ) :
    finrank k ((TopPair.ofSubset (X := TopCat.of Z) X).singularHomology V n : ModuleCat k) =
      Nat.card {i : ι // finrank ℝ (F i) = n} * finrank k V := by
  let S := {i : ι // finrank ℝ (F i) = n}
  cases nonempty_fintype S
  rw [(singularHomologyIsoOfAttachDiscBundlesOfRadiusOfUniqueBase
    hnorm hr hrpos hf hX hfX hdisj hfcover V n).toLinearEquiv.finrank_eq,
    finrank_biproduct_moduleCat (fun _ : S ↦ V) (fun _ ↦ inferInstance),
    Finset.sum_const, Finset.card_univ, smul_eq_mul, Nat.card_eq_fintype_card]

end PointAttachment

end PointBase

end TauCeti
