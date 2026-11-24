/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.ModuleCat.Finrank
public import TauCeti.Topology.VectorBundle.Thom.Attachment.Basic
public import TauCeti.Topology.VectorBundle.Thom.PointBase
public import TauCeti.Topology.VectorBundle.Thom.RankDegreeHomology
import TauCeti.Algebra.Category.ModuleCat.Biproducts
import TauCeti.CategoryTheory.Limits.Shapes.Biproduct.Basic

/-!
# Dimensions, rank bounds and point-base specialization for disc-bundle attachments

From the direct-sum Thom-pair decompositions of
`TauCeti.Topology.VectorBundle.Thom.Attachment.Basic`, this file derives quantitative and
rank-filtered consequences for spaces `Z` obtained from a closed subset `X` by attaching a finite
family of closed gauge disc bundles `D_{ρᵢ}(Eᵢ)` along their sphere bundles `S_{ρᵢ}(Eᵢ)`:

* **Finite generation and rank additivity**
  (`TauCeti.finite_singularHomology_of_attach_gaugeDiscBundles`,
  `TauCeti.finrank_singularHomology_of_attach_gaugeDiscBundles_eq_sum`): over an arbitrary ring `R`,
  finite generation passes from the Thom pairs to `(Z, X)`. Over a ring satisfying the strong rank
  condition and the rank-nullity property (`HasRankNullity`, such as a division ring or a
  commutative domain like `ℤ`, even with torsion),
  `finrank R Hₙ(Z, X; V) = ∑ᵢ finrank R Hₙ(Eᵢ, (Eᵢ)₀; V)`.
* **Vanishing below all ranks**
  (`TauCeti.isZero_singularHomology_of_attach_gaugeDiscBundles_of_lt_finrank`,
  `TauCeti.isZero_singularCohomology_of_attach_gaugeDiscBundles_of_lt_finrank`): `Hₙ(Z, X)` and
  `Hⁿ(Z, X)` vanish whenever `n < finrank ℝ (F i)` for all `i`.
* **Bottom nonvanishing degree without orientation**
  (`TauCeti.singularHomologyAttachGaugeDiscBundlesIsoH0OfLeFinrank`): when
  `d ≤ finrank ℝ (F i)` for all `i` and `K` is a commutative ring with `Subsingleton Kˣ` (such as
  `ZMod 2`), `H_d(Z, X; K) ≅ ⨁_{finrank ℝ (F i) = d} H₀(Bᵢ; K)` over arbitrary bases and without
  any orientability assumption.
* **Point-base specialization (classical Morse handle attachment)**
  (`TauCeti.singularHomologyIsoOfAttachGaugeDiscBundlesOfUniqueBase`,
  `TauCeti.finrank_singularHomology_of_attach_gaugeDiscBundles_of_unique_base`): when each `Bᵢ` is a
  point (`Unique (Bᵢ)`), `Hₙ(Z, X; R) ≅ ⨁_{finrank ℝ (F i) = n} R`, and over any ring with
  `StrongRankCondition` and `HasRankNullity`,
  `finrank R Hₙ(Z, X; V) = #{i | dim Fᵢ = n} · finrank R V`.

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

section Finrank

variable {ι : Type*} {B : ι → Type w} {F : ι → Type uF} {E : ∀ i, B i → Type w}
  [∀ i, TopologicalSpace (B i)] [∀ i, NormedAddCommGroup (F i)] [∀ i, NormedSpace ℝ (F i)]
  [∀ i b, AddCommGroup (E i b)] [∀ i b, Module ℝ (E i b)]
  [∀ i b, TopologicalSpace (E i b)] [∀ i, TopologicalSpace (TotalSpace (F i) (E i))]
  [∀ i, FiberBundle (F i) (E i)] [∀ i, VectorBundle ℝ (F i) (E i)]
  {ρ : ∀ i, TotalSpace (F i) (E i) → ℝ} (hρ : ∀ i, IsFiberGauge (ρ i))
  {Z : Type w} [TopologicalSpace Z] {X : Set Z}
  {f : ∀ i, gaugeDiscSpherePair (ρ i) ⟶ TopPair.ofSubset (X := TopCat.of Z) X}
  (hf : ∀ i, IsClosedEmbedding (TopPair.Hom.fst (f i))) (hX : IsClosed X)
  (hfX : ∀ i (v : gaugeDiscBundle (ρ i)),
    TopPair.Hom.fst (f i) v ∈ X → (v : TotalSpace (F i) (E i)) ∈ gaugeSphereBundle (ρ i))
  (hdisj : Pairwise fun i j ↦
    Disjoint (range (TopPair.Hom.fst (f i)) \ X) (range (TopPair.Hom.fst (f j)) \ X))
  (hfcover : X ∪ ⋃ i, range (TopPair.Hom.fst (f i)) = univ)

include hρ hf hX hfX hdisj hfcover in
/-- **Finite generation of relative homology for a finite gauge disc-bundle attachment.** Over an
arbitrary ring `R`, if each Thom-pair homology `Hₙ(Eᵢ, (Eᵢ)₀; V)` is finitely generated as an
`R`-module, then so is `Hₙ(Z, X; V)`. -/
theorem finite_singularHomology_of_attach_gaugeDiscBundles [Finite ι]
    {R : Type*} [Ring R] (V : ModuleCat.{w} R) (n : ℕ)
    [∀ i, Module.Finite R ((thomPair (F i) (E i)).singularHomology V n : ModuleCat R)] :
    Module.Finite R ((TopPair.ofSubset (X := TopCat.of Z) X).singularHomology V n : ModuleCat R) :=
  have := ModuleCat.finite_biproduct (fun i ↦ (thomPair (F i) (E i)).singularHomology V n)
  Module.Finite.equiv (singularHomologyIsoThomPairsOfAttachGaugeDiscBundles
    hρ hf hX hfX hdisj hfcover V n).toLinearEquiv

include hρ hf hX hfX hdisj hfcover in
/-- **Finrank additivity for a finite gauge disc-bundle attachment.** Over a ring `R` satisfying
the strong rank condition and the rank-nullity property (`HasRankNullity`, e.g. a division ring or
a commutative domain such as `ℤ`), if each Thom-pair homology `Hₙ(Eᵢ, (Eᵢ)₀; V)` is finitely
generated, then `finrank R Hₙ(Z, X; V) = ∑ᵢ finrank R Hₙ(Eᵢ, (Eᵢ)₀; V)`. -/
theorem finrank_singularHomology_of_attach_gaugeDiscBundles_eq_sum [Fintype ι]
    {R : Type*} [Ring R] [StrongRankCondition R] [HasRankNullity.{w} R]
    (V : ModuleCat.{w} R) (n : ℕ)
    [∀ i, Module.Finite R ((thomPair (F i) (E i)).singularHomology V n : ModuleCat R)] :
    finrank R ((TopPair.ofSubset (X := TopCat.of Z) X).singularHomology V n : ModuleCat R) =
      ∑ i, finrank R ((thomPair (F i) (E i)).singularHomology V n : ModuleCat R) := by
  rw [← (singularHomologyIsoThomPairsOfAttachGaugeDiscBundles
    hρ hf hX hfX hdisj hfcover V n).toLinearEquiv.finrank_eq]
  exact ModuleCat.finrank_biproduct _

end Finrank

/-! ### Below-rank vanishing and rank-degree `H₀` without orientation -/

section RankBounds

variable {ι : Type*} [Finite ι]
  {B : ι → Type w} {F : ι → Type w} {E : ∀ i, B i → Type w}
  [∀ i, TopologicalSpace (B i)] [∀ i, NormedAddCommGroup (F i)] [∀ i, NormedSpace ℝ (F i)]
  [∀ i, FiniteDimensional ℝ (F i)]
  [∀ i b, AddCommGroup (E i b)] [∀ i b, Module ℝ (E i b)]
  [∀ i b, TopologicalSpace (E i b)] [∀ i, TopologicalSpace (TotalSpace (F i) (E i))]
  [∀ i, FiberBundle (F i) (E i)] [∀ i, VectorBundle ℝ (F i) (E i)]
  {ρ : ∀ i, TotalSpace (F i) (E i) → ℝ} (hρ : ∀ i, IsFiberGauge (ρ i))
  {Z : Type w} [TopologicalSpace Z] {X : Set Z}
  {f : ∀ i, gaugeDiscSpherePair (ρ i) ⟶ TopPair.ofSubset (X := TopCat.of Z) X}
  (hf : ∀ i, IsClosedEmbedding (TopPair.Hom.fst (f i))) (hX : IsClosed X)
  (hfX : ∀ i (v : gaugeDiscBundle (ρ i)),
    TopPair.Hom.fst (f i) v ∈ X → (v : TotalSpace (F i) (E i)) ∈ gaugeSphereBundle (ρ i))
  (hdisj : Pairwise fun i j ↦
    Disjoint (range (TopPair.Hom.fst (f i)) \ X) (range (TopPair.Hom.fst (f j)) \ X))
  (hfcover : X ∪ ⋃ i, range (TopPair.Hom.fst (f i)) = univ)

include hρ hf hX hfX hdisj hfcover in
/-- **Vanishing below the ranks in relative homology.** When `Z` is obtained from `X` by attaching
finite-rank real gauge disc bundles `D_{ρᵢ}(Eᵢ)` along `S_{ρᵢ}(Eᵢ)`, `Hₙ(Z, X; R)` vanishes in
every degree `n` strictly below all ranks `finrank ℝ (F i)`. -/
theorem isZero_singularHomology_of_attach_gaugeDiscBundles_of_lt_finrank
    {C : Type u} [Category.{v} C] [HasCoproducts.{w} C] [Abelian C]
    [HasFilteredColimitsOfSize.{w, w} C] [AB5OfSize.{w, w} C]
    (R : C) {n : ℕ} (hn : ∀ i, n < finrank ℝ (F i)) :
    IsZero ((TopPair.ofSubset (X := TopCat.of Z) X).singularHomology R n) := by
  have := Abelian.hasFiniteBiproducts (C := C)
  refine IsZero.of_iso ?_
    (singularHomologyIsoThomPairsOfAttachGaugeDiscBundles
      hρ hf hX hfX hdisj hfcover R n).symm
  exact (IsZero.iff_id_eq_zero _).2 (biproduct.hom_ext' _ _ fun i ↦
    (isZero_singularHomology_thomPair R (hn i)).eq_of_src _ _)

include hρ hf hX hfX hdisj hfcover in
/-- **Vanishing below the ranks in relative cohomology.** With projective chain coefficients,
`Hⁿ(Z, X; R, M)` vanishes in every degree `n` strictly below all ranks `finrank ℝ (F i)`. -/
theorem isZero_singularCohomology_of_attach_gaugeDiscBundles_of_lt_finrank
    {k : Type*} [CommRing k] [Linear k (ModuleCat.{w} k)] (R M : ModuleCat.{w} k)
    [Module.Projective k R] {n : ℕ} (hn : ∀ i, n < finrank ℝ (F i)) :
    IsZero ((TopPair.ofSubset (X := TopCat.of Z) X).singularCohomology R k M n) := by
  refine IsZero.of_iso ?_
    (singularCohomologyIsoThomPairsOfAttachGaugeDiscBundles
      hρ hf hX hfX hdisj hfcover R k M n)
  exact (IsZero.iff_id_eq_zero _).2 (biproduct.hom_ext _ _ fun i ↦
    (isZero_singularCohomology_thomPair R M (hn i)).eq_of_tgt _ _)

/-- **Bottom nonvanishing degree without orientation.** Suppose every attached bundle has rank at
least `d`, and let `K` be a commutative ring whose only unit is `1` (such as `ZMod 2`). Then the
bundles of rank strictly above `d` contribute zero in degree `d`, while each bundle of rank `d`
contributes `H₀(Bᵢ; K)` (`TauCeti.thomPairSingularHomologyFinrankIso`), giving
`H_d(Z, X; K) ≅ ⨁_{dim Fᵢ = d} H₀(Bᵢ; K)` over arbitrary bases and without orientability. -/
def singularHomologyAttachGaugeDiscBundlesIsoH0OfLeFinrank
    (K : Type w) [CommRing K] [Subsingleton Kˣ] {d : ℕ} (hd : ∀ i, d ≤ finrank ℝ (F i)) :
    (TopPair.ofSubset (X := TopCat.of Z) X).singularHomology (ModuleCat.of K K) d ≅
      ⨁ fun x : {i : ι // finrank ℝ (F i) = d} ↦
        ((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{w} K) 0).obj
          (ModuleCat.of K K)).obj (TopCat.of (B x.val)) :=
  (singularHomologyIsoThomPairsOfAttachGaugeDiscBundles
      hρ hf hX hfX hdisj hfcover (ModuleCat.of K K) d).symm ≪≫
    (biproductSubtypeIsoOfIsZero
      (fun i ↦ (thomPair (F i) (E i)).singularHomology (ModuleCat.of K K) d)
      (fun i ↦ finrank ℝ (F i) = d) fun i hi ↦
        isZero_singularHomology_thomPair (ModuleCat.of K K)
          (lt_of_le_of_ne (hd i) (Ne.symm hi))).symm ≪≫
    biproduct.mapIso fun x ↦
      TopPair.singularHomologyCongrDegreeIso (thomPair (F x.val) (E x.val)) (ModuleCat.of K K)
          x.property.symm ≪≫
        thomPairSingularHomologyFinrankIso K (F x.val) (E x.val)

@[reassoc (attr := simp)]
theorem ι_singularHomologyAttachGaugeDiscBundlesIsoH0OfLeFinrank_inv
    (K : Type w) [CommRing K] [Subsingleton Kˣ] {d : ℕ} (hd : ∀ i, d ≤ finrank ℝ (F i))
    (x : {i : ι // finrank ℝ (F i) = d}) :
    biproduct.ι
        (fun y : {i : ι // finrank ℝ (F i) = d} ↦
          ((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{w} K) 0).obj
            (ModuleCat.of K K)).obj (TopCat.of (B y.val))) x ≫
      (singularHomologyAttachGaugeDiscBundlesIsoH0OfLeFinrank
        hρ hf hX hfX hdisj hfcover K hd).inv =
      (thomPairSingularHomologyFinrankIso K (F x.val) (E x.val)).inv ≫
        eqToHom (congrArg ((thomPair (F x.val) (E x.val)).singularHomology (ModuleCat.of K K))
          x.property) ≫
        biproduct.ι (fun i ↦ (thomPair (F i) (E i)).singularHomology (ModuleCat.of K K) d) x.val ≫
        (singularHomologyIsoThomPairsOfAttachGaugeDiscBundles
          hρ hf hX hfX hdisj hfcover (ModuleCat.of K K) d).hom := by
  simp only [singularHomologyAttachGaugeDiscBundlesIsoH0OfLeFinrank, Iso.trans_inv,
    Iso.symm_inv, biproduct.mapIso_inv, TopPair.singularHomologyCongrDegreeIso_inv,
    biproductSubtypeIsoOfIsZero_hom, Category.assoc, biproduct.ι_map_assoc,
    biproduct.ι_fromSubtype_assoc]

end RankBounds

/-! ### Point-base specialization (classical Morse handle attachment) -/

section PointAttachment

variable {ι : Type*} [Finite ι]
  {B : ι → Type w} [∀ i, TopologicalSpace (B i)] [∀ i, Unique (B i)]
  {F : ι → Type uF} [∀ i, NormedAddCommGroup (F i)] [∀ i, NormedSpace ℝ (F i)]
  [∀ i, FiniteDimensional ℝ (F i)]
  {E : ∀ i, B i → Type w}
  [∀ i b, AddCommGroup (E i b)] [∀ i b, Module ℝ (E i b)]
  [∀ i b, TopologicalSpace (E i b)] [∀ i, TopologicalSpace (TotalSpace (F i) (E i))]
  [∀ i, FiberBundle (F i) (E i)] [∀ i, VectorBundle ℝ (F i) (E i)]
  {ρ : ∀ i, TotalSpace (F i) (E i) → ℝ} (hρ : ∀ i, IsFiberGauge (ρ i))
  {Z : Type w} [TopologicalSpace Z] {X : Set Z}
  {f : ∀ i, gaugeDiscSpherePair (ρ i) ⟶ TopPair.ofSubset (X := TopCat.of Z) X}
  (hf : ∀ i, IsClosedEmbedding (TopPair.Hom.fst (f i))) (hX : IsClosed X)
  (hfX : ∀ i (v : gaugeDiscBundle (ρ i)),
    TopPair.Hom.fst (f i) v ∈ X → (v : TotalSpace (F i) (E i)) ∈ gaugeSphereBundle (ρ i))
  (hdisj : Pairwise fun i j ↦
    Disjoint (range (TopPair.Hom.fst (f i)) \ X) (range (TopPair.Hom.fst (f j)) \ X))
  (hfcover : X ∪ ⋃ i, range (TopPair.Hom.fst (f i)) = univ)

/-- **Point-base specialization (classical Morse handle attachment)**: when each attached bundle has
a one-point base `Bᵢ`, `Hₙ(Z, X; R)` is isomorphic to one copy of `R` for each index `i` of rank
`finrank ℝ (F i) = n`. -/
def singularHomologyIsoOfAttachGaugeDiscBundlesOfUniqueBase
    {C : Type u} [Category.{v} C] [HasCoproducts.{w} C] [Abelian C] [HasFiniteBiproducts C]
    (R : C) (n : ℕ) :
    (TopPair.ofSubset (X := TopCat.of Z) X).singularHomology R n ≅
      ⨁ fun _ : {i : ι // finrank ℝ (F i) = n} ↦ R :=
  (singularHomologyIsoThomPairsOfAttachGaugeDiscBundles
      hρ hf hX hfX hdisj hfcover R n).symm ≪≫
    (biproductSubtypeIsoOfIsZero
      (fun i ↦ (thomPair (F i) (E i)).singularHomology R n)
      (fun i ↦ finrank ℝ (F i) = n) fun _ hi ↦
        isZero_singularHomology_thomPair_of_subsingleton_of_ne R (Ne.symm hi)).symm ≪≫
    biproduct.mapIso fun x ↦
      TopPair.singularHomologyCongrDegreeIso (thomPair (F x.val) (E x.val)) R x.property.symm ≪≫
        singularHomologyThomPairIsoOfUnique (F x.val) (E x.val) R

@[reassoc (attr := simp)]
theorem ι_singularHomologyIsoOfAttachGaugeDiscBundlesOfUniqueBase_inv
    {C : Type u} [Category.{v} C] [HasCoproducts.{w} C] [Abelian C] [HasFiniteBiproducts C]
    (R : C) (n : ℕ) (x : {i : ι // finrank ℝ (F i) = n}) :
    biproduct.ι (fun _ : {i : ι // finrank ℝ (F i) = n} ↦ R) x ≫
      (singularHomologyIsoOfAttachGaugeDiscBundlesOfUniqueBase
        hρ hf hX hfX hdisj hfcover R n).inv =
      (singularHomologyThomPairIsoOfUnique (F x.val) (E x.val) R).inv ≫
        eqToHom (congrArg ((thomPair (F x.val) (E x.val)).singularHomology R) x.property) ≫
        biproduct.ι (fun i ↦ (thomPair (F i) (E i)).singularHomology R n) x.val ≫
        (singularHomologyIsoThomPairsOfAttachGaugeDiscBundles
          hρ hf hX hfX hdisj hfcover R n).hom := by
  simp only [singularHomologyIsoOfAttachGaugeDiscBundlesOfUniqueBase, Iso.trans_inv,
    Iso.symm_inv, biproduct.mapIso_inv, TopPair.singularHomologyCongrDegreeIso_inv,
    biproductSubtypeIsoOfIsZero_hom, Category.assoc, biproduct.ι_map_assoc,
    biproduct.ι_fromSubtype_assoc]

include hρ hf hX hfX hdisj hfcover in
/-- **Rank count in the point-base specialization**: over a ring `R` satisfying the strong rank
condition and the rank-nullity property (`HasRankNullity`, e.g. a division ring or a commutative
domain such as `ℤ`) with a finitely generated coefficient module `V`,
`finrank R Hₙ(Z, X; V) = #{i | dim Fᵢ = n} · finrank R V`. -/
theorem finrank_singularHomology_of_attach_gaugeDiscBundles_of_unique_base
    {R : Type*} [Ring R] [StrongRankCondition R] [HasRankNullity.{w} R]
    (V : ModuleCat.{w} R) [Module.Finite R V] (n : ℕ) :
    finrank R ((TopPair.ofSubset (X := TopCat.of Z) X).singularHomology V n : ModuleCat R) =
      Nat.card {i : ι // finrank ℝ (F i) = n} * finrank R V := by
  let S := {i : ι // finrank ℝ (F i) = n}
  cases nonempty_fintype S
  rw [(singularHomologyIsoOfAttachGaugeDiscBundlesOfUniqueBase
    hρ hf hX hfX hdisj hfcover V n).toLinearEquiv.finrank_eq,
    ModuleCat.finrank_biproduct (fun _ : S ↦ V),
    Finset.sum_const, Finset.card_univ, smul_eq_mul, Nat.card_eq_fintype_card]

end PointAttachment

end TauCeti
