/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Biproducts
public import TauCeti.Topology.VectorBundle.Thom.Attachment.Single
import Mathlib.Logic.Equiv.Fin.Basic
import TauCeti.AlgebraicTopology.Cohomology.Triple
import TauCeti.CategoryTheory.Limits.Shapes.Biproduct

/-!
# Attaching finite families of disc bundles and Thom-pair decompositions

Let `Eᵢ → Bᵢ` (`i : ι`, `[Finite ι]`) be a finite family of real vector bundles equipped with fibre
gauges `ρᵢ : TotalSpace (F i) (E i) → ℝ` (`TauCeti.IsFiberGauge`), with disc bundles
`D_{ρᵢ}(Eᵢ) = {ρᵢ ≤ 1}` and sphere bundles `S_{ρᵢ}(Eᵢ) = {ρᵢ = 1}` (`TauCeti.gaugeDiscBundle`,
`TauCeti.gaugeSphereBundle`). This covers unit fibre norms (`TauCeti.isFiberGauge_norm`),
rescalings by continuous positive radius functions `rᵢ : Bᵢ → ℝ`
(`TauCeti.IsFiberGauge.div_comp_proj`), and quadratic-form / Morse–Bott normal Hessian gauges
(`TauCeti.isFiberGauge_sqrt`).

Suppose `Z` is obtained from a closed subset `X` by attaching `D_{ρᵢ}(Eᵢ)` along `S_{ρᵢ}(Eᵢ)`
through closed embeddings `fᵢ : (D_{ρᵢ}(Eᵢ), S_{ρᵢ}(Eᵢ)) ⟶ (Z, X)` whose open disc interiors
`fᵢ(D_{ρᵢ}(Eᵢ)) \ X` are pairwise disjoint (while their attaching sphere images inside `X` may
overlap arbitrarily). This file proves that the maps `fᵢ` induce direct-sum decompositions on
relative singular homology and cohomology in every degree, and identifies each summand with the
Thom pair `(Eᵢ, (Eᵢ)₀)`:

* **Direct-sum isomorphism on relative singular homology**
  (`TauCeti.isIso_biproductDesc_singularHomologyMap_of_attach_gaugeDiscBundles`,
  `TauCeti.singularHomologyIsoThomPairsOfAttachGaugeDiscBundles`):
  `⨁ᵢ Hₙ(Eᵢ, (Eᵢ)₀; R) ≅ Hₙ(Z, X; R)`.
* **Direct-sum isomorphism on relative singular cohomology**
  (`TauCeti.isIso_biproductLift_singularCohomologyMap_of_attach_gaugeDiscBundles`,
  `TauCeti.singularCohomologyIsoThomPairsOfAttachGaugeDiscBundles`):
  `Hⁿ(Z, X; R, M) ≅ ⨁ᵢ Hⁿ(Eᵢ, (Eᵢ)₀; R, M)`.
* **Ambient strong deformation retract**
  (`TauCeti.singularHomologyIsoThomPairsOfDeformationRetractAttachGaugeDiscBundles`): when `Y`
  contains `Z` and strong deformation retracts onto `Z`, `⨁ᵢ Hₙ(Eᵢ, (Eᵢ)₀; R) ≅ Hₙ(Y, X; R)`.

For a family indexed by `Option α`, let `X'` be the union of `X` with the images of `f (some j)`.
Because each `f (some j)` is a closed embedding and `α` is finite, `X'` is closed in `Z`, and the
remaining bundle `f none` meets `X'` only along its sphere bundle. In the long exact sequence of the
triple `(Z, X', X)`, the map from `(D_{ρ_none}(E_none), S_{ρ_none}(E_none))` into `(Z, X)` lifts
the isomorphism onto `(Z, X')` in every degree, splitting the triple sequence in both homology
(`TauCeti.TopTriple.isIso_biprod_desc_singularHomology`) and cohomology
(`TauCeti.TopTriple.isIso_biprod_lift_singularCohomology`).

## References

* R. Bott, *Nondegenerate critical manifolds*, Annals of Mathematics 60 (1954), 248–261.
* J. Milnor, *Morse Theory*, Annals of Mathematics Studies 51, Princeton University Press (1963),
  §3 and §5.
* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf), §2.1 and §4.D.
-/

noncomputable section

open Bundle CategoryTheory Limits Set Topology

universe uF w v u

namespace TauCeti

/-! ### Attaching a finite family of gauge disc bundles -/

section FiniteFamily

private structure GaugeAttachData.{uι, uF', w'} (ι : Type uι) where
  {Z : Type w'}
  [tZ : TopologicalSpace Z]
  X : Set Z
  {B : ι → Type w'}
  {F : ι → Type uF'}
  {E : ∀ i, B i → Type w'}
  [tB : ∀ i, TopologicalSpace (B i)]
  [nF : ∀ i, NormedAddCommGroup (F i)]
  [sF : ∀ i, NormedSpace ℝ (F i)]
  [gE : ∀ i b, AddCommGroup (E i b)]
  [mE : ∀ i b, Module ℝ (E i b)]
  [tEf : ∀ i b, TopologicalSpace (E i b)]
  [tE : ∀ i, TopologicalSpace (TotalSpace (F i) (E i))]
  [fb : ∀ i, FiberBundle (F i) (E i)]
  [vb : ∀ i, VectorBundle ℝ (F i) (E i)]
  ρ : ∀ i, TotalSpace (F i) (E i) → ℝ
  hρ : ∀ i, IsFiberGauge (ρ i)
  f : ∀ i, gaugeDiscSpherePair (ρ i) ⟶ TopPair.ofSubset (X := TopCat.of Z) X
  hf : ∀ i, IsClosedEmbedding (TopPair.Hom.fst (f i))
  hX : IsClosed X
  hfX : ∀ i (v : gaugeDiscBundle (ρ i)),
    TopPair.Hom.fst (f i) v ∈ X → (v : TotalSpace (F i) (E i)) ∈ gaugeSphereBundle (ρ i)
  hdisj : Pairwise fun i j ↦
    Disjoint (range (TopPair.Hom.fst (f i)) \ X) (range (TopPair.Hom.fst (f j)) \ X)
  hfcover : X ∪ ⋃ i, range (TopPair.Hom.fst (f i)) = univ

attribute [local instance] GaugeAttachData.tZ GaugeAttachData.tB GaugeAttachData.nF
  GaugeAttachData.sF GaugeAttachData.gE GaugeAttachData.mE GaugeAttachData.tEf
  GaugeAttachData.tE GaugeAttachData.fb GaugeAttachData.vb

private abbrev GaugeAttachData.reindex {α β : Type*} (D : GaugeAttachData.{_, uF, w} β)
    (e : α ≃ β) : GaugeAttachData.{_, uF, w} α :=
  ⟨D.X, fun i ↦ D.ρ (e i), fun i ↦ D.hρ (e i), fun i ↦ D.f (e i), fun i ↦ D.hf (e i), D.hX,
    fun i ↦ D.hfX (e i), fun _ _ hne ↦ D.hdisj (e.injective.ne hne),
    eq_univ_of_forall fun z ↦ (eq_univ_iff_forall.1 D.hfcover z).imp_right fun hz ↦ by
      obtain ⟨b, hb⟩ := mem_iUnion.1 hz
      obtain ⟨a, rfl⟩ := e.surjective b
      exact mem_iUnion.2 ⟨a, hb⟩⟩

section OptionStep

variable {α : Type*} (D : GaugeAttachData.{_, uF, w} (Option α))

private def intermediateSubset : Set D.Z :=
  D.X ∪ ⋃ j : α, range (TopPair.Hom.fst (D.f (some j)))

private lemma subset_intermediateSubset : D.X ⊆ intermediateSubset D := subset_union_left

private lemma isClosed_intermediateSubset [Finite α] : IsClosed (intermediateSubset D) :=
  D.hX.union (isClosed_iUnion_of_finite fun j ↦ (D.hf (some j)).isClosed_range)

private def restrictAttachSome (j : α) :
    gaugeDiscSpherePair (D.ρ (some j)) ⟶
      TopPair.ofSubset (X := TopCat.of (intermediateSubset D)) (Subtype.val ⁻¹' D.X) :=
  TopPair.ofHom
    (TopCat.ofHom ⟨fun v ↦ ⟨TopPair.Hom.fst (D.f (some j)) v, Or.inr (mem_iUnion.2 ⟨j, v, rfl⟩)⟩,
      Continuous.subtype_mk (TopPair.Hom.fst (D.f (some j))).hom.continuous _⟩)
    (TopCat.ofHom ⟨fun v ↦ ⟨⟨(TopPair.Hom.snd (D.f (some j)) v).val,
        Or.inl (TopPair.Hom.snd (D.f (some j)) v).property⟩,
        (TopPair.Hom.snd (D.f (some j)) v).property⟩,
      Continuous.subtype_mk (Continuous.subtype_mk
        (continuous_subtypeVal.comp (TopPair.Hom.snd (D.f (some j))).hom.continuous) _) _⟩)
    (TopCat.ext fun v ↦ Subtype.ext (TopPair.Hom.w_apply (D.f (some j)) v))

private abbrev restrictSomeData [Finite α] : GaugeAttachData.{_, uF, w} α :=
  ⟨Subtype.val ⁻¹' D.X, fun j ↦ D.ρ (some j), fun j ↦ D.hρ (some j), restrictAttachSome D,
    fun j ↦ ((isClosed_intermediateSubset D).isClosedEmbedding_subtypeVal.of_comp_iff
      (f := TopPair.Hom.fst (restrictAttachSome D j))).1 (D.hf (some j)),
    D.hX.preimage continuous_subtypeVal, fun j v hv ↦ D.hfX (some j) v hv,
    fun _ _ hj ↦ disjoint_left.2 fun ⟨_, _⟩ ⟨⟨v, hv⟩, hzX⟩ ⟨⟨w, hw⟩, _⟩ ↦
      disjoint_left.1 (D.hdisj ((Option.some_injective α).ne hj))
        ⟨⟨v, congrArg Subtype.val hv⟩, hzX⟩ ⟨⟨w, congrArg Subtype.val hw⟩, hzX⟩,
    eq_univ_of_forall fun ⟨_, hz⟩ ↦ hz.elim Or.inl fun hzU ↦ by
      obtain ⟨j, v, rfl⟩ := mem_iUnion.1 hzU
      exact Or.inr (mem_iUnion.2 ⟨j, v, rfl⟩)⟩

private abbrev innerPairIso :
    TopPair.ofSubset (X := TopCat.of (intermediateSubset D)) (Subtype.val ⁻¹' D.X) ≅
      TopTriple.innerPair.obj
        (TopTriple.ofSubset (X := TopCat.of D.Z) (subset_intermediateSubset D)) :=
  TopPair.ofSubsetPreimageValIso (X := TopCat.of D.Z) (subset_intermediateSubset D)

private lemma restrictAttachSome_comp_innerToTotal (j : α) :
    restrictAttachSome D j ≫ (innerPairIso D).hom ≫
        TopTriple.innerToTotal.app
          (TopTriple.ofSubset (X := TopCat.of D.Z) (subset_intermediateSubset D)) =
      (D.f (some j) : _ ⟶ TopTriple.totalPair.obj
        (TopTriple.ofSubset (X := TopCat.of D.Z) (subset_intermediateSubset D))) :=
  TopPair.hom_ext_of_fst _ <| TopCat.ext fun v ↦
    (ConcreteCategory.comp_apply _ _ v).trans <| (ConcreteCategory.comp_apply _ _ _).trans <|
      (congrArg (TopPair.Hom.fst (TopTriple.innerToTotal.app _))
        (TopPair.ofSubsetPreimageValIso_hom_fst_apply _)).trans rfl

private lemma mem_gaugeSphereBundle_attachNone (v : gaugeDiscBundle (D.ρ none))
    (hv : TopPair.Hom.fst ((D.f none : _ ⟶ TopTriple.totalPair.obj
        (TopTriple.ofSubset (X := TopCat.of D.Z) (subset_intermediateSubset D))) ≫
      TopTriple.totalToOuter.app
        (TopTriple.ofSubset (X := TopCat.of D.Z) (subset_intermediateSubset D))) v ∈
          intermediateSubset D) :
    (v : TotalSpace (D.F none) (D.E none)) ∈ gaugeSphereBundle (D.ρ none) := by
  rcases (hv : TopPair.Hom.fst (D.f none) v ∈ intermediateSubset D) with hvX | hvU
  · exact D.hfX none v hvX
  · obtain ⟨j, w, hw⟩ := mem_iUnion.1 hvU
    exact D.hfX none v (by_contra fun hnX ↦
      disjoint_left.1 (D.hdisj (Option.some_ne_none j).symm) ⟨⟨v, rfl⟩, hnX⟩ ⟨⟨w, hw⟩, hnX⟩)

private lemma cover_attachNone :
    intermediateSubset D ∪
      range (TopPair.Hom.fst ((D.f none : _ ⟶ TopTriple.totalPair.obj
          (TopTriple.ofSubset (X := TopCat.of D.Z) (subset_intermediateSubset D))) ≫
        TopTriple.totalToOuter.app
          (TopTriple.ofSubset (X := TopCat.of D.Z) (subset_intermediateSubset D)))) = univ :=
  eq_univ_of_forall fun z ↦ (eq_univ_iff_forall.1 D.hfcover z).elim (Or.inl ∘ Or.inl) fun hzU ↦ by
    obtain ⟨i | j, v, rfl⟩ := mem_iUnion.1 hzU
    · exact Or.inr ⟨v, rfl⟩
    · exact Or.inl (Or.inr (mem_iUnion.2 ⟨j, v, rfl⟩))

private theorem isIso_biproductDesc_option [Finite α]
    {C : Type u} [Category.{v} C] [HasCoproducts.{w} C] [Abelian C] [HasFiniteBiproducts C]
    (R : C) (n : ℕ)
    (hsome0 : IsIso (biproduct.desc fun j ↦
      TopPair.singularHomologyMap ((restrictSomeData D).f j) R n)) :
    IsIso (biproduct.desc fun i ↦ TopPair.singularHomologyMap (D.f i) R n) := by
  let T := TopTriple.ofSubset (X := TopCat.of D.Z) (subset_intermediateSubset D)
  let f' : ∀ i, gaugeDiscSpherePair (D.ρ i) ⟶ TopTriple.totalPair.obj T := D.f
  have hnone : ∀ m, IsIso (TopPair.singularHomologyMap (f' none) R m ≫
      TopPair.singularHomologyMap (TopTriple.totalToOuter.app T) R m) := fun m ↦ by
    rw [← TopPair.singularHomologyMap_comp (f' none) R (TopTriple.totalToOuter.app T) m]
    exact isIso_singularHomologyMap_of_attach_gaugeDiscBundle (D.hρ none)
      (isClosed_intermediateSubset D) R m (D.hf none)
      (mem_gaugeSphereBundle_attachNone D) (cover_attachNone D)
  have hsplit := T.isIso_biprod_desc_singularHomology R n
    (TopPair.singularHomologyMap (f' none) R n)
    (TopPair.singularHomologyMap (f' none) R (n + 1)) (hnone n) (hnone (n + 1))
  let hsomeIso :=
    asIso (biproduct.desc fun j ↦ TopPair.singularHomologyMap ((restrictSomeData D).f j) R n) ≪≫
      TopPair.singularHomologyMapIso R (innerPairIso D) n
  have hfac := biproductOptionIso_hom_comp_biprod_desc
    (f := fun i ↦ (gaugeDiscSpherePair (D.ρ i)).singularHomology R n) hsomeIso
    (TopPair.singularHomologyMap (f' none) R n)
    (TopPair.singularHomologyMap (TopTriple.innerToTotal.app T) R n)
    (fun i ↦ TopPair.singularHomologyMap (f' i) R n) rfl fun j ↦ by
      rw [Iso.trans_hom, asIso_hom, TopPair.singularHomologyMapIso_hom, Category.assoc,
        biproduct.ι_desc_assoc, ← TopPair.singularHomologyMap_comp,
        ← TopPair.singularHomologyMap_comp, restrictAttachSome_comp_innerToTotal]
  have hiso : IsIso (biproduct.desc fun i ↦ TopPair.singularHomologyMap (f' i) R n) := by
    rw [← hfac]; infer_instance
  exact hiso

private theorem isIso_biproductLift_option [Finite α]
    {C : Type u} [Category.{v} C] [HasCoproducts.{w} C] [Abelian C] (R : C)
    (k : Type*) [Ring k] [Linear k C] (M : C) (n : ℕ)
    (hsome0 : IsIso (biproduct.lift fun j ↦
      TopPair.singularCohomologyMap (R := R) (k := k) (M := M) ((restrictSomeData D).f j) n)) :
    IsIso (biproduct.lift fun i ↦
      TopPair.singularCohomologyMap (R := R) (k := k) (M := M) (D.f i) n) := by
  let T := TopTriple.ofSubset (X := TopCat.of D.Z) (subset_intermediateSubset D)
  let f' : ∀ i, gaugeDiscSpherePair (D.ρ i) ⟶ TopTriple.totalPair.obj T := D.f
  have hnone : ∀ m, IsIso
      (TopPair.singularCohomologyMap (R := R) (k := k) (M := M)
          (TopTriple.totalToOuter.app T) m ≫
        TopPair.singularCohomologyMap (f' none) m) := fun m ↦ by
    rw [← TopPair.singularCohomologyMap_comp (R := R) (k := k) (M := M)
      (f' none) (TopTriple.totalToOuter.app T) m]
    exact isIso_singularCohomologyMap_of_attach_gaugeDiscBundle (D.hρ none)
      (isClosed_intermediateSubset D) R m k M (D.hf none)
      (mem_gaugeSphereBundle_attachNone D) (cover_attachNone D)
  have hsplit := T.isIso_biprod_lift_singularCohomology R k M n
    (TopPair.singularCohomologyMap (f' none) n)
    (TopPair.singularCohomologyMap (f' none) (n + 1)) (hnone n) (hnone (n + 1))
  let eInner : (TopTriple.innerPair.obj T).singularCohomology R k M n ≅
      (TopPair.ofSubset (X := TopCat.of (intermediateSubset D))
        (Subtype.val ⁻¹' D.X)).singularCohomology R k M n :=
    (TopPair.singularCohomologyFunctor R k M n).mapIso (innerPairIso D).op
  have heInner : eInner.hom =
      TopPair.singularCohomologyMap (R := R) (k := k) (M := M) (innerPairIso D).hom n := rfl
  let hsomeIso :=
    eInner ≪≫
      asIso (biproduct.lift fun j ↦
        TopPair.singularCohomologyMap (R := R) (k := k) (M := M) ((restrictSomeData D).f j) n)
  have hfac := biprod_lift_comp_biproductOptionIso_inv
    (f := fun i ↦ (gaugeDiscSpherePair (D.ρ i)).singularCohomology R k M n) hsomeIso
    (TopPair.singularCohomologyMap (f' none) n)
    (TopPair.singularCohomologyMap (TopTriple.innerToTotal.app T) n)
    (fun i ↦ TopPair.singularCohomologyMap (f' i) n) rfl fun j ↦ by
      rw [Iso.trans_hom, heInner, asIso_hom, Category.assoc, biproduct.lift_π,
        ← TopPair.singularCohomologyMap_comp, ← TopPair.singularCohomologyMap_comp,
        Category.assoc, restrictAttachSome_comp_innerToTotal]
  have hiso : IsIso (biproduct.lift fun i ↦
      TopPair.singularCohomologyMap (R := R) (k := k) (M := M) (f' i) n) := by
    rw [← hfac]; infer_instance
  exact hiso

end OptionStep

private theorem isIso_biproductDesc_fin
    {C : Type u} [Category.{v} C] [HasCoproducts.{w} C] [Abelian C] [HasFiniteBiproducts C]
    (R : C) (n : ℕ) :
    ∀ (m : ℕ) (D : GaugeAttachData.{_, uF, w} (Fin m)),
      IsIso (biproduct.desc fun i ↦ TopPair.singularHomologyMap (D.f i) R n)
  | 0, D => by
    have hXuniv : D.X = univ := by simpa using D.hfcover
    have htgt := TopPair.isZero_singularHomology_of_surjective_map
      (TopPair.ofSubset (X := TopCat.of D.Z) D.X) R (fun z ↦ ⟨⟨z, hXuniv.symm ▸ mem_univ z⟩, rfl⟩) n
    exact isIso_of_source_target_iso_zero _ (isZero_biproduct_of_isEmpty _).isoZero htgt.isoZero
  | m + 1, D =>
    let e := (finSuccEquiv m).symm
    (isIso_biproductDesc_iff_of_equiv e).1 <|
      isIso_biproductDesc_option (D.reindex e) R n
        (isIso_biproductDesc_fin R n m (restrictSomeData (D.reindex e)))

private theorem isIso_biproductLift_fin
    {C : Type u} [Category.{v} C] [HasCoproducts.{w} C] [Abelian C] (R : C)
    (k : Type*) [Ring k] [Linear k C] (M : C) (n : ℕ) :
    ∀ (m : ℕ) (D : GaugeAttachData.{_, uF, w} (Fin m)),
      IsIso (biproduct.lift fun i ↦
        TopPair.singularCohomologyMap (R := R) (k := k) (M := M) (D.f i) n)
  | 0, D => by
    have hXuniv : D.X = univ := by simpa using D.hfcover
    have hsrc := TopPair.isZero_singularCohomology_of_surjective_map
      (TopPair.ofSubset (X := TopCat.of D.Z) D.X) R k M
      (fun z ↦ ⟨⟨z, hXuniv.symm ▸ mem_univ z⟩, rfl⟩) n
    exact isIso_of_source_target_iso_zero _ hsrc.isoZero (isZero_biproduct_of_isEmpty _).isoZero
  | m + 1, D =>
    let e := (finSuccEquiv m).symm
    (isIso_biproductLift_iff_of_equiv e).1 <|
      isIso_biproductLift_option (D.reindex e) R k M n
        (isIso_biproductLift_fin R k M n m (restrictSomeData (D.reindex e)))

end FiniteFamily

/-! ### Finite-family Thom-pair decompositions -/

public section

section FamilyDecompositions

variable {ι : Type*} [Finite ι]
  {B : ι → Type w} {F : ι → Type uF} {E : ∀ i, B i → Type w}
  [∀ i, TopologicalSpace (B i)] [∀ i, NormedAddCommGroup (F i)] [∀ i, NormedSpace ℝ (F i)]
  [∀ i b, AddCommGroup (E i b)] [∀ i b, Module ℝ (E i b)]
  [∀ i b, TopologicalSpace (E i b)] [∀ i, TopologicalSpace (TotalSpace (F i) (E i))]
  [∀ i, FiberBundle (F i) (E i)] [∀ i, VectorBundle ℝ (F i) (E i)]
  {ρ : ∀ i, TotalSpace (F i) (E i) → ℝ} (hρ : ∀ i, IsFiberGauge (ρ i))

section Subset

variable {Z : Type w} [TopologicalSpace Z] {X : Set Z}
  {f : ∀ i, gaugeDiscSpherePair (ρ i) ⟶ TopPair.ofSubset (X := TopCat.of Z) X}
  (hf : ∀ i, IsClosedEmbedding (TopPair.Hom.fst (f i))) (hX : IsClosed X)
  (hfX : ∀ i (v : gaugeDiscBundle (ρ i)),
    TopPair.Hom.fst (f i) v ∈ X → (v : TotalSpace (F i) (E i)) ∈ gaugeSphereBundle (ρ i))
  (hdisj : Pairwise fun i j ↦
    Disjoint (range (TopPair.Hom.fst (f i)) \ X) (range (TopPair.Hom.fst (f j)) \ X))
  (hfcover : X ∪ ⋃ i, range (TopPair.Hom.fst (f i)) = univ)
  {C : Type u} [Category.{v} C] [HasCoproducts.{w} C] [Abelian C]

include hρ hf hX hfX hdisj hfcover in
/-- **Attaching a finite family of gauge disc bundles induces direct-sum isomorphisms on relative
singular homology.** Let `Eᵢ → Bᵢ` (`i : ι`, `[Finite ι]`) be real vector bundles equipped with
fibre gauges `ρᵢ`, `X` a closed subset of `Z`, and `fᵢ : (D_{ρᵢ}(Eᵢ), S_{ρᵢ}(Eᵢ)) ⟶ (Z, X)` closed
embeddings whose images meet `X` only along `S_{ρᵢ}(Eᵢ)`, whose open disc interiors
`fᵢ(D_{ρᵢ}(Eᵢ)) \ X` are pairwise disjoint, and which together with `X` cover `Z`. Then
`⨁ᵢ Hₙ(D_{ρᵢ}(Eᵢ), S_{ρᵢ}(Eᵢ); R) ⟶ Hₙ(Z, X; R)` is an isomorphism in every degree. -/
theorem isIso_biproductDesc_singularHomologyMap_of_attach_gaugeDiscBundles
    [HasFiniteBiproducts C] (R : C) (n : ℕ) :
    IsIso (biproduct.desc fun i ↦ TopPair.singularHomologyMap (f i) R n) := by
  obtain ⟨m, ⟨e⟩⟩ := Finite.exists_equiv_fin ι
  let D : GaugeAttachData.{_, uF, w} ι := ⟨X, ρ, hρ, f, hf, hX, hfX, hdisj, hfcover⟩
  exact (isIso_biproductDesc_iff_of_equiv e.symm).1
    (isIso_biproductDesc_fin R n m (D.reindex e.symm))

include hρ hf hX hfX hdisj hfcover in
/-- **Attaching a finite family of gauge disc bundles induces direct-sum isomorphisms on relative
singular cohomology.** Under the hypotheses of
`TauCeti.isIso_biproductDesc_singularHomologyMap_of_attach_gaugeDiscBundles`,
`Hⁿ(Z, X; R, M) ⟶ ⨁ᵢ Hⁿ(D_{ρᵢ}(Eᵢ), S_{ρᵢ}(Eᵢ); R, M)` is an isomorphism in every degree. -/
theorem isIso_biproductLift_singularCohomologyMap_of_attach_gaugeDiscBundles
    (R : C) (k : Type*) [Ring k] [Linear k C] (M : C) (n : ℕ) :
    IsIso (biproduct.lift fun i ↦
      TopPair.singularCohomologyMap (R := R) (k := k) (M := M) (f i) n) := by
  obtain ⟨m, ⟨e⟩⟩ := Finite.exists_equiv_fin ι
  let D : GaugeAttachData.{_, uF, w} ι := ⟨X, ρ, hρ, f, hf, hX, hfX, hdisj, hfcover⟩
  exact (isIso_biproductLift_iff_of_equiv e.symm).1
    (isIso_biproductLift_fin R k M n m (D.reindex e.symm))

/-- **Thom-pair homology decomposition of a finite gauge disc-bundle attachment**:
`⨁ᵢ Hₙ(Eᵢ, (Eᵢ)₀; R) ≅ Hₙ(Z, X; R)`. -/
def singularHomologyIsoThomPairsOfAttachGaugeDiscBundles [HasFiniteBiproducts C] (R : C) (n : ℕ) :
    (⨁ fun i ↦ (thomPair (F i) (E i)).singularHomology R n) ≅
      (TopPair.ofSubset (X := TopCat.of Z) X).singularHomology R n :=
  (biproduct.mapIso fun i ↦ (@asIso _ _ _ _
      (TopPair.singularHomologyMap (gaugeDiscSpherePairMap (hρ i)) R n)
      (isIso_singularHomologyMap_gaugeDiscSpherePairMap (hρ i) R n)).symm) ≪≫
  @asIso _ _ _ _ (biproduct.desc fun i ↦ TopPair.singularHomologyMap (f i) R n)
    (isIso_biproductDesc_singularHomologyMap_of_attach_gaugeDiscBundles
      hρ hf hX hfX hdisj hfcover R n)

@[reassoc (attr := simp)]
theorem singularHomologyMap_gaugeDiscSpherePairMap_comp_ι_isoThomPairs_hom
    [HasFiniteBiproducts C] (R : C) (n : ℕ) (i : ι) :
    TopPair.singularHomologyMap (gaugeDiscSpherePairMap (hρ i)) R n ≫
        biproduct.ι (fun j ↦ (thomPair (F j) (E j)).singularHomology R n) i ≫
          (singularHomologyIsoThomPairsOfAttachGaugeDiscBundles
            hρ hf hX hfX hdisj hfcover R n).hom =
      TopPair.singularHomologyMap (f i) R n := by
  have := isIso_singularHomologyMap_gaugeDiscSpherePairMap (hρ i) R n
  have := isIso_biproductDesc_singularHomologyMap_of_attach_gaugeDiscBundles
    hρ hf hX hfX hdisj hfcover R n
  simp [singularHomologyIsoThomPairsOfAttachGaugeDiscBundles]

/-- **Thom-pair cohomology decomposition of a finite gauge disc-bundle attachment**:
`Hⁿ(Z, X; R, M) ≅ ⨁ᵢ Hⁿ(Eᵢ, (Eᵢ)₀; R, M)`. -/
def singularCohomologyIsoThomPairsOfAttachGaugeDiscBundles
    (R : C) (k : Type*) [Ring k] [Linear k C] (M : C) (n : ℕ) :
    (TopPair.ofSubset (X := TopCat.of Z) X).singularCohomology R k M n ≅
      ⨁ fun i ↦ (thomPair (F i) (E i)).singularCohomology R k M n :=
  @asIso _ _ _ _ (biproduct.lift fun i ↦
      TopPair.singularCohomologyMap (R := R) (k := k) (M := M) (f i) n)
    (isIso_biproductLift_singularCohomologyMap_of_attach_gaugeDiscBundles
      hρ hf hX hfX hdisj hfcover R k M n) ≪≫
  biproduct.mapIso fun i ↦ (@asIso _ _ _ _
      (TopPair.singularCohomologyMap (R := R) (k := k) (M := M)
        (gaugeDiscSpherePairMap (hρ i)) n)
      (isIso_singularCohomologyMap_gaugeDiscSpherePairMap (hρ i) R k M n)).symm

@[reassoc (attr := simp)]
theorem singularCohomologyIsoThomPairsOfAttachGaugeDiscBundles_hom_comp_π_comp
    (R : C) (k : Type*) [Ring k] [Linear k C] (M : C) (n : ℕ) (i : ι) :
    (singularCohomologyIsoThomPairsOfAttachGaugeDiscBundles
        hρ hf hX hfX hdisj hfcover R k M n).hom ≫
      biproduct.π (fun j ↦ (thomPair (F j) (E j)).singularCohomology R k M n) i ≫
      TopPair.singularCohomologyMap (gaugeDiscSpherePairMap (hρ i)) n =
      TopPair.singularCohomologyMap (f i) n := by
  have := isIso_singularCohomologyMap_gaugeDiscSpherePairMap (hρ i) R k M n
  have := isIso_biproductLift_singularCohomologyMap_of_attach_gaugeDiscBundles
    hρ hf hX hfX hdisj hfcover R k M n
  simp [singularCohomologyIsoThomPairsOfAttachGaugeDiscBundles]

end Subset

section DeformationRetract

variable {M : Type w} [TopologicalSpace M] {X Z Y : Set M} (hXZ : X ⊆ Z) (hZY : Z ⊆ Y)
  {f : ∀ i, gaugeDiscSpherePair (ρ i) ⟶ TopPair.ofInclusion (X := TopCat.of M) hXZ}
  (hf : ∀ i, IsClosedEmbedding (TopPair.Hom.fst (f i)))
  (hX : IsClosed (Subtype.val ⁻¹' X : Set Z))
  (hfX : ∀ i (v : gaugeDiscBundle (ρ i)),
    TopPair.Hom.fst (f i) v ∈ (Subtype.val ⁻¹' X : Set Z) →
      (v : TotalSpace (F i) (E i)) ∈ gaugeSphereBundle (ρ i))
  (hdisj : Pairwise fun i j ↦
    Disjoint (range (TopPair.Hom.fst (f i)) \ Subtype.val ⁻¹' X)
      (range (TopPair.Hom.fst (f j)) \ Subtype.val ⁻¹' X))
  (hfcover : (Subtype.val ⁻¹' X : Set Z) ∪ ⋃ i, range (TopPair.Hom.fst (f i)) = univ)
  (ret : C(Y, Z))
  (G : ((ContinuousMap.inclusion hZY).comp ret).HomotopyRel (ContinuousMap.id Y)
    {y | (y : M) ∈ Z})

omit [Finite ι] [∀ i, TopologicalSpace (B i)] [∀ i, NormedAddCommGroup (F i)]
  [∀ i, NormedSpace ℝ (F i)] [∀ i b, AddCommGroup (E i b)] [∀ i b, Module ℝ (E i b)]
  [∀ i b, TopologicalSpace (E i b)] [∀ i, FiberBundle (F i) (E i)]
  [∀ i, VectorBundle ℝ (F i) (E i)] in
private lemma fst_comp_ofSubsetPreimageValIso_inv (i : ι) :
    TopPair.Hom.fst (f i ≫ (TopPair.ofSubsetPreimageValIso (X := TopCat.of M) hXZ).inv) =
      TopPair.Hom.fst (f i) :=
  TopCat.ext fun v ↦ (ConcreteCategory.comp_apply _ _ v).trans
    (TopPair.ofSubsetPreimageValIso_inv_fst_apply (TopPair.Hom.fst (f i) v))

omit [Finite ι] [∀ i, TopologicalSpace (B i)] [∀ i, NormedAddCommGroup (F i)]
  [∀ i, NormedSpace ℝ (F i)] [∀ i b, AddCommGroup (E i b)] [∀ i b, Module ℝ (E i b)]
  [∀ i b, TopologicalSpace (E i b)] [∀ i, FiberBundle (F i) (E i)]
  [∀ i, VectorBundle ℝ (F i) (E i)] in
include hdisj in
private lemma pairwise_disjoint_comp_ofSubsetPreimageValIso_inv :
    Pairwise fun i j ↦
      Disjoint
        (range (TopPair.Hom.fst (f i ≫ (TopPair.ofSubsetPreimageValIso (X := TopCat.of M) hXZ).inv))
          \ (Subtype.val ⁻¹' X : Set Z))
        (range (TopPair.Hom.fst (f j ≫ (TopPair.ofSubsetPreimageValIso (X := TopCat.of M) hXZ).inv))
          \ (Subtype.val ⁻¹' X : Set Z)) :=
  fun i j hij ↦ disjoint_left.2 fun _ ⟨hz₁, hzX⟩ ⟨hz₂, _⟩ ↦ disjoint_left.1 (hdisj hij)
    ⟨by rwa [fst_comp_ofSubsetPreimageValIso_inv] at hz₁, hzX⟩
    ⟨by rwa [fst_comp_ofSubsetPreimageValIso_inv] at hz₂, hzX⟩

variable {C : Type u} [Category.{v} C] [HasCoproducts.{w} C] [Abelian C] [HasFiniteBiproducts C]

/-- **Thom-pair homology across an ambient strong deformation retract onto an attached disc-bundle
complex.** Let `X ⊆ Z ⊆ Y` be nested subsets of `M` such that `X` is closed in `Z`, `Z` is obtained
from `X` by attaching a finite family of gauge disc bundles `D_{ρᵢ}(Eᵢ)` along `S_{ρᵢ}(Eᵢ)`, and
`Y` strong deformation retracts onto `Z`. Then `⨁ᵢ Hₙ(Eᵢ, (Eᵢ)₀; R) ≅ Hₙ(Y, X; R)`. Across a
Morse–Bott critical level `c`, taking `X = {g ≤ c - ε}`, `Y = {g ≤ c + ε}` and `Z` the lower
sublevel union the attached negative disc bundles computes the relative homology of the sublevel
pair. -/
def singularHomologyIsoThomPairsOfDeformationRetractAttachGaugeDiscBundles (R : C) (n : ℕ) :
    (⨁ fun i ↦ (thomPair (F i) (E i)).singularHomology R n) ≅
      (TopPair.ofInclusion (X := TopCat.of M) (hXZ.trans hZY)).singularHomology R n :=
  singularHomologyIsoThomPairsOfAttachGaugeDiscBundles (Z := Z) (X := Subtype.val ⁻¹' X)
      (f := fun i ↦ f i ≫ (TopPair.ofSubsetPreimageValIso (X := TopCat.of M) hXZ).inv) hρ
      (fun i ↦ (fst_comp_ofSubsetPreimageValIso_inv hXZ (f := f) i).symm ▸ hf i) hX
      (fun i v hv ↦ hfX i v (by rwa [fst_comp_ofSubsetPreimageValIso_inv] at hv))
      (pairwise_disjoint_comp_ofSubsetPreimageValIso_inv hXZ hdisj)
      (eq_univ_of_forall fun z ↦ (eq_univ_iff_forall.1 hfcover z).imp_right fun hz ↦ by
        obtain ⟨i, hzi⟩ := mem_iUnion.1 hz
        exact mem_iUnion.2 ⟨i, by rwa [fst_comp_ofSubsetPreimageValIso_inv]⟩) R n ≪≫
    TopPair.singularHomologyMapIso R (TopPair.ofSubsetPreimageValIso (X := TopCat.of M) hXZ) n ≪≫
    @asIso _ _ _ _ _
      (TopPair.isIso_singularHomologyMap_ofInclusionMap_inclusion_of_homotopyRel
        (X := TopCat.of M) hXZ hZY ret G R n)

@[reassoc (attr := simp)]
theorem singularHomologyMap_gaugeDiscSpherePairMap_comp_ι_isoDeformationRetract_hom
    (R : C) (n : ℕ) (i : ι) :
    TopPair.singularHomologyMap (gaugeDiscSpherePairMap (hρ i)) R n ≫
        biproduct.ι (fun j ↦ (thomPair (F j) (E j)).singularHomology R n) i ≫
          (singularHomologyIsoThomPairsOfDeformationRetractAttachGaugeDiscBundles
            hρ hXZ hZY hf hX hfX hdisj hfcover ret G R n).hom =
      TopPair.singularHomologyMap
        (f i ≫ TopPair.ofInclusionMap hXZ (hXZ.trans hZY) (ContinuousMap.inclusion hZY)
          fun _ hx ↦ by simpa using hx) R n := by
  have := TopPair.isIso_singularHomologyMap_ofInclusionMap_inclusion_of_homotopyRel
    (X := TopCat.of M) hXZ hZY ret G R n
  rw [singularHomologyIsoThomPairsOfDeformationRetractAttachGaugeDiscBundles, Iso.trans_hom,
    Iso.trans_hom, TopPair.singularHomologyMapIso_hom, asIso_hom,
    singularHomologyMap_gaugeDiscSpherePairMap_comp_ι_isoThomPairs_hom_assoc,
    ← TopPair.singularHomologyMap_comp_assoc, Category.assoc, Iso.inv_hom_id, Category.comp_id,
    ← TopPair.singularHomologyMap_comp]

end DeformationRetract

end FamilyDecompositions

end

end TauCeti
