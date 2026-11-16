/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Biproducts
public import TauCeti.CategoryTheory.Limits.Shapes.Biproduct
public import TauCeti.Topology.VectorBundle.Thom.Attachment.Single
import Mathlib.Logic.Equiv.Fin.Basic

/-!
# Attaching finite families of disc bundles and Thom-pair decompositions

Let `Eᵢ → Bᵢ` (`i : ι`, `[Finite ι]`) be a finite family of real vector bundles with continuous
fibre norms and `rᵢ : Bᵢ → ℝ` continuous positive radius functions. Suppose `Z` is obtained from a
closed subset `X` by attaching `D_{rᵢ}(Eᵢ)` along `S_{rᵢ}(Eᵢ)` through closed embeddings
`fᵢ : (D_{rᵢ}(Eᵢ), S_{rᵢ}(Eᵢ)) ⟶ (Z, X)` whose open disc interiors `fᵢ(D_{rᵢ}(Eᵢ)) \ X` are
pairwise disjoint (while their attaching sphere images inside `X` may overlap arbitrarily).

This file proves that the maps `fᵢ` induce direct-sum decompositions on relative singular homology
and cohomology in every degree, and identifies each summand with the Thom pair `(Eᵢ, (Eᵢ)₀)`:

* **Finite family of unit or radius-`r` disc bundles**
  (`TauCeti.isIso_biproductDesc_singularHomologyMap_of_attach_discBundles`,
  `TauCeti.isIso_biproductDesc_singularHomologyMap_of_attach_discBundlesOfRadius`,
  `TauCeti.singularHomologyIsoThomPairsOfAttachDiscBundles`,
  `TauCeti.singularHomologyIsoThomPairsOfAttachDiscBundlesOfRadius`):
  `⨁ᵢ Hₙ(Eᵢ, (Eᵢ)₀; R) ≅ Hₙ(Z, X; R)`, with dual cohomology decompositions
  `Hⁿ(Z, X; R, M) ≅ ⨁ᵢ Hⁿ(Eᵢ, (Eᵢ)₀; R, M)`
  (`TauCeti.singularCohomologyIsoThomPairsOfAttachDiscBundles`,
  `TauCeti.singularCohomologyIsoThomPairsOfAttachDiscBundlesOfRadius`).
* **Ambient strong deformation retract**
  (`TauCeti.singularHomologyIsoThomPairsOfDeformationRetractAttachDiscBundlesOfRadius`): when `Y`
  contains `Z` and strong deformation retracts onto `Z`, `⨁ᵢ Hₙ(Eᵢ, (Eᵢ)₀; R) ≅ Hₙ(Y, X; R)`.

For a family indexed by `Option α`, let `X'` be the union of `X` with the images of `f (some j)`.
Because each `f (some j)` is a closed embedding and `α` is finite, `X'` is closed in `Z`, and the
remaining bundle `f none` meets `X'` only along its sphere bundle. In the long exact sequence of
the triple `(Z, X', X)`, the map from `(D(E_none), S(E_none))` into `(Z, X)` lifts the isomorphism
onto `(Z, X')` in every degree, splitting the triple sequence in both homology and cohomology.

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

/-! ### Splitting relative homology and cohomology across a triple -/

section TripleSplitting

variable {C : Type u} [Category.{v} C] [Abelian C] [HasCoproducts.{w} C]

/-- In a triple `T = (Z, X', X)`, if morphisms into `Hₙ(Z, X)` and `Hₙ₊₁(Z, X)` compose with
`H_*(Z, X) ⟶ H_*(Z, X')` to isomorphisms, then `B₀ ⊞ Hₙ(X', X) ⟶ Hₙ(Z, X)` is an isomorphism. -/
private theorem isIso_biprod_desc_triple_singularHomology (T : TopTriple.{w}) (R : C) (n : ℕ)
    {B₀ B₁ : C}
    (s₀ : B₀ ⟶ (TopTriple.totalPair.obj T).singularHomology R n)
    (s₁ : B₁ ⟶ (TopTriple.totalPair.obj T).singularHomology R (n + 1))
    (hs₀ : IsIso (s₀ ≫ TopPair.singularHomologyMap (TopTriple.totalToOuter.app T) R n))
    (hs₁ : IsIso (s₁ ≫ TopPair.singularHomologyMap (TopTriple.totalToOuter.app T) R (n + 1))) :
    IsIso (biprod.desc s₀ (TopPair.singularHomologyMap (TopTriple.innerToTotal.app T) R n)) := by
  let i₀ := TopPair.singularHomologyMap (TopTriple.innerToTotal.app T) R n
  let q₀ := TopPair.singularHomologyMap (TopTriple.totalToOuter.app T) R n
  let q₁ := TopPair.singularHomologyMap (TopTriple.totalToOuter.app T) R (n + 1)
  have hδ : T.singularHomologyδ R (n + 1) n rfl = 0 := by
    rw [← Category.id_comp (T.singularHomologyδ R (n + 1) n rfl), ← IsIso.inv_hom_id (s₁ ≫ q₁),
      Category.assoc, Category.assoc, T.comp_singularHomologyδ R (n + 1) n rfl,
      comp_zero, comp_zero]
  have hmono : Mono i₀ := (T.singularHomology_exact_inner R (n + 1) n rfl).mono_g hδ
  let S := ShortComplex.mk i₀ q₀ (T.singularHomologyMap_innerToTotal_comp_totalToOuter R n)
  let s' : S.X₃ ⟶ S.X₂ := inv (s₀ ≫ q₀) ≫ s₀
  have hs' : s' ≫ S.g = 𝟙 _ := by dsimp only [S, s']; rw [Category.assoc]; exact IsIso.inv_hom_id _
  let spl := ShortComplex.Splitting.ofExactOfSection S (T.singularHomology_exact_total R n)
    s' hs' hmono
  have hspl : IsIso (biprod.desc i₀ s') := spl.isoBinaryBiproduct.isIso_inv
  have hfac : (biprod.braiding' B₀ S.X₁).hom ≫
      (biprod.mapIso (Iso.refl _) (asIso (s₀ ≫ q₀))).hom ≫ biprod.desc i₀ s' =
      biprod.desc s₀ i₀ :=
    biprod.hom_ext' _ _ (by simp [s']) (by simp)
  rw [← hfac]; infer_instance

private abbrev tripleSingularCochainShortComplex (T : TopTriple.{w}) (R : C)
    (k : Type*) [Ring k] [Linear k C] (M : C) :
    ShortComplex (CochainComplex (ModuleCat.{v} k) ℕ) :=
  ShortComplex.mk
    (TopPair.singularCochainComplexMap (R := R) (k := k) (M := M) (TopTriple.totalToOuter.app T))
    (TopPair.singularCochainComplexMap (R := R) (k := k) (M := M) (TopTriple.innerToTotal.app T))
    (((T.singularChainComplexShortComplex R).op.map
      (TauCeti.ChainComplex.linearYonedaFunctor k M)).zero)

private theorem shortExact_tripleSingularCochainShortComplex (T : TopTriple.{w}) (R : C)
    (k : Type*) [Ring k] [Linear k C] (M : C) :
    (tripleSingularCochainShortComplex T R k M).ShortExact := by
  have : ∀ i, IsSplitMono ((T.singularChainComplexShortComplex R).f.f i) := fun i ↦ by
    let P := TopPair.toSSetPair.obj (TopTriple.outerPair.obj T)
    have hsec : ((SSetPair.chainComplexXSplitting R P i).s ≫
          ((TopTriple.totalPair.obj T).singularChainComplexπ R).f i) ≫
        (TopPair.singularChainComplexMap (TopTriple.totalToOuter.app T) R).f i = 𝟙 _ :=
      (Category.assoc _ _ _).trans <|
        (congrArg ((SSetPair.chainComplexXSplitting R P i).s ≫ ·)
          ((HomologicalComplex.comp_f _ _ i).symm.trans
            (congrArg (fun φ ↦ φ.f i) (T.singularChainComplexπ_comp_totalToOuter R)))).trans
          (SSetPair.chainComplexXSplitting R P i).s_g
    exact ((HomologicalComplex.shortExact_iff_degreewise_shortExact _).1
      (T.shortExact_singularChainComplexShortComplex R) i).isSplitMono_f_iff_isSplitEpi_g.2
        (IsSplitEpi.mk' ⟨_, hsec⟩)
  exact TauCeti.ChainComplex.shortExact_map_linearYonedaFunctor k M
    (T.shortExact_singularChainComplexShortComplex R)

private theorem isIso_biprod_lift_triple_singularCohomology (T : TopTriple.{w}) (R : C)
    (k : Type*) [Ring k] [Linear k C] (M : C) (n : ℕ) {B₀ B₁ : ModuleCat.{v} k}
    (p₀ : (TopTriple.totalPair.obj T).singularCohomology R k M n ⟶ B₀)
    (p₁ : (TopTriple.totalPair.obj T).singularCohomology R k M (n + 1) ⟶ B₁)
    (hp₀ : IsIso (TopPair.singularCohomologyMap (TopTriple.totalToOuter.app T) n ≫ p₀))
    (hp₁ : IsIso (TopPair.singularCohomologyMap (TopTriple.totalToOuter.app T) (n + 1) ≫ p₁)) :
    IsIso (biprod.lift p₀
      (TopPair.singularCohomologyMap (TopTriple.innerToTotal.app T) n)) := by
  have hCS := shortExact_tripleSingularCochainShortComplex T R k M
  let q₀ := TopPair.singularCohomologyMap (R := R) (k := k) (M := M)
    (TopTriple.totalToOuter.app T) n
  let q₁ := TopPair.singularCohomologyMap (R := R) (k := k) (M := M)
    (TopTriple.totalToOuter.app T) (n + 1)
  let i₀ := TopPair.singularCohomologyMap (R := R) (k := k) (M := M)
    (TopTriple.innerToTotal.app T) n
  have hδ : hCS.δ n (n + 1) (by simp) = 0 := by
    rw [← Category.comp_id (hCS.δ n (n + 1) (by simp)), ← IsIso.hom_inv_id (q₁ ≫ p₁),
      ← Category.assoc, ← Category.assoc, hCS.δ_comp n (n + 1) (by simp), zero_comp, zero_comp]
  have hepi : Epi i₀ := (hCS.homology_exact₃ n (n + 1) (by simp)).epi_f hδ
  let r' : (TopTriple.totalPair.obj T).singularCohomology R k M n ⟶
      (TopTriple.outerPair.obj T).singularCohomology R k M n := p₀ ≫ inv (q₀ ≫ p₀)
  have hr' : q₀ ≫ r' = 𝟙 _ := by dsimp only [r']; rw [← Category.assoc]; exact IsIso.hom_inv_id _
  let spl := ShortComplex.Splitting.ofExactOfRetraction _ (hCS.homology_exact₂ n) r' hr' hepi
  have hspl : IsIso (biprod.lift r' i₀) := spl.isoBinaryBiproduct.isIso_hom
  have hfac : biprod.lift r' i₀ ≫ (biprod.mapIso (asIso (q₀ ≫ p₀)) (Iso.refl _)).hom =
      biprod.lift p₀ i₀ :=
    biprod.hom_ext _ _ (by simp [r', biprod.lift_fst_assoc]) (by simp)
  rw [← hfac]; infer_instance

private theorem isZero_singularCohomology_ofSubset_of_eq_univ
    {Z : Type w} [TopologicalSpace Z] {X : Set Z} (hX : X = univ) (R : C)
    (k : Type*) [Ring k] [Linear k C] (M : C) (n : ℕ) :
    IsZero ((TopPair.ofSubset (X := TopCat.of Z) X).singularCohomology R k M n) := by
  have hiso : IsIso (TopPair.ofSubset (X := TopCat.of Z) X).map :=
    ⟨TopCat.ofHom ⟨fun z ↦ ⟨z, hX.symm ▸ mem_univ z⟩, by fun_prop⟩, rfl, rfl⟩
  let S := (TopPair.ofSubset (X := TopCat.of Z) X).singularCochainComplexShortComplex R k M
  have hS := (TopPair.ofSubset (X := TopCat.of Z) X).shortExact_singularCochainComplexShortComplex
    R k M
  have : IsIso S.g := by
    rw [TopPair.singularCochainComplexShortComplex_g_eq]
    exact ⟨TopCat.singularCochainComplexMap (inv (TopPair.ofSubset (X := TopCat.of Z) X).map),
      by rw [← TopCat.singularCochainComplexMap_comp, IsIso.inv_hom_id,
        TopCat.singularCochainComplexMap_id],
      by rw [← TopCat.singularCochainComplexMap_comp, IsIso.hom_inv_id,
        TopCat.singularCochainComplexMap_id]⟩
  have hf0 : S.f = 0 := (cancel_mono S.g).1 (S.zero.trans zero_comp.symm)
  have := hS.mono_f
  have hid : 𝟙 S.X₁ = 0 := (cancel_mono S.f).1 (by rw [Category.id_comp, hf0, zero_comp])
  exact (HomologicalComplex.homologyFunctor _ _ n).map_isZero ((IsZero.iff_id_eq_zero _).2 hid)

end TripleSplitting

/-! ### Attaching a finite family of disc bundles -/

section FiniteFamily

@[simps]
private def singularCohomologyMapIso {C : Type u} [Category.{v} C] [HasCoproducts.{w} C]
    [Abelian C] {P Q : TopPair.{w}} (e : P ≅ Q) (R : C) (k : Type*) [Ring k] [Linear k C]
    (M : C) (n : ℕ) :
    Q.singularCohomology R k M n ≅ P.singularCohomology R k M n where
  hom := TopPair.singularCohomologyMap e.hom n
  inv := TopPair.singularCohomologyMap e.inv n
  hom_inv_id := by
    rw [← TopPair.singularCohomologyMap_comp, e.inv_hom_id, TopPair.singularCohomologyMap_id]
  inv_hom_id := by
    rw [← TopPair.singularCohomologyMap_comp, e.hom_inv_id, TopPair.singularCohomologyMap_id]

private lemma biproductOptionIso_hom_comp_biprod_desc
    {C : Type u} [Category.{v} C] [HasZeroMorphisms C] [HasBinaryBiproducts C]
    [HasFiniteBiproducts C] {α : Type*} [Finite α] (M : Option α → C) {W Y : C}
    (hsomeIso : (⨁ fun j ↦ M (some j)) ≅ W)
    (g₀ : M none ⟶ Y) (g₁ : W ⟶ Y) (φ : ∀ i, M i ⟶ Y) (h0 : g₀ = φ none)
    (hs : ∀ j, biproduct.ι (fun j ↦ M (some j)) j ≫ hsomeIso.hom ≫ g₁ = φ (some j)) :
    (biproductOptionIso M).hom ≫ (biprod.mapIso (Iso.refl (M none)) hsomeIso).hom ≫
      biprod.desc g₀ g₁ = biproduct.desc φ := by
  rw [← Iso.eq_inv_comp]
  refine biprod.hom_ext' _ _ ?_ ?_
  · rw [biprod.mapIso_hom, Iso.refl_hom, biprod.inl_map_assoc, Category.id_comp,
      biprod.inl_desc, ← Category.assoc, biprod_inl_biproductOptionIso_inv, biproduct.ι_desc, h0]
  · rw [biprod.mapIso_hom, biprod.inr_map_assoc, biprod.inr_desc]
    refine biproduct.hom_ext' _ _ fun j ↦ ?_
    rw [hs j, ← biproduct.ι_desc φ (some j), ← biproduct_ι_biprod_inr_biproductOptionIso_inv]
    simp only [Category.assoc]

private lemma biprod_lift_comp_biproductOptionIso_inv
    {C : Type u} [Category.{v} C] [HasZeroMorphisms C] [HasBinaryBiproducts C]
    [HasFiniteBiproducts C] {α : Type*} [Finite α] (N : Option α → C) {X W : C}
    (hsomeIso : W ≅ ⨁ fun j ↦ N (some j))
    (p₀ : X ⟶ N none) (p₁ : X ⟶ W) (ψ : ∀ i, X ⟶ N i) (h0 : p₀ = ψ none)
    (hs : ∀ j, p₁ ≫ hsomeIso.hom ≫ biproduct.π (fun j ↦ N (some j)) j = ψ (some j)) :
    biprod.lift p₀ p₁ ≫ (biprod.mapIso (Iso.refl (N none)) hsomeIso).hom ≫
      (biproductOptionIso N).inv = biproduct.lift ψ := by
  rw [← Category.assoc, Iso.comp_inv_eq]
  refine biprod.hom_ext _ _ ?_ (biproduct.hom_ext _ _ fun j ↦ ?_)
  · simp only [Category.assoc, biprod.mapIso_hom, Iso.refl_hom, biprod.map_fst, Category.comp_id,
      biprod.lift_fst, biproductOptionIso_hom_fst, biproduct.lift_π, h0]
  · simp only [Category.assoc, biprod.mapIso_hom, biprod.map_snd_assoc, biprod.lift_snd_assoc, hs j]
    rw [← biproduct.lift_π ψ (some j), biproductOptionIso_hom_snd_π]

private structure UnitAttachData.{uι, uF', w'} (ι : Type uι) where
  {Z : Type w'}
  [tZ : TopologicalSpace Z]
  X : Set Z
  {B : ι → Type w'}
  {F : ι → Type uF'}
  {E : ∀ i, B i → Type w'}
  [tB : ∀ i, TopologicalSpace (B i)]
  [nF : ∀ i, NormedAddCommGroup (F i)]
  [sF : ∀ i, NormedSpace ℝ (F i)]
  [nE : ∀ i b, NormedAddCommGroup (E i b)]
  [sE : ∀ i b, NormedSpace ℝ (E i b)]
  [tE : ∀ i, TopologicalSpace (TotalSpace (F i) (E i))]
  [fb : ∀ i, FiberBundle (F i) (E i)]
  [vb : ∀ i, VectorBundle ℝ (F i) (E i)]
  hnorm : ∀ i, Continuous fun v : TotalSpace (F i) (E i) ↦ ‖v.2‖
  f : ∀ i, discSpherePair (F i) (E i) ⟶ TopPair.ofSubset (X := TopCat.of Z) X
  hf : ∀ i, IsClosedEmbedding (TopPair.Hom.fst (f i))
  hX : IsClosed X
  hfX : ∀ i (v : discBundle (F i) (E i)),
    TopPair.Hom.fst (f i) v ∈ X → (v : TotalSpace (F i) (E i)) ∈ sphereBundle (F i) (E i)
  hdisj : Pairwise fun i j ↦
    Disjoint (range (TopPair.Hom.fst (f i)) \ X) (range (TopPair.Hom.fst (f j)) \ X)
  hfcover : X ∪ ⋃ i, range (TopPair.Hom.fst (f i)) = univ

attribute [local instance] UnitAttachData.tZ UnitAttachData.tB UnitAttachData.nF UnitAttachData.sF
  UnitAttachData.nE UnitAttachData.sE UnitAttachData.tE UnitAttachData.fb UnitAttachData.vb

private abbrev UnitAttachData.reindex {α β : Type*} (D : UnitAttachData.{_, uF, w} β) (e : α ≃ β) :
    UnitAttachData.{_, uF, w} α :=
  ⟨D.X, fun i ↦ D.hnorm (e i), fun i ↦ D.f (e i), fun i ↦ D.hf (e i), D.hX,
    fun i ↦ D.hfX (e i), fun _ _ hne ↦ D.hdisj (e.injective.ne hne),
    eq_univ_of_forall fun z ↦ (eq_univ_iff_forall.1 D.hfcover z).imp_right fun hz ↦ by
      obtain ⟨b, hb⟩ := mem_iUnion.1 hz
      obtain ⟨a, rfl⟩ := e.surjective b
      exact mem_iUnion.2 ⟨a, hb⟩⟩

section OptionStep

variable {α : Type*} (D : UnitAttachData.{_, uF, w} (Option α))

private def intermediateSubset : Set D.Z :=
  D.X ∪ ⋃ j : α, range (TopPair.Hom.fst (D.f (some j)))

private lemma subset_intermediateSubset : D.X ⊆ intermediateSubset D := subset_union_left

private lemma isClosed_intermediateSubset [Finite α] : IsClosed (intermediateSubset D) :=
  D.hX.union (isClosed_iUnion_of_finite fun j ↦ (D.hf (some j)).isClosed_range)

private def restrictAttachSome (j : α) :
    discSpherePair (D.F (some j)) (D.E (some j)) ⟶
      TopPair.ofSubset (X := TopCat.of (intermediateSubset D)) (Subtype.val ⁻¹' D.X) :=
  TopPair.ofHom
    (TopCat.ofHom ⟨fun v ↦ ⟨TopPair.Hom.fst (D.f (some j)) v, Or.inr (mem_iUnion.2 ⟨j, v, rfl⟩)⟩,
      Continuous.subtype_mk (TopPair.Hom.fst (D.f (some j))).hom.continuous _⟩)
    (TopCat.ofHom ⟨fun v ↦ ⟨⟨(TopPair.Hom.snd (D.f (some j)) v).1,
        Or.inl (TopPair.Hom.snd (D.f (some j)) v).2⟩, (TopPair.Hom.snd (D.f (some j)) v).2⟩,
      Continuous.subtype_mk (Continuous.subtype_mk
        (continuous_subtype_val.comp (TopPair.Hom.snd (D.f (some j))).hom.continuous) _) _⟩)
    (TopCat.ext fun v ↦ Subtype.ext (TopPair.Hom.w_apply (D.f (some j)) v))

private abbrev restrictSomeData [Finite α] : UnitAttachData.{_, uF, w} α :=
  ⟨Subtype.val ⁻¹' D.X, fun j ↦ D.hnorm (some j), restrictAttachSome D,
    fun j ↦ ((isClosed_intermediateSubset D).isClosedEmbedding_subtypeVal.of_comp_iff
      (f := TopPair.Hom.fst (restrictAttachSome D j))).1 (D.hf (some j)),
    D.hX.preimage continuous_subtype_val, fun j v hv ↦ D.hfX (some j) v hv,
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

private lemma mem_sphereBundle_attachNone (v : discBundle (D.F none) (D.E none))
    (hv : TopPair.Hom.fst ((D.f none : _ ⟶ TopTriple.totalPair.obj
        (TopTriple.ofSubset (X := TopCat.of D.Z) (subset_intermediateSubset D))) ≫
      TopTriple.totalToOuter.app
        (TopTriple.ofSubset (X := TopCat.of D.Z) (subset_intermediateSubset D))) v ∈
          intermediateSubset D) :
    (v : TotalSpace (D.F none) (D.E none)) ∈ sphereBundle (D.F none) (D.E none) := by
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
  let f' : ∀ i, discSpherePair (D.F i) (D.E i) ⟶ TopTriple.totalPair.obj T := D.f
  have hnone : ∀ m, IsIso (TopPair.singularHomologyMap (f' none) R m ≫
      TopPair.singularHomologyMap (TopTriple.totalToOuter.app T) R m) := fun m ↦ by
    rw [← TopPair.singularHomologyMap_comp (f' none) R (TopTriple.totalToOuter.app T) m]
    exact isIso_singularHomologyMap_of_attach_discBundle (D.hnorm none)
      (isClosed_intermediateSubset D) R m (D.hf none)
      (mem_sphereBundle_attachNone D) (cover_attachNone D)
  have hsplit := isIso_biprod_desc_triple_singularHomology T R n
    (TopPair.singularHomologyMap (f' none) R n)
    (TopPair.singularHomologyMap (f' none) R (n + 1)) (hnone n) (hnone (n + 1))
  let hsomeIso :=
    asIso (biproduct.desc fun j ↦ TopPair.singularHomologyMap ((restrictSomeData D).f j) R n) ≪≫
      TopPair.singularHomologyMapIso R (innerPairIso D) n
  have hfac := biproductOptionIso_hom_comp_biprod_desc
    (fun i ↦ (discSpherePair (D.F i) (D.E i)).singularHomology R n) hsomeIso
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
  let f' : ∀ i, discSpherePair (D.F i) (D.E i) ⟶ TopTriple.totalPair.obj T := D.f
  have hnone : ∀ m, IsIso
      (TopPair.singularCohomologyMap (R := R) (k := k) (M := M)
          (TopTriple.totalToOuter.app T) m ≫
        TopPair.singularCohomologyMap (f' none) m) := fun m ↦ by
    rw [← TopPair.singularCohomologyMap_comp (R := R) (k := k) (M := M)
      (f' none) (TopTriple.totalToOuter.app T) m]
    exact isIso_singularCohomologyMap_of_attach_discBundle (D.hnorm none)
      (isClosed_intermediateSubset D) R m k M (D.hf none)
      (mem_sphereBundle_attachNone D) (cover_attachNone D)
  have hsplit := isIso_biprod_lift_triple_singularCohomology T R k M n
    (TopPair.singularCohomologyMap (f' none) n)
    (TopPair.singularCohomologyMap (f' none) (n + 1)) (hnone n) (hnone (n + 1))
  let hsomeIso :=
    singularCohomologyMapIso (innerPairIso D) R k M n ≪≫
      asIso (biproduct.lift fun j ↦
        TopPair.singularCohomologyMap (R := R) (k := k) (M := M) ((restrictSomeData D).f j) n)
  have hfac := biprod_lift_comp_biproductOptionIso_inv
    (fun i ↦ (discSpherePair (D.F i) (D.E i)).singularCohomology R k M n) hsomeIso
    (TopPair.singularCohomologyMap (f' none) n)
    (TopPair.singularCohomologyMap (TopTriple.innerToTotal.app T) n)
    (fun i ↦ TopPair.singularCohomologyMap (f' i) n) rfl fun j ↦ by
      rw [Iso.trans_hom, singularCohomologyMapIso_hom, asIso_hom, Category.assoc, biproduct.lift_π,
        ← TopPair.singularCohomologyMap_comp, ← TopPair.singularCohomologyMap_comp, Category.assoc,
        restrictAttachSome_comp_innerToTotal]
  have hiso : IsIso (biproduct.lift fun i ↦
      TopPair.singularCohomologyMap (R := R) (k := k) (M := M) (f' i) n) := by
    rw [← hfac]; infer_instance
  exact hiso

end OptionStep

private theorem isIso_biproductDesc_of_equiv {α β : Type*} [Finite α] [Finite β] (e : α ≃ β)
    {C : Type u} [Category.{v} C] [HasZeroMorphisms C] [HasFiniteBiproducts C]
    {M : β → C} {Y : C} {φ : ∀ b, M b ⟶ Y}
    (h : IsIso (biproduct.desc fun a ↦ φ (e a))) : IsIso (biproduct.desc φ) := by
  let wIso : (⨁ fun a ↦ M (e a)) ≅ ⨁ M := biproduct.whiskerEquiv e fun _ ↦ Iso.refl _
  have hfac : wIso.hom ≫ biproduct.desc φ = biproduct.desc fun a ↦ φ (e a) :=
    biproduct.hom_ext' _ _ fun a ↦ by simp [wIso]
  have : IsIso (wIso.hom ≫ biproduct.desc φ) := by rw [hfac]; exact h
  exact IsIso.of_isIso_comp_left wIso.hom _

private theorem isIso_biproductLift_of_equiv {α β : Type*} [Finite α] [Finite β] (e : α ≃ β)
    {C : Type u} [Category.{v} C] [HasZeroMorphisms C] [HasFiniteBiproducts C]
    {X : C} {M : β → C} {ψ : ∀ b, X ⟶ M b}
    (h : IsIso (biproduct.lift fun a ↦ ψ (e a))) : IsIso (biproduct.lift ψ) := by
  let wIso : ⨁ M ≅ ⨁ fun a ↦ M (e a) :=
    biproduct.whiskerEquiv e.symm fun b ↦ eqToIso (congrArg M (e.apply_symm_apply b))
  have hfac : biproduct.lift (fun a ↦ ψ (e a)) ≫ wIso.inv = biproduct.lift ψ :=
    biproduct.hom_ext _ _ fun b ↦ by
      obtain ⟨a, rfl⟩ := e.surjective b
      rw [Category.assoc, biproduct.whiskerEquiv_inv_eq_lift]; simp
  have : IsIso (biproduct.lift (fun a ↦ ψ (e a)) ≫ wIso.inv) := inferInstance
  rwa [hfac] at this

private theorem isIso_biproductDesc_fin
    {C : Type u} [Category.{v} C] [HasCoproducts.{w} C] [Abelian C] [HasFiniteBiproducts C]
    (R : C) (n : ℕ) :
    ∀ (m : ℕ) (D : UnitAttachData.{_, uF, w} (Fin m)),
      IsIso (biproduct.desc fun i ↦ TopPair.singularHomologyMap (D.f i) R n)
  | 0, D => by
    have hXuniv : D.X = univ := by simpa using D.hfcover
    have htgt := TopPair.isZero_singularHomology_of_surjective_map
      (TopPair.ofSubset (X := TopCat.of D.Z) D.X) R (fun z ↦ ⟨⟨z, hXuniv.symm ▸ mem_univ z⟩, rfl⟩) n
    exact isIso_of_source_target_iso_zero _ (isZero_biproduct_of_isEmpty _).isoZero htgt.isoZero
  | m + 1, D =>
    let e := (finSuccEquiv m).symm
    isIso_biproductDesc_of_equiv e <|
      isIso_biproductDesc_option (D.reindex e) R n
        (isIso_biproductDesc_fin R n m (restrictSomeData (D.reindex e)))

private theorem isIso_biproductLift_fin
    {C : Type u} [Category.{v} C] [HasCoproducts.{w} C] [Abelian C] (R : C)
    (k : Type*) [Ring k] [Linear k C] (M : C) (n : ℕ) :
    ∀ (m : ℕ) (D : UnitAttachData.{_, uF, w} (Fin m)),
      IsIso (biproduct.lift fun i ↦
        TopPair.singularCohomologyMap (R := R) (k := k) (M := M) (D.f i) n)
  | 0, D =>
    isIso_of_source_target_iso_zero _
      (isZero_singularCohomology_ofSubset_of_eq_univ (by simpa using D.hfcover) R k M n).isoZero
      (isZero_biproduct_of_isEmpty _).isoZero
  | m + 1, D =>
    let e := (finSuccEquiv m).symm
    isIso_biproductLift_of_equiv e <|
      isIso_biproductLift_option (D.reindex e) R k M n
        (isIso_biproductLift_fin R k M n m (restrictSomeData (D.reindex e)))

end FiniteFamily

/-! ### Unit-radius and radius-`r` finite-family decompositions -/

public section

section FamilyDecompositions

variable {ι : Type*} [Finite ι]
  {B : ι → Type w} {F : ι → Type uF} {E : ∀ i, B i → Type w}
  [∀ i, TopologicalSpace (B i)] [∀ i, NormedAddCommGroup (F i)] [∀ i, NormedSpace ℝ (F i)]
  [∀ i b, NormedAddCommGroup (E i b)] [∀ i b, NormedSpace ℝ (E i b)]
  [∀ i, TopologicalSpace (TotalSpace (F i) (E i))] [∀ i, FiberBundle (F i) (E i)]
  [∀ i, VectorBundle ℝ (F i) (E i)]
  (hnorm : ∀ i, Continuous fun v : TotalSpace (F i) (E i) ↦ ‖v.2‖)

section UnitRadius

variable {Z : Type w} [TopologicalSpace Z] {X : Set Z}
  {f : ∀ i, discSpherePair (F i) (E i) ⟶ TopPair.ofSubset (X := TopCat.of Z) X}
  (hf : ∀ i, IsClosedEmbedding (TopPair.Hom.fst (f i))) (hX : IsClosed X)
  (hfX : ∀ i (v : discBundle (F i) (E i)),
    TopPair.Hom.fst (f i) v ∈ X → (v : TotalSpace (F i) (E i)) ∈ sphereBundle (F i) (E i))
  (hdisj : Pairwise fun i j ↦
    Disjoint (range (TopPair.Hom.fst (f i)) \ X) (range (TopPair.Hom.fst (f j)) \ X))
  (hfcover : X ∪ ⋃ i, range (TopPair.Hom.fst (f i)) = univ)
  {C : Type u} [Category.{v} C] [HasCoproducts.{w} C] [Abelian C]

include hnorm hf hX hfX hdisj hfcover in
/-- **Attaching a finite family of unit disc bundles induces direct-sum isomorphisms on relative
singular homology.** Let `Eᵢ → Bᵢ` (`i : ι`, `[Finite ι]`) be real vector bundles with continuous
fibre norms, `X` a closed subset of `Z`, and `fᵢ : (D(Eᵢ), S(Eᵢ)) ⟶ (Z, X)` closed embeddings
whose images meet `X` only along `S(Eᵢ)`, whose open disc interiors `fᵢ(D(Eᵢ)) \ X` are pairwise
disjoint, and which together with `X` cover `Z`. Then
`⨁ᵢ Hₙ(D(Eᵢ), S(Eᵢ); R) ⟶ Hₙ(Z, X; R)` is an isomorphism in every degree. -/
theorem isIso_biproductDesc_singularHomologyMap_of_attach_discBundles
    [HasFiniteBiproducts C] (R : C) (n : ℕ) :
    IsIso (biproduct.desc fun i ↦ TopPair.singularHomologyMap (f i) R n) := by
  obtain ⟨m, ⟨e⟩⟩ := Finite.exists_equiv_fin ι
  let D : UnitAttachData.{_, uF, w} ι := ⟨X, hnorm, f, hf, hX, hfX, hdisj, hfcover⟩
  exact isIso_biproductDesc_of_equiv e.symm (isIso_biproductDesc_fin R n m (D.reindex e.symm))

include hnorm hf hX hfX hdisj hfcover in
/-- **Attaching a finite family of unit disc bundles induces direct-sum isomorphisms on relative
singular cohomology.** Under the hypotheses of
`TauCeti.isIso_biproductDesc_singularHomologyMap_of_attach_discBundles`,
`Hⁿ(Z, X) ⟶ ⨁ᵢ Hⁿ(D(Eᵢ), S(Eᵢ))` is an isomorphism in every degree. -/
theorem isIso_biproductLift_singularCohomologyMap_of_attach_discBundles
    (R : C) (k : Type*) [Ring k] [Linear k C] (M : C) (n : ℕ) :
    IsIso (biproduct.lift fun i ↦
      TopPair.singularCohomologyMap (R := R) (k := k) (M := M) (f i) n) := by
  obtain ⟨m, ⟨e⟩⟩ := Finite.exists_equiv_fin ι
  let D : UnitAttachData.{_, uF, w} ι := ⟨X, hnorm, f, hf, hX, hfX, hdisj, hfcover⟩
  exact isIso_biproductLift_of_equiv e.symm (isIso_biproductLift_fin R k M n m (D.reindex e.symm))

/-- **Thom-pair homology decomposition of a finite unit disc-bundle attachment**:
`⨁ᵢ Hₙ(Eᵢ, (Eᵢ)₀; R) ≅ Hₙ(Z, X; R)`. -/
def singularHomologyIsoThomPairsOfAttachDiscBundles [HasFiniteBiproducts C] (R : C) (n : ℕ) :
    (⨁ fun i ↦ (thomPair (F i) (E i)).singularHomology R n) ≅
      (TopPair.ofSubset (X := TopCat.of Z) X).singularHomology R n :=
  (biproduct.mapIso fun i ↦ (@asIso _ _ _ _
      (TopPair.singularHomologyMap (discSpherePairMap (F i) (E i)) R n)
      (isIso_singularHomologyMap_discSpherePairMap (F i) (E i) (hnorm i) R n)).symm) ≪≫
  @asIso _ _ _ _ (biproduct.desc fun i ↦ TopPair.singularHomologyMap (f i) R n)
    (isIso_biproductDesc_singularHomologyMap_of_attach_discBundles hnorm hf hX hfX hdisj hfcover
      R n)

@[reassoc (attr := simp)]
theorem singularHomologyMap_discSpherePairMap_comp_ι_isoThomPairs_hom
    [HasFiniteBiproducts C] (R : C) (n : ℕ) (i : ι) :
    TopPair.singularHomologyMap (discSpherePairMap (F i) (E i)) R n ≫
        biproduct.ι (fun j ↦ (thomPair (F j) (E j)).singularHomology R n) i ≫
          (singularHomologyIsoThomPairsOfAttachDiscBundles
            hnorm hf hX hfX hdisj hfcover R n).hom =
      TopPair.singularHomologyMap (f i) R n := by
  have := isIso_singularHomologyMap_discSpherePairMap (F i) (E i) (hnorm i) R n
  have := isIso_biproductDesc_singularHomologyMap_of_attach_discBundles
    hnorm hf hX hfX hdisj hfcover R n
  simp [singularHomologyIsoThomPairsOfAttachDiscBundles]

/-- **Thom-pair cohomology decomposition of a finite unit disc-bundle attachment**:
`Hⁿ(Z, X; R, M) ≅ ⨁ᵢ Hⁿ(Eᵢ, (Eᵢ)₀; R, M)`. -/
def singularCohomologyIsoThomPairsOfAttachDiscBundles
    (R : C) (k : Type*) [Ring k] [Linear k C] (M : C) (n : ℕ) :
    (TopPair.ofSubset (X := TopCat.of Z) X).singularCohomology R k M n ≅
      ⨁ fun i ↦ (thomPair (F i) (E i)).singularCohomology R k M n :=
  @asIso _ _ _ _ (biproduct.lift fun i ↦
      TopPair.singularCohomologyMap (R := R) (k := k) (M := M) (f i) n)
    (isIso_biproductLift_singularCohomologyMap_of_attach_discBundles
      hnorm hf hX hfX hdisj hfcover R k M n) ≪≫
  biproduct.mapIso fun i ↦ (@asIso _ _ _ _
      (TopPair.singularCohomologyMap (R := R) (k := k) (M := M)
        (discSpherePairMap (F i) (E i)) n)
      (isIso_singularCohomologyMap_discSpherePairMap (F i) (E i) (hnorm i) R k M n)).symm

@[reassoc (attr := simp)]
theorem singularCohomologyIsoThomPairsOfAttachDiscBundles_hom_comp_π_comp
    (R : C) (k : Type*) [Ring k] [Linear k C] (M : C) (n : ℕ) (i : ι) :
    (singularCohomologyIsoThomPairsOfAttachDiscBundles
        hnorm hf hX hfX hdisj hfcover R k M n).hom ≫
      biproduct.π (fun j ↦ (thomPair (F j) (E j)).singularCohomology R k M n) i ≫
      TopPair.singularCohomologyMap (discSpherePairMap (F i) (E i)) n =
      TopPair.singularCohomologyMap (f i) n := by
  have := isIso_singularCohomologyMap_discSpherePairMap (F i) (E i) (hnorm i) R k M n
  have := isIso_biproductLift_singularCohomologyMap_of_attach_discBundles
    hnorm hf hX hfX hdisj hfcover R k M n
  simp [singularCohomologyIsoThomPairsOfAttachDiscBundles]

end UnitRadius

section Radius

variable {r : ∀ i, B i → ℝ} (hr : ∀ i, Continuous (r i)) (hrpos : ∀ i b, 0 < r i b)

section Subset

variable {Z : Type w} [TopologicalSpace Z] {X : Set Z}
  {f : ∀ i, discSpherePairOfRadius (F i) (E i) (r i) ⟶ TopPair.ofSubset (X := TopCat.of Z) X}
  (hf : ∀ i, IsClosedEmbedding (TopPair.Hom.fst (f i))) (hX : IsClosed X)
  (hfX : ∀ i (v : discBundleOfRadius (F i) (E i) (r i)),
    TopPair.Hom.fst (f i) v ∈ X →
      (v : TotalSpace (F i) (E i)) ∈ sphereBundleOfRadius (F i) (E i) (r i))
  (hdisj : Pairwise fun i j ↦
    Disjoint (range (TopPair.Hom.fst (f i)) \ X) (range (TopPair.Hom.fst (f j)) \ X))
  (hfcover : X ∪ ⋃ i, range (TopPair.Hom.fst (f i)) = univ)

omit [Finite ι] in
include hr hrpos hdisj in
private lemma pairwise_disjoint_rescaledFamily :
    Pairwise fun i j ↦
      Disjoint
        (range (TopPair.Hom.fst
          ((discSpherePairIsoOfRadius (F i) (E i) (hr i) (hrpos i)).hom ≫ f i)) \ X)
        (range (TopPair.Hom.fst
          ((discSpherePairIsoOfRadius (F j) (E j) (hr j) (hrpos j)).hom ≫ f j)) \ X) :=
  fun i j hij ↦ disjoint_left.2 fun _ ⟨hz₁, hzX⟩ ⟨hz₂, _⟩ ↦
    disjoint_left.1 (hdisj hij)
      ⟨(mem_range_fst_discSpherePairIsoOfRadius_hom_comp (hr i) (hrpos i)).1 hz₁, hzX⟩
      ⟨(mem_range_fst_discSpherePairIsoOfRadius_hom_comp (hr j) (hrpos j)).1 hz₂, hzX⟩

omit [Finite ι] in
include hr hrpos hfcover in
private lemma cover_rescaledFamily :
    X ∪ ⋃ i, range (TopPair.Hom.fst
      ((discSpherePairIsoOfRadius (F i) (E i) (hr i) (hrpos i)).hom ≫ f i)) = univ :=
  eq_univ_of_forall fun z ↦ (eq_univ_iff_forall.1 hfcover z).imp_right fun hz ↦ by
    obtain ⟨i, hzi⟩ := mem_iUnion.1 hz
    exact mem_iUnion.2 ⟨i,
      (mem_range_fst_discSpherePairIsoOfRadius_hom_comp (hr i) (hrpos i)).2 hzi⟩

variable {C : Type u} [Category.{v} C] [HasCoproducts.{w} C] [Abelian C]

include hnorm hr hrpos hf hX hfX hdisj hfcover in
/-- **Attaching a finite family of disc bundles of positive continuous radii induces direct-sum
isomorphisms on relative singular homology**:
`⨁ᵢ Hₙ(D_{rᵢ}(Eᵢ), S_{rᵢ}(Eᵢ); R) ≅ Hₙ(Z, X; R)`. -/
theorem isIso_biproductDesc_singularHomologyMap_of_attach_discBundlesOfRadius
    [HasFiniteBiproducts C] (R : C) (n : ℕ) :
    IsIso (biproduct.desc fun i ↦ TopPair.singularHomologyMap (f i) R n) := by
  let g := fun i ↦ (discSpherePairIsoOfRadius (F i) (E i) (hr i) (hrpos i)).hom ≫ f i
  have hg : IsIso (biproduct.desc fun i ↦ TopPair.singularHomologyMap (g i) R n) :=
    isIso_biproductDesc_singularHomologyMap_of_attach_discBundles hnorm
      (fun i ↦ isClosedEmbedding_fst_discSpherePairIsoOfRadius_hom_comp (hr i) (hrpos i) (hf i)) hX
      (fun i ↦ mem_sphereBundle_of_discSpherePairIsoOfRadius_hom_comp_mem (hr i) (hrpos i) (hfX i))
      (pairwise_disjoint_rescaledFamily hr hrpos hdisj)
      (cover_rescaledFamily hr hrpos hfcover) R n
  let rescaleIso := biproduct.mapIso fun i ↦
    TopPair.singularHomologyMapIso R (discSpherePairIsoOfRadius (F i) (E i) (hr i) (hrpos i)) n
  have hfac : rescaleIso.hom ≫ biproduct.desc (fun i ↦ TopPair.singularHomologyMap (f i) R n) =
      biproduct.desc (fun i ↦ TopPair.singularHomologyMap (g i) R n) := by
    simp [rescaleIso, g, TopPair.singularHomologyMap_comp]
  have : IsIso
      (rescaleIso.hom ≫ biproduct.desc (fun i ↦ TopPair.singularHomologyMap (f i) R n)) := by
    rw [hfac]; exact hg
  exact IsIso.of_isIso_comp_left rescaleIso.hom _

include hnorm hr hrpos hf hX hfX hdisj hfcover in
/-- **Attaching a finite family of disc bundles of positive continuous radii induces direct-sum
isomorphisms on relative singular cohomology**:
`Hⁿ(Z, X; R, M) ≅ ⨁ᵢ Hⁿ(D_{rᵢ}(Eᵢ), S_{rᵢ}(Eᵢ); R, M)`. -/
theorem isIso_biproductLift_singularCohomologyMap_of_attach_discBundlesOfRadius
    (R : C) (k : Type*) [Ring k] [Linear k C] (M : C) (n : ℕ) :
    IsIso (biproduct.lift fun i ↦
      TopPair.singularCohomologyMap (R := R) (k := k) (M := M) (f i) n) := by
  let g := fun i ↦ (discSpherePairIsoOfRadius (F i) (E i) (hr i) (hrpos i)).hom ≫ f i
  have hg : IsIso (biproduct.lift fun i ↦
      TopPair.singularCohomologyMap (R := R) (k := k) (M := M) (g i) n) :=
    isIso_biproductLift_singularCohomologyMap_of_attach_discBundles hnorm
      (fun i ↦ isClosedEmbedding_fst_discSpherePairIsoOfRadius_hom_comp (hr i) (hrpos i) (hf i)) hX
      (fun i ↦ mem_sphereBundle_of_discSpherePairIsoOfRadius_hom_comp_mem (hr i) (hrpos i) (hfX i))
      (pairwise_disjoint_rescaledFamily hr hrpos hdisj)
      (cover_rescaledFamily hr hrpos hfcover) R k M n
  let rescaleIso := biproduct.mapIso fun i ↦
    singularCohomologyMapIso (discSpherePairIsoOfRadius (F i) (E i) (hr i) (hrpos i)) R k M n
  have hfac : biproduct.lift (fun i ↦
        TopPair.singularCohomologyMap (R := R) (k := k) (M := M) (f i) n) ≫ rescaleIso.hom =
      biproduct.lift (fun i ↦ TopPair.singularCohomologyMap (g i) n) := by
    simp [rescaleIso, g, TopPair.singularCohomologyMap_comp]
  have : IsIso (biproduct.lift (fun i ↦
      TopPair.singularCohomologyMap (R := R) (k := k) (M := M) (f i) n) ≫ rescaleIso.hom) := by
    rw [hfac]; exact hg
  exact IsIso.of_isIso_comp_right _ rescaleIso.hom

/-- **Thom-pair homology decomposition of a finite radius-`r` disc-bundle attachment**:
`⨁ᵢ Hₙ(Eᵢ, (Eᵢ)₀; R) ≅ Hₙ(Z, X; R)`. -/
def singularHomologyIsoThomPairsOfAttachDiscBundlesOfRadius
    [HasFiniteBiproducts C] (R : C) (n : ℕ) :
    (⨁ fun i ↦ (thomPair (F i) (E i)).singularHomology R n) ≅
      (TopPair.ofSubset (X := TopCat.of Z) X).singularHomology R n :=
  (biproduct.mapIso fun i ↦ (@asIso _ _ _ _
      (TopPair.singularHomologyMap
        (discSpherePairOfRadiusMap (F i) (E i) fun b ↦ (hrpos i b).ne') R n)
      (isIso_singularHomologyMap_discSpherePairOfRadiusMap
        (F i) (E i) (hnorm i) (hr i) (hrpos i) R n)).symm) ≪≫
  @asIso _ _ _ _ (biproduct.desc fun i ↦ TopPair.singularHomologyMap (f i) R n)
    (isIso_biproductDesc_singularHomologyMap_of_attach_discBundlesOfRadius
      hnorm hr hrpos hf hX hfX hdisj hfcover R n)

@[reassoc (attr := simp)]
theorem singularHomologyMap_discSpherePairOfRadiusMap_comp_ι_isoThomPairs_hom
    [HasFiniteBiproducts C] (R : C) (n : ℕ) (i : ι) :
    TopPair.singularHomologyMap
          (discSpherePairOfRadiusMap (F i) (E i) fun b ↦ (hrpos i b).ne') R n ≫
        biproduct.ι (fun j ↦ (thomPair (F j) (E j)).singularHomology R n) i ≫
          (singularHomologyIsoThomPairsOfAttachDiscBundlesOfRadius
            hnorm hr hrpos hf hX hfX hdisj hfcover R n).hom =
      TopPair.singularHomologyMap (f i) R n := by
  have := isIso_singularHomologyMap_discSpherePairOfRadiusMap
    (F i) (E i) (hnorm i) (hr i) (hrpos i) R n
  have := isIso_biproductDesc_singularHomologyMap_of_attach_discBundlesOfRadius
    hnorm hr hrpos hf hX hfX hdisj hfcover R n
  simp [singularHomologyIsoThomPairsOfAttachDiscBundlesOfRadius]

/-- **Thom-pair cohomology decomposition of a finite radius-`r` disc-bundle attachment**:
`Hⁿ(Z, X; R, M) ≅ ⨁ᵢ Hⁿ(Eᵢ, (Eᵢ)₀; R, M)`. -/
def singularCohomologyIsoThomPairsOfAttachDiscBundlesOfRadius
    (R : C) (k : Type*) [Ring k] [Linear k C] (M : C) (n : ℕ) :
    (TopPair.ofSubset (X := TopCat.of Z) X).singularCohomology R k M n ≅
      ⨁ fun i ↦ (thomPair (F i) (E i)).singularCohomology R k M n :=
  @asIso _ _ _ _ (biproduct.lift fun i ↦
      TopPair.singularCohomologyMap (R := R) (k := k) (M := M) (f i) n)
    (isIso_biproductLift_singularCohomologyMap_of_attach_discBundlesOfRadius
      hnorm hr hrpos hf hX hfX hdisj hfcover R k M n) ≪≫
  biproduct.mapIso fun i ↦ (@asIso _ _ _ _
      (TopPair.singularCohomologyMap (R := R) (k := k) (M := M)
        (discSpherePairOfRadiusMap (F i) (E i) fun b ↦ (hrpos i b).ne') n)
      (isIso_singularCohomologyMap_discSpherePairOfRadiusMap
        (F i) (E i) (hnorm i) (hr i) (hrpos i) R k M n)).symm

@[reassoc (attr := simp)]
theorem singularCohomologyIsoThomPairsOfAttachDiscBundlesOfRadius_hom_comp_π_comp
    (R : C) (k : Type*) [Ring k] [Linear k C] (M : C) (n : ℕ) (i : ι) :
    (singularCohomologyIsoThomPairsOfAttachDiscBundlesOfRadius
        hnorm hr hrpos hf hX hfX hdisj hfcover R k M n).hom ≫
      biproduct.π (fun j ↦ (thomPair (F j) (E j)).singularCohomology R k M n) i ≫
      TopPair.singularCohomologyMap
        (discSpherePairOfRadiusMap (F i) (E i) fun b ↦ (hrpos i b).ne') n =
      TopPair.singularCohomologyMap (f i) n := by
  have := isIso_singularCohomologyMap_discSpherePairOfRadiusMap
    (F i) (E i) (hnorm i) (hr i) (hrpos i) R k M n
  have := isIso_biproductLift_singularCohomologyMap_of_attach_discBundlesOfRadius
    hnorm hr hrpos hf hX hfX hdisj hfcover R k M n
  simp [singularCohomologyIsoThomPairsOfAttachDiscBundlesOfRadius]

end Subset

section DeformationRetract

variable {M : Type w} [TopologicalSpace M] {X Z Y : Set M} (hXZ : X ⊆ Z) (hZY : Z ⊆ Y)
  {f : ∀ i, discSpherePairOfRadius (F i) (E i) (r i) ⟶ TopPair.ofInclusion (X := TopCat.of M) hXZ}
  (hf : ∀ i, IsClosedEmbedding (TopPair.Hom.fst (f i)))
  (hX : IsClosed (Subtype.val ⁻¹' X : Set Z))
  (hfX : ∀ i (v : discBundleOfRadius (F i) (E i) (r i)),
    TopPair.Hom.fst (f i) v ∈ (Subtype.val ⁻¹' X : Set Z) →
      (v : TotalSpace (F i) (E i)) ∈ sphereBundleOfRadius (F i) (E i) (r i))
  (hdisj : Pairwise fun i j ↦
    Disjoint (range (TopPair.Hom.fst (f i)) \ Subtype.val ⁻¹' X)
      (range (TopPair.Hom.fst (f j)) \ Subtype.val ⁻¹' X))
  (hfcover : (Subtype.val ⁻¹' X : Set Z) ∪ ⋃ i, range (TopPair.Hom.fst (f i)) = univ)
  (ret : C(Y, Z))
  (G : ((ContinuousMap.inclusion hZY).comp ret).HomotopyRel (ContinuousMap.id Y)
    {y | (y : M) ∈ Z})

omit [Finite ι] [∀ i, TopologicalSpace (B i)] [∀ i, NormedAddCommGroup (F i)]
  [∀ i, NormedSpace ℝ (F i)] [∀ i b, NormedSpace ℝ (E i b)] [∀ i, FiberBundle (F i) (E i)]
  [∀ i, VectorBundle ℝ (F i) (E i)] in
private lemma fst_comp_ofSubsetPreimageValIso_inv (i : ι) :
    TopPair.Hom.fst (f i ≫ (TopPair.ofSubsetPreimageValIso (X := TopCat.of M) hXZ).inv) =
      TopPair.Hom.fst (f i) :=
  TopCat.ext fun v ↦ (ConcreteCategory.comp_apply _ _ v).trans
    (TopPair.ofSubsetPreimageValIso_inv_fst_apply (TopPair.Hom.fst (f i) v))

variable {C : Type u} [Category.{v} C] [HasCoproducts.{w} C] [Abelian C] [HasFiniteBiproducts C]

/-- **Thom-pair homology across an ambient strong deformation retract onto an attached disc-bundle
complex.** Let `X ⊆ Z ⊆ Y` be nested subsets of `M` such that `X` is closed in `Z`, `Z` is obtained
from `X` by attaching a finite family of disc bundles `D_{rᵢ}(Eᵢ)` along `S_{rᵢ}(Eᵢ)`, and `Y`
strong deformation retracts onto `Z`. Then `⨁ᵢ Hₙ(Eᵢ, (Eᵢ)₀; R) ≅ Hₙ(Y, X; R)`. Across a Morse–Bott
critical level `c`, taking `X = {g ≤ c - ε}`, `Y = {g ≤ c + ε}` and `Z` the lower sublevel union the
attached negative disc bundles computes the relative homology of the sublevel pair. -/
def singularHomologyIsoThomPairsOfDeformationRetractAttachDiscBundlesOfRadius (R : C) (n : ℕ) :
    (⨁ fun i ↦ (thomPair (F i) (E i)).singularHomology R n) ≅
      (TopPair.ofInclusion (X := TopCat.of M) (hXZ.trans hZY)).singularHomology R n :=
  singularHomologyIsoThomPairsOfAttachDiscBundlesOfRadius (Z := Z) (X := Subtype.val ⁻¹' X)
      (f := fun i ↦ f i ≫ (TopPair.ofSubsetPreimageValIso (X := TopCat.of M) hXZ).inv)
      hnorm hr hrpos
      (fun i ↦ (fst_comp_ofSubsetPreimageValIso_inv hXZ (f := f) i).symm ▸ hf i) hX
      (fun i v hv ↦ hfX i v (by rwa [fst_comp_ofSubsetPreimageValIso_inv] at hv))
      (show Pairwise fun i j ↦ Disjoint _ _ from fun i j hij ↦
        disjoint_left.2 fun _ ⟨hz₁, hzX⟩ ⟨hz₂, _⟩ ↦ disjoint_left.1 (hdisj hij)
          ⟨by rwa [fst_comp_ofSubsetPreimageValIso_inv] at hz₁, hzX⟩
          ⟨by rwa [fst_comp_ofSubsetPreimageValIso_inv] at hz₂, hzX⟩)
      (eq_univ_of_forall fun z ↦ (eq_univ_iff_forall.1 hfcover z).imp_right fun hz ↦ by
        obtain ⟨i, hzi⟩ := mem_iUnion.1 hz
        exact mem_iUnion.2 ⟨i, by rwa [fst_comp_ofSubsetPreimageValIso_inv]⟩) R n ≪≫
    TopPair.singularHomologyMapIso R (TopPair.ofSubsetPreimageValIso (X := TopCat.of M) hXZ) n ≪≫
    @asIso _ _ _ _ _
      (TopPair.isIso_singularHomologyMap_ofInclusionMap_inclusion_of_homotopyRel
        (X := TopCat.of M) hXZ hZY ret G R n)

@[reassoc (attr := simp)]
theorem singularHomologyMap_discSpherePairOfRadiusMap_comp_ι_isoDeformationRetract_hom
    (R : C) (n : ℕ) (i : ι) :
    TopPair.singularHomologyMap
          (discSpherePairOfRadiusMap (F i) (E i) fun b ↦ (hrpos i b).ne') R n ≫
        biproduct.ι (fun j ↦ (thomPair (F j) (E j)).singularHomology R n) i ≫
          (singularHomologyIsoThomPairsOfDeformationRetractAttachDiscBundlesOfRadius
            hnorm hr hrpos hXZ hZY hf hX hfX hdisj hfcover ret G R n).hom =
      TopPair.singularHomologyMap
        (f i ≫ TopPair.ofInclusionMap hXZ (hXZ.trans hZY) (ContinuousMap.inclusion hZY)
          fun _ hx ↦ by simpa using hx) R n := by
  have := TopPair.isIso_singularHomologyMap_ofInclusionMap_inclusion_of_homotopyRel
    (X := TopCat.of M) hXZ hZY ret G R n
  rw [singularHomologyIsoThomPairsOfDeformationRetractAttachDiscBundlesOfRadius, Iso.trans_hom,
    Iso.trans_hom, TopPair.singularHomologyMapIso_hom, asIso_hom,
    singularHomologyMap_discSpherePairOfRadiusMap_comp_ι_isoThomPairs_hom_assoc,
    ← TopPair.singularHomologyMap_comp_assoc, Category.assoc, Iso.inv_hom_id, Category.comp_id,
    ← TopPair.singularHomologyMap_comp]

end DeformationRetract

end Radius

end FamilyDecompositions

end

end TauCeti
