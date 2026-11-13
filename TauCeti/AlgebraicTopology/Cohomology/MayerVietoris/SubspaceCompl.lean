/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Cohomology.MayerVietoris.Cup
public import TauCeti.AlgebraicTopology.Cohomology.UniversalCoefficient
public import TauCeti.AlgebraicTopology.Singular.MayerVietoris.SubspaceCompl

/-!
# Cohomology modulo the preimage of the complement of a subspace

Let `q : X → F` be a continuous map to a real normed space of finite dimension `r`, and let `K` be
a commutative ring. For a subspace `W` of `F`, `TauCeti.subspaceComplPair q W` is the pair
`(X, q⁻¹(F ∖ W))`. Assume, as in `TauCeti.isZero_singularHomology_subspaceComplPair`, that `X` is
acyclic with coefficients in `K` modulo the preimage of the complement of every closed
half-subspace of `F`. This file shows that the relative cohomology of `(X, q⁻¹(F ∖ W))` is a free
module of rank one over the cohomology of `X`, on a generator pulled back from `F`: there is a
class `g ∈ Hᶜ(F, F ∖ W; K)`, `c` the codimension of `W`, such that for every such `X` and `q` and
every module `M` of coefficients, cupping with `q^* g` is a bijection

`Hⁿ(X; M) ⟶ Hⁿ⁺ᶜ(X, q⁻¹(F ∖ W); M)`,  `a ↦ a ⌣ q^* g`

(`TauCeti.exists_bijective_singularCup_subspaceComplPair`). For `X = B × F` and the projection
`q` to `F`, with `W = 0`, this is the Thom isomorphism of the product bundle `B × F → B`.

The proof removes one dimension at a time, as in homology. For an extension `W ⊆ W'` of `W` by a
line (`Submodule.LineExtension`), `q⁻¹(F ∖ W)` is the union of the two open sets
`q⁻¹(F ∖ {y ∈ W' | ±ψ y ≤ 0})`, which intersect in `q⁻¹(F ∖ W')`. Modulo either of them, `X` has
vanishing cohomology, so the connecting morphism of the Mayer–Vietoris sequence of the two pairs
(`TopCat.singularCohomologyPairMayerVietorisδ`) is an isomorphism
`Hⁿ(X, q⁻¹(F ∖ W')) ≅ Hⁿ⁺¹(X, q⁻¹(F ∖ W))`. It is natural in maps over `F`, and it is linear over
the cohomology of `X` up to the sign `(-1)ᵖ`
(`TopCat.singularCohomologyPairMayerVietorisδ_singularCup_singularCohomologyMap`). So if cupping
with `q^* g'` is bijective for `W'`, then so is cupping with `q^* δ g' = δ q^* g'` for `W`.
Starting from `W = F`, where `q⁻¹(F ∖ W)` is empty and `g = 1`, and repeating `c` times reaches
`W`.

## Main results

* `TauCeti.exists_bijective_singularCup_subspaceComplPair`: cupping with a class pulled back from
  `(F, F ∖ W)` identifies the cohomology of `X` with that of `(X, q⁻¹(F ∖ W))`, shifted by the
  codimension of `W`.

## References

* A. Hatcher, *Algebraic Topology*, Section 4.D, Theorem 4D.10 and its proof (the Thom
  isomorphism, first for a product bundle).
* J. W. Milnor, J. D. Stasheff, *Characteristic Classes*, Annals of Mathematics Studies 76,
  Princeton (1974), §10, proof of Theorem 10.4 (the case of a trivial bundle).
-/

public section

noncomputable section

open CategoryTheory Limits MonoidalCategory Module

universe w

namespace TauCeti

variable {K : Type w} [CommRing K] {F : Type w} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {X : TopCat.{w}} (q : C(X, F))

namespace SubspaceComplPair

/-- The preimage of the complement of the closed half-subspace `{y ∈ W | ψ y ≤ 0}`. -/
private abbrev half (W : Submodule ℝ F) (ψ : F →ₗ[ℝ] ℝ) : Set X :=
  q ⁻¹' {y | y ∈ W ∧ ψ y ≤ 0}ᶜ

private lemma isOpen_half [FiniteDimensional ℝ F] (W : Submodule ℝ F) (ψ : F →ₗ[ℝ] ℝ) :
    IsOpen (half q W ψ) :=
  ((W.isClosed_of_finiteDimensional.inter (isClosed_le ψ.continuous_of_finiteDimensional
    continuous_const)).isOpen_compl).preimage q.continuous

variable {W : Submodule ℝ F} (s : W.LineExtension)

/-- The two half-subspace complements of a step, as subsets of `Set.univ`. -/
private lemma half_subset_univ (ψ : F →ₗ[ℝ] ℝ) : half q s.W' ψ ⊆ Set.univ :=
  Set.subset_univ _

private lemma mem_half_inter_half_iff (x : X) :
    x ∈ half q s.W' s.extend ∩ half q s.W' (-s.extend) ↔ q x ∈ (s.W' : Set F)ᶜ := by
  rw [← Set.preimage_inter, s.compl_inter_compl]
  rfl

private lemma mem_half_union_half_iff (x : X) :
    x ∈ half q s.W' s.extend ∪ half q s.W' (-s.extend) ↔ q x ∈ (W : Set F)ᶜ := by
  rw [← Set.preimage_union, s.compl_union_compl s.extend_comp_subtype]
  rfl

/-- The pair `(univ ∩ univ, half₊ ∩ half₋)` of the Mayer–Vietoris sequence of the two
half-subspace complements of a step. -/
private abbrev interPair : TopPair.{w} :=
  TopPair.ofInclusion (Set.inter_subset_inter (half_subset_univ q s s.extend)
    (half_subset_univ q s (-s.extend)))

/-- The pair `(univ ∪ univ, half₊ ∪ half₋)` of the Mayer–Vietoris sequence of the two
half-subspace complements of a step. -/
private abbrev unionPair : TopPair.{w} :=
  TopPair.ofInclusion (Set.union_subset_union (half_subset_univ q s s.extend)
    (half_subset_univ q s (-s.extend)))

/-- The intersection pair of the Mayer–Vietoris sequence of the two half-subspace complements of
a step is `(X, q⁻¹(F ∖ W'))`. -/
private def interIso : interPair q s ≅ subspaceComplPair q s.W' :=
  TopPair.ofInclusionIsoOfSubset (Set.inter_subset_inter (half_subset_univ q s s.extend)
    (half_subset_univ q s (-s.extend))) (fun _ ↦ ⟨trivial, trivial⟩) (mem_half_inter_half_iff q s)

/-- The pair `(X, q⁻¹(F ∖ W))` is the union pair of the Mayer–Vietoris sequence of the two
half-subspace complements of a step. -/
private def unionIso : subspaceComplPair q W ≅ unionPair q s :=
  (TopPair.ofInclusionIsoOfSubset (Set.union_subset_union (half_subset_univ q s s.extend)
    (half_subset_univ q s (-s.extend))) (fun _ ↦ Or.inl trivial)
      (mem_half_union_half_iff q s)).symm

private lemma interIso_hom_fst : TopPair.Hom.fst (interIso q s).hom =
    TopCat.ofHom (ContinuousMap.subtypeVal ((Set.univ : Set X) ∩ Set.univ)) :=
  TopCat.ext fun x ↦ TopPair.ofInclusionIsoOfSubset_hom_fst_apply _ _ x

private lemma unionIso_inv_fst : TopPair.Hom.fst (unionIso q s).inv =
    TopCat.ofHom (ContinuousMap.subtypeVal ((Set.univ : Set X) ∪ Set.univ)) :=
  TopCat.ext fun x ↦ TopPair.ofInclusionIsoOfSubset_hom_fst_apply _ _ x

private lemma unionIso_hom_fst_comp : TopPair.Hom.fst (unionIso q s).hom ≫
    TopCat.ofHom (ContinuousMap.subtypeVal ((Set.univ : Set X) ∪ Set.univ)) = 𝟙 X := by
  have h := congrArg TopPair.Hom.fst (unionIso q s).hom_inv_id
  rw [TopPair.Hom.fst_comp, unionIso_inv_fst, TopPair.Hom.fst_id] at h
  exact h

private lemma unionIso_hom_fst_apply (x : X) : (TopPair.Hom.fst (unionIso q s).hom x).1 = x :=
  ConcreteCategory.congr_hom (unionIso_hom_fst_comp q s) x

variable [FiniteDimensional ℝ F]

private lemma isOpen_univ_union : IsOpen ((↑) ⁻¹' (Set.univ : Set X) :
    Set ↥((Set.univ : Set X) ∪ Set.univ)) :=
  isOpen_univ.preimage continuous_subtype_val

private lemma isOpen_half_left :
    IsOpen ((↑) ⁻¹' half q s.W' s.extend : Set ↥(half q s.W' s.extend ∪ half q s.W' (-s.extend))) :=
  (isOpen_half q _ _).preimage continuous_subtype_val

private lemma isOpen_half_right :
    IsOpen ((↑) ⁻¹' half q s.W' (-s.extend) :
      Set ↥(half q s.W' s.extend ∪ half q s.W' (-s.extend))) :=
  (isOpen_half q _ _).preimage continuous_subtype_val

variable (R M : ModuleCat.{w} K)

/-- The connecting morphism `Hⁿ(X, q⁻¹(F ∖ W')) ⟶ Hⁿ⁺¹(X, q⁻¹(F ∖ W))` of a step: the
Mayer–Vietoris connecting morphism of the pairs `(X, q⁻¹(F ∖ {y ∈ W' | ±ψ y ≤ 0}))`. -/
private def stepδ (n m : ℕ) (h : n + 1 = m) :
    (subspaceComplPair q s.W').singularCohomology R K M n ⟶
      (subspaceComplPair q W).singularCohomology R K M m :=
  TopPair.singularCohomologyMap (interIso q s).hom n ≫
    TopCat.singularCohomologyPairMayerVietorisδ R K M (half_subset_univ q s s.extend)
      (half_subset_univ q s (-s.extend)) isOpen_univ_union isOpen_univ_union
      (isOpen_half_left q s) (isOpen_half_right q s) n m h ≫
    TopPair.singularCohomologyMap (unionIso q s).hom m

/-- **The connecting morphism of a step is linear over the cohomology of `X`, up to sign**:
`δ (a ⌣ y) = (-1)ᵖ a ⌣ δ y` for `a ∈ Hᵖ(X)`. -/
private lemma stepδ_singularCup {R' M' S N T L : ModuleCat.{w} K} (u : T ⟶ R' ⊗ S)
    (μ : M' ⊗ N ⟶ L) {p i n j m : ℕ} (h : p + i = n) (hj : i + 1 = j) (hm : n + 1 = m)
    (h' : p + j = m) (a : X.singularCohomology R' K M' p)
    (y : (subspaceComplPair q s.W').singularCohomology S K N i) :
    stepδ q s T L n m hm ((subspaceComplPair q s.W').singularCup K u μ p i n h a y) =
      ((-1 : ℤ) ^ p) • (subspaceComplPair q W).singularCup K u μ p j m h' a
        (stepδ q s S N i j hj y) := by
  simp only [stepδ, ConcreteCategory.comp_apply]
  -- The ambient space of `subspaceComplPair q _` is `X` only up to unfolding `TopPair.ofSubset`,
  -- so the classes of `X` appear at two syntactically different types and `rw` cannot match them;
  -- `erw` matches up to that unfolding.
  have e₁ := TopPair.singularCup_naturality K (interIso q s).hom u μ p i n h a y
  rw [interIso_hom_fst] at e₁
  erw [← e₁]
  erw [TopCat.singularCohomologyPairMayerVietorisδ_singularCup_singularCohomologyMap K
      (half_subset_univ q s s.extend) (half_subset_univ q s (-s.extend)) (isOpen_half_left q s)
      (isOpen_half_right q s) isOpen_univ_union isOpen_univ_union u μ h hj hm h']
  rw [map_zsmul]
  have e₂ := TopPair.singularCup_naturality K (unionIso q s).hom u μ p j m h'
    (TopCat.singularCohomologyMap (TopCat.ofHom (ContinuousMap.subtypeVal
      ((Set.univ : Set X) ∪ Set.univ))) p a)
    (TopCat.singularCohomologyPairMayerVietorisδ S K N (half_subset_univ q s s.extend)
      (half_subset_univ q s (-s.extend)) isOpen_univ_union isOpen_univ_union
      (isOpen_half_left q s) (isOpen_half_right q s) i j hj
      (TopPair.singularCohomologyMap (interIso q s).hom i y))
  have ha : TopCat.singularCohomologyMap (TopPair.Hom.fst (unionIso q s).hom) p
      (TopCat.singularCohomologyMap (TopCat.ofHom (ContinuousMap.subtypeVal
        ((Set.univ : Set X) ∪ Set.univ))) p a) = a := by
    have hcomp := TopCat.singularCohomologyMap_comp (R := R') (k := K) (M := M')
      (TopPair.Hom.fst (unionIso q s).hom)
      (TopCat.ofHom (ContinuousMap.subtypeVal ((Set.univ : Set X) ∪ Set.univ))) p
    rw [unionIso_hom_fst_comp] at hcomp
    erw [TopCat.singularCohomologyMap_id] at hcomp
    exact (ConcreteCategory.congr_hom hcomp a).symm
  rw [ha] at e₂
  erw [← e₂]

section Naturality

variable {q} {X' : TopCat.{w}} {q' : C(X', F)} (f : X ⟶ X') (hf : ∀ x, q' (f x) = q x)

omit [FiniteDimensional ℝ F] in
include hf in
private lemma mapsTo_half (ψ : F →ₗ[ℝ] ℝ) : Set.MapsTo f (half q s.W' ψ) (half q' s.W' ψ) :=
  fun x hx ↦ by rw [Set.mem_preimage, hf]; exact hx

/-- **Naturality of the connecting morphism of a step** in maps over `F`. -/
private lemma singularCohomologyMap_subspaceComplPairMap_comp_stepδ (n m : ℕ) (h : n + 1 = m) :
    TopPair.singularCohomologyMap (subspaceComplPairMap f hf s.W') n ≫ stepδ q s R M n m h =
      stepδ q' s R M n m h ≫ TopPair.singularCohomologyMap (subspaceComplPairMap f hf W) m := by
  have hinter : (interIso q s).hom ≫ subspaceComplPairMap f hf s.W' =
      TopPair.ofInclusionMap _ _ ⟨((Set.mapsTo_univ f Set.univ).inter_inter
        (Set.mapsTo_univ f Set.univ)).restrict, f.hom.continuous.restrict _⟩
        (fun _ hx ↦ (mapsTo_half s f hf _).inter_inter (mapsTo_half s f hf _) hx) ≫
        (interIso q' s).hom := by
    refine TopPair.hom_ext_of_fst _ ?_
    rw [TopPair.Hom.fst_comp, TopPair.Hom.fst_comp, interIso_hom_fst, interIso_hom_fst,
      subspaceComplPairMap_fst]
    exact TopCat.ext fun x ↦ (congrArg Subtype.val (TopPair.ofInclusionMap_fst_apply
      (hst := Set.inter_subset_inter (half_subset_univ q s s.extend)
        (half_subset_univ q s (-s.extend)))
      (hst' := Set.inter_subset_inter (half_subset_univ q' s s.extend)
        (half_subset_univ q' s (-s.extend)))
      ⟨((Set.mapsTo_univ f Set.univ).inter_inter (Set.mapsTo_univ f Set.univ)).restrict,
        f.hom.continuous.restrict _⟩
      (fun _ hx ↦ (mapsTo_half s f hf _).inter_inter (mapsTo_half s f hf _) hx) x)).symm
  have hunion : (unionIso q s).hom ≫ TopPair.ofInclusionMap _ _
      ⟨((Set.mapsTo_univ f Set.univ).union_union (Set.mapsTo_univ f Set.univ)).restrict,
        f.hom.continuous.restrict _⟩
      (fun _ hx ↦ (mapsTo_half s f hf _).union_union (mapsTo_half s f hf _) hx) =
        subspaceComplPairMap f hf W ≫ (unionIso q' s).hom := by
    refine TopPair.hom_ext_of_fst _ ?_
    rw [TopPair.Hom.fst_comp, TopPair.Hom.fst_comp, subspaceComplPairMap_fst]
    exact TopCat.ext fun x ↦ Subtype.ext ((congrArg Subtype.val
      (TopPair.ofInclusionMap_fst_apply _ _ _)).trans ((congrArg f
        (unionIso_hom_fst_apply q s x)).trans (unionIso_hom_fst_apply q' s (f x)).symm))
  simp only [stepδ, ← Category.assoc, ← TopPair.singularCohomologyMap_comp, hinter]
  rw [TopPair.singularCohomologyMap_comp, Category.assoc, Category.assoc, Category.assoc,
    ← TopCat.singularCohomologyPairMayerVietorisδ_naturality_assoc R K M
      (half_subset_univ q s s.extend) (half_subset_univ q s (-s.extend))
      isOpen_univ_union isOpen_univ_union (isOpen_half_left q s) (isOpen_half_right q s)
      (half_subset_univ q' s s.extend) (half_subset_univ q' s (-s.extend))
      isOpen_univ_union isOpen_univ_union (isOpen_half_left q' s) (isOpen_half_right q' s) f
      (Set.mapsTo_univ f Set.univ) (Set.mapsTo_univ f Set.univ) (mapsTo_half s f hf _)
      (mapsTo_half s f hf _) n m h,
    ← TopPair.singularCohomologyMap_comp, hunion, TopPair.singularCohomologyMap_comp]
  simp only [Category.assoc]

end Naturality

variable {q R}

private lemma isIso_singularCohomologyMap_hom {P P' : TopPair.{w}} (e : P ≅ P') (n : ℕ) :
    IsIso (TopPair.singularCohomologyMap (R := R) (k := K) (M := M) e.hom n) :=
  (inferInstance : IsIso ((TopPair.singularCohomologyFunctor R K M n).map e.hom.op))

variable [Module.Projective K R]
  (hq : ∀ (W : Submodule ℝ F) (φ : F →ₗ[ℝ] ℝ) (v : F), v ∈ W → φ v = 1 → ∀ n,
    IsZero ((TopPair.ofSubset (q ⁻¹' {y | y ∈ W ∧ φ y ≤ 0}ᶜ)).singularHomology R n))

omit [FiniteDimensional ℝ F] in
include hq in
/-- Modulo the complement of a closed half-subspace containing a vector on which the functional is
positive, `X` has vanishing cohomology. -/
private lemma isZero_singularCohomology_half (W' : Submodule ℝ F) (ψ : F →ₗ[ℝ] ℝ) (v : F)
    (hv : v ∈ W') (hψv : ψ v = 1) (n : ℕ) :
    IsZero ((TopPair.ofInclusion (Set.subset_univ (half q W' ψ))).singularCohomology R K M n) :=
  ((TopPair.ofSubset (half q W' ψ)).isZero_singularCohomology_of_isZero_singularHomology R M n
    fun j _ ↦ hq W' ψ v hv hψv j).of_iso
      ((TopPair.singularCohomologyFunctor R K M n).mapIso
        (TopPair.ofInclusionIsoOfSubset _ Set.mem_univ fun _ ↦ Iff.rfl).op).symm

include hq in
private lemma isIso_stepδ (n m : ℕ) (h : n + 1 = m) : IsIso (stepδ q s R M n m h) := by
  have hz (j : ℕ) : IsZero
      ((TopPair.ofInclusion (half_subset_univ q s s.extend)).singularCohomology R K M j ⊞
        (TopPair.ofInclusion (half_subset_univ q s (-s.extend))).singularCohomology R K M j) :=
    biprod_isZero_iff _ _ |>.2
      ⟨isZero_singularCohomology_half M hq s.W' s.extend s.v s.v.2 s.extend_apply_v j,
        isZero_singularCohomology_half M hq s.W' (-s.extend) (-s.v) (neg_mem s.v.2)
          (by simp) j⟩
  have := (TopCat.singularCohomologyPairMayerVietoris_exact₃ R K M (half_subset_univ q s s.extend)
    (half_subset_univ q s (-s.extend)) isOpen_univ_union isOpen_univ_union
    (isOpen_half_left q s) (isOpen_half_right q s) n m h).mono_g ((hz n).eq_of_src _ _)
  have := (TopCat.singularCohomologyPairMayerVietoris_exact₁ R K M (half_subset_univ q s s.extend)
    (half_subset_univ q s (-s.extend)) isOpen_univ_union isOpen_univ_union
    (isOpen_half_left q s) (isOpen_half_right q s) n m h).epi_f ((hz m).eq_of_tgt _ _)
  have := isIso_of_mono_of_epi (TopCat.singularCohomologyPairMayerVietorisδ R K M
    (half_subset_univ q s s.extend) (half_subset_univ q s (-s.extend)) isOpen_univ_union
    isOpen_univ_union (isOpen_half_left q s) (isOpen_half_right q s) n m h)
  have := isIso_singularCohomologyMap_hom (R := R) M (interIso q s) n
  have := isIso_singularCohomologyMap_hom (R := R) M (unionIso q s) m
  unfold stepδ
  infer_instance

/-- Multiplying by the Koszul sign `(-1)ⁿ` is an involution. -/
private lemma involutive_neg_one_pow_smul {N : Type*} [AddCommGroup N] (n : ℕ) :
    Function.Involutive fun x : N ↦ ((-1 : ℤ) ^ n) • x := fun x ↦ by
  simp only [smul_smul, ← mul_pow, neg_one_mul, neg_neg, one_pow, one_smul]

end SubspaceComplPair

open SubspaceComplPair

variable [FiniteDimensional ℝ F]

/-- **The cohomology modulo the preimage of the complement of a subspace.** For a subspace `W` of
`F` of codimension `c`, there is a class `g ∈ Hᶜ(F, F ∖ W; K)` such that, whenever `X` is acyclic
with coefficients in `K` modulo the preimage under `q : X → F` of the complement of every closed
half-subspace of `F`, cupping with the pull-back `q^* g` is a bijection
`Hⁿ(X; M) ⟶ Hⁿ⁺ᶜ(X, q⁻¹(F ∖ W); M)` for every module `M` and every `n`.

The class is the image of `1 ∈ H⁰(F; K)` under `c` Mayer–Vietoris connecting morphisms along a
flag of subspaces from `F` down to `W`; it does not depend on `X` or `q`. -/
theorem exists_bijective_singularCup_subspaceComplPair :
    ∀ (c : ℕ) (W : Submodule ℝ F), finrank ℝ W + c = finrank ℝ F →
      ∃ g : (subspaceComplPair (ContinuousMap.id F : C(TopCat.of F, F)) W).singularCohomology
          (ModuleCat.of K K) K (ModuleCat.of K K) c,
        ∀ (X : TopCat.{w}) (q : C(X, F)),
          (∀ (W : Submodule ℝ F) (φ : F →ₗ[ℝ] ℝ) (v : F), v ∈ W → φ v = 1 → ∀ n,
            IsZero ((TopPair.ofSubset (q ⁻¹' {y | y ∈ W ∧ φ y ≤ 0}ᶜ)).singularHomology
              (ModuleCat.of K K) n)) →
          ∀ (M : ModuleCat.{w} K) (n m : ℕ) (h : n + c = m),
            Function.Bijective fun a : X.singularCohomology (ModuleCat.of K K) K M n ↦
              (subspaceComplPair q W).singularCup K (λ_ (𝟙_ (ModuleCat.{w} K))).inv (ρ_ M).hom
                n c m h a (TopPair.singularCohomologyMap
                  (subspaceComplPairMap (TopCat.ofHom q) (fun _ ↦ rfl) W) c g)
  | 0, W, hW => by
    obtain rfl := Submodule.eq_top_of_finrank_eq (by omega : finrank ℝ W = finrank ℝ F)
    -- Modulo the empty set, take the class restricting to `1 ∈ H⁰(F; K)`.
    refine ⟨inv ((subspaceComplPair (ContinuousMap.id F : C(TopCat.of F, F)) ⊤).singularCohomologyπ
      (ModuleCat.of K K) K (ModuleCat.of K K) 0)
        (((TopCat.of F).singularCochainComplex (ModuleCat.of K K) K (ModuleCat.of K K)).homologyπ 0
          ((TopCat.of F).constSingularCocycle K (𝟙 (ModuleCat.of K K)))), ?_⟩
    intro X q _ M n m h
    subst h
    -- Restricted to `X`, cupping with the pull-back of this class is the inverse of the
    -- isomorphism `Hⁿ(X, ∅) ⟶ Hⁿ(X)`.
    have hπ := ConcreteCategory.bijective_of_isIso
      ((subspaceComplPair q ⊤).singularCohomologyπ (ModuleCat.of K K) K M (n + 0))
    refine (fun hl : Function.LeftInverse
      ((subspaceComplPair q ⊤).singularCohomologyπ (ModuleCat.of K K) K M (n + 0)) _ ↦
        Function.bijective_iff_has_inverse.2 ⟨_, hl, hl.rightInverse_of_injective hπ.1⟩) ?_
    intro a
    rw [TopPair.singularCohomologyπ_singularCup, ← ConcreteCategory.comp_apply,
      ← TopPair.singularCohomologyπ_naturality, ConcreteCategory.comp_apply]
    -- The coefficients appear both as `ModuleCat.of K K` and as `𝟙_ (ModuleCat K)`, equal only up
    -- to unfolding, so these rewrites need `erw`.
    erw [IsIso.inv_hom_id_apply]
    erw [TopCat.singularCohomologyMap_homologyπ_constSingularCocycle (R := ModuleCat.of K K)
      (M := ModuleCat.of K K) (TopPair.Hom.fst (subspaceComplPairMap (TopCat.ofHom q)
        (q' := (ContinuousMap.id F : C(TopCat.of F, F))) (fun _ ↦ rfl) ⊤)) K
      (𝟙 (ModuleCat.of K K))]
    exact TopCat.singularCup_constSingularCocycle_right X K (e := 𝟙 (ModuleCat.of K K))
      (η := 𝟙 _) (by simp only [unitors_inv_equal, whiskerLeft_id, Category.comp_id]; rfl)
      (by simp) rfl a
  | c + 1, W, hW => by
    -- Remove one dimension along a chosen extension of `W` by a line.
    obtain ⟨s⟩ := Submodule.nonempty_lineExtension
      (Submodule.lt_top_of_finrank_lt_finrank (by omega : finrank ℝ W < finrank ℝ F)).ne
    obtain ⟨g', hg'⟩ := exists_bijective_singularCup_subspaceComplPair c s.W'
      (by rw [s.finrank_eq]; omega)
    refine ⟨stepδ (X := TopCat.of F) (ContinuousMap.id F) s (ModuleCat.of K K)
      (ModuleCat.of K K) c (c + 1) rfl g', ?_⟩
    intro X q hq M n m h
    subst h
    -- The pull-back of `δ g'` is `δ` of the pull-back of `g'`.
    have hnat := ConcreteCategory.congr_hom
      (singularCohomologyMap_subspaceComplPairMap_comp_stepδ (q := q) (X' := TopCat.of F)
        (q' := ContinuousMap.id F) s (ModuleCat.of K K) (ModuleCat.of K K) (TopCat.ofHom q)
        (fun _ ↦ rfl) c (c + 1) rfl) g'
    simp only [ConcreteCategory.comp_apply] at hnat
    -- Cupping with `δ y` is `(-1)ⁿ δ` of cupping with `y`.
    have hδ := isIso_stepδ s M hq (n + c) (n + (c + 1)) (by omega)
    have key : ∀ a, (subspaceComplPair q W).singularCup K (λ_ (𝟙_ (ModuleCat.{w} K))).inv
        (ρ_ M).hom n (c + 1) (n + (c + 1)) rfl a (stepδ q s (ModuleCat.of K K) (ModuleCat.of K K)
          c (c + 1) rfl (TopPair.singularCohomologyMap
            (subspaceComplPairMap (TopCat.ofHom q) (fun _ ↦ rfl) s.W') c g')) =
        ((-1 : ℤ) ^ n) • stepδ q s (ModuleCat.of K K) M (n + c) (n + (c + 1)) (by omega)
          ((subspaceComplPair q s.W').singularCup K (λ_ (𝟙_ (ModuleCat.{w} K))).inv (ρ_ M).hom
            n c (n + c) rfl a (TopPair.singularCohomologyMap
              (subspaceComplPairMap (TopCat.ofHom q) (fun _ ↦ rfl) s.W') c g')) := fun a ↦ by
      have e := stepδ_singularCup q s (λ_ (𝟙_ (ModuleCat.{w} K))).inv (ρ_ M).hom
        (rfl : n + c = n + c) (rfl : c + 1 = c + 1) (by omega : n + c + 1 = n + (c + 1))
        (rfl : n + (c + 1) = n + (c + 1)) a (TopPair.singularCohomologyMap
          (subspaceComplPairMap (TopCat.ofHom q) (fun _ ↦ rfl) s.W') c g')
      erw [e]
      exact (involutive_neg_one_pow_smul n _).symm
    have hsign : Function.Bijective fun x : (subspaceComplPair q W).singularCohomology
        (ModuleCat.of K K) K M (n + (c + 1)) ↦ ((-1 : ℤ) ^ n) • x :=
      (involutive_neg_one_pow_smul n).bijective
    convert hsign.comp ((ConcreteCategory.bijective_of_isIso
      (stepδ q s (ModuleCat.of K K) M (n + c) (n + (c + 1)) rfl)).comp
        (hg' X q hq M n (n + c) rfl)) using 1
    funext a
    erw [← hnat]
    exact key a

end TauCeti
