/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.LocalHomology.System
public import TauCeti.AlgebraicTopology.Singular.MayerVietoris.Relative

/-!
# Mayer–Vietoris for local homology

For closed subsets `S` and `T` of a space `M`, the relative Mayer–Vietoris sequence of the open
sets `M ∖ S` and `M ∖ T` (`TopCat.relativeMayerVietoris_exact₁`) contains the segment
`Hₖ₊₁(M, M ∖ (S ∩ T)) ⟶ Hₖ(M, M ∖ (S ∪ T)) ⟶ Hₖ(M, M ∖ S) ⊞ Hₖ(M, M ∖ T)` of local homology
groups (`TauCeti.localHomology`).

## Main results

* `TauCeti.isZero_localHomology_union`: for closed `S` and `T`, if `Hₖ(M, M ∖ S)`, `Hₖ(M, M ∖ T)`
  and `Hₖ₊₁(M, M ∖ (S ∩ T))` vanish, then so does `Hₖ(M, M ∖ (S ∪ T))`.
* `TauCeti.isZero_localHomology_biUnion`: local homology vanishes above a degree along finite
  unions of members of a family of closed sets that is closed under intersections and along which
  it vanishes above that degree.
* `TauCeti.localHomology_hom_ext_of_union`: for closed `S` and `T` with
  `Hₖ₊₁(M, M ∖ (S ∩ T)) = 0`, maps into `Hₖ(M, M ∖ (S ∪ T))` are determined by their
  restrictions to `S` and to `T`.
* `TauCeti.exists_localHomologyRestriction_union_eq`: with coefficients in a module, classes along
  closed sets `S` and `T` with the same restriction to `S ∩ T` are the restrictions of a single
  class along `S ∪ T`.
* `TauCeti.eq_zero_of_disjoint_isOpen_of_isZero_localHomology`: if `M ∖ D = U ∪ V` is a union of
  disjoint open subsets `U, V ⊆ M` and `Hₖ₊₁(M, M ∖ D; N) = 0`, any class in `Hₖ(M; N)` coming
  from both `Hₖ(U; N)` and `Hₖ(V; N)` is zero.
-/

public section

noncomputable section

open CategoryTheory Limits Set

universe w v u

namespace TauCeti

variable {A : Type u} [Category.{v} A] [HasCoproducts.{w} A] [Abelian A] {R : A}
  {M : Type w} [TopologicalSpace M]

/-- **Vanishing of local homology along a union.** For closed sets `S` and `T`, if `Hₖ(M, M ∖ S)`,
`Hₖ(M, M ∖ T)` and `Hₖ₊₁(M, M ∖ (S ∩ T))` vanish, then so does `Hₖ(M, M ∖ (S ∪ T))`, by the
relative Mayer–Vietoris sequence of the open sets `M ∖ S` and `M ∖ T`. -/
theorem isZero_localHomology_union {S T : Set M} (hS : IsClosed S) (hT : IsClosed T) {k : ℕ}
    (hSk : IsZero (localHomology R S k)) (hTk : IsZero (localHomology R T k))
    (h : IsZero (localHomology R (S ∩ T) (k + 1))) :
    IsZero (localHomology R (S ∪ T) k) := by
  dsimp only [localHomology] at hSk hTk h ⊢
  rw [compl_union]
  rw [compl_inter] at h
  have := TopCat.mono_relativeMayerVietorisToBiprod R hS.isOpen_compl hT.isOpen_compl h
  exact IsZero.of_mono (TopCat.relativeMayerVietorisToBiprod R _ _ k)
    ((biprod_isZero_iff _ _).2 ⟨hSk, hTk⟩)

/-- **Vanishing of local homology along finite unions.** Let `𝒢` be a family of closed sets which
is closed under binary intersections and along each of which local homology vanishes above
degree `n`. Then local homology along every finite union of members of `𝒢` vanishes above
degree `n`. This is the induction of Hatcher's Lemma 3.27 along the relative Mayer–Vietoris
sequence (`TauCeti.isZero_localHomology_union`). -/
theorem isZero_localHomology_biUnion {n : ℕ} {𝒢 : Set (Set M)} (hc : ∀ G ∈ 𝒢, IsClosed G)
    (hi : ∀ G ∈ 𝒢, ∀ G' ∈ 𝒢, G ∩ G' ∈ 𝒢)
    (hz : ∀ G ∈ 𝒢, ∀ k, n < k → IsZero (localHomology R G k)) {ι : Type*} (s : Finset ι)
    {G : ι → Set M} (hG : ∀ i ∈ s, G i ∈ 𝒢) {k : ℕ} (hk : n < k) :
    IsZero (localHomology R (⋃ i ∈ s, G i) k) := by
  classical
  induction s using Finset.induction_on generalizing G k with
  | empty => simpa using isZero_localHomology_empty R k
  | insert b s _ ih =>
    have hb := hG b (Finset.mem_insert_self b s)
    have hs (i) (hi : i ∈ s) : G i ∈ 𝒢 := hG i (Finset.mem_insert_of_mem hi)
    rw [Finset.set_biUnion_insert]
    refine isZero_localHomology_union (hc _ hb) (isClosed_biUnion_finset fun i hi ↦ hc _ (hs i hi))
      (hz _ hb k hk) (ih hs hk) ?_
    -- The intersection of `G b` with the union is the union of the intersections `G b ∩ G i`.
    rw [inter_iUnion₂]
    exact ih (G := fun i ↦ G b ∩ G i) (fun i hi' ↦ hi _ hb _ (hs i hi')) (by lia)

/-- **Maps into local homology of a union are detected on the pieces.** Let `S` and `T` be closed
and let `Hₖ₊₁(M, M ∖ (S ∩ T))` vanish. Two maps into `Hₖ(M, M ∖ (S ∪ T))` that agree after
restriction to `S` and to `T` are equal. -/
theorem localHomology_hom_ext_of_union {S T : Set M} (hS : IsClosed S) (hT : IsClosed T) {k : ℕ}
    (h : IsZero (localHomology R (S ∩ T) (k + 1))) {Z : A}
    {f g : Z ⟶ localHomology R (S ∪ T) k}
    (hfS : f ≫ localHomologyRestriction R subset_union_left k =
      g ≫ localHomologyRestriction R subset_union_left k)
    (hfT : f ≫ localHomologyRestriction R subset_union_right k =
      g ≫ localHomologyRestriction R subset_union_right k) :
    f = g := by
  dsimp only [localHomology] at h
  rw [compl_inter] at h
  have := TopCat.mono_relativeMayerVietorisToBiprod R hS.isOpen_compl hT.isOpen_compl h
  rw [localHomologyRestriction_def] at hfS hfT
  -- The sequence is stated for `(M ∖ S) ∩ (M ∖ T)`, which is `M ∖ (S ∪ T)` only propositionally,
  -- so generalize the subspace before comparing with the first map of the sequence.
  suffices key : ∀ (W : Set (TopCat.of M)) (_ : W = Sᶜ ∩ Tᶜ) (hWS : W ⊆ Sᶜ) (hWT : W ⊆ Tᶜ)
      (f g : Z ⟶ (TopPair.ofSubset W).singularHomology R k),
      f ≫ TopPair.singularHomologyMap (TopPair.ofSubsetMap (𝟙 _) hWS) R k =
          g ≫ TopPair.singularHomologyMap (TopPair.ofSubsetMap (𝟙 _) hWS) R k →
        f ≫ TopPair.singularHomologyMap (TopPair.ofSubsetMap (𝟙 _) hWT) R k =
          g ≫ TopPair.singularHomologyMap (TopPair.ofSubsetMap (𝟙 _) hWT) R k → f = g from
    key _ (compl_union S T) _ _ f g hfS hfT
  rintro W rfl hWS hWT f g hS hT
  rw [← cancel_mono (TopCat.relativeMayerVietorisToBiprod R (X := TopCat.of M) Sᶜ Tᶜ k)]
  ext
  · simpa using hS
  · simpa using hT

section Module

variable {Λ : Type w} [Ring Λ] (N : ModuleCat.{w} Λ)

/-- **Local homology classes on two closed sets glue.** Let `S` and `T` be closed. Classes of
`Hₖ(M, M ∖ S)` and `Hₖ(M, M ∖ T)` with the same restriction to `S ∩ T` are the restrictions of a
single class of `Hₖ(M, M ∖ (S ∪ T))`. This is exactness of the relative Mayer–Vietoris sequence
at `Hₖ(M, M ∖ S) ⊞ Hₖ(M, M ∖ T)`. -/
theorem exists_localHomologyRestriction_union_eq {S T : Set M} (hS : IsClosed S)
    (hT : IsClosed T) {k : ℕ} (α : (localHomology N S k : ModuleCat.{w} Λ))
    (β : (localHomology N T k : ModuleCat.{w} Λ))
    (h : localHomologyRestriction N inter_subset_left k α =
      localHomologyRestriction N inter_subset_right k β) :
    ∃ γ : (localHomology N (S ∪ T) k : ModuleCat.{w} Λ),
      localHomologyRestriction N subset_union_left k γ = α ∧
        localHomologyRestriction N subset_union_right k γ = β := by
  have hex := TopCat.relativeMayerVietoris_exact₂ N (X := TopCat.of M) hS.isOpen_compl
    hT.isOpen_compl k
  rw [ShortComplex.moduleCat_exact_iff] at hex
  simp only [localHomologyRestriction_def] at h ⊢
  -- As in `TauCeti.localHomology_hom_ext_of_union`, the sequence is stated for `Sᶜ ∩ Tᶜ` and
  -- `Sᶜ ∪ Tᶜ`, which are `(S ∪ T)ᶜ` and `(S ∩ T)ᶜ` only propositionally, so generalize them.
  suffices key : ∀ (W₁ W₂ : Set (TopCat.of M)) (_ : W₁ = Sᶜ ∩ Tᶜ) (_ : W₂ = Sᶜ ∪ Tᶜ)
      (hW₁S : W₁ ⊆ Sᶜ) (hW₁T : W₁ ⊆ Tᶜ) (hSW₂ : Sᶜ ⊆ W₂) (hTW₂ : Tᶜ ⊆ W₂),
      TopPair.singularHomologyMap (TopPair.ofSubsetMap (𝟙 (TopCat.of M)) hSW₂) N k α =
          TopPair.singularHomologyMap (TopPair.ofSubsetMap (𝟙 (TopCat.of M)) hTW₂) N k β →
        ∃ γ : ((TopPair.ofSubset W₁).singularHomology N k : ModuleCat.{w} Λ),
          TopPair.singularHomologyMap (TopPair.ofSubsetMap (𝟙 (TopCat.of M)) hW₁S) N k γ = α ∧
            TopPair.singularHomologyMap (TopPair.ofSubsetMap (𝟙 (TopCat.of M)) hW₁T) N k γ = β from
    key _ _ (compl_union S T) (compl_inter S T) _ _ _ _ h
  rintro W₁ W₂ rfl rfl hW₁S hW₁T hSW₂ hTW₂ h
  let HS := (TopPair.ofSubset (Sᶜ : Set (TopCat.of M))).singularHomology N k
  let HT := (TopPair.ofSubset (Tᶜ : Set (TopCat.of M))).singularHomology N k
  obtain ⟨γ, hγ⟩ := hex ((biprod.inl : HS ⟶ HS ⊞ HT) α - (biprod.inr : HT ⟶ HS ⊞ HT) β) (by
    simp [HS, HT, ← ConcreteCategory.comp_apply, TopCat.inl_relativeMayerVietorisFromBiprod,
      TopCat.inr_relativeMayerVietorisFromBiprod, h])
  refine ⟨γ, ?_, ?_⟩
  · simpa [HS, HT, ← ConcreteCategory.comp_apply] using congrArg (biprod.fst : HS ⊞ HT ⟶ HS) hγ
  · simpa [HS, HT, ← ConcreteCategory.comp_apply] using congrArg (biprod.snd : HS ⊞ HT ⟶ HT) hγ

end Module

section DisjointOpen

variable {Λ : Type*} [Ring Λ] (N : ModuleCat.{w} Λ)

/-- If a homology class `α ∈ Hₖ(M; N)` comes from a subset `U ⊆ W`, it also comes from `W` via a
class pushed forward from `Subtype.val ⁻¹' U : Set W`. -/
private lemma exists_homologyMap_preimage_eq_of_subset {U W : Set M} (hUW : U ⊆ W) {k : ℕ}
    {α : ((TopCat.toSSet.obj (TopCat.of M)).homology N k : ModuleCat.{w} Λ)}
    (hU : ∃ γU, SSet.homologyMap
      (TopCat.toSSet.map (TopCat.ofHom (ContinuousMap.subtypeVal U))) N k γU = α) :
    ∃ δU : ((TopCat.toSSet.obj (TopCat.of ↥(Subtype.val ⁻¹' U : Set (TopCat.of W)))).homology
        N k : ModuleCat.{w} Λ),
      SSet.homologyMap (TopCat.toSSet.map (TopCat.ofHom (ContinuousMap.subtypeVal W))) N k
        (SSet.homologyMap (TopCat.toSSet.map
          (TopCat.ofHom (ContinuousMap.subtypeVal
            (Subtype.val ⁻¹' U : Set (TopCat.of W))))) N k δU) = α := by
  obtain ⟨γU, hγU⟩ := hU
  let U' : Set (TopCat.of W) := Subtype.val ⁻¹' U
  let jU : TopCat.of ↥U ⟶ TopCat.of ↥U' :=
    TopCat.ofHom ⟨fun x ↦ ⟨⟨x.val, hUW x.property⟩, x.property⟩, by fun_prop⟩
  have hfac : jU ≫ TopCat.ofHom (ContinuousMap.subtypeVal U') ≫
      TopCat.ofHom (ContinuousMap.subtypeVal W) = TopCat.ofHom (ContinuousMap.subtypeVal U) := by
    ext; rfl
  refine ⟨SSet.homologyMap (TopCat.toSSet.map jU) N k γU, ?_⟩
  rw [← hγU, ← hfac]
  simp [SSet.homologyMap_comp]

/-- On a space `W` covered by two disjoint open subsets `U'` and `V'`, a class in `Hₖ(W; N)`
pushed forward from `U'` and also from `V'` is zero: the Mayer–Vietoris map from the direct sum is
injective because `U' ∩ V'` is empty. -/
private lemma eq_zero_of_disjoint_isOpen_cover {W : TopCat.{w}} {U' V' : Set W}
    (hU'o : IsOpen U') (hV'o : IsOpen V') (hUV'd : Disjoint U' V') (hUV' : U' ∪ V' = univ)
    {k : ℕ}
    {δU : ((TopCat.toSSet.obj (TopCat.of ↥U')).homology N k : ModuleCat.{w} Λ)}
    {δV : ((TopCat.toSSet.obj (TopCat.of ↥V')).homology N k : ModuleCat.{w} Λ)}
    (hEq : SSet.homologyMap (TopCat.toSSet.map (TopCat.ofHom (ContinuousMap.subtypeVal U'))) N k
        δU =
      SSet.homologyMap (TopCat.toSSet.map (TopCat.ofHom (ContinuousMap.subtypeVal V'))) N k δV) :
    SSet.homologyMap (TopCat.toSSet.map (TopCat.ofHom (ContinuousMap.subtypeVal U'))) N k δU =
      0 := by
  have : IsEmpty (TopCat.of ↥(U' ∩ V')) := ⟨fun ⟨_, hxU, hxV⟩ ↦ hUV'd.le_bot ⟨hxU, hxV⟩⟩
  have hZeroUV : IsZero ((TopCat.toSSet.obj (TopCat.of ↥(U' ∩ V'))).homology N k) := by
    rw [← singularHomologyFunctor_obj_obj_eq_toSSet_homology]
    exact isZero_singularHomology_of_isEmpty N (TopCat.of ↥(U' ∩ V')) k
  have hMV := (TopCat.mayerVietoris_exact₂ N hU'o hV'o hUV' k).mono_g (hZeroUV.eq_of_src _ _)
  let HU := (TopCat.toSSet.obj (TopCat.of ↥U')).homology N k
  let HV := (TopCat.toSSet.obj (TopCat.of ↥V')).homology N k
  have hMVzero : SSet.mayerVietorisFromBiprod N
      (TopCat.toSSet.map (TopCat.ofHom (ContinuousMap.subtypeVal U')))
      (TopCat.toSSet.map (TopCat.ofHom (ContinuousMap.subtypeVal V'))) k
      ((biprod.inl : HU ⟶ HU ⊞ HV) δU - (biprod.inr : HV ⟶ HU ⊞ HV) δV) = 0 := by
    rw [map_sub, ← ConcreteCategory.comp_apply biprod.inl, SSet.inl_mayerVietorisFromBiprod,
      ← ConcreteCategory.comp_apply biprod.inr, SSet.inr_mayerVietorisFromBiprod]
    exact sub_eq_zero.2 hEq
  have hbiprod := (ModuleCat.mono_iff_injective _).1 hMV (hMVzero.trans (map_zero _).symm)
  have hδU : δU = 0 := by
    have h := congrArg (biprod.fst : HU ⊞ HV ⟶ HU) hbiprod
    rw [map_sub, ← ConcreteCategory.comp_apply biprod.inl, biprod.inl_fst,
      ← ConcreteCategory.comp_apply biprod.inr, biprod.inr_fst] at h
    simpa using h
  rw [hδU, map_zero]

/-- If `M ∖ D = U ∪ V` is decomposed into disjoint open subsets `U` and `V` of `M` and
`Hₖ₊₁(M, M ∖ D; N) = 0`, then any class `α ∈ Hₖ(M; N)` lying in the images of both
`Hₖ(U; N) ⟶ Hₖ(M; N)` and `Hₖ(V; N) ⟶ Hₖ(M; N)` is zero. -/
theorem eq_zero_of_disjoint_isOpen_of_isZero_localHomology {D U V : Set M}
    (hUo : IsOpen U) (hVo : IsOpen V) (hUV : Disjoint U V) (hUVD : U ∪ V = Dᶜ) {k : ℕ}
    (hhigh : IsZero (localHomology N D (k + 1)))
    {α : ((TopCat.toSSet.obj (TopCat.of M)).homology N k : ModuleCat.{w} Λ)}
    (hU : ∃ γU, SSet.homologyMap
      (TopCat.toSSet.map (TopCat.ofHom (ContinuousMap.subtypeVal U))) N k γU = α)
    (hV : ∃ γV, SSet.homologyMap
      (TopCat.toSSet.map (TopCat.ofHom (ContinuousMap.subtypeVal V))) N k γV = α) :
    α = 0 := by
  -- Lift the pushforwards from `U` and `V` to the disjoint open cover of `W = M \ D`.
  obtain ⟨δU, hU'α⟩ := exists_homologyMap_preimage_eq_of_subset N
    (subset_union_left.trans hUVD.subset) hU
  obtain ⟨δV, hV'α⟩ := exists_homologyMap_preimage_eq_of_subset N
    (subset_union_right.trans hUVD.subset) hV
  -- Vanishing of `Hₖ₊₁(M, W; N)` makes `Hₖ(W; N) ⟶ Hₖ(M; N)` injective, so the lifts agree on `W`.
  have hMonoW : Mono (SSet.homologyMap
      (TopCat.toSSet.map (TopCat.ofHom (ContinuousMap.subtypeVal (Dᶜ : Set M)))) N k) :=
    (TopPair.ofSubset (Dᶜ : Set (TopCat.of M))).mono_homologyMap_map_of_isZero N hhigh
  have hEqW := (ModuleCat.mono_iff_injective _).1 hMonoW (hU'α.trans hV'α.symm)
  -- Mayer–Vietoris on the disjoint open cover of `W` then kills the class on `W`, hence `α`.
  have hZero := eq_zero_of_disjoint_isOpen_cover N (W := TopCat.of ↥(Dᶜ : Set M))
    (hUo.preimage continuous_subtypeVal) (hVo.preimage continuous_subtypeVal)
    (hUV.preimage _) (eq_univ_of_forall fun x ↦ hUVD.symm.subset x.property) hEqW
  rw [← hU'α, hZero, map_zero]

end DisjointOpen

end TauCeti
