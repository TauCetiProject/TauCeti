/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Cohomology.CompactSupport.Extension
public import TauCeti.AlgebraicTopology.Cohomology.MayerVietoris.Pair
public import TauCeti.Topology.Category.TopCat.Opens

/-!
# The Mayer–Vietoris sequence of cohomology with compact supports

Let `X` be a Hausdorff space covered by two open sets `U V : Opens X`, and write `Hⁿ_c(-)` for
singular cohomology with compact supports. Extension by zero along the inclusions of open sets
(`TopCat.compactSupportCohomologyExtend`) gives the maps
`Hⁿ_c(U ∩ V) ⟶ Hⁿ_c(U) ⊞ Hⁿ_c(V) ⟶ Hⁿ_c(X)` of the Mayer–Vietoris sequence of cohomology with
compact supports, the first with components the extension to `U` and minus the extension to `V`,
the second the sum of the extensions to `X`. This file constructs these two maps and proves that
the sequence is exact at `Hⁿ_c(U) ⊞ Hⁿ_c(V)`.

The proof follows Hatcher's proof of Lemma 3.36. For compact sets `K ⊆ U` and `L ⊆ V`, the
Mayer–Vietoris sequence of the pairs `(X, X ∖ K)` and `(X, X ∖ L)` reads
`Hⁿ(X, X ∖ (K ∩ L)) ⟶ Hⁿ(X, X ∖ K) ⊞ Hⁿ(X, X ∖ L) ⟶ Hⁿ(X, X ∖ (K ∪ L))`, exact at the middle term
(`TopCat.exists_singularCohomologyComplRestrict_eq_of_add_eq_zero`), and excision identifies
its first two terms with `Hⁿ(U ∩ V, U ∩ V ∖ (K ∩ L))` and `Hⁿ(U, U ∖ K) ⊞ Hⁿ(V, V ∖ L)`. Passing to
the colimits over the compact sets, every compact subset of `X = U ∪ V` is of the form `K ∪ L`
(`IsCompact.binary_compact_cover`), so the third terms give `Hⁿ_c(X)`. Exactness survives the
filtered colimits; here this is checked on elements, using the description of the elements of
`Hⁿ_c` in `TopCat.exists_compactSupportCohomologyι_eq` and
`TopCat.compactSupportCohomologyι_eq_zero_iff`.

## Main definitions and results

* `TopCat.compactSupportCohomologyMayerVietorisToBiprod`: the map
  `Hⁿ_c(U ∩ V) ⟶ Hⁿ_c(U) ⊞ Hⁿ_c(V)`, with components the extension to `U` and minus the
  extension to `V`.
* `TopCat.compactSupportCohomologyMayerVietorisFromBiprod`: the map
  `Hⁿ_c(U) ⊞ Hⁿ_c(V) ⟶ Hⁿ_c(X)`, the sum of the extensions to `X`.
* `TopCat.compactSupportCohomologyMayerVietorisToBiprod_fromBiprod`: the two maps compose to zero.
* `TopCat.compactSupportCohomologyMayerVietoris_exact₂`: exactness at `Hⁿ_c(U) ⊞ Hⁿ_c(V)` when
  `U ⊔ V = ⊤`.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 3.3, the Mayer–Vietoris sequence `Hⁿ_c(U ∩ V) ⟶ Hⁿ_c(U) ⊕ Hⁿ_c(V) ⟶ Hⁿ_c(X) ⟶ ⋯` in the
  proof of Lemma 3.36.
-/

public section

noncomputable section

open CategoryTheory Limits TopologicalSpace Topology Opens

universe v u

namespace TopCat

variable {C : Type u} [Category.{v} C] [HasCoproducts.{v} C] [Abelian C] {R : C}
  {k : Type v} [Ring k] [Linear k C] {M : C} {X : TopCat.{v}}

/-! ### The first two maps -/

variable (R k M) (U V : Opens X) [T2Space X]

/-- The first map `Hⁿ_c(U ∩ V) ⟶ Hⁿ_c(U) ⊞ Hⁿ_c(V)` of the Mayer–Vietoris sequence of cohomology
with compact supports, with components the extension by zero to `U` and minus the extension by
zero to `V`. -/
def compactSupportCohomologyMayerVietorisToBiprod (n : ℕ) :
    ((Opens.toTopCat X).obj (U ⊓ V)).compactSupportCohomology R k M n ⟶
      ((Opens.toTopCat X).obj U).compactSupportCohomology R k M n ⊞
        ((Opens.toTopCat X).obj V).compactSupportCohomology R k M n :=
  biprod.lift
    (compactSupportCohomologyExtend (isOpenEmbedding_toTopCat_map (homOfLE inf_le_left)) n)
    (-compactSupportCohomologyExtend (isOpenEmbedding_toTopCat_map (homOfLE inf_le_right)) n)

/-- The second map `Hⁿ_c(U) ⊞ Hⁿ_c(V) ⟶ Hⁿ_c(X)` of the Mayer–Vietoris sequence of cohomology
with compact supports, the sum of the extensions by zero to `X`. -/
def compactSupportCohomologyMayerVietorisFromBiprod (n : ℕ) :
    ((Opens.toTopCat X).obj U).compactSupportCohomology R k M n ⊞
        ((Opens.toTopCat X).obj V).compactSupportCohomology R k M n ⟶
      X.compactSupportCohomology R k M n :=
  biprod.desc (compactSupportCohomologyExtend U.isOpenEmbedding n)
    (compactSupportCohomologyExtend V.isOpenEmbedding n)

@[reassoc (attr := simp)]
lemma compactSupportCohomologyMayerVietorisToBiprod_fst (n : ℕ) :
    compactSupportCohomologyMayerVietorisToBiprod R k M U V n ≫ biprod.fst =
      compactSupportCohomologyExtend (isOpenEmbedding_toTopCat_map (homOfLE inf_le_left)) n :=
  biprod.lift_fst _ _

@[reassoc (attr := simp)]
lemma compactSupportCohomologyMayerVietorisToBiprod_snd (n : ℕ) :
    compactSupportCohomologyMayerVietorisToBiprod R k M U V n ≫ biprod.snd =
      -compactSupportCohomologyExtend (isOpenEmbedding_toTopCat_map (homOfLE inf_le_right)) n :=
  biprod.lift_snd _ _

@[reassoc (attr := simp)]
lemma inl_compactSupportCohomologyMayerVietorisFromBiprod (n : ℕ) :
    biprod.inl ≫ compactSupportCohomologyMayerVietorisFromBiprod R k M U V n =
      compactSupportCohomologyExtend U.isOpenEmbedding n :=
  biprod.inl_desc _ _

@[reassoc (attr := simp)]
lemma inr_compactSupportCohomologyMayerVietorisFromBiprod (n : ℕ) :
    biprod.inr ≫ compactSupportCohomologyMayerVietorisFromBiprod R k M U V n =
      compactSupportCohomologyExtend V.isOpenEmbedding n :=
  biprod.inr_desc _ _

/-- The first two maps of the Mayer–Vietoris sequence of cohomology with compact supports compose
to zero: both composites `Hⁿ_c(U ∩ V) ⟶ Hⁿ_c(X)` are the extension by zero. -/
@[reassoc (attr := simp)]
lemma compactSupportCohomologyMayerVietorisToBiprod_fromBiprod (n : ℕ) :
    compactSupportCohomologyMayerVietorisToBiprod R k M U V n ≫
      compactSupportCohomologyMayerVietorisFromBiprod R k M U V n = 0 := by
  rw [compactSupportCohomologyMayerVietorisToBiprod,
    compactSupportCohomologyMayerVietorisFromBiprod,
    biprod.lift_desc, Preadditive.neg_comp,
    ← compactSupportCohomologyExtend_comp _ _ n
      (U.isOpenEmbedding.comp (isOpenEmbedding_toTopCat_map (homOfLE inf_le_left))),
    ← compactSupportCohomologyExtend_comp _ _ n
      (V.isOpenEmbedding.comp (isOpenEmbedding_toTopCat_map (homOfLE inf_le_right))),
    -- both composites are the inclusion of `U ⊓ V` into `X`
    compactSupportCohomologyExtend_congr (toTopCat_map_comp_inclusion' _) _
      (U ⊓ V).isOpenEmbedding,
    compactSupportCohomologyExtend_congr (toTopCat_map_comp_inclusion' _) _
      (U ⊓ V).isOpenEmbedding, add_neg_cancel]

/-! ### Exactness at `Hⁿ_c(U) ⊞ Hⁿ_c(V)` -/

variable {R k M U V}

/-- The heart of exactness of the Mayer–Vietoris sequence of cohomology with compact supports at
`Hⁿ_c(U) ⊞ Hⁿ_c(V)`: if the extensions of `x ∈ Hⁿ_c(U)` and `y ∈ Hⁿ_c(V)` to `X = U ∪ V` cancel,
then `x` and `-y` are the extensions of one class of `Hⁿ_c(U ∩ V)`. Represent `x` and `y` on
compact sets `K ⊆ U` and `L ⊆ V`; the sum of their extensions vanishes on some compact `C ⊇ K ∪ L`
of `X`, which splits as `K₂ ∪ L₂` with `K ⊆ K₂ ⊆ U` and `L ⊆ L₂ ⊆ V` compact; Mayer–Vietoris for
`(X, X ∖ K₂)` and `(X, X ∖ L₂)` gives a class supported in `K₂ ∩ L₂ ⊆ U ∩ V`. -/
private lemma exists_compactSupportCohomologyExtend_eq_neg_of_add_eq_zero (hUV : U ⊔ V = ⊤)
    {n : ℕ} (x : ((Opens.toTopCat X).obj U).compactSupportCohomology R k M n)
    (y : ((Opens.toTopCat X).obj V).compactSupportCohomology R k M n)
    (h : compactSupportCohomologyExtend U.isOpenEmbedding n x +
      compactSupportCohomologyExtend V.isOpenEmbedding n y = 0) :
    ∃ w : ((Opens.toTopCat X).obj (U ⊓ V)).compactSupportCohomology R k M n,
      compactSupportCohomologyExtend (isOpenEmbedding_toTopCat_map (homOfLE inf_le_left)) n w =
          x ∧
        compactSupportCohomologyExtend (isOpenEmbedding_toTopCat_map (homOfLE inf_le_right)) n w =
          -y := by
  have hiU := U.isOpenEmbedding
  have hiV := V.isOpenEmbedding
  have hiW := (U ⊓ V).isOpenEmbedding
  obtain ⟨K, -, x', rfl⟩ := exists_compactSupportCohomologyι_eq x ⊥
  obtain ⟨L, -, y', rfl⟩ := exists_compactSupportCohomologyι_eq y ⊥
  obtain ⟨a, rfl⟩ : ∃ a, singularCohomologyComplCompactsMap hiU.injective K n a = x' := by
    refine ⟨(singularCohomologyComplCompactsMapIso R k M hiU K n).inv x', ?_⟩
    have := (singularCohomologyComplCompactsMapIso R k M hiU K n).inv_hom_id_apply x'
    rwa [singularCohomologyComplCompactsMapIso_hom] at this
  obtain ⟨b, rfl⟩ : ∃ b, singularCohomologyComplCompactsMap hiV.injective L n b = y' := by
    refine ⟨(singularCohomologyComplCompactsMapIso R k M hiV L n).inv y', ?_⟩
    have := (singularCohomologyComplCompactsMapIso R k M hiV L n).inv_hom_id_apply y'
    rwa [singularCohomologyComplCompactsMapIso_hom] at this
  have hxa := ConcreteCategory.congr_hom
    (singularCohomologyMap_comp_compactSupportCohomologyι_comp_extend hiU n K) a
  have hyb := ConcreteCategory.congr_hom
    (singularCohomologyMap_comp_compactSupportCohomologyι_comp_extend hiV n L) b
  simp only [ConcreteCategory.comp_apply] at hxa hyb
  rw [hxa, hyb] at h
  -- the sum of the extensions vanishes on some compact set `C` containing `K ∪ L`
  let KX := K.map _ (Opens.inclusion' U).hom.continuous
  let LX := L.map _ (Opens.inclusion' V).hom.continuous
  rw [← singularCohomologyMap_comp_compactSupportCohomologyι_apply n (le_sup_left : KX ≤ KX ⊔ LX),
    ← singularCohomologyMap_comp_compactSupportCohomologyι_apply n (le_sup_right : LX ≤ KX ⊔ LX),
    ← map_add, compactSupportCohomologyι_eq_zero_iff] at h
  obtain ⟨C', hC', hzero⟩ := h
  rw [map_add,
    singularCohomologyComplRestrict_apply_singularCohomologyComplRestrict
      (le_sup_left : KX ≤ KX ⊔ LX) hC',
    singularCohomologyComplRestrict_apply_singularCohomologyComplRestrict
      (le_sup_right : LX ≤ KX ⊔ LX) hC'] at hzero
  -- split `C` as `K₁ ∪ L₁` with `K₁ ⊆ U` and `L₁ ⊆ V`, and enlarge `K` and `L` accordingly
  obtain ⟨K₁, L₁, hK₁, hL₁, hK₁U, hL₁V, hC'eq⟩ :=
    C'.isCompact.binary_compact_cover U.isOpen V.isOpen
      (by rw [← Opens.coe_sup, hUV, Opens.coe_top]; exact Set.subset_univ _)
  obtain ⟨K₂, hK₂⟩ := exists_compacts_map_inclusion'_eq (K := KX ⊔ ⟨K₁, hK₁⟩)
    (Set.union_subset (by rintro _ ⟨x, -, rfl⟩; exact x.2) hK₁U)
  obtain ⟨L₂, hL₂⟩ := exists_compacts_map_inclusion'_eq (K := LX ⊔ ⟨L₁, hL₁⟩)
    (Set.union_subset (by rintro _ ⟨x, -, rfl⟩; exact x.2) hL₁V)
  let S := (K₂.map _ (Opens.inclusion' U).hom.continuous : Set X)
  let T := (L₂.map _ (Opens.inclusion' V).hom.continuous : Set X)
  have hSeq : S = (KX : Set X) ∪ K₁ := hK₂
  have hTeq : T = (LX : Set X) ∪ L₁ := hL₂
  have hKS : (KX : Set X) ⊆ S := hSeq ▸ Set.subset_union_left
  have hLT : (LX : Set X) ⊆ T := hTeq ▸ Set.subset_union_left
  have hCST : (C' : Set X) ⊆ S ∪ T := by
    rw [hC'eq, hSeq, hTeq]
    exact Set.union_subset_union Set.subset_union_right Set.subset_union_right
  have hKK₂ : K ≤ K₂ := fun x hx ↦ by
    have : Opens.inclusion' U x ∈ S := hKS ⟨x, hx, rfl⟩
    simpa only [S, Compacts.coe_map, hiU.injective.mem_set_image, SetLike.mem_coe] using this
  have hLL₂ : L ≤ L₂ := fun x hx ↦ by
    have : Opens.inclusion' V x ∈ T := hLT ⟨x, hx, rfl⟩
    simpa only [T, Compacts.coe_map, hiV.injective.mem_set_image, SetLike.mem_coe] using this
  -- Mayer–Vietoris for `(X, X ∖ S)` and `(X, X ∖ T)`
  have hsum : singularCohomologyComplRestrict R k M Set.subset_union_left n
        (singularCohomologyComplRestrict R k M hKS n a) +
      singularCohomologyComplRestrict R k M Set.subset_union_right n
        (singularCohomologyComplRestrict R k M hLT n b) = 0 := by
    simpa only [map_add, map_zero,
      singularCohomologyComplRestrict_apply_singularCohomologyComplRestrict] using
      congrArg (singularCohomologyComplRestrict R k M hCST n) hzero
  obtain ⟨z, hzS, hzT⟩ := exists_singularCohomologyComplRestrict_eq_of_add_eq_zero
    (K₂.map _ (map_continuous _)).isCompact.isClosed
    (L₂.map _ (map_continuous _)).isCompact.isClosed _ _ hsum
  -- the class `z` is supported in the compact set `S ∩ T ⊆ U ∩ V`
  obtain ⟨M', hM'⟩ := exists_compacts_map_inclusion'_eq (U := U ⊓ V)
    (K := ⟨S ∩ T, (K₂.map _ (map_continuous _)).isCompact.inter_right
      (L₂.map _ (map_continuous _)).isCompact.isClosed⟩)
    (Set.inter_subset_inter (by rintro _ ⟨x, -, rfl⟩; exact x.2)
      (by rintro _ ⟨x, -, rfl⟩; exact x.2))
  refine ⟨compactSupportCohomologyι n M' (singularCohomologyComplCompactsMap hiW.injective M'
    n (singularCohomologyComplRestrict R k M hM'.ge n z)), ?_, ?_⟩
  · rw [compactSupportCohomologyExtend_compactSupportCohomologyι_singularCohomologyComplCompactsMap
      hiU (isOpenEmbedding_toTopCat_map (homOfLE inf_le_left)) hiW
      (toTopCat_map_comp_inclusion' _)
      (K := K₂) (hM'.trans_subset Set.inter_subset_left),
      singularCohomologyComplRestrict_apply_singularCohomologyComplRestrict, hzS,
      compactSupportCohomologyι_singularCohomologyComplCompactsMap_singularCohomologyComplRestrict
        hiU.injective hKK₂]
  · rw [compactSupportCohomologyExtend_compactSupportCohomologyι_singularCohomologyComplCompactsMap
      hiV (isOpenEmbedding_toTopCat_map (homOfLE inf_le_right)) hiW
      (toTopCat_map_comp_inclusion' _)
      (K := L₂) (hM'.trans_subset Set.inter_subset_right),
      singularCohomologyComplRestrict_apply_singularCohomologyComplRestrict, hzT,
      map_neg, map_neg,
      compactSupportCohomologyι_singularCohomologyComplCompactsMap_singularCohomologyComplRestrict
        hiV.injective hLL₂]

variable (R k M U V) in
/-- **Exactness of the Mayer–Vietoris sequence of cohomology with compact supports at
`Hⁿ_c(U) ⊞ Hⁿ_c(V)`**, for an open cover `X = U ∪ V` of a Hausdorff space. -/
lemma compactSupportCohomologyMayerVietoris_exact₂ (hUV : U ⊔ V = ⊤) (n : ℕ) :
    (ShortComplex.mk _ _
      (compactSupportCohomologyMayerVietorisToBiprod_fromBiprod R k M U V n)).Exact := by
  rw [ShortComplex.moduleCat_exact_iff]
  intro p hp
  let HU := ((toTopCat X).obj U).compactSupportCohomology R k M n
  let HV := ((toTopCat X).obj V).compactSupportCohomology R k M n
  have h₁ := ConcreteCategory.congr_hom
    (inl_compactSupportCohomologyMayerVietorisFromBiprod R k M U V n)
    ((biprod.fst : HU ⊞ HV ⟶ HU) p)
  have h₂ := ConcreteCategory.congr_hom
    (inr_compactSupportCohomologyMayerVietorisFromBiprod R k M U V n)
    ((biprod.snd : HU ⊞ HV ⟶ HV) p)
  rw [ConcreteCategory.comp_apply] at h₁ h₂
  rw [← ModuleCat.biprod_inl_fst_add_inr_snd_apply p, map_add, h₁, h₂] at hp
  obtain ⟨w, hwU, hwV⟩ := exists_compactSupportCohomologyExtend_eq_neg_of_add_eq_zero hUV _ _ hp
  refine ⟨w, ?_⟩
  have h₃ := ConcreteCategory.congr_hom
    (compactSupportCohomologyMayerVietorisToBiprod_fst R k M U V n) w
  have h₄ := ConcreteCategory.congr_hom
    (compactSupportCohomologyMayerVietorisToBiprod_snd R k M U V n) w
  rw [ConcreteCategory.comp_apply] at h₃ h₄
  rw [← ModuleCat.biprod_inl_fst_add_inr_snd_apply
      (compactSupportCohomologyMayerVietorisToBiprod R k M U V n w),
    h₃, h₄, hwU]
  simp only [ModuleCat.hom_neg, LinearMap.neg_apply, hwV, neg_neg]
  exact ModuleCat.biprod_inl_fst_add_inr_snd_apply p

end TopCat
