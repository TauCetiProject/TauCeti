/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Cohomology.CompactSupport.Extension
public import TauCeti.AlgebraicTopology.Cohomology.MayerVietoris.Compl
public import TauCeti.AlgebraicTopology.Cohomology.Point
public import TauCeti.Topology.Category.TopCat.Opens

/-!
# The Mayer–Vietoris sequence of cohomology with compact supports

Let `X` be a Hausdorff space covered by two open sets `U V : Opens X`, and write `Hⁿ_c(-)` for
singular cohomology with compact supports. Extension by zero along the inclusions of open sets
(`TopCat.compactSupportCohomologyExtend`) gives the maps
`Hⁿ_c(U ∩ V) ⟶ Hⁿ_c(U) ⊞ Hⁿ_c(V) ⟶ Hⁿ_c(X)` of the Mayer–Vietoris sequence of cohomology with
compact supports, the first with components the extension to `U` and minus the extension to `V`,
the second the sum of the extensions to `X`. This file constructs these two maps and the connecting
map `Hⁿ_c(X) ⟶ Hᵐ_c(U ∩ V)`, `n + 1 = m`, and proves that the resulting long sequence
`⋯ ⟶ Hⁿ_c(U ∩ V) ⟶ Hⁿ_c(U) ⊞ Hⁿ_c(V) ⟶ Hⁿ_c(X) ⟶ Hᵐ_c(U ∩ V) ⟶ Hᵐ_c(U) ⊞ Hᵐ_c(V) ⟶ ⋯`
is exact. This is the long exact sequence used in Hatcher's proof of Lemma 3.36, the induction
step of Poincaré duality for open subsets of a manifold.

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

For the connecting map, the Mayer–Vietoris sequence of the pairs `(X, X ∖ K)` and `(X, X ∖ L)` has
the connecting morphism `Hⁿ(X, X ∖ (K ∪ L)) ⟶ Hᵐ(X, X ∖ (K ∩ L))`
(`TopCat.singularCohomologyComplMayerVietorisδ`). Composing it with excision
`Hᵐ(X, X ∖ (K ∩ L)) ≅ Hᵐ(U ∩ V, U ∩ V ∖ (K ∩ L))` gives a map `Hⁿ(X, X ∖ (K ∪ L)) ⟶ Hᵐ_c(U ∩ V)`.
These maps are compatible with enlarging `K` and `L`, by naturality, and every compact subset of
`X` lies in some `K ∪ L`, so they define a map out of the colimit `Hⁿ_c(X)`. The signs follow
`TopCat.compactSupportCohomologyMayerVietorisToBiprod`, whose components are the extension to `U`
and minus the extension to `V`; the connecting map carries no extra sign, since the signs of the
first two maps do not affect the kernels and images at `Hⁿ_c(X)` and `Hᵐ_c(U ∩ V)`.

## Main definitions and results

* `TopCat.compactSupportCohomologyMayerVietorisToBiprod`: the map
  `Hⁿ_c(U ∩ V) ⟶ Hⁿ_c(U) ⊞ Hⁿ_c(V)`, with components the extension to `U` and minus the
  extension to `V`.
* `TopCat.compactSupportCohomologyMayerVietorisFromBiprod`: the map
  `Hⁿ_c(U) ⊞ Hⁿ_c(V) ⟶ Hⁿ_c(X)`, the sum of the extensions to `X`.
* `TopCat.compactSupportCohomologyMayerVietorisToBiprod_fromBiprod`: the two maps compose to zero.
* `TopCat.compactSupportCohomologyMayerVietoris_exact₂`: exactness at `Hⁿ_c(U) ⊞ Hⁿ_c(V)` when
  `U ⊔ V = ⊤`.
* `TopCat.compactSupportCohomologyMayerVietorisδ`: the connecting map `Hⁿ_c(X) ⟶ Hᵐ_c(U ∩ V)`,
  characterized on `Hⁿ(X, X ∖ C)` by
  `TopCat.compactSupportCohomologyι_compactSupportCohomologyMayerVietorisδ`.
* `TopCat.compactSupportCohomologyMayerVietorisFromBiprod_δ` and
  `TopCat.compactSupportCohomologyMayerVietorisδ_toBiprod`: the composites with the neighbouring
  maps vanish.
* `TopCat.compactSupportCohomologyMayerVietoris_exact₃` and
  `TopCat.compactSupportCohomologyMayerVietoris_exact₁`: exactness at `Hⁿ_c(X)` and at
  `Hᵐ_c(U ∩ V)`.
* `TopCat.isIso_compactSupportCohomologyMayerVietorisFromBiprod_of_isZero`: the middle map is an
  isomorphism when `Hⁿ_c(U ∩ V)` and `Hⁿ⁺¹_c(U ∩ V)` vanish.
* `TopCat.isZero_compactSupportCohomology_of_sup_eq_top`: `Hⁿ_c(X)` vanishes when `Hⁿ_c(U)`,
  `Hⁿ_c(V)` and `Hⁿ⁺¹_c(U ∩ V)` do.
* `TopCat.isIso_biprodDesc_compactSupportCohomologyExtend_of_disjoint`: for a cover by two disjoint
  open sets, `Hⁿ_c(U) ⊞ Hⁿ_c(V) ≅ Hⁿ_c(X)`.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 3.3, the Mayer–Vietoris sequence `⋯ ⟶ Hⁿ_c(U ∩ V) ⟶ Hⁿ_c(U) ⊕ Hⁿ_c(V) ⟶ Hⁿ_c(X) ⟶
  Hⁿ⁺¹_c(U ∩ V) ⟶ ⋯` in the proof of Lemma 3.36.
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

@[reassoc (attr := simp), elementwise (attr := simp)]
lemma compactSupportCohomologyMayerVietorisToBiprod_fst (n : ℕ) :
    compactSupportCohomologyMayerVietorisToBiprod R k M U V n ≫ biprod.fst =
      compactSupportCohomologyExtend (isOpenEmbedding_toTopCat_map (homOfLE inf_le_left)) n :=
  biprod.lift_fst _ _

@[reassoc (attr := simp), elementwise (attr := simp)]
lemma compactSupportCohomologyMayerVietorisToBiprod_snd (n : ℕ) :
    compactSupportCohomologyMayerVietorisToBiprod R k M U V n ≫ biprod.snd =
      -compactSupportCohomologyExtend (isOpenEmbedding_toTopCat_map (homOfLE inf_le_right)) n :=
  biprod.lift_snd _ _

@[reassoc (attr := simp), elementwise (attr := simp)]
lemma inl_compactSupportCohomologyMayerVietorisFromBiprod (n : ℕ) :
    biprod.inl ≫ compactSupportCohomologyMayerVietorisFromBiprod R k M U V n =
      compactSupportCohomologyExtend U.isOpenEmbedding n :=
  biprod.inl_desc _ _

@[reassoc (attr := simp), elementwise (attr := simp)]
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
    (Set.union_subset (by rintro _ ⟨x, -, rfl⟩; exact x.property) hK₁U)
  obtain ⟨L₂, hL₂⟩ := exists_compacts_map_inclusion'_eq (K := LX ⊔ ⟨L₁, hL₁⟩)
    (Set.union_subset (by rintro _ ⟨x, -, rfl⟩; exact x.property) hL₁V)
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
    (Set.inter_subset_inter (by rintro _ ⟨x, -, rfl⟩; exact x.property)
      (by rintro _ ⟨x, -, rfl⟩; exact x.property))
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

/-! ### The connecting map -/

section Connecting

variable (U V)

omit [T2Space X] in
private lemma inter_subset_range_inclusion'_inf {K L : Set X} (hKU : K ⊆ U) (hLV : L ⊆ V) :
    K ∩ L ⊆ Set.range (Opens.inclusion' (U ⊓ V)) := by
  rw [set_range_inclusion', Opens.coe_inf]
  exact Set.inter_subset_inter hKU hLV

/-- Every compact subset of `X = U ∪ V` lies in `K ∪ L` for compact sets `K ⊆ U` and `L ⊆ V`. -/
private lemma exists_isCompact_subset_union (hUV : U ⊔ V = ⊤) {C : Set X} (hC : IsCompact C) :
    ∃ KL : Set X × Set X, IsCompact KL.1 ∧ IsCompact KL.2 ∧ KL.1 ⊆ U ∧ KL.2 ⊆ V ∧
      C ⊆ KL.1 ∪ KL.2 := by
  obtain ⟨K, L, hK, hL, hKU, hLV, rfl⟩ := hC.binary_compact_cover U.isOpen V.isOpen
    (by rw [← Opens.coe_sup, hUV, Opens.coe_top]; exact Set.subset_univ _)
  exact ⟨(K, L), hK, hL, hKU, hLV, subset_rfl⟩

variable (R k M) in
/-- The connecting map on `Hⁿ(X, X ∖ (K ∪ L))` for compact sets `K ⊆ U` and `L ⊆ V`: the
connecting morphism into `Hᵐ(X, X ∖ (K ∩ L))`, followed by excision to `Hᵐ_c(U ∩ V)`. -/
private def mayerVietorisδAux {K L : Set X} (hK : IsCompact K) (hL : IsCompact L) (hKU : K ⊆ U)
    (hLV : L ⊆ V) (n m : ℕ) (h : n + 1 = m) :
    (TopPair.ofSubset (K ∪ L)ᶜ).singularCohomology R k M n ⟶
      ((Opens.toTopCat X).obj (U ⊓ V)).compactSupportCohomology R k M m :=
  singularCohomologyComplMayerVietorisδ R k M hK.isClosed hL.isClosed n m h ≫
    compactSupportCohomologyRestrict R k M (U ⊓ V).isOpenEmbedding (hK.inter_right hL.isClosed)
      (inter_subset_range_inclusion'_inf U V hKU hLV) m

private lemma mayerVietorisδAux_apply {K L : Set X} (hK : IsCompact K) (hL : IsCompact L)
    (hKU : K ⊆ U) (hLV : L ⊆ V) {n m : ℕ} (h : n + 1 = m)
    (a : (TopPair.ofSubset (K ∪ L)ᶜ).singularCohomology R k M n) :
    mayerVietorisδAux R k M U V hK hL hKU hLV n m h a =
      compactSupportCohomologyRestrict R k M (U ⊓ V).isOpenEmbedding (hK.inter_right hL.isClosed)
        (inter_subset_range_inclusion'_inf U V hKU hLV) m
        (singularCohomologyComplMayerVietorisδ R k M hK.isClosed hL.isClosed n m h a) :=
  ConcreteCategory.comp_apply _ _ a

/-- The connecting maps on `Hⁿ(X, X ∖ (K ∪ L))` are compatible with enlarging `K` and `L`. -/
private lemma mayerVietorisδAux_singularCohomologyComplRestrict {K L K' L' : Set X}
    (hK : IsCompact K) (hL : IsCompact L) (hKU : K ⊆ U) (hLV : L ⊆ V) (hK' : IsCompact K')
    (hL' : IsCompact L') (hK'U : K' ⊆ U) (hL'V : L' ⊆ V) (hKK' : K ⊆ K') (hLL' : L ⊆ L')
    {n m : ℕ} (h : n + 1 = m) (a : (TopPair.ofSubset (K ∪ L)ᶜ).singularCohomology R k M n) :
    mayerVietorisδAux R k M U V hK' hL' hK'U hL'V n m h
        (singularCohomologyComplRestrict R k M (Set.union_subset_union hKK' hLL') n a) =
      mayerVietorisδAux R k M U V hK hL hKU hLV n m h a := by
  rw [mayerVietorisδAux_apply, mayerVietorisδAux_apply,
    ← singularCohomologyComplMayerVietorisδ_naturality_of_subset_apply R k M hK.isClosed
      hL.isClosed hK'.isClosed hL'.isClosed hKK' hLL' n m h,
    singularCohomologyComplRestrict_compactSupportCohomologyRestrict_apply]

variable (R k M) in
/-- The connecting map on `Hⁿ(X, X ∖ C)`, through a chosen cover of `C` by compact sets `K ⊆ U`
and `L ⊆ V`. -/
private def mayerVietorisδOn (hUV : U ⊔ V = ⊤) (C : Compacts X) (n m : ℕ) (h : n + 1 = m) :
    (TopPair.ofSubset (C : Set X)ᶜ).singularCohomology R k M n ⟶
      ((Opens.toTopCat X).obj (U ⊓ V)).compactSupportCohomology R k M m :=
  have hKL := (exists_isCompact_subset_union U V hUV C.isCompact).choose_spec
  singularCohomologyComplRestrict R k M hKL.2.2.2.2 n ≫
    mayerVietorisδAux R k M U V hKL.1 hKL.2.1 hKL.2.2.1 hKL.2.2.2.1 n m h

/-- The connecting map on `Hⁿ(X, X ∖ C)` may be computed through any cover of `C` by compact sets
`K ⊆ U` and `L ⊆ V`. -/
private lemma mayerVietorisδOn_apply (hUV : U ⊔ V = ⊤) (C : Compacts X) {K L : Set X}
    (hK : IsCompact K) (hL : IsCompact L) (hKU : K ⊆ U) (hLV : L ⊆ V)
    (hC : (C : Set X) ⊆ K ∪ L) {n m : ℕ} (h : n + 1 = m)
    (a : (TopPair.ofSubset (C : Set X)ᶜ).singularCohomology R k M n) :
    mayerVietorisδOn R k M U V hUV C n m h a =
      mayerVietorisδAux R k M U V hK hL hKU hLV n m h
        (singularCohomologyComplRestrict R k M hC n a) := by
  obtain ⟨hK₀, hL₀, hK₀U, hL₀V, -⟩ :=
    (exists_isCompact_subset_union U V hUV C.isCompact).choose_spec
  rw [mayerVietorisδOn, ConcreteCategory.comp_apply,
    ← mayerVietorisδAux_singularCohomologyComplRestrict U V hK₀ hL₀ hK₀U hL₀V (hK.union hK₀)
      (hL.union hL₀) (Set.union_subset hKU hK₀U) (Set.union_subset hLV hL₀V)
      Set.subset_union_right Set.subset_union_right,
    ← mayerVietorisδAux_singularCohomologyComplRestrict U V hK hL hKU hLV (hK.union hK₀)
      (hL.union hL₀) (Set.union_subset hKU hK₀U) (Set.union_subset hLV hL₀V)
      Set.subset_union_left Set.subset_union_left,
    singularCohomologyComplRestrict_apply_singularCohomologyComplRestrict,
    singularCohomologyComplRestrict_apply_singularCohomologyComplRestrict]

variable (R k M) in
/-- The **connecting map** `Hⁿ_c(X) ⟶ Hᵐ_c(U ∩ V)`, `n + 1 = m`, of the Mayer–Vietoris sequence of
cohomology with compact supports, for an open cover `X = U ∪ V` of a Hausdorff space. On
`Hⁿ(X, X ∖ (K ∪ L))` for compact sets `K ⊆ U` and `L ⊆ V` it is the connecting morphism
`Hⁿ(X, X ∖ (K ∪ L)) ⟶ Hᵐ(X, X ∖ (K ∩ L))` of the Mayer–Vietoris sequence of the pairs
`(X, X ∖ K)` and `(X, X ∖ L)`, followed by excision to `Hᵐ(U ∩ V, U ∩ V ∖ (K ∩ L))` and the map into
`Hᵐ_c(U ∩ V)` (`TopCat.compactSupportCohomologyι_compactSupportCohomologyMayerVietorisδ`). -/
def compactSupportCohomologyMayerVietorisδ (hUV : U ⊔ V = ⊤) (n m : ℕ)
    (h : n + 1 = m := by lia) :
    X.compactSupportCohomology R k M n ⟶
      ((Opens.toTopCat X).obj (U ⊓ V)).compactSupportCohomology R k M m :=
  compactSupportCohomologyDesc (fun C ↦ mayerVietorisδOn R k M U V hUV C n m h)
    fun C C' hCC' ↦ by
      obtain ⟨hK, hL, hKU, hLV, hC'⟩ :=
        (exists_isCompact_subset_union U V hUV C'.isCompact).choose_spec
      refine ConcreteCategory.ext_apply fun a ↦ ?_
      rw [ConcreteCategory.comp_apply, mayerVietorisδOn_apply U V hUV C' hK hL hKU hLV hC',
        singularCohomologyComplRestrict_apply_singularCohomologyComplRestrict
          (hCC' : (C : Set X) ⊆ C') hC',
        ← mayerVietorisδOn_apply U V hUV C hK hL hKU hLV
          (Set.Subset.trans (hCC' : (C : Set X) ⊆ C') hC')]

private lemma compactSupportCohomologyMayerVietorisδ_compactSupportCohomologyι_apply
    (hUV : U ⊔ V = ⊤) {n m : ℕ} (h : n + 1 = m) (C : Compacts X) {K L : Set X}
    (hK : IsCompact K) (hL : IsCompact L) (hKU : K ⊆ U) (hLV : L ⊆ V)
    (hC : (C : Set X) ⊆ K ∪ L) (a : (TopPair.ofSubset (C : Set X)ᶜ).singularCohomology R k M n) :
    compactSupportCohomologyMayerVietorisδ R k M U V hUV n m h (compactSupportCohomologyι n C a) =
      mayerVietorisδAux R k M U V hK hL hKU hLV n m h
        (singularCohomologyComplRestrict R k M hC n a) := by
  rw [← mayerVietorisδOn_apply, compactSupportCohomologyMayerVietorisδ,
    ← ConcreteCategory.comp_apply, compactSupportCohomologyι_desc]

variable (R k M) in
/-- **The connecting map of the Mayer–Vietoris sequence of cohomology with compact supports on
`Hⁿ(X, X ∖ C)`.** For compact sets `K ⊆ U` and `L ⊆ V` with `C ⊆ K ∪ L`, a class of
`Hⁿ(X, X ∖ C)` is restricted to `Hⁿ(X, X ∖ (K ∪ L))`, carried by the connecting morphism of the
pairs `(X, X ∖ K)` and `(X, X ∖ L)` to `Hᵐ(X, X ∖ (K ∩ L))`, restricted to `Hᵐ(X, X ∖ N)` and then
to `Hᵐ(U ∩ V, U ∩ V ∖ N)` for any compact `N ⊆ U ∩ V` containing `K ∩ L`, and mapped to
`Hᵐ_c(U ∩ V)`. -/
@[reassoc, elementwise]
lemma compactSupportCohomologyι_compactSupportCohomologyMayerVietorisδ (hUV : U ⊔ V = ⊤)
    (C : Compacts X) {K L : Set X} (hK : IsCompact K) (hL : IsCompact L) (hKU : K ⊆ U)
    (hLV : L ⊆ V) (hC : (C : Set X) ⊆ K ∪ L) (N : Compacts ((Opens.toTopCat X).obj (U ⊓ V)))
    (hN : K ∩ L ⊆ (N.map (Opens.inclusion' (U ⊓ V)) (Opens.inclusion' (U ⊓ V)).hom.continuous))
    (n m : ℕ) (h : n + 1 = m := by lia) :
    compactSupportCohomologyι n C ≫ compactSupportCohomologyMayerVietorisδ R k M U V hUV n m h =
      singularCohomologyComplRestrict R k M hC n ≫
        singularCohomologyComplMayerVietorisδ R k M hK.isClosed hL.isClosed n m h ≫
          singularCohomologyComplRestrict R k M hN m ≫
            singularCohomologyComplCompactsMap (U ⊓ V).isOpenEmbedding.injective N m ≫
              compactSupportCohomologyι m N :=
  ConcreteCategory.ext_apply fun a ↦ by
    simp only [ConcreteCategory.comp_apply]
    rw [compactSupportCohomologyMayerVietorisδ_compactSupportCohomologyι_apply U V hUV h C hK hL
      hKU hLV hC, mayerVietorisδAux_apply, compactSupportCohomologyRestrict_apply _ _ _ hN]

/-- The connecting map vanishes on classes supported in `U` or in `V`. -/
private lemma compactSupportCohomologyMayerVietorisδ_compactSupportCohomologyι_eq_zero
    (hUV : U ⊔ V = ⊤) {n m : ℕ} (h : n + 1 = m) (C : Compacts X)
    (hC : (C : Set X) ⊆ U ∨ (C : Set X) ⊆ V)
    (a : (TopPair.ofSubset (C : Set X)ᶜ).singularCohomology R k M n) :
    compactSupportCohomologyMayerVietorisδ R k M U V hUV n m h (compactSupportCohomologyι n C a) =
      0 := by
  rcases hC with hC | hC
  · rw [compactSupportCohomologyMayerVietorisδ_compactSupportCohomologyι_apply U V hUV h C
      C.isCompact isCompact_empty hC (Set.empty_subset _) Set.subset_union_left,
      mayerVietorisδAux_apply,
      singularCohomologyComplRestrict_singularCohomologyComplMayerVietorisδ_left_apply R k M
        C.isCompact.isClosed isCompact_empty.isClosed n m h, map_zero]
  · rw [compactSupportCohomologyMayerVietorisδ_compactSupportCohomologyι_apply U V hUV h C
      isCompact_empty C.isCompact (Set.empty_subset _) hC Set.subset_union_right,
      mayerVietorisδAux_apply,
      singularCohomologyComplRestrict_singularCohomologyComplMayerVietorisδ_right_apply R k M
        isCompact_empty.isClosed C.isCompact.isClosed n m h, map_zero]

variable (R k M) in
/-- The connecting map vanishes on classes extended from `Hⁿ_c(U)` and from `Hⁿ_c(V)`: the
composite `Hⁿ_c(U) ⊞ Hⁿ_c(V) ⟶ Hⁿ_c(X) ⟶ Hᵐ_c(U ∩ V)` is zero. -/
@[reassoc (attr := simp)]
lemma compactSupportCohomologyMayerVietorisFromBiprod_δ (hUV : U ⊔ V = ⊤) (n m : ℕ)
    (h : n + 1 = m := by lia) :
    compactSupportCohomologyMayerVietorisFromBiprod R k M U V n ≫
      compactSupportCohomologyMayerVietorisδ R k M U V hUV n m h = 0 := by
  have key (W : Opens X) (hW : W = U ∨ W = V) :
      compactSupportCohomologyExtend (R := R) (k := k) (M := M) W.isOpenEmbedding n ≫
        compactSupportCohomologyMayerVietorisδ R k M U V hUV n m h = 0 := by
    refine compactSupportCohomology_hom_ext fun K ↦ ?_
    rw [compactSupportCohomologyι_comp_extend_assoc, comp_zero]
    ext a
    have hK : (K.map (Opens.inclusion' W) (Opens.inclusion' W).hom.continuous : Set X) ⊆ W :=
      (Set.image_subset_range _ _).trans_eq (set_range_inclusion' W)
    simp only [ModuleCat.hom_comp, LinearMap.coe_comp, Function.comp_apply, ModuleCat.hom_zero,
      LinearMap.zero_apply]
    exact compactSupportCohomologyMayerVietorisδ_compactSupportCohomologyι_eq_zero U V hUV h _
      (hW.imp (fun hWU ↦ hWU ▸ hK) fun hWV ↦ hWV ▸ hK) _
  apply biprod.hom_ext'
  · rw [inl_compactSupportCohomologyMayerVietorisFromBiprod_assoc, comp_zero]
    exact key U (Or.inl rfl)
  · rw [inr_compactSupportCohomologyMayerVietorisFromBiprod_assoc, comp_zero]
    exact key V (Or.inr rfl)

/-- The extensions to `U` and to `V` of a class in the image of the connecting map vanish. -/
private lemma compactSupportCohomologyExtend_compactSupportCohomologyMayerVietorisδ_eq_zero
    (hUV : U ⊔ V = ⊤) {n m : ℕ} (h : n + 1 = m) (x : X.compactSupportCohomology R k M n) :
    compactSupportCohomologyExtend (isOpenEmbedding_toTopCat_map (homOfLE inf_le_left)) m
        (compactSupportCohomologyMayerVietorisδ R k M U V hUV n m h x) = 0 ∧
      compactSupportCohomologyExtend (isOpenEmbedding_toTopCat_map (homOfLE inf_le_right)) m
        (compactSupportCohomologyMayerVietorisδ R k M U V hUV n m h x) = 0 := by
  obtain ⟨C, -, a, rfl⟩ := exists_compactSupportCohomologyι_eq x ⊥
  obtain ⟨⟨K, L⟩, hK, hL, hKU, hLV, hC⟩ := exists_isCompact_subset_union U V hUV C.isCompact
  rw [compactSupportCohomologyMayerVietorisδ_compactSupportCohomologyι_apply U V hUV h C hK hL
    hKU hLV hC, mayerVietorisδAux_apply]
  constructor
  · rw [compactSupportCohomologyExtend_compactSupportCohomologyRestrict_of_comp_eq R k M
      U.isOpenEmbedding _ (U ⊓ V).isOpenEmbedding (toTopCat_map_comp_inclusion' _) _ _ hK
      (by rwa [set_range_inclusion']) Set.inter_subset_left,
      singularCohomologyComplMayerVietorisδ_singularCohomologyComplRestrict_left_apply R k M
        hK.isClosed hL.isClosed n m h, map_zero]
  · rw [compactSupportCohomologyExtend_compactSupportCohomologyRestrict_of_comp_eq R k M
      V.isOpenEmbedding _ (U ⊓ V).isOpenEmbedding (toTopCat_map_comp_inclusion' _) _ _ hL
      (by rwa [set_range_inclusion']) Set.inter_subset_right,
      singularCohomologyComplMayerVietorisδ_singularCohomologyComplRestrict_right_apply R k M
        hK.isClosed hL.isClosed n m h, map_zero]

variable (R k M) in
/-- The connecting map followed by `Hᵐ_c(U ∩ V) ⟶ Hᵐ_c(U) ⊞ Hᵐ_c(V)` is zero. -/
@[reassoc (attr := simp)]
lemma compactSupportCohomologyMayerVietorisδ_toBiprod (hUV : U ⊔ V = ⊤) (n m : ℕ)
    (h : n + 1 = m := by lia) :
    compactSupportCohomologyMayerVietorisδ R k M U V hUV n m h ≫
      compactSupportCohomologyMayerVietorisToBiprod R k M U V m = 0 := by
  apply biprod.hom_ext
  · rw [Category.assoc, compactSupportCohomologyMayerVietorisToBiprod_fst, zero_comp]
    refine ModuleCat.hom_ext (LinearMap.ext fun x ↦ ?_)
    simpa using (compactSupportCohomologyExtend_compactSupportCohomologyMayerVietorisδ_eq_zero
      U V hUV h x).1
  · rw [Category.assoc, compactSupportCohomologyMayerVietorisToBiprod_snd, zero_comp]
    refine ModuleCat.hom_ext (LinearMap.ext fun x ↦ ?_)
    simpa using (compactSupportCohomologyExtend_compactSupportCohomologyMayerVietorisδ_eq_zero
      U V hUV h x).2

/-- The heart of exactness of the Mayer–Vietoris sequence of cohomology with compact supports at
`Hⁿ_c(X)`: a class killed by the connecting map is the difference of the extensions of classes of
`Hⁿ_c(U)` and `Hⁿ_c(V)`. Represent the class on `K ∪ L` with `K ⊆ U` and `L ⊆ V` compact; its image
under the connecting morphism of `(X, X ∖ K)` and `(X, X ∖ L)` dies on a compact `T ⊆ U ∩ V`, so
after enlarging `K` and `L` by `T` it is killed by the connecting morphism, and Mayer–Vietoris
for the pairs splits it as a difference of classes supported in `K ∪ T ⊆ U` and `L ∪ T ⊆ V`. -/
private lemma exists_compactSupportCohomologyExtend_sub_eq (hUV : U ⊔ V = ⊤) {n m : ℕ}
    (h : n + 1 = m) (x : X.compactSupportCohomology R k M n)
    (hx : compactSupportCohomologyMayerVietorisδ R k M U V hUV n m h x = 0) :
    ∃ (y : ((Opens.toTopCat X).obj U).compactSupportCohomology R k M n)
      (z : ((Opens.toTopCat X).obj V).compactSupportCohomology R k M n),
        compactSupportCohomologyExtend U.isOpenEmbedding n y -
          compactSupportCohomologyExtend V.isOpenEmbedding n z = x := by
  obtain ⟨C, -, a, rfl⟩ := exists_compactSupportCohomologyι_eq x ⊥
  obtain ⟨⟨K, L⟩, hK, hL, hKU, hLV, hC⟩ := exists_isCompact_subset_union U V hUV C.isCompact
  dsimp only at hK hL hKU hLV hC
  rw [compactSupportCohomologyMayerVietorisδ_compactSupportCohomologyι_apply U V hUV h C hK hL
    hKU hLV hC, mayerVietorisδAux_apply] at hx
  -- the image of the class in `Hᵐ(X, X ∖ (K ∩ L))` dies on some compact `T ⊆ U ∩ V`
  obtain ⟨T, hT, hTW, hKLT, hzero⟩ :=
    exists_singularCohomologyComplRestrict_eq_zero_of_compactSupportCohomologyRestrict_eq_zero
      (U ⊓ V).isOpenEmbedding (hK.inter_right hL.isClosed)
      (inter_subset_range_inclusion'_inf U V hKU hLV) _ hx
  have hTUV : T ⊆ (U ⊓ V : Opens X) := by rwa [set_range_inclusion'] at hTW
  rw [Opens.coe_inf] at hTUV
  -- enlarge `K` and `L` by `T`
  have hK' := hK.union hT
  have hL' := hL.union hT
  have hK'U : K ∪ T ⊆ U := Set.union_subset hKU (hTUV.trans Set.inter_subset_left)
  have hL'V : L ∪ T ⊆ V := Set.union_subset hLV (hTUV.trans Set.inter_subset_right)
  have hδ : singularCohomologyComplMayerVietorisδ R k M hK'.isClosed hL'.isClosed n m h
      (singularCohomologyComplRestrict R k M
        (Set.union_subset_union (Set.subset_union_left (t := T))
          (Set.subset_union_left (t := T))) n
        (singularCohomologyComplRestrict R k M hC n a)) = 0 := by
    rw [← singularCohomologyComplMayerVietorisδ_naturality_of_subset_apply R k M hK.isClosed
      hL.isClosed hK'.isClosed hL'.isClosed Set.subset_union_left Set.subset_union_left n m h,
      ← singularCohomologyComplRestrict_apply_singularCohomologyComplRestrict hKLT
        (Set.subset_inter Set.subset_union_right Set.subset_union_right), hzero, map_zero]
  obtain ⟨b, c, hbc⟩ :=
    exists_sub_eq_of_singularCohomologyComplMayerVietorisδ_eq_zero
      hK'.isClosed hL'.isClosed h _ hδ
  refine ⟨compactSupportCohomologyRestrict R k M U.isOpenEmbedding hK'
      (by rwa [set_range_inclusion']) n b,
    compactSupportCohomologyRestrict R k M V.isOpenEmbedding hL'
      (by rwa [set_range_inclusion']) n c, ?_⟩
  rw [compactSupportCohomologyRestrict_comp_extend_apply,
    compactSupportCohomologyRestrict_comp_extend_apply]
  -- compare the two classes on the compact set `(K ∪ T) ∪ (L ∪ T)`
  let B : Compacts X := ⟨(K ∪ T) ∪ (L ∪ T), hK'.union hL'⟩
  rw [← singularCohomologyMap_comp_compactSupportCohomologyι_apply n (K := ⟨K ∪ T, hK'⟩) (L := B)
      Set.subset_union_left b,
    ← singularCohomologyMap_comp_compactSupportCohomologyι_apply n (K := ⟨L ∪ T, hL'⟩) (L := B)
      Set.subset_union_right c,
    ← map_sub, hbc, singularCohomologyComplRestrict_apply_singularCohomologyComplRestrict]
  exact singularCohomologyMap_comp_compactSupportCohomologyι_apply n (K := C) (L := B)
    (hC.trans (Set.union_subset_union Set.subset_union_left Set.subset_union_left)) a

variable (R k M) in
/-- **Exactness of the Mayer–Vietoris sequence of cohomology with compact supports at
`Hⁿ_c(X)`**, for an open cover `X = U ∪ V` of a Hausdorff space: a class killed by the connecting
map is a sum of extensions of classes of `Hⁿ_c(U)` and `Hⁿ_c(V)`. -/
lemma compactSupportCohomologyMayerVietoris_exact₃ (hUV : U ⊔ V = ⊤) (n m : ℕ)
    (h : n + 1 = m := by lia) :
    (ShortComplex.mk _ _
      (compactSupportCohomologyMayerVietorisFromBiprod_δ R k M U V hUV n m h)).Exact := by
  rw [ShortComplex.moduleCat_exact_iff]
  intro x hx
  obtain ⟨y, z, hyz⟩ := exists_compactSupportCohomologyExtend_sub_eq U V hUV h x hx
  let HU := ((Opens.toTopCat X).obj U).compactSupportCohomology R k M n
  let HV := ((Opens.toTopCat X).obj V).compactSupportCohomology R k M n
  refine ⟨(biprod.inl : HU ⟶ HU ⊞ HV) y + (biprod.inr : HV ⟶ HU ⊞ HV) (-z), ?_⟩
  dsimp only
  rw [map_add, inl_compactSupportCohomologyMayerVietorisFromBiprod_apply,
    inr_compactSupportCohomologyMayerVietorisFromBiprod_apply, map_neg, ← sub_eq_add_neg, hyz]

variable (R k M) in
/-- **Exactness of the Mayer–Vietoris sequence of cohomology with compact supports at
`Hᵐ_c(U ∩ V)`**, for an open cover `X = U ∪ V` of a Hausdorff space: a class whose extensions to
`U` and to `V` vanish is in the image of the connecting map. -/
lemma compactSupportCohomologyMayerVietoris_exact₁ (hUV : U ⊔ V = ⊤) (n m : ℕ)
    (h : n + 1 = m := by lia) :
    (ShortComplex.mk _ _
      (compactSupportCohomologyMayerVietorisδ_toBiprod R k M U V hUV n m h)).Exact := by
  rw [ShortComplex.moduleCat_exact_iff]
  intro y hy
  dsimp only at hy ⊢
  have hfst := compactSupportCohomologyMayerVietorisToBiprod_fst_apply R k M U V m y
  have hsnd := compactSupportCohomologyMayerVietorisToBiprod_snd_apply R k M U V m y
  rw [hy, map_zero] at hfst hsnd
  replace hfst := hfst.symm
  replace hsnd : compactSupportCohomologyExtend
      (isOpenEmbedding_toTopCat_map (homOfLE inf_le_right)) m y = 0 := by
    simpa using hsnd.symm
  obtain ⟨S, hS, hSW, z, rfl⟩ :=
    exists_compactSupportCohomologyRestrict_eq R k M (U ⊓ V).isOpenEmbedding y
  have hSUV : S ⊆ (U ⊓ V : Opens X) := by rwa [set_range_inclusion'] at hSW
  rw [Opens.coe_inf] at hSUV
  rw [compactSupportCohomologyExtend_compactSupportCohomologyRestrict_of_comp_eq R k M
    U.isOpenEmbedding _ (U ⊓ V).isOpenEmbedding (toTopCat_map_comp_inclusion' _) hS hSW hS
    (by rw [set_range_inclusion']; exact hSUV.trans Set.inter_subset_left) subset_rfl] at hfst
  rw [compactSupportCohomologyExtend_compactSupportCohomologyRestrict_of_comp_eq R k M
    V.isOpenEmbedding _ (U ⊓ V).isOpenEmbedding (toTopCat_map_comp_inclusion' _) hS hSW hS
    (by rw [set_range_inclusion']; exact hSUV.trans Set.inter_subset_right) subset_rfl] at hsnd
  obtain ⟨K, hK, hKU, hSK, hK0⟩ :=
    exists_singularCohomologyComplRestrict_eq_zero_of_compactSupportCohomologyRestrict_eq_zero
      _ _ _ _ hfst
  obtain ⟨L, hL, hLV, hSL, hL0⟩ :=
    exists_singularCohomologyComplRestrict_eq_zero_of_compactSupportCohomologyRestrict_eq_zero
      _ _ _ _ hsnd
  rw [singularCohomologyComplRestrict_apply_singularCohomologyComplRestrict] at hK0 hL0
  have hKU' : K ⊆ U := by rwa [set_range_inclusion'] at hKU
  have hLV' : L ⊆ V := by rwa [set_range_inclusion'] at hLV
  obtain ⟨a, ha⟩ := exists_singularCohomologyComplMayerVietorisδ_eq hK.isClosed hL.isClosed h
    (singularCohomologyComplRestrict R k M (Set.subset_inter hSK hSL) m z)
    (by rw [singularCohomologyComplRestrict_apply_singularCohomologyComplRestrict]; exact hK0)
    (by rw [singularCohomologyComplRestrict_apply_singularCohomologyComplRestrict]; exact hL0)
  have hid : singularCohomologyComplRestrict R k M (subset_rfl : K ∪ L ⊆ K ∪ L) n a = a := by
    rw [singularCohomologyComplRestrict, TopPair.ofSubsetMap_id, TopPair.singularCohomologyMap_id,
      ModuleCat.id_apply]
  refine ⟨compactSupportCohomologyι n ⟨K ∪ L, hK.union hL⟩ a, ?_⟩
  rw [compactSupportCohomologyMayerVietorisδ_compactSupportCohomologyι_apply U V hUV h _ hK hL
    hKU' hLV' subset_rfl, hid, mayerVietorisδAux_apply, ha,
    singularCohomologyComplRestrict_compactSupportCohomologyRestrict_apply]

variable (R k M) in
/-- If `Hⁿ_c(U ∩ V)` and `Hⁿ⁺¹_c(U ∩ V)` vanish, for instance when `U` and `V` are disjoint, the
middle map `Hⁿ_c(U) ⊞ Hⁿ_c(V) ⟶ Hⁿ_c(X)` of the Mayer–Vietoris sequence of an open cover
`X = U ∪ V` is an isomorphism. -/
lemma isIso_compactSupportCohomologyMayerVietorisFromBiprod_of_isZero (hUV : U ⊔ V = ⊤) (n : ℕ)
    (h₀ : IsZero (((Opens.toTopCat X).obj (U ⊓ V)).compactSupportCohomology R k M n))
    (h₁ : IsZero (((Opens.toTopCat X).obj (U ⊓ V)).compactSupportCohomology R k M (n + 1))) :
    IsIso (compactSupportCohomologyMayerVietorisFromBiprod R k M U V n) := by
  have := (compactSupportCohomologyMayerVietoris_exact₂ R k M U V hUV n).mono_g
    (h₀.eq_of_src _ _)
  have := (compactSupportCohomologyMayerVietoris_exact₃ R k M U V hUV n (n + 1)).epi_f
    (h₁.eq_of_tgt _ _)
  exact isIso_of_mono_of_epi _

variable (R k M) in
/-- If `Hⁿ_c(U)`, `Hⁿ_c(V)` and `Hⁿ⁺¹_c(U ∩ V)` vanish, then so does `Hⁿ_c(X)`, for an open cover
`X = U ∪ V` of a Hausdorff space: it sits between `Hⁿ_c(U) ⊞ Hⁿ_c(V)` and `Hⁿ⁺¹_c(U ∩ V)` in the
Mayer–Vietoris sequence. -/
lemma isZero_compactSupportCohomology_of_sup_eq_top (hUV : U ⊔ V = ⊤) (n : ℕ)
    (hU : IsZero (((Opens.toTopCat X).obj U).compactSupportCohomology R k M n))
    (hV : IsZero (((Opens.toTopCat X).obj V).compactSupportCohomology R k M n))
    (hUV₁ : IsZero (((Opens.toTopCat X).obj (U ⊓ V)).compactSupportCohomology R k M (n + 1))) :
    IsZero (X.compactSupportCohomology R k M n) :=
  (compactSupportCohomologyMayerVietoris_exact₃ R k M U V hUV n (n + 1)).isZero_X₂
    (((biprod_isZero_iff _ _).2 ⟨hU, hV⟩).eq_of_src _ _) (hUV₁.eq_of_tgt _ _)

variable (R k M) in
/-- For a cover of `X` by two disjoint open sets `U` and `V`, the sum
`Hⁿ_c(U) ⊞ Hⁿ_c(V) ⟶ Hⁿ_c(X)` of the extensions along the subspace inclusions `↥U → X` and
`↥V → X` is an isomorphism: it is the middle map of the Mayer–Vietoris sequence, and
`Hᵐ_c(U ∩ V)` vanishes in every degree. -/
lemma isIso_biprodDesc_compactSupportCohomologyExtend_of_disjoint (hUV : U ⊔ V = ⊤)
    (hd : Disjoint U V) (n : ℕ) :
    IsIso (biprod.desc
      (compactSupportCohomologyExtend (R := R) (k := k) (M := M)
        (f := ofHom (⟨Subtype.val, continuous_subtypeVal⟩ : C(U, X))) U.isOpenEmbedding' n)
      (compactSupportCohomologyExtend (R := R) (k := k) (M := M)
        (f := ofHom (⟨Subtype.val, continuous_subtypeVal⟩ : C(V, X))) V.isOpenEmbedding' n)) := by
  have : IsEmpty ((Opens.toTopCat X).obj (U ⊓ V)) :=
    ⟨fun x ↦ Set.disjoint_left.1 (Opens.coe_disjoint.2 hd) (Opens.mem_inf.1 x.property).1
      (Opens.mem_inf.1 x.property).2⟩
  have h (m : ℕ) := (TauCeti.isZero_singularCohomology_of_isEmpty R k M
    ((Opens.toTopCat X).obj (U ⊓ V)) m).of_iso (compactSupportCohomologyIsoOfCompactSpace m)
  -- By definition, `compactSupportCohomologyMayerVietorisFromBiprod` is this map, read on
  -- `(Opens.toTopCat X).obj U = TopCat.of ↥U`, with `Opens.inclusion' U` the subspace inclusion.
  exact isIso_compactSupportCohomologyMayerVietorisFromBiprod_of_isZero R k M U V hUV n (h n)
    (h (n + 1))

end Connecting

end TopCat
