/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.HomologySequenceLemmas
public import TauCeti.Algebra.Homology.HomologicalComplex.Biprod
public import TauCeti.AlgebraicTopology.Singular.MayerVietoris.Basic
public import TauCeti.AlgebraicTopology.Singular.Subdivision.Small.Subcomplex
public import TauCeti.Geometry.Manifold.SmoothSingular.Subdivision

/-!
# The Mayer–Vietoris step for smooth singular chains

Let `U` and `V` be open subsets of a manifold `M`. A singular simplex of `M` comes from a smooth
singular simplex of `U` exactly when it is smooth and its image lies in `U`
(`TauCeti.range_smoothSingularSubcomplex_ι_comp_subtypeVal`), because smoothness into an open
submanifold is smoothness into `M`. Hence the smooth singular simplicial sets of `U ∩ V`, `U` and
`V` form a pushout square with the smooth singular simplices of `M` lying in `U` or in `V`
(`TauCeti.isPushout_smoothSingularSubcomplex_inf`), the smooth analogue of the square of singular
simplicial sets behind the Mayer–Vietoris sequence of singular homology
(`TopCat.isPushout_toSSet_inter_smallSingularSubcomplex`).

The inclusions of smooth singular simplices into singular simplices form a map from the smooth
square to the singular one, hence a map of Mayer–Vietoris short exact sequences of chain
complexes. If `U` and `V` cover `M` and the inclusion of smooth into singular chains is a
quasi-isomorphism on `U ∩ V`, on `U` and on `V`, the five lemma makes the map on the third terms a
quasi-isomorphism: the smooth singular chains of `M` subordinate to the cover include into the
singular chains subordinate to it by a quasi-isomorphism. By the small-chain theorems for smooth
chains (`TauCeti.quasiIso_chainComplexMap_homOfLE_inf_smallSingularSubcomplex`) and for singular
chains (`TauCeti.quasiIso_chainComplexMap_smallSingularSubcomplex_ι`), the inclusion of smooth
singular chains of `M` into all singular chains of `M` is then a quasi-isomorphism
(`TauCeti.quasiIso_chainComplexMap_smoothSingularSubcomplex_ι_of_union_eq_univ`). The five-lemma
argument follows `TauCeti.quasiIso_chainComplexMap_smallSingularSubcomplex_ι_of_nhds` in
`TauCeti/AlgebraicTopology/Singular/MayerVietoris/Excisive.lean`, through the shared
`SSet.quasiIso_chainComplexMap_of_isPushout`.

This is the Mayer–Vietoris step of the comparison of smooth with continuous singular homology, by
induction over open sets (`TauCeti.mayerVietoris_induction`); the disjoint-union step is
`TauCeti.quasiIso_chainComplexMap_smoothSingularSubcomplex_ι_iSup`. No finite-dimensionality,
separation or boundarylessness of `M` is used.

## Main results

* `TauCeti.isPushout_smoothSingularSubcomplex_inf`: the smooth singular simplicial sets of
  `U ∩ V`, `U` and `V` form a pushout square with the smooth singular simplices of `M` lying in
  `U` or in `V`.
* `TauCeti.quasiIso_chainComplexMap_homOfLE_smoothSingularSubcomplex_inf`: if smooth chains
  include into singular chains by a quasi-isomorphism on `U ∩ V`, `U` and `V`, the smooth chains
  of `M` subordinate to `{U, V}` include into the singular chains subordinate to `{U, V}` by a
  quasi-isomorphism.
* `TauCeti.quasiIso_chainComplexMap_smoothSingularSubcomplex_ι_of_union_eq_univ`: if smooth
  chains include into singular chains by a quasi-isomorphism on `U ∩ V`, `U` and `V`, and `U`
  and `V` cover `M`, they do so on `M`.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Chapter 18, proof of Theorem 18.7 (the
  Mayer–Vietoris step of the comparison of smooth and singular homology).
* A. Hatcher, *Algebraic Topology*, Section 2.2, the Mayer–Vietoris sequences.
-/

public section

noncomputable section

open CategoryTheory Limits TopologicalSpace

universe u v w

namespace TauCeti

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} {M : Type u} [TopologicalSpace M] [ChartedSpace H M]

/-! ### Smooth singular simplices of open subsets -/

/-- A singular simplex of `M` comes from a smooth singular simplex of an open subset `W` exactly
when it is smooth and its image lies in `W`. -/
theorem mem_range_smoothSingularSubcomplex_ι_comp_subtypeVal_iff (W : Opens M)
    {n : SimplexCategoryᵒᵖ} (σ : (TopCat.toSSet.obj (TopCat.of M)).obj n) :
    σ ∈ (SSet.Subcomplex.range ((smoothSingularSubcomplex I W).ι ≫
        TopCat.toSSet.map (TopCat.ofHom (ContinuousMap.subtypeVal (W : Set M))))).obj n ↔
      σ ∈ (smoothSingularSubcomplex I M).obj n ∧
        Set.range ((TopCat.of M).toSSetObjEquiv n σ) ⊆ W := by
  rw [range_smoothSingularSubcomplex_ι_comp_subtypeVal, Subfunctor.min_obj, Set.mem_inter_iff]
  exact and_congr_right' (TopCat.mem_range_toSSet_subtypeVal_iff (X := TopCat.of M) W n σ)

variable (I) in
/-- The map from the smooth singular simplices of an open subset `W` of `M` to the smooth singular
simplices of `M` subordinate to a family of sets `S`, one of which contains `W`. -/
def toSmoothSmallSingularSubcomplex {ι : Type*} (S : ι → Set M) {W : Opens M} {i : ι}
    (h : (W : Set M) ⊆ S i) :
    (smoothSingularSubcomplex I W : SSet) ⟶
      ((smoothSingularSubcomplex I M ⊓ (TopCat.of M).smallSingularSubcomplex S :
        (TopCat.toSSet.obj (TopCat.of M)).Subcomplex) : SSet) :=
  SSet.Subcomplex.lift ((smoothSingularSubcomplex I W).ι ≫
      TopCat.toSSet.map (TopCat.ofHom (ContinuousMap.subtypeVal (W : Set M)))) (by
    rintro n _ ⟨σ, rfl⟩
    obtain ⟨hσ, hW⟩ :=
      (mem_range_smoothSingularSubcomplex_ι_comp_subtypeVal_iff W _).1 ⟨σ, rfl⟩
    exact ⟨hσ, ((TopCat.of M).mem_smallSingularSubcomplex_iff S _).2 ⟨i, hW.trans h⟩⟩)

/-- Followed by the inclusion into singular simplices of `M`, the map
`toSmoothSmallSingularSubcomplex` reads a smooth singular simplex of `W` in `M`. -/
@[reassoc (attr := simp)]
theorem toSmoothSmallSingularSubcomplex_ι {ι : Type*} (S : ι → Set M) {W : Opens M} {i : ι}
    (h : (W : Set M) ⊆ S i) :
    toSmoothSmallSingularSubcomplex I S h ≫
        (smoothSingularSubcomplex I M ⊓ (TopCat.of M).smallSingularSubcomplex S).ι =
      (smoothSingularSubcomplex I W).ι ≫
        TopCat.toSSet.map (TopCat.ofHom (ContinuousMap.subtypeVal (W : Set M))) :=
  SSet.Subcomplex.lift_ι _ _

/-- The map `toSmoothSmallSingularSubcomplex` followed by the inclusion of smooth subordinate
simplices into all subordinate simplices is the map of `W` into the subordinate singular
simplices of `M`, restricted to smooth simplices. -/
@[reassoc (attr := simp)]
theorem toSmoothSmallSingularSubcomplex_homOfLE {ι : Type*} (S : ι → Set M) {W : Opens M} {i : ι}
    (h : (W : Set M) ⊆ S i) :
    toSmoothSmallSingularSubcomplex I S h ≫ SSet.Subcomplex.homOfLE inf_le_right =
      (smoothSingularSubcomplex I W).ι ≫ (TopCat.of M).toSmallSingularSubcomplex S h := by
  rw [← cancel_mono (SSet.Subcomplex.ι _), Category.assoc, SSet.Subcomplex.homOfLE_ι,
    toSmoothSmallSingularSubcomplex_ι, Category.assoc, TopCat.toSmallSingularSubcomplex_ι]

/-! ### The smooth Mayer–Vietoris square -/

/-- The smooth singular simplices of `M` lying in `U ∩ V`, in `U`, in `V`, and in `U` or in `V`,
form a bicartesian square of subcomplexes. -/
private theorem bicartSq_range_smoothSingularSubcomplex (U V : Opens M) :
    SSet.Subcomplex.BicartSq
      (SSet.Subcomplex.range ((smoothSingularSubcomplex I ↥(U ⊓ V)).ι ≫
        TopCat.toSSet.map (TopCat.ofHom (ContinuousMap.subtypeVal ((U ⊓ V : Opens M) : Set M)))))
      (SSet.Subcomplex.range ((smoothSingularSubcomplex I U).ι ≫
        TopCat.toSSet.map (TopCat.ofHom (ContinuousMap.subtypeVal (U : Set M)))))
      (SSet.Subcomplex.range ((smoothSingularSubcomplex I V).ι ≫
        TopCat.toSSet.map (TopCat.ofHom (ContinuousMap.subtypeVal (V : Set M)))))
      (smoothSingularSubcomplex I M ⊓ (TopCat.of M).smallSingularSubcomplex ![(U : Set M), V]) where
  sup_eq := by
    ext n σ
    simp only [Subfunctor.max_obj, Subfunctor.min_obj, Set.mem_union, Set.mem_inter_iff,
      mem_range_smoothSingularSubcomplex_ι_comp_subtypeVal_iff,
      TopCat.mem_smallSingularSubcomplex_iff, Fin.exists_fin_two, Matrix.cons_val_zero,
      Matrix.cons_val_one]
    tauto
  inf_eq := by
    ext n σ
    rw [Subfunctor.min_obj, Set.mem_inter_iff,
      mem_range_smoothSingularSubcomplex_ι_comp_subtypeVal_iff,
      mem_range_smoothSingularSubcomplex_ι_comp_subtypeVal_iff,
      mem_range_smoothSingularSubcomplex_ι_comp_subtypeVal_iff, Opens.coe_inf,
      Set.subset_inter_iff]
    tauto

variable (I) in
/-- **The smooth singular simplicial sets of an intersection form a pushout square.** For open
subsets `U` and `V` of `M`, the smooth singular simplicial sets of `U ∩ V`, `U` and `V` form a
pushout square with the smooth singular simplices of `M` whose image lies in `U` or in `V`. -/
theorem isPushout_smoothSingularSubcomplex_inf (U V : Opens M) :
    IsPushout
      (smoothSingularSubcomplexMap (Opens.inclusion (inf_le_left : U ⊓ V ≤ U))
        (contMDiff_inclusion _))
      (smoothSingularSubcomplexMap (Opens.inclusion (inf_le_right : U ⊓ V ≤ V))
        (contMDiff_inclusion _))
      (toSmoothSmallSingularSubcomplex I ![(U : Set M), V] (W := U)
        (Matrix.cons_val_zero (U : Set M) ![(V : Set M)]).superset)
      (toSmoothSmallSingularSubcomplex I ![(U : Set M), V] (W := V)
        ((Matrix.cons_val_one (U : Set M) ![(V : Set M)]).trans
          (Matrix.cons_val_zero (V : Set M) ![])).superset) := by
  -- Each smooth singular simplicial set of an open subset embeds in that of `M`.
  let g (W : Opens M) : (smoothSingularSubcomplex I W : SSet) ⟶ TopCat.toSSet.obj (TopCat.of M) :=
    (smoothSingularSubcomplex I W).ι ≫
      TopCat.toSSet.map (TopCat.ofHom (ContinuousMap.subtypeVal (W : Set M)))
  have hg (W : Opens M) : Mono (g W) := by
    have : Mono (TopCat.toSSet.map (TopCat.ofHom (ContinuousMap.subtypeVal (W : Set M)))) :=
      Functor.map_mono _ _
    exact mono_comp _ _
  let A := SSet.Subcomplex.range (g (U ⊓ V))
  let B := SSet.Subcomplex.range (g U)
  let C := SSet.Subcomplex.range (g V)
  have sq : SSet.Subcomplex.BicartSq A B C _ := bicartSq_range_smoothSingularSubcomplex U V
  refine sq.isPushout.of_iso' (asIso (SSet.Subcomplex.toRange (g (U ⊓ V))))
    (asIso (SSet.Subcomplex.toRange (g U))) (asIso (SSet.Subcomplex.toRange (g V))) (Iso.refl _)
    ?_ ?_ ?_ ?_
  · rw [← cancel_mono B.ι]
    simp only [A, B, asIso_hom, Category.assoc, SSet.Subcomplex.homOfLE_ι,
      SSet.Subcomplex.toRange_ι, g]
    rw [smoothSingularSubcomplexMap_inclusion_ι_assoc, ← Functor.map_comp, ← TopCat.ofHom_comp,
      ContinuousMap.subtypeVal_comp_inclusion]
  · rw [← cancel_mono C.ι]
    simp only [A, C, asIso_hom, Category.assoc, SSet.Subcomplex.homOfLE_ι,
      SSet.Subcomplex.toRange_ι, g]
    rw [smoothSingularSubcomplexMap_inclusion_ι_assoc, ← Functor.map_comp, ← TopCat.ofHom_comp,
      ContinuousMap.subtypeVal_comp_inclusion]
  · rw [← cancel_mono (SSet.Subcomplex.ι _)]
    simp only [asIso_hom, Iso.refl_hom, Category.assoc, Category.comp_id,
      SSet.Subcomplex.homOfLE_ι, toSmoothSmallSingularSubcomplex_ι]
    exact SSet.Subcomplex.toRange_ι _
  · rw [← cancel_mono (SSet.Subcomplex.ι _)]
    simp only [asIso_hom, Iso.refl_hom, Category.assoc, Category.comp_id,
      SSet.Subcomplex.homOfLE_ι, toSmoothSmallSingularSubcomplex_ι]
    exact SSet.Subcomplex.toRange_ι _

/-! ### The Mayer–Vietoris step of the comparison with singular chains -/

variable {C : Type v} [Category.{w} C] [Abelian C] [HasCoproducts.{u} C] (R : C)

/-- **Mayer–Vietoris for the inclusion of smooth chains.** Let `U` and `V` be open subsets of `M`.
If the inclusion of smooth singular chains into singular chains with coefficients in `R` is a
quasi-isomorphism on `U ∩ V`, on `U` and on `V`, then the smooth singular chains of `M` subordinate
to the cover by `U` and `V` include into the singular chains subordinate to it by a
quasi-isomorphism. -/
theorem quasiIso_chainComplexMap_homOfLE_smoothSingularSubcomplex_inf {U V : Opens M}
    (hU : QuasiIso (SSet.chainComplexMap (smoothSingularSubcomplex I U).ι R))
    (hV : QuasiIso (SSet.chainComplexMap (smoothSingularSubcomplex I V).ι R))
    (hUinfV : QuasiIso (SSet.chainComplexMap (smoothSingularSubcomplex I ↥(U ⊓ V)).ι R)) :
    QuasiIso (SSet.chainComplexMap (SSet.Subcomplex.homOfLE (inf_le_right :
      smoothSingularSubcomplex I M ⊓ (TopCat.of M).smallSingularSubcomplex ![(U : Set M), V] ≤
        (TopCat.of M).smallSingularSubcomplex ![(U : Set M), V])) R) := by
  -- The inclusions of smooth singular simplices form a map from the smooth Mayer–Vietoris square
  -- to the singular one.
  have ht : smoothSingularSubcomplexMap (Opens.inclusion (inf_le_left : U ⊓ V ≤ U))
        (contMDiff_inclusion _) ≫ (smoothSingularSubcomplex I U).ι =
      (smoothSingularSubcomplex I ↥(U ⊓ V)).ι ≫ TopCat.toSSet.map (TopCat.ofHom
        (ContinuousMap.inclusion (Set.inter_subset_left (s := (U : Set M)) (t := V)))) :=
    smoothSingularSubcomplexMap_inclusion_ι _
  have hl : smoothSingularSubcomplexMap (Opens.inclusion (inf_le_right : U ⊓ V ≤ V))
        (contMDiff_inclusion _) ≫ (smoothSingularSubcomplex I V).ι =
      (smoothSingularSubcomplex I ↥(U ⊓ V)).ι ≫ TopCat.toSSet.map (TopCat.ofHom
        (ContinuousMap.inclusion (Set.inter_subset_right (s := (U : Set M)) (t := V)))) :=
    smoothSingularSubcomplexMap_inclusion_ι _
  -- The map of Mayer–Vietoris short exact sequences is a quasi-isomorphism on the first two
  -- terms, hence on the third.
  exact SSet.quasiIso_chainComplexMap_of_isPushout R (isPushout_smoothSingularSubcomplex_inf I U V)
    (TopCat.isPushout_toSSet_inter_smallSingularSubcomplex (X := TopCat.of M) U V) ht hl
    (toSmoothSmallSingularSubcomplex_homOfLE _ _) (toSmoothSmallSingularSubcomplex_homOfLE _ _)
    hUinfV hU hV

/-- **The Mayer–Vietoris step of the smoothing theorem.** Let `U` and `V` be open subsets covering
`M`. If the inclusion of smooth singular chains into singular chains with coefficients in `R` is a
quasi-isomorphism on `U ∩ V`, on `U` and on `V`, then it is a quasi-isomorphism on `M`. -/
theorem quasiIso_chainComplexMap_smoothSingularSubcomplex_ι_of_union_eq_univ {U V : Opens M}
    (hUV : (U : Set M) ∪ V = Set.univ)
    (hU : QuasiIso (SSet.chainComplexMap (smoothSingularSubcomplex I U).ι R))
    (hV : QuasiIso (SSet.chainComplexMap (smoothSingularSubcomplex I V).ι R))
    (hUinfV : QuasiIso (SSet.chainComplexMap (smoothSingularSubcomplex I ↥(U ⊓ V)).ι R)) :
    QuasiIso (SSet.chainComplexMap (smoothSingularSubcomplex I M).ι R) := by
  have hcov : ⋃ i, ![(U : Set M), V] i = Set.univ := ((U : Set M).iUnion_vecCons_pair V).trans hUV
  have hopen : ∀ i, IsOpen (![(U : Set M), V] i) := U.isOpen.vecCons V.isOpen
  let D := smoothSingularSubcomplex I M ⊓
    (TopCat.of M).smallSingularSubcomplex ![(U : Set M), V]
  -- The inclusion of the smooth chains subordinate to the cover into all singular chains factors
  -- through all smooth chains and through all chains subordinate to the cover. The small-chain
  -- theorems make the second maps of both factorizations quasi-isomorphisms.
  have := quasiIso_chainComplexMap_homOfLE_inf_smallSingularSubcomplex R
    (smoothSingularSubcomplex I M) ![(U : Set M), V] hopen hcov
  have := quasiIso_chainComplexMap_smallSingularSubcomplex_ι R (X := TopCat.of M)
    ![(U : Set M), V] hopen hcov
  have := quasiIso_chainComplexMap_homOfLE_smoothSingularSubcomplex_inf R hU hV hUinfV
  have hfac : SSet.chainComplexMap (SSet.Subcomplex.homOfLE (inf_le_left : D ≤ _)) R ≫
        SSet.chainComplexMap (smoothSingularSubcomplex I M).ι R =
      SSet.chainComplexMap (SSet.Subcomplex.homOfLE (inf_le_right : D ≤ _)) R ≫
        SSet.chainComplexMap ((TopCat.of M).smallSingularSubcomplex ![(U : Set M), V]).ι R := by
    simp only [← Functor.map_comp, SSet.Subcomplex.homOfLE_ι]
  have : QuasiIso (SSet.chainComplexMap (SSet.Subcomplex.homOfLE (inf_le_left : D ≤ _)) R ≫
      SSet.chainComplexMap (smoothSingularSubcomplex I M).ι R) := by
    rw [hfac]
    infer_instance
  exact quasiIso_of_comp_left
    (SSet.chainComplexMap (SSet.Subcomplex.homOfLE (inf_le_left : D ≤ _)) R)
    (SSet.chainComplexMap (smoothSingularSubcomplex I M).ι R)

end TauCeti
