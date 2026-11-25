/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.SimplicialSet.Subcomplex
public import TauCeti.AlgebraicTopology.Singular.MayerVietoris.Basic
public import TauCeti.AlgebraicTopology.Singular.Subdivision.Small.Subcomplex
public import TauCeti.Geometry.Manifold.SmoothSingular.Subdivision

/-!
# The Mayer–Vietoris sequence of smooth singular chains

Let `M` be a manifold and let `U` and `V` be open subsets. This file proves that if the inclusion
of smooth singular chains into singular chains is a quasi-isomorphism on `U`, on `V` and on
`U ∩ V`, then it is one on `U ∪ V`
(`TauCeti.quasiIso_chainComplexMap_smoothSingularSubcomplex_ι_sup`). This is the binary-union
hypothesis of Mayer–Vietoris induction (`TauCeti.mayerVietoris_induction`) for the comparison of
smooth with singular homology; the disjoint-union hypothesis is
`TauCeti.quasiIso_chainComplexMap_smoothSingularSubcomplex_ι_iSup`.

Write `W = U ∪ V` and `S` for the smooth singular simplices of `W`. Inside the singular simplicial
set of `W`, the simplices lying in `U ∩ V`, in `U` and in `V` and the simplices lying in `U` or in
`V` form a bicartesian square of subcomplexes (`TopCat.bicartSq_range_toSSet_map_inclusion`), and
intersecting it with `S` gives the bicartesian square of the corresponding smooth simplices
(`Lattice.BicartSq.inf_left`). Its corners are the smooth simplices of `U ∩ V`, of
`U` and of `V`: a singular simplex of `W` lying in `U` is smooth exactly when it is smooth as a
simplex of `U` (`TauCeti.range_smoothSingularSubcomplexMap_inclusion_ι`). The inclusion of the
smooth square into the singular square is a map of Mayer–Vietoris short exact sequences of chain
complexes. By hypothesis it is a quasi-isomorphism on the first two terms
(`TauCeti.quasiIso_chainComplexMap_smoothSingularSubcomplex_ι_iff_homOfLE`), hence on the third,
the chains of simplices lying in `U` or in `V`
(`SSet.quasiIso_chainComplexMap_homOfLE_inf_of_bicartSq`). The small-chain theorems, for singular
chains and for the affinely stable subcomplex `S`, identify the homology of those chains with the
singular and the smooth singular homology of `W`
(`TauCeti.quasiIso_chainComplexMap_ι_iff_homOfLE_inf_smallSingularSubcomplex`), which gives the
conclusion.

A singular simplex of an open set `U` is smooth in `U` precisely when its image in `M` is smooth,
so the smooth singular subcomplexes of `U ⊓ V`, `U`, and `V` form a pushout square with the
subcomplex `TauCeti.smallSmoothSingularSubcomplex I ![(U : Set M), (V : Set M)]` of smooth singular
simplices of `M` whose image lies in `U` or in `V`
(`TauCeti.isPushout_smoothSingularSubcomplex_inter_smallSmoothSingularSubcomplex`). When
`U ⊔ V = ⊤`, the small-chain theorem for affinely stable subcomplexes
(`TauCeti.subcomplexSmallHomologyIso`) identifies the homology of this subcomplex with the smooth
singular homology of `M`; combined with the Mayer–Vietoris sequence of a pushout of simplicial sets
this gives the Mayer–Vietoris long exact sequence of smooth singular homology, with connecting
morphism `TauCeti.smoothMayerVietorisδ`, compatible with the singular Mayer–Vietoris connecting
morphism (`TauCeti.smoothMayerVietorisδ_ι`).

No `IsManifold` hypothesis on `M`, Hausdorff property or finite-dimensionality is used.

## Main results

* `TauCeti.quasiIso_chainComplexMap_smoothSingularSubcomplex_ι_iff_homOfLE`: for open sets
  `U ≤ W`, the inclusion of smooth into singular chains of `U` is a quasi-isomorphism exactly when
  that of the smooth simplices of `W` lying in `U` into all singular simplices of `W` lying in `U`
  is.
* `TauCeti.quasiIso_chainComplexMap_smoothSingularSubcomplex_ι_sup`: the Mayer–Vietoris step of the
  comparison of smooth and singular chains.
* `TauCeti.smallSmoothSingularSubcomplex`, `TauCeti.mem_smallSmoothSingularSubcomplex_iff`, and
  `TauCeti.toSmallSmoothSingularSubcomplex`: the subcomplex of smooth singular simplices
  subordinate to a family of subsets, its membership characterization, and the map into it from an
  open subset contained in a member of the family.
* `TauCeti.isPushout_smoothSingularSubcomplex_inter_smallSmoothSingularSubcomplex`: the pushout
  square of smooth singular subcomplexes for two open sets.
* `TauCeti.smoothMayerVietorisδ`, `TauCeti.smoothMayerVietoris_exact₁`,
  `TauCeti.smoothMayerVietoris_exact₂`, `TauCeti.smoothMayerVietoris_exact₃`: the Mayer–Vietoris
  connecting morphism and long exact sequence in smooth singular homology, compatible with singular
  Mayer–Vietoris via `TauCeti.smoothMayerVietorisδ_ι`.
* `TauCeti.quasiIso_chainComplexMap_smoothSingularSubcomplex_ι_of_sup_eq_top`: the binary-cover
  step of the comparison: for `U ⊔ V = ⊤`, quasi-isomorphisms on `U`, `V` and `U ⊓ V` give one on
  `M`.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Chapter 18, proof of Theorem 18.7 (the
  Mayer–Vietoris step of the comparison of smooth and singular homology).
* A. Hatcher, *Algebraic Topology*, Section 2.2, the Mayer–Vietoris sequences.
-/

public section

noncomputable section

open CategoryTheory Limits TopologicalSpace Topology
open scoped Manifold ContDiff

universe u v w

namespace TauCeti

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} {M : Type u} [TopologicalSpace M] [ChartedSpace H M]

section Inclusion

variable {U W : Opens M} (h : U ≤ W)

variable {C : Type v} [Category.{w} C] [Preadditive C] [HasCoproducts.{u} C]
  [CategoryWithHomology C] (R : C)

variable (I) in
/-- For open sets `U ≤ W` of `M`, the inclusion of smooth singular chains into singular chains of
`U` is a quasi-isomorphism exactly when the inclusion of the chains of the smooth singular
simplices of `W` lying in `U` into the chains of all singular simplices of `W` lying in `U` is
one. The two inclusions are isomorphic as arrows. -/
theorem quasiIso_chainComplexMap_smoothSingularSubcomplex_ι_iff_homOfLE :
    QuasiIso (SSet.chainComplexMap (smoothSingularSubcomplex I U).ι R) ↔
      QuasiIso (SSet.chainComplexMap (SSet.Subcomplex.homOfLE (inf_le_right :
        smoothSingularSubcomplex I W ⊓ SSet.Subcomplex.range
            (TopCat.toSSet.map (TopCat.ofHom ⟨Opens.inclusion h, continuous_inclusion h⟩)) ≤
          SSet.Subcomplex.range
            (TopCat.toSSet.map (TopCat.ofHom ⟨Opens.inclusion h, continuous_inclusion h⟩))))
        R) := by
  have : Mono (TopCat.ofHom ⟨Opens.inclusion h, continuous_inclusion h⟩) :=
    (TopCat.mono_iff_injective _).2 (Set.inclusion_injective h)
  refine SSet.Subcomplex.morphismProperty_iff_homOfLE_of_range_eq
    ((HomologicalComplex.quasiIso C _).inverseImage ((SSet.chainComplexFunctor C).obj R)) _ _ _ ?_
    rfl
  rw [← range_smoothSingularSubcomplexMap_inclusion_ι h, smoothSingularSubcomplexMap_ι]

end Inclusion

section MayerVietoris

variable (I) {C : Type v} [Category.{w} C] [Abelian C] [HasCoproducts.{u} C] (R : C)

/-- **The Mayer–Vietoris step of the comparison of smooth and singular chains.** If the inclusion
of smooth singular chains into singular chains, with coefficients in `R`, is a quasi-isomorphism on
the open sets `U`, `V` and `U ∩ V` of `M`, then it is a quasi-isomorphism on `U ∪ V`. -/
theorem quasiIso_chainComplexMap_smoothSingularSubcomplex_ι_sup (U V : Opens M)
    (hU : QuasiIso (SSet.chainComplexMap (smoothSingularSubcomplex I U).ι R))
    (hV : QuasiIso (SSet.chainComplexMap (smoothSingularSubcomplex I V).ι R))
    (hUV : QuasiIso (SSet.chainComplexMap (smoothSingularSubcomplex I ↥(U ⊓ V)).ι R)) :
    QuasiIso (SSet.chainComplexMap (smoothSingularSubcomplex I ↥(U ⊔ V)).ι R) := by
  let S := smoothSingularSubcomplex I ↥(U ⊔ V)
  -- Intersecting the bicartesian square of singular simplices lying in `U ∩ V`, `U`, `V` and
  -- `U` or `V` with `S` gives the square of smooth simplices, and comparing their Mayer–Vietoris
  -- sequences gives a quasi-isomorphism on the chains of simplices lying in `U` or in `V`.
  have h₃ := SSet.quasiIso_chainComplexMap_homOfLE_inf_of_bicartSq (S := S) R
    (TopCat.bicartSq_range_toSSet_map_inclusion U V)
    ((quasiIso_chainComplexMap_smoothSingularSubcomplex_ι_iff_homOfLE I _ R).1 hUV)
    ((quasiIso_chainComplexMap_smoothSingularSubcomplex_ι_iff_homOfLE I
      (le_sup_left : U ≤ U ⊔ V) R).1 hU)
    ((quasiIso_chainComplexMap_smoothSingularSubcomplex_ι_iff_homOfLE I
      (le_sup_right : V ≤ U ⊔ V) R).1 hV)
  -- By the small-chain theorems, this is the conclusion.
  have hcov : ⋃ i, ![{x : ↥(U ⊔ V) | (x : M) ∈ U}, {x | (x : M) ∈ V}] i = Set.univ := by
    rw [Set.iUnion_vecCons_pair]
    exact Set.eq_univ_of_forall fun x ↦ Opens.mem_sup.1 x.property
  exact (quasiIso_chainComplexMap_ι_iff_homOfLE_inf_smallSingularSubcomplex R S _
    (IsOpen.vecCons (U.isOpen.preimage continuous_subtypeVal)
      (V.isOpen.preimage continuous_subtypeVal)) hcov).2 h₃

end MayerVietoris

/-! ### Small smooth singular simplices -/

section Subcomplex

open SSet.Subcomplex

variable (I) in
/-- The subcomplex of smooth singular simplices of `M` whose image lies in some member of the
family `S` of subsets of `M`. -/
def smallSmoothSingularSubcomplex {ι : Type*} (S : ι → Set M) :
    (TopCat.toSSet.obj (TopCat.of M)).Subcomplex :=
  smoothSingularSubcomplex I M ⊓ (TopCat.of M).smallSingularSubcomplex S

/-- The small smooth singular subcomplex is the intersection of the smooth singular subcomplex and
the small singular subcomplex. -/
theorem smallSmoothSingularSubcomplex_eq {ι : Type*} (S : ι → Set M) :
    smallSmoothSingularSubcomplex I S =
      smoothSingularSubcomplex I M ⊓ (TopCat.of M).smallSingularSubcomplex S := by
  rfl

variable (I) in
/-- Every small smooth singular simplex is a smooth singular simplex. -/
theorem smallSmoothSingularSubcomplex_le_smoothSingularSubcomplex {ι : Type*} (S : ι → Set M) :
    smallSmoothSingularSubcomplex I S ≤ smoothSingularSubcomplex I M :=
  inf_le_left

variable (I) in
/-- Every small smooth singular simplex is a small singular simplex. -/
theorem smallSmoothSingularSubcomplex_le_smallSingularSubcomplex {ι : Type*} (S : ι → Set M) :
    smallSmoothSingularSubcomplex I S ≤ (TopCat.of M).smallSingularSubcomplex S :=
  inf_le_right

/-- A singular simplex lies in `smallSmoothSingularSubcomplex I S` if and only if it is smooth
and its image is contained in some member of `S`. -/
@[simp]
theorem mem_smallSmoothSingularSubcomplex_iff {ι : Type*} (S : ι → Set M)
    {k : SimplexCategoryᵒᵖ} (σ : (TopCat.toSSet.obj (TopCat.of M)).obj k) :
    σ ∈ (smallSmoothSingularSubcomplex I S).obj k ↔
      ContMDiffOnSubset I ∞
        ((TopCat.of M).toSSetObjEquiv k σ ∘ fullSimplexEquivStdSimplex k.unop.len) ∧
      ∃ i, Set.range ((TopCat.of M).toSSetObjEquiv k σ) ⊆ S i := by
  simp only [smallSmoothSingularSubcomplex, Subfunctor.min_obj, Set.mem_inter_iff,
    mem_smoothSingularSubcomplex_iff, TopCat.mem_smallSingularSubcomplex_iff]

variable (I) in
/-- For an open subset `V` contained in a member `S i` of a family `S` of subsets of `M`, the map
from the smooth singular subcomplex of `V` into the small smooth singular subcomplex of `S`. -/
def toSmallSmoothSingularSubcomplex {ι : Type*} (S : ι → Set M) {V : Opens M} {i : ι}
    (h : (V : Set M) ⊆ S i) :
    (smoothSingularSubcomplex I V : SSet) ⟶ (smallSmoothSingularSubcomplex I S : SSet) :=
  SSet.Subcomplex.lift
    ((smoothSingularSubcomplex I V).ι ≫
      TopCat.toSSet.map (TopCat.ofHom (ContinuousMap.subtypeVal (V : Set M)))) (by
      rintro n _ ⟨σ, rfl⟩
      rw [mem_smallSmoothSingularSubcomplex_iff]
      refine ⟨(mem_smoothSingularSubcomplex_iff _).1
        (smoothSingularSubcomplex_le_preimage (contMDiff_subtypeVal (I := I)) n σ.property), ?_⟩
      rw [NatTrans.comp_app, ConcreteCategory.comp_apply, Subfunctor.ι_app, TypeCat.ofHom_apply,
        TauCeti.TopCat.toSSetObjEquiv_toSSet_map_app, ContinuousMap.coe_comp, Set.range_comp]
      exact ⟨i, (Set.image_subset_range _ _).trans (Subtype.range_coe.trans_subset h)⟩)

/-- Composing `toSmallSmoothSingularSubcomplex` with the inclusion into all singular simplices of
`M` recovers the inclusion of smooth simplices of `V` followed by the subspace map. -/
@[reassoc (attr := simp)]
theorem toSmallSmoothSingularSubcomplex_ι {ι : Type*} (S : ι → Set M) {V : Opens M} {i : ι}
    (h : (V : Set M) ⊆ S i) :
    toSmallSmoothSingularSubcomplex I S h ≫ (smallSmoothSingularSubcomplex I S).ι =
      (smoothSingularSubcomplex I V).ι ≫
        TopCat.toSSet.map (TopCat.ofHom (ContinuousMap.subtypeVal (V : Set M))) :=
  SSet.Subcomplex.lift_ι _ _

/-- Composing `toSmallSmoothSingularSubcomplex` with the inclusion into all smooth singular
simplices of `M` gives the map of smooth singular subcomplexes induced by `V ⊆ M`. -/
@[reassoc (attr := simp)]
theorem toSmallSmoothSingularSubcomplex_homOfLE_left {ι : Type*} (S : ι → Set M) {V : Opens M}
    {i : ι} (h : (V : Set M) ⊆ S i) :
    toSmallSmoothSingularSubcomplex I S h ≫
        homOfLE (smallSmoothSingularSubcomplex_le_smoothSingularSubcomplex I S) =
      smoothSingularSubcomplexMap (Subtype.val : V → M) (contMDiff_subtypeVal (I := I)) := by
  rw [← cancel_mono (smoothSingularSubcomplex I M).ι, Category.assoc, homOfLE_ι,
    toSmallSmoothSingularSubcomplex_ι, smoothSingularSubcomplexMap_subtypeVal_ι]

/-- Composing `toSmallSmoothSingularSubcomplex` with the inclusion into singular small simplices
intertwines the smooth-to-singular inclusions of `V` and of the small subcomplex. -/
@[reassoc (attr := simp)]
theorem toSmallSmoothSingularSubcomplex_homOfLE_right {ι : Type*} (S : ι → Set M) {V : Opens M}
    {i : ι} (h : (V : Set M) ⊆ S i) :
    toSmallSmoothSingularSubcomplex I S h ≫
        homOfLE (smallSmoothSingularSubcomplex_le_smallSingularSubcomplex I S) =
      (smoothSingularSubcomplex I V).ι ≫
        TopCat.toSmallSingularSubcomplex (X := TopCat.of M) S h := by
  rw [← cancel_mono ((TopCat.of M).smallSingularSubcomplex S).ι, Category.assoc, Category.assoc,
    homOfLE_ι, toSmallSmoothSingularSubcomplex_ι, TopCat.toSmallSingularSubcomplex_ι]

private lemma bicartSq_range_smoothSingularSubcomplex (U V : Opens M) :
    SSet.Subcomplex.BicartSq
      (SSet.Subcomplex.range ((smoothSingularSubcomplex I ↥(U ⊓ V)).ι ≫
        TopCat.toSSet.map (TopCat.ofHom (ContinuousMap.subtypeVal ((U ⊓ V : Opens M) : Set M)))))
      (SSet.Subcomplex.range ((smoothSingularSubcomplex I U).ι ≫
        TopCat.toSSet.map (TopCat.ofHom (ContinuousMap.subtypeVal (U : Set M)))))
      (SSet.Subcomplex.range ((smoothSingularSubcomplex I V).ι ≫
        TopCat.toSSet.map (TopCat.ofHom (ContinuousMap.subtypeVal (V : Set M)))))
      (smallSmoothSingularSubcomplex I ![(U : Set M), (V : Set M)]) := by
  refine ⟨?_, ?_⟩
  · ext n σ
    simp only [Subfunctor.max_obj, range_smoothSingularSubcomplex_ι_comp_subtypeVal,
      Subfunctor.min_obj, Set.mem_union, Set.mem_inter_iff, mem_smallSmoothSingularSubcomplex_iff,
      mem_smoothSingularSubcomplex_iff]
    rw [TopCat.mem_range_toSSet_subtypeVal_iff (X := TopCat.of M) (U : Set M),
      TopCat.mem_range_toSSet_subtypeVal_iff (X := TopCat.of M) (V : Set M)]
    simp only [Fin.exists_fin_two, Matrix.cons_val_zero, Matrix.cons_val_one]
    tauto
  · ext n σ
    simp only [Subfunctor.min_obj, range_smoothSingularSubcomplex_ι_comp_subtypeVal,
      Set.mem_inter_iff]
    rw [TopCat.mem_range_toSSet_subtypeVal_iff (X := TopCat.of M) (U : Set M),
      TopCat.mem_range_toSSet_subtypeVal_iff (X := TopCat.of M) (V : Set M),
      TopCat.mem_range_toSSet_subtypeVal_iff (X := TopCat.of M) ((U ⊓ V : Opens M) : Set M),
      Opens.coe_inf, Set.subset_inter_iff]
    tauto

variable (I) in
/-- **The smooth singular subcomplexes of two open sets form a pushout square.** For open sets `U`
and `V` of `M`, the smooth singular subcomplexes of `U ⊓ V`, `U`, and `V` form a pushout square
with the subcomplex of smooth singular simplices of `M` whose image lies in `U` or in `V`. -/
theorem isPushout_smoothSingularSubcomplex_inter_smallSmoothSingularSubcomplex (U V : Opens M) :
    IsPushout
      (smoothSingularSubcomplexMap (Opens.inclusion (inf_le_left : U ⊓ V ≤ U))
        (contMDiff_inclusion (I := I) _))
      (smoothSingularSubcomplexMap (Opens.inclusion (inf_le_right : U ⊓ V ≤ V))
        (contMDiff_inclusion (I := I) _))
      (toSmallSmoothSingularSubcomplex I ![(U : Set M), (V : Set M)] (i := 0)
        (Matrix.cons_val_zero (U : Set M) ![(V : Set M)]).superset)
      (toSmallSmoothSingularSubcomplex I ![(U : Set M), (V : Set M)] (i := 1)
        ((Matrix.cons_val_one (U : Set M) ![(V : Set M)]).trans
          (Matrix.cons_val_zero (V : Set M) ![])).superset) := by
  let gI := (smoothSingularSubcomplex I ↥(U ⊓ V)).ι ≫
    TopCat.toSSet.map (TopCat.ofHom (ContinuousMap.subtypeVal ((U ⊓ V : Opens M) : Set M)))
  let gU := (smoothSingularSubcomplex I U).ι ≫
    TopCat.toSSet.map (TopCat.ofHom (ContinuousMap.subtypeVal (U : Set M)))
  let gV := (smoothSingularSubcomplex I V).ι ≫
    TopCat.toSSet.map (TopCat.ofHom (ContinuousMap.subtypeVal (V : Set M)))
  refine (bicartSq_range_smoothSingularSubcomplex (I := I) U V).isPushout.of_iso'
    (asIso (SSet.Subcomplex.toRange gI)) (asIso (SSet.Subcomplex.toRange gU))
    (asIso (SSet.Subcomplex.toRange gV)) (Iso.refl _) ?_ ?_ ?_ ?_
  · rw [← cancel_mono (SSet.Subcomplex.range gU).ι]
    simp only [asIso_hom, Category.assoc, homOfLE_ι, SSet.Subcomplex.toRange_ι, gI, gU,
      smoothSingularSubcomplexMap_inclusion_ι_assoc, ← Functor.map_comp, ← TopCat.ofHom_comp]
    rw [ContinuousMap.subtypeVal_comp_inclusion]
  · rw [← cancel_mono (SSet.Subcomplex.range gV).ι]
    simp only [asIso_hom, Category.assoc, homOfLE_ι, SSet.Subcomplex.toRange_ι, gI, gV,
      smoothSingularSubcomplexMap_inclusion_ι_assoc, ← Functor.map_comp, ← TopCat.ofHom_comp]
    rw [ContinuousMap.subtypeVal_comp_inclusion]
  · rw [← cancel_mono (smallSmoothSingularSubcomplex I ![(U : Set M), (V : Set M)]).ι]
    simp [gU]
  · rw [← cancel_mono (smallSmoothSingularSubcomplex I ![(U : Set M), (V : Set M)]).ι]
    simp [gV]

/-- The inclusions of `U ⊓ V` into `U` and `V` and of `U` and `V` into `M` form a commutative
square of smooth singular subcomplexes. -/
theorem commSq_smoothSingularSubcomplexMap_inter (I : ModelWithCorners ℝ E H) (U V : Opens M) :
    CommSq
      (smoothSingularSubcomplexMap (Opens.inclusion (inf_le_left : U ⊓ V ≤ U))
        (contMDiff_inclusion (I := I) _))
      (smoothSingularSubcomplexMap (Opens.inclusion (inf_le_right : U ⊓ V ≤ V))
        (contMDiff_inclusion (I := I) _))
      (smoothSingularSubcomplexMap (Subtype.val : U → M) (contMDiff_subtypeVal (I := I)))
      (smoothSingularSubcomplexMap (Subtype.val : V → M) (contMDiff_subtypeVal (I := I))) where
  w := by
    rw [← cancel_mono (smoothSingularSubcomplex I M).ι]
    simp only [Category.assoc, smoothSingularSubcomplexMap_subtypeVal_ι,
      smoothSingularSubcomplexMap_inclusion_ι_assoc, ← Functor.map_comp, ← TopCat.ofHom_comp]
    rw [ContinuousMap.subtypeVal_comp_inclusion, ContinuousMap.subtypeVal_comp_inclusion]

end Subcomplex

/-! ### The Mayer–Vietoris sequence of an open cover by two sets -/

section SmoothMayerVietoris

open SSet.Subcomplex

variable (I) {C : Type v} [Category.{w} C] [HasCoproducts.{u} C] [Abelian C] (R : C)
  {U V : Opens M}

private def smoothCoverHomologyIso (hUV : U ⊔ V = ⊤) (n : ℕ) :
    (smallSmoothSingularSubcomplex I ![(U : Set M), (V : Set M)] : SSet).homology R n ≅
      (smoothSingularSubcomplex I M : SSet).homology R n :=
  subcomplexSmallHomologyIso R (smoothSingularSubcomplex I M) ![(U : Set M), (V : Set M)]
    (U.isOpen.vecCons V.isOpen)
    (by rw [Set.iUnion_vecCons_pair, ← Opens.coe_sup, hUV, Opens.coe_top]) n

@[simp]
private lemma smoothCoverHomologyIso_hom (hUV : U ⊔ V = ⊤) (n : ℕ) :
    (smoothCoverHomologyIso I R hUV n).hom =
      SSet.homologyMap
        (homOfLE (smallSmoothSingularSubcomplex_le_smoothSingularSubcomplex I
          ![(U : Set M), (V : Set M)])) R n :=
  subcomplexSmallHomologyIso_hom R (smoothSingularSubcomplex I M) _ _ _ n

/-- The Mayer–Vietoris connecting morphism `Hₙ^∞(M) ⟶ Hₘ^∞(U ⊓ V)`, `m + 1 = n`, in smooth
singular homology for an open cover `U ⊔ V = ⊤` of `M`. -/
def smoothMayerVietorisδ (hUV : U ⊔ V = ⊤) (n m : ℕ) (h : m + 1 = n := by lia) :
    (smoothSingularSubcomplex I M : SSet).homology R n ⟶
      (smoothSingularSubcomplex I ↥(U ⊓ V) : SSet).homology R m :=
  (smoothCoverHomologyIso I R hUV n).inv ≫
    SSet.mayerVietorisδ R
      (isPushout_smoothSingularSubcomplex_inter_smallSmoothSingularSubcomplex I U V) n m h

/-- On the homology of the smooth simplices subordinate to the cover, `smoothMayerVietorisδ`
restricts to the connecting morphism of the pushout square of smooth singular subcomplexes. -/
@[reassoc (attr := simp)]
theorem homologyMap_homOfLE_comp_smoothMayerVietorisδ (hUV : U ⊔ V = ⊤) (n m : ℕ)
    (h : m + 1 = n := by lia) :
    SSet.homologyMap
        (homOfLE (smallSmoothSingularSubcomplex_le_smoothSingularSubcomplex I
          ![(U : Set M), (V : Set M)])) R n ≫
      smoothMayerVietorisδ I R hUV n m h =
      SSet.mayerVietorisδ R
        (isPushout_smoothSingularSubcomplex_inter_smallSmoothSingularSubcomplex I U V) n m h := by
  rw [smoothMayerVietorisδ, ← smoothCoverHomologyIso_hom I R hUV n, Iso.hom_inv_id_assoc]

/-- The inclusion of smooth singular chains into singular chains intertwines the smooth and
singular Mayer–Vietoris connecting morphisms. -/
@[reassoc]
theorem smoothMayerVietorisδ_ι (hUV : U ⊔ V = ⊤) (n m : ℕ) (h : m + 1 = n := by lia) :
    smoothMayerVietorisδ I R hUV n m h ≫
        SSet.homologyMap (smoothSingularSubcomplex I ↥(U ⊓ V)).ι R m =
      SSet.homologyMap (smoothSingularSubcomplex I M).ι R n ≫
        TopCat.mayerVietorisδ R U.isOpen V.isOpen
          (by rw [← Opens.coe_sup, hUV, Opens.coe_top]) n m h := by
  have hcomm :
      SSet.homologyMap
          (homOfLE (smallSmoothSingularSubcomplex_le_smoothSingularSubcomplex I
            ![(U : Set M), (V : Set M)])) R n ≫
        SSet.homologyMap (smoothSingularSubcomplex I M).ι R n =
      SSet.homologyMap
          (homOfLE (smallSmoothSingularSubcomplex_le_smallSingularSubcomplex I
            ![(U : Set M), (V : Set M)])) R n ≫
        SSet.homologyMap ((TopCat.of M).smallSingularSubcomplex ![(U : Set M), (V : Set M)]).ι
          R n := by
    simp [← SSet.homologyMap_comp]
  rw [← cancel_epi (smoothCoverHomologyIso I R hUV n).hom]
  simp only [smoothCoverHomologyIso_hom, homologyMap_homOfLE_comp_smoothMayerVietorisδ_assoc,
    reassoc_of% hcomm]
  rw [TopCat.homologyMap_ι_comp_mayerVietorisδ _ _ _ _ n m h]
  exact SSet.mayerVietorisδ_naturality R _ _ _ _
    (isPushout_smoothSingularSubcomplex_inter_smallSmoothSingularSubcomplex I U V)
    (TopCat.isPushout_toSSet_inter_smallSingularSubcomplex (X := TopCat.of M)
      (U : Set M) (V : Set M))
    (smoothSingularSubcomplexMap_inclusion_ι (inf_le_left : U ⊓ V ≤ U))
    (smoothSingularSubcomplexMap_inclusion_ι (inf_le_right : U ⊓ V ≤ V))
    (toSmallSmoothSingularSubcomplex_homOfLE_right _ _)
    (toSmallSmoothSingularSubcomplex_homOfLE_right _ _) n m h

private lemma smoothMayerVietorisFromBiprod_comp_homologyMap
    (hU : (U : Set M) ⊆ ![(U : Set M), (V : Set M)] 0)
    (hV : (V : Set M) ⊆ ![(U : Set M), (V : Set M)] 1) (n : ℕ) :
    SSet.mayerVietorisFromBiprod R
        (toSmallSmoothSingularSubcomplex I ![(U : Set M), (V : Set M)] hU)
        (toSmallSmoothSingularSubcomplex I ![(U : Set M), (V : Set M)] hV) n ≫
      SSet.homologyMap
        (homOfLE (smallSmoothSingularSubcomplex_le_smoothSingularSubcomplex I
          ![(U : Set M), (V : Set M)])) R n =
    SSet.mayerVietorisFromBiprod R
      (smoothSingularSubcomplexMap (Subtype.val : U → M) (contMDiff_subtypeVal (I := I)))
      (smoothSingularSubcomplexMap (Subtype.val : V → M) (contMDiff_subtypeVal (I := I))) n := by
  ext <;> simp [← SSet.homologyMap_comp]

/-- Composing `smoothMayerVietorisδ` with the inclusion difference into `Hₘ^∞(U) ⊞ Hₘ^∞(V)` is
zero. -/
@[reassoc (attr := simp)]
theorem smoothMayerVietorisδ_toBiprod (hUV : U ⊔ V = ⊤) (n m : ℕ) (h : m + 1 = n := by lia) :
    smoothMayerVietorisδ I R hUV n m h ≫
      SSet.mayerVietorisToBiprod R
        (smoothSingularSubcomplexMap (Opens.inclusion (inf_le_left : U ⊓ V ≤ U))
          (contMDiff_inclusion (I := I) _))
        (smoothSingularSubcomplexMap (Opens.inclusion (inf_le_right : U ⊓ V ≤ V))
          (contMDiff_inclusion (I := I) _)) m = 0 := by
  simp [smoothMayerVietorisδ]

/-- Composing the sum of inclusions from `Hₙ^∞(U) ⊞ Hₙ^∞(V)` with `smoothMayerVietorisδ` is
zero. -/
@[reassoc (attr := simp)]
theorem smoothMayerVietorisFromBiprod_δ (hUV : U ⊔ V = ⊤) (n m : ℕ) (h : m + 1 = n := by lia) :
    SSet.mayerVietorisFromBiprod R
        (smoothSingularSubcomplexMap (Subtype.val : U → M) (contMDiff_subtypeVal (I := I)))
        (smoothSingularSubcomplexMap (Subtype.val : V → M) (contMDiff_subtypeVal (I := I))) n ≫
      smoothMayerVietorisδ I R hUV n m h = 0 := by
  rw [← smoothMayerVietorisFromBiprod_comp_homologyMap I R
      (by simp) (by simp), Category.assoc,
    homologyMap_homOfLE_comp_smoothMayerVietorisδ I R hUV n m h,
    SSet.mayerVietorisFromBiprod_δ R _ n m h]

/-- **Exactness of the smooth Mayer–Vietoris sequence at `Hₘ^∞(U ⊓ V)`.** -/
theorem smoothMayerVietoris_exact₁ (hUV : U ⊔ V = ⊤) (n m : ℕ) (h : m + 1 = n := by lia) :
    (ShortComplex.mk _ _ (smoothMayerVietorisδ_toBiprod I R hUV n m h)).Exact := by
  refine (ShortComplex.exact_iff_of_iso ?_).1 (SSet.mayerVietoris_exact₁ R
    (isPushout_smoothSingularSubcomplex_inter_smallSmoothSingularSubcomplex I U V) n m h)
  refine ShortComplex.isoMk (smoothCoverHomologyIso I R hUV n) (Iso.refl _) (Iso.refl _) ?_
    (by simp)
  simp

/-- **Exactness of the smooth Mayer–Vietoris sequence at `Hₙ^∞(U) ⊞ Hₙ^∞(V)`.** -/
theorem smoothMayerVietoris_exact₂ (hUV : U ⊔ V = ⊤) (n : ℕ) :
    (ShortComplex.mk _ _ (SSet.mayerVietorisToBiprod_fromBiprod R
      (commSq_smoothSingularSubcomplexMap_inter I U V) n)).Exact := by
  refine (ShortComplex.exact_iff_of_iso ?_).1 (SSet.mayerVietoris_exact₂ R
    (isPushout_smoothSingularSubcomplex_inter_smallSmoothSingularSubcomplex I U V) n)
  refine ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (smoothCoverHomologyIso I R hUV n)
    (by simp) ?_
  simp [smoothMayerVietorisFromBiprod_comp_homologyMap]

/-- **Exactness of the smooth Mayer–Vietoris sequence at `Hₙ^∞(M)`.** -/
theorem smoothMayerVietoris_exact₃ (hUV : U ⊔ V = ⊤) (n m : ℕ) (h : m + 1 = n := by lia) :
    (ShortComplex.mk _ _ (smoothMayerVietorisFromBiprod_δ I R hUV n m h)).Exact := by
  refine (ShortComplex.exact_iff_of_iso ?_).1 (SSet.mayerVietoris_exact₃ R
    (isPushout_smoothSingularSubcomplex_inter_smallSmoothSingularSubcomplex I U V) n m h)
  refine ShortComplex.isoMk (Iso.refl _) (smoothCoverHomologyIso I R hUV n) (Iso.refl _) ?_ ?_
  · simp [smoothMayerVietorisFromBiprod_comp_homologyMap]
  · simp

end SmoothMayerVietoris

/-! ### The binary-cover step of smoothing -/

section QuasiIso

open SSet.Subcomplex

variable {C : Type v} [Category.{w} C] [HasCoproducts.{u} C] [Abelian C] (R : C)

/-- **The binary-cover step of the smoothing theorem.** Let `U` and `V` be open subsets of `M`
with `U ⊔ V = ⊤`. If the inclusion of smooth singular chains into singular chains with
coefficients in `R` is a quasi-isomorphism on `U`, on `V`, and on `U ⊓ V`, then it is a
quasi-isomorphism on `M`. -/
theorem quasiIso_chainComplexMap_smoothSingularSubcomplex_ι_of_sup_eq_top
    {U V : Opens M} (hUV : U ⊔ V = ⊤)
    (hU : QuasiIso (SSet.chainComplexMap (smoothSingularSubcomplex I U).ι R))
    (hV : QuasiIso (SSet.chainComplexMap (smoothSingularSubcomplex I V).ι R))
    (hI : QuasiIso (SSet.chainComplexMap (smoothSingularSubcomplex I ↥(U ⊓ V)).ι R)) :
    QuasiIso (SSet.chainComplexMap (smoothSingularSubcomplex I M).ι R) := by
  let sqS := isPushout_smoothSingularSubcomplex_inter_smallSmoothSingularSubcomplex I U V
  let sqT := TopCat.isPushout_toSSet_inter_smallSingularSubcomplex (X := TopCat.of M)
    (U : Set M) (V : Set M)
  let ψ := SSet.mayerVietorisShortComplexMap R sqS sqT
    (smoothSingularSubcomplexMap_inclusion_ι (inf_le_left : U ⊓ V ≤ U))
    (smoothSingularSubcomplexMap_inclusion_ι (inf_le_right : U ⊓ V ≤ V))
    (toSmallSmoothSingularSubcomplex_homOfLE_right _ _)
    (toSmallSmoothSingularSubcomplex_homOfLE_right _ _)
  have h₃ : QuasiIso (SSet.chainComplexMap
      (homOfLE (smallSmoothSingularSubcomplex_le_smallSingularSubcomplex I
        ![(U : Set M), (V : Set M)])) R) := by
    have hτ₃ := HomologicalComplex.HomologySequence.quasiIso_τ₃ ψ
      (SSet.shortExact_mayerVietorisShortComplex R sqS)
      (SSet.shortExact_mayerVietorisShortComplex R sqT)
      (by dsimp only [ψ]; rwa [SSet.mayerVietorisShortComplexMap_τ₁])
      (by dsimp only [ψ]; rw [SSet.mayerVietorisShortComplexMap_τ₂]
          exact HomologicalComplex.quasiIso_biprod_map _ _)
    dsimp only [ψ] at hτ₃
    rwa [SSet.mayerVietorisShortComplexMap_τ₃] at hτ₃
  have hcov : ⋃ i, ![(U : Set M), (V : Set M)] i = Set.univ := by
    rw [Set.iUnion_vecCons_pair, ← Opens.coe_sup, hUV, Opens.coe_top]
  let jL : (smallSmoothSingularSubcomplex I ![(U : Set M), (V : Set M)] : SSet) ⟶
      (smoothSingularSubcomplex I M : SSet) :=
    homOfLE (smallSmoothSingularSubcomplex_le_smoothSingularSubcomplex I _)
  have : QuasiIso (SSet.chainComplexMap jL R) :=
    quasiIso_chainComplexMap_homOfLE_inf_smallSingularSubcomplex R
      (smoothSingularSubcomplex I M) ![(U : Set M), (V : Set M)] (U.isOpen.vecCons V.isOpen) hcov
  have : QuasiIso (SSet.chainComplexMap
      ((TopCat.of M).smallSingularSubcomplex ![(U : Set M), (V : Set M)]).ι R) :=
    quasiIso_chainComplexMap_smallSingularSubcomplex_ι (X := TopCat.of M) R
      ![(U : Set M), (V : Set M)] (U.isOpen.vecCons V.isOpen) hcov
  have : QuasiIso (SSet.chainComplexMap jL R ≫
      SSet.chainComplexMap (smoothSingularSubcomplex I M).ι R) := by
    rw [← Functor.map_comp, homOfLE_ι,
      ← homOfLE_ι (smallSmoothSingularSubcomplex_le_smallSingularSubcomplex I _), Functor.map_comp]
    infer_instance
  exact quasiIso_of_comp_left (SSet.chainComplexMap jL R) _

end QuasiIso

end TauCeti
