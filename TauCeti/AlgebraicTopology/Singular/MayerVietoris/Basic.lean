/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicTopology.SimplicialSet.SubcomplexColimits
public import TauCeti.AlgebraicTopology.SimplicialSet.Homology.MayerVietoris
public import TauCeti.AlgebraicTopology.Singular.Reduced
public import TauCeti.AlgebraicTopology.Singular.Subspace

public import TauCeti.AlgebraicTopology.Singular.Subdivision.Small.Equiv
public import TauCeti.Data.Set.Lattice
public import TauCeti.Topology.Category.TopCat.Subspace
public import TauCeti.Topology.Sets.FinTwo

/-!
# The Mayer–Vietoris sequence in singular homology

Let `U` and `V` be open subsets of a topological space `X` with `U ∪ V = X`, and let `R` be an
object of an abelian category with coproducts. This file constructs the Mayer–Vietoris long exact
sequence of singular homology with coefficients in `R`,
`⋯ ⟶ Hₙ(U ∩ V) ⟶ Hₙ(U) ⊞ Hₙ(V) ⟶ Hₙ(X) ⟶ Hₙ₋₁(U ∩ V) ⟶ ⋯`,
whose first map is `(i_U, -i_V)` and whose second map is `j_U + j_V`, the `i` and `j` being the
maps induced by the inclusions. The connecting morphism is natural in maps of covered spaces.

The construction is the one of Hatcher. For any two subsets `U` and `V` of `X`, the singular
simplicial sets of `U ∩ V`, `U` and `V` form a pushout square with the subcomplex of singular
simplices of `X` lying in `U` or in `V` (`TopCat.isPushout_toSSet_inter_smallSingularSubcomplex`),
so the Mayer–Vietoris sequence of simplicial sets applies to it. When `U` and `V` are open and
cover `X`, the small-chain theorem (`TauCeti.smallSingularHomologyIso`), which is also the core
of the proof of excision, identifies the homology of that subcomplex with the singular homology
of `X`.

## Main definitions and results

* `TopCat.bicartSq_range_toSSet_subtypeVal`, `TopCat.bicartSq_range_toSSet_map_inclusion`: the
  singular simplices lying in `U ∩ V`, in `U`, in `V`, and in `U` or in `V` form a bicartesian
  square of subcomplexes, for subsets and for open sets.
* `TopCat.isPushout_toSSet_inter_smallSingularSubcomplex`: the pushout square of singular
  simplicial sets of an intersection.
* `TopCat.mayerVietorisδ`: the Mayer–Vietoris connecting morphism `Hₙ(X) ⟶ Hₘ(U ∩ V)`,
  `m + 1 = n`, characterized by `TopCat.homologyMap_ι_comp_mayerVietorisδ`. The other two maps
  of the sequence are `SSet.mayerVietorisToBiprod` and `SSet.mayerVietorisFromBiprod` applied to
  the maps of singular simplicial sets induced by the inclusions.
* `TopCat.mayerVietoris_exact₁`, `TopCat.mayerVietoris_exact₂`, `TopCat.mayerVietoris_exact₃`:
  exactness at `Hₘ(U ∩ V)`, at `Hₙ(U) ⊞ Hₙ(V)` and at `Hₙ(X)`.
* `TopCat.epi_mayerVietorisFromBiprod_zero`: surjectivity at the degree-zero endpoint.
* `TopCat.isIso_mayerVietorisToBiprod_of_isZero`: when `Hₙ₊₁(X)` and `Hₙ(X)` vanish,
  `Hₙ(U ∩ V) ≅ Hₙ(U) ⊞ Hₙ(V)`.
* `TopCat.isIso_mayerVietorisFromBiprod_of_isZero`: when `Hₙ(U ∩ V)` and `Hₙ₋₁(U ∩ V)` vanish,
  `Hₙ(U) ⊞ Hₙ(V) ≅ Hₙ(X)`.
* `TopCat.isIso_biprodDesc_singularHomologyFunctor_map_of_disjoint`: for a cover by two disjoint
  open sets, `Hₙ(U) ⊞ Hₙ(V) ≅ Hₙ(X)`.
* `TopCat.mayerVietorisδ_naturality`: naturality of the connecting morphism.

## References

* A. Hatcher, *Algebraic Topology*, Section 2.2, the Mayer–Vietoris sequences.
-/

public section

noncomputable section

open CategoryTheory Limits Topology

universe w v u

namespace TopCat

variable {X : TopCat.{w}}

variable (U V : Set X)

/-- For subsets `U` and `V` of `X`, the singular simplices of `X` lying in `U ∩ V`, in `U`, in `V`,
and in `U` or in `V` form a bicartesian square of subcomplexes. -/
theorem bicartSq_range_toSSet_subtypeVal :
    SSet.Subcomplex.BicartSq
      (SSet.Subcomplex.range (toSSet.map (ofHom (ContinuousMap.subtypeVal (U ∩ V)))))
      (SSet.Subcomplex.range (toSSet.map (ofHom (ContinuousMap.subtypeVal U))))
      (SSet.Subcomplex.range (toSSet.map (ofHom (ContinuousMap.subtypeVal V))))
      (X.smallSingularSubcomplex ![U, V]) where
  sup_eq := by
    ext n σ
    simp only [Subfunctor.max_obj, Set.mem_union, mem_range_toSSet_subtypeVal_iff,
      mem_smallSingularSubcomplex_iff, Fin.exists_fin_two, Matrix.cons_val_zero,
      Matrix.cons_val_one]
  inf_eq := by
    ext n σ
    simp only [Subfunctor.min_obj, Set.mem_inter_iff, mem_range_toSSet_subtypeVal_iff]
    exact Set.subset_inter_iff.symm

/-- For open sets `U` and `V` of a space `M`, the singular simplices of `U ∪ V` lying in `U ∩ V`, in
`U`, in `V`, and in `U` or in `V` form a bicartesian square of subcomplexes. -/
theorem bicartSq_range_toSSet_map_inclusion {M : Type*} [TopologicalSpace M]
    (U V : TopologicalSpace.Opens M) :
    SSet.Subcomplex.BicartSq
      (SSet.Subcomplex.range (toSSet.map (ofHom
        ⟨TopologicalSpace.Opens.inclusion (inf_le_left.trans le_sup_left : U ⊓ V ≤ U ⊔ V),
          continuous_inclusion (inf_le_left.trans le_sup_left : U ⊓ V ≤ U ⊔ V)⟩)))
      (SSet.Subcomplex.range (toSSet.map (ofHom
        ⟨TopologicalSpace.Opens.inclusion (le_sup_left : U ≤ U ⊔ V),
          continuous_inclusion (le_sup_left : U ≤ U ⊔ V)⟩)))
      (SSet.Subcomplex.range (toSSet.map (ofHom
        ⟨TopologicalSpace.Opens.inclusion (le_sup_right : V ≤ U ⊔ V),
          continuous_inclusion (le_sup_right : V ≤ U ⊔ V)⟩)))
      ((of ↥(U ⊔ V)).smallSingularSubcomplex ![{x | (x : M) ∈ U}, {x | (x : M) ∈ V}]) := by
  convert bicartSq_range_toSSet_subtypeVal (X := of ↥(U ⊔ V)) {x | (x : M) ∈ U}
    {x | (x : M) ∈ V} using 1 <;>
    ext n σ <;>
    rw [mem_range_toSSet_map_inclusion_iff, mem_range_toSSet_subtypeVal_iff]
  -- The points of `U ⊔ V` lying in `U ⊓ V` are those lying in `U` and in `V`.
  rfl

/-- **The singular simplicial sets of an intersection form a pushout square.** For subsets `U` and
`V` of `X`, the singular simplicial sets of `U ∩ V`, `U` and `V` form a pushout square with the
subcomplex of singular simplices of `X` whose image lies in `U` or in `V`. -/
theorem isPushout_toSSet_inter_smallSingularSubcomplex :
    IsPushout (toSSet.map (ofHom (ContinuousMap.inclusion (Set.inter_subset_left (t := V)))))
      (toSSet.map (ofHom (ContinuousMap.inclusion (Set.inter_subset_right (s := U)))))
      (toSmallSingularSubcomplex ![U, V] (Matrix.cons_val_zero U ![V]).superset)
      (toSmallSingularSubcomplex ![U, V]
        ((Matrix.cons_val_one U ![V]).trans (Matrix.cons_val_zero V ![])).superset) := by
  let fI := toSSet.map (ofHom (ContinuousMap.subtypeVal (U ∩ V)))
  let fU := toSSet.map (ofHom (ContinuousMap.subtypeVal U))
  let fV := toSSet.map (ofHom (ContinuousMap.subtypeVal V))
  let A := SSet.Subcomplex.range fI
  let B := SSet.Subcomplex.range fU
  let C := SSet.Subcomplex.range fV
  let D := X.smallSingularSubcomplex ![U, V]
  have sq : SSet.Subcomplex.BicartSq A B C D := bicartSq_range_toSSet_subtypeVal U V
  have hi : Mono fI := Functor.map_mono _ _
  have hu : Mono fU := Functor.map_mono _ _
  have hv : Mono fV := Functor.map_mono _ _
  refine sq.isPushout.of_iso'
    (asIso (SSet.Subcomplex.toRange fI))
    (asIso (SSet.Subcomplex.toRange fU))
    (asIso (SSet.Subcomplex.toRange fV)) (Iso.refl _) ?_ ?_ ?_ ?_
  · rw [← cancel_mono B.ι]
    -- `toRange` followed by the range inclusion is the original singular map.
    change fI = toSSet.map (ofHom (ContinuousMap.inclusion (Set.inter_subset_left (t := V)))) ≫ fU
    rw [← Functor.map_comp]
    rfl
  · rw [← cancel_mono C.ι]
    -- `toRange` followed by the range inclusion is the original singular map.
    change fI = toSSet.map (ofHom (ContinuousMap.inclusion (Set.inter_subset_right (s := U)))) ≫ fV
    rw [← Functor.map_comp]
    rfl
  · rw [← cancel_mono D.ι]
    -- The range isomorphism reduces this side to the inclusion into `X.toSSet`.
    change fU = toSmallSingularSubcomplex ![U, V]
      (Matrix.cons_val_zero U ![V]).superset ≫ D.ι
    exact (toSmallSingularSubcomplex_ι _ _).symm
  · rw [← cancel_mono D.ι]
    -- The range isomorphism reduces this side to the inclusion into `X.toSSet`.
    change fV = toSmallSingularSubcomplex ![U, V]
      ((Matrix.cons_val_one U ![V]).trans (Matrix.cons_val_zero V ![])).superset ≫ D.ι
    exact (toSmallSingularSubcomplex_ι _ _).symm

/-- Restricting `f` to a set `A` lying in a member of the family `S` and then passing to the small
singular subcomplex of `T` agrees with passing to the small singular subcomplex of `S` first and
then mapping by `f`. -/
@[reassoc]
lemma toSmallSingularSubcomplex_comp_smallSingularSubcomplexMap {Y : TopCat.{w}} {ι κ : Type*}
    (S : ι → Set X) (T : κ → Set Y) (f : X ⟶ Y) (r : ι → κ)
    (hf : ∀ i, Set.MapsTo f (S i) (T (r i))) {A : Set X} {B : Set Y} {i : ι} {j : κ}
    (hA : A ⊆ S i) (hB : B ⊆ T j) (hAB : Set.MapsTo f A B) :
    toSmallSingularSubcomplex S hA ≫ X.smallSingularSubcomplexMap S T f r hf =
      toSSet.map (ofHom ⟨hAB.restrict, f.hom.continuous.restrict hAB⟩) ≫
        toSmallSingularSubcomplex T hB := by
  rw [← cancel_mono (Y.smallSingularSubcomplex T).ι, Category.assoc, Category.assoc,
    smallSingularSubcomplexMap_ι, toSmallSingularSubcomplex_ι_assoc, toSmallSingularSubcomplex_ι,
    ← Functor.map_comp, ← Functor.map_comp, ofHom_subtypeVal_comp f hAB]

/-! ### The Mayer–Vietoris sequence of an open cover by two sets -/

variable {C : Type u} [Category.{v} C] [HasCoproducts.{w} C] [Abelian C] (R : C)
  {U V} (hU : IsOpen U) (hV : IsOpen V) (hUV : U ∪ V = Set.univ)

/-- The Mayer–Vietoris connecting morphism `Hₙ(X) ⟶ Hₘ(U ∩ V)`, where `m + 1 = n`, for an open
cover of `X` by `U` and `V`. It is the connecting morphism of the Mayer–Vietoris sequence of the
singular simplicial sets of `U ∩ V`, `U` and `V`, precomposed with the inverse of the small-chain
isomorphism. -/
def mayerVietorisδ (n m : ℕ) (h : m + 1 = n := by lia) :
    (toSSet.obj X).homology R n ⟶ (toSSet.obj (of ↥(U ∩ V))).homology R m :=
  (TauCeti.smallSingularHomologyIso R ![U, V] (hU.vecCons hV)
    ((U.iUnion_vecCons_pair V).trans hUV) n).inv ≫
    SSet.mayerVietorisδ R (isPushout_toSSet_inter_smallSingularSubcomplex U V) n m h

/-- The Mayer–Vietoris connecting morphism of the open cover restricts, on the homology of the
singular simplices lying in `U` or in `V`, to that of the pushout square of singular simplicial
sets. Since that homology maps isomorphically onto `Hₙ(X)`, this characterizes it. -/
@[reassoc (attr := simp)]
lemma homologyMap_ι_comp_mayerVietorisδ (n m : ℕ) (h : m + 1 = n := by lia) :
    SSet.homologyMap (X.smallSingularSubcomplex ![U, V]).ι R n ≫ mayerVietorisδ R hU hV hUV n m h =
      SSet.mayerVietorisδ R (isPushout_toSSet_inter_smallSingularSubcomplex U V) n m h := by
  rw [mayerVietorisδ, SSet.homologyMap, ← TauCeti.smallSingularHomologyIso_hom R ![U, V]
    (hU.vecCons hV) ((U.iUnion_vecCons_pair V).trans hUV),
    Iso.hom_inv_id_assoc]

private lemma mayerVietorisFromBiprod_comp_homologyMap_ι (n : ℕ) :
    SSet.mayerVietorisFromBiprod R
        (toSmallSingularSubcomplex ![U, V] (Matrix.cons_val_zero U ![V]).superset)
        (toSmallSingularSubcomplex ![U, V]
          ((Matrix.cons_val_one U ![V]).trans (Matrix.cons_val_zero V ![])).superset) n ≫
      SSet.homologyMap (X.smallSingularSubcomplex ![U, V]).ι R n =
    SSet.mayerVietorisFromBiprod R (toSSet.map (ofHom (ContinuousMap.subtypeVal U)))
      (toSSet.map (ofHom (ContinuousMap.subtypeVal V))) n := by
  ext <;> simp [← SSet.homologyMap_comp]

@[reassoc (attr := simp)]
lemma mayerVietorisδ_toBiprod (n m : ℕ) (h : m + 1 = n := by lia) :
    mayerVietorisδ R hU hV hUV n m h ≫
      SSet.mayerVietorisToBiprod R
        (toSSet.map (ofHom (ContinuousMap.inclusion (Set.inter_subset_left (t := V)))))
        (toSSet.map (ofHom (ContinuousMap.inclusion (Set.inter_subset_right (s := U))))) m = 0 := by
  simp [mayerVietorisδ]

@[reassoc (attr := simp)]
lemma mayerVietorisFromBiprod_δ (n m : ℕ) (h : m + 1 = n := by lia) :
    SSet.mayerVietorisFromBiprod R (toSSet.map (ofHom (ContinuousMap.subtypeVal U)))
        (toSSet.map (ofHom (ContinuousMap.subtypeVal V))) n ≫
      mayerVietorisδ R hU hV hUV n m h = 0 := by
  rw [← mayerVietorisFromBiprod_comp_homologyMap_ι, Category.assoc,
    homologyMap_ι_comp_mayerVietorisδ R hU hV hUV n m h, SSet.mayerVietorisFromBiprod_δ R _ n m h]

/-- **Exactness of the Mayer–Vietoris sequence at `Hₘ(U ∩ V)`.** -/
lemma mayerVietoris_exact₁ (n m : ℕ) (h : m + 1 = n := by lia) :
    (ShortComplex.mk _ _ (mayerVietorisδ_toBiprod R hU hV hUV n m h)).Exact := by
  refine (ShortComplex.exact_iff_of_iso ?_).1
    (SSet.mayerVietoris_exact₁ R (isPushout_toSSet_inter_smallSingularSubcomplex U V) n m h)
  refine ShortComplex.isoMk
    (TauCeti.smallSingularHomologyIso R _ (hU.vecCons hV)
      ((U.iUnion_vecCons_pair V).trans hUV) n)
    (Iso.refl _) (Iso.refl _) ?_ (by simp only [Iso.refl_hom, Category.id_comp, Category.comp_id])
  dsimp only
  rw [Iso.refl_hom, Category.comp_id, TauCeti.smallSingularHomologyIso_hom,
    homologyMap_ι_comp_mayerVietorisδ R hU hV hUV n m h]

include hU hV hUV in
/-- **Exactness of the Mayer–Vietoris sequence at `Hₙ(U) ⊞ Hₙ(V)`.** -/
lemma mayerVietoris_exact₂ (n : ℕ) :
    (ShortComplex.mk _ _
      (SSet.mayerVietorisToBiprod_fromBiprod R ((commSq_ofHom_inter U V).map toSSet) n)).Exact := by
  refine (ShortComplex.exact_iff_of_iso ?_).1
    (SSet.mayerVietoris_exact₂ R (isPushout_toSSet_inter_smallSingularSubcomplex U V) n)
  refine ShortComplex.isoMk (Iso.refl _) (Iso.refl _)
    (TauCeti.smallSingularHomologyIso R _ (hU.vecCons hV)
      ((U.iUnion_vecCons_pair V).trans hUV) n)
    (by simp only [Iso.refl_hom, Category.id_comp, Category.comp_id]) ?_
  dsimp only
  rw [TauCeti.smallSingularHomologyIso_hom, Iso.refl_hom, Category.id_comp,
    mayerVietorisFromBiprod_comp_homologyMap_ι]

/-- **Exactness of the Mayer–Vietoris sequence at `Hₙ(X)`.** -/
lemma mayerVietoris_exact₃ (n m : ℕ) (h : m + 1 = n := by lia) :
    (ShortComplex.mk _ _ (mayerVietorisFromBiprod_δ R hU hV hUV n m h)).Exact := by
  refine (ShortComplex.exact_iff_of_iso ?_).1
    (SSet.mayerVietoris_exact₃ R (isPushout_toSSet_inter_smallSingularSubcomplex U V) n m h)
  refine ShortComplex.isoMk (Iso.refl _)
    (TauCeti.smallSingularHomologyIso R _ (hU.vecCons hV)
      ((U.iUnion_vecCons_pair V).trans hUV) n)
    (Iso.refl _) ?_ ?_
  · dsimp only
    rw [TauCeti.smallSingularHomologyIso_hom, Iso.refl_hom, Category.id_comp,
      mayerVietorisFromBiprod_comp_homologyMap_ι]
  · dsimp only
    rw [Iso.refl_hom, Category.comp_id, TauCeti.smallSingularHomologyIso_hom,
    homologyMap_ι_comp_mayerVietorisδ R hU hV hUV n m h]

include hU hV hUV in
/-- If `Hₙ₊₁(X)` and `Hₙ(X)` vanish, the first map `Hₙ(U ∩ V) ⟶ Hₙ(U) ⊞ Hₙ(V)` of the
Mayer–Vietoris sequence of an open cover is an isomorphism. -/
lemma isIso_mayerVietorisToBiprod_of_isZero (n : ℕ)
    (h₁ : IsZero ((toSSet.obj X).homology R (n + 1))) (h₀ : IsZero ((toSSet.obj X).homology R n)) :
    IsIso (SSet.mayerVietorisToBiprod R
      (toSSet.map (ofHom (ContinuousMap.inclusion (Set.inter_subset_left (t := V)))))
      (toSSet.map (ofHom (ContinuousMap.inclusion (Set.inter_subset_right (s := U))))) n) := by
  have := (mayerVietoris_exact₁ R hU hV hUV (n + 1) n).mono_g (h₁.eq_of_src _ _)
  have := (mayerVietoris_exact₂ R hU hV hUV n).epi_f (h₀.eq_of_tgt _ _)
  exact isIso_of_mono_of_epi _

include hUV in
/-- The map `H₀(U) ⊞ H₀(V) ⟶ H₀(X)` at the end of the Mayer–Vietoris sequence is an
epimorphism, for any cover of `X` by two subspaces: every singular point of `X` lies in `U` or
in `V`. -/
lemma epi_mayerVietorisFromBiprod_zero :
    Epi (SSet.mayerVietorisFromBiprod R (toSSet.map (ofHom (ContinuousMap.subtypeVal U)))
      (toSSet.map (ofHom (ContinuousMap.subtypeVal V))) 0) := by
  have hepi : Epi (SSet.mayerVietorisFromBiprod R
      (toSmallSingularSubcomplex ![U, V] (Matrix.cons_val_zero U ![V]).superset)
      (toSmallSingularSubcomplex ![U, V]
        ((Matrix.cons_val_one U ![V]).trans (Matrix.cons_val_zero V ![])).superset) 0 ≫
      SSet.homologyMap (X.smallSingularSubcomplex ![U, V]).ι R 0) := by
    have : Epi (SSet.homologyMap (X.smallSingularSubcomplex ![U, V]).ι R 0) := by
      -- the inclusion is bijective on singular points, so it is onto in degree `0` of the chains
      change Epi (HomologicalComplex.homologyMap
        (SSet.chainComplexMap (X.smallSingularSubcomplex ![U, V]).ι R) 0)
      have : Epi ((SSet.chainComplexMap (X.smallSingularSubcomplex ![U, V]).ι R).f 0) :=
        ⟨fun g h hgh ↦ SSet.chainComplex_hom_ext fun x ↦ by
          have hx : x ∈ (X.smallSingularSubcomplex ![U, V]).obj
              (Opposite.op (SimplexCategory.mk 0)) := by
            rw [mem_smallSingularSubcomplex_iff]
            open Convexity in
            obtain ⟨t⟩ : Nonempty (StdSimplex ℝ (Fin 1)) := inferInstance
            have : X.toSSetObjEquiv (Opposite.op (SimplexCategory.mk 0)) x t ∈ U ∪ V :=
              hUV ▸ Set.mem_univ _
            rcases this with h | h
            · exact ⟨0, by rintro _ ⟨s, rfl⟩; simpa [Subsingleton.elim s t] using h⟩
            · exact ⟨1, by rintro _ ⟨s, rfl⟩; simpa [Subsingleton.elim s t] using h⟩
          have key : (X.smallSingularSubcomplex ![U, V] : SSet).ιChainComplex (R := R)
                ⟨x, hx⟩ ≫
              (SSet.chainComplexMap (X.smallSingularSubcomplex ![U, V]).ι R).f 0 =
              (toSSet.obj X).ιChainComplex x :=
            SSet.ι_chainComplexMap_f (f := (X.smallSingularSubcomplex ![U, V]).ι) (R := R)
              (x := ⟨x, hx⟩)
          rw [← key, Category.assoc, Category.assoc, hgh]⟩
      exact HomologicalComplex.epi_homologyMap_of_epi_of_not_rel _ _ (by simp)
    have := SSet.epi_mayerVietorisFromBiprod_zero R
      (isPushout_toSSet_inter_smallSingularSubcomplex U V)
    exact epi_comp _ _
  rw [mayerVietorisFromBiprod_comp_homologyMap_ι] at hepi
  exact hepi

include hU hV hUV in
/-- If `Hₙ(U ∩ V)` vanishes, and so does `Hₘ(U ∩ V)` when `n = m + 1`, for instance when `U` and
`V` are disjoint, the second map `Hₙ(U) ⊞ Hₙ(V) ⟶ Hₙ(X)` of the Mayer–Vietoris sequence of an
open cover is an isomorphism. -/
lemma isIso_mayerVietorisFromBiprod_of_isZero (n : ℕ)
    (h₀ : IsZero ((toSSet.obj (of ↥(U ∩ V))).homology R n))
    (h₁ : ∀ m, n = m + 1 → IsZero ((toSSet.obj (of ↥(U ∩ V))).homology R m)) :
    IsIso (SSet.mayerVietorisFromBiprod R (toSSet.map (ofHom (ContinuousMap.subtypeVal U)))
      (toSSet.map (ofHom (ContinuousMap.subtypeVal V))) n) := by
  have := (mayerVietoris_exact₂ R hU hV hUV n).mono_g (h₀.eq_of_src _ _)
  rcases n with _ | m
  · have := epi_mayerVietorisFromBiprod_zero R hUV
    exact isIso_of_mono_of_epi _
  · have := (mayerVietoris_exact₃ R hU hV hUV (m + 1) m).epi_f ((h₁ m rfl).eq_of_tgt _ _)
    exact isIso_of_mono_of_epi _

include hU hV hUV in
/-- For a cover of `X` by two disjoint open sets `U` and `V`, the sum `Hₙ(U) ⊞ Hₙ(V) ⟶ Hₙ(X)` of
the maps induced by the subspace inclusions is an isomorphism: it is the second map of the
Mayer–Vietoris sequence, and the homology of `U ∩ V` vanishes in every degree. -/
lemma isIso_biprodDesc_singularHomologyFunctor_map_of_disjoint (hd : Disjoint U V) (n : ℕ) :
    IsIso (biprod.desc
      (((AlgebraicTopology.singularHomologyFunctor C n).obj R).map
        (ofHom (ContinuousMap.subtypeVal U)))
      (((AlgebraicTopology.singularHomologyFunctor C n).obj R).map
        (ofHom (ContinuousMap.subtypeVal V)))) := by
  have : IsEmpty ↥(U ∩ V) := ⟨fun x ↦ Set.disjoint_left.1 hd x.property.1 x.property.2⟩
  have h (m : ℕ) := TauCeti.isZero_singularHomology_of_isEmpty R (of ↥(U ∩ V)) m
  have := isIso_mayerVietorisFromBiprod_of_isZero R hU hV hUV n (h n) fun m _ ↦ h m
  -- The Mayer–Vietoris map is this map: singular homology is by definition the homology of the
  -- singular simplicial set (`TauCeti.singularHomologyFunctor_obj_map`).
  rwa [show SSet.mayerVietorisFromBiprod R _ _ n = biprod.desc _ _ from biprod.hom_ext' _ _
    ((SSet.inl_mayerVietorisFromBiprod R _ _ n).trans (biprod.inl_desc _ _).symm)
    ((SSet.inr_mayerVietorisFromBiprod R _ _ n).trans (biprod.inr_desc _ _).symm)] at this

variable {Y : TopCat.{w}} {U' V' : Set Y} (hU' : IsOpen U') (hV' : IsOpen V')
  (hUV' : U' ∪ V' = Set.univ) (f : X ⟶ Y) (hfU : Set.MapsTo f U U') (hfV : Set.MapsTo f V V')

/-- **Naturality of the Mayer–Vietoris connecting morphism.** A map `f : X ⟶ Y` carrying `U` into
`U'` and `V` into `V'` commutes with the connecting morphisms, where `U ∩ V ⟶ U' ∩ V'` is the
restriction of `f`. -/
@[reassoc]
lemma mayerVietorisδ_naturality (n m : ℕ) (h : m + 1 = n := by lia) :
    mayerVietorisδ R hU hV hUV n m h ≫
        SSet.homologyMap (toSSet.map (ofHom ⟨(hfU.inter_inter hfV).restrict,
          f.hom.continuous.restrict (hfU.inter_inter hfV)⟩)) R m =
      SSet.homologyMap (toSSet.map f) R n ≫ mayerVietorisδ R hU' hV' hUV' n m h := by
  have hf : ∀ i, Set.MapsTo f (![U, V] i) (![U', V'] (id i)) := by
    simp [Fin.forall_fin_two, hfU, hfV]
  have hsmall := TauCeti.smallSingularHomologyIso_naturality R ![U, V]
    (hU.vecCons hV) ((U.iUnion_vecCons_pair V).trans hUV) ![U', V'] f id hf
    (hU'.vecCons hV') ((U'.iUnion_vecCons_pair V').trans hUV') n
  have hnat := SSet.mayerVietorisδ_naturality R
    (toSSet.map (ofHom ⟨(hfU.inter_inter hfV).restrict,
      f.hom.continuous.restrict (hfU.inter_inter hfV)⟩))
    (toSSet.map (ofHom ⟨hfU.restrict, f.hom.continuous.restrict hfU⟩))
    (toSSet.map (ofHom ⟨hfV.restrict, f.hom.continuous.restrict hfV⟩))
    (X.smallSingularSubcomplexMap ![U, V] ![U', V'] f id hf)
    (isPushout_toSSet_inter_smallSingularSubcomplex U V)
    (isPushout_toSSet_inter_smallSingularSubcomplex U' V') ?_ ?_ ?_ ?_ n m h
  · rw [mayerVietorisδ, mayerVietorisδ, Category.assoc, hnat, ← Category.assoc,
      ← Category.assoc]
    congr 1
    rw [Iso.inv_comp_eq, ← Category.assoc, hsmall, Category.assoc, Iso.hom_inv_id,
      Category.comp_id]
  -- The four squares of singular simplicial sets commute because the underlying squares of
  -- continuous maps do.
  · rw [← Functor.map_comp, ← Functor.map_comp, ofHom_inclusion_comp]
  · rw [← Functor.map_comp, ← Functor.map_comp, ofHom_inclusion_comp]
  · exact toSmallSingularSubcomplex_comp_smallSingularSubcomplexMap _ _ f id hf _ _ hfU
  · exact toSmallSingularSubcomplex_comp_smallSingularSubcomplexMap _ _ f id hf _ _ hfV

end TopCat
