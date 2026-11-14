/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Endomorphism
public import TauCeti.AlgebraicTopology.Singular.Subdivision.Small.Basic
public import TauCeti.AlgebraicTopology.Singular.Subdivision.Subcomplex
public import TauCeti.AlgebraicTopology.Singular.Subspace

/-!
# Singular chains subordinate to an open cover

A singular simplex is *small* for a family of subsets when its image is contained in one member
of the family. Small simplices form a subcomplex of the singular simplicial set: every face and
degeneracy of a small simplex is still small. Applying Mathlib's simplicial chain-complex functor
therefore gives the complex of chains subordinate to the family, together with its canonical
inclusion into singular chains.

For an open cover, sufficiently fine barycentric subdivision of each singular simplex factors
through this inclusion. This is the chain-level smallness statement used to construct the
small-chain equivalence and prove excision.

## Main definitions and results

* `TopCat.smallSingularSubcomplex`: the subcomplex of singular simplices whose image lies in one
  member of a family of subsets.
* `TopCat.smallSingularSubcomplexMap`: a covered map restricts to the small subcomplexes.
* `TopCat.preimage_smallSingularSubcomplex`: the preimage of a small subcomplex along a map is
  the small subcomplex of the preimage family.
* `TopCat.toSmallSingularSubcomplex`: the singular simplicial set of a subset of a member of the
  family maps into the small subcomplex.
* `TopCat.chainComplexMap_f_toSmallSingularSubcomplex_comp`: restriction of singular cochains
  along the small-chain inclusion followed by a subspace inclusion.
* `TopCat.chainComplexMap_smallSingularSubcomplex_ι_comp_eq_zero`: a chain map vanishing on the
  singular chains of each member of the family vanishes on the small chains.
* `TopCat.smallSingularSubcomplex` is affinely stable (`SSet.Subcomplex.IsAffineStable`), so
  barycentric subdivision and its prism operator restrict to it
  (`TauCeti.subcomplexSubdivisionHomotopy`).
* `TauCeti.AffineChain.exists_singularChain_small_factor`: a pushed-forward affine chain supported
  on small simplices factors through the small-chain complex.
* `TauCeti.exists_iterate_singularSubdivision_factor_small`: a sufficiently fine subdivision of
  any singular simplex factors through the small-chain inclusion.

## References

* A. Hatcher, *Algebraic Topology*, Section 2.1, proof of Proposition 2.21, step (4).
-/

public section

noncomputable section

open CategoryTheory Limits Convexity Simplicial AlgebraicTopology Finsupp

universe w v u

namespace TopCat

variable (X : TopCat.{w}) {ι : Type*}

/-- The subcomplex of the singular simplicial set consisting of the simplices whose image is
contained in one member of the family `U`. No covering or openness hypothesis is needed for the
definition. -/
def smallSingularSubcomplex (U : ι → Set X) : (toSSet.obj X).Subcomplex where
  obj n := {σ | ∃ i, Set.range (X.toSSetObjEquiv n σ) ⊆ U i}
  map f σ := by
    rintro ⟨i, hi⟩
    refine ⟨i, ?_⟩
    rintro _ ⟨z, rfl⟩
    exact hi ⟨StdSimplex.map f.unop z,
      (toSSetObjEquiv_naturality_apply f.unop σ z).symm⟩

@[simp]
lemma mem_smallSingularSubcomplex_iff (U : ι → Set X) {n : SimplexCategoryᵒᵖ}
    (σ : (toSSet.obj X).obj n) :
    σ ∈ (X.smallSingularSubcomplex U).obj n ↔
      ∃ i, Set.range (X.toSSetObjEquiv n σ) ⊆ U i :=
  Iff.rfl

/-- Every affine subsimplex of a small singular simplex lies in a member of the same family. -/
lemma exists_range_comp_affineMapMk_subset_of_mem_smallSingularSubcomplex
    (U : ι → Set X) {m k : ℕ} {σ : (toSSet.obj X) _⦋m⦌}
    (hσ : σ ∈ (X.smallSingularSubcomplex U).obj _)
    (a : Fin (k + 1) → StdSimplex ℝ (Fin (m + 1))) :
    ∃ i, Set.range ((X.toSSetObjEquiv _ σ).comp (StdSimplex.continuousAffineMapMk a)) ⊆ U i := by
  obtain ⟨i, hi⟩ := (mem_smallSingularSubcomplex_iff X U σ).1 hσ
  refine ⟨i, ?_⟩
  rw [ContinuousMap.coe_comp]
  exact (Set.range_comp_subset_range _ _).trans hi

/-- The small singular subcomplex is affinely stable, so barycentric subdivision and its prism
operator restrict to chains subordinate to a family of subsets. -/
instance (U : ι → Set X) : (X.smallSingularSubcomplex U).IsAffineStable where
  comp_affineMapMk_mem hσ v := by
    rw [mem_smallSingularSubcomplex_iff, Equiv.apply_symm_apply]
    exact X.exists_range_comp_affineMapMk_subset_of_mem_smallSingularSubcomplex U hσ v

/-- Shrinking the members of the family shrinks the small singular subcomplex. -/
lemma smallSingularSubcomplex_mono {U U' : ι → Set X} (h : ∀ i, U i ⊆ U' i) :
    X.smallSingularSubcomplex U ≤ X.smallSingularSubcomplex U' := by
  rintro n σ ⟨i, hi⟩
  exact ⟨i, hi.trans (h i)⟩

variable {X} {κ : Type*} {Y : TopCat.{w}} (U : ι → Set X) (V : κ → Set Y)

/-- A map carrying each member of one family into a member of another restricts to a map of the
corresponding small singular subcomplexes. -/
def smallSingularSubcomplexMap (f : X ⟶ Y) (r : ι → κ)
    (hf : ∀ i, Set.MapsTo f (U i) (V (r i))) :
    (X.smallSingularSubcomplex U : SSet) ⟶ (Y.smallSingularSubcomplex V : SSet) :=
  SSet.Subcomplex.lift
    ((X.smallSingularSubcomplex U).ι ≫ toSSet.map f) (by
      rintro n _ ⟨σ, rfl⟩
      rw [mem_smallSingularSubcomplex_iff]
      obtain ⟨i, hi⟩ := σ.property
      refine ⟨r i, ?_⟩
      rintro _ ⟨z, rfl⟩
      exact hf i (hi ⟨z, rfl⟩))

@[reassoc (attr := simp)]
lemma smallSingularSubcomplexMap_ι (f : X ⟶ Y) (r : ι → κ)
    (hf : ∀ i, Set.MapsTo f (U i) (V (r i))) :
    X.smallSingularSubcomplexMap U V f r hf ≫ (Y.smallSingularSubcomplex V).ι =
      (X.smallSingularSubcomplex U).ι ≫ toSSet.map f :=
  SSet.Subcomplex.lift_ι _ _

@[simp]
lemma smallSingularSubcomplexMap_id :
    X.smallSingularSubcomplexMap U U (𝟙 X) id (fun i ↦ Set.mapsTo_id (U i)) = 𝟙 _ := by
  ext n σ
  rfl

/-- The preimage of the small singular subcomplex of a family along a continuous map is the small
singular subcomplex of the preimage family. -/
@[simp]
lemma preimage_smallSingularSubcomplex (f : Y ⟶ X) :
    (X.smallSingularSubcomplex U).preimage (toSSet.map f) =
      Y.smallSingularSubcomplex (fun i ↦ f ⁻¹' U i) := by
  ext n σ
  simp [Set.range_comp, Set.image_subset_iff]

/-- The singular simplicial set of a subset `S` contained in a member `U i` of the family maps into
the small singular subcomplex of the family: every singular simplex of `S` is small. -/
def toSmallSingularSubcomplex {S : Set X} {i : ι} (h : S ⊆ U i) :
    toSSet.obj (of S) ⟶ (X.smallSingularSubcomplex U : SSet) :=
  SSet.Subcomplex.lift (toSSet.map (ofHom (ContinuousMap.subtypeVal S))) (by
    rintro n _ ⟨σ, rfl⟩
    rw [mem_smallSingularSubcomplex_iff, TauCeti.TopCat.toSSetObjEquiv_toSSet_map_app,
      ContinuousMap.coe_comp, Set.range_comp]
    exact ⟨i, (Set.image_subset_range _ _).trans fun _ ⟨x, hx⟩ ↦ hx ▸ h x.2⟩)

@[reassoc (attr := simp)]
lemma toSmallSingularSubcomplex_ι {S : Set X} {i : ι} (h : S ⊆ U i) :
    toSmallSingularSubcomplex U h ≫ (X.smallSingularSubcomplex U).ι =
      toSSet.map (ofHom (ContinuousMap.subtypeVal S)) :=
  SSet.Subcomplex.lift_ι _ _

@[simp]
lemma toSmallSingularSubcomplex_app_coe {S : Set X} {i : ι} (h : S ⊆ U i) {n : SimplexCategoryᵒᵖ}
    (σ : (toSSet.obj (of S)).obj n) :
    dsimp% ((toSmallSingularSubcomplex U h).app n σ).val =
      (toSSet.map (ofHom (ContinuousMap.subtypeVal S))).app n σ :=
  SSet.Subcomplex.lift_app_coe _ _ _

variable {μ : Type*} {Z : TopCat.{w}} (W : μ → Set Z)

/-- Restriction of covered maps to small singular subcomplexes respects composition. -/
lemma smallSingularSubcomplexMap_comp (f : X ⟶ Y) (g : Y ⟶ Z) (r : ι → κ) (s : κ → μ)
    (hf : ∀ i, Set.MapsTo f (U i) (V (r i)))
    (hg : ∀ j, Set.MapsTo g (V j) (W (s j))) :
    X.smallSingularSubcomplexMap U W (f ≫ g) (s ∘ r) (fun i ↦ (hg (r i)).comp (hf i)) =
      X.smallSingularSubcomplexMap U V f r hf ≫
        Y.smallSingularSubcomplexMap V W g s hg := by
  ext n σ
  rfl

/-- A chain map out of the singular chains of `X` vanishes on the chains of the singular simplices
lying in some member of the family `U` as soon as it vanishes on the singular chains of each
member. -/
lemma chainComplexMap_smallSingularSubcomplex_ι_comp_eq_zero {C : Type u} [Category.{v} C]
    [Preadditive C] [HasCoproducts.{w} C] {T : C} {K : ChainComplex C ℕ}
    (F : (toSSet.obj X).chainComplex T ⟶ K)
    (hF : ∀ i, SSet.chainComplexMap
      (toSSet.map (ofHom (ContinuousMap.subtypeVal (U i)))) T ≫ F = 0) :
    SSet.chainComplexMap (X.smallSingularSubcomplex U).ι T ≫ F = 0 := by
  ext n : 1
  refine SSet.chainComplex_hom_ext fun σ ↦ ?_
  obtain ⟨i, hi⟩ := (mem_smallSingularSubcomplex_iff X U σ.1).1 σ.2
  -- `σ` is the image of a singular simplex of `U i`
  obtain ⟨τ, hτ⟩ := (mem_range_toSSet_subtypeVal_iff (U i) _ σ.1).2 hi
  have h : (toSSet.obj (of (U i))).ιChainComplex (R := T) τ ≫
      (SSet.chainComplexMap (toSSet.map (ofHom (ContinuousMap.subtypeVal (U i))))
        T).f n ≫ F.f n = 0 := by
    rw [← HomologicalComplex.comp_f, hF, HomologicalComplex.zero_f, comp_zero]
  rw [SSet.ι_chainComplexMap_f_assoc, hτ] at h
  simp only [HomologicalComplex.comp_f, HomologicalComplex.zero_f, comp_zero,
    SSet.ι_chainComplexMap_f_assoc]
  exact h

end TopCat

namespace TopCat

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasCoproducts.{w} C]
  {R M : C} {X : TopCat.{w}}

/-- Restricting singular cochains of `X` to the simplices subordinate to a cover, and then to a
subspace lying in a member of the cover, is restricting to that subspace. -/
lemma chainComplexMap_f_toSmallSingularSubcomplex_comp {ι : Type*} (U : ι → Set X)
    {S' : Set X} {i : ι} (hS' : S' ⊆ U i) (n : ℕ) (z : ((toSSet.obj X).chainComplex R).X n ⟶ M) :
    (SSet.chainComplexMap (toSmallSingularSubcomplex U hS') R).f n ≫
        (SSet.chainComplexMap (X.smallSingularSubcomplex U).ι R).f n ≫ z =
      (SSet.chainComplexMap (toSSet.map (ofHom (ContinuousMap.subtypeVal S'))) R).f n ≫ z := by
  rw [← Category.assoc, ← HomologicalComplex.comp_f, ← Functor.map_comp,
    toSmallSingularSubcomplex_ι]

end TopCat

namespace TauCeti

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasCoproducts.{w} C] (R : C)
  {X : TopCat.{w}} {ι : Type*} (U : ι → Set X)

namespace AffineChain

/-- Pushing forward an affine chain supported on simplices subordinate to `U` factors through
the chain complex of the small singular subcomplex. -/
theorem exists_singularChain_small_factor {m k : ℕ}
    (σ : C(StdSimplex ℝ (Fin (m + 1)), X))
    (c : (Fin (k + 1) → StdSimplex ℝ (Fin (m + 1))) →₀ ℤ)
    (hc : ∀ v ∈ c.support, ∃ i,
      Set.range (σ.comp (StdSimplex.continuousAffineMapMk v)) ⊆ U i) :
    ∃ f : R ⟶ ((X.smallSingularSubcomplex U : SSet).chainComplex R).X k,
      f ≫ (SSet.chainComplexMap (X.smallSingularSubcomplex U).ι R).f k =
        singularChain R σ k c := by
  classical
  have hsing : singularChain R σ k c =
      ∑ v : {v // v ∈ c.support}, c v • (TopCat.toSSet.obj X).ιChainComplex
        ((X.toSSetObjEquiv _).symm (σ.comp (StdSimplex.continuousAffineMapMk v))) := by
    calc
      _ = singularChain R σ k (c.sum fun v a ↦ single v a) := by rw [c.sum_single]
      _ = c.sum fun v a ↦ a • (TopCat.toSSet.obj X).ιChainComplex
          ((X.toSSetObjEquiv _).symm (σ.comp (StdSimplex.continuousAffineMapMk v))) := by
        rw [map_finsuppSum]
        simp only [singularChain_single]
      _ = _ := by
        rw [Finsupp.sum, ← Finset.sum_attach, Finset.attach_eq_univ]
  let smallSimplex (v : Fin (k + 1) → StdSimplex ℝ (Fin (m + 1))) (hv : v ∈ c.support) :
      (X.smallSingularSubcomplex U : SSet) _⦋k⦌ :=
    ⟨(X.toSSetObjEquiv _).symm (σ.comp (StdSimplex.continuousAffineMapMk v)), by
      rw [TopCat.mem_smallSingularSubcomplex_iff]
      exact hc v hv⟩
  let f : R ⟶ ((X.smallSingularSubcomplex U : SSet).chainComplex R).X k :=
    ∑ v : {v // v ∈ c.support}, c v •
      (X.smallSingularSubcomplex U : SSet).ιChainComplex (smallSimplex v v.property)
  refine ⟨f, ?_⟩
  rw [hsing]
  simp only [f, Preadditive.sum_comp, Preadditive.zsmul_comp,
    SSet.ι_chainComplexMap_f]
  rfl

end AffineChain

open AffineChain

/-- For an open cover, a sufficiently fine iterated barycentric subdivision of every singular
simplex factors through the inclusion of the complex of chains subordinate to the cover. -/
theorem exists_iterate_singularSubdivision_factor_small (hU : ∀ i, IsOpen (U i))
    (hcov : ⋃ i, U i = Set.univ) {k : ℕ} (σ : TopCat.toSSet.obj X _⦋k⦌) :
    ∃ n₀, ∀ n ≥ n₀,
      ∃ f : R ⟶ ((X.smallSingularSubcomplex U : SSet).chainComplex R).X k,
        f ≫ (SSet.chainComplexMap (X.smallSingularSubcomplex U).ι R).f k =
          (TopCat.toSSet.obj X).ιChainComplex σ ≫
            ((CategoryTheory.End.of (singularSubdivisionChainMap R X)) ^ n).asHom.f k := by
  obtain ⟨n₀, hn₀⟩ := ContinuousMap.exists_forall_mem_support_subdivision_iterate_range_subset
    (X.toSSetObjEquiv _ σ) hU hcov k
  refine ⟨n₀, fun n hn ↦ ?_⟩
  obtain ⟨f, hf⟩ := exists_singularChain_small_factor R U (X.toSSetObjEquiv _ σ)
    ((subdivision _ k)^[n] (simplex k)) (hn₀ n hn (simplex k))
  refine ⟨f, hf.trans ?_⟩
  rw [singularChain_subdivision_iterate, singularChain_simplex]

end TauCeti
