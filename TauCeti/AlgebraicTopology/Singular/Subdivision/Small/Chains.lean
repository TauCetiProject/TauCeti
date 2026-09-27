/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Endomorphism
public import TauCeti.AlgebraicTopology.Singular.Subdivision.Small.Basic

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
* `TauCeti.AffineChain.smallSingularChain`: push affine chains forward along a small simplex
  with values in the small-chain complex.
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
def smallSingularSubcomplex (U : ι → Set X) : (TopCat.toSSet.obj X).Subcomplex where
  obj n := {σ | ∃ i, Set.range (X.toSSetObjEquiv n σ) ⊆ U i}
  map f σ := by
    rintro ⟨i, hi⟩
    refine ⟨i, ?_⟩
    rintro _ ⟨z, rfl⟩
    exact hi ⟨StdSimplex.map f.unop z,
      (TopCat.toSSetObjEquiv_naturality_apply f.unop σ z).symm⟩

@[simp]
lemma mem_smallSingularSubcomplex_iff (U : ι → Set X) {n : SimplexCategoryᵒᵖ}
    (σ : (TopCat.toSSet.obj X).obj n) :
    σ ∈ (X.smallSingularSubcomplex U).obj n ↔
      ∃ i, Set.range (X.toSSetObjEquiv n σ) ⊆ U i :=
  Iff.rfl

variable {X} {κ : Type*} {Y : TopCat.{w}} (U : ι → Set X) (V : κ → Set Y)

/-- A map carrying each member of one family into a member of another restricts to a map of the
corresponding small singular subcomplexes. -/
def smallSingularSubcomplexMap (f : X ⟶ Y) (r : ι → κ)
    (hf : ∀ i, Set.MapsTo f (U i) (V (r i))) :
    (X.smallSingularSubcomplex U : SSet) ⟶ (Y.smallSingularSubcomplex V : SSet) :=
  SSet.Subcomplex.lift
    ((X.smallSingularSubcomplex U).ι ≫ TopCat.toSSet.map f) (by
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
      (X.smallSingularSubcomplex U).ι ≫ TopCat.toSSet.map f :=
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
    (X.smallSingularSubcomplex U).preimage (TopCat.toSSet.map f) =
      Y.smallSingularSubcomplex (fun i ↦ f ⁻¹' U i) := by
  ext n σ
  simp [Set.range_comp, Set.image_subset_iff]

/-- The singular simplicial set of a subset `S` contained in a member `U i` of the family maps into
the small singular subcomplex of the family: every singular simplex of `S` is small. -/
def toSmallSingularSubcomplex {S : Set X} {i : ι} (h : S ⊆ U i) :
    TopCat.toSSet.obj (TopCat.of S) ⟶ (X.smallSingularSubcomplex U : SSet) :=
  SSet.Subcomplex.lift (TopCat.toSSet.map (TopCat.ofHom (ContinuousMap.subtypeVal S))) (by
    rintro n _ ⟨σ, rfl⟩
    rw [mem_smallSingularSubcomplex_iff, TauCeti.TopCat.toSSetObjEquiv_toSSet_map_app,
      ContinuousMap.coe_comp, Set.range_comp]
    exact ⟨i, (Set.image_subset_range _ _).trans fun _ ⟨x, hx⟩ ↦ hx ▸ h x.2⟩)

@[reassoc (attr := simp)]
lemma toSmallSingularSubcomplex_ι {S : Set X} {i : ι} (h : S ⊆ U i) :
    toSmallSingularSubcomplex U h ≫ (X.smallSingularSubcomplex U).ι =
      TopCat.toSSet.map (TopCat.ofHom (ContinuousMap.subtypeVal S)) :=
  SSet.Subcomplex.lift_ι _ _

@[simp]
lemma toSmallSingularSubcomplex_app_coe {S : Set X} {i : ι} (h : S ⊆ U i) {n : SimplexCategoryᵒᵖ}
    (σ : (TopCat.toSSet.obj (TopCat.of S)).obj n) :
    dsimp% ((toSmallSingularSubcomplex U h).app n σ).val =
      (TopCat.toSSet.map (TopCat.ofHom (ContinuousMap.subtypeVal S))).app n σ :=
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

/-- Push an affine chain forward along a small singular simplex, with values in the
small-chain complex. Every resulting simplex has image inside the original simplex. -/
def smallSingularChain {m : ℕ} (σ : (X.smallSingularSubcomplex U : SSet) _⦋m⦌) (k : ℕ) :
    ((Fin (k + 1) → StdSimplex ℝ (Fin (m + 1))) →₀ ℤ) →ₗ[ℤ]
      (R ⟶ ((X.smallSingularSubcomplex U : SSet).chainComplex R).X k) :=
  linearCombination ℤ fun v ↦ (X.smallSingularSubcomplex U : SSet).ιChainComplex
    ⟨(X.toSSetObjEquiv _).symm
      ((X.toSSetObjEquiv _ σ.val).comp (StdSimplex.continuousAffineMapMk v)), by
      obtain ⟨i, hi⟩ := σ.property
      exact ⟨i, fun _ ⟨z, hz⟩ ↦ hi ⟨StdSimplex.continuousAffineMapMk v z, hz⟩⟩⟩

@[simp]
lemma smallSingularChain_single {m k : ℕ}
    (σ : (X.smallSingularSubcomplex U : SSet) _⦋m⦌)
    (v : Fin (k + 1) → StdSimplex ℝ (Fin (m + 1))) (a : ℤ) :
    smallSingularChain R U σ k (single v a) = a •
      (X.smallSingularSubcomplex U : SSet).ιChainComplex
        ⟨(X.toSSetObjEquiv _).symm
          ((X.toSSetObjEquiv _ σ.val).comp (StdSimplex.continuousAffineMapMk v)), by
          obtain ⟨i, hi⟩ := σ.property
          exact ⟨i, fun _ ⟨z, hz⟩ ↦ hi ⟨StdSimplex.continuousAffineMapMk v z, hz⟩⟩⟩ := by
  simp [smallSingularChain]

/-- The small-chain push-forward agrees with the ordinary push-forward after inclusion. -/
@[reassoc (attr := simp)]
lemma smallSingularChain_ι {m k : ℕ}
    (σ : (X.smallSingularSubcomplex U : SSet) _⦋m⦌)
    (c : (Fin (k + 1) → StdSimplex ℝ (Fin (m + 1))) →₀ ℤ) :
    smallSingularChain R U σ k c ≫
        (SSet.chainComplexMap (X.smallSingularSubcomplex U).ι R).f k =
      singularChain R (X.toSSetObjEquiv _ σ.val) k c := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => simp only [map_add, Preadditive.add_comp, hc, hd]
  | single v a => simp

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
            ((CategoryTheory.End.of (singularSubdivisionChainMap R X)) ^ n).f k := by
  obtain ⟨n₀, hn₀⟩ := ContinuousMap.exists_forall_mem_support_subdivision_iterate_range_subset
    (X.toSSetObjEquiv _ σ) hU hcov k
  refine ⟨n₀, fun n hn ↦ ?_⟩
  obtain ⟨f, hf⟩ := exists_singularChain_small_factor R U (X.toSSetObjEquiv _ σ)
    ((subdivision _ k)^[n] (simplex k)) (hn₀ n hn (simplex k))
  refine ⟨f, hf.trans ?_⟩
  rw [singularChain_subdivision_iterate, singularChain_simplex]

end TauCeti
