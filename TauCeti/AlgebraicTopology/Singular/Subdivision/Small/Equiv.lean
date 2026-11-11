/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.QuasiIso
public import TauCeti.AlgebraicTopology.SimplicialSet.Homology.ChainRetraction
public import TauCeti.AlgebraicTopology.Singular.Subdivision.Small.Chains

/-!
# Chains subordinate to a cover are a deformation retract of all singular chains

For an open cover `U` of a space `X`, the singular chains subordinate to `U` — those supported on
simplices whose image lies in a single member of `U` — include into all singular chains by a chain
homotopy equivalence. This is the small-chain theorem, the analytic heart of excision: it lets
every singular chain be replaced, without changing its homology class, by one assembled from
simplices small enough to be seen inside a single member of the cover.

Both results here are instances of the abstract chain retraction
`TauCeti.chainRangeHomotopyEquiv`, applied to barycentric subdivision and its prism operator.
Subdivision is chain homotopic to the identity through the prism operator, both operators
preserve the chains subordinate to `U`, and every singular simplex becomes subordinate to an open
cover after enough subdivisions. The homotopy inverse is a strict retraction, but the number of
subdivisions it uses depends on the simplex, so it is not natural in the space. The inclusion
itself is natural, hence so is the induced isomorphism `smallSingularHomologyIso` on homology.

The same argument runs inside any affinely stable subcomplex `S` of the singular simplicial set,
because subdivision and the prism operator restrict to the chains of `S`: the chains of
`S ⊓ X.smallSingularSubcomplex U` are a deformation retract of the chains of `S`
(`TauCeti.subcomplexSmallChainHomotopyEquiv`). For the smooth singular simplices of a manifold,
`TauCeti.smoothSingularSubcomplex`, this is the small-chain theorem for smooth chains.

## Main definitions and results

* `TauCeti.smallSingularChainHomotopyEquiv`: the small-chain inclusion is a chain homotopy
  equivalence, and `TauCeti.smallSingularHomologyIso` the induced isomorphism on homology.
* `TauCeti.subcomplexSmallChainHomotopyEquiv`: the same for the chains of an affinely stable
  subcomplex.

## References

* A. Hatcher, *Algebraic Topology*, Section 2.1, Proposition 2.21.
-/

public section

noncomputable section

open CategoryTheory Limits Convexity Simplicial AlgebraicTopology

universe w v u

namespace TauCeti

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasCoproducts.{w} C] (R : C)
  {X : TopCat.{w}} {ι : Type*} (U : ι → Set X)

section Singular

variable (hU : ∀ i, IsOpen (U i)) (hcov : ⋃ i, U i = Set.univ)
include hU hcov

/-- **Chains subordinate to an open cover are a deformation retract of all singular chains.**
The inclusion of the chains subordinate to an open cover `U` into the singular chain complex is a
chain homotopy equivalence, whose homotopy inverse is even a strict retraction. -/
def smallSingularChainHomotopyEquiv :
    HomotopyEquiv ((X.smallSingularSubcomplex U : SSet).chainComplex R)
      ((TopCat.toSSet.obj X).chainComplex R) :=
  chainRangeHomotopyEquiv (i := (X.smallSingularSubcomplex U).ι)
    (h := singularSubdivisionHomotopy R X)
    (fun n ↦ ⟨subcomplexSubdivisionX R _ n, by simp⟩)
    (fun n ↦ ⟨subcomplexPrismX R _ n, by simp⟩)
    fun _ σ ↦ by
      obtain ⟨n₀, hn₀⟩ := exists_iterate_singularSubdivision_factor_small R U hU hcov σ
      exact ⟨n₀, (mem_chainRange_iff _).2 (hn₀ n₀ le_rfl)⟩

/-- The forward map of the small-chain homotopy equivalence is the inclusion of the chains
subordinate to the cover. -/
@[simp]
lemma smallSingularChainHomotopyEquiv_hom :
    (smallSingularChainHomotopyEquiv R U hU hcov).hom =
      SSet.chainComplexMap (X.smallSingularSubcomplex U).ι R :=
  chainRangeHomotopyEquiv_hom ..

/-- The isomorphism on homology induced by the inclusion of the chains subordinate to an open
cover.  Since the inclusion is natural in the covered space, so is this isomorphism, whereas the
homotopy inverse underlying it is not. -/
def smallSingularHomologyIso [CategoryWithHomology C] (n : ℕ) :
    ((X.smallSingularSubcomplex U : SSet).chainComplex R).homology n ≅
      ((TopCat.toSSet.obj X).chainComplex R).homology n :=
  (smallSingularChainHomotopyEquiv R U hU hcov).toHomologyIso n

@[simp]
lemma smallSingularHomologyIso_hom [CategoryWithHomology C] (n : ℕ) :
    (smallSingularHomologyIso R U hU hcov n).hom = HomologicalComplex.homologyMap
      (SSet.chainComplexMap (X.smallSingularSubcomplex U).ι R) n :=
  congrArg (HomologicalComplex.homologyMap · n) (smallSingularChainHomotopyEquiv_hom R U hU hcov)

/-- The small-chain homology isomorphism is natural under maps carrying members of one cover
into members of another. -/
lemma smallSingularHomologyIso_naturality [CategoryWithHomology C]
    {κ : Type*} {Y : TopCat.{w}} (V : κ → Set Y) (f : X ⟶ Y) (r : ι → κ)
    (hf : ∀ i, Set.MapsTo f (U i) (V (r i))) (hV : ∀ j, IsOpen (V j))
    (hcovV : ⋃ j, V j = Set.univ) (n : ℕ) :
    (smallSingularHomologyIso R U hU hcov n).hom ≫
        HomologicalComplex.homologyMap
          (SSet.chainComplexMap (TopCat.toSSet.map f) R) n =
      HomologicalComplex.homologyMap
          (SSet.chainComplexMap (X.smallSingularSubcomplexMap U V f r hf) R) n ≫
        (smallSingularHomologyIso R V hV hcovV n).hom := by
  rw [smallSingularHomologyIso_hom, smallSingularHomologyIso_hom,
    ← HomologicalComplex.homologyMap_comp, ← HomologicalComplex.homologyMap_comp,
    ← Functor.map_comp, ← Functor.map_comp, TopCat.smallSingularSubcomplexMap_ι]

/-- The inclusion of the chains subordinate to an open cover induces an isomorphism on homology
in every degree. -/
theorem isIso_homologyMap_smallSingularChainι [CategoryWithHomology C] (n : ℕ) :
    IsIso (HomologicalComplex.homologyMap
      (SSet.chainComplexMap (X.smallSingularSubcomplex U).ι R) n) := by
  rw [← smallSingularHomologyIso_hom R U hU hcov n]
  infer_instance

/-- The inclusion of the chains subordinate to an open cover is a quasi-isomorphism. -/
theorem quasiIso_chainComplexMap_smallSingularSubcomplex_ι [CategoryWithHomology C] :
    QuasiIso (SSet.chainComplexMap (X.smallSingularSubcomplex U).ι R) := by
  rw [quasiIso_iff]
  intro n
  rw [quasiIsoAt_iff_isIso_homologyMap]
  exact isIso_homologyMap_smallSingularChainι R U hU hcov n

end Singular

/-! ### Affinely stable subcomplexes -/

section Subcomplex

open AffineChain SSet.Subcomplex

variable (S : (TopCat.toSSet.obj X).Subcomplex) [S.IsAffineStable]

/-- Pushing forward an affine chain along a simplex of an affinely stable subcomplex `S` gives a
chain of a smaller subcomplex `T` as soon as every simplex in its support lies in `T`. -/
lemma AffineChain.subcomplexChain_mem_chainRange {T : (TopCat.toSSet.obj X).Subcomplex}
    (hT : T ≤ S) {m k : ℕ} (σ : (S : SSet) _⦋m⦌)
    (c : (Fin (k + 1) → StdSimplex ℝ (Fin (m + 1))) →₀ ℤ)
    (hc : ∀ v ∈ c.support, (X.toSSetObjEquiv _).symm
      ((X.toSSetObjEquiv _ σ.val).comp (StdSimplex.continuousAffineMapMk v)) ∈
        T.obj (Opposite.op ⦋k⦌)) :
    subcomplexChain R S σ k c ∈ chainRange R (homOfLE hT) k := by
  rw [← c.sum_single, map_finsuppSum, Finsupp.sum]
  refine AddSubgroup.sum_mem _ fun v hv ↦ ?_
  rw [subcomplexChain_single]
  exact AddSubgroup.zsmul_mem _ (ιChainComplex_app_mem_chainRange (i := homOfLE hT) ⟨_, hc v hv⟩) _

variable (hU : ∀ i, IsOpen (U i)) (hcov : ⋃ i, U i = Set.univ)
include hU hcov

/-- For an open cover, a sufficiently fine iterated subdivision of every simplex of an affinely
stable subcomplex `S` is a chain of the simplices of `S` subordinate to the cover. -/
theorem exists_ιChainComplex_comp_subcomplexSubdivisionChainMap_pow_mem_chainRange {k : ℕ}
    (σ : (S : SSet) _⦋k⦌) :
    ∃ n, (S : SSet).ιChainComplex σ ≫
        (End.of (subcomplexSubdivisionChainMap R S) ^ n).asHom.f k ∈
      chainRange R (homOfLE (inf_le_left : S ⊓ X.smallSingularSubcomplex U ≤ S)) k := by
  obtain ⟨n₀, hn₀⟩ := ContinuousMap.exists_forall_mem_support_subdivision_iterate_range_subset
    (X.toSSetObjEquiv _ σ.val) hU hcov k
  refine ⟨n₀, ?_⟩
  rw [← subcomplexChain_simplex, ← subcomplexChain_subdivision_iterate]
  exact subcomplexChain_mem_chainRange R S _ σ _ fun v hv ↦
    ⟨IsAffineStable.comp_affineMapMk_mem σ.property v,
      (TopCat.mem_smallSingularSubcomplex_iff X U _).2 (hn₀ n₀ le_rfl _ v hv)⟩

/-- **The small-chain theorem inside an affinely stable subcomplex.** For an affinely stable
subcomplex `S` of the singular simplicial set and an open cover `U`, the inclusion of the chains
of the simplices of `S` subordinate to `U` into the chains of `S` is a chain homotopy equivalence,
whose homotopy inverse is a strict retraction. For the smooth singular simplices of a manifold,
`TauCeti.smoothSingularSubcomplex`, this is the small-chain theorem for smooth chains. -/
def subcomplexSmallChainHomotopyEquiv :
    HomotopyEquiv (((S ⊓ X.smallSingularSubcomplex U : (TopCat.toSSet.obj X).Subcomplex) :
      SSet).chainComplex R) ((S : SSet).chainComplex R) :=
  chainRangeHomotopyEquiv (i := homOfLE inf_le_left) (h := subcomplexSubdivisionHomotopy R S)
    (fun n ↦ ⟨(subcomplexSubdivisionChainMap R _).f n, by
      rw [← HomologicalComplex.comp_f, ← HomologicalComplex.comp_f,
        ← subcomplexSubdivisionChainMap_naturality R _ S (𝟙 X) (homOfLE inf_le_left) (by simp)]⟩)
    (fun n ↦ ⟨subcomplexPrismX R _ n, by
      rw [subcomplexSubdivisionHomotopy_hom]
      exact (subcomplexPrismX_naturality R _ S (𝟙 X) (homOfLE inf_le_left) (by simp) n).symm⟩)
    fun _ σ ↦ exists_ιChainComplex_comp_subcomplexSubdivisionChainMap_pow_mem_chainRange R U S hU
      hcov σ

/-- The forward map of the small-chain homotopy equivalence of an affinely stable subcomplex is
the inclusion of the chains subordinate to the cover. -/
@[simp]
lemma subcomplexSmallChainHomotopyEquiv_hom :
    (subcomplexSmallChainHomotopyEquiv R U S hU hcov).hom =
      SSet.chainComplexMap (homOfLE inf_le_left) R :=
  chainRangeHomotopyEquiv_hom ..

end Subcomplex

end TauCeti
