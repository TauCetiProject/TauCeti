/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.QuasiIso
public import TauCeti.AlgebraicTopology.SimplicialSet.Homology.DeformationRetract
public import TauCeti.AlgebraicTopology.Singular.Subdivision.Small.Chains

/-!
# Chains subordinate to a cover are a deformation retract of all singular chains

For an open cover `U` of a space `X`, the singular chains subordinate to `U` — those supported on
simplices whose image lies in a single member of `U` — include into all singular chains by a chain
homotopy equivalence.  This is the small-chain theorem, the analytic heart of excision: it lets
every singular chain be replaced, without changing its homology class, by one assembled from
simplices small enough to be seen inside a single member of the cover.

The construction is Hatcher's.  It is carried out in
`TauCeti.AlgebraicTopology.SimplicialSet.Homology.DeformationRetract` for an arbitrary
monomorphism of simplicial sets together with a subdivision-like chain endomorphism and a chain
homotopy from the identity to it (`TauCeti.chainComplexMapHomotopyEquivOfSubdivision`).  Here it
is applied to the singular chains of `X` and the chains subordinate to `U`, with `s` barycentric
subdivision and `h` its prism operator.  The same operators restrict to every affinely stable
subcomplex of the singular simplicial set, such as the smooth singular simplices of a manifold;
that case is `TauCeti.AlgebraicTopology.Singular.Subdivision.Small.Subcomplex`.

The number of iterations depends on the simplex, so the resulting retraction is not natural in
the space.  The inclusion itself is natural, hence so is the induced isomorphism
`smallSingularHomologyIso` on homology.

## Main definitions and results

* `TauCeti.comp_singularSubdivisionX_mem_chainRange`,
  `TauCeti.comp_singularPrismX_mem_chainRange`: barycentric subdivision and its prism operator
  preserve the chains of every affinely stable subcomplex.
* `TauCeti.smallSingularChainHomotopyEquiv`: the small-chain inclusion is a chain homotopy
  equivalence, and `TauCeti.smallSingularHomologyIso` the induced isomorphism on homology. Its
  homotopy inverse is a strict retraction
  (`TauCeti.chainComplexMap_comp_smallSingularChainHomotopyEquiv_inv`).

## References

* A. Hatcher, *Algebraic Topology*, Section 2.1, Proposition 2.21.
-/

public section

noncomputable section

open CategoryTheory Limits Convexity Simplicial AlgebraicTopology

universe w v u

namespace TauCeti

/-! ### Chains subordinate to an open cover -/

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasCoproducts.{w} C] (R : C)
  {X : TopCat.{w}} {ι : Type*} (U : ι → Set X)

variable {R} in
/-- Barycentric subdivision preserves the chains of an affinely stable subcomplex, such as the
chains subordinate to an open cover. -/
lemma comp_singularSubdivisionX_mem_chainRange {T : (TopCat.toSSet.obj X).Subcomplex}
    [T.IsAffineStable] {n : ℕ} {f : R ⟶ ((TopCat.toSSet.obj X).chainComplex R).X n}
    (hf : f ∈ chainRange R T.ι n) :
    f ≫ singularSubdivisionX R X n ∈ chainRange R T.ι n := by
  obtain ⟨g, rfl⟩ := (mem_chainRange_iff _).1 hf
  exact (mem_chainRange_iff _).2 ⟨g ≫ subcomplexSubdivisionX R T n, by simp⟩

variable {R} in
/-- The prism operator of barycentric subdivision preserves the chains of an affinely stable
subcomplex, such as the chains subordinate to an open cover. -/
lemma comp_singularPrismX_mem_chainRange {T : (TopCat.toSSet.obj X).Subcomplex}
    [T.IsAffineStable] {n : ℕ} {f : R ⟶ ((TopCat.toSSet.obj X).chainComplex R).X n}
    (hf : f ∈ chainRange R T.ι n) :
    f ≫ singularPrismX R X n ∈ chainRange R T.ι (n + 1) := by
  obtain ⟨g, rfl⟩ := (mem_chainRange_iff _).1 hf
  exact (mem_chainRange_iff _).2 ⟨g ≫ subcomplexPrismX R T n, by simp⟩

variable (hU : ∀ i, IsOpen (U i)) (hcov : ⋃ i, U i = Set.univ)

include hU hcov

/-- **Chains subordinate to an open cover are a deformation retract of all singular chains.**
The inclusion of the chains subordinate to an open cover `U` into the singular chain complex is a
chain homotopy equivalence, whose homotopy inverse is even a strict retraction. -/
def smallSingularChainHomotopyEquiv :
    HomotopyEquiv ((X.smallSingularSubcomplex U : SSet).chainComplex R)
      ((TopCat.toSSet.obj X).chainComplex R) :=
  chainComplexMapHomotopyEquivOfSubdivision (R := R) (i := (X.smallSingularSubcomplex U).ι)
    (h := singularSubdivisionHomotopy R X)
    (fun _ _ hf ↦ by
      simpa only [singularSubdivisionChainMap_f] using comp_singularSubdivisionX_mem_chainRange hf)
    (fun _ _ hf ↦ by
      simpa only [singularSubdivisionHomotopy_hom] using comp_singularPrismX_mem_chainRange hf)
    (fun _ σ ↦ by
      obtain ⟨m, hm⟩ := exists_iterate_singularSubdivision_factor_small R U hU hcov σ
      exact ⟨m, (mem_chainRange_iff _).2 (hm m le_rfl)⟩)

/-- The forward map of the small-chain homotopy equivalence is the inclusion of the chains
subordinate to the cover. -/
@[simp]
lemma smallSingularChainHomotopyEquiv_hom :
    (smallSingularChainHomotopyEquiv R U hU hcov).hom =
      SSet.chainComplexMap (X.smallSingularSubcomplex U).ι R :=
  chainComplexMapHomotopyEquivOfSubdivision_hom _ _ _

/-- The homotopy inverse of the small-chain homotopy equivalence is a strict retraction of the
inclusion of the chains subordinate to the cover. -/
@[reassoc (attr := simp)]
lemma chainComplexMap_comp_smallSingularChainHomotopyEquiv_inv :
    SSet.chainComplexMap (X.smallSingularSubcomplex U).ι R ≫
      (smallSingularChainHomotopyEquiv R U hU hcov).inv = 𝟙 _ := by
  rw [smallSingularChainHomotopyEquiv, chainComplexMapHomotopyEquivOfSubdivision_inv,
    chainComplexMap_comp_subdivisionRetraction]

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
      (SSet.chainComplexMap (X.smallSingularSubcomplex U).ι R) n := by
  rw [← smallSingularChainHomotopyEquiv_hom R U hU hcov]
  rfl

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

end TauCeti
