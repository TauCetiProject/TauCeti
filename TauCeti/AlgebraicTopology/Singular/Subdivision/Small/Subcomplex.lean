/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.Subdivision.Small.Equiv

/-!
# The small-chain theorem on affinely stable subcomplexes

Let `S` be an affinely stable subcomplex of the singular simplicial set of a space `X`
(`SSet.Subcomplex.IsAffineStable`), such as the smooth singular simplices of a manifold
(`TauCeti.smoothSingularSubcomplex`), and let `U` be an open cover of `X`. The simplices of `S`
whose image lies in a single member of `U` form the subcomplex `S ⊓ X.smallSingularSubcomplex U`.
This file proves that the inclusion of its chains into the chains of `S` is a chain homotopy
equivalence (`TauCeti.subcomplexSmallChainHomotopyEquiv`), and hence a quasi-isomorphism.

Barycentric subdivision and its prism operator restrict to the chains of every affinely stable
subcomplex (`TauCeti.subcomplexSubdivisionHomotopy`). On the chains of `S` they preserve the chains
of every affinely stable subcomplex of `S`
(`TauCeti.comp_subcomplexSubdivisionX_mem_chainRange`), in particular those of
`S ⊓ X.smallSingularSubcomplex U`, and a sufficiently fine
iterated subdivision of each simplex of `S` is a chain of `S ⊓ X.smallSingularSubcomplex U`
(`TauCeti.exists_ιChainComplex_comp_subcomplexSubdivisionChainMap_pow_mem_chainRange`), by the
Lebesgue number argument of the singular case. So the general construction
`TauCeti.chainComplexMapHomotopyEquivOfSubdivision` applies. For smooth singular chains this is
the small-chain theorem needed for the Mayer–Vietoris sequence of smooth singular chains and for
comparing smooth with continuous singular homology.

## Main results

* `TauCeti.AffineChain.subcomplexChain_mem_chainRange`: pushing forward an affine chain supported
  on small simplices gives a chain of `S ⊓ X.smallSingularSubcomplex U`.
* `TauCeti.exists_ιChainComplex_comp_subcomplexSubdivisionChainMap_pow_mem_chainRange`: a
  sufficiently fine iterated subdivision of each simplex of `S` is subordinate to the open
  cover.
* `TauCeti.subcomplexSmallChainHomotopyEquiv`: the inclusion of the chains of `S` subordinate to
  an open cover into the chains of `S` is a chain homotopy equivalence. Its homotopy inverse is a
  strict retraction (`TauCeti.chainComplexMap_comp_subcomplexSmallChainHomotopyEquiv_inv`).
* `TauCeti.subcomplexSmallHomologyIso`: the induced isomorphism on homology, natural under maps
  compatible with the inclusions (`TauCeti.subcomplexSmallHomologyIso_naturality`).
* `TauCeti.quasiIso_chainComplexMap_homOfLE_inf_smallSingularSubcomplex`: that inclusion is a
  quasi-isomorphism.

## References

* A. Hatcher, *Algebraic Topology*, Section 2.1, Proposition 2.21.
* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Chapter 18, proof of Theorem 18.7.
-/

public section

noncomputable section

open CategoryTheory Limits Convexity Simplicial AlgebraicTopology SSet.Subcomplex

universe w v u

namespace TauCeti

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasCoproducts.{w} C] (R : C)
  {X : TopCat.{w}} (S : (TopCat.toSSet.obj X).Subcomplex) [S.IsAffineStable]
  {ι : Type*} (U : ι → Set X)

namespace AffineChain

/-- Pushing forward an affine chain along a simplex of an affinely stable subcomplex `S` gives a
chain of the simplices of `S` subordinate to `U`, provided each affine simplex of the chain is
carried into a member of `U`. -/
theorem subcomplexChain_mem_chainRange {m k : ℕ} (σ : (S : SSet) _⦋m⦌)
    (c : (Fin (k + 1) → StdSimplex ℝ (Fin (m + 1))) →₀ ℤ)
    (hc : ∀ v ∈ c.support, ∃ i,
      Set.range ((X.toSSetObjEquiv _ σ.val).comp (StdSimplex.continuousAffineMapMk v)) ⊆ U i) :
    subcomplexChain R S σ k c ∈
      chainRange R (homOfLE (inf_le_left : S ⊓ X.smallSingularSubcomplex U ≤ S)) k := by
  rw [← c.sum_single, map_finsuppSum]
  refine AddSubgroup.sum_mem _ fun v hv ↦ ?_
  dsimp only
  rw [subcomplexChain_single]
  refine AddSubgroup.zsmul_mem _ ((mem_chainRange_iff _).2
    ⟨((S ⊓ X.smallSingularSubcomplex U : (TopCat.toSSet.obj X).Subcomplex) : SSet).ιChainComplex
      ⟨(X.toSSetObjEquiv _).symm
        ((X.toSSetObjEquiv _ σ.val).comp (StdSimplex.continuousAffineMapMk v)),
        IsAffineStable.comp_affineMapMk_mem σ.property v, by
          rw [TopCat.mem_smallSingularSubcomplex_iff, Equiv.apply_symm_apply]
          exact hc v hv⟩, ?_⟩) _
  rw [SSet.ι_chainComplexMap_f]
  exact congrArg _ (Subtype.ext (homOfLE_app_val _ _ _))

end AffineChain

open AffineChain

/-- Iterated subdivision of a simplex of an affinely stable subcomplex is the push-forward of the
iterated subdivision of the standard simplex. -/
lemma ιChainComplex_comp_subcomplexSubdivisionChainMap_pow_f {k : ℕ} (σ : (S : SSet) _⦋k⦌)
    (n : ℕ) :
    (S : SSet).ιChainComplex σ ≫ (End.of (subcomplexSubdivisionChainMap R S) ^ n).asHom.f k =
      subcomplexChain R S σ k ((subdivision _ k)^[n] (simplex k)) := by
  apply (cancel_mono ((SSet.chainComplexMap S.ι R).f k)).1
  rw [Category.assoc, subcomplexSubdivisionChainMap_pow_f_ι, SSet.ι_chainComplexMap_f_assoc,
    subcomplexChain_ι, singularChain_subdivision_iterate, singularChain_simplex]
  simp

/-- For an open cover, a sufficiently fine iterated barycentric subdivision of each simplex of an
affinely stable subcomplex `S` is a chain of the simplices of `S` subordinate to the cover. -/
theorem exists_ιChainComplex_comp_subcomplexSubdivisionChainMap_pow_mem_chainRange
    (hU : ∀ i, IsOpen (U i)) (hcov : ⋃ i, U i = Set.univ) {k : ℕ} (σ : (S : SSet) _⦋k⦌) :
    ∃ n, (S : SSet).ιChainComplex σ ≫
        (End.of (subcomplexSubdivisionChainMap R S) ^ n).asHom.f k ∈
      chainRange R (homOfLE (inf_le_left : S ⊓ X.smallSingularSubcomplex U ≤ S)) k := by
  obtain ⟨n, hn⟩ := ContinuousMap.exists_forall_mem_support_subdivision_iterate_range_subset
    (X.toSSetObjEquiv _ σ.val) hU hcov k
  refine ⟨n, ?_⟩
  rw [ιChainComplex_comp_subcomplexSubdivisionChainMap_pow_f]
  exact subcomplexChain_mem_chainRange R S U σ _ (hn n le_rfl (simplex k))

variable {R S} in
/-- Restricted barycentric subdivision of the chains of `S` preserves the chains of every affinely
stable subcomplex `T ≤ S`, such as the simplices of `S` subordinate to an open cover. -/
lemma comp_subcomplexSubdivisionX_mem_chainRange {T : (TopCat.toSSet.obj X).Subcomplex}
    [T.IsAffineStable] (hTS : T ≤ S) {n : ℕ} {f : R ⟶ ((S : SSet).chainComplex R).X n}
    (hf : f ∈ chainRange R (homOfLE hTS) n) :
    f ≫ subcomplexSubdivisionX R S n ∈ chainRange R (homOfLE hTS) n := by
  obtain ⟨g, rfl⟩ := (mem_chainRange_iff _).1 hf
  refine (mem_chainRange_iff _).2 ⟨g ≫ subcomplexSubdivisionX R T n, ?_⟩
  rw [Category.assoc, Category.assoc, ← subcomplexSubdivisionChainMap_f,
    ← subcomplexSubdivisionChainMap_f, ← HomologicalComplex.comp_f, ← HomologicalComplex.comp_f,
    subcomplexSubdivisionChainMap_naturality R T S (𝟙 X) _ (by simp)]

variable {R S} in
/-- The restricted prism operator of the chains of `S` preserves the chains of every affinely
stable subcomplex `T ≤ S`, such as the simplices of `S` subordinate to an open cover. -/
lemma comp_subcomplexPrismX_mem_chainRange {T : (TopCat.toSSet.obj X).Subcomplex}
    [T.IsAffineStable] (hTS : T ≤ S) {n : ℕ} {f : R ⟶ ((S : SSet).chainComplex R).X n}
    (hf : f ∈ chainRange R (homOfLE hTS) n) :
    f ≫ subcomplexPrismX R S n ∈ chainRange R (homOfLE hTS) (n + 1) := by
  obtain ⟨g, rfl⟩ := (mem_chainRange_iff _).1 hf
  refine (mem_chainRange_iff _).2 ⟨g ≫ subcomplexPrismX R T n, ?_⟩
  rw [Category.assoc, Category.assoc, subcomplexPrismX_naturality R T S (𝟙 X) _ (by simp)]

variable (hU : ∀ i, IsOpen (U i)) (hcov : ⋃ i, U i = Set.univ)

include hU hcov

/-- **The small-chain theorem on an affinely stable subcomplex.** For an open cover `U` of `X`
and an affinely stable subcomplex `S` of the singular simplicial set of `X`, the inclusion of the
chains of the simplices of `S` subordinate to `U` into the chains of `S` is a chain homotopy
equivalence, whose homotopy inverse is even a strict retraction. -/
def subcomplexSmallChainHomotopyEquiv :
    HomotopyEquiv
      (((S ⊓ X.smallSingularSubcomplex U : (TopCat.toSSet.obj X).Subcomplex) : SSet).chainComplex R)
      ((S : SSet).chainComplex R) :=
  chainComplexMapHomotopyEquivOfSubdivision (R := R)
    (i := homOfLE (inf_le_left : S ⊓ X.smallSingularSubcomplex U ≤ S))
    (h := subcomplexSubdivisionHomotopy R S)
    (fun _ _ hf ↦ by
      simpa only [subcomplexSubdivisionChainMap_f] using
        comp_subcomplexSubdivisionX_mem_chainRange inf_le_left hf)
    (fun _ _ hf ↦ by
      simpa only [subcomplexSubdivisionHomotopy_hom] using
        comp_subcomplexPrismX_mem_chainRange inf_le_left hf)
    (fun _ σ ↦ exists_ιChainComplex_comp_subcomplexSubdivisionChainMap_pow_mem_chainRange
      R S U hU hcov σ)

/-- The forward map of the small-chain homotopy equivalence of an affinely stable subcomplex is the
inclusion of the chains subordinate to the cover. -/
@[simp]
lemma subcomplexSmallChainHomotopyEquiv_hom :
    (subcomplexSmallChainHomotopyEquiv R S U hU hcov).hom =
      SSet.chainComplexMap (homOfLE (inf_le_left : S ⊓ X.smallSingularSubcomplex U ≤ S)) R :=
  chainComplexMapHomotopyEquivOfSubdivision_hom _ _ _

/-- The homotopy inverse of the small-chain homotopy equivalence of an affinely stable subcomplex
is a strict retraction of the inclusion of the chains subordinate to the cover. -/
@[reassoc (attr := simp)]
lemma chainComplexMap_comp_subcomplexSmallChainHomotopyEquiv_inv :
    SSet.chainComplexMap (homOfLE (inf_le_left : S ⊓ X.smallSingularSubcomplex U ≤ S)) R ≫
      (subcomplexSmallChainHomotopyEquiv R S U hU hcov).inv = 𝟙 _ := by
  rw [subcomplexSmallChainHomotopyEquiv, chainComplexMapHomotopyEquivOfSubdivision_inv,
    chainComplexMap_comp_subdivisionRetraction]

/-- The isomorphism on homology induced by the inclusion of the chains of an affinely stable
subcomplex subordinate to an open cover. Since that inclusion is natural, so is this isomorphism,
whereas the homotopy inverse underlying it is not. -/
def subcomplexSmallHomologyIso [CategoryWithHomology C] (n : ℕ) :
    (((S ⊓ X.smallSingularSubcomplex U : (TopCat.toSSet.obj X).Subcomplex) :
      SSet).chainComplex R).homology n ≅ ((S : SSet).chainComplex R).homology n :=
  (subcomplexSmallChainHomotopyEquiv R S U hU hcov).toHomologyIso n

@[simp]
lemma subcomplexSmallHomologyIso_hom [CategoryWithHomology C] (n : ℕ) :
    (subcomplexSmallHomologyIso R S U hU hcov n).hom = HomologicalComplex.homologyMap
      (SSet.chainComplexMap (homOfLE (inf_le_left : S ⊓ X.smallSingularSubcomplex U ≤ S)) R) n :=
  congrArg (HomologicalComplex.homologyMap · n)
    (subcomplexSmallChainHomotopyEquiv_hom R S U hU hcov)

/-- The small-chain homology isomorphism of an affinely stable subcomplex is natural under maps of
simplicial sets compatible with the inclusions of the chains subordinate to the covers. -/
lemma subcomplexSmallHomologyIso_naturality [CategoryWithHomology C]
    {Y : TopCat.{w}} (S' : (TopCat.toSSet.obj Y).Subcomplex) [S'.IsAffineStable]
    {κ : Type*} (V : κ → Set Y) (hV : ∀ j, IsOpen (V j)) (hcovV : ⋃ j, V j = Set.univ)
    (f : ((S ⊓ X.smallSingularSubcomplex U : (TopCat.toSSet.obj X).Subcomplex) : SSet) ⟶
      ((S' ⊓ Y.smallSingularSubcomplex V : (TopCat.toSSet.obj Y).Subcomplex) : SSet))
    (g : (S : SSet) ⟶ (S' : SSet))
    (hfg : f ≫ homOfLE inf_le_left = homOfLE inf_le_left ≫ g) (n : ℕ) :
    (subcomplexSmallHomologyIso R S U hU hcov n).hom ≫
        HomologicalComplex.homologyMap (SSet.chainComplexMap g R) n =
      HomologicalComplex.homologyMap (SSet.chainComplexMap f R) n ≫
        (subcomplexSmallHomologyIso R S' V hV hcovV n).hom := by
  rw [subcomplexSmallHomologyIso_hom, subcomplexSmallHomologyIso_hom,
    ← HomologicalComplex.homologyMap_comp, ← HomologicalComplex.homologyMap_comp,
    ← Functor.map_comp, ← Functor.map_comp, hfg]

/-- The inclusion of the chains of an affinely stable subcomplex subordinate to an open cover into
all of its chains is a quasi-isomorphism. -/
theorem quasiIso_chainComplexMap_homOfLE_inf_smallSingularSubcomplex [CategoryWithHomology C] :
    QuasiIso
      (SSet.chainComplexMap (homOfLE (inf_le_left : S ⊓ X.smallSingularSubcomplex U ≤ S)) R) := by
  rw [← subcomplexSmallChainHomotopyEquiv_hom R S U hU hcov]
  exact (subcomplexSmallChainHomotopyEquiv R S U hU hcov).quasiIso_hom

end TauCeti
