/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Convex.Contractible
public import Mathlib.Topology.Homotopy.TopCat.ToSSet
public import TauCeti.AlgebraicTopology.SimplicialSet.Homotopy
public import TauCeti.AlgebraicTopology.Singular.Twisted.Basic
public import TauCeti.CategoryTheory.EqToHom

/-!
# Homotopy invariance of singular homology with local coefficients

Let `H` be a homotopy from `f : X ⟶ Y` to `g : X ⟶ Y` and let `L` be a local coefficient system
on `Y`. The two maps induced on twisted singular chains start from different coefficient systems,
`f⁎L` and `g⁎L`, which `LocalCoefficientSystem.pullbackHomotopyIso` identifies by transport along
the paths `t ↦ H (t, x)`. This file shows that after this identification the two maps are chain
homotopic (`TopCat.Homotopy.twistedChainComplexHomotopy`), so that they agree on twisted homology
(`TopCat.Homotopy.twistedHomologyMap_eq_comp`).

This is the homotopy axiom for homology with local coefficients. The cohomological form is in
`TauCeti.AlgebraicTopology.Cohomology.Twisted.HomotopyInvariance`.

## Main declarations

* `TopCat.Homotopy.twistedChainsHomotopy`: the simplicial homotopy of twisted chains.
* `TopCat.Homotopy.twistedChainComplexHomotopy`: the chain homotopy of twisted chain complexes.
* `TopCat.Homotopy.twistedHomologyMap_eq_comp`: homotopic maps induce the same map on twisted
  homology, up to the identification of the two pullback systems.

## Implementation notes

The argument follows Mathlib's proof of homotopy invariance of untwisted singular homology by
F. Odermatt and J. Riou (`TopCat.Homotopy.singularChainComplexFunctorObjMap` in
`Mathlib/AlgebraicTopology/SingularHomology/HomotopyInvariance.lean`, which goes through
`SSet.Homotopy.chainComplexMap` and `SimplicialObject.Homotopy.sSetChainComplexMap` in
`Mathlib/AlgebraicTopology/SimplicialSet/Homology/HomotopyInvariance.lean`), with coefficients in
a local coefficient system. As there, the chain homotopy is obtained from a simplicial homotopy by
Mathlib's `SimplicialObject.Homotopy.toChainHomotopy` (F. Odermatt), here through
`SimplicialObject.Homotopy.toTwistedChainComplexHomotopy`.

The chain homotopy comes from a simplicial homotopy of twisted chains, which lifts the
combinatorial homotopy `H.toSSet.toSimplicialObjectHomotopy` of singular simplicial sets, obtained
from `TopCat.Homotopy.toSSet` by Mathlib's `SSet.Homotopy.toSimplicialObjectHomotopy` (J. Riou).
That homotopy sends a singular simplex `σ` of `X` to simplices `h i σ` of `Y` which start at the
image under `f` of the initial vertex of `σ`, so the coefficients of `σ` are carried to those of
`h i σ` without transport. The simplicial identities then reduce to the identities of the
combinatorial homotopy, except where the zeroth face moves the initial vertex. There the
coefficient transport runs along the first edge of `h i σ`: for `i ≥ 1` this edge is the image
under `f` of the first edge of `σ`, and for `i = 0` it is the path traced by `H` at the initial
vertex of `σ` (`TopCat.Homotopy.pathTransport_toSimplicialObjectHomotopy_h_zero_heq`), which is
the transport that defines the identification of `f⁎L` with `g⁎L`.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 3.H, for homotopy invariance of homology with local coefficients.
* J. P. May, *Simplicial Objects in Algebraic Topology*, Chapter I, for simplicial homotopies.
-/

public section

noncomputable section

open CategoryTheory SimplexCategory Opposite TauCeti.LocalCoefficientSystem
open scoped Simplicial

universe u v w

namespace TopCat.Homotopy

variable {R : Type u} [Ring R] {X Y : TopCat.{v}} {f g : X ⟶ Y} (H : TopCat.Homotopy f g)

/-- The simplices of the combinatorial homotopy extracted from a homotopy `H` are obtained by
evaluating `H` on a degeneracy of the given simplex and on a parametrization of the unit
interval. -/
lemma simplexMap_toSimplicialObjectHomotopy_h_apply {n : ℕ} (i : Fin (n + 1))
    (x : (TopCat.toSSet.obj X) _⦋n⦌) (p : SimplexCategory.toTop.{v}.obj ⦋n + 1⦌) :
    TauCeti.TopCat.simplexMap (H.toSSet.toSimplicialObjectHomotopy.h i x) p =
      H (TopCat.I.homeomorph (TauCeti.TopCat.simplexMap
          (SSet.stdSimplex.toSSetObjI.app _ (SSet.stdSimplex.objMk₁ i.succ.castSucc)) p),
        TauCeti.TopCat.simplexMap x (SimplexCategory.toTop.map (SimplexCategory.σ i) p)) := by
  -- Unfold `TopCat.Homotopy.toSSet`: the simplex is the image under `H.h` of the simplex of
  -- `X ⊗ I` assembled by the lax monoidal structure of the singular simplicial set functor.
  change H.h (TauCeti.TopCat.simplexMap
    ((Functor.LaxMonoidal.μ TopCat.toSSet X TopCat.I).app _ ⟨_, _⟩) p) = _
  rw [TauCeti.TopCat.simplexMap_μ_apply]
  -- The rest holds by definition, as `TopCat.Homotopy.h_hom_apply` and
  -- `TauCeti.TopCat.simplexMap_map` record: `H.h (a, b) = H (I.homeomorph b, a)`, and the two
  -- components of the simplex of `X ⊗ Δ[1]` attached to `i` are the degeneracy
  -- `X.map (σ i).op x` and `objMk₁ i.succ.castSucc`.
  -- Neither lemma rewrites here, since the pair is typed in `X × I` rather than `X ⊗ I` and the
  -- first component is only definitionally a reindexing.
  rfl

/-- The combinatorial homotopy extracted from a homotopy `H` from `f` to `g` starts every simplex
at the image under `f` of its initial vertex. -/
lemma initialVertex_toSimplicialObjectHomotopy_h {n : ℕ} (i : Fin (n + 1))
    (σ : (TopCat.toSSet.obj X) _⦋n⦌) :
    initialVertex (H.toSSet.toSimplicialObjectHomotopy.h i σ) =
      (FundamentalGroupoid.map f.hom).obj (initialVertex σ) := by
  have h := congr(TauCeti.TopCat.simplexMap
    $(SSet.Homotopy.map_const_toSimplicialObjectHomotopy_h H.toSSet i σ)
    (toTopInitialVertex ⦋0⦌))
  simp only [TauCeti.TopCat.simplexMap_map, TauCeti.TopCat.simplexMap_app,
    ContinuousMap.comp_apply] at h
  rw [toTop_map_toTopInitialVertex _ rfl, toTop_map_toTopInitialVertex _ rfl] at h
  exact congrArg FundamentalGroupoid.mk h

/-- The first edge of the image of a vertex `y` under the combinatorial homotopy extracted from a
homotopy `H` runs along the path `t ↦ H (t, y)`. -/
lemma pathTransport_toSimplicialObjectHomotopy_h_zero_heq (y : (TopCat.toSSet.obj X) _⦋0⦌) :
    pathTransport (H.toSSet.toSimplicialObjectHomotopy.h 0 y) (toTopInitialVertex ⦋1⦌)
        (toTop.map (δ 0) (toTopInitialVertex ⦋0⦌)) ≍
      (⟦H.evalAt (TauCeti.TopCat.simplexMap y (toTopInitialVertex ⦋0⦌))⟧ :
        FundamentalGroupoid.mk (f (TauCeti.TopCat.simplexMap y (toTopInitialVertex ⦋0⦌))) ⟶
          FundamentalGroupoid.mk (g (TauCeti.TopCat.simplexMap y (toTopInitialVertex ⦋0⦌)))) := by
  have : ContractibleSpace unitInterval := (convex_Icc (0 : ℝ) 1).contractibleSpace ⟨0, by simp⟩
  set x := TauCeti.TopCat.simplexMap y (toTopInitialVertex ⦋0⦌)
  -- The simplex factors through the unit interval, through the parametrization `ψ` of `Δ[1]`.
  let ψ : C(toTop.{v}.obj ⦋1⦌, unitInterval) :=
    ⟨fun p ↦ TopCat.I.homeomorph (TauCeti.TopCat.simplexMap
      (SSet.stdSimplex.toSSetObjI.app (op ⦋1⦌) (SSet.stdSimplex.objMk₁ 1)) p), by fun_prop⟩
  let Γ : C(unitInterval, Y) := ⟨fun t ↦ H (t, x), by fun_prop⟩
  have hF : TauCeti.TopCat.simplexMap (H.toSSet.toSimplicialObjectHomotopy.h 0 y) =
      Γ.comp ψ := by
    ext p
    rw [simplexMap_toSimplicialObjectHomotopy_h_apply]
    exact congrArg (fun z ↦ H (_, TauCeti.TopCat.simplexMap y z)) (Subsingleton.elim _ _)
  have hz : ψ (toTopInitialVertex ⦋1⦌) = 0 :=
    TauCeti.TopCat.homeomorph_simplexMap_toSSetObjI_toTopInitialVertex
  have hw : ψ (toTop.map (δ 0) (toTopInitialVertex ⦋0⦌)) = 1 :=
    TauCeti.TopCat.homeomorph_simplexMap_toSSetObjI_toTop_map_δ_zero
  let path01 : Path (0 : unitInterval) 1 := ⟨ContinuousMap.id _, rfl, rfl⟩
  rw [pathTransport_def, hF, FundamentalGroupoid.map_comp_map,
    Subsingleton.elim ((FundamentalGroupoid.map ψ).map _) ⟦path01.cast hz hw⟧]
  refine HEq.trans (heq_of_eq ?_) (Path.Homotopic.Quotient.cast_heq
    ((congrArg (fun t ↦ H (t, x)) hz).trans (H.apply_zero x))
    ((congrArg (fun t ↦ H (t, x)) hw).trans (H.apply_one x)))
  exact congrArg _ (Path.ext rfl)

/-- On the summand of a simplex `σ` with at least one edge, the transport along the zeroth face of
the simplex `h (j + 1) σ` of the combinatorial homotopy is the image under `f` of the transport
along the zeroth face of `σ`. -/
lemma vertexTransport_δ_zero_toSimplicialObjectHomotopy_h_succ_heq {k : ℕ} (j : Fin (k + 1))
    (σ : (TopCat.toSSet.obj X) _⦋k + 1⦌) :
    vertexTransport (δ 0).op (H.toSSet.toSimplicialObjectHomotopy.h j.succ σ) ≍
      (FundamentalGroupoid.map f.hom).map (vertexTransport (δ 0).op σ) := by
  refine (vertexTransport_δ_zero_heq _).trans ?_
  refine (pathTransport_heq
    (SSet.Homotopy.map_mkOfLe_toSimplicialObjectHomotopy_h_succ H.toSSet j σ) rfl rfl).trans ?_
  rw [← map_pathTransport]
  refine Functor.map_heq _ ?_ ?_ (vertexTransport_δ_zero_heq σ).symm
  · exact congrArg (fun z ↦ (⟨TauCeti.TopCat.simplexMap σ z⟩ : FundamentalGroupoid X))
      (toTop_map_mkOfLe_toTopInitialVertex k)
  · exact congrArg (fun z ↦ (⟨TauCeti.TopCat.simplexMap σ z⟩ : FundamentalGroupoid X))
      (toTop_map_mkOfLe_toTop_map_δ_zero k)

/-- On the summand of a simplex `σ`, the transport along the zeroth face of the simplex `h 0 σ` of
the combinatorial homotopy is transport along the path traced by `H` at the initial vertex of
`σ`. -/
lemma vertexTransport_δ_zero_toSimplicialObjectHomotopy_h_zero_heq {k : ℕ}
    (σ : (TopCat.toSSet.obj X) _⦋k⦌) :
    vertexTransport (δ 0).op (H.toSSet.toSimplicialObjectHomotopy.h 0 σ) ≍
      (⟦H.evalAt (TauCeti.TopCat.simplexMap σ (toTopInitialVertex ⦋k⦌))⟧ :
        FundamentalGroupoid.mk (f (TauCeti.TopCat.simplexMap σ (toTopInitialVertex ⦋k⦌))) ⟶
          FundamentalGroupoid.mk (g (TauCeti.TopCat.simplexMap σ (toTopInitialVertex ⦋k⦌)))) := by
  refine (vertexTransport_δ_zero_heq _).trans ?_
  refine (pathTransport_heq
    (SSet.Homotopy.map_mkOfLe_toSimplicialObjectHomotopy_h_zero H.toSSet σ) rfl rfl).trans ?_
  refine (pathTransport_toSimplicialObjectHomotopy_h_zero_heq H _).trans ?_
  have hx : TauCeti.TopCat.simplexMap
      ((TopCat.toSSet.obj X).map (SimplexCategory.const ⦋0⦌ ⦋k⦌ 0).op σ)
      (toTopInitialVertex ⦋0⦌) = TauCeti.TopCat.simplexMap σ (toTopInitialVertex ⦋k⦌) :=
    congrArg (TauCeti.TopCat.simplexMap σ) (toTop_map_toTopInitialVertex _ rfl)
  rw [hx]

variable (L : TauCeti.LocalCoefficientSystem.{u, v, max v w} R Y)

/-- The coefficient module of the pullback system at the initial vertex of a simplex is the
coefficient module at the initial vertex of its image under the combinatorial homotopy. -/
lemma obj_initialVertex_toSimplicialObjectHomotopy_h {n : ℕ} (i : Fin (n + 1))
    (σ : (TopCat.toSSet.obj X) _⦋n⦌) :
    ((pullback f.hom).obj L).obj (initialVertex σ) =
      L.obj (initialVertex (H.toSSet.toSimplicialObjectHomotopy.h i σ)) :=
  congrArg L.obj (initialVertex_toSimplicialObjectHomotopy_h H i σ).symm

/-- The components of the simplicial homotopy of twisted chains induced by a homotopy. -/
private def twistedChainsHomotopyApp {n : ℕ} (i : Fin (n + 1)) :
    (twistedChains ((pullback f.hom).obj L)) _⦋n⦌ ⟶ (twistedChains L) _⦋n + 1⦌ :=
  twistedChainsDesc _ fun σ ↦ eqToHom (obj_initialVertex_toSimplicialObjectHomotopy_h H L i σ) ≫
    ιTwistedChains L (H.toSSet.toSimplicialObjectHomotopy.h i σ)

@[reassoc]
private lemma ιTwistedChains_twistedChainsHomotopyApp {n : ℕ} (i : Fin (n + 1))
    (σ : (TopCat.toSSet.obj X) _⦋n⦌) :
    ιTwistedChains ((pullback f.hom).obj L) σ ≫ twistedChainsHomotopyApp H L i =
      eqToHom (obj_initialVertex_toSimplicialObjectHomotopy_h H L i σ) ≫
        ιTwistedChains L (H.toSSet.toSimplicialObjectHomotopy.h i σ) :=
  ιTwistedChains_twistedChainsDesc _ _ _

/-- A homotopy `H` from `f` to `g` induces a simplicial homotopy from the morphism of twisted
chains induced by `f` to the morphism induced by `g`, preceded by the identification of the
pullback systems along `H`. It sends the summand of a simplex `σ` identically onto the summand of
the simplex `h i σ` of the combinatorial homotopy `H.toSSet.toSimplicialObjectHomotopy`. -/
def twistedChainsHomotopy :
    SimplicialObject.Homotopy (twistedChainsMap f L)
      (twistedChainsCoefficientMap ((pullbackHomotopyIso H).hom.app L) ≫ twistedChainsMap g L)
    where
  h i := twistedChainsHomotopyApp H L i
  -- Every face and degeneracy other than the zeroth face fixes the initial vertex, so those
  -- identities reduce to the identities of the combinatorial homotopy; the two identities
  -- involving the zeroth face transport the coefficients along the first edge.
  h_zero_comp_δ_zero n := by
    refine twistedChains_hom_ext _ fun σ ↦ ?_
    simp only [SimplicialObject.δ, NatTrans.comp_app, ιTwistedChains_twistedChainsHomotopyApp_assoc,
      ιTwistedChains_twistedChainsMap_app, ιTwistedChains_twistedChainsCoefficientMap_app_assoc,
      ιTwistedChains_map, pullbackHomotopyIso_hom_app_app]
    have hτ := congr($(H.toSSet.toSimplicialObjectHomotopy.h_zero_comp_δ_zero n) σ)
    rw [← Category.assoc]
    exact comp_ιTwistedChains_eq_of_heq L hτ ((eqToHom_comp_heq _ _).trans (Functor.map_heq L
      (initialVertex_toSimplicialObjectHomotopy_h H 0 σ) (congrArg initialVertex hτ)
      (vertexTransport_δ_zero_toSimplicialObjectHomotopy_h_zero_heq H σ)))
  h_last_comp_δ_last n := by
    refine twistedChains_hom_ext _ fun σ ↦ ?_
    simp only [SimplicialObject.δ, ιTwistedChains_twistedChainsHomotopyApp_assoc,
      ιTwistedChains_twistedChainsMap_app, ιTwistedChains_map_δ_of_ne_zero L Fin.last_pos.ne']
    rw [eqToHom_trans_assoc]
    exact (eqToHom_comp_ιTwistedChains_eq L
      congr($(H.toSSet.toSimplicialObjectHomotopy.h_last_comp_δ_last n) σ) _ rfl).trans
      (Category.id_comp _)
  h_succ_comp_δ_castSucc_of_lt i j hij := by
    refine twistedChains_hom_ext _ fun σ ↦ ?_
    have hτ := congr($(H.toSSet.toSimplicialObjectHomotopy.h_succ_comp_δ_castSucc_of_lt i j hij) σ)
    obtain rfl | hi := eq_or_ne i 0
    · -- The zeroth face moves the initial vertex: transport along the first edge.
      simp only [SimplicialObject.δ, ιTwistedChains_twistedChainsHomotopyApp_assoc,
        ιTwistedChains_map_assoc, ιTwistedChains_map, ιTwistedChains_twistedChainsHomotopyApp]
      rw [← Category.assoc, ← Category.assoc]
      exact comp_ιTwistedChains_eq_of_heq L hτ ((eqToHom_comp_heq _ _).trans ((Functor.map_heq L
        (initialVertex_toSimplicialObjectHomotopy_h H j.succ σ)
        ((congrArg initialVertex hτ).trans (initialVertex_toSimplicialObjectHomotopy_h H j _))
        (vertexTransport_δ_zero_toSimplicialObjectHomotopy_h_succ_heq H j σ)).trans
        (comp_eqToHom_heq _ _).symm))
    · simp only [SimplicialObject.δ, ιTwistedChains_twistedChainsHomotopyApp_assoc,
        ιTwistedChains_map_δ_of_ne_zero L (Fin.castSucc_ne_zero_iff.mpr hi),
        ιTwistedChains_map_δ_of_ne_zero_assoc _ hi, ιTwistedChains_twistedChainsHomotopyApp]
      rw [eqToHom_trans_assoc, eqToHom_trans_assoc]
      exact eqToHom_comp_ιTwistedChains_eq L hτ _ _
  h_succ_comp_δ_castSucc_succ j := by
    refine twistedChains_hom_ext _ fun σ ↦ ?_
    simp only [SimplicialObject.δ, ιTwistedChains_twistedChainsHomotopyApp_assoc,
      ιTwistedChains_map_δ_of_ne_zero L (Fin.succ_ne_zero _)]
    rw [eqToHom_trans_assoc, eqToHom_trans_assoc]
    exact eqToHom_comp_ιTwistedChains_eq L
      congr($(H.toSSet.toSimplicialObjectHomotopy.h_succ_comp_δ_castSucc_succ j) σ) _ _
  h_castSucc_comp_δ_succ_of_lt i j hji := by
    refine twistedChains_hom_ext _ fun σ ↦ ?_
    have hi : i ≠ 0 := by
      rintro rfl
      exact Fin.not_lt_zero _ hji
    simp only [SimplicialObject.δ, ιTwistedChains_twistedChainsHomotopyApp_assoc,
      ιTwistedChains_map_δ_of_ne_zero L (Fin.succ_ne_zero _),
      ιTwistedChains_map_δ_of_ne_zero_assoc _ hi, ιTwistedChains_twistedChainsHomotopyApp]
    rw [eqToHom_trans_assoc, eqToHom_trans_assoc]
    exact eqToHom_comp_ιTwistedChains_eq L
      congr($(H.toSSet.toSimplicialObjectHomotopy.h_castSucc_comp_δ_succ_of_lt i j hji) σ) _ _
  h_comp_σ_castSucc_of_le i j hij := by
    refine twistedChains_hom_ext _ fun σ ↦ ?_
    simp only [SimplicialObject.σ, ιTwistedChains_twistedChainsHomotopyApp_assoc,
      ιTwistedChains_map_σ, ιTwistedChains_map_σ_assoc, ιTwistedChains_twistedChainsHomotopyApp]
    rw [eqToHom_trans_assoc, eqToHom_trans_assoc]
    exact eqToHom_comp_ιTwistedChains_eq L
      congr($(H.toSSet.toSimplicialObjectHomotopy.h_comp_σ_castSucc_of_le i j hij) σ) _ _
  h_comp_σ_succ_of_lt i j hji := by
    refine twistedChains_hom_ext _ fun σ ↦ ?_
    simp only [SimplicialObject.σ, ιTwistedChains_twistedChainsHomotopyApp_assoc,
      ιTwistedChains_map_σ, ιTwistedChains_map_σ_assoc, ιTwistedChains_twistedChainsHomotopyApp]
    rw [eqToHom_trans_assoc, eqToHom_trans_assoc]
    exact eqToHom_comp_ιTwistedChains_eq L
      congr($(H.toSSet.toSimplicialObjectHomotopy.h_comp_σ_succ_of_lt i j hji) σ) _ _

/-- The simplicial homotopy of twisted chains sends the summand of a simplex `σ` identically onto
the summand of the simplex `h i σ` of the combinatorial homotopy. -/
@[reassoc (attr := simp)]
lemma ιTwistedChains_twistedChainsHomotopy_h {n : ℕ} (i : Fin (n + 1))
    (σ : (TopCat.toSSet.obj X) _⦋n⦌) :
    ιTwistedChains ((pullback f.hom).obj L) σ ≫ (H.twistedChainsHomotopy L).h i =
      eqToHom (obj_initialVertex_toSimplicialObjectHomotopy_h H L i σ) ≫
        ιTwistedChains L (H.toSSet.toSimplicialObjectHomotopy.h i σ) :=
  ιTwistedChains_twistedChainsHomotopyApp H L i σ

/-- A homotopy `H` from `f` to `g` induces a chain homotopy from the map of twisted chain
complexes induced by `f` to the map induced by `g`, preceded by the identification of the pullback
systems along `H`. -/
def twistedChainComplexHomotopy :
    _root_.Homotopy (twistedChainComplexMap f L)
      (twistedChainComplexCoefficientMap ((pullbackHomotopyIso H).hom.app L) ≫
        twistedChainComplexMap g L) :=
  (H.twistedChainsHomotopy L).toTwistedChainComplexHomotopy

/-- **Homotopy invariance of homology with local coefficients**: homotopic maps induce the same map
on twisted singular homology, after the identification of the two pullback systems by transport
along the homotopy. -/
lemma twistedHomologyMap_eq_comp (k : ℕ) :
    twistedHomologyMap f L k =
      twistedHomologyCoefficientMap ((pullbackHomotopyIso H).hom.app L) k ≫
        twistedHomologyMap g L k :=
  ((H.twistedChainComplexHomotopy L).homologyMap_eq k).trans
    (HomologicalComplex.homologyMap_comp _ _ k)

end TopCat.Homotopy
