/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicTopology.SingularHomology.Basic
public import Mathlib.CategoryTheory.Limits.MonoCoprod
public import TauCeti.AlgebraicTopology.FundamentalGroupoid.Basic
public import TauCeti.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
public import TauCeti.AlgebraicTopology.LocalCoefficient
public import TauCeti.AlgebraicTopology.TopologicalSimplex

/-!
# Singular chains with local coefficients

A local coefficient system `L` on a space `X` is a functor from its fundamental groupoid to
modules, so it assigns a module to every point and a transport isomorphism to every path class.
Twisting the singular chain complex by `L` replaces the free module on the singular `n`-simplices
by the coproduct, over singular `n`-simplices `σ`, of the fibre of `L` at the initial vertex of
`σ`.  Reindexing a simplex moves its initial vertex inside the simplex, so the structure maps of
the resulting simplicial module also transport the coefficients along the image of a path joining
the old initial vertex to the new one.

The topological simplex is simply connected, so that path class, and hence the transport, is
determined by its endpoints alone.  This is what makes the simplicial identities hold: a
composite of transports is again the transport between its endpoints, and the boundary of a
twisted chain complex therefore squares to zero for the same formal reason as in the untwisted
case.

For a constant system the twisting is trivial and the construction returns Mathlib's singular
chain complex, while a continuous map `f : X ⟶ Y` induces a chain map from the chains of `X`
twisted by the system pulled back along `f`.

## Main declarations

* `TauCeti.LocalCoefficientSystem.twistedChains`: the simplicial module of twisted chains, and
  `twistedChainComplex`, `twistedHomology` for its alternating face map complex and homology.
* `TauCeti.LocalCoefficientSystem.twistedChainsFunctor`: twisted chains as a functor of the
  coefficient system, with `twistedChainComplexCoefficientMap` and
  `twistedHomologyCoefficientMap` for the induced maps of complexes and of homology, together
  with their identity and composition laws.
* `TauCeti.LocalCoefficientSystem.twistedHomologyConstantIso`: for a constant system, twisted
  homology is ordinary singular homology, naturally both in the module of coefficients and in the
  space.
* `TauCeti.LocalCoefficientSystem.twistedChainComplexMap`: the chain map induced by a continuous
  map, and `twistedHomologyMap` the resulting map on twisted homology, together with their
  identity and composition laws and their naturality in the coefficient system.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 3.H.
-/

public section

noncomputable section

open CategoryTheory Limits Convexity SimplexCategory

open scoped Simplicial

universe u v w

namespace TauCeti

namespace LocalCoefficientSystem

variable {R : Type u} [Ring R] {X Y : TopCat.{v}} {m n p : SimplexCategoryᵒᵖ}

/-- The initial vertex of a singular simplex, as an object of the fundamental groupoid. -/
-- This is an `abbrev` so that the coefficient module attached to a simplex stays transparent to
-- unification.
abbrev initialVertex (σ : (TopCat.toSSet.obj X).obj n) : FundamentalGroupoid X :=
  ⟨TopCat.simplexMap σ (toTopInitialVertex n.unop)⟩

/-- The morphism of the fundamental groupoid of `X` obtained by running a singular simplex along
the unique path class between two points of its simplex. -/
def pathTransport (σ : (TopCat.toSSet.obj X).obj n) (z w : toTop.{v}.obj n.unop) :
    (⟨TopCat.simplexMap σ z⟩ : FundamentalGroupoid X) ⟶ ⟨TopCat.simplexMap σ w⟩ :=
  (FundamentalGroupoid.map (TopCat.simplexMap σ)).map
    (default : (⟨z⟩ : FundamentalGroupoid (toTop.{v}.obj n.unop)) ⟶ ⟨w⟩)

/-- Transport inside a simplex from a point to itself is the identity. -/
@[simp]
lemma pathTransport_self (σ : (TopCat.toSSet.obj X).obj n) (z : toTop.{v}.obj n.unop) :
    pathTransport σ z z = 𝟙 _ :=
  Functor.map_default_self _ _

/-- Transports inside a simplex compose: running from `z` to `w` and then from `w` to `y` is
running from `z` to `y`. -/
@[reassoc (attr := simp)]
lemma pathTransport_comp (σ : (TopCat.toSSet.obj X).obj n)
    (z w y : toTop.{v}.obj n.unop) :
    pathTransport σ z w ≫ pathTransport σ w y = pathTransport σ z y :=
  Functor.map_default_comp _ _ _ _

/-- Transport inside a simplex may be moved along an equality of its target point. -/
@[reassoc]
lemma pathTransport_eqToHom (σ : (TopCat.toSSet.obj X).obj n) (z : toTop.{v}.obj n.unop)
    {w w' : toTop.{v}.obj n.unop} (h : w = w') :
    pathTransport σ z w ≫
        eqToHom (congrArg (fun y ↦ (⟨TopCat.simplexMap σ y⟩ : FundamentalGroupoid X)) h) =
      pathTransport σ z w' := by
  subst h
  simp

/-- Transport inside a reindexed simplex is transport inside the original simplex, between the
images of the two points under the reindexing. -/
lemma pathTransport_map (α : m ⟶ n) (σ : (TopCat.toSSet.obj X).obj m)
    (z w : toTop.{v}.obj n.unop) :
    pathTransport ((TopCat.toSSet.obj X).map α σ) z w =
      pathTransport σ (toTop.map α.unop z) (toTop.map α.unop w) := by
  have h : ((FundamentalGroupoid.map (toTop.map α.unop).hom).map
        (default : (⟨z⟩ : FundamentalGroupoid (toTop.{v}.obj n.unop)) ⟶ ⟨w⟩) :
      (⟨toTop.map α.unop z⟩ : FundamentalGroupoid (toTop.{v}.obj m.unop)) ⟶
        ⟨toTop.map α.unop w⟩) = default := Subsingleton.elim _ _
  exact (FundamentalGroupoid.map_comp_map _ _ _).trans (congrArg _ h)

/-- Pushing a singular simplex forward along a continuous map carries transport inside it to
transport inside the image simplex. -/
lemma map_pathTransport (f : X ⟶ Y) (σ : (TopCat.toSSet.obj X).obj n)
    (z w : toTop.{v}.obj n.unop) :
    (FundamentalGroupoid.map f.hom).map (pathTransport σ z w) =
      pathTransport ((TopCat.toSSet.map f).app n σ) z w :=
  (FundamentalGroupoid.map_comp_map _ _ _).symm

section Chains

variable (L : LocalCoefficientSystem.{u, v, max v w} R X)

/-- The transport from the initial vertex of a singular `m`-simplex `σ` to the initial vertex of
the singular `n`-simplex obtained from `σ` by reindexing along `α`. -/
def vertexTransport (α : m ⟶ n) (σ : (TopCat.toSSet.obj X).obj m) :
    initialVertex σ ⟶ initialVertex ((TopCat.toSSet.obj X).map α σ) :=
  pathTransport σ (toTopInitialVertex m.unop) (toTop.map α.unop (toTopInitialVertex n.unop))

/-- Reindexing along an identity does not move the initial vertex, so the transport it induces is
the canonical identification of the two coefficient modules. -/
lemma vertexTransport_id (σ : (TopCat.toSSet.obj X).obj n) :
    vertexTransport (𝟙 n) σ = eqToHom (by simp) := by
  have hz : toTopInitialVertex n.unop =
      toTop.{v}.map (𝟙 n).unop (toTopInitialVertex n.unop) := by
    rw [unop_id, CategoryTheory.Functor.map_id]
    rfl
  simp only [vertexTransport, ← pathTransport_eqToHom σ (toTopInitialVertex n.unop) hz,
    pathTransport_self, Category.id_comp]
  -- Both sides are now `eqToHom` between the same two objects; proof irrelevance finishes.
  rfl

/-- Reindexing along a composite induces the composite of the two vertex transports, up to the
canonical identification of the two resulting simplices. -/
lemma vertexTransport_comp (α : m ⟶ n) (β : n ⟶ p)
    (σ : (TopCat.toSSet.obj X).obj m) :
    vertexTransport α σ ≫ vertexTransport β ((TopCat.toSSet.obj X).map α σ) =
      vertexTransport (α ≫ β) σ ≫ eqToHom (by simp) := by
  have hz : toTop.{v}.map (α ≫ β).unop (toTopInitialVertex p.unop) =
      toTop.{v}.map α.unop (toTop.{v}.map β.unop (toTopInitialVertex p.unop)) := by
    rw [unop_comp, CategoryTheory.Functor.map_comp]
    rfl
  simp only [vertexTransport, pathTransport_map]
  exact (pathTransport_comp σ _ _ _).trans
    (pathTransport_eqToHom σ (toTopInitialVertex m.unop) hz).symm

/-- The simplicial object of singular chains of `X` twisted by the local coefficient system `L`.
In degree `n` it is the coproduct, over the singular `n`-simplices `σ` of `X`, of the fibre of
`L` at the initial vertex of `σ`; a reindexing acts on the summands by transport along the
initial vertices. -/
def twistedChains : SimplicialObject (ModuleCat.{max v w} R) where
  obj n := ∐ fun σ : (TopCat.toSSet.obj X).obj n ↦ L.obj (initialVertex σ)
  map {m n} α :=
    Sigma.map' ((TopCat.toSSet.obj X).map α) fun σ ↦ L.map (vertexTransport α σ)
  map_id n := by
    refine Sigma.hom_ext _ _ fun σ ↦ ?_
    have hσ : σ = (TopCat.toSSet.obj X).map (𝟙 n) σ := by simp
    rw [Sigma.ι_comp_map', Category.comp_id, vertexTransport_id, eqToHom_map]
    exact Sigma.eqToHom_comp_ι
      (fun τ : (TopCat.toSSet.obj X).obj n ↦ L.obj (initialVertex τ)) hσ
  map_comp {m n p} α β := by
    refine Sigma.hom_ext _ _ fun σ ↦ ?_
    have hσ : (TopCat.toSSet.obj X).map (α ≫ β) σ =
        (TopCat.toSSet.obj X).map β ((TopCat.toSSet.obj X).map α σ) := by simp
    rw [Sigma.ι_comp_map', ← Category.assoc, Sigma.ι_comp_map', Category.assoc,
      Sigma.ι_comp_map', ← Category.assoc, ← L.map_comp, vertexTransport_comp, L.map_comp,
      Category.assoc, eqToHom_map]
    exact congrArg (L.map (vertexTransport (α ≫ β) σ) ≫ ·)
      (Sigma.eqToHom_comp_ι (fun τ : (TopCat.toSSet.obj X).obj p ↦ L.obj (initialVertex τ))
        hσ).symm

/-- The inclusion into twisted chains of the coefficient module attached to a singular simplex. -/
def ιTwistedChains (σ : (TopCat.toSSet.obj X).obj n) :
    L.obj (initialVertex σ) ⟶ (twistedChains L).obj n :=
  Sigma.ι (fun τ : (TopCat.toSSet.obj X).obj n ↦ L.obj (initialVertex τ)) σ

/-- Two maps out of a module of twisted chains agree as soon as they agree on every summand. -/
@[ext]
lemma twistedChains_hom_ext {A : ModuleCat.{max v w} R} {f g : (twistedChains L).obj n ⟶ A}
    (h : ∀ σ, ιTwistedChains L σ ≫ f = ιTwistedChains L σ ≫ g) : f = g :=
  Sigma.hom_ext _ _ h

/-- A structure map of twisted chains sends the summand of a simplex `σ` into the summand of the
reindexed simplex, after transporting the coefficients along the initial vertices. -/
@[reassoc (attr := simp)]
lemma ιTwistedChains_map (α : m ⟶ n) (σ : (TopCat.toSSet.obj X).obj m) :
    ιTwistedChains L σ ≫ (twistedChains L).map α =
      L.map (vertexTransport α σ) ≫ ιTwistedChains L ((TopCat.toSSet.obj X).map α σ) :=
  Sigma.ι_comp_map' _ _ _

/-- The chain complex of singular chains of `X` twisted by the local coefficient system `L`. -/
def twistedChainComplex : ChainComplex (ModuleCat.{max v w} R) ℕ :=
  (AlgebraicTopology.alternatingFaceMapComplex _).obj (twistedChains L)

/-- The inclusion into the degree-`k` term of the twisted chain complex of the coefficient module
attached to a singular `k`-simplex. -/
def ιTwistedChainComplex (k : ℕ) (σ : (TopCat.toSSet.obj X) _⦋k⦌) :
    L.obj (initialVertex σ) ⟶ (twistedChainComplex L).X k :=
  ιTwistedChains L σ

/-- Two maps out of a degree of the twisted chain complex agree as soon as they agree on every
summand. -/
@[ext]
lemma twistedChainComplex_hom_ext {k : ℕ} {A : ModuleCat.{max v w} R}
    {f g : (twistedChainComplex L).X k ⟶ A}
    (h : ∀ σ, ιTwistedChainComplex L k σ ≫ f = ιTwistedChainComplex L k σ ≫ g) : f = g :=
  twistedChains_hom_ext L h

/-- The boundary of the twisted chain complex sends the summand of a singular `(k + 1)`-simplex
`σ` to the alternating sum of the summands of the faces of `σ`, the coefficients being transported
from the initial vertex of `σ` to the initial vertex of each face. -/
@[reassoc (attr := simp)]
lemma ιTwistedChainComplex_d (k : ℕ) (σ : (TopCat.toSSet.obj X) _⦋k + 1⦌) :
    ιTwistedChainComplex L (k + 1) σ ≫ (twistedChainComplex L).d (k + 1) k =
      ∑ i : Fin (k + 2), (-1 : ℤ) ^ (i : ℕ) •
        (L.map (vertexTransport (SimplexCategory.δ i).op σ) ≫
          ιTwistedChainComplex L k ((TopCat.toSSet.obj X).map (SimplexCategory.δ i).op σ)) := by
  simp [twistedChainComplex, ιTwistedChainComplex, SimplicialObject.δ, Preadditive.comp_sum]
  -- Both sides are now the same alternating sum, written once over the degree-`k` term of the
  -- complex and once over the module of twisted `k`-chains it is built from.
  rfl

/-- Singular homology of `X` with coefficients in the local coefficient system `L`. -/
abbrev twistedHomology (k : ℕ) : ModuleCat.{max v w} R := (twistedChainComplex L).homology k

end Chains

section Coefficients

variable {L K J : LocalCoefficientSystem.{u, v, max v w} R X}

-- The degreewise map is kept as a separate definition so that the coefficient modules of the
-- two sides, which agree only definitionally, stay hidden from the naturality proof below.
private def twistedChainsCoefficientApp (η : L ⟶ K) (n : SimplexCategoryᵒᵖ) :
    (twistedChains L).obj n ⟶ (twistedChains K).obj n :=
  Limits.Sigma.map fun σ ↦ η.app (initialVertex σ)

@[reassoc]
private lemma ιTwistedChains_twistedChainsCoefficientApp (η : L ⟶ K) (n : SimplexCategoryᵒᵖ)
    (σ : (TopCat.toSSet.obj X).obj n) :
    ιTwistedChains L σ ≫ twistedChainsCoefficientApp η n =
      η.app (initialVertex σ) ≫ ιTwistedChains K σ :=
  Limits.Sigma.ι_map _ _

/-- The morphism of twisted chains induced by a morphism of local coefficient systems. -/
def twistedChainsCoefficientMap (η : L ⟶ K) : twistedChains L ⟶ twistedChains K where
  app := twistedChainsCoefficientApp η
  naturality _ _ _ := by
    refine twistedChains_hom_ext _ fun σ ↦ ?_
    simp [ιTwistedChains_twistedChainsCoefficientApp,
      ιTwistedChains_twistedChainsCoefficientApp_assoc]

/-- A morphism of local coefficient systems acts on the summand of a simplex `σ` through its
component at the initial vertex of `σ`. -/
@[reassoc (attr := simp)]
lemma ιTwistedChains_twistedChainsCoefficientMap (η : L ⟶ K) (n : SimplexCategoryᵒᵖ)
    (σ : (TopCat.toSSet.obj X).obj n) :
    ιTwistedChains L σ ≫ (twistedChainsCoefficientMap η).app n =
      η.app (initialVertex σ) ≫ ιTwistedChains K σ :=
  ιTwistedChains_twistedChainsCoefficientApp η n σ

variable (R X) in
/-- Twisted singular chains as a functor of the local coefficient system. -/
def twistedChainsFunctor :
    LocalCoefficientSystem.{u, v, max v w} R X ⥤ SimplicialObject (ModuleCat.{max v w} R) where
  obj L := twistedChains L
  map η := twistedChainsCoefficientMap η
  map_id L := by
    refine NatTrans.ext (funext fun n ↦ twistedChains_hom_ext _ fun σ ↦ ?_)
    simp
  map_comp η θ := by
    refine NatTrans.ext (funext fun n ↦ twistedChains_hom_ext _ fun σ ↦ ?_)
    simp

/-- The identity morphism of a coefficient system induces the identity of twisted chains. -/
@[simp]
lemma twistedChainsCoefficientMap_id (L : LocalCoefficientSystem.{u, v, max v w} R X) :
    twistedChainsCoefficientMap (𝟙 L) = 𝟙 (twistedChains L) :=
  (twistedChainsFunctor R X).map_id L

/-- A composite of morphisms of coefficient systems induces the composite of the two induced
morphisms of twisted chains. -/
@[simp, reassoc]
lemma twistedChainsCoefficientMap_comp (η : L ⟶ K) (θ : K ⟶ J) :
    twistedChainsCoefficientMap (η ≫ θ) =
      twistedChainsCoefficientMap η ≫ twistedChainsCoefficientMap θ :=
  (twistedChainsFunctor R X).map_comp η θ

/-- The morphism of twisted chain complexes induced by a morphism of local coefficient systems. -/
def twistedChainComplexCoefficientMap (η : L ⟶ K) :
    twistedChainComplex L ⟶ twistedChainComplex K :=
  (AlgebraicTopology.alternatingFaceMapComplex _).map (twistedChainsCoefficientMap η)

/-- In each degree, a morphism of local coefficient systems acts on the summand of a simplex `σ`
through its component at the initial vertex of `σ`. -/
@[reassoc (attr := simp)]
lemma ιTwistedChainComplex_twistedChainComplexCoefficientMap (η : L ⟶ K) (k : ℕ)
    (σ : (TopCat.toSSet.obj X) _⦋k⦌) :
    ιTwistedChainComplex L k σ ≫ (twistedChainComplexCoefficientMap η).f k =
      η.app (initialVertex σ) ≫ ιTwistedChainComplex K k σ :=
  ιTwistedChains_twistedChainsCoefficientMap η _ σ

/-- The identity morphism of a coefficient system induces the identity of twisted chain
complexes. -/
@[simp]
lemma twistedChainComplexCoefficientMap_id (L : LocalCoefficientSystem.{u, v, max v w} R X) :
    twistedChainComplexCoefficientMap (𝟙 L) = 𝟙 (twistedChainComplex L) :=
  (congrArg (fun φ ↦ (AlgebraicTopology.alternatingFaceMapComplex _).map φ)
    (twistedChainsCoefficientMap_id L)).trans (CategoryTheory.Functor.map_id _ _)

/-- A composite of morphisms of coefficient systems induces the composite of the two induced
morphisms of twisted chain complexes. -/
@[simp, reassoc]
lemma twistedChainComplexCoefficientMap_comp (η : L ⟶ K) (θ : K ⟶ J) :
    twistedChainComplexCoefficientMap (η ≫ θ) =
      twistedChainComplexCoefficientMap η ≫ twistedChainComplexCoefficientMap θ :=
  (congrArg (fun φ ↦ (AlgebraicTopology.alternatingFaceMapComplex _).map φ)
    (twistedChainsCoefficientMap_comp η θ)).trans (CategoryTheory.Functor.map_comp _ _ _)

/-- An isomorphism of local coefficient systems induces an isomorphism of twisted chain
complexes. -/
-- The body is exposed only so that `@[simps]` can record the two components as definitional
-- equalities; both of them are the already public `twistedChainComplexCoefficientMap`.  The
-- `mapIso` of `twistedChainsFunctor` is not usable here: its type mentions the unexposed
-- `twistedChains` and `twistedChainComplex`, so it does not elaborate against the stated type.
@[expose, simps]
def twistedChainComplexCoefficientIso (e : L ≅ K) :
    twistedChainComplex L ≅ twistedChainComplex K where
  hom := twistedChainComplexCoefficientMap e.hom
  inv := twistedChainComplexCoefficientMap e.inv
  hom_inv_id := by
    rw [← twistedChainComplexCoefficientMap_comp, e.hom_inv_id,
      twistedChainComplexCoefficientMap_id]
  inv_hom_id := by
    rw [← twistedChainComplexCoefficientMap_comp, e.inv_hom_id,
      twistedChainComplexCoefficientMap_id]

/-- The map on twisted homology induced by a morphism of local coefficient systems. -/
def twistedHomologyCoefficientMap (η : L ⟶ K) (k : ℕ) :
    twistedHomology L k ⟶ twistedHomology K k :=
  (HomologicalComplex.homologyFunctor _ _ k).map (twistedChainComplexCoefficientMap η)

/-- The identity morphism of a coefficient system induces the identity of twisted homology. -/
@[simp]
lemma twistedHomologyCoefficientMap_id (L : LocalCoefficientSystem.{u, v, max v w} R X) (k : ℕ) :
    twistedHomologyCoefficientMap (𝟙 L) k = 𝟙 (twistedHomology L k) :=
  (congrArg (fun φ ↦ (HomologicalComplex.homologyFunctor _ _ k).map φ)
    (twistedChainComplexCoefficientMap_id L)).trans (CategoryTheory.Functor.map_id _ _)

/-- A composite of morphisms of coefficient systems induces the composite of the two induced maps
of twisted homology. -/
@[simp, reassoc]
lemma twistedHomologyCoefficientMap_comp (η : L ⟶ K) (θ : K ⟶ J) (k : ℕ) :
    twistedHomologyCoefficientMap (η ≫ θ) k =
      twistedHomologyCoefficientMap η k ≫ twistedHomologyCoefficientMap θ k :=
  (congrArg (fun φ ↦ (HomologicalComplex.homologyFunctor _ _ k).map φ)
    (twistedChainComplexCoefficientMap_comp η θ)).trans (CategoryTheory.Functor.map_comp _ _ _)

end Coefficients

section Constant

variable (X) in
/-- For a constant local coefficient system, twisted chains are the ordinary singular chains. -/
def twistedChainsConstantIso (M : ModuleCat.{max v w} R) :
    twistedChains ((constantFunctor X).obj M) ≅
      TopCat.toSSet.obj X ⋙ (sigmaConst.{v}).obj M :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _) (by
    intro m n α
    refine Sigma.hom_ext _ _ fun σ ↦ ?_
    -- A constant system transports by the identity, so both structure maps are the reindexing
    -- `Sigma.desc fun σ ↦ Sigma.ι _ (α · σ)` of the summands, and `rfl` identifies them.
    simp only [Iso.refl_hom, twistedChains, Functor.comp_map, sigmaConst]
    rfl)

variable (X) in
/-- In each degree, the comparison of twisted chains with ordinary singular chains carries the
summand of a simplex `σ` onto the summand of `σ`. -/
@[reassoc (attr := simp)]
lemma ιTwistedChains_twistedChainsConstantIso_hom (M : ModuleCat.{max v w} R)
    (n : SimplexCategoryᵒᵖ) (σ : (TopCat.toSSet.obj X).obj n) :
    ιTwistedChains ((constantFunctor X).obj M) σ ≫ (twistedChainsConstantIso X M).hom.app n =
      Sigma.ι (fun _ : (TopCat.toSSet.obj X).obj n ↦ M) σ :=
  -- The comparison is the identity in every degree, and a constant system attaches the same
  -- module `M` to every simplex, so the two inclusions are the same map.
  (rfl)

variable (X) in
/-- In each degree, the inverse of the comparison of twisted chains with ordinary singular chains
carries the summand of a simplex `σ` onto the twisted summand of `σ`. -/
@[reassoc (attr := simp)]
lemma ι_twistedChainsConstantIso_inv (M : ModuleCat.{max v w} R)
    (n : SimplexCategoryᵒᵖ) (σ : (TopCat.toSSet.obj X).obj n) :
    Sigma.ι (fun _ : (TopCat.toSSet.obj X).obj n ↦ M) σ ≫
        (twistedChainsConstantIso X M).inv.app n =
      ιTwistedChains ((constantFunctor X).obj M) σ :=
  -- The comparison is the identity in every degree, so its inverse is too.
  (rfl)

variable (X) in
/-- The comparison of twisted chains with ordinary singular chains is natural in the coefficient
module: a morphism of modules acts on the twisted side through the constant systems it induces,
and on the singular side summandwise. -/
lemma twistedChainsConstantIso_hom_naturality {M N : ModuleCat.{max v w} R} (φ : M ⟶ N) :
    twistedChainsCoefficientMap ((constantFunctor X).map φ) ≫
        (twistedChainsConstantIso X N).hom =
      (twistedChainsConstantIso X M).hom ≫
        Functor.whiskerLeft (TopCat.toSSet.obj X) ((sigmaConst.{v}).map φ) :=
  -- In each degree the comparison is the identity, so both sides act on the summand of a simplex
  -- through the component of `φ` at that summand.
  NatTrans.ext (funext fun n ↦ twistedChains_hom_ext _ fun σ ↦
    Eq.trans (ιTwistedChains_twistedChainsCoefficientMap ((constantFunctor X).map φ) n σ)
      (Sigma.ι_map (f := fun _ : (TopCat.toSSet.obj X).obj n ↦ M)
        (g := fun _ : (TopCat.toSSet.obj X).obj n ↦ N) (fun _ ↦ φ) σ).symm)

variable (X) in
/-- For a constant local coefficient system, the twisted chain complex is the ordinary singular
chain complex with coefficients in the same module. -/
def twistedChainComplexConstantIso (M : ModuleCat.{max v w} R) :
    twistedChainComplex ((constantFunctor X).obj M) ≅
      ((AlgebraicTopology.singularChainComplexFunctor (ModuleCat.{max v w} R)).obj M).obj X :=
  (AlgebraicTopology.alternatingFaceMapComplex _).mapIso (twistedChainsConstantIso X M)

variable (X) in
/-- In each degree, the comparison of the twisted chain complex with the ordinary singular chain
complex carries the summand of a simplex `σ` onto the summand of `σ`. -/
@[reassoc (attr := simp)]
lemma ιTwistedChainComplex_twistedChainComplexConstantIso_hom (M : ModuleCat.{max v w} R) (k : ℕ)
    (σ : (TopCat.toSSet.obj X) _⦋k⦌) :
    ιTwistedChainComplex ((constantFunctor X).obj M) k σ ≫
        (twistedChainComplexConstantIso X M).hom.f k =
      Sigma.ι (fun _ : (TopCat.toSSet.obj X) _⦋k⦌ ↦ M) σ := by
  -- The comparison is the identity in every degree, and a constant system attaches the same
  -- module `M` to every simplex, so the two inclusions are the same map.
  rfl

variable (X) in
/-- In each degree, the inverse of the comparison of the twisted chain complex with the ordinary
singular chain complex carries the summand of a simplex `σ` onto the twisted summand of `σ`. -/
-- No `reassoc` here, unlike for the forward comparison: the coproduct is only definitionally the
-- degree-`k` term of the singular chain complex, so `Category.assoc` cannot see through the left
-- hand side and the reassociated lemma would come out unassociated, hence redundant.
@[simp]
lemma ι_twistedChainComplexConstantIso_inv (M : ModuleCat.{max v w} R) (k : ℕ)
    (σ : (TopCat.toSSet.obj X) _⦋k⦌) :
    Sigma.ι (fun _ : (TopCat.toSSet.obj X) _⦋k⦌ ↦ M) σ ≫
        (twistedChainComplexConstantIso X M).inv.f k =
      ιTwistedChainComplex ((constantFunctor X).obj M) k σ := by
  -- The comparison is the identity in every degree, so its inverse is too.
  rfl

variable (X) in
/-- The comparison of the twisted chain complex with the ordinary singular chain complex is
natural in the coefficient module. -/
lemma twistedChainComplexConstantIso_hom_naturality {M N : ModuleCat.{max v w} R} (φ : M ⟶ N) :
    twistedChainComplexCoefficientMap ((constantFunctor X).map φ) ≫
        (twistedChainComplexConstantIso X N).hom =
      (twistedChainComplexConstantIso X M).hom ≫
        ((AlgebraicTopology.singularChainComplexFunctor (ModuleCat.{max v w} R)).map φ).app X :=
  ((AlgebraicTopology.alternatingFaceMapComplex _).map_comp _ _).symm.trans
    ((congrArg (fun ψ ↦ (AlgebraicTopology.alternatingFaceMapComplex _).map ψ)
      (twistedChainsConstantIso_hom_naturality X φ)).trans
      ((AlgebraicTopology.alternatingFaceMapComplex _).map_comp _ _))

variable (X) in
/-- For a constant local coefficient system, twisted homology is ordinary singular homology. -/
-- The body is exposed only so that the two component lemmas below can be stated as definitional
-- equalities; both of their right hand sides are already public.
@[expose]
def twistedHomologyConstantIso (M : ModuleCat.{max v w} R) (k : ℕ) :
    twistedHomology ((constantFunctor X).obj M) k ≅
      ((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{max v w} R) k).obj M).obj X :=
  (HomologicalComplex.homologyFunctor _ _ k).mapIso (twistedChainComplexConstantIso X M)

-- Not `simp` lemmas, here or for the relative comparison in
-- `TauCeti.AlgebraicTopology.Singular.Twisted.Relative`: the comparison isomorphism is the simp
-- normal form, so that the lemmas relating it to the other maps of the theory can themselves be
-- `simp`.  They are stated for rewriting a comparison down to the chain level when needed.
variable (X) in
/-- The comparison of twisted homology with ordinary singular homology is the map induced on
homology by the comparison of the chain complexes. -/
lemma twistedHomologyConstantIso_hom (M : ModuleCat.{max v w} R) (k : ℕ) :
    (twistedHomologyConstantIso X M k).hom =
      HomologicalComplex.homologyMap (twistedChainComplexConstantIso X M).hom k :=
  rfl

variable (X) in
/-- The inverse of the comparison of twisted homology with ordinary singular homology is the map
induced on homology by the inverse comparison of the chain complexes. -/
lemma twistedHomologyConstantIso_inv (M : ModuleCat.{max v w} R) (k : ℕ) :
    (twistedHomologyConstantIso X M k).inv =
      HomologicalComplex.homologyMap (twistedChainComplexConstantIso X M).inv k :=
  rfl

variable (X) in
/-- The comparison of twisted homology with ordinary singular homology is natural in the
coefficient module. -/
lemma twistedHomologyConstantIso_hom_naturality {M N : ModuleCat.{max v w} R} (φ : M ⟶ N)
    (k : ℕ) :
    twistedHomologyCoefficientMap ((constantFunctor X).map φ) k ≫
        (twistedHomologyConstantIso X N k).hom =
      (twistedHomologyConstantIso X M k).hom ≫
        ((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{max v w} R) k).map φ).app X :=
  ((HomologicalComplex.homologyFunctor _ _ k).map_comp _ _).symm.trans
    ((congrArg (fun ψ ↦ (HomologicalComplex.homologyFunctor _ _ k).map ψ)
      (twistedChainComplexConstantIso_hom_naturality X φ)).trans
      ((HomologicalComplex.homologyFunctor _ _ k).map_comp _ _))

end Constant

section Map

variable {Y : TopCat.{v}} (f : X ⟶ Y) (L : LocalCoefficientSystem.{u, v, max v w} R Y)

-- The degreewise map is kept as a separate definition so that the coefficient modules of the
-- two sides, which agree only definitionally, stay hidden from the naturality proof below.
private def twistedChainsMapApp (n : SimplexCategoryᵒᵖ) :
    (twistedChains ((pullback f.hom).obj L)).obj n ⟶ (twistedChains L).obj n :=
  Sigma.map' ((TopCat.toSSet.map f).app n) fun _ ↦ 𝟙 _

private lemma ιTwistedChains_twistedChainsMapApp (n : SimplexCategoryᵒᵖ)
    (σ : (TopCat.toSSet.obj X).obj n) :
    ιTwistedChains ((pullback f.hom).obj L) σ ≫ twistedChainsMapApp f L n =
      ιTwistedChains L ((TopCat.toSSet.map f).app n σ) :=
  (Sigma.ι_comp_map' _ _ _).trans (Category.id_comp _)

/-- The morphism of twisted chains induced by a continuous map, from the chains twisted by the
pullback system to the chains twisted by `L`. -/
def twistedChainsMap : twistedChains ((pullback f.hom).obj L) ⟶ twistedChains L where
  app := twistedChainsMapApp f L
  naturality {m n} α := by
    refine twistedChains_hom_ext _ fun σ ↦ ?_
    rw [← Category.assoc, ιTwistedChains_map, Category.assoc,
      ιTwistedChains_twistedChainsMapApp, ← Category.assoc,
      ιTwistedChains_twistedChainsMapApp]
    refine Eq.trans ?_ (ιTwistedChains_map L α ((TopCat.toSSet.map f).app m σ)).symm
    exact congrArg (· ≫ ιTwistedChains L ((TopCat.toSSet.obj Y).map α
        ((TopCat.toSSet.map f).app m σ)))
      (congrArg L.map (map_pathTransport f σ (toTopInitialVertex m.unop)
        (toTop.map α.unop (toTopInitialVertex n.unop))))

/-- A continuous map sends the summand of a simplex `σ` of `X` identically onto the summand of its
image simplex in `Y`. -/
@[reassoc (attr := simp)]
lemma ιTwistedChains_twistedChainsMap (n : SimplexCategoryᵒᵖ)
    (σ : (TopCat.toSSet.obj X).obj n) :
    ιTwistedChains ((pullback f.hom).obj L) σ ≫ (twistedChainsMap f L).app n =
      ιTwistedChains L ((TopCat.toSSet.map f).app n σ) :=
  ιTwistedChains_twistedChainsMapApp f L n σ

/-- The morphism of twisted chain complexes induced by a continuous map. -/
def twistedChainComplexMap :
    twistedChainComplex ((pullback f.hom).obj L) ⟶ twistedChainComplex L :=
  (AlgebraicTopology.alternatingFaceMapComplex _).map (twistedChainsMap f L)

/-- In each degree, a continuous map sends the summand of a simplex `σ` of `X` identically onto
the summand of its image simplex in `Y`. -/
@[reassoc (attr := simp)]
lemma ιTwistedChainComplex_twistedChainComplexMap (k : ℕ)
    (σ : (TopCat.toSSet.obj X) _⦋k⦌) :
    ιTwistedChainComplex ((pullback f.hom).obj L) k σ ≫ (twistedChainComplexMap f L).f k =
      ιTwistedChainComplex L k ((TopCat.toSSet.map f).app _ σ) :=
  ιTwistedChains_twistedChainsMap f L _ σ

/-- The map on twisted homology induced by a continuous map, from the homology of `X` twisted by
the pullback system to the homology of `Y` twisted by `L`. -/
abbrev twistedHomologyMap (k : ℕ) :
    twistedHomology ((pullback f.hom).obj L) k ⟶ twistedHomology L k :=
  HomologicalComplex.homologyMap (twistedChainComplexMap f L) k

/-- A monomorphism of spaces, that is, a continuous map with injective underlying function,
induces a monomorphism of twisted chains in every degree: it reindexes the summands along an
injection of singular simplices. -/
-- The term has type `Mono (Sigma.map' ((TopCat.toSSet.map f).app k) fun _ ↦ 𝟙 _)`, so it uses two
-- definitional equalities that the section otherwise keeps hidden: that `twistedChainsMap` is
-- `twistedChainsMapApp` in every degree, and that the summand `((pullback f.hom).obj L).obj
-- (initialVertex σ)` of the source is `L.obj (initialVertex ((TopCat.toSSet.map f).app k σ))`.
instance mono_twistedChainsMap_app [Mono f] (k : SimplexCategoryᵒᵖ) :
    Mono ((twistedChainsMap f L).app k) :=
  MonoCoprod.mono_map'_of_injective (fun σ ↦ L.obj (initialVertex σ))
    ((TopCat.toSSet.map f).app k)
    ((CategoryTheory.mono_iff_injective ((TopCat.toSSet.map f).app k)).mp inferInstance)

/-- A monomorphism of spaces induces a monomorphism of twisted chain complexes in every
degree. -/
instance mono_twistedChainComplexMap_f [Mono f] (k : ℕ) :
    Mono ((twistedChainComplexMap f L).f k) :=
  mono_twistedChainsMap_app f L _

/-- A monomorphism of spaces induces a monomorphism of twisted chain complexes. -/
instance mono_twistedChainComplexMap [Mono f] : Mono (twistedChainComplexMap f L) :=
  HomologicalComplex.mono_of_mono_f _ fun k ↦ mono_twistedChainComplexMap_f f L k

end Map

section MapComp

variable {Y Z : TopCat.{v}} (f : X ⟶ Y) (g : Y ⟶ Z)

/-- The identity map induces on twisted chains the map coming from the identification of a
coefficient system with its pullback along the identity. -/
@[simp]
lemma twistedChainsMap_id (L : LocalCoefficientSystem.{u, v, max v w} R X) :
    twistedChainsMap (𝟙 X) L = twistedChainsCoefficientMap ((pullbackIdIso X).hom.app L) := by
  refine NatTrans.ext (funext fun n ↦ twistedChains_hom_ext _ fun σ ↦ ?_)
  refine (ιTwistedChains_twistedChainsMap (𝟙 X) L n σ).trans ?_
  refine Eq.trans ?_
    (ιTwistedChains_twistedChainsCoefficientMap ((pullbackIdIso X).hom.app L) n σ).symm
  rw [pullbackIdIso_hom_app_app]
  exact (Category.id_comp (ιTwistedChains L σ)).symm

/-- A composite of continuous maps induces on twisted chains the composite of the two induced
maps, after the identification of the pullback along the composite with the iterated pullback. -/
@[simp, reassoc]
lemma twistedChainsMap_comp (L : LocalCoefficientSystem.{u, v, max v w} R Z) :
    twistedChainsMap (f ≫ g) L =
      twistedChainsCoefficientMap ((pullbackCompIso f.hom g.hom).hom.app L) ≫
        twistedChainsMap f ((pullback g.hom).obj L) ≫ twistedChainsMap g L := by
  refine NatTrans.ext (funext fun n ↦ twistedChains_hom_ext _ fun σ ↦ ?_)
  refine (ιTwistedChains_twistedChainsMap (f ≫ g) L n σ).trans ?_
  refine Eq.trans ?_ (ιTwistedChains_twistedChainsCoefficientMap_assoc
    ((pullbackCompIso f.hom g.hom).hom.app L) n σ _).symm
  rw [pullbackCompIso_hom_app_app]
  refine Eq.trans ?_ (Category.id_comp _).symm
  exact ((ιTwistedChains_twistedChainsMap_assoc f ((pullback g.hom).obj L) n σ
    ((twistedChainsMap g L).app n)).trans
    (ιTwistedChains_twistedChainsMap g L n ((TopCat.toSSet.map f).app n σ))).symm

/-- The chain-complex form of `twistedChainsMap_id`. -/
@[simp]
lemma twistedChainComplexMap_id (L : LocalCoefficientSystem.{u, v, max v w} R X) :
    twistedChainComplexMap (𝟙 X) L =
      twistedChainComplexCoefficientMap ((pullbackIdIso X).hom.app L) :=
  congrArg (fun φ ↦ (AlgebraicTopology.alternatingFaceMapComplex _).map φ)
    (twistedChainsMap_id L)

/-- The chain-complex form of `twistedChainsMap_comp`. -/
@[simp, reassoc]
lemma twistedChainComplexMap_comp (L : LocalCoefficientSystem.{u, v, max v w} R Z) :
    twistedChainComplexMap (f ≫ g) L =
      twistedChainComplexCoefficientMap ((pullbackCompIso f.hom g.hom).hom.app L) ≫
        twistedChainComplexMap f ((pullback g.hom).obj L) ≫ twistedChainComplexMap g L :=
  (congrArg (fun φ ↦ (AlgebraicTopology.alternatingFaceMapComplex _).map φ)
      (twistedChainsMap_comp f g L)).trans
    (by rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp]; rfl)

/-- The homology form of `twistedChainsMap_id`. -/
@[simp]
lemma twistedHomologyMap_id (L : LocalCoefficientSystem.{u, v, max v w} R X) (k : ℕ) :
    twistedHomologyMap (𝟙 X) L k =
      twistedHomologyCoefficientMap ((pullbackIdIso X).hom.app L) k :=
  congrArg (fun φ ↦ (HomologicalComplex.homologyFunctor _ _ k).map φ)
    (twistedChainComplexMap_id L)

/-- The homology form of `twistedChainsMap_comp`. -/
@[simp, reassoc]
lemma twistedHomologyMap_comp (L : LocalCoefficientSystem.{u, v, max v w} R Z) (k : ℕ) :
    twistedHomologyMap (f ≫ g) L k =
      twistedHomologyCoefficientMap ((pullbackCompIso f.hom g.hom).hom.app L) k ≫
        twistedHomologyMap f ((pullback g.hom).obj L) k ≫ twistedHomologyMap g L k :=
  (congrArg (fun φ ↦ (HomologicalComplex.homologyFunctor _ _ k).map φ)
      (twistedChainComplexMap_comp f g L)).trans
    (by rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp]; rfl)

end MapComp

section MapCoefficient

variable {Y : TopCat.{v}} (f : X ⟶ Y) {L K : LocalCoefficientSystem.{u, v, max v w} R Y}

/-- The morphism of twisted chains induced by a continuous map is natural in the coefficient
system: pushing simplices forward along `f` and then applying a morphism of systems on `Y` is the
same as applying the pulled back morphism on `X` and then pushing forward. -/
lemma twistedChainsMap_naturality (η : L ⟶ K) :
    twistedChainsMap f L ≫ twistedChainsCoefficientMap η =
      twistedChainsCoefficientMap ((pullback f.hom).map η) ≫ twistedChainsMap f K := by
  refine NatTrans.ext (funext fun n ↦ twistedChains_hom_ext _ fun σ ↦ ?_)
  simp only [NatTrans.comp_app, ιTwistedChains_twistedChainsMap_assoc,
    ιTwistedChains_twistedChainsCoefficientMap_assoc, ιTwistedChains_twistedChainsMap,
    pullback_map_app]
  exact ιTwistedChains_twistedChainsCoefficientMap η n _

/-- The chain-complex form of `twistedChainsMap_naturality`. -/
lemma twistedChainComplexMap_naturality (η : L ⟶ K) :
    twistedChainComplexMap f L ≫ twistedChainComplexCoefficientMap η =
      twistedChainComplexCoefficientMap ((pullback f.hom).map η) ≫ twistedChainComplexMap f K :=
  ((AlgebraicTopology.alternatingFaceMapComplex _).map_comp _ _).symm.trans
    ((congrArg (fun φ ↦ (AlgebraicTopology.alternatingFaceMapComplex _).map φ)
      (twistedChainsMap_naturality f η)).trans
      ((AlgebraicTopology.alternatingFaceMapComplex _).map_comp _ _))

/-- The homology form of `twistedChainsMap_naturality`. -/
lemma twistedHomologyMap_naturality (η : L ⟶ K) (k : ℕ) :
    twistedHomologyMap f L k ≫ twistedHomologyCoefficientMap η k =
      twistedHomologyCoefficientMap ((pullback f.hom).map η) k ≫ twistedHomologyMap f K k :=
  ((HomologicalComplex.homologyFunctor _ _ k).map_comp _ _).symm.trans
    ((congrArg (fun φ ↦ (HomologicalComplex.homologyFunctor _ _ k).map φ)
      (twistedChainComplexMap_naturality f η)).trans
      ((HomologicalComplex.homologyFunctor _ _ k).map_comp _ _))

end MapCoefficient

section ConstantMap

variable {Y : TopCat.{v}} (f : X ⟶ Y) (M : ModuleCat.{max v w} R)

/-- The comparison of twisted chains with ordinary singular chains is natural in the space: a
continuous map acts on both sides by pushing singular simplices forward, once the pullback of a
constant system is identified with the constant system. -/
lemma twistedChainsConstantIso_hom_space_naturality :
    twistedChainsMap f ((constantFunctor Y).obj M) ≫ (twistedChainsConstantIso Y M).hom =
      twistedChainsCoefficientMap (pullbackConstantIso f.hom M).hom ≫
        (twistedChainsConstantIso X M).hom ≫
          Functor.whiskerRight (TopCat.toSSet.map f) ((sigmaConst.{v}).obj M) := by
  refine NatTrans.ext (funext fun n ↦ twistedChains_hom_ext _ fun σ ↦ ?_)
  -- The coefficient modules on the two sides agree only definitionally, so rewriting with the
  -- summand formulas leaves a goal that `rw` can no longer see into; each step is therefore
  -- applied as a term.
  have key : ιTwistedChains ((constantFunctor X).obj M) σ ≫
        (twistedChainsConstantIso X M).hom.app n ≫
          (Functor.whiskerRight (TopCat.toSSet.map f) ((sigmaConst.{v}).obj M)).app n =
      Sigma.ι (fun _ : (TopCat.toSSet.obj Y).obj n ↦ M) ((TopCat.toSSet.map f).app n σ) :=
    (ιTwistedChains_twistedChainsConstantIso_hom_assoc X M n σ _).trans
      ((Sigma.ι_comp_map' (f := fun _ : (TopCat.toSSet.obj X).obj n ↦ M)
          (g := fun _ : (TopCat.toSSet.obj Y).obj n ↦ M)
          (fun τ ↦ (TopCat.toSSet.map f).app n τ) (fun _ ↦ 𝟙 M) σ).trans
        (Category.id_comp _))
  refine ((ιTwistedChains_twistedChainsMap_assoc f ((constantFunctor Y).obj M) n σ
      ((twistedChainsConstantIso Y M).hom.app n)).trans
    (ιTwistedChains_twistedChainsConstantIso_hom Y M n _)).trans ?_
  refine Eq.trans ?_ (ιTwistedChains_twistedChainsCoefficientMap_assoc
    (pullbackConstantIso f.hom M).hom n σ _).symm
  rw [pullbackConstantIso_hom_app]
  exact key.symm.trans (Category.id_comp _).symm

/-- The chain-complex form of `twistedChainsConstantIso_hom_space_naturality`. -/
lemma twistedChainComplexConstantIso_hom_space_naturality :
    twistedChainComplexMap f ((constantFunctor Y).obj M) ≫
        (twistedChainComplexConstantIso Y M).hom =
      twistedChainComplexCoefficientMap (pullbackConstantIso f.hom M).hom ≫
        (twistedChainComplexConstantIso X M).hom ≫
          ((AlgebraicTopology.singularChainComplexFunctor (ModuleCat.{max v w} R)).obj M).map f :=
  ((AlgebraicTopology.alternatingFaceMapComplex _).map_comp _ _).symm.trans
    ((congrArg (fun φ ↦ (AlgebraicTopology.alternatingFaceMapComplex _).map φ)
      (twistedChainsConstantIso_hom_space_naturality f M)).trans
      (by rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp]; rfl))

/-- The homology form of `twistedChainsConstantIso_hom_space_naturality`. -/
lemma twistedHomologyConstantIso_hom_space_naturality (k : ℕ) :
    twistedHomologyMap f ((constantFunctor Y).obj M) k ≫ (twistedHomologyConstantIso Y M k).hom =
      twistedHomologyCoefficientMap (pullbackConstantIso f.hom M).hom k ≫
        (twistedHomologyConstantIso X M k).hom ≫
          ((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{max v w} R) k).obj M).map f :=
  ((HomologicalComplex.homologyFunctor _ _ k).map_comp _ _).symm.trans
    ((congrArg (fun φ ↦ (HomologicalComplex.homologyFunctor _ _ k).map φ)
      (twistedChainComplexConstantIso_hom_space_naturality f M)).trans
      (by rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp]; rfl))

end ConstantMap

end LocalCoefficientSystem

end TauCeti
