/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicTopology.SingularHomology.Basic
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
  coefficient system.
* `TauCeti.LocalCoefficientSystem.twistedHomologyConstantIso`: for a constant system, twisted
  homology is ordinary singular homology.
* `TauCeti.LocalCoefficientSystem.twistedChainComplexMap`: the chain map induced by a continuous
  map.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 3.H.
-/

public section

noncomputable section

open CategoryTheory Limits Convexity SimplexCategory

universe u v w

namespace TauCeti

namespace TopCat

variable {X Y : TopCat.{v}} {m n : SimplexCategoryᵒᵖ}

/-- The continuous map underlying a singular simplex, on the topological simplex
`SimplexCategory.toTop.obj n.unop` rather than on the unlifted model used by
`TopCat.toSSetObjEquiv`, so that it composes directly with the maps `SimplexCategory.toTop.map`.
The body is exposed because the two identities below, describing how it reacts to the simplicial
and to the space variable, hold definitionally. -/
@[expose]
def simplexMap (σ : (TopCat.toSSet.obj X).obj n) :
    C(SimplexCategory.toTop.{v}.obj n.unop, X) := σ.down.hom

@[simp]
lemma simplexMap_map (α : m ⟶ n) (σ : (TopCat.toSSet.obj X).obj m) :
    simplexMap ((TopCat.toSSet.obj X).map α σ) =
      (simplexMap σ).comp (SimplexCategory.toTop.map α.unop).hom := rfl

@[simp]
lemma simplexMap_app (f : X ⟶ Y) (σ : (TopCat.toSSet.obj X).obj n) :
    simplexMap ((TopCat.toSSet.map f).app n σ) = f.hom.comp (simplexMap σ) := rfl

end TopCat

namespace LocalCoefficientSystem

variable {R : Type u} [Ring R] {X Y : TopCat.{v}} {m n p : SimplexCategoryᵒᵖ}

/-- The initial vertex of a singular simplex, as an object of the fundamental groupoid.  This is
reducible so that the coefficient module attached to a simplex is transparent to unification. -/
abbrev vertex (σ : (TopCat.toSSet.obj X).obj n) : FundamentalGroupoid X :=
  ⟨TopCat.simplexMap σ (toTopInitialVertex n.unop)⟩

/-- The morphism of the fundamental groupoid of `X` obtained by running a singular simplex along
the unique path class between two points of its simplex. -/
def pathTransport (σ : (TopCat.toSSet.obj X).obj n) (z w : toTop.{v}.obj n.unop) :
    (⟨TopCat.simplexMap σ z⟩ : FundamentalGroupoid X) ⟶ ⟨TopCat.simplexMap σ w⟩ :=
  (FundamentalGroupoid.map (TopCat.simplexMap σ)).map
    (default : (⟨z⟩ : FundamentalGroupoid (toTop.{v}.obj n.unop)) ⟶ ⟨w⟩)

@[simp]
lemma pathTransport_self (σ : (TopCat.toSSet.obj X).obj n) (z : toTop.{v}.obj n.unop) :
    pathTransport σ z z = 𝟙 _ :=
  FundamentalGroupoid.map_default_self _ _

@[reassoc (attr := simp)]
lemma pathTransport_comp (σ : (TopCat.toSSet.obj X).obj n)
    (z w y : toTop.{v}.obj n.unop) :
    pathTransport σ z w ≫ pathTransport σ w y = pathTransport σ z y :=
  FundamentalGroupoid.map_default_comp _ _ _ _

@[reassoc]
lemma pathTransport_eqToHom (σ : (TopCat.toSSet.obj X).obj n) (z : toTop.{v}.obj n.unop)
    {w w' : toTop.{v}.obj n.unop} (h : w = w') :
    pathTransport σ z w ≫
        eqToHom (congrArg (fun y ↦ (⟨TopCat.simplexMap σ y⟩ : FundamentalGroupoid X)) h) =
      pathTransport σ z w' := by
  subst h
  simp

lemma pathTransport_map (α : m ⟶ n) (σ : (TopCat.toSSet.obj X).obj m)
    (z w : toTop.{v}.obj n.unop) :
    pathTransport ((TopCat.toSSet.obj X).map α σ) z w =
      pathTransport σ (toTop.map α.unop z) (toTop.map α.unop w) := by
  have h : ((FundamentalGroupoid.map (toTop.map α.unop).hom).map
        (default : (⟨z⟩ : FundamentalGroupoid (toTop.{v}.obj n.unop)) ⟶ ⟨w⟩) :
      (⟨toTop.map α.unop z⟩ : FundamentalGroupoid (toTop.{v}.obj m.unop)) ⟶
        ⟨toTop.map α.unop w⟩) = default := Subsingleton.elim _ _
  exact (FundamentalGroupoid.map_comp_map _ _ _).trans (congrArg _ h)

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
    vertex σ ⟶ vertex ((TopCat.toSSet.obj X).map α σ) :=
  pathTransport σ (toTopInitialVertex m.unop) (toTop.map α.unop (toTopInitialVertex n.unop))

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
  obj n := ∐ fun σ : (TopCat.toSSet.obj X).obj n ↦ L.obj (vertex σ)
  map {m n} α := Sigma.desc fun σ ↦ L.map (vertexTransport α σ) ≫
    Sigma.ι (fun τ : (TopCat.toSSet.obj X).obj n ↦ L.obj (vertex τ))
      ((TopCat.toSSet.obj X).map α σ)
  map_id n := by
    refine Sigma.hom_ext _ _ fun σ ↦ ?_
    have hσ : σ = (TopCat.toSSet.obj X).map (𝟙 n) σ := by simp
    rw [Sigma.ι_desc, Category.comp_id, vertexTransport_id, eqToHom_map]
    exact Sigma.eqToHom_comp_ι (fun τ : (TopCat.toSSet.obj X).obj n ↦ L.obj (vertex τ)) hσ
  map_comp {m n p} α β := by
    refine Sigma.hom_ext _ _ fun σ ↦ ?_
    have hσ : (TopCat.toSSet.obj X).map (α ≫ β) σ =
        (TopCat.toSSet.obj X).map β ((TopCat.toSSet.obj X).map α σ) := by simp
    rw [Sigma.ι_desc, ← Category.assoc, Sigma.ι_desc, Category.assoc, Sigma.ι_desc,
      ← Category.assoc, ← L.map_comp, vertexTransport_comp, L.map_comp, Category.assoc,
      eqToHom_map]
    exact congrArg (L.map (vertexTransport (α ≫ β) σ) ≫ ·)
      (Sigma.eqToHom_comp_ι (fun τ : (TopCat.toSSet.obj X).obj p ↦ L.obj (vertex τ))
        hσ).symm

/-- The inclusion into twisted chains of the coefficient module attached to a singular simplex. -/
def ιTwistedChains (σ : (TopCat.toSSet.obj X).obj n) :
    L.obj (vertex σ) ⟶ (twistedChains L).obj n :=
  Sigma.ι (fun τ : (TopCat.toSSet.obj X).obj n ↦ L.obj (vertex τ)) σ

@[ext]
lemma twistedChains_hom_ext {A : ModuleCat.{max v w} R} {f g : (twistedChains L).obj n ⟶ A}
    (h : ∀ σ, ιTwistedChains L σ ≫ f = ιTwistedChains L σ ≫ g) : f = g :=
  Sigma.hom_ext _ _ h

@[reassoc (attr := simp)]
lemma ιTwistedChains_map (α : m ⟶ n) (σ : (TopCat.toSSet.obj X).obj m) :
    ιTwistedChains L σ ≫ (twistedChains L).map α =
      L.map (vertexTransport α σ) ≫ ιTwistedChains L ((TopCat.toSSet.obj X).map α σ) :=
  Sigma.ι_desc _ _

/-- The chain complex of singular chains of `X` twisted by the local coefficient system `L`. -/
def twistedChainComplex : ChainComplex (ModuleCat.{max v w} R) ℕ :=
  (AlgebraicTopology.alternatingFaceMapComplex _).obj (twistedChains L)

/-- Singular homology of `X` with coefficients in the local coefficient system `L`. -/
def twistedHomology (k : ℕ) : ModuleCat.{max v w} R := (twistedChainComplex L).homology k

end Chains

section Coefficients

variable {L K : LocalCoefficientSystem.{u, v, max v w} R X}

/-- The map on twisted chains in a single degree induced by a morphism of local coefficient
systems. -/
def twistedChainsCoefficientApp (η : L ⟶ K) (n : SimplexCategoryᵒᵖ) :
    (twistedChains L).obj n ⟶ (twistedChains K).obj n :=
  Sigma.desc fun σ ↦ η.app (vertex σ) ≫ ιTwistedChains K σ

@[reassoc (attr := simp)]
lemma ιTwistedChains_twistedChainsCoefficientApp (η : L ⟶ K) (n : SimplexCategoryᵒᵖ)
    (σ : (TopCat.toSSet.obj X).obj n) :
    ιTwistedChains L σ ≫ twistedChainsCoefficientApp η n = η.app (vertex σ) ≫ ιTwistedChains K σ :=
  Sigma.ι_desc _ _

variable (R X) in
/-- Twisted singular chains as a functor of the local coefficient system. -/
def twistedChainsFunctor :
    LocalCoefficientSystem.{u, v, max v w} R X ⥤ SimplicialObject (ModuleCat.{max v w} R) where
  obj L := twistedChains L
  map η := { app := twistedChainsCoefficientApp η
             naturality := fun _ _ _ ↦ by
               refine twistedChains_hom_ext _ fun σ ↦ ?_
               simp }
  map_id L := by
    refine NatTrans.ext (funext fun n ↦ twistedChains_hom_ext _ fun σ ↦ ?_)
    simp
  map_comp η θ := by
    refine NatTrans.ext (funext fun n ↦ twistedChains_hom_ext _ fun σ ↦ ?_)
    simp

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
/-- For a constant local coefficient system, the twisted chain complex is the ordinary singular
chain complex with coefficients in the same module. -/
def twistedChainComplexConstantIso (M : ModuleCat.{max v w} R) :
    twistedChainComplex ((constantFunctor X).obj M) ≅
      ((AlgebraicTopology.singularChainComplexFunctor (ModuleCat.{max v w} R)).obj M).obj X :=
  (AlgebraicTopology.alternatingFaceMapComplex _).mapIso (twistedChainsConstantIso X M)

variable (X) in
/-- For a constant local coefficient system, twisted homology is ordinary singular homology. -/
def twistedHomologyConstantIso (M : ModuleCat.{max v w} R) (k : ℕ) :
    twistedHomology ((constantFunctor X).obj M) k ≅
      ((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{max v w} R) k).obj M).obj X :=
  (HomologicalComplex.homologyFunctor _ _ k).mapIso (twistedChainComplexConstantIso X M)

end Constant

section Map

variable {Y : TopCat.{v}} (f : X ⟶ Y) (L : LocalCoefficientSystem.{u, v, max v w} R Y)

/-- The map on twisted chains in a single degree induced by a continuous map: a singular simplex
of `X` is sent to its image in `Y`.  The coefficient modules agree because the initial vertex of
the image simplex is the image of the initial vertex. -/
def twistedChainsMapApp (n : SimplexCategoryᵒᵖ) :
    (twistedChains ((pullback f.hom).obj L)).obj n ⟶ (twistedChains L).obj n :=
  Sigma.desc fun σ ↦ ιTwistedChains L ((TopCat.toSSet.map f).app n σ)

@[reassoc (attr := simp)]
lemma ιTwistedChains_twistedChainsMapApp (n : SimplexCategoryᵒᵖ)
    (σ : (TopCat.toSSet.obj X).obj n) :
    ιTwistedChains ((pullback f.hom).obj L) σ ≫ twistedChainsMapApp f L n =
      ιTwistedChains L ((TopCat.toSSet.map f).app n σ) :=
  Sigma.ι_desc _ _

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

/-- The morphism of twisted chain complexes induced by a continuous map. -/
def twistedChainComplexMap :
    twistedChainComplex ((pullback f.hom).obj L) ⟶ twistedChainComplex L :=
  (AlgebraicTopology.alternatingFaceMapComplex _).map (twistedChainsMap f L)

end Map

end LocalCoefficientSystem

end TauCeti
