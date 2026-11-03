/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.SimplicialSet.Homology.HomotopyInvariance
public import TauCeti.AlgebraicTopology.Singular.Homotopy.Basic
public import TauCeti.AlgebraicTopology.Singular.ModuleChains.Basic
public import Mathlib.AlgebraicTopology.SingularHomology.HomotopyInvariance
public import Mathlib.Topology.Homotopy.Equiv
public import TauCeti.Topology.Category.TopPair

/-!
# Homotopy invariance of relative singular homology

A homotopy between maps of topological pairs induces a chain homotopy between the induced maps
of relative singular chain complexes, so homotopic maps of pairs induce the same map on relative
singular homology, and maps of pairs that are inverse to each other up to homotopy induce
isomorphisms on it.  This is the homotopy axiom of Eilenberg--Steenrod for the relative singular
theory.  In particular, if `s ⊆ c ⊆ t` and `t` strong deformation retracts onto `c`, the inclusion
of pairs `(c, s) ⟶ (t, s)` induces isomorphisms on relative singular homology
(`TopPair.isIso_singularHomologyMap_ofInclusionMap_inclusion_of_homotopyRel`).  In the absolute
case, a homotopy equivalence of spaces induces an isomorphism on singular homology
(`ContinuousMap.HomotopyEquiv.singularHomologyIso`).

The homotopy is transported to the singular simplicial sets of the two spaces, where the
compatibility of the two simplicial homotopies over the inclusion of the subspace descends the
chain homotopy to the relative chain complexes.  The absolute case is
`Mathlib/AlgebraicTopology/SingularHomology/HomotopyInvariance.lean` (F. Odermatt, J. Riou),
whose proof plan through `TopCat.Homotopy.toSSet` this file follows for pairs.

The source is Eilenberg--Steenrod, *Foundations of Algebraic Topology*, Chapter VII, where the
homotopy axiom is verified for the singular theory; see also Hatcher, *Algebraic Topology*, §2.1,
Theorem 2.10 and its relative form.
-/

@[expose] public section

noncomputable section

open CategoryTheory Limits

universe w v u

namespace TopPair.Homotopy

variable {P P' : TopPair.{w}} {f g : P ⟶ P'} (H : Homotopy f g)
  {C : Type u} [Category.{v} C] [HasCoproducts.{w} C] [Preadditive C] (R : C)

/-- A homotopy between maps of topological pairs induces a chain homotopy between the induced
maps of relative singular chain complexes. -/
@[no_expose]
def singularChainComplexMap :
    _root_.Homotopy (P.singularChainComplexMap f R) (P.singularChainComplexMap g R) :=
  H.toSSetPair.chainComplexMap R

@[reassoc (attr := simp)]
lemma singularChainComplexMap_hom (p q : ℕ) :
    (P.singularChainComplexπ R).f p ≫ (H.singularChainComplexMap R).hom p q =
      (H.fst.toSSet.chainComplexMap R).hom p q ≫ (P'.singularChainComplexπ R).f q := by
  rw [← H.toSSetPair_right]
  exact H.toSSetPair.chainComplexMap_hom R p q

include H in
/-- Homotopic maps of topological pairs induce the same map on relative singular homology. -/
lemma congr_singularHomologyMap [CategoryWithHomology C] (n : ℕ) :
    P.singularHomologyMap f R n = P.singularHomologyMap g R n :=
  H.toSSetPair.congr_homologyMap R n

end TopPair.Homotopy

namespace TopPair

variable {P P' : TopPair.{w}} {C : Type u} [Category.{v} C] [HasCoproducts.{w} C] [Preadditive C]
  [CategoryWithHomology C]

/-- Maps of topological pairs which are inverse to each other up to homotopy induce isomorphisms
on relative singular homology. -/
lemma isIso_singularHomologyMap (f : P ⟶ P') (f' : P' ⟶ P) (H : Homotopy (f ≫ f') (𝟙 P))
    (H' : Homotopy (f' ≫ f) (𝟙 P')) (R : C) (n : ℕ) :
    IsIso (P.singularHomologyMap f R n) := by
  refine SSetPair.isIso_homologyMap _ (toSSetPair.map f') ?_ ?_ R n
  · rw [← Functor.map_comp, ← CategoryTheory.Functor.map_id]
    exact H.toSSetPair
  · rw [← Functor.map_comp, ← CategoryTheory.Functor.map_id]
    exact H'.toSSetPair

/-- **A pair whose identity deforms into its subspace has no relative homology**: if the identity
of `P` is homotopic, as a map of pairs, to a map whose map of ambient spaces factors through the
subspace, as when the subspace is a strong deformation retract, then the relative singular
homology of `P` vanishes in every degree. -/
lemma isZero_singularHomology_of_homotopy {f : P ⟶ P} (H : Homotopy (𝟙 P) f)
    (g : P.fst ⟶ P.snd) (hg : g ≫ P.map = Hom.fst f) (R : C) (n : ℕ) :
    IsZero (P.singularHomology R n) := by
  rw [IsZero.iff_id_eq_zero, ← singularHomologyMap_id, H.congr_singularHomologyMap R n]
  exact singularHomologyMap_eq_zero_of_fac f R g hg n

/-- **Enlarging the subspace along a deformation.** Let `B ⊆ N` be subsets of `X` and let `H` be a
homotopy from the identity of `X` to a map `ρ` carrying `N` into `B`.  If `H` keeps `B` inside `B`
and `N` inside `N` at every time, the inclusion `(X, B) ⟶ (X, N)` induces isomorphisms on relative
singular homology: `ρ` is a homotopy inverse as a map of pairs.  This is how a subspace may be
replaced by a neighbourhood which deformation retracts onto it. -/
lemma isIso_singularHomologyMap_ofSubsetMap_id_of_homotopy {X : TopCat.{w}} {B N : Set X}
    (hBN : Set.MapsTo (𝟙 X) B N) {ρ : X ⟶ X} (H : (TopCat.Hom.hom (𝟙 X)).Homotopy ρ.hom)
    (hB : ∀ (τ : unitInterval) (x : X), x ∈ B → H (τ, x) ∈ B)
    (hN : ∀ (τ : unitInterval) (x : X), x ∈ N → H (τ, x) ∈ N) (hρ : Set.MapsTo ρ N B) (R : C)
    (n : ℕ) : IsIso (TopPair.singularHomologyMap (ofSubsetMap (𝟙 X) hBN) R n) := by
  refine isIso_singularHomologyMap _ (ofSubsetMap ρ hρ) ?_ ?_ R n
  · rw [← ofSubsetMap_comp _ _ hBN hρ (hρ.comp hBN), ← ofSubsetMap_id (B := B) fun _ hx ↦ hx]
    simpa only [Category.id_comp] using (ofSubsetHomotopy H hB).symm
  · rw [← ofSubsetMap_comp _ _ hρ hBN (hBN.comp hρ), ← ofSubsetMap_id (B := N) fun _ hx ↦ hx]
    simpa only [Category.comp_id] using (ofSubsetHomotopy H hN).symm

/-- **A strong deformation retraction of the ambient space induces isomorphisms on relative
singular homology.** If `s ⊆ c ⊆ t` and `t` deformation retracts onto `c` relative to `c`, the
inclusion `(c, s) ⟶ (t, s)` induces isomorphisms on relative singular homology. -/
theorem isIso_singularHomologyMap_ofInclusionMap_inclusion_of_homotopyRel {X : TopCat.{w}}
    {s c t : Set X} (hsc : s ⊆ c) (hct : c ⊆ t) (r : C(t, c))
    (G : ((ContinuousMap.inclusion hct).comp r).HomotopyRel (ContinuousMap.id t)
      {x | (x : X) ∈ c})
    (R : C) (n : ℕ) :
    IsIso ((ofInclusion hsc).singularHomologyMap
      (ofInclusionMap hsc (hsc.trans hct) (ContinuousMap.inclusion hct)
        fun _ hx ↦ by simpa using hx) R n) := by
  -- The retraction fixes every point of `c`, in particular every point of `s`.
  have hrc (x : t) (hx : (x : X) ∈ c) : (r x : X) = x :=
    congrArg Subtype.val (G.fst_eq_snd (x := x) hx)
  have hrs (x : t) (hx : (x : X) ∈ s) : (r x : X) ∈ s := (hrc x (hsc hx)).symm ▸ hx
  refine isIso_singularHomologyMap _ (ofInclusionMap (hsc.trans hct) hsc r hrs) ?_ ?_ R n
  · rw [← ofInclusionMap_comp, ← ofInclusionMap_id]
    have hid : r.comp (ContinuousMap.inclusion hct) = ContinuousMap.id c := by
      ext x
      exact hrc _ x.2
    simp only [hid]
    exact Homotopy.refl _
  · rw [← ofInclusionMap_comp, ← ofInclusionMap_id]
    -- The homotopy is stationary on `c ⊇ s`, so it keeps `s` inside `s`.
    refine ofInclusionHomotopy G.toHomotopy fun τ x hx ↦ ?_
    have h : G.toHomotopy (τ, x) = _ := G.eq_fst τ (hsc hx)
    exact h ▸ hrs x hx

end TopPair

namespace ContinuousMap.HomotopyEquiv

open AlgebraicTopology

variable {X Y : Type w} [TopologicalSpace X] [TopologicalSpace Y]
  (e : ContinuousMap.HomotopyEquiv X Y)
  {C : Type u} [Category.{v} C] [HasCoproducts.{w} C] [Preadditive C] [CategoryWithHomology C]
  (R : C)

/-- A homotopy equivalence induces an isomorphism on singular homology in every degree, with
inverse induced by the homotopy inverse. -/
@[no_expose]
def singularHomologyIso (n : ℕ) :
    ((singularHomologyFunctor C n).obj R).obj (TopCat.of X) ≅
      ((singularHomologyFunctor C n).obj R).obj (TopCat.of Y) where
  hom := ((singularHomologyFunctor C n).obj R).map (TopCat.ofHom e.toFun)
  inv := ((singularHomologyFunctor C n).obj R).map (TopCat.ofHom e.invFun)
  hom_inv_id := by
    rw [← Functor.map_comp, ← CategoryTheory.Functor.map_id]
    exact TopCat.Homotopy.congr_homologyMap_singularChainComplexFunctor e.left_inv.some R n
  inv_hom_id := by
    rw [← Functor.map_comp, ← CategoryTheory.Functor.map_id]
    exact TopCat.Homotopy.congr_homologyMap_singularChainComplexFunctor e.right_inv.some R n

@[simp]
lemma singularHomologyIso_hom (n : ℕ) :
    (e.singularHomologyIso R n).hom =
      ((singularHomologyFunctor C n).obj R).map (TopCat.ofHom e.toFun) := (rfl)

@[simp]
lemma singularHomologyIso_inv (n : ℕ) :
    (e.singularHomologyIso R n).inv =
      ((singularHomologyFunctor C n).obj R).map (TopCat.ofHom e.invFun) := (rfl)

end ContinuousMap.HomotopyEquiv

namespace ContinuousMap

open TauCeti

variable (k : Type w) [Ring k] (n : ℕ)

/-- Homotopic continuous maps induce the same map on singular homology. -/
theorem singularHomologyMap_eq_of_homotopic {Y Z : Type w} [TopologicalSpace Y]
    [TopologicalSpace Z] {g g' : C(Y, Z)} (H : g.Homotopic g') :
    singularHomologyMap k n g = singularHomologyMap k n g' :=
  congrArg ModuleCat.Hom.hom
    (TopCat.Homotopy.congr_homologyMap_singularChainComplexFunctor
      (f := TopCat.ofHom g) (g := TopCat.ofHom g') H.some (ModuleCat.of k k) n)

/-- A homotopy equivalence induces a bijection on singular homology. -/
theorem HomotopyEquiv.bijective_singularHomologyMap {Y Z : Type w}
    [TopologicalSpace Y] [TopologicalSpace Z]
    (e : ContinuousMap.HomotopyEquiv Y Z) : Function.Bijective (singularHomologyMap k n e.toFun) :=
  ConcreteCategory.bijective_of_isIso (e.singularHomologyIso (ModuleCat.of k k) n).hom

end ContinuousMap
