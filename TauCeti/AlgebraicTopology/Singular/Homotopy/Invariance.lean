/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicTopology.SingularHomology.HomotopyInvariance
public import Mathlib.Topology.Homotopy.Equiv
public import TauCeti.AlgebraicTopology.SimplicialSet.Homology.HomotopyInvariance
public import TauCeti.AlgebraicTopology.Singular.Homotopy.Basic
public import TauCeti.AlgebraicTopology.Singular.ModuleChains.Basic
public import TauCeti.Topology.Category.TopPair
public import TauCeti.Topology.Homotopy.Homotopic.Translation

/-!
# Homotopy invariance of relative singular homology

A homotopy between maps of topological pairs induces a chain homotopy between the induced maps
of relative singular chain complexes, so homotopic maps of pairs induce the same map on relative
singular homology, and maps of pairs that are inverse to each other up to homotopy induce
isomorphisms on it.  This is the homotopy axiom of Eilenberg--Steenrod for the relative singular
theory.  In particular, if `s ⊆ c ⊆ t` and `t` strong deformation retracts onto `c`, the inclusion
of pairs `(c, s) ⟶ (t, s)` induces isomorphisms on relative singular homology
(`TopPair.isIso_singularHomologyMap_ofInclusionMap_inclusion_of_homotopyRel`), and if `t` strong
deformation retracts onto `s` the relative homology of `(t, s)` vanishes
(`TopPair.isZero_singularHomology_ofInclusion_of_homotopyRel`), as it does whenever a homotopy
from the identity into `s` keeps `s` inside `s`
(`TopPair.isZero_singularHomology_ofSubset_of_homotopy`).  In the absolute
case, homotopic maps induce the same map on singular homology
(`ContinuousMap.Homotopic.homologyMap_eq`), right multiplication in a path-connected topological
monoid acts trivially on it (`ContinuousMap.singularHomologyMap_mulRight`,
`ContinuousMap.singularHomologyMap_addRight`), and a homotopy equivalence of spaces induces an
isomorphism on it (`ContinuousMap.HomotopyEquiv.singularHomologyIso`), so by the five lemma a map
of pairs which is a homotopy equivalence on both spaces induces isomorphisms on relative singular
homology (`TopPair.isIso_singularHomologyMap_of_homotopyEquiv`). In particular, if `j : s → X` is
an embedding and `h : X ≃ₕ t` is a homotopy equivalence with `h ∘ j` the inclusion `s ⊆ t`, then
`Hₙ(X, j s) ≅ Hₙ(t, s)` (`TopPair.nonempty_singularHomology_ofInclusion_iso_of_homotopyEquiv`).

The singular chain homotopies of homotopies forming a commutative square of spaces commute with the
chain maps of the square (`TopCat.Homotopy.singularChainComplexFunctorObjMap_hom_comm`); for
instance, on the chains of a subspace, the chain homotopy of a homotopy which keeps the subspace
inside a subspace of the target is that of its restriction.

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

open CategoryTheory Limits MonoidalCategory AlgebraicTopology

open scoped Simplicial

universe w v u

namespace TopCat.Homotopy

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasCoproducts.{w} C]
  {X Y X' Y' : TopCat.{w}} {f g : X ⟶ Y} {f' g' : X' ⟶ Y'}

/-- The singular chain homotopies of homotopies `H` and `H'` which form a commutative square with
maps `u : X ⟶ X'` and `v : Y ⟶ Y'`, that is, `H' (t, u x) = v (H (t, x))`, commute with the
singular chain maps of `u` and `v`. -/
@[reassoc]
lemma singularChainComplexFunctorObjMap_hom_comm (H : TopCat.Homotopy f g)
    (H' : TopCat.Homotopy f' g') {u : X ⟶ X'} {v : Y ⟶ Y'} (huv : u ▷ TopCat.I ≫ H'.h = H.h ≫ v)
    (R : C) (p q : ℕ) :
    (((singularChainComplexFunctor C).obj R).map u).f p ≫
        (H'.singularChainComplexFunctorObjMap R).hom p q =
      (H.singularChainComplexFunctorObjMap R).hom p q ≫
        (((singularChainComplexFunctor C).obj R).map v).f q := by
  -- Transport the commutative square to the singular simplicial sets.
  have hu : TopCat.toSSet.map u ▷ Δ[1] ≫ H'.toSSet.h = H.toSSet.h ≫ TopCat.toSSet.map v := by
    simp only [TopCat.Homotopy.toSSet, Category.assoc]
    rw [← whisker_exchange_assoc (TopCat.toSSet.map u) SSet.stdSimplex.toSSetObjI,
      Functor.LaxMonoidal.μ_natural_left_assoc]
    simp only [← Functor.map_comp, huv]
  exact H.toSSet.chainComplexMap_hom_comm H'.toSSet hu R p q

end TopCat.Homotopy

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
      exact hrc _ x.property
    simp only [hid]
    exact Homotopy.refl _
  · rw [← ofInclusionMap_comp, ← ofInclusionMap_id]
    -- The homotopy is stationary on `c ⊇ s`, so it keeps `s` inside `s`.
    refine ofInclusionHomotopy G.toHomotopy fun τ x hx ↦ ?_
    have h : G.toHomotopy (τ, x) = _ := G.eq_fst τ (hsc hx)
    exact h ▸ hrs x hx

/-- **A pair with a strong deformation retraction onto its subspace has no relative homology.**
If `s ⊆ t` and `t` deformation retracts onto `s` relative to `s`, the relative singular homology
of `(t, s)` vanishes in every degree. -/
theorem isZero_singularHomology_ofInclusion_of_homotopyRel {X : TopCat.{w}} {s t : Set X}
    (hst : s ⊆ t) (r : C(t, s))
    (G : ((ContinuousMap.inclusion hst).comp r).HomotopyRel (ContinuousMap.id t)
      {x | (x : X) ∈ s})
    (R : C) (n : ℕ) :
    IsZero ((ofInclusion hst).singularHomology R n) := by
  -- The identity of the pair is homotopic to the retraction, which factors through `s`.
  refine isZero_singularHomology_of_homotopy
    (f := ofInclusionMap hst hst ((ContinuousMap.inclusion hst).comp r) fun x _ ↦ (r x).property)
    ?_ (TopCat.ofHom r)
    (by ext x; exact (ofInclusionMap_fst_apply (hst := hst) (hst' := hst) _ _ x).symm) R n
  rw [← ofInclusionMap_id]
  refine ofInclusionHomotopy G.symm.toHomotopy fun τ x hx ↦ ?_
  have h : G.symm.toHomotopy (τ, x) = x := G.symm.eq_fst τ hx
  rw [h]
  exact hx

/-- **A pair whose ambient space deforms into its subspace has no relative homology.** If a
homotopy from the identity of `X` to a map `ρ` with values in `S` keeps `S` inside `S` at every
time, the relative singular homology of `(X, S)` vanishes in every degree. Unlike
`TopPair.isZero_singularHomology_ofInclusion_of_homotopyRel`, the homotopy need not fix `S`. -/
theorem isZero_singularHomology_ofSubset_of_homotopy {X : TopCat.{w}} {S : Set X} {ρ : X ⟶ X}
    (H : (TopCat.Hom.hom (𝟙 X)).Homotopy ρ.hom)
    (hS : ∀ (τ : unitInterval) (x : X), x ∈ S → H (τ, x) ∈ S) (hρ : ∀ x, ρ x ∈ S) (R : C)
    (n : ℕ) : IsZero ((ofSubset S).singularHomology R n) := by
  refine isZero_singularHomology_of_homotopy (f := ofSubsetMap ρ fun x _ ↦ hρ x) ?_
    (TopCat.ofHom ⟨fun x ↦ ⟨ρ x, hρ x⟩, by fun_prop⟩)
    (by ext x; exact (ofSubsetMap_fst_apply ρ _ x).symm) R n
  rw [← ofSubsetMap_id (B := S) fun _ hx ↦ hx]
  exact ofSubsetHomotopy H hS

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

/-- A homotopy equivalence induces isomorphisms on the homology of the singular simplicial sets,
in the form `SSet.homologyMap (TopCat.toSSet.map _)` used for the homology of pairs. -/
theorem isIso_homologyMap (n : ℕ) :
    IsIso (SSet.homologyMap (TopCat.toSSet.map (TopCat.ofHom e.toFun)) R n) :=
  -- `((singularHomologyFunctor C n).obj R).map` is `SSet.homologyMap ∘ TopCat.toSSet.map` by
  -- definition.
  (e.singularHomologyIso R n).isIso_hom

end ContinuousMap.HomotopyEquiv

namespace TopPair

variable {C : Type u} [Category.{v} C] [HasCoproducts.{w} C] [Abelian C]

/-- **A homotopy equivalence of pairs induces isomorphisms on relative singular homology.** A map
of pairs `f : (X, A) ⟶ (X', A')` whose maps of spaces `X → X'` and `A → A'` are homotopy
equivalences induces isomorphisms `Hₙ(X, A) ≅ Hₙ(X', A')`, by the five lemma. -/
theorem isIso_singularHomologyMap_of_homotopyEquiv {P P' : TopPair.{w}} (f : P ⟶ P')
    (e₁ : ContinuousMap.HomotopyEquiv P.fst P'.fst) (e₂ : ContinuousMap.HomotopyEquiv P.snd P'.snd)
    (h₁ : Hom.fst f = TopCat.ofHom e₁.toFun) (h₂ : Hom.snd f = TopCat.ofHom e₂.toFun) (R : C)
    (n : ℕ) : IsIso (P.singularHomologyMap f R n) := by
  have hfst (m : ℕ) : IsIso (SSet.homologyMap (TopCat.toSSet.map (Hom.fst f)) R m) :=
    h₁ ▸ e₁.isIso_homologyMap R m
  have hsnd (m : ℕ) : IsIso (SSet.homologyMap (TopCat.toSSet.map (Hom.snd f)) R m) :=
    h₂ ▸ e₂.isIso_homologyMap R m
  exact isIso_singularHomologyMap_of_isIso R f n (hfst n) (hsnd n) (fun m _ ↦ hfst m)
    fun m _ ↦ hsnd m

/-- **The relative homology of a homotopy model of a pair.** Let `s ⊆ t` be subsets of a space
`Y`, and let `j : s → X` be an embedding and `h : X ≃ₕ t` a homotopy equivalence with `h ∘ j` the
inclusion `s ⊆ t`. Then the pair `(X, j s)` has the relative singular homology of `(t, s)`, in
every degree and for every coefficient object. -/
theorem nonempty_singularHomology_ofInclusion_iso_of_homotopyEquiv {X Y : Type w}
    [TopologicalSpace X] [TopologicalSpace Y] {s t : Set Y} (hst : s ⊆ t) {j : C(s, X)}
    (hj : Topology.IsEmbedding j) (h : ContinuousMap.HomotopyEquiv X t)
    (hh : ∀ x, (h (j x) : Y) = x) (R : C) (n : ℕ) :
    Nonempty ((ofInclusion (X := TopCat.of X) (Set.subset_univ (Set.range j))).singularHomology
      R n ≅ (ofInclusion (X := TopCat.of Y) hst).singularHomology R n) := by
  -- On the total spaces the map of pairs is `h`, and on the subspaces it is `j⁻¹`.
  let φ := ofInclusionMap (X := TopCat.of X) (Y := TopCat.of Y) (Set.subset_univ (Set.range j))
    hst (h.toFun.restrict Set.univ) fun x ⟨w, hw⟩ ↦ by simp [← hw, hh]
  have := isIso_singularHomologyMap_of_homotopyEquiv φ
    ((Homeomorph.Set.univ X).toHomotopyEquiv.trans h) hj.toHomeomorph.symm.toHomotopyEquiv
    (by ext x; exact ofInclusionMap_fst_apply _ _ x)
    (by
      ext ⟨_, w, rfl⟩
      refine Subtype.ext ((ofInclusionMap_snd_apply _ _ _).trans ((hh w).trans ?_))
      exact congrArg Subtype.val (hj.toHomeomorph_symm_apply w).symm) R n
  exact ⟨asIso (TopPair.singularHomologyMap φ R n)⟩

end TopPair

namespace ContinuousMap

open AlgebraicTopology TauCeti

variable {X Y : Type w} [TopologicalSpace X] [TopologicalSpace Y]

/-- **Homotopy invariance** in the form `SSet.homologyMap (TopCat.toSSet.map _)` used for the
homology of pairs: homotopic maps induce the same map on singular homology, with coefficients `R`
in any category. -/
theorem Homotopic.homologyMap_eq {f g : C(X, Y)} (H : f.Homotopic g) {C : Type u}
    [Category.{v} C] [HasCoproducts.{w} C] [Preadditive C] [CategoryWithHomology C] (R : C)
    (n : ℕ) :
    SSet.homologyMap (TopCat.toSSet.map (TopCat.ofHom f)) R n =
      SSet.homologyMap (TopCat.toSSet.map (TopCat.ofHom g)) R n :=
  TopCat.Homotopy.congr_homologyMap_singularChainComplexFunctor H.some R n

/-- Homotopic continuous maps induce the same map on singular homology with coefficients in any
object `R`. -/
theorem singularHomologyFunctor_map_eq_of_homotopic {C : Type u} [Category.{v} C]
    [HasCoproducts.{w} C] [Preadditive C] [CategoryWithHomology C] (R : C) (n : ℕ)
    {Y Z : Type w} [TopologicalSpace Y] [TopologicalSpace Z] {g g' : C(Y, Z)}
    (H : g.Homotopic g') :
    ((singularHomologyFunctor C n).obj R).map (TopCat.ofHom g) =
      ((singularHomologyFunctor C n).obj R).map (TopCat.ofHom g') :=
  -- `((singularHomologyFunctor C n).obj R).map` is the homology of the map of singular chains by
  -- definition.
  H.homologyMap_eq R n

variable (k : Type w) [Ring k] (n : ℕ)

/-- Homotopic continuous maps induce the same map on singular homology. -/
theorem singularHomologyMap_eq_of_homotopic {Y Z : Type w} [TopologicalSpace Y]
    [TopologicalSpace Z] {g g' : C(Y, Z)} (H : g.Homotopic g') :
    singularHomologyMap k n g = singularHomologyMap k n g' :=
  congrArg ModuleCat.Hom.hom (singularHomologyFunctor_map_eq_of_homotopic (ModuleCat.of k k) n H)

/-- A continuous map with a left inverse up to homotopy is injective on singular homology. -/
theorem injective_singularHomologyMap_of_homotopic_comp_id {Y Z : Type w} [TopologicalSpace Y]
    [TopologicalSpace Z] {s : C(Y, Z)} {r : C(Z, Y)} (H : (r.comp s).Homotopic (.id Y)) :
    Function.Injective (singularHomologyMap k n s) :=
  Function.LeftInverse.injective (g := singularHomologyMap k n r) fun y ↦ by
    rw [← singularHomologyMap_comp, singularHomologyMap_eq_of_homotopic k n H,
      singularHomologyMap_id]

/-- A homotopy equivalence induces a bijection on singular homology. -/
theorem HomotopyEquiv.bijective_singularHomologyMap {Y Z : Type w}
    [TopologicalSpace Y] [TopologicalSpace Z]
    (e : ContinuousMap.HomotopyEquiv Y Z) : Function.Bijective (singularHomologyMap k n e.toFun) :=
  ConcreteCategory.bijective_of_isIso (e.singularHomologyIso (ModuleCat.of k k) n).hom

variable {k n} in
/-- Right multiplication by an element joined to `1` acts trivially on singular homology. -/
@[to_additive (dont_translate := k)
  /-- Right addition by an element joined to `0` acts trivially on singular homology. -/]
theorem singularHomologyMap_mulRight_of_joined {G : Type w} [TopologicalSpace G] [MulOneClass G]
    [ContinuousMul G] {g : G} (h : Joined 1 g)
    (x : ((singularChains k).obj (TopCat.of G)).homology n) :
    singularHomologyMap k n (ContinuousMap.mulRight g) x = x := by
  rw [singularHomologyMap_eq_of_homotopic k n h.homotopic_id_mulRight.symm, singularHomologyMap_id]

variable {k n} in
/-- In a path-connected topological monoid, right multiplication acts trivially on singular
homology. -/
@[to_additive (dont_translate := k) (attr := simp)
  /-- In a path-connected additive topological monoid, right addition acts trivially on singular
  homology. -/]
theorem singularHomologyMap_mulRight {G : Type w} [TopologicalSpace G] [MulOneClass G]
    [ContinuousMul G] [PathConnectedSpace G] (g : G)
    (x : ((singularChains k).obj (TopCat.of G)).homology n) :
    singularHomologyMap k n (ContinuousMap.mulRight g) x = x :=
  singularHomologyMap_mulRight_of_joined (PathConnectedSpace.joined 1 g) x

end ContinuousMap
