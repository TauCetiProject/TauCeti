/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Cohomology.Relative
public import TauCeti.AlgebraicTopology.Singular.Homotopy.Invariance

/-!
# Homotopy invariance of singular cohomology

Singular cochains are obtained from singular chains by applying `Hom(-, M)`, and an additive
functor carries chain homotopies to chain homotopies.  So the chain homotopy that a homotopy of
maps induces on singular chains gives a cochain homotopy on singular cochains, and homotopic
maps induce the same map on singular cohomology.  Maps that are inverse to each other up to
homotopy therefore induce isomorphisms on singular cohomology.  This is the homotopy axiom of
Eilenberg--Steenrod for the singular cohomology theory, in both its absolute and its relative
form.  The chain homotopies it is deduced from are Mathlib's `SSet.Homotopy.chainComplexMap`,
applied to the simplicial homotopy `TopCat.Homotopy.toSSet`, for a space, and
`TopPair.Homotopy.singularChainComplexMap` for a pair.  The homology counterparts of the results
below are `Mathlib/AlgebraicTopology/SingularHomology/HomotopyInvariance.lean`
(F. Odermatt, J. Riou) for a space and
`TauCeti/AlgebraicTopology/Singular/Homotopy/Invariance.lean` for a pair.

## Main results

* `TopCat.Homotopy.singularCochainComplexMap` and `TopPair.Homotopy.singularCochainComplexMap`:
  the cochain homotopy induced by a homotopy of maps of spaces, respectively of pairs.
* `TopCat.Homotopy.congr_singularCohomologyMap` and
  `TopPair.Homotopy.congr_singularCohomologyMap`: homotopic maps induce the same map on singular
  cohomology.
* `TopCat.isIso_singularCohomologyMap` and `TopPair.isIso_singularCohomologyMap`: a map with a
  homotopy inverse induces an isomorphism on singular cohomology.
* `TopCat.singularCohomologyMap_lift_const_eq_of_joined`: restrictions of a class on `X × Y` to
  the slices through two points joined by a path agree.
* `TopPair.isIso_singularCohomologyMap_ofSubsetMap_id_of_homotopy`: enlarging the subspace of a
  pair to a neighbourhood which deforms back into it does not change relative cohomology.
* `TopPair.isIso_singularCohomologyMap_ofInclusionMap_inclusion_of_homotopyRel`: a strong
  deformation retraction of the ambient space onto an intermediate subset does not change relative
  cohomology.
* `TopPair.isZero_singularCohomology_of_homotopy` and
  `TopPair.isZero_singularCohomology_ofInclusion_of_homotopyRel`: a pair whose ambient space
  deforms into its subspace has no relative cohomology.
* `ContinuousMap.HomotopyEquiv.isIso_singularCohomologyMap` and
  `ContinuousMap.HomotopyEquiv.singularCohomologyIso`: the induced isomorphism on singular
  cohomology for a bundled homotopy equivalence of spaces.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 3.1.
* S. Eilenberg and N. Steenrod, *Foundations of Algebraic Topology*, Chapter VII.
-/

@[expose] public section

noncomputable section

open CategoryTheory Limits

universe w v u

namespace TopCat.Homotopy

variable {X Y : TopCat.{w}} {f g : X ⟶ Y} (H : Homotopy f g)
  {C : Type u} [Category.{v} C] [HasCoproducts.{w} C] [Abelian C] (R : C)
  (k : Type*) [Ring k] [Linear k C] (M : C)

/-- A homotopy between continuous maps induces a cochain homotopy between the induced maps of
singular cochain complexes. -/
@[no_expose]
def singularCochainComplexMap :
    _root_.Homotopy (singularCochainComplexMap (R := R) (k := k) (M := M) f)
      (singularCochainComplexMap g) :=
  (H.toSSet.chainComplexMap R).linearYonedaFunctorMap k M

/-- The cochain homotopy induced by a homotopy of continuous maps is precomposition with the
chain homotopy it induces on singular chains. -/
@[simp]
lemma singularCochainComplexMap_hom_apply (p q : ℕ) (x : (Y.singularCochainComplex R k M).X p) :
    ConcreteCategory.hom ((H.singularCochainComplexMap R k M).hom p q) x =
        (H.toSSet.chainComplexMap R).hom q p ≫ x :=
  (H.toSSet.chainComplexMap R).linearYonedaFunctorMap_hom_apply k M p q x

include H in
/-- Homotopic continuous maps induce the same map on singular cohomology. -/
lemma congr_singularCohomologyMap (n : ℕ) :
    TopCat.singularCohomologyMap (R := R) (k := k) (M := M) f n =
      TopCat.singularCohomologyMap g n :=
  (H.singularCochainComplexMap R k M).homologyMap_eq n

end TopCat.Homotopy

namespace TopCat

variable {X Y : TopCat.{w}} {C : Type u} [Category.{v} C] [HasCoproducts.{w} C] [Abelian C]

/-- Continuous maps which are inverse to each other up to homotopy induce isomorphisms on
singular cohomology. -/
lemma isIso_singularCohomologyMap (f : X ⟶ Y) (f' : Y ⟶ X) (H : Homotopy (f ≫ f') (𝟙 X))
    (H' : Homotopy (f' ≫ f) (𝟙 Y)) (R : C) (k : Type*) [Ring k] [Linear k C] (M : C) (n : ℕ) :
    IsIso (TopCat.singularCohomologyMap (R := R) (k := k) (M := M) f n) := by
  refine ⟨TopCat.singularCohomologyMap f' n, ?_, ?_⟩
  · rw [← singularCohomologyMap_comp, H'.congr_singularCohomologyMap R k M n,
      singularCohomologyMap_id]
  · rw [← singularCohomologyMap_comp, H.congr_singularCohomologyMap R k M n,
      singularCohomologyMap_id]

/-- **Restrictions to slices through joined points agree**: if `x` and `x'` are joined by a path,
then for `g : Z ⟶ Y` the maps `z ↦ (x, g z)` and `z ↦ (x', g z)` into `X × Y` are homotopic, so
they induce the same map on singular cohomology. For `g = 𝟙 Y` these are the restrictions to the
slices `{x} × Y` and `{x'} × Y`. -/
@[reassoc, elementwise]
lemma singularCohomologyMap_lift_const_eq_of_joined {Z : TopCat.{w}} {x x' : X} (h : Joined x x')
    {g : Z ⟶ Y} {R : C} {k : Type*} [Ring k] [Linear k C] {M : C} (n : ℕ) :
    TopCat.singularCohomologyMap (R := R) (k := k) (M := M)
        (CartesianMonoidalCategory.lift (ofHom (ContinuousMap.const Z x)) g) n =
      TopCat.singularCohomologyMap
        (CartesianMonoidalCategory.lift (ofHom (ContinuousMap.const Z x')) g) n := by
  -- pairing a path from `x` to `x'` with the constant homotopy at `g` connects the two maps
  have hlift (x₁ : X) : (ContinuousMap.const Z x₁).prodMk g.hom =
      (CartesianMonoidalCategory.lift (ofHom (ContinuousMap.const Z x₁)) g).hom := by
    ext z
    · exact (congrArg Prod.fst (TopCat.lift_apply (x := z))).symm
    · exact (congrArg Prod.snd (TopCat.lift_apply (x := z))).symm
  exact Homotopy.congr_singularCohomologyMap
    ((h.somePath.toHomotopyConst.prodMk (.refl g.hom)).cast (hlift x) (hlift x')) R k M n

end TopCat

namespace ContinuousMap.HomotopyEquiv

variable {X Y : Type w} [TopologicalSpace X] [TopologicalSpace Y]
  (e : ContinuousMap.HomotopyEquiv X Y)
  {C : Type u} [Category.{v} C] [HasCoproducts.{w} C] [Abelian C] (R : C)
  (k : Type*) [Ring k] [Linear k C] (M : C)

/-- A homotopy equivalence induces isomorphisms on singular cohomology in every degree. -/
lemma isIso_singularCohomologyMap (n : ℕ) :
    IsIso (TopCat.singularCohomologyMap (R := R) (k := k) (M := M) (TopCat.ofHom e.toFun) n) :=
  TopCat.isIso_singularCohomologyMap _ (TopCat.ofHom e.invFun) e.left_inv.some e.right_inv.some
    R k M n

/-- A homotopy equivalence induces an isomorphism on singular cohomology in every degree, with
forward map induced by pullback along `e` and inverse induced by pullback along `e.symm`. -/
@[no_expose]
def singularCohomologyIso (n : ℕ) :
    (TopCat.of Y).singularCohomology R k M n ≅ (TopCat.of X).singularCohomology R k M n where
  hom := TopCat.singularCohomologyMap (TopCat.ofHom e.toFun) n
  inv := TopCat.singularCohomologyMap (TopCat.ofHom e.invFun) n
  hom_inv_id := by
    rw [← TopCat.singularCohomologyMap_comp, ← TopCat.singularCohomologyMap_id]
    exact TopCat.Homotopy.congr_singularCohomologyMap e.right_inv.some R k M n
  inv_hom_id := by
    rw [← TopCat.singularCohomologyMap_comp, ← TopCat.singularCohomologyMap_id]
    exact TopCat.Homotopy.congr_singularCohomologyMap e.left_inv.some R k M n

/-- The forward map of `ContinuousMap.HomotopyEquiv.singularCohomologyIso` is pullback along `e`. -/
@[simp]
lemma singularCohomologyIso_hom (n : ℕ) :
    (e.singularCohomologyIso R k M n).hom =
      TopCat.singularCohomologyMap (TopCat.ofHom e.toFun) n := (rfl)

/-- The inverse map of `ContinuousMap.HomotopyEquiv.singularCohomologyIso` is pullback along
`e.symm`. -/
@[simp]
lemma singularCohomologyIso_inv (n : ℕ) :
    (e.singularCohomologyIso R k M n).inv =
      TopCat.singularCohomologyMap (TopCat.ofHom e.invFun) n := (rfl)

end ContinuousMap.HomotopyEquiv

namespace TopPair.Homotopy

variable {P P' : TopPair.{w}} {f g : P ⟶ P'} (H : Homotopy f g)
  {C : Type u} [Category.{v} C] [HasCoproducts.{w} C] [Abelian C] (R : C)
  (k : Type*) [Ring k] [Linear k C] (M : C)

/-- A homotopy between maps of topological pairs induces a cochain homotopy between the induced
maps of relative singular cochain complexes. -/
@[no_expose]
def singularCochainComplexMap :
    _root_.Homotopy (singularCochainComplexMap (R := R) (k := k) (M := M) f)
      (singularCochainComplexMap g) :=
  (H.singularChainComplexMap R).linearYonedaFunctorMap k M

/-- The cochain homotopy induced by a homotopy of maps of pairs is precomposition with the chain
homotopy it induces on relative singular chains. -/
@[simp]
lemma singularCochainComplexMap_hom_apply (p q : ℕ) (x : (P'.singularCochainComplex R k M).X p) :
    ConcreteCategory.hom ((H.singularCochainComplexMap R k M).hom p q) x =
        (H.singularChainComplexMap R).hom q p ≫ x :=
  (H.singularChainComplexMap R).linearYonedaFunctorMap_hom_apply k M p q x

include H in
/-- Homotopic maps of topological pairs induce the same map on relative singular cohomology. -/
lemma congr_singularCohomologyMap (n : ℕ) :
    TopPair.singularCohomologyMap (R := R) (k := k) (M := M) f n =
      TopPair.singularCohomologyMap g n :=
  (H.singularCochainComplexMap R k M).homologyMap_eq n

end TopPair.Homotopy

namespace TopPair

variable {P P' : TopPair.{w}} {C : Type u} [Category.{v} C] [HasCoproducts.{w} C] [Abelian C]

/-- Maps of topological pairs which are inverse to each other up to homotopy induce isomorphisms
on relative singular cohomology. -/
lemma isIso_singularCohomologyMap (f : P ⟶ P') (f' : P' ⟶ P) (H : Homotopy (f ≫ f') (𝟙 P))
    (H' : Homotopy (f' ≫ f) (𝟙 P')) (R : C) (k : Type*) [Ring k] [Linear k C] (M : C) (n : ℕ) :
    IsIso (TopPair.singularCohomologyMap (R := R) (k := k) (M := M) f n) := by
  refine ⟨TopPair.singularCohomologyMap f' n, ?_, ?_⟩
  · rw [← singularCohomologyMap_comp, H'.congr_singularCohomologyMap R k M n,
      singularCohomologyMap_id]
  · rw [← singularCohomologyMap_comp, H.congr_singularCohomologyMap R k M n,
      singularCohomologyMap_id]

/-- **A pair whose identity deforms into its subspace has no relative cohomology**: if the identity
of `P` is homotopic, as a map of pairs, to a map whose map of ambient spaces factors through the
subspace, as when the subspace is a strong deformation retract, then the relative singular
cohomology of `P` vanishes in every degree. -/
lemma isZero_singularCohomology_of_homotopy {f : P ⟶ P} (H : Homotopy (𝟙 P) f)
    (g : P.fst ⟶ P.snd) (hg : g ≫ P.map = Hom.fst f) (R : C)
    (k : Type*) [Ring k] [Linear k C] (M : C) (n : ℕ) :
    IsZero (P.singularCohomology R k M n) := by
  rw [IsZero.iff_id_eq_zero, ← singularCohomologyMap_id, H.congr_singularCohomologyMap R k M n]
  exact singularCohomologyMap_eq_zero_of_fac R k M f g hg n

/-- **Enlarging the subspace along a deformation.** Let `B ⊆ N` be subsets of `X` and let `H` be a
homotopy from the identity of `X` to a map `ρ` carrying `N` into `B`.  If `H` keeps `B` inside `B`
and `N` inside `N` at every time, the inclusion `(X, B) ⟶ (X, N)` induces isomorphisms on relative
singular cohomology: `ρ` is a homotopy inverse as a map of pairs.  This is the cohomology form of
`TopPair.isIso_singularHomologyMap_ofSubsetMap_id_of_homotopy`. -/
lemma isIso_singularCohomologyMap_ofSubsetMap_id_of_homotopy {X : TopCat.{w}} {B N : Set X}
    (hBN : Set.MapsTo (𝟙 X) B N) {ρ : X ⟶ X} (H : (TopCat.Hom.hom (𝟙 X)).Homotopy ρ.hom)
    (hB : ∀ (τ : unitInterval) (x : X), x ∈ B → H (τ, x) ∈ B)
    (hN : ∀ (τ : unitInterval) (x : X), x ∈ N → H (τ, x) ∈ N) (hρ : Set.MapsTo ρ N B) (R : C)
    (k : Type*) [Ring k] [Linear k C] (M : C) (n : ℕ) :
    IsIso (TopPair.singularCohomologyMap (R := R) (k := k) (M := M) (ofSubsetMap (𝟙 X) hBN) n) := by
  refine isIso_singularCohomologyMap _ (ofSubsetMap ρ hρ) ?_ ?_ R k M n
  · rw [← ofSubsetMap_comp _ _ hBN hρ (hρ.comp hBN), ← ofSubsetMap_id (B := B) fun _ hx ↦ hx]
    simpa only [Category.id_comp] using (ofSubsetHomotopy H hB).symm
  · rw [← ofSubsetMap_comp _ _ hρ hBN (hBN.comp hρ), ← ofSubsetMap_id (B := N) fun _ hx ↦ hx]
    simpa only [Category.comp_id] using (ofSubsetHomotopy H hN).symm

/-- **A strong deformation retraction of the ambient space induces isomorphisms on relative
singular cohomology.** If `s ⊆ c ⊆ t` and `t` deformation retracts onto `c` relative to `c`, the
inclusion `(c, s) ⟶ (t, s)` induces isomorphisms on relative singular cohomology.  This is the
cohomology form of `TopPair.isIso_singularHomologyMap_ofInclusionMap_inclusion_of_homotopyRel`. -/
theorem isIso_singularCohomologyMap_ofInclusionMap_inclusion_of_homotopyRel {X : TopCat.{w}}
    {s c t : Set X} (hsc : s ⊆ c) (hct : c ⊆ t) (r : C(t, c))
    (G : ((ContinuousMap.inclusion hct).comp r).HomotopyRel (ContinuousMap.id t)
      {x | (x : X) ∈ c})
    (R : C) (k : Type*) [Ring k] [Linear k C] (M : C) (n : ℕ) :
    IsIso (TopPair.singularCohomologyMap (R := R) (k := k) (M := M)
      (ofInclusionMap hsc (hsc.trans hct) (ContinuousMap.inclusion hct)
        fun _ hx ↦ by simpa using hx) n) := by
  -- The retraction fixes every point of `c`, in particular every point of `s`.
  have hrc (x : t) (hx : (x : X) ∈ c) : (r x : X) = x :=
    congrArg Subtype.val (G.fst_eq_snd (x := x) hx)
  have hrs (x : t) (hx : (x : X) ∈ s) : (r x : X) ∈ s := (hrc x (hsc hx)).symm ▸ hx
  refine isIso_singularCohomologyMap _ (ofInclusionMap (hsc.trans hct) hsc r hrs) ?_ ?_ R k M n
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

/-- **A pair with a strong deformation retraction onto its subspace has no relative cohomology.**
If `s ⊆ t` and `t` deformation retracts onto `s` relative to `s`, the relative singular cohomology
of `(t, s)` vanishes in every degree. -/
theorem isZero_singularCohomology_ofInclusion_of_homotopyRel {X : TopCat.{w}} {s t : Set X}
    (hst : s ⊆ t) (r : C(t, s))
    (G : ((ContinuousMap.inclusion hst).comp r).HomotopyRel (ContinuousMap.id t)
      {x | (x : X) ∈ s})
    (R : C) (k : Type*) [Ring k] [Linear k C] (M : C) (n : ℕ) :
    IsZero ((ofInclusion hst).singularCohomology R k M n) := by
  refine isZero_singularCohomology_of_homotopy
    (f := ofInclusionMap hst hst ((ContinuousMap.inclusion hst).comp r) fun x _ ↦ (r x).property)
    ?_ (TopCat.ofHom r)
    (by ext x; exact (ofInclusionMap_fst_apply (hst := hst) (hst' := hst) _ _ x).symm) R k M n
  rw [← ofInclusionMap_id]
  refine ofInclusionHomotopy G.symm.toHomotopy fun τ x hx ↦ ?_
  have h : G.symm.toHomotopy (τ, x) = x := G.symm.eq_fst τ hx
  rw [h]
  exact hx

end TopPair
