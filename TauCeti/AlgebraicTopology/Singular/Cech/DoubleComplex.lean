/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.TotalComplex
public import Mathlib.AlgebraicTopology.AlternatingFaceMapComplex
public import TauCeti.Topology.Category.TopCat.Cech.Nerve
public import TauCeti.AlgebraicTopology.Singular.Basic

/-!
# The Čech double complex of a family of open sets

A family of open sets gives a map from their disjoint union to the ambient space. Its Čech nerve
has the intersections of cover members in each degree, with face maps induced by forgetting an
index. Applying singular chains to each degree and then taking the alternating-face complex gives
commuting Čech and singular differentials. The total complex uses the usual sign on the vertical
differential. This is the unnormalized complex, whose degrees include tuples with repeated indices.

The construction uses Mathlib's `SimplicialObject.cechNerve`,
`alternatingFaceMapComplex`, and `HomologicalComplex₂.total`. Maps of covered spaces induce
chain maps. Its normalization to strictly increasing tuples and the comparison with
singular chains of the ambient space require a separate descent argument.

## References

* A. Hatcher, *Algebraic Topology*, Section 2.2, for Čech--singular chains of an open cover.
* J. McCleary, *A User's Guide to Spectral Sequences*, Chapters 1--2, for the total complex.
-/

public section

noncomputable section

open CategoryTheory Limits AlgebraicTopology TopologicalSpace Preadditive
open scoped Simplicial

universe v u

namespace TauCeti.TopCat

variable {X : TopCat.{u}} {ι : Type u} (U : ι → Opens X)

variable {C : Type v} [Category C] [Preadditive C] [HasZeroObject C]
  [HasCoproducts.{u} C] [HasCoproducts.{0} C] (R : C)

/-- The Čech nerve of the cover, with singular chains in every simplicial degree. -/
abbrev openCoverSingularNerve : SimplicialObject (ChainComplex C ℕ) :=
  ((SimplicialObject.whiskering TopCat.{u} (ChainComplex C ℕ)).obj
    ((singularChainComplexFunctor.{u} C).obj R)).obj
      ((SimplicialObject.cechNerve (C := TopCat.{u})).obj (openCoverArrow U))

/-- The augmented Čech nerve of the cover, with singular chains in every degree. -/
def openCoverAugmentedSingularNerve : SimplicialObject.Augmented (ChainComplex C ℕ) :=
  ((SimplicialObject.Augmented.whiskering TopCat.{u} (ChainComplex C ℕ)).obj
    ((singularChainComplexFunctor.{u} C).obj R)).obj (openCoverArrow U).augmentedCechNerve

/-- The bicomplex of Čech and singular chains of a family of opens. Its horizontal differential
is the alternating sum of the face maps, and its vertical differential is the singular boundary. -/
abbrev openCoverSingularBicomplex : HomologicalComplex₂ C (ComplexShape.down ℕ)
    (ComplexShape.down ℕ) :=
  (alternatingFaceMapComplex (ChainComplex C ℕ)).obj (openCoverSingularNerve U R)

omit [HasCoproducts.{0} C] [HasZeroObject C] in
/-- The column in Čech degree `p` is the singular chain complex of the `p`-th term of
the cover's Čech nerve. -/
theorem openCoverSingularBicomplex_X (p : ℕ) :
    (openCoverSingularBicomplex U R).X p =
      ((singularChainComplexFunctor.{u} C).obj R).obj
        ((openCoverArrow U).cechNerve.obj (Opposite.op ⦋p⦌)) :=
  (rfl)

omit [HasCoproducts.{0} C] [HasZeroObject C] in
/-- The vertical differential in each column is the singular boundary of the corresponding
Čech-nerve space. -/
theorem openCoverSingularBicomplex_vertical (p q : ℕ) :
    ((openCoverSingularBicomplex U R).X p).d (q + 1) q =
      (((singularChainComplexFunctor.{u} C).obj R).obj
        ((openCoverArrow U).cechNerve.obj (Opposite.op ⦋p⦌))).d (q + 1) q :=
  (rfl)

omit [HasCoproducts.{0} C] [HasZeroObject C] in
/-- A Čech face acts on each column by the induced singular-chain map. -/
theorem openCoverSingularNerve_δ (p : ℕ) (j : Fin (p + 2)) :
    (openCoverSingularNerve U R).δ j =
      ((singularChainComplexFunctor.{u} C).obj R).map ((openCoverArrow U).cechNerve.δ j) :=
  (rfl)

omit [HasCoproducts.{0} C] [HasZeroObject C] in
/-- The horizontal differential is the alternating sum of the singular-chain maps induced by
the face maps of the Čech nerve. -/
theorem openCoverSingularBicomplex_d (p : ℕ) :
    (openCoverSingularBicomplex U R).d (p + 1) p =
      ∑ j : Fin (p + 2), (-1 : ℤ) ^ (j : ℕ) • (openCoverSingularNerve U R).δ j :=
  alternatingFaceMapComplex_obj_d _ p

/-- The augmentation from the horizontal Čech complex to singular chains of the ambient space,
placed in Čech degree zero. -/
def openCoverSingularAugmentation :
    openCoverSingularBicomplex U R ⟶
      (ChainComplex.single₀ (ChainComplex C ℕ)).obj
        (((singularChainComplexFunctor.{u} C).obj R).obj X) :=
  AlternatingFaceMapComplex.ε.app (openCoverAugmentedSingularNerve U R)

omit [HasCoproducts.{0} C] in
/-- In Čech degree zero, the augmentation is the singular-chain map induced by the
projection of the first Čech nerve object onto the ambient space. -/
@[simp]
theorem openCoverSingularAugmentation_f_zero :
    (openCoverSingularAugmentation U R).f 0 =
      ((singularChainComplexFunctor.{u} C).obj R).map
        ((openCoverArrow U).augmentedCechNerve.hom.app (Opposite.op ⦋0⦌)) := by
  rw [openCoverSingularAugmentation, AlternatingFaceMapComplex.ε_app_f_zero]
  dsimp [openCoverAugmentedSingularNerve, SimplicialObject.Augmented.whiskering,
    SimplicialObject.Augmented.whiskeringObj]
  -- The generated whiskering map hides an identity comparison behind an opaque functor;
  -- expose that composite to use the identity law.
  change ((singularChainComplexFunctor.{u} C).obj R).map
    ((openCoverArrow U).augmentedCechNerve.hom.app (Opposite.op ⦋0⦌)) ≫ 𝟙 _ = _
  rw [Category.comp_id]
  rfl

/-- A map of covered spaces induces a map of their Čech--singular bicomplexes. -/
def openCoverSingularBicomplexMap {Y : TopCat.{u}} {κ : Type u} (V : κ → Opens Y)
    (f : X ⟶ Y) (r : ι → κ) (hf : ∀ i, Set.MapsTo f (U i) (V (r i))) :
    openCoverSingularBicomplex U R ⟶ openCoverSingularBicomplex V R :=
  (alternatingFaceMapComplex (ChainComplex C ℕ)).map <|
    ((SimplicialObject.whiskering TopCat.{u} (ChainComplex C ℕ)).obj
      ((singularChainComplexFunctor.{u} C).obj R)).map
        ((SimplicialObject.cechNerve (C := TopCat.{u})).map (openCoverArrowMap U V f r hf))

omit [HasZeroObject C] [HasCoproducts.{0} C] in
/-- The induced bicomplex map acts in each bidegree by the singular-chain map of the
corresponding map of Čech-nerve spaces. -/
@[simp]
theorem openCoverSingularBicomplexMap_f {Y : TopCat.{u}} {κ : Type u} (V : κ → Opens Y)
    (f : X ⟶ Y) (r : ι → κ) (hf : ∀ i, Set.MapsTo f (U i) (V (r i))) (p q : ℕ) :
    ((openCoverSingularBicomplexMap U R V f r hf).f p).f q =
      (((singularChainComplexFunctor.{u} C).obj R).map
        ((Arrow.mapCechNerve (openCoverArrowMap U V f r hf)).app
          (Opposite.op ⦋p⦌))).f q := by
  rfl

omit [HasZeroObject C] [HasCoproducts.{0} C] in
/-- The identity map of a cover induces the identity bicomplex map. -/
@[simp]
theorem openCoverSingularBicomplexMap_id :
    openCoverSingularBicomplexMap U R U (𝟙 X) id
      (fun i => by
        intro x hx
        exact hx) = 𝟙 _ := by
  simp [openCoverSingularBicomplexMap, openCoverSingularBicomplex,
    openCoverArrowMap_id,
    Arrow.mapCechNerve, SimplicialObject.cechNerve]

omit [HasZeroObject C] [HasCoproducts.{0} C] in
/-- Induced maps of Čech--singular bicomplexes respect composition. -/
theorem openCoverSingularBicomplexMap_comp {Y Z : TopCat.{u}} {κ τ : Type u}
    (V : κ → Opens Y) (W : τ → Opens Z) (f : X ⟶ Y) (g : Y ⟶ Z)
    (r : ι → κ) (s : κ → τ) (hf : ∀ i, Set.MapsTo f (U i) (V (r i)))
    (hg : ∀ j, Set.MapsTo g (V j) (W (s j))) :
    openCoverSingularBicomplexMap U R W (f ≫ g) (s ∘ r)
        (fun i _ hx => hg (r i) (hf i hx)) =
      openCoverSingularBicomplexMap U R V f r hf ≫
        openCoverSingularBicomplexMap V R W g s hg := by
  -- Expose the composite of the two functor maps so `openCoverArrowMap_comp` can
  -- rewrite its inner arrow before applying functoriality.
  change (alternatingFaceMapComplex (ChainComplex C ℕ)).map
      (((SimplicialObject.whiskering TopCat.{u} (ChainComplex C ℕ)).obj
        ((singularChainComplexFunctor.{u} C).obj R)).map
        ((SimplicialObject.cechNerve (C := TopCat.{u})).map
          (openCoverArrowMap U W (f ≫ g) (s ∘ r)
            (fun i _ hx => hg (r i) (hf i hx))))) = _
  rw [openCoverArrowMap_comp]
  dsimp [openCoverSingularBicomplexMap]
  simp only [Functor.map_comp, Functor.whiskerRight_comp]

/-- The total Čech--singular complex of a family of open sets. -/
@[expose] def openCoverSingularTotal : ChainComplex C ℕ :=
  (openCoverSingularBicomplex U R).total (ComplexShape.down ℕ)

omit [HasZeroObject C] in
/-- The total-complex construction used by `openCoverSingularTotal`. -/
theorem openCoverSingularTotal_def :
    openCoverSingularTotal U R =
      (openCoverSingularBicomplex U R).total (ComplexShape.down ℕ) := by
  rfl

/-- The graded object in total degree `n` is the coproduct of the bidegrees summing to `n`.
This is the summand inclusion into that coproduct. -/
noncomputable def openCoverSingularTotalInclusion (p q n : ℕ)
    (h : ComplexShape.π (ComplexShape.down ℕ) (ComplexShape.down ℕ)
      (ComplexShape.down ℕ) (p, q) = n) :
    ((openCoverSingularBicomplex U R).X p).X q ⟶
      (openCoverSingularTotal U R).X n := by
  exact HomologicalComplex₂.ιTotal (openCoverSingularBicomplex U R)
    (ComplexShape.down ℕ) p q n h

omit [HasZeroObject C] in
/-- The total differential after inclusion of a bidegree summand is the sum of its signed
horizontal and vertical contributions. -/
theorem openCoverSingularTotalInclusion_d (p q n : ℕ)
    (h : ComplexShape.π (ComplexShape.down ℕ) (ComplexShape.down ℕ)
      (ComplexShape.down ℕ) (p, q) = n + 1) :
    openCoverSingularTotalInclusion U R p q (n + 1) h ≫
        (openCoverSingularTotal U R).d (n + 1) n =
      (openCoverSingularBicomplex U R).d₁ (ComplexShape.down ℕ) p q n +
      (openCoverSingularBicomplex U R).d₂ (ComplexShape.down ℕ) p q n := by
  -- The total differential is defined as `D₁ + D₂`; expose its two terms to
  -- apply the separate inclusion formulas `ι_D₁` and `ι_D₂`.
  change HomologicalComplex₂.ιTotal (openCoverSingularBicomplex U R)
      (ComplexShape.down ℕ) p q (n + 1) h ≫
      ((openCoverSingularBicomplex U R).D₁ (ComplexShape.down ℕ) (n + 1) n +
        (openCoverSingularBicomplex U R).D₂ (ComplexShape.down ℕ) (n + 1) n) = _
  rw [comp_add]
  simp only [HomologicalComplex₂.ι_D₁, HomologicalComplex₂.ι_D₂]

/-- A map of covered spaces induces a chain map between the total Čech--singular complexes. -/
def openCoverSingularTotalMap {Y : TopCat.{u}} {κ : Type u} (V : κ → Opens Y)
    (f : X ⟶ Y) (r : ι → κ) (hf : ∀ i, Set.MapsTo f (U i) (V (r i))) :
    openCoverSingularTotal U R ⟶ openCoverSingularTotal V R :=
  HomologicalComplex₂.total.map (openCoverSingularBicomplexMap U R V f r hf)
    (ComplexShape.down ℕ)

omit [HasZeroObject C] in
/-- The total map on a summand is induced by the bicomplex map in that bidegree. -/
@[reassoc (attr := simp)]
theorem openCoverSingularTotalMap_inclusion {Y : TopCat.{u}} {κ : Type u}
    (V : κ → Opens Y) (f : X ⟶ Y) (r : ι → κ)
    (hf : ∀ i, Set.MapsTo f (U i) (V (r i))) (p q n : ℕ)
    (h : ComplexShape.π (ComplexShape.down ℕ) (ComplexShape.down ℕ)
      (ComplexShape.down ℕ) (p, q) = n) :
    openCoverSingularTotalInclusion U R p q n h ≫
        (openCoverSingularTotalMap U R V f r hf).f n =
      ((openCoverSingularBicomplexMap U R V f r hf).f p).f q ≫
        openCoverSingularTotalInclusion V R p q n h := by
  exact HomologicalComplex₂.ιTotal_map
      (K := openCoverSingularBicomplex U R)
      (L := openCoverSingularBicomplex V R)
      (φ := openCoverSingularBicomplexMap U R V f r hf)
      (ComplexShape.down ℕ) p q n h

omit [HasZeroObject C] in
/-- The identity map of a cover induces the identity total-complex map. -/
@[simp]
theorem openCoverSingularTotalMap_id :
    openCoverSingularTotalMap U R U (𝟙 X) id (fun _ _ h => h) = 𝟙 _ := by
  -- Reveal the total functor map so `simp` can use the bicomplex identity law.
  change HomologicalComplex₂.total.map _ _ = 𝟙 _
  simp

omit [HasZeroObject C] in
/-- Induced maps of total Čech--singular complexes respect composition. -/
theorem openCoverSingularTotalMap_comp {Y Z : TopCat.{u}} {κ τ : Type u}
    (V : κ → Opens Y) (W : τ → Opens Z) (f : X ⟶ Y) (g : Y ⟶ Z)
    (r : ι → κ) (s : κ → τ) (hf : ∀ i, Set.MapsTo f (U i) (V (r i)))
    (hg : ∀ j, Set.MapsTo g (V j) (W (s j))) :
    openCoverSingularTotalMap U R W (f ≫ g) (s ∘ r)
        (fun i _ hx => hg (r i) (hf i hx)) =
      openCoverSingularTotalMap U R V f r hf ≫
        openCoverSingularTotalMap V R W g s hg := by
  -- Reveal the total functor map so the bicomplex composition law can rewrite
  -- its argument before applying `HomologicalComplex₂.total.map_comp`.
  change HomologicalComplex₂.total.map
      (openCoverSingularBicomplexMap U R W (f ≫ g) (s ∘ r)
        (fun i _ hx => hg (r i) (hf i hx))) (ComplexShape.down ℕ) = _
  rw [openCoverSingularBicomplexMap_comp]
  exact HomologicalComplex₂.total.map_comp
    (φ := openCoverSingularBicomplexMap U R V f r hf)
    (ψ := openCoverSingularBicomplexMap V R W g s hg) (ComplexShape.down ℕ)

end TauCeti.TopCat
