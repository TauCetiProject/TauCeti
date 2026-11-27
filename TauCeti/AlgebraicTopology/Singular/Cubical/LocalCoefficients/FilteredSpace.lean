/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.SpectralSequence.Filtered.Naturality
public import TauCeti.AlgebraicTopology.Singular.Cubical.LocalCoefficients.Comparison.Homotopy
public import TauCeti.AlgebraicTopology.Singular.Twisted.FilteredSpace
import TauCeti.Algebra.Homology.Embedding.ExtendSubobject

/-!
# The spectral sequence of a filtered space with local coefficients on cubical chains

Let `L` be a local coefficient system on a space `Y` and `X : ℤ → Set Y` an increasing family of
subsets. The normalized cubical chains of the `X q` with coefficients in the restrictions of `L`
form an increasing filtration of the normalized cubical chains of `Y` with coefficients in `L`
(`TauCeti.LocalCoefficientSystem.twistedCubicalChainFiltration`): the inclusion of a subspace
induces a monomorphism of normalized cubical chains with local coefficients
(`TauCeti.LocalCoefficientSystem.mono_normalizedTwistedCubicalChainComplexMap`). This is the
cubical counterpart of the filtration of simplicial singular chains with local coefficients,
`TauCeti.LocalCoefficientSystem.twistedChainFiltration`. Over the skeletal filtration of the base
of a fibration, its spectral sequence is the Serre spectral sequence with local coefficients.

The comparison map `TauCeti.LocalCoefficientSystem.twistedCubicalToSingularMap` from cubical to
simplicial chains with local coefficients is natural in the space
(`TauCeti.LocalCoefficientSystem.twistedCubicalToSingularMap_naturality`), so it carries the
cubical chains of each `X q` into the simplicial chains of `X q`: it is a morphism of filtered
complexes (`TauCeti.LocalCoefficientSystem.twistedCubicalToSingularFiltrationMap`). On every stage
it is the comparison map of `X q` with the restricted system, a quasi-isomorphism
(`TauCeti.LocalCoefficientSystem.quasiIso_twistedCubicalToSingularFiltrationMap_app`). So it
induces an isomorphism of the spectral objects of the two filtrations
(`TauCeti.LocalCoefficientSystem.twistedCubicalSingularSpectralObjectIso`), and hence of their
spectral sequences on every page, from the first page on
(`TauCeti.LocalCoefficientSystem.twistedCubicalSingularSpectralSequenceIso`), with no boundedness
or exhaustiveness assumption on the filtration. On the abutments it is the map in homology of the
comparison map of `Y`
(`TauCeti.LocalCoefficientSystem.twistedCubicalSingularSpectralObjectIso_hom_abutment_comp`).

## Main definitions

* `TauCeti.LocalCoefficientSystem.twistedCubicalChainFiltration L X`: the filtration of the
  normalized cubical chains of `Y` with coefficients in `L` by those of the `X q`.
* `TauCeti.LocalCoefficientSystem.twistedCubicalToSingularFiltrationMap`: the comparison map as a
  morphism of filtered complexes.
* `TauCeti.LocalCoefficientSystem.twistedCubicalSingularSpectralObjectIso`,
  `TauCeti.LocalCoefficientSystem.twistedCubicalSingularSpectralSequenceIso`: the isomorphisms of
  spectral objects and of spectral sequences it induces.

## References

* J.-P. Serre, *Homologie singulière des espaces fibrés. Applications*, Ann. of Math. 54 (1951),
  425–505, Chapter II (cubical chains with local coefficients and the spectral sequence of a
  fibration).
* W. S. Massey, *Singular Homology Theory*, GTM 70, Springer, 1980, Chapters II and VII (the
  comparison of cubical and simplicial chains).
* J. McCleary, *A User's Guide to Spectral Sequences*, 2nd ed., Cambridge University Press, 2001,
  Section 2.2 and Theorem 3.5 (the comparison theorem).
-/

public section

noncomputable section

open CategoryTheory Limits HomologicalComplex

universe u v w

namespace TauCeti

namespace LocalCoefficientSystem

variable {R : Type u} [Ring R] {Y : TopCat.{v}}

/-! ### The cubical filtration -/

section Filtration

variable (L : LocalCoefficientSystem.{u, v, w} R Y) (X : ℤ → Set Y)

/-- The inclusion of the normalized cubical chains of `X q`, with coefficients in the restriction
of `L`, into those of `Y`, with both chain complexes reindexed as cochain complexes in nonpositive
degrees along `n ↦ -n`. -/
def twistedCubicalChainFiltrationι (q : ℤ) :
    ((pullback (X := TopCat.of ↥(X q)) (ContinuousMap.subtypeVal (X q))).obj
        L).normalizedTwistedCubicalChainComplex.extend ComplexShape.embeddingDownNat ⟶
      L.normalizedTwistedCubicalChainComplex.extend ComplexShape.embeddingDownNat :=
  extendMap (normalizedTwistedCubicalChainComplexMap (X := TopCat.of ↥(X q))
    (ContinuousMap.subtypeVal (X q)) L) _

/-- The inclusion of the cubical chains of `X q` is induced by the inclusion of the subspace
`X q`. -/
lemma twistedCubicalChainFiltrationι_def (q : ℤ) :
    twistedCubicalChainFiltrationι L X q =
      extendMap (normalizedTwistedCubicalChainComplexMap (X := TopCat.of ↥(X q))
        (ContinuousMap.subtypeVal (X q)) L) ComplexShape.embeddingDownNat :=
  (rfl)

/-- The cubical chains of `X q` form a subcomplex of those of `Y`, also after reindexing. -/
instance (q : ℤ) : Mono (twistedCubicalChainFiltrationι L X q) := by
  rw [twistedCubicalChainFiltrationι]
  exact mono_extendMap _ _

/-- **The filtration of cubical chains with local coefficients by subspaces.** The normalized
cubical chains of `Y` with coefficients in `L` are filtered by those of the subsets `X q`, with the
coefficients restricted, and with the chain complexes reindexed as cochain complexes in
nonpositive degrees along `n ↦ -n`. -/
def twistedCubicalChainFiltration (q : ℤ) :
    Subobject (L.normalizedTwistedCubicalChainComplex.extend ComplexShape.embeddingDownNat) :=
  Subobject.mk (twistedCubicalChainFiltrationι L X q)

/-- The `q`-th stage of the cubical filtration is the subobject given by the inclusion of the
cubical chains of `X q`. -/
lemma twistedCubicalChainFiltration_def (q : ℤ) :
    twistedCubicalChainFiltration L X q = Subobject.mk (twistedCubicalChainFiltrationι L X q) :=
  (rfl)

variable {X}

/-- For `X a ⊆ X b`, the inclusion of the cubical chains of `X a` into those of `Y` factors
through the cubical chains of `X b`. -/
@[reassoc (attr := simp)]
lemma extendMap_subsetNormalizedTwistedCubicalChainComplexMap_comp_twistedCubicalChainFiltrationι
    {a b : ℤ} (hab : X a ⊆ X b) :
    extendMap (subsetNormalizedTwistedCubicalChainComplexMap L hab) ComplexShape.embeddingDownNat ≫
        twistedCubicalChainFiltrationι L X b =
      twistedCubicalChainFiltrationι L X a :=
  (extendMap_comp _ _ _).symm.trans <| congrArg (extendMap · _)
    (subsetNormalizedTwistedCubicalChainComplexMap_normalizedTwistedCubicalChainComplexMap L hab)

/-- The cubical filtration is monotone in the subsets. -/
lemma twistedCubicalChainFiltration_mono {a b : ℤ} (hab : X a ⊆ X b) :
    twistedCubicalChainFiltration L X a ≤ twistedCubicalChainFiltration L X b :=
  Subobject.mk_le_mk_of_comm _
    (extendMap_subsetNormalizedTwistedCubicalChainComplexMap_comp_twistedCubicalChainFiltrationι
      L hab)

/-- An increasing family of subsets gives an increasing filtration of cubical chains with local
coefficients. -/
lemma monotone_twistedCubicalChainFiltration (hX : Monotone X) :
    Monotone (twistedCubicalChainFiltration L X) :=
  fun _ _ h ↦ twistedCubicalChainFiltration_mono L (hX h)

/-- The stage of the cubical filtration at an empty subset is zero. -/
@[simp]
lemma twistedCubicalChainFiltration_eq_bot {a : ℤ} (ha : X a = ∅) :
    twistedCubicalChainFiltration L X a = ⊥ := by
  have : IsEmpty (X a) := by rw [ha]; exact Set.isEmpty_coe_sort.2 rfl
  -- An empty space has no singular cubes, so its normalized cubical chains vanish in every degree.
  have hZ : IsZero ((pullback (X := TopCat.of ↥(X a)) (ContinuousMap.subtypeVal (X a))).obj
      L).normalizedTwistedCubicalChainComplex :=
    (IsZero.iff_id_eq_zero _).2 <| HomologicalComplex.hom_ext _ _ fun _ ↦ ModuleCat.hom_ext <|
      NormalizedTwistedCubicalChain.hom_ext fun c ↦ (IsEmpty.false (c 0)).elim
  exact Subobject.mk_eq_bot_iff_zero.2
    (((ComplexShape.embeddingDownNat.extendFunctor _).map_isZero hZ).eq_of_src _ _)

/-- The stage of the cubical filtration at the whole space is everything. -/
@[simp]
lemma twistedCubicalChainFiltration_eq_top {b : ℤ} (hb : X b = Set.univ) :
    twistedCubicalChainFiltration L X b = ⊤ := by
  let s : C(Y, X b) := ⟨fun y ↦ ⟨y, Set.eq_univ_iff_forall.1 hb y⟩, by fun_prop⟩
  -- Every singular cube of `Y` lies in `X b`, so the inclusion of the normalized cubical chains of
  -- `X b` is onto in every degree.
  have (n : ℕ) : Epi ((normalizedTwistedCubicalChainComplexMap (X := TopCat.of ↥(X b))
      (ContinuousMap.subtypeVal (X b)) L).f n) := by
    refine ⟨fun g h hgh ↦ ModuleCat.hom_ext <| NormalizedTwistedCubicalChain.hom_ext fun c ↦
      LinearMap.ext fun x ↦ ?_⟩
    obtain ⟨c, rfl⟩ : ∃ c', (ContinuousMap.subtypeVal (X b)).comp c' = c := ⟨s.comp c, rfl⟩
    have hx := NormalizedTwistedCubicalChain.map_ofCube (X := TopCat.of ↥(X b))
      (f := ContinuousMap.subtypeVal (X b)) (L := L) c x
    rw [normalizedTwistedCubicalChainComplexMap_f] at hgh
    -- Evaluate the composites with `ofCube` produced by the extensionality lemma at `x`. This needs
    -- `change`: in that goal `g.hom` is applied as a map out of `NormalizedTwistedCubicalChain n`,
    -- which is the object of the chain complex in degree `n` only up to unfolding, so the goal is
    -- not type-correct at the transparency `rw [LinearMap.comp_apply]` or `dsimp` work at.
    change g.hom (NormalizedTwistedCubicalChain.ofCube L _ x) =
      h.hom (NormalizedTwistedCubicalChain.ofCube L _ x)
    rw [← hx]
    exact congrArg (fun φ ↦ φ.hom
      (NormalizedTwistedCubicalChain.ofCube (X := TopCat.of ↥(X b)) _ c x)) hgh
  have (n : ℕ) : IsIso ((normalizedTwistedCubicalChainComplexMap (X := TopCat.of ↥(X b))
      (ContinuousMap.subtypeVal (X b)) L).f n) :=
    isIso_of_mono_of_epi _
  have := HomologicalComplex.Hom.isIso_of_components
    (normalizedTwistedCubicalChainComplexMap (X := TopCat.of ↥(X b))
      (ContinuousMap.subtypeVal (X b)) L)
  have : IsIso (twistedCubicalChainFiltrationι L X b) := by
    rw [twistedCubicalChainFiltrationι]
    infer_instance
  exact Subobject.mk_eq_top_of_isIso _

/-- The abutment of the cubical spectral sequence of a filtered space with local coefficients in
degree `-n` is the normalized cubical homology `Hₙ(Y; L)`. -/
def twistedCubicalChainFiltrationAbutmentIso (hX : Monotone X) (n : ℕ) :
    (CochainComplex.spectralObject
        (CochainComplex.filtrationFunctor _ (monotone_twistedCubicalChainFiltration L hX))).abutment
        (-n) ≅
      L.normalizedTwistedCubicalChainComplex.homology n :=
  CochainComplex.filtrationAbutmentIso _ _ _ ≪≫
    extendHomologyIso _ ComplexShape.embeddingDownNat rfl

/-- The identification of the abutment is the identification
`CochainComplex.filtrationAbutmentIso` of the abutment of a filtered complex with its cohomology,
followed by the identification of the cohomology of the reindexed complex. -/
lemma twistedCubicalChainFiltrationAbutmentIso_eq (hX : Monotone X) (n : ℕ) :
    twistedCubicalChainFiltrationAbutmentIso L hX n =
      CochainComplex.filtrationAbutmentIso _ _ _ ≪≫
        extendHomologyIso _ ComplexShape.embeddingDownNat rfl :=
  (rfl)

end Filtration

/-! ### The comparison with simplicial chains -/

section Comparison

variable (L : LocalCoefficientSystem.{u, v, v} R Y) {X : ℤ → Set Y}

/-- On the cubical chains of `X q`, the comparison map of `Y` is the comparison map of `X q` with
the restricted system, followed by the inclusion of the simplicial chains of `X q`. -/
@[reassoc]
lemma twistedCubicalChainFiltrationι_comp_extendMap (q : ℤ) :
    twistedCubicalChainFiltrationι L X q ≫
        extendMap (twistedCubicalToSingularMap L) ComplexShape.embeddingDownNat =
      extendMap (twistedCubicalToSingularMap _) ComplexShape.embeddingDownNat ≫
        twistedChainFiltrationι.{u, v, v} L X q := by
  rw [twistedCubicalChainFiltrationι_def, twistedChainFiltrationι_def, ← extendMap_comp,
    ← extendMap_comp]
  exact congrArg (extendMap · _)
    (twistedCubicalToSingularMap_naturality (TopCat.ofHom (ContinuousMap.subtypeVal (X q))) L)

/-- The comparison map carries each stage of the cubical filtration into the same stage of the
simplicial filtration. -/
lemma factors_twistedChainFiltration_twistedCubicalToSingularMap (q : ℤ) :
    (twistedChainFiltration.{u, v, v} L X q).Factors
      ((twistedCubicalChainFiltration L X q).arrow ≫
        extendMap (twistedCubicalToSingularMap L) ComplexShape.embeddingDownNat) := by
  rw [twistedChainFiltration_def.{u, v, v}, twistedCubicalChainFiltration_def]
  exact (Subobject.mk_factors_iff _ _).2
    ⟨(Subobject.underlyingIso (twistedCubicalChainFiltrationι L X q)).hom ≫
      extendMap (twistedCubicalToSingularMap _) ComplexShape.embeddingDownNat,
    (Category.assoc _ _ _).trans <|
      (congrArg (_ ≫ ·) (twistedCubicalChainFiltrationι_comp_extendMap L q).symm).trans <|
        (Category.assoc _ _ _).symm.trans
          (congrArg (· ≫ _) (Subobject.underlyingIso_hom_comp_eq_mk _))⟩

/-- **The comparison of cubical and simplicial chains with local coefficients as a morphism of
filtered complexes.** The comparison map `twistedCubicalToSingularMap L` carries the cubical chains
of each `X q` into the simplicial chains of `X q`, so it is a morphism from the filtration of the
cubical chains of `Y` by those of the `X q` to the filtration of the simplicial chains. -/
def twistedCubicalToSingularFiltrationMap (hX : Monotone X) :
    CochainComplex.filtrationFunctor _ (monotone_twistedCubicalChainFiltration L hX) ⟶
      CochainComplex.filtrationFunctor _ (monotone_twistedChainFiltration.{u, v, v} L hX) :=
  CochainComplex.filtrationFunctorMap _ _ _
    (factors_twistedChainFiltration_twistedCubicalToSingularMap L)

/-- `TauCeti.LocalCoefficientSystem.twistedCubicalToSingularFiltrationMap` is the morphism of
filtration functors given by the comparison map of `Y`. -/
lemma twistedCubicalToSingularFiltrationMap_def (hX : Monotone X) :
    twistedCubicalToSingularFiltrationMap L hX =
      CochainComplex.filtrationFunctorMap _ _ _
        (factors_twistedChainFiltration_twistedCubicalToSingularMap L) :=
  (rfl)

/-- On the stage `F_q`, identified with the cubical chains of `X q`, the morphism of filtrations is
the comparison map of `X q` with the restricted system. -/
@[reassoc]
lemma twistedCubicalToSingularFiltrationMap_app_comp_filtrationFunctorObjIsoOfEqMk_hom
    (hX : Monotone X) (q : ℤ) :
    (twistedCubicalToSingularFiltrationMap L hX).app q ≫
        (CochainComplex.filtrationFunctorObjIsoOfEqMk _
          (monotone_twistedChainFiltration.{u, v, v} L hX) (twistedChainFiltrationι.{u, v, v} L X q)
          (twistedChainFiltration_def.{u, v, v} L X q)).hom =
      (CochainComplex.filtrationFunctorObjIsoOfEqMk _ (monotone_twistedCubicalChainFiltration L hX)
          (twistedCubicalChainFiltrationι L X q) (twistedCubicalChainFiltration_def L X q)).hom ≫
        extendMap (twistedCubicalToSingularMap _) ComplexShape.embeddingDownNat := by
  rw [← cancel_mono (twistedChainFiltrationι.{u, v, v} L X q), Category.assoc, Category.assoc,
    CochainComplex.filtrationFunctorObjIsoOfEqMk_hom_comp,
    ← twistedCubicalChainFiltrationι_comp_extendMap,
    CochainComplex.filtrationFunctorObjIsoOfEqMk_hom_comp_assoc]
  exact (CochainComplex.filtrationFunctorMap_app_comp _ _ q).trans (Category.assoc _ _ _).symm

/-- On every stage, including those at `⊥` and `⊤`, the morphism of filtrations given by the
comparison map is a quasi-isomorphism. -/
instance quasiIso_twistedCubicalToSingularFiltrationMap_app (hX : Monotone X) (a : EInt) :
    QuasiIso ((twistedCubicalToSingularFiltrationMap L hX).app a) := by
  rw [twistedCubicalToSingularFiltrationMap_def]
  refine CochainComplex.quasiIso_filtrationFunctorMap_app _ _ (fun q ↦ ?_) a
  -- On the stage at `q`, identified with the cubical chains of `X q`, the morphism is the
  -- comparison map of `X q`.
  have h := twistedCubicalToSingularFiltrationMap_app_comp_filtrationFunctorObjIsoOfEqMk_hom L hX q
  rw [← Iso.eq_comp_inv] at h
  rw [← twistedCubicalToSingularFiltrationMap_def L hX, h]
  infer_instance

/-- **Cubical and simplicial chains with local coefficients give the same spectral sequence of a
filtered space.** The spectral objects of the filtrations of the cubical and of the simplicial
chains of `Y` with coefficients in `L` by those of the `X q` are isomorphic through the comparison
map. -/
def twistedCubicalSingularSpectralObjectIso (hX : Monotone X) :
    CochainComplex.spectralObject
        (CochainComplex.filtrationFunctor _ (monotone_twistedCubicalChainFiltration L hX)) ≅
      CochainComplex.spectralObject
        (CochainComplex.filtrationFunctor _ (monotone_twistedChainFiltration.{u, v, v} L hX)) :=
  asIso (CochainComplex.spectralObjectMap (twistedCubicalToSingularFiltrationMap L hX))

/-- The isomorphism `TauCeti.LocalCoefficientSystem.twistedCubicalSingularSpectralObjectIso` is
the morphism of spectral objects induced by the comparison map. -/
@[simp]
lemma twistedCubicalSingularSpectralObjectIso_hom (hX : Monotone X) :
    (twistedCubicalSingularSpectralObjectIso L hX).hom =
      CochainComplex.spectralObjectMap (twistedCubicalToSingularFiltrationMap L hX) :=
  (rfl)

/-- **The cubical and simplicial spectral sequences of a filtered space with local coefficients
are isomorphic** on every page, from the first page on, through the comparison map. -/
def twistedCubicalSingularSpectralSequenceIso (hX : Monotone X) :
    CochainComplex.spectralSequence
        (CochainComplex.filtrationFunctor _ (monotone_twistedCubicalChainFiltration L hX)) ≅
      CochainComplex.spectralSequence
        (CochainComplex.filtrationFunctor _ (monotone_twistedChainFiltration.{u, v, v} L hX)) :=
  asIso (Abelian.SpectralObject.spectralSequenceMap Abelian.SpectralObject.coreE₂Cohomological
    (twistedCubicalSingularSpectralObjectIso L hX).hom)

/-- The isomorphism `TauCeti.LocalCoefficientSystem.twistedCubicalSingularSpectralSequenceIso` is
the morphism of spectral sequences induced by the comparison map. -/
@[simp]
lemma twistedCubicalSingularSpectralSequenceIso_hom (hX : Monotone X) :
    (twistedCubicalSingularSpectralSequenceIso L hX).hom =
      Abelian.SpectralObject.spectralSequenceMap Abelian.SpectralObject.coreE₂Cohomological
        (CochainComplex.spectralObjectMap (twistedCubicalToSingularFiltrationMap L hX)) :=
  (rfl)

/-- **The comparison of the cubical and simplicial abutments with local coefficients.** Under the
identifications of the abutments in degree `-n` with the cubical and the simplicial twisted
homology `Hₙ(Y; L)`, the isomorphism of spectral objects is the map in homology of the comparison
map of `Y`. -/
@[reassoc]
lemma twistedCubicalSingularSpectralObjectIso_hom_abutment_comp (hX : Monotone X) (n : ℕ) :
    ((twistedCubicalSingularSpectralObjectIso L hX).hom.hom (-n)).app
        (ComposableArrows.mk₁ (homOfLE (bot_le : (⊥ : EInt) ≤ ⊤))) ≫
        (twistedChainFiltrationAbutmentIso.{u, v, v} L hX n).hom =
      (twistedCubicalChainFiltrationAbutmentIso L hX n).hom ≫
        homologyMap (twistedCubicalToSingularMap L) n := by
  rw [twistedCubicalSingularSpectralObjectIso_hom, twistedChainFiltrationAbutmentIso_eq,
    twistedCubicalChainFiltrationAbutmentIso_eq, twistedCubicalToSingularFiltrationMap_def]
  -- The homology objects of the extended complexes carry `HasHomology` instances that `rw` does
  -- not identify, so the square is assembled as a term.
  exact (Category.assoc _ _ _).symm.trans <| (congrArg (· ≫ _)
    (CochainComplex.spectralObjectMap_filtrationFunctorMap_hom_app_comp_filtrationAbutmentIso_hom
      _ _ _)).trans <| (Category.assoc _ _ _).trans <| (congrArg
      ((CochainComplex.filtrationAbutmentIso _ (monotone_twistedCubicalChainFiltration L hX)
        _).hom ≫ ·) (extendHomologyIso_hom_naturality _ _ _)).trans (Category.assoc _ _ _).symm

end Comparison

end LocalCoefficientSystem

end TauCeti
