/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Cohomology.Relative
public import TauCeti.Geometry.Manifold.SmoothSingular.Smoothing

import TauCeti.Algebra.Homology.DerivedCategory.KProjective
import TauCeti.Algebra.Homology.Homotopy

/-!
# The smoothing theorem for open pairs

Let `U` be an open subset of a smooth manifold `M`. A smooth singular simplex of `M` with image in
`U` is a smooth singular simplex of `U`
(`TauCeti.smoothSingularSubcomplex_preimage_subtypeVal`), so the inclusion of `U` induces a
monomorphism from the smooth singular simplicial set of `U` to that of `M`. This is the *smooth
singular pair* `TauCeti.smoothSingularPair I U` of `(M, U)`. Its relative chains are the smooth
singular chains of `M` modulo those of `U`, and its relative homology is the smooth relative
homology of `(M, U)`: a smooth relative cycle is a smooth chain of `M` whose boundary is a smooth
chain of `U`.

The inclusions of smooth singular simplices into singular simplices of `U` and of `M` form a map
of pairs `TauCeti.smoothSingularPairι I U` from the smooth singular pair to the singular pair of
the topological pair `(M, U)`. When `M` is a Hausdorff `σ`-compact manifold modelled on a
finite-dimensional real model with corners, the smoothing theorem
(`TauCeti.quasiIso_chainComplexMap_smoothSingularSubcomplex_ι_opens`) applies to `U` and to `M`,
and the five lemma for pairs (`SSetPair.quasiIso_chainComplexMap`) turns it into the **relative
smoothing theorem**: the map of relative chain complexes is a quasi-isomorphism
(`TauCeti.quasiIso_chainComplexMap_smoothSingularPairι`). Hence smooth relative homology is
relative singular homology (`TauCeti.smoothSingularRelativeHomologyIso`). The identification is
natural in smooth maps of pairs, compatible with the maps from absolute to relative homology and
with the connecting maps of the two long exact sequences. In particular, a smooth relative cycle
whose relative singular class vanishes is, up to a smooth chain of `U`, the boundary of a smooth
chain of `M`.

When the coefficient object is projective, all relative chain groups are projective, so the
quasi-isomorphism is a chain homotopy equivalence
(`TauCeti.smoothSingularPairChainHomotopyEquiv`) whose homotopy inverse is natural up to chain
homotopy, and applying `Hom(-, Y)` gives the dual cochain homotopy equivalence
(`TauCeti.smoothSingularPairCochainHomotopyEquiv`), the dual statement for relative cochains
(`TauCeti.quasiIso_cochainComplexMap_smoothSingularPairι`) and an isomorphism from relative
singular cohomology to smooth relative cohomology (`TauCeti.smoothSingularRelativeCohomologyIso`).
It is again natural in smooth maps of pairs and
compatible with the maps from relative to absolute cohomology and with the connecting maps.

This is the comparison through which integrals of differential forms over smooth relative cycles,
such as a positively oriented simplex around the support of a top form, can be compared with
relative singular homology classes, such as fundamental classes along compact subsets.

## Main definitions

* `TauCeti.smoothSingularPair I U`: the pair of smooth singular simplicial sets of `(M, U)`.
* `TauCeti.smoothSingularPairι I U`: its inclusion into the singular pair of `(M, U)`.
* `TauCeti.smoothSingularPairMap hf hUV`: the map of smooth singular pairs induced by a smooth map
  of pairs.
* `TauCeti.smoothSingularRelativeHomologyIso I R U n`: smooth relative homology is relative
  singular homology.
* `TauCeti.smoothSingularPairChainHomotopyEquiv I R U`: the relative smoothing chain homotopy
  equivalence for projective coefficients.
* `TauCeti.smoothSingularPairCochainHomotopyEquiv I R k Y U`: the dual relative smoothing cochain
  homotopy equivalence.
* `TauCeti.smoothSingularRelativeCohomologyIso I R k Y U n`: relative singular cohomology is smooth
  relative cohomology.

## Main results

* `TauCeti.quasiIso_chainComplexMap_smoothSingularPairι`: the relative smoothing theorem.
* `TauCeti.smoothSingularRelativeHomologyIso_hom_naturality`: naturality in smooth maps of pairs.
* `TauCeti.homologyπ_comp_smoothSingularRelativeHomologyIso_hom`: compatibility with the maps from
  absolute to relative homology.
* `TauCeti.smoothSingularRelativeHomologyIso_hom_comp_singularHomologyδ`: compatibility with the
  connecting maps.
* `TauCeti.smoothSingularPairChainHomotopyEquivInvNaturality`,
  `TauCeti.smoothSingularPairCochainHomotopyEquivInvNaturality`: the relative smoothing homotopy
  inverses are natural up to chain homotopy.
* `TauCeti.quasiIso_cochainComplexMap_smoothSingularPairι`: the relative smoothing theorem for
  cochains.
* `TauCeti.smoothSingularRelativeCohomologyIso_hom_naturality`,
  `TauCeti.smoothSingularRelativeCohomologyIso_inv_naturality`,
  `TauCeti.singularCohomologyπ_comp_smoothSingularCohomologyIso_hom` and
  `TauCeti.singularCohomologyδ_comp_smoothSingularRelativeCohomologyIso_hom`: naturality of the
  cohomology isomorphism and its compatibility with the long exact sequences.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Chapter 18, Theorem 18.7 (the absolute
  smoothing theorem, from which the relative one follows by the five lemma).
-/

public section

noncomputable section

open CategoryTheory Limits TopologicalSpace
open scoped Manifold ContDiff

universe u v w

namespace TauCeti

/-! ### The smooth singular pair of an open subset -/

section Pair

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  (I : ModelWithCorners ℝ E H) {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
  {E' H' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H']
  {J : ModelWithCorners ℝ E' H'} {N : Type u} [TopologicalSpace N] [ChartedSpace H' N]

/-- The smooth singular pair `(M, U)` of an open subset `U` of `M`: the inclusion of the smooth
singular simplicial set of `U` into that of `M` induced by the inclusion of `U`. Its relative
chains are the smooth singular chains of `M` modulo those of `U`. -/
@[expose] def smoothSingularPair (U : Opens M) : SSetPair.{u} :=
  SSetPair.of (smoothSingularSubcomplexMap (Subtype.val : U → M) (contMDiff_subtypeVal (I := I)))

@[simp]
theorem smoothSingularPair_left (U : Opens M) :
    (smoothSingularPair I U).left = (smoothSingularSubcomplex I U : SSet) :=
  rfl

@[simp]
theorem smoothSingularPair_right (U : Opens M) :
    (smoothSingularPair I U).right = (smoothSingularSubcomplex I M : SSet) :=
  rfl

@[simp]
theorem smoothSingularPair_hom (U : Opens M) :
    (smoothSingularPair I U).hom =
      smoothSingularSubcomplexMap (Subtype.val : U → M) (contMDiff_subtypeVal (I := I)) :=
  rfl

/-- The inclusion of the smooth singular pair of `(M, U)` into the singular pair of the
topological pair `(M, U)`: on both members it is the inclusion of smooth singular simplices into
singular simplices. -/
def smoothSingularPairι (U : Opens M) :
    smoothSingularPair I U ⟶ TopPair.toSSetPair.obj (TopPair.ofSubset (U : Set (TopCat.of M))) :=
  SSetPair.homMk (smoothSingularSubcomplex I U).ι (smoothSingularSubcomplex I M).ι
    (by
      rw [TopPair.toSSetPair_obj_hom, TopPair.ofSubset_map]
      exact (smoothSingularSubcomplexMap_subtypeVal_ι U).symm)

@[simp]
theorem smoothSingularPairι_left (U : Opens M) :
    (smoothSingularPairι I U).left = (smoothSingularSubcomplex I U).ι :=
  (rfl)

@[simp]
theorem smoothSingularPairι_right (U : Opens M) :
    (smoothSingularPairι I U).right = (smoothSingularSubcomplex I M).ι :=
  (rfl)

variable {I}

/-- The map of smooth singular pairs `(M, U) ⟶ (N, V)` induced by a smooth map `f : M → N`
carrying `U` into `V`. On the smooth singular simplices of `U` it is induced by the restriction
`U → V` of `f`, which is smooth because the charts of `U` and `V` are restrictions of those of
`M` and `N`. -/
def smoothSingularPairMap {f : M → N} (hf : ContMDiff I J ∞ f) {U : Opens M} {V : Opens N}
    (hUV : Set.MapsTo f U V) : smoothSingularPair I U ⟶ smoothSingularPair J V :=
  SSetPair.homMk
    (smoothSingularSubcomplexMap (hUV.restrict f U V)
      ((ContMDiff.subtypeVal_comp_iff V _).1 (hf.comp contMDiff_subtypeVal)))
    (smoothSingularSubcomplexMap f hf)
    -- Both composites are induced by `x ↦ f x` on `U`.
    ((smoothSingularSubcomplexMap_comp contMDiff_subtypeVal _).symm.trans
      (smoothSingularSubcomplexMap_comp hf contMDiff_subtypeVal))

/-- On the smooth singular simplices of `U`, the map of smooth singular pairs induced by `f` is the
restriction of the map of singular simplicial sets induced by the restriction `U → V` of `f`. -/
@[reassoc]
theorem smoothSingularPairMap_left_comp_ι {f : M → N} (hf : ContMDiff I J ∞ f) {U : Opens M}
    {V : Opens N} (hUV : Set.MapsTo f U V) :
    (smoothSingularPairMap hf hUV).left ≫ (smoothSingularSubcomplex J V).ι =
      (smoothSingularSubcomplex I U).ι ≫
        TopCat.toSSet.map (TopCat.ofHom ⟨hUV.restrict f U V, hf.continuous.restrict hUV⟩) :=
  smoothSingularSubcomplexMap_ι _

@[simp]
theorem smoothSingularPairMap_left {f : M → N} (hf : ContMDiff I J ∞ f) {U : Opens M}
    {V : Opens N} (hUV : Set.MapsTo f U V) :
    (smoothSingularPairMap hf hUV).left =
      smoothSingularSubcomplexMap (M := U) (N := V) (hUV.restrict f U V)
        ((ContMDiff.subtypeVal_comp_iff V _).1 (hf.comp contMDiff_subtypeVal)) :=
  (rfl)

@[simp]
theorem smoothSingularPairMap_right {f : M → N} (hf : ContMDiff I J ∞ f) {U : Opens M}
    {V : Opens N} (hUV : Set.MapsTo f U V) :
    (smoothSingularPairMap hf hUV).right = smoothSingularSubcomplexMap f hf :=
  (rfl)

/-- The identity of `M` induces the identity of the smooth singular pair `(M, U)`. -/
@[simp]
theorem smoothSingularPairMap_id (U : Opens M) :
    smoothSingularPairMap (I := I) (J := I) contMDiff_id (Set.mapsTo_id (U : Set M)) = 𝟙 _ :=
  MorphismProperty.Arrow.Hom.ext smoothSingularSubcomplexMap_id smoothSingularSubcomplexMap_id

/-- The map of smooth singular pairs induced by a composite of smooth maps of pairs is the
composite of the induced maps. -/
theorem smoothSingularPairMap_comp {E'' H'' : Type*} [NormedAddCommGroup E'']
    [NormedSpace ℝ E''] [TopologicalSpace H''] {K : ModelWithCorners ℝ E'' H''} {P : Type u}
    [TopologicalSpace P] [ChartedSpace H'' P] {f : M → N} {g : N → P} (hf : ContMDiff I J ∞ f)
    (hg : ContMDiff J K ∞ g) {U : Opens M} {V : Opens N} {W : Opens P}
    (hUV : Set.MapsTo f U V) (hVW : Set.MapsTo g V W) :
    smoothSingularPairMap (hg.comp hf) (hVW.comp hUV) =
      smoothSingularPairMap hf hUV ≫ smoothSingularPairMap hg hVW :=
  MorphismProperty.Arrow.Hom.ext
    (smoothSingularSubcomplexMap_comp (M := U) (N := V) (P := W) (φ := hUV.restrict f U V)
      (ψ := hVW.restrict g V W) _ _)
    (smoothSingularSubcomplexMap_comp hg hf)

/-- The inclusion of smooth singular pairs into singular pairs is natural in smooth maps of
pairs. -/
@[reassoc]
theorem smoothSingularPairMap_comp_smoothSingularPairι {f : M → N} (hf : ContMDiff I J ∞ f)
    {U : Opens M} {V : Opens N} (hUV : Set.MapsTo f U V) :
    smoothSingularPairMap hf hUV ≫ smoothSingularPairι J V =
      smoothSingularPairι I U ≫
        TopPair.toSSetPair.map (TopPair.ofSubsetMap (TopCat.ofHom ⟨f, hf.continuous⟩) hUV) :=
  MorphismProperty.Arrow.Hom.ext
    ((smoothSingularPairMap_left_comp_ι hf hUV).trans
      (congrArg ((smoothSingularSubcomplex I U).ι ≫ TopCat.toSSet.map ·)
        (by
          ext x
          exact (TopPair.ofSubsetMap_snd_apply (TopCat.ofHom ⟨f, hf.continuous⟩) hUV x).symm)))
    ((smoothSingularSubcomplexMap_ι hf).trans
      (congrArg ((smoothSingularSubcomplex I M).ι ≫ TopCat.toSSet.map ·)
        (TopPair.ofSubsetMap_fst _ hUV).symm))

end Pair

/-! ### The relative smoothing theorem -/

section QuasiIso

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
  {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
  [T2Space M] [SigmaCompactSpace M] [IsManifold I ∞ M]
  {C : Type v} [Category.{w} C] [Abelian C] [HasCoproducts.{u} C]
  [HasExactColimitsOfShape (Discrete ℕ) C] (R : C)

/-- **The relative smoothing theorem.** For an open subset `U` of a Hausdorff `σ`-compact smooth
manifold `M` modelled on a finite-dimensional real model with corners, the inclusion of the smooth
relative singular chains of `(M, U)` into its relative singular chains, with coefficients in `R`,
is a quasi-isomorphism whenever countable coproducts are exact in `C`. -/
instance quasiIso_chainComplexMap_smoothSingularPairι (U : Opens M) :
    QuasiIso (SSetPair.chainComplexMap (smoothSingularPairι I U) R) := by
  have : QuasiIso (SSet.chainComplexMap (smoothSingularPairι I U).left R) :=
    quasiIso_chainComplexMap_smoothSingularSubcomplex_ι_opens R U
  have : QuasiIso (SSet.chainComplexMap (smoothSingularPairι I U).right R) :=
    quasiIso_chainComplexMap_smoothSingularSubcomplex_ι R
  exact SSetPair.quasiIso_chainComplexMap _ R

/-- **Smooth relative homology is relative singular homology.** The inclusion of smooth singular
simplices induces an isomorphism from the smooth relative homology of `(M, U)` to its relative
singular homology, in every degree. -/
def smoothSingularRelativeHomologyIso (U : Opens M) (n : ℕ) :
    (smoothSingularPair I U).homology R n ≅
      (TopPair.ofSubset (U : Set (TopCat.of M))).singularHomology R n :=
  asIso (SSetPair.homologyMap (smoothSingularPairι I U) R n)

@[simp]
theorem smoothSingularRelativeHomologyIso_hom (U : Opens M) (n : ℕ) :
    (smoothSingularRelativeHomologyIso I R U n).hom =
      SSetPair.homologyMap (smoothSingularPairι I U) R n :=
  (rfl)

/-- The map from absolute to relative homology commutes with the smoothing isomorphisms: a smooth
cycle of `M` has the same relative class, read in smooth or in singular relative homology. -/
@[reassoc]
theorem homologyπ_comp_smoothSingularRelativeHomologyIso_hom (U : Opens M) (n : ℕ) :
    (smoothSingularPair I U).homologyπ R n ≫ (smoothSingularRelativeHomologyIso I R U n).hom =
      (smoothSingularHomologyIso I M R n).hom ≫
        (TopPair.ofSubset (U : Set (TopCat.of M))).singularHomologyπ R n := by
  rw [smoothSingularRelativeHomologyIso_hom, smoothSingularHomologyIso_hom,
    ← SSetPair.homologyπ_naturality, smoothSingularPairι_right]
  -- `TopPair.singularHomologyπ` abbreviates `SSetPair.homologyπ` of the singular pair, whose
  -- ambient member is `TopCat.toSSet.obj (TopCat.of M)` by definition (`toSSetPair_obj_right`), so
  -- the two sides differ only in how that codomain of `SSet.homologyMap` is written.
  rfl

/-- The smoothing isomorphisms commute with the connecting maps of the long exact sequences of the
smooth and the singular pair: the boundary of a smooth relative cycle of `(M, U)` is a smooth cycle
of `U`, whose singular class is the singular connecting map of its relative class. -/
@[reassoc]
theorem smoothSingularRelativeHomologyIso_hom_comp_singularHomologyδ (U : Opens M) (n m : ℕ)
    (h : m + 1 = n := by lia) :
    (smoothSingularRelativeHomologyIso I R U n).hom ≫
        (TopPair.ofSubset (U : Set (TopCat.of M))).singularHomologyδ R n m h =
      (smoothSingularPair I U).homologyδ R n m h ≫
        SSet.homologyMap (smoothSingularSubcomplex I U).ι R m := by
  rw [smoothSingularRelativeHomologyIso_hom, ← SSetPair.homologyδ_naturality _ R n m h,
    smoothSingularPairι_left]
  -- `TopPair.singularHomologyδ` abbreviates `SSetPair.homologyδ` of the singular pair, whose
  -- subspace member is `TopCat.toSSet.obj U` by definition (`toSSetPair_obj_left`), so the two
  -- sides differ only in how that codomain of `SSet.homologyMap` is written.
  rfl

variable {I} {E' H' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
  [TopologicalSpace H'] {J : ModelWithCorners ℝ E' H'}
  {N : Type u} [TopologicalSpace N] [ChartedSpace H' N]
  [T2Space N] [SigmaCompactSpace N] [IsManifold J ∞ N]

/-- `smoothSingularRelativeHomologyIso` is natural in smooth maps of pairs. -/
@[reassoc]
theorem smoothSingularRelativeHomologyIso_hom_naturality {f : M → N} (hf : ContMDiff I J ∞ f)
    {U : Opens M} {V : Opens N} (hUV : Set.MapsTo f U V) (n : ℕ) :
    (smoothSingularRelativeHomologyIso I R U n).hom ≫
        TopPair.singularHomologyMap
          (TopPair.ofSubsetMap (TopCat.ofHom ⟨f, hf.continuous⟩) hUV) R n =
      SSetPair.homologyMap (smoothSingularPairMap hf hUV) R n ≫
        (smoothSingularRelativeHomologyIso J R V n).hom := by
  rw [smoothSingularRelativeHomologyIso_hom, smoothSingularRelativeHomologyIso_hom,
    TopPair.singularHomologyMap, ← SSetPair.homologyMap_comp, ← SSetPair.homologyMap_comp,
    smoothSingularPairMap_comp_smoothSingularPairι]

/-- The inverse of `smoothSingularRelativeHomologyIso` is natural in smooth maps of pairs. -/
@[reassoc]
theorem smoothSingularRelativeHomologyIso_inv_naturality {f : M → N} (hf : ContMDiff I J ∞ f)
    {U : Opens M} {V : Opens N} (hUV : Set.MapsTo f U V) (n : ℕ) :
    (smoothSingularRelativeHomologyIso I R U n).inv ≫
        SSetPair.homologyMap (smoothSingularPairMap hf hUV) R n =
      TopPair.singularHomologyMap
          (TopPair.ofSubsetMap (TopCat.ofHom ⟨f, hf.continuous⟩) hUV) R n ≫
        (smoothSingularRelativeHomologyIso J R V n).inv := by
  rw [Iso.inv_comp_eq, ← Category.assoc, Iso.eq_comp_inv,
    smoothSingularRelativeHomologyIso_hom_naturality R hf hUV]

end QuasiIso

/-! ### Chain homotopy equivalence and relative cohomology -/

section Projective

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
  {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
  [T2Space M] [SigmaCompactSpace M] [IsManifold I ∞ M]
  {C : Type v} [Category.{w} C] [Abelian C] [HasCoproducts.{u} C]
  [HasExactColimitsOfShape (Discrete ℕ) C] (R : C) [Projective R]

/-- **The relative smoothing theorem (chain homotopy equivalence form).** When `R` is projective,
the relative chain groups of both pairs are projective, so the inclusion of smooth relative
singular chains of `(M, U)` into relative singular chains is a chain homotopy equivalence. -/
def smoothSingularPairChainHomotopyEquiv (U : Opens M) :
    HomotopyEquiv ((smoothSingularPair I U).chainComplex R)
      ((TopPair.ofSubset (U : Set (TopCat.of M))).singularChainComplex R) :=
  .ofQuasiIsoOfProjective (SSetPair.chainComplexMap (smoothSingularPairι I U) R)

@[simp]
theorem smoothSingularPairChainHomotopyEquiv_hom (U : Opens M) :
    (smoothSingularPairChainHomotopyEquiv I R U).hom =
      SSetPair.chainComplexMap (smoothSingularPairι I U) R := by
  rw [smoothSingularPairChainHomotopyEquiv, HomotopyEquiv.ofQuasiIsoOfProjective_hom]

/-- The map induced on homology by the inverse of `smoothSingularPairChainHomotopyEquiv` is the
inverse of `smoothSingularRelativeHomologyIso`. -/
@[simp]
theorem homologyMap_smoothSingularPairChainHomotopyEquiv_inv (U : Opens M) (n : ℕ) :
    HomologicalComplex.homologyMap (smoothSingularPairChainHomotopyEquiv I R U).inv n =
      (smoothSingularRelativeHomologyIso I R U n).inv := by
  rw [smoothSingularPairChainHomotopyEquiv, HomotopyEquiv.homologyMap_ofQuasiIsoOfProjective_inv,
    smoothSingularRelativeHomologyIso]

variable (k : Type*) [Ring k] [Linear k C] (Y : C)

/-- **The relative smoothing theorem for cochains.** When `R` is projective, restricting relative
singular cochains of `(M, U)` with values in `Y` to smooth relative chains is a quasi-isomorphism.
-/
instance quasiIso_cochainComplexMap_smoothSingularPairι (U : Opens M) :
    QuasiIso (SSetPair.cochainComplexMap (R := R) (k := k) (M := Y) (smoothSingularPairι I U)) :=
  ChainComplex.quasiIso_linearYonedaFunctor_map_of_projective _ k Y

/-- **The dual relative smoothing cochain homotopy equivalence.** Applying `Hom(-, Y)` to
`smoothSingularPairChainHomotopyEquiv` yields a cochain homotopy equivalence from the relative
singular cochain complex of `(M, U)` to its smooth relative cochain complex. -/
def smoothSingularPairCochainHomotopyEquiv (U : Opens M) :
    HomotopyEquiv ((TopPair.ofSubset (U : Set (TopCat.of M))).singularCochainComplex R k Y)
      (((smoothSingularPair I U).chainComplex R).linearYonedaObj k Y) :=
  (smoothSingularPairChainHomotopyEquiv I R U).linearYonedaFunctorMap k Y

/-- The forward map of `smoothSingularPairCochainHomotopyEquiv` is restriction of relative
singular cochains to smooth relative chains. -/
@[simp]
theorem smoothSingularPairCochainHomotopyEquiv_hom (U : Opens M) :
    (smoothSingularPairCochainHomotopyEquiv I R k Y U).hom =
      SSetPair.cochainComplexMap (smoothSingularPairι I U) := by
  rw [smoothSingularPairCochainHomotopyEquiv, HomotopyEquiv.linearYonedaFunctorMap_hom,
    smoothSingularPairChainHomotopyEquiv_hom]

/-- The inverse map of `smoothSingularPairCochainHomotopyEquiv` is precomposition with the inverse
of `smoothSingularPairChainHomotopyEquiv`. -/
theorem smoothSingularPairCochainHomotopyEquiv_inv (U : Opens M) :
    (smoothSingularPairCochainHomotopyEquiv I R k Y U).inv =
      (ChainComplex.linearYonedaFunctor k Y).map
        (smoothSingularPairChainHomotopyEquiv I R U).inv.op := by
  rw [smoothSingularPairCochainHomotopyEquiv, HomotopyEquiv.linearYonedaFunctorMap_inv]

/-- **Relative singular cohomology is smooth relative cohomology.** When `R` is projective,
restriction to smooth simplices induces an isomorphism from the relative singular cohomology of
`(M, U)` with values in `Y` to its smooth relative cohomology, in every degree. -/
def smoothSingularRelativeCohomologyIso (U : Opens M) (n : ℕ) :
    (TopPair.ofSubset (U : Set (TopCat.of M))).singularCohomology R k Y n ≅
      (((smoothSingularPair I U).chainComplex R).linearYonedaObj k Y).homology n :=
  asIso (HomologicalComplex.homologyMap
    (SSetPair.cochainComplexMap (R := R) (k := k) (M := Y) (smoothSingularPairι I U)) n)

@[simp]
theorem smoothSingularRelativeCohomologyIso_hom (U : Opens M) (n : ℕ) :
    (smoothSingularRelativeCohomologyIso I R k Y U n).hom =
      HomologicalComplex.homologyMap
        (SSetPair.cochainComplexMap (R := R) (k := k) (M := Y) (smoothSingularPairι I U)) n :=
  (rfl)

/-- Restricting the image of a smooth relative cohomology class under the inverse of
`smoothSingularRelativeCohomologyIso` back to smooth relative chains recovers the class. -/
@[simp]
theorem homologyMap_cochainComplexMap_smoothSingularRelativeCohomologyIso_inv_apply (U : Opens M)
    (n : ℕ) (x : (((smoothSingularPair I U).chainComplex R).linearYonedaObj k Y).homology n) :
    HomologicalComplex.homologyMap
        (SSetPair.cochainComplexMap (R := R) (k := k) (M := Y) (smoothSingularPairι I U)) n
        ((smoothSingularRelativeCohomologyIso I R k Y U n).inv x) = x := by
  rw [← smoothSingularRelativeCohomologyIso_hom, Iso.inv_hom_id_apply]

/-- The map induced on cohomology by the inverse of `smoothSingularPairCochainHomotopyEquiv` is the
inverse of `smoothSingularRelativeCohomologyIso`. -/
@[simp]
theorem homologyMap_smoothSingularPairCochainHomotopyEquiv_inv (U : Opens M) (n : ℕ) :
    HomologicalComplex.homologyMap (smoothSingularPairCochainHomotopyEquiv I R k Y U).inv n =
      (smoothSingularRelativeCohomologyIso I R k Y U n).inv := by
  simp only [HomotopyEquiv.homologyMap_inv, smoothSingularPairCochainHomotopyEquiv_hom,
    smoothSingularRelativeCohomologyIso, asIso_inv]

/-- The map from relative to absolute cohomology commutes with the smoothing isomorphisms: a
relative singular cocycle of `(M, U)` restricts to the same smooth cochain of `M`, whether it is
first restricted to smooth relative chains or first regarded as a cochain of `M`. -/
@[reassoc]
theorem singularCohomologyπ_comp_smoothSingularCohomologyIso_hom (U : Opens M) (n : ℕ) :
    (TopPair.ofSubset (U : Set (TopCat.of M))).singularCohomologyπ R k Y n ≫
        (smoothSingularCohomologyIso I M R k Y n).hom =
      (smoothSingularRelativeCohomologyIso I R k Y U n).hom ≫
        HomologicalComplex.homologyMap (SSetPair.cochainComplexπ R k Y (smoothSingularPair I U))
          n := by
  have h := congrArg (HomologicalComplex.homologyMap · n)
    (SSetPair.cochainComplexπ_naturality R k Y (smoothSingularPairι I U))
  rw [HomologicalComplex.homologyMap_comp, HomologicalComplex.homologyMap_comp,
    smoothSingularPairι_right] at h
  rw [smoothSingularCohomologyIso_hom, smoothSingularRelativeCohomologyIso_hom]
  -- `singularCohomologyπ` is by definition the cohomology map of `SSetPair.cochainComplexπ` of the
  -- singular pair, whose ambient member is the singular simplicial set of `M`
  -- (`TopPair.toSSetPair_obj_right`).
  exact h

/-- The smoothing isomorphisms commute with the connecting maps of the long exact cohomology
sequences of the singular and the smooth pair: the relative singular class of the coboundary of a
singular cochain of `U` restricts to the smooth connecting map of its restriction to smooth chains
of `U`. -/
@[reassoc]
theorem singularCohomologyδ_comp_smoothSingularRelativeCohomologyIso_hom (U : Opens M) (n m : ℕ)
    (h : n + 1 = m := by lia) :
    (TopPair.ofSubset (U : Set (TopCat.of M))).singularCohomologyδ R k Y n m h ≫
        (smoothSingularRelativeCohomologyIso I R k Y U m).hom =
      HomologicalComplex.homologyMap
          (SSet.cochainComplexMap (R := R) (k := k) (M := Y) (smoothSingularSubcomplex I U).ι) n ≫
        (ChainComplex.shortExact_map_linearYonedaFunctor k Y
          ((smoothSingularPair I U).shortExact_chainComplexShortComplex R)).δ n m (by simpa) := by
  have h := HomologicalComplex.HomologySequence.δ_naturality
    (S₁ := (TopPair.ofSubset (U : Set (TopCat.of M))).singularCochainComplexShortComplex R k Y)
    (S₂ := ((smoothSingularPair I U).chainComplexShortComplex R).op.map
      (ChainComplex.linearYonedaFunctor k Y))
    ((ChainComplex.linearYonedaFunctor k Y).mapShortComplex.map
      (ShortComplex.opMap (SSetPair.chainComplexShortComplexMap (smoothSingularPairι I U) R)))
    ((TopPair.ofSubset (U : Set (TopCat.of M))).shortExact_singularCochainComplexShortComplex R k Y)
    (ChainComplex.shortExact_map_linearYonedaFunctor k Y
      ((smoothSingularPair I U).shortExact_chainComplexShortComplex R)) n m (by simpa)
  rw [Functor.mapShortComplex_map_τ₁, ShortComplex.opMap_τ₁,
    SSetPair.chainComplexShortComplexMap_τ₃, Functor.mapShortComplex_map_τ₃,
    ShortComplex.opMap_τ₃, SSetPair.chainComplexShortComplexMap_τ₁, smoothSingularPairι_left] at h
  -- Both cochain sequences are by definition `Hom(-, Y)` of the chain sequences of the pairs
  -- (`TopPair.singularCochainComplexShortComplex_eq_map`), whose members are the singular
  -- simplicial sets of `U` and `M` (`TopPair.toSSetPair_obj_left`, `TopPair.toSSetPair_obj_right`).
  exact h

variable {I} {E' H' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
  [TopologicalSpace H'] {J : ModelWithCorners ℝ E' H'}
  {N : Type u} [TopologicalSpace N] [ChartedSpace H' N]
  [T2Space N] [SigmaCompactSpace N] [IsManifold J ∞ N]

/-- The forward map of `smoothSingularPairChainHomotopyEquiv` commutes strictly with the chain maps
induced by a smooth map of pairs. -/
@[reassoc]
theorem smoothSingularPairChainHomotopyEquiv_hom_naturality {f : M → N} (hf : ContMDiff I J ∞ f)
    {U : Opens M} {V : Opens N} (hUV : Set.MapsTo f U V) :
    (smoothSingularPairChainHomotopyEquiv I R U).hom ≫
        TopPair.singularChainComplexMap
          (TopPair.ofSubsetMap (TopCat.ofHom ⟨f, hf.continuous⟩) hUV) R =
      SSetPair.chainComplexMap (smoothSingularPairMap hf hUV) R ≫
        (smoothSingularPairChainHomotopyEquiv J R V).hom := by
  rw [smoothSingularPairChainHomotopyEquiv_hom, smoothSingularPairChainHomotopyEquiv_hom,
    TopPair.singularChainComplexMap, ← Functor.map_comp, ← Functor.map_comp,
    smoothSingularPairMap_comp_smoothSingularPairι]

/-- **Naturality up to chain homotopy of the relative smoothing inverse.** For a smooth map of
pairs `f : (M, U) → (N, V)`, composing the relative smoothing homotopy inverse on `(M, U)` with the
smooth pushforward along `f` is chain homotopic to pushing forward relative singular chains along
`f` and then applying the relative smoothing homotopy inverse on `(N, V)`. -/
def smoothSingularPairChainHomotopyEquivInvNaturality {f : M → N} (hf : ContMDiff I J ∞ f)
    {U : Opens M} {V : Opens N} (hUV : Set.MapsTo f U V) :
    Homotopy
      ((smoothSingularPairChainHomotopyEquiv I R U).inv ≫
        SSetPair.chainComplexMap (smoothSingularPairMap hf hUV) R)
      (TopPair.singularChainComplexMap
          (TopPair.ofSubsetMap (TopCat.ofHom ⟨f, hf.continuous⟩) hUV) R ≫
        (smoothSingularPairChainHomotopyEquiv J R V).inv) :=
  (smoothSingularPairChainHomotopyEquiv I R U).invNaturality
    (smoothSingularPairChainHomotopyEquiv J R V)
    (smoothSingularPairChainHomotopyEquiv_hom_naturality R hf hUV)

/-- The forward map of `smoothSingularPairCochainHomotopyEquiv` commutes strictly with the cochain
maps induced by a smooth map of pairs. -/
@[reassoc]
theorem smoothSingularPairCochainHomotopyEquiv_hom_naturality {f : M → N}
    (hf : ContMDiff I J ∞ f) {U : Opens M} {V : Opens N} (hUV : Set.MapsTo f U V) :
    TopPair.singularCochainComplexMap (TopPair.ofSubsetMap (TopCat.ofHom ⟨f, hf.continuous⟩) hUV) ≫
        (smoothSingularPairCochainHomotopyEquiv I R k Y U).hom =
      (smoothSingularPairCochainHomotopyEquiv J R k Y V).hom ≫
        SSetPair.cochainComplexMap (smoothSingularPairMap hf hUV) := by
  rw [smoothSingularPairCochainHomotopyEquiv_hom, smoothSingularPairCochainHomotopyEquiv_hom,
    TopPair.singularCochainComplexMap_eq, ← SSetPair.cochainComplexMap_comp,
    ← SSetPair.cochainComplexMap_comp, smoothSingularPairMap_comp_smoothSingularPairι]

/-- **Naturality up to cochain homotopy of the dual relative smoothing inverse.** For a smooth map
of pairs `f : (M, U) → (N, V)`, pulling back smooth relative cochains along `f` and extending to
relative singular cochains on `(M, U)` is cochain homotopic to extending on `(N, V)` first and then
pulling back relative singular cochains along `f`. -/
def smoothSingularPairCochainHomotopyEquivInvNaturality {f : M → N} (hf : ContMDiff I J ∞ f)
    {U : Opens M} {V : Opens N} (hUV : Set.MapsTo f U V) :
    Homotopy
      (SSetPair.cochainComplexMap (smoothSingularPairMap hf hUV) ≫
        (smoothSingularPairCochainHomotopyEquiv I R k Y U).inv)
      ((smoothSingularPairCochainHomotopyEquiv J R k Y V).inv ≫
        TopPair.singularCochainComplexMap
          (TopPair.ofSubsetMap (TopCat.ofHom ⟨f, hf.continuous⟩) hUV)) :=
  ((smoothSingularPairCochainHomotopyEquiv J R k Y V).invNaturality
    (smoothSingularPairCochainHomotopyEquiv I R k Y U)
    (smoothSingularPairCochainHomotopyEquiv_hom_naturality R k Y hf hUV).symm).symm

/-- `smoothSingularRelativeCohomologyIso` is natural in smooth maps of pairs. -/
@[reassoc]
theorem smoothSingularRelativeCohomologyIso_hom_naturality {f : M → N} (hf : ContMDiff I J ∞ f)
    {U : Opens M} {V : Opens N} (hUV : Set.MapsTo f U V) (n : ℕ) :
    TopPair.singularCohomologyMap (TopPair.ofSubsetMap (TopCat.ofHom ⟨f, hf.continuous⟩) hUV) n ≫
        (smoothSingularRelativeCohomologyIso I R k Y U n).hom =
      (smoothSingularRelativeCohomologyIso J R k Y V n).hom ≫
        HomologicalComplex.homologyMap (SSetPair.cochainComplexMap (smoothSingularPairMap hf hUV))
          n := by
  have h := congrArg (fun g ↦
    HomologicalComplex.homologyMap (SSetPair.cochainComplexMap (R := R) (k := k) (M := Y) g) n)
    (smoothSingularPairMap_comp_smoothSingularPairι hf hUV)
  rw [SSetPair.cochainComplexMap_comp, SSetPair.cochainComplexMap_comp,
    HomologicalComplex.homologyMap_comp, HomologicalComplex.homologyMap_comp] at h
  rw [smoothSingularRelativeCohomologyIso_hom, smoothSingularRelativeCohomologyIso_hom,
    TopPair.singularCohomologyMap_eq]
  exact h.symm

/-- The inverse of `smoothSingularRelativeCohomologyIso` is natural in smooth maps of pairs. -/
@[reassoc]
theorem smoothSingularRelativeCohomologyIso_inv_naturality {f : M → N} (hf : ContMDiff I J ∞ f)
    {U : Opens M} {V : Opens N} (hUV : Set.MapsTo f U V) (n : ℕ) :
    HomologicalComplex.homologyMap (SSetPair.cochainComplexMap (smoothSingularPairMap hf hUV)) n ≫
        (smoothSingularRelativeCohomologyIso I R k Y U n).inv =
      (smoothSingularRelativeCohomologyIso J R k Y V n).inv ≫
        TopPair.singularCohomologyMap
          (TopPair.ofSubsetMap (TopCat.ofHom ⟨f, hf.continuous⟩) hUV) n := by
  rw [Iso.comp_inv_eq, Category.assoc, Iso.eq_inv_comp,
    smoothSingularRelativeCohomologyIso_hom_naturality R k Y hf hUV]

end Projective

end TauCeti
