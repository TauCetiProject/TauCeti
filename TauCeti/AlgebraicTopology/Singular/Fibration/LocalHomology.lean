/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.Fibration.Disk
public import TauCeti.AlgebraicTopology.Singular.Excision
public import TauCeti.AlgebraicTopology.Singular.LocalHomology.LivesOver
public import TauCeti.Topology.OpenPartialHomeomorph.Ball

/-!
# Local homology of a Serre fibration along a closed set

Let `p : E → B` be a Serre fibration. This file computes the local homology `Hₖ(E, E ∖ p⁻¹(C))`
of `E` along the part over a closed set `C` of `B` that has a **normal coordinate**
(`TauCeti.TopCat.singularHomologyComplPreimageIsoOfProj`, see the computation below), and then
specializes it to a fibre, where `C` is a point.

Suppose `B` is `T₁` and `b` is a point of `B` in the source of an open partial homeomorphism
`e : B → V` to a real normed space of finite dimension `r`, such as a chart of a topological
manifold modelled on `V`. The **local homology of `E` along the fibre** `F = p⁻¹(b)` is the
relative singular homology `Hₖ(E, E ∖ F)`. With coefficients in a ring `R`:

* `Hₘ(E, E ∖ F; R) = 0` for `m < r` (`TauCeti.TopCat.isZero_singularHomology_complFiber`);
* `Hₙ₊ᵣ(E, E ∖ F; R) ≅ Hₙ(F; R)` (`TauCeti.TopCat.singularHomologyComplFiberIso`).

For the identity of `B` this is the local homology of `B` at `b`
(`TauCeti.singularHomologyComplSingletonFinrankIso`). The composite
`Hₙ₊ᵣ(E) → Hₙ₊ᵣ(E, E ∖ F) ≅ Hₙ(F)` is a shriek map `j_!` of the inclusion `j` of the point `b`,
with untwisted coefficients on the total space. Barraud, Damian, Humilière and Oancea read their
`j_!` through `Hₙ₊ᵣ(E) → Hₙ₊ᵣ(E, E|_{B'}) ≅ Hₙ(F)`, where `B'` is the `(r - 1)`-skeleton of a CW
structure on `B` with a single top cell containing `b` (their Proposition 2.6), and use it to
detect classes **living over the fundamental class** of the base. A class `α ∈ Hₖ(E)` lives over
the fundamental class at `b` when its localization in `Hₖ(E, E ∖ F)` is nonzero
(`TauCeti.LivesOverFundamentalClass`). For a Serre fibration this happens exactly when
`j_! α ≠ 0` (`TauCeti.livesOverFundamentalClass_iff_singularHomologyComplFiberIso_hom_ne_zero`), and
only in degrees at least `r` (`TauCeti.LivesOverFundamentalClass.finrank_le`).

The relative group, rather than the shriek map itself, is used in the definition because it does
not depend on the chart: the identification `Hₙ₊ᵣ(E, E ∖ F) ≅ Hₙ(F)` depends on the chart. Its
construction `TauCeti.TopCat.singularHomologyComplFiberIso` takes a ball in the target of the
chart as an explicit argument.

## The computation

The computation works along the part `p⁻¹(C)` of `E` over any closed set `C` of `B` with an open
neighbourhood `U` and a **normal coordinate** `q : p⁻¹(U) → K`: a Serre fibration to a convex
neighbourhood `K` of `0` in `V` whose fibre over `0` is `p⁻¹(C)`. Excision onto the open set
`p⁻¹(U)`, which contains the closed set `p⁻¹(C)`, identifies `Hₖ(E, E ∖ p⁻¹(C))` with
`Hₖ(p⁻¹(U), p⁻¹(U) ∖ p⁻¹(C))`
(`TopPair.isIso_singularHomologyMap_excisionMap_of_isClosed_subset`), and the part of `p⁻¹(U)`
over `K ∖ {0}` is `p⁻¹(U) ∖ p⁻¹(C)` (`TauCeti.TopCat.complPreimagePairIso`). The homology of a
Serre fibration over a convex neighbourhood of `0` modulo the part over the punctured base is the
shifted homology of the fibre over `0` (`TauCeti.TopCat.singularHomologyPreimageNeZeroIso`), here
`p⁻¹(C)` (`TauCeti.TopCat.preimageZeroHomeomorph`), and vanishes below the dimension
(`TauCeti.TopCat.isZero_singularHomology_preimage_ne_zero`). This gives
`TauCeti.TopCat.singularHomologyComplPreimageIsoOfProj`, natural in maps of fibrations
(`TauCeti.TopCat.singularHomologyComplPreimageIsoOfProj_hom_naturality`).

For the fibre `F` over `b`, choose a ball of positive radius `ε` about `e b` inside the target of
`e`, and let `U` be its preimage in the source of `e` (`OpenPartialHomeomorph.chartBall`), an open
neighbourhood of `b`. The restriction of `p` over `U`, followed by the homeomorphism
`x ↦ e x - e b` of `U` with the ball `K` of radius `ε` about `0`
(`OpenPartialHomeomorph.chartBallHomeomorph`), is a normal coordinate along `C = {b}`
(`OpenPartialHomeomorph.chartBallProj`).

## Main definitions and results

* `TauCeti.TopCat.singularHomologyComplPreimageIsoOfProj`: `Hₙ₊ᵣ(E, E ∖ p⁻¹(C)) ≅ Hₙ(p⁻¹(C))`,
  constructed from a normal coordinate along `C`, and
  `TauCeti.TopCat.isZero_singularHomology_complPreimage_of_proj`: `Hₘ(E, E ∖ p⁻¹(C)) = 0` for
  `m < r`.
* `TauCeti.TopCat.singularHomologyComplFiberIso`: `Hₙ₊ᵣ(E, E ∖ p⁻¹(b)) ≅ Hₙ(p⁻¹(b))`,
  constructed from a ball about `e b` inside the target of `e`. After excision onto the part of `E`
  over the ball, it is `TauCeti.TopCat.singularHomologyPreimageNeZeroIso` for the restricted
  fibration (`TauCeti.TopCat.singularHomologyMap_excisionMap_comp_singularHomologyComplFiberIso_hom`
  and `TauCeti.TopCat.singularHomologyComplFiberIso_inv`).
* `TauCeti.TopCat.isZero_singularHomology_complFiber`: `Hₘ(E, E ∖ p⁻¹(b)) = 0` for `m < r`.
* `TauCeti.livesOverFundamentalClass_iff_singularHomologyComplFiberIso_hom_ne_zero`: a class lives
  over the fundamental class exactly when its image in `Hₖ₋ᵣ(p⁻¹(b))` is nonzero.
* `TauCeti.LivesOverFundamentalClass.finrank_le`: such a class has degree at least `r`.

## References

* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Floer homology with DG coefficients.
  Applications to cotangent bundles*, arXiv:2404.07953, §2.4, Definition 2.3, Example 2.4 and
  Proposition 2.6.
* J.-P. Serre, *Homologie singulière des espaces fibrés. Applications*, Ann. of Math. 54 (1951),
  Chapter II.
-/

public section

noncomputable section

open CategoryTheory Limits Module Metric Set Topology

universe u

namespace OpenPartialHomeomorph

open TauCeti.TopCat

variable {V : Type u} [SeminormedAddCommGroup V] {E B : _root_.TopCat.{u}}
  (e : OpenPartialHomeomorph B V) {b : B} (hb : b ∈ e.source)
  {ε : ℝ} (hε : ball (e b) ε ⊆ e.target)

/-- The restriction of `p` over `chartBall e b ε`, read in the ball about `0` through
`x ↦ e x - e b` (`OpenPartialHomeomorph.chartBallHomeomorph`). -/
def chartBallProj (p : E ⟶ B) :
    _root_.TopCat.of (p ⁻¹' chartBall e b ε) ⟶ _root_.TopCat.of (ball (0 : V) ε) :=
  _root_.TopCat.ofHom (p.hom.restrictPreimage (chartBall e b ε)) ≫
    (_root_.TopCat.isoOfHomeo (X := _root_.TopCat.of (chartBall e b ε))
      (e.chartBallHomeomorph hε)).hom

/-- `chartBallProj e hε p` is the restriction of `p` over `chartBall e b ε` followed by
`OpenPartialHomeomorph.chartBallHomeomorph`. -/
lemma chartBallProj_def (p : E ⟶ B) :
    chartBallProj e hε p =
      _root_.TopCat.ofHom (p.hom.restrictPreimage (chartBall e b ε)) ≫
        (_root_.TopCat.isoOfHomeo (X := _root_.TopCat.of (chartBall e b ε))
          (e.chartBallHomeomorph hε)).hom :=
  chartBallProj.eq_1 e hε p

@[simp]
lemma coe_chartBallProj_apply {p : E ⟶ B} (z : _root_.TopCat.of (p ⁻¹' chartBall e b ε)) :
    (chartBallProj e hε p z : V) = e (p z) - e b := by
  simp [chartBallProj]

include hb in
/-- A point over `chartBall e b ε` lies over `0` in the ball exactly when it lies over `b`. -/
lemma coe_chartBallProj_eq_zero_iff {p : E ⟶ B} (z : _root_.TopCat.of (p ⁻¹' chartBall e b ε)) :
    (chartBallProj e hε p z : V) = 0 ↔ p z = b := by
  rw [coe_chartBallProj_apply, sub_eq_zero]
  exact e.injOn.eq_iff (e.chartBall_subset_source b ε z.2) hb

lemma mem_serreFibrations_chartBallProj {p : E ⟶ B} (hp : serreFibrations p) :
    serreFibrations (chartBallProj e hε p) :=
  serreFibrations.comp_mem _ _ (mem_serreFibrations_restrictPreimage hp _)
    (serreFibrations.of_isIso _)

end OpenPartialHomeomorph

namespace TauCeti

namespace TopCat

/-! ### Local homology along the part over a closed set with a normal coordinate -/

section NormalCoordinate

variable {V : Type u} [NormedAddCommGroup V] {E B : _root_.TopCat.{u}} {p : E ⟶ B}
  {U C : Set B} {K : Set V} {q : _root_.TopCat.of (p ⁻¹' U) ⟶ _root_.TopCat.of K}

/-- Let `q : p⁻¹(U) ⟶ K` be a map whose fibre over `0` is the part of `E` over `C`. Then, over
`U`, the complement of the part of `E` over `C` is the part over `K ∖ {0}` of `q`. -/
def complPreimagePairIso (hq : ∀ z : p ⁻¹' U, (q z : V) = 0 ↔ p z ∈ C) :
    TopPair.interPair (X := E) (p ⁻¹' U) (p ⁻¹' C)ᶜ ≅
      TopPair.ofSubset (q ⁻¹' {x | (x : V) ≠ 0}) :=
  TopPair.ofSubsetIso (Homeomorph.refl _) fun z ↦ (hq z).not.symm

/-- The forward map of `TauCeti.TopCat.complPreimagePairIso` is induced by the identity of
`p⁻¹(U)`. -/
lemma complPreimagePairIso_hom (hq : ∀ z : p ⁻¹' U, (q z : V) = 0 ↔ p z ∈ C) :
    (complPreimagePairIso hq).hom =
      TopPair.ofSubsetMap (_root_.TopCat.ofHom (Homeomorph.refl (p ⁻¹' U)))
        fun z hz ↦ (hq z).not.2 hz :=
  TopPair.ofSubsetIso_hom _ _

/-- The inverse map of `TauCeti.TopCat.complPreimagePairIso` is induced by the identity of
`p⁻¹(U)`. -/
lemma complPreimagePairIso_inv (hq : ∀ z : p ⁻¹' U, (q z : V) = 0 ↔ p z ∈ C) :
    (complPreimagePairIso hq).inv =
      TopPair.ofSubsetMap (_root_.TopCat.ofHom (Homeomorph.refl (p ⁻¹' U)))
        fun z hz ↦ (hq z).not.1 hz :=
  TopPair.ofSubsetIso_inv _ _

/-- Let `q : p⁻¹(U) ⟶ K` be a map whose fibre over `0` is the part of `E` over `C ⊆ U`. Then the
fibre of `q` over `0` is the part `p⁻¹(C)` of `E`. -/
def preimageZeroHomeomorph (hq : ∀ z : p ⁻¹' U, (q z : V) = 0 ↔ p z ∈ C) (hCU : C ⊆ U) :
    (q ⁻¹' {x | (x : V) = 0}) ≃ₜ (p ⁻¹' C) where
  toFun z := ⟨z.1.1, (hq z.1).1 z.2⟩
  invFun y := ⟨⟨y.1, hCU y.2⟩, (hq _).2 y.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
  continuous_invFun := (continuous_subtype_val.subtype_mk _).subtype_mk _

/-- `TauCeti.TopCat.preimageZeroHomeomorph` does not move the underlying point of `E`. -/
lemma coe_preimageZeroHomeomorph_apply (hq : ∀ z : p ⁻¹' U, (q z : V) = 0 ↔ p z ∈ C)
    (hCU : C ⊆ U) (z : q ⁻¹' {x | (x : V) = 0}) :
    (preimageZeroHomeomorph hq hCU z : E) = z.1.1 :=
  (rfl)

/-- The inverse of `TauCeti.TopCat.preimageZeroHomeomorph` does not move the underlying point of
`E`. -/
lemma coe_preimageZeroHomeomorph_symm_apply (hq : ∀ z : p ⁻¹' U, (q z : V) = 0 ↔ p z ∈ C)
    (hCU : C ⊆ U) (y : p ⁻¹' C) : ((preimageZeroHomeomorph hq hCU).symm y).1.1 = y.1 :=
  (rfl)

variable (R : Type u) [Ring R]

/-- Excision onto the part of `E` over an open neighbourhood `U` of a closed set `C` is an
isomorphism on homology. -/
private lemma isIso_singularHomologyMap_excisionMap_preimage (hU : IsOpen U) (hC : IsClosed C)
    (hCU : C ⊆ U) (m : ℕ) :
    IsIso (TopPair.singularHomologyMap
      (TopPair.excisionMap (X := E) (p ⁻¹' U) (p ⁻¹' C)ᶜ) (ModuleCat.of R R) m) :=
  TopPair.isIso_singularHomologyMap_excisionMap_of_isClosed_subset (ModuleCat.of R R)
    (X := E) (hU.preimage p.hom.continuous) (hC.preimage p.hom.continuous) (preimage_mono hCU) m

/-- Excision onto the part of `E` over `U`, followed by `TauCeti.TopCat.complPreimagePairIso`. -/
private def excisionIso (hU : IsOpen U) (hC : IsClosed C) (hCU : C ⊆ U)
    (hq : ∀ z : p ⁻¹' U, (q z : V) = 0 ↔ p z ∈ C) (m : ℕ) :
    (TopPair.ofSubset (p ⁻¹' C)ᶜ).singularHomology (ModuleCat.of R R) m ≅
      (TopPair.ofSubset (q ⁻¹' {x | (x : V) ≠ 0})).singularHomology (ModuleCat.of R R) m :=
  haveI := isIso_singularHomologyMap_excisionMap_preimage (p := p) R hU hC hCU m
  (asIso (TopPair.singularHomologyMap
      (TopPair.excisionMap (X := E) (p ⁻¹' U) (p ⁻¹' C)ᶜ) _ m)).symm ≪≫
    TopPair.singularHomologyMapIso _ (complPreimagePairIso hq) m

/-- The defining square of `excisionIso`: after the excision inclusion it is the map induced by
`TauCeti.TopCat.complPreimagePairIso`. -/
@[reassoc]
private lemma singularHomologyMap_excisionMap_comp_excisionIso_hom (hU : IsOpen U)
    (hC : IsClosed C) (hCU : C ⊆ U) (hq : ∀ z : p ⁻¹' U, (q z : V) = 0 ↔ p z ∈ C) (m : ℕ) :
    TopPair.singularHomologyMap
        (TopPair.excisionMap (X := E) (p ⁻¹' U) (p ⁻¹' C)ᶜ) (ModuleCat.of R R) m ≫
        (excisionIso R hU hC hCU hq m).hom =
      TopPair.singularHomologyMap (complPreimagePairIso hq).hom (ModuleCat.of R R) m := by
  simp [excisionIso]

section Naturality

variable {E' : _root_.TopCat.{u}} {p' : E' ⟶ B} {g : E ⟶ E'}
  {q' : _root_.TopCat.of (p' ⁻¹' U) ⟶ _root_.TopCat.of K}

/-- The isomorphism `excisionIso` is natural in maps `g` over `B` commuting with the maps to `K`:
after excision, the map induced by `g` is the map induced by its restriction over `U`. -/
@[reassoc]
private lemma excisionIso_hom_naturality (hU : IsOpen U) (hC : IsClosed C) (hCU : C ⊆ U)
    (hq : ∀ z : p ⁻¹' U, (q z : V) = 0 ↔ p z ∈ C)
    (hq' : ∀ z : p' ⁻¹' U, (q' z : V) = 0 ↔ p' z ∈ C) (hg : g ≫ p' = p)
    (hgq : g.preimageMap hg U ≫ q' = q) (m : ℕ) :
    TopPair.singularHomologyMap (TopPair.ofSubsetMap g (g.mapsTo_preimage_of_comp_eq hg Cᶜ))
        (ModuleCat.of R R) m ≫ (excisionIso R hU hC hCU hq' m).hom =
      (excisionIso R hU hC hCU hq m).hom ≫
        TopPair.singularHomologyMap (TopPair.ofSubsetMap (g.preimageMap hg U)
          ((g.preimageMap hg U).mapsTo_preimage_of_comp_eq hgq _)) (ModuleCat.of R R) m := by
  -- The map of excision data induced by `g`.
  let Q := TopPair.interPairMap g (g.mapsTo_preimage_of_comp_eq hg U)
    (g.mapsTo_preimage_of_comp_eq hg Cᶜ)
  have hQ : TopPair.excisionMap (X := E) (p ⁻¹' U) (p ⁻¹' C)ᶜ ≫
        TopPair.ofSubsetMap g (g.mapsTo_preimage_of_comp_eq hg Cᶜ) =
      Q ≫ TopPair.excisionMap (X := E') (p' ⁻¹' U) (p' ⁻¹' C)ᶜ :=
    (TopPair.interPairMap_comp_excisionMap g _ _).symm
  have hQ' : (complPreimagePairIso hq).hom ≫
        TopPair.ofSubsetMap (g.preimageMap hg U)
          ((g.preimageMap hg U).mapsTo_preimage_of_comp_eq hgq _) =
      Q ≫ (complPreimagePairIso hq').hom :=
    TopPair.hom_ext_of_fst _ (by
      ext x
      apply Subtype.ext
      rw [complPreimagePairIso_hom, complPreimagePairIso_hom, TopPair.Hom.fst_comp,
        TopPair.Hom.fst_comp]
      -- The ambient spaces of the pairs are `TopCat.of` of subtypes, which `rw` does not unfold.
      erw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply, TopPair.ofSubsetMap_fst_apply,
        TopPair.ofSubsetMap_fst_apply, TopPair.ofSubsetMap_fst_apply]
      exact (_root_.TopCat.Hom.coe_preimageMap_apply g hg _ x).trans
        (TopPair.interPairMap_fst_apply _ _ _ x).symm)
  have := isIso_singularHomologyMap_excisionMap_preimage (p := p) R hU hC hCU m
  rw [← cancel_epi (TopPair.singularHomologyMap
      (TopPair.excisionMap (X := E) (p ⁻¹' U) (p ⁻¹' C)ᶜ) (ModuleCat.of R R) m),
    singularHomologyMap_excisionMap_comp_excisionIso_hom_assoc,
    ← TopPair.singularHomologyMap_comp_assoc, hQ, TopPair.singularHomologyMap_comp_assoc,
    singularHomologyMap_excisionMap_comp_excisionIso_hom, ← TopPair.singularHomologyMap_comp,
    ← TopPair.singularHomologyMap_comp, hQ']

/-- The identifications `TauCeti.TopCat.preimageZeroHomeomorph` of the fibres over `0` with the
parts over `C` carry the restriction of `g` over `U` to the restriction of `g` over `C`. -/
private lemma preimageZeroHomeomorph_naturality (hCU : C ⊆ U)
    (hq : ∀ z : p ⁻¹' U, (q z : V) = 0 ↔ p z ∈ C)
    (hq' : ∀ z : p' ⁻¹' U, (q' z : V) = 0 ↔ p' z ∈ C) (hg : g ≫ p' = p)
    (hgq : g.preimageMap hg U ≫ q' = q) :
    (_root_.TopCat.isoOfHomeo (preimageZeroHomeomorph hq hCU)).hom ≫ g.preimageMap hg C =
      (g.preimageMap hg U).preimageMap hgq {x | (x : V) = 0} ≫
        (_root_.TopCat.isoOfHomeo (preimageZeroHomeomorph hq' hCU)).hom := by
  ext x
  rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply,
    _root_.TopCat.Hom.coe_preimageMap_apply, _root_.TopCat.isoOfHomeo_hom,
    _root_.TopCat.ofHom_apply, ContinuousMap.coe_ofClass, coe_preimageZeroHomeomorph_apply]
  exact ((congrArg Subtype.val (_root_.TopCat.Hom.coe_preimageMap_apply _ _ _ x)).trans
    (_root_.TopCat.Hom.coe_preimageMap_apply _ _ _ x.1)).symm

end Naturality

variable [NormedSpace ℝ V] [FiniteDimensional ℝ V]

/-- **The homology of a Serre fibration modulo the complement of the part over a closed set with
a normal coordinate vanishes below the dimension.** Let `C ⊆ U` be a closed set and an open set
of `B`, and `q : p⁻¹(U) ⟶ K` a Serre fibration to a convex neighbourhood `K` of `0` in a
finite-dimensional real normed space `V`, whose fibre over `0` is the part of `E` over `C`. Then
`Hₘ(E, E ∖ p⁻¹(C); R) = 0` for every `m < dim V`. -/
theorem isZero_singularHomology_complPreimage_of_proj (hU : IsOpen U) (hC : IsClosed C)
    (hCU : C ⊆ U) (hq : ∀ z : p ⁻¹' U, (q z : V) = 0 ↔ p z ∈ C) (hqs : serreFibrations q)
    (hK : Convex ℝ K) (hK₀ : K ∈ 𝓝 (0 : V)) {m : ℕ} (hm : m < finrank ℝ V) :
    IsZero ((TopPair.ofSubset (p ⁻¹' C)ᶜ).singularHomology (ModuleCat.of R R) m) :=
  (isZero_singularHomology_preimage_ne_zero R hqs hK hK₀ hm).of_iso
    (excisionIso R hU hC hCU hq m)

/-- **The homology of a Serre fibration modulo the complement of the part over a closed set with
a normal coordinate is the shifted homology of that part.** Let `C ⊆ U` be a closed set and an
open set of `B`, and `q : p⁻¹(U) ⟶ K` a Serre fibration to a convex neighbourhood `K` of `0` in a
real normed space `V` of finite dimension `r`, whose fibre over `0` is the part of `E` over `C`.
Then `Hₘ(E, E ∖ p⁻¹(C); R) ≅ Hₙ(p⁻¹(C); R)` for `m = n + r`.

The isomorphism is excision onto the part of `E` over `U`, followed by
`TauCeti.TopCat.singularHomologyPreimageNeZeroIso` for `q`
(`TauCeti.TopCat.singularHomologyMap_excisionMap_comp_singularHomologyComplPreimageIsoOfProj_hom`).
-/
def singularHomologyComplPreimageIsoOfProj (hU : IsOpen U) (hC : IsClosed C) (hCU : C ⊆ U)
    (hq : ∀ z : p ⁻¹' U, (q z : V) = 0 ↔ p z ∈ C) (hqs : serreFibrations q) (hK : Convex ℝ K)
    (hK₀ : K ∈ 𝓝 (0 : V)) (n m : ℕ) (h : n + finrank ℝ V = m) :
    (TopPair.ofSubset (p ⁻¹' C)ᶜ).singularHomology (ModuleCat.of R R) m ≅
      ((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} R) n).obj
        (ModuleCat.of R R)).obj (_root_.TopCat.of (p ⁻¹' C)) :=
  excisionIso R hU hC hCU hq m ≪≫ singularHomologyPreimageNeZeroIso R hqs hK hK₀ n m h ≪≫
    ((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} R) n).obj
      (ModuleCat.of R R)).mapIso (_root_.TopCat.isoOfHomeo (preimageZeroHomeomorph hq hCU))

/-- The isomorphism `TauCeti.TopCat.singularHomologyComplPreimageIsoOfProj` commutes with
excision onto the part of `E` over `U`: after excision it is
`TauCeti.TopCat.singularHomologyPreimageNeZeroIso` for `q`, followed by the identification of the
fibre of `q` over `0` with the part of `E` over `C`. -/
@[reassoc]
lemma singularHomologyMap_excisionMap_comp_singularHomologyComplPreimageIsoOfProj_hom
    (hU : IsOpen U) (hC : IsClosed C) (hCU : C ⊆ U)
    (hq : ∀ z : p ⁻¹' U, (q z : V) = 0 ↔ p z ∈ C) (hqs : serreFibrations q) (hK : Convex ℝ K)
    (hK₀ : K ∈ 𝓝 (0 : V)) (n m : ℕ) (h : n + finrank ℝ V = m) :
    TopPair.singularHomologyMap
        (TopPair.excisionMap (X := E) (p ⁻¹' U) (p ⁻¹' C)ᶜ) (ModuleCat.of R R) m ≫
        (singularHomologyComplPreimageIsoOfProj R hU hC hCU hq hqs hK hK₀ n m h).hom =
      TopPair.singularHomologyMap (complPreimagePairIso hq).hom (ModuleCat.of R R) m ≫
        (singularHomologyPreimageNeZeroIso R hqs hK hK₀ n m h).hom ≫
        ((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} R) n).obj
          (ModuleCat.of R R)).map
          (_root_.TopCat.isoOfHomeo (preimageZeroHomeomorph hq hCU)).hom := by
  simp [singularHomologyComplPreimageIsoOfProj, excisionIso]

/-- The inverse of `TauCeti.TopCat.singularHomologyComplPreimageIsoOfProj` is the inverse of the
identification `TauCeti.TopCat.preimageZeroHomeomorph` of the fibre of `q` over `0` with the part
of `E` over `C`, followed by the inverse of `TauCeti.TopCat.singularHomologyPreimageNeZeroIso`,
the inverse of `TauCeti.TopCat.complPreimagePairIso` and the excision inclusion. -/
@[reassoc]
lemma singularHomologyComplPreimageIsoOfProj_inv (hU : IsOpen U) (hC : IsClosed C)
    (hCU : C ⊆ U) (hq : ∀ z : p ⁻¹' U, (q z : V) = 0 ↔ p z ∈ C) (hqs : serreFibrations q)
    (hK : Convex ℝ K) (hK₀ : K ∈ 𝓝 (0 : V)) (n m : ℕ) (h : n + finrank ℝ V = m) :
    (singularHomologyComplPreimageIsoOfProj R hU hC hCU hq hqs hK hK₀ n m h).inv =
      ((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} R) n).obj
          (ModuleCat.of R R)).map
          (_root_.TopCat.isoOfHomeo (preimageZeroHomeomorph hq hCU)).inv ≫
        (singularHomologyPreimageNeZeroIso R hqs hK hK₀ n m h).inv ≫
        TopPair.singularHomologyMap (complPreimagePairIso hq).inv (ModuleCat.of R R) m ≫
        TopPair.singularHomologyMap
          (TopPair.excisionMap (X := E) (p ⁻¹' U) (p ⁻¹' C)ᶜ) (ModuleCat.of R R) m := by
  simp [singularHomologyComplPreimageIsoOfProj, excisionIso]

/-- **The local homology along the part over a closed set with a normal coordinate is natural in
maps of fibrations.** Let `p : E ⟶ B` and `p' : E' ⟶ B` carry Serre fibrations `q` and `q'` as in
`TauCeti.TopCat.singularHomologyComplPreimageIsoOfProj`, and let `g : E ⟶ E'` be a map over `B`
whose restriction over `U` is a map over `K`. Under these isomorphisms, the map induced by `g` on
relative homology is the map induced by the restriction `p⁻¹(C) ⟶ p'⁻¹(C)` of `g`. -/
@[reassoc]
theorem singularHomologyComplPreimageIsoOfProj_hom_naturality {E' : _root_.TopCat.{u}}
    {p' : E' ⟶ B} {g : E ⟶ E'} {q' : _root_.TopCat.of (p' ⁻¹' U) ⟶ _root_.TopCat.of K}
    (hU : IsOpen U) (hC : IsClosed C) (hCU : C ⊆ U)
    (hq : ∀ z : p ⁻¹' U, (q z : V) = 0 ↔ p z ∈ C)
    (hq' : ∀ z : p' ⁻¹' U, (q' z : V) = 0 ↔ p' z ∈ C) (hqs : serreFibrations q)
    (hqs' : serreFibrations q') (hK : Convex ℝ K) (hK₀ : K ∈ 𝓝 (0 : V)) (hg : g ≫ p' = p)
    (hgq : g.preimageMap hg U ≫ q' = q) (n m : ℕ) (h : n + finrank ℝ V = m) :
    TopPair.singularHomologyMap (TopPair.ofSubsetMap g (g.mapsTo_preimage_of_comp_eq hg Cᶜ))
        (ModuleCat.of R R) m ≫
        (singularHomologyComplPreimageIsoOfProj R hU hC hCU hq' hqs' hK hK₀ n m h).hom =
      (singularHomologyComplPreimageIsoOfProj R hU hC hCU hq hqs hK hK₀ n m h).hom ≫
        ((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} R) n).obj
          (ModuleCat.of R R)).map (g.preimageMap hg C) := by
  simp only [singularHomologyComplPreimageIsoOfProj, Iso.trans_hom, Functor.mapIso_hom,
    Category.assoc]
  rw [excisionIso_hom_naturality_assoc R hU hC hCU hq hq' hg hgq m,
    singularHomologyPreimageNeZeroIso_hom_naturality_assoc R hqs hqs' hK hK₀ hgq
      ((g.preimageMap hg U).preimageMap hgq {x | (x : V) = 0})
      (fun x ↦ _root_.TopCat.Hom.coe_preimageMap_apply _ _ _ x) n m h,
    ← Functor.map_comp, ← Functor.map_comp, preimageZeroHomeomorph_naturality hCU hq hq' hg hgq]

end NormalCoordinate

section Chart

variable {V : Type u} [NormedAddCommGroup V] {E B : _root_.TopCat.{u}}
  {p : E ⟶ B} (R : Type u) [Ring R] (e : OpenPartialHomeomorph B V) {b : B} (hb : b ∈ e.source)
  {ε : ℝ} (hε : ball (e b) ε ⊆ e.target)

variable [T1Space B] [NormedSpace ℝ V] [FiniteDimensional ℝ V]

include e hb in
/-- **The homology of a Serre fibration modulo the complement of a fibre vanishes below the
dimension.** Let `p : E ⟶ B` be a Serre fibration over a `T₁` space, and let `b` lie in the source
of an open partial homeomorphism `e : B → V` to a finite-dimensional real normed space. Then
`Hₘ(E, E ∖ p⁻¹(b); R) = 0` for every `m < dim V`. -/
theorem isZero_singularHomology_complFiber (hp : serreFibrations p) {m : ℕ}
    (hm : m < finrank ℝ V) :
    IsZero ((TopPair.ofSubset (p ⁻¹' {b})ᶜ).singularHomology (ModuleCat.of R R) m) := by
  obtain ⟨ε, hε₀, hε⟩ := Metric.isOpen_iff.1 e.open_target (e b) (e.map_source hb)
  exact isZero_singularHomology_complPreimage_of_proj R (e.isOpen_chartBall b ε)
    isClosed_singleton (singleton_subset_iff.2 (e.mem_chartBall_self hb hε₀))
    (e.coe_chartBallProj_eq_zero_iff hb hε) (e.mem_serreFibrations_chartBallProj hε hp)
    (convex_ball 0 _) (ball_mem_nhds 0 hε₀) hm

/-- **The homology of a Serre fibration modulo the complement of a fibre is the shifted homology
of the fibre.** Let `p : E ⟶ B` be a Serre fibration over a `T₁` space, and let `b` lie in the
source of an open partial homeomorphism `e : B → V` to a real normed space of finite dimension `r`,
such as the chart `chartAt V b` of a topological manifold modelled on `V`. Then
`Hₘ(E, E ∖ p⁻¹(b); R) ≅ Hₙ(p⁻¹(b); R)` for `m = n + r`.

The isomorphism depends on `e`, and is constructed from a ball of radius `ε` about `e b` inside
the target of `e`: it is `TauCeti.TopCat.singularHomologyComplPreimageIsoOfProj` for the
restriction `OpenPartialHomeomorph.chartBallProj` of `p` over
`OpenPartialHomeomorph.chartBall e b ε`, that is, excision onto the part of `E` over that set,
followed by `TauCeti.TopCat.singularHomologyPreimageNeZeroIso` for the restriction of `p`
(`TauCeti.TopCat.singularHomologyMap_excisionMap_comp_singularHomologyComplFiberIso_hom`). -/
def singularHomologyComplFiberIso (hε₀ : 0 < ε) (hp : serreFibrations p) (n m : ℕ)
    (h : n + finrank ℝ V = m) :
    (TopPair.ofSubset (p ⁻¹' {b})ᶜ).singularHomology (ModuleCat.of R R) m ≅
      ((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} R) n).obj
        (ModuleCat.of R R)).obj (_root_.TopCat.of (p ⁻¹' {b})) :=
  singularHomologyComplPreimageIsoOfProj R (e.isOpen_chartBall b ε) isClosed_singleton
    (singleton_subset_iff.2 (e.mem_chartBall_self hb hε₀)) (e.coe_chartBallProj_eq_zero_iff hb hε)
    (e.mem_serreFibrations_chartBallProj hε hp) (convex_ball 0 _) (ball_mem_nhds 0 hε₀) n m h

/-- The isomorphism `TauCeti.TopCat.singularHomologyComplFiberIso` commutes with excision
onto the part of `E` over `OpenPartialHomeomorph.chartBall e b ε`: after excision it is
`TauCeti.TopCat.singularHomologyPreimageNeZeroIso` for the restricted fibration, followed by the
identification of its fibre over `0` with the fibre over `b`. -/
@[reassoc]
lemma singularHomologyMap_excisionMap_comp_singularHomologyComplFiberIso_hom
    (hε₀ : 0 < ε) (hp : serreFibrations p) (n m : ℕ) (h : n + finrank ℝ V = m) :
    TopPair.singularHomologyMap
        (TopPair.excisionMap (X := E) (p ⁻¹' e.chartBall b ε) (p ⁻¹' {b})ᶜ)
        (ModuleCat.of R R) m ≫
        (singularHomologyComplFiberIso R e hb hε hε₀ hp n m h).hom =
      TopPair.singularHomologyMap (complPreimagePairIso (e.coe_chartBallProj_eq_zero_iff hb hε)).hom
          (ModuleCat.of R R) m ≫
        (singularHomologyPreimageNeZeroIso R (e.mem_serreFibrations_chartBallProj hε hp)
          (convex_ball 0 _) (ball_mem_nhds 0 hε₀) n m h).hom ≫
        ((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} R) n).obj
          (ModuleCat.of R R)).map
          (_root_.TopCat.isoOfHomeo (preimageZeroHomeomorph (e.coe_chartBallProj_eq_zero_iff hb hε)
            (singleton_subset_iff.2 (e.mem_chartBall_self hb hε₀)))).hom :=
  singularHomologyMap_excisionMap_comp_singularHomologyComplPreimageIsoOfProj_hom R _ _ _ _ _ _ _
    n m h

/-- The inverse of `TauCeti.TopCat.singularHomologyComplFiberIso` is the inverse of the
identification `TauCeti.TopCat.preimageZeroHomeomorph` of the fibre over `0` of the restricted
fibration with the fibre over `b`, followed by the inverse of
`TauCeti.TopCat.singularHomologyPreimageNeZeroIso`, the inverse of
`TauCeti.TopCat.complPreimagePairIso` and the excision inclusion. -/
@[reassoc]
lemma singularHomologyComplFiberIso_inv
    (hε₀ : 0 < ε) (hp : serreFibrations p) (n m : ℕ) (h : n + finrank ℝ V = m) :
    (singularHomologyComplFiberIso R e hb hε hε₀ hp n m h).inv =
      ((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} R) n).obj
          (ModuleCat.of R R)).map
          (_root_.TopCat.isoOfHomeo (preimageZeroHomeomorph (e.coe_chartBallProj_eq_zero_iff hb hε)
            (singleton_subset_iff.2 (e.mem_chartBall_self hb hε₀)))).inv ≫
        (singularHomologyPreimageNeZeroIso R (e.mem_serreFibrations_chartBallProj hε hp)
          (convex_ball 0 _) (ball_mem_nhds 0 hε₀) n m h).inv ≫
        TopPair.singularHomologyMap
          (complPreimagePairIso (e.coe_chartBallProj_eq_zero_iff hb hε)).inv (ModuleCat.of R R) m ≫
        TopPair.singularHomologyMap
          (TopPair.excisionMap (X := E) (p ⁻¹' e.chartBall b ε) (p ⁻¹' {b})ᶜ)
          (ModuleCat.of R R) m :=
  singularHomologyComplPreimageIsoOfProj_inv R _ _ _ _ _ _ _ n m h

end Chart

end TopCat

/-! ### Classes living over the fundamental class -/

variable {V : Type u} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  {E B : _root_.TopCat.{u}} [T1Space B] {p : E ⟶ B} {R : Type u} [Ring R]
  (e : OpenPartialHomeomorph B V) {b : B} (hb : b ∈ e.source)

/-- **Living over the fundamental class through the shriek map.** For a Serre fibration over a
`T₁` space with a chart `e` of dimension `r` at `b`, a class `α ∈ Hₙ₊ᵣ(E; R)` lives over the
fundamental class at `b` exactly when its image under the shriek map
`Hₙ₊ᵣ(E) → Hₙ₊ᵣ(E, E ∖ p⁻¹(b)) ≅ Hₙ(p⁻¹(b))` of the inclusion of `b` is nonzero, for any ball about
`e b` inside the target of `e`. -/
theorem livesOverFundamentalClass_iff_singularHomologyComplFiberIso_hom_ne_zero
    {ε : ℝ} (hε : ball (e b) ε ⊆ e.target) (hε₀ : 0 < ε) (hp : TopCat.serreFibrations p)
    {n m : ℕ} (h : n + finrank ℝ V = m)
    (α : ((_root_.TopCat.toSSet.obj E).homology (ModuleCat.of R R) m : ModuleCat.{u} R)) :
    LivesOverFundamentalClass (ModuleCat.of R R) p b α ↔
      (TopCat.singularHomologyComplFiberIso R e hb hε hε₀ hp n m h).hom.hom
        ((fiberLocalization (ModuleCat.of R R) p b m).hom α) ≠ 0 := by
  rw [livesOverFundamentalClass_iff, not_iff_not]
  exact ⟨fun hα ↦ by rw [hα, map_zero], fun hα ↦ by
    simpa using congrArg (TopCat.singularHomologyComplFiberIso R e hb hε hε₀ hp n m h).inv.hom hα⟩

include hb in
/-- **A class living over the fundamental class has degree at least the dimension of the base.**
For a Serre fibration over a `T₁` space with a chart of dimension `r` at `b`, the local homology
`Hₖ(E, E ∖ p⁻¹(b))` vanishes for `k < r`, so no class of degree below `r` lives over the
fundamental class at `b`. -/
theorem LivesOverFundamentalClass.finrank_le (hp : TopCat.serreFibrations p) {d : ℕ}
    {α : ((_root_.TopCat.toSSet.obj E).homology (ModuleCat.of R R) d : ModuleCat.{u} R)}
    (h : LivesOverFundamentalClass (ModuleCat.of R R) p b α) : finrank ℝ V ≤ d := by
  by_contra hd
  have := ModuleCat.isZero_iff_subsingleton.1 (TopCat.isZero_singularHomology_complFiber R e hb hp
    (not_le.1 hd))
  exact (livesOverFundamentalClass_iff _ _ _ _).1 h (Subsingleton.elim _ _)

end TauCeti
