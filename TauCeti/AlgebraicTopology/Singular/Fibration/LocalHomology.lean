/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.FiberBundle.Trivialization
public import TauCeti.AlgebraicTopology.Singular.Fibration.Disk
public import TauCeti.AlgebraicTopology.Singular.Excision
public import TauCeti.AlgebraicTopology.Singular.LocalHomology.LivesOver
public import TauCeti.Topology.OpenPartialHomeomorph.Ball

/-!
# Local homology of a Serre fibration along a fibre

Let `p : E → B` be a Serre fibration over a `T₁` space `B` and `b` a point of `B` in the source
of an open partial homeomorphism `e : B → V` to a real normed space of finite dimension `r`, such
as a chart of a topological manifold modelled on `V`. The **local homology of `E` along the
fibre** `F = p⁻¹(b)` is the relative singular homology `Hₖ(E, E ∖ F)`. This file computes it,
with coefficients in a module `M` over a ring `R`:

* `Hₘ(E, E ∖ F; M) = 0` for `m < r` (`TauCeti.TopCat.isZero_singularHomology_complFiber`);
* `Hₙ₊ᵣ(E, E ∖ F; M) ≅ Hₙ(F; M)` (`TauCeti.TopCat.singularHomologyComplFiberIso`).

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

The identification is natural in maps of fibrations: for a second Serre fibration
`p' : E' ⟶ B` and a map `f : E ⟶ E'` over `B`, the map induced by `f` on `Hₙ₊ᵣ(E, E ∖ F)` becomes,
for the same chart and ball, the map induced on `Hₙ(F)` by the restriction `F ⟶ F'` of `f` to the
fibres (`TauCeti.TopCat.singularHomologyComplFiberIso_hom_naturality`). So the shriek maps commute
with `f`, `j_! ∘ f_* = f_* ∘ j_!` (the source's Proposition 2.12), and `f_* α` lives over the
fundamental class exactly when `f_* (j_! α) ≠ 0`
(`TauCeti.livesOverFundamentalClass_homologyMap_iff`). This is the step of the source's
Corollary 2.13 that passes from a nonvanishing class of the fibre to a class of the total space
living over the fundamental class.

The relative group, rather than the shriek map itself, is used in the definition because it does
not depend on the chart: the identification `Hₙ₊ᵣ(E, E ∖ F) ≅ Hₙ(F)` depends on the chart. Its
construction `TauCeti.TopCat.singularHomologyComplFiberIso` takes a ball in the target of the
chart as an explicit argument.

## The computation

Choose a ball of positive radius `ε` about `e b` inside the target of `e`, and let `U` be its
preimage in the source of `e` (`OpenPartialHomeomorph.chartBall`), an open neighbourhood of `b`.
Excision onto the open set `p⁻¹(U)`, which contains the closed fibre `F`, identifies
`Hₖ(E, E ∖ F)` with `Hₖ(p⁻¹(U), p⁻¹(U) ∖ F)`
(`TopPair.isIso_singularHomologyMap_excisionMap_of_isClosed_subset`). The restriction of `p` over
`U`, followed by the homeomorphism `x ↦ e x - e b` of `U` with the ball `K` of radius `ε` about
`0` (`OpenPartialHomeomorph.chartBallHomeomorph`), is a Serre fibration over the convex
neighbourhood `K` of `0` (`OpenPartialHomeomorph.chartBallProj`) whose fibre over `0` is `F`
(`OpenPartialHomeomorph.chartBallProjFiberHomeomorph`), and the part of `p⁻¹(U)` over `K ∖ {0}` is
`p⁻¹(U) ∖ F` (`OpenPartialHomeomorph.chartBallComplFiberPairIso`). The homology of a Serre
fibration over a convex neighbourhood of `0` modulo the part over the punctured base is the shifted
homology of the fibre (`TauCeti.TopCat.singularHomologyPreimageNeZeroIso`), and vanishes below the
dimension
(`TauCeti.TopCat.isZero_singularHomology_preimage_ne_zero`).

## Main definitions and results

* `TauCeti.TopCat.singularHomologyComplFiberIso`: `Hₙ₊ᵣ(E, E ∖ p⁻¹(b)) ≅ Hₙ(p⁻¹(b))`,
  constructed from a ball about `e b` inside the target of `e`. After excision onto the part of `E`
  over the ball, it is `TauCeti.TopCat.singularHomologyPreimageNeZeroIso` for the restricted
  fibration (`TauCeti.TopCat.singularHomologyMap_excisionMap_comp_singularHomologyComplFiberIso_hom`
  and `TauCeti.TopCat.singularHomologyComplFiberIso_inv`).
* `TauCeti.TopCat.isZero_singularHomology_complFiber`: `Hₘ(E, E ∖ p⁻¹(b)) = 0` for `m < r`.
* `TauCeti.livesOverFundamentalClass_iff_singularHomologyComplFiberIso_hom_ne_zero`: a class lives
  over the fundamental class exactly when its image in `Hₖ₋ᵣ(p⁻¹(b))` is nonzero.
* `TauCeti.LivesOverFundamentalClass.finrank_le`: such a class has degree at least `r`.
* `OpenPartialHomeomorph.chartBallTrivialization`: a trivialization of `p` over the chart ball
  identifies the part of `E` over it with the product of the ball of radius `ε` about `0` and the
  fibre, compatibly with `OpenPartialHomeomorph.chartBallProj`
  (`OpenPartialHomeomorph.chartBallTrivialization_apply_fst`).
* `TauCeti.TopCat.singularHomologyComplFiberIso_hom_naturality`: the identification is natural in
  maps of fibrations over `B`.
* `TauCeti.homologyMap_comp_fiberLocalization_comp_singularHomologyComplFiberIso_hom`: the shriek
  map of the inclusion of `b` commutes with maps of fibrations over `B`.
* `TauCeti.livesOverFundamentalClass_homologyMap_iff`: the image of a class under a map of
  fibrations lives over the fundamental class exactly when the image of its shriek is nonzero.

## References

* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Floer homology with DG coefficients.
  Applications to cotangent bundles*, arXiv:2404.07953, §2.4, Definition 2.3, Example 2.4,
  Proposition 2.6, Proposition 2.12 and Corollary 2.13.
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

/-- Over `chartBall e b ε`, the restriction of a map `f` over `B` is a map over the ball: it
commutes with `chartBallProj`. -/
@[reassoc]
lemma preimageMap_comp_chartBallProj {E' : _root_.TopCat.{u}} {p : E ⟶ B} {p' : E' ⟶ B}
    {f : E ⟶ E'} (hf : f ≫ p' = p) :
    f.preimageMap hf (chartBall e b ε) ≫ chartBallProj e hε p' = chartBallProj e hε p := by
  ext z
  rw [ConcreteCategory.comp_apply, coe_chartBallProj_apply, coe_chartBallProj_apply,
    TopCat.Hom.coe_preimageMap_apply, ← ConcreteCategory.comp_apply, hf]

include hb in
/-- A point over `chartBall e b ε` lies over `0` in the ball exactly when it lies over `b`. -/
lemma coe_chartBallProj_eq_zero_iff {p : E ⟶ B} (z : _root_.TopCat.of (p ⁻¹' chartBall e b ε)) :
    (chartBallProj e hε p z : V) = 0 ↔ p z = b := by
  rw [coe_chartBallProj_apply, sub_eq_zero]
  exact e.injOn.eq_iff (e.chartBall_subset_source b ε z.property) hb

lemma mem_serreFibrations_chartBallProj {p : E ⟶ B} (hp : serreFibrations p) :
    serreFibrations (chartBallProj e hε p) :=
  serreFibrations.comp_mem _ _ (mem_serreFibrations_restrictPreimage hp _)
    (serreFibrations.of_isIso _)

/-- Over `chartBall e b ε`, the complement of the fibre of `p` over `b` is the part over the
punctured ball of `chartBallProj e hε p`. -/
def chartBallComplFiberPairIso (p : E ⟶ B) :
    TopPair.interPair (X := E) (p ⁻¹' chartBall e b ε) (p ⁻¹' {b})ᶜ ≅
      TopPair.ofSubset (chartBallProj e hε p ⁻¹' {x | (x : V) ≠ 0}) :=
  TopPair.ofSubsetIso (Homeomorph.refl _) fun z ↦
    (coe_chartBallProj_eq_zero_iff e hb hε z).not.symm

/-- The forward map of `chartBallComplFiberPairIso` is induced by the identity of
`p⁻¹(chartBall e b ε)`. -/
lemma chartBallComplFiberPairIso_hom (p : E ⟶ B) :
    (chartBallComplFiberPairIso e hb hε p).hom =
      TopPair.ofSubsetMap (_root_.TopCat.ofHom (Homeomorph.refl (p ⁻¹' chartBall e b ε)))
        fun z hz ↦ (coe_chartBallProj_eq_zero_iff e hb hε z).not.2 hz :=
  TopPair.ofSubsetIso_hom _ _

/-- The inverse map of `chartBallComplFiberPairIso` is induced by the identity of
`p⁻¹(chartBall e b ε)`. -/
lemma chartBallComplFiberPairIso_inv (p : E ⟶ B) :
    (chartBallComplFiberPairIso e hb hε p).inv =
      TopPair.ofSubsetMap (_root_.TopCat.ofHom (Homeomorph.refl (p ⁻¹' chartBall e b ε)))
        fun z hz ↦ (coe_chartBallProj_eq_zero_iff e hb hε z).not.1 hz :=
  TopPair.ofSubsetIso_inv _ _

/-- The fibre over `0` of `chartBallProj e hε p` is the fibre of `p` over `b`. -/
def chartBallProjFiberHomeomorph (p : E ⟶ B) (hε₀ : 0 < ε) :
    (chartBallProj e hε p ⁻¹' {x | (x : V) = 0}) ≃ₜ (p ⁻¹' {b}) where
  toFun z := ⟨z.val.val, (coe_chartBallProj_eq_zero_iff e hb hε z.val).1 z.property⟩
  invFun y :=
    have hy : p y.val = b := mem_singleton_iff.1 y.property
    ⟨⟨y.val, by
      rw [mem_preimage, hy]
      exact mem_chartBall_self e hb hε₀⟩, (coe_chartBallProj_eq_zero_iff e hb hε _).2 hy⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := (continuous_subtypeVal.comp continuous_subtypeVal).subtype_mk _
  continuous_invFun := (continuous_subtypeVal.subtype_mk _).subtype_mk _

lemma coe_chartBallProjFiberHomeomorph_apply (p : E ⟶ B) (hε₀ : 0 < ε)
    (z : chartBallProj e hε p ⁻¹' {x | (x : V) = 0}) :
    (chartBallProjFiberHomeomorph e hb hε p hε₀ z : E) = z.val.val :=
  (rfl)

lemma coe_chartBallProjFiberHomeomorph_symm_apply (p : E ⟶ B) (hε₀ : 0 < ε) (y : p ⁻¹' {b}) :
    ((chartBallProjFiberHomeomorph e hb hε p hε₀).symm y).val.val = y.val :=
  (rfl)

/-- Over `chartBall e b ε`, a trivialization of `p` over a base set containing the chart ball
identifies the part of `E` with the product of the ball of radius `ε` about `0` and the fibre. -/
def chartBallTrivialization {p : E ⟶ B} {Y : Type u} [TopologicalSpace Y]
    (T : Bundle.Trivialization Y p) (hT : chartBall e b ε ⊆ T.baseSet) :
    p ⁻¹' chartBall e b ε ≃ₜ ball (0 : V) ε × Y :=
  (T.preimageHomeomorph hT).trans ((e.chartBallHomeomorph hε).prodCongr (Homeomorph.refl Y))

/-- The first coordinate of `chartBallTrivialization` is `chartBallProj`. -/
@[simp]
lemma chartBallTrivialization_apply_fst {p : E ⟶ B} {Y : Type u} [TopologicalSpace Y]
    (T : Bundle.Trivialization Y p) (hT : chartBall e b ε ⊆ T.baseSet)
    (z : p ⁻¹' chartBall e b ε) :
    (chartBallTrivialization e hε T hT z).1 = chartBallProj e hε p z :=
  Subtype.ext (by
    rw [coe_chartBallProj_apply]
    simp [chartBallTrivialization, T.preimageHomeomorph_apply])

/-- The second coordinate of `chartBallTrivialization` is the fibre coordinate of `T`. -/
@[simp]
lemma chartBallTrivialization_apply_snd {p : E ⟶ B} {Y : Type u} [TopologicalSpace Y]
    (T : Bundle.Trivialization Y p) (hT : chartBall e b ε ⊆ T.baseSet)
    (z : p ⁻¹' chartBall e b ε) :
    (chartBallTrivialization e hε T hT z).2 = (T z.val).2 := by
  simp [chartBallTrivialization]

/-- The inverse of `chartBallTrivialization` is the inverse of `T` after reading the ball
coordinate back in `B` through `OpenPartialHomeomorph.chartBallHomeomorph`. -/
@[simp]
lemma coe_chartBallTrivialization_symm_apply {p : E ⟶ B} {Y : Type u} [TopologicalSpace Y]
    (T : Bundle.Trivialization Y p) (hT : chartBall e b ε ⊆ T.baseSet)
    (x : ball (0 : V) ε × Y) :
    ((chartBallTrivialization e hε T hT).symm x : E) =
      T.toOpenPartialHomeomorph.symm (((e.chartBallHomeomorph hε).symm x.1 : B), x.2) := by
  simp [chartBallTrivialization]

end OpenPartialHomeomorph

namespace TauCeti

namespace TopCat

section Chart

variable {V : Type u} [NormedAddCommGroup V] {E B : _root_.TopCat.{u}}
  {p : E ⟶ B} {R : Type*} [Ring R] (M : ModuleCat.{u} R) (e : OpenPartialHomeomorph B V) {b : B}
  (hb : b ∈ e.source)
  {ε : ℝ} (hε : ball (e b) ε ⊆ e.target)

variable [T1Space B]

include hb in
/-- Excision onto the part of `E` over `e.chartBall b ε` is an isomorphism on homology. -/
private lemma isIso_singularHomologyMap_excisionMap_chartBall (hε₀ : 0 < ε) (m : ℕ) :
    IsIso (TopPair.singularHomologyMap
      (TopPair.excisionMap (X := E) (p ⁻¹' e.chartBall b ε) (p ⁻¹' {b})ᶜ) M m) :=
  TopPair.isIso_singularHomologyMap_excisionMap_of_isClosed_subset M
    (X := E) ((e.isOpen_chartBall b ε).preimage p.hom.continuous)
    (isClosed_singleton.preimage p.hom.continuous)
    (preimage_mono (singleton_subset_iff.2 (e.mem_chartBall_self hb hε₀))) m

/-- Excision onto the part of `E` over `e.chartBall b ε`, followed by
`OpenPartialHomeomorph.chartBallComplFiberPairIso`. -/
private def excisionIso (hε₀ : 0 < ε) (m : ℕ) :
    (TopPair.ofSubset (p ⁻¹' {b})ᶜ).singularHomology M m ≅
      (TopPair.ofSubset (e.chartBallProj hε p ⁻¹' {x | (x : V) ≠ 0})).singularHomology M m :=
  haveI := isIso_singularHomologyMap_excisionMap_chartBall (p := p) M e hb hε₀ m
  (asIso (TopPair.singularHomologyMap
      (TopPair.excisionMap (X := E) (p ⁻¹' e.chartBall b ε) (p ⁻¹' {b})ᶜ) _ m)).symm ≪≫
    TopPair.singularHomologyMapIso _ (e.chartBallComplFiberPairIso hb hε p) m

/-- The defining square of `excisionIso`: after the excision inclusion it is the map induced by
`OpenPartialHomeomorph.chartBallComplFiberPairIso`. -/
@[reassoc]
private lemma singularHomologyMap_excisionMap_comp_excisionIso_hom (hε₀ : 0 < ε) (m : ℕ) :
    TopPair.singularHomologyMap
        (TopPair.excisionMap (X := E) (p ⁻¹' e.chartBall b ε) (p ⁻¹' {b})ᶜ)
        M m ≫ (excisionIso M e hb hε hε₀ m).hom =
      TopPair.singularHomologyMap (e.chartBallComplFiberPairIso hb hε p).hom
        M m := by
  simp [excisionIso]

variable [NormedSpace ℝ V] [FiniteDimensional ℝ V]

include e hb in
/-- **The homology of a Serre fibration modulo the complement of a fibre vanishes below the
dimension.** Let `p : E ⟶ B` be a Serre fibration over a `T₁` space, and let `b` lie in the source
of an open partial homeomorphism `e : B → V` to a finite-dimensional real normed space. Then
`Hₘ(E, E ∖ p⁻¹(b); M) = 0` for every `m < dim V`. -/
theorem isZero_singularHomology_complFiber (hp : serreFibrations p) {m : ℕ}
    (hm : m < finrank ℝ V) :
    IsZero ((TopPair.ofSubset (p ⁻¹' {b})ᶜ).singularHomology M m) := by
  obtain ⟨ε, hε₀, hε⟩ := Metric.isOpen_iff.1 e.open_target (e b) (e.map_source hb)
  exact (isZero_singularHomology_preimage_ne_zero M (e.mem_serreFibrations_chartBallProj hε hp)
    (convex_ball 0 _) (ball_mem_nhds 0 hε₀) hm).of_iso (excisionIso M e hb hε hε₀ m)

/-- **The homology of a Serre fibration modulo the complement of a fibre is the shifted homology
of the fibre.** Let `p : E ⟶ B` be a Serre fibration over a `T₁` space, and let `b` lie in the
source of an open partial homeomorphism `e : B → V` to a real normed space of finite dimension `r`,
such as the chart `chartAt V b` of a topological manifold modelled on `V`. Then
`Hₘ(E, E ∖ p⁻¹(b); M) ≅ Hₙ(p⁻¹(b); M)` for `m = n + r`.

The isomorphism depends on `e`, and is constructed from a ball of radius `ε` about `e b` inside
the target of `e`: it is excision onto the part of `E` over
`OpenPartialHomeomorph.chartBall e b ε`, followed by
`TauCeti.TopCat.singularHomologyPreimageNeZeroIso` for the restriction of `p` over that set
(`TauCeti.TopCat.singularHomologyMap_excisionMap_comp_singularHomologyComplFiberIso_hom`). -/
def singularHomologyComplFiberIso (hε₀ : 0 < ε) (hp : serreFibrations p) (n m : ℕ)
    (h : n + finrank ℝ V = m) :
    (TopPair.ofSubset (p ⁻¹' {b})ᶜ).singularHomology M m ≅
      ((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} R) n).obj
        M).obj (_root_.TopCat.of (p ⁻¹' {b})) :=
  excisionIso M e hb hε hε₀ m ≪≫
    singularHomologyPreimageNeZeroIso M (e.mem_serreFibrations_chartBallProj hε hp)
      (convex_ball 0 _) (ball_mem_nhds 0 hε₀) n m h ≪≫
    ((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} R) n).obj M).mapIso
        (_root_.TopCat.isoOfHomeo (e.chartBallProjFiberHomeomorph hb hε p hε₀))

/-- The isomorphism `TauCeti.TopCat.singularHomologyComplFiberIso` commutes with excision
onto the part of `E` over `OpenPartialHomeomorph.chartBall e b ε`: after excision it is
`TauCeti.TopCat.singularHomologyPreimageNeZeroIso` for the restricted fibration, followed by the
identification of its fibre over `0` with the fibre over `b`. -/
@[reassoc]
lemma singularHomologyMap_excisionMap_comp_singularHomologyComplFiberIso_hom
    (hε₀ : 0 < ε) (hp : serreFibrations p) (n m : ℕ) (h : n + finrank ℝ V = m) :
    TopPair.singularHomologyMap
        (TopPair.excisionMap (X := E) (p ⁻¹' e.chartBall b ε) (p ⁻¹' {b})ᶜ)
        M m ≫
        (singularHomologyComplFiberIso M e hb hε hε₀ hp n m h).hom =
      TopPair.singularHomologyMap (e.chartBallComplFiberPairIso hb hε p).hom
          M m ≫
        (singularHomologyPreimageNeZeroIso M (e.mem_serreFibrations_chartBallProj hε hp)
          (convex_ball 0 _) (ball_mem_nhds 0 hε₀) n m h).hom ≫
        ((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} R) n).obj M).map
          (_root_.TopCat.isoOfHomeo (e.chartBallProjFiberHomeomorph hb hε p hε₀)).hom := by
  simp [singularHomologyComplFiberIso, excisionIso]

/-- The inverse of `TauCeti.TopCat.singularHomologyComplFiberIso` is the inverse of the
identification `OpenPartialHomeomorph.chartBallProjFiberHomeomorph` of the fibre over `0` of the
restricted fibration with the fibre over `b`, followed by the inverse of
`TauCeti.TopCat.singularHomologyPreimageNeZeroIso`, the inverse of
`OpenPartialHomeomorph.chartBallComplFiberPairIso` and the excision inclusion. -/
@[reassoc]
lemma singularHomologyComplFiberIso_inv
    (hε₀ : 0 < ε) (hp : serreFibrations p) (n m : ℕ) (h : n + finrank ℝ V = m) :
    (singularHomologyComplFiberIso M e hb hε hε₀ hp n m h).inv =
      ((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} R) n).obj M).map
          (_root_.TopCat.isoOfHomeo (e.chartBallProjFiberHomeomorph hb hε p hε₀)).inv ≫
        (singularHomologyPreimageNeZeroIso M (e.mem_serreFibrations_chartBallProj hε hp)
          (convex_ball 0 _) (ball_mem_nhds 0 hε₀) n m h).inv ≫
        TopPair.singularHomologyMap (e.chartBallComplFiberPairIso hb hε p).inv
          M m ≫
        TopPair.singularHomologyMap
          (TopPair.excisionMap (X := E) (p ⁻¹' e.chartBall b ε) (p ⁻¹' {b})ᶜ)
          M m := by
  simp [singularHomologyComplFiberIso, excisionIso]

/-! ### Naturality in maps of fibrations -/

section Naturality

variable {E' : _root_.TopCat.{u}} {p' : E' ⟶ B} {f : E ⟶ E'}

omit [NormedSpace ℝ V] [FiniteDimensional ℝ V] in
/-- The isomorphism `excisionIso` is natural in maps of fibrations over `B`: after excision, the
map induced by `f` is the map induced by its restriction over
`OpenPartialHomeomorph.chartBall e b ε`. -/
@[reassoc]
private lemma excisionIso_hom_naturality (hε₀ : 0 < ε) (hf : f ≫ p' = p) (m : ℕ) :
    TopPair.singularHomologyMap (TopPair.ofSubsetMap f (f.mapsTo_preimage_of_comp_eq hf {b}ᶜ))
        M m ≫ (excisionIso (p := p') M e hb hε hε₀ m).hom =
      (excisionIso (p := p) M e hb hε hε₀ m).hom ≫
        TopPair.singularHomologyMap (TopPair.ofSubsetMap (f.preimageMap hf (e.chartBall b ε))
          ((f.preimageMap hf (e.chartBall b ε)).mapsTo_preimage_of_comp_eq
            (e.preimageMap_comp_chartBallProj hε hf) _)) M m := by
  -- The map of excision data induced by `f`.
  let Q := TopPair.interPairMap f (f.mapsTo_preimage_of_comp_eq hf (e.chartBall b ε))
    (f.mapsTo_preimage_of_comp_eq hf {b}ᶜ)
  have hQ : TopPair.excisionMap (X := E) (p ⁻¹' e.chartBall b ε) (p ⁻¹' {b})ᶜ ≫
        TopPair.ofSubsetMap f (f.mapsTo_preimage_of_comp_eq hf {b}ᶜ) =
      Q ≫ TopPair.excisionMap (X := E') (p' ⁻¹' e.chartBall b ε) (p' ⁻¹' {b})ᶜ :=
    (TopPair.interPairMap_comp_excisionMap f _ _).symm
  have hQ' : (e.chartBallComplFiberPairIso hb hε p).hom ≫
        TopPair.ofSubsetMap (f.preimageMap hf (e.chartBall b ε))
          ((f.preimageMap hf (e.chartBall b ε)).mapsTo_preimage_of_comp_eq
            (e.preimageMap_comp_chartBallProj hε hf) _) =
      Q ≫ (e.chartBallComplFiberPairIso hb hε p').hom :=
    TopPair.hom_ext_of_fst _ (by
      ext x
      apply Subtype.ext
      rw [OpenPartialHomeomorph.chartBallComplFiberPairIso_hom,
        OpenPartialHomeomorph.chartBallComplFiberPairIso_hom, TopPair.Hom.fst_comp,
        TopPair.Hom.fst_comp]
      -- The ambient spaces of the pairs are `TopCat.of` of subtypes, which `rw` does not unfold.
      erw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply, TopPair.ofSubsetMap_fst_apply,
        TopPair.ofSubsetMap_fst_apply, TopPair.ofSubsetMap_fst_apply]
      exact (TopCat.Hom.coe_preimageMap_apply f hf _ x).trans
        (TopPair.interPairMap_fst_apply _ _ _ x).symm)
  have := isIso_singularHomologyMap_excisionMap_chartBall (p := p) M e hb hε₀ m
  rw [← cancel_epi (TopPair.singularHomologyMap
      (TopPair.excisionMap (X := E) (p ⁻¹' e.chartBall b ε) (p ⁻¹' {b})ᶜ) M m),
    singularHomologyMap_excisionMap_comp_excisionIso_hom_assoc,
    ← TopPair.singularHomologyMap_comp_assoc, hQ, TopPair.singularHomologyMap_comp_assoc,
    singularHomologyMap_excisionMap_comp_excisionIso_hom, ← TopPair.singularHomologyMap_comp,
    ← TopPair.singularHomologyMap_comp, hQ']

omit [T1Space B] [NormedSpace ℝ V] [FiniteDimensional ℝ V] in
/-- The identifications `OpenPartialHomeomorph.chartBallProjFiberHomeomorph` of the fibres over `0`
with the fibres over `b` carry the restriction of `f` over `OpenPartialHomeomorph.chartBall e b ε`
to the restriction of `f` to the fibres over `b`. -/
private lemma chartBallProjFiberHomeomorph_naturality (hε₀ : 0 < ε) (hf : f ≫ p' = p) :
    (_root_.TopCat.isoOfHomeo (e.chartBallProjFiberHomeomorph hb hε p hε₀)).hom ≫
        f.preimageMap hf {b} =
      (f.preimageMap hf (e.chartBall b ε)).preimageMap (e.preimageMap_comp_chartBallProj hε hf)
          {x | (x : V) = 0} ≫
        (_root_.TopCat.isoOfHomeo (e.chartBallProjFiberHomeomorph hb hε p' hε₀)).hom := by
  ext x
  rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply, TopCat.Hom.coe_preimageMap_apply]
  -- The homeomorphism is applied through `TopCat.isoOfHomeo`, which `rw` does not see through.
  erw [OpenPartialHomeomorph.coe_chartBallProjFiberHomeomorph_apply]
  exact ((congrArg Subtype.val (TopCat.Hom.coe_preimageMap_apply _ _ _ x)).trans
    (TopCat.Hom.coe_preimageMap_apply _ _ _ x.val)).symm

/-- **The homology of a Serre fibration modulo the complement of a fibre is natural in maps of
fibrations.** Let `p : E ⟶ B` and `p' : E' ⟶ B` be Serre fibrations over a `T₁` space, `e` a chart
of dimension `r` at `b`, and `f : E ⟶ E'` a map over `B`. Under the isomorphisms
`Hₙ₊ᵣ(E, E ∖ p⁻¹(b); R) ≅ Hₙ(p⁻¹(b); R)` of `TauCeti.TopCat.singularHomologyComplFiberIso`, built
from the same ball about `e b`, the map induced by `f` on relative homology is the map induced by
the restriction `p⁻¹(b) ⟶ p'⁻¹(b)` of `f` on the homology of the fibres. -/
@[reassoc]
theorem singularHomologyComplFiberIso_hom_naturality (hε₀ : 0 < ε) (hp : serreFibrations p)
    (hp' : serreFibrations p') (hf : f ≫ p' = p) (n m : ℕ) (h : n + finrank ℝ V = m) :
    TopPair.singularHomologyMap (TopPair.ofSubsetMap f (f.mapsTo_preimage_of_comp_eq hf {b}ᶜ))
        M m ≫ (singularHomologyComplFiberIso M e hb hε hε₀ hp' n m h).hom =
      (singularHomologyComplFiberIso M e hb hε hε₀ hp n m h).hom ≫
        ((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} R) n).obj
          M).map (f.preimageMap hf {b}) := by
  simp only [singularHomologyComplFiberIso, Iso.trans_hom, Functor.mapIso_hom, Category.assoc]
  rw [excisionIso_hom_naturality_assoc M e hb hε hε₀ hf m,
    singularHomologyPreimageNeZeroIso_hom_naturality_assoc M
      (e.mem_serreFibrations_chartBallProj hε hp) (e.mem_serreFibrations_chartBallProj hε hp')
      (convex_ball 0 _) (ball_mem_nhds 0 hε₀) (e.preimageMap_comp_chartBallProj hε hf)
      ((f.preimageMap hf (e.chartBall b ε)).preimageMap (e.preimageMap_comp_chartBallProj hε hf)
        {x | (x : V) = 0}) (fun x ↦ TopCat.Hom.coe_preimageMap_apply _ _ _ x) n m h,
    ← Functor.map_comp, ← Functor.map_comp, chartBallProjFiberHomeomorph_naturality]

end Naturality

end Chart

section PathConnected

variable {V : Type u} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  {E B : _root_.TopCat.{u}} [T1Space B] {p : E ⟶ B} (R : Type u) [Ring R]
  (e : OpenPartialHomeomorph B V) {b : B} (hb : b ∈ e.source) {ε : ℝ}
  (hε : ball (e b) ε ⊆ e.target)

/-- **The local homology along a path-connected fibre.** For a Serre fibration over a `T₁` space
whose fibre over `b` is path connected, with a chart of dimension `r` at `b`, the local homology
`Hᵣ(E, E ∖ p⁻¹(b); R)` along the fibre is the coefficient ring `R`: it is the zeroth homology
of the fibre (`TauCeti.TopCat.singularHomologyComplFiberIso`), followed by the augmentation. -/
def singularHomologyComplFiberIsoOfPathConnectedSpace [PathConnectedSpace (p ⁻¹' {b})]
    (hε₀ : 0 < ε) (hp : serreFibrations p) :
    (TopPair.ofSubset (p ⁻¹' {b})ᶜ).singularHomology (ModuleCat.of R R) (finrank ℝ V) ≅
      ModuleCat.of R R :=
  singularHomologyComplFiberIso (ModuleCat.of R R) e hb hε hε₀ hp 0 _ (zero_add _) ≪≫
    asIso ((_root_.TopCat.of (p ⁻¹' {b})).singularHomology₀ε (ModuleCat.of R R))

/-- `TauCeti.TopCat.singularHomologyComplFiberIsoOfPathConnectedSpace` is
`TauCeti.TopCat.singularHomologyComplFiberIso` onto the zeroth homology of the fibre, followed by
the augmentation. -/
@[reassoc]
lemma singularHomologyComplFiberIsoOfPathConnectedSpace_hom [PathConnectedSpace (p ⁻¹' {b})]
    (hε₀ : 0 < ε) (hp : serreFibrations p) :
    (singularHomologyComplFiberIsoOfPathConnectedSpace R e hb hε hε₀ hp).hom =
      (singularHomologyComplFiberIso (ModuleCat.of R R) e hb hε hε₀ hp 0 _ (zero_add _)).hom ≫
        (_root_.TopCat.of (p ⁻¹' {b})).singularHomology₀ε (ModuleCat.of R R) := by
  simp [singularHomologyComplFiberIsoOfPathConnectedSpace]

end PathConnected

end TopCat

/-! ### Classes living over the fundamental class -/

variable {V : Type u} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  {E B : _root_.TopCat.{u}} [T1Space B] {p : E ⟶ B} {R : Type*} [Ring R] {M : ModuleCat.{u} R}
  (e : OpenPartialHomeomorph B V) {b : B} (hb : b ∈ e.source)

/-- **Living over the fundamental class through the shriek map.** For a Serre fibration over a
`T₁` space with a chart `e` of dimension `r` at `b`, a class `α ∈ Hₙ₊ᵣ(E; M)` lives over the
fundamental class at `b` exactly when its image under the shriek map
`Hₙ₊ᵣ(E) → Hₙ₊ᵣ(E, E ∖ p⁻¹(b)) ≅ Hₙ(p⁻¹(b))` of the inclusion of `b` is nonzero, for any ball about
`e b` inside the target of `e`. -/
theorem livesOverFundamentalClass_iff_singularHomologyComplFiberIso_hom_ne_zero
    {ε : ℝ} (hε : ball (e b) ε ⊆ e.target) (hε₀ : 0 < ε) (hp : TopCat.serreFibrations p)
    {n m : ℕ} (h : n + finrank ℝ V = m)
    (α : ((_root_.TopCat.toSSet.obj E).homology M m : ModuleCat.{u} R)) :
    LivesOverFundamentalClass M p b α ↔
      (TopCat.singularHomologyComplFiberIso M e hb hε hε₀ hp n m h).hom.hom
        ((fiberLocalization M p b m).hom α) ≠ 0 := by
  rw [livesOverFundamentalClass_iff, not_iff_not]
  exact ⟨fun hα ↦ by rw [hα, map_zero], fun hα ↦ by
    simpa using congrArg (TopCat.singularHomologyComplFiberIso M e hb hε hε₀ hp n m h).inv.hom hα⟩

include hb in
/-- **A class living over the fundamental class has degree at least the dimension of the base.**
For a Serre fibration over a `T₁` space with a chart of dimension `r` at `b`, the local homology
`Hₖ(E, E ∖ p⁻¹(b))` vanishes for `k < r`, so no class of degree below `r` lives over the
fundamental class at `b`. -/
theorem LivesOverFundamentalClass.finrank_le (hp : TopCat.serreFibrations p) {d : ℕ}
    {α : ((_root_.TopCat.toSSet.obj E).homology M d : ModuleCat.{u} R)}
    (h : LivesOverFundamentalClass M p b α) : finrank ℝ V ≤ d := by
  by_contra hd
  have := ModuleCat.isZero_iff_subsingleton.1 (TopCat.isZero_singularHomology_complFiber M e hb hp
    (not_le.1 hd))
  exact (livesOverFundamentalClass_iff _ _ _ _).1 h (Subsingleton.elim _ _)

/-! ### Naturality of the shriek map -/

section ShriekNaturality

variable {ε : ℝ} (hε : ball (e b) ε ⊆ e.target) (hε₀ : 0 < ε) {E' : _root_.TopCat.{u}}
  {p' : E' ⟶ B} (hp : TopCat.serreFibrations p) (hp' : TopCat.serreFibrations p')
  {f : E ⟶ E'} (hf : f ≫ p' = p) {n m : ℕ} (h : n + finrank ℝ V = m)

/-- **Naturality of the shriek map of a point** (Barraud–Damian–Humilière–Oancea,
Proposition 2.12). Let `p : E ⟶ B` and `p' : E' ⟶ B` be Serre fibrations over a `T₁` space, with a
chart `e` of dimension `r` at `b`, and let `f : E ⟶ E'` be a map over `B`. The shriek map
`j_! : Hₙ₊ᵣ(E) → Hₙ(p⁻¹(b))` of the inclusion of `b` is the localization at the fibre followed by
`TauCeti.TopCat.singularHomologyComplFiberIso`. It commutes with `f`: `j_! ∘ f_* = f_* ∘ j_!`, where
on the right `f` acts through its restriction `p⁻¹(b) ⟶ p'⁻¹(b)` to the fibres. -/
@[reassoc]
theorem homologyMap_comp_fiberLocalization_comp_singularHomologyComplFiberIso_hom :
    SSet.homologyMap (_root_.TopCat.toSSet.map f) M m ≫
        fiberLocalization M p' b m ≫
          (TopCat.singularHomologyComplFiberIso M e hb hε hε₀ hp' n m h).hom =
      fiberLocalization M p b m ≫
        (TopCat.singularHomologyComplFiberIso M e hb hε hε₀ hp n m h).hom ≫
          ((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} R) n).obj
            M).map (f.preimageMap hf {b}) := by
  have hloc : SSet.homologyMap (_root_.TopCat.toSSet.map f) M m ≫
        fiberLocalization M p' b m =
      fiberLocalization M p b m ≫
        TopPair.singularHomologyMap (TopPair.ofSubsetMap f (f.mapsTo_preimage_of_comp_eq hf {b}ᶜ))
          M m := by
    have hσ := homologyMap_comp_fiberLocalization M f.hom
      (congrArg (fun g : E ⟶ B ↦ ⇑g.hom) hf) b m
    -- `hσ` is stated for `TopCat.ofHom f.hom` on `TopCat.of E`, which `exact` identifies with `f`.
    rw [localHomologyMap_def] at hσ
    exact hσ
  rw [reassoc_of% hloc, TopCat.singularHomologyComplFiberIso_hom_naturality M e hb hε hε₀ hp hp' hf]

include hp' in
/-- **Living over the fundamental class under maps of fibrations.** Let `p : E ⟶ B` and
`p' : E' ⟶ B` be Serre fibrations over a `T₁` space, with a chart `e` of dimension `r` at `b`, and
let `f : E ⟶ E'` be a map over `B`. A class `f_* α`, for `α ∈ Hₙ₊ᵣ(E; R)`, lives over the
fundamental class at `b` exactly when the restriction `p⁻¹(b) ⟶ p'⁻¹(b)` of `f` sends the shriek
image `j_! α ∈ Hₙ(p⁻¹(b); R)` to a nonzero class. This is the argument of
Barraud–Damian–Humilière–Oancea, Corollary 2.13, in which `j_! α` is the fundamental class of the
fibre of a fibre bundle of closed oriented manifolds. -/
theorem livesOverFundamentalClass_homologyMap_iff
    (α : ((_root_.TopCat.toSSet.obj E).homology M m : ModuleCat.{u} R)) :
    LivesOverFundamentalClass M p' b
        ((SSet.homologyMap (_root_.TopCat.toSSet.map f) M m).hom α) ↔
      (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} R) n).obj
          M).map (f.preimageMap hf {b})).hom
        ((TopCat.singularHomologyComplFiberIso M e hb hε hε₀ hp n m h).hom.hom
          ((fiberLocalization M p b m).hom α)) ≠ 0 := by
  have h' := congrArg (fun φ ↦ φ.hom α)
    (homologyMap_comp_fiberLocalization_comp_singularHomologyComplFiberIso_hom e hb hε hε₀ hp hp'
      hf h)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h'
  rw [livesOverFundamentalClass_iff_singularHomologyComplFiberIso_hom_ne_zero e hb hε hε₀ hp' h, h']

end ShriekNaturality

end TauCeti
