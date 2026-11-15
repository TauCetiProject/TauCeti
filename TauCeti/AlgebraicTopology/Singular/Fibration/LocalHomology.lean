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
# Local homology of a Serre fibration along a fibre

Let `p : E → B` be a Serre fibration over a `T₁` space `B` and `b` a point of `B` in the source
of an open partial homeomorphism `e : B → V` to a real normed space of finite dimension `r`, such
as a chart of a topological manifold modelled on `V`. The **local homology of `E` along the
fibre** `F = p⁻¹(b)` is the relative singular homology `Hₖ(E, E ∖ F)`. This file computes it,
with coefficients in a ring `R`:

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
  toFun z := ⟨z.1.1, (coe_chartBallProj_eq_zero_iff e hb hε z.1).1 z.2⟩
  invFun y :=
    have hy : p y.1 = b := mem_singleton_iff.1 y.2
    ⟨⟨y.1, by
      rw [mem_preimage, hy]
      exact mem_chartBall_self e hb hε₀⟩, (coe_chartBallProj_eq_zero_iff e hb hε _).2 hy⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
  continuous_invFun := (continuous_subtype_val.subtype_mk _).subtype_mk _

lemma coe_chartBallProjFiberHomeomorph_apply (p : E ⟶ B) (hε₀ : 0 < ε)
    (z : chartBallProj e hε p ⁻¹' {x | (x : V) = 0}) :
    (chartBallProjFiberHomeomorph e hb hε p hε₀ z : E) = z.1.1 :=
  (rfl)

lemma coe_chartBallProjFiberHomeomorph_symm_apply (p : E ⟶ B) (hε₀ : 0 < ε) (y : p ⁻¹' {b}) :
    ((chartBallProjFiberHomeomorph e hb hε p hε₀).symm y).1.1 = y.1 :=
  (rfl)

end OpenPartialHomeomorph

namespace TauCeti

namespace TopCat

section Chart

variable {V : Type u} [NormedAddCommGroup V] {E B : _root_.TopCat.{u}}
  {p : E ⟶ B} (R : Type u) [Ring R] (e : OpenPartialHomeomorph B V) {b : B} (hb : b ∈ e.source)
  {ε : ℝ} (hε : ball (e b) ε ⊆ e.target)

variable [T1Space B]

/-- Excision onto the part of `E` over `e.chartBall b ε`, followed by
`OpenPartialHomeomorph.chartBallComplFiberPairIso`. -/
private def excisionIso (hε₀ : 0 < ε) (m : ℕ) :
    (TopPair.ofSubset (p ⁻¹' {b})ᶜ).singularHomology (ModuleCat.of R R) m ≅
      (TopPair.ofSubset (e.chartBallProj hε p ⁻¹' {x | (x : V) ≠ 0})).singularHomology
        (ModuleCat.of R R) m :=
  haveI := TopPair.isIso_singularHomologyMap_excisionMap_of_isClosed_subset (ModuleCat.of R R)
    (X := E) ((e.isOpen_chartBall b ε).preimage p.hom.continuous)
    (isClosed_singleton.preimage p.hom.continuous)
    (preimage_mono (singleton_subset_iff.2 (e.mem_chartBall_self hb hε₀))) m
  (asIso (TopPair.singularHomologyMap
      (TopPair.excisionMap (X := E) (p ⁻¹' e.chartBall b ε) (p ⁻¹' {b})ᶜ) _ m)).symm ≪≫
    TopPair.singularHomologyMapIso _ (e.chartBallComplFiberPairIso hb hε p) m

variable [NormedSpace ℝ V] [FiniteDimensional ℝ V]

include e hb in
/-- **The homology of a Serre fibration modulo the complement of a fibre vanishes below the
dimension.** Let `p : E ⟶ B` be a Serre fibration over a `T₁` space, and let `b` lie in the source
of an open partial homeomorphism `e : B → V` to a finite-dimensional real normed space. Then
`Hₘ(E, E ∖ p⁻¹(b); R) = 0` for every `m < dim V`. -/
theorem isZero_singularHomology_complFiber (hp : serreFibrations p) {m : ℕ}
    (hm : m < finrank ℝ V) :
    IsZero ((TopPair.ofSubset (p ⁻¹' {b})ᶜ).singularHomology (ModuleCat.of R R) m) := by
  obtain ⟨ε, hε₀, hε⟩ := Metric.isOpen_iff.1 e.open_target (e b) (e.map_source hb)
  exact (isZero_singularHomology_preimage_ne_zero R (e.mem_serreFibrations_chartBallProj hε hp)
    (convex_ball 0 _) (ball_mem_nhds 0 hε₀) hm).of_iso (excisionIso R e hb hε hε₀ m)

/-- **The homology of a Serre fibration modulo the complement of a fibre is the shifted homology
of the fibre.** Let `p : E ⟶ B` be a Serre fibration over a `T₁` space, and let `b` lie in the
source of an open partial homeomorphism `e : B → V` to a real normed space of finite dimension `r`,
such as the chart `chartAt V b` of a topological manifold modelled on `V`. Then
`Hₘ(E, E ∖ p⁻¹(b); R) ≅ Hₙ(p⁻¹(b); R)` for `m = n + r`.

The isomorphism depends on `e`, and is constructed from a ball of radius `ε` about `e b` inside
the target of `e`: it is excision onto the part of `E` over
`OpenPartialHomeomorph.chartBall e b ε`, followed by
`TauCeti.TopCat.singularHomologyPreimageNeZeroIso` for the restriction of `p` over that set
(`TauCeti.TopCat.singularHomologyMap_excisionMap_comp_singularHomologyComplFiberIso_hom`). -/
def singularHomologyComplFiberIso (hε₀ : 0 < ε) (hp : serreFibrations p) (n m : ℕ)
    (h : n + finrank ℝ V = m) :
    (TopPair.ofSubset (p ⁻¹' {b})ᶜ).singularHomology (ModuleCat.of R R) m ≅
      ((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} R) n).obj
        (ModuleCat.of R R)).obj (_root_.TopCat.of (p ⁻¹' {b})) :=
  excisionIso R e hb hε hε₀ m ≪≫
    singularHomologyPreimageNeZeroIso R (e.mem_serreFibrations_chartBallProj hε hp)
      (convex_ball 0 _) (ball_mem_nhds 0 hε₀) n m h ≪≫
    ((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} R) n).obj
      (ModuleCat.of R R)).mapIso
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
        (ModuleCat.of R R) m ≫
        (singularHomologyComplFiberIso R e hb hε hε₀ hp n m h).hom =
      TopPair.singularHomologyMap (e.chartBallComplFiberPairIso hb hε p).hom
          (ModuleCat.of R R) m ≫
        (singularHomologyPreimageNeZeroIso R (e.mem_serreFibrations_chartBallProj hε hp)
          (convex_ball 0 _) (ball_mem_nhds 0 hε₀) n m h).hom ≫
        ((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} R) n).obj
          (ModuleCat.of R R)).map
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
    (singularHomologyComplFiberIso R e hb hε hε₀ hp n m h).inv =
      ((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} R) n).obj
          (ModuleCat.of R R)).map
          (_root_.TopCat.isoOfHomeo (e.chartBallProjFiberHomeomorph hb hε p hε₀)).inv ≫
        (singularHomologyPreimageNeZeroIso R (e.mem_serreFibrations_chartBallProj hε hp)
          (convex_ball 0 _) (ball_mem_nhds 0 hε₀) n m h).inv ≫
        TopPair.singularHomologyMap (e.chartBallComplFiberPairIso hb hε p).inv
          (ModuleCat.of R R) m ≫
        TopPair.singularHomologyMap
          (TopPair.excisionMap (X := E) (p ⁻¹' e.chartBall b ε) (p ⁻¹' {b})ᶜ)
          (ModuleCat.of R R) m := by
  simp [singularHomologyComplFiberIso, excisionIso]

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
