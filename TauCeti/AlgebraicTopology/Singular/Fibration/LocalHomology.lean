/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.Fibration.Disk
public import TauCeti.AlgebraicTopology.Singular.Excision
public import TauCeti.AlgebraicTopology.Singular.LocalHomology.LivesOver

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
not depend on the chart: the identification `Hₙ₊ᵣ(E, E ∖ F) ≅ Hₙ(F)` does.

## The computation

Translate `e` so that `e b = 0` and choose a ball `K` about `0` inside its target. Over the open
set `U = e⁻¹(K)`, excision onto the open set `p⁻¹(U)`, which contains the closed fibre `F`,
identifies `Hₖ(E, E ∖ F)` with `Hₖ(p⁻¹(U), p⁻¹(U) ∖ F)`
(`TopPair.isIso_singularHomologyMap_excisionMap_of_isClosed_subset`). The restriction of `p` over
`U`, followed by the homeomorphism `U ≃ K` given by `e`, is a Serre fibration over the convex
neighbourhood `K` of `0` whose fibre over `0` is `F`, and the part of `p⁻¹(U)` over `K ∖ {0}` is
`p⁻¹(U) ∖ F`. The homology of a Serre fibration over a convex neighbourhood of `0` modulo the part
over the punctured base is the shifted homology of the fibre
(`TauCeti.TopCat.singularHomologyPreimageNeZeroIso`), and vanishes below the dimension
(`TauCeti.TopCat.isZero_singularHomology_preimage_ne_zero`).

## Main definitions and results

* `TauCeti.TopCat.singularHomologyComplFiberIso`: `Hₙ₊ᵣ(E, E ∖ p⁻¹(b)) ≅ Hₙ(p⁻¹(b))`.
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

namespace TauCeti

namespace TopCat

section Chart

variable {V : Type u} [NormedAddCommGroup V]
  {E B : _root_.TopCat.{u}} (R : Type u) [Ring R]
  (e : OpenPartialHomeomorph B V) {b : B} (hb : b ∈ e.source)

namespace LocalFiber

variable (b) in
/-- The open partial homeomorphism `e` translated so that it sends `b` to `0`. -/
private def chart : OpenPartialHomeomorph B V :=
  e.trans (Homeomorph.addRight (-e b)).toOpenPartialHomeomorph

include hb in
private lemma mem_chart_source : b ∈ (chart e b).source := by
  simpa [chart] using hb

private lemma chart_apply (x : B) : chart e b x = e x - e b := by
  simp [chart, sub_eq_add_neg]

include hb in
private lemma zero_mem_chart_target : (0 : V) ∈ (chart e b).target := by
  simpa [chart_apply] using (chart e b).map_source (mem_chart_source e hb)

include hb in
private lemma exists_ball_subset :
    ∃ r > 0, ball (0 : V) r ⊆ (chart e b).target :=
  Metric.isOpen_iff.1 (chart e b).open_target 0 (zero_mem_chart_target e hb)

/-- A radius of a ball about `0` inside the target of the translated chart. -/
private def radius : ℝ :=
  (exists_ball_subset e hb).choose

private lemma radius_pos : 0 < radius e hb :=
  (exists_ball_subset e hb).choose_spec.1

private lemma ball_subset : ball (0 : V) (radius e hb) ⊆ (chart e b).target :=
  (exists_ball_subset e hb).choose_spec.2

/-- The ball of radius `radius e hb` about `0`, the base of the local fibration. -/
private abbrev base : Set V :=
  ball (0 : V) (radius e hb)

/-- The open neighbourhood `U` of `b` over which the fibration is restricted. -/
private abbrev nbhd : Set B :=
  (chart e b).source ∩ chart e b ⁻¹' base e hb

private lemma image_nbhd : chart e b '' nbhd e hb = base e hb := by
  refine Subset.antisymm (image_subset_iff.2 fun x hx ↦ hx.2) fun y hy ↦ ?_
  have hy' := ball_subset e hb hy
  exact ⟨(chart e b).symm y, ⟨(chart e b).map_target hy', by
    simpa [(chart e b).right_inv hy'] using hy⟩, (chart e b).right_inv hy'⟩

/-- The homeomorphism `U ≃ K` of the neighbourhood of `b` with the ball about `0`. -/
private def nbhdHomeomorph : nbhd e hb ≃ₜ base e hb :=
  (chart e b).homeomorphOfImageSubsetSource inter_subset_left (image_nbhd e hb)

private lemma isOpen_nbhd : IsOpen (nbhd e hb) :=
  (chart e b).isOpen_inter_preimage isOpen_ball

private lemma mem_nbhd : b ∈ nbhd e hb :=
  ⟨mem_chart_source e hb, by simpa [chart_apply] using radius_pos e hb⟩

/-- For `x ∈ U`, the translated chart vanishes at `x` exactly when `x = b`. -/
private lemma chart_eq_zero_iff {x : B} (hx : x ∈ nbhd e hb) : chart e b x = 0 ↔ x = b := by
  refine ⟨fun h ↦ (chart e b).injOn hx.1 (mem_chart_source e hb) ?_, fun h ↦ ?_⟩
  · rw [h, chart_apply, sub_self]
  · rw [h, chart_apply, sub_self]

/-- The restriction of `p` over `U`, followed by `U ≃ K`: a fibration over the ball `K`. -/
private def proj (p : E ⟶ B) :
    _root_.TopCat.of (p ⁻¹' nbhd e hb) ⟶ _root_.TopCat.of (base e hb) :=
  _root_.TopCat.ofHom (p.hom.restrictPreimage (nbhd e hb)) ≫
    (_root_.TopCat.isoOfHomeo (nbhdHomeomorph e hb)).hom

private lemma serreFibrations_proj {p : E ⟶ B} (hp : serreFibrations p) :
    serreFibrations (proj e hb p) :=
  (serreFibrations.cancel_right_of_respectsIso _ _).2
    (mem_serreFibrations_restrictPreimage hp (nbhd e hb))

/-- A point of `p⁻¹(U)` lies outside the fibre exactly when it lies over `K ∖ {0}`. -/
private lemma mem_compl_fiber_iff {p : E ⟶ B} (x : p ⁻¹' nbhd e hb) :
    (x : E) ∈ (p ⁻¹' {b})ᶜ ↔ x ∈ proj e hb p ⁻¹' {y : base e hb | (y : V) ≠ 0} := by
  simp only [mem_compl_iff, mem_preimage, mem_singleton_iff]
  exact (chart_eq_zero_iff e hb x.2).not.symm

/-- The excised pair `(p⁻¹(U), p⁻¹(U) ∖ F)` is the pair of the fibration over `K` modulo the part
over `K ∖ {0}`. -/
private def pairIso (p : E ⟶ B) :
    TopPair.interPair (p ⁻¹' nbhd e hb) ((p ⁻¹' {b})ᶜ) ≅
      TopPair.ofSubset (proj e hb p ⁻¹' {y : base e hb | (y : V) ≠ 0}) :=
  TopPair.ofSubsetIso (Homeomorph.refl _) (mem_compl_fiber_iff e hb)

private lemma mem_nbhd_of_mem_fiber {p : E ⟶ B} {x : E} (hx : x ∈ p ⁻¹' {b}) :
    x ∈ p ⁻¹' nbhd e hb := by
  rw [mem_preimage, mem_singleton_iff] at hx
  rw [mem_preimage, hx]
  exact mem_nbhd e hb

/-- The fibre over `0` of the fibration over `K` is the fibre `F = p⁻¹(b)`. -/
private def fiberHomeomorph (p : E ⟶ B) :
    (proj e hb p ⁻¹' {y : base e hb | (y : V) = 0}) ≃ₜ (p ⁻¹' {b}) where
  toFun x := ⟨x.1.1, (chart_eq_zero_iff e hb x.1.2).1 x.2⟩
  invFun y := ⟨⟨y.1, mem_nbhd_of_mem_fiber e hb y.2⟩,
    (chart_eq_zero_iff e hb (mem_nbhd_of_mem_fiber e hb y.2)).2 y.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
  continuous_invFun := (continuous_subtype_val.subtype_mk _).subtype_mk _

variable [T1Space B]

include hb in
private lemma isIso_excision (p : E ⟶ B) (m : ℕ) :
    IsIso (TopPair.singularHomologyMap (TopPair.excisionMap (p ⁻¹' nbhd e hb) ((p ⁻¹' {b})ᶜ))
      (ModuleCat.of R R) m) :=
  TopPair.isIso_singularHomologyMap_excisionMap_of_isClosed_subset (ModuleCat.of R R)
    ((isOpen_nbhd e hb).preimage p.hom.continuous)
    ((isClosed_singleton (x := b)).preimage p.hom.continuous)
    (fun _ ↦ mem_nbhd_of_mem_fiber e hb) m

/-- `Hₘ(E, E ∖ F) ≅ Hₘ(p⁻¹(U), p⁻¹(U) ∖ F)`, the excision isomorphism followed by the
identification of the excised pair with the pair of the fibration over `K`. -/
private def excisionIso (p : E ⟶ B) (m : ℕ) :
    (TopPair.ofSubset ((p ⁻¹' {b})ᶜ : Set E)).singularHomology (ModuleCat.of R R) m ≅
      (TopPair.ofSubset (proj e hb p ⁻¹' {y : base e hb | (y : V) ≠ 0})).singularHomology
        (ModuleCat.of R R) m :=
  haveI := isIso_excision R e hb p m
  (asIso (TopPair.singularHomologyMap (TopPair.excisionMap (p ⁻¹' nbhd e hb) ((p ⁻¹' {b})ᶜ))
    (ModuleCat.of R R) m)).symm ≪≫
    asIso (TopPair.singularHomologyMap (pairIso e hb p).hom (ModuleCat.of R R) m)

end LocalFiber

open LocalFiber

variable [NormedSpace ℝ V] [FiniteDimensional ℝ V] [T1Space B] {p : E ⟶ B}

include hb in
/-- **The local homology of a Serre fibration along a fibre vanishes below the dimension.** Let
`p : E ⟶ B` be a Serre fibration over a `T₁` space and let `b` lie in the source of an open partial
homeomorphism `e : B → V` to a finite-dimensional real normed space. Then
`Hₘ(E, E ∖ p⁻¹(b); R) = 0` for every `m < dim V`. -/
theorem isZero_singularHomology_complFiber (hp : serreFibrations p) {m : ℕ}
    (hm : m < finrank ℝ V) :
    IsZero ((TopPair.ofSubset ((p ⁻¹' {b})ᶜ : Set E)).singularHomology (ModuleCat.of R R) m) :=
  (isZero_singularHomology_preimage_ne_zero R (serreFibrations_proj e hb hp) (convex_ball _ _)
    (ball_mem_nhds _ (radius_pos e hb)) hm).of_iso (excisionIso R e hb p m)

/-- **The local homology of a Serre fibration along a fibre is the shifted homology of the
fibre.** Let `p : E ⟶ B` be a Serre fibration over a `T₁` space and let `b` lie in the source of
an open partial homeomorphism `e : B → V` to a real normed space of finite dimension `r`, such as a
chart of a topological manifold. Then `Hₘ(E, E ∖ p⁻¹(b); R) ≅ Hₙ(p⁻¹(b); R)` for `m = n + r`.

The isomorphism is excision onto the part of `E` over a ball of the chart about `b`, followed by
`TauCeti.TopCat.singularHomologyPreimageNeZeroIso` for the restricted fibration. It depends on `e`.
Preceded by `Hₙ₊ᵣ(E) → Hₙ₊ᵣ(E, E ∖ p⁻¹(b))`, it gives a shriek map `Hₙ₊ᵣ(E) → Hₙ(p⁻¹(b))` of the
inclusion of the point `b`. -/
def singularHomologyComplFiberIso (hp : serreFibrations p) (n m : ℕ)
    (h : n + finrank ℝ V = m) :
    (TopPair.ofSubset ((p ⁻¹' {b})ᶜ : Set E)).singularHomology (ModuleCat.of R R) m ≅
      ((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} R) n).obj
        (ModuleCat.of R R)).obj (_root_.TopCat.of (p ⁻¹' {b})) :=
  excisionIso R e hb p m ≪≫
    singularHomologyPreimageNeZeroIso R (serreFibrations_proj e hb hp) (convex_ball _ _)
      (ball_mem_nhds _ (radius_pos e hb)) n m h ≪≫
    ((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} R) n).obj
      (ModuleCat.of R R)).mapIso (_root_.TopCat.isoOfHomeo (fiberHomeomorph e hb p))

end Chart

end TopCat

/-! ### Classes living over the fundamental class -/

variable {V : Type u} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  {E B : _root_.TopCat.{u}} [T1Space B] {p : E ⟶ B} {R : Type u} [Ring R]
  (e : OpenPartialHomeomorph B V) {b : B} (hb : b ∈ e.source)

/-- **Living over the fundamental class through the shriek map.** For a Serre fibration over a
`T₁` space with a chart `e` of dimension `r` at `b`, a class `α ∈ Hₙ₊ᵣ(E; R)` lives over the
fundamental class at `b` exactly when its image under the shriek map
`Hₙ₊ᵣ(E) → Hₙ₊ᵣ(E, E ∖ p⁻¹(b)) ≅ Hₙ(p⁻¹(b))` of the inclusion of `b` is nonzero. -/
theorem livesOverFundamentalClass_iff_singularHomologyComplFiberIso_hom_ne_zero
    (hp : TopCat.serreFibrations p) {n m : ℕ} (h : n + finrank ℝ V = m)
    (α : ((_root_.TopCat.toSSet.obj E).homology (ModuleCat.of R R) m : ModuleCat.{u} R)) :
    LivesOverFundamentalClass (ModuleCat.of R R) p b α ↔
      (TopCat.singularHomologyComplFiberIso R e hb hp n m h).hom.hom
        ((fiberLocalization (ModuleCat.of R R) p b m).hom α) ≠ 0 := by
  rw [livesOverFundamentalClass_iff, not_iff_not]
  exact ⟨fun hα ↦ by rw [hα, map_zero], fun hα ↦ by
    simpa using congrArg (TopCat.singularHomologyComplFiberIso R e hb hp n m h).inv.hom hα⟩

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
