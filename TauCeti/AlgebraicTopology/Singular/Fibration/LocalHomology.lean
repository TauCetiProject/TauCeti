/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.Fibration.Disk
public import TauCeti.AlgebraicTopology.Singular.Excision
public import TauCeti.AlgebraicTopology.Singular.LocalHomology.FundamentalClass

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
detect classes **living above the fundamental class** of the base: a class
`α ∈ Hₖ(E)` lives above the fundamental class at `b` when its image in `Hₖ(E, E ∖ F)` is nonzero
(`TauCeti.TopCat.LivesAboveFundamentalClass`), equivalently when `j_! α ≠ 0`
(`TauCeti.TopCat.livesAboveFundamentalClass_iff_singularHomologyComplFiberIso`). Such a class has
degree at least `r` (`TauCeti.TopCat.LivesAboveFundamentalClass.finrank_le`). For the identity
fibration of a compact connected oriented manifold `M`, the classes of `Hₙ(M; ℤ)` living above the
fundamental class are exactly the nonzero multiples of the fundamental class
(`TauCeti.HomologicalOrientation.livesAboveFundamentalClass_id_iff`), which motivates the name.

The relative group, rather than the shriek map itself, is used in the definition because it does
not depend on the chart: the identification `Hₙ₊ᵣ(E, E ∖ F) ≅ Hₙ(F)` depends on the chart and on a
ball in it.

## The computation

Choose a ball of radius `ε` about `e b` inside the target of `e`, and let `U` be its preimage in
the source of `e` (`TauCeti.TopCat.SerreChart.chartBall`), an open neighbourhood of `b`. Excision
onto the open set `p⁻¹(U)`, which contains the closed fibre `F`, identifies `Hₖ(E, E ∖ F)` with
`Hₖ(p⁻¹(U), p⁻¹(U) ∖ F)` (`TopPair.isIso_singularHomologyMap_excisionMap_of_isClosed_subset`). The
restriction of `p` over `U`, followed by the homeomorphism `x ↦ e x - e b` of `U` with the ball `K`
of radius `ε` about `0`, is a Serre fibration over the convex neighbourhood `K` of `0`
(`TauCeti.TopCat.SerreChart.chartFibration`) whose fibre over `0` is `F`
(`TauCeti.TopCat.SerreChart.fiberHomeomorph`), and the part of `p⁻¹(U)` over `K ∖ {0}` is
`p⁻¹(U) ∖ F` (`TauCeti.TopCat.SerreChart.interPairIso`). The homology of a Serre fibration over a
convex neighbourhood of `0` modulo the part over the punctured base is the shifted homology of the
fibre (`TauCeti.TopCat.singularHomologyPreimageNeZeroIso`), and vanishes below the dimension
(`TauCeti.TopCat.isZero_singularHomology_preimage_ne_zero`).

## Main definitions and results

* `TauCeti.TopCat.singularHomologyComplFiberIso`: `Hₙ₊ᵣ(E, E ∖ p⁻¹(b)) ≅ Hₙ(p⁻¹(b))`, for a
  chosen ball about `e b` inside the target of `e`. After excision onto the part of `E` over the
  ball, it is `TauCeti.TopCat.singularHomologyPreimageNeZeroIso` for the restricted fibration
  (`TauCeti.TopCat.singularHomologyMap_excisionMap_comp_singularHomologyComplFiberIso_hom` and
  `TauCeti.TopCat.map_fiberHomeomorph_comp_singularHomologyComplFiberIso_inv`).
* `TauCeti.TopCat.isZero_singularHomology_complFiber`: `Hₘ(E, E ∖ p⁻¹(b)) = 0` for `m < r`.
* `TauCeti.TopCat.LivesAboveFundamentalClass`: classes of `Hₖ(E)` with nonzero image in
  `Hₖ(E, E ∖ p⁻¹(b))`.
* `TauCeti.TopCat.livesAboveFundamentalClass_iff_singularHomologyComplFiberIso`: the same
  condition read in `Hₖ₋ᵣ(p⁻¹(b))`.
* `TauCeti.TopCat.LivesAboveFundamentalClass.of_map`: a class whose image under a map over `B`
  lives above the fundamental class lives above it.
* `TauCeti.HomologicalOrientation.livesAboveFundamentalClass_id_iff`: for the identity fibration
  of a compact connected oriented manifold, these are the nonzero multiples of `[M]`.

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

variable {V : Type u} [NormedAddCommGroup V] {E B : _root_.TopCat.{u}}
  {p : E ⟶ B} (R : Type u) [Ring R] (e : OpenPartialHomeomorph B V) {b : B} (hb : b ∈ e.source)
  {ε : ℝ} (hε : ball (e b) ε ⊆ e.target)

namespace SerreChart

/-- The open neighbourhood `e.source ∩ e⁻¹(D)` of `b`, for the ball `D` about `e b` of radius
`ε`. -/
def chartBall (b : B) (ε : ℝ) : Set B :=
  e.source ∩ e ⁻¹' ball (e b) ε

@[simp]
lemma mem_chartBall {b x : B} {ε : ℝ} :
    x ∈ chartBall e b ε ↔ x ∈ e.source ∧ e x ∈ ball (e b) ε :=
  Iff.rfl

lemma isOpen_chartBall (b : B) (ε : ℝ) : IsOpen (chartBall e b ε) :=
  e.isOpen_inter_preimage isOpen_ball

include hb in
lemma mem_chartBall_self (hε₀ : 0 < ε) : b ∈ chartBall e b ε :=
  ⟨hb, mem_ball_self hε₀⟩

/-- The chart `e` followed by the translation `v ↦ v - e b`, which sends `b` to `0`. -/
private def translatedChart (b : B) : OpenPartialHomeomorph B V :=
  e.trans (Homeomorph.addRight (-e b)).toOpenPartialHomeomorph

private lemma translatedChart_apply (b x : B) : translatedChart e b x = e x - e b :=
  (sub_eq_add_neg _ _).symm

include hε in
private lemma image_translatedChart_chartBall :
    translatedChart e b '' chartBall e b ε = ball (0 : V) ε := by
  ext v
  refine ⟨?_, fun hv ↦ ?_⟩
  · rintro ⟨x, hx, rfl⟩
    rw [translatedChart_apply, mem_ball_zero_iff, ← dist_eq_norm]
    exact hx.2
  · have hv' : v + e b ∈ ball (e b) ε := by
      rwa [mem_ball, dist_eq_norm, add_sub_cancel_right, ← mem_ball_zero_iff]
    exact ⟨e.symm (v + e b), ⟨e.map_target (hε hv'), by rwa [mem_preimage, e.right_inv (hε hv')]⟩,
      by rw [translatedChart_apply, e.right_inv (hε hv'), add_sub_cancel_right]⟩

/-- The restriction of `p` over `chartBall e b ε`, read in the ball about `0` through
`x ↦ e x - e b`. -/
def chartFibration (p : E ⟶ B) :
    _root_.TopCat.of (p ⁻¹' chartBall e b ε) ⟶ _root_.TopCat.of (ball (0 : V) ε) :=
  _root_.TopCat.ofHom (p.hom.restrictPreimage (chartBall e b ε)) ≫
    (_root_.TopCat.isoOfHomeo (X := _root_.TopCat.of (chartBall e b ε))
      ((translatedChart e b).homeomorphOfImageSubsetSource
        (fun _ hx ↦ ⟨(hx : _ ∈ chartBall e b ε).1, trivial⟩)
        (image_translatedChart_chartBall e hε))).hom

lemma coe_chartFibration_apply (z : _root_.TopCat.of (p ⁻¹' chartBall e b ε)) :
    (chartFibration e hε p z : V) = e (p z) - e b :=
  translatedChart_apply e b (p z)

include hb in
/-- A point over `chartBall e b ε` lies over `0` in the ball exactly when it lies over `b`. -/
lemma coe_chartFibration_eq_zero_iff (z : _root_.TopCat.of (p ⁻¹' chartBall e b ε)) :
    (chartFibration e hε p z : V) = 0 ↔ p z = b := by
  rw [coe_chartFibration_apply, sub_eq_zero]
  exact e.injOn.eq_iff z.2.1 hb

lemma mem_serreFibrations_chartFibration (hp : serreFibrations p) :
    serreFibrations (chartFibration e hε p) :=
  serreFibrations.comp_mem _ _ (mem_serreFibrations_restrictPreimage hp _)
    (serreFibrations.of_isIso _)

/-- Over `chartBall e b ε`, the complement of the fibre over `b` is the part over the punctured
ball. -/
def interPairIso :
    TopPair.interPair (X := E) (p ⁻¹' chartBall e b ε) (p ⁻¹' {b})ᶜ ≅
      TopPair.ofSubset (chartFibration e hε p ⁻¹' {x | (x : V) ≠ 0}) :=
  TopPair.ofSubsetIso (Homeomorph.refl _) fun z ↦ by
    exact (coe_chartFibration_eq_zero_iff e hb hε z).not.symm

/-- The forward map of `interPairIso` is induced by the identity of `p⁻¹(chartBall e b ε)`. -/
lemma interPairIso_hom :
    (interPairIso (p := p) e hb hε).hom =
      TopPair.ofSubsetMap (_root_.TopCat.ofHom (Homeomorph.refl (p ⁻¹' chartBall e b ε)))
        fun z hz ↦ by exact (coe_chartFibration_eq_zero_iff e hb hε z).not.2 hz := by
  unfold interPairIso
  exact TopPair.ofSubsetIso_hom _ _

/-- The inverse map of `interPairIso` is induced by the identity of `p⁻¹(chartBall e b ε)`. -/
lemma interPairIso_inv :
    (interPairIso (p := p) e hb hε).inv =
      TopPair.ofSubsetMap (_root_.TopCat.ofHom (Homeomorph.refl (p ⁻¹' chartBall e b ε)))
        fun z hz ↦ by exact (coe_chartFibration_eq_zero_iff e hb hε z).not.1 hz := by
  unfold interPairIso
  exact TopPair.ofSubsetIso_inv _ _

/-- The fibre over `0` of `chartFibration e hε p` is the fibre of `p` over `b`. -/
def fiberHomeomorph (hε₀ : 0 < ε) :
    (chartFibration e hε p ⁻¹' {x | (x : V) = 0}) ≃ₜ (p ⁻¹' {b}) where
  toFun z := ⟨z.1.1, (e.injOn.eq_iff z.1.2.1 hb).1 <|
    sub_eq_zero.1 <| by
      rw [← coe_chartFibration_apply e hε]
      exact z.2⟩
  invFun y :=
    have hy : p y.1 = b := y.2
    ⟨⟨y.1, by
      rw [mem_preimage, hy]
      exact mem_chartBall_self e hb hε₀⟩, by
      rw [mem_preimage, mem_ofPred_eq, coe_chartFibration_apply]
      exact sub_eq_zero.2 (congrArg e hy)⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
  continuous_invFun := (continuous_subtype_val.subtype_mk _).subtype_mk _

lemma coe_fiberHomeomorph_apply (hε₀ : 0 < ε) (z : chartFibration e hε p ⁻¹' {x | (x : V) = 0}) :
    (fiberHomeomorph e hb hε hε₀ z : E) = z.1.1 :=
  (rfl)

lemma coe_fiberHomeomorph_symm_apply (hε₀ : 0 < ε) (y : p ⁻¹' {b}) :
    ((fiberHomeomorph e hb hε hε₀).symm y).1.1 = y.1 :=
  (rfl)

variable [T1Space B]

/-- Excision onto the part of `E` over `chartBall e b ε`, followed by `interPairIso`. -/
private def excisionIso (hε₀ : 0 < ε) (m : ℕ) :
    (TopPair.ofSubset (p ⁻¹' {b})ᶜ).singularHomology (ModuleCat.of R R) m ≅
      (TopPair.ofSubset (chartFibration e hε p ⁻¹' {x | (x : V) ≠ 0})).singularHomology
        (ModuleCat.of R R) m :=
  haveI := TopPair.isIso_singularHomologyMap_excisionMap_of_isClosed_subset (ModuleCat.of R R)
    (X := E) ((isOpen_chartBall e b ε).preimage p.hom.continuous)
    (isClosed_singleton.preimage p.hom.continuous)
    (preimage_mono (singleton_subset_iff.2 (mem_chartBall_self e hb hε₀))) m
  (asIso (TopPair.singularHomologyMap
      (TopPair.excisionMap (X := E) (p ⁻¹' chartBall e b ε) (p ⁻¹' {b})ᶜ) _ m)).symm ≪≫
    asIso (TopPair.singularHomologyMap (interPairIso e hb hε).hom _ m)

end SerreChart

open SerreChart

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
  exact (isZero_singularHomology_preimage_ne_zero R (mem_serreFibrations_chartFibration e hε hp)
    (convex_ball 0 _) (ball_mem_nhds 0 hε₀) hm).of_iso (excisionIso R e hb hε hε₀ m)

/-- **The homology of a Serre fibration modulo the complement of a fibre is the shifted homology
of the fibre.** Let `p : E ⟶ B` be a Serre fibration over a `T₁` space, and let `b` lie in the
source of an open partial homeomorphism `e : B → V` to a real normed space of finite dimension `r`,
such as the chart `chartAt V b` of a topological manifold modelled on `V`. Then
`Hₘ(E, E ∖ p⁻¹(b); R) ≅ Hₙ(p⁻¹(b); R)` for `m = n + r`.

The isomorphism depends on a ball of radius `ε` about `e b` inside the target of `e`: it is
excision onto the part of `E` over `TauCeti.TopCat.SerreChart.chartBall e b ε`, followed by
`TauCeti.TopCat.singularHomologyPreimageNeZeroIso` for the restriction of `p` over that set
(`TauCeti.TopCat.singularHomologyMap_excisionMap_comp_singularHomologyComplFiberIso_hom`). -/
def singularHomologyComplFiberIso (hε₀ : 0 < ε) (hp : serreFibrations p) (n m : ℕ)
    (h : n + finrank ℝ V = m) :
    (TopPair.ofSubset (p ⁻¹' {b})ᶜ).singularHomology (ModuleCat.of R R) m ≅
      ((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} R) n).obj
        (ModuleCat.of R R)).obj (_root_.TopCat.of (p ⁻¹' {b})) :=
  excisionIso R e hb hε hε₀ m ≪≫
    singularHomologyPreimageNeZeroIso R (mem_serreFibrations_chartFibration e hε hp)
      (convex_ball 0 _) (ball_mem_nhds 0 hε₀) n m h ≪≫
    ((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} R) n).obj
      (ModuleCat.of R R)).mapIso (_root_.TopCat.isoOfHomeo (fiberHomeomorph e hb hε hε₀))

/-- The isomorphism `TauCeti.TopCat.singularHomologyComplFiberIso` commutes with excision
onto the part of `E` over `TauCeti.TopCat.SerreChart.chartBall e b ε`: after excision it is
`TauCeti.TopCat.singularHomologyPreimageNeZeroIso` for the restricted fibration, followed by the
identification of its fibre over `0` with the fibre over `b`. -/
@[reassoc]
lemma singularHomologyMap_excisionMap_comp_singularHomologyComplFiberIso_hom
    (hε₀ : 0 < ε) (hp : serreFibrations p) (n m : ℕ) (h : n + finrank ℝ V = m) :
    TopPair.singularHomologyMap
        (TopPair.excisionMap (X := E) (p ⁻¹' chartBall e b ε) (p ⁻¹' {b})ᶜ)
        (ModuleCat.of R R) m ≫
        (singularHomologyComplFiberIso R e hb hε hε₀ hp n m h).hom =
      TopPair.singularHomologyMap (interPairIso e hb hε).hom (ModuleCat.of R R) m ≫
        (singularHomologyPreimageNeZeroIso R (mem_serreFibrations_chartFibration e hε hp)
          (convex_ball 0 _) (ball_mem_nhds 0 hε₀) n m h).hom ≫
        ((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} R) n).obj
          (ModuleCat.of R R)).map (_root_.TopCat.isoOfHomeo (fiberHomeomorph e hb hε hε₀)).hom := by
  simp [singularHomologyComplFiberIso, excisionIso]

/-- The inverse of `TauCeti.TopCat.singularHomologyComplFiberIso`, after the identification
of the fibre over `b` with the fibre over `0` of the restricted fibration, is the inverse of
`TauCeti.TopCat.singularHomologyPreimageNeZeroIso` followed by excision. -/
@[reassoc]
lemma map_fiberHomeomorph_comp_singularHomologyComplFiberIso_inv
    (hε₀ : 0 < ε) (hp : serreFibrations p) (n m : ℕ) (h : n + finrank ℝ V = m) :
    ((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} R) n).obj
          (ModuleCat.of R R)).map (_root_.TopCat.isoOfHomeo (fiberHomeomorph e hb hε hε₀)).hom ≫
        (singularHomologyComplFiberIso R e hb hε hε₀ hp n m h).inv =
      (singularHomologyPreimageNeZeroIso R (mem_serreFibrations_chartFibration e hε hp)
          (convex_ball 0 _) (ball_mem_nhds 0 hε₀) n m h).inv ≫
        TopPair.singularHomologyMap (interPairIso e hb hε).inv (ModuleCat.of R R) m ≫
        TopPair.singularHomologyMap
          (TopPair.excisionMap (X := E) (p ⁻¹' chartBall e b ε) (p ⁻¹' {b})ᶜ)
          (ModuleCat.of R R) m := by
  rw [Iso.comp_inv_eq, Category.assoc, Category.assoc,
    singularHomologyMap_excisionMap_comp_singularHomologyComplFiberIso_hom,
    ← TopPair.singularHomologyMap_comp_assoc, Iso.inv_hom_id, TopPair.singularHomologyMap_id,
    Category.id_comp, Iso.inv_hom_id_assoc]

end Chart

/-! ### Classes living above the fundamental class -/

section LivesAbove

variable {E B E' : _root_.TopCat.{u}} {k : Type*} [Ring k] (M : ModuleCat.{u} k)

/-- A class `α ∈ H_d(E; M)` **lives above the fundamental class** of the base at `b`, for a map
`p : E ⟶ B`, if its image in the local homology `H_d(E, E ∖ p⁻¹(b); M)` along the fibre is
nonzero. For a Serre fibration over a manifold of dimension `r`, this group is
`H_{d-r}(p⁻¹(b))`, and the condition says that the shriek map of the inclusion of the point `b`
does not kill `α` (`TauCeti.TopCat.livesAboveFundamentalClass_iff_singularHomologyComplFiberIso`).
-/
def LivesAboveFundamentalClass (p : E ⟶ B) (b : B) {d : ℕ}
    (α : ((_root_.TopCat.toSSet.obj E).homology M d : ModuleCat.{u} k)) : Prop :=
  ((TopPair.ofSubset ((p ⁻¹' {b})ᶜ : Set E)).singularHomologyπ M d).hom α ≠ 0

theorem livesAboveFundamentalClass_iff (p : E ⟶ B) (b : B) {d : ℕ}
    (α : ((_root_.TopCat.toSSet.obj E).homology M d : ModuleCat.{u} k)) :
    LivesAboveFundamentalClass M p b α ↔
      ((TopPair.ofSubset ((p ⁻¹' {b})ᶜ : Set E)).singularHomologyπ M d).hom α ≠ 0 :=
  Iff.rfl

variable {M}

/-- The zero class does not live above the fundamental class. -/
@[simp]
theorem not_livesAboveFundamentalClass_zero (p : E ⟶ B) (b : B) (d : ℕ) :
    ¬ LivesAboveFundamentalClass M p b
      (0 : ((_root_.TopCat.toSSet.obj E).homology M d : ModuleCat.{u} k)) :=
  fun h ↦ h (map_zero _)

/-- **Pulling back along a map over the base.** If `f : E ⟶ E'` is a map over `B`, from `p` to
`p'`, and the image `f_* α` lives above the fundamental class for `p'`, then `α` lives above the
fundamental class for `p`. -/
theorem LivesAboveFundamentalClass.of_map {p : E ⟶ B} {p' : E' ⟶ B} (f : E ⟶ E')
    (hf : f ≫ p' = p) {b : B} {d : ℕ}
    {α : ((_root_.TopCat.toSSet.obj E).homology M d : ModuleCat.{u} k)}
    (h : LivesAboveFundamentalClass M p' b
      ((SSet.homologyMap (_root_.TopCat.toSSet.map f) M d).hom α)) :
    LivesAboveFundamentalClass M p b α := by
  have hmaps : MapsTo f ((p ⁻¹' {b})ᶜ) ((p' ⁻¹' {b})ᶜ) := fun x hx ↦ by
    simpa [← hf] using hx
  intro hα
  apply h
  have := ConcreteCategory.congr_hom
    (TopPair.singularHomologyπ_naturality (TopPair.ofSubsetMap f hmaps) M d) α
  rw [TopPair.ofSubsetMap_fst] at this
  -- The composites are stated between definitionally equal homology objects, so the element-level
  -- identities are closed by `rfl` rather than by rewriting with `ConcreteCategory.comp_apply`.
  calc _ = ((SSet.homologyMap (_root_.TopCat.toSSet.map f) M d ≫
          (TopPair.ofSubset ((p' ⁻¹' {b})ᶜ : Set E')).singularHomologyπ M d).hom α) := rfl
    _ = (TopPair.singularHomologyMap (TopPair.ofSubsetMap f hmaps) M d).hom
          (((TopPair.ofSubset ((p ⁻¹' {b})ᶜ : Set E)).singularHomologyπ M d).hom α) := this
    _ = 0 := by rw [hα, map_zero]

variable {V : Type u} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [T1Space B] {p : E ⟶ B} {R : Type u} [Ring R]
  (e : OpenPartialHomeomorph B V) {b : B} (hb : b ∈ e.source)

/-- **Living above the fundamental class through the shriek map.** For a Serre fibration over a
`T₁` space with a chart `e` of dimension `r` at `b`, a class `α ∈ Hₙ₊ᵣ(E; R)` lives above the
fundamental class at `b` exactly when its image under
`Hₙ₊ᵣ(E) → Hₙ₊ᵣ(E, E ∖ p⁻¹(b)) ≅ Hₙ(p⁻¹(b))` is nonzero, for any ball about `e b` inside the
target of `e`. -/
theorem livesAboveFundamentalClass_iff_singularHomologyComplFiberIso {ε : ℝ}
    (hε : ball (e b) ε ⊆ e.target) (hε₀ : 0 < ε) (hp : serreFibrations p)
    {n m : ℕ} (h : n + finrank ℝ V = m)
    (α : ((_root_.TopCat.toSSet.obj E).homology (ModuleCat.of R R) m : ModuleCat.{u} R)) :
    LivesAboveFundamentalClass (ModuleCat.of R R) p b α ↔
      (singularHomologyComplFiberIso R e hb hε hε₀ hp n m h).hom.hom
        (((TopPair.ofSubset ((p ⁻¹' {b})ᶜ : Set E)).singularHomologyπ (ModuleCat.of R R) m).hom
          α) ≠ 0 := by
  rw [livesAboveFundamentalClass_iff, not_iff_not]
  exact ⟨fun hα ↦ by rw [hα, map_zero], fun hα ↦ by
    simpa using congrArg (singularHomologyComplFiberIso R e hb hε hε₀ hp n m h).inv.hom hα⟩

include hb in
/-- **A class living above the fundamental class has degree at least the dimension of the base.**
-/
theorem LivesAboveFundamentalClass.finrank_le (hp : serreFibrations p) {d : ℕ}
    {α : ((_root_.TopCat.toSSet.obj E).homology (ModuleCat.of R R) d : ModuleCat.{u} R)}
    (h : LivesAboveFundamentalClass (ModuleCat.of R R) p b α) : finrank ℝ V ≤ d := by
  by_contra hd
  have := ModuleCat.isZero_iff_subsingleton.1 (isZero_singularHomology_complFiber R e hb hp
    (not_le.1 hd))
  exact h (Subsingleton.elim _ _)

end LivesAbove

end TopCat

/-! ### The identity fibration of an oriented manifold -/

namespace HomologicalOrientation

variable {M E : Type} [TopologicalSpace M] [T2Space M]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [ChartedSpace E M]
  {n : ℕ} (o : HomologicalOrientation M E n) (hn : finrank ℝ E = n) [CompactSpace M]

/-- The image of `c • [M]` in the local homology at `x` is `c • o x`. -/
private theorem singularHomologyπ_zsmul_fundamentalClass (x : M) (c : ℤ) :
    ((TopPair.ofSubset (((𝟙 (_root_.TopCat.of M)) ⁻¹' {x})ᶜ : Set (_root_.TopCat.of M)))
      |>.singularHomologyπ (ModuleCat.of ℤ (ULift.{0} ℤ)) n).hom (c • o.fundamentalClass hn) =
      c • (o x).val :=
  (map_zsmul _ c _).trans (congrArg (c • ·)
    ((o.singularHomologyπ_fundamentalClass hn isCompact_singleton).trans
      (o.fundamentalClassOn_singleton hn x isCompact_singleton)))

/-- **The fundamental class lives above itself.** For the identity fibration of a compact oriented
manifold `M`, the fundamental class lives above the fundamental class at every point. -/
theorem livesAboveFundamentalClass_fundamentalClass (x : M) :
    TopCat.LivesAboveFundamentalClass (ModuleCat.of ℤ (ULift.{0} ℤ)) (𝟙 (_root_.TopCat.of M)) x
      (o.fundamentalClass hn) := by
  intro h
  refine one_ne_zero (((o.zsmul_left_injective hn x).eq_iff' (zero_zsmul _)).1 ?_)
  rw [← o.singularHomologyπ_zsmul_fundamentalClass hn x, one_zsmul]
  exact h

/-- **Classes living above the fundamental class of a manifold.** For the identity fibration of a
compact connected oriented manifold `M`, a class of `Hₙ(M; ℤ)` lives above the fundamental class at
a point exactly when it is a nonzero multiple of the fundamental class. -/
theorem livesAboveFundamentalClass_id_iff [ConnectedSpace M] (x : M)
    (γ : ((_root_.TopCat.toSSet.obj (_root_.TopCat.of M)).homology
      (ModuleCat.of ℤ (ULift.{0} ℤ)) n : ModuleCat.{0} ℤ)) :
    TopCat.LivesAboveFundamentalClass (ModuleCat.of ℤ (ULift.{0} ℤ)) (𝟙 (_root_.TopCat.of M)) x
      γ ↔ ∃ c : ℤ, c ≠ 0 ∧ γ = c • o.fundamentalClass hn := by
  obtain ⟨c, rfl⟩ := o.exists_eq_zsmul_fundamentalClass hn γ
  refine (not_congr (((congrArg (· = 0)
    (o.singularHomologyπ_zsmul_fundamentalClass hn x c)).to_iff).trans
      ((o.zsmul_left_injective hn x).eq_iff' (zero_zsmul _)))).trans ?_
  refine ⟨fun hc ↦ ⟨c, hc, rfl⟩, ?_⟩
  rintro ⟨c', hc', h⟩
  rwa [((o.fundamentalClassEquiv hn).injective ((o.fundamentalClassEquiv_apply hn c).trans
    (h.trans (o.fundamentalClassEquiv_apply hn c').symm)))]

end HomologicalOrientation

end TauCeti
