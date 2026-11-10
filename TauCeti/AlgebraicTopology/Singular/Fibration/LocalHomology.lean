/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.Excision
public import TauCeti.AlgebraicTopology.Singular.Fibration.Disk

/-!
# Homology of a Serre fibration relative to the complement of a fibre

Let `p : E → B` be a Serre fibration over a `T₁` space `B`, and let `b` be a point in the source
of an open partial homeomorphism `φ : B → V` to a real normed space `V` of finite dimension `r`,
such as a chart of a topological manifold modelled on `V`. Write `F_b = p⁻¹(b)` for the fibre over
`b`. With coefficients in a ring `R`, the relative singular homology of `E` modulo the complement
of the fibre is the homology of the fibre, shifted up by `r`:

* `Hₘ(E, E ∖ F_b; R) = 0` for `m < r`
  (`TauCeti.TopCat.isZero_singularHomology_complFiber_of_lt`);
* `Hₙ₊ᵣ(E, E ∖ F_b; R) ≅ Hₙ(F_b; R)`
  (`TauCeti.TopCat.singularHomologyComplFiberIsoOfChart`).

For the identity of `B` the fibre is the point `b`, and the statement reduces to the computation
of the local homology `Hₖ(B, B ∖ {b})` in `TauCeti.singularHomologyComplSingletonIsoOfChart` and
`TauCeti.isZero_singularHomology_complSingleton_of_ne`. For a fibration over a closed oriented
`r`-manifold, Barraud–Damian–Humilière–Oancea (Lemma 2.9) identify the restriction
`Hₘ(E) → Hₘ(E, E ∖ F_b)`, followed by an isomorphism `Hₘ(E, E ∖ F_b) ≅ Hₘ₋ᵣ(F_b)` of this kind,
with the shriek map of the inclusion of the point `b`; a class of `Hₘ(E)` lives over the
fundamental class of the base (their Definition 2.3 and Example 2.4) when this image is nonzero.
That comparison with their Morse-theoretic shriek map is not made here.

## The argument

The fibre `F_b` is closed, since `B` is `T₁`. Choose a ball `D` about `φ b` inside the target of
`φ`, and let `U = φ.source ∩ φ⁻¹(D)`, an open neighbourhood of `b`. By excision
(`TopPair.isIso_singularHomologyMap_excisionMap_of_isClosed_subset`), the pair `(E, E ∖ F_b)` may
be replaced by `(p⁻¹(U), p⁻¹(U) ∖ F_b)`. Over `U`, the fibration `p` restricts to a Serre fibration,
and the homeomorphism `x ↦ φ x - φ b` of `U` with a ball about `0` turns it into a Serre fibration
over a convex neighbourhood of `0` whose fibre over `0` is `F_b`. Its homology modulo the part over
the punctured ball is computed in `TauCeti.AlgebraicTopology.Singular.Fibration.Disk`
(`TauCeti.TopCat.singularHomologyPreimageNeZeroIso` and
`TauCeti.TopCat.isZero_singularHomology_preimage_ne_zero`).

## Main results

* `TauCeti.TopCat.isZero_singularHomology_complFiber_of_lt`: `Hₘ(E, E ∖ F_b; R) = 0` below the
  dimension of the chart.
* `TauCeti.TopCat.singularHomologyComplFiberIsoOfChart`: `Hₙ₊ᵣ(E, E ∖ F_b; R) ≅ Hₙ(F_b; R)`.

## References

* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Floer homology with DG coefficients.
  Applications to cotangent bundles*, arXiv:2404.07953, Definition 2.3 and Lemma 2.9.
* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Morse homology with differential graded
  coefficients*, Progress in Mathematics 360, Birkhäuser, 2025, Lemma 9.18.
* J.-P. Serre, *Homologie singulière des espaces fibrés. Applications*, Ann. of Math. 54 (1951),
  Chapter II.
-/

public section

noncomputable section

open CategoryTheory Limits Metric Module Set Topology

universe u

namespace TauCeti

namespace TopCat

variable {V : Type u} [NormedAddCommGroup V] {E B : _root_.TopCat.{u}}
  {p : E ⟶ B} (R : Type u) [Ring R] (φ : OpenPartialHomeomorph B V) {b : B} (hb : b ∈ φ.source)

namespace SerreChart

/-- The radius of a ball about `φ b` contained in the target of `φ`. -/
private def radius : ℝ :=
  (Metric.isOpen_iff.1 φ.open_target (φ b) (φ.map_source hb)).choose

private lemma radius_pos : 0 < radius φ hb :=
  (Metric.isOpen_iff.1 φ.open_target (φ b) (φ.map_source hb)).choose_spec.1

private lemma ball_subset_target : ball (φ b) (radius φ hb) ⊆ φ.target :=
  (Metric.isOpen_iff.1 φ.open_target (φ b) (φ.map_source hb)).choose_spec.2

/-- The open neighbourhood `φ.source ∩ φ⁻¹(D)` of `b`, for the ball `D` about `φ b`. -/
private def chartBall : Set B :=
  φ.source ∩ φ ⁻¹' ball (φ b) (radius φ hb)

private lemma mem_chartBall_iff {x : B} :
    x ∈ chartBall φ hb ↔ x ∈ φ.source ∧ φ x ∈ ball (φ b) (radius φ hb) :=
  Iff.rfl

private lemma isOpen_chartBall : IsOpen (chartBall φ hb) :=
  φ.isOpen_inter_preimage isOpen_ball

private lemma mem_chartBall : b ∈ chartBall φ hb :=
  (mem_chartBall_iff φ hb).2 ⟨hb, mem_ball_self (radius_pos φ hb)⟩

private lemma add_mem_ball {v : V} (hv : v ∈ ball (0 : V) (radius φ hb)) :
    v + φ b ∈ ball (φ b) (radius φ hb) := by
  rwa [mem_ball, dist_eq_norm, add_sub_cancel_right, ← mem_ball_zero_iff]

private lemma add_mem_target (v : ball (0 : V) (radius φ hb)) : v + φ b ∈ φ.target :=
  ball_subset_target φ hb (add_mem_ball φ hb v.2)

private lemma sub_mem_ball (x : chartBall φ hb) : φ x - φ b ∈ ball (0 : V) (radius φ hb) := by
  rw [mem_ball_zero_iff, ← dist_eq_norm]
  exact ((mem_chartBall_iff φ hb).1 x.2).2

private lemma symm_add_mem_chartBall (v : ball (0 : V) (radius φ hb)) :
    φ.symm (v + φ b) ∈ chartBall φ hb := by
  refine (mem_chartBall_iff φ hb).2 ⟨φ.map_target (add_mem_target φ hb v), ?_⟩
  rw [φ.right_inv (add_mem_target φ hb v)]
  exact add_mem_ball φ hb v.2

private lemma continuous_sub_chart : Continuous fun x : chartBall φ hb ↦ φ x - φ b :=
  (φ.continuousOn.comp_continuous continuous_subtype_val
    fun x ↦ ((mem_chartBall_iff φ hb).1 x.2).1).sub continuous_const

private lemma continuous_symm_add :
    Continuous fun v : ball (0 : V) (radius φ hb) ↦ φ.symm (v + φ b) :=
  φ.continuousOn_symm.comp_continuous (continuous_subtype_val.add continuous_const)
    (add_mem_target φ hb)

/-- The homeomorphism `x ↦ φ x - φ b` of the neighbourhood `chartBall φ hb` of `b` with the ball
about `0` of the same radius. -/
private def chartBallHomeomorph : chartBall φ hb ≃ₜ ball (0 : V) (radius φ hb) where
  toFun x := ⟨φ x - φ b, sub_mem_ball φ hb x⟩
  invFun v := ⟨φ.symm (v + φ b), symm_add_mem_chartBall φ hb v⟩
  left_inv x := Subtype.ext <|
    (congrArg φ.symm (sub_add_cancel _ _)).trans (φ.left_inv ((mem_chartBall_iff φ hb).1 x.2).1)
  right_inv v := Subtype.ext <|
    (congrArg (· - φ b) (φ.right_inv (add_mem_target φ hb v))).trans (add_sub_cancel_right _ _)
  continuous_toFun := (continuous_sub_chart φ hb).subtype_mk (sub_mem_ball φ hb)
  continuous_invFun := (continuous_symm_add φ hb).subtype_mk (symm_add_mem_chartBall φ hb)

/-- The restriction of `p` over `chartBall φ hb`, read in the ball about `0` through
`x ↦ φ x - φ b`. -/
private def chartFibration (p : E ⟶ B) :
    _root_.TopCat.of (p ⁻¹' chartBall φ hb) ⟶ _root_.TopCat.of (ball (0 : V) (radius φ hb)) :=
  _root_.TopCat.ofHom (p.hom.restrictPreimage (chartBall φ hb)) ≫
    (_root_.TopCat.isoOfHomeo (X := _root_.TopCat.of (chartBall φ hb))
      (chartBallHomeomorph φ hb)).hom

private lemma coe_chartFibration_apply (z : _root_.TopCat.of (p ⁻¹' chartBall φ hb)) :
    (chartFibration φ hb p z : V) = φ (p z) - φ b :=
  (rfl)

private lemma mem_serreFibrations_chartFibration (hp : serreFibrations p) :
    serreFibrations (chartFibration φ hb p) :=
  serreFibrations.comp_mem _ _ (mem_serreFibrations_restrictPreimage hp _)
    (serreFibrations.of_isIso _)

/-- Over `chartBall φ hb`, the complement of the fibre over `b` is the part over the punctured
ball. -/
private def pairIso :
    TopPair.interPair (X := E) (p ⁻¹' chartBall φ hb) (p ⁻¹' {b})ᶜ ≅
      TopPair.ofSubset (chartFibration φ hb p ⁻¹' {x | (x : V) ≠ 0}) :=
  TopPair.ofSubsetIso (Homeomorph.refl _) fun z ↦ by
    simp only [mem_compl_iff, mem_preimage, mem_singleton_iff, mem_ofPred_eq,
      Homeomorph.refl_apply, id]
    rw [coe_chartFibration_apply, sub_ne_zero]
    exact (φ.injOn.eq_iff ((mem_chartBall_iff φ hb).1 z.2).1 hb).not.symm

/-- The fibre over `0` of `chartFibration φ hb p` is the fibre of `p` over `b`. -/
private def fiberHomeomorph :
    (chartFibration φ hb p ⁻¹' {x | (x : V) = 0}) ≃ₜ (p ⁻¹' {b}) where
  toFun z := ⟨z.1.1, (φ.injOn.eq_iff ((mem_chartBall_iff φ hb).1 z.1.2).1 hb).1 <|
    sub_eq_zero.1 <| by
      rw [← coe_chartFibration_apply]
      exact z.2⟩
  invFun y :=
    have hy : p y.1 = b := y.2
    ⟨⟨y.1, by
      rw [mem_preimage, hy]
      exact mem_chartBall φ hb⟩, by
      rw [mem_preimage, mem_ofPred_eq, coe_chartFibration_apply]
      exact sub_eq_zero.2 (congrArg φ hy)⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
  continuous_invFun := (continuous_subtype_val.subtype_mk _).subtype_mk _

variable [T1Space B]

/-- Excision onto the part of `E` over `chartBall φ hb`, followed by `pairIso`. -/
private def excisionIso (m : ℕ) :
    (TopPair.ofSubset (p ⁻¹' {b})ᶜ).singularHomology (ModuleCat.of R R) m ≅
      (TopPair.ofSubset (chartFibration φ hb p ⁻¹' {x | (x : V) ≠ 0})).singularHomology
        (ModuleCat.of R R) m :=
  haveI := TopPair.isIso_singularHomologyMap_excisionMap_of_isClosed_subset (ModuleCat.of R R)
    (X := E) ((isOpen_chartBall φ hb).preimage p.hom.continuous)
    (isClosed_singleton.preimage p.hom.continuous)
    (preimage_mono (singleton_subset_iff.2 (mem_chartBall φ hb))) m
  (asIso (TopPair.singularHomologyMap
      (TopPair.excisionMap (X := E) (p ⁻¹' chartBall φ hb) (p ⁻¹' {b})ᶜ) _ m)).symm ≪≫
    asIso (TopPair.singularHomologyMap (pairIso φ hb).hom _ m)

end SerreChart

open SerreChart

variable [T1Space B] [NormedSpace ℝ V] [FiniteDimensional ℝ V]

include φ hb in
/-- **The homology of a Serre fibration modulo the complement of a fibre vanishes below the
dimension.** Let `p : E ⟶ B` be a Serre fibration over a `T₁` space, and let `b` lie in the source
of an open partial homeomorphism `φ : B → V` to a finite-dimensional real normed space. Then
`Hₘ(E, E ∖ p⁻¹(b); R) = 0` for every `m < dim V`. -/
theorem isZero_singularHomology_complFiber_of_lt (hp : serreFibrations p) {m : ℕ}
    (hm : m < finrank ℝ V) :
    IsZero ((TopPair.ofSubset (p ⁻¹' {b})ᶜ).singularHomology (ModuleCat.of R R) m) :=
  (isZero_singularHomology_preimage_ne_zero R (mem_serreFibrations_chartFibration φ hb hp)
    (convex_ball 0 _) (ball_mem_nhds 0 (radius_pos φ hb)) hm).of_iso (excisionIso R φ hb m)

/-- **The homology of a Serre fibration modulo the complement of a fibre is the shifted homology
of the fibre.** Let `p : E ⟶ B` be a Serre fibration over a `T₁` space, and let `b` lie in the
source of an open partial homeomorphism `φ : B → V` to a real normed space of finite dimension `r`,
such as the chart `chartAt V b` of a topological manifold modelled on `V`. Then
`Hₘ(E, E ∖ p⁻¹(b); R) ≅ Hₙ(p⁻¹(b); R)` for `m = n + r`.

The isomorphism is excision onto the part of `E` over a ball about `b` in the chart `φ`, followed by
`TauCeti.TopCat.singularHomologyPreimageNeZeroIso` for the restriction of `p` over that ball. -/
def singularHomologyComplFiberIsoOfChart (hp : serreFibrations p) (n m : ℕ)
    (h : n + finrank ℝ V = m) :
    (TopPair.ofSubset (p ⁻¹' {b})ᶜ).singularHomology (ModuleCat.of R R) m ≅
      ((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} R) n).obj
        (ModuleCat.of R R)).obj (_root_.TopCat.of (p ⁻¹' {b})) :=
  excisionIso R φ hb m ≪≫
    singularHomologyPreimageNeZeroIso R (mem_serreFibrations_chartFibration φ hb hp)
      (convex_ball 0 _) (ball_mem_nhds 0 (radius_pos φ hb)) n m h ≪≫
    ((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} R) n).obj
      (ModuleCat.of R R)).mapIso (_root_.TopCat.isoOfHomeo (fiberHomeomorph φ hb))

end TopCat

end TauCeti
