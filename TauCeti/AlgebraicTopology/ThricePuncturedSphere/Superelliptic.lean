/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.ThricePuncturedSphere.Deck
public import TauCeti.AlgebraicTopology.ThricePuncturedSphere.PuncturedNeighborhoodComponents
public import TauCeti.AlgebraicTopology.UniversalCover.Deck.Quotient.ActingGroup
public import TauCeti.Combinatorics.PermutationTriple.Examples
public import TauCeti.GroupTheory.Perm.OrbitCount.Basic

import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.RingTheory.RootsOfUnity.Complex
import TauCeti.Analysis.Normed.Module.Connected
import TauCeti.Analysis.Polynomial.SimpleRoots.Covering
import TauCeti.Combinatorics.PermutationTriple.Regular
import TauCeti.Combinatorics.PermutationTriple.SmallDegrees
import TauCeti.RingTheory.RootsOfUnity.PowFiber

/-!
# The superelliptic cover `y ^ 4 = t (t - 1)` of the thrice-punctured sphere

The affine curve `y ^ 4 = t (t - 1)` maps to the `t`-line, and over the thrice-punctured sphere
`U = ℂ ∖ {0, 1}` its points form the space `TauCeti.ThricePuncturedSphere.superellipticCurve` of
pairs `(t, y)` with `t ∈ U`. The projection `(t, y) ↦ t` is the unbranched part of the Belyi map
`β = t` of the compact superelliptic curve, a curve of genus one. This file reads off the
topology of this cover directly from the equation, and identifies its monodromy with the Euclidean
torus triple `TauCeti.PermutationTriple.torusTriple`.

* **A four-sheeted cover.** Over `t ∈ U` the radicand `t (t - 1)` is nonzero, so the quartic
  `Y ^ 4 - t (t - 1)` is separable and the fibre is its four roots. The projection is therefore a
  covering map, as the root space of a separable family of polynomials.
* **The cyclic deck action.** The fourth roots of unity act by `y ↦ ζ y` over `U`, freely and
  transitively on each fibre, so the projection is the quotient covering by this action.
* **One sheet over `0` and over `1`.** Over the standard punctured disc `0 < |t| < 1/2`, the map
  `w ↦ (w ^ 4 / 2, c w (1 - w ^ 4 / 2) ^ (1/4))`, for a constant `c` with `c ^ 4 = -1/2`,
  parametrises the whole preimage by the punctured unit disc, so the preimage is path connected:
  the exponent `1` of `t` in the radicand is coprime to `4`. The substitution `t ↦ 1 - t` fixes
  the radicand and gives the same over `1`. Since the components of these preimages are the cycles
  of `σ0` and `σ1`, both are `4`-cycles.
* **At most two sheets over `∞`.** Over `|t| > 2` the radicand is `t ^ 2 (1 - 1/t)`, of order
  `-2` at `∞`, and `gcd(4, 2) = 2`: the preimage is covered by the two connected images of
  `v ↦ (2 / v ^ 2, ζ c v⁻¹ (1 - v ^ 2 / 2) ^ (1/4))` for `ζ = 1, i` and `c ^ 4 = 4`.
* **Connectedness and regularity.** A single cycle of `σ0` makes the monodromy transitive, so the
  cover is path connected. Its deck group is then the group of fourth roots of unity, of order the
  degree, and the monodromy triple is regular.
* **The torus triple.** In a regular triple a nontrivial element of the monodromy group has no
  fixed point, and `σinf` is even, being the inverse of the product of two `4`-cycles. So `σinf`
  is a product of two disjoint transpositions, the cycle data are `[4], [4], [2, 2]`, and these
  determine the torus triple among connected triples of degree four.

## Main declarations

* `TauCeti.ThricePuncturedSphere.superellipticCurve`: the points `(t, y)` with `t ∈ U` and
  `y ^ 4 = t (t - 1)`, with the projection `superellipticProj`.
* `TauCeti.ThricePuncturedSphere.isCoveringMap_superellipticProj`: the projection is a covering
  map.
* `TauCeti.ThricePuncturedSphere.isQuotientCoveringMap_superellipticProj`: it is the quotient
  covering by the fourth roots of unity, acting by `y ↦ ζ y`.
* `TauCeti.ThricePuncturedSphere.natCard_superellipticProj_preimage_singleton`: its fibres have
  four points.
* `isPathConnected_superellipticProj_preimage_puncturedNeighborhoodZero` and
  `isPathConnected_superellipticProj_preimage_puncturedNeighborhoodOne`: one sheet over each of
  the punctured discs about `0` and `1`.
* `TauCeti.ThricePuncturedSphere.superellipticCurve.instPathConnectedSpace`: the cover is path
  connected.
* `TauCeti.ThricePuncturedSphere.superellipticDeckMulEquiv`: its deck group is the group of
  fourth roots of unity, cyclic of order `4`.
* `TauCeti.ThricePuncturedSphere.isRegular_monodromyTriple_superellipticProj`: its monodromy
  triple is regular.
* `TauCeti.ThricePuncturedSphere.cycleData_monodromyTriple_superellipticProj`: its cycle data are
  `[4], [4], [2, 2]`.
* `TauCeti.ThricePuncturedSphere.isoClass_monodromyTriple_superellipticProj`: its monodromy
  triple is isomorphic to the torus triple.

## References

* O. Forster, *Lectures on Riemann Surfaces*, Graduate Texts in Mathematics 81, Springer, 1981,
  §8 (the Riemann surface of an algebraic function, whose unbranched part is the root space of a
  separable family).
* E. Girondo and G. González-Diez, *Introduction to Compact Riemann Surfaces and Dessins
  d'Enfants*, London Mathematical Society Student Texts 79, Cambridge University Press, 2012,
  §1.2.7 (one point of the compactification for each component over a puncture) and §2.7
  (monodromy, deck groups and regular covers).
-/

public section

noncomputable section

open Complex Equiv Equiv.Perm Metric MulAction Polynomial Set

namespace TauCeti

namespace ThricePuncturedSphere

/-! ### The cover and its projection -/

/-- The points of the **superelliptic curve** `y ^ 4 = t (t - 1)` lying over the thrice-punctured
sphere: the pairs `(t, y)` with `t ∈ ℂ ∖ {0, 1}` and `y ^ 4 = t (t - 1)`. -/
def superellipticCurve : Set (ThricePuncturedSphere × ℂ) :=
  {q | q.2 ^ 4 = (q.1 : ℂ) * (q.1 - 1)}

@[simp]
theorem mem_superellipticCurve {q : ThricePuncturedSphere × ℂ} :
    q ∈ superellipticCurve ↔ q.2 ^ 4 = (q.1 : ℂ) * (q.1 - 1) :=
  Iff.rfl

/-- The projection `(t, y) ↦ t` of the superelliptic curve to the thrice-punctured sphere. -/
def superellipticProj (q : superellipticCurve) : ThricePuncturedSphere :=
  (q : ThricePuncturedSphere × ℂ).1

@[simp]
theorem superellipticProj_apply (q : superellipticCurve) :
    superellipticProj q = (q : ThricePuncturedSphere × ℂ).1 :=
  (rfl)

/-- Over the thrice-punctured sphere the radicand `t (t - 1)` does not vanish. -/
private theorem mul_sub_one_ne_zero (t : ThricePuncturedSphere) : (t : ℂ) * (t - 1) ≠ 0 :=
  mul_ne_zero t.ne_zero (sub_ne_zero.2 t.ne_one)

/-- The `y`-coordinate of a point of the superelliptic curve over the thrice-punctured sphere is
nonzero. -/
theorem snd_ne_zero_of_mem_superellipticCurve {q : ThricePuncturedSphere × ℂ}
    (hq : q ∈ superellipticCurve) : q.2 ≠ 0 := fun h ↦
  mul_sub_one_ne_zero q.1 (by rw [← mem_superellipticCurve.1 hq, h, zero_pow four_ne_zero])

/-- **The superelliptic curve is a covering space of the thrice-punctured sphere.** It is the root
space of the family of quartics `Y ^ 4 - t (t - 1)`, which are separable because the radicand does
not vanish over `ℂ ∖ {0, 1}`. -/
theorem isCoveringMap_superellipticProj : IsCoveringMap superellipticProj := by
  have hF := Polynomial.isCoveringMap_fst_isRoot (B := ThricePuncturedSphere) (𝕜 := ℂ) (d := 4)
    (F := fun t ↦ X ^ 4 - C ((t : ℂ) * (t - 1)))
    (fun i _ ↦ by
      simp only [coeff_sub, coeff_X_pow, coeff_C]
      exact continuous_const.sub (.if_const _ (by fun_prop) continuous_const))
    (fun _ ↦ natDegree_X_pow_sub_C _)
    (fun t ↦ separable_X_pow_sub_C _ (by norm_num) (mul_sub_one_ne_zero t))
  exact hF.comp_homeomorph ((Homeomorph.refl _).subtype fun q ↦ by
    simp [sub_eq_zero])

/-! ### The action of the fourth roots of unity -/

/-- The fourth roots of unity act on the superelliptic curve by `y ↦ ζ y`, over the
thrice-punctured sphere. -/
instance superellipticCurve.instMulAction : MulAction (rootsOfUnity 4 ℂ) superellipticCurve where
  smul ζ q := ⟨((q : ThricePuncturedSphere × ℂ).1, ζ • (q : ThricePuncturedSphere × ℂ).2), by
    rw [mem_superellipticCurve, rootsOfUnity.smul_pow]
    exact q.2⟩
  one_smul q := Subtype.ext (Prod.ext rfl (one_smul _ _))
  mul_smul ζ η q := Subtype.ext (Prod.ext rfl (mul_smul ζ η _))

@[simp]
theorem coe_rootsOfUnity_smul_superellipticCurve (ζ : rootsOfUnity 4 ℂ) (q : superellipticCurve) :
    ((ζ • q : superellipticCurve) : ThricePuncturedSphere × ℂ) =
      ((q : ThricePuncturedSphere × ℂ).1, ζ • (q : ThricePuncturedSphere × ℂ).2) :=
  (rfl)

/-- Multiplication of the `y`-coordinate by a fourth root of unity is continuous. -/
instance superellipticCurve.instContinuousConstSMul :
    ContinuousConstSMul (rootsOfUnity 4 ℂ) superellipticCurve where
  continuous_const_smul ζ := by
    refine Continuous.subtype_mk ?_ _
    exact continuous_subtype_val.fst.prodMk ((continuous_const_smul ζ).comp
      continuous_subtype_val.snd)

/-- The fourth roots of unity act freely on the superelliptic curve, whose `y`-coordinates are
nonzero over the thrice-punctured sphere. -/
instance superellipticCurve.instIsCancelSMul :
    IsCancelSMul (rootsOfUnity 4 ℂ) superellipticCurve where
  right_cancel' ζ η q h := by
    have h' := congrArg (fun q : superellipticCurve ↦ (q : ThricePuncturedSphere × ℂ).2) h
    simp only [coe_rootsOfUnity_smul_superellipticCurve, rootsOfUnity.smul_eq_mul] at h'
    exact Subtype.ext <| Units.ext <|
      mul_right_cancel₀ (snd_ne_zero_of_mem_superellipticCurve q.2) h'

/-- **The superelliptic curve is the quotient covering by the fourth roots of unity.** Two points
lie over the same `t` exactly when their `y`-coordinates have the same fourth power, that is, when
they differ by a fourth root of unity. -/
theorem isQuotientCoveringMap_superellipticProj :
    IsQuotientCoveringMap superellipticProj (rootsOfUnity 4 ℂ) := by
  rw [isQuotientCoveringMap_iff_isCoveringMap_and]
  refine ⟨isCoveringMap_superellipticProj, fun t ↦ ?_, inferInstance, inferInstance,
    fun {q q'} ↦ ?_⟩
  · obtain ⟨y, hy⟩ := IsAlgClosed.exists_pow_nat_eq ((t : ℂ) * (t - 1)) four_pos
    exact ⟨⟨(t, y), hy⟩, rfl⟩
  · rw [mem_orbit_iff, superellipticProj_apply, superellipticProj_apply]
    refine ⟨fun h ↦ ?_, ?_⟩
    · have hpow :
          (q' : ThricePuncturedSphere × ℂ).2 ^ 4 = (q : ThricePuncturedSphere × ℂ).2 ^ 4 := by
        rw [mem_superellipticCurve.1 q.2, mem_superellipticCurve.1 q'.2, h]
      obtain ⟨ζ, hζ⟩ := (pow_eq_pow_iff_exists_rootsOfUnity_smul four_ne_zero).1 hpow
      exact ⟨ζ, Subtype.ext (Prod.ext h.symm hζ)⟩
    · rintro ⟨ζ, rfl⟩
      rfl

/-- **The superelliptic curve is a four-sheeted cover:** each fibre is a torsor under the fourth
roots of unity. -/
theorem natCard_superellipticProj_preimage_singleton (t : ThricePuncturedSphere) :
    Nat.card (superellipticProj ⁻¹' {t}) = 4 := by
  obtain ⟨q, rfl⟩ := isQuotientCoveringMap_superellipticProj.surjective t
  rw [Nat.card_congr (isQuotientCoveringMap_superellipticProj.fiberEquivGroup ⟨q, rfl⟩),
    Complex.card_rootsOfUnity]

/-! ### The sheets over the punctured discs about `0` and `1` -/

/-- A constant `c` with `c ^ 4 = -1/2`, used to parametrise the curve near `t = 0`. -/
private def localConst : ℂ :=
  (IsAlgClosed.exists_pow_nat_eq (-2⁻¹ : ℂ) four_pos).choose

private theorem localConst_pow_four : localConst ^ 4 = -2⁻¹ :=
  (IsAlgClosed.exists_pow_nat_eq (-2⁻¹ : ℂ) four_pos).choose_spec

/-- The fourth root `c w (1 - w ^ 4 / 2) ^ (1/4)` of `s (s - 1)` for `s = w ^ 4 / 2`. -/
private def localRoot (w : ℂ) : ℂ :=
  localConst * w * (1 - w ^ 4 / 2) ^ (4⁻¹ : ℂ)

private theorem localRoot_pow_four (w : ℂ) :
    localRoot w ^ 4 = w ^ 4 / 2 * (w ^ 4 / 2 - 1) := by
  rw [localRoot, mul_pow, mul_pow, cpow_ofNat_inv_pow, localConst_pow_four]
  ring

/-- For `w` in the unit disc and `k ≠ 0`, `w ^ k / 2` lies in the disc of radius `1/2`. -/
private theorem norm_pow_div_two_lt {w : ℂ} {k : ℕ} (hk : k ≠ 0) (hw : ‖w‖ < 1) :
    ‖w ^ k / 2‖ < 1 / 2 := by
  rw [norm_div, norm_pow, RCLike.norm_ofNat]
  have : ‖w‖ ^ k < 1 := pow_lt_one₀ (norm_nonneg w) hw hk
  linarith

/-- For `w` in the unit disc and `k ≠ 0`, `1 - w ^ k / 2` lies in the slit plane, where the
principal fourth root is continuous. -/
private theorem one_sub_pow_div_two_mem_slitPlane {w : ℂ} {k : ℕ} (hk : k ≠ 0) (hw : ‖w‖ < 1) :
    1 - w ^ k / 2 ∈ slitPlane := by
  rw [sub_eq_add_neg]
  exact mem_slitPlane_of_norm_lt_one (by linarith [norm_neg (w ^ k / 2), norm_pow_div_two_lt hk hw])

private theorem continuousOn_localRoot : ContinuousOn localRoot (ball (0 : ℂ) 1) := fun w hw ↦ by
  have h : ContinuousAt (fun w : ℂ ↦ (1 - w ^ 4 / 2) ^ (4⁻¹ : ℂ)) w :=
    (continuousAt_cpow_const (one_sub_pow_div_two_mem_slitPlane four_ne_zero
      (mem_ball_zero_iff.1 hw))).comp (f := fun w : ℂ ↦ 1 - w ^ 4 / 2) (by fun_prop)
  refine ContinuousAt.continuousWithinAt ?_
  unfold localRoot
  exact (continuousAt_const.mul continuousAt_id).mul h

private theorem pow_four_div_two_ne_zero {w : ℂ} (hw : w ≠ 0) : w ^ 4 / 2 ≠ 0 :=
  div_ne_zero (pow_ne_zero 4 hw) two_ne_zero

private theorem ne_one_of_norm_lt {s : ℂ} (hs : ‖s‖ < 1 / 2) : s ≠ 1 := by
  rintro rfl
  norm_num at hs

/-- Every point `(s, y)` of the curve with `0 < |s| < 1/2` is `(w ^ 4 / 2, localRoot w)` for some
`w` in the punctured unit disc. -/
private theorem exists_eq_localRoot {s y : ℂ} (hs0 : s ≠ 0) (hs : ‖s‖ < 1 / 2)
    (hy : y ^ 4 = s * (s - 1)) :
    ∃ w ∈ ball (0 : ℂ) 1 \ {0}, w ^ 4 / 2 = s ∧ localRoot w = y := by
  set r := (1 - s) ^ (4⁻¹ : ℂ)
  have hr4 : r ^ 4 = 1 - s := cpow_ofNat_inv_pow _ _
  have hr : r ≠ 0 := fun h ↦ by
    rw [h, zero_pow four_ne_zero, eq_comm, sub_eq_zero] at hr4
    exact ne_one_of_norm_lt hs hr4.symm
  have hc : localConst ≠ 0 := fun h ↦ by
    have := localConst_pow_four
    rw [h, zero_pow four_ne_zero] at this
    norm_num at this
  set w := y / (localConst * r)
  have hw4 : w ^ 4 / 2 = s := by
    have h1s : 1 - s ≠ 0 := sub_ne_zero.2 (ne_one_of_norm_lt hs).symm
    rw [div_pow, mul_pow, hy, hr4, localConst_pow_four]
    field_simp
    ring
  have hw0 : w ≠ 0 := fun h ↦ hs0 (by rw [← hw4, h]; norm_num)
  have hw1 : ‖w‖ < 1 := by
    have h : ‖w‖ ^ 4 = 2 * ‖s‖ := by
      rw [← norm_pow, ← hw4]
      simp only [norm_div, RCLike.norm_ofNat]
      ring
    by_contra hge
    have : 1 ≤ ‖w‖ ^ 4 := one_le_pow₀ (not_lt.1 hge)
    linarith
  have hwy : localConst * w * r = y := by
    simp only [w]
    field_simp
  refine ⟨w, ⟨mem_ball_zero_iff.2 hw1, hw0⟩, hw4, ?_⟩
  rw [localRoot, hw4]
  exact hwy

/-- The point `(w ^ 4 / 2, localRoot w)` of the curve over the punctured disc about `0`. -/
private def chartZero (w : ↥(ball (0 : ℂ) 1 \ {0})) : superellipticCurve :=
  ⟨(⟨(w : ℂ) ^ 4 / 2, pow_four_div_two_ne_zero w.2.2,
      ne_one_of_norm_lt (norm_pow_div_two_lt four_ne_zero (mem_ball_zero_iff.1 w.2.1))⟩,
    localRoot w), localRoot_pow_four w⟩

/-- The point `(1 - w ^ 4 / 2, localRoot w)` of the curve over the punctured disc about `1`, the
image of `chartZero w` under `t ↦ 1 - t`, which fixes the radicand `t (t - 1)`. -/
private def chartOne (w : ↥(ball (0 : ℂ) 1 \ {0})) : superellipticCurve :=
  ⟨(⟨1 - (w : ℂ) ^ 4 / 2,
      sub_ne_zero.2
        (ne_one_of_norm_lt (norm_pow_div_two_lt four_ne_zero (mem_ball_zero_iff.1 w.2.1))).symm,
      by simpa using pow_four_div_two_ne_zero w.2.2⟩,
    localRoot w), by
      rw [mem_superellipticCurve, localRoot_pow_four]
      ring⟩

private theorem continuous_localRoot_comp :
    Continuous fun w : ↥(ball (0 : ℂ) 1 \ {0}) ↦ localRoot w :=
  continuousOn_localRoot.comp_continuous continuous_subtype_val fun w ↦ w.2.1

private theorem continuous_chartZero : Continuous chartZero :=
  ((Continuous.subtype_mk (by fun_prop) _).prodMk continuous_localRoot_comp).subtype_mk _

private theorem continuous_chartOne : Continuous chartOne :=
  ((Continuous.subtype_mk (by fun_prop) _).prodMk continuous_localRoot_comp).subtype_mk _

/-- The image of the punctured unit disc under a continuous map is path connected. -/
private theorem isPathConnected_range_of_puncturedDisc {X : Type*} [TopologicalSpace X]
    {f : ↥(ball (0 : ℂ) 1 \ {0}) → X} (hf : Continuous f) : IsPathConnected (range f) :=
  have := isPathConnected_iff_pathConnectedSpace.1
    (isPathConnected_ball_sdiff_singleton (by simp [Complex.rank_real_complex]) (0 : ℂ) one_pos)
  isPathConnected_range hf

private theorem range_chartZero :
    range chartZero = superellipticProj ⁻¹' puncturedNeighborhoodZero := by
  ext q
  refine ⟨?_, fun hq ↦ ?_⟩
  · rintro ⟨w, rfl⟩
    rw [mem_preimage, mem_puncturedNeighborhoodZero]
    exact norm_pow_div_two_lt four_ne_zero (mem_ball_zero_iff.1 w.2.1)
  · rw [mem_preimage, mem_puncturedNeighborhoodZero] at hq
    obtain ⟨⟨t, y⟩, hq'⟩ := q
    obtain ⟨w, hw, hwt, hwy⟩ := exists_eq_localRoot t.ne_zero hq hq'
    exact ⟨⟨w, hw⟩, Subtype.ext (Prod.ext (Subtype.ext hwt) hwy)⟩

private theorem range_chartOne :
    range chartOne = superellipticProj ⁻¹' puncturedNeighborhoodOne := by
  ext q
  refine ⟨?_, fun hq ↦ ?_⟩
  · rintro ⟨w, rfl⟩
    have := norm_pow_div_two_lt four_ne_zero (mem_ball_zero_iff.1 w.2.1)
    rw [mem_preimage, mem_puncturedNeighborhoodOne]
    simpa [chartOne, norm_neg] using this
  · rw [mem_preimage, mem_puncturedNeighborhoodOne] at hq
    obtain ⟨⟨t, y⟩, hq'⟩ := q
    have hs : ‖1 - (t : ℂ)‖ < 1 / 2 := by
      rw [norm_sub_rev]
      exact hq
    obtain ⟨w, hw, hwt, hwy⟩ := exists_eq_localRoot (sub_ne_zero.2 t.ne_one.symm) hs
      (by rw [mem_superellipticCurve] at hq'; rw [hq']; ring)
    exact ⟨⟨w, hw⟩, Subtype.ext (Prod.ext (Subtype.ext (by simp [chartOne, hwt])) hwy)⟩

/-- **The superelliptic curve has one sheet over the punctured disc about `0`:** the preimage of
`0 < |t| < 1/2` is path connected, being parametrised by `w ↦ (w ^ 4 / 2, c w (1 - w ^ 4 / 2) ^
(1/4))` on the punctured unit disc. -/
theorem isPathConnected_superellipticProj_preimage_puncturedNeighborhoodZero :
    IsPathConnected (superellipticProj ⁻¹' puncturedNeighborhoodZero) :=
  range_chartZero ▸ isPathConnected_range_of_puncturedDisc continuous_chartZero

/-- **The superelliptic curve has one sheet over the punctured disc about `1`:** the preimage of
`0 < |t - 1| < 1/2` is path connected. -/
theorem isPathConnected_superellipticProj_preimage_puncturedNeighborhoodOne :
    IsPathConnected (superellipticProj ⁻¹' puncturedNeighborhoodOne) :=
  range_chartOne ▸ isPathConnected_range_of_puncturedDisc continuous_chartOne

/-- If the cycles of `σ` are the components of a path-connected set, then `σ` has a single
cycle. -/
private theorem sameCycle_of_isPathConnected {X : Type*} [TopologicalSpace X] {S : Set X}
    {n : ℕ} {σ : Perm (Fin n)} (e : Quotient (SameCycle.setoid σ) ≃ ConnectedComponents S)
    (hS : IsPathConnected S) (i j : Fin n) : σ.SameCycle i j :=
  have := isPathConnected_iff_pathConnectedSpace.1 hS
  Quotient.exact (e.injective (Subsingleton.elim _ _))

variable {n : ℕ} (ν : superellipticProj ⁻¹' {basePt} ≃ Fin n)

/-- The monodromy at `0` of the superelliptic curve is a single cycle, since the components of the
preimage of the punctured disc about `0` are the cycles of `σ0`. -/
private theorem sameCycle_monodromyTriple_superellipticProj_σ0 (i j : Fin n) :
    (isCoveringMap_superellipticProj.monodromyTriple ν).σ0.SameCycle i j :=
  sameCycle_of_isPathConnected
    (isCoveringMap_superellipticProj.sameCycleQuotientσ0EquivConnectedComponents ν)
    isPathConnected_superellipticProj_preimage_puncturedNeighborhoodZero i j

/-- The monodromy at `1` of the superelliptic curve is a single cycle, since the components of the
preimage of the punctured disc about `1` are the cycles of `σ1`. -/
private theorem sameCycle_monodromyTriple_superellipticProj_σ1 (i j : Fin n) :
    (isCoveringMap_superellipticProj.monodromyTriple ν).σ1.SameCycle i j :=
  sameCycle_of_isPathConnected
    (isCoveringMap_superellipticProj.sameCycleQuotientσ1EquivConnectedComponents ν)
    isPathConnected_superellipticProj_preimage_puncturedNeighborhoodOne i j

/-! ### At most two sheets over the punctured neighbourhood of `∞` -/

/-- A constant `c` with `c ^ 4 = 4`, used to parametrise the curve near `t = ∞`. -/
private def localConstInf : ℂ :=
  (IsAlgClosed.exists_pow_nat_eq (4 : ℂ) four_pos).choose

private theorem localConstInf_pow_four : localConstInf ^ 4 = 4 :=
  (IsAlgClosed.exists_pow_nat_eq (4 : ℂ) four_pos).choose_spec

/-- The fourth root `c v⁻¹ (1 - v ^ 2 / 2) ^ (1/4)` of `s (s - 1)` for `s = 2 / v ^ 2`. -/
private def localRootInf (v : ℂ) : ℂ :=
  localConstInf * v⁻¹ * (1 - v ^ 2 / 2) ^ (4⁻¹ : ℂ)

private theorem localRootInf_pow_four {v : ℂ} (hv : v ≠ 0) :
    localRootInf v ^ 4 = 2 / v ^ 2 * (2 / v ^ 2 - 1) := by
  rw [localRootInf, mul_pow, mul_pow, cpow_ofNat_inv_pow, localConstInf_pow_four]
  field_simp
  ring

private theorem localRootInf_neg (v : ℂ) : localRootInf (-v) = -localRootInf v := by
  simp only [localRootInf, inv_neg, neg_sq]
  ring

private theorem continuousOn_localRootInf :
    ContinuousOn localRootInf (ball (0 : ℂ) 1 \ {0}) := fun v hv ↦ by
  have h : ContinuousAt (fun v : ℂ ↦ (1 - v ^ 2 / 2) ^ (4⁻¹ : ℂ)) v :=
    (continuousAt_cpow_const (one_sub_pow_div_two_mem_slitPlane two_ne_zero
      (mem_ball_zero_iff.1 hv.1))).comp (f := fun v : ℂ ↦ 1 - v ^ 2 / 2) (by fun_prop)
  refine ContinuousAt.continuousWithinAt ?_
  unfold localRootInf
  exact (continuousAt_const.mul (continuousAt_inv₀ hv.2)).mul h

/-- For `v` in the punctured unit disc, `2 / v ^ 2` lies outside the closed disc of radius `2`. -/
private theorem two_lt_norm_two_div_sq {v : ℂ} (hv0 : v ≠ 0) (hv : ‖v‖ < 1) :
    2 < ‖2 / v ^ 2‖ := by
  rw [norm_div, norm_pow, RCLike.norm_ofNat, lt_div_iff₀ (by positivity)]
  have : ‖v‖ ^ 2 < 1 := pow_lt_one₀ (norm_nonneg v) hv two_ne_zero
  linarith

private theorem two_div_sq_ne_one {v : ℂ} (hv0 : v ≠ 0) (hv : ‖v‖ < 1) : 2 / v ^ 2 ≠ 1 := by
  intro h
  have := two_lt_norm_two_div_sq hv0 hv
  rw [h, norm_one] at this
  norm_num at this

/-- The multiplier `1` or `i` distinguishing the two charts over the neighbourhood of `∞`. -/
private def chartInfMul (b : Bool) : ℂ :=
  bif b then I else 1

private theorem chartInfMul_pow_four (b : Bool) : chartInfMul b ^ 4 = 1 := by
  cases b <;> simp [chartInfMul, I_pow_four]

/-- The point `(2 / v ^ 2, ζ localRootInf v)` of the curve over the punctured neighbourhood of
`∞`, for `ζ = 1` or `ζ = i`. -/
private def chartInf (b : Bool) (v : ↥(ball (0 : ℂ) 1 \ {0})) :
    ↥(superellipticProj ⁻¹' puncturedNeighborhoodInf) :=
  ⟨⟨(⟨2 / (v : ℂ) ^ 2, div_ne_zero two_ne_zero (pow_ne_zero 2 v.2.2),
      two_div_sq_ne_one v.2.2 (mem_ball_zero_iff.1 v.2.1)⟩, chartInfMul b * localRootInf v), by
    rw [mem_superellipticCurve, mul_pow, chartInfMul_pow_four, one_mul,
      localRootInf_pow_four v.2.2]⟩,
    by
      rw [mem_preimage, mem_puncturedNeighborhoodInf]
      exact two_lt_norm_two_div_sq v.2.2 (mem_ball_zero_iff.1 v.2.1)⟩

private theorem continuous_chartInf (b : Bool) : Continuous (chartInf b) :=
  (((Continuous.subtype_mk (continuous_const.div (by fun_prop) fun v ↦ pow_ne_zero 2 v.2.2)
    _).prodMk (continuous_const.mul
    (continuousOn_localRootInf.comp_continuous continuous_subtype_val fun v ↦ v.2))).subtype_mk
      _).subtype_mk _

/-- Every point `(s, y)` of the curve with `2 < |s|` is `(2 / v ^ 2, ζ localRootInf v)` for some
`v` in the punctured unit disc and `ζ = 1` or `ζ = i`: the other two fourth roots of unity are
absorbed by `v ↦ -v`. -/
private theorem exists_eq_localRootInf {s y : ℂ} (hs : 2 < ‖s‖) (hy : y ^ 4 = s * (s - 1)) :
    ∃ b : Bool, ∃ v ∈ ball (0 : ℂ) 1 \ {0}, 2 / v ^ 2 = s ∧ chartInfMul b * localRootInf v = y := by
  have hs0 : s ≠ 0 := norm_pos_iff.1 (by linarith)
  have hs1 : s ≠ 1 := by
    rintro rfl
    norm_num at hs
  obtain ⟨v, hv⟩ := IsAlgClosed.exists_pow_nat_eq (2 / s) two_pos
  have hv0 : v ≠ 0 := by
    rintro rfl
    rw [zero_pow two_ne_zero, eq_comm] at hv
    exact div_ne_zero two_ne_zero hs0 hv
  have hvs : 2 / v ^ 2 = s := by
    rw [hv]
    field_simp
  have hv1 : ‖v‖ < 1 := by
    have h : ‖v‖ ^ 2 * ‖s‖ = 2 := by
      rw [← norm_pow, hv, norm_div, RCLike.norm_ofNat]
      field_simp
    by_contra hge
    have : 1 ≤ ‖v‖ ^ 2 := one_le_pow₀ (not_lt.1 hge)
    nlinarith
  have hY4 : localRootInf v ^ 4 = y ^ 4 := by
    rw [localRootInf_pow_four hv0, hvs, hy]
  have hY : localRootInf v ≠ 0 := fun h ↦ by
    rw [h, zero_pow four_ne_zero, eq_comm, hy] at hY4
    exact mul_ne_zero hs0 (sub_ne_zero.2 hs1) hY4
  -- `y = ζ Y` for a fourth root of unity `ζ`, which is `1`, `-1`, `i` or `-i`
  set ζ := y / localRootInf v
  have hζy : ζ * localRootInf v = y := div_mul_cancel₀ y hY
  have hζ : (ζ - 1) * (ζ + 1) * (ζ - I) * (ζ + I) = 0 := by
    have h4 : ζ ^ 4 = 1 := by rw [div_pow, ← hY4, div_self (pow_ne_zero 4 hY)]
    linear_combination h4 - (ζ ^ 2 - 1) * I_sq
  have hv' : -v ∈ ball (0 : ℂ) 1 \ {0} := ⟨by simpa using hv1, neg_ne_zero.2 hv0⟩
  have hvs' : 2 / (-v) ^ 2 = s := by rwa [neg_sq]
  rcases mul_eq_zero.1 hζ with hζ | hζ
  · rcases mul_eq_zero.1 hζ with hζ | hζ
    · rcases mul_eq_zero.1 hζ with hζ | hζ
      · refine ⟨false, v, ⟨mem_ball_zero_iff.2 hv1, hv0⟩, hvs, ?_⟩
        rw [← hζy, sub_eq_zero.1 hζ, chartInfMul, Bool.cond_false]
      · refine ⟨false, -v, hv', hvs', ?_⟩
        rw [← hζy, eq_neg_of_add_eq_zero_left hζ, chartInfMul, Bool.cond_false, localRootInf_neg]
        ring
    · refine ⟨true, v, ⟨mem_ball_zero_iff.2 hv1, hv0⟩, hvs, ?_⟩
      rw [← hζy, sub_eq_zero.1 hζ, chartInfMul, Bool.cond_true]
  · refine ⟨true, -v, hv', hvs', ?_⟩
    rw [← hζy, eq_neg_of_add_eq_zero_left hζ, chartInfMul, Bool.cond_true, localRootInf_neg]
    ring

/-- **The superelliptic curve has at most two sheets over the punctured neighbourhood of `∞`:**
the preimage of `|t| > 2` is covered by the images of the two charts, each of which is connected. -/
private theorem natCard_connectedComponents_preimage_puncturedNeighborhoodInf_le :
    Nat.card (ConnectedComponents (superellipticProj ⁻¹' puncturedNeighborhoodInf)) ≤ 2 := by
  let v₀ : ↥(ball (0 : ℂ) 1 \ {0}) := ⟨1 / 2, by norm_num [mem_ball_zero_iff]⟩
  have hsurj : Function.Surjective fun b : Bool ↦ (ConnectedComponents.mk (chartInf b v₀)) := by
    intro c
    obtain ⟨⟨⟨⟨t, y⟩, hq⟩, ht⟩, rfl⟩ := ConnectedComponents.surjective_coe c
    have ht' := ht
    rw [mem_preimage, mem_puncturedNeighborhoodInf] at ht'
    obtain ⟨b, v, hv, hvt, hvy⟩ := exists_eq_localRootInf ht' hq
    refine ⟨b, ConnectedComponents.coe_eq_coe'.2 ?_⟩
    have hx : chartInf b ⟨v, hv⟩ = ⟨⟨(t, y), hq⟩, ht⟩ :=
      Subtype.ext (Subtype.ext (Prod.ext (Subtype.ext hvt) hvy))
    rw [← hx]
    exact (isPathConnected_range_of_puncturedDisc (continuous_chartInf b)).isConnected
      |>.isPreconnected.subset_connectedComponent
      (mem_range_self _) (mem_range_self _)
  simpa using Nat.card_le_card_of_surjective _ hsurj

/-- The monodromy at `∞` of the superelliptic curve has at most two cycles. -/
private theorem orbitCount_monodromyTriple_superellipticProj_σinf_le :
    orbitCount (isCoveringMap_superellipticProj.monodromyTriple ν).σinf ≤ 2 := by
  rw [orbitCount_def, Nat.card_congr
    (isCoveringMap_superellipticProj.sameCycleQuotientσinfEquivConnectedComponents ν)]
  exact natCard_connectedComponents_preimage_puncturedNeighborhoodInf_le

include ν in
/-- A numbering of a fibre of the superelliptic curve uses four labels. -/
private theorem eq_four_of_superellipticProj_preimage_equiv : n = 4 := by
  rw [← Nat.card_fin n, ← Nat.card_congr ν, natCard_superellipticProj_preimage_singleton]

/-! ### Connectedness, the deck group and regularity -/

/-- **The monodromy triple of the superelliptic curve is connected:** its monodromy group already
contains the single cycle `σ0`. -/
theorem isConnected_monodromyTriple_superellipticProj :
    (isCoveringMap_superellipticProj.monodromyTriple ν).IsConnected := by
  set t := isCoveringMap_superellipticProj.monodromyTriple ν
  refine PermutationTriple.isConnected_iff.2
    ⟨by rw [eq_four_of_superellipticProj_preimage_equiv ν]; norm_num, ⟨fun i j ↦ ?_⟩⟩
  obtain ⟨k, hk⟩ := sameCycle_monodromyTriple_superellipticProj_σ0 ν i j
  exact ⟨⟨t.σ0 ^ k, zpow_mem t.σ0_mem_monodromyGroup k⟩, hk⟩

/-- **The superelliptic curve over the thrice-punctured sphere is path connected.** -/
instance superellipticCurve.instPathConnectedSpace : PathConnectedSpace superellipticCurve := by
  have : Finite (superellipticProj ⁻¹' {basePt}) :=
    Nat.finite_of_card_ne_zero (by rw [natCard_superellipticProj_preimage_singleton]; norm_num)
  let ν := Finite.equivFinOfCardEq (natCard_superellipticProj_preimage_singleton basePt)
  exact (isCoveringMap_superellipticProj.isConnected_monodromyTriple_iff ν).1
    (isConnected_monodromyTriple_superellipticProj ν)

/-- **The deck group of the superelliptic curve is the group of fourth roots of unity**, acting by
`y ↦ ζ y` (`superellipticDeckMulEquiv_apply`). -/
def superellipticDeckMulEquiv : rootsOfUnity 4 ℂ ≃* deck superellipticProj :=
  Deck.IsQuotientCoveringMap.deckMulEquiv isQuotientCoveringMap_superellipticProj

@[simp]
theorem superellipticDeckMulEquiv_apply (ζ : rootsOfUnity 4 ℂ) (q : superellipticCurve) :
    (superellipticDeckMulEquiv ζ).1 q = ζ • q :=
  Deck.IsQuotientCoveringMap.deckMulEquiv_apply _ ζ q

/-- The deck group of the superelliptic curve is cyclic. -/
instance isCyclic_deck_superellipticProj : IsCyclic (deck superellipticProj) :=
  isCyclic_of_surjective superellipticDeckMulEquiv superellipticDeckMulEquiv.surjective

/-- The deck group of the superelliptic curve has order `4`. -/
theorem natCard_deck_superellipticProj : Nat.card (deck superellipticProj) = 4 := by
  rw [← Nat.card_congr superellipticDeckMulEquiv.toEquiv, Complex.card_rootsOfUnity]

/-- **The superelliptic curve is a regular cover:** its monodromy triple is regular, its
automorphism group being the deck group, of order the degree `4`. -/
theorem isRegular_monodromyTriple_superellipticProj :
    (isCoveringMap_superellipticProj.monodromyTriple ν).IsRegular := by
  rw [PermutationTriple.isRegular_iff_card_automorphismGroup]
  refine ⟨isConnected_monodromyTriple_superellipticProj ν, ?_⟩
  rw [← Nat.card_congr (isCoveringMap_superellipticProj.deckMulEquivAutomorphismGroup ν).toEquiv,
    natCard_deck_superellipticProj, eq_four_of_superellipticProj_preimage_equiv ν]

/-! ### The monodromy triple is the torus triple -/

/-- A `4`-cycle is an odd permutation. -/
private theorem sign_eq_neg_one_of_fullCycleType_eq_four {σ : Perm (Fin 4)}
    (h : fullCycleType σ = {4}) : sign σ = -1 := by
  rw [sign_of_cycleType, ← filter_fullCycleType_eq_cycleType, h]
  decide

/-- A fixed-point-free permutation of four points with at most two cycles, other than a `4`-cycle,
is a product of two disjoint transpositions. -/
private theorem fullCycleType_eq_two_two {σ : Perm (Fin 4)} (hle : orbitCount σ ≤ 2)
    (hsupp : σ.support = Finset.univ) (h4 : fullCycleType σ ≠ {4}) :
    fullCycleType σ = {2, 2} := by
  have hsum := sum_fullCycleType σ
  have hcount := count_one_fullCycleType σ
  rw [Fintype.card_fin] at hsum
  rw [hsupp, Finset.card_univ, Fintype.card_fin, Nat.sub_self] at hcount
  rw [orbitCount_eq_card_parts_partition, ← fullCycleType_def] at hle
  interval_cases hcard : Multiset.card (fullCycleType σ)
  · rw [Multiset.card_eq_zero.1 hcard, Multiset.sum_zero] at hsum
    norm_num at hsum
  · obtain ⟨a, ha⟩ := Multiset.card_eq_one.1 hcard
    rw [ha, Multiset.sum_singleton] at hsum
    exact absurd (ha.trans (by rw [hsum])) h4
  · obtain ⟨a, b, hab⟩ := Multiset.card_eq_two.1 hcard
    have ha := pos_of_mem_fullCycleType (σ := σ) (n := a) (by simp [hab])
    have hb := pos_of_mem_fullCycleType (σ := σ) (n := b) (by simp [hab])
    rw [hab, Multiset.insert_eq_cons, Multiset.sum_cons, Multiset.sum_singleton] at hsum
    rw [hab, Multiset.insert_eq_cons, Multiset.count_cons, Multiset.count_singleton] at hcount
    have ha1 : a ≠ 1 := fun h ↦ by simp [h] at hcount
    have hb1 : b ≠ 1 := fun h ↦ by simp [h] at hcount
    obtain ⟨rfl, rfl⟩ : a = 2 ∧ b = 2 := by omega
    exact hab

/-- **The cycle data of the superelliptic curve are `[4], [4], [2, 2]`.** Over `0` and `1` there is
one sheet, so `σ0` and `σ1` are `4`-cycles. Over `∞` there are at most two sheets, so `σinf` is not
the identity, and in a regular triple a nontrivial monodromy element has no fixed point. Finally
`σinf` is not a `4`-cycle, which would be odd while `σinf⁻¹ = σ1 σ0` is even. -/
theorem cycleData_monodromyTriple_superellipticProj :
    (isCoveringMap_superellipticProj.monodromyTriple ν).cycleData = ({4}, {4}, {2, 2}) := by
  obtain rfl := eq_four_of_superellipticProj_preimage_equiv ν
  set t := isCoveringMap_superellipticProj.monodromyTriple ν
  have h0 : fullCycleType t.σ0 = {4} :=
    (fullCycleType_of_forall_sameCycle _ (sameCycle_monodromyTriple_superellipticProj_σ0 ν 0)).trans
      (by rw [Fintype.card_fin])
  have h1 : fullCycleType t.σ1 = {4} :=
    (fullCycleType_of_forall_sameCycle _ (sameCycle_monodromyTriple_superellipticProj_σ1 ν 0)).trans
      (by rw [Fintype.card_fin])
  have hle : orbitCount t.σinf ≤ 2 := orbitCount_monodromyTriple_superellipticProj_σinf_le ν
  -- `σinf` moves every point: it is not the identity, which has four cycles, and the monodromy
  -- group of a regular triple acts freely
  have hsupp : t.σinf.support = Finset.univ := by
    have hne : t.σinf ≠ 1 := fun h ↦ by
      rw [h, orbitCount_one, Nat.card_fin] at hle
      norm_num at hle
    have := (isRegular_monodromyTriple_superellipticProj ν).isCancelSMul
    refine Finset.eq_univ_of_forall fun i ↦ mem_support.2 fun hi ↦ hne ?_
    have hg : (⟨t.σinf, t.σinf_mem_monodromyGroup⟩ : t.monodromyGroup) • i =
        (1 : t.monodromyGroup) • i := hi
    exact congrArg Subtype.val (IsCancelSMul.right_cancel _ _ i hg)
  -- `σinf` is even, so it is not a `4`-cycle
  have h4 : fullCycleType t.σinf ≠ {4} := fun h ↦ by
    have hsign := congrArg sign t.σ1_mul_σ0_eq_σinf_inv
    rw [map_mul, map_inv, sign_eq_neg_one_of_fullCycleType_eq_four h0,
      sign_eq_neg_one_of_fullCycleType_eq_four h1,
      sign_eq_neg_one_of_fullCycleType_eq_four h] at hsign
    exact absurd hsign (by decide)
  rw [Prod.ext_iff, Prod.ext_iff, PermutationTriple.cycleData_σ0, PermutationTriple.cycleData_σ1,
    PermutationTriple.cycleData_σinf, ← fullCycleType_def, ← fullCycleType_def,
    ← fullCycleType_def]
  exact ⟨h0, h1, fullCycleType_eq_two_two hle hsupp h4⟩

/-- **The monodromy triple of the superelliptic curve is the Euclidean torus triple**, up to
relabelling: both are connected of degree four with cycle data `[4], [4], [2, 2]`, which classify
connected triples in degree four. -/
theorem isoClass_monodromyTriple_superellipticProj (ν : superellipticProj ⁻¹' {basePt} ≃ Fin 4) :
    PermutationTriple.IsoClass.mk (isCoveringMap_superellipticProj.monodromyTriple ν) =
      PermutationTriple.IsoClass.mk PermutationTriple.torusTriple := by
  rw [PermutationTriple.IsoClass.mk_eq_mk_iff]
  refine (PermutationTriple.equivalent_iff_cycleData_eq_of_degree_le_four le_rfl
    ⟨_, isConnected_monodromyTriple_superellipticProj ν⟩
    ⟨_, PermutationTriple.isConnected_torusTriple⟩).2 ?_
  rw [cycleData_monodromyTriple_superellipticProj, PermutationTriple.cycleData_torusTriple]

end ThricePuncturedSphere

end TauCeti
