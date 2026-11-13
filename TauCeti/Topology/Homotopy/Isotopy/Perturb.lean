/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Affine.AddTorsor
public import Mathlib.Topology.MetricSpace.Contracting
public import TauCeti.Topology.Homotopy.Isotopy.Restrict

/-!
# Contracting perturbations of the identity are ambient isotopies

Let `P` be a complete real normed affine space with space of translations `V`, and let
`u : P → V` be a displacement field which is Lipschitz with constant `c < 1`. Moving every point
along the straight line `x ↦ t • u x +ᵥ x`, for `t ∈ [0, 1]`, is an ambient isotopy of `P`
(`TauCeti.AmbientIsotopy.perturb`). Its time-`t` map is bi-Lipschitz, with

`(1 - c) * dist x y ≤ dist (t • u x +ᵥ x) (t • u y +ᵥ y) ≤ (1 + c) * dist x y`,

and it fixes every point at which `u` vanishes. So when `u` vanishes outside a set `s`, every time
slice preserves `s`, and the isotopy restricts to an ambient isotopy of `s`
(`TauCeti.AmbientIsotopy.perturb_apply_mem_iff`, the hypothesis of
`TauCeti.AmbientIsotopy.restrict`).

The inverse of the time-`t` map sends `y` to the unique fixed point of the contraction
`x ↦ -(t • u x) +ᵥ y`, which exists by the Banach fixed-point theorem
(`ContractingWith.fixedPoint`). The lower Lipschitz bound, applied at two different times, shows
that this inverse is jointly continuous in the time and the point: if `t • u a +ᵥ a = y` and
`s • u b +ᵥ b = z`, then `(1 - c) * dist a b ≤ |s - t| * ‖u a‖ + dist y z`. Hence the
level-preserving total map is a homeomorphism of `[0, 1] × P`.

For a single time slice of a perturbation of the identity of a normed space this is the global
Lipschitz inverse function theorem, Mathlib's `ApproximatesLinearOn.toHomeomorph` applied to the
identity; the point here is the affine setting and the continuity in time. Ambient isotopies of
this form move a polygonal knot by small displacements of its vertices: interpolating the vertex
displacements over a triangulation gives a Lipschitz field with a small constant.

## Main definitions

* `TauCeti.AmbientIsotopy.perturb`: the ambient isotopy `(t, x) ↦ t • u x +ᵥ x`.

## Main results

* `TauCeti.AmbientIsotopy.perturb_apply`: the formula of the isotopy.
* `TauCeti.AmbientIsotopy.lipschitzWith_perturb_apply` and
  `TauCeti.AmbientIsotopy.antilipschitzWith_perturb_apply`: the time slices are
  `(1 + c)`-Lipschitz and `(1 - c)⁻¹`-antilipschitz.
* `TauCeti.AmbientIsotopy.lipschitzWith_perturb_symm_apply`: the inverse time slices are
  `(1 - c)⁻¹`-Lipschitz.
* `TauCeti.AmbientIsotopy.perturb_symm_apply`: the inverse time slice at `y` is the fixed point of
  `x ↦ -(t • u x) +ᵥ y`.
* `TauCeti.AmbientIsotopy.dist_perturb_apply`: the point `x` moves by `t * ‖u x‖`.
* `TauCeti.AmbientIsotopy.perturb_apply_of_eq_zero` and
  `TauCeti.AmbientIsotopy.perturb_apply_mem_iff`: the isotopy fixes the zeros of `u`, and
  preserves every set outside which `u` vanishes.
* `TauCeti.AmbientIsotopy.perturb_zero`: the zero field gives the constant isotopy.

## References

* S. Banach, *Sur les opérations dans les ensembles abstraits et leur application aux équations
  intégrales*, Fund. Math. 3 (1922), for the contraction principle.
* G. Burde, H. Zieschang, *Knots*, 2nd ed., De Gruyter Studies in Mathematics 5 (2003),
  Chapter 1 §B, for moving polygonal knots by ambient isotopies.
-/

public section

noncomputable section

open unitInterval NNReal

namespace TauCeti

namespace AmbientIsotopy

variable {V P : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [MetricSpace P]
  [NormedAddTorsor V P] {u : P → V} {c : ℝ≥0}

/-- The difference of two displaced points, at the same time `s`. -/
private theorem smul_vadd_vsub_smul_vadd (s : ℝ) (x y : P) :
    (s • u x +ᵥ x) -ᵥ (s • u y +ᵥ y) = s • (u x - u y) + (x -ᵥ y) := by
  rw [vadd_vsub_vadd_comm, smul_sub]

omit [NormedAddTorsor V P] in
/-- At a time `s ∈ [0, 1]`, two displacements differ by at most `c` times the distance. -/
private theorem norm_smul_sub_le (hu : LipschitzWith c u) {s : ℝ} (hs₀ : 0 ≤ s) (hs₁ : s ≤ 1)
    (x y : P) : ‖s • (u x - u y)‖ ≤ c * dist x y := by
  rw [norm_smul, Real.norm_of_nonneg hs₀, ← dist_eq_norm]
  calc s * dist (u x) (u y) ≤ 1 * (c * dist x y) :=
        mul_le_mul hs₁ (hu.dist_le_mul x y) dist_nonneg zero_le_one
    _ = c * dist x y := one_mul _

/-- The upper Lipschitz bound of a time slice. -/
private theorem dist_smul_vadd_le (hu : LipschitzWith c u) {s : ℝ} (hs₀ : 0 ≤ s) (hs₁ : s ≤ 1)
    (x y : P) : dist (s • u x +ᵥ x) (s • u y +ᵥ y) ≤ (1 + c) * dist x y := by
  rw [dist_eq_norm_vsub V (s • u x +ᵥ x), smul_vadd_vsub_smul_vadd, dist_eq_norm_vsub V x y]
  have h₁ := norm_smul_sub_le hu hs₀ hs₁ x y
  have h₂ := norm_add_le (s • (u x - u y)) (x -ᵥ y)
  rw [dist_eq_norm_vsub V x y] at h₁
  linarith

/-- The lower Lipschitz bound of a time slice. -/
private theorem mul_dist_le_dist_smul_vadd (hu : LipschitzWith c u) {s : ℝ} (hs₀ : 0 ≤ s)
    (hs₁ : s ≤ 1) (x y : P) : (1 - c) * dist x y ≤ dist (s • u x +ᵥ x) (s • u y +ᵥ y) := by
  rw [dist_eq_norm_vsub V (s • u x +ᵥ x), smul_vadd_vsub_smul_vadd, dist_eq_norm_vsub V x y]
  have h₁ := norm_smul_sub_le hu hs₀ hs₁ x y
  have h₂ := norm_sub_le (s • (u x - u y) + (x -ᵥ y)) (s • (u x - u y))
  rw [add_sub_cancel_left] at h₂
  rw [dist_eq_norm_vsub V x y] at h₁
  linarith

/-- For `y : P` and a time `t ∈ [0, 1]`, the map `x ↦ -(t • u x) +ᵥ y` is a contraction, whose
fixed point is the preimage of `y` under the time-`t` slice. -/
private theorem contractingWith_neg_smul_vadd (hu : LipschitzWith c u) (hc : c < 1) (t : I)
    (y : P) : ContractingWith c fun x => -((t : ℝ) • u x) +ᵥ y := by
  refine ⟨hc, LipschitzWith.of_dist_le_mul fun x x' => ?_⟩
  rw [dist_vadd_cancel_right, dist_neg_neg, dist_eq_norm, ← smul_sub]
  exact norm_smul_sub_le hu t.2.1 t.2.2 x x'

/-- The preimage of `y` under the time-`t` slice, as the fixed point of a contraction. -/
private def perturbInv [CompleteSpace P] (hu : LipschitzWith c u) (hc : c < 1) (t : I) (y : P) :
    P :=
  haveI : Nonempty P := ⟨y⟩
  ContractingWith.fixedPoint _ (contractingWith_neg_smul_vadd hu hc t y)

variable [CompleteSpace P]

private theorem neg_smul_vadd_perturbInv (hu : LipschitzWith c u) (hc : c < 1) (t : I) (y : P) :
    -((t : ℝ) • u (perturbInv hu hc t y)) +ᵥ y = perturbInv hu hc t y :=
  haveI : Nonempty P := ⟨y⟩
  ContractingWith.fixedPoint_isFixedPt (contractingWith_neg_smul_vadd hu hc t y)

private theorem smul_vadd_perturbInv (hu : LipschitzWith c u) (hc : c < 1) (t : I) (y : P) :
    (t : ℝ) • u (perturbInv hu hc t y) +ᵥ perturbInv hu hc t y = y :=
  calc _ = (t : ℝ) • u (perturbInv hu hc t y) +ᵥ
        (-((t : ℝ) • u (perturbInv hu hc t y)) +ᵥ y) := by rw [neg_smul_vadd_perturbInv]
    _ = y := vadd_neg_vadd _ _

private theorem perturbInv_smul_vadd (hu : LipschitzWith c u) (hc : c < 1) (t : I) (x : P) :
    perturbInv hu hc t ((t : ℝ) • u x +ᵥ x) = x :=
  haveI : Nonempty P := ⟨x⟩
  ((contractingWith_neg_smul_vadd hu hc t _).fixedPoint_unique (neg_vadd_vadd _ x)).symm

/-- The inverse slices at two times and points are close: the lower Lipschitz bound at time `s`,
applied to the preimages of `z` at time `s` and of `y` at time `t`. -/
private theorem dist_perturbInv_le (hu : LipschitzWith c u) (hc : c < 1) (s t : I) (z y : P) :
    dist (perturbInv hu hc s z) (perturbInv hu hc t y) ≤
      (|(s : ℝ) - t| * ‖u (perturbInv hu hc t y)‖ + dist z y) / (1 - c) := by
  set a := perturbInv hu hc t y
  set b := perturbInv hu hc s z
  -- the time-`s` slice moves `a` to a point within `|s - t| * ‖u a‖` of `y`
  have ha : (s : ℝ) • u a +ᵥ a = ((s : ℝ) - t) • u a +ᵥ y :=
    calc _ = (s : ℝ) • u a +ᵥ (-((t : ℝ) • u a) +ᵥ y) := by
          rw [neg_smul_vadd_perturbInv hu hc t y]
      _ = ((s : ℝ) - t) • u a +ᵥ y := by rw [vadd_vadd, sub_smul, sub_eq_add_neg]
  have hlow := mul_dist_le_dist_smul_vadd hu s.2.1 s.2.2 b a
  rw [smul_vadd_perturbInv hu hc s z, ha] at hlow
  have hy : dist y (((s : ℝ) - t) • u a +ᵥ y) = |(s : ℝ) - t| * ‖u a‖ := by
    rw [dist_comm, dist_vadd_left, norm_smul, Real.norm_eq_abs]
  have hyz := dist_triangle z y (((s : ℝ) - t) • u a +ᵥ y)
  rw [le_div_iff₀ (sub_pos.2 (NNReal.coe_lt_one.2 hc)), mul_comm]
  linarith

private theorem continuous_perturbInv (hu : LipschitzWith c u) (hc : c < 1) :
    Continuous fun q : I × P => perturbInv hu hc q.1 q.2 := by
  refine continuous_iff_continuousAt.2 fun q => ?_
  rw [ContinuousAt, tendsto_iff_dist_tendsto_zero]
  refine squeeze_zero (fun _ => dist_nonneg) (fun r => dist_perturbInv_le hu hc r.1 q.1 r.2 q.2) ?_
  have hbound : Continuous fun r : I × P =>
      (|(r.1 : ℝ) - q.1| * ‖u (perturbInv hu hc q.1 q.2)‖ + dist r.2 q.2) / (1 - c) := by
    fun_prop
  simpa using hbound.tendsto q

/-- The level-preserving total map `(t, x) ↦ (t, t • u x +ᵥ x)`, as a homeomorphism. -/
private def perturbTotal (hu : LipschitzWith c u) (hc : c < 1) : (I × P) ≃ₜ (I × P) where
  toFun q := (q.1, (q.1 : ℝ) • u q.2 +ᵥ q.2)
  invFun q := (q.1, perturbInv hu hc q.1 q.2)
  left_inv q := Prod.ext rfl (perturbInv_smul_vadd hu hc q.1 q.2)
  right_inv q := Prod.ext rfl (smul_vadd_perturbInv hu hc q.1 q.2)
  continuous_toFun := by
    have := hu.continuous
    fun_prop
  continuous_invFun := continuous_fst.prodMk (continuous_perturbInv hu hc)

/-- The **perturbation** of the identity of a complete real normed affine space `P` by a
displacement field `u : P → V` which is Lipschitz with constant `c < 1`: at time `t` it moves `x`
to `t • u x +ᵥ x`. Every time slice is a homeomorphism, and the total map is jointly continuous
together with its inverse, so this is an ambient isotopy. It fixes the points where `u` vanishes
at all times. -/
def perturb (hu : LipschitzWith c u) (hc : c < 1) : AmbientIsotopy P where
  toFun q := (q.1 : ℝ) • u q.2 +ᵥ q.2
  continuous_toFun := by
    have := hu.continuous
    fun_prop
  isHomeomorph_total' := (perturbTotal hu hc).isHomeomorph
  map_zero_left' x := by simp

variable (hu : LipschitzWith c u) (hc : c < 1)

/-- The perturbation at a time-point pair `(t, x)` is `t • u x +ᵥ x`. -/
@[simp]
theorem perturb_apply (q : I × P) :
    (perturb hu hc).toContinuousMap q = (q.1 : ℝ) • u q.2 +ᵥ q.2 :=
  (rfl)

/-- The final map of the perturbation moves `x` by `u x`. -/
theorem perturb_final_apply (x : P) : (perturb hu hc).final x = u x +ᵥ x := by
  simp

/-- At time `t` the perturbation moves `x` by exactly `t * ‖u x‖`. -/
theorem dist_perturb_apply (t : I) (x : P) :
    dist ((perturb hu hc).toContinuousMap (t, x)) x = t * ‖u x‖ := by
  rw [perturb_apply, dist_vadd_left, norm_smul, Real.norm_of_nonneg t.2.1]

/-- Every time slice of the perturbation is `(1 + c)`-Lipschitz. -/
theorem lipschitzWith_perturb_apply (t : I) :
    LipschitzWith (1 + c) fun x => (perturb hu hc).toContinuousMap (t, x) :=
  LipschitzWith.of_dist_le_mul fun x y => by
    simpa using dist_smul_vadd_le hu t.2.1 t.2.2 x y

/-- Every time slice of the perturbation is `(1 - c)⁻¹`-antilipschitz: it shrinks distances by
at most the factor `1 - c`. -/
theorem antilipschitzWith_perturb_apply (t : I) :
    AntilipschitzWith (1 - c)⁻¹ fun x => (perturb hu hc).toContinuousMap (t, x) := by
  refine AntilipschitzWith.of_le_mul_dist fun x y => ?_
  have hc' : (0 : ℝ) < 1 - c := sub_pos.2 (NNReal.coe_lt_one.2 hc)
  rw [NNReal.coe_inv, NNReal.coe_sub hc.le, NNReal.coe_one, ← div_eq_inv_mul, le_div_iff₀ hc',
    mul_comm]
  simpa using mul_dist_le_dist_smul_vadd hu t.2.1 t.2.2 x y

/-- Every inverse time slice of the perturbation is `(1 - c)⁻¹`-Lipschitz. -/
theorem lipschitzWith_perturb_symm_apply (t : I) :
    LipschitzWith (1 - c)⁻¹ fun y => (perturb hu hc).symm.toContinuousMap (t, y) :=
  (antilipschitzWith_perturb_apply hu hc t).to_rightInverse fun y =>
    (perturb hu hc).apply_symm_apply_slice t y

/-- The inverse time-`t` slice of the perturbation sends `y` to the point `a` with
`a = -(t • u a) +ᵥ y`, the fixed point of a contraction. -/
theorem perturb_symm_apply (t : I) (y : P) :
    (perturb hu hc).symm.toContinuousMap (t, y) =
      -((t : ℝ) • u ((perturb hu hc).symm.toContinuousMap (t, y))) +ᵥ y := by
  have h := (perturb hu hc).apply_symm_apply_slice t y
  rw [perturb_apply] at h
  exact (neg_vadd_vadd _ _).symm.trans (congrArg _ h)

/-- The perturbation fixes every point at which the displacement field vanishes, at all
times. -/
theorem perturb_apply_of_eq_zero {x : P} (hx : u x = 0) (t : I) :
    (perturb hu hc).toContinuousMap (t, x) = x := by
  simp [hx]

/-- If the displacement field vanishes outside `s`, every time slice of the perturbation
preserves `s` in both directions, so the perturbation restricts to an ambient isotopy of `s`
(`TauCeti.AmbientIsotopy.restrict`). -/
theorem perturb_apply_mem_iff {s : Set P} (hs : ∀ x ∉ s, u x = 0) (t : I) (x : P) :
    (perturb hu hc).toContinuousMap (t, x) ∈ s ↔ x ∈ s :=
  (perturb hu hc).apply_mem_iff_of_forall_notMem
    (fun t x hx => perturb_apply_of_eq_zero hu hc (hs x hx) t) t x

/-- The zero displacement field gives the constant ambient isotopy. -/
@[simp]
theorem perturb_zero (hu : LipschitzWith c (0 : P → V)) : perturb hu hc = refl P := by
  ext q
  simp

end AmbientIsotopy

end TauCeti
