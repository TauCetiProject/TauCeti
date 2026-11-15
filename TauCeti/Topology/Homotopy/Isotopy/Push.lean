/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Affine.AddTorsor
public import TauCeti.Topology.Homotopy.Isotopy.Basic
import Mathlib.Topology.Maps.Proper.CompactlyGenerated
import Mathlib.Topology.Order.IntermediateValue

/-!
# Pushing along a vector inside a region

Let `P` be a real normed affine space with space of translations `V`, let `p : P` and `v : V`, and
let `μ : V → ℝ` be continuous and nonnegative. The **push** along `v` weighted by `μ` moves a
point `x` by

`x ↦ (t * max (1 - μ (x -ᵥ p)) 0) • v +ᵥ x`

at time `t ∈ [0, 1]`. It is the identity where `μ (x -ᵥ p) ≥ 1`, and it moves the point `p` itself
by `t • v` when `μ 0 = 0`. If `μ` grows more slowly than unit speed along `v`, that is
`μ (w + r • v) < μ w + r` for all `w` and `r > 0`, then every time-`t` map is a homeomorphism of
`P`, and the push is an ambient isotopy (`TauCeti.AmbientIsotopy.push`). Each time-`t` map
preserves the lines parallel to `v`, along which it is strictly increasing, and it moves every point
by at most `‖v‖`, so its level-preserving total map is a proper continuous bijection of `I × P`.

The growth condition holds for the gauge `μ` of a convex neighbourhood `Q` of `0` in `V`
(or any continuous sublinear function) as soon as `μ v < 1`, that is `p +ᵥ v` lies in the
interior of `p +ᵥ Q`. Then the push is supported in `p +ᵥ Q`, and when `μ` is positively homogeneous
its final map carries each segment from `p` to a point `y` with `μ (y -ᵥ p) = 1` affinely onto the
segment from `v +ᵥ p` to `y`: it pushes `p` to `v +ᵥ p` and drags the segments ending at `p`
along. This is the motion realizing a Δ-move of a polygonal knot by an ambient isotopy
(Burde and Zieschang, Proposition 1.10).

## Main definitions

* `TauCeti.AmbientIsotopy.push`: the push along `v` weighted by `μ`, as an ambient isotopy.

## Main results

* `TauCeti.AmbientIsotopy.push_apply`: the formula of the push.
* `TauCeti.AmbientIsotopy.push_final_apply`: the formula of its final map.
* `TauCeti.AmbientIsotopy.push_apply_of_one_le`: the push fixes every point `x` with
  `1 ≤ μ (x -ᵥ p)`.

## References

* G. Burde, H. Zieschang, *Knots*, 2nd ed., De Gruyter Studies in Mathematics 5 (2003),
  Chapter 1 §B, Proposition 1.10, for realizing Δ-moves by ambient isotopies.
-/

public section

noncomputable section

open Set unitInterval Topology

namespace TauCeti

namespace AmbientIsotopy

variable {V P : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [MetricSpace P]
  [NormedAddTorsor V P] {μ : V → ℝ} {p : P} {v : V}

/-- Along each line parallel to `v`, the displacement `s ↦ s + t * max (1 - μ (·)) 0` of the push
at a time `t ∈ [0, 1]` is strictly increasing, because `μ` grows more slowly than unit speed
along `v`. -/
private theorem strictMono_add_mul_max
    (hv : ∀ (w : V) (r : ℝ), 0 < r → μ (w + r • v) < μ w + r) {t : ℝ} (ht₀ : 0 ≤ t)
    (ht₁ : t ≤ 1) (x : P) :
    StrictMono fun s : ℝ => s + t * max (1 - μ ((s • v +ᵥ x) -ᵥ p)) 0 := by
  intro s₁ s₂ hs
  have hw : (s₂ • v +ᵥ x) -ᵥ p = ((s₁ • v +ᵥ x) -ᵥ p) + (s₂ - s₁) • v := by
    rw [vadd_vsub_assoc, vadd_vsub_assoc, sub_smul]
    abel
  have hμ := hv ((s₁ • v +ᵥ x) -ᵥ p) (s₂ - s₁) (sub_pos.2 hs)
  rw [← hw] at hμ
  dsimp only
  -- The weight drops by less than the distance travelled along `v`.
  have hA : max (1 - μ ((s₁ • v +ᵥ x) -ᵥ p)) 0 - max (1 - μ ((s₂ • v +ᵥ x) -ᵥ p)) 0 <
      s₂ - s₁ := by
    rcases le_total (1 - μ ((s₁ • v +ᵥ x) -ᵥ p)) 0 with h | h
    · rw [max_eq_right h]
      linarith [le_max_right (1 - μ ((s₂ • v +ᵥ x) -ᵥ p)) 0]
    · rw [max_eq_left h]
      linarith [le_max_left (1 - μ ((s₂ • v +ᵥ x) -ᵥ p)) 0]
  rcases le_total (max (1 - μ ((s₁ • v +ᵥ x) -ᵥ p)) 0)
    (max (1 - μ ((s₂ • v +ᵥ x) -ᵥ p)) 0) with h | h
  · nlinarith
  · nlinarith

omit [NormedSpace ℝ V] in
/-- The push weight `max (1 - μ (x -ᵥ p)) 0` lies in `[0, 1]` when `μ` is nonnegative. -/
private theorem max_one_sub_le_one (hμ₀ : ∀ w, 0 ≤ μ w) (x : P) :
    max (1 - μ (x -ᵥ p)) 0 ≤ 1 :=
  max_le (by linarith [hμ₀ (x -ᵥ p)]) zero_le_one

/-- The time-`t` map of the push, for `t ∈ [0, 1]`, is a bijection of `P`. -/
private theorem bijective_push (hμ : Continuous μ) (hμ₀ : ∀ w, 0 ≤ μ w)
    (hv : ∀ (w : V) (r : ℝ), 0 < r → μ (w + r • v) < μ w + r) {t : ℝ} (ht₀ : 0 ≤ t)
    (ht₁ : t ≤ 1) :
    Function.Bijective fun x : P => (t * max (1 - μ (x -ᵥ p)) 0) • v +ᵥ x := by
  refine ⟨fun x y hxy => ?_, fun y => ?_⟩
  · -- Two points with the same image differ by a multiple `d • v` of `v`, and the displacement
    -- along that line is injective.
    dsimp only at hxy
    set d := t * max (1 - μ (x -ᵥ p)) 0 - t * max (1 - μ (y -ᵥ p)) 0 with hd
    have hy : y = d • v +ᵥ x := by
      refine vadd_left_cancel ((t * max (1 - μ (y -ᵥ p)) 0) • v) ?_
      rw [← hxy, vadd_vadd, hd, sub_smul, add_sub_cancel]
    have h := (strictMono_add_mul_max (p := p) hv ht₀ ht₁ x).injective
      (a₁ := d) (a₂ := 0) (by
        rw [← hy, zero_smul, zero_vadd, zero_add, hd]
        ring)
    rw [hy, h, zero_smul, zero_vadd]
  · -- The point at parameter `s` before `y` on the line through `y` parallel to `v` is mapped
    -- to `y` when `s` is the push at that point; one such `s ∈ [0, 1]` exists by the
    -- intermediate value theorem.
    have hcont : ContinuousOn
        (fun s : ℝ => s - t * max (1 - μ (((-s) • v +ᵥ y) -ᵥ p)) 0) (Icc 0 1) :=
      (by fun_prop : Continuous _).continuousOn
    have h0 : (0 : ℝ) ∈ Icc
        ((fun s : ℝ => s - t * max (1 - μ (((-s) • v +ᵥ y) -ᵥ p)) 0) 0)
        ((fun s : ℝ => s - t * max (1 - μ (((-s) • v +ᵥ y) -ᵥ p)) 0) 1) := by
      dsimp only
      constructor
      · nlinarith [le_max_right (1 - μ (((-0 : ℝ) • v +ᵥ y) -ᵥ p)) 0]
      · nlinarith [max_one_sub_le_one (p := p) hμ₀ ((-1 : ℝ) • v +ᵥ y),
          le_max_right (1 - μ (((-1 : ℝ) • v +ᵥ y) -ᵥ p)) 0]
    obtain ⟨s, -, hs⟩ := intermediate_value_Icc zero_le_one hcont h0
    refine ⟨(-s) • v +ᵥ y, ?_⟩
    dsimp only at hs ⊢
    rw [vadd_vadd, ← add_smul, show t * max (1 - μ (((-s) • v +ᵥ y) -ᵥ p)) 0 + -s = 0 by
      linarith, zero_smul, zero_vadd]

/-- The level-preserving total map of the push is a homeomorphism of `I × P`: it is a continuous
bijection, and it is proper because it moves every point by a multiple `s • v` of `v` with
`s ∈ [0, 1]`. -/
private theorem isHomeomorph_push (hμ : Continuous μ) (hμ₀ : ∀ w, 0 ≤ μ w)
    (hv : ∀ (w : V) (r : ℝ), 0 < r → μ (w + r • v) < μ w + r) :
    IsHomeomorph fun q : I × P => (q.1, ((q.1 : ℝ) * max (1 - μ (q.2 -ᵥ p)) 0) • v +ᵥ q.2) := by
  set F := fun q : I × P => (q.1, ((q.1 : ℝ) * max (1 - μ (q.2 -ᵥ p)) 0) • v +ᵥ q.2)
  have hF : Continuous F := by fun_prop
  have hbij : Function.Bijective F := by
    refine ⟨fun q q' hqq' => ?_, fun y => ?_⟩
    · have ht : q.1 = q'.1 := (Prod.ext_iff.1 hqq').1
      have hx := (Prod.ext_iff.1 hqq').2
      simp only [F, ← ht] at hx
      exact Prod.ext ht ((bijective_push hμ hμ₀ hv q.1.2.1 q.1.2.2).injective hx)
    · obtain ⟨x, hx⟩ := (bijective_push (p := p) hμ hμ₀ hv y.1.2.1 y.1.2.2).surjective y.2
      exact ⟨(y.1, x), Prod.ext rfl hx⟩
  -- Preimages of compact sets are compact: a point is recovered from its image `y` by moving it
  -- back by `s • v` for some `s ∈ [0, 1]`.
  have hproper : IsProperMap F := by
    refine isProperMap_iff_isCompact_preimage.2 ⟨hF, fun K hK => ?_⟩
    let G : (I × P) × ℝ → I × P := fun q => (q.1.1, (-q.2) • v +ᵥ q.1.2)
    have hG : Continuous G := by fun_prop
    refine (hK.prod (isCompact_Icc (a := (0 : ℝ)) (b := 1))).image hG |>.of_isClosed_subset
      (hK.isClosed.preimage hF) fun q hq => ?_
    refine ⟨(F q, (q.1 : ℝ) * max (1 - μ (q.2 -ᵥ p)) 0), ⟨hq, ?_, ?_⟩, ?_⟩
    · exact mul_nonneg q.1.2.1 (le_max_right _ _)
    · have := max_one_sub_le_one (p := p) hμ₀ q.2
      nlinarith [q.1.2.1, q.1.2.2, le_max_right (1 - μ (q.2 -ᵥ p)) 0]
    · simp only [G, F, neg_smul, neg_vadd_vadd]
  exact isHomeomorph_iff_continuous_isClosedMap_bijective.2 ⟨hF, hproper.isClosedMap, hbij⟩

variable (μ p v) in
/-- The **push** along `v` weighted by `μ`, from the base point `p`: at time `t` it moves `x` to
`(t * max (1 - μ (x -ᵥ p)) 0) • v +ᵥ x`. It is an ambient isotopy when `μ` is continuous and
nonnegative and grows more slowly than unit speed along `v`. It fixes the points `x` with
`1 ≤ μ (x -ᵥ p)` at all times. -/
def push (hμ : Continuous μ) (hμ₀ : ∀ w, 0 ≤ μ w)
    (hv : ∀ (w : V) (r : ℝ), 0 < r → μ (w + r • v) < μ w + r) : AmbientIsotopy P where
  toFun q := ((q.1 : ℝ) * max (1 - μ (q.2 -ᵥ p)) 0) • v +ᵥ q.2
  continuous_toFun := by fun_prop
  isHomeomorph_total' := isHomeomorph_push hμ hμ₀ hv
  map_zero_left' x := by simp

variable (hμ : Continuous μ) (hμ₀ : ∀ w, 0 ≤ μ w)
  (hv : ∀ (w : V) (r : ℝ), 0 < r → μ (w + r • v) < μ w + r)

/-- The push evaluated at a time-point pair `(t, x)`: at time `t` it moves `x` to
`(t * max (1 - μ (x -ᵥ p)) 0) • v +ᵥ x`. -/
@[simp]
theorem push_apply (q : I × P) :
    (push μ p v hμ hμ₀ hv).toContinuousMap q =
      ((q.1 : ℝ) * max (1 - μ (q.2 -ᵥ p)) 0) • v +ᵥ q.2 :=
  (rfl)

/-- The final map of the push moves `x` by `max (1 - μ (x -ᵥ p)) 0 • v`. -/
theorem push_final_apply (x : P) :
    (push μ p v hμ hμ₀ hv).final x = max (1 - μ (x -ᵥ p)) 0 • v +ᵥ x := by
  simp

/-- The push fixes every point `x` with `1 ≤ μ (x -ᵥ p)`, at all times. -/
theorem push_apply_of_one_le {x : P} (hx : 1 ≤ μ (x -ᵥ p)) (t : I) :
    (push μ p v hμ hμ₀ hv).toContinuousMap (t, x) = x := by
  simp [max_eq_right (sub_nonpos.2 hx)]

end AmbientIsotopy

end TauCeti
