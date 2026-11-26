/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Instances.EReal.Lemmas
import TauCeti.Algebra.Order.Field.Basic
import TauCeti.Data.EReal.Operations
import TauCeti.Topology.Instances.EReal

/-!
# Convexity along curves

The predicate `TauCeti.ConvexAlong` expresses the quadratic convexity inequality for
extended-real energies along arbitrary curves in pseudometric spaces. It is stable under
sums, nonnegative multiples, suprema and pointwise limits whose endpoint values are below `⊤`.

## Main results

* `TauCeti.convexAlong_def`: the characteristic inequality for introduction and elimination.
* `TauCeti.convexAlong_zero`: the zero energy is convex with modulus zero along every curve.
* `TauCeti.ConvexAlong.mono`: convexity persists when its modulus decreases.
* `TauCeti.ConvexAlong.apply_ne_top`: the effective domain is convex along a curve of convexity.
* `TauCeti.ConvexAlong.reverse`: convexity is preserved when the curve is reversed.
* `TauCeti.ConvexAlong.add`, `TauCeti.ConvexAlong.const_mul`, `TauCeti.ConvexAlong.iSup` and
  `TauCeti.ConvexAlong.of_tendsto`: stability under operations on energies.
* `TauCeti.ConvexAlong.apply_add_le_of_forall_le`: a quadratic lower bound at the endpoint
  from a minimum on a curve.
* `TauCeti.ConvexAlong.mul_dist_sq_div_four_le_sub`: the midpoint penalty bound.

The endpoint and midpoint estimates are used for minimizing sequences, as in Ambrosio, Gigli
and Savaré, *Gradient Flows in Metric Spaces and in the Space of Probability Measures*,
2nd ed., Section 2.4, Lemma 4.1.1 and Theorem 4.1.2.
-/

public section

open Filter Set Topology

namespace TauCeti

variable {X : Type*} [PseudoMetricSpace X] {m m' : ℝ} {φ ψ : X → EReal} {γ : ℝ → X}

/-- The energy `φ` is *`m`-convex along* the curve `γ`, read on `[0, 1]`: for every `t ∈ [0, 1]`,
`φ (γ t) ≤ (1 - t) φ (γ 0) + t φ (γ 1) - (m / 2) t (1 - t) d(γ 0, γ 1)²`. -/
def ConvexAlong (m : ℝ) (φ : X → EReal) (γ : ℝ → X) : Prop :=
  ∀ t ∈ Icc (0 : ℝ) 1, φ (γ t) ≤ ((1 - t : ℝ) : EReal) * φ (γ 0) + (t : EReal) * φ (γ 1) -
    ((m / 2 * t * (1 - t) * dist (γ 0) (γ 1) ^ 2 : ℝ) : EReal)

/-- The defining inequality of convexity along a curve. -/
theorem convexAlong_def :
    ConvexAlong m φ γ ↔ ∀ t ∈ Icc (0 : ℝ) 1, φ (γ t) ≤ ((1 - t : ℝ) : EReal) * φ (γ 0) +
      (t : EReal) * φ (γ 1) - ((m / 2 * t * (1 - t) * dist (γ 0) (γ 1) ^ 2 : ℝ) : EReal) := by
  unfold ConvexAlong
  rfl

/-- The zero energy is convex with modulus zero along every curve. -/
@[simp]
theorem convexAlong_zero : ConvexAlong 0 (fun _ ↦ (0 : EReal)) γ := by
  intro t _
  simp

/-- Convexity along a curve with a parameter `m` implies it for every smaller parameter. -/
theorem ConvexAlong.mono (h : ConvexAlong m φ γ) (hm : m' ≤ m) : ConvexAlong m' φ γ :=
  fun t ht ↦ (h t ht).trans <| EReal.sub_le_sub le_rfl <| EReal.coe_le_coe_iff.2 <| by
    have : 0 ≤ t * (1 - t) * dist (γ 0) (γ 1) ^ 2 :=
      mul_nonneg (mul_nonneg ht.1 (sub_nonneg.2 ht.2)) (sq_nonneg _)
    nlinarith

/-- **The effective domain is convex along a curve of convexity.** If `φ` is `m`-convex along `γ`
and both endpoint values are `≠ ⊤`, then so is `φ (γ t)` for every `t ∈ [0, 1]`. -/
theorem ConvexAlong.apply_ne_top (h : ConvexAlong m φ γ) (h₀ : φ (γ 0) ≠ ⊤) (h₁ : φ (γ 1) ≠ ⊤)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) : φ (γ t) ≠ ⊤ :=
  ne_top_of_le_ne_top
    (EReal.coe_mul_add_coe_mul_sub_coe_ne_top h₀ h₁ (sub_nonneg.2 ht.2) ht.1) (h t ht)

/-- Convexity along a curve is unchanged by running the curve backwards. -/
theorem ConvexAlong.reverse (h : ConvexAlong m φ γ) : ConvexAlong m φ fun t ↦ γ (1 - t) := by
  intro t ht
  have h' := h (1 - t) ⟨sub_nonneg.2 ht.2, sub_le_self _ ht.1⟩
  rw [sub_sub_cancel] at h'
  simp only [sub_zero, sub_self]
  rw [add_comm, dist_comm, mul_right_comm (m / 2) t]
  exact h'

/-- **Sum of convex energies.** If `φ` is `m`-convex and `ψ` is `m'`-convex along the same curve,
then `φ + ψ` is `(m + m')`-convex along it. -/
theorem ConvexAlong.add (hφ : ConvexAlong m φ γ) (hψ : ConvexAlong m' ψ γ) :
    ConvexAlong (m + m') (φ + ψ) γ := by
  intro t ht
  calc (φ + ψ) (γ t) = φ (γ t) + ψ (γ t) := rfl
    _ ≤ _ := add_le_add (hφ t ht) (hψ t ht)
    _ = _ := by
      rw [EReal.coe_mul_add_coe_mul_sub_add_sub_comm _ _ _ _ (sub_nonneg.2 ht.2) ht.1]
      congr 2
      ring

/-- **Nonnegative multiple of a convex energy.** If `φ` is `m`-convex along a curve and `c ≥ 0`,
then `c φ` is `(c m)`-convex along it. -/
theorem ConvexAlong.const_mul (h : ConvexAlong m φ γ) {c : ℝ} (hc : 0 ≤ c) :
    ConvexAlong (c * m) (fun x ↦ (c : EReal) * φ x) γ := by
  intro t ht
  have hc' : (0 : EReal) ≤ c := EReal.coe_nonneg.2 hc
  calc (c : EReal) * φ (γ t) ≤ (c : EReal) * (((1 - t : ℝ) : EReal) * φ (γ 0) +
        (t : EReal) * φ (γ 1) - ((m / 2 * t * (1 - t) * dist (γ 0) (γ 1) ^ 2 : ℝ) : EReal)) :=
      mul_le_mul_of_nonneg_left (h t ht) hc'
    _ = _ := by
      rw [EReal.coe_mul_coe_mul_add_coe_mul_sub _ _ hc]
      congr 2
      ring

/-- **Supremum of convex energies.** The pointwise supremum of a family of energies, each
`m`-convex along a curve, is `m`-convex along it. -/
theorem ConvexAlong.iSup {ι : Sort*} {φs : ι → X → EReal} (h : ∀ i, ConvexAlong m (φs i) γ) :
    ConvexAlong m (⨆ i, φs i) γ := by
  intro t ht
  simp only [iSup_apply]
  refine iSup_le fun i ↦ (h i t ht).trans ?_
  exact EReal.coe_mul_add_coe_mul_sub_le_of_le (le_iSup (fun i ↦ φs i (γ 0)) i)
    (le_iSup (fun i ↦ φs i (γ 1)) i) (sub_nonneg.2 ht.2) ht.1 _

/-- **Convexity along a curve passes to pointwise limits.** If the energies `φs i` are eventually
`m`-convex along `γ` and converge to `φ` at every point `γ t`, `t ∈ [0, 1]`, and the endpoint
values of `φ` are `≠ ⊤`, then `φ` is `m`-convex along `γ`. -/
theorem ConvexAlong.of_tendsto {ι : Type*} {l : Filter ι} [l.NeBot] {φs : ι → X → EReal}
    (h : ∀ᶠ i in l, ConvexAlong m (φs i) γ)
    (hφ : ∀ t ∈ Icc (0 : ℝ) 1, Tendsto (fun i ↦ φs i (γ t)) l (𝓝 (φ (γ t))))
    (h₀ : φ (γ 0) ≠ ⊤) (h₁ : φ (γ 1) ≠ ⊤) : ConvexAlong m φ γ := by
  intro t ht
  exact le_of_tendsto_of_tendsto (hφ t ht)
    (EReal.tendsto_coe_mul_add_coe_mul_sub (hφ 0 (left_mem_Icc.2 zero_le_one))
      (hφ 1 (right_mem_Icc.2 zero_le_one)) h₀ h₁ (sub_nonneg.2 ht.2) ht.1 _)
    (h.mono fun i hi ↦ hi t ht)

/-- **Quadratic lower bound at the endpoint of a curve of convexity.** If `φ` is `m`-convex
along `γ` and its smallest value along `γ` on `[0, 1]` is attained at `γ 0`, then
`φ (γ 0) + (m / 2) d(γ 0, γ 1)² ≤ φ (γ 1)`. The modulus `m` may be negative. -/
theorem ConvexAlong.apply_add_le_of_forall_le (h : ConvexAlong m φ γ)
    (hmin : ∀ t ∈ Icc (0 : ℝ) 1, φ (γ 0) ≤ φ (γ t)) :
    φ (γ 0) + ((m / 2 * dist (γ 0) (γ 1) ^ 2 : ℝ) : EReal) ≤ φ (γ 1) := by
  have h₁ := hmin 1 (right_mem_Icc.2 zero_le_one)
  induction hb : φ (γ 1) using EReal.rec with
  | top => exact le_top
  | bot =>
    rw [hb, le_bot_iff] at h₁
    simp [h₁]
  | coe b =>
    induction ha : φ (γ 0) using EReal.rec with
    | bot => simp
    | top => simp [ha, hb] at h₁
    | coe a =>
      have hbound : a + m / 2 * dist (γ 0) (γ 1) ^ 2 ≤ b := by
        apply add_le_of_le_affine_sub
        intro t ht
        have ht' := Ioo_subset_Icc_self ht
        have h' := (hmin t ht').trans (h t ht')
        rw [ha, hb] at h'
        have hr : a ≤ (1 - t) * a + t * b - m / 2 * t * (1 - t) * dist (γ 0) (γ 1) ^ 2 := by
          exact_mod_cast h'
        convert hr using 1
        ring
      exact_mod_cast hbound

/-- The quantitative midpoint bound for a convex curve with real endpoint values.
A real lower bound at its midpoint forces a corresponding gap at the endpoints. -/
theorem ConvexAlong.mul_dist_sq_div_four_le_sub (h : ConvexAlong m φ γ)
    {a b c : ℝ} (hb : φ (γ 0) = b) (hc : φ (γ 1) = c)
    (hlow : (a : EReal) ≤ φ (γ (1 / 2))) :
    (m / 2 * dist (γ 0) (γ 1) ^ 2) / 4 ≤ (b + c) / 2 - a := by
  have hmid := hlow.trans (h (1 / 2) (by norm_num))
  rw [hb, hc] at hmid
  have hr : a ≤ (1 - 1 / 2) * b + (1 / 2) * c -
      m / 2 * (1 / 2) * (1 - 1 / 2) * dist (γ 0) (γ 1) ^ 2 := by
    exact_mod_cast hmid
  linarith

end TauCeti
