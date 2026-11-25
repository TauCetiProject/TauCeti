/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Order.Group.PosPart
public import Mathlib.Basic.ENNReal.Real
import Mathlib.Basic.ENNReal.Inv
import Mathlib.Basic.Real.Pointwise

/-!
# `ENNReal.ofReal` of positive parts, differences, and suprema of maxima

Because `ENNReal.ofReal` vanishes on `(-∞, 0]`, it absorbs the positive part
(`ENNReal.ofReal_posPart`), and for `p > 1` it preserves the Hölder conjugate ratio `p / (p - 1)`
(`ENNReal.ofReal_div_sub_one`). For `0 ≤ q ≤ p`, `ENNReal.ofReal` splits `p` into `p - q` and `q`.
With `p = 1` and `q = θ`, this says that the interpolation weights `1 - θ` and `θ` sum to one in
`ℝ≥0∞`. In the other direction, `ENNReal.toReal` vanishes at `∞`, so an exponent `q` with
`0 < a * q.toReal` is finite.

For a class `P` of functions `α → ℝ`, the quantity
`⨆ (F : α → ℝ) (_ : P F), ENNReal.ofReal (⨆ x, F x)` in `ℝ≥0∞` is the supremum of the maxima of
the functions in the class. Capacities in symplectic geometry, such as the Hofer–Zehnder capacity
and its variants, are defined this way, and their conformality and symplectic invariance reduce to
the two facts here: the supremum scales with a rescaling of the class, and it is unchanged by a
reparametrization of the class along surjections.

## Main results

* `ENNReal.ofReal_posPart`: `ENNReal.ofReal (x⁺) = ENNReal.ofReal x`.
* `ENNReal.toNNReal_ofReal`: `(ENNReal.ofReal r).toNNReal = r.toNNReal`.
* `ENNReal.ofReal_div_sub_one`:
  `ENNReal.ofReal (p / (p - 1)) = ENNReal.ofReal p / (ENNReal.ofReal p - 1)` for `1 < p`.
* `ENNReal.ne_top_of_pos_mul_toReal`: `q ≠ ∞` whenever `0 < a * q.toReal`.
* `ENNReal.iSup_ofReal_min_natCast`:
  `⨆ n : ℕ, ENNReal.ofReal (min x n) = ENNReal.ofReal x`.
* `TauCeti.ofReal_sub_add_ofReal`: `ENNReal.ofReal (p - q) + ENNReal.ofReal q = ENNReal.ofReal p`
  for `0 ≤ q ≤ p`.
* `TauCeti.le_ofReal_inv_add_mul_of_add_le`: if `a + b ≤ V` and `b ≥ ω V`, then
  `a ≤ (1 + ω)⁻¹ V`.
* `TauCeti.ofReal_mul_ofReal_add_ofReal_mul_ofReal`: `ENNReal.ofReal` folds
  `D * (s + r * F)` for `0 ≤ s, r, F`.
* `TauCeti.le_ofReal_mul_add_ofReal_mul_top`: `D * (s + r * ∞)` is `∞` for `D, r > 0`.
* `TauCeti.iSup₂_ofReal_iSup_eq_ofReal_mul`: if the class `Q` consists of the `c • F` with `F`
  in `P`, for `c > 0`, then the supremum for `Q` is `c` times that for `P`.
* `TauCeti.iSup₂_ofReal_iSup_eq_of_comp`: classes related by composition with surjections have
  the same supremum of maxima.
-/

public section

open scoped ENNReal

namespace ENNReal

/-- The positive part of a real number, through `ℝ≥0∞`, is `Real.toNNReal`. -/
@[simp]
theorem toNNReal_ofReal (r : ℝ) : (ENNReal.ofReal r).toNNReal = r.toNNReal :=
  toNNReal_coe r.toNNReal

/-- `ENNReal.ofReal` absorbs the positive part since it already vanishes on `(-∞, 0]`. -/
@[simp]
theorem ofReal_posPart (x : ℝ) : ENNReal.ofReal (x⁺) = ENNReal.ofReal x := by
  rcases le_total 0 x with hx | hx
  · rw [posPart_eq_self.2 hx]
  · rw [posPart_eq_zero.2 hx, ofReal_zero, ofReal_eq_zero.2 hx]

/-- For `1 < p`, `ENNReal.ofReal` commutes with the Hölder conjugate ratio `p / (p - 1)`. -/
theorem ofReal_div_sub_one {p : ℝ} (hp : 1 < p) :
    ENNReal.ofReal (p / (p - 1)) = ENNReal.ofReal p / (ENNReal.ofReal p - 1) := by
  rw [ofReal_div_of_pos (sub_pos.2 hp), ofReal_sub _ zero_le_one, ofReal_one]

/-- An extended nonnegative real `q` with `0 < a * q.toReal` is finite, since `∞.toReal = 0`. -/
theorem ne_top_of_pos_mul_toReal {a : ℝ} {q : ℝ≥0∞} (h : 0 < a * q.toReal) : q ≠ ∞ := by
  rintro rfl
  rw [toReal_top, mul_zero] at h
  exact h.false

/-- Truncating a real number `x` at `n : ℕ` and taking the supremum in `ℝ≥0∞` recovers
`ENNReal.ofReal x`. -/
theorem iSup_ofReal_min_natCast (x : ℝ) :
    (⨆ n : ℕ, ENNReal.ofReal (min x n)) = ENNReal.ofReal x := by
  refine le_antisymm (iSup_le fun _ ↦ ENNReal.ofReal_le_ofReal (min_le_left _ _)) ?_
  obtain ⟨n, hn⟩ := exists_nat_ge x
  exact le_iSup_of_le n (by rw [min_eq_left hn])

end ENNReal

namespace TauCeti

variable {α β : Type*}

/-- For `0 ≤ q ≤ p`, `ENNReal.ofReal` adds `p - q` and `q` back up to `p`. -/
@[simp]
theorem ofReal_sub_add_ofReal {p q : ℝ} (hq : 0 ≤ q) (hqp : q ≤ p) :
    ENNReal.ofReal (p - q) + ENNReal.ofReal q = ENNReal.ofReal p := by
  rw [← ENNReal.ofReal_add (sub_nonneg.2 hqp) hq, sub_add_cancel]

/-- If `a + b ≤ V` and `b ≥ ω V`, then `a ≤ (1 + ω)⁻¹ V`: the complement of a set filling an
`ω` fraction of a set of measure `V` fills at most a `(1 + ω)⁻¹` fraction of it. -/
theorem le_ofReal_inv_add_mul_of_add_le {a b : ℝ≥0∞} {V ω : ℝ} (hV : 0 ≤ V) (hω : 0 ≤ ω)
    (hb : ENNReal.ofReal (ω * V) ≤ b) (hab : a + b ≤ ENNReal.ofReal V) :
    a ≤ ENNReal.ofReal (1 + ω)⁻¹ * ENNReal.ofReal V := by
  have hδV : V - ω * V ≤ (1 + ω)⁻¹ * V := by
    have h : (1 + ω)⁻¹ * V - (V - ω * V) = ω ^ 2 / (1 + ω) * V := by
      field_simp
      ring
    nlinarith [mul_nonneg (div_nonneg (sq_nonneg ω) (by positivity : (0 : ℝ) ≤ 1 + ω)) hV]
  calc a ≤ ENNReal.ofReal V - b :=
        ENNReal.le_sub_of_add_le_right (ne_top_of_le_ne_top ENNReal.ofReal_ne_top
          (le_add_self.trans hab)) hab
    _ ≤ ENNReal.ofReal V - ENNReal.ofReal (ω * V) := tsub_le_tsub_left hb _
    _ = ENNReal.ofReal (V - ω * V) := (ENNReal.ofReal_sub _ (by positivity)).symm
    _ ≤ ENNReal.ofReal ((1 + ω)⁻¹ * V) := ENNReal.ofReal_le_ofReal hδV
    _ = ENNReal.ofReal (1 + ω)⁻¹ * ENNReal.ofReal V := ENNReal.ofReal_mul (by positivity)

/-- `ENNReal.ofReal` folds `D * (s + r * F)` for `0 ≤ s, r, F`; the outer factor `D` may have
either sign, since `ENNReal.ofReal` sends negative reals to `0`. -/
theorem ofReal_mul_ofReal_add_ofReal_mul_ofReal (D : ℝ) {s r F : ℝ} (hs : 0 ≤ s)
    (hr : 0 ≤ r) (hF : 0 ≤ F) :
    ENNReal.ofReal D * (ENNReal.ofReal s + ENNReal.ofReal r * ENNReal.ofReal F) =
      ENNReal.ofReal (D * (s + r * F)) := by
  rw [← ENNReal.ofReal_mul hr, ← ENNReal.ofReal_add hs (mul_nonneg hr hF),
    ← ENNReal.ofReal_mul' (add_nonneg hs (mul_nonneg hr hF))]

/-- If `D, r > 0`, then `ENNReal.ofReal D * (ENNReal.ofReal s + ENNReal.ofReal r * ∞)` is `∞`,
so it bounds everything. -/
theorem le_ofReal_mul_add_ofReal_mul_top {X : ℝ≥0∞} {D r : ℝ} (hD : 0 < D) (hr : 0 < r)
    (s : ℝ) : X ≤ ENNReal.ofReal D * (ENNReal.ofReal s + ENNReal.ofReal r * ∞) := by
  rw [ENNReal.mul_top (ENNReal.ofReal_pos.2 hr).ne', add_top,
    ENNReal.mul_top (ENNReal.ofReal_pos.2 hD).ne']
  exact le_top

/-- **Rescaling a class of functions.** If, for `c > 0`, the functions satisfying `Q` are exactly
the `c • F` with `F` satisfying `P`, then the supremum of their maxima is `c` times that for `P`. -/
theorem iSup₂_ofReal_iSup_eq_ofReal_mul {P Q : (α → ℝ) → Prop} {c : ℝ} (hc : 0 < c)
    (h : ∀ F, Q (c • F) ↔ P F) :
    ⨆ (F : α → ℝ) (_ : Q F), ENNReal.ofReal (⨆ x, F x) =
      ENNReal.ofReal c * ⨆ (F : α → ℝ) (_ : P F), ENNReal.ofReal (⨆ x, F x) := by
  -- The maximum of `c • F` is `c` times the maximum of `F`.
  have hmax (F : α → ℝ) :
      ENNReal.ofReal (⨆ x, (c • F) x) = ENNReal.ofReal c * ENNReal.ofReal (⨆ x, F x) := by
    simp only [Pi.smul_apply, smul_eq_mul, ← Real.mul_iSup_of_nonneg hc.le,
      ENNReal.ofReal_mul hc.le]
  refine le_antisymm (iSup₂_le fun F hF ↦ ?_) ?_
  · have hF' : F = c • (c⁻¹ • F) := by rw [smul_smul, mul_inv_cancel₀ hc.ne', one_smul]
    rw [hF'] at hF ⊢
    rw [hmax]
    gcongr
    exact le_iSup₂ (f := fun F (_ : P F) ↦ ENNReal.ofReal (⨆ x, F x)) _ ((h _).1 hF)
  · simp only [ENNReal.mul_iSup]
    refine iSup₂_le fun F hF ↦ ?_
    rw [← hmax]
    exact le_iSup₂ (f := fun F (_ : Q F) ↦ ENNReal.ofReal (⨆ x, F x)) _ ((h F).2 hF)

/-- **Reparametrizing a class of functions.** If surjections `f : α → β` and `g : β → α` carry
the functions satisfying `P` to functions satisfying `Q` by `F ↦ F ∘ g`, and back by
`G ↦ G ∘ f`, then the suprema of the maxima of the two classes agree. -/
theorem iSup₂_ofReal_iSup_eq_of_comp {P : (α → ℝ) → Prop} {Q : (β → ℝ) → Prop} {f : α → β}
    {g : β → α} (hf : f.Surjective) (hg : g.Surjective) (hPQ : ∀ F, P F → Q (F ∘ g))
    (hQP : ∀ G, Q G → P (G ∘ f)) :
    ⨆ (G : β → ℝ) (_ : Q G), ENNReal.ofReal (⨆ y, G y) =
      ⨆ (F : α → ℝ) (_ : P F), ENNReal.ofReal (⨆ x, F x) := by
  refine le_antisymm (iSup₂_le fun G hG ↦ ?_) (iSup₂_le fun F hF ↦ ?_)
  · rw [← hf.iSup_comp G]
    exact le_iSup₂ (f := fun F (_ : P F) ↦ ENNReal.ofReal (⨆ x, F x)) (G ∘ f) (hQP G hG)
  · rw [← hg.iSup_comp F]
    exact le_iSup₂ (f := fun G (_ : Q G) ↦ ENNReal.ofReal (⨆ y, G y)) (F ∘ g) (hPQ F hF)

end TauCeti
