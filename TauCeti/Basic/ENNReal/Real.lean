/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Basic.ENNReal.Real
import Mathlib.Basic.ENNReal.Inv
import Mathlib.Basic.Real.Pointwise

/-!
# `ENNReal.ofReal` of differences and suprema of maxima

For `0 ≤ q ≤ p`, the embedding `ENNReal.ofReal` splits `p` into `p - q` and `q`. With `p = 1`
and `q = θ`, this says that the interpolation weights `1 - θ` and `θ` sum to one in `ℝ≥0∞`.

For a class `P` of functions `α → ℝ`, the quantity
`⨆ (F : α → ℝ) (_ : P F), ENNReal.ofReal (⨆ x, F x)` in `ℝ≥0∞` is the supremum of the maxima of
the functions in the class. Capacities in symplectic geometry, such as the Hofer–Zehnder capacity
and its variants, are defined this way, and their conformality and symplectic invariance reduce to
the two facts here: the supremum scales with a rescaling of the class, and it is unchanged by a
reparametrization of the class along surjections.

## Main results

* `TauCeti.ofReal_sub_add_ofReal`: `ENNReal.ofReal (p - q) + ENNReal.ofReal q = ENNReal.ofReal p`
  for `0 ≤ q ≤ p`.
* `TauCeti.le_ofReal_inv_add_mul_of_add_le`: if `a + b ≤ V` and `b ≥ ω V`, then
  `a ≤ (1 + ω)⁻¹ V`.
* `TauCeti.iSup₂_ofReal_iSup_eq_ofReal_mul`: if the class `Q` consists of the `c • F` with `F`
  in `P`, for `c > 0`, then the supremum for `Q` is `c` times that for `P`.
* `TauCeti.iSup₂_ofReal_iSup_eq_of_comp`: classes related by composition with surjections have
  the same supremum of maxima.
-/

public section

open scoped ENNReal

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
