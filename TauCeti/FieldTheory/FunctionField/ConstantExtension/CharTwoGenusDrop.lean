/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.FunctionField.ConstantExtension.InseparableGenusDrop
public import TauCeti.FieldTheory.FunctionField.PlaneCurve.Mordell
-- Proof-only: a compositum inside `k'(X)` containing `X` is everything.
import TauCeti.FieldTheory.FunctionField.ConstantExtension.RatFunc

/-!
# A genus-one function field in characteristic two that becomes rational

Let `k` be a field of characteristic two, `a ∈ k` not a square, and `F = k(x, y)` with `y`
transcendental over `k` and

`y ^ 2 = x ^ 3 + a`.

Since `3` is invertible in `k` and `Y ^ 2 - a` is squarefree, `y` is a separating element, `k` is
the exact constant field of `F`, and `F / k` has genus one
(`TauCeti.genus_eq_one_of_sq_eq_pow_three_add`). The equation has Weierstrass shape with
`a₁ = a₂ = a₃ = a₄ = 0`, so its discriminant `-432 a ^ 2` vanishes, although `F` has genus one.
The singularity becomes visible over `k(b)`, `b ^ 2 = a`: there `(y + b) ^ 2 = x ^ 3` is a cusp,
and with `u = (y + b) / x` one has `x = u ^ 2` and `y + b = u ^ 3`, so the constant field
extension `F · k(b)` is the rational function field `k(b)(u)` and has genus zero. A purely
inseparable constant field extension can therefore lower the genus even of a separably generated
function field with exact constants. The odd-characteristic counterpart is `TauCeti.GenusDrop`.

This file realizes the genus drop for `k = 𝔽₂(t)` inside `k' = 𝔽₂(s)`, `t = s ^ 2`, and
`F' = k'(u)` with `x = u ^ 2` and `y = u ^ 3 + s`.

## Main results

* `TauCeti.CharTwoGenusDrop.curveField`: the field `F = k(x, y)` inside `F' = 𝔽₂(s)(u)`.
* `TauCeti.CharTwoGenusDrop.constantCompositum_eq_top`: `F' = F · k'`.
* `TauCeti.CharTwoGenusDrop.genus_lt_genus`: `F' / k'` has genus `0`, below the genus `1` of
  `F / k`.

## References

* H. Stichtenoth, *Algebraic Function Fields and Codes*, 2nd ed., GTM 254, Springer, 2009,
  Section III.6 and Proposition 3.7.3.
-/

public section

open scoped IntermediateField

/-! ### The genus drop over `𝔽₂(t) ⊆ 𝔽₂(s)` -/

namespace TauCeti.CharTwoGenusDrop

open GenusDrop

/-- `x = u ^ 2` in `F' = 𝔽₂(s)(u)`. -/
noncomputable def genX : RatFunc (RatFunc (ZMod 2)) :=
  RatFunc.X ^ 2

theorem genX_def : genX = RatFunc.X ^ 2 := (rfl)

/-- `y = u ^ 3 + s` in `F' = 𝔽₂(s)(u)`. -/
noncomputable def genY : RatFunc (RatFunc (ZMod 2)) :=
  RatFunc.X ^ 3 + sElement 2

theorem genY_def : genY = RatFunc.X ^ 3 + sElement 2 := (rfl)

/-- The equation `y ^ 2 = x ^ 3 + t` in `F'`, with `t = s ^ 2`. -/
theorem genY_sq : genY ^ 2 = genX ^ 3 + algebraMap (constants 2) _ (radicand 2) := by
  rw [algebraMap_radicand, genX, genY, add_pow_char, ← pow_mul, ← pow_mul]

/-- `y` is transcendental over `k = 𝔽₂(t)`. -/
theorem transcendental_genY : Transcendental (constants 2) genY := by
  -- Otherwise `u ^ 3 = y - s` would be algebraic over `k' = 𝔽₂(s)`.
  intro halg
  have h : IsAlgebraic (RatFunc (ZMod 2)) ((RatFunc.X : RatFunc (RatFunc (ZMod 2))) ^ 3) := by
    have := (halg.tower_top (RatFunc (ZMod 2))).sub
      (isAlgebraic_algebraMap (RatFunc.X : RatFunc (ZMod 2)))
    rwa [genY, sElement_def, add_sub_cancel_right] at this
  exact RatFunc.transcendental_X (IsAlgebraic.of_pow three_pos h)

/-- The function field `F = k(x, y)` of `y ^ 2 = x ^ 3 + t` over `k = 𝔽₂(t)`, inside
`F' = 𝔽₂(s)(u)`. -/
noncomputable def curveField : IntermediateField (constants 2) (RatFunc (RatFunc (ZMod 2))) :=
  (constants 2)⟮genX, genY⟯

theorem curveField_def : curveField = (constants 2)⟮genX, genY⟯ := (rfl)

/-- `x`, as an element of `F`. -/
noncomputable def curveX : curveField :=
  ⟨genX, IntermediateField.subset_adjoin _ _ (Set.mem_insert _ _)⟩

/-- `y`, as an element of `F`. -/
noncomputable def curveY : curveField :=
  ⟨genY, IntermediateField.subset_adjoin _ _ (Set.mem_insert_of_mem _ rfl)⟩

@[simp]
theorem coe_curveX : (curveX : RatFunc (RatFunc (ZMod 2))) = genX := (rfl)

@[simp]
theorem coe_curveY : (curveY : RatFunc (RatFunc (ZMod 2))) = genY := (rfl)

/-- `x` and `y` generate `F` over `k`. -/
theorem adjoin_curveX_curveY_eq_top : (constants 2)⟮curveX, curveY⟯ = ⊤ :=
  IntermediateField.lift_injective _ (by
    rw [IntermediateField.lift_adjoin, IntermediateField.lift_top, Set.image_insert_eq,
      Set.image_singleton, coe_curveX, coe_curveY]
    exact curveField_def.symm)

/-- The equation `y ^ 2 = x ^ 3 + t` in `F`. -/
theorem curveY_sq : curveY ^ 2 = curveX ^ 3 + algebraMap (constants 2) curveField (radicand 2) :=
  Subtype.ext (by simpa using genY_sq)

/-- `y` is transcendental over `k`, as an element of `F`. -/
theorem transcendental_curveY : Transcendental (constants 2) curveY :=
  (transcendental_algebraMap_iff (algebraMap curveField _).injective).mp transcendental_genY

/-- `3` is invertible in `k = 𝔽₂(t)`. -/
private theorem three_ne_zero_constants : (3 : constants 2) ≠ 0 := by
  have h : ((3 : ℕ) : constants 2) ≠ 0 := by
    rw [Ne, CharP.cast_eq_zero_iff _ 2]
    decide
  exact_mod_cast h

/-- `k = 𝔽₂(t)` is the exact constant field of `F`. -/
theorem isIntegrallyClosedIn_curveField : IsIntegrallyClosedIn (constants 2) curveField :=
  isIntegrallyClosedIn_of_sq_eq_pow_three_add three_ne_zero_constants transcendental_curveY
    adjoin_curveX_curveY_eq_top curveY_sq

/-- **The genus of `y ^ 2 = x ^ 3 + t` over `k = 𝔽₂(t)` is one.** -/
theorem genus_curveField : genus (constants 2) curveField = 1 :=
  genus_eq_one_of_sq_eq_pow_three_add three_ne_zero_constants transcendental_curveY
    adjoin_curveX_curveY_eq_top curveY_sq (irreducible_X_pow_sub_C_radicand 2).squarefree

/-- `u = (y + s) / x`. -/
theorem X_eq_genY_add_div :
    (RatFunc.X : RatFunc (RatFunc (ZMod 2))) = (genY + sElement 2) / genX := by
  rw [genY, genX, add_assoc, CharTwo.add_self_eq_zero, add_zero,
    eq_div_iff (pow_ne_zero _ RatFunc.X_ne_zero), ← pow_succ']

/-- **`F' = F · k'`**: the extension `F' / F` is the constant field extension by `k' = 𝔽₂(s)`. -/
theorem constantCompositum_eq_top :
    constantCompositum curveField (RatFunc (ZMod 2)) (RatFunc (RatFunc (ZMod 2))) = ⊤ := by
  set C := constantCompositum curveField (RatFunc (ZMod 2)) (RatFunc (RatFunc (ZMod 2)))
  have hs : sElement 2 ∈ C := by
    rw [sElement_def]
    exact algebraMap_mem_constantCompositum _ _ _ RatFunc.X
  have hx : genX ∈ C := IntermediateField.algebraMap_mem C curveX
  have hy : genY ∈ C := IntermediateField.algebraMap_mem C curveY
  have hX : (RatFunc.X : RatFunc (RatFunc (ZMod 2))) ∈ C := by
    rw [X_eq_genY_add_div]
    exact div_mem (add_mem hy hs) hx
  exact constantCompositum_eq_top_of_X_mem hX

/-- **The genus drops**: `F' / k'` is rational, of genus `0`, while `F / k` has genus `1`. -/
theorem genus_lt_genus :
    genus (RatFunc (ZMod 2)) (RatFunc (RatFunc (ZMod 2))) < genus (constants 2) curveField := by
  rw [genus_ratFunc, genus_curveField]
  exact one_pos

end TauCeti.CharTwoGenusDrop
