/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.FunctionField.Place.Basic
public import TauCeti.RingTheory.Valuation.ExpNeg

/-!
# Places from additive order functions

Order functions met in analysis are usually additive: the order of vanishing `ord_x f` of a
meromorphic function at a point is an additive valuation `F → WithTop ℤ`, with `ord_x 0 = ⊤`.
A place of `F / k` (`TauCeti.Place`) is stored multiplicatively, as a normalized valuation
`F → ℤᵐ⁰`. This file converts the first into the second: a surjective additive valuation
`v : F → WithTop ℤ` vanishing on the nonzero constants of `k` is the place whose valuation is
`f ↦ exp (-v f)`, sending `⊤` to `0` (`AddValuation.expNeg`).

## Main definitions

* `TauCeti.Place.ofAddValuation`: the place of `F / k` with additive order function `v`.

## Main results

* `TauCeti.Place.ord_ofAddValuation`: the order function of `ofAddValuation v` is `v`, read in
  `ℤ` with the junk value `0` at `f = 0`.
* `TauCeti.Place.ofAddValuation_inj`: two additive valuations give the same place exactly when
  they are equal.
-/

public section

open scoped WithZero

namespace TauCeti

namespace Place

variable {k F : Type*} [Field k] [Field F] [Algebra k F]

/-- **The place of an additive order function.** A surjective additive valuation
`v : F → WithTop ℤ` that vanishes on the nonzero constants is a place of `F / k`, whose
valuation is `f ↦ exp (-v f)`. Its order function is `v` (`TauCeti.Place.ord_ofAddValuation`). -/
noncomputable def ofAddValuation (v : AddValuation F (WithTop ℤ)) (hv : Function.Surjective v)
    (hk : ∀ c : k, c ≠ 0 → v (algebraMap k F c) = 0) : Place k F where
  valuation := v.expNeg
  valuation_surjective γ := by
    induction γ using WithZero.expRecOn with
    | zero => exact ⟨0, by rw [map_zero]⟩
    | exp n =>
      obtain ⟨f, hf⟩ := hv (-n : ℤ)
      exact ⟨f, by rw [AddValuation.expNeg_apply, hf, WithTop.expNeg_coe, neg_neg]⟩
  isTrivialOn := ⟨fun c hc ↦ by rw [AddValuation.expNeg_apply, hk c hc, WithTop.expNeg_zero]⟩

variable {v : AddValuation F (WithTop ℤ)} {hv : Function.Surjective v}
  {hk : ∀ c : k, c ≠ 0 → v (algebraMap k F c) = 0}

/-- The valuation of `ofAddValuation v` is `f ↦ exp (-v f)`. -/
@[simp]
theorem valuation_ofAddValuation : (ofAddValuation v hv hk).valuation = v.expNeg :=
  (rfl)

/-- The valuation of `ofAddValuation v` at a function of finite order `n` is `exp (-n)`. -/
theorem valuation_ofAddValuation_of_eq_coe {f : F} {n : ℤ} (hf : v f = n) :
    (ofAddValuation v hv hk).valuation f = WithZero.exp (-n) := by
  rw [valuation_ofAddValuation, AddValuation.expNeg_apply, hf, WithTop.expNeg_coe]

/-- **The order function of `ofAddValuation v` is `v`**, read in `ℤ`: the value `⊤`, taken only
at `0`, becomes the junk value `ord_P 0 = 0`. -/
@[simp]
theorem ord_ofAddValuation (f : F) : (ofAddValuation v hv hk).ord f = (v f).untopD 0 := by
  rcases eq_or_ne f 0 with rfl | hf
  · simp
  obtain ⟨n, hn⟩ := WithTop.ne_top_iff_exists.mp ((v.ne_top_iff).mpr hf)
  rw [ord_def, valuation_ofAddValuation_of_eq_coe hn.symm, WithZero.log_exp, neg_neg, ← hn,
    WithTop.untopD_coe]

/-- For `f ≠ 0`, the order of `f` at `ofAddValuation v` is `v f`. -/
theorem coe_ord_ofAddValuation {f : F} (hf : f ≠ 0) :
    ((ofAddValuation v hv hk).ord f : WithTop ℤ) = v f := by
  obtain ⟨n, hn⟩ := WithTop.ne_top_iff_exists.mp ((v.ne_top_iff).mpr hf)
  rw [ord_ofAddValuation, ← hn, WithTop.untopD_coe]

/-- A function is integral at `ofAddValuation v` exactly when its additive order is
nonnegative. -/
theorem mem_integers_ofAddValuation_iff {f : F} :
    f ∈ (ofAddValuation v hv hk).integers ↔ 0 ≤ v f := by
  rcases eq_or_ne f 0 with rfl | hf
  · simp
  rw [mem_integers_iff_ord_nonneg, ← WithTop.coe_le_coe, coe_ord_ofAddValuation hf,
    WithTop.coe_zero]

/-- **Two additive valuations give the same place exactly when they are equal.** -/
theorem ofAddValuation_inj {w : AddValuation F (WithTop ℤ)} {hw : Function.Surjective w}
    {hk' : ∀ c : k, c ≠ 0 → w (algebraMap k F c) = 0} :
    ofAddValuation v hv hk = ofAddValuation w hw hk' ↔ v = w := by
  refine ⟨fun h ↦ AddValuation.ext fun f ↦ ?_, fun h ↦ by subst h; rfl⟩
  rcases eq_or_ne f 0 with rfl | hf
  · simp
  rw [← coe_ord_ofAddValuation (hv := hv) (hk := hk) hf,
    ← coe_ord_ofAddValuation (hv := hw) (hk := hk') hf, h]

end Place

end TauCeti
