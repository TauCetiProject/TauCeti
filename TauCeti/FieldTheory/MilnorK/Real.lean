/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.Coeff
public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.Algebra.Polynomial.Monomial
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Data.ZMod.Basic
public import TauCeti.FieldTheory.MilnorK.Basic
public import TauCeti.FieldTheory.MilnorK.SymbolGroup

/-!
# Real Milnor K-theory and the sign detector

This file constructs the real sign detector on `SymbolGroup ℝ` and `MilnorK ℝ`, proves the
positive-entry divisibility and direct-sum decomposition of `MilnorK.degree ℝ n` (and of
`SymbolGroup ℝ`) for `n ≥ 1`, and identifies the mod-2 quotient of `MilnorK ℝ` with
`Polynomial (ZMod 2)`.

## Main definitions

* `TauCeti.realSign`: the sign map `ℝˣ → ZMod 2` taking negative units to `1` and positive units
  to `0`.
* `TauCeti.realSignPairing`: the Steinberg pairing `(a, b) ↦ realSign a * realSign b` detecting
  `symbol (-1) (-1)`.
* `TauCeti.realSignSymbolHom`: the induced `ℤ`-linear map `SymbolGroup ℝ →ₗ[ℤ] ZMod 2`.
* `TauCeti.MilnorK.realSignRingHom`: the ring homomorphism `MilnorK ℝ →+* Polynomial (ZMod 2)`
  sending `ofUnit a` to `C (realSign a) * X`.
* `TauCeti.MilnorK.realSignDegree`: the degree-`n` coefficient `ℤ`-linear map
  `MilnorK.degree ℝ n →ₗ[ℤ] ZMod 2`.
* `TauCeti.MilnorK.realPositive`: the positive-entry submodule of `MilnorK.degree ℝ n`.
* `TauCeti.SymbolGroup.realPositive`: the positive-entry submodule of `SymbolGroup ℝ`.
* `TauCeti.SymbolGroup.realEquiv`: the `ℤ`-linear equivalence
  `SymbolGroup ℝ ≃ₗ[ℤ] ZMod 2 × SymbolGroup.realPositive`.

## Main results

* `TauCeti.symbol_neg_one_neg_one_ne_zero`: `symbol (-1 : ℝˣ) (-1 : ℝˣ) ≠ 0` in `SymbolGroup ℝ`.
* `TauCeti.MilnorK.symbol_replicate_neg_one_ne_zero`: `MilnorK.symbol (List.replicate n (-1)) ≠ 0`.
* `TauCeti.MilnorK.real_decomposition`: for `n ≥ 1`, `MilnorK.realPositive n` is divisible and
  `MilnorK.degree ℝ n ≃+ ZMod 2 × MilnorK.realPositive n`.
* `TauCeti.MilnorK.real_modTwo_equiv_polynomial`: the quotient of `MilnorK ℝ` by `2 = 0` is
  isomorphic as a ring to `Polynomial (ZMod 2)` via `ofUnit (-1) ↦ X`.

## References

* C. A. Weibel, *The K-book: An Introduction to Algebraic K-Theory*, Examples III.6.2.1 and
  III.7.2(c).
-/

public section

namespace TauCeti

private theorem zmod_two_eq_zero_or_one (c : ZMod 2) : c = 0 ∨ c = 1 := by
  revert c
  decide

private theorem val_one_zmod_two : (1 : ZMod 2).val = 1 := by
  decide

/-! ### The real sign map and Steinberg pairing -/

/-- The sign map `ℝˣ → ZMod 2`, taking negative real units to `1` and positive real units to `0`. -/
noncomputable def realSign (a : ℝˣ) : ZMod 2 :=
  if (a : ℝ) < 0 then 1 else 0

/-- `realSign` takes negative units to `1`. -/
@[simp]
theorem realSign_of_neg {a : ℝˣ} (ha : (a : ℝ) < 0) : realSign a = 1 := by
  simp [realSign, ha]

/-- `realSign` takes positive units to `0`. -/
@[simp]
theorem realSign_of_pos {a : ℝˣ} (ha : 0 < (a : ℝ)) : realSign a = 0 := by
  simp [realSign, not_lt.mpr ha.le]

/-- `realSign` sends `1` to `0`. -/
theorem realSign_one : realSign (1 : ℝˣ) = 0 :=
  realSign_of_pos one_pos

/-- `realSign` sends `-1` to `1`. -/
theorem realSign_neg_one : realSign (-1 : ℝˣ) = 1 :=
  realSign_of_neg (by norm_num)

/-- `realSign` is a homomorphism from `ℝˣ` (multiplicative) to `ZMod 2` (additive). -/
theorem realSign_mul (a b : ℝˣ) : realSign (a * b) = realSign a + realSign b := by
  rcases lt_or_gt_of_ne a.ne_zero with ha | ha <;>
  rcases lt_or_gt_of_ne b.ne_zero with hb | hb
  · have hab : (0 : ℝ) < ((a * b : ℝˣ) : ℝ) := mul_pos_of_neg_of_neg ha hb
    rw [realSign_of_pos hab, realSign_of_neg ha, realSign_of_neg hb]
    decide
  · have hab : ((a * b : ℝˣ) : ℝ) < 0 := mul_neg_of_neg_of_pos ha hb
    rw [realSign_of_neg hab, realSign_of_neg ha, realSign_of_pos hb, add_zero]
  · have hab : ((a * b : ℝˣ) : ℝ) < 0 := mul_neg_of_pos_of_neg ha hb
    rw [realSign_of_neg hab, realSign_of_pos ha, realSign_of_neg hb, zero_add]
  · have hab : (0 : ℝ) < ((a * b : ℝˣ) : ℝ) := mul_pos ha hb
    rw [realSign_of_pos hab, realSign_of_pos ha, realSign_of_pos hb, add_zero]

/-- The real sign pairing `ℝˣ → ℝˣ → ZMod 2`, equal to `1` if and only if both units are
negative. -/
noncomputable def realSignPairing (a b : ℝˣ) : ZMod 2 :=
  realSign a * realSign b

/-- `realSignPairing a b = 1` if and only if both `a` and `b` are negative. -/
theorem realSignPairing_eq_one_iff (a b : ℝˣ) :
    realSignPairing a b = 1 ↔ (a : ℝ) < 0 ∧ (b : ℝ) < 0 := by
  rcases lt_or_gt_of_ne a.ne_zero with ha | ha <;>
  rcases lt_or_gt_of_ne b.ne_zero with hb | hb
  · simp [realSignPairing, ha, hb]
  · simp [realSignPairing, realSign_of_neg ha, realSign_of_pos hb, not_lt.mpr hb.le]
  · simp [realSignPairing, realSign_of_pos ha, realSign_of_neg hb, not_lt.mpr ha.le]
  · simp [realSignPairing, realSign_of_pos ha, realSign_of_pos hb, not_lt.mpr ha.le]

/-- `realSignPairing (-1) (-1) = 1`. -/
@[simp]
theorem realSignPairing_neg_one_neg_one : realSignPairing (-1 : ℝˣ) (-1 : ℝˣ) = 1 := by
  simp [realSignPairing]

/-- `realSignPairing a b = 0` whenever `a` is positive. -/
theorem realSignPairing_of_pos_left {a : ℝˣ} (ha : 0 < (a : ℝ)) (b : ℝˣ) :
    realSignPairing a b = 0 := by
  simp [realSignPairing, realSign_of_pos ha]

/-- `realSignPairing a b = 0` whenever `b` is positive. -/
theorem realSignPairing_of_pos_right (a : ℝˣ) {b : ℝˣ} (hb : 0 < (b : ℝ)) :
    realSignPairing a b = 0 := by
  simp [realSignPairing, realSign_of_pos hb]

/-- `realSignPairing` is a Steinberg pairing on `ℝ` with values in `ZMod 2`. -/
theorem isSteinbergPairing_realSignPairing : IsSteinbergPairing realSignPairing where
  map_mul_left a₁ a₂ b := by
    simp only [realSignPairing, realSign_mul, add_mul]
  map_mul_right a b₁ b₂ := by
    simp only [realSignPairing, realSign_mul, mul_add]
  steinberg := by
    intro a b hab
    rcases lt_or_gt_of_ne a.ne_zero with ha | ha
    · have hb : 0 < (b : ℝ) := by linarith
      exact realSignPairing_of_pos_right a hb
    · exact realSignPairing_of_pos_left ha b

/-- The `ℤ`-linear sign map `SymbolGroup ℝ →ₗ[ℤ] ZMod 2` induced by `realSignPairing`. -/
noncomputable def realSignSymbolHom : SymbolGroup ℝ →ₗ[ℤ] ZMod 2 :=
  SymbolGroup.lift realSignPairing isSteinbergPairing_realSignPairing

/-- On generators, `realSignSymbolHom` evaluates `realSignPairing`. -/
@[simp]
theorem realSignSymbolHom_symbol (a b : ℝˣ) :
    realSignSymbolHom (symbol a b) = realSignPairing a b :=
  SymbolGroup.lift_symbol realSignPairing isSteinbergPairing_realSignPairing a b

/-- The symbol `{-1, -1}` is nonzero in `SymbolGroup ℝ`. -/
theorem symbol_neg_one_neg_one_ne_zero : symbol (-1 : ℝˣ) (-1 : ℝˣ) ≠ 0 := by
  intro h
  have h1 : realSignSymbolHom (symbol (-1 : ℝˣ) (-1 : ℝˣ)) = 0 := by rw [h, map_zero]
  rw [realSignSymbolHom_symbol, realSignPairing_neg_one_neg_one] at h1
  exact one_ne_zero h1

/-! ### Positive real `m`-th roots -/

private theorem exists_pos_unit_pow_eq {b : ℝˣ} (hb : 0 < (b : ℝ)) {m : ℕ} (hm : 0 < m) :
    ∃ c : ℝˣ, 0 < (c : ℝ) ∧ c ^ m = b := by
  have hr : 0 < (b : ℝ) ^ ((m : ℝ)⁻¹) := Real.rpow_pos_of_pos hb _
  refine ⟨Units.mk0 ((b : ℝ) ^ ((m : ℝ)⁻¹)) hr.ne', hr, ?_⟩
  ext
  simpa using Real.rpow_inv_natCast_pow hb.le hm.ne'

private theorem neg_one_sq_units : (-1 : ℝˣ) ^ 2 = 1 := by
  ext
  norm_num

/-! ### Positive-entry subgroup and decomposition of `SymbolGroup ℝ` -/

namespace SymbolGroup

/-- The positive-entry submodule of `SymbolGroup ℝ`, generated by symbols `{a, b}` with `a > 0`
or `b > 0`. -/
def realPositive : Submodule ℤ (SymbolGroup ℝ) :=
  Submodule.span ℤ {x | ∃ a b : ℝˣ, (0 < (a : ℝ) ∨ 0 < (b : ℝ)) ∧ x = symbol a b}

/-- A real symbol with positive left entry belongs to `SymbolGroup.realPositive`. -/
theorem symbol_mem_realPositive_left {a : ℝˣ} (ha : 0 < (a : ℝ)) (b : ℝˣ) :
    symbol a b ∈ realPositive :=
  Submodule.subset_span ⟨a, b, Or.inl ha, rfl⟩

/-- A real symbol with positive right entry belongs to `SymbolGroup.realPositive`. -/
theorem symbol_mem_realPositive_right (a : ℝˣ) {b : ℝˣ} (hb : 0 < (b : ℝ)) :
    symbol a b ∈ realPositive :=
  Submodule.subset_span ⟨a, b, Or.inr hb, rfl⟩

/-- Multiplication by any positive integer is surjective on `SymbolGroup.realPositive`. -/
theorem surjective_nsmul_realPositive {m : ℕ} (hm : 0 < m) :
    Function.Surjective (fun x : realPositive ↦ m • x) := by
  intro ⟨x, hx⟩
  suffices ∃ y ∈ realPositive, m • y = x by
    obtain ⟨y, hy, rfl⟩ := this
    exact ⟨⟨y, hy⟩, rfl⟩
  refine Submodule.span_induction ?_ ?_ ?_ ?_ hx
  · rintro _ ⟨a, b, ha | hb, rfl⟩
    · obtain ⟨c, hc, rfl⟩ := exists_pos_unit_pow_eq ha hm
      exact ⟨symbol c b, symbol_mem_realPositive_left hc b, (symbol_pow_left c b m).symm⟩
    · obtain ⟨c, hc, rfl⟩ := exists_pos_unit_pow_eq hb hm
      exact ⟨symbol a c, symbol_mem_realPositive_right a hc, (symbol_pow_right a c m).symm⟩
  · exact ⟨0, Submodule.zero_mem _, smul_zero m⟩
  · rintro _ _ _ _ ⟨y₁, hy₁, rfl⟩ ⟨y₂, hy₂, rfl⟩
    exact ⟨y₁ + y₂, Submodule.add_mem _ hy₁ hy₂, smul_add m y₁ y₂⟩
  · rintro k _ _ ⟨y, hy, rfl⟩
    exact ⟨k • y, Submodule.smul_mem _ k hy, smul_comm m k y⟩

private theorem two_nsmul_symbol_neg_one_neg_one :
    2 • symbol (-1 : ℝˣ) (-1 : ℝˣ) = 0 := by
  rw [← symbol_pow_left, neg_one_sq_units, symbol_one_left]

private def negOneAddHom : ZMod 2 →+ SymbolGroup ℝ where
  toFun ε := ε.val • symbol (-1 : ℝˣ) (-1 : ℝˣ)
  map_zero' := by simp
  map_add' ε₁ ε₂ := by
    rcases zmod_two_eq_zero_or_one ε₁ with rfl | rfl <;>
    rcases zmod_two_eq_zero_or_one ε₂ with rfl | rfl
    · simp
    · simp
    · simp
    · rw [show (1 : ZMod 2) + 1 = 0 by decide]
      simp only [ZMod.val_zero, ZMod.val_one, zero_smul, one_smul]
      rw [← two_nsmul, two_nsmul_symbol_neg_one_neg_one]

private def negOneHom : ZMod 2 →ₗ[ℤ] SymbolGroup ℝ :=
  negOneAddHom.toIntLinearMap

private theorem realSignSymbolHom_negOneHom (ε : ZMod 2) :
    realSignSymbolHom (negOneHom ε) = ε := by
  rcases zmod_two_eq_zero_or_one ε with rfl | rfl <;> simp [negOneHom, negOneAddHom]

private theorem sub_negOneHom_mem_realPositive (x : SymbolGroup ℝ) :
    x - negOneHom (realSignSymbolHom x) ∈ realPositive := by
  induction x using SymbolGroup.inductionOn with
  | symbol a b =>
    rcases lt_or_gt_of_ne a.ne_zero with ha | ha
    · rcases lt_or_gt_of_ne b.ne_zero with hb | hb
      · have ha' : 0 < ((-a : ℝˣ) : ℝ) := by simpa using neg_pos.mpr ha
        have hb' : 0 < ((-b : ℝˣ) : ℝ) := by simpa using neg_pos.mpr hb
        have hdecomp : symbol a b =
            symbol (-1 : ℝˣ) (-1 : ℝˣ) + symbol (-1 : ℝˣ) (-b) +
              (symbol (-a) (-1 : ℝˣ) + symbol (-a) (-b)) := by
          have ha_eq : a = (-1 : ℝˣ) * (-a) := by ext; simp
          have hb_eq : b = (-1 : ℝˣ) * (-b) := by ext; simp
          conv_lhs => rw [ha_eq, hb_eq]
          rw [symbol_mul_left, symbol_mul_right, symbol_mul_right]
        have hsign : realSignSymbolHom (symbol a b) = 1 := by
          rw [realSignSymbolHom_symbol]
          exact (realSignPairing_eq_one_iff a b).mpr ⟨ha, hb⟩
        rw [hsign]
        have hneg : negOneHom (1 : ZMod 2) = symbol (-1 : ℝˣ) (-1 : ℝˣ) := by
          simp [negOneHom, negOneAddHom, val_one_zmod_two]
        rw [hneg, hdecomp, add_assoc, add_sub_cancel_left]
        exact Submodule.add_mem _ (symbol_mem_realPositive_right _ hb')
          (Submodule.add_mem _ (symbol_mem_realPositive_left ha' _)
            (symbol_mem_realPositive_left ha' _))
      · have hsign : realSignSymbolHom (symbol a b) = 0 := by
          rw [realSignSymbolHom_symbol]
          exact realSignPairing_of_pos_right a hb
        rw [hsign, map_zero, sub_zero]
        exact symbol_mem_realPositive_right a hb
    · have hsign : realSignSymbolHom (symbol a b) = 0 := by
        rw [realSignSymbolHom_symbol]
        exact realSignPairing_of_pos_left ha b
      rw [hsign, map_zero, sub_zero]
      exact symbol_mem_realPositive_left ha b
  | add x y hx hy =>
    have h : (x + y) - negOneHom (realSignSymbolHom (x + y)) =
        (x - negOneHom (realSignSymbolHom x)) + (y - negOneHom (realSignSymbolHom y)) := by
      rw [map_add, map_add]
      abel
    rw [h]
    exact Submodule.add_mem _ hx hy

/-- The kernel of `realSignSymbolHom` is precisely `SymbolGroup.realPositive`. -/
theorem ker_realSignSymbolHom : LinearMap.ker realSignSymbolHom = realPositive := by
  refine le_antisymm ?_ ?_
  · intro x hx
    rw [LinearMap.mem_ker] at hx
    simpa [hx] using sub_negOneHom_mem_realPositive x
  · rw [realPositive, Submodule.span_le]
    rintro _ ⟨a, b, ha | hb, rfl⟩
    · simp [LinearMap.mem_ker, realSignPairing_of_pos_left ha b]
    · simp [LinearMap.mem_ker, realSignPairing_of_pos_right a hb]

/-- The class `{-1, -1}` does not belong to `SymbolGroup.realPositive`. -/
theorem symbol_neg_one_neg_one_notMem_realPositive :
    symbol (-1 : ℝˣ) (-1 : ℝˣ) ∉ realPositive := by
  rw [← ker_realSignSymbolHom, LinearMap.mem_ker, realSignSymbolHom_symbol,
    realSignPairing_neg_one_neg_one]
  exact one_ne_zero

/-- The canonical `ℤ`-linear equivalence `SymbolGroup ℝ ≃ₗ[ℤ] ZMod 2 × SymbolGroup.realPositive`,
sending `d ∈ realPositive` to `(0, d)` and `symbol (-1) (-1)` to `(1, 0)`. -/
noncomputable def realEquiv : SymbolGroup ℝ ≃ₗ[ℤ] ZMod 2 × realPositive :=
  LinearEquiv.ofLinearMap
    { toFun := fun x ↦
        (realSignSymbolHom x,
          ⟨x - negOneHom (realSignSymbolHom x), sub_negOneHom_mem_realPositive x⟩)
      map_add' := fun x y ↦ by
        refine Prod.ext (map_add realSignSymbolHom x y) (Subtype.ext ?_)
        change (x + y) - negOneHom (realSignSymbolHom (x + y)) =
          (x - negOneHom (realSignSymbolHom x)) + (y - negOneHom (realSignSymbolHom y))
        rw [map_add, map_add]
        abel
      map_smul' := fun k x ↦ by
        refine Prod.ext (map_smul realSignSymbolHom k x) (Subtype.ext ?_)
        change k • x - negOneHom (realSignSymbolHom (k • x)) =
          k • (x - negOneHom (realSignSymbolHom x))
        rw [map_smul, map_smul, smul_sub] }
    { toFun := fun p ↦ negOneHom p.1 + p.2.val
      map_add' := fun p q ↦ by
        simp only [Prod.fst_add, Prod.snd_add, map_add, Submodule.coe_add]
        abel
      map_smul' := fun k p ↦ by
        simp only [Prod.smul_fst, Prod.smul_snd, map_smul, Submodule.coe_smul, smul_add,
          RingHom.id_apply] }
    (LinearMap.ext fun p ↦ by
      have hp : realSignSymbolHom p.2.val = 0 := by
        rw [← LinearMap.mem_ker, ker_realSignSymbolHom]
        exact p.2.property
      refine Prod.ext ?_ (Subtype.ext ?_)
      · change realSignSymbolHom (negOneHom p.1 + p.2.val) = p.1
        rw [map_add, realSignSymbolHom_negOneHom, hp, add_zero]
      · change (negOneHom p.1 + p.2.val) -
            negOneHom (realSignSymbolHom (negOneHom p.1 + p.2.val)) = p.2.val
        rw [map_add, realSignSymbolHom_negOneHom, hp, add_zero, add_sub_cancel_left])
    (LinearMap.ext fun x ↦ by
      change negOneHom (realSignSymbolHom x) + (x - negOneHom (realSignSymbolHom x)) = x
      exact add_sub_cancel _ _)

/-- `SymbolGroup.realEquiv` sends every element of `realPositive` into the second factor. -/
@[simp]
theorem realEquiv_coe_realPositive (d : realPositive) : realEquiv d.val = (0, d) := by
  have hd : realSignSymbolHom d.val = 0 := by
    rw [← LinearMap.mem_ker, ker_realSignSymbolHom]
    exact d.property
  refine Prod.ext ?_ (Subtype.ext ?_)
  · exact hd
  · change d.val - negOneHom (realSignSymbolHom d.val) = d.val
    rw [hd, map_zero, sub_zero]

/-- `SymbolGroup.realEquiv` sends `symbol (-1) (-1)` to `(1, 0)`. -/
@[simp]
theorem realEquiv_symbol_neg_one_neg_one :
    realEquiv (symbol (-1 : ℝˣ) (-1 : ℝˣ)) = (1, 0) := by
  have h1 : realSignSymbolHom (symbol (-1 : ℝˣ) (-1 : ℝˣ)) = 1 := by simp
  refine Prod.ext h1 (Subtype.ext ?_)
  change symbol (-1 : ℝˣ) (-1 : ℝˣ) -
      negOneHom (realSignSymbolHom (symbol (-1 : ℝˣ) (-1 : ℝˣ))) = 0
  rw [h1]
  simp [negOneHom, negOneAddHom, val_one_zmod_two]

end SymbolGroup

/-! ### Graded polynomial detector and decomposition of `MilnorK ℝ` -/

namespace MilnorK

/-- The graded ring homomorphism `MilnorK ℝ →+* Polynomial (ZMod 2)` sending `ofUnit a` to
`C (realSign a) * X`. -/
noncomputable def realSignRingHom : MilnorK ℝ →+* Polynomial (ZMod 2) :=
  lift (fun a ↦ Polynomial.C (realSign a) * Polynomial.X)
    (fun a b ↦ by rw [realSign_mul, map_add, add_mul])
    (fun a b hab ↦ by
      have h0 : realSign a * realSign b = 0 :=
        isSteinbergPairing_realSignPairing.steinberg hab
      calc
        Polynomial.C (realSign a) * Polynomial.X * (Polynomial.C (realSign b) * Polynomial.X)
            = Polynomial.C (realSign a * realSign b) * Polynomial.X ^ 2 := by
              rw [map_mul]
              ring
        _ = 0 := by rw [h0, map_zero, zero_mul])

/-- `realSignRingHom` sends `ofUnit a` to `C (realSign a) * X`. -/
@[simp]
theorem realSignRingHom_ofUnit (a : ℝˣ) :
    realSignRingHom (ofUnit a) = Polynomial.C (realSign a) * Polynomial.X :=
  lift_ofUnit _ _ _ a

/-- `realSignRingHom` sends a real Milnor symbol `{a₁, …, aₙ}` to
`C (∏ i, realSign aᵢ) * X ^ n`. -/
theorem realSignRingHom_symbol (l : List ℝˣ) :
    realSignRingHom (symbol l) = Polynomial.C (l.map realSign).prod * Polynomial.X ^ l.length := by
  induction l with
  | nil => simp
  | cons a l ih =>
    rw [symbol_cons, map_mul, realSignRingHom_ofUnit, ih, List.map_cons, List.prod_cons,
      List.length_cons, map_mul, pow_succ]
    ring

/-- `realSignRingHom` sends `{-1, …, -1}` (length `n`) to `X ^ n`. -/
@[simp]
theorem realSignRingHom_symbol_replicate_neg_one (n : ℕ) :
    realSignRingHom (symbol (List.replicate n (-1 : ℝˣ))) = Polynomial.X ^ n := by
  rw [realSignRingHom_symbol, List.map_replicate, List.prod_replicate, realSign_neg_one, one_pow,
    map_one, one_mul, List.length_replicate]

/-- For every `n`, the `n`-fold symbol `{-1, …, -1}` is nonzero in `MilnorK ℝ`. -/
theorem symbol_replicate_neg_one_ne_zero (n : ℕ) :
    symbol (List.replicate n (-1 : ℝˣ)) ≠ 0 := by
  intro h
  have h0 : ((Polynomial.X : Polynomial (ZMod 2)) ^ n).coeff n = 0 := by
    rw [← realSignRingHom_symbol_replicate_neg_one, h, map_zero, Polynomial.coeff_zero]
  rw [Polynomial.coeff_X_pow_self] at h0
  exact one_ne_zero h0

/-- The `ℤ`-linear degree-`n` sign detector `MilnorK.degree ℝ n →ₗ[ℤ] ZMod 2`, obtained by taking
the degree-`n` coefficient of `realSignRingHom`. -/
noncomputable def realSignDegree (n : ℕ) : degree ℝ n →ₗ[ℤ] ZMod 2 where
  toFun x := (realSignRingHom x.val).coeff n
  map_add' x y := by
    simp only [Submodule.coe_add, map_add, Polynomial.coeff_add]
  map_smul' k x := by
    simp only [SetLike.val_smul, map_zsmul, RingHom.id_apply]
    exact (Polynomial.lcoeff (ZMod 2) n).toAddMonoidHom.map_zsmul k (realSignRingHom x.val)

/-- On a degree-`n` symbol, `realSignDegree n` evaluates the product of signs of its entries. -/
theorem realSignDegree_symbol {l : List ℝˣ} {n : ℕ} (hl : l.length = n) :
    realSignDegree n ⟨symbol l, symbol_mem_degree_of_length hl⟩ = (l.map realSign).prod := by
  change (realSignRingHom (symbol l)).coeff n = (l.map realSign).prod
  rw [realSignRingHom_symbol, hl, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow_self, mul_one]

/-- `realSignDegree n` vanishes on any symbol containing a positive entry. -/
theorem realSignDegree_symbol_of_exists_pos {l : List ℝˣ} {n : ℕ} (hl : l.length = n)
    (hpos : ∃ b ∈ l, 0 < (b : ℝ)) :
    realSignDegree n ⟨symbol l, symbol_mem_degree_of_length hl⟩ = 0 := by
  rw [realSignDegree_symbol hl]
  obtain ⟨b, hb, hbpos⟩ := hpos
  exact List.prod_eq_zero (List.mem_map.mpr ⟨b, hb, realSign_of_pos hbpos⟩)

/-- `realSignDegree n` equals `1` on any symbol whose entries are all negative. -/
theorem realSignDegree_symbol_of_forall_neg {l : List ℝˣ} {n : ℕ} (hl : l.length = n)
    (hneg : ∀ b ∈ l, (b : ℝ) < 0) :
    realSignDegree n ⟨symbol l, symbol_mem_degree_of_length hl⟩ = 1 := by
  rw [realSignDegree_symbol hl]
  refine List.prod_eq_one fun c hc ↦ ?_
  obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hc
  exact realSign_of_neg (hneg b hb)

/-- `realSignDegree n` sends `{-1, …, -1}` to `1`. -/
@[simp]
theorem realSignDegree_symbol_replicate_neg_one (n : ℕ) :
    realSignDegree n ⟨symbol (List.replicate n (-1 : ℝˣ)),
      symbol_mem_degree_of_length List.length_replicate⟩ = 1 :=
  realSignDegree_symbol_of_forall_neg List.length_replicate fun b hb ↦ by
    rw [List.eq_of_mem_replicate hb]
    norm_num

/-- The positive-entry subgroup in the degree-`n` real Milnor group. -/
noncomputable def realPositive (n : ℕ) : Submodule ℤ (degree ℝ n) :=
  Submodule.comap (degree ℝ n).subtype
    (Submodule.span ℤ {x | ∃ a : List ℝˣ, a.length = n ∧
      (∃ b ∈ a, 0 < (b : ℝ)) ∧ x = symbol a})

private def realPositiveAmbient (n : ℕ) : Submodule ℤ (MilnorK ℝ) :=
  Submodule.span ℤ {x | ∃ a : List ℝˣ, a.length = n ∧ (∃ b ∈ a, 0 < (b : ℝ)) ∧ x = symbol a}

private theorem realPositiveAmbient_le_degree (n : ℕ) :
    realPositiveAmbient n ≤ degree ℝ n := by
  rw [realPositiveAmbient, Submodule.span_le]
  rintro _ ⟨a, ha, _, rfl⟩
  exact symbol_mem_degree_of_length ha

/-- A real symbol of length `n` with a positive entry lies in `MilnorK.realPositive n`. -/
theorem symbol_mem_realPositive {l : List ℝˣ} {n : ℕ} (hl : l.length = n)
    (hpos : ∃ b ∈ l, 0 < (b : ℝ)) :
    (⟨symbol l, symbol_mem_degree_of_length hl⟩ : degree ℝ n) ∈ realPositive n :=
  Submodule.subset_span ⟨l, hl, hpos, rfl⟩

/-- Multiplication by any positive integer is surjective on `MilnorK.realPositive n`. -/
theorem surjective_nsmul_realPositive (n : ℕ) {m : ℕ} (hm : 0 < m) :
    Function.Surjective (fun x : realPositive n ↦ m • x) := by
  intro ⟨⟨x, hx_deg⟩, hx_pos⟩
  have hx_amb : x ∈ realPositiveAmbient n := hx_pos
  suffices ∃ y ∈ realPositiveAmbient n, m • y = x by
    obtain ⟨y, hy, rfl⟩ := this
    exact ⟨⟨⟨y, realPositiveAmbient_le_degree n hy⟩, hy⟩, rfl⟩
  refine Submodule.span_induction ?_ ?_ ?_ ?_ hx_amb
  · rintro _ ⟨a, ha, ⟨b, hb, hbpos⟩, rfl⟩
    obtain ⟨l₁, l₂, rfl⟩ := List.append_of_mem hb
    obtain ⟨c, hc, rfl⟩ := exists_pos_unit_pow_eq hbpos hm
    refine ⟨symbol (l₁ ++ c :: l₂), Submodule.subset_span ⟨l₁ ++ c :: l₂, ?_, ?_, rfl⟩,
      (symbol_pow_at l₁ c m l₂).symm⟩
    · simpa [List.length_append] using ha
    · exact ⟨c, by simp, hc⟩
  · exact ⟨0, Submodule.zero_mem _, smul_zero m⟩
  · rintro _ _ _ _ ⟨y₁, hy₁, rfl⟩ ⟨y₂, hy₂, rfl⟩
    exact ⟨y₁ + y₂, Submodule.add_mem _ hy₁ hy₂, smul_add m y₁ y₂⟩
  · rintro k _ _ ⟨y, hy, rfl⟩
    exact ⟨k • y, Submodule.smul_mem _ k hy, smul_comm m k y⟩

/-- In positive degree, `{-1, …, -1}` is 2-torsion in `MilnorK ℝ`. -/
theorem two_nsmul_symbol_replicate_neg_one {n : ℕ} (hn : 1 ≤ n) :
    2 • symbol (List.replicate n (-1 : ℝˣ)) = 0 := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  rw [List.replicate_succ, symbol_cons]
  have h2 : 2 • ofUnit (-1 : ℝˣ) = 0 := by
    rw [← ofUnit_pow, neg_one_sq_units, ofUnit_one]
  rw [← smul_mul_assoc 2 (ofUnit (-1 : ℝˣ)), h2, zero_mul]

private theorem ofUnit_mul_mem_realPositiveAmbient {n : ℕ} (u : ℝˣ) {d : MilnorK ℝ}
    (hd : d ∈ realPositiveAmbient n) :
    ofUnit u * d ∈ realPositiveAmbient (n + 1) := by
  refine Submodule.span_induction ?_ ?_ ?_ ?_ hd
  · rintro _ ⟨a, ha, ⟨b, hb, hbpos⟩, rfl⟩
    rw [← symbol_cons]
    exact Submodule.subset_span ⟨u :: a, by simp [ha], ⟨b, List.mem_cons_of_mem u hb, hbpos⟩, rfl⟩
  · rw [mul_zero]
    exact Submodule.zero_mem _
  · intro x y _ _ hx hy
    rw [mul_add]
    exact Submodule.add_mem _ hx hy
  · intro k x _ hx
    rw [mul_smul_comm k (ofUnit u)]
    exact Submodule.smul_mem _ k hx

private theorem exists_realPositiveAmbient_decomp :
    ∀ l : List ℝˣ, l ≠ [] →
      ∃ (c : ℤ) (d : MilnorK ℝ), d ∈ realPositiveAmbient l.length ∧
        symbol l = c • symbol (List.replicate l.length (-1 : ℝˣ)) + d
  | [], h => absurd rfl h
  | [u], _ => by
    rcases lt_or_gt_of_ne u.ne_zero with hu | hu
    · have hu' : 0 < ((-u : ℝˣ) : ℝ) := by simpa using neg_pos.mpr hu
      have hu_eq : u = (-1 : ℝˣ) * (-u) := by ext; simp
      refine ⟨1, symbol [-u], Submodule.subset_span ⟨[-u], rfl, ⟨-u, by simp, hu'⟩, rfl⟩, ?_⟩
      simp only [List.length_singleton, List.replicate_one, symbol_singleton, one_zsmul]
      conv_lhs => rw [hu_eq]
      exact ofUnit_mul (-1 : ℝˣ) (-u)
    · refine ⟨0, symbol [u], Submodule.subset_span ⟨[u], rfl, ⟨u, by simp, hu⟩, rfl⟩, ?_⟩
      simp
  | u :: a :: rest, _ => by
    rcases lt_or_gt_of_ne u.ne_zero with hu | hu
    · obtain ⟨c, d, hd, hsym⟩ :=
        exists_realPositiveAmbient_decomp (a :: rest) (List.cons_ne_nil _ _)
      have hu' : 0 < ((-u : ℝˣ) : ℝ) := by simpa using neg_pos.mpr hu
      have hu_eq : u = (-1 : ℝˣ) * (-u) := by ext; simp
      refine ⟨c, ofUnit (-1 : ℝˣ) * d + symbol ((-u) :: a :: rest),
        Submodule.add_mem _ (ofUnit_mul_mem_realPositiveAmbient (-1 : ℝˣ) hd)
          (Submodule.subset_span ⟨(-u) :: a :: rest, rfl, ⟨-u, by simp, hu'⟩, rfl⟩), ?_⟩
      calc
        symbol (u :: a :: rest)
            = ofUnit u * symbol (a :: rest) := symbol_cons u (a :: rest)
        _ = (ofUnit (-1 : ℝˣ) + ofUnit (-u)) * symbol (a :: rest) := by
              rw [← ofUnit_mul, ← hu_eq]
        _ = ofUnit (-1 : ℝˣ) * symbol (a :: rest) + ofUnit (-u) * symbol (a :: rest) :=
              add_mul _ _ _
        _ = ofUnit (-1 : ℝˣ) * (c • symbol (List.replicate (a :: rest).length (-1 : ℝˣ)) + d) +
              symbol ((-u) :: a :: rest) := by
              rw [← symbol_cons (-u), hsym]
        _ = c • (ofUnit (-1 : ℝˣ) * symbol (List.replicate (a :: rest).length (-1 : ℝˣ))) +
              (ofUnit (-1 : ℝˣ) * d + symbol ((-u) :: a :: rest)) := by
              rw [mul_add, mul_smul_comm c (ofUnit (-1 : ℝˣ)), add_assoc]
        _ = c • symbol (List.replicate (u :: a :: rest).length (-1 : ℝˣ)) +
              (ofUnit (-1 : ℝˣ) * d + symbol ((-u) :: a :: rest)) := by
              rw [← symbol_cons, ← List.replicate_succ]
              rfl
    · refine ⟨0, symbol (u :: a :: rest),
        Submodule.subset_span ⟨u :: a :: rest, rfl, ⟨u, by simp, hu⟩, rfl⟩, ?_⟩
      simp

private def eNegOne (n : ℕ) : degree ℝ n :=
  ⟨symbol (List.replicate n (-1 : ℝˣ)), symbol_mem_degree_of_length List.length_replicate⟩

private def negOneDegreeAddHom (n : ℕ) (hn : 1 ≤ n) : ZMod 2 →+ degree ℝ n where
  toFun ε := ε.val • eNegOne n
  map_zero' := by simp
  map_add' ε₁ ε₂ := by
    rcases zmod_two_eq_zero_or_one ε₁ with rfl | rfl <;>
    rcases zmod_two_eq_zero_or_one ε₂ with rfl | rfl
    · simp
    · simp
    · simp
    · rw [show (1 : ZMod 2) + 1 = 0 by decide]
      simp only [ZMod.val_zero, ZMod.val_one, zero_smul, one_smul]
      rw [← two_nsmul]
      exact Subtype.ext (two_nsmul_symbol_replicate_neg_one hn).symm

private def negOneDegreeHom (n : ℕ) (hn : 1 ≤ n) : ZMod 2 →ₗ[ℤ] degree ℝ n :=
  (negOneDegreeAddHom n hn).toIntLinearMap

private theorem realSignDegree_negOneDegreeHom {n : ℕ} (hn : 1 ≤ n) (ε : ZMod 2) :
    realSignDegree n (negOneDegreeHom n hn ε) = ε := by
  rcases zmod_two_eq_zero_or_one ε with rfl | rfl
  · simp [negOneDegreeHom, negOneDegreeAddHom]
  · change realSignDegree n ((1 : ZMod 2).val • eNegOne n) = 1
    simp [val_one_zmod_two, eNegOne]

private theorem realSignDegree_eq_zero_of_mem_realPositive {n : ℕ} {x : degree ℝ n}
    (hx : x ∈ realPositive n) :
    realSignDegree n x = 0 := by
  have hx_amb : x.val ∈ realPositiveAmbient n := hx
  change (realSignRingHom x.val).coeff n = 0
  refine Submodule.span_induction ?_ ?_ ?_ ?_ hx_amb
  · rintro _ ⟨a, ha, hpos, rfl⟩
    exact realSignDegree_symbol_of_exists_pos ha hpos
  · simp
  · intro u v _ _ hu hv
    simp [hu, hv]
  · intro k u _ hu
    have hk : (realSignRingHom (k • u)).coeff n = k • (realSignRingHom u).coeff n := by
      rw [map_zsmul]
      exact (Polynomial.lcoeff (ZMod 2) n).toAddMonoidHom.map_zsmul k (realSignRingHom u)
    rw [hk, hu, smul_zero]

private theorem sub_negOneDegreeHom_mem_realPositive {n : ℕ} (hn : 1 ≤ n) (x : degree ℝ n) :
    x - negOneDegreeHom n hn (realSignDegree n x) ∈ realPositive n := by
  induction x using degree_inductionOn with
  | zero => simp
  | symbol l hl =>
    have hne : l ≠ [] := by intro h; subst h; simp at hl; omega
    obtain ⟨c, d, hd, hsym⟩ := exists_realPositiveAmbient_decomp l hne
    rw [hl] at hd hsym
    have hd_deg : d ∈ degree ℝ n := realPositiveAmbient_le_degree n hd
    let d' : degree ℝ n := ⟨d, hd_deg⟩
    have hx_eq : (⟨symbol l, symbol_mem_degree_of_length hl⟩ : degree ℝ n) =
        c • eNegOne n + d' := Subtype.ext hsym
    have hsign : realSignDegree n ⟨symbol l, symbol_mem_degree_of_length hl⟩ = (c : ZMod 2) := by
      rw [hx_eq, map_add, map_zsmul, realSignDegree_eq_zero_of_mem_realPositive (x := d') hd,
        add_zero]
      change c • realSignDegree n (eNegOne n) = (c : ZMod 2)
      rw [eNegOne, realSignDegree_symbol_replicate_neg_one, zsmul_eq_mul, mul_one]
    have hneg_c : negOneDegreeHom n hn (c : ZMod 2) = c • eNegOne n := by
      have hc : (c : ZMod 2) = c • (1 : ZMod 2) := by rw [zsmul_eq_mul, mul_one]
      rw [hc, map_zsmul]
      congr 1
      simp [negOneDegreeHom, negOneDegreeAddHom, val_one_zmod_two]
    rw [hsign, hneg_c, hx_eq, add_sub_cancel_left]
    exact hd
  | add x y hx hy =>
    have h : (x + y) - negOneDegreeHom n hn (realSignDegree n (x + y)) =
        (x - negOneDegreeHom n hn (realSignDegree n x)) +
          (y - negOneDegreeHom n hn (realSignDegree n y)) := by
      rw [map_add, map_add]
      abel
    rw [h]
    exact Submodule.add_mem _ hx hy
  | smul k x hx =>
    have h : k • x - negOneDegreeHom n hn (realSignDegree n (k • x)) =
        k • (x - negOneDegreeHom n hn (realSignDegree n x)) := by
      rw [map_smul, map_smul, smul_sub]
    rw [h]
    exact Submodule.smul_mem _ k hx

/-- For every `n ≥ 1`, the kernel of `realSignDegree n` is `MilnorK.realPositive n`. -/
theorem ker_realSignDegree {n : ℕ} (hn : 1 ≤ n) :
    LinearMap.ker (realSignDegree n) = realPositive n := by
  refine le_antisymm ?_ ?_
  · intro x hx
    rw [LinearMap.mem_ker] at hx
    simpa [hx] using sub_negOneDegreeHom_mem_realPositive hn x
  · intro x hx
    exact realSignDegree_eq_zero_of_mem_realPositive hx

/-- For every `n ≥ 1`, the canonical `ℤ`-linear equivalence
`MilnorK.degree ℝ n ≃ₗ[ℤ] ZMod 2 × MilnorK.realPositive n`. -/
noncomputable def realEquiv (n : ℕ) (hn : 1 ≤ n) :
    degree ℝ n ≃ₗ[ℤ] ZMod 2 × realPositive n :=
  LinearEquiv.ofLinearMap
    { toFun := fun x ↦
        (realSignDegree n x,
          ⟨x - negOneDegreeHom n hn (realSignDegree n x),
            sub_negOneDegreeHom_mem_realPositive hn x⟩)
      map_add' := fun x y ↦ by
        refine Prod.ext (map_add (realSignDegree n) x y) (Subtype.ext ?_)
        change (x + y) - negOneDegreeHom n hn (realSignDegree n (x + y)) =
          (x - negOneDegreeHom n hn (realSignDegree n x)) +
            (y - negOneDegreeHom n hn (realSignDegree n y))
        rw [map_add, map_add]
        abel
      map_smul' := fun k x ↦ by
        refine Prod.ext (map_smul (realSignDegree n) k x) (Subtype.ext ?_)
        change k • x - negOneDegreeHom n hn (realSignDegree n (k • x)) =
          k • (x - negOneDegreeHom n hn (realSignDegree n x))
        rw [map_smul, map_smul, smul_sub] }
    { toFun := fun p ↦ negOneDegreeHom n hn p.1 + p.2.val
      map_add' := fun p q ↦ by
        simp only [Prod.fst_add, Prod.snd_add, map_add, Submodule.coe_add]
        abel
      map_smul' := fun k p ↦ by
        simp only [Prod.smul_fst, Prod.smul_snd, map_smul, Submodule.coe_smul, smul_add,
          RingHom.id_apply] }
    (LinearMap.ext fun p ↦ by
      refine Prod.ext ?_ (Subtype.ext ?_)
      · change realSignDegree n (negOneDegreeHom n hn p.1 + p.2.val) = p.1
        rw [map_add, realSignDegree_negOneDegreeHom,
          realSignDegree_eq_zero_of_mem_realPositive p.2.property, add_zero]
      · change (negOneDegreeHom n hn p.1 + p.2.val) -
            negOneDegreeHom n hn (realSignDegree n (negOneDegreeHom n hn p.1 + p.2.val)) =
          p.2.val
        rw [map_add, realSignDegree_negOneDegreeHom,
          realSignDegree_eq_zero_of_mem_realPositive p.2.property, add_zero, add_sub_cancel_left])
    (LinearMap.ext fun x ↦ by
      change negOneDegreeHom n hn (realSignDegree n x) +
          (x - negOneDegreeHom n hn (realSignDegree n x)) = x
      exact add_sub_cancel _ _)

/-- Over `ℝ`, the positive-entry subgroup is divisible and complements the order-two class
`{-1, …, -1}` in every positive degree. -/
theorem real_decomposition (n : ℕ) (hn : 1 ≤ n) :
    (∀ m : ℕ, 0 < m → Function.Surjective (fun x : realPositive n ↦ m • x)) ∧
    ∃ e : degree ℝ n ≃+ ZMod 2 × realPositive n,
      (∀ d : realPositive n, e d.val = (0, d)) ∧
      ∀ x : degree ℝ n,
        x.val = symbol (List.replicate n (-1 : ℝˣ)) → e x = (1, 0) := by
  refine ⟨fun m hm ↦ surjective_nsmul_realPositive n hm, (realEquiv n hn).toAddEquiv, ?_, ?_⟩
  · intro d
    have hd : realSignDegree n d.val = 0 := realSignDegree_eq_zero_of_mem_realPositive d.property
    refine Prod.ext hd (Subtype.ext ?_)
    change d.val - negOneDegreeHom n hn (realSignDegree n d.val) = d.val
    rw [hd, map_zero, sub_zero]
  · intro x hx
    have hx_eq : x = eNegOne n := Subtype.ext hx
    subst hx_eq
    have h1 : realSignDegree n (eNegOne n) = 1 := realSignDegree_symbol_replicate_neg_one n
    refine Prod.ext h1 (Subtype.ext ?_)
    change eNegOne n - negOneDegreeHom n hn (realSignDegree n (eNegOne n)) = 0
    rw [h1]
    simp [negOneDegreeHom, negOneDegreeAddHom, val_one_zmod_two]

/-- The real Milnor ring modulo `2` is isomorphic as a ring to `Polynomial (ZMod 2)`, sending the
degree-one class of `-1` to `Polynomial.X`. -/
theorem real_modTwo_equiv_polynomial :
    let r : MilnorK ℝ → MilnorK ℝ → Prop := fun x y ↦ x = 2 ∧ y = 0
    ∃ e : RingQuot r ≃+* Polynomial (ZMod 2),
      e (RingQuot.mkRingHom r (ofUnit (-1 : ℝˣ))) = Polynomial.X := by
  intro r
  have h2_mk : RingQuot.mkRingHom r (2 : MilnorK ℝ) = 0 := by
    simpa only [map_zero] using RingQuot.mkRingHom_rel (r := r) (show r 2 0 from ⟨rfl, rfl⟩)
  have h2_ring : (2 : RingQuot r) = 0 := by
    simpa only [map_ofNat] using h2_mk
  have h2_poly : (2 : Polynomial (ZMod 2)) = 0 := by
    rw [← map_ofNat (Polynomial.C (R := ZMod 2)), show (2 : ZMod 2) = 0 by decide, map_zero]
  have hrel : ∀ ⦃x y : MilnorK ℝ⦄, r x y → realSignRingHom x = realSignRingHom y := by
    rintro _ _ ⟨rfl, rfl⟩
    rw [map_zero, map_ofNat, h2_poly]
  let f : RingQuot r →+* Polynomial (ZMod 2) := RingQuot.lift ⟨realSignRingHom, hrel⟩
  have hf_mk : ∀ x : MilnorK ℝ, f (RingQuot.mkRingHom r x) = realSignRingHom x := fun x ↦
    RingQuot.lift_mkRingHom_apply realSignRingHom hrel x
  let base : ZMod 2 →+* RingQuot r :=
    { toFun := fun c ↦ if c = 0 then 0 else 1
      map_one' := by simp
      map_mul' := fun a b ↦ by
        rcases zmod_two_eq_zero_or_one a with rfl | rfl <;>
        rcases zmod_two_eq_zero_or_one b with rfl | rfl <;> simp
      map_zero' := by simp
      map_add' := fun a b ↦ by
        rcases zmod_two_eq_zero_or_one a with rfl | rfl <;>
        rcases zmod_two_eq_zero_or_one b with rfl | rfl
        · simp
        · simp
        · simp
        · rw [show (1 : ZMod 2) + 1 = 0 by decide]
          simp only [↓reduceIte, one_ne_zero]
          rw [one_add_one_eq_two, h2_ring] }
  let g : Polynomial (ZMod 2) →+* RingQuot r :=
    Polynomial.eval₂RingHom' base (RingQuot.mkRingHom r (ofUnit (-1 : ℝˣ))) fun c ↦ by
      rcases zmod_two_eq_zero_or_one c with rfl | rfl <;> simp [base]
  have hfg : f.comp g = RingHom.id (Polynomial (ZMod 2)) := by
    refine Polynomial.ringHom_ext' ?_ ?_
    · refine RingHom.ext fun c ↦ ?_
      rcases zmod_two_eq_zero_or_one c with rfl | rfl <;> simp [g, base]
    · simp [g, hf_mk]
  have hmk_pos : ∀ a : ℝˣ, 0 < (a : ℝ) → RingQuot.mkRingHom r (ofUnit a) = 0 := by
    intro a ha
    obtain ⟨c, _, rfl⟩ := exists_pos_unit_pow_eq ha (by omega : 0 < 2)
    rw [ofUnit_pow, two_nsmul, map_add, ← two_mul, h2_ring, zero_mul]
  have hgf : g.comp f = RingHom.id (RingQuot r) := by
    refine RingQuot.ringQuot_ext (g.comp f) (RingHom.id (RingQuot r))
      (MilnorK.ringHom_ext fun a ↦ ?_)
    simp only [RingHom.comp_apply, RingHom.id_apply, hf_mk, realSignRingHom_ofUnit]
    rcases lt_or_gt_of_ne a.ne_zero with ha | ha
    · have ha' : 0 < ((-a : ℝˣ) : ℝ) := by simpa using neg_pos.mpr ha
      have ha_eq : a = (-1 : ℝˣ) * (-a) := by ext; simp
      rw [realSign_of_neg ha, map_one, one_mul]
      conv_rhs => rw [ha_eq, ofUnit_mul, map_add, hmk_pos (-a) ha', add_zero]
      simp [g]
    · rw [realSign_of_pos ha, map_zero, zero_mul, map_zero, hmk_pos a ha]
  refine ⟨{ toFun := f
            invFun := g
            left_inv := fun x ↦ RingHom.congr_fun hgf x
            right_inv := fun p ↦ RingHom.congr_fun hfg p
            map_mul' := f.map_mul
            map_add' := f.map_add }, ?_⟩
  change f (RingQuot.mkRingHom r (ofUnit (-1 : ℝˣ))) = Polynomial.X
  rw [hf_mk, realSignRingHom_ofUnit, realSign_neg_one, map_one, one_mul]

end MilnorK

end TauCeti
