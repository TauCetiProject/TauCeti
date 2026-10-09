/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.HilbertSymbol.Basic
public import TauCeti.NumberTheory.Padics.SerreSigns
import Mathlib.NumberTheory.Padics.LocalField
import TauCeti.Algebra.Group.Units.Basic
import TauCeti.NumberTheory.LocalField.Padic
import TauCeti.NumberTheory.LocalField.QuadraticForm.Bimultiplicativity
import TauCeti.NumberTheory.Padics.PadicIntegers

/-!
# The Hilbert symbol over `ℚ_2`

Write `a, b ∈ ℚ_2ˣ` as `a = 2 ^ α u` and `b = 2 ^ β v` with `u, v` units of `ℤ_2`. Serre's
closed formula for the Hilbert symbol over `ℚ_2` is

`(a, b) = (-1) ^ (ε(u) ε(v) + α ω(v) + β ω(u))`,

where `ε(u) = (u − 1)/2` and `ω(u) = (u² − 1)/8` modulo `2` are the sign functions
`TauCeti.serreEps` and `TauCeti.serreOmega`. The exponent lives in `ZMod 2`, and the sign is
`(-1 : ℤˣ) ^ x` for `x : ZMod 2`. This explicit formula over `ℚ_2` pins down the sign
convention of the local Hilbert symbol in residue characteristic `2`.

The classes of `-1`, `2` and `5` form a `ZMod 2`-basis of `ℚ_2ˣ/(ℚ_2ˣ)²`: they generate it, since
every unit of `ℤ_2` is `(-1) ^ ε(u) 5 ^ ω(u)` times a square
(`TauCeti.exists_eq_neg_one_pow_mul_five_pow_mul_sq`), and they are independent because the symbol
is nondegenerate on them. On these generators the symbol takes the values

* `(-1, 2) = (-1, 5) = (2, 2) = (5, 5) = +1`, and
* `(-1, -1) = (2, 5) = −1`,

so in coordinates `x₀, x₁, x₂` along `-1`, `2`, `5` it is `(-1) ^ (x₀ y₀ + x₁ y₂ + x₂ y₁)`. Read
on the eight representatives `1, -1, 5, -5, 2, -2, 10, -10` of the square classes this gives the
full `8 × 8` table of the symbol over `ℚ_2`, the check that pins the dyadic sign convention.

## Main results

* `TauCeti.hilbertSymbol_padicTwo`: Serre's formula for the Hilbert symbol over `ℚ_2`.
* `TauCeti.hilbertSymbol_neg_one_neg_one_padicTwo`: `(-1, -1) = −1` over `ℚ_2`, that is `-1` is
  not of the form `x² + y²` in `ℚ_2`.
* `TauCeti.hilbertSymbol_two_five_padicTwo`: `(2, 5) = −1` over `ℚ_2`.
* `TauCeti.padicTwoSquareClassBasis`: the classes of `-1`, `2`, `5` as a `ZMod 2`-basis of the
  square-class group of `ℚ_2`.
* `TauCeti.hilbertSymbolOnSquareClasses_padicTwo`: the symbol on square classes in the coordinates
  of that basis, that is its Gram matrix.
* `TauCeti.bijective_squareClass_padicTwoSquareClassRep`: `1, -1, 5, -5, 2, -2, 10, -10` represent
  each square class of `ℚ_2` exactly once.
* `TauCeti.hilbertSymbol_padicTwoSquareClassRep`: the `8 × 8` table of the symbol on these
  representatives.

## References

* J.-P. Serre, *A Course in Arithmetic*, Chapter III, §1.2, Theorem 1.
-/

public section

namespace TauCeti

/-- `2` as a unit of `ℚ_2`. -/
private noncomputable abbrev unitTwo : ℚ_[2]ˣ := Units.mk0 2 two_ne_zero

/-- `5` as a unit of `ℚ_2`. -/
private noncomputable abbrev unitFive : ℚ_[2]ˣ := Units.mk0 5 (by norm_num)

private theorem two_ne_zero_padicTwo : (2 : ℚ_[2]) ≠ 0 := two_ne_zero

private noncomputable instance : Invertible (2 : ℚ_[2]) := invertibleOfNonzero two_ne_zero_padicTwo

/-- A unit of `ℤ_2`, read in `ℚ_2ˣ`, is `(-1) ^ ε(u) 5 ^ ω(u)` times a square. -/
private theorem exists_eq_neg_one_zpow_mul_unitFive_zpow_mul_sq {a : ℚ_[2]ˣ} {u : ℤ_[2]ˣ}
    (ha : (a : ℚ_[2]) = u) :
    ∃ w : ℚ_[2]ˣ,
      a = (-1) ^ ((serreEps u).val : ℤ) * unitFive ^ ((serreOmega u).val : ℤ) * w ^ 2 := by
  obtain ⟨w, hw⟩ := exists_eq_neg_one_pow_mul_five_pow_mul_sq u
  have hw0 : ((w : ℤ_[2]) : ℚ_[2]) ≠ 0 := PadicInt.coe_ne_zero.mpr w.ne_zero
  refine ⟨Units.mk0 _ hw0, Units.ext ?_⟩
  rw [ha, hw]
  simp only [Units.val_mul, zpow_natCast, Units.val_pow_eq_pow_val,
    Units.val_neg, Units.val_one, Units.val_mk0]
  norm_cast

/-- Expansion of the symbol in its second argument along the generators `2`, `-1`, `5`. -/
private theorem hilbertSymbol_eq_of_eq_two_zpow_mul (c b : ℚ_[2]ˣ) {β : ℤ} {v : ℤ_[2]ˣ}
    (hb : (b : ℚ_[2]) = 2 ^ β * v) :
    hilbertSymbol c b = hilbertSymbol c unitTwo ^ β *
      hilbertSymbol c (-1) ^ ((serreEps v).val : ℤ) *
        hilbertSymbol c unitFive ^ ((serreOmega v).val : ℤ) := by
  have hv0 : ((v : ℤ_[2]) : ℚ_[2]) ≠ 0 := PadicInt.coe_ne_zero.mpr v.ne_zero
  obtain ⟨w, hw⟩ := exists_eq_neg_one_zpow_mul_unitFive_zpow_mul_sq (a := Units.mk0 _ hv0) rfl
  have hb' : b = unitTwo ^ β * Units.mk0 _ hv0 := Units.ext (by simp [hb])
  rw [hb', hw, hilbertSymbol_mul_right two_ne_zero_padicTwo, hilbertSymbol_mul_sq_right]
  simp only [hilbertSymbol_mul_right two_ne_zero_padicTwo,
    hilbertSymbol_zpow_right two_ne_zero_padicTwo, mul_assoc]

/-- Every element of `ℚ_2ˣ` is `2 ^ β` times a unit of `ℤ_2`. -/
private theorem exists_eq_two_zpow_mul (b : ℚ_[2]ˣ) :
    ∃ (β : ℤ) (v : ℤ_[2]ˣ), (b : ℚ_[2]) = 2 ^ β * v := by
  obtain ⟨v, hv⟩ := Padic.exists_eq_zpow_valuation_mul b.ne_zero
  exact ⟨_, v, by exact_mod_cast hv⟩

/-- A unit of `ℤ_2` that is not `1 mod 8` is a nonsquare of `ℚ_2ˣ`. -/
private theorem not_isSquare_of_toZModPow_ne_one {a : ℚ_[2]ˣ} {u : ℤ_[2]ˣ}
    (ha : (a : ℚ_[2]) = u) (hu : PadicInt.toZModPow 3 (u : ℤ_[2]) ≠ 1) : ¬IsSquare a := by
  rw [← isSquare_units_val_iff, ha, isSquare_coe_iff_mem_unitsPrincipal_three,
    mem_unitsPrincipal_iff_toZModPow]
  exact hu

/-- For a nonsquare `c`, the symbol `(c, ·)` is nontrivial on one of the generators `2`, `-1`,
`5` of `ℚ_2ˣ/(ℚ_2ˣ)²`. -/
private theorem not_hilbertSymbol_generators_eq_one {c : ℚ_[2]ˣ} (hc : ¬IsSquare c)
    (ht : hilbertSymbol c unitTwo = 1) (hm : hilbertSymbol c (-1) = 1)
    (hf : hilbertSymbol c unitFive = 1) : False := by
  -- Nondegeneracy gives `b` with `(c, b) = −1`; expanding `b` in the generators by
  -- bimultiplicativity, the three trivial values give `(c, b) = +1`.
  obtain ⟨b, hb⟩ := exists_hilbertSymbol_eq_neg_one two_ne_zero_padicTwo hc
  obtain ⟨β, v, hv⟩ := exists_eq_two_zpow_mul b
  rw [hilbertSymbol_eq_of_eq_two_zpow_mul c b hv, ht, hm, hf] at hb
  simp at hb

-- The `+1` values on the generators, from explicit solutions of `b = x² − a y²`.
private theorem hilbertSymbol_neg_one_unitTwo : hilbertSymbol (-1) unitTwo = 1 :=
  (hilbertSymbol_eq_one_iff _ _).mpr ⟨1, 1, by norm_num⟩

private theorem hilbertSymbol_neg_one_unitFive : hilbertSymbol (-1) unitFive = 1 :=
  (hilbertSymbol_eq_one_iff _ _).mpr ⟨1, 2, by norm_num⟩

private theorem hilbertSymbol_unitFive_unitFive : hilbertSymbol unitFive unitFive = 1 :=
  (hilbertSymbol_eq_one_iff _ _).mpr ⟨5, 2, by norm_num⟩

/-- `(-1, -1) = −1` over `ℚ_2`: `-1` is not of the form `x² + y²` with `x, y ∈ ℚ_2`. -/
theorem hilbertSymbol_neg_one_neg_one_padicTwo : hilbertSymbol (-1 : ℚ_[2]ˣ) (-1) = -1 := by
  -- `-1` is a nonsquare, and `(-1, 2) = (-1, 5) = +1`, so `(-1, -1)` must be `−1`.
  have hc : ¬IsSquare (-1 : ℚ_[2]ˣ) :=
    not_isSquare_of_toZModPow_ne_one (u := -1) (by simp)
      (by rw [Units.val_neg, Units.val_one, map_neg, map_one]; decide)
  exact (Int.units_eq_one_or _).resolve_left fun h ↦ not_hilbertSymbol_generators_eq_one hc
    hilbertSymbol_neg_one_unitTwo h hilbertSymbol_neg_one_unitFive

/-- `(2, 5) = −1` over `ℚ_2`: `5` is not of the form `x² − 2 y²` with `x, y ∈ ℚ_2`. -/
theorem hilbertSymbol_two_five_padicTwo :
    hilbertSymbol (Units.mk0 (2 : ℚ_[2]) two_ne_zero) (Units.mk0 5 (by norm_num)) = -1 := by
  -- `5` is a nonsquare, and `(5, -1) = (5, 5) = +1`, so `(5, 2)` must be `−1`.
  have hc : ¬IsSquare unitFive := by
    rw [← isSquare_units_val_iff]
    exact Padic.not_isSquare_five
  rw [hilbertSymbol_comm]
  exact (Int.units_eq_one_or _).resolve_left fun h ↦ not_hilbertSymbol_generators_eq_one hc h
    (by rw [hilbertSymbol_comm]; exact hilbertSymbol_neg_one_unitFive)
    hilbertSymbol_unitFive_unitFive

/-- **Serre's formula for the Hilbert symbol over `ℚ_2`.** For `a = 2 ^ α u` and `b = 2 ^ β v`
with `u, v` units of `ℤ_2`,

`(a, b) = (-1) ^ (ε(u) ε(v) + α ω(v) + β ω(u))`,

with the exponent computed in `ZMod 2`. -/
theorem hilbertSymbol_padicTwo {a b : ℚ_[2]ˣ} {α β : ℤ} {u v : ℤ_[2]ˣ}
    (ha : (a : ℚ_[2]) = 2 ^ α * u) (hb : (b : ℚ_[2]) = 2 ^ β * v) :
    hilbertSymbol a b = (-1 : ℤˣ) ^ (serreEps u * serreEps v + (α : ZMod 2) * serreOmega v +
      (β : ZMod 2) * serreOmega u) := by
  have h2m : hilbertSymbol unitTwo (-1) = 1 := by
    rw [hilbertSymbol_comm]
    exact hilbertSymbol_neg_one_unitTwo
  have h5m : hilbertSymbol unitFive (-1) = 1 := by
    rw [hilbertSymbol_comm]
    exact hilbertSymbol_neg_one_unitFive
  have h52 : hilbertSymbol unitFive unitTwo = -1 := by
    rw [hilbertSymbol_comm]
    exact hilbertSymbol_two_five_padicTwo
  -- The symbol of each generator `2`, `-1`, `5` against `a`.
  have hta : hilbertSymbol unitTwo a = (-1) ^ ((serreOmega u).val : ℤ) := by
    simp [hilbertSymbol_eq_of_eq_two_zpow_mul _ a ha, h2m, hilbertSymbol_two_five_padicTwo]
  have hma : hilbertSymbol (-1) a = (-1) ^ ((serreEps u).val : ℤ) := by
    simp [hilbertSymbol_eq_of_eq_two_zpow_mul _ a ha, hilbertSymbol_neg_one_unitTwo,
      hilbertSymbol_neg_one_neg_one_padicTwo, hilbertSymbol_neg_one_unitFive]
  have hfa : hilbertSymbol unitFive a = (-1) ^ α := by
    simp [hilbertSymbol_eq_of_eq_two_zpow_mul _ a ha, h52, h5m]
  rw [hilbertSymbol_eq_of_eq_two_zpow_mul a b hb, hilbertSymbol_comm a, hilbertSymbol_comm a,
    hilbertSymbol_comm a, hta, hma, hfa]
  simp only [← uzpow_intCast (R := ZMod 2), ← uzpow_mul, ← uzpow_add]
  congr 1
  simp only [Int.cast_natCast, ZMod.natCast_zmod_val]
  ring

/-! ### The symbol on a basis of the square classes, and the `8 × 8` table -/

private theorem isUnit_five_padicInt : IsUnit (5 : ℤ_[2]) := by
  rw [PadicInt.isUnit_iff]
  exact_mod_cast PadicInt.norm_natCast_eq_one_iff.mpr (by norm_num)

/-- The unit `(-1) ^ c₀ 5 ^ c₂` of `ℤ_2`. -/
private noncomputable def unitPart (c : Fin 3 → ZMod 2) : ℤ_[2]ˣ :=
  (-1) ^ (c 0).val * isUnit_five_padicInt.unit ^ (c 2).val

/-- The element `(-1) ^ c₀ 2 ^ c₁ 5 ^ c₂` of `ℚ_2ˣ`, the representative of the square class with
coordinates `c` in the basis `-1`, `2`, `5`. -/
private noncomputable def basisProd (c : Fin 3 → ZMod 2) : ℚ_[2]ˣ :=
  (-1) ^ (c 0).val * unitTwo ^ (c 1).val * unitFive ^ (c 2).val

private theorem serreEps_unitPart (c : Fin 3 → ZMod 2) : serreEps (unitPart c) = c 0 := by
  have h5 : serreEps isUnit_five_padicInt.unit = 0 := serreEps_eq_zero_of_coe_eq_five rfl
  rw [unitPart, serreEps_mul]
  have h01 : ∀ t : ZMod 2, t = 0 ∨ t = 1 := by decide
  rcases h01 (c 0) with h | h <;> rcases h01 (c 2) with h' | h' <;> simp [h, h', h5, ZMod.val_one]

private theorem serreOmega_unitPart (c : Fin 3 → ZMod 2) : serreOmega (unitPart c) = c 2 := by
  have h5 : serreOmega isUnit_five_padicInt.unit = 1 := serreOmega_eq_one_of_coe_eq_five rfl
  rw [unitPart, serreOmega_mul]
  have h01 : ∀ t : ZMod 2, t = 0 ∨ t = 1 := by decide
  rcases h01 (c 0) with h | h <;> rcases h01 (c 2) with h' | h' <;> simp [h, h', h5, ZMod.val_one]

private theorem coe_basisProd (c : Fin 3 → ZMod 2) :
    (basisProd c : ℚ_[2]) = 2 ^ ((c 1).val : ℤ) * ((unitPart c : ℤ_[2]) : ℚ_[2]) := by
  have h5 : ((5 : ℤ_[2]) : ℚ_[2]) = 5 := by norm_cast
  rw [zpow_natCast]
  simp [basisProd, unitPart, -ZMod.natCast_val, h5]
  ring

/-- Serre's formula read on the basis `-1`, `2`, `5`: the symbol is `(-1) ^ B(c, d)` for the
bilinear form `B(c, d) = c₀ d₀ + c₁ d₂ + c₂ d₁` over `ZMod 2`. -/
private theorem hilbertSymbol_basisProd (c d : Fin 3 → ZMod 2) :
    hilbertSymbol (basisProd c) (basisProd d) =
      (-1 : ℤˣ) ^ (c 0 * d 0 + c 1 * d 2 + c 2 * d 1) := by
  rw [hilbertSymbol_padicTwo (coe_basisProd c) (coe_basisProd d), serreEps_unitPart,
    serreEps_unitPart, serreOmega_unitPart, serreOmega_unitPart]
  simp only [Int.cast_natCast, ZMod.natCast_zmod_val]
  congr 1
  ring

/-- The square classes of `-1`, `2` and `5`. -/
private noncomputable abbrev basisClass : Fin 3 → SquareClassGroup ℚ_[2] :=
  ![squareClass (-1), squareClass unitTwo, squareClass unitFive]

private theorem sum_smul_basisClass (c : Fin 3 → ZMod 2) :
    ∑ i, c i • basisClass i = squareClass (basisProd c) := by
  have hval (t : ZMod 2) (x : SquareClassGroup ℚ_[2]) : t.val • x = t • x := by
    rw [← Nat.cast_smul_eq_nsmul (ZMod 2) t.val x, ZMod.natCast_zmod_val]
  simp [basisProd, squareClass_mul, Fin.sum_univ_three, hval]

private theorem linearIndependent_basisClass : LinearIndependent (ZMod 2) basisClass := by
  rw [Fintype.linearIndependent_iff]
  intro c hc
  rw [sum_smul_basisClass, squareClass_eq_zero_iff] at hc
  -- A square pairs trivially with every class, and the Gram matrix of `B` is invertible.
  have key (d : Fin 3 → ZMod 2) : (-1 : ℤˣ) ^ (c 0 * d 0 + c 1 * d 2 + c 2 * d 1) = 1 := by
    rw [← hilbertSymbol_basisProd]
    exact hilbertSymbol_eq_one_of_isSquare_left hc _
  have h1 : ∀ t : ZMod 2, (-1 : ℤˣ) ^ t = 1 → t = 0 := by decide
  have h0 := h1 _ (key ![1, 0, 0])
  have h2 := h1 _ (key ![0, 1, 0])
  have h3 := h1 _ (key ![0, 0, 1])
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons, mul_one, mul_zero, add_zero, zero_add] at h0 h2 h3
  intro i
  fin_cases i <;> assumption

private theorem squareClass_mem_span_basisClass (a : ℚ_[2]ˣ) :
    squareClass a ∈ Submodule.span (ZMod 2) (Set.range basisClass) := by
  obtain ⟨β, v, hv⟩ := exists_eq_two_zpow_mul a
  have hv0 : ((v : ℤ_[2]) : ℚ_[2]) ≠ 0 := PadicInt.coe_ne_zero.mpr v.ne_zero
  obtain ⟨w, hw⟩ := exists_eq_neg_one_zpow_mul_unitFive_zpow_mul_sq (a := Units.mk0 _ hv0) rfl
  have ha : a = unitTwo ^ β * Units.mk0 _ hv0 := Units.ext (by simp [hv])
  rw [Submodule.mem_span_range_iff_exists_fun]
  refine ⟨![serreEps v, (β : ZMod 2), serreOmega v], ?_⟩
  have hw2 : squareClass (w ^ 2) = 0 := (squareClass_eq_zero_iff _).mpr (IsSquare.sq w)
  have hz (n : ℤ) (x : SquareClassGroup ℚ_[2]) : n • x = (n : ZMod 2) • x :=
    (Int.cast_smul_eq_zsmul (ZMod 2) n x).symm
  rw [ha, hw]
  simp only [Fin.sum_univ_three, squareClass_mul, hw2, squareClass_zpow, hz, Int.cast_natCast,
    ZMod.natCast_zmod_val, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons]
  abel

/-- **The basis `-1`, `2`, `5` of the square classes of `ℚ_2`.** The classes of `-1`, `2` and `5`
form a `ZMod 2`-basis of `ℚ_2ˣ/(ℚ_2ˣ)²`, which therefore has eight elements. -/
noncomputable def padicTwoSquareClassBasis :
    Module.Basis (Fin 3) (ZMod 2) (SquareClassGroup ℚ_[2]) :=
  .mk linearIndependent_basisClass fun x _ ↦ by
    rw [← squareClass_toMul_out x]
    exact squareClass_mem_span_basisClass _

/-- The basis vectors of `TauCeti.padicTwoSquareClassBasis` are the classes of `-1`, `2`, `5`. -/
@[simp]
theorem coe_padicTwoSquareClassBasis :
    ⇑padicTwoSquareClassBasis =
      ![squareClass (-1), squareClass (Units.mk0 (2 : ℚ_[2]) two_ne_zero),
        squareClass (Units.mk0 (5 : ℚ_[2]) (by norm_num))] :=
  Module.Basis.coe_mk _ _

private theorem squareClass_basisProd_repr (x : SquareClassGroup ℚ_[2]) :
    squareClass (basisProd (padicTwoSquareClassBasis.repr x)) = x := by
  have h := padicTwoSquareClassBasis.sum_repr x
  rw [coe_padicTwoSquareClassBasis] at h
  rw [← sum_smul_basisClass]
  exact h

/-- **The Gram matrix of the Hilbert symbol over `ℚ_2`.** In the coordinates `x₀, x₁, x₂` of a
square class with respect to the basis `-1`, `2`, `5` (`TauCeti.padicTwoSquareClassBasis`), the
Hilbert symbol is `(x, y) = (-1) ^ (x₀ y₀ + x₁ y₂ + x₂ y₁)`. Its Gram matrix

```text
        −1   2   5
  −1     1   0   0
   2     0   0   1
   5     0   1   0
```

is invertible over `ZMod 2`, which is the nondegeneracy of the symbol read on this basis. -/
theorem hilbertSymbolOnSquareClasses_padicTwo (x y : SquareClassGroup ℚ_[2]) :
    hilbertSymbolOnSquareClasses x y = (-1 : ℤˣ) ^
      (padicTwoSquareClassBasis.repr x 0 * padicTwoSquareClassBasis.repr y 0 +
        padicTwoSquareClassBasis.repr x 1 * padicTwoSquareClassBasis.repr y 2 +
        padicTwoSquareClassBasis.repr x 2 * padicTwoSquareClassBasis.repr y 1) := by
  conv_lhs => rw [← squareClass_basisProd_repr x, ← squareClass_basisProd_repr y]
  rw [hilbertSymbolOnSquareClasses_squareClass, hilbertSymbol_basisProd]

/-- The eight representatives `1, -1, 5, -5, 2, -2, 10, -10` of the square classes of `ℚ_2`, in
this order. -/
noncomputable def padicTwoSquareClassRep (i : Fin 8) : ℚ_[2]ˣ :=
  Units.mk0 (![1, -1, 5, -5, 2, -2, 10, -10] i) (by fin_cases i <;> norm_num)

/-- The values of `TauCeti.padicTwoSquareClassRep` in `ℚ_2`. -/
@[simp]
theorem coe_padicTwoSquareClassRep (i : Fin 8) :
    (padicTwoSquareClassRep i : ℚ_[2]) = ![1, -1, 5, -5, 2, -2, 10, -10] i :=
  Units.val_mk0 _

/-- The coordinates of `padicTwoSquareClassRep i` in the basis `-1`, `2`, `5`. -/
private def repCoords : Fin 8 → Fin 3 → ZMod 2 :=
  ![![0, 0, 0], ![1, 0, 0], ![0, 0, 1], ![1, 0, 1], ![0, 1, 0], ![1, 1, 0], ![0, 1, 1],
    ![1, 1, 1]]

private theorem padicTwoSquareClassRep_eq_basisProd (i : Fin 8) :
    padicTwoSquareClassRep i = basisProd (repCoords i) := by
  ext
  fin_cases i <;> simp [basisProd, repCoords, ZMod.val_one] <;> norm_num

/-- `1, -1, 5, -5, 2, -2, 10, -10` represent each square class of `ℚ_2` exactly once. -/
theorem bijective_squareClass_padicTwoSquareClassRep :
    Function.Bijective fun i ↦ squareClass (padicTwoSquareClassRep i) := by
  have hc : Function.Bijective repCoords := by decide
  have h : (fun i ↦ squareClass (padicTwoSquareClassRep i)) =
      padicTwoSquareClassBasis.equivFun.symm ∘ repCoords := by
    ext i
    rw [Function.comp_apply, Module.Basis.equivFun_symm_apply, coe_padicTwoSquareClassBasis,
      padicTwoSquareClassRep_eq_basisProd, ← sum_smul_basisClass]
  rw [h]
  exact padicTwoSquareClassBasis.equivFun.symm.bijective.comp hc

/-- **The `8 × 8` table of the Hilbert symbol over `ℚ_2`** on the representatives
`1, -1, 5, -5, 2, -2, 10, -10` of the square classes (Serre, *A Course in Arithmetic*, III §1.2).
Rows and columns are listed in this order. -/
theorem hilbertSymbol_padicTwoSquareClassRep (i j : Fin 8) :
    hilbertSymbol (padicTwoSquareClassRep i) (padicTwoSquareClassRep j) =
      !![1,  1,  1,  1,  1,  1,  1,  1;
         1, -1,  1, -1,  1, -1,  1, -1;
         1,  1,  1,  1, -1, -1, -1, -1;
         1, -1,  1, -1, -1,  1, -1,  1;
         1,  1, -1, -1,  1,  1, -1, -1;
         1, -1, -1,  1,  1, -1, -1,  1;
         1,  1, -1, -1, -1, -1,  1,  1;
         1, -1, -1,  1, -1,  1,  1, -1] i j := by
  rw [padicTwoSquareClassRep_eq_basisProd, padicTwoSquareClassRep_eq_basisProd,
    hilbertSymbol_basisProd]
  fin_cases i <;> fin_cases j <;> decide

end TauCeti
