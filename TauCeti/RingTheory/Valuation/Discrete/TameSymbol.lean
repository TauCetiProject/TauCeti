/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Valuation.Discrete.UnitPart
public import TauCeti.RingTheory.Valuation.UnitGroup

/-!
# The tame symbol of a discrete valuation

Let `v : F → ℤᵐ⁰` be a valuation on a field `F`, with additive order `ord_v`, valuation ring `𝒪_v`
and residue field `k_v`. For `f, g ∈ Fˣ` the **tame symbol** is
`∂_v{f, g} = (-1) ^ (ord_v f · ord_v g) · res (f ^ ord_v g / g ^ ord_v f) ∈ k_vˣ`,
where `res` denotes reduction of a unit of `𝒪_v` to the residue field.

The element `(-1) ^ (ord_v f · ord_v g) · f ^ ord_v g · g ^ (-ord_v f)` of `Fˣ` has order zero, so
it lies in the unit group of `𝒪_v`; it is `Valuation.tameUnit`, and `Valuation.tameSymbol` is its
residue. At the level of `Fˣ` this unit is already bimultiplicative and inverts when its arguments
are swapped; the tame symbol inherits both properties, and in addition satisfies the Steinberg
relation `∂_v{r, 1 - r} = 1`. Writing `f = t ^ a u` and `g = t ^ b w` with `t` of order one and `u`,
`w` units of `𝒪_v`, the tame symbol is `(-1) ^ (a b) res u ^ b res w ^ (-a)`
(`Valuation.tameSymbol_eq_unitPart`); in particular it does not depend on `t`.

Along a field extension `E / F` with valuations `v` on `F` and `w` on `E` related by
`ord_w r = e · ord_v r` for `r ∈ F`, the tame symbol of two elements of `F` raises to the `e`-th
power: `∂_w{f, g} = ∂_v{f, g} ^ e` in `k_wˣ`, through the residue-field embedding `k_v → k_w`
(`Valuation.tameSymbol_map_algebraMap`). The sign needs no case split on the parity of `e`, since
`e²` and `e` have the same parity. No finiteness of `E / F` is assumed.

With this convention `∂_v{u, t} = res u` and `∂_v{t, u} = (res u)⁻¹` for a unit `u` of `𝒪_v` and
`t` of order one. This is the convention of Dokchitser, de Jeu and Zagier; the tame symbol of
Weibel's *K-book*, Lemma III.6.3, is `∂_v{g, f} = ∂_v{f, g}⁻¹`.

No hypothesis on `v` is needed: the order of a non-surjective `ℤᵐ⁰`-valued valuation is still
additive, and all statements below are about the order rather than about a chosen uniformizer.

## Main definitions

* `Valuation.tameUnit v f g`: the unit `(-1) ^ (ord_v f · ord_v g) f ^ ord_v g g ^ (-ord_v f)` of
  order zero.
* `Valuation.tameSymbol v f g`: its residue, a unit of the residue field of `𝒪_v`.

## Main results

* `Valuation.tameSymbol_mul_left`, `Valuation.tameSymbol_mul_right`: bimultiplicativity.
* `Valuation.tameSymbol_swap`: `∂_v{g, f} = ∂_v{f, g}⁻¹`.
* `Valuation.tameSymbol_of_add_eq_one`: the Steinberg relation `∂_v{r, s} = 1` when `r + s = 1`.
* `Valuation.tameSymbol_of_ord_eq_zero`: the symbol of two units of `𝒪_v` is trivial.
* `Valuation.tameSymbol_coe_left`, `Valuation.tameSymbol_coe_right`:
  `∂_v{u, f} = res u ^ ord_v f` and `∂_v{f, u} = res u ^ (-ord_v f)` for a unit `u` of `𝒪_v`; in
  particular `∂_v{u, t} = res u` and `∂_v{t, u} = (res u)⁻¹` when `ord_v t = 1`
  (`Valuation.tameSymbol_coe_left_of_ord_eq_one`, `Valuation.tameSymbol_coe_right_of_ord_eq_one`).
* `Valuation.tameSymbol_self`: `∂_v{f, f} = (-1) ^ ord_v f`, and `Valuation.tameSymbol_self_neg`:
  `∂_v{f, -f} = 1`.
* `Valuation.tameSymbol_eq_unitPart`: the expression through unit parts relative to any element of
  order one.
* `Valuation.tameSymbol_map_algebraMap`: the ramification formula `∂_w{f, g} = ∂_v{f, g} ^ e`
  along a field extension with `ord_w = e · ord_v` on the base field, and
  `Valuation.tameSymbol_map_algebraMap_of_ord_eq` for the unramified case `e = 1`.

## References

* C. Weibel, *The K-book*, Lemma III.6.3 and Remark III.6.3.1.
* T. Dokchitser, R. de Jeu and D. Zagier, *Numerical verification of Beilinson's conjecture for
  K₂ of hyperelliptic curves*, (3.1).
-/

public section

open scoped WithZero

namespace Valuation

variable {F : Type*} [Field F] (v : Valuation F ℤᵐ⁰)

section TameUnit

/-- The **tame unit** `(-1) ^ (ord_v f · ord_v g) · f ^ ord_v g · g ^ (-ord_v f)` of two field
units. It has order zero (`Valuation.ord_tameUnit`), and its residue is the tame symbol
`Valuation.tameSymbol`. -/
noncomputable def tameUnit (f g : Fˣ) : Fˣ :=
  (-1) ^ (v.ord (f : F) * v.ord (g : F)) * f ^ v.ord (g : F) * g ^ (-v.ord (f : F))

theorem tameUnit_def (f g : Fˣ) : v.tameUnit f g =
    (-1) ^ (v.ord (f : F) * v.ord (g : F)) * f ^ v.ord (g : F) * g ^ (-v.ord (f : F)) :=
  (rfl)

/-- The tame unit has order zero. -/
@[simp]
theorem ord_tameUnit (f g : Fˣ) : v.ord (v.tameUnit f g : F) = 0 := by
  rw [tameUnit_def, Units.val_mul, ord_units_mul, Units.val_mul, ord_units_mul]
  simp [ord_neg]
  ring

/-- The tame unit is a unit of the valuation ring. -/
theorem tameUnit_mem_unitGroup (f g : Fˣ) :
    v.tameUnit f g ∈ v.valuationSubring.unitGroup :=
  (v.mem_unitGroup_iff_ord_eq_zero _).2 (v.ord_tameUnit f g)

/-- The tame unit is multiplicative in its first argument. -/
theorem tameUnit_mul_left (f₁ f₂ g : Fˣ) :
    v.tameUnit (f₁ * f₂) g = v.tameUnit f₁ g * v.tameUnit f₂ g := by
  simp only [tameUnit_def, Units.val_mul, ord_units_mul, add_mul, neg_add, zpow_add, mul_zpow]
  simp only [mul_comm, mul_assoc, mul_left_comm]

/-- The tame unit is multiplicative in its second argument. -/
theorem tameUnit_mul_right (f g₁ g₂ : Fˣ) :
    v.tameUnit f (g₁ * g₂) = v.tameUnit f g₁ * v.tameUnit f g₂ := by
  simp only [tameUnit_def, Units.val_mul, ord_units_mul, mul_add, zpow_add, mul_zpow]
  simp only [mul_comm, mul_assoc, mul_left_comm]

/-- Swapping the arguments inverts the tame unit. -/
theorem tameUnit_swap (f g : Fˣ) : v.tameUnit g f = (v.tameUnit f g)⁻¹ := by
  simp only [tameUnit_def, mul_inv, ← zpow_neg, mul_comm (v.ord (g : F)), ← inv_zpow', inv_neg_one,
    inv_inv]
  simp only [mul_comm, mul_left_comm]

/-- The tame unit of a field unit and a unit of the valuation ring is a power of the latter. -/
theorem tameUnit_coe_right (f : Fˣ) (u : v.valuationSubring.unitGroup) :
    v.tameUnit f u = (u : Fˣ) ^ (-v.ord (f : F)) := by
  have hu := (v.mem_unitGroup_iff_ord_eq_zero _).1 u.property
  simp [tameUnit_def, hu]

/-- The tame unit of a unit of the valuation ring and a field unit is a power of the former. -/
theorem tameUnit_coe_left (u : v.valuationSubring.unitGroup) (f : Fˣ) :
    v.tameUnit u f = (u : Fˣ) ^ v.ord (f : F) := by
  rw [tameUnit_swap, tameUnit_coe_right, zpow_neg, inv_inv]

/-- The tame unit of a field unit with itself is the sign `(-1) ^ ord_v f`. -/
theorem tameUnit_self (f : Fˣ) : v.tameUnit f f = (-1) ^ v.ord (f : F) := by
  rw [tameUnit_def, mul_assoc, ← zpow_add, add_neg_cancel, zpow_zero, mul_one]
  rcases Int.even_or_odd (v.ord (f : F)) with h | h
  · rw [h.neg_one_zpow, (h.mul_left _).neg_one_zpow]
  · rw [h.neg_one_zpow, (h.mul h).neg_one_zpow]

/-- The tame unit through unit parts: if `t` has order one, then
`(-1) ^ (ord_v f · ord_v g) · f ^ ord_v g · g ^ (-ord_v f)` is
`(-1) ^ (ord_v f · ord_v g) · u_f ^ ord_v g · u_g ^ (-ord_v f)`, where `f = t ^ ord_v f · u_f` and
`g = t ^ ord_v g · u_g`. -/
theorem tameUnit_eq_unitPart (t : Fˣ) (ht : v.ord (t : F) = 1) (f g : Fˣ) :
    v.tameUnit f g = (-1) ^ (v.ord (f : F) * v.ord (g : F)) *
      (v.unitPart t ht f : Fˣ) ^ v.ord (g : F) * (v.unitPart t ht g : Fˣ) ^ (-v.ord (f : F)) := by
  simp only [tameUnit_def, coe_unitPart, mul_zpow, zpow_neg]
  group

end TameUnit

section TameSymbol

/-- The **tame symbol**
`∂_v{f, g} = (-1) ^ (ord_v f · ord_v g) · res (f ^ ord_v g / g ^ ord_v f)` of two field units, where
`res` is reduction of a unit of the valuation ring to the residue field. It is the residue of the
tame unit `Valuation.tameUnit`, a unit of the residue field of the valuation ring.

This is the convention in which `∂_v{u, t} = res u` for a unit `u` of the valuation ring and `t` of
order one (`Valuation.tameSymbol_coe_left_of_ord_eq_one`); the tame symbol of Weibel's *K-book*,
Lemma III.6.3, is `v.tameSymbol g f = (v.tameSymbol f g)⁻¹` (`Valuation.tameSymbol_swap`). -/
noncomputable def tameSymbol (f g : Fˣ) : (IsLocalRing.ResidueField v.valuationSubring)ˣ :=
  v.valuationSubring.unitGroupToResidueFieldUnits ⟨v.tameUnit f g, v.tameUnit_mem_unitGroup f g⟩

theorem tameSymbol_def (f g : Fˣ) : v.tameSymbol f g =
    v.valuationSubring.unitGroupToResidueFieldUnits
      ⟨v.tameUnit f g, v.tameUnit_mem_unitGroup f g⟩ :=
  (rfl)

/-- If the tame unit of `f` and `g` is the unit `u` of the valuation ring, then the tame symbol of
`f` and `g` is the residue of `u`. -/
theorem tameSymbol_eq_of_tameUnit_eq {f g : Fˣ} (u : v.valuationSubring.unitGroup)
    (h : v.tameUnit f g = u) :
    v.tameSymbol f g = v.valuationSubring.unitGroupToResidueFieldUnits u :=
  congrArg _ (Subtype.ext h)

/-- The tame symbol is multiplicative in its first argument. -/
theorem tameSymbol_mul_left (f₁ f₂ g : Fˣ) :
    v.tameSymbol (f₁ * f₂) g = v.tameSymbol f₁ g * v.tameSymbol f₂ g := by
  rw [v.tameSymbol_eq_of_tameUnit_eq (⟨_, v.tameUnit_mem_unitGroup f₁ g⟩ *
    ⟨_, v.tameUnit_mem_unitGroup f₂ g⟩) (v.tameUnit_mul_left f₁ f₂ g), map_mul, tameSymbol_def,
    tameSymbol_def]

/-- The tame symbol is multiplicative in its second argument. -/
theorem tameSymbol_mul_right (f g₁ g₂ : Fˣ) :
    v.tameSymbol f (g₁ * g₂) = v.tameSymbol f g₁ * v.tameSymbol f g₂ := by
  rw [v.tameSymbol_eq_of_tameUnit_eq (⟨_, v.tameUnit_mem_unitGroup f g₁⟩ *
    ⟨_, v.tameUnit_mem_unitGroup f g₂⟩) (v.tameUnit_mul_right f g₁ g₂), map_mul, tameSymbol_def,
    tameSymbol_def]

/-- **Swapping the arguments inverts the tame symbol.** In particular the tame symbol of
Weibel's *K-book*, Lemma III.6.3, is `v.tameSymbol g f`. -/
theorem tameSymbol_swap (f g : Fˣ) : v.tameSymbol g f = (v.tameSymbol f g)⁻¹ := by
  rw [v.tameSymbol_eq_of_tameUnit_eq ⟨_, v.tameUnit_mem_unitGroup f g⟩⁻¹ (v.tameUnit_swap f g),
    _root_.map_inv, tameSymbol_def]

/-- The tame symbol of a field unit and a unit `u` of the valuation ring is
`res u ^ (-ord_v f)`. -/
theorem tameSymbol_coe_right (f : Fˣ) (u : v.valuationSubring.unitGroup) :
    v.tameSymbol f u = v.valuationSubring.unitGroupToResidueFieldUnits u ^ (-v.ord (f : F)) := by
  rw [v.tameSymbol_eq_of_tameUnit_eq (u ^ (-v.ord (f : F))) (v.tameUnit_coe_right f u), map_zpow]

/-- The tame symbol of a unit `u` of the valuation ring and a field unit is `res u ^ ord_v f`. -/
theorem tameSymbol_coe_left (u : v.valuationSubring.unitGroup) (f : Fˣ) :
    v.tameSymbol u f = v.valuationSubring.unitGroupToResidueFieldUnits u ^ v.ord (f : F) := by
  rw [v.tameSymbol_eq_of_tameUnit_eq (u ^ v.ord (f : F)) (v.tameUnit_coe_left u f), map_zpow]

/-- The tame symbol of two field units of order zero is trivial. -/
theorem tameSymbol_of_ord_eq_zero {f g : Fˣ} (hf : v.ord (f : F) = 0) (hg : v.ord (g : F) = 0) :
    v.tameSymbol f g = 1 := by
  simpa [hf] using v.tameSymbol_coe_right f ⟨g, (v.mem_unitGroup_iff_ord_eq_zero g).2 hg⟩

/-- The tame symbol with fixed second argument is multiplicative in the first. -/
private noncomputable def tameSymbolLeft (g : Fˣ) :
    Fˣ →* (IsLocalRing.ResidueField v.valuationSubring)ˣ :=
  MonoidHom.mk' (v.tameSymbol · g) fun f₁ f₂ => v.tameSymbol_mul_left f₁ f₂ g

/-- The tame symbol with fixed first argument is multiplicative in the second. -/
private noncomputable def tameSymbolRight (f : Fˣ) :
    Fˣ →* (IsLocalRing.ResidueField v.valuationSubring)ˣ :=
  MonoidHom.mk' (v.tameSymbol f) (v.tameSymbol_mul_right f)

/-- The tame symbol of `1` and a field unit is trivial. -/
@[simp]
theorem tameSymbol_one_left (g : Fˣ) : v.tameSymbol 1 g = 1 := by
  simpa [tameSymbolLeft] using map_one (v.tameSymbolLeft g)

/-- The tame symbol of a field unit and `1` is trivial. -/
@[simp]
theorem tameSymbol_one_right (f : Fˣ) : v.tameSymbol f 1 = 1 := by
  simpa [tameSymbolRight] using map_one (v.tameSymbolRight f)

/-- The tame symbol inverts when its first argument is inverted. -/
theorem tameSymbol_inv_left (f g : Fˣ) : v.tameSymbol f⁻¹ g = (v.tameSymbol f g)⁻¹ := by
  simpa [tameSymbolLeft] using _root_.map_inv (v.tameSymbolLeft g) f

/-- The tame symbol inverts when its second argument is inverted. -/
theorem tameSymbol_inv_right (f g : Fˣ) : v.tameSymbol f g⁻¹ = (v.tameSymbol f g)⁻¹ := by
  simpa [tameSymbolRight] using _root_.map_inv (v.tameSymbolRight f) g

/-- The tame symbol commutes with integer powers of its first argument. -/
theorem tameSymbol_zpow_left (f g : Fˣ) (n : ℤ) :
    v.tameSymbol (f ^ n) g = v.tameSymbol f g ^ n := by
  simpa [tameSymbolLeft] using map_zpow (v.tameSymbolLeft g) f n

/-- The tame symbol commutes with integer powers of its second argument. -/
theorem tameSymbol_zpow_right (f g : Fˣ) (n : ℤ) :
    v.tameSymbol f (g ^ n) = v.tameSymbol f g ^ n := by
  simpa [tameSymbolRight] using map_zpow (v.tameSymbolRight f) g n

/-- The tame symbol of a field unit with itself is `(-1) ^ ord_v f`. -/
theorem tameSymbol_self (f : Fˣ) : v.tameSymbol f f = (-1) ^ v.ord (f : F) := by
  rw [v.tameSymbol_eq_of_tameUnit_eq (⟨-1, v.valuationSubring.neg_one_mem_unitGroup⟩ ^
    v.ord (f : F)) (v.tameUnit_self f), map_zpow,
    ValuationSubring.unitGroupToResidueFieldUnits_neg_one]

/-- The tame symbol of `-1` and a field unit is `(-1) ^ ord_v f`. -/
theorem tameSymbol_neg_one_left (f : Fˣ) : v.tameSymbol (-1) f = (-1) ^ v.ord (f : F) := by
  rw [← ValuationSubring.unitGroupToResidueFieldUnits_neg_one, ← tameSymbol_coe_left]

/-- The tame symbol of a field unit and `-1` is `(-1) ^ ord_v f`. -/
theorem tameSymbol_neg_one_right (f : Fˣ) : v.tameSymbol f (-1) = (-1) ^ v.ord (f : F) := by
  rw [v.tameSymbol_swap (-1) f, tameSymbol_neg_one_left, ← inv_zpow, inv_neg_one]

/-- The tame symbol of `f` and `-f` is trivial. -/
theorem tameSymbol_self_neg (f : Fˣ) : v.tameSymbol f (-f) = 1 := by
  rw [← neg_one_mul, tameSymbol_mul_right, tameSymbol_neg_one_right, tameSymbol_self, ← mul_zpow,
    neg_one_mul, neg_neg, one_zpow]

/-- **The tame symbol of a unit `u` of order zero and an element `t` of order one is the residue
`res u`.** -/
theorem tameSymbol_coe_left_of_ord_eq_one (u : v.valuationSubring.unitGroup) {t : Fˣ}
    (ht : v.ord (t : F) = 1) :
    v.tameSymbol u t = v.valuationSubring.unitGroupToResidueFieldUnits u := by
  rw [tameSymbol_coe_left, ht, zpow_one]

/-- The tame symbol of an element `t` of order one and a unit `u` of order zero is
`(res u)⁻¹`. -/
theorem tameSymbol_coe_right_of_ord_eq_one {t : Fˣ} (ht : v.ord (t : F) = 1)
    (u : v.valuationSubring.unitGroup) :
    v.tameSymbol t u = (v.valuationSubring.unitGroupToResidueFieldUnits u)⁻¹ := by
  rw [tameSymbol_coe_right, ht, zpow_neg_one]

/-- **The tame symbol through unit parts.** Let `t` have order one, and write `f = t ^ a · u` and
`g = t ^ b · w` with `u = v.unitPart t ht f` and `w = v.unitPart t ht g` units of the valuation
ring. Then `∂_v{f, g} = (-1) ^ (a b) · res u ^ b · res w ^ (-a)`. As the left-hand side does not
involve `t`, neither does the right-hand side. -/
theorem tameSymbol_eq_unitPart (t : Fˣ) (ht : v.ord (t : F) = 1) (f g : Fˣ) :
    v.tameSymbol f g = (-1) ^ (v.ord (f : F) * v.ord (g : F)) *
      v.valuationSubring.unitGroupToResidueFieldUnits (v.unitPart t ht f) ^ v.ord (g : F) *
      v.valuationSubring.unitGroupToResidueFieldUnits (v.unitPart t ht g) ^ (-v.ord (f : F)) := by
  rw [v.tameSymbol_eq_of_tameUnit_eq (⟨-1, v.valuationSubring.neg_one_mem_unitGroup⟩ ^
      (v.ord (f : F) * v.ord (g : F)) * v.unitPart t ht f ^ v.ord (g : F) *
      v.unitPart t ht g ^ (-v.ord (f : F))) (v.tameUnit_eq_unitPart t ht f g),
    map_mul, map_mul, map_zpow, map_zpow, map_zpow,
    ValuationSubring.unitGroupToResidueFieldUnits_neg_one]

/-- The Steinberg relation when the first entry has positive order. -/
private theorem tameSymbol_of_add_eq_one_of_ord_pos {r s : Fˣ} (h : (r : F) + s = 1)
    (hr : 0 < v.ord (r : F)) : v.tameSymbol r s = 1 := by
  have hs : (s : F) = 1 + -(r : F) := by rw [← h]; ring
  have hs0 : v.ord (s : F) = 0 := by
    rw [hs, v.ord_add_eq_min_of_ord_ne (by simp) (v.ne_zero_iff.2 (neg_ne_zero.2 r.ne_zero))
      (by rw [ord_one, ord_neg]; omega), ord_one, ord_neg]
    omega
  let u : v.valuationSubring.unitGroup := ⟨s, (v.mem_unitGroup_iff_ord_eq_zero s).2 hs0⟩
  have hu : v.valuationSubring.unitGroupToResidueFieldUnits u = 1 :=
    v.unitGroupToResidueFieldUnits_eq_one_of_ord_sub_one_pos u (by
      rw [show ((u : Fˣ) : F) - 1 = -(r : F) by simp [u, hs], ord_neg]
      exact hr)
  simpa [hu] using v.tameSymbol_coe_right r u

/-- The Steinberg relation when the first entry has negative order, reduced to positive order
through `1 - r⁻¹ = -s r⁻¹`. -/
private theorem tameSymbol_of_add_eq_one_of_ord_neg {r s : Fˣ} (h : (r : F) + s = 1)
    (hr : v.ord (r : F) < 0) : v.tameSymbol r s = 1 := by
  have h' : ((r⁻¹ : Fˣ) : F) + ((-(s * r⁻¹) : Fˣ) : F) = 1 := by
    have hr0 := r.ne_zero
    simp only [Units.val_inv_eq_inv_val, Units.val_neg, Units.val_mul]
    field_simp
    linear_combination -h
  have hs : s = -r * -(s * r⁻¹) := by
    rw [neg_mul_neg, mul_left_comm, mul_inv_cancel, mul_one]
  rw [hs, tameSymbol_mul_right, tameSymbol_self_neg, one_mul, ← inv_inv r, tameSymbol_inv_left,
    inv_inv, tameSymbol_of_add_eq_one_of_ord_pos v h' (by simpa using hr), inv_one]

/-- **The Steinberg relation**: `∂_v{r, s} = 1` whenever `r + s = 1`. -/
theorem tameSymbol_of_add_eq_one {r s : Fˣ} (h : (r : F) + s = 1) : v.tameSymbol r s = 1 := by
  have h' : (s : F) + r = 1 := by rw [add_comm, h]
  rcases lt_trichotomy (v.ord (r : F)) 0 with hr | hr | hr
  · exact v.tameSymbol_of_add_eq_one_of_ord_neg h hr
  · rcases lt_trichotomy (v.ord (s : F)) 0 with hs | hs | hs
    · rw [v.tameSymbol_swap s r, v.tameSymbol_of_add_eq_one_of_ord_neg h' hs, inv_one]
    · exact v.tameSymbol_of_ord_eq_zero hr hs
    · rw [v.tameSymbol_swap s r, v.tameSymbol_of_add_eq_one_of_ord_pos h' hs, inv_one]
  · exact v.tameSymbol_of_add_eq_one_of_ord_pos h hr

end TameSymbol

section Extension

/-! ### Behaviour under a valued field extension -/

variable {E : Type*} [Field E] [Algebra F E] (w : Valuation E ℤᵐ⁰)

/-- **The tame unit along a field extension.** If `ord_w r = e · ord_v r` for every `r ∈ F`, then
the tame unit for `w` of the images of `f, g ∈ Fˣ` is the image of the `e`-th power of the tame
unit for `v`. -/
theorem tameUnit_map_algebraMap {e : ℤ} (h : ∀ r : F, w.ord (algebraMap F E r) = e * v.ord r)
    (f g : Fˣ) :
    w.tameUnit (Units.map (algebraMap F E : F →* E) f) (Units.map (algebraMap F E : F →* E) g) =
      Units.map (algebraMap F E : F →* E) (v.tameUnit f g) ^ e := by
  rw [tameUnit_def, tameUnit_def]
  simp only [Units.coe_map, MonoidHom.coe_ofClass, h, map_mul, map_zpow, Units.map_neg_one,
    mul_zpow, ← zpow_mul]
  congr 2
  · -- The signs agree because `e * e` and `e` have the same parity.
    rw [show e * v.ord (f : F) * (e * v.ord (g : F)) = v.ord (f : F) * v.ord (g : F) * e +
        v.ord (f : F) * v.ord (g : F) * (e * (e - 1)) by ring, zpow_add,
      zpow_mul' (-1) (v.ord (f : F) * v.ord (g : F)) (e * (e - 1)),
      (Int.even_mul_pred_self e).neg_one_zpow, one_zpow, mul_one]
  all_goals congr 1; ring

/-- **The ramification formula for the tame symbol** (Weibel, *K-book*, Remark III.6.3.1). Let
`w` extend `v` along `E / F` with `ord_w r = e · ord_v r` for every `r ∈ F`. Then for
`f, g ∈ Fˣ` the tame symbol for `w` of their images is the `e`-th power of the image of
`∂_v{f, g}` under the residue-field embedding `k_v → k_w`. No finiteness of `E / F` is assumed;
`Valuation.HasExtension.of_ord_algebraMap_eq_mul` provides the extension when `e > 0`. -/
theorem tameSymbol_map_algebraMap [v.HasExtension w] {e : ℤ}
    (h : ∀ r : F, w.ord (algebraMap F E r) = e * v.ord r) (f g : Fˣ) :
    w.tameSymbol (Units.map (algebraMap F E : F →* E) f) (Units.map (algebraMap F E : F →* E) g) =
      Units.map (algebraMap (IsLocalRing.ResidueField v.valuationSubring)
        (IsLocalRing.ResidueField w.valuationSubring) : _ →* _) (v.tameSymbol f g) ^ e := by
  rw [w.tameSymbol_eq_of_tameUnit_eq (⟨_, (HasExtension.map_mem_unitGroup_iff v w).2
      (v.tameUnit_mem_unitGroup f g)⟩ ^ e) (v.tameUnit_map_algebraMap w h f g), map_zpow,
    HasExtension.unitGroupToResidueFieldUnits_map v w (v.tameUnit_mem_unitGroup f g),
    tameSymbol_def]

/-- **The tame symbol along an unramified extension.** If `ord_w r = ord_v r` for every `r ∈ F`,
then the tame symbol for `w` of the images of `f, g ∈ Fˣ` is the image of `∂_v{f, g}` under the
residue-field embedding `k_v → k_w`. Applied to each valuation of a finite extension over `v`, all
unramified, this says that the diagonal embedding of `k_vˣ` carries `∂_v{f, g}` to the family of
tame symbols over `v`. -/
theorem tameSymbol_map_algebraMap_of_ord_eq [v.HasExtension w]
    (h : ∀ r : F, w.ord (algebraMap F E r) = v.ord r) (f g : Fˣ) :
    w.tameSymbol (Units.map (algebraMap F E : F →* E) f) (Units.map (algebraMap F E : F →* E) g) =
      Units.map (algebraMap (IsLocalRing.ResidueField v.valuationSubring)
        (IsLocalRing.ResidueField w.valuationSubring) : _ →* _) (v.tameSymbol f g) := by
  simpa using v.tameSymbol_map_algebraMap w (e := 1) (by simpa using h) f g

end Extension

end Valuation
