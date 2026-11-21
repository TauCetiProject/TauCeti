/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.LegendreSymbol.Basic
public import Mathlib.NumberTheory.Padics.PadicIntegers
public import Mathlib.NumberTheory.Padics.RingHoms
import TauCeti.NumberTheory.Padics.PadicIntegers
import TauCeti.NumberTheory.Padics.RingHoms
import TauCeti.RingTheory.Henselian.SquareClasses

/-!
# Odd-prime square classes in `ℤ_p`

For an odd prime `p`, `ℤ_p` is a Henselian local ring in which `2` is a unit, so a `p`-adic unit is
a square in `ℤ_p` if and only if its reduction modulo `p` is a square in `𝔽_p`. Equivalently, the
quadratic character of its reduction modulo `p` equals `1`, and a product of `p`-adic units is a
square in `ℤ_p` exactly when the corresponding product of Legendre symbols of integer lifts modulo
`p` matches.

## Main results

* `TauCeti.PadicInt.isSquare_iff_quadraticChar_toZMod_eq_one`: a unit of `ℤ_p` is a square in
  `ℤ_p` exactly when its reduction modulo `p` has quadratic character `1`.
* `TauCeti.PadicInt.isSquare_intCast_iff_legendreSym_eq_one`: an integer prime to `p` is a square
  in `ℤ_p` exactly when it is a square modulo `p`.
* `TauCeti.PadicInt.isSquare_mul_iff_quadraticChar_toZMod_eq`: the product of two units of `ℤ_p` is
  a square in `ℤ_p` exactly when their reductions modulo `p` have equal quadratic characters.
* `TauCeti.PadicInt.isSquare_mul_of_dvd_sub`: two `p`-adic integers congruent modulo `p`, one of
  which is a unit, have a square product in `ℤ_p`.
* `TauCeti.PadicInt.quadraticChar_toZMod_prod_eq_prod_legendreSym` and
  `TauCeti.PadicInt.isSquare_prod_mul_prod_iff_legendreSym_eq`: finite products of `p`-adic units
  have the same square class in `ℤ_p` exactly when the corresponding products of Legendre symbols
  of integer lifts modulo `p` agree.
-/

public section

open IsLocalRing

namespace TauCeti.PadicInt

variable {p : ℕ} [Fact p.Prime]

/-- **Squares of units in `ℤ_p`.** For an odd prime `p`, a unit of `ℤ_p` is a square in `ℤ_p` if
and only if its reduction modulo `p` has quadratic character `1`. -/
theorem isSquare_iff_quadraticChar_toZMod_eq_one (hp : p ≠ 2) {u : ℤ_[p]} (hu : IsUnit u) :
    IsSquare u ↔ quadraticChar (ZMod p) (_root_.PadicInt.toZMod u) = 1 := by
  have hres : IsSquare (residue ℤ_[p] u) ↔ IsSquare (_root_.PadicInt.toZMod u) := by
    rw [_root_.PadicInt.toZMod_eq_residueField_comp_residue, RingHom.comp_apply]
    exact ⟨fun h ↦ h.map _root_.PadicInt.residueField,
      fun h ↦ by simpa using h.map _root_.PadicInt.residueField.symm⟩
  rw [TauCeti.HenselianLocalRing.isSquare_iff_residue_isSquare (_root_.PadicInt.isUnit_two hp) hu,
    hres, quadraticChar_one_iff_isSquare ((_root_.PadicInt.isUnit_iff_toZMod_ne_zero u).mp hu)]

/-- **Squares in `ℤ_p` of integers prime to `p`.** For an odd prime `p` and an integer `n` prime
to `p`, the image of `n` in `ℤ_p` is a square in `ℤ_p` exactly when `n` is a square modulo `p`,
that is `(n / p) = 1`. -/
theorem isSquare_intCast_iff_legendreSym_eq_one (hp : p ≠ 2) {n : ℤ} (hn : ¬ (p : ℤ) ∣ n) :
    IsSquare (n : ℤ_[p]) ↔ legendreSym p n = 1 := by
  have hu : IsUnit (n : ℤ_[p]) := _root_.PadicInt.isUnit_intCast_iff.mpr hn
  simpa [legendreSym] using isSquare_iff_quadraticChar_toZMod_eq_one hp hu

/-- For an odd prime `p`, the product of two units of `ℤ_p` is a square in `ℤ_p` if and only if
their reductions modulo `p` have equal quadratic characters. -/
theorem isSquare_mul_iff_quadraticChar_toZMod_eq (hp : p ≠ 2) {u v : ℤ_[p]}
    (hu : IsUnit u) (hv : IsUnit v) :
    IsSquare (u * v) ↔
      quadraticChar (ZMod p) (_root_.PadicInt.toZMod u) =
        quadraticChar (ZMod p) (_root_.PadicInt.toZMod v) := by
  rw [isSquare_iff_quadraticChar_toZMod_eq_one hp (hu.mul hv), map_mul, map_mul]
  rcases quadraticChar_dichotomy ((_root_.PadicInt.isUnit_iff_toZMod_ne_zero u).mp hu) with
    h1 | h1 <;>
    rcases quadraticChar_dichotomy ((_root_.PadicInt.isUnit_iff_toZMod_ne_zero v).mp hv) with
      h2 | h2 <;>
    simp [h1, h2]

/-- For an odd prime `p`, if two `p`-adic integers agree modulo `p` and one is a unit, then their
product is a square in `ℤ_p`. -/
theorem isSquare_mul_of_dvd_sub (hp : p ≠ 2) {u v : ℤ_[p]} (hu : IsUnit u)
    (huv : (p : ℤ_[p]) ∣ u - v) : IsSquare (u * v) := by
  have hmod : _root_.PadicInt.toZMod u = _root_.PadicInt.toZMod v :=
    (_root_.PadicInt.toZMod_eq_iff_dvd_sub u v).mpr huv
  have hv : IsUnit v := (_root_.PadicInt.isUnit_iff_toZMod_ne_zero v).mpr
    (hmod ▸ (_root_.PadicInt.isUnit_iff_toZMod_ne_zero u).mp hu)
  exact (isSquare_mul_iff_quadraticChar_toZMod_eq hp hu hv).mpr (by rw [hmod])

/-- For a finite family of `p`-adic integers congruent modulo `p` to integers `a i`, the quadratic
character of `∏ i ∈ s, u i` modulo `p` equals `∏ i ∈ s, legendreSym p (a i)`. -/
theorem quadraticChar_toZMod_prod_eq_prod_legendreSym {ι : Type*} (s : Finset ι)
    (u : ι → ℤ_[p]) (a : ι → ℤ) (ha : ∀ i ∈ s, (p : ℤ_[p]) ∣ u i - a i) :
    quadraticChar (ZMod p) (_root_.PadicInt.toZMod (∏ i ∈ s, u i)) =
      ∏ i ∈ s, legendreSym p (a i) := by
  rw [map_prod, map_prod]
  refine Finset.prod_congr rfl fun i hi ↦ ?_
  have hmod : _root_.PadicInt.toZMod (u i) = (a i : ZMod p) := by
    simpa only [map_intCast] using (_root_.PadicInt.toZMod_eq_iff_dvd_sub (u i) (a i)).mpr (ha i hi)
  rw [hmod, legendreSym]

/-- For an odd prime `p` and finite families of `p`-adic units congruent modulo `p` to integers
`a i` and `b j`, the product `(∏ i ∈ s, u i) * (∏ j ∈ t, v j)` is a square in `ℤ_p` if and only if
`∏ i ∈ s, legendreSym p (a i) = ∏ j ∈ t, legendreSym p (b j)`. -/
theorem isSquare_prod_mul_prod_iff_legendreSym_eq (hp : p ≠ 2) {ι κ : Type*}
    (s : Finset ι) (t : Finset κ) (u : ι → ℤ_[p]) (v : κ → ℤ_[p]) (a : ι → ℤ) (b : κ → ℤ)
    (hu : ∀ i ∈ s, IsUnit (u i)) (hv : ∀ j ∈ t, IsUnit (v j))
    (ha : ∀ i ∈ s, (p : ℤ_[p]) ∣ u i - a i) (hb : ∀ j ∈ t, (p : ℤ_[p]) ∣ v j - b j) :
    IsSquare ((∏ i ∈ s, u i) * ∏ j ∈ t, v j) ↔
      ∏ i ∈ s, legendreSym p (a i) = ∏ j ∈ t, legendreSym p (b j) := by
  rw [isSquare_mul_iff_quadraticChar_toZMod_eq hp (IsUnit.prod_iff.mpr hu) (IsUnit.prod_iff.mpr hv),
    quadraticChar_toZMod_prod_eq_prod_legendreSym s u a ha,
    quadraticChar_toZMod_prod_eq_prod_legendreSym t v b hb]

end TauCeti.PadicInt
