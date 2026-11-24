/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.Padics.PadicIntegers
public import TauCeti.GroupTheory.SpecificGroups.Affine.Basic

/-!
# The `p`-adic affine groups `P(ℤ_p) ⊆ P(ℚ_p)`

Write `P(R)` for the affine group `TauCeti.AffineGroup R` of a ring `R`, the mirabolic group of
matrices `(a b; 0 1)`. This file studies `P(ℤ_p)` inside `P(ℚ_p)`, through the element
`φ = diag(p, 1)`, the dilation `x ↦ p x` of `ℚ_p`.

An element of `P(ℚ_p)` comes from `P(ℤ_p)` exactly when its translation part is integral and its
linear part is a `p`-adic unit. Conjugation by `φ` multiplies translation parts by `p`, and every
`g ∈ P(ℚ_p)` is brought into `P(ℤ_p)` by multiplying by suitable powers of `φ` on both sides.

## Main definitions

* `TauCeti.AffineGroup.padicPhi`: the element `φ = diag(p, 1)` of `P(ℚ_p)`.

## Main results

* `TauCeti.AffineGroup.exists_map_padicInt_eq_iff`: the integrality criterion for `P(ℤ_p)`.
* `TauCeti.AffineGroup.norm_map_smul_le_one_iff`: elements of `P(ℤ_p)` preserve `ℤ_p ⊆ ℚ_p`.
* `TauCeti.AffineGroup.padicPhi_mul_map_mul_inv`: `φ (b, a) φ⁻¹ = (p b, a)`.
* `TauCeti.AffineGroup.exists_map_eq_padicPhi_pow_mul_mul_inv_pow`: for every `g ∈ P(ℚ_p)` and
  `n`, some `φ^m g φ^{-l}` with `n ≤ m` lies in `P(ℤ_p)`.
-/

public noncomputable section

namespace TauCeti.AffineGroup

variable (p : ℕ) [hp : Fact p.Prime]

/-- The element `φ = diag(p, 1)` of `P(ℚ_p)`, the dilation `x ↦ p x`. -/
def padicPhi : AffineGroup ℚ_[p] :=
  SemidirectProduct.inr (Units.mk0 (p : ℚ_[p]) (Nat.cast_ne_zero.mpr hp.out.ne_zero))

/-- `φ` has no translation part. -/
@[simp]
theorem padicPhi_left : (padicPhi p).left = 1 :=
  (rfl)

/-- `φ` is the dilation by `p`. -/
@[simp]
theorem coe_padicPhi_right : ((padicPhi p).right : ℚ_[p]) = p :=
  (rfl)

/-- `φ` acts on `ℚ_p` by `x ↦ p x`. -/
@[simp]
theorem padicPhi_smul (x : ℚ_[p]) : padicPhi p • x = (p : ℚ_[p]) * x := by
  simp [smul_def]

/-- `φ^k` has no translation part. -/
@[simp]
theorem padicPhi_pow_left (k : ℕ) : (padicPhi p ^ k).left = 1 := by
  simp [padicPhi, ← map_pow]

/-- `φ^k` is the dilation by `p^k`. -/
@[simp]
theorem coe_padicPhi_pow_right (k : ℕ) : ((padicPhi p ^ k).right : ℚ_[p]) = (p : ℚ_[p]) ^ k := by
  simp [padicPhi, ← map_pow]

/-- `φ^k` acts on `ℚ_p` by `x ↦ p^k x`. -/
@[simp]
theorem padicPhi_pow_smul (k : ℕ) (x : ℚ_[p]) : padicPhi p ^ k • x = (p : ℚ_[p]) ^ k * x := by
  simp [smul_def]

variable {p}

/-- The translation part of `φ^m g φ^{-l}` is `p^m` times that of `g`. -/
theorem toAdd_padicPhi_pow_mul_mul_inv_pow_left (m l : ℕ) (g : AffineGroup ℚ_[p]) :
    (padicPhi p ^ m * g * (padicPhi p ^ l)⁻¹).left.toAdd = (p : ℚ_[p]) ^ m * g.left.toAdd := by
  simp [padicPhi, ← map_pow]

/-- The linear part of `φ^m g φ^{-l}` is `p^(m - l)` times that of `g`. -/
theorem coe_padicPhi_pow_mul_mul_inv_pow_right (m l : ℕ) (g : AffineGroup ℚ_[p]) :
    ((padicPhi p ^ m * g * (padicPhi p ^ l)⁻¹).right : ℚ_[p]) =
      (p : ℚ_[p]) ^ m * g.right * ((p : ℚ_[p]) ^ l)⁻¹ := by
  simp [padicPhi, ← map_pow]

/-- The norm of the linear part of `φ^m g φ^{-l}` is `p^(l - m)` times that of `g`. -/
theorem norm_coe_padicPhi_pow_mul_mul_inv_pow_right (m l : ℕ) (g : AffineGroup ℚ_[p]) :
    ‖((padicPhi p ^ m * g * (padicPhi p ^ l)⁻¹).right : ℚ_[p])‖ =
      (p : ℝ) ^ ((l : ℤ) - m) * ‖(g.right : ℚ_[p])‖ := by
  rw [coe_padicPhi_pow_mul_mul_inv_pow_right]
  simp [zpow_sub₀ (Nat.cast_ne_zero.mpr hp.out.ne_zero : (p : ℝ) ≠ 0)]
  ring

/-- An element of `P(ℚ_p)` comes from `P(ℤ_p)` exactly when its translation part is integral
and its linear part is a unit of `ℤ_p`. -/
theorem exists_map_padicInt_eq_iff (g : AffineGroup ℚ_[p]) :
    (∃ h : AffineGroup ℤ_[p], map PadicInt.Coe.ringHom h = g) ↔
      ‖g.left.toAdd‖ ≤ 1 ∧ ‖(g.right : ℚ_[p])‖ = 1 := by
  constructor
  · rintro ⟨h, rfl⟩
    simp only [toAdd_map_left, PadicInt.Coe.ringHom_apply, coe_map_right]
    exact ⟨PadicInt.norm_le_one _, PadicInt.isUnit_iff.mp h.right.isUnit⟩
  · rintro ⟨hb, ha⟩
    refine ⟨⟨.ofAdd (Padic.lift _ hb), PadicInt.mkUnits ha⟩, ?_⟩
    ext
    · rw [toAdd_map_left, toAdd_ofAdd, PadicInt.Coe.ringHom_apply, PadicInt.coe_lift]
    · rw [coe_map_right, PadicInt.Coe.ringHom_apply, PadicInt.mkUnits_eq]

/-- Elements of `P(ℤ_p)` preserve `ℤ_p ⊆ ℚ_p` in both directions. -/
theorem norm_map_smul_le_one_iff (h : AffineGroup ℤ_[p]) (y : ℚ_[p]) :
    ‖map PadicInt.Coe.ringHom h • y‖ ≤ 1 ↔ ‖y‖ ≤ 1 := by
  have key (h : AffineGroup ℤ_[p]) (y : ℚ_[p]) (hy : ‖y‖ ≤ 1) :
      ‖map PadicInt.Coe.ringHom h • y‖ ≤ 1 := by
    obtain ⟨y, rfl⟩ : ∃ z : ℤ_[p], (z : ℚ_[p]) = y := ⟨Padic.lift y hy, PadicInt.coe_lift hy⟩
    rw [← PadicInt.Coe.ringHom_apply, map_smul]
    exact PadicInt.norm_le_one _
  refine ⟨fun hy ↦ ?_, key h y⟩
  simpa [← mul_smul] using key h⁻¹ _ hy

/-- Conjugation by `φ` multiplies translation parts by `p`:
`φ (b, a) φ⁻¹ = (p b, a)`. -/
theorem padicPhi_mul_map_mul_inv (b : ℤ_[p]) (a : ℤ_[p]ˣ) :
    padicPhi p * map PadicInt.Coe.ringHom ⟨.ofAdd b, a⟩ * (padicPhi p)⁻¹ =
      map PadicInt.Coe.ringHom ⟨.ofAdd ((p : ℤ_[p]) * b), a⟩ := by
  ext <;> simp

/-- A power `φ^m φ^{-l}` comes from `P(ℤ_p)` only when `m = l`. -/
theorem eq_of_map_eq_padicPhi_pow_mul_inv_pow {m l : ℕ} {h : AffineGroup ℤ_[p]}
    (hh : map PadicInt.Coe.ringHom h = padicPhi p ^ m * (padicPhi p ^ l)⁻¹) : m = l := by
  have hnorm := ((exists_map_padicInt_eq_iff (p := p) _).mp ⟨h, hh⟩).2
  rw [← mul_one (padicPhi p ^ m), norm_coe_padicPhi_pow_mul_mul_inv_pow_right] at hnorm
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.out.one_lt
  have := (zpow_eq_one_iff_right₀ (by positivity) hp1.ne').mp (by simpa using hnorm)
  omega

/-- For every `g ∈ P(ℚ_p)` and `n`, some `φ^m g φ^{-l}` with `n ≤ m` comes from `P(ℤ_p)`. -/
theorem exists_map_eq_padicPhi_pow_mul_mul_inv_pow (g : AffineGroup ℚ_[p]) (n : ℕ) :
    ∃ m l : ℕ, ∃ h : AffineGroup ℤ_[p], n ≤ m ∧
      map PadicInt.Coe.ringHom h = padicPhi p ^ m * g * (padicPhi p ^ l)⁻¹ := by
  set e := Padic.valuation (g.right : ℚ_[p])
  set f := Padic.valuation g.left.toAdd
  set m := n + (-e).toNat + (-f).toNat
  set l := (m + e).toNat
  have hl : (l : ℤ) = m + e := Int.toNat_of_nonneg (by omega)
  have hp0 : (p : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hp.out.ne_zero
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp.out.one_lt.le
  have hleft : ‖(padicPhi p ^ m * g * (padicPhi p ^ l)⁻¹).left.toAdd‖ ≤ 1 := by
    rw [toAdd_padicPhi_pow_mul_mul_inv_pow_left, norm_mul, Padic.norm_p_pow]
    by_cases hb : g.left.toAdd = 0
    · simp [hb]
    rw [Padic.norm_eq_zpow_neg_valuation hb, ← zpow_add₀ hp0]
    exact zpow_le_one_of_nonpos₀ hp1 (by omega)
  have hright : ‖((padicPhi p ^ m * g * (padicPhi p ^ l)⁻¹).right : ℚ_[p])‖ = 1 := by
    rw [norm_coe_padicPhi_pow_mul_mul_inv_pow_right,
      Padic.norm_eq_zpow_neg_valuation g.right.ne_zero, ← zpow_add₀ hp0, hl]
    convert zpow_zero (p : ℝ) using 2
    ring
  obtain ⟨h, hh⟩ := (exists_map_padicInt_eq_iff _).mpr ⟨hleft, hright⟩
  exact ⟨m, l, h, by omega, hh⟩

end TauCeti.AffineGroup
