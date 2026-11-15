/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.RootsOfUnity.TateModule

import TauCeti.Topology.Algebra.Group.Profinite.ZHat.Units

/-!
# Basis change for `ℤ̂`-coordinates of the roots-of-unity Tate module

Over an integral domain `R`, a compatible system `ζ = (ζ_n)_n` of primitive roots of unity in
`PrimeToPTateModule 1 R = lim_n μ_n(R)` determines a parametrization
`e_ζ = (continuousMulEquivZHat ζ hζ).symm : zHat →ₜ* PrimeToPTateModule 1 R`, `a ↦ ζ ^ᶻ a`, and its
inverse coordinate isomorphism
`c_ζ = continuousMulEquivZHat ζ hζ : PrimeToPTateModule 1 R ≃ₜ* zHat`.

Any two compatible primitive systems differ by powering by a unique unit `u ∈ (Additive zHat)ˣ` of
the profinite integers (`TauCeti.PrimeToPTateModule.zpowHat_zHatUnit`). Replacing `ζ` by `ζ ^ᶻ u`
transforms the parametrization and its coordinate map in opposite ways:

* **Forward parametrization:** `e_{ζ^u}(a) = e_ζ(u * a)`
  (`TauCeti.PrimeToPTateModule.continuousMulEquivZHat_zpowHat_symm_apply`).
* **Coordinate map:** `c_{ζ^u}(x) = u⁻¹ * c_ζ(x)` for every fixed `x ∈ PrimeToPTateModule 1 R`
  (`TauCeti.PrimeToPTateModule.ofMul_continuousMulEquivZHat_zpowHat_apply`).

In particular, the fixed element `ζ` itself has coordinate `1` relative to `ζ` and coordinate `u⁻¹`
relative to `ζ ^ᶻ u`, whose mod-`n` reduction is `(u mod n)⁻¹ ∈ (ZMod n)ˣ`
(`TauCeti.PrimeToPTateModule.toZMod_ofMul_continuousMulEquivZHat_zpowHat_self`). When
`u ≡ 2 (mod 5)` (witnessed concretely by `1 + ω_5`, where `ω_5 = zHat.idem 5` is the `5`-adic
idempotent), the new coordinate of `ζ` reduces modulo `5` to `3` — since `(ζ_5 ^ 2) ^ 3 = ζ_5` —
and not to `2` (`TauCeti.PrimeToPTateModule.toZMod_five_continuousMulEquivZHat_zpowHat_self`,
`TauCeti.PrimeToPTateModule.exists_unit_toZMod_five_continuousMulEquivZHat_zpowHat_self`). Note that
complex conjugation `u = -1` alone cannot distinguish `u` from `u⁻¹`, because `(-1)⁻¹ = -1`.

## Main results

* `TauCeti.PrimeToPTateModule.continuousMulEquivZHat_zpowHat_symm_apply`: `e_{ζ^u}(a) = e_ζ(u * a)`.
* `TauCeti.PrimeToPTateModule.ofMul_continuousMulEquivZHat_zpowHat_apply`:
  `c_{ζ^u}(x) = u⁻¹ * c_ζ(x)`.
* `TauCeti.PrimeToPTateModule.toZMod_ofMul_continuousMulEquivZHat_zpowHat_self`: for every `n : ℕ+`,
  the coordinate of `ζ` relative to `ζ ^ᶻ u` reduces modulo `n` to `(u mod n)⁻¹`.
* `TauCeti.PrimeToPTateModule.toZMod_five_continuousMulEquivZHat_zpowHat_self`,
  `TauCeti.PrimeToPTateModule.exists_unit_toZMod_five_continuousMulEquivZHat_zpowHat_self`: for
  `u ≡ 2 (mod 5)` in `(Additive zHat)ˣ`, `ζ` has coordinate `1` in the original basis and residue
  `3` (not `2`) modulo `5` in the rescaled basis `ζ ^ᶻ u`, and such a unit `u` exists.
-/

public section

namespace TauCeti.PrimeToPTateModule

open Additive
open scoped TauCeti.zHat

universe u

/-- The profinite integer `1 + ω_5` (with `5`-adic component `2` and `ℓ`-adic component `1` for
`ℓ ≠ 5`) is a unit of `ℤ̂` congruent to `2` modulo `5`. -/
private theorem exists_unit_toZMod_five_eq_two :
    ∃ u : (Additive zHat.{u})ˣ, zHat.toZMod 5 (u : Additive zHat.{u}) = 2 := by
  have h20 : (1 + 1 : ZMod (5 ^ 1)) ≠ 0 := by decide
  have : Fact (Nat.Prime 5) := ⟨by decide⟩
  have hunit : IsUnit (1 + zHat.idem.{u} 5) := by
    rw [zHat.isUnit_iff_component]
    intro ℓ hℓ
    by_cases h5 : ℓ = 5
    · subst h5
      rw [map_add, map_one, zHat.component_idem_self]
      by_contra hnu
      have hdvd : (5 : ℤ_[5]) ∣ (1 + 1 : ℤ_[5]) :=
        (PadicInt.norm_lt_one_iff_dvd _).mp (PadicInt.not_isUnit_iff.mp hnu)
      have hz : PadicInt.toZModPow 1 (1 + 1 : ℤ_[5]) = 0 :=
        (PadicInt.toZModPow_eq_zero_iff_dvd 1 _).mpr (by simpa using hdvd)
      rw [map_add, map_one] at hz
      exact h20 hz
    · rw [map_add, map_one, zHat.component_idem_of_ne 5 h5, add_zero]
      exact isUnit_one
  refine ⟨hunit.unit, ?_⟩
  rw [IsUnit.unit_spec, map_add, map_one,
    zHat.toZMod_idem_of_dvd_pow (ℓ := 5) (n := 5) (k := 1) (by decide)]
  decide

section BasisChange

variable {R : Type*} [CommRing R] [IsDomain R] {ζ : PrimeToPTateModule 1 R}
  (hζ : ∀ m : {m : ℕ // m ≠ 0 ∧ m.Coprime 1}, IsPrimitiveRoot (proj m ζ : Rˣ) m)
include hζ

/-- **Basis change for the parametrization `e_ζ : ℤ̂ → lim_n μ_n(R)`.** Replacing the compatible
primitive system `ζ` by `ζ ^ᶻ u` (`u ∈ ℤ̂ˣ`) precomposes `e_ζ = (continuousMulEquivZHat ζ hζ).symm`
with multiplication by `u`: `e_{ζ^u}(a) = e_ζ(u * a)`. -/
theorem continuousMulEquivZHat_zpowHat_symm_apply (u : (Additive zHat.{u})ˣ)
    (a : Additive zHat.{u}) :
    (continuousMulEquivZHat.{u} (ζ ^ᶻ (u : Additive zHat.{u}))
        (isPrimitiveRoot_proj_zpowHat hζ u)).symm (toMul a) =
      (continuousMulEquivZHat.{u} ζ hζ).symm (toMul ((u : Additive zHat.{u}) * a)) := by
  rw [continuousMulEquivZHat_symm_apply, continuousMulEquivZHat_symm_apply, ← zpowHat_def,
    ← zpowHat_def, zpowHat_mul]

/-- **Basis change for the coordinate map `c_ζ : lim_n μ_n(R) → ℤ̂`.** Replacing `ζ` by `ζ ^ᶻ u`
(`u ∈ ℤ̂ˣ`) multiplies the `ℤ̂`-coordinate of any fixed Tate-module element `x` by `u⁻¹`:
`c_{ζ^u}(x) = u⁻¹ * c_ζ(x)`. -/
theorem ofMul_continuousMulEquivZHat_zpowHat_apply (u : (Additive zHat.{u})ˣ)
    (x : PrimeToPTateModule 1 R) :
    ofMul (continuousMulEquivZHat.{u} (ζ ^ᶻ (u : Additive zHat.{u}))
        (isPrimitiveRoot_proj_zpowHat hζ u) x) =
      ((u⁻¹ : (Additive zHat.{u})ˣ) : Additive zHat.{u}) *
        ofMul (continuousMulEquivZHat.{u} ζ hζ x) := by
  rw [continuousMulEquivZHat_apply_eq_zpowHat hζ (isPrimitiveRoot_proj_zpowHat hζ u) x,
    zHatUnit_zpowHat]
  have h := congrArg ofMul
    (toMul_zpowHat (ofMul (continuousMulEquivZHat.{u} ζ hζ x))
      ((u⁻¹ : (Additive zHat.{u})ˣ) : Additive zHat.{u}))
  simpa [mul_comm] using h

/-- **Mod-`n` coordinate of `ζ` in a rescaled basis `ζ ^ᶻ u`.** For every `n : ℕ+` and every unit
`u ∈ (Additive zHat)ˣ`, the coordinate of the fixed generator `ζ` relative to `ζ ^ᶻ u` is `u⁻¹`,
which reduces modulo `n` to `(u mod n)⁻¹ ∈ (ZMod n)ˣ`. -/
theorem toZMod_ofMul_continuousMulEquivZHat_zpowHat_self (n : ℕ+) (u : (Additive zHat.{u})ˣ) :
    zHat.toZMod n (ofMul (continuousMulEquivZHat.{u} (ζ ^ᶻ (u : Additive zHat.{u}))
        (isPrimitiveRoot_proj_zpowHat hζ u) ζ)) =
      (((Units.map (zHat.toZMod.{u} n).toMonoidHom u)⁻¹ : (ZMod n)ˣ) : ZMod n) := by
  rw [ofMul_continuousMulEquivZHat_zpowHat_apply hζ u ζ, continuousMulEquivZHat_self,
    zHat.ofMul_gen, mul_one]
  rfl

/-- **Mod-`5` coordinate check.** Relative to `ζ`, the fixed element `ζ` itself has coordinate `1`
in `ℤ̂`, whereas for any profinite unit `u` with `u ≡ 2 (mod 5)`, the coordinate of `ζ` relative to
the rescaled basis `ζ ^ᶻ u` reduces modulo `5` to `3` (since `(ζ₅²)³ = ζ₅`) and in particular not
to `2`. -/
theorem toZMod_five_continuousMulEquivZHat_zpowHat_self {u : (Additive zHat.{u})ˣ}
    (hu : zHat.toZMod 5 (u : Additive zHat.{u}) = 2) :
    ofMul (continuousMulEquivZHat.{u} ζ hζ ζ) = 1 ∧
      zHat.toZMod 5
        (ofMul (continuousMulEquivZHat.{u} (ζ ^ᶻ (u : Additive zHat.{u}))
          (isPrimitiveRoot_proj_zpowHat hζ u) ζ)) = 3 ∧
      zHat.toZMod 5
        (ofMul (continuousMulEquivZHat.{u} (ζ ^ᶻ (u : Additive zHat.{u}))
          (isPrimitiveRoot_proj_zpowHat hζ u) ζ)) ≠ 2 := by
  have horig : ofMul (continuousMulEquivZHat.{u} ζ hζ ζ) = 1 := by
    rw [continuousMulEquivZHat_self, zHat.ofMul_gen]
  have hmul : zHat.toZMod 5 (u : Additive zHat.{u}) *
      zHat.toZMod 5 ((u⁻¹ : (Additive zHat.{u})ˣ) : Additive zHat.{u}) = 1 := by
    rw [← map_mul, Units.mul_inv, map_one]
  rw [hu] at hmul
  have h32 : (3 : ZMod (5 : ℕ+)) * 2 = 1 := by decide
  have hinv : zHat.toZMod 5 ((u⁻¹ : (Additive zHat.{u})ˣ) : Additive zHat.{u}) = 3 := by
    have h := congrArg ((3 : ZMod (5 : ℕ+)) * ·) hmul
    rwa [← mul_assoc, h32, one_mul, mul_one] at h
  have hnew : zHat.toZMod 5
      (ofMul (continuousMulEquivZHat.{u} (ζ ^ᶻ (u : Additive zHat.{u}))
        (isPrimitiveRoot_proj_zpowHat hζ u) ζ)) = 3 := by
    rw [toZMod_ofMul_continuousMulEquivZHat_zpowHat_self hζ 5 u]
    exact hinv
  exact ⟨horig, hnew, hnew.symm ▸ by decide⟩

/-- **Non-vacuity of the mod-`5` basis-change check:** there exists a profinite unit `u ∈ ℤ̂ˣ` with
`u ≡ 2 (mod 5)`, and for this `u` the fixed element `ζ` has coordinate `1` in the original basis and
residue `3` (not `2`) modulo `5` in the rescaled basis `ζ ^ᶻ u`. -/
theorem exists_unit_toZMod_five_continuousMulEquivZHat_zpowHat_self :
    ∃ u : (Additive zHat.{u})ˣ, zHat.toZMod 5 (u : Additive zHat.{u}) = 2 ∧
      ofMul (continuousMulEquivZHat.{u} ζ hζ ζ) = 1 ∧
      zHat.toZMod 5
        (ofMul (continuousMulEquivZHat.{u} (ζ ^ᶻ (u : Additive zHat.{u}))
          (isPrimitiveRoot_proj_zpowHat hζ u) ζ)) = 3 ∧
      zHat.toZMod 5
        (ofMul (continuousMulEquivZHat.{u} (ζ ^ᶻ (u : Additive zHat.{u}))
          (isPrimitiveRoot_proj_zpowHat hζ u) ζ)) ≠ 2 := by
  obtain ⟨u, hu⟩ := exists_unit_toZMod_five_eq_two.{u}
  exact ⟨u, hu, toZMod_five_continuousMulEquivZHat_zpowHat_self hζ hu⟩

end BasisChange

end TauCeti.PrimeToPTateModule
