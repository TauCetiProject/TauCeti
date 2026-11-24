/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.RootsOfUnity.TateModule

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
(`TauCeti.PrimeToPTateModule.toZMod_ofMul_continuousMulEquivZHat_zpowHat_self`).

## Main results

* `TauCeti.PrimeToPTateModule.continuousMulEquivZHat_zpowHat_symm_apply`: `e_{ζ^u}(a) = e_ζ(u * a)`.
* `TauCeti.PrimeToPTateModule.ofMul_continuousMulEquivZHat_zpowHat_apply`:
  `c_{ζ^u}(x) = u⁻¹ * c_ζ(x)`.
* `TauCeti.PrimeToPTateModule.toZMod_ofMul_continuousMulEquivZHat_zpowHat_self`: for every `n : ℕ+`,
  the coordinate of `ζ` relative to `ζ ^ᶻ u` reduces modulo `n` to `(u mod n)⁻¹`.
-/

public section

namespace TauCeti.PrimeToPTateModule

open Additive
open scoped TauCeti.zHat

universe u

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
    zHat.ofMul_gen, mul_one, Units.coe_map_inv, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_ofClass]

end BasisChange

end TauCeti.PrimeToPTateModule
