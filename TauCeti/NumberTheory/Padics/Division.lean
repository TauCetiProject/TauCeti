/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.Padics.RingHoms
public import TauCeti.Topology.ContinuousMap.Clopen
import Mathlib.Topology.ContinuousMap.Compact
import TauCeti.NumberTheory.Padics.PadicIntegers

/-!
# Exact division on p-adic multiples

The multiples of `p` form a clopen subset of `ℤ_p`. Multiplication by `p` is a homeomorphism from
`ℤ_p` onto this subset, so its inverse extends continuously by zero to all of `ℤ_p`. The resulting
function `PadicInt.divideByP` divides exactly on `pℤ_p` and vanishes on the units.

This continuous partial division is used to construct the left inverse of Frobenius on bounded
p-adic measures.

## Main definitions

* `PadicInt.multiplesClopen`: the clopen subset `pℤ_p`.
* `PadicInt.mulPHomeomorph`: multiplication by `p`, as a homeomorphism onto `pℤ_p`.
* `PadicInt.divideByP`: division by `p` on `pℤ_p`, extended by zero.

## References

* J. Rodrigues Jacinto and C. Williams, *An introduction to p-adic L-functions*, §3.5.5.
-/

public noncomputable section

open ContinuousMap TopologicalSpace

namespace PadicInt

variable (p : ℕ) [Fact p.Prime]

/-- The clopen subset `pℤ_p` of p-adic integers divisible by `p`. -/
def multiplesClopen : Clopens ℤ_[p] where
  carrier := (toZMod : ℤ_[p] →+* ZMod p) ⁻¹' {0}
  isClopen' := IsClopen.preimage (isClopen_discrete {0}) continuous_toZMod

/-- A p-adic integer belongs to `pℤ_p` exactly when it is divisible by `p`. -/
@[simp]
theorem mem_multiplesClopen_iff {x : ℤ_[p]} : x ∈ multiplesClopen p ↔ (p : ℤ_[p]) ∣ x := by
  exact toZMod_eq_zero_iff_dvd x

/-- Multiplication by `p` is a homeomorphism from `ℤ_p` onto the clopen subset `pℤ_p`. -/
def mulPHomeomorph : ℤ_[p] ≃ₜ multiplesClopen p := by
  let f : ℤ_[p] → multiplesClopen p := fun x ↦
    ⟨p * x, (mem_multiplesClopen_iff (p := p)).mpr ⟨x, rfl⟩⟩
  have hf : Continuous f := continuous_induced_rng.mpr (continuous_const.mul continuous_id)
  have hinj : Function.Injective f := fun x y h ↦ by
    apply mul_left_cancel₀ (NeZero.ne (p : ℤ_[p]))
    exact congrArg Subtype.val h
  have hsurj : Function.Surjective f := fun y ↦ by
    obtain ⟨x, hx⟩ := (mem_multiplesClopen_iff (p := p)).mp y.2
    exact ⟨x, Subtype.ext hx.symm⟩
  let e := Equiv.ofBijective f ⟨hinj, hsurj⟩
  exact
    { toEquiv := e
      continuous_toFun := hf
      continuous_invFun := hf.continuous_symm_of_equiv_compact_to_t2 (f := e) }

/-- Multiplication by `p`, viewed in `pℤ_p`, is the forward map of `mulPHomeomorph`. -/
@[simp]
theorem mulPHomeomorph_apply (x : ℤ_[p]) :
    mulPHomeomorph p x =
      ⟨p * x, (mem_multiplesClopen_iff (p := p)).mpr ⟨x, rfl⟩⟩ :=
  (rfl)

/-- The inverse homeomorphism divides a multiple of `p` by `p`. -/
@[simp]
theorem mulPHomeomorph_symm_apply_mul (x : ℤ_[p]) :
    (mulPHomeomorph p).symm
        ⟨p * x, (mem_multiplesClopen_iff (p := p)).mpr ⟨x, rfl⟩⟩ = x :=
  (mulPHomeomorph p).symm_apply_apply x

/-- Division by `p` as a continuous map from `pℤ_p` to `ℤ_p`. -/
private def divideOnMultiples : C(multiplesClopen p, ℤ_[p]) :=
  ⟨(mulPHomeomorph p).symm, (mulPHomeomorph p).symm.continuous⟩

/-- Division by `p` on `pℤ_p`, extended continuously by zero to the p-adic units. -/
def divideByP : C(ℤ_[p], ℤ_[p]) :=
  zeroExtendClopen ℤ_[p] (multiplesClopen p) (divideOnMultiples p)

/-- Exact division by `p`: dividing `p * x` recovers `x`. -/
@[simp]
theorem divideByP_mul (x : ℤ_[p]) : divideByP p (p * x) = x := by
  rw [divideByP, zeroExtendClopen_apply_mem (multiplesClopen p)
    (divideOnMultiples p) ((mem_multiplesClopen_iff (p := p)).mpr ⟨x, rfl⟩)]
  exact mulPHomeomorph_symm_apply_mul p x

/-- Multiplying the exact quotient by `p` recovers every multiple of `p`. -/
theorem mul_divideByP {x : ℤ_[p]} (hx : (p : ℤ_[p]) ∣ x) : p * divideByP p x = x := by
  obtain ⟨y, rfl⟩ := hx
  rw [divideByP_mul]

/-- Exact division by `p` vanishes away from `pℤ_p`. -/
@[simp]
theorem divideByP_of_not_dvd {x : ℤ_[p]} (hx : ¬(p : ℤ_[p]) ∣ x) : divideByP p x = 0 :=
  zeroExtendClopen_apply_not_mem (multiplesClopen p) (divideOnMultiples p)
    (by simpa using hx)

end PadicInt
