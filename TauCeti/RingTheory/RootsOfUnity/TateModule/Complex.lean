/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.RootsOfUnity.Complex.Exp
public import TauCeti.RingTheory.RootsOfUnity.TateModule

/-!
# The standard compatible system of complex roots of unity

Over `ℂ` there is a canonical compatible system of primitive roots of unity, namely
`ζ_m = exp(2πi / m)`: for `n ∣ m` one has `exp(2πi / m) ^ (m / n) = exp(2πi / n)`. This file
packages it as a point `TauCeti.PrimeToPTateModule.complexExp p` of the prime-to-`p` Tate module
`lim_m μ_m(ℂ)`, whose components are all primitive (Mathlib's `Complex.isPrimitiveRoot_exp`).
Over a domain with a primitive `m`-th root of unity for every nonzero `m` prime to `p`, such a
point exists but is only chosen (`TauCeti.PrimeToPTateModule.exists_forall_isPrimitiveRoot`);
this one is explicit. The compatibility of the components is `TauCeti.exp_two_pi_I_div_pow_div`.

## Main definitions

* `TauCeti.PrimeToPTateModule.complexExp p`: the point `(exp(2πi / m))_m` of
  `PrimeToPTateModule p ℂ`.

## Main results

* `TauCeti.PrimeToPTateModule.coe_proj_complexExp`: the level-`m` component of `complexExp p` is
  `exp(2πi / m)`.
* `TauCeti.PrimeToPTateModule.isPrimitiveRoot_proj_complexExp`: each component of `complexExp p`
  is a primitive root of unity of its level.
-/

public section

noncomputable section

open Complex Real

namespace TauCeti.PrimeToPTateModule

variable (p : ℕ)

/-- The **standard compatible system of complex roots of unity**: the point of the prime-to-`p`
Tate module `lim_m μ_m(ℂ)` whose level-`m` component is the primitive root `exp(2πi / m)`. -/
def complexExp : PrimeToPTateModule p ℂ :=
  mk (fun m ↦ haveI : NeZero (m : ℕ) := ⟨m.2.1⟩
      rootsOfUnity.mkOfPowEq (exp (2 * π * I / m)) (isPrimitiveRoot_exp m m.2.1).pow_eq_one)
    (mem_primeToPTateModuleSubgroup_iff.2 fun m n h ↦ Units.ext <| by
      simpa using exp_two_pi_I_div_pow_div m.2.1 h)

/-- The level-`m` component of `complexExp p` is `exp(2πi / m)`. -/
@[simp]
theorem coe_proj_complexExp (m : {m : ℕ // m ≠ 0 ∧ m.Coprime p}) :
    ((proj m (complexExp p) : ℂˣ) : ℂ) = exp (2 * π * I / m) := by
  simp [complexExp]

/-- Each component of `complexExp p` is a primitive root of unity of its level: `exp(2πi / m)` is
a primitive `m`-th root of unity. -/
theorem isPrimitiveRoot_proj_complexExp (m : {m : ℕ // m ≠ 0 ∧ m.Coprime p}) :
    IsPrimitiveRoot (proj m (complexExp p) : ℂˣ) m := by
  rw [← IsPrimitiveRoot.coe_units_iff, coe_proj_complexExp]
  exact isPrimitiveRoot_exp m m.2.1

end TauCeti.PrimeToPTateModule
