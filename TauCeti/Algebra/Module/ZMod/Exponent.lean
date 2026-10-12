/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.ZMod
public import Mathlib.GroupTheory.Exponent

/-!
# The exponent of a group whose additive copy is a `ℤ/nℤ`-module

Scalars from `ZMod n` act on a `ZMod n`-module, so `n` kills it. Written multiplicatively, a
commutative group whose additive copy carries a `ZMod n`-module structure therefore has exponent
dividing `n`; for a prime `n` it is elementary abelian. This is the converse of
`AddCommGroup.zmodModule`, which builds the module structure out of that divisibility, and it is
what recovers the group-theoretic hypothesis from a module structure that some other construction
supplied. The additive form is the same statement, through `AddMonoid.exponent_additive`.

## Main results

* `TauCeti.exponent_dvd_of_module_zmod`: a commutative group whose additive copy is a
  `ZMod n`-module has exponent dividing `n`.
-/

public section

namespace TauCeti

/-- A commutative group whose additive copy is a `ZMod n`-module has exponent dividing `n`, since
`n` kills every `ZMod n`-module. -/
theorem exponent_dvd_of_module_zmod {n : ℕ} {W : Type*} [CommGroup W]
    [Module (ZMod n) (Additive W)] : Monoid.exponent W ∣ n :=
  Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr fun w ↦ by
    have h := congrArg Additive.toMul (ZModModule.char_nsmul_eq_zero n (Additive.ofMul w))
    rwa [toMul_nsmul, toMul_ofMul, toMul_zero] at h

end TauCeti
