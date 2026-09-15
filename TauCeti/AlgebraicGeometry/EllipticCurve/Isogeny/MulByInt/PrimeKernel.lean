/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.MulByInt.Kernel.Basic
public import Mathlib.Algebra.Module.ZMod

/-!
# The kernel of multiplication by a prime is a `ZMod ℓ`-module

For a prime `ℓ`, multiplication by `ℓ` needs no separate non-vanishing hypothesis: primality
supplies it. Every point of its kernel is killed by `ℓ`, which is exactly what makes the kernel a
module over `ZMod ℓ`.

Nothing here assumes anything about the base field beyond its being a field — no algebraic
closure, and no condition on the characteristic. Those enter only when the kernel's cardinality is
computed, which is why they are not imposed at this layer.

## Main definitions

* `TauCeti.Isogeny.mulByPrimeIsogeny`: multiplication by a prime `ℓ`, with the division
  polynomial's non-vanishing supplied by primality rather than assumed.
* `TauCeti.Isogeny.kerZModModule`: the `ZMod ℓ`-module structure on `ker [ℓ]`. It is a global
  instance, so typeclass synthesis supplies it and a consumer writing
  `Module.finrank (ZMod ℓ) (mulByPrimeIsogeny W ℓ).ker` never names it.

## Main results

* `TauCeti.Isogeny.nsmul_eq_zero_of_mem_ker_mulByPrimeIsogeny`: the kernel is killed by `ℓ`.

## References

* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], III.6.4.
-/

public section

namespace TauCeti.Isogeny

open WeierstrassCurve.Affine

variable {F : Type*} [Field F] [DecidableEq F] (W : WeierstrassCurve.Affine F) [W.IsElliptic]
  {l : ℕ} [hl : Fact l.Prime]

variable (l) in
/-- **Multiplication by a prime `ℓ`**: primality supplies the non-vanishing hypothesis the
division-polynomial construction asks for, so no such hypothesis is exposed here. -/
noncomputable abbrev mulByPrimeIsogeny : Isogeny W W :=
  mulByIntIsogenyOfNeZero W (Int.natCast_ne_zero.mpr hl.out.ne_zero)

/-- Every point of `ker [ℓ]` is killed by `ℓ`. -/
@[simp]
theorem nsmul_eq_zero_of_mem_ker_mulByPrimeIsogeny (x : (mulByPrimeIsogeny W l).ker) :
    l • x = 0 := by
  have hx : ((l : ℤ)) • (x : (W⁄F).toAffine.Point) = 0 :=
    (mem_ker_mulByIntIsogeny_iff W _).1 x.2
  have : ((l : ℤ)) • x = 0 := Subtype.ext (by simpa using hx)
  simpa using this

variable (l) in
/-- **The `ZMod ℓ`-module structure on `ker [ℓ]`**, from every point being killed by `ℓ`. -/
noncomputable instance kerZModModule : Module (ZMod l) (mulByPrimeIsogeny W l).ker :=
  AddCommGroup.zmodModule (nsmul_eq_zero_of_mem_ker_mulByPrimeIsogeny W)

end TauCeti.Isogeny

end
