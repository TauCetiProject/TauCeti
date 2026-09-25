/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.NumberField.Cyclotomic.Galois
import TauCeti.RingTheory.RootsOfUnity.PrimitiveRoots

/-!
# Cyclotomic characters in a rational cyclotomic field

Let `K` be the `n`-th cyclotomic field over `ℚ` and let `m ∣ n`. Mathlib identifies `Gal(K/ℚ)`
with `(ZMod n)ˣ` through `IsCyclotomicExtension.Rat.galEquivZMod`, which records the exponent by
which an automorphism acts on every `n`-th root of unity. A primitive `m`-th root of unity `ζ` in
`K` carries its own cyclotomic character `IsPrimitiveRoot.autToPow`, with values in `(ZMod m)ˣ`;
this file shows that it is the reduction of `galEquivZMod` modulo `m`.

## Main results

* `IsPrimitiveRoot.autToPow_eq_unitsMap_galEquivZMod`: the cyclotomic character of a primitive
  `m`-th root of unity in the `n`-th cyclotomic field is `galEquivZMod` reduced modulo `m`.
* `TauCeti.IsCyclotomicExtension.Rat.galEquivZMod_eq_zeta_spec_autToPow`: the special case for
  Mathlib's chosen primitive root.
-/

public section

open IsCyclotomicExtension.Rat

variable {n : ℕ} [NeZero n] {K : Type*} [Field K] [NumberField K]
  [IsCyclotomicExtension {n} ℚ K]

/-- The cyclotomic character of a primitive `m`-th root of unity in the `n`-th cyclotomic field,
for `m ∣ n`, is the reduction modulo `m` of `galEquivZMod`. -/
theorem IsPrimitiveRoot.autToPow_eq_unitsMap_galEquivZMod {m : ℕ} [NeZero m] {ζ : K}
    (hζ : IsPrimitiveRoot ζ m) (hmn : m ∣ n) (σ : Gal(K/ℚ)) :
    hζ.autToPow ℚ σ = ZMod.unitsMap hmn (galEquivZMod n K σ) := by
  -- Both exponents send `ζ` to `σ ζ`, so they agree modulo the order `m` of `ζ`.
  have hexp : ζ ^ (hζ.autToPow ℚ σ : ZMod m).val = ζ ^ (galEquivZMod n K σ).val.val := by
    rw [hζ.autToPow_spec (R := ℚ), galEquivZMod_apply_of_pow_eq n K σ
      ((hζ.pow_eq_one_iff_dvd n).mpr hmn)]
  rw [(hζ.isOfFinOrder (NeZero.ne m)).pow_eq_pow_iff_modEq, ← hζ.eq_orderOf,
    ← ZMod.natCast_eq_natCast_iff, ZMod.natCast_zmod_val] at hexp
  exact Units.ext (hexp.trans (ZMod.natCast_val _))

namespace TauCeti

namespace IsCyclotomicExtension.Rat

/-- Mathlib's rational cyclotomic Galois equivalence agrees with the power character of
`zeta_spec`: both record the exponent by which an automorphism acts on the chosen primitive root.
-/
theorem galEquivZMod_eq_zeta_spec_autToPow (n : ℕ) [NeZero n]
    (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {n} ℚ K]
    (σ : Gal(K/ℚ)) :
    IsCyclotomicExtension.Rat.galEquivZMod n K σ =
      (IsCyclotomicExtension.zeta_spec n ℚ K).autToPow ℚ σ := by
  have hζ := IsCyclotomicExtension.zeta_spec n ℚ K
  have h :=
    (IsCyclotomicExtension.Rat.galEquivZMod_apply_of_pow_eq n K σ hζ.pow_eq_one).symm.trans
      (hζ.autToPow_spec ℚ σ).symm
  exact Units.ext <| ZMod.val_injective n <| hζ.pow_inj (ZMod.val_lt _) (ZMod.val_lt _) h

end IsCyclotomicExtension.Rat

end TauCeti
