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
* `AlgEquiv.galEquivZMod_restrictNormal`: an automorphism of a larger field acting on the `n`-th
  roots of unity through `u` restricts to `galEquivZMod.symm u`.
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

/-- **Restricting to the `n`-th cyclotomic field.** If an automorphism `τ` of an extension `L` of
`K` raises every `n`-th root of unity of `L` to the power `u`, then `galEquivZMod` sends its
restriction to `K` to `u`. -/
theorem AlgEquiv.galEquivZMod_restrictNormal {L : Type*} [Field L] [Algebra ℚ L] [Algebra K L]
    [IsScalarTower ℚ K L] [Normal ℚ K] (τ : L ≃ₐ[ℚ] L) (u : (ZMod n)ˣ)
    (hτ : ∀ z : L, z ^ n = 1 → τ z = z ^ (u : ZMod n).val) :
    galEquivZMod n K (τ.restrictNormal K) = u := by
  have hζ := IsCyclotomicExtension.zeta_spec n ℚ K
  have h := congrArg (algebraMap K L)
    (galEquivZMod_apply_of_pow_eq n K (τ.restrictNormal K) hζ.pow_eq_one)
  rw [map_pow, AlgEquiv.restrictNormal_commutes,
    hτ _ (by rw [← map_pow, hζ.pow_eq_one, map_one])] at h
  have hζL := hζ.map_of_injective (algebraMap K L).injective
  exact Units.ext (ZMod.val_injective _ (hζL.pow_inj (ZMod.val_lt _) (ZMod.val_lt _) h).symm)
