/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Data.ZMod.QuotientRing

/-!
# Integer modules

Bundling additive homomorphisms as integer-linear categorical morphisms preserves and
reflects vanishing of their composite. This transports zero-composite laws between
additive groups and `ModuleCat ℤ`.

An endomorphism `φ` of `ℤ` in `ModuleCat ℤ` is multiplication by `φ 1`, so its cokernel is
`ℤ / φ 1`, and `Nat.card` of the cokernel is `|φ 1|` (`ModuleCat.natCard_cokernel_int`): for
`φ ≠ 0` the cokernel has `|φ 1|` elements, and for `φ = 0` it is the infinite group `ℤ`. This
recovers `φ` up to sign from its cokernel.
-/

public section

open CategoryTheory

namespace AddMonoidHom

universe u

variable {M N P : Type u} [AddCommGroup M] [AddCommGroup N] [AddCommGroup P]

/-- The categorical composite of the integer-linear maps associated to additive homomorphisms
vanishes exactly when their additive composite vanishes. -/
theorem ofHom_toIntLinearMap_comp_eq_zero_iff (a : M →+ N) (b : N →+ P) :
    ModuleCat.ofHom a.toIntLinearMap ≫ ModuleCat.ofHom b.toIntLinearMap = 0 ↔
      b.comp a = 0 := by
  rw [← ModuleCat.ofHom_comp, ← ModuleCat.hom_injective.eq_iff]
  simp only [ModuleCat.hom_ofHom, ModuleCat.hom_zero, LinearMap.ext_iff,
    LinearMap.comp_apply, AddMonoidHom.coe_toIntLinearMap, LinearMap.zero_apply,
    AddMonoidHom.ext_iff, AddMonoidHom.comp_apply, AddMonoidHom.zero_apply]

end AddMonoidHom

namespace ModuleCat

open Limits

/-- **The cokernel of an endomorphism of `ℤ`.** `Nat.card` of the cokernel of `φ : ℤ ⟶ ℤ` in
`ModuleCat ℤ` is `|φ 1|`: for `φ ≠ 0` the cokernel has `|φ 1|` elements, and for `φ = 0` it is
`ℤ`, which is infinite, so `Nat.card` is `0`. -/
theorem natCard_cokernel_int (φ : of ℤ ℤ ⟶ of ℤ ℤ) :
    Nat.card (cokernel (C := ModuleCat.{0} ℤ) φ) = (φ.hom 1).natAbs := by
  have hφ : φ.hom = LinearMap.toSpanSingleton ℤ ℤ (φ.hom 1) := LinearMap.ext_ring (by simp)
  rw [Nat.card_congr (cokernelIsoRangeQuotient φ).toLinearEquiv.toEquiv, hφ,
    LinearMap.range_toSpanSingleton,
    Nat.card_congr (Int.quotientSpanEquivZMod (φ.hom 1)).toEquiv, Nat.card_zmod]
  simp

end ModuleCat
