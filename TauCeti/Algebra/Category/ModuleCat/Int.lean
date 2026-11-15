/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Data.ZMod.QuotientRing
import Mathlib.SetTheory.Cardinal.Finite

/-!
# Additive homomorphisms as morphisms of integer modules

Bundling additive homomorphisms as integer-linear categorical morphisms preserves and
reflects vanishing of their composite. This transports zero-composite laws between
additive groups and `ModuleCat ℤ`.

An endomorphism of `ℤ` in `ModuleCat ℤ` is multiplication by an integer `m`, and its cokernel is
`ℤ/(m)`. So it is determined up to sign by its cokernel: if the cokernel is `ℤ/n`, it is
multiplication by `n` or by `-n` (`ModuleCat.eq_smul_id_or_eq_neg_smul_id_of_cokernel_iso_zmod`).
-/

public section

open CategoryTheory CategoryTheory.Limits

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

/-- An endomorphism of `ℤ` whose cokernel is `ℤ/n` is multiplication by `n` or by `-n`. -/
theorem eq_smul_id_or_eq_neg_smul_id_of_cokernel_iso_zmod {n : ℕ}
    (φ : ModuleCat.of ℤ ℤ ⟶ ModuleCat.of ℤ ℤ) (e : cokernel φ ≅ ModuleCat.of ℤ (ZMod n)) :
    φ = (n : ℤ) • 𝟙 _ ∨ φ = -(n : ℤ) • 𝟙 _ := by
  -- `φ` is multiplication by `m = φ 1`, whose range is the ideal `(m)`.
  set m := φ.hom 1
  have hφ : φ.hom = LinearMap.toSpanSingleton ℤ ℤ m := LinearMap.ext_ring (by simp [m])
  have hrange : φ.hom.range = Ideal.span {m} := by
    rw [hφ, LinearMap.range_toSpanSingleton]
  -- Counting the cokernel `ℤ/(m) ≅ ℤ/|m|` gives `|m| = n`.
  have hcard : m.natAbs = n := by
    rw [← Nat.card_zmod m.natAbs, ← Nat.card_zmod n,
      ← Nat.card_congr (Int.quotientSpanEquivZMod m).toEquiv, ← hrange]
    exact Nat.card_congr ((cokernelIsoRangeQuotient φ).symm ≪≫ e).toLinearEquiv.toEquiv
  have hφ' : ∀ c : ℤ, m = c → φ = c • 𝟙 _ := fun c hc ↦ by
    ext : 1
    exact LinearMap.ext_ring (by simp [← hc, m])
  rcases Int.natAbs_eq m with h | h
  · exact .inl (hφ' n (by rw [h, hcard]))
  · exact .inr (hφ' (-n) (by rw [h, hcard]))

end ModuleCat
