/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.KrullTopology
public import Mathlib.Topology.Algebra.ContinuousMonoidHom
import TauCeti.FieldTheory.Galois.SquareRoot
import TauCeti.FieldTheory.KrullTopology

/-!
# The sign character of a square root

Let `L/K` be a field extension and `a ∈ L` a square root of an element of `K`. Every
`K`-automorphism `g` of `L` sends `a` to `a` or to `-a`, so `g a = η(g) • a` for a sign
`η(g) ∈ ℤˣ`. The signs can be chosen to form a homomorphism `η : Gal(L/K) → ℤˣ`, continuous for
the Krull topology, because the automorphisms fixing the finite extension `K⟮a⟯` form an open
subgroup on which `η` is trivial. When `a ≠ 0` and `2 ≠ 0` in `L`, the signs are forced, so
`η` is unique.

For `L` an algebraic closure this is the quadratic character of the absolute Galois group
attached to `K(a)`, the character that describes a quadratic twist of an elliptic curve.

## Main results

* `TauCeti.exists_continuousMonoidHom_apply_eq_zsmul_of_sq_eq`: some continuous character
  `η : Gal(L/K) →ₜ* ℤˣ` satisfies `g a = η(g) • a` for every `g`.
* `TauCeti.continuousMonoidHom_eq_of_apply_eq_zsmul`: two such characters agree when `a ≠ 0` and
  `2 ≠ 0` in `L`.
-/

public section

namespace TauCeti

variable {K L : Type*} [Field K] [Field L] [Algebra K L]

/-- **The sign character of a square root.** If `a ∈ L` squares to an element of `K`, then some
continuous character `η` of `Gal(L/K)`, for the Krull topology, with values in `ℤˣ`, satisfies
`g a = η(g) • a` for every `g`. -/
theorem exists_continuousMonoidHom_apply_eq_zsmul_of_sq_eq {a : L} {c : K}
    (ha : a ^ 2 = algebraMap K L c) :
    ∃ η : (L ≃ₐ[K] L) →ₜ* ℤˣ, ∀ g : L ≃ₐ[K] L, g a = (η g : ℤ) • a := by
  classical
  have hpm (g : L ≃ₐ[K] L) : g a = a ∨ g a = -a := g.apply_eq_or_eq_neg_of_sq_eq ha
  let f : (L ≃ₐ[K] L) →* ℤˣ :=
    { toFun g := if g a = a then 1 else -1
      map_one' := by simp
      map_mul' g h := by
        by_cases hneg : -a = a
        · -- then `a` is fixed by every automorphism, and the sign is constantly `1`
          have hfix (k : L ≃ₐ[K] L) : k a = a := (hpm k).elim id fun h ↦ h.trans hneg
          simp [hfix]
        rcases hpm g with hg | hg <;> rcases hpm h with hh | hh <;>
          simp [AlgEquiv.mul_apply, hg, hh, hneg] }
  have hf (g : L ≃ₐ[K] L) : g a = (f g : ℤ) • a := by
    by_cases hg : g a = a
    · simp [f, hg]
    · simp only [f, MonoidHom.coe_mk, OneHom.coe_mk, ite_eq_right hg]
      simp [(hpm g).resolve_left hg]
  -- `f g` depends only on `g a`, and the orbit map of the integral element `a` is locally constant
  have hint : IsIntegral K a := ⟨Polynomial.X ^ 2 - Polynomial.C c,
    Polynomial.monic_X_pow_sub_C c two_ne_zero, by simp [ha]⟩
  exact ⟨⟨f, (hint.isLocallyConstant_apply.comp fun y ↦ if y = a then (1 : ℤˣ) else -1).continuous⟩,
    hf⟩

/-- **The sign character of a square root is unique.** If `a ≠ 0` and `2 ≠ 0` in `L`, two
characters `η, η'` with `g a = η(g) • a = η'(g) • a` for every automorphism `g` are equal. -/
theorem continuousMonoidHom_eq_of_apply_eq_zsmul {a : L} (ha : a ≠ 0) (h2 : (2 : L) ≠ 0)
    {η η' : (L ≃ₐ[K] L) →ₜ* ℤˣ} (h : ∀ g : L ≃ₐ[K] L, g a = (η g : ℤ) • a)
    (h' : ∀ g : L ≃ₐ[K] L, g a = (η' g : ℤ) • a) : η = η' := by
  ext g
  have hne : -a ≠ a := fun hn ↦ ha <|
    (mul_eq_zero.mp (by linear_combination -hn : (2 : L) * a = 0)).resolve_left h2
  have hg := (h g).symm.trans (h' g)
  rcases Int.units_eq_one_or (η g) with h1 | h1 <;>
    rcases Int.units_eq_one_or (η' g) with h1' | h1' <;> simp_all [Ne.symm hne]

end TauCeti
