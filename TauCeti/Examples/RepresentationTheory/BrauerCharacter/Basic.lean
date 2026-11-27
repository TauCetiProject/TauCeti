/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Field.ZMod
public import TauCeti.RepresentationTheory.BrauerCharacter.Basic

/-!
# Examples of Brauer characters

Checks of `Representation.brauerCharacter`, for the cyclic group `C₃` realized as the group
`μ₃(k)` of cube roots of unity of a field `k` containing a primitive cube root of unity (for
instance `𝔽₄`), acting on the line `k` by multiplication, with `p` prime to `3` (for instance
`p = 2`), and for `C₂` in characteristic `2`.

* **The value depends on `τ`**: on the line `k` with `ζ ∈ μ₃(k)` acting by `ζ`, the Brauer
  character at `ζ` is `τ ζ`; replacing `τ` by `τ ∘ inv` gives `τ ζ⁻¹`, a different value when
  `ζ ≠ 1`.
* **Duals**: the dual of that line has Brauer character `τ ζ⁻¹` at `ζ`, again different from
  `τ ζ` when `ζ ≠ 1`, so a model of the dual ignoring the inverse is wrong.
* **The eigenvalue reading**: the sum of the line and its dual has Brauer character `-1` at
  `ζ ≠ 1` over every domain `L`, the sum of the two primitive cube roots of unity of `L`. Its
  trace in `k` is `ζ + ζ⁻¹ = -1`, which is `1` in characteristic `2`: casting the trace into `L`
  gives `1 ≠ -1`.
* **`C₂` at `p = 2`**: the regular representation of `C₂` over `𝔽₂` and the trivial
  representation on `𝔽₂ ⊕ 𝔽₂` have the same Brauer character, `2` at `1` and `0` at the
  generator, although only the second is semisimple: Brauer characters see composition factors,
  not modules.
-/

public section

open Module

namespace TauCeti.BrauerCharacterExamples

open _root_.Representation

variable {k L : Type*} [Field k] [CommRing L] (p : ℕ) (τ : rootsOfUnity 3 k ≃* rootsOfUnity 3 L)

/-- The line `k` with `μ₃(k)` acting by multiplication. -/
noncomputable abbrev cubeRootLine (k : Type*) [Field k] : Representation k (rootsOfUnity 3 k) k :=
  ofLinearCharacter (rootsOfUnity 3 k).subtype

/-- Every element of `μ₃` cubes to `1`. -/
theorem pow_three_eq_one {M : Type*} [CommMonoid M] (ζ : rootsOfUnity 3 M) : ζ ^ 3 = 1 :=
  Subtype.ext (by simpa using (mem_rootsOfUnity 3 _).1 ζ.property)

/-- An element of `μ₃(k)` other than `1` has order `3`. -/
theorem orderOf_eq_three {ζ : rootsOfUnity 3 k} (hζ : ζ ≠ 1) : orderOf ζ = 3 :=
  orderOf_eq_prime (pow_three_eq_one ζ) hζ

/-- At `ζ ∈ μ₃(k)` the Brauer character of the line is `τ ζ`. -/
theorem brauerCharacter_cubeRootLine (hp : p.Coprime 3) (ζ : rootsOfUnity 3 k) :
    (cubeRootLine k).brauerCharacter p τ ζ = ((τ ζ : Lˣ) : L) := by
  have hg : p.Coprime (orderOf ζ) :=
    hp.coprime_dvd_right (orderOf_dvd_of_pow_eq_one (pow_three_eq_one ζ))
  rw [brauerCharacter_ofLinearCharacter p τ _ hg, Subgroup.coe_subtype,
    TauCeti.rootsOfUnityLift_coe]

/-- For `ζ ≠ 1` in `μ₃`, `ζ⁻¹ ≠ ζ`. -/
theorem inv_ne_self {G : Type*} [CommGroup G] {ζ : G} (h3 : ζ ^ 3 = 1) (hζ : ζ ≠ 1) :
    ζ⁻¹ ≠ ζ := by
  intro h
  have h2 : ζ ^ 2 = 1 := by rw [sq, ← inv_mul_cancel ζ, h]
  have : ζ = 1 := by
    calc ζ = ζ ^ 3 * (ζ ^ 2)⁻¹ := by group
      _ = 1 := by rw [h3, h2, inv_one, mul_one]
  exact hζ this

/-- **The Brauer character depends on `τ`.** Precomposing `τ` with inversion changes the value of
the Brauer character of the line at every `ζ ≠ 1`. -/
theorem brauerCharacter_cubeRootLine_ne (hp : p.Coprime 3) {ζ : rootsOfUnity 3 k} (hζ : ζ ≠ 1) :
    (cubeRootLine k).brauerCharacter p ((MulEquiv.inv _).trans τ) ζ ≠
      (cubeRootLine k).brauerCharacter p τ ζ := by
  rw [brauerCharacter_cubeRootLine, brauerCharacter_cubeRootLine p τ hp]
  · intro h
    refine inv_ne_self (pow_three_eq_one ζ) hζ
      (τ.injective (rootsOfUnity.coe_injective h))
  · exact hp

/-- **Duals.** The dual of the line has Brauer character `τ ζ⁻¹` at `ζ`. -/
theorem brauerCharacter_dual_cubeRootLine (hp : p.Coprime 3) (ζ : rootsOfUnity 3 k) :
    (cubeRootLine k).dual.brauerCharacter p τ ζ = ((τ ζ⁻¹ : Lˣ) : L) := by
  rw [brauerCharacter_dual, brauerCharacter_cubeRootLine p τ hp]

/-- **Duals are not the identity.** At `ζ ≠ 1`, the Brauer characters of the line and of its dual
differ. -/
theorem brauerCharacter_dual_cubeRootLine_ne (hp : p.Coprime 3) {ζ : rootsOfUnity 3 k}
    (hζ : ζ ≠ 1) :
    (cubeRootLine k).dual.brauerCharacter p τ ζ ≠ (cubeRootLine k).brauerCharacter p τ ζ := by
  rw [brauerCharacter_dual_cubeRootLine p τ hp, brauerCharacter_cubeRootLine p τ hp]
  intro h
  exact inv_ne_self (pow_three_eq_one ζ) hζ
    (τ.injective (rootsOfUnity.coe_injective h))

/-- **The eigenvalue reading.** Over a domain `L`, the sum of the line and its dual has Brauer
character `-1` at `ζ ≠ 1`: the two eigenvalues `ζ, ζ⁻¹` lift to the two primitive cube roots of
unity of `L`, whose sum is `-1`. -/
theorem brauerCharacter_prod_dual_cubeRootLine [IsDomain L] (hp : p.Coprime 3)
    {ζ : rootsOfUnity 3 k} (hζ : ζ ≠ 1) :
    ((cubeRootLine k).prod (cubeRootLine k).dual).brauerCharacter p τ ζ = -1 := by
  rw [brauerCharacter_prod, brauerCharacter_dual_cubeRootLine p τ hp,
    brauerCharacter_cubeRootLine p τ hp, map_inv]
  set x : L := ((τ ζ : Lˣ) : L)
  have hx1 : x ≠ 1 := fun h ↦ hζ (τ.injective (rootsOfUnity.coe_injective (h.trans (by simp))))
  have hx3 : x ^ 3 = 1 := by
    simp only [x, ← Units.val_pow_eq_pow_val, ← SubmonoidClass.coe_pow, pow_three_eq_one,
      OneMemClass.coe_one, Units.val_one]
  set y : L := ((((τ ζ)⁻¹ : rootsOfUnity 3 L) : Lˣ) : L)
  have hxy : x * y = 1 := by
    simp only [x, y, ← Units.val_mul, ← Subgroup.coe_mul, mul_inv_cancel, OneMemClass.coe_one,
      Units.val_one]
  have hy : y = x ^ 2 := by
    calc y = y * x ^ 3 := by rw [hx3, mul_one]
      _ = (x * y) * x ^ 2 := by ring
      _ = x ^ 2 := by rw [hxy, one_mul]
  have h : (x - 1) * (x ^ 2 + x + 1) = 0 := by linear_combination hx3
  have h2 := (mul_eq_zero.1 h).resolve_left (sub_ne_zero.2 hx1)
  rw [hy]
  linear_combination h2

/-! ### `C₂` at `p = 2` -/

/-- The generator of `C₂ = Multiplicative (ZMod 2)` has order `2`. -/
theorem orderOf_ofAdd_one : orderOf (Multiplicative.ofAdd (1 : ZMod 2)) = 2 := by
  rw [orderOf_ofAdd_eq_addOrderOf, ZMod.addOrderOf_one]

variable {m : ℕ} [NeZero m] (τ₂ : rootsOfUnity m (ZMod 2) ≃* rootsOfUnity m L)

/-- The regular representation of `C₂` over `𝔽₂` has Brauer character `2` at `1`. -/
theorem brauerCharacter_regular_one :
    brauerCharacter 2 τ₂
      (ofMulAction (ZMod 2) (Multiplicative (ZMod 2)) (Multiplicative (ZMod 2))) 1 = 2 := by
  rw [brauerCharacter_one, finrank_eq_card_basis (MonoidAlgebra.basis _ _)]
  simp

/-- The trivial representation of `C₂` on `𝔽₂ ⊕ 𝔽₂` has Brauer character `2` at `1`. -/
theorem brauerCharacter_trivial_one :
    brauerCharacter 2 τ₂ (trivial (ZMod 2) (Multiplicative (ZMod 2)) (ZMod 2 × ZMod 2)) 1 = 2 := by
  rw [brauerCharacter_one]
  simp

/-- Both vanish at the generator, which is `2`-singular. -/
theorem brauerCharacter_ofAdd_one {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V] (ρ : Representation (ZMod 2) (Multiplicative (ZMod 2)) V) :
    ρ.brauerCharacter 2 τ₂ (Multiplicative.ofAdd 1) = 0 :=
  brauerCharacter_of_not_coprime 2 τ₂ ρ (by rw [orderOf_ofAdd_one]; decide)

end TauCeti.BrauerCharacterExamples
