/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.ZMod.Basic
public import TauCeti.RepresentationTheory.CharacterTable.Glauberman.CanonicalExtension

/-!
# Checks for Glauberman's canonical extension

These examples check `TauCeti.IsCanonicalExtension` in two small cases.

* Trivial action: `Γ ⋊[1] S` is `Γ × S`, and the canonical extension of `χ` is `χ × 1_S`,
  `x ↦ χ x.left`.
* `S₃ = C₃ ⋊ C₂`, with `C₂ = ℤˣ` acting on `C₃` by inversion: the sign character `x ↦ x.right`
  also extends the trivial character of `C₃`, but the canonical extension of `1` is `1`, and the
  sign is not canonical.
-/

public section

open SemidirectProduct

namespace TauCeti.Examples.RepresentationTheory.CanonicalExtension

variable {k : Type*} [Field k]

/-- **Trivial action**: for the trivial action, `Γ ⋊[1] S ≅ Γ × S`, and the canonical extension of
an irreducible character `χ` of `Γ` is `χ × 1_S`, read through the first coordinate. -/
example {Γ S : Type*} [Group Γ] [Group S] {χ : Γ → k} (hχ : χ ∈ irreducibleCharacters k Γ) :
    IsCanonicalExtension (1 : S →* MulAut Γ) χ fun x => χ x.left := by
  obtain ⟨n, ρ, -, rfl⟩ := mem_irreducibleCharacters_iff.1 hχ
  let π : Γ ⋊[(1 : S →* MulAut Γ)] S →* Γ := (MonoidHom.fst Γ S).comp mulEquivProd.toMonoidHom
  have hπ : Function.Surjective π := fun g => ⟨inl g, rfl⟩
  refine isCanonicalExtension_iff.2
    ⟨π.comp_mem_irreducibleCharacters hπ hχ, rfl, n, ρ.comp π, rfl, fun s => ?_⟩
  change (ρ 1).det = 1
  rw [map_one, map_one]

/-- `ℤˣ` acting on a commutative group `A` by powers, so that `-1` acts by inversion. -/
def zpowAction (A : Type*) [CommGroup A] : ℤˣ →* MulAut A where
  toFun u :=
    { toFun a := a ^ (u : ℤ)
      invFun a := a ^ (u : ℤ)
      left_inv a := by simp [← zpow_mul, ← Units.val_mul]
      right_inv a := by simp [← zpow_mul, ← Units.val_mul]
      map_mul' a b := mul_zpow a b _ }
  map_one' := by ext; simp
  map_mul' u v := by
    ext a
    simp only [MulEquiv.coe_mk, Equiv.coe_fn_mk, MulAut.mul_apply, Units.val_mul]
    rw [mul_comm, zpow_mul]

variable [IsAlgClosed k] [CharZero k]

/-- **`S₃ = C₃ ⋊ C₂`**: the sign character `x ↦ x.right` of `C₃ ⋊ ℤˣ` extends the trivial
character of `C₃`, but it is not the canonical extension of `1`, which is `1`: the sign has
determinant `-1` on `C₂`. -/
example :
    ((fun x : Multiplicative (ZMod 3) ⋊[zpowAction _] ℤˣ => ((x.right : ℤ) : k)) ∘ inl =
      fun _ => (1 : k)) ∧
      IsCanonicalExtension (zpowAction (Multiplicative (ZMod 3))) (fun _ => (1 : k))
        (fun _ => 1) ∧
      ¬ IsCanonicalExtension (zpowAction (Multiplicative (ZMod 3))) (fun _ => (1 : k))
        fun x => ((x.right : ℤ) : k) := by
  refine ⟨funext fun _ => by simp, isCanonicalExtension_one, fun h => ?_⟩
  have hcop : (Nat.card (Multiplicative (ZMod 3))).Coprime (Nat.card ℤˣ) := by
    simp only [Nat.card_eq_fintype_card, Fintype.card_multiplicative, ZMod.card,
      Fintype.card_units_int, Nat.coprime_two_right]
    decide
  have h1 := congrFun (h.eq_one hcop) (inr (-1))
  norm_num at h1

end TauCeti.Examples.RepresentationTheory.CanonicalExtension
