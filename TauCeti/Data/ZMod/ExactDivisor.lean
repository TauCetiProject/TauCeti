/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.ZMod.Units
public import TauCeti.Algebra.Ring.IdempotentUnits
public import TauCeti.Data.Nat.ExactDivisor
import Mathlib.Algebra.Group.Prod

/-!
# The Chinese remainder splitting of `ZMod N` at an exact divisor

For an exact divisor `Q` of `N` (`Q ∣ N` with `Q` coprime to `N / Q`) the Chinese remainder
theorem splits `ZMod N` as `ZMod Q × ZMod (N / Q)`. This file records the splitting as the ring
equivalence `ZMod N ≃+* ZMod Q × ZMod (N / Q)` and, on unit groups, as the product equivalence
`(ZMod N)ˣ ≃* (ZMod Q)ˣ × (ZMod (N / Q))ˣ`; the components of both are the two reductions.
Inside `ZMod N` it records the splitting through its idempotent, the residue `e_Q` that is `1`
modulo `Q` and `0` modulo `N / Q`, so that operations on one component are expressed without a
cast between `ZMod N` and `ZMod (Q * (N / Q))`.

Inverting the `Q`-component of a unit and fixing its `N / Q`-component is then the automorphism
`u ↦ e_Q u⁻¹ + (1 - e_Q) u` of `(ZMod N)ˣ`, the instance of `IsIdempotentElem.unitsInvPart` at
`e_Q`. On characters it is the operation `χ_Q · χ_{N/Q} ↦ χ_Q⁻¹ · χ_{N/Q}`, inverting the
`Q`-part of a character and keeping its `N / Q`-part. This is how the Atkin–Lehner operator `W_Q`
moves the nebentypus of a modular form of level `N`. At `Q = N` it is inversion, the shift
`χ ↦ χ⁻¹` of the Fricke operator, and at `Q = 1` it is the identity.

## Main definitions

* `TauCeti.exactDivisorIdempotent N Q`: the residue `e_Q = (N / Q) · y` of `ZMod N`, for the
  Bézout coefficient `y` of `Q · x + (N / Q) · y = 1`.
* `TauCeti.Nat.IsExactDivisor.ringEquivProd`: the Chinese remainder ring equivalence
  `ZMod N ≃+* ZMod Q × ZMod (N / Q)`.
* `TauCeti.Nat.IsExactDivisor.unitsEquivProd`: the Chinese remainder equivalence
  `(ZMod N)ˣ ≃* (ZMod Q)ˣ × (ZMod (N / Q))ˣ`.
* `TauCeti.Nat.IsExactDivisor.unitsInvPart`: the automorphism of `(ZMod N)ˣ` inverting the
  residue modulo `Q` and fixing the residue modulo `N / Q`.

## Main results

* `TauCeti.Nat.IsExactDivisor.ringEquivProd_apply`: `ringEquivProd` is the pair of reductions
  modulo `Q` and modulo `N / Q`.
* `TauCeti.Nat.IsExactDivisor.unitsEquivProd_apply_fst`,
  `TauCeti.Nat.IsExactDivisor.unitsEquivProd_apply_snd`: the components of `unitsEquivProd` are
  the reductions modulo `Q` and modulo `N / Q`.
* `TauCeti.Nat.IsExactDivisor.eq_of_castHom_eq`: an element of `ZMod N` is determined by its
  residues modulo `Q` and modulo `N / Q`.
* `TauCeti.Nat.IsExactDivisor.eq_exactDivisorIdempotent_iff`: `e_Q` is the residue that is `1`
  modulo `Q` and `0` modulo `N / Q`; it is idempotent
  (`TauCeti.Nat.IsExactDivisor.isIdempotentElem_exactDivisorIdempotent`).
* `TauCeti.Nat.IsExactDivisor.eq_unitsInvPart_iff`: the unit `unitsInvPart u` is characterized by
  its residues, `u⁻¹` modulo `Q` and `u` modulo `N / Q`.
* `TauCeti.Nat.IsExactDivisor.comp_unitsInvPart`: on a character `χ_Q · χ_{N/Q}` pulled back from
  the two factors, precomposition with `unitsInvPart` inverts `χ_Q`.
* `TauCeti.Nat.IsExactDivisor.unitsInvPart_self`, `TauCeti.Nat.IsExactDivisor.unitsInvPart_one`:
  at `Q = N` it is inversion, and at `Q = 1` the identity.

## References

* A. O. L. Atkin and W.-C. W. Li, *Twists of newforms and pseudo-eigenvalues of
  `W`-operators*, Invent. Math. **48** (1978), 221–243, §1.
-/

public section

open scoped TauCeti.ExactDivisor

namespace TauCeti

/-- The residue `e_Q` of `ZMod N` that is `1` modulo `Q` and `0` modulo `N / Q`, when `Q` is an
exact divisor of `N` (`Nat.IsExactDivisor.eq_exactDivisorIdempotent_iff`). It is `(N / Q) · y` for
the Bézout coefficient `y` of `Q · x + (N / Q) · y = 1`, the coefficient that also builds the
Atkin–Lehner matrix `TauCeti.atkinLehnerMatrix N Q`. -/
def exactDivisorIdempotent (N Q : ℕ) : ZMod N :=
  (((N / Q : ℕ) : ℤ) * Nat.gcdB Q (N / Q) : ℤ)

namespace Nat.IsExactDivisor

variable {N Q : ℕ}

/-- **The Chinese remainder ring equivalence at an exact divisor.** For `Q ∥ N`, a residue
modulo `N` is identified with its reductions modulo `Q` and modulo `N / Q`
(`Nat.IsExactDivisor.ringEquivProd_apply`). -/
noncomputable def ringEquivProd (h : Q ∥ N) : ZMod N ≃+* ZMod Q × ZMod (N / Q) :=
  (ZMod.ringEquivCongr (Nat.mul_div_cancel' h.dvd).symm).trans (ZMod.chineseRemainder h.coprime)

/-- The Chinese remainder ring equivalence is the pair of reductions modulo `Q` and modulo
`N / Q`. -/
@[simp]
theorem ringEquivProd_apply (h : Q ∥ N) (x : ZMod N) :
    h.ringEquivProd x =
      (ZMod.castHom h.dvd (ZMod Q) x, ZMod.castHom (Nat.div_dvd_of_dvd h.dvd) (ZMod (N / Q)) x) :=
  -- Both sides are ring homs out of `ZMod N`, and such a ring hom is unique.
  congr($(RingHom.ext_zmod (h.ringEquivProd : ZMod N →+* ZMod Q × ZMod (N / Q))
    ((ZMod.castHom h.dvd (ZMod Q)).prod (ZMod.castHom (Nat.div_dvd_of_dvd h.dvd) _))) x)

/-- **The Chinese remainder equivalence on unit groups at an exact divisor.** For `Q ∥ N`, a unit
modulo `N` is identified with its reductions modulo `Q` and modulo `N / Q`. -/
noncomputable def unitsEquivProd (h : Q ∥ N) :
    (ZMod N)ˣ ≃* (ZMod Q)ˣ × (ZMod (N / Q))ˣ :=
  (Units.mapEquiv h.ringEquivProd.toMulEquiv).trans MulEquiv.prodUnits

/-- The first component of the unit-group Chinese remainder equivalence is reduction modulo the
exact divisor. -/
@[simp]
theorem unitsEquivProd_apply_fst (h : Q ∥ N) (u : (ZMod N)ˣ) :
    (h.unitsEquivProd u).1 = ZMod.unitsMap h.dvd u :=
  Units.ext congr(($(h.ringEquivProd_apply u)).1)

/-- The second component of the unit-group Chinese remainder equivalence is reduction modulo the
complementary divisor. -/
@[simp]
theorem unitsEquivProd_apply_snd (h : Q ∥ N) (u : (ZMod N)ˣ) :
    (h.unitsEquivProd u).2 = ZMod.unitsMap (Nat.div_dvd_of_dvd h.dvd) u :=
  Units.ext congr(($(h.ringEquivProd_apply u)).2)

/-- **An element of `ZMod N` is determined by its residues modulo `Q` and modulo `N / Q`**, for an
exact divisor `Q` of `N`: the injectivity half of the Chinese remainder theorem. -/
theorem eq_of_castHom_eq (h : Q ∥ N) {x y : ZMod N}
    (hQ : ZMod.castHom h.dvd (ZMod Q) x = ZMod.castHom h.dvd (ZMod Q) y)
    (hR : ZMod.castHom (Nat.div_dvd_of_dvd h.dvd) (ZMod (N / Q)) x =
      ZMod.castHom (Nat.div_dvd_of_dvd h.dvd) (ZMod (N / Q)) y) : x = y :=
  h.ringEquivProd.injective <| by rw [ringEquivProd_apply, ringEquivProd_apply, hQ, hR]

/-- `e_Q` is `1` modulo `Q`. -/
theorem castHom_exactDivisorIdempotent_left (h : Q ∥ N) :
    ZMod.castHom h.dvd (ZMod Q) (exactDivisorIdempotent N Q) = 1 := by
  have hbez : (1 : ℤ) = Q * Nat.gcdA Q (N / Q) + (N / Q : ℕ) * Nat.gcdB Q (N / Q) := by
    have := Nat.gcd_eq_gcd_ab Q (N / Q)
    rwa [h.coprime, Nat.cast_one] at this
  rw [exactDivisorIdempotent, map_intCast, eq_sub_of_add_eq' hbez.symm]
  simp

/-- `e_Q` is `0` modulo `N / Q`. -/
theorem castHom_exactDivisorIdempotent_right (h : Q ∥ N) :
    ZMod.castHom (Nat.div_dvd_of_dvd h.dvd) (ZMod (N / Q)) (exactDivisorIdempotent N Q) = 0 := by
  rw [exactDivisorIdempotent, map_intCast, Int.cast_mul, Int.cast_natCast, ZMod.natCast_self,
    zero_mul]

/-- **`e_Q` is the residue that is `1` modulo `Q` and `0` modulo `N / Q`.** -/
theorem eq_exactDivisorIdempotent_iff (h : Q ∥ N) {x : ZMod N} :
    x = exactDivisorIdempotent N Q ↔ ZMod.castHom h.dvd (ZMod Q) x = 1 ∧
      ZMod.castHom (Nat.div_dvd_of_dvd h.dvd) (ZMod (N / Q)) x = 0 := by
  refine ⟨?_, fun ⟨hQ, hR⟩ ↦ h.eq_of_castHom_eq ?_ ?_⟩
  · rintro rfl
    exact ⟨h.castHom_exactDivisorIdempotent_left, h.castHom_exactDivisorIdempotent_right⟩
  · rw [hQ, h.castHom_exactDivisorIdempotent_left]
  · rw [hR, h.castHom_exactDivisorIdempotent_right]

/-- `e_Q` is idempotent: `e_Q ^ 2` has the same residues `1` and `0`. -/
theorem isIdempotentElem_exactDivisorIdempotent (h : Q ∥ N) :
    IsIdempotentElem (exactDivisorIdempotent N Q) := by
  refine (h.eq_exactDivisorIdempotent_iff.mpr ⟨?_, ?_⟩ :)
  · rw [map_mul, h.castHom_exactDivisorIdempotent_left, mul_one]
  · rw [map_mul, h.castHom_exactDivisorIdempotent_right, mul_zero]

/-- **Inverting the residue modulo `Q`**: for an exact divisor `Q` of `N`, the automorphism
`u ↦ e_Q u⁻¹ + (1 - e_Q) u` of `(ZMod N)ˣ`, which inverts the residue of a unit modulo `Q` and
fixes its residue modulo `N / Q` (`Nat.IsExactDivisor.eq_unitsInvPart_iff`). -/
def unitsInvPart (h : Q ∥ N) : (ZMod N)ˣ ≃* (ZMod N)ˣ :=
  h.isIdempotentElem_exactDivisorIdempotent.unitsInvPart

/-- The value of `unitsInvPart` at a unit `u` is `e_Q u⁻¹ + (1 - e_Q) u`. -/
theorem coe_unitsInvPart (h : Q ∥ N) (u : (ZMod N)ˣ) :
    (h.unitsInvPart u : ZMod N) =
      exactDivisorIdempotent N Q * ↑u⁻¹ + (1 - exactDivisorIdempotent N Q) * u :=
  IsIdempotentElem.coe_unitsInvPart _ u

/-- **`unitsInvPart` is an involution**: it is its own inverse. -/
@[simp]
theorem unitsInvPart_symm (h : Q ∥ N) : h.unitsInvPart.symm = h.unitsInvPart :=
  IsIdempotentElem.unitsInvPart_symm _

/-- **`unitsInvPart` is an involution**, applied twice to a unit. -/
@[simp]
theorem unitsInvPart_unitsInvPart (h : Q ∥ N) (u : (ZMod N)ˣ) :
    h.unitsInvPart (h.unitsInvPart u) = u :=
  IsIdempotentElem.unitsInvPart_unitsInvPart _ u

/-- **`unitsInvPart` inverts the residue modulo `Q`.** -/
@[simp]
theorem unitsMap_unitsInvPart_left (h : Q ∥ N) (u : (ZMod N)ˣ) :
    ZMod.unitsMap h.dvd (h.unitsInvPart u) = (ZMod.unitsMap h.dvd u)⁻¹ := by
  refine Units.ext ?_
  rw [← map_inv, ZMod.unitsMap_val, ZMod.unitsMap_val, ← ZMod.castHom_apply (h := h.dvd),
    ← ZMod.castHom_apply (h := h.dvd), coe_unitsInvPart, map_add, map_mul, map_mul, map_sub,
    map_one, h.castHom_exactDivisorIdempotent_left, sub_self, zero_mul, add_zero, one_mul]

/-- **`unitsInvPart` fixes the residue modulo `N / Q`.** -/
@[simp]
theorem unitsMap_unitsInvPart_right (h : Q ∥ N) (u : (ZMod N)ˣ) :
    ZMod.unitsMap (Nat.div_dvd_of_dvd h.dvd) (h.unitsInvPart u) =
      ZMod.unitsMap (Nat.div_dvd_of_dvd h.dvd) u := by
  refine Units.ext ?_
  rw [ZMod.unitsMap_val, ZMod.unitsMap_val, ← ZMod.castHom_apply (h := Nat.div_dvd_of_dvd h.dvd),
    ← ZMod.castHom_apply (h := Nat.div_dvd_of_dvd h.dvd), coe_unitsInvPart, map_add, map_mul,
    map_mul, map_sub, map_one, h.castHom_exactDivisorIdempotent_right, sub_zero, zero_mul,
    zero_add, one_mul]

/-- **`unitsInvPart u` is the unit with residue `u⁻¹` modulo `Q` and `u` modulo `N / Q`.** -/
theorem eq_unitsInvPart_iff (h : Q ∥ N) {u v : (ZMod N)ˣ} :
    v = h.unitsInvPart u ↔ ZMod.unitsMap h.dvd v = (ZMod.unitsMap h.dvd u)⁻¹ ∧
      ZMod.unitsMap (Nat.div_dvd_of_dvd h.dvd) v = ZMod.unitsMap (Nat.div_dvd_of_dvd h.dvd) u := by
  refine ⟨?_, fun ⟨hQ, hR⟩ ↦ Units.ext <| h.eq_of_castHom_eq ?_ ?_⟩
  · rintro rfl
    exact ⟨h.unitsMap_unitsInvPart_left u, h.unitsMap_unitsInvPart_right u⟩
  · rw [ZMod.castHom_apply, ZMod.castHom_apply, ← ZMod.unitsMap_val h.dvd,
      ← ZMod.unitsMap_val h.dvd, h.unitsMap_unitsInvPart_left, hQ]
  · rw [ZMod.castHom_apply, ZMod.castHom_apply, ← ZMod.unitsMap_val (Nat.div_dvd_of_dvd h.dvd),
      ← ZMod.unitsMap_val (Nat.div_dvd_of_dvd h.dvd), h.unitsMap_unitsInvPart_right, hR]

/-- **The character shift `χ_Q · χ_{N/Q} ↦ χ_Q⁻¹ · χ_{N/Q}`**: on a character of `(ZMod N)ˣ` pulled
back from a character `ψ` modulo `Q` and a character `φ` modulo `N / Q`, precomposition with
`unitsInvPart` inverts `ψ` and keeps `φ`. -/
theorem comp_unitsInvPart {G : Type*} [CommGroup G] (h : Q ∥ N) (ψ : (ZMod Q)ˣ →* G)
    (φ : (ZMod (N / Q))ˣ →* G) :
    (ψ.comp (ZMod.unitsMap h.dvd) * φ.comp (ZMod.unitsMap (Nat.div_dvd_of_dvd h.dvd))).comp
        h.unitsInvPart.toMonoidHom =
      ψ⁻¹.comp (ZMod.unitsMap h.dvd) * φ.comp (ZMod.unitsMap (Nat.div_dvd_of_dvd h.dvd)) := by
  ext u
  simp

/-- **At `Q = N` the automorphism is inversion**: every residue is a residue modulo `Q`. -/
@[simp]
theorem unitsInvPart_self (h : N ∥ N) : h.unitsInvPart = MulEquiv.inv (ZMod N)ˣ := by
  refine MulEquiv.ext fun u ↦ ((h.eq_unitsInvPart_iff (u := u)).mpr ⟨?_, ?_⟩).symm
  · simp
  · have : Subsingleton (ZMod (N / N)) := by rw [Nat.div_self h.pos]; infer_instance
    exact Units.ext (Subsingleton.elim _ _)

/-- **At `Q = 1` the automorphism is the identity**: every residue is a residue modulo `N / Q`. -/
@[simp]
theorem unitsInvPart_one (h : 1 ∥ N) : h.unitsInvPart = MulEquiv.refl (ZMod N)ˣ := by
  refine MulEquiv.ext fun u ↦ ((h.eq_unitsInvPart_iff (u := u)).mpr ⟨?_, ?_⟩).symm
  · exact Subsingleton.elim _ _
  · simp [ZMod.unitsMap_def]

end Nat.IsExactDivisor

end TauCeti
