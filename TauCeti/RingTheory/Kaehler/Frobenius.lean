/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.PurelyInseparable.Basic
public import Mathlib.RingTheory.Kaehler.Basic

/-!
# Kähler differentials in prime characteristic and the Frobenius subfield

Every derivation out of a ring of characteristic `p` vanishes on `p`-th powers. Consequently,
every derivation out of a field `k` of prime characteristic `p` vanishes on the Frobenius subfield
`k ^ p = (frobenius k p).fieldRange`, and for any base ring `R` whose image in `k` lies in
`k ^ p`, the module of Kähler differentials `Ω[k⁄R]` is canonically `k`-linearly isomorphic to
`Ω[k⁄(frobenius k p).fieldRange]`.

## Main definitions

* `TauCeti.kaehlerEquivFrobeniusRange`: the canonical `k`-linear equivalence
  `Ω[k⁄R] ≃ₗ[k] Ω[k⁄(frobenius k p).fieldRange]`.

## Main results

* `Derivation.map_pow_char`: in characteristic `p`, any derivation vanishes on `p`-th powers.
* `Derivation.map_eq_zero_of_mem_fieldRange_frobenius`: any derivation out of `k` vanishes on
  `k ^ p`.
* `TauCeti.D_pow_char`: `D R A (x ^ p) = 0` in characteristic `p`.
* `TauCeti.D_eq_zero_of_mem_fieldRange_frobenius`: `D R k` vanishes on `k ^ p`.
-/

public section

noncomputable section

namespace Derivation

/-- In characteristic `p`, any derivation annihilates `p`-th powers. -/
theorem map_pow_char {R A M : Type*} [CommSemiring R] [CommSemiring A] [Algebra R A]
    [AddCommMonoid M] [Module R M] [Module A M] {p : ℕ} [CharP A p]
    (d : Derivation R A M) (x : A) : d (x ^ p) = 0 := by
  rw [Derivation.leibniz_pow, ← Nat.cast_smul_eq_nsmul A, CharP.cast_eq_zero, zero_smul]

/-- Every element of the Frobenius subfield `k ^ p` is annihilated by any derivation out of `k`. -/
theorem map_eq_zero_of_mem_fieldRange_frobenius {p : ℕ} [Fact p.Prime] {R k M : Type*}
    [CommSemiring R] [Field k] [ExpChar k p] [Algebra R k] [AddCommMonoid M] [Module R M]
    [Module k M] (d : Derivation R k M) {x : k} (hx : x ∈ (frobenius k p).fieldRange) :
    d x = 0 := by
  have : CharP k p := (expChar_prime_iff k Fact.out).mp ‹_›
  obtain ⟨a, rfl⟩ := hx
  rw [frobenius_def, d.map_pow_char]

end Derivation

namespace TauCeti

open KaehlerDifferential

/-- In characteristic `p`, the universal derivation vanishes on `p`-th powers. -/
theorem D_pow_char (R : Type*) {A : Type*} [CommRing R] [CommRing A] [Algebra R A]
    {p : ℕ} [CharP A p] (x : A) : D R A (x ^ p) = 0 :=
  (D R A).map_pow_char x

/-- Every element of the Frobenius subfield `k ^ p` has vanishing universal differential over any
commutative base ring `R`. -/
theorem D_eq_zero_of_mem_fieldRange_frobenius {p : ℕ} [Fact p.Prime] {R k : Type*}
    [CommRing R] [Field k] [ExpChar k p] [Algebra R k] {x : k}
    (hx : x ∈ (frobenius k p).fieldRange) :
    D R k x = 0 :=
  (D R k).map_eq_zero_of_mem_fieldRange_frobenius hx

private def derivationOfMapZero {R S A M : Type*} [CommRing R] [CommRing S] [CommRing A]
    [Algebra R A] [Algebra S A] [AddCancelCommMonoid M] [Module R M] [Module S M] [Module A M]
    [IsScalarTower S A M] (d : Derivation R A M)
    (hS : ∀ s : S, d (algebraMap S A s) = 0) : Derivation S A M :=
  Derivation.mk'
    { toFun := d
      map_add' := d.map_add
      map_smul' := fun s a ↦ by
        rw [RingHom.id_apply, Algebra.smul_def, d.leibniz, hS s, smul_zero, add_zero,
          IsScalarTower.algebraMap_smul] }
    d.leibniz

@[simp]
private theorem derivationOfMapZero_apply {R S A M : Type*} [CommRing R] [CommRing S] [CommRing A]
    [Algebra R A] [Algebra S A] [AddCancelCommMonoid M] [Module R M] [Module S M] [Module A M]
    [IsScalarTower S A M] (d : Derivation R A M)
    (hS : ∀ s : S, d (algebraMap S A s) = 0) (a : A) :
    derivationOfMapZero d hS a = d a :=
  rfl

variable (p : ℕ) [Fact p.Prime] (R k : Type*) [CommRing R] [Field k] [ExpChar k p] [Algebra R k]

/-- The canonical `k`-linear equivalence `Ω[k⁄R] ≃ₗ[k] Ω[k⁄k ^ p]` when the image of `R` in `k`
lies in the Frobenius subfield `k ^ p`. -/
def kaehlerEquivFrobeniusRange
    (hR : ∀ r : R, algebraMap R k r ∈ (frobenius k p).fieldRange) :
    Ω[k⁄R] ≃ₗ[k] Ω[k⁄(frobenius k p).fieldRange] :=
  letI : Algebra R (frobenius k p).fieldRange :=
    RingHom.toAlgebra ((algebraMap R k).codRestrict (frobenius k p).fieldRange hR)
  haveI : IsScalarTower R (frobenius k p).fieldRange k := IsScalarTower.of_algebraMap_eq' rfl
  let fwd : Ω[k⁄R] →ₗ[k] Ω[k⁄(frobenius k p).fieldRange] :=
    KaehlerDifferential.map R (frobenius k p).fieldRange k k
  let bwd : Ω[k⁄(frobenius k p).fieldRange] →ₗ[k] Ω[k⁄R] :=
    (derivationOfMapZero (D R k)
      fun c ↦ D_eq_zero_of_mem_fieldRange_frobenius c.2).liftKaehlerDifferential
  LinearEquiv.ofLinearMap fwd bwd
    (Derivation.liftKaehlerDifferential_unique _ _ (by
      ext x
      simp [fwd, bwd]))
    (Derivation.liftKaehlerDifferential_unique _ _ (by
      ext x
      simp [fwd, bwd]))

/-- `kaehlerEquivFrobeniusRange` sends `D R k x` to `D (frobenius k p).fieldRange k x`. -/
@[simp]
theorem kaehlerEquivFrobeniusRange_D
    (hR : ∀ r : R, algebraMap R k r ∈ (frobenius k p).fieldRange) (x : k) :
    kaehlerEquivFrobeniusRange p R k hR (D R k x) = D (frobenius k p).fieldRange k x := by
  let _ : Algebra R (frobenius k p).fieldRange :=
    RingHom.toAlgebra ((algebraMap R k).codRestrict (frobenius k p).fieldRange hR)
  have _ : IsScalarTower R (frobenius k p).fieldRange k := IsScalarTower.of_algebraMap_eq' rfl
  rw [kaehlerEquivFrobeniusRange, LinearEquiv.coe_ofLinearMap, KaehlerDifferential.map_D]
  rfl

/-- The inverse of `kaehlerEquivFrobeniusRange` sends `D (frobenius k p).fieldRange k x` to
`D R k x`. -/
@[simp]
theorem kaehlerEquivFrobeniusRange_symm_D
    (hR : ∀ r : R, algebraMap R k r ∈ (frobenius k p).fieldRange) (x : k) :
    (kaehlerEquivFrobeniusRange p R k hR).symm (D (frobenius k p).fieldRange k x) = D R k x := by
  let _ : Algebra R (frobenius k p).fieldRange :=
    RingHom.toAlgebra ((algebraMap R k).codRestrict (frobenius k p).fieldRange hR)
  have _ : IsScalarTower R (frobenius k p).fieldRange k := IsScalarTower.of_algebraMap_eq' rfl
  rw [kaehlerEquivFrobeniusRange, LinearEquiv.symm_ofLinearMap, LinearEquiv.coe_ofLinearMap,
    Derivation.liftKaehlerDifferential_comp_D, derivationOfMapZero_apply]

end TauCeti

end
