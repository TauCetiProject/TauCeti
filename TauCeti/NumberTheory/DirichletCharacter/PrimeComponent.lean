/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Data.ZMod.ExactDivisor
public import TauCeti.NumberTheory.DirichletCharacter.Conductor
import TauCeti.NumberTheory.MulChar.Basic

/-!
# The prime components of a Dirichlet character

For a Dirichlet character `χ` modulo `N` and a natural number `r`, the Chinese remainder theorem
splits `(ZMod N)ˣ` as `(ZMod (r ^ v_r(N)))ˣ × (ZMod (N / r ^ v_r(N)))ˣ`. The *component of `χ`
at `r`* is the restriction of `χ` to the first factor: the character modulo `r ^ v_r(N)` whose
value at a unit `u` is the value of `χ` at the unit modulo `N` that is `u` modulo `r ^ v_r(N)` and
`1` modulo `N / r ^ v_r(N)`. For `r` not a prime factor of `N` the level `r ^ v_r(N)` is `1`.

The components are multiplicative in `χ`, commute with a change of coefficient ring, and
determine `χ`: `χ` is the product of its components at the prime factors of `N`, raised to level
`N`, and this is the only way to write `χ` as such a product. The order of `χ` is the least common
multiple of the orders of its components, and the conductor of the component at `r` is the
`r`-primary part `r ^ v_r(f_χ)` of the conductor `f_χ` of `χ`.

## Main definitions

* `TauCeti.primeComponent r`: the component at `r`, as a monoid homomorphism from the characters
  modulo `N` to the characters modulo `r ^ v_r(N)`.

## Main results

* `TauCeti.primeComponent_apply_unit`: the value of the component at a unit.
* `TauCeti.prod_changeLevel_primeComponent`: for `N ≠ 0`, `χ` is the product over the prime
  factors `r` of `N` of its components at `r`, raised to level `N`.
* `TauCeti.prod_changeLevel_eq_iff`: uniqueness, a product of characters modulo the prime powers
  `r ^ v_r(N)` raised to level `N` equals `χ` exactly when its factors are the components of `χ`.
* `TauCeti.orderOf_eq_lcm_orderOf_primeComponent`: for `N ≠ 0`, the order of `χ` is the least
  common multiple of the orders of its prime components.
* `TauCeti.primeComponent_changeLevel`: components commute with raising the level.
* `TauCeti.primeComponent_ringHomComp`: components commute with a change of coefficient ring.
* `TauCeti.conductor_primeComponent`: the conductor of the component at `r` is `r ^ v_r(f_χ)`.
-/

public noncomputable section

namespace TauCeti

open DirichletCharacter

variable {R : Type*} [CommMonoidWithZero R] {N : ℕ}

/-- The component at `r` of a Dirichlet character `χ` modulo `N`: the character modulo
`r ^ v_r(N)` obtained by restricting `χ` along the Chinese remainder embedding
`u ↦ (u, 1)` of `(ZMod (r ^ v_r(N)))ˣ` into `(ZMod N)ˣ`. -/
def primeComponent (r : ℕ) :
    DirichletCharacter R N →* DirichletCharacter R (r ^ N.factorization r) where
  toFun χ := MulChar.ofUnitHom <| χ.toUnitHom.comp <|
    (Nat.isExactDivisor_primePow (N := N) (p := r)).unitsEquivProd.symm.toMonoidHom.comp
      (MonoidHom.inl _ _)
  map_one' := by ext; simp
  map_mul' χ ψ := by ext; simp

/-- The component at `r` evaluated at a unit `u` is the value of `χ` at the unit modulo `N` that
is `u` modulo `r ^ v_r(N)` and `1` modulo `N / r ^ v_r(N)`. -/
theorem primeComponent_apply_unit (r : ℕ) (χ : DirichletCharacter R N)
    (u : (ZMod (r ^ N.factorization r))ˣ) :
    primeComponent r χ u =
      χ ((Nat.isExactDivisor_primePow (N := N) (p := r)).unitsEquivProd.symm (u, 1) : ZMod N) := by
  simp [primeComponent]

/-- A character raised to level `N` takes at a unit modulo `N` its value at the reduction. -/
private theorem changeLevel_apply_unit {M : ℕ} (hMN : M ∣ N) (χ : DirichletCharacter R M)
    (u : (ZMod N)ˣ) : changeLevel hMN χ u = χ (ZMod.unitsMap hMN u : ZMod M) := by
  rw [changeLevel_eq_cast_of_dvd, ZMod.unitsMap_val]

/-- **The component of a character raised from a level `M`.** For `M ∣ N` with `N ≠ 0`, the
component at `r` of a character modulo `M` raised to level `N` is its component at `r` raised from
level `r ^ v_r(M)` to level `r ^ v_r(N)`. -/
theorem primeComponent_changeLevel {M : ℕ} (hN : N ≠ 0) (hMN : M ∣ N) (r : ℕ)
    (χ : DirichletCharacter R M) :
    primeComponent r (changeLevel hMN χ) =
      changeLevel (Nat.ordProj_dvd_ordProj_of_dvd hN hMN r) (primeComponent r χ) := by
  set hM := Nat.isExactDivisor_primePow (N := M) (p := r)
  set hN' := Nat.isExactDivisor_primePow (N := N) (p := r)
  refine MulChar.ext fun u ↦ ?_
  -- reducing the lift `(u, 1)` modulo `M` gives the lift of the reduction of `u`
  have hlift : ZMod.unitsMap hMN (hN'.unitsEquivProd.symm (u, 1)) =
      hM.unitsEquivProd.symm (ZMod.unitsMap (Nat.ordProj_dvd_ordProj_of_dvd hN hMN r) u, 1) := by
    rw [MulEquiv.eq_symm_apply]
    refine Prod.ext ?_ ?_
    · rw [hM.unitsEquivProd_apply_fst, ← MonoidHom.comp_apply, ZMod.unitsMap_comp,
        ← ZMod.unitsMap_comp (Nat.ordProj_dvd_ordProj_of_dvd hN hMN r) hN'.dvd,
        MonoidHom.comp_apply, ← hN'.unitsEquivProd_apply_fst, MulEquiv.apply_symm_apply]
    · rw [hM.unitsEquivProd_apply_snd, ← MonoidHom.comp_apply, ZMod.unitsMap_comp,
        hN'.unitsMap_unitsEquivProd_symm_of_dvd_div (Nat.ordCompl_dvd_ordCompl_of_dvd hMN r),
        map_one]
  rw [primeComponent_apply_unit, changeLevel_apply_unit, hlift, changeLevel_apply_unit,
    primeComponent_apply_unit]

/-- The component at `r` of a character raised from a divisor `M` of `r ^ v_r(N)` is that
character raised to level `r ^ v_r(N)`. -/
theorem primeComponent_changeLevel_of_dvd_ordProj {M r : ℕ} (hM : M ∣ r ^ N.factorization r)
    (χ : DirichletCharacter R M) :
    primeComponent r (changeLevel (hM.trans (Nat.ordProj_dvd N r)) χ) = changeLevel hM χ := by
  refine MulChar.ext fun u ↦ ?_
  rw [primeComponent_apply_unit, changeLevel_apply_unit, changeLevel_apply_unit,
    Nat.isExactDivisor_primePow.unitsMap_unitsEquivProd_symm_of_dvd hM]

/-- The component at `r` of a character modulo `r ^ v_r(N)` raised to level `N` is that
character. -/
@[simp]
theorem primeComponent_changeLevel_ordProj (r : ℕ)
    (χ : DirichletCharacter R (r ^ N.factorization r)) :
    primeComponent r (changeLevel (Nat.ordProj_dvd N r) χ) = χ := by
  rw [primeComponent_changeLevel_of_dvd_ordProj dvd_rfl, changeLevel_self]

/-- The component at `r` of a character raised from a divisor `M` of `N / r ^ v_r(N)` is
trivial. -/
theorem primeComponent_changeLevel_of_dvd_ordCompl {M r : ℕ}
    (hM : M ∣ N / r ^ N.factorization r) (χ : DirichletCharacter R M) :
    primeComponent r (changeLevel (hM.trans (Nat.div_dvd_of_dvd (Nat.ordProj_dvd N r))) χ) = 1 := by
  refine MulChar.ext fun u ↦ ?_
  rw [primeComponent_apply_unit, changeLevel_apply_unit,
    Nat.isExactDivisor_primePow.unitsMap_unitsEquivProd_symm_of_dvd_div hM, map_one,
    Units.val_one, map_one, MulChar.one_apply_coe]

/-- **A character is the product of its prime components.** For `N ≠ 0`, a character modulo `N`
is the product over the prime factors `r` of `N` of its components at `r`, raised to level `N`. -/
theorem prod_changeLevel_primeComponent (hN : N ≠ 0) (χ : DirichletCharacter R N) :
    ∏ r ∈ N.primeFactors, changeLevel (Nat.ordProj_dvd N r) (primeComponent r χ) = χ := by
  refine MulChar.ext fun u ↦ ?_
  conv_rhs => rw [← Nat.prod_unitsEquivProd_symm_primePow hN u, Units.coe_prod, map_prod]
  simp only [MulChar.prod_apply_coe, changeLevel_apply_unit, primeComponent_apply_unit]

/-- The component at `q` of a product over the prime factors `r` of `N` of characters modulo the
prime powers `r ^ v_r(N)`, raised to level `N`, is the factor at `q`. Away from the prime factors
of `N` both sides are characters modulo `1`. -/
theorem primeComponent_prod_changeLevel
    (χ : (r : ℕ) → DirichletCharacter R (r ^ N.factorization r)) (q : ℕ) :
    primeComponent q (∏ r ∈ N.primeFactors, changeLevel (Nat.ordProj_dvd N r) (χ r)) = χ q := by
  by_cases hq : q ∈ N.primeFactors
  · rw [map_prod, Finset.prod_eq_single q, primeComponent_changeLevel_ordProj]
    · exact fun r _ hrq ↦ primeComponent_changeLevel_of_dvd_ordCompl
        (Nat.ordProj_dvd_ordCompl_of_ne (Nat.prime_of_mem_primeFactors hq) hrq) _
    · exact fun h ↦ (h hq).elim
  have h1 : q ^ N.factorization q = 1 := by
    rw [Finsupp.notMem_support_iff.mp (by rwa [Nat.support_factorization]), pow_zero]
  exact (level_one' _ h1).trans (level_one' _ h1).symm

/-- **Uniqueness of the prime decomposition.** For `N ≠ 0`, a product over the prime factors `r`
of `N` of characters modulo `r ^ v_r(N)`, raised to level `N`, equals `ψ` exactly when each factor
is the component of `ψ` at `r`. -/
theorem prod_changeLevel_eq_iff (hN : N ≠ 0)
    (χ : (r : ℕ) → DirichletCharacter R (r ^ N.factorization r)) (ψ : DirichletCharacter R N) :
    ∏ r ∈ N.primeFactors, changeLevel (Nat.ordProj_dvd N r) (χ r) = ψ ↔
      ∀ r ∈ N.primeFactors, χ r = primeComponent r ψ := by
  refine ⟨fun h r _ ↦ h ▸ (primeComponent_prod_changeLevel χ r).symm, fun h ↦ ?_⟩
  rw [Finset.prod_congr rfl fun r hr ↦ congrArg _ (h r hr), prod_changeLevel_primeComponent hN]

/-- **The order of a character is the least common multiple of the orders of its prime
components**, for `N ≠ 0`. -/
theorem orderOf_eq_lcm_orderOf_primeComponent (hN : N ≠ 0) (χ : DirichletCharacter R N) :
    orderOf χ = N.primeFactors.lcm fun r ↦ orderOf (primeComponent r χ) := by
  set L := N.primeFactors.lcm fun r ↦ orderOf (primeComponent r χ)
  refine Nat.dvd_antisymm (orderOf_dvd_of_pow_eq_one ?_)
    (Finset.lcm_dvd fun r _ ↦ orderOf_map_dvd (primeComponent r) χ)
  -- each component is killed by `L`, hence so is their product `χ`
  have hpow (r : ℕ) (hr : r ∈ N.primeFactors) : primeComponent r χ ^ L = 1 :=
    orderOf_dvd_iff_pow_eq_one.mp (Finset.dvd_lcm hr)
  rw [← prod_changeLevel_primeComponent hN χ, ← Finset.prod_pow]
  exact Finset.prod_eq_one fun r hr ↦ by rw [← map_pow, hpow r hr, map_one]

/-- Components commute with a change of coefficient ring: they are compatible with Galois
conjugation of the values. -/
theorem primeComponent_ringHomComp {S S' : Type*} [CommRing S] [CommRing S'] (r : ℕ)
    (χ : DirichletCharacter S N) (f : S →+* S') :
    primeComponent r (χ.ringHomComp f) = (primeComponent r χ).ringHomComp f := by
  ext u
  simp [primeComponent_apply_unit, MulChar.ringHomComp_apply]

/-- The component at `r` of a primitive character modulo `N ≠ 0` is primitive: its conductor is
the full level `r ^ v_r(N)`. -/
private theorem conductor_primeComponent_of_isPrimitive (hN : N ≠ 0) (r : ℕ)
    {χ : DirichletCharacter R N} (hχ : χ.IsPrimitive) :
    (primeComponent r χ).conductor = r ^ N.factorization r := by
  have : NeZero N := ⟨hN⟩
  set h := Nat.isExactDivisor_primePow (N := N) (p := r)
  -- the restriction of `χ` to the complementary Chinese remainder factor
  let τ : DirichletCharacter R (N / r ^ N.factorization r) := MulChar.ofUnitHom
    ((χ.toUnitHom.comp h.unitsEquivProd.symm.toMonoidHom).comp (MonoidHom.inr _ _))
  have hsplit : χ = changeLevel h.dvd (primeComponent r χ) *
      changeLevel (Nat.div_dvd_of_dvd h.dvd) τ := by
    refine MulChar.ext fun u ↦ ?_
    have hu := congrArg Units.val (DFunLike.congr_fun (h.eq_mul_comp_unitsMap χ.toUnitHom) u)
    simpa [τ, changeLevel_def, primeComponent] using hu
  -- `N = f_χ` divides the product of the conductors of the two factors
  have hc := (conductor_mul_dvd_lcm_conductor (changeLevel h.dvd (primeComponent r χ))
    (changeLevel (Nat.div_dvd_of_dvd h.dvd) τ)).trans (Nat.lcm_dvd_mul _ _)
  rw [← hsplit, hχ, conductor_changeLevel, conductor_changeLevel] at hc
  refine Nat.dvd_antisymm (conductor_dvd_level _) ?_
  exact (h.coprime.of_dvd_right τ.conductor_dvd_level).dvd_of_dvd_mul_right
    ((Nat.ordProj_dvd N r).trans hc)

/-- **The conductor of a prime component.** The conductor of the component at `r` of a
character `χ` is the `r`-primary part `r ^ v_r(f_χ)` of the conductor `f_χ` of `χ`. -/
theorem conductor_primeComponent (r : ℕ) (χ : DirichletCharacter R N) :
    (primeComponent r χ).conductor = r ^ χ.conductor.factorization r := by
  obtain rfl | hN := eq_or_ne N 0
  · have hc : χ.conductor = 0 := conductor_eq_zero_iff_level_eq_zero.mpr rfl
    rw [hc]
    conv_rhs => rw [Nat.factorization_zero, Finsupp.coe_zero, Pi.zero_apply, pow_zero]
    exact Nat.eq_one_of_dvd_one ((conductor_dvd_level _).trans (by simp))
  have : NeZero N := ⟨hN⟩
  have : NeZero (r ^ N.factorization r) := ⟨(Nat.ordProj_pos N r).ne'⟩
  have h := primeComponent_changeLevel hN χ.conductor_dvd_level r χ.primitiveCharacter
  rw [changeLevel_primitiveCharacter] at h
  rw [h, conductor_changeLevel, conductor_primeComponent_of_isPrimitive χ.conductor_ne_zero r
    χ.primitiveCharacter_isPrimitive]

end TauCeti
