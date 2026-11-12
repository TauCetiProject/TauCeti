/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Data.ZMod.ExactDivisor
public import TauCeti.NumberTheory.DirichletCharacter.Conductor
public import TauCeti.NumberTheory.DirichletCharacter.Quadratic

/-!
# The local factors of a Dirichlet character

Let `χ` be a Dirichlet character of level `N` and `p` a prime, with `p ^ k` the exact power of
`p` dividing `N`. The Chinese remainder theorem `(ℤ/N)ˣ ≃ (ℤ/p^k)ˣ × (ℤ/(N/p^k))ˣ` restricts `χ`
to a character of level `p ^ k`, the *local factor* of `χ` at `p`: its value at a unit `a` modulo
`p ^ k` is `χ x` for the unit `x` modulo `N` with `x ≡ a (mod p ^ k)` and `x ≡ 1 (mod N / p ^ k)`.
(This is the `p`-primary component of `χ`, not the Euler factor of its `L`-function at `p`.)

For `N ≠ 0`, `χ` is the product of the lifts of its local factors to level `N`, and the local
factors are the only characters of the levels `p ^ k` with this property. The conductor is
multiplicative over this decomposition: the conductor of `χ` is the product of the conductors of
its local factors, and the conductor of the local factor at `p` is the exact power of `p` dividing
the conductor of `χ`. A character is quadratic exactly when all its local factors are. This
reduces questions about conductors of (quadratic) characters to prime-power levels.

## Main definitions

* `DirichletCharacter.localFactor p`: the local factor at `p`, as a homomorphism from the
  characters of level `N` to the characters of level `p ^ v_p(N)`.

## Main results

* `DirichletCharacter.localFactor_apply_of_unitsMap`: the value of the local factor at a unit `a`
  is `χ x` for any unit `x` that is `a` modulo `p ^ v_p(N)` and `1` modulo the complementary
  divisor.
* `DirichletCharacter.prod_changeLevel_localFactor`: for `N ≠ 0`, `χ` is the product over the
  primes `p ∣ N` of the lifts of its local factors.
* `DirichletCharacter.localFactor_prod_changeLevel`: the local factors of such a product are its
  factors, so the decomposition is unique.
* `DirichletCharacter.conductor_eq_prod_conductor_localFactor`: the conductor of `χ` is the
  product of the conductors of its local factors.
* `DirichletCharacter.conductor_localFactor`: the conductor of the local factor at `p` is
  `p ^ v_p(cond χ)`.
* `DirichletCharacter.isQuadratic_iff_forall_isQuadratic_localFactor`: `χ` is quadratic exactly
  when all its local factors are.

## References

* H. L. Montgomery and R. C. Vaughan, *Multiplicative Number Theory I: Classical Theory*,
  Cambridge Studies in Advanced Mathematics 97 (2006), Lemma 9.3 and §9.3.
-/

public section

open scoped TauCeti.ExactDivisor

namespace DirichletCharacter

open TauCeti.Nat

variable {R : Type*} [CommMonoidWithZero R] {N : ℕ}

/-- **The local factor at `p`** of a Dirichlet character `χ` of level `N`: the character of level
`p ^ v_p(N)` whose value at a unit `a` is `χ x` for the unit `x` modulo `N` that is `a` modulo
`p ^ v_p(N)` and `1` modulo `N / p ^ v_p(N)` (`DirichletCharacter.localFactor_apply_of_unitsMap`).
For `p` not a prime factor of `N` the level is `1`. -/
noncomputable def localFactor (p : ℕ) :
    DirichletCharacter R N →* DirichletCharacter R (ordProj[p] N) where
  toFun χ := MulChar.ofUnitHom <| χ.toUnitHom.comp <|
    (isExactDivisor_primePow (N := N) (p := p)).unitsEquivProd.symm.toMonoidHom.comp
      (MonoidHom.inl _ _)
  map_one' := by ext; simp
  map_mul' χ ψ := by ext; simp

/-- The value of the local factor at a unit `a` is the value of `χ` at the Chinese remainder lift
of `(a, 1)`. -/
@[simp]
theorem localFactor_apply_unit (p : ℕ) (χ : DirichletCharacter R N)
    (a : (ZMod (ordProj[p] N))ˣ) :
    localFactor p χ a = χ (isExactDivisor_primePow.unitsEquivProd.symm (a, 1) : ZMod N) := by
  simp [localFactor]

/-- The value of the local factor at a unit `a` is `χ u` for any unit `u` modulo `N` that is `a`
modulo `p ^ v_p(N)` and `1` modulo `N / p ^ v_p(N)`. -/
theorem localFactor_apply_of_unitsMap (p : ℕ) (χ : DirichletCharacter R N)
    {a : (ZMod (ordProj[p] N))ˣ} {u : (ZMod N)ˣ}
    (ha : ZMod.unitsMap (Nat.ordProj_dvd N p) u = a)
    (h1 : ZMod.unitsMap (Nat.div_dvd_of_dvd (Nat.ordProj_dvd N p)) u = 1) :
    localFactor p χ a = χ u := by
  rw [localFactor_apply_unit, (MulEquiv.symm_apply_eq _).mpr (Prod.ext ?_ ?_)]
  · exact (isExactDivisor_primePow.unitsEquivProd_apply_fst u).trans ha |>.symm
  · exact (isExactDivisor_primePow.unitsEquivProd_apply_snd u).trans h1 |>.symm

/-- **A Dirichlet character is the product of its local factors**: for `N ≠ 0`, `χ` is the
product over the primes `p ∣ N` of its local factors lifted back to level `N`. -/
theorem prod_changeLevel_localFactor [NeZero N] (χ : DirichletCharacter R N) :
    ∏ p ∈ N.primeFactors, changeLevel (Nat.ordProj_dvd N p) (localFactor p χ) = χ := by
  refine MulChar.ext fun u ↦ ?_
  -- evaluate the product of characters at a unit through `MulChar.mulEquivToUnitHom`
  have h (ψ : DirichletCharacter R N) (v : (ZMod N)ˣ) :
      ψ v = (MulChar.mulEquivToUnitHom ψ v : R) := by simp
  conv_rhs => rw [← prod_unitsEquivProd_symm_primePow (NeZero.ne N) u, Units.coe_prod, map_prod]
  rw [h, map_prod, MonoidHom.finsetProd_apply, Units.coe_prod]
  refine Finset.prod_congr rfl fun p _ ↦ ?_
  rw [← h, changeLevel_eq_cast_of_dvd, ← ZMod.unitsMap_val, localFactor_apply_unit]

/-- **Uniqueness of the local decomposition**: if `ψ p` is a character of level `p ^ v_p(N)` for
each prime `p ∣ N`, then the local factor at `q` of the product of their lifts to level `N` is
`ψ q`. With `DirichletCharacter.prod_changeLevel_localFactor`, the local factors are the only
such family whose product is a given character. -/
theorem localFactor_prod_changeLevel (ψ : ∀ p, DirichletCharacter R (ordProj[p] N))
    {q : ℕ} (hq : q ∈ N.primeFactors) :
    localFactor q (∏ p ∈ N.primeFactors, changeLevel (Nat.ordProj_dvd N p) (ψ p)) = ψ q := by
  rw [map_prod, Finset.prod_eq_single q]
  · refine MulChar.ext fun a ↦ ?_
    rw [localFactor_apply_unit, changeLevel_eq_cast_of_dvd,
      ← ZMod.unitsMap_val (Nat.ordProj_dvd N q),
      isExactDivisor_primePow.unitsMap_unitsEquivProd_symm_of_dvd dvd_rfl, ZMod.unitsMap_self,
      MonoidHom.id_apply]
  · -- for `p ≠ q`, the lift of `(a, 1)` is `1` modulo `p ^ v_p(N)`
    intro p _ hpq
    refine MulChar.ext fun a ↦ ?_
    rw [localFactor_apply_unit, changeLevel_eq_cast_of_dvd,
      ← ZMod.unitsMap_val (Nat.ordProj_dvd N p),
      isExactDivisor_primePow.unitsMap_unitsEquivProd_symm_of_dvd_div
        (ordProj_dvd_ordCompl_of_ne (Nat.prime_of_mem_primeFactors hq) hpq), map_one,
      MulChar.one_apply_coe, Units.val_one, map_one]
  · exact fun h ↦ (h hq).elim

/-- **The conductor is the product of the local conductors**: for `N ≠ 0`, the conductor of `χ` is
the product over the primes `p ∣ N` of the conductors of its local factors. -/
theorem conductor_eq_prod_conductor_localFactor [NeZero N] (χ : DirichletCharacter R N) :
    χ.conductor = ∏ p ∈ N.primeFactors, (localFactor p χ).conductor := by
  conv_lhs => rw [← prod_changeLevel_localFactor χ]
  rw [conductor_prod_of_pairwise_coprime ?_ (Or.inr (NeZero.ne N))]
  · exact Finset.prod_congr rfl fun p _ ↦ conductor_changeLevel ..
  · intro p hp q hq hpq
    simp only [conductor_changeLevel]
    exact ((Nat.coprime_pow_primes _ _ (Nat.prime_of_mem_primeFactors hp)
      (Nat.prime_of_mem_primeFactors hq) hpq).coprime_dvd_left (conductor_dvd_level _))
        |>.coprime_dvd_right (conductor_dvd_level _)

/-- **The local conductor**: the conductor of the local factor of `χ` at `p` is `p ^ v_p(c)`, the
exact power of `p` dividing the conductor `c` of `χ`. -/
@[simp]
theorem conductor_localFactor (p : ℕ) (χ : DirichletCharacter R N) :
    (localFactor p χ).conductor = ordProj[p] χ.conductor := by
  by_cases hp : p ∈ N.primeFactors
  · -- the local conductor is a power of `p`, and the other local conductors are prime to `p`
    have : NeZero N := ⟨(Nat.mem_primeFactors.1 hp).2.2⟩
    have hpp := Nat.prime_of_mem_primeFactors hp
    obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow hpp).1 (conductor_dvd_level (localFactor p χ))
    rw [conductor_eq_prod_conductor_localFactor χ, Nat.factorization_prod_apply fun q _ ↦
      conductor_eq_zero_iff_level_eq_zero.not.2 (Nat.ordProj_pos N q).ne',
      Finset.sum_eq_single p, hi, hpp.factorization_pow, Finsupp.single_eq_same]
    · intro q hq hqp
      refine Nat.factorization_eq_zero_of_not_dvd fun hdvd ↦ hqp ?_
      exact (Nat.prime_eq_prime_of_dvd_pow hpp (Nat.prime_of_mem_primeFactors hq)
        (hdvd.trans (conductor_dvd_level _))).symm
    · exact fun h ↦ (h hp).elim
  · -- both `v_p(N)` and `v_p(c)` vanish, so both sides are `1`
    have hN : N.factorization p = 0 := by
      rwa [← Finsupp.notMem_support_iff, Nat.support_factorization]
    have hc : χ.conductor.factorization p = 0 := by
      rw [← Finsupp.notMem_support_iff, Nat.support_factorization]
      refine fun h ↦ hp (Nat.primeFactors_mono (conductor_dvd_level χ) ?_ h)
      exact conductor_eq_zero_iff_level_eq_zero.not.1 ((Nat.mem_primeFactors.1 h).2.2)
    rw [hc, pow_zero]
    simpa [hN] using conductor_dvd_level (localFactor p χ)

/-- The local factors of a quadratic character are quadratic. -/
theorem _root_.MulChar.IsQuadratic.localFactor {R : Type*} [CommRing R]
    {χ : DirichletCharacter R N} (hχ : χ.IsQuadratic) (p : ℕ) :
    (localFactor p χ).IsQuadratic := by
  intro a
  by_cases ha : IsUnit a
  · rw [← ha.unit_spec, localFactor_apply_unit]
    exact hχ _
  · exact Or.inl (MulChar.map_nonunit _ ha)

/-- For `N ≠ 0`, a Dirichlet character is quadratic exactly when all its local factors are. -/
theorem isQuadratic_iff_forall_isQuadratic_localFactor {R : Type*} [CommRing R] [NeZero N]
    {χ : DirichletCharacter R N} : χ.IsQuadratic ↔ ∀ p, (localFactor p χ).IsQuadratic :=
  ⟨fun hχ p ↦ hχ.localFactor p, fun h ↦ prod_changeLevel_localFactor χ ▸
    MulChar.isQuadratic_prod fun p _ ↦ (h p).changeLevel _⟩

end DirichletCharacter
