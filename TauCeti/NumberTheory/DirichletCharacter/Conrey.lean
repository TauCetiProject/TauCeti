/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.DirichletCharacter.Orthogonality
public import TauCeti.Analysis.Fourier.FiniteAbelian.PontryaginDuality
public import TauCeti.Data.ZMod.Divisibility
import TauCeti.Data.ZMod.OrderOf
import TauCeti.RingTheory.ZMod.UnitsTwoPow

/-!
# The Conrey labelling of Dirichlet characters

The group of Dirichlet characters modulo `N` is isomorphic to `(ℤ/N)ˣ`, but only noncanonically
(`DirichletCharacter.mulEquiv_units`). Conrey's labelling fixes an explicit isomorphism
`m ↦ χ_N(m, ·)`, which is how the LMFDB names Dirichlet characters, and through them the
nebentypus of a modular form. It is built from an explicit pairing on each prime-power factor of
`(ℤ/N)ˣ`, written with `e(x) = exp(2 π i x)`:

* for an odd prime `p`, let `g_p` be the least positive integer that is a primitive root
  modulo every power of `p` (`TauCeti.conreyGenerator`); for `m ≡ g_p ^ a` and `n ≡ g_p ^ b`
  modulo `p ^ e`, `χ_{p ^ e}(m, n) = e(a b / φ(p ^ e))`;
* modulo `2` the factor is trivial, and for `m ≡ (-1) ^ x 5 ^ a` and `n ≡ (-1) ^ y 5 ^ b`
  modulo `2 ^ (e + 2)`,
  `χ_{2 ^ (e + 2)}(m, n) = e(x y / 2 + a b / 2 ^ e)`, so that `χ_4(-1, -1) = -1`;

and `χ_N(m, n)` is the product of `χ_{p ^ v}(m, n)` over the prime powers `p ^ v` exactly dividing
`N`. Each factor is a symmetric pairing that is multiplicative in each variable and
nondegenerate, so `m ↦ χ_N(m, ·)` is an injective homomorphism from `(ℤ/N)ˣ` to the Dirichlet
characters modulo `N`, and an isomorphism because both groups have `φ(N)` elements. The label of
a character `χ` is `(conreyCharacter N).symm χ`.

## Main definitions

* `TauCeti.conreyGenerator p`: the least natural number that is a primitive root modulo `p ²`.
* `TauCeti.conreyLocal p e`: the pairing `χ_{p ^ e}` on `(ℤ/p ^ e)ˣ`, with values in the unit
  circle.
* `TauCeti.conreyPairing N`: the pairing `χ_N(m, n)` on `(ℤ/N)ˣ`.
* `TauCeti.conreyCharacter N`: the Conrey labelling `(ℤ/N)ˣ ≃* DirichletCharacter ℂ N`,
  `m ↦ χ_N(m, ·)`.

## Main results

* `TauCeti.orderOf_conreyGenerator`, `TauCeti.conreyGenerator_le`: for an odd prime `p`, the
  Conrey generator is a primitive root modulo every power of `p`, and it is the least natural
  number that is a primitive root modulo `p ²`; for instance `g_3 = 2`
  (`TauCeti.conreyGenerator_three`).
* `TauCeti.conreyLocal_apply_of_eq_pow`, `TauCeti.conreyLocal_two_apply`: the explicit values of
  the prime-power pairings.
* `TauCeti.conreyPairing_apply`: `χ_N` is the product of the prime-power pairings.
* `TauCeti.conreyCharacter_apply`: `χ_N(m, ·)` evaluates to `χ_N(m, n)` on a unit `n`.
* `TauCeti.conreyCharacter_comm`: the symmetry `χ_N(m, n) = χ_N(n, m)`.

## References

* B. Conrey, as described by the LMFDB Collaboration, *Conrey labels for Dirichlet characters*,
  <https://www.lmfdb.org/knowledge/show/character.dirichlet.conrey>.
-/

public section

open Multiplicative Complex

open scoped Real

namespace TauCeti

/-! ### The Conrey generator -/

open scoped Classical in
/-- **The Conrey generator** of an odd prime `p`: the least natural number that is a primitive
root modulo `p ²`. It is then a primitive root modulo every power of `p`
(`TauCeti.orderOf_conreyGenerator`), so it is also the least natural number that is a primitive
root modulo every power of `p`. The value for other `p` carries no meaning. -/
noncomputable def conreyGenerator (p : ℕ) : ℕ :=
  if h : ∃ g : ℕ, orderOf (g : ZMod (p ^ 2)) = (p ^ 2).totient then Nat.find h else 0

private theorem orderOf_conreyGenerator_sq {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    orderOf (conreyGenerator p : ZMod (p ^ 2)) = (p ^ 2).totient := by
  have : NeZero (p ^ 2) := ⟨pow_ne_zero 2 hp.ne_zero⟩
  have := ZMod.isCyclic_units_of_prime_pow p hp hp2 2
  have h := ZMod.exists_orderOf_natCast_eq_totient (n := p ^ 2)
  rw [conreyGenerator, dite_eq_left h]
  exact Nat.find_spec h

/-- **The Conrey generator is a primitive root modulo every power of `p`**, for an odd prime
`p`. -/
theorem orderOf_conreyGenerator {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (e : ℕ) :
    orderOf (conreyGenerator p : ZMod (p ^ e)) = (p ^ e).totient :=
  ZMod.orderOf_natCast_prime_pow_eq_totient hp hp2 (orderOf_conreyGenerator_sq hp hp2) e

/-- The Conrey generator is the least natural number that is a primitive root modulo `p ²`. -/
theorem conreyGenerator_le {p g : ℕ} (hg : orderOf (g : ZMod (p ^ 2)) = (p ^ 2).totient) :
    conreyGenerator p ≤ g := by
  have h : ∃ g : ℕ, orderOf (g : ZMod (p ^ 2)) = (p ^ 2).totient := ⟨g, hg⟩
  rw [conreyGenerator, dite_eq_left h]
  exact Nat.find_min' h hg

/-- The Conrey generator of `3` is `2`. -/
theorem conreyGenerator_three : conreyGenerator 3 = 2 := by
  have htot : (3 ^ 2).totient = 6 := by decide
  have h2 : orderOf ((2 : ℕ) : ZMod (3 ^ 2)) = (3 ^ 2).totient := by
    rw [htot, orderOf_eq_iff (by norm_num)]
    refine ⟨by decide, fun m hm hm0 ↦ ?_⟩
    interval_cases m <;> decide
  refine le_antisymm (conreyGenerator_le h2) ?_
  have h := orderOf_conreyGenerator Nat.prime_three (by norm_num) 2
  rw [htot] at h
  -- Neither `0` nor `1` has order `6` modulo `9`.
  by_contra hlt
  interval_cases hg : conreyGenerator 3
  · rw [Nat.cast_zero, orderOf_eq_zero_iff'.mpr fun n hn ↦ by rw [zero_pow hn.ne']; decide] at h
    exact absurd h (by norm_num)
  · rw [Nat.cast_one, orderOf_one] at h
    exact absurd h (by norm_num)

private theorem coprime_conreyGenerator {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (e : ℕ) :
    Nat.Coprime (conreyGenerator p) (p ^ e) := by
  have : NeZero (p ^ e) := ⟨pow_ne_zero e hp.ne_zero⟩
  exact (ZMod.isUnit_iff_coprime _ _).mp
    (ZMod.isUnit_of_orderOf_eq_totient (orderOf_conreyGenerator hp hp2 e))

/-! ### The prime-power pairings -/

private theorem conreyGenerator_mem_zpowers {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (e : ℕ)
    (u : (ZMod (p ^ e))ˣ) :
    u ∈ Subgroup.zpowers (ZMod.unitOfCoprime _ (coprime_conreyGenerator hp hp2 e)) := by
  have : NeZero (p ^ e) := ⟨pow_ne_zero e hp.ne_zero⟩
  refine (Subgroup.eq_top_iff' _).mp (ZMod.zpowers_eq_top_of_orderOf_eq_totient ?_) u
  rw [← orderOf_units, ZMod.coe_unitOfCoprime, orderOf_conreyGenerator hp hp2]

/-- The discrete logarithm to the base of the Conrey generator modulo `p ^ e`. -/
private noncomputable def conreyLog {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (e : ℕ) :
    (ZMod (p ^ e))ˣ ≃* Multiplicative (ZMod (p ^ e).totient) :=
  have : NeZero (p ^ e) := ⟨pow_ne_zero e hp.ne_zero⟩
  (zmodMulEquivOfGenerator (conreyGenerator_mem_zpowers hp hp2 e)
    (by rw [Nat.card_eq_fintype_card, ZMod.card_units_eq_totient])).symm

private theorem conreyLog_pow {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (e a : ℕ) :
    conreyLog hp hp2 e (ZMod.unitOfCoprime _ (coprime_conreyGenerator hp hp2 e) ^ a) =
      ofAdd (a : ZMod (p ^ e).totient) := by
  rw [conreyLog, ← zpow_natCast, zmodMulEquivOfGenerator_symm_apply_zpow, Int.cast_natCast]

private instance {p : ℕ} [hp : Fact p.Prime] (e : ℕ) : NeZero (p ^ e).totient :=
  ⟨(Nat.totient_pos.mpr (pow_pos hp.out.pos e)).ne'⟩

/-- The Conrey pairing modulo `p ^ e`, for an odd prime `p`. -/
private noncomputable def conreyOdd {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (e : ℕ) :
    (ZMod (p ^ e))ˣ →* (ZMod (p ^ e))ˣ →* Circle :=
  have : Fact p.Prime := ⟨hp⟩
  ((zmodPairing _).compl₂ (conreyLog hp hp2 e).toMonoidHom).comp (conreyLog hp hp2 e).toMonoidHom

/-- The Conrey pairing modulo `2 ^ v`. -/
private noncomputable def conreyTwoPow : (v : ℕ) → (ZMod (2 ^ v))ˣ →* (ZMod (2 ^ v))ˣ →* Circle
  | 0 | 1 => 1
  | e + 2 =>
    let x := (AddMonoidHom.fst _ _).toMultiplicative.comp (ZMod.unitsTwoPowEquiv e).toMonoidHom
    let a := (AddMonoidHom.snd _ _).toMultiplicative.comp (ZMod.unitsTwoPowEquiv e).toMonoidHom
    ((zmodPairing 2).compl₂ x).comp x * ((zmodPairing (2 ^ e)).compl₂ a).comp a

private theorem conreyTwoPow_add_two_apply (e : ℕ) (m n : (ZMod (2 ^ (e + 2)))ˣ) :
    conreyTwoPow (e + 2) m n =
      zmodPairing 2 (ofAdd (ZMod.unitsTwoPowEquiv e m).toAdd.1)
          (ofAdd (ZMod.unitsTwoPowEquiv e n).toAdd.1) *
        zmodPairing (2 ^ e) (ofAdd (ZMod.unitsTwoPowEquiv e m).toAdd.2)
          (ofAdd (ZMod.unitsTwoPowEquiv e n).toAdd.2) := by
  simp [conreyTwoPow]

private theorem conreyTwoPow_of_le_one {v : ℕ} (hv : v ≤ 1) : conreyTwoPow v = 1 := by
  interval_cases v <;> simp [conreyTwoPow]

/-- **The Conrey pairing modulo the prime power `p ^ e`**, with values in the unit circle.

For an odd prime `p`, it is `e(a b / φ(p ^ e))` on `g_p ^ a` and `g_p ^ b`, where `g_p` is the
Conrey generator (`TauCeti.conreyLocal_apply_of_eq_pow`). Modulo `2 ^ (e + 2)` it is
`e(x y / 2 + a b / 2 ^ e)` on `(-1) ^ x 5 ^ a` and `(-1) ^ y 5 ^ b`
(`TauCeti.conreyLocal_two_apply`), and modulo `1` and `2` it is trivial. The value for other `p`
carries no meaning. -/
noncomputable def conreyLocal (p e : ℕ) : (ZMod (p ^ e))ˣ →* (ZMod (p ^ e))ˣ →* Circle :=
  if h2 : p = 2 then h2 ▸ conreyTwoPow e else if hp : p.Prime then conreyOdd hp h2 e else 1

private theorem conreyLocal_of_ne_two {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (e : ℕ) :
    conreyLocal p e = conreyOdd hp hp2 e := by
  rw [conreyLocal, dite_eq_right hp2, dite_eq_left hp]

private theorem conreyLocal_two (e : ℕ) : conreyLocal 2 e = conreyTwoPow e := by
  rw [conreyLocal, dite_eq_left rfl]

/-- **The Conrey pairing modulo an odd prime power**: if `m ≡ g_p ^ a` and `n ≡ g_p ^ b` modulo
`p ^ e`, where `g_p` is the Conrey generator, then `χ_{p ^ e}(m, n) = e(a b / φ(p ^ e))`. -/
theorem conreyLocal_apply_of_eq_pow {p e : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {m n : (ZMod (p ^ e))ˣ} {a b : ℕ}
    (hm : (m : ZMod (p ^ e)) = (conreyGenerator p : ZMod (p ^ e)) ^ a)
    (hn : (n : ZMod (p ^ e)) = (conreyGenerator p : ZMod (p ^ e)) ^ b) :
    (conreyLocal p e m n : ℂ) = exp (2 * π * I * (a * b) / (p ^ e).totient) := by
  have : Fact p.Prime := ⟨hp⟩
  have hm' : m = ZMod.unitOfCoprime _ (coprime_conreyGenerator hp hp2 e) ^ a :=
    Units.ext (by simpa using hm)
  have hn' : n = ZMod.unitOfCoprime _ (coprime_conreyGenerator hp hp2 e) ^ b :=
    Units.ext (by simpa using hn)
  rw [conreyLocal_of_ne_two hp hp2, conreyOdd, MonoidHom.comp_apply,
    MonoidHom.compl₂_apply, hm', hn']
  simp [conreyLog_pow, zmodPairing_apply, ← Nat.cast_mul, ZMod.toCircle_natCast]

/-- **The Conrey pairing modulo `2 ^ (e + 2)`**: if `m ≡ (-1) ^ x 5 ^ a` and `n ≡ (-1) ^ y 5 ^ b`
modulo `2 ^ (e + 2)`, then `χ_{2 ^ (e + 2)}(m, n) = e(x y / 2) e(a b / 2 ^ e)`. -/
theorem conreyLocal_two_apply {e : ℕ} {m n : (ZMod (2 ^ (e + 2)))ˣ} {x y a b : ℕ}
    (hm : (m : ZMod (2 ^ (e + 2))) = (-1) ^ x * 5 ^ a)
    (hn : (n : ZMod (2 ^ (e + 2))) = (-1) ^ y * 5 ^ b) :
    (conreyLocal 2 (e + 2) m n : ℂ) =
      exp (2 * π * I * (x * y) / 2) * exp (2 * π * I * (a * b) / 2 ^ e) := by
  have hm' : ZMod.unitsTwoPowEquiv e m = ofAdd ((x : ZMod 2), (a : ZMod (2 ^ e))) := by
    rw [← MulEquiv.eq_symm_apply, ZMod.unitsTwoPowEquiv_symm_ofAdd_natCast]
    exact Units.ext (by simp [hm])
  have hn' : ZMod.unitsTwoPowEquiv e n = ofAdd ((y : ZMod 2), (b : ZMod (2 ^ e))) := by
    rw [← MulEquiv.eq_symm_apply, ZMod.unitsTwoPowEquiv_symm_ofAdd_natCast]
    exact Units.ext (by simp [hn])
  rw [conreyLocal_two, conreyTwoPow_add_two_apply, hm', hn']
  simp [zmodPairing_apply, ← Nat.cast_mul, ZMod.toCircle_natCast]

/-- Modulo `1` and `2` the Conrey pairing is trivial. -/
theorem conreyLocal_two_of_le_one {v : ℕ} (hv : v ≤ 1) : conreyLocal 2 v = 1 := by
  rw [conreyLocal_two, conreyTwoPow_of_le_one hv]

/-- The Conrey pairing modulo a prime power is symmetric. -/
theorem conreyLocal_comm (p e : ℕ) (m n : (ZMod (p ^ e))ˣ) :
    conreyLocal p e m n = conreyLocal p e n m := by
  by_cases h2 : p = 2
  · subst h2
    rw [conreyLocal_two]
    obtain he | ⟨e, rfl⟩ : e ≤ 1 ∨ ∃ e', e = e' + 2 :=
      (le_or_gt e 1).imp_right fun h ↦ ⟨e - 2, by omega⟩
    · simp [conreyTwoPow_of_le_one he]
    · rw [conreyTwoPow_add_two_apply, conreyTwoPow_add_two_apply, zmodPairing_comm 2,
        zmodPairing_comm (2 ^ e)]
  by_cases hp : p.Prime
  · have : Fact p.Prime := ⟨hp⟩
    rw [conreyLocal_of_ne_two hp h2, conreyOdd, MonoidHom.comp_apply, MonoidHom.compl₂_apply,
      MonoidHom.comp_apply, MonoidHom.compl₂_apply, zmodPairing_comm]
  · simp [conreyLocal, h2, hp]

/-- The Conrey pairing modulo a prime power is nondegenerate: only `m = 1` pairs trivially with
every unit. -/
@[simp]
theorem conreyLocal_eq_one_iff {p e : ℕ} (hp : p.Prime) (m : (ZMod (p ^ e))ˣ) :
    conreyLocal p e m = 1 ↔ m = 1 := by
  refine ⟨fun h ↦ ?_, fun h ↦ h ▸ map_one _⟩
  by_cases h2 : p = 2
  · subst h2
    rw [conreyLocal_two] at h
    obtain he | ⟨e, rfl⟩ : e ≤ 1 ∨ ∃ e', e = e' + 2 :=
      (le_or_gt e 1).imp_right fun h ↦ ⟨e - 2, by omega⟩
    · -- There is only one unit modulo `1` and modulo `2`.
      have : Subsingleton (ZMod (2 ^ e))ˣ := Fintype.card_le_one_iff_subsingleton.mp <| by
        rw [ZMod.card_units_eq_totient]
        interval_cases e <;> decide
      exact Subsingleton.elim _ _
    · -- Pair `m` with `-1` and with `5`, whose coordinates are `(1, 0)` and `(0, 1)`.
      have h1 := DFunLike.congr_fun h (-1)
      have h5 := DFunLike.congr_fun h (ZMod.unitsTwoPowFive e)
      simp only [conreyTwoPow_add_two_apply, ZMod.unitsTwoPowEquiv_neg_one, toAdd_ofAdd,
        ofAdd_zero, map_one, mul_one, MonoidHom.one_apply] at h1
      simp only [conreyTwoPow_add_two_apply, ZMod.unitsTwoPowEquiv_five, toAdd_ofAdd, ofAdd_zero,
        map_one, one_mul, MonoidHom.one_apply] at h5
      rw [zmodPairing_eq_one_iff, ofAdd_eq_one] at h1 h5
      apply (ZMod.unitsTwoPowEquiv e).injective
      rw [map_one, ← toAdd_eq_zero]
      exact Prod.ext h1 h5
  · have : Fact p.Prime := ⟨hp⟩
    rw [conreyLocal_of_ne_two hp h2] at h
    -- Pair `m` with the Conrey generator, whose logarithm is `1`.
    have := DFunLike.congr_fun h (ZMod.unitOfCoprime _ (coprime_conreyGenerator hp h2 e) ^ 1)
    rw [conreyOdd, MonoidHom.comp_apply, MonoidHom.compl₂_apply, MulEquiv.coe_toMonoidHom,
      conreyLog_pow] at this
    simpa [zmodPairing_eq_one_iff] using this

/-! ### The Conrey pairing and the Conrey labelling -/

/-- **The Conrey pairing modulo `N`**: `χ_N(m, n)` is the product, over the prime powers `p ^ v`
exactly dividing `N`, of the prime-power pairings `TauCeti.conreyLocal p v` of the reductions of
`m` and `n` modulo `p ^ v` (`TauCeti.conreyPairing_apply`). -/
noncomputable def conreyPairing (N : ℕ) : (ZMod N)ˣ →* (ZMod N)ˣ →* Circle :=
  ∏ p : N.primeFactors, ((conreyLocal p (N.factorization p)).compl₂
    (ZMod.unitsMap (Nat.ordProj_dvd N p))).comp (ZMod.unitsMap (Nat.ordProj_dvd N p))

/-- `χ_N(m, n)` is the product of the prime-power pairings of the reductions of `m` and `n`. -/
theorem conreyPairing_apply (N : ℕ) (m n : (ZMod N)ˣ) :
    conreyPairing N m n = ∏ p : N.primeFactors, conreyLocal p (N.factorization p)
      (ZMod.unitsMap (Nat.ordProj_dvd N p) m) (ZMod.unitsMap (Nat.ordProj_dvd N p) n) := by
  simp [conreyPairing]

/-- The Conrey pairing is symmetric: `χ_N(m, n) = χ_N(n, m)`. -/
theorem conreyPairing_comm (N : ℕ) (m n : (ZMod N)ˣ) :
    conreyPairing N m n = conreyPairing N n m := by
  simp only [conreyPairing_apply, conreyLocal_comm _ _ (ZMod.unitsMap _ m)]

/-- The Conrey pairing is nondegenerate: only `m = 1` pairs trivially with every unit. -/
@[simp]
theorem conreyPairing_eq_one_iff {N : ℕ} [NeZero N] (m : (ZMod N)ˣ) :
    conreyPairing N m = 1 ↔ m = 1 := by
  refine ⟨fun h ↦ ?_, fun h ↦ h ▸ map_one _⟩
  have hN := NeZero.ne N
  apply (ZMod.unitsEquivPi hN).injective
  ext1 p
  rw [map_one, Pi.one_apply, ZMod.unitsEquivPi_apply,
    ← conreyLocal_eq_one_iff (Nat.prime_of_mem_primeFactors p.2)]
  ext u : 1
  -- Pair `m` with the unit that is `u` modulo `p ^ v` and `1` modulo the other prime powers.
  let v : Π q : N.primeFactors, (ZMod (q ^ N.factorization q))ˣ := Pi.mulSingle p u
  have hu := DFunLike.congr_fun h ((ZMod.unitsEquivPi hN).symm v)
  rw [conreyPairing_apply, MonoidHom.one_apply, Fintype.prod_eq_single p] at hu
  · simpa [v] using hu
  · intro q hq
    simp [v, Pi.mulSingle_eq_of_ne hq]

/-- `m ↦ χ_N(m, ·)`, as a homomorphism to the Dirichlet characters. -/
private noncomputable def conreyHom (N : ℕ) : (ZMod N)ˣ →* DirichletCharacter ℂ N :=
  MulChar.mulEquivToUnitHom.symm.toMonoidHom.comp ((conreyPairing N).compr₂ Circle.toUnits)

private theorem conreyHom_apply (N : ℕ) (m n : (ZMod N)ˣ) :
    conreyHom N m n = conreyPairing N m n := by
  simp [conreyHom]

private theorem conreyHom_bijective (N : ℕ) [NeZero N] : Function.Bijective (conreyHom N) := by
  refine (Fintype.bijective_iff_injective_and_card _).mpr
    ⟨(injective_iff_map_eq_one _).mpr fun m hm ↦ ?_, by
      rw [ZMod.card_units_eq_totient, ← Nat.card_eq_fintype_card,
        DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity]⟩
  rw [← conreyPairing_eq_one_iff]
  ext n : 1
  have := congrArg (fun χ : DirichletCharacter ℂ N ↦ χ n) hm
  rw [conreyHom_apply, MulChar.one_apply_coe] at this
  rw [MonoidHom.one_apply, ← Circle.coe_eq_one]
  exact this

/-- **The Conrey labelling** of the Dirichlet characters modulo `N`: the isomorphism
`(ℤ/N)ˣ ≃* DirichletCharacter ℂ N` sending `m` to the character `χ_N(m, ·)` whose value at a unit
`n` is the Conrey pairing `χ_N(m, n)` (`TauCeti.conreyCharacter_apply`). The Conrey label of a
character `χ` is `(conreyCharacter N).symm χ`. -/
noncomputable def conreyCharacter (N : ℕ) [NeZero N] : (ZMod N)ˣ ≃* DirichletCharacter ℂ N :=
  MulEquiv.ofBijective (conreyHom N) (conreyHom_bijective N)

/-- The Conrey character `χ_N(m, ·)` takes the value `χ_N(m, n)` at a unit `n`. -/
@[simp]
theorem conreyCharacter_apply (N : ℕ) [NeZero N] (m n : (ZMod N)ˣ) :
    conreyCharacter N m n = conreyPairing N m n :=
  conreyHom_apply N m n

/-- **Conrey symmetry**: `χ_N(m, n) = χ_N(n, m)`. -/
theorem conreyCharacter_comm (N : ℕ) [NeZero N] (m n : (ZMod N)ˣ) :
    conreyCharacter N m n = conreyCharacter N n m := by
  rw [conreyCharacter_apply, conreyCharacter_apply, conreyPairing_comm]

end TauCeti
