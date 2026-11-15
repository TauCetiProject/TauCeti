/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Order.PiLex
public import Mathlib.RingTheory.AdicCompletion.LocalRing
public import Mathlib.RingTheory.Length
public import Mathlib.RingTheory.LocalRing.Length
public import TauCeti.RingTheory.Ideal.Order
import Mathlib.Algebra.QuadraticAlgebra.NormDeterminant
import TauCeti.RingTheory.AdicCompletion.Algebra
import TauCeti.RingTheory.Length

/-!
# The Hilbert–Samuel function of a local quotient ring

For a local commutative ring `(A, 𝔪)` and an ideal `I : Ideal A`, the Hilbert–Samuel function
`TauCeti.localQuotientHilbertSamuel A I : ℕ → ℕ∞` sends `n` to the `A`-module length of
`A ⧸ (I ⊔ 𝔪 ^ (n + 1))`. When `I = ⊥` this is the local Hilbert–Samuel function
`n ↦ length_A (A ⧸ 𝔪 ^ (n + 1))` of `A`; when `I` is a proper ideal, it agrees with the local
Hilbert–Samuel function of the quotient local ring `A ⧸ I`; when `I = ⊤`, the quotient is zero and
every value is `0`.

Measuring by `Module.length A` rather than dimension over a ground field `k` normalizes away the
residue degree `[κ(A) : k]` (`TauCeti.finrank_quotient_sup_maximalIdeal_pow`): in particular, a
field extension of `ℚ` of degree two has `localQuotientHilbertSamuel L ⊥ 0 = 1` despite having
`ℚ`-dimension `2`.

Over a Noetherian local ring `A`, every value `localQuotientHilbertSamuel A I n` is finite
(`TauCeti.localQuotientHilbertSamuel_lt_top`), recovers `I.localOrder` as the threshold where
`localQuotientHilbertSamuel A I` first drops below `localQuotientHilbertSamuel A ⊥`
(`TauCeti.localQuotientHilbertSamuel_eq_bot_iff`), and detects equality along ideal inclusions
(`TauCeti.eq_of_le_of_localQuotientHilbertSamuel_eq`). Whenever `𝔪` is finitely generated (in
particular for Noetherian `A`), passing to the maximal-adic completion `AdicCompletion 𝔪 A` and
extending `I` preserves every value (`TauCeti.localQuotientHilbertSamuel_adicCompletion`).

## Main definitions

* `TauCeti.localQuotientHilbertSamuel`: `n ↦ Module.length A (A ⧸ (I ⊔ maximalIdeal A ^ (n + 1)))`.

## Main results

* `TauCeti.localQuotientHilbertSamuel_eq_zero_iff`,
  `TauCeti.localQuotientHilbertSamuel_zero_of_ne_top`: vanishing characterizes the unit ideal, and
  every proper ideal has value `1` at `0`.
* `TauCeti.localQuotientHilbertSamuel_anti`, `TauCeti.toLex_localQuotientHilbertSamuel_anti`,
  `TauCeti.localQuotientHilbertSamuel_mono`: ideal antitonicity in both the pointwise and
  lexicographic orders, and degree monotonicity.
* `TauCeti.localQuotientHilbertSamuel_map_of_surjective`,
  `TauCeti.localQuotientHilbertSamuel_quotient_bot`,
  `TauCeti.localQuotientHilbertSamuel_map_equiv`: transport along surjective local homomorphisms,
  quotient local rings, and ring equivalences.
* `TauCeti.localQuotientHilbertSamuel_lt_top`,
  `TauCeti.natCast_toNat_localQuotientHilbertSamuel`: finiteness and natural-number identification
  over Noetherian local rings.
* `TauCeti.localQuotientHilbertSamuel_eq_bot_iff`,
  `TauCeti.eq_of_le_of_localQuotientHilbertSamuel_eq`: recovery of `Ideal.localOrder` and rigidity
  along ideal inclusions over Noetherian local rings.
* `TauCeti.localQuotientHilbertSamuel_adicCompletion_of_fg`,
  `TauCeti.localQuotientHilbertSamuel_adicCompletion`: invariance under maximal-adic completion.

## References

* Edward Bierstone and Pierre D. Milman, *Canonical desingularization in characteristic zero by
  blowing up the maximum strata of a local invariant*, Invent. Math. 128 (1997), 207–302,
  Remarks 1.3 and 1.8, pp. 213–216; Corollary 3.20, p. 239; Theorem 9.2, p. 276.
-/

public section

namespace TauCeti

open IsLocalRing

section Basic

variable (A : Type*) [CommRing A] [IsLocalRing A]

/-- The Hilbert–Samuel function of `A ⧸ I` over a local ring `A`, sending `n` to the `A`-module
length of `A ⧸ (I ⊔ maximalIdeal A ^ (n + 1))`. -/
noncomputable def localQuotientHilbertSamuel (I : Ideal A) (n : ℕ) : ℕ∞ :=
  Module.length A (A ⧸ (I ⊔ maximalIdeal A ^ (n + 1)))

/-- Defining formula for `TauCeti.localQuotientHilbertSamuel`. -/
theorem localQuotientHilbertSamuel_def (I : Ideal A) (n : ℕ) :
    localQuotientHilbertSamuel A I n =
      Module.length A (A ⧸ (I ⊔ maximalIdeal A ^ (n + 1))) := (rfl)

/-- For `I = ⊥`, `localQuotientHilbertSamuel A ⊥ n` is the length of `A ⧸ 𝔪 ^ (n + 1)`. -/
theorem localQuotientHilbertSamuel_bot_def (n : ℕ) :
    localQuotientHilbertSamuel A ⊥ n = Module.length A (A ⧸ maximalIdeal A ^ (n + 1)) := by
  rw [localQuotientHilbertSamuel_def, bot_sup_eq]

/-- The unit ideal has Hilbert–Samuel value `0` in every degree. -/
@[simp]
theorem localQuotientHilbertSamuel_top (n : ℕ) :
    localQuotientHilbertSamuel A ⊤ n = 0 := by
  rw [localQuotientHilbertSamuel_def, top_sup_eq]
  exact Module.length_eq_zero_iff.mpr inferInstance

variable {A}

/-- A degree-`n` Hilbert–Samuel value vanishes if and only if `I = ⊤`. -/
@[simp]
theorem localQuotientHilbertSamuel_eq_zero_iff {I : Ideal A} {n : ℕ} :
    localQuotientHilbertSamuel A I n = 0 ↔ I = ⊤ := by
  rw [localQuotientHilbertSamuel_def, Module.length_eq_zero_iff, Ideal.Quotient.subsingleton_iff]
  refine ⟨fun h ↦ by_contra fun hI ↦ (maximalIdeal.isMaximal A).ne_top (top_unique <|
    h ▸ sup_le (le_maximalIdeal hI) (Ideal.pow_le_self n.succ_ne_zero)), fun h ↦ by simp [h]⟩

/-- A degree-`n` Hilbert–Samuel value is positive if and only if `I` is a proper ideal. -/
theorem localQuotientHilbertSamuel_pos_iff {I : Ideal A} {n : ℕ} :
    0 < localQuotientHilbertSamuel A I n ↔ I ≠ ⊤ :=
  pos_iff_ne_zero.trans localQuotientHilbertSamuel_eq_zero_iff.not

/-- Every proper ideal has Hilbert–Samuel value `1` at degree `0`. -/
theorem localQuotientHilbertSamuel_zero_of_ne_top {I : Ideal A} (hI : I ≠ ⊤) :
    localQuotientHilbertSamuel A I 0 = 1 := by
  rw [localQuotientHilbertSamuel_def, zero_add, pow_one,
    sup_eq_right.mpr (le_maximalIdeal hI), Ideal.length_quotient_eq_one]

@[simp]
theorem localQuotientHilbertSamuel_bot_zero :
    localQuotientHilbertSamuel A ⊥ 0 = 1 :=
  localQuotientHilbertSamuel_zero_of_ne_top bot_ne_top

/-- At degree `0`, `localQuotientHilbertSamuel A I 0` is `0` for `I = ⊤` and `1` otherwise. -/
theorem localQuotientHilbertSamuel_zero (I : Ideal A) [Decidable (I = ⊤)] :
    localQuotientHilbertSamuel A I 0 = if I = ⊤ then 0 else 1 := by
  split_ifs with hI
  · simp [hI]
  · exact localQuotientHilbertSamuel_zero_of_ne_top hI

/-- Inclusion of ideals reverses their Hilbert–Samuel functions at every degree. -/
theorem localQuotientHilbertSamuel_anti {I J : Ideal A} (h : I ≤ J) (n : ℕ) :
    localQuotientHilbertSamuel A J n ≤ localQuotientHilbertSamuel A I n :=
  length_quotient_anti (sup_le_sup_right h _)

/-- Inclusion of ideals reverses their Hilbert–Samuel functions in the lexicographic order. -/
theorem toLex_localQuotientHilbertSamuel_anti {I J : Ideal A} (h : I ≤ J) :
    toLex (localQuotientHilbertSamuel A J) ≤ toLex (localQuotientHilbertSamuel A I) :=
  Pi.toLex_monotone (localQuotientHilbertSamuel_anti h)

/-- Every ideal's Hilbert–Samuel function is bounded above by that of `⊥`. -/
theorem localQuotientHilbertSamuel_le_bot (I : Ideal A) (n : ℕ) :
    localQuotientHilbertSamuel A I n ≤ localQuotientHilbertSamuel A ⊥ n :=
  localQuotientHilbertSamuel_anti bot_le n

/-- For a fixed ideal `I`, `localQuotientHilbertSamuel A I` is monotone in the degree `n`. -/
theorem localQuotientHilbertSamuel_mono (I : Ideal A) :
    Monotone (localQuotientHilbertSamuel A I) :=
  fun _ _ hmn ↦ length_quotient_anti
    (sup_le_sup_left (Ideal.pow_le_pow_right (Nat.succ_le_succ hmn)) I)

/-- Every proper ideal has Hilbert–Samuel values at least `1` in all degrees. -/
theorem one_le_localQuotientHilbertSamuel_of_ne_top {I : Ideal A} (hI : I ≠ ⊤) (n : ℕ) :
    1 ≤ localQuotientHilbertSamuel A I n := by
  rw [← localQuotientHilbertSamuel_zero_of_ne_top hI]
  exact localQuotientHilbertSamuel_mono I (Nat.zero_le n)

/-- If `(n + 1 : ℕ∞) ≤ I.localOrder`, then `I` lies in `𝔪 ^ (n + 1)` and so does not affect the
degree-`n` Hilbert–Samuel value. -/
theorem localQuotientHilbertSamuel_eq_bot_of_le_localOrder {I : Ideal A} {n : ℕ}
    (h : ((n + 1 : ℕ) : ℕ∞) ≤ I.localOrder) :
    localQuotientHilbertSamuel A I n = localQuotientHilbertSamuel A ⊥ n := by
  have hle : I ≤ maximalIdeal A ^ (n + 1) := (I.natCast_le_localOrder_iff (n + 1)).mp h
  rw [localQuotientHilbertSamuel_def, localQuotientHilbertSamuel_bot_def, sup_eq_right.mpr hle]

/-- Over a field `K`, the Hilbert–Samuel function of the zero ideal is identically `1`. -/
@[simp]
theorem localQuotientHilbertSamuel_bot_of_field (K : Type*) [Field K] (n : ℕ) :
    localQuotientHilbertSamuel K ⊥ n = 1 := by
  have hbot : (maximalIdeal K) ^ (n + 1) = ⊥ :=
    le_antisymm ((Ideal.pow_le_self (Nat.succ_ne_zero n)).trans (maximalIdeal_eq_bot.le)) bot_le
  rw [localQuotientHilbertSamuel_bot_def, hbot, Ideal.length_quotient_eq_one]

/-- For a local `k`-algebra `A`, the `k`-dimension of `A ⧸ (I ⊔ 𝔪 ^ (n + 1))` equals the local
Hilbert–Samuel value multiplied by the residue degree `[κ(A) : k]`. -/
theorem finrank_quotient_sup_maximalIdeal_pow (k : Type*) [Field k] [Algebra k A]
    (I : Ideal A) (n : ℕ) :
    Module.finrank k (A ⧸ (I ⊔ maximalIdeal A ^ (n + 1))) =
      (localQuotientHilbertSamuel A I n).toNat * Module.finrank k (ResidueField A) :=
  finrank_eq_length_mul_finrank_residueField k A (A ⧸ (I ⊔ maximalIdeal A ^ (n + 1)))

end Basic

section Transport

variable {A B : Type*} [CommRing A] [IsLocalRing A] [CommRing B] [IsLocalRing B]

/-- Along a surjective homomorphism `f` of local rings, the Hilbert–Samuel function of `I.map f` in
`B` agrees with that of `I ⊔ ker f` in `A`. -/
theorem localQuotientHilbertSamuel_map_of_surjective {F : Type*} [FunLike F A B]
    [RingHomClass F A B] {f : F} (hf : Function.Surjective f) (I : Ideal A) (n : ℕ) :
    localQuotientHilbertSamuel B (I.map f) n =
      localQuotientHilbertSamuel A (I ⊔ RingHom.ker f) n := by
  have hmax : (maximalIdeal A).map f = maximalIdeal B :=
    map_maximalIdeal_of_surjective (f : A →+* B) hf
  rw [localQuotientHilbertSamuel_def, ← hmax, ← Ideal.map_pow,
    ← Ideal.map_sup, Ideal.length_quotient_map_of_surjective _ hf, localQuotientHilbertSamuel_def,
    sup_right_comm]

@[simp]
theorem localQuotientHilbertSamuel_quotient_map {I : Ideal A} [IsLocalRing (A ⧸ I)]
    (J : Ideal A) (n : ℕ) :
    localQuotientHilbertSamuel (A ⧸ I) (J.map (Ideal.Quotient.mk I)) n =
      localQuotientHilbertSamuel A (J ⊔ I) n := by
  rw [localQuotientHilbertSamuel_map_of_surjective Ideal.Quotient.mk_surjective, Ideal.mk_ker]

/-- The local Hilbert–Samuel function of a proper quotient `A ⧸ I` agrees with
`localQuotientHilbertSamuel A I`. -/
@[simp]
theorem localQuotientHilbertSamuel_quotient_bot {I : Ideal A} [IsLocalRing (A ⧸ I)] (n : ℕ) :
    localQuotientHilbertSamuel (A ⧸ I) ⊥ n = localQuotientHilbertSamuel A I n := by
  rw [← Ideal.map_bot (f := Ideal.Quotient.mk I), localQuotientHilbertSamuel_quotient_map,
    bot_sup_eq]

/-- A ring equivalence between local rings preserves `localQuotientHilbertSamuel`. -/
@[simp]
theorem localQuotientHilbertSamuel_map_equiv (e : A ≃+* B) (I : Ideal A) (n : ℕ) :
    localQuotientHilbertSamuel B (I.map e) n = localQuotientHilbertSamuel A I n := by
  rw [localQuotientHilbertSamuel_map_of_surjective e.surjective, RingHom.ker_equiv, sup_bot_eq]

@[simp]
theorem localQuotientHilbertSamuel_comap_equiv (e : A ≃+* B) (J : Ideal B) (n : ℕ) :
    localQuotientHilbertSamuel A (J.comap e) n = localQuotientHilbertSamuel B J n := by
  simpa only [Ideal.comap_coe, ← Ideal.map_symm] using
    localQuotientHilbertSamuel_map_equiv e.symm J n

theorem localQuotientHilbertSamuel_bot_of_ringEquiv (e : A ≃+* B) (n : ℕ) :
    localQuotientHilbertSamuel B ⊥ n = localQuotientHilbertSamuel A ⊥ n := by
  simpa using localQuotientHilbertSamuel_map_equiv e ⊥ n

end Transport

section Noetherian

variable {A B : Type*} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
  [CommRing B] [IsLocalRing B] [IsNoetherianRing B]

/-- Over a Noetherian local ring `A`, `A ⧸ (I ⊔ 𝔪 ^ (n + 1))` has finite length for every ideal
`I`, including `I = ⊤`. -/
theorem isFiniteLength_quotient_sup_maximalIdeal_pow (I : Ideal A) (n : ℕ) :
    IsFiniteLength A (A ⧸ (I ⊔ maximalIdeal A ^ (n + 1))) :=
  (isFiniteLength_quotient_maximalIdeal_pow (n + 1)).of_surjective
    (Submodule.factor_surjective (le_sup_right : maximalIdeal A ^ (n + 1) ≤ _))

@[simp]
theorem localQuotientHilbertSamuel_ne_top (I : Ideal A) (n : ℕ) :
    localQuotientHilbertSamuel A I n ≠ ⊤ :=
  Module.length_ne_top_iff.mpr (isFiniteLength_quotient_sup_maximalIdeal_pow I n)

/-- Over a Noetherian local ring `A`, every value of `localQuotientHilbertSamuel A I` is finite. -/
theorem localQuotientHilbertSamuel_lt_top (I : Ideal A) (n : ℕ) :
    localQuotientHilbertSamuel A I n < ⊤ :=
  (localQuotientHilbertSamuel_ne_top I n).lt_top

@[simp]
theorem natCast_toNat_localQuotientHilbertSamuel (I : Ideal A) (n : ℕ) :
    ((localQuotientHilbertSamuel A I n).toNat : ℕ∞) = localQuotientHilbertSamuel A I n :=
  ENat.natCast_toNat (localQuotientHilbertSamuel_ne_top I n)

theorem toNat_localQuotientHilbertSamuel_le_iff {I : Ideal A} {J : Ideal B} {n : ℕ} :
    (localQuotientHilbertSamuel A I n).toNat ≤ (localQuotientHilbertSamuel B J n).toNat ↔
      localQuotientHilbertSamuel A I n ≤ localQuotientHilbertSamuel B J n := by
  rw [← Nat.cast_le (α := ℕ∞), natCast_toNat_localQuotientHilbertSamuel,
    natCast_toNat_localQuotientHilbertSamuel]

theorem toNat_localQuotientHilbertSamuel_lt_iff {I : Ideal A} {J : Ideal B} {n : ℕ} :
    (localQuotientHilbertSamuel A I n).toNat < (localQuotientHilbertSamuel B J n).toNat ↔
      localQuotientHilbertSamuel A I n < localQuotientHilbertSamuel B J n := by
  rw [← Nat.cast_lt (α := ℕ∞), natCast_toNat_localQuotientHilbertSamuel,
    natCast_toNat_localQuotientHilbertSamuel]

theorem toNat_localQuotientHilbertSamuel_eq_iff {I : Ideal A} {J : Ideal B} {n : ℕ} :
    (localQuotientHilbertSamuel A I n).toNat = (localQuotientHilbertSamuel B J n).toNat ↔
      localQuotientHilbertSamuel A I n = localQuotientHilbertSamuel B J n := by
  rw [← Nat.cast_inj (R := ℕ∞), natCast_toNat_localQuotientHilbertSamuel,
    natCast_toNat_localQuotientHilbertSamuel]

/-- Over Noetherian local rings, strict lexicographic comparison of `toNat`-valued Hilbert–Samuel
functions agrees with that of `ℕ∞`-valued Hilbert–Samuel functions. -/
theorem toLex_toNat_localQuotientHilbertSamuel_lt_iff {I : Ideal A} {J : Ideal B} :
    toLex (fun n ↦ (localQuotientHilbertSamuel A I n).toNat) <
      toLex (fun n ↦ (localQuotientHilbertSamuel B J n).toNat) ↔
      toLex (localQuotientHilbertSamuel A I) < toLex (localQuotientHilbertSamuel B J) :=
  exists_congr fun _ ↦ and_congr
    (forall₂_congr fun _ _ ↦ toNat_localQuotientHilbertSamuel_eq_iff)
    toNat_localQuotientHilbertSamuel_lt_iff

/-- Over Noetherian local rings, lexicographic comparison of `toNat`-valued Hilbert–Samuel
functions agrees with that of `ℕ∞`-valued Hilbert–Samuel functions. -/
theorem toLex_toNat_localQuotientHilbertSamuel_le_iff {I : Ideal A} {J : Ideal B} :
    toLex (fun n ↦ (localQuotientHilbertSamuel A I n).toNat) ≤
      toLex (fun n ↦ (localQuotientHilbertSamuel B J n).toNat) ↔
      toLex (localQuotientHilbertSamuel A I) ≤ toLex (localQuotientHilbertSamuel B J) := by
  rw [le_iff_lt_or_eq, le_iff_lt_or_eq, toLex_inj, toLex_inj, funext_iff, funext_iff]
  exact or_congr toLex_toNat_localQuotientHilbertSamuel_lt_iff
    (forall_congr' fun _ ↦ toNat_localQuotientHilbertSamuel_eq_iff)

/-- Over a Noetherian local ring `A`, `localQuotientHilbertSamuel A I n` equals the ambient value
`localQuotientHilbertSamuel A ⊥ n` if and only if `(n + 1 : ℕ∞) ≤ I.localOrder`. -/
theorem localQuotientHilbertSamuel_eq_bot_iff (I : Ideal A) (n : ℕ) :
    localQuotientHilbertSamuel A I n = localQuotientHilbertSamuel A ⊥ n ↔
      ((n + 1 : ℕ) : ℕ∞) ≤ I.localOrder := by
  refine ⟨fun h ↦ ?_, localQuotientHilbertSamuel_eq_bot_of_le_localOrder⟩
  let P : Ideal A := maximalIdeal A ^ (n + 1)
  have hadd := length_quotient_eq_length_map_add_length_quotient_sup I P
  rw [← localQuotientHilbertSamuel_bot_def, sup_comm, ← localQuotientHilbertSamuel_def, h] at hadd
  have hfin := localQuotientHilbertSamuel_ne_top (A := A) ⊥ n
  have hmap0 : Module.length A (Submodule.map P.mkQ I) = 0 :=
    (ENat.add_left_injective_of_ne_top hfin (by simpa only [zero_add] using hadd)).symm
  rw [Module.length_eq_zero_iff, Submodule.subsingleton_iff_eq_bot] at hmap0
  have hle : I ≤ P := by
    simpa only [Submodule.comap_bot, Submodule.ker_mkQ] using
      Submodule.map_le_iff_le_comap.mp hmap0.le
  exact (I.natCast_le_localOrder_iff (n + 1)).mpr hle

/-- Over a Noetherian local ring, ideals with the same Hilbert–Samuel function have the same
`Ideal.localOrder`. -/
theorem localOrder_eq_of_localQuotientHilbertSamuel_eq {I J : Ideal A}
    (h : localQuotientHilbertSamuel A I = localQuotientHilbertSamuel A J) :
    I.localOrder = J.localOrder := by
  apply ENat.eq_of_forall_natCast_le_iff
  intro k
  cases k with
  | zero => simp
  | succ n =>
    rw [← localQuotientHilbertSamuel_eq_bot_iff, ← localQuotientHilbertSamuel_eq_bot_iff,
      congrFun h n]

/-- Over a Noetherian local ring, an ideal has the same Hilbert–Samuel function as `⊥` if and only
if it is `⊥`. -/
@[simp]
theorem localQuotientHilbertSamuel_eq_bot_fun_iff {I : Ideal A} :
    localQuotientHilbertSamuel A I = localQuotientHilbertSamuel A ⊥ ↔ I = ⊥ := by
  refine ⟨fun h ↦ ?_, fun h ↦ h ▸ rfl⟩
  have hord := localOrder_eq_of_localQuotientHilbertSamuel_eq h
  rw [Ideal.localOrder_bot, Ideal.localOrder_eq_top_iff_eq_bot] at hord
  exact hord

/-- **Hilbert–Samuel rigidity along ideal inclusions**: in a Noetherian local ring, if `I ≤ J` and
`I` and `J` have the same Hilbert–Samuel function, then `I = J`. -/
theorem eq_of_le_of_localQuotientHilbertSamuel_eq {I J : Ideal A} (hle : I ≤ J)
    (h : localQuotientHilbertSamuel A I = localQuotientHilbertSamuel A J) :
    I = J := by
  rcases eq_or_ne I ⊤ with rfl | hI
  · exact (top_unique hle).symm
  have : Nontrivial (A ⧸ I) := Ideal.Quotient.nontrivial_iff.mpr hI
  have : IsLocalRing (A ⧸ I) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
  have : IsNoetherianRing (A ⧸ I) :=
    isNoetherianRing_of_surjective A (A ⧸ I) (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
  have hquot : localQuotientHilbertSamuel (A ⧸ I) (J.map (Ideal.Quotient.mk I)) =
      localQuotientHilbertSamuel (A ⧸ I) ⊥ := by
    ext n
    rw [localQuotientHilbertSamuel_quotient_map, localQuotientHilbertSamuel_quotient_bot,
      sup_eq_left.mpr hle, congrFun h n]
  have hmap : J.map (Ideal.Quotient.mk I) = ⊥ :=
    localQuotientHilbertSamuel_eq_bot_fun_iff.mp hquot
  rw [Ideal.map_eq_bot_iff_le_ker, Ideal.mk_ker] at hmap
  exact le_antisymm hle hmap

end Noetherian

section Completion

/-- If the maximal ideal of a local ring `A` is finitely generated, extending an ideal `I` to the
maximal-adic completion `AdicCompletion (maximalIdeal A) A` preserves every value of
`localQuotientHilbertSamuel`. -/
theorem localQuotientHilbertSamuel_adicCompletion_of_fg {A : Type*} [CommRing A] [IsLocalRing A]
    (fg : (maximalIdeal A).FG) (I : Ideal A) (n : ℕ) :
    letI := AdicCompletion.isLocalRing_of_fg fg
    localQuotientHilbertSamuel (AdicCompletion (maximalIdeal A) A)
      (I.map (algebraMap A (AdicCompletion (maximalIdeal A) A))) n =
      localQuotientHilbertSamuel A I n := by
  have := AdicCompletion.isLocalRing_of_fg fg
  set B := AdicCompletion (maximalIdeal A) A
  let ψ := AdicCompletion.evalₐ (maximalIdeal A) (n + 1)
  have hker : RingHom.ker ψ = maximalIdeal B ^ (n + 1) := by
    rw [AdicCompletion.ker_evalₐ_eq_map_pow fg (n + 1),
      AdicCompletion.maximalIdeal_eq_map_of_fg fg, Ideal.map_pow]
  have hmap : (I.map (algebraMap A B)).map ψ =
      I.map (Ideal.Quotient.mk (maximalIdeal A ^ (n + 1))) := by
    have hAB : I.map (algebraMap A B) = Ideal.span (algebraMap A B '' I) := rfl
    rw [hAB, Ideal.map_span, Set.image_image, Ideal.map]
    congr 2
  calc
    localQuotientHilbertSamuel B (I.map (algebraMap A B)) n
        = Module.length B (B ⧸ (I.map (algebraMap A B) ⊔ RingHom.ker ψ)) := by
          rw [localQuotientHilbertSamuel_def, hker]
    _ = Module.length (A ⧸ maximalIdeal A ^ (n + 1))
          ((A ⧸ maximalIdeal A ^ (n + 1)) ⧸ (I.map (algebraMap A B)).map ψ) :=
          (Ideal.length_quotient_map_of_surjective _
            (AdicCompletion.surjective_evalₐ (maximalIdeal A) (n + 1))).symm
    _ = localQuotientHilbertSamuel A I n := by
          rw [hmap, Ideal.length_quotient_map_of_surjective _ Ideal.Quotient.mk_surjective,
            Ideal.mk_ker, localQuotientHilbertSamuel_def]

/-- Over a Noetherian local ring `A`, extending an ideal `I` to the maximal-adic completion
preserves every value of `localQuotientHilbertSamuel`. -/
@[simp]
theorem localQuotientHilbertSamuel_adicCompletion (A : Type*) [CommRing A] [IsLocalRing A]
    [IsNoetherianRing A] (I : Ideal A) (n : ℕ) :
    localQuotientHilbertSamuel (AdicCompletion (maximalIdeal A) A)
      (I.map (algebraMap A (AdicCompletion (maximalIdeal A) A))) n =
      localQuotientHilbertSamuel A I n :=
  localQuotientHilbertSamuel_adicCompletion_of_fg (maximalIdeal A).fg_of_isNoetherianRing I n

/-- Over a Noetherian local ring `A`, the maximal-adic completion has the same Hilbert–Samuel
function as `A`. -/
@[simp]
theorem localQuotientHilbertSamuel_adicCompletion_bot (A : Type*) [CommRing A] [IsLocalRing A]
    [IsNoetherianRing A] (n : ℕ) :
    localQuotientHilbertSamuel (AdicCompletion (maximalIdeal A) A) ⊥ n =
      localQuotientHilbertSamuel A ⊥ n := by
  simpa using localQuotientHilbertSamuel_adicCompletion A ⊥ n

end Completion

-- A degree-two closed point over `ℚ` (here `ℚ(i) = QuadraticAlgebra ℚ (-1) 0`) has local
-- Hilbert–Samuel value `1` at `0` by local length, even though its `ℚ`-dimension is `2`.
example :
    letI : Fact (¬ IsSquare (-1 : ℚ)) := ⟨not_isSquare_of_neg (by norm_num)⟩
    localQuotientHilbertSamuel (QuadraticAlgebra ℚ (-1) 0) ⊥ 0 = 1 ∧
      Module.finrank ℚ (QuadraticAlgebra ℚ (-1) 0) = 2 := by
  have : Fact (¬ IsSquare (-1 : ℚ)) := ⟨not_isSquare_of_neg (by norm_num)⟩
  refine ⟨localQuotientHilbertSamuel_bot_of_field _ 0, ?_⟩
  simpa using Module.finrank_eq_card_basis (QuadraticAlgebra.basis (-1 : ℚ) 0)

end TauCeti
