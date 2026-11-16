/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.AdicCompletion.LocalRing
public import Mathlib.RingTheory.Length
public import Mathlib.RingTheory.LocalRing.Basic
import Mathlib.RingTheory.LocalRing.Quotient
import TauCeti.RingTheory.AdicCompletion.Algebra
import TauCeti.RingTheory.Length

/-!
# The Hilbert–Samuel function of a local ring and its quotients

For a commutative local ring `(A, 𝔪)` and an ideal `I : Ideal A`, the Hilbert–Samuel function of
the quotient `A ⧸ I` is defined by
`H_{A / I}(n) = Module.length A (A ⧸ (I ⊔ 𝔪 ^ (n + 1)))` (`TauCeti.localQuotientHilbertSamuel`).
This handles the unit ideal `I = ⊤` uniformly (giving the zero function) while agreeing with the
intrinsic Hilbert–Samuel function `H_{A / I}(n) = Module.length (A ⧸ I) ((A ⧸ I) ⧸ 𝔪_{A/I}^{n+1})`
whenever `A ⧸ I` is a local ring (`TauCeti.localQuotientHilbertSamuel_quotient_bot`).

For a Noetherian local ring `A`, every value of `localQuotientHilbertSamuel A I` is finite
(`TauCeti.localQuotientHilbertSamuel_ne_top`) and hence identifies with a natural number
(`TauCeti.natCast_toNat_localQuotientHilbertSamuel`). Passing to the `𝔪`-adic completion
`AdicCompletion 𝔪 A` preserves every value of the Hilbert–Samuel function whenever `𝔪` is finitely
generated (`TauCeti.localQuotientHilbertSamuel_adicCompletion_of_fg`), and in particular for every
Noetherian local ring (`TauCeti.localQuotientHilbertSamuel_adicCompletion`).

## Main definitions

* `TauCeti.localQuotientHilbertSamuel`: the Hilbert–Samuel function
  `n ↦ length_A(A ⧸ (I + 𝔪 ^ (n + 1)))` of a local quotient `A ⧸ I`.

## Main results

* `TauCeti.localQuotientHilbertSamuel_mono`, `TauCeti.localQuotientHilbertSamuel_anti`:
  monotonicity in the degree `n` and antitonicity in the ideal `I`.
* `TauCeti.localQuotientHilbertSamuel_zero_of_ne_top`,
  `TauCeti.localQuotientHilbertSamuel_eq_zero_iff`, `TauCeti.localQuotientHilbertSamuel_field`:
  a proper ideal has `H(0) = 1`, `H(n) = 0 ↔ I = ⊤`, and a field has `H(n) = 1` for all `n`
  (measured by local length, not dimension over a subfield).
* `TauCeti.localQuotientHilbertSamuel_ne_top`,
  `TauCeti.isFiniteLength_quotient_sup_maximalIdeal_pow`,
  `TauCeti.natCast_toNat_localQuotientHilbertSamuel`: finiteness for Noetherian local rings.
* `TauCeti.localQuotientHilbertSamuel_map_of_surjective`,
  `TauCeti.localQuotientHilbertSamuel_quotient_bot`,
  `TauCeti.localQuotientHilbertSamuel_map_ringEquiv`: invariance under quotients and ring
  isomorphisms.
* `TauCeti.localQuotientHilbertSamuel_adicCompletion_of_fg`,
  `TauCeti.localQuotientHilbertSamuel_adicCompletion`: invariance under maximal-adic completion.

## References

* Edward Bierstone and Pierre D. Milman, *Canonical desingularization in characteristic zero by
  blowing up the maximum strata of a local invariant*, Invent. Math. 128 (1997), 207–302,
  Remarks 1.3, pp. 213–214.
-/

public section

namespace TauCeti

open IsLocalRing

/-- The Hilbert–Samuel function of the quotient `A ⧸ I` of a local ring `A`, measured by
local-ring length `length_A(A ⧸ (I + 𝔪 ^ (n + 1)))`. For `I = ⊤` this is identically zero; for a
Noetherian local ring every value is finite. -/
noncomputable def localQuotientHilbertSamuel (A : Type*) [CommRing A] [IsLocalRing A]
    (I : Ideal A) (n : ℕ) : ℕ∞ :=
  Module.length A (A ⧸ (I ⊔ maximalIdeal A ^ (n + 1)))

section Basic

variable (A : Type*) [CommRing A] [IsLocalRing A]

/-- Definitional unfolding of `localQuotientHilbertSamuel`. -/
theorem localQuotientHilbertSamuel_def (I : Ideal A) (n : ℕ) :
    localQuotientHilbertSamuel A I n =
      Module.length A (A ⧸ (I ⊔ maximalIdeal A ^ (n + 1))) := (rfl)

/-- The unit ideal gives the zero Hilbert–Samuel function. -/
@[simp]
theorem localQuotientHilbertSamuel_top (n : ℕ) :
    localQuotientHilbertSamuel A ⊤ n = 0 := by
  rw [localQuotientHilbertSamuel_def, top_sup_eq]
  have : Subsingleton (A ⧸ (⊤ : Ideal A)) := Ideal.Quotient.subsingleton_iff.mpr rfl
  exact Module.length_eq_zero_iff.mpr this

/-- The Hilbert–Samuel function of `A` itself (at `I = ⊥`). -/
theorem localQuotientHilbertSamuel_bot (n : ℕ) :
    localQuotientHilbertSamuel A ⊥ n = Module.length A (A ⧸ maximalIdeal A ^ (n + 1)) := by
  rw [localQuotientHilbertSamuel_def, bot_sup_eq]

/-- Every proper ideal of a local ring has Hilbert–Samuel value `1` in degree `0`. -/
theorem localQuotientHilbertSamuel_zero_of_ne_top {I : Ideal A} (hI : I ≠ ⊤) :
    localQuotientHilbertSamuel A I 0 = 1 := by
  rw [localQuotientHilbertSamuel_def, zero_add, pow_one,
    sup_eq_right.mpr (le_maximalIdeal hI), Ideal.length_quotient_eq_one]

/-- Every local ring has Hilbert–Samuel value `1` in degree `0`. -/
@[simp]
theorem localQuotientHilbertSamuel_bot_zero :
    localQuotientHilbertSamuel A ⊥ 0 = 1 :=
  localQuotientHilbertSamuel_zero_of_ne_top A bot_ne_top

/-- The Hilbert–Samuel function is monotone in the degree `n`. -/
theorem localQuotientHilbertSamuel_mono (I : Ideal A) :
    Monotone (localQuotientHilbertSamuel A I) := fun _ _ h ↦
  length_quotient_anti (sup_le_sup_left (Ideal.pow_le_pow_right (Nat.add_le_add_right h 1)) I)

/-- Larger ideals have smaller Hilbert–Samuel functions. -/
theorem localQuotientHilbertSamuel_anti (n : ℕ) :
    Antitone fun I : Ideal A ↦ localQuotientHilbertSamuel A I n := fun _ _ h ↦
  length_quotient_anti (sup_le_sup_right h _)

/-- Every quotient ideal has Hilbert–Samuel function bounded above by that of the ambient ring. -/
theorem localQuotientHilbertSamuel_le_bot (I : Ideal A) (n : ℕ) :
    localQuotientHilbertSamuel A I n ≤ localQuotientHilbertSamuel A ⊥ n :=
  localQuotientHilbertSamuel_anti A n bot_le

/-- Every proper ideal of a local ring has Hilbert–Samuel value at least `1` in every degree. -/
theorem one_le_localQuotientHilbertSamuel_of_ne_top {I : Ideal A} (hI : I ≠ ⊤) (n : ℕ) :
    1 ≤ localQuotientHilbertSamuel A I n := by
  rw [← localQuotientHilbertSamuel_zero_of_ne_top A hI]
  exact localQuotientHilbertSamuel_mono A I (Nat.zero_le n)

/-- The Hilbert–Samuel value of `A ⧸ I` vanishes if and only if `I = ⊤`. -/
@[simp]
theorem localQuotientHilbertSamuel_eq_zero_iff {I : Ideal A} {n : ℕ} :
    localQuotientHilbertSamuel A I n = 0 ↔ I = ⊤ := by
  refine ⟨fun h ↦ by_contra fun hI ↦ ?_, fun h ↦ h ▸ localQuotientHilbertSamuel_top A n⟩
  have h1 := one_le_localQuotientHilbertSamuel_of_ne_top A hI n
  rw [h] at h1
  exact not_le_of_gt zero_lt_one h1

end Basic

section Field

/-- Every field has Hilbert–Samuel function identically equal to `1`, regardless of its degree
over any base subfield. -/
@[simp]
theorem localQuotientHilbertSamuel_field (K : Type*) [Field K] (n : ℕ) :
    localQuotientHilbertSamuel K ⊥ n = 1 := by
  rw [localQuotientHilbertSamuel_bot, maximalIdeal_eq_bot, ← Ideal.zero_eq_bot,
    zero_pow (Nat.succ_ne_zero n), Ideal.zero_eq_bot, ← maximalIdeal_eq_bot (R := K),
    Ideal.length_quotient_eq_one]

-- A field extension of degree > 1 still has `H(0) = 1` when measured by intrinsic local length.
example (L : Type*) [Field L] [Algebra ℚ L] : localQuotientHilbertSamuel L ⊥ 0 = 1 :=
  localQuotientHilbertSamuel_field L 0

end Field

section Noetherian

variable (A : Type*) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]

/-- For a Noetherian local ring, every value of `localQuotientHilbertSamuel` is finite. -/
theorem localQuotientHilbertSamuel_ne_top (I : Ideal A) (n : ℕ) :
    localQuotientHilbertSamuel A I n ≠ ⊤ := by
  rw [← lt_top_iff_ne_top]
  refine (localQuotientHilbertSamuel_le_bot A I n).trans_lt ?_
  rw [localQuotientHilbertSamuel_bot, lt_top_iff_ne_top, Module.length_ne_top_iff]
  exact isFiniteLength_quotient_maximalIdeal_pow (n + 1)

/-- Every quotient of a Noetherian local ring by `I ⊔ 𝔪 ^ (n + 1)` has finite length. -/
theorem isFiniteLength_quotient_sup_maximalIdeal_pow (I : Ideal A) (n : ℕ) :
    IsFiniteLength A (A ⧸ (I ⊔ maximalIdeal A ^ (n + 1))) :=
  Module.length_ne_top_iff.mp (localQuotientHilbertSamuel_ne_top A I n)

/-- For a Noetherian local ring, `localQuotientHilbertSamuel` agrees with the cast of its
natural-number value. -/
@[simp]
theorem natCast_toNat_localQuotientHilbertSamuel (I : Ideal A) (n : ℕ) :
    ((localQuotientHilbertSamuel A I n).toNat : ℕ∞) = localQuotientHilbertSamuel A I n :=
  ENat.natCast_toNat (localQuotientHilbertSamuel_ne_top A I n)

end Noetherian

section Transport

/-- Along a surjective homomorphism of local rings `ψ : A →+* B`, the Hilbert–Samuel function of
`B ⧸ I.map ψ` equals that of `A ⧸ (I ⊔ ker ψ)`. -/
theorem localQuotientHilbertSamuel_map_of_surjective {A B : Type*} [CommRing A] [IsLocalRing A]
    [CommRing B] [IsLocalRing B] {ψ : A →+* B} (hψ : Function.Surjective ψ)
    (I : Ideal A) (n : ℕ) :
    localQuotientHilbertSamuel B (I.map ψ) n =
      localQuotientHilbertSamuel A (I ⊔ RingHom.ker ψ) n := by
  rw [localQuotientHilbertSamuel_def, localQuotientHilbertSamuel_def,
    ← map_maximalIdeal_of_surjective ψ hψ, ← Ideal.map_pow, ← Ideal.map_sup,
    Ideal.length_quotient_map_of_surjective _ hψ, sup_right_comm]

/-- For a local quotient `A ⧸ I`, the Hilbert–Samuel function of `(A ⧸ I) ⧸ J.map mk` equals that
of `A ⧸ (J ⊔ I)`. -/
theorem localQuotientHilbertSamuel_quotient {A : Type*} [CommRing A] [IsLocalRing A]
    (I : Ideal A) [IsLocalRing (A ⧸ I)] (J : Ideal A) (n : ℕ) :
    localQuotientHilbertSamuel (A ⧸ I) (J.map (Ideal.Quotient.mk I)) n =
      localQuotientHilbertSamuel A (J ⊔ I) n := by
  rw [localQuotientHilbertSamuel_map_of_surjective Ideal.Quotient.mk_surjective,
    Ideal.mk_ker]

/-- Whenever `A ⧸ I` is a local ring, its intrinsic Hilbert–Samuel function equals
`localQuotientHilbertSamuel A I`. -/
@[simp]
theorem localQuotientHilbertSamuel_quotient_bot {A : Type*} [CommRing A] [IsLocalRing A]
    (I : Ideal A) [IsLocalRing (A ⧸ I)] (n : ℕ) :
    localQuotientHilbertSamuel (A ⧸ I) ⊥ n = localQuotientHilbertSamuel A I n := by
  simpa only [Ideal.map_bot, bot_sup_eq] using
    localQuotientHilbertSamuel_quotient I ⊥ n

/-- Ring isomorphisms preserve the Hilbert–Samuel function. -/
theorem localQuotientHilbertSamuel_map_ringEquiv {A B : Type*} [CommRing A] [IsLocalRing A]
    [CommRing B] [IsLocalRing B] (e : A ≃+* B) (I : Ideal A) (n : ℕ) :
    localQuotientHilbertSamuel B (I.map (e : A →+* B)) n = localQuotientHilbertSamuel A I n := by
  rw [localQuotientHilbertSamuel_map_of_surjective (ψ := (e : A →+* B)) e.surjective,
    (RingHom.injective_iff_ker_eq_bot (e : A →+* B)).mp e.injective, sup_bot_eq]

end Transport

section Completion

/-- Maximal-adic completion preserves every value of `localQuotientHilbertSamuel` whenever the
maximal ideal of `A` is finitely generated. -/
theorem localQuotientHilbertSamuel_adicCompletion_of_fg {A : Type*} [CommRing A] [IsLocalRing A]
    (hfg : (maximalIdeal A).FG) (I : Ideal A) (n : ℕ) :
    have := AdicCompletion.isLocalRing_of_fg hfg
    localQuotientHilbertSamuel (AdicCompletion (maximalIdeal A) A)
      (I.map (algebraMap A (AdicCompletion (maximalIdeal A) A))) n =
      localQuotientHilbertSamuel A I n := by
  dsimp only
  have : IsLocalRing (AdicCompletion (maximalIdeal A) A) := AdicCompletion.isLocalRing_of_fg hfg
  set 𝔪 := maximalIdeal A
  set Â := AdicCompletion 𝔪 A
  have hcomp : (AdicCompletion.evalₐ 𝔪 (n + 1)).toRingHom.comp (algebraMap A Â) =
      Ideal.Quotient.mk (𝔪 ^ (n + 1)) :=
    RingHom.ext fun a ↦ AdicCompletion.evalₐ_of 𝔪 (n + 1) a
  have h1 := Ideal.length_quotient_map_of_surjective
    (ψ := (AdicCompletion.evalₐ 𝔪 (n + 1)).toRingHom)
    (I.map (algebraMap A Â)) (AdicCompletion.surjective_evalₐ 𝔪 (n + 1))
  have h2 := Ideal.length_quotient_map_of_surjective I
    (Ideal.Quotient.mk_surjective (I := 𝔪 ^ (n + 1)))
  rw [Ideal.map_map, hcomp, AlgHom.toRingHom_eq_coe, RingHom.ker_coe_toRingHom,
    AdicCompletion.ker_evalₐ_eq_map_pow hfg, Ideal.map_pow,
    ← AdicCompletion.maximalIdeal_eq_map_of_fg hfg] at h1
  rw [Ideal.mk_ker] at h2
  exact h1.symm.trans h2

/-- Maximal-adic completion of a Noetherian local ring preserves every value of
`localQuotientHilbertSamuel`. -/
@[simp]
theorem localQuotientHilbertSamuel_adicCompletion {A : Type*} [CommRing A] [IsLocalRing A]
    [IsNoetherianRing A] (I : Ideal A) (n : ℕ) :
    localQuotientHilbertSamuel (AdicCompletion (maximalIdeal A) A)
      (I.map (algebraMap A (AdicCompletion (maximalIdeal A) A))) n =
      localQuotientHilbertSamuel A I n :=
  localQuotientHilbertSamuel_adicCompletion_of_fg (maximalIdeal A).fg_of_isNoetherianRing I n

/-- Maximal-adic completion of a Noetherian local ring preserves its intrinsic Hilbert–Samuel
function. -/
@[simp]
theorem localQuotientHilbertSamuel_adicCompletion_bot {A : Type*} [CommRing A] [IsLocalRing A]
    [IsNoetherianRing A] (n : ℕ) :
    localQuotientHilbertSamuel (AdicCompletion (maximalIdeal A) A) ⊥ n =
      localQuotientHilbertSamuel A ⊥ n := by
  simpa only [Ideal.map_bot] using localQuotientHilbertSamuel_adicCompletion (⊥ : Ideal A) n

end Completion

end TauCeti
