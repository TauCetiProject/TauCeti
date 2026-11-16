/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.AdicCompletion.LocalRing
public import Mathlib.RingTheory.Length
import TauCeti.RingTheory.AdicCompletion.Algebra
import TauCeti.RingTheory.Length

/-!
# The Hilbert–Samuel function of an ideal in a local ring

For a commutative local ring `(A, 𝔪)` and an ideal `I : Ideal A`, the Hilbert–Samuel function of
the quotient `A ⧸ I` at degree `n : ℕ` is the `A`-module length
`I.hilbertSamuel n = Module.length A (A ⧸ (I ⊔ 𝔪 ^ (n + 1))) : ℕ∞`. This convention handles the
unit ideal uniformly (`⊤.hilbertSamuel n = 0`) and identifies `(⊥ : Ideal A).hilbertSamuel n` with
`Module.length A (A ⧸ 𝔪 ^ (n + 1))`.

Because length is measured over the local ring `A` rather than a base field, every proper ideal
satisfies `I.hilbertSamuel 0 = 1`, independently of the degree of the residue field over a ground
field. Every surjective homomorphism `ψ : A →+* B` of local rings satisfies
`(I.map ψ).hilbertSamuel n = (I ⊔ ker ψ).hilbertSamuel n`, yielding invariance under ring
equivalences and identifying `I.hilbertSamuel` with the Hilbert–Samuel function of `⊥` in `A ⧸ I`.

When `A` is Noetherian, every value `I.hilbertSamuel n` is finite (`Ideal.hilbertSamuel_ne_top`).
Moreover, whenever the maximal ideal `𝔪` is finitely generated (in particular, when `A` is
Noetherian), the `𝔪`-adic completion `Â = AdicCompletion 𝔪 A` has the same reductions modulo powers
of the maximal ideal, so extending `I` to `Â` preserves every value of `I.hilbertSamuel`
(`Ideal.hilbertSamuel_map_adicCompletion_of_fg`, `Ideal.hilbertSamuel_map_adicCompletion`).

## Main definitions

* `Ideal.hilbertSamuel`: the Hilbert–Samuel function `n ↦ Module.length A (A ⧸ (I ⊔ 𝔪 ^ (n + 1)))`.

## Main results

* `Ideal.hilbertSamuel_top`, `Ideal.hilbertSamuel_bot`, `Ideal.hilbertSamuel_eq_zero_iff`:
  boundary values and vanishing characterization.
* `Ideal.hilbertSamuel_zero_of_ne_top`, `Ideal.hilbertSamuel_bot_of_field`: value `1` at degree `0`
  for every proper ideal (and at every degree for a field).
* `Ideal.hilbertSamuel_anti`, `Ideal.hilbertSamuel_mono`: antitonicity in the ideal and
  monotonicity in the degree.
* `Ideal.hilbertSamuel_map_of_surjective`, `Ideal.hilbertSamuel_map_quotientMk`,
  `Ideal.hilbertSamuel_quotient_bot`, `Ideal.hilbertSamuel_map_equiv`: behaviour along surjections,
  quotients, and ring equivalences.
* `Ideal.hilbertSamuel_ne_top`, `Ideal.natCast_toNat_hilbertSamuel`: finiteness over a Noetherian
  local ring.
* `Ideal.hilbertSamuel_map_adicCompletion_of_fg`, `Ideal.hilbertSamuel_map_adicCompletion`:
  invariance under maximal-adic completion.

## References

* Edward Bierstone and Pierre D. Milman, *Canonical desingularization in characteristic zero by
  blowing up the maximum strata of a local invariant*, Invent. Math. 128 (1997), 207–302,
  Remarks 1.3 (pp. 213–214), Corollary 3.20 (p. 239), Theorem 9.2 and Lemma 9.3 (p. 276).
-/

public section

namespace Ideal

open IsLocalRing

section Basic

variable {A : Type*} [CommRing A] [IsLocalRing A]

/-- The Hilbert–Samuel function of `A ⧸ I` at degree `n`: the `A`-module length of
`A ⧸ (I ⊔ 𝔪 ^ (n + 1))`. -/
noncomputable def hilbertSamuel (I : Ideal A) (n : ℕ) : ℕ∞ :=
  Module.length A (A ⧸ (I ⊔ maximalIdeal A ^ (n + 1)))

/-- Definitional unfolding of `Ideal.hilbertSamuel`. -/
theorem hilbertSamuel_def (I : Ideal A) (n : ℕ) :
    I.hilbertSamuel n = Module.length A (A ⧸ (I ⊔ maximalIdeal A ^ (n + 1))) := by
  rw [hilbertSamuel]

/-- The unit ideal has identically zero Hilbert–Samuel function. -/
@[simp]
theorem hilbertSamuel_top (n : ℕ) : (⊤ : Ideal A).hilbertSamuel n = 0 := by
  rw [hilbertSamuel_def, top_sup_eq, Module.length_eq_zero_iff, Submodule.Quotient.subsingleton_iff]

/-- The Hilbert–Samuel function of the zero ideal is the length of `A ⧸ 𝔪 ^ (n + 1)`. -/
theorem hilbertSamuel_bot (n : ℕ) :
    (⊥ : Ideal A).hilbertSamuel n = Module.length A (A ⧸ maximalIdeal A ^ (n + 1)) := by
  rw [hilbertSamuel_def, bot_sup_eq]

/-- An ideal has zero Hilbert–Samuel value at degree `n` if and only if it is the unit ideal. -/
@[simp]
theorem hilbertSamuel_eq_zero_iff (I : Ideal A) (n : ℕ) : I.hilbertSamuel n = 0 ↔ I = ⊤ := by
  rw [hilbertSamuel_def, Module.length_eq_zero_iff, Submodule.Quotient.subsingleton_iff]
  refine ⟨fun h ↦ ?_, fun h ↦ by rw [h, top_sup_eq]⟩
  by_contra hI
  have hle : I ⊔ maximalIdeal A ^ (n + 1) ≤ maximalIdeal A :=
    sup_le (le_maximalIdeal hI) (pow_le_self (Nat.succ_ne_zero n))
  exact (maximalIdeal.isMaximal A).ne_top (top_unique (h ▸ hle))

/-- Every proper ideal of a local ring has Hilbert–Samuel value `1` at degree `0`, independently
of any ground-field degree of the residue field. -/
theorem hilbertSamuel_zero_of_ne_top {I : Ideal A} (hI : I ≠ ⊤) : I.hilbertSamuel 0 = 1 := by
  rw [hilbertSamuel_def, zero_add, pow_one, sup_eq_right.mpr (le_maximalIdeal hI)]
  exact Ideal.length_quotient_eq_one (maximalIdeal A)

/-- The zero ideal of a local ring has Hilbert–Samuel value `1` at degree `0`. -/
@[simp]
theorem hilbertSamuel_zero_bot : (⊥ : Ideal A).hilbertSamuel 0 = 1 :=
  hilbertSamuel_zero_of_ne_top bot_ne_top

/-- The zero ideal of a field has identically `1` Hilbert–Samuel function. -/
@[simp]
theorem hilbertSamuel_bot_of_field {K : Type*} [Field K] (n : ℕ) :
    (⊥ : Ideal K).hilbertSamuel n = 1 := by
  rw [hilbertSamuel_bot, maximalIdeal_eq_bot, ← Ideal.zero_eq_bot,
    zero_pow (Nat.succ_ne_zero n), Ideal.zero_eq_bot]
  exact Ideal.length_quotient_eq_one (⊥ : Ideal K)

/-- Larger ideals have smaller Hilbert–Samuel functions. -/
theorem hilbertSamuel_anti {I J : Ideal A} (h : I ≤ J) (n : ℕ) :
    J.hilbertSamuel n ≤ I.hilbertSamuel n :=
  TauCeti.length_quotient_anti (sup_le_sup_right h _)

/-- The Hilbert–Samuel function is nondecreasing in the degree. -/
theorem hilbertSamuel_mono (I : Ideal A) : Monotone I.hilbertSamuel := fun _ _ hmn ↦
  TauCeti.length_quotient_anti
    (sup_le_sup_left (Ideal.pow_le_pow_right (Nat.succ_le_succ hmn)) I)

/-- Along any surjective homomorphism `ψ : A →+* B` of local rings, the Hilbert–Samuel function
of `I.map ψ` agrees with that of `I ⊔ ker ψ`. -/
theorem hilbertSamuel_map_of_surjective {B F : Type*} [CommRing B] [IsLocalRing B]
    [FunLike F A B] [RingHomClass F A B] (I : Ideal A) {ψ : F} (hψ : Function.Surjective ψ)
    (n : ℕ) :
    (I.map ψ).hilbertSamuel n = (I ⊔ RingHom.ker ψ).hilbertSamuel n := by
  rw [hilbertSamuel_def, hilbertSamuel_def,
    ← map_maximalIdeal_of_surjective (ψ : A →+* B) hψ, Ideal.map_coe,
    ← Ideal.map_pow, ← Ideal.map_sup, Ideal.length_quotient_map_of_surjective _ hψ, sup_right_comm]

/-- Pushing an ideal `J` along `A →+* A ⧸ I` computes the Hilbert–Samuel function of `J ⊔ I`. -/
theorem hilbertSamuel_map_quotientMk (J I : Ideal A) [IsLocalRing (A ⧸ I)] (n : ℕ) :
    (J.map (Ideal.Quotient.mk I)).hilbertSamuel n = (J ⊔ I).hilbertSamuel n := by
  rw [J.hilbertSamuel_map_of_surjective Ideal.Quotient.mk_surjective, Ideal.mk_ker]

/-- The Hilbert–Samuel function of `A ⧸ I` (at `⊥`) equals `I.hilbertSamuel`. -/
@[simp]
theorem hilbertSamuel_quotient_bot (I : Ideal A) [IsLocalRing (A ⧸ I)] (n : ℕ) :
    (⊥ : Ideal (A ⧸ I)).hilbertSamuel n = I.hilbertSamuel n := by
  simpa using (⊥ : Ideal A).hilbertSamuel_map_quotientMk I n

/-- A ring equivalence between local rings preserves the Hilbert–Samuel function. -/
@[simp]
theorem hilbertSamuel_map_equiv {B : Type*} [CommRing B] [IsLocalRing B]
    (I : Ideal A) (e : A ≃+* B) (n : ℕ) :
    (I.map e).hilbertSamuel n = I.hilbertSamuel n := by
  rw [I.hilbertSamuel_map_of_surjective e.surjective,
    (RingHom.injective_iff_ker_eq_bot e).mp e.injective, sup_bot_eq]

end Basic

section Finiteness

variable {A : Type*} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]

/-- In a Noetherian local ring, every value of the Hilbert–Samuel function of any ideal is
finite. -/
theorem hilbertSamuel_ne_top (I : Ideal A) (n : ℕ) :
    I.hilbertSamuel n ≠ ⊤ := by
  have hbot : (⊥ : Ideal A).hilbertSamuel n ≠ ⊤ := by
    rw [hilbertSamuel_bot, Module.length_ne_top_iff]
    exact TauCeti.isFiniteLength_quotient_maximalIdeal_pow (n + 1)
  exact ne_top_of_le_ne_top hbot (hilbertSamuel_anti bot_le n)

/-- In a Noetherian local ring, `I.hilbertSamuel n` equals the cast of its `toNat`. -/
@[simp]
theorem natCast_toNat_hilbertSamuel (I : Ideal A) (n : ℕ) :
    ((I.hilbertSamuel n).toNat : ℕ∞) = I.hilbertSamuel n :=
  ENat.natCast_toNat (I.hilbertSamuel_ne_top n)

end Finiteness

section Completion

variable {A : Type*} [CommRing A] [IsLocalRing A]

/-- Extending an ideal to the maximal-adic completion preserves every value of the Hilbert–Samuel
function whenever the maximal ideal is finitely generated. -/
theorem hilbertSamuel_map_adicCompletion_of_fg (hfg : (maximalIdeal A).FG) (I : Ideal A) (n : ℕ) :
    haveI := AdicCompletion.isLocalRing_of_fg hfg
    (I.map (algebraMap A (AdicCompletion (maximalIdeal A) A))).hilbertSamuel n =
      I.hilbertSamuel n := by
  have := AdicCompletion.isLocalRing_of_fg hfg
  set 𝔪 := maximalIdeal A
  set Â := AdicCompletion 𝔪 A
  have hq_surj : Function.Surjective (AdicCompletion.evalₐ 𝔪 (n + 1)) :=
    AdicCompletion.surjective_evalₐ 𝔪 (n + 1)
  have hq_ker : RingHom.ker (AdicCompletion.evalₐ 𝔪 (n + 1)) = maximalIdeal Â ^ (n + 1) := by
    rw [AdicCompletion.ker_evalₐ_eq_map_pow hfg (n + 1), Ideal.map_pow,
      AdicCompletion.maximalIdeal_eq_map_of_fg hfg]
  have hcomp :
      (AdicCompletion.evalₐ 𝔪 (n + 1)).toRingHom.comp (algebraMap A Â) =
        Ideal.Quotient.mk (𝔪 ^ (n + 1)) := by
    ext x
    exact AdicCompletion.evalₐ_of 𝔪 (n + 1) x
  rw [hilbertSamuel_def, ← hq_ker,
    ← Ideal.length_quotient_map_of_surjective (I.map (algebraMap A Â)) hq_surj,
    ← Ideal.map_coe, Ideal.map_map, ← AlgHom.toRingHom_eq_coe, hcomp,
    Ideal.length_quotient_map_of_surjective I Ideal.Quotient.mk_surjective,
    Ideal.mk_ker, ← hilbertSamuel_def]

/-- Extending an ideal of a Noetherian local ring to its maximal-adic completion preserves every
value of the Hilbert–Samuel function. -/
@[simp]
theorem hilbertSamuel_map_adicCompletion [IsNoetherianRing A] (I : Ideal A) (n : ℕ) :
    (I.map (algebraMap A (AdicCompletion (maximalIdeal A) A))).hilbertSamuel n =
      I.hilbertSamuel n :=
  hilbertSamuel_map_adicCompletion_of_fg (IsNoetherian.noetherian _) I n

end Completion

-- A closed point whose residue field has degree 2 over a base field still has `H(0) = 1` by
-- local-ring length.
example {K L : Type*} [Field K] [Field L] [Algebra K L] (_ : Module.finrank K L = 2) :
    (⊥ : Ideal L).hilbertSamuel 0 = 1 :=
  Ideal.hilbertSamuel_zero_bot

end Ideal
