/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.AdicCompletion.LocalRing
public import Mathlib.RingTheory.Length
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic

import Mathlib.RingTheory.LocalRing.Length
import Mathlib.RingTheory.LocalRing.RingHom.Basic
import TauCeti.RingTheory.AdicCompletion.Algebra
import TauCeti.RingTheory.Length

/-!
# The Hilbert–Samuel function of a local quotient

For a commutative local ring `(A, 𝔪_A)` and an ideal `I : Ideal A`, the *Hilbert–Samuel function*
of the local quotient `A ⧸ I` is
`TauCeti.localQuotientHilbertSamuel A I n = Module.length A (A ⧸ (I ⊔ 𝔪_A ^ (n + 1)))`.
Measuring by `Module.length A` rather than vector-space dimension over a ground field `k` makes
`localQuotientHilbertSamuel A I 0 = 1` for every proper ideal `I` regardless of any residue-field
extension `[κ(A) : k]` (`TauCeti.localQuotientHilbertSamuel_zero_of_ne_top`,
`TauCeti.finrank_quotient_sup_maximalIdeal_pow`), while `I = ⊤` has constant value `0`.

Along any surjective ring homomorphism `φ : A →+* B` between local rings,
`localQuotientHilbertSamuel B (I.map φ) n = localQuotientHilbertSamuel A (I ⊔ RingHom.ker φ) n`
(`TauCeti.localQuotientHilbertSamuel_map_of_surjective`). In particular,
`localQuotientHilbertSamuel` is invariant under ring isomorphisms
(`TauCeti.localQuotientHilbertSamuel_map_equiv`), passing to a nontrivial local quotient `A ⧸ I`
(`TauCeti.localQuotientHilbertSamuel_quotient_bot`), and `𝔪_A`-adic completion
(`TauCeti.localQuotientHilbertSamuel_adicCompletion`). Over a Noetherian local ring, every value
`localQuotientHilbertSamuel A I n` is finite (`TauCeti.localQuotientHilbertSamuel_ne_top`).

## Main definitions and results

* `TauCeti.localQuotientHilbertSamuel`: `Module.length A (A ⧸ (I ⊔ 𝔪_A ^ (n + 1)))`.
* `TauCeti.localQuotientHilbertSamuel_anti`, `TauCeti.localQuotientHilbertSamuel_mono`:
  antitonicity in the ideal `I` and monotonicity in the cutoff `n`.
* `TauCeti.localQuotientHilbertSamuel_zero_of_ne_top`,
  `TauCeti.localQuotientHilbertSamuel_top`: evaluation at `n = 0` for proper ideals and at `I = ⊤`.
* `TauCeti.localQuotientHilbertSamuel_map_of_surjective`,
  `TauCeti.localQuotientHilbertSamuel_comap_of_surjective`,
  `TauCeti.localQuotientHilbertSamuel_map_equiv`,
  `TauCeti.localQuotientHilbertSamuel_quotient_bot`: functoriality along surjective local ring
  homomorphisms, isomorphisms, and local quotients.
* `TauCeti.localQuotientHilbertSamuel_ne_top`: finiteness over a Noetherian local ring.
* `TauCeti.localQuotientHilbertSamuel_adicCompletion_of_fg`,
  `TauCeti.localQuotientHilbertSamuel_adicCompletion`: invariance under `𝔪_A`-adic completion.
* `TauCeti.finrank_quotient_sup_maximalIdeal_pow`,
  `TauCeti.localQuotientHilbertSamuel_eq_length_field`: comparison with `k`-dimension and `k`-length
  for a local `k`-algebra.

## References

* H. Matsumura, *Commutative Ring Theory*, §13.
* Edward Bierstone and Pierre D. Milman, *Canonical desingularization in characteristic zero by
  blowing up the maximum strata of a local invariant*, Invent. Math. 128 (1997), 207–302, §3.
-/

public section

open IsLocalRing

namespace TauCeti

section Basic

variable {A B : Type*} [CommRing A] [IsLocalRing A] [CommRing B] [IsLocalRing B]

/-- The Hilbert–Samuel function `H_{A/I}(n) = length_A (A ⧸ (I + 𝔪_A ^ (n + 1)))` of the local
quotient `A ⧸ I` of a local ring `(A, 𝔪_A)`. -/
noncomputable def localQuotientHilbertSamuel (A : Type*) [CommRing A] [IsLocalRing A]
    (I : Ideal A) (n : ℕ) : ℕ∞ :=
  Module.length A (A ⧸ (I ⊔ maximalIdeal A ^ (n + 1)))

/-- Definitional unfolding of `localQuotientHilbertSamuel`. -/
theorem localQuotientHilbertSamuel_def (I : Ideal A) (n : ℕ) :
    localQuotientHilbertSamuel A I n =
      Module.length A (A ⧸ (I ⊔ maximalIdeal A ^ (n + 1))) :=
  (rfl)

/-- Larger ideals give no larger Hilbert–Samuel values at every order `n`. -/
theorem localQuotientHilbertSamuel_anti {I J : Ideal A} (h : I ≤ J) (n : ℕ) :
    localQuotientHilbertSamuel A J n ≤ localQuotientHilbertSamuel A I n :=
  length_quotient_anti (sup_le_sup_right h _)

/-- For a fixed ideal `I`, `localQuotientHilbertSamuel A I` is monotone in `n`. -/
theorem localQuotientHilbertSamuel_mono (I : Ideal A) :
    Monotone (localQuotientHilbertSamuel A I) := fun _ _ h ↦
  length_quotient_anti (sup_le_sup_left (Ideal.pow_le_pow_right (Nat.succ_le_succ h)) I)

/-- Adding `𝔪_A ^ m` for `n + 1 ≤ m` does not change `localQuotientHilbertSamuel` at `n`. -/
theorem localQuotientHilbertSamuel_sup_maximalIdeal_pow_of_le (I : Ideal A) {n m : ℕ}
    (h : n + 1 ≤ m) :
    localQuotientHilbertSamuel A (I ⊔ maximalIdeal A ^ m) n =
      localQuotientHilbertSamuel A I n := by
  have hsup : maximalIdeal A ^ m ⊔ maximalIdeal A ^ (n + 1) = maximalIdeal A ^ (n + 1) :=
    sup_eq_right.mpr (Ideal.pow_le_pow_right h)
  rw [localQuotientHilbertSamuel_def, localQuotientHilbertSamuel_def, sup_assoc, hsup]

/-- `localQuotientHilbertSamuel A I n` depends on `I` only through `I ⊔ 𝔪_A ^ (n + 1)`. -/
@[simp]
theorem localQuotientHilbertSamuel_sup_maximalIdeal_pow (I : Ideal A) (n : ℕ) :
    localQuotientHilbertSamuel A (I ⊔ maximalIdeal A ^ (n + 1)) n =
      localQuotientHilbertSamuel A I n :=
  localQuotientHilbertSamuel_sup_maximalIdeal_pow_of_le I le_rfl

/-- At the unit ideal `⊤`, `localQuotientHilbertSamuel` vanishes at every order `n`. -/
@[simp]
theorem localQuotientHilbertSamuel_top (n : ℕ) :
    localQuotientHilbertSamuel A ⊤ n = 0 := by
  rw [localQuotientHilbertSamuel_def, top_sup_eq, Module.length_eq_zero_iff]
  infer_instance

/-- At `n = 0`, every proper ideal `I ≠ ⊤` of a local ring `A` has `H_{A/I}(0) = 1`. -/
theorem localQuotientHilbertSamuel_zero_of_ne_top {I : Ideal A} (hI : I ≠ ⊤) :
    localQuotientHilbertSamuel A I 0 = 1 := by
  rw [localQuotientHilbertSamuel_def, zero_add, pow_one,
    sup_eq_right.mpr (le_maximalIdeal hI)]
  exact Ideal.length_quotient_eq_one (maximalIdeal A)

/-- `localQuotientHilbertSamuel A I 0 = 0` if and only if `I = ⊤`. -/
@[simp]
theorem localQuotientHilbertSamuel_zero_eq_zero_iff {I : Ideal A} :
    localQuotientHilbertSamuel A I 0 = 0 ↔ I = ⊤ := by
  refine ⟨fun h ↦ ?_, fun h ↦ h ▸ localQuotientHilbertSamuel_top 0⟩
  by_contra hne
  rw [localQuotientHilbertSamuel_zero_of_ne_top hne] at h
  exact one_ne_zero h

/-- `localQuotientHilbertSamuel A I 0 = 1` if and only if `I` is a proper ideal. -/
@[simp]
theorem localQuotientHilbertSamuel_zero_eq_one_iff {I : Ideal A} :
    localQuotientHilbertSamuel A I 0 = 1 ↔ I ≠ ⊤ := by
  refine ⟨fun h htop ↦ ?_, localQuotientHilbertSamuel_zero_of_ne_top⟩
  rw [htop, localQuotientHilbertSamuel_top] at h
  exact zero_ne_one h

/-- The Hilbert–Samuel function of a local ring `A` itself (`I = ⊥`) equals `1` at `n = 0`. -/
@[simp]
theorem localQuotientHilbertSamuel_bot_zero :
    localQuotientHilbertSamuel A ⊥ 0 = 1 :=
  localQuotientHilbertSamuel_zero_of_ne_top bot_ne_top

/-- Along a surjective homomorphism `φ : A →+* B` between local rings, the Hilbert–Samuel function
of `B ⧸ I.map φ` equals that of `A ⧸ (I ⊔ ker φ)`. -/
theorem localQuotientHilbertSamuel_map_of_surjective {φ : A →+* B} (hφ : Function.Surjective φ)
    (I : Ideal A) (n : ℕ) :
    localQuotientHilbertSamuel B (I.map φ) n =
      localQuotientHilbertSamuel A (I ⊔ RingHom.ker φ) n := by
  rw [localQuotientHilbertSamuel_def, localQuotientHilbertSamuel_def,
    ← map_maximalIdeal_of_surjective φ hφ, ← Ideal.map_pow, ← Ideal.map_sup,
    Ideal.length_quotient_map_of_surjective _ hφ, sup_right_comm]

/-- Along a surjective homomorphism `φ : A →+* B` between local rings, pulling back an ideal
`J : Ideal B` preserves the Hilbert–Samuel function. -/
theorem localQuotientHilbertSamuel_comap_of_surjective {φ : A →+* B} (hφ : Function.Surjective φ)
    (J : Ideal B) (n : ℕ) :
    localQuotientHilbertSamuel A (J.comap φ) n = localQuotientHilbertSamuel B J n := by
  have hker : RingHom.ker φ ≤ J.comap φ := by
    rw [RingHom.ker_eq_comap_bot]
    exact Ideal.comap_mono bot_le
  rw [← Ideal.map_comap_of_surjective φ hφ J,
    localQuotientHilbertSamuel_map_of_surjective hφ (J.comap φ) n,
    Ideal.map_comap_of_surjective φ hφ J, sup_eq_left.mpr hker]

/-- Ring isomorphisms preserve `localQuotientHilbertSamuel`. -/
theorem localQuotientHilbertSamuel_map_equiv (e : A ≃+* B) (I : Ideal A) (n : ℕ) :
    localQuotientHilbertSamuel B (I.map e) n = localQuotientHilbertSamuel A I n := by
  have he : I.map e = I.map (e : A →+* B) := rfl
  rw [he, localQuotientHilbertSamuel_map_of_surjective e.surjective I n,
    (RingHom.injective_iff_ker_eq_bot (e : A →+* B)).mp e.injective, sup_bot_eq]

/-- When `A ⧸ I` is nontrivial (hence a local ring), its intrinsic Hilbert–Samuel function
`localQuotientHilbertSamuel (A ⧸ I) ⊥` agrees with `localQuotientHilbertSamuel A I`. -/
theorem localQuotientHilbertSamuel_quotient_bot (I : Ideal A) [IsLocalRing (A ⧸ I)] (n : ℕ) :
    localQuotientHilbertSamuel (A ⧸ I) ⊥ n = localQuotientHilbertSamuel A I n := by
  have hbot : (⊥ : Ideal A).map (Ideal.Quotient.mk I) = ⊥ := Ideal.map_bot
  rw [← hbot, localQuotientHilbertSamuel_map_of_surjective Ideal.Quotient.mk_surjective ⊥ n,
    Ideal.mk_ker, bot_sup_eq]

end Basic

section NoetherianAndCompletion

variable {A : Type*} [CommRing A] [IsLocalRing A]

/-- Over a Noetherian local ring, `A ⧸ (I ⊔ 𝔪_A ^ (n + 1))` has finite length over `A` for every
ideal `I` (including `I = ⊤`) and every `n : ℕ`. -/
theorem isFiniteLength_quotient_sup_maximalIdeal_pow [IsNoetherianRing A] (I : Ideal A) (n : ℕ) :
    IsFiniteLength A (A ⧸ (I ⊔ maximalIdeal A ^ (n + 1))) := by
  rw [← Module.length_ne_top_iff]
  refine ne_top_of_le_ne_top ?_ (length_quotient_anti le_sup_right)
  exact Module.length_ne_top_iff.mpr (isFiniteLength_quotient_maximalIdeal_pow (n + 1))

/-- Over a Noetherian local ring, `localQuotientHilbertSamuel A I n` is finite for every ideal `I`
and every `n : ℕ`. -/
theorem localQuotientHilbertSamuel_ne_top [IsNoetherianRing A] (I : Ideal A) (n : ℕ) :
    localQuotientHilbertSamuel A I n ≠ ⊤ :=
  Module.length_ne_top_iff.mpr (isFiniteLength_quotient_sup_maximalIdeal_pow I n)

/-- Over a Noetherian local ring, `localQuotientHilbertSamuel A I n` is strictly less than `⊤`. -/
theorem localQuotientHilbertSamuel_lt_top [IsNoetherianRing A] (I : Ideal A) (n : ℕ) :
    localQuotientHilbertSamuel A I n < ⊤ :=
  (localQuotientHilbertSamuel_ne_top I n).lt_top

/-- Over a Noetherian local ring, casting `(localQuotientHilbertSamuel A I n).toNat` back to `ℕ∞`
recovers `localQuotientHilbertSamuel A I n`. -/
@[simp]
theorem natCast_toNat_localQuotientHilbertSamuel [IsNoetherianRing A] (I : Ideal A) (n : ℕ) :
    ((localQuotientHilbertSamuel A I n).toNat : ℕ∞) = localQuotientHilbertSamuel A I n :=
  ENat.natCast_toNat (localQuotientHilbertSamuel_ne_top I n)

/-- **Completion invariance (finitely generated maximal ideal)**: if `𝔪_A` is finitely generated,
extending `I` to `AdicCompletion 𝔪_A A` preserves `localQuotientHilbertSamuel` at every order `n`.
-/
theorem localQuotientHilbertSamuel_adicCompletion_of_fg (hfg : (maximalIdeal A).FG)
    (I : Ideal A) (n : ℕ) :
    haveI := AdicCompletion.isLocalRing_of_fg hfg
    localQuotientHilbertSamuel (AdicCompletion (maximalIdeal A) A)
        (I.map (algebraMap A (AdicCompletion (maximalIdeal A) A))) n =
      localQuotientHilbertSamuel A I n := by
  have := AdicCompletion.isLocalRing_of_fg hfg
  let 𝔪 := maximalIdeal A
  let ψ : AdicCompletion 𝔪 A →+* A ⧸ 𝔪 ^ (n + 1) := (AdicCompletion.evalₐ 𝔪 (n + 1)).toRingHom
  have hψ : Function.Surjective ψ := AdicCompletion.surjective_evalₐ 𝔪 (n + 1)
  have hker : RingHom.ker ψ = maximalIdeal (AdicCompletion 𝔪 A) ^ (n + 1) := by
    rw [AdicCompletion.maximalIdeal_eq_map_of_fg hfg, ← Ideal.map_pow]
    exact AdicCompletion.ker_evalₐ_eq_map_pow hfg (n + 1)
  have hmap : (I.map (algebraMap A (AdicCompletion 𝔪 A))).map ψ =
      I.map (Ideal.Quotient.mk (𝔪 ^ (n + 1))) := by
    rw [Ideal.map_map]
    exact congrArg (Ideal.map · I) (RingHom.ext (AdicCompletion.evalₐ_of 𝔪 (n + 1)))
  rw [localQuotientHilbertSamuel_def, localQuotientHilbertSamuel_def, ← hker,
    ← Ideal.length_quotient_map_of_surjective _ hψ, hmap,
    Ideal.length_quotient_map_of_surjective _ Ideal.Quotient.mk_surjective, Ideal.mk_ker]

/-- **Completion invariance**: over a Noetherian local ring `A`, extending `I` to the `𝔪_A`-adic
completion preserves `localQuotientHilbertSamuel` at every order `n`. -/
@[simp]
theorem localQuotientHilbertSamuel_adicCompletion [IsNoetherianRing A] (I : Ideal A) (n : ℕ) :
    localQuotientHilbertSamuel (AdicCompletion (maximalIdeal A) A)
        (I.map (algebraMap A (AdicCompletion (maximalIdeal A) A))) n =
      localQuotientHilbertSamuel A I n :=
  localQuotientHilbertSamuel_adicCompletion_of_fg (maximalIdeal A).fg_of_isNoetherianRing I n

/-- A Noetherian local ring and its `𝔪_A`-adic completion have the same Hilbert–Samuel function at
`I = ⊥`. -/
@[simp]
theorem localQuotientHilbertSamuel_adicCompletion_bot [IsNoetherianRing A] (n : ℕ) :
    localQuotientHilbertSamuel (AdicCompletion (maximalIdeal A) A) ⊥ n =
      localQuotientHilbertSamuel A ⊥ n := by
  simpa only [Ideal.map_bot] using localQuotientHilbertSamuel_adicCompletion (A := A) ⊥ n

end NoetherianAndCompletion

section FieldAlgebra

variable (k : Type*) {A : Type*} [Field k] [CommRing A] [IsLocalRing A] [Algebra k A]

/-- For a local `k`-algebra `A`, the `k`-dimension of `A ⧸ (I ⊔ 𝔪_A ^ (n + 1))` equals
`(localQuotientHilbertSamuel A I n).toNat * [κ(A) : k]`. -/
theorem finrank_quotient_sup_maximalIdeal_pow (I : Ideal A) (n : ℕ) :
    Module.finrank k (A ⧸ (I ⊔ maximalIdeal A ^ (n + 1))) =
      (localQuotientHilbertSamuel A I n).toNat * Module.finrank k (ResidueField A) :=
  finrank_eq_length_mul_finrank_residueField k A (A ⧸ (I ⊔ maximalIdeal A ^ (n + 1)))

/-- When the residue field of a local `k`-algebra `A` is generated over `k` by `algebraMap k _`,
every `A`-module has the same length over `A` as over `k`. -/
theorem length_eq_length_field_of_surjective_algebraMap_residueField
    (hsurj : Function.Surjective (algebraMap k (ResidueField A)))
    (M : Type*) [AddCommGroup M] [Module A M] [Module k M] [IsScalarTower k A M] :
    Module.length A M = Module.length k M := by
  have h := IsLocalRing.length_restrictScalars k A M
  rw [← Module.length_eq_of_surjective (S := k) (R := ResidueField k) (M := ResidueField A)
      IsLocalRing.residue_surjective,
    Module.length_eq_of_surjective (S := k) (R := ResidueField A) (M := ResidueField A) hsurj,
    Module.length_eq_one (ResidueField A) (ResidueField A), mul_one] at h
  exact h.symm

/-- When `algebraMap k (ResidueField A)` is surjective, `localQuotientHilbertSamuel A I n` equals
the `k`-module length of `A ⧸ (I ⊔ 𝔪_A ^ (n + 1))`. -/
theorem localQuotientHilbertSamuel_eq_length_field
    (hsurj : Function.Surjective (algebraMap k (ResidueField A))) (I : Ideal A) (n : ℕ) :
    localQuotientHilbertSamuel A I n =
      Module.length k (A ⧸ (I ⊔ maximalIdeal A ^ (n + 1))) :=
  length_eq_length_field_of_surjective_algebraMap_residueField k hsurj _

end FieldAlgebra

end TauCeti
