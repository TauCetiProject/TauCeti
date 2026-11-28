/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.AdicCompletion.LocalRing
public import TauCeti.RingTheory.Length

import TauCeti.RingTheory.AdicCompletion.Algebra

/-!
# The Hilbert–Samuel function of a quotient of a local ring

For a local ring `(A, 𝔪)` and an ideal `I` of `A`, `I.localQuotientHilbertSamuel n` is the length
over `A` of `A ⧸ (I + 𝔪 ^ (n + 1))`. When `I` is proper, `B = A ⧸ I` is local and this is the
Hilbert–Samuel function `n ↦ ℓ_B(B ⧸ 𝔪_B ^ (n + 1))` of `B`
(`Ideal.localQuotientHilbertSamuel_bot_quotient`). For the unit ideal it vanishes identically.
Indexing by ideals of a fixed ambient local ring keeps the unit ideal in scope and lets the
functions of different ideals of the same ring be compared, which is how they are used to
measure singularities of closed subschemes of a fixed regular ambient space.

The values lie in `ℕ∞` and are finite when `A` is noetherian. The function is monotone in `n` and
antitone in `I`, its value at `n` only depends on `I + 𝔪 ^ (n + 1)`, and for a proper ideal its
value at `0` is `1`. Lengths are taken over the local ring: at a closed point whose residue field
has degree two over a ground field `k`, the value at `0` is still `1`, not `2`.

The function only sees the jets `A ⧸ 𝔪 ^ (n + 1)` of `A`. A ring homomorphism `A → B` into a local
ring that induces isomorphisms `A ⧸ 𝔪 ^ (n + 1) ≃ B ⧸ 𝔪_B ^ (n + 1)` therefore carries the function
of `I` to that of the extended ideal `I B`. In particular a noetherian local ring and its
`𝔪`-adic completion `Â` have the same Hilbert–Samuel functions: the value at `n` of `I` equals that
of `I Â`. This links the Hilbert–Samuel function of a local ring to computations in complete local
rings, such as formal power series rings over a field.

## Main definitions

* `Ideal.localQuotientHilbertSamuel I n`: the length of `A ⧸ (I ⊔ 𝔪 ^ (n + 1))` over `A`.

## Main results

* `Ideal.localQuotientHilbertSamuel_ne_top`: over a noetherian local ring the values are finite.
* `Ideal.localQuotientHilbertSamuel_eq_zero_iff`: a value vanishes exactly for the unit ideal.
* `Ideal.localQuotientHilbertSamuel_zero`: the value at `0` of a proper ideal is `1`.
* `Ideal.localQuotientHilbertSamuel_bot_quotient`: for a proper ideal `I`, the function of `I` is
  the Hilbert–Samuel function of the local ring `A ⧸ I`.
* `Ideal.localQuotientHilbertSamuel_map_of_surjective`: a ring homomorphism `A → B` of local rings
  inducing an isomorphism `A ⧸ 𝔪 ^ (n + 1) ≃ B ⧸ 𝔪_B ^ (n + 1)` preserves the value at `n`.
* `Ideal.localQuotientHilbertSamuel_map_algebraMap_adicCompletion`: completion preserves the
  Hilbert–Samuel function of every ideal of a noetherian local ring.

## References

* Edward Bierstone and Pierre D. Milman, *Canonical desingularization in characteristic zero by
  blowing up the maximum strata of a local invariant*, Invent. Math. 128 (1997), 207–302,
  Remarks 1.3, pp. 213–214, and Corollary 3.20, p. 239.
* H. Matsumura, *Commutative Ring Theory*, §13.
-/

public section

namespace Ideal

open IsLocalRing

variable {A : Type*} [CommRing A] [IsLocalRing A]

/-- The Hilbert–Samuel function of the quotient of a local ring `(A, 𝔪)` by an ideal `I`: its
value at `n` is the length over `A` of `A ⧸ (I + 𝔪 ^ (n + 1))`. It vanishes for `I = ⊤`; for a
proper ideal it is the Hilbert–Samuel function of the local ring `A ⧸ I`. -/
noncomputable def localQuotientHilbertSamuel (I : Ideal A) (n : ℕ) : ℕ∞ :=
  Module.length A (A ⧸ (I ⊔ maximalIdeal A ^ (n + 1)))

theorem localQuotientHilbertSamuel_def (I : Ideal A) (n : ℕ) :
    I.localQuotientHilbertSamuel n = Module.length A (A ⧸ (I ⊔ maximalIdeal A ^ (n + 1))) :=
  (rfl)

/-- The Hilbert–Samuel function of the zero ideal is that of the local ring itself. -/
theorem localQuotientHilbertSamuel_bot (n : ℕ) :
    (⊥ : Ideal A).localQuotientHilbertSamuel n =
      Module.length A (A ⧸ maximalIdeal A ^ (n + 1)) := by
  rw [localQuotientHilbertSamuel_def, bot_sup_eq]

/-- A value of the Hilbert–Samuel function vanishes exactly for the unit ideal, whose quotient is
the zero ring. -/
@[simp]
theorem localQuotientHilbertSamuel_eq_zero_iff {I : Ideal A} {n : ℕ} :
    I.localQuotientHilbertSamuel n = 0 ↔ I = ⊤ := by
  rw [localQuotientHilbertSamuel_def, Module.length_eq_zero_iff,
    Submodule.Quotient.subsingleton_iff]
  refine ⟨fun h ↦ ?_, fun h ↦ by rw [h, top_sup_eq]⟩
  by_contra hI
  refine (maximalIdeal.isMaximal A).ne_top (top_le_iff.mp (h ▸ sup_le (le_maximalIdeal hI) ?_))
  exact pow_le_self n.succ_ne_zero

@[simp]
theorem localQuotientHilbertSamuel_top (n : ℕ) : (⊤ : Ideal A).localQuotientHilbertSamuel n = 0 :=
  localQuotientHilbertSamuel_eq_zero_iff.mpr rfl

/-- The Hilbert–Samuel function of a proper ideal takes the value `1` at `0`: the quotient by
`I + 𝔪 = 𝔪` is the residue field. -/
theorem localQuotientHilbertSamuel_zero {I : Ideal A} (hI : I ≠ ⊤) :
    I.localQuotientHilbertSamuel 0 = 1 := by
  rw [localQuotientHilbertSamuel_def, zero_add, pow_one, sup_eq_right.mpr (le_maximalIdeal hI)]
  exact length_quotient_eq_one _

/-- The Hilbert–Samuel function is monotone. -/
theorem localQuotientHilbertSamuel_monotone (I : Ideal A) : Monotone I.localQuotientHilbertSamuel :=
  fun _ _ h ↦ TauCeti.length_quotient_anti
    (sup_le_sup_left (pow_le_pow_right (Nat.succ_le_succ h)) I)

/-- Enlarging the ideal can only decrease its Hilbert–Samuel function. -/
theorem localQuotientHilbertSamuel_anti {I J : Ideal A} (h : I ≤ J) (n : ℕ) :
    J.localQuotientHilbertSamuel n ≤ I.localQuotientHilbertSamuel n :=
  TauCeti.length_quotient_anti (sup_le_sup_right h _)

/-- The value at `n` only depends on `I + 𝔪 ^ (n + 1)`: adding a power `𝔪 ^ k` with `n < k`
does not change it. -/
theorem localQuotientHilbertSamuel_sup_maximalIdeal_pow (I : Ideal A) {k n : ℕ} (h : n < k) :
    (I ⊔ maximalIdeal A ^ k).localQuotientHilbertSamuel n = I.localQuotientHilbertSamuel n := by
  rw [localQuotientHilbertSamuel_def, localQuotientHilbertSamuel_def, sup_assoc,
    sup_eq_right.mpr (pow_le_pow_right h : maximalIdeal A ^ k ≤ maximalIdeal A ^ (n + 1))]

/-- Over a noetherian local ring every value of the Hilbert–Samuel function is finite. -/
theorem localQuotientHilbertSamuel_ne_top [IsNoetherianRing A] (I : Ideal A) (n : ℕ) :
    I.localQuotientHilbertSamuel n ≠ ⊤ :=
  ne_top_of_le_ne_top
    (Module.length_ne_top_iff.mpr (TauCeti.isFiniteLength_quotient_maximalIdeal_pow (n + 1)))
    (TauCeti.length_quotient_anti le_sup_right)

/-- For a proper ideal `I`, the Hilbert–Samuel function of `I` is that of the local ring
`A ⧸ I`, measured by lengths over `A ⧸ I`. -/
@[simp]
theorem localQuotientHilbertSamuel_bot_quotient (I : Ideal A) [IsLocalRing (A ⧸ I)] (n : ℕ) :
    (⊥ : Ideal (A ⧸ I)).localQuotientHilbertSamuel n = I.localQuotientHilbertSamuel n := by
  rw [localQuotientHilbertSamuel_bot,
    ← map_maximalIdeal_of_surjective (Quotient.mk I) Quotient.mk_surjective, ← Ideal.map_pow,
    length_quotient_map_of_surjective _ Quotient.mk_surjective, mk_ker, sup_comm,
    localQuotientHilbertSamuel_def]

/-- **Invariance under maps inducing isomorphisms of jets.** Let `f : A → B` be a ring
homomorphism into a local ring such that the composite `A → B ⧸ 𝔪_B ^ (n + 1)` is surjective with
kernel `𝔪_A ^ (n + 1)`, that is, `f` induces an isomorphism `A ⧸ 𝔪_A ^ (n + 1) ≃ B ⧸ 𝔪_B ^ (n + 1)`.
Then the Hilbert–Samuel function of the extended ideal `I B` takes the same value at `n` as that
of `I`. -/
theorem localQuotientHilbertSamuel_map_of_surjective {B : Type*} [CommRing B] [IsLocalRing B]
    (f : A →+* B) {n : ℕ}
    (hf : Function.Surjective ((Quotient.mk (maximalIdeal B ^ (n + 1))).comp f))
    (hker : (maximalIdeal B ^ (n + 1)).comap f = maximalIdeal A ^ (n + 1)) (I : Ideal A) :
    (I.map f).localQuotientHilbertSamuel n = I.localQuotientHilbertSamuel n := by
  have hker' : RingHom.ker ((Quotient.mk (maximalIdeal B ^ (n + 1))).comp f) =
      maximalIdeal A ^ (n + 1) := by
    rw [← hker, ← RingHom.comap_ker, mk_ker]
  -- Both sides are lengths of quotients of `B ⧸ 𝔪_B ^ (n + 1)`, which `A` surjects onto.
  rw [localQuotientHilbertSamuel_def, localQuotientHilbertSamuel_def,
    ← mk_ker (I := maximalIdeal B ^ (n + 1)),
    ← length_quotient_map_of_surjective _ Quotient.mk_surjective, map_map,
    length_quotient_map_of_surjective _ hf, hker']

/-- **Completion preserves the Hilbert–Samuel function.** For an ideal `I` of a noetherian local
ring `A` with `𝔪`-adic completion `Â`, the Hilbert–Samuel function of the extended ideal `I Â`
agrees with that of `I`: both measure `A ⧸ (I + 𝔪 ^ (n + 1)) ≃ Â ⧸ (I Â + 𝔪_Â ^ (n + 1))`. -/
@[simp]
theorem localQuotientHilbertSamuel_map_algebraMap_adicCompletion [IsNoetherianRing A]
    (I : Ideal A) (n : ℕ) :
    (I.map (algebraMap A (AdicCompletion (maximalIdeal A) A))).localQuotientHilbertSamuel n =
      I.localQuotientHilbertSamuel n := by
  have fg := (maximalIdeal A).fg_of_isNoetherianRing
  refine localQuotientHilbertSamuel_map_of_surjective _ (fun x ↦ ?_) ?_ I
  · obtain ⟨x, rfl⟩ := Quotient.mk_surjective x
    obtain ⟨y, hy⟩ := AdicCompletion.exists_sub_algebraMap_mem_map_pow fg (n + 1) x
    rw [Ideal.map_pow, ← AdicCompletion.maximalIdeal_eq_map] at hy
    exact ⟨y, (Quotient.eq.mpr hy).symm⟩
  · ext a
    rw [mem_comap, AdicCompletion.maximalIdeal_eq_map, ← Ideal.map_pow,
      AdicCompletion.algebraMap_mem_map_pow_iff]

end Ideal
