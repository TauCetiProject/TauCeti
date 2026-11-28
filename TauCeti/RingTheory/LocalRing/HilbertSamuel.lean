/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Length

import Mathlib.RingTheory.TensorProduct.Quotient

/-!
# The Hilbert–Samuel function of a quotient of a local ring

For a local ring `(A, 𝔪)` and an ideal `I` of `A`, `I.localQuotientHilbertSamuel n` is the length
over `A` of `A ⧸ (I + 𝔪 ^ (n + 1))`. When `I` is proper, `B = A ⧸ I` is local and this is the
Hilbert–Samuel function `n ↦ ℓ_B(B ⧸ 𝔪_B ^ (n + 1))` of `B`
(`Ideal.localQuotientHilbertSamuel_bot_quotient`). For the unit ideal it vanishes identically
(`Ideal.localQuotientHilbertSamuel_top`), while for `I = 𝔪` every value equals `1`
(`Ideal.localQuotientHilbertSamuel_maximalIdeal`) and adjoining `𝔪 ^ (k + 1)` truncates the
function at `min k n` (`Ideal.localQuotientHilbertSamuel_sup_maximalIdeal_pow_succ`,
`Ideal.localQuotientHilbertSamuel_maximalIdeal_pow_succ`). Indexing by ideals of a fixed ambient
local ring keeps the unit ideal in scope and lets the functions of different ideals of the same ring
be compared, which is how they are used to measure singularities of closed subschemes of a fixed
regular ambient space.

The values lie in `ℕ∞` and are finite when `A` is noetherian
(`Ideal.localQuotientHilbertSamuel_ne_top`, `Ideal.localQuotientHilbertSamuel_lt_top`,
`Ideal.natCast_toNat_localQuotientHilbertSamuel`). The function is monotone in `n` and antitone in
`I`, its value at `n` only depends on `I + 𝔪 ^ (n + 1)`, and for a proper ideal its value at `0`
is `1`. Lengths are taken over the local ring: at a closed point whose residue field has degree two
over a ground field `k`, the value at `0` is still `1`, not `2`
(`TauCeti.length_quotient_sup_maximalIdeal_pow_eq_mul_length_residueField`). Along any surjective
local ring homomorphism `f : A → B`, computing `localQuotientHilbertSamuel` at `I.map f` on `B`
agrees with computing it at `RingHom.ker f ⊔ I` on `A`
(`Ideal.localQuotientHilbertSamuel_map_eq_ker_sup_of_surjective`), specializing to local quotients
and ring or algebra equivalences (`Ideal.localQuotientHilbertSamuel_map_equiv`,
`Ideal.localQuotientHilbertSamuel_comap_equiv`). Along any flat extension of local rings `A → B`
with `𝔪_A B = 𝔪_B`, flat base change of lengths (`IsLocalRing.length_baseChange`) shows that
extending `I` to `B` preserves every value of the Hilbert–Samuel function without any noetherian
hypothesis (`Ideal.localQuotientHilbertSamuel_map_of_flat_of_map_maximalIdeal_eq`).

The function only sees the jets `A ⧸ 𝔪 ^ (n + 1)` of `A`. A ring homomorphism `A → B` into a local
ring that induces isomorphisms `A ⧸ 𝔪 ^ (n + 1) ≃ B ⧸ 𝔪_B ^ (n + 1)` therefore carries the function
of `I` to that of the extended ideal `I B` (`Ideal.localQuotientHilbertSamuel_map_of_surjective`),
which applies in particular to the `𝔪`-adic completion `Â` of a noetherian local ring. This links
the Hilbert–Samuel function of a local ring to computations in complete local rings, such as formal
power series rings over a field.

## Main definitions

* `Ideal.localQuotientHilbertSamuel I n`: the length of `A ⧸ (I ⊔ 𝔪 ^ (n + 1))` over `A`.

## Main results

* `Ideal.localQuotientHilbertSamuel_ne_top`, `Ideal.localQuotientHilbertSamuel_lt_top`,
  `Ideal.natCast_toNat_localQuotientHilbertSamuel`: over a noetherian local ring the values are
  finite.
* `Ideal.localQuotientHilbertSamuel_eq_zero_iff`, `Ideal.localQuotientHilbertSamuel_pos_iff`: a
  value vanishes exactly for the unit ideal.
* `Ideal.localQuotientHilbertSamuel_zero`, `Ideal.localQuotientHilbertSamuel_bot_zero`,
  `Ideal.localQuotientHilbertSamuel_maximalIdeal`: the value at `0` of a proper ideal is `1`, and
  `H_{A/𝔪}(n) = 1` for all `n`.
* `Ideal.localQuotientHilbertSamuel_monotone`, `Ideal.localQuotientHilbertSamuel_anti`,
  `Ideal.localQuotientHilbertSamuel_sup_maximalIdeal_pow`,
  `Ideal.localQuotientHilbertSamuel_sup_maximalIdeal_pow_succ`,
  `Ideal.localQuotientHilbertSamuel_maximalIdeal_pow_succ`, `Ideal.localQuotientHilbertSamuel_succ`:
  monotonicity in `n`, antitonicity in `I`, truncation by powers of `𝔪`, and the one-step
  filtration identity.
* `Ideal.localQuotientHilbertSamuel_map_eq_ker_sup_of_surjective`,
  `Ideal.localQuotientHilbertSamuel_quotient_map`,
  `Ideal.localQuotientHilbertSamuel_bot_quotient`,
  `Ideal.localQuotientHilbertSamuel_map_equiv`, `Ideal.localQuotientHilbertSamuel_comap_equiv`,
  `TauCeti.localQuotientHilbertSamuel_bot_of_equiv`: compatibility with surjective local ring
  homomorphisms, local quotients `A ⧸ I`, and ring/algebra equivalences.
* `TauCeti.length_quotient_sup_maximalIdeal_pow_eq_mul_length_residueField`: comparison between
  `A`-length and local base-ring length via the residue-field length.
* `Ideal.localQuotientHilbertSamuel_map_of_flat_of_map_maximalIdeal_eq`: invariance under flat
  local extensions with `𝔪_A B = 𝔪_B`.
* `Ideal.localQuotientHilbertSamuel_map_of_surjective`: a ring homomorphism `A → B` of local rings
  inducing an isomorphism `A ⧸ 𝔪 ^ (n + 1) ≃ B ⧸ 𝔪_B ^ (n + 1)` preserves the value at `n`.

## References

* Edward Bierstone and Pierre D. Milman, *Canonical desingularization in characteristic zero by
  blowing up the maximum strata of a local invariant*, Invent. Math. 128 (1997), 207–302, §1
  (Remarks 1.3, pp. 213–214), §3 (Corollary 3.20, p. 239), and §9 (p. 276).
* H. Matsumura, *Commutative Ring Theory*, §13.
-/

public section

namespace Ideal

open IsLocalRing

section Basic

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

/-- `0 < I.localQuotientHilbertSamuel n` if and only if `I` is a proper ideal. -/
@[simp]
theorem localQuotientHilbertSamuel_pos_iff {I : Ideal A} {n : ℕ} :
    0 < I.localQuotientHilbertSamuel n ↔ I ≠ ⊤ := by
  rw [pos_iff_ne_zero, not_iff_not, localQuotientHilbertSamuel_eq_zero_iff]

@[simp]
theorem localQuotientHilbertSamuel_top (n : ℕ) : (⊤ : Ideal A).localQuotientHilbertSamuel n = 0 :=
  localQuotientHilbertSamuel_eq_zero_iff.mpr rfl

/-- The Hilbert–Samuel function of a proper ideal takes the value `1` at `0`: the quotient by
`I + 𝔪 = 𝔪` is the residue field. -/
theorem localQuotientHilbertSamuel_zero {I : Ideal A} (hI : I ≠ ⊤) :
    I.localQuotientHilbertSamuel 0 = 1 := by
  rw [localQuotientHilbertSamuel_def, zero_add, pow_one, sup_eq_right.mpr (le_maximalIdeal hI)]
  exact length_quotient_eq_one _

/-- At degree `0`, the Hilbert–Samuel function of a local ring `A` itself (`I = ⊥`) equals `1`. -/
@[simp]
theorem localQuotientHilbertSamuel_bot_zero :
    (⊥ : Ideal A).localQuotientHilbertSamuel 0 = 1 :=
  localQuotientHilbertSamuel_zero bot_ne_top

/-- For the maximal ideal `𝔪` of a local ring `A`, every Hilbert–Samuel value equals `1`. -/
@[simp]
theorem localQuotientHilbertSamuel_maximalIdeal (n : ℕ) :
    (maximalIdeal A).localQuotientHilbertSamuel n = 1 := by
  rw [localQuotientHilbertSamuel_def, sup_eq_left.mpr (pow_le_self n.succ_ne_zero),
    length_quotient_eq_one]

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

/-- Adjoining `𝔪 ^ (k + 1)` to `I` truncates `I.localQuotientHilbertSamuel` at degree
`min k n`. -/
theorem localQuotientHilbertSamuel_sup_maximalIdeal_pow_succ (I : Ideal A) (k n : ℕ) :
    (I ⊔ maximalIdeal A ^ (k + 1)).localQuotientHilbertSamuel n =
      I.localQuotientHilbertSamuel (min k n) := by
  rw [localQuotientHilbertSamuel_def, localQuotientHilbertSamuel_def, sup_assoc]
  refine congrArg (fun J ↦ Module.length A (A ⧸ (I ⊔ J))) ?_
  rcases le_total k n with hkn | hnk
  · rw [min_eq_left hkn, sup_eq_left.mpr (pow_le_pow_right (Nat.add_le_add_right hkn 1))]
  · rw [min_eq_right hnk, sup_eq_right.mpr (pow_le_pow_right (Nat.add_le_add_right hnk 1))]

/-- For `𝔪 ^ (k + 1)`, the Hilbert–Samuel value at degree `n` agrees with that of `⊥` at degree
`min k n`. -/
theorem localQuotientHilbertSamuel_maximalIdeal_pow_succ (k n : ℕ) :
    (maximalIdeal A ^ (k + 1)).localQuotientHilbertSamuel n =
      (⊥ : Ideal A).localQuotientHilbertSamuel (min k n) := by
  rw [← bot_sup_eq (maximalIdeal A ^ (k + 1)), localQuotientHilbertSamuel_sup_maximalIdeal_pow_succ]

/-- Filtration step: `H_{A/I}(n + 1)` equals `H_{A/I}(n)` plus the length of the image of
`𝔪 ^ (n + 1)` in `A ⧸ (I + 𝔪 ^ (n + 2))`. -/
theorem localQuotientHilbertSamuel_succ (I : Ideal A) (n : ℕ) :
    I.localQuotientHilbertSamuel (n + 1) =
      I.localQuotientHilbertSamuel n +
        Module.length A
          (Submodule.map (I ⊔ maximalIdeal A ^ (n + 2)).mkQ (maximalIdeal A ^ (n + 1))) := by
  have hsup : (I ⊔ maximalIdeal A ^ (n + 2)) ⊔ maximalIdeal A ^ (n + 1) =
      I ⊔ maximalIdeal A ^ (n + 1) := by
    rw [sup_assoc]
    exact congrArg (I ⊔ ·) (sup_eq_right.mpr (pow_le_pow_right (Nat.le_succ (n + 1))))
  rw [localQuotientHilbertSamuel_def, localQuotientHilbertSamuel_def,
    TauCeti.length_quotient_eq_length_map_add_length_quotient_sup (maximalIdeal A ^ (n + 1))
      (I ⊔ maximalIdeal A ^ (n + 2)),
    hsup, add_comm]

/-- Along any surjective homomorphism `f : A → B` between local rings, computing
`localQuotientHilbertSamuel` on `B` at `I.map f` agrees with computing it on `A` at
`RingHom.ker f ⊔ I`. -/
theorem localQuotientHilbertSamuel_map_eq_ker_sup_of_surjective {B F : Type*}
    [CommRing B] [IsLocalRing B] [FunLike F A B] [RingHomClass F A B]
    (I : Ideal A) {f : F} (hf : Function.Surjective f) (n : ℕ) :
    (I.map f).localQuotientHilbertSamuel n =
      (RingHom.ker f ⊔ I).localQuotientHilbertSamuel n := by
  have hmap : I.map f ⊔ maximalIdeal B ^ (n + 1) =
      (I ⊔ maximalIdeal A ^ (n + 1)).map f := by
    rw [← map_maximalIdeal_of_surjective (f : A →+* B) hf, ← Ideal.map_pow, Ideal.map_coe,
      ← Ideal.map_sup]
  rw [localQuotientHilbertSamuel_def, hmap, length_quotient_map_of_surjective _ hf,
    sup_comm _ (RingHom.ker f), ← sup_assoc, localQuotientHilbertSamuel_def]

/-- Computing `localQuotientHilbertSamuel` on a local quotient `A ⧸ I` at `J.map (Quotient.mk I)`
agrees with computing it on `A` at `I ⊔ J`. -/
@[simp]
theorem localQuotientHilbertSamuel_quotient_map (I J : Ideal A) [IsLocalRing (A ⧸ I)] (n : ℕ) :
    (J.map (Quotient.mk I)).localQuotientHilbertSamuel n =
      (I ⊔ J).localQuotientHilbertSamuel n := by
  rw [localQuotientHilbertSamuel_map_eq_ker_sup_of_surjective J Quotient.mk_surjective, mk_ker]

/-- For a proper ideal `I`, the Hilbert–Samuel function of `I` is that of the local ring
`A ⧸ I`, measured by lengths over `A ⧸ I`. -/
@[simp]
theorem localQuotientHilbertSamuel_bot_quotient (I : Ideal A) [IsLocalRing (A ⧸ I)] (n : ℕ) :
    (⊥ : Ideal (A ⧸ I)).localQuotientHilbertSamuel n = I.localQuotientHilbertSamuel n := by
  simpa only [Ideal.map_bot, sup_bot_eq] using
    localQuotientHilbertSamuel_quotient_map I (⊥ : Ideal A) n

/-- Any ring equivalence `e : A ≃+* B` (or algebra equivalence, via `RingEquivClass`) between
local rings preserves `localQuotientHilbertSamuel` under `Ideal.map e`. -/
@[simp]
theorem localQuotientHilbertSamuel_map_equiv {B E : Type*}
    [CommRing B] [IsLocalRing B] [EquivLike E A B] [RingEquivClass E A B]
    (I : Ideal A) (e : E) (n : ℕ) :
    (I.map e).localQuotientHilbertSamuel n = I.localQuotientHilbertSamuel n := by
  rw [localQuotientHilbertSamuel_map_eq_ker_sup_of_surjective I (EquivLike.surjective e),
    RingHom.ker_equiv, bot_sup_eq]

/-- Any ring equivalence `e : A ≃+* B` (or algebra equivalence, via `RingEquivClass`) between
local rings preserves `localQuotientHilbertSamuel` under `Ideal.comap e`. -/
@[simp]
theorem localQuotientHilbertSamuel_comap_equiv {B E : Type*}
    [CommRing B] [IsLocalRing B] [EquivLike E A B] [RingEquivClass E A B]
    (J : Ideal B) (e : E) (n : ℕ) :
    (J.comap e).localQuotientHilbertSamuel n = J.localQuotientHilbertSamuel n := by
  rw [← localQuotientHilbertSamuel_map_equiv (J.comap e) e n,
    map_comap_of_surjective e (EquivLike.surjective e)]

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

end Basic

section Noetherian

variable {A : Type*} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]

/-- Over a noetherian local ring every value of the Hilbert–Samuel function is finite. -/
@[simp]
theorem localQuotientHilbertSamuel_ne_top (I : Ideal A) (n : ℕ) :
    I.localQuotientHilbertSamuel n ≠ ⊤ :=
  Module.length_ne_top_iff.mpr (I.isFiniteLength_quotient_sup_maximalIdeal_pow (n + 1))

/-- Over a noetherian local ring `A`, every value of `I.localQuotientHilbertSamuel` is strictly
less than `⊤`. -/
@[simp]
theorem localQuotientHilbertSamuel_lt_top (I : Ideal A) (n : ℕ) :
    I.localQuotientHilbertSamuel n < ⊤ :=
  lt_top_iff_ne_top.mpr (localQuotientHilbertSamuel_ne_top I n)

/-- Over a noetherian local ring `A`, `I.localQuotientHilbertSamuel n` equals the coercion of its
`ℕ`-value `(I.localQuotientHilbertSamuel n).toNat`. -/
@[simp]
theorem natCast_toNat_localQuotientHilbertSamuel (I : Ideal A) (n : ℕ) :
    ((I.localQuotientHilbertSamuel n).toNat : ℕ∞) = I.localQuotientHilbertSamuel n :=
  ENat.natCast_toNat (localQuotientHilbertSamuel_ne_top I n)

end Noetherian

section Flat

/-- Along a flat homomorphism `A → B` of local rings such that `𝔪_A B = 𝔪_B`, extending `I` to `B`
preserves every value of `localQuotientHilbertSamuel`. -/
theorem localQuotientHilbertSamuel_map_of_flat_of_map_maximalIdeal_eq
    {A B : Type*} [CommRing A] [IsLocalRing A] [CommRing B] [IsLocalRing B]
    [Algebra A B] [Module.Flat A B] (I : Ideal A)
    (hm : (maximalIdeal A).map (algebraMap A B) = maximalIdeal B) (n : ℕ) :
    (I.map (algebraMap A B)).localQuotientHilbertSamuel n = I.localQuotientHilbertSamuel n := by
  have : IsLocalHom (algebraMap A B) :=
    ((local_hom_tfae (algebraMap A B)).out 1 3).mpr hm.le
  have hmap : I.map (algebraMap A B) ⊔ maximalIdeal B ^ (n + 1) =
      (I ⊔ maximalIdeal A ^ (n + 1)).map (algebraMap A B) := by
    rw [← hm, ← Ideal.map_pow, ← Ideal.map_sup]
  have hlen : Module.length B (B ⧸ (maximalIdeal A).map (algebraMap A B)) = 1 := by
    rw [hm, length_quotient_eq_one]
  rw [localQuotientHilbertSamuel_def, hmap,
    (Algebra.TensorProduct.quotIdealMapEquivTensorQuot B
      (I ⊔ maximalIdeal A ^ (n + 1))).toLinearEquiv.length_eq,
    IsLocalRing.length_baseChange A B (A ⧸ (I ⊔ maximalIdeal A ^ (n + 1))),
    hlen, mul_one, localQuotientHilbertSamuel_def]

end Flat

end Ideal

namespace TauCeti

/-- Isomorphic local rings have the same intrinsic Hilbert–Samuel function (`I = ⊥`). -/
theorem localQuotientHilbertSamuel_bot_of_equiv {A B E : Type*}
    [CommRing A] [IsLocalRing A] [CommRing B] [IsLocalRing B]
    [EquivLike E A B] [RingEquivClass E A B] (e : E) (n : ℕ) :
    (⊥ : Ideal A).localQuotientHilbertSamuel n = (⊥ : Ideal B).localQuotientHilbertSamuel n := by
  rw [← Ideal.comap_bot_of_injective e (EquivLike.injective e),
    Ideal.localQuotientHilbertSamuel_comap_equiv]

/-- Over a local extension `K → A`, the `K`-length of `A ⧸ (I + 𝔪_A ^ (n + 1))` equals
`I.localQuotientHilbertSamuel n * Module.length K (ResidueField A)`. In particular, this applies
whenever `K` is a ground field. -/
theorem length_quotient_sup_maximalIdeal_pow_eq_mul_length_residueField
    (K A : Type*) [CommRing K] [IsLocalRing K] [CommRing A] [IsLocalRing A]
    [Algebra K A] [IsLocalHom (algebraMap K A)] (I : Ideal A) (n : ℕ) :
    Module.length K (A ⧸ (I ⊔ IsLocalRing.maximalIdeal A ^ (n + 1))) =
      I.localQuotientHilbertSamuel n * Module.length K (IsLocalRing.ResidueField A) := by
  rw [Ideal.localQuotientHilbertSamuel_def, IsLocalRing.length_restrictScalars K A,
    Module.length_eq_of_surjective (IsLocalRing.residue_surjective (R := K))]

end TauCeti
