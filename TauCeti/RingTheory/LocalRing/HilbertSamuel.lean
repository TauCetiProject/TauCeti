/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.AdicCompletion.LocalRing
public import Mathlib.RingTheory.Length
public import Mathlib.RingTheory.LocalRing.ResidueField.Defs
import Mathlib.RingTheory.AdicCompletion.AsTensorProduct
import Mathlib.RingTheory.LocalRing.Length
import Mathlib.RingTheory.TensorProduct.Quotient
import TauCeti.RingTheory.Length

/-!
# Local quotient Hilbert–Samuel functions

For a local commutative ring `(A, 𝔪)` and an ideal `I` of `A`, the *local quotient Hilbert–Samuel
function* `TauCeti.localQuotientHilbertSamuel A I : ℕ → ℕ∞` sends `n` to the `A`-module length of
`A ⧸ (I ⊔ 𝔪 ^ (n + 1))`. Measuring length over `A` (equivalently over `A ⧸ I` when `I` is proper,
`TauCeti.localQuotientHilbertSamuel_quotient_bot`) normalizes each simple composition factor to have
length `1`, rather than multiplying by the degree of the residue field over a local base ring or
ground field (`TauCeti.length_quotient_sup_maximalIdeal_pow_eq_mul_length_residueField`): in
particular, `H_{A/I}(0) = 1` for every proper ideal `I`
(`TauCeti.localQuotientHilbertSamuel_zero_of_ne_top`), even at non-rational closed points whose
residue field has degree greater than `1`. For `I = ⊤`, the quotient is zero and every value
vanishes (`TauCeti.localQuotientHilbertSamuel_top`), while for `I = 𝔪` every value equals `1`
(`TauCeti.localQuotientHilbertSamuel_maximalIdeal`) and adjoining `𝔪 ^ (k + 1)` truncates the
function at `min k n` (`TauCeti.localQuotientHilbertSamuel_sup_maximalIdeal_pow_succ`,
`TauCeti.localQuotientHilbertSamuel_maximalIdeal_pow_succ`).

When `A` is Noetherian, every quotient `A ⧸ (I ⊔ 𝔪 ^ n)` has finite length
(`Ideal.isFiniteLength_quotient_sup_maximalIdeal_pow`), so every value
`localQuotientHilbertSamuel A I n` is finite (`TauCeti.localQuotientHilbertSamuel_lt_top`,
`TauCeti.natCast_toNat_localQuotientHilbertSamuel`). Along any surjective local ring homomorphism
`f : A → B`, computing `localQuotientHilbertSamuel` at `I.map f` on `B` agrees with computing it at
`RingHom.ker f ⊔ I` on `A` (`TauCeti.localQuotientHilbertSamuel_map_of_surjective`), specializing
to both local quotients and ring or algebra equivalences
(`TauCeti.localQuotientHilbertSamuel_map_equiv`, `TauCeti.localQuotientHilbertSamuel_comap_equiv`).
Along any flat extension of local rings `A → B` with `𝔪_A B = 𝔪_B`, flat base change of lengths
(`IsLocalRing.length_baseChange`) shows that extending `I` to `B` preserves every value of the
Hilbert–Samuel function without any Noetherian hypothesis
(`TauCeti.localQuotientHilbertSamuel_map_of_flat_of_map_maximalIdeal_eq`). Specializing to the
`𝔪`-adic completion of a Noetherian local ring yields completion invariance
(`TauCeti.localQuotientHilbertSamuel_adicCompletion`).

## Main definitions

* `TauCeti.localQuotientHilbertSamuel`: `n ↦ Module.length A (A ⧸ (I ⊔ 𝔪 ^ (n + 1)))`.

## Main results

* `TauCeti.localQuotientHilbertSamuel_eq_zero_iff`,
  `TauCeti.localQuotientHilbertSamuel_zero_of_ne_top`,
  `TauCeti.localQuotientHilbertSamuel_maximalIdeal`: vanishing characterizes `I = ⊤`, every proper
  ideal satisfies `H_{A/I}(0) = 1`, and `H_{A/𝔪}(n) = 1` for all `n`.
* `TauCeti.localQuotientHilbertSamuel_mono`, `TauCeti.localQuotientHilbertSamuel_anti`,
  `TauCeti.localQuotientHilbertSamuel_sup_maximalIdeal_pow_succ`,
  `TauCeti.localQuotientHilbertSamuel_maximalIdeal_pow_succ`,
  `TauCeti.localQuotientHilbertSamuel_succ`: monotonicity in `n`, antitonicity in `I`, truncation by
  powers of `𝔪`, and the one-step filtration identity.
* `TauCeti.localQuotientHilbertSamuel_map_of_surjective`,
  `TauCeti.localQuotientHilbertSamuel_quotient_map`,
  `TauCeti.localQuotientHilbertSamuel_quotient_bot`,
  `TauCeti.localQuotientHilbertSamuel_map_equiv`,
  `TauCeti.localQuotientHilbertSamuel_comap_equiv`,
  `TauCeti.localQuotientHilbertSamuel_bot_of_equiv`: compatibility with surjective local ring
  homomorphisms, local quotients `A ⧸ I`, and ring/algebra equivalences.
* `TauCeti.length_quotient_sup_maximalIdeal_pow_restrictScalars`,
  `TauCeti.length_quotient_sup_maximalIdeal_pow_eq_mul_length_residueField`: comparison between
  `A`-length and local base-ring length via the residue-field length.
* `TauCeti.localQuotientHilbertSamuel_ne_top`,
  `TauCeti.localQuotientHilbertSamuel_lt_top`,
  `TauCeti.natCast_toNat_localQuotientHilbertSamuel`: finiteness over Noetherian local rings.
* `TauCeti.localQuotientHilbertSamuel_map_of_flat_of_map_maximalIdeal_eq`,
  `TauCeti.localQuotientHilbertSamuel_adicCompletion`,
  `TauCeti.localQuotientHilbertSamuel_adicCompletion_bot`: invariance under flat unramified local
  extensions and `𝔪`-adic completion.

## References

* Edward Bierstone and Pierre D. Milman, *Canonical desingularization in characteristic zero by
  blowing up the maximum strata of a local invariant*, Invent. Math. 128 (1997), 207–302, §1
  (Remarks 1.3, pp. 213–214), §3 (Corollary 3.20, p. 239), and §9 (p. 276).
* Hideyuki Matsumura, *Commutative Ring Theory*, Cambridge Studies in Advanced Mathematics 8,
  Cambridge University Press, 1986, §13.
-/

public section

namespace TauCeti

section Basic

variable (A : Type*) [CommRing A] [IsLocalRing A]

/-- The local quotient Hilbert–Samuel function `H_{A/I}(n) = length_A (A ⧸ (I + 𝔪 ^ (n + 1)))` of
an ideal `I` in a local commutative ring `(A, 𝔪)`. -/
noncomputable def localQuotientHilbertSamuel (I : Ideal A) (n : ℕ) : ℕ∞ :=
  Module.length A (A ⧸ (I ⊔ IsLocalRing.maximalIdeal A ^ (n + 1)))

variable {A}

theorem localQuotientHilbertSamuel_def (I : Ideal A) (n : ℕ) :
    localQuotientHilbertSamuel A I n =
      Module.length A (A ⧸ (I ⊔ IsLocalRing.maximalIdeal A ^ (n + 1))) := (rfl)

/-- For the unit ideal `⊤`, the quotient is zero and every Hilbert–Samuel value vanishes. -/
@[simp]
theorem localQuotientHilbertSamuel_top (n : ℕ) :
    localQuotientHilbertSamuel A (⊤ : Ideal A) n = 0 := by
  simp [localQuotientHilbertSamuel_def]

/-- `localQuotientHilbertSamuel A I n = 0` if and only if `I = ⊤`. -/
@[simp]
theorem localQuotientHilbertSamuel_eq_zero_iff {I : Ideal A} {n : ℕ} :
    localQuotientHilbertSamuel A I n = 0 ↔ I = ⊤ := by
  rw [localQuotientHilbertSamuel_def, Module.length_eq_zero_iff,
    Submodule.Quotient.subsingleton_iff]
  refine ⟨fun h ↦ ?_, fun h ↦ by simp [h]⟩
  by_contra hI
  have hle : I ⊔ IsLocalRing.maximalIdeal A ^ (n + 1) ≤ IsLocalRing.maximalIdeal A :=
    sup_le (IsLocalRing.le_maximalIdeal hI) (Ideal.pow_le_self (Nat.succ_ne_zero n))
  exact (IsLocalRing.maximalIdeal.isMaximal A).ne_top (top_unique (h ▸ hle))

/-- `0 < localQuotientHilbertSamuel A I n` if and only if `I` is a proper ideal. -/
@[simp]
theorem localQuotientHilbertSamuel_pos_iff {I : Ideal A} {n : ℕ} :
    0 < localQuotientHilbertSamuel A I n ↔ I ≠ ⊤ := by
  rw [pos_iff_ne_zero, not_iff_not, localQuotientHilbertSamuel_eq_zero_iff]

/-- For every proper ideal `I ≠ ⊤` of a local ring `A`, `localQuotientHilbertSamuel A I 0 = 1`. -/
theorem localQuotientHilbertSamuel_zero_of_ne_top {I : Ideal A} (hI : I ≠ ⊤) :
    localQuotientHilbertSamuel A I 0 = 1 := by
  rw [localQuotientHilbertSamuel_def, zero_add, pow_one,
    sup_eq_right.mpr (IsLocalRing.le_maximalIdeal hI), Ideal.length_quotient_eq_one]

/-- At degree `0`, the Hilbert–Samuel function of a local ring `A` itself (`I = ⊥`) equals `1`. -/
@[simp]
theorem localQuotientHilbertSamuel_bot_zero :
    localQuotientHilbertSamuel A (⊥ : Ideal A) 0 = 1 :=
  localQuotientHilbertSamuel_zero_of_ne_top bot_ne_top

/-- For the maximal ideal `𝔪` of a local ring `A`, every Hilbert–Samuel value equals `1`. -/
@[simp]
theorem localQuotientHilbertSamuel_maximalIdeal (n : ℕ) :
    localQuotientHilbertSamuel A (IsLocalRing.maximalIdeal A) n = 1 := by
  rw [localQuotientHilbertSamuel_def,
    sup_eq_left.mpr (Ideal.pow_le_self (Nat.succ_ne_zero n)),
    Ideal.length_quotient_eq_one]

/-- `localQuotientHilbertSamuel A I` is monotone in the jet degree `n`. -/
theorem localQuotientHilbertSamuel_mono (I : Ideal A) :
    Monotone (localQuotientHilbertSamuel A I) := fun _ _ hmn ↦
  length_quotient_anti (sup_le_sup_left (Ideal.pow_le_pow_right (Nat.add_le_add_right hmn 1)) I)

/-- Enlarging the ideal `I` cannot increase `localQuotientHilbertSamuel A I n`. -/
theorem localQuotientHilbertSamuel_anti {I J : Ideal A} (h : I ≤ J) (n : ℕ) :
    localQuotientHilbertSamuel A J n ≤ localQuotientHilbertSamuel A I n :=
  length_quotient_anti (sup_le_sup_right h _)

/-- Adjoining `𝔪 ^ (k + 1)` to `I` truncates `localQuotientHilbertSamuel A I` at degree
`min k n`. -/
theorem localQuotientHilbertSamuel_sup_maximalIdeal_pow_succ (I : Ideal A) (k n : ℕ) :
    localQuotientHilbertSamuel A (I ⊔ IsLocalRing.maximalIdeal A ^ (k + 1)) n =
      localQuotientHilbertSamuel A I (min k n) := by
  rw [localQuotientHilbertSamuel_def, localQuotientHilbertSamuel_def, sup_assoc]
  refine congrArg (fun J ↦ Module.length A (A ⧸ (I ⊔ J))) ?_
  rcases le_total k n with hkn | hnk
  · rw [min_eq_left hkn,
      sup_eq_left.mpr (Ideal.pow_le_pow_right (Nat.add_le_add_right hkn 1))]
  · rw [min_eq_right hnk,
      sup_eq_right.mpr (Ideal.pow_le_pow_right (Nat.add_le_add_right hnk 1))]

/-- For `𝔪 ^ (k + 1)`, the Hilbert–Samuel value at degree `n` agrees with that of `⊥` at degree
`min k n`. -/
theorem localQuotientHilbertSamuel_maximalIdeal_pow_succ (k n : ℕ) :
    localQuotientHilbertSamuel A (IsLocalRing.maximalIdeal A ^ (k + 1)) n =
      localQuotientHilbertSamuel A ⊥ (min k n) := by
  rw [← bot_sup_eq (IsLocalRing.maximalIdeal A ^ (k + 1)),
    localQuotientHilbertSamuel_sup_maximalIdeal_pow_succ]

/-- Filtration step: `H_{A/I}(n + 1)` equals `H_{A/I}(n)` plus the length of the image of
`𝔪 ^ (n + 1)` in `A ⧸ (I + 𝔪 ^ (n + 2))`. -/
theorem localQuotientHilbertSamuel_succ (I : Ideal A) (n : ℕ) :
    localQuotientHilbertSamuel A I (n + 1) =
      localQuotientHilbertSamuel A I n +
        Module.length A
          (Submodule.map (I ⊔ IsLocalRing.maximalIdeal A ^ (n + 2)).mkQ
            (IsLocalRing.maximalIdeal A ^ (n + 1))) := by
  have hsup : (I ⊔ IsLocalRing.maximalIdeal A ^ (n + 2)) ⊔
      IsLocalRing.maximalIdeal A ^ (n + 1) = I ⊔ IsLocalRing.maximalIdeal A ^ (n + 1) := by
    rw [sup_assoc]
    exact congrArg (I ⊔ ·) (sup_eq_right.mpr (Ideal.pow_le_pow_right (Nat.le_succ (n + 1))))
  rw [localQuotientHilbertSamuel_def, localQuotientHilbertSamuel_def,
    length_quotient_eq_length_map_add_length_quotient_sup (IsLocalRing.maximalIdeal A ^ (n + 1))
      (I ⊔ IsLocalRing.maximalIdeal A ^ (n + 2)),
    hsup, add_comm]

/-- Along any surjective homomorphism `f : A → B` between local rings, computing
`localQuotientHilbertSamuel` on `B` at `I.map f` agrees with computing it on `A` at
`RingHom.ker f ⊔ I`. -/
theorem localQuotientHilbertSamuel_map_of_surjective {B F : Type*}
    [CommRing B] [IsLocalRing B] [FunLike F A B] [RingHomClass F A B]
    {f : F} (hf : Function.Surjective f) (I : Ideal A) (n : ℕ) :
    localQuotientHilbertSamuel B (I.map f) n =
      localQuotientHilbertSamuel A (RingHom.ker f ⊔ I) n := by
  let φ : A →+* B := f
  let _ : Algebra A B := φ.toAlgebra
  have hφ : Function.Surjective (algebraMap A B) := by
    rwa [RingHom.algebraMap_toAlgebra]
  have h𝔪 : (IsLocalRing.maximalIdeal A).map φ = IsLocalRing.maximalIdeal B :=
    IsLocalRing.map_maximalIdeal_of_surjective φ hf
  set Q : Ideal B := I.map f ⊔ IsLocalRing.maximalIdeal B ^ (n + 1)
  have hQ : Q = (I ⊔ IsLocalRing.maximalIdeal A ^ (n + 1)).map φ := by
    rw [Ideal.map_sup, Ideal.map_pow, h𝔪, Ideal.map_coe]
  let ψ : A →ₐ[A] B ⧸ Q := Algebra.ofId A (B ⧸ Q)
  have hψa (a : A) : ψ a = Ideal.Quotient.mk Q (f a) := by
    rw [Algebra.ofId_apply, IsScalarTower.algebraMap_apply A B (B ⧸ Q),
      RingHom.algebraMap_toAlgebra, Ideal.Quotient.algebraMap_eq, RingHom.coe_coe]
  have hψ : Function.Surjective ψ := fun y ↦ by
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective y
    obtain ⟨a, rfl⟩ := hf b
    exact ⟨a, hψa a⟩
  have hker : RingHom.ker ψ =
      (RingHom.ker f ⊔ I) ⊔ IsLocalRing.maximalIdeal A ^ (n + 1) := by
    ext a
    rw [RingHom.mem_ker, hψa, Ideal.Quotient.eq_zero_iff_mem, hQ, Ideal.map_coe,
      ← Ideal.mem_comap, Ideal.comap_map_of_surjective' f hf, sup_comm _ (RingHom.ker f),
      sup_assoc]
  rw [localQuotientHilbertSamuel_def, ← Module.length_eq_of_surjective hφ,
    ← (Ideal.quotientKerAlgEquivOfSurjective hψ).toLinearEquiv.length_eq,
    (Ideal.quotientEquivAlgOfEq A hker).toLinearEquiv.length_eq,
    localQuotientHilbertSamuel_def]

/-- Computing `localQuotientHilbertSamuel` on a local quotient `A ⧸ I` at `J.map (Quotient.mk I)`
agrees with computing it on `A` at `I ⊔ J`. -/
theorem localQuotientHilbertSamuel_quotient_map (I J : Ideal A) [IsLocalRing (A ⧸ I)] (n : ℕ) :
    localQuotientHilbertSamuel (A ⧸ I) (J.map (Ideal.Quotient.mk I)) n =
      localQuotientHilbertSamuel A (I ⊔ J) n := by
  rw [localQuotientHilbertSamuel_map_of_surjective Ideal.Quotient.mk_surjective, Ideal.mk_ker]

/-- The intrinsic Hilbert–Samuel function of a local quotient ring `A ⧸ I` (`J = ⊥`) agrees with
`localQuotientHilbertSamuel A I`. -/
@[simp]
theorem localQuotientHilbertSamuel_quotient_bot (I : Ideal A) [IsLocalRing (A ⧸ I)] (n : ℕ) :
    localQuotientHilbertSamuel (A ⧸ I) ⊥ n = localQuotientHilbertSamuel A I n := by
  simpa using localQuotientHilbertSamuel_quotient_map I ⊥ n

/-- Any ring or algebra equivalence `e : A ≃ B` between local rings preserves
`localQuotientHilbertSamuel` under `Ideal.map e`. -/
theorem localQuotientHilbertSamuel_map_equiv {B E : Type*}
    [CommRing B] [IsLocalRing B] [EquivLike E A B] [RingEquivClass E A B]
    (e : E) (I : Ideal A) (n : ℕ) :
    localQuotientHilbertSamuel B (I.map e) n = localQuotientHilbertSamuel A I n := by
  rw [localQuotientHilbertSamuel_map_of_surjective (EquivLike.surjective e),
    RingHom.ker_equiv, bot_sup_eq]

/-- Any ring or algebra equivalence `e : A ≃ B` between local rings preserves
`localQuotientHilbertSamuel` under `Ideal.comap e`. -/
theorem localQuotientHilbertSamuel_comap_equiv {B E : Type*}
    [CommRing B] [IsLocalRing B] [EquivLike E A B] [RingEquivClass E A B]
    (e : E) (J : Ideal B) (n : ℕ) :
    localQuotientHilbertSamuel A (J.comap e) n = localQuotientHilbertSamuel B J n := by
  rw [← localQuotientHilbertSamuel_map_equiv e (J.comap e) n,
    Ideal.map_comap_of_surjective e (EquivLike.surjective e)]

/-- Isomorphic local rings have the same intrinsic Hilbert–Samuel function (`I = ⊥`). -/
theorem localQuotientHilbertSamuel_bot_of_equiv {B E : Type*}
    [CommRing B] [IsLocalRing B] [EquivLike E A B] [RingEquivClass E A B]
    (e : E) (n : ℕ) :
    localQuotientHilbertSamuel A ⊥ n = localQuotientHilbertSamuel B ⊥ n := by
  rw [← Ideal.comap_bot_of_injective e (EquivLike.injective e),
    localQuotientHilbertSamuel_comap_equiv]

end Basic

section RestrictScalars

/-- Over a local extension `K → A`, the `K`-length of `A ⧸ (I + 𝔪_A ^ (n + 1))` multiplies
`localQuotientHilbertSamuel A I n` by `[κ(A) : κ(K)]`. -/
theorem length_quotient_sup_maximalIdeal_pow_restrictScalars
    (K A : Type*) [CommRing K] [IsLocalRing K] [CommRing A] [IsLocalRing A]
    [Algebra K A] [IsLocalHom (algebraMap K A)] (I : Ideal A) (n : ℕ) :
    Module.length K (A ⧸ (I ⊔ IsLocalRing.maximalIdeal A ^ (n + 1))) =
      localQuotientHilbertSamuel A I n *
        Module.length (IsLocalRing.ResidueField K) (IsLocalRing.ResidueField A) :=
  IsLocalRing.length_restrictScalars K A (A ⧸ (I ⊔ IsLocalRing.maximalIdeal A ^ (n + 1)))

/-- Over a local extension `K → A`, the `K`-length of `A ⧸ (I + 𝔪_A ^ (n + 1))` equals
`localQuotientHilbertSamuel A I n * Module.length K (ResidueField A)`. In particular, this applies
whenever `K` is a ground field. -/
theorem length_quotient_sup_maximalIdeal_pow_eq_mul_length_residueField
    (K A : Type*) [CommRing K] [IsLocalRing K] [CommRing A] [IsLocalRing A]
    [Algebra K A] [IsLocalHom (algebraMap K A)] (I : Ideal A) (n : ℕ) :
    Module.length K (A ⧸ (I ⊔ IsLocalRing.maximalIdeal A ^ (n + 1))) =
      localQuotientHilbertSamuel A I n * Module.length K (IsLocalRing.ResidueField A) := by
  rw [length_quotient_sup_maximalIdeal_pow_restrictScalars K A I n,
    Module.length_eq_of_surjective (IsLocalRing.residue_surjective (R := K))]

end RestrictScalars

section Noetherian

variable {A : Type*} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]

/-- Over a Noetherian local ring `A`, `localQuotientHilbertSamuel A I n` is never `⊤`. -/
theorem localQuotientHilbertSamuel_ne_top (I : Ideal A) (n : ℕ) :
    localQuotientHilbertSamuel A I n ≠ ⊤ :=
  Module.length_ne_top_iff.mpr (I.isFiniteLength_quotient_sup_maximalIdeal_pow (n + 1))

/-- Over a Noetherian local ring `A`, every value of `localQuotientHilbertSamuel A I` is strictly
less than `⊤`. -/
theorem localQuotientHilbertSamuel_lt_top (I : Ideal A) (n : ℕ) :
    localQuotientHilbertSamuel A I n < ⊤ :=
  lt_top_iff_ne_top.mpr (localQuotientHilbertSamuel_ne_top I n)

/-- Over a Noetherian local ring `A`, `localQuotientHilbertSamuel A I n` equals the coercion of its
`ℕ`-value `(localQuotientHilbertSamuel A I n).toNat`. -/
@[simp]
theorem natCast_toNat_localQuotientHilbertSamuel (I : Ideal A) (n : ℕ) :
    ((localQuotientHilbertSamuel A I n).toNat : ℕ∞) = localQuotientHilbertSamuel A I n :=
  ENat.natCast_toNat (localQuotientHilbertSamuel_ne_top I n)

end Noetherian

section FlatAndCompletion

/-- Along a flat homomorphism `A → B` of local rings such that `𝔪_A B = 𝔪_B`, extending `I` to `B`
preserves every value of `localQuotientHilbertSamuel`. -/
theorem localQuotientHilbertSamuel_map_of_flat_of_map_maximalIdeal_eq
    {A B : Type*} [CommRing A] [IsLocalRing A] [CommRing B] [IsLocalRing B]
    [Algebra A B] [Module.Flat A B]
    (hm : (IsLocalRing.maximalIdeal A).map (algebraMap A B) = IsLocalRing.maximalIdeal B)
    (I : Ideal A) (n : ℕ) :
    localQuotientHilbertSamuel B (I.map (algebraMap A B)) n =
      localQuotientHilbertSamuel A I n := by
  have : IsLocalHom (algebraMap A B) :=
    ((IsLocalRing.local_hom_tfae (algebraMap A B)).out 1 3).mpr hm.le
  have hmap : I.map (algebraMap A B) ⊔ IsLocalRing.maximalIdeal B ^ (n + 1) =
      (I ⊔ IsLocalRing.maximalIdeal A ^ (n + 1)).map (algebraMap A B) := by
    rw [← hm, ← Ideal.map_pow, ← Ideal.map_sup]
  have hlen : Module.length B (B ⧸ (IsLocalRing.maximalIdeal A).map (algebraMap A B)) = 1 := by
    rw [hm, Ideal.length_quotient_eq_one]
  rw [localQuotientHilbertSamuel_def, hmap,
    (Algebra.TensorProduct.quotIdealMapEquivTensorQuot B
      (I ⊔ IsLocalRing.maximalIdeal A ^ (n + 1))).toLinearEquiv.length_eq,
    IsLocalRing.length_baseChange A B (A ⧸ (I ⊔ IsLocalRing.maximalIdeal A ^ (n + 1))),
    hlen, mul_one, localQuotientHilbertSamuel_def]

/-- Extending an ideal `I` of a Noetherian local ring `A` to its `𝔪`-adic completion preserves
every value of `localQuotientHilbertSamuel`. -/
theorem localQuotientHilbertSamuel_adicCompletion
    {A : Type*} [CommRing A] [IsLocalRing A] [IsNoetherianRing A] (I : Ideal A) (n : ℕ) :
    localQuotientHilbertSamuel (AdicCompletion (IsLocalRing.maximalIdeal A) A)
        (I.map (algebraMap A (AdicCompletion (IsLocalRing.maximalIdeal A) A))) n =
      localQuotientHilbertSamuel A I n :=
  localQuotientHilbertSamuel_map_of_flat_of_map_maximalIdeal_eq
    AdicCompletion.maximalIdeal_eq_map.symm I n

/-- The `𝔪`-adic completion of a Noetherian local ring `A` has the same Hilbert–Samuel function as
`A` at `⊥`. -/
@[simp]
theorem localQuotientHilbertSamuel_adicCompletion_bot
    (A : Type*) [CommRing A] [IsLocalRing A] [IsNoetherianRing A] (n : ℕ) :
    localQuotientHilbertSamuel (AdicCompletion (IsLocalRing.maximalIdeal A) A) ⊥ n =
      localQuotientHilbertSamuel A ⊥ n := by
  simpa using localQuotientHilbertSamuel_adicCompletion (⊥ : Ideal A) n

end FlatAndCompletion

end TauCeti
