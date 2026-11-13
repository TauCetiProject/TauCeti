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
import Mathlib.Algebra.Polynomial.SpecificDegree
import Mathlib.RingTheory.AdicCompletion.AsTensorProduct
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.RingTheory.LocalRing.Length
import Mathlib.RingTheory.PrincipalIdealDomain
import Mathlib.RingTheory.TensorProduct.Quotient
import TauCeti.RingTheory.Length

/-!
# Local quotient Hilbert–Samuel functions

For a local commutative ring `(A, 𝔪)` and an ideal `I` of `A`, the *local quotient Hilbert–Samuel
function* `TauCeti.localQuotientHilbertSamuel A I : ℕ → ℕ∞` sends `n` to the `A`-module length of
`A ⧸ (I ⊔ 𝔪 ^ (n + 1))`. Measuring length over `A` (equivalently over `A ⧸ I` when `I` is proper,
`TauCeti.localQuotientHilbertSamuel_quotient_bot`) normalizes each simple composition factor to have
length `1`, rather than multiplying by the degree of the residue field over a ground field
(`TauCeti.length_quotient_sup_maximalIdeal_pow_of_field`): in particular, `H_{A/I}(0) = 1` for every
proper ideal `I` (`TauCeti.localQuotientHilbertSamuel_zero_of_ne_top`), even at non-rational closed
points whose residue field has degree greater than `1`. For `I = ⊤`, the quotient is zero and every
value vanishes (`TauCeti.localQuotientHilbertSamuel_top`).

When `A` is Noetherian, every value `localQuotientHilbertSamuel A I n` is finite
(`TauCeti.localQuotientHilbertSamuel_lt_top`, `TauCeti.natCast_toNat_localQuotientHilbertSamuel`).
Along any flat extension of local rings `A → B` with `𝔪_A B = 𝔪_B`, flat base change of lengths
(`IsLocalRing.length_baseChange`) shows that extending `I` to `B` preserves every value of the
Hilbert–Samuel function without any Noetherian hypothesis
(`TauCeti.localQuotientHilbertSamuel_map_of_flat`). Specializing to the `𝔪`-adic completion of a
Noetherian local ring yields completion invariance
(`TauCeti.localQuotientHilbertSamuel_adicCompletion`).

## Main definitions

* `TauCeti.localQuotientHilbertSamuel`: `n ↦ Module.length A (A ⧸ (I ⊔ 𝔪 ^ (n + 1)))`.

## Main results

* `TauCeti.localQuotientHilbertSamuel_eq_zero_iff`,
  `TauCeti.localQuotientHilbertSamuel_zero_of_ne_top`: vanishing characterizes `I = ⊤`, while every
  proper ideal satisfies `H_{A/I}(0) = 1`.
* `TauCeti.localQuotientHilbertSamuel_mono`, `TauCeti.localQuotientHilbertSamuel_anti`,
  `TauCeti.localQuotientHilbertSamuel_succ`: monotonicity in `n`, antitonicity in `I`, and the
  one-step filtration identity.
* `TauCeti.localQuotientHilbertSamuel_quotient_map`,
  `TauCeti.localQuotientHilbertSamuel_quotient_bot`,
  `RingEquiv.localQuotientHilbertSamuel_map`: compatibility with passage to local quotients `A ⧸ I`
  and ring isomorphisms.
* `TauCeti.length_quotient_sup_maximalIdeal_pow_restrictScalars`,
  `TauCeti.length_quotient_sup_maximalIdeal_pow_of_field`: comparison between `A`-length and
  base-ring or ground-field length via the residue-field degree.
* `TauCeti.localQuotientHilbertSamuel_lt_top`,
  `TauCeti.natCast_toNat_localQuotientHilbertSamuel`: finiteness over Noetherian local rings.
* `TauCeti.localQuotientHilbertSamuel_map_of_flat`,
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

/-- `localQuotientHilbertSamuel A I` is monotone in the jet degree `n`. -/
theorem localQuotientHilbertSamuel_mono (I : Ideal A) :
    Monotone (localQuotientHilbertSamuel A I) := fun _ _ hmn ↦
  length_quotient_anti (sup_le_sup_left (Ideal.pow_le_pow_right (Nat.add_le_add_right hmn 1)) I)

/-- Enlarging the ideal `I` cannot increase `localQuotientHilbertSamuel A I n`. -/
theorem localQuotientHilbertSamuel_anti {I J : Ideal A} (h : I ≤ J) (n : ℕ) :
    localQuotientHilbertSamuel A J n ≤ localQuotientHilbertSamuel A I n :=
  length_quotient_anti (sup_le_sup_right h _)

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

/-- Computing `localQuotientHilbertSamuel` on a local quotient `A ⧸ I` at `J.map (Quotient.mk I)`
agrees with computing it on `A` at `I ⊔ J`. -/
theorem localQuotientHilbertSamuel_quotient_map (I J : Ideal A) [IsLocalRing (A ⧸ I)] (n : ℕ) :
    localQuotientHilbertSamuel (A ⧸ I) (J.map (Ideal.Quotient.mk I)) n =
      localQuotientHilbertSamuel A (I ⊔ J) n := by
  let π : A →+* A ⧸ I := Ideal.Quotient.mk I
  have h𝔪 : (IsLocalRing.maximalIdeal A).map π = IsLocalRing.maximalIdeal (A ⧸ I) :=
    IsLocalRing.map_maximalIdeal_of_surjective π Ideal.Quotient.mk_surjective
  have hmap : J.map π ⊔ IsLocalRing.maximalIdeal (A ⧸ I) ^ (n + 1) =
      (J ⊔ IsLocalRing.maximalIdeal A ^ (n + 1)).map (Ideal.Quotient.mkₐ A I) := by
    rw [← h𝔪, ← Ideal.map_pow, ← Ideal.map_sup]
    rfl
  rw [localQuotientHilbertSamuel_def, hmap,
    ← Module.length_eq_of_surjective (Ideal.Quotient.mk_surjective (I := I)),
    (DoubleQuot.quotQuotEquivQuotSupₐ A I
      (J ⊔ IsLocalRing.maximalIdeal A ^ (n + 1))).toLinearEquiv.length_eq,
    ← sup_assoc, localQuotientHilbertSamuel_def]

/-- The intrinsic Hilbert–Samuel function of a local quotient ring `A ⧸ I` (`J = ⊥`) agrees with
`localQuotientHilbertSamuel A I`. -/
@[simp]
theorem localQuotientHilbertSamuel_quotient_bot (I : Ideal A) [IsLocalRing (A ⧸ I)] (n : ℕ) :
    localQuotientHilbertSamuel (A ⧸ I) ⊥ n = localQuotientHilbertSamuel A I n := by
  simpa using localQuotientHilbertSamuel_quotient_map I ⊥ n

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

/-- Over a ground field `K`, the `K`-length of `A ⧸ (I + 𝔪_A ^ (n + 1))` equals
`localQuotientHilbertSamuel A I n * Module.length K (ResidueField A)`. -/
theorem length_quotient_sup_maximalIdeal_pow_of_field
    (K A : Type*) [Field K] [CommRing A] [IsLocalRing A] [Algebra K A]
    (I : Ideal A) (n : ℕ) :
    Module.length K (A ⧸ (I ⊔ IsLocalRing.maximalIdeal A ^ (n + 1))) =
      localQuotientHilbertSamuel A I n * Module.length K (IsLocalRing.ResidueField A) := by
  rw [length_quotient_sup_maximalIdeal_pow_restrictScalars K A I n,
    Module.length_eq_of_surjective (IsLocalRing.residue_surjective (R := K))]

end RestrictScalars

section Noetherian

variable {A : Type*} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]

/-- Over a Noetherian local ring `A`, every quotient `A ⧸ (I + 𝔪 ^ n)` has finite length. -/
theorem isFiniteLength_quotient_sup_maximalIdeal_pow (I : Ideal A) (n : ℕ) :
    IsFiniteLength A (A ⧸ (I ⊔ IsLocalRing.maximalIdeal A ^ n)) := by
  rw [← Module.length_ne_top_iff, ← lt_top_iff_ne_top]
  exact (length_quotient_anti le_sup_right).trans_lt
    (lt_top_iff_ne_top.mpr (Module.length_ne_top_iff.mpr
      (isFiniteLength_quotient_maximalIdeal_pow n)))

/-- Over a Noetherian local ring `A`, `localQuotientHilbertSamuel A I n` is never `⊤`. -/
theorem localQuotientHilbertSamuel_ne_top (I : Ideal A) (n : ℕ) :
    localQuotientHilbertSamuel A I n ≠ ⊤ :=
  Module.length_ne_top_iff.mpr (isFiniteLength_quotient_sup_maximalIdeal_pow I (n + 1))

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
theorem localQuotientHilbertSamuel_map_of_flat
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
  localQuotientHilbertSamuel_map_of_flat AdicCompletion.maximalIdeal_eq_map.symm I n

/-- The `𝔪`-adic completion of a Noetherian local ring `A` has the same Hilbert–Samuel function as
`A` at `⊥`. -/
@[simp]
theorem localQuotientHilbertSamuel_adicCompletion_bot
    (A : Type*) [CommRing A] [IsLocalRing A] [IsNoetherianRing A] (n : ℕ) :
    localQuotientHilbertSamuel (AdicCompletion (IsLocalRing.maximalIdeal A) A) ⊥ n =
      localQuotientHilbertSamuel A ⊥ n := by
  simpa using localQuotientHilbertSamuel_adicCompletion (⊥ : Ideal A) n

end FlatAndCompletion

section Examples

open Polynomial in
/-- At the degree-two closed point `(X ^ 2 + 1)` of `ℚ[X]`, the local Hilbert–Samuel value `H(0)` is
`1` by local length, even though the quotient `A ⧸ 𝔪` has `ℚ`-dimension `2`. -/
example : ∃ (p : ℚ[X]) (hmax : (Ideal.span {p}).IsMaximal),
    letI : (Ideal.span {p}).IsMaximal := hmax
    let A := Localization.AtPrime (Ideal.span {p})
    localQuotientHilbertSamuel A ⊥ 0 = 1 ∧
      Module.length ℚ (A ⧸ IsLocalRing.maximalIdeal A) = 2 := by
  let p : ℚ[X] := X ^ 2 + 1
  have hp_monic : p.Monic := monic_X_pow_add_C 1 two_ne_zero
  have hp_deg : p.natDegree = 2 := by simp [p]
  have hp_irr : Irreducible p := by
    rw [hp_monic.irreducible_iff_roots_eq_zero_of_degree_le_three (by omega) (by omega)]
    refine Multiset.eq_zero_iff_forall_notMem.mpr fun q hq ↦ ?_
    have hroot : q ^ 2 + 1 = 0 := by simpa [p, IsRoot.def] using isRoot_of_mem_roots hq
    linarith [sq_nonneg q]
  have hmax : (Ideal.span {p}).IsMaximal := PrincipalIdealRing.isMaximal_of_irreducible hp_irr
  refine ⟨p, hmax, localQuotientHilbertSamuel_bot_zero, ?_⟩
  let A := Localization.AtPrime (Ideal.span {p})
  have : Module.Finite ℚ (ℚ[X] ⧸ Ideal.span {p}) := (AdjoinRoot.powerBasis hp_irr.ne_zero).finite
  have hres : Module.length ℚ (IsLocalRing.ResidueField A) = 2 := by
    rw [MaximalSpectrum.length_residueField_localization_eq ⟨Ideal.span {p}, hmax⟩,
      Module.length_eq_finrank, finrank_quotient_span_eq_natDegree, hp_deg]
    rfl
  exact hres

end Examples

end TauCeti

namespace RingEquiv

/-- A ring isomorphism `e : A ≃+* B` between local rings preserves `localQuotientHilbertSamuel`. -/
theorem localQuotientHilbertSamuel_map {A B : Type*} [CommRing A] [IsLocalRing A]
    [CommRing B] [IsLocalRing B] (e : A ≃+* B) (I : Ideal A) (n : ℕ) :
    TauCeti.localQuotientHilbertSamuel B (I.map (e : A →+* B)) n =
      TauCeti.localQuotientHilbertSamuel A I n := by
  have h𝔪 : (IsLocalRing.maximalIdeal A).map (e : A →+* B) = IsLocalRing.maximalIdeal B :=
    IsLocalRing.map_maximalIdeal_of_surjective (e : A →+* B) e.surjective
  set P : Ideal A := I ⊔ IsLocalRing.maximalIdeal A ^ (n + 1)
  set Q : Ideal B := I.map (e : A →+* B) ⊔ IsLocalRing.maximalIdeal B ^ (n + 1)
  have hPQ : P.map (e : A →+* B) = Q := by
    simp only [P, Q, Ideal.map_sup, Ideal.map_pow, h𝔪]
  let qEquiv : (A ⧸ P) ≃+* (B ⧸ Q) := Ideal.quotientEquiv P Q e hPQ.symm
  let f : (A ⧸ P) →ₛₗ[(e : A →+* B)] (B ⧸ Q) :=
    { toFun := qEquiv
      map_add' := qEquiv.map_add
      map_smul' := fun r x ↦ by
        obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
        exact qEquiv.map_mul (Ideal.Quotient.mk P r) (Ideal.Quotient.mk P x) }
  have : RingHomSurjective (e : A →+* B) := ⟨e.surjective⟩
  exact (LinearMap.length_eq_of_bijective f qEquiv.bijective).symm

end RingEquiv
