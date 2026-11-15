/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Order.PiLex
public import Mathlib.RingTheory.AdicCompletion.LocalRing
public import Mathlib.RingTheory.Length
public import Mathlib.RingTheory.LocalRing.Quotient
import TauCeti.RingTheory.AdicCompletion.Algebra
import TauCeti.RingTheory.Length

/-!
# The Hilbert–Samuel function of a local ring and its quotients

For a commutative local ring `(A, 𝔪)` and an ideal `I` of `A`, the (cumulative) *Hilbert–Samuel
function* of `A ⧸ I` at order `n : ℕ` is the `A`-module length
`TauCeti.localQuotientHilbertSamuel A I n = Module.length A (A ⧸ (I ⊔ 𝔪 ^ (n + 1)))`, specializing
at `I = ⊥` to `TauCeti.localHilbertSamuel A n = Module.length A (A ⧸ 𝔪 ^ (n + 1))`. When `I` is a
proper ideal, `A ⧸ I` is itself a local ring whose intrinsic Hilbert–Samuel function agrees with
`localQuotientHilbertSamuel A I` (`TauCeti.localHilbertSamuel_quotient`).

For any finitely generated ideal `𝔪` of a commutative ring `R` and any ideal `I` of `R`, the
canonical homomorphism `R →+* AdicCompletion 𝔪 R` induces a bijection
`R ⧸ (I ⊔ 𝔪 ^ n) → AdicCompletion 𝔪 R ⧸ (I R̂ ⊔ (𝔪 R̂) ^ n)`
(`AdicCompletion.quotientMap_sup_pow_bijective`). Consequently, when the maximal ideal of a local
ring `A` is finitely generated (in particular when `A` is Noetherian), the Hilbert–Samuel function
of `A ⧸ I` is unchanged upon passing to the `𝔪`-adic completion `Â` and the extended ideal `I Â`
(`TauCeti.localQuotientHilbertSamuel_adicCompletion_of_fg`,
`TauCeti.localQuotientHilbertSamuel_adicCompletion`).

## Main definitions

* `TauCeti.localQuotientHilbertSamuel`:
  `Module.length A (A ⧸ (I ⊔ IsLocalRing.maximalIdeal A ^ (n + 1)))`.
* `TauCeti.localHilbertSamuel`: `localQuotientHilbertSamuel A ⊥ n`.

## Main results

* `TauCeti.localQuotientHilbertSamuel_zero_of_ne_top`, `TauCeti.localHilbertSamuel_zero`: at
  `n = 0`, the Hilbert–Samuel value is `1` for every proper ideal `I`.
* `TauCeti.localQuotientHilbertSamuel_anti`, `TauCeti.localQuotientHilbertSamuel_mono`,
  `TauCeti.toLex_localQuotientHilbertSamuel_anti`: antitonicity in `I` (pointwise and in `Lex`) and
  monotonicity in `n`.
* `TauCeti.localQuotientHilbertSamuel_quotient_map`, `TauCeti.localHilbertSamuel_quotient`:
  compatibility with local ring quotients `A ⧸ I`.
* `TauCeti.localQuotientHilbertSamuel_lt_top`: finiteness of `localQuotientHilbertSamuel A I n`
  over a Noetherian local ring.
* `AdicCompletion.quotientMap_sup_pow_bijective`,
  `TauCeti.localQuotientHilbertSamuel_adicCompletion_of_fg`,
  `TauCeti.localQuotientHilbertSamuel_adicCompletion`: invariance under maximal-adic completion.

## References

* H. Matsumura, *Commutative Ring Theory*, Cambridge University Press (1986), §13.
* B. M. Bennett, *On the characteristic functions of a local ring*, Ann. of Math. (2) 91 (1970),
  25–87.
-/

public section

namespace AdicCompletion

variable {R : Type*} [CommRing R] {𝔪 : Ideal R}

/-- For a finitely generated ideal `𝔪` and an arbitrary ideal `I` of `R`, the canonical map
`R →+* AdicCompletion 𝔪 R` induces a bijection
`R ⧸ (I ⊔ 𝔪 ^ n) → AdicCompletion 𝔪 R ⧸ (I R̂ ⊔ (𝔪 R̂) ^ n)`. -/
theorem quotientMap_sup_pow_bijective (fg : 𝔪.FG) (I : Ideal R) (n : ℕ)
    {H : I ⊔ 𝔪 ^ n ≤
      (I.map (algebraMap R (AdicCompletion 𝔪 R)) ⊔
        (𝔪.map (algebraMap R (AdicCompletion 𝔪 R))) ^ n).comap
        (algebraMap R (AdicCompletion 𝔪 R))} :
    Function.Bijective (Ideal.quotientMap _ (algebraMap R (AdicCompletion 𝔪 R)) H) := by
  let φ := algebraMap R (AdicCompletion 𝔪 R)
  let π : AdicCompletion 𝔪 R →+* R ⧸ (I ⊔ 𝔪 ^ n) :=
    (Ideal.Quotient.factor (le_sup_right : 𝔪 ^ n ≤ I ⊔ 𝔪 ^ n)).comp (evalₐ 𝔪 n).toRingHom
  have hπφ (y : R) : π (φ y) = Ideal.Quotient.mk (I ⊔ 𝔪 ^ n) y := by
    simp [π, φ]
  have hker : I.map φ ⊔ (𝔪.map φ) ^ n ≤ RingHom.ker π := by
    refine sup_le (Ideal.map_le_iff_le_comap.mpr fun y hy ↦ ?_) ?_
    · rw [Ideal.mem_comap, RingHom.mem_ker, hπφ, Ideal.Quotient.eq_zero_iff_mem]
      exact Ideal.mem_sup_left hy
    · rw [← Ideal.map_pow, ← ker_evalₐ_eq_map_pow fg n]
      intro z hz
      rw [RingHom.mem_ker] at hz ⊢
      simp [π, hz]
  refine ⟨Ideal.quotientMap_injective' fun x hx ↦ ?_, fun z ↦ ?_⟩
  · have hx0 : π (φ x) = 0 := RingHom.mem_ker.mp (hker (Ideal.mem_comap.mp hx))
    rwa [hπφ, Ideal.Quotient.eq_zero_iff_mem] at hx0
  · obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective z
    obtain ⟨y, hy⟩ := exists_sub_algebraMap_mem_map_pow fg n x
    rw [Ideal.map_pow] at hy
    exact ⟨Ideal.Quotient.mk _ y, (Ideal.Quotient.eq.mpr (Ideal.mem_sup_right hy)).symm⟩

end AdicCompletion

namespace TauCeti

open IsLocalRing

section Basic

variable {A : Type*} [CommRing A] [IsLocalRing A]

variable (A) in
/-- The (cumulative) Hilbert–Samuel function of `A ⧸ I` for a local ring `(A, 𝔪)`:
`localQuotientHilbertSamuel A I n = length_A (A ⧸ (I ⊔ 𝔪 ^ (n + 1)))`. -/
noncomputable def localQuotientHilbertSamuel (I : Ideal A) (n : ℕ) : ℕ∞ :=
  Module.length A (A ⧸ (I ⊔ maximalIdeal A ^ (n + 1)))

theorem localQuotientHilbertSamuel_def (I : Ideal A) (n : ℕ) :
    localQuotientHilbertSamuel A I n =
      Module.length A (A ⧸ (I ⊔ maximalIdeal A ^ (n + 1))) :=
  (rfl)

variable (A) in
/-- The (cumulative) Hilbert–Samuel function of a local ring `(A, 𝔪)`:
`localHilbertSamuel A n = length_A (A ⧸ 𝔪 ^ (n + 1))`. -/
noncomputable def localHilbertSamuel (n : ℕ) : ℕ∞ :=
  localQuotientHilbertSamuel A ⊥ n

theorem localHilbertSamuel_def (n : ℕ) :
    localHilbertSamuel A n = localQuotientHilbertSamuel A ⊥ n :=
  (rfl)

theorem localHilbertSamuel_eq_length (n : ℕ) :
    localHilbertSamuel A n = Module.length A (A ⧸ maximalIdeal A ^ (n + 1)) := by
  rw [localHilbertSamuel_def, localQuotientHilbertSamuel_def, bot_sup_eq]

@[simp]
theorem localQuotientHilbertSamuel_bot (n : ℕ) :
    localQuotientHilbertSamuel A ⊥ n = localHilbertSamuel A n :=
  (rfl)

@[simp]
theorem localQuotientHilbertSamuel_top (n : ℕ) :
    localQuotientHilbertSamuel A ⊤ n = 0 := by
  rw [localQuotientHilbertSamuel_def, top_sup_eq, Module.length_eq_zero_iff]
  infer_instance

/-- For any proper ideal `I` of a local ring `A`, `localQuotientHilbertSamuel A I 0 = 1`. -/
@[simp]
theorem localQuotientHilbertSamuel_zero_of_ne_top {I : Ideal A} (hI : I ≠ ⊤) :
    localQuotientHilbertSamuel A I 0 = 1 := by
  rw [localQuotientHilbertSamuel_def, zero_add, pow_one,
    sup_eq_right.mpr (le_maximalIdeal hI), Ideal.length_quotient_eq_one]

@[simp]
theorem localHilbertSamuel_zero : localHilbertSamuel A 0 = 1 :=
  localQuotientHilbertSamuel_zero_of_ne_top bot_ne_top

@[simp]
theorem localQuotientHilbertSamuel_eq_zero_iff {I : Ideal A} {n : ℕ} :
    localQuotientHilbertSamuel A I n = 0 ↔ I = ⊤ := by
  refine ⟨fun h ↦ ?_, fun h ↦ by simp [h]⟩
  rw [localQuotientHilbertSamuel_def, Module.length_eq_zero_iff,
    Ideal.Quotient.subsingleton_iff] at h
  by_contra hI
  have hle : I ⊔ maximalIdeal A ^ (n + 1) ≤ maximalIdeal A :=
    sup_le (le_maximalIdeal hI) (Ideal.pow_le_self (Nat.succ_ne_zero n))
  exact (maximalIdeal.isMaximal A).ne_top (top_unique (h ▸ hle))

theorem localQuotientHilbertSamuel_pos_iff {I : Ideal A} {n : ℕ} :
    0 < localQuotientHilbertSamuel A I n ↔ I ≠ ⊤ := by
  rw [pos_iff_ne_zero, ne_eq, localQuotientHilbertSamuel_eq_zero_iff]

theorem localHilbertSamuel_pos (n : ℕ) : 0 < localHilbertSamuel A n :=
  localQuotientHilbertSamuel_pos_iff.mpr bot_ne_top

/-- Larger ideals yield smaller quotient Hilbert–Samuel values at every order `n`. -/
theorem localQuotientHilbertSamuel_anti (n : ℕ) :
    Antitone (fun I : Ideal A ↦ localQuotientHilbertSamuel A I n) :=
  fun _ _ hIJ ↦ length_quotient_anti (sup_le_sup_right hIJ _)

/-- The quotient Hilbert–Samuel function `n ↦ localQuotientHilbertSamuel A I n` is monotone. -/
theorem localQuotientHilbertSamuel_mono (I : Ideal A) :
    Monotone (localQuotientHilbertSamuel A I) :=
  fun _ _ hmn ↦
    length_quotient_anti (sup_le_sup_left (Ideal.pow_le_pow_right (Nat.succ_le_succ hmn)) _)

theorem localHilbertSamuel_mono : Monotone (localHilbertSamuel A) :=
  localQuotientHilbertSamuel_mono ⊥

/-- Enlarging the ideal `I` decreases `toLex (localQuotientHilbertSamuel A I)` in the lexicographic
order on `ℕ → ℕ∞`. -/
theorem toLex_localQuotientHilbertSamuel_anti :
    Antitone (fun I : Ideal A ↦ toLex (localQuotientHilbertSamuel A I)) :=
  fun _ _ hIJ ↦ Pi.toLex_monotone fun n ↦ localQuotientHilbertSamuel_anti n hIJ

/-- Ring isomorphisms preserve `localQuotientHilbertSamuel`. -/
theorem localQuotientHilbertSamuel_congr {B : Type*} [CommRing B] [IsLocalRing B]
    (e : A ≃+* B) (I : Ideal A) (n : ℕ) :
    localQuotientHilbertSamuel B (I.map e) n =
      localQuotientHilbertSamuel A I n := by
  have hmap : I.map e ⊔ maximalIdeal B ^ (n + 1) =
      (I ⊔ maximalIdeal A ^ (n + 1)).map e := by
    rw [Ideal.map_sup, Ideal.map_pow, map_ringEquiv_maximalIdeal e]
  have hker : RingHom.ker e = ⊥ := (Submodule.eq_bot_iff _).mpr fun x hx ↦
    e.injective ((RingHom.mem_ker.mp hx).trans (map_zero e).symm)
  rw [localQuotientHilbertSamuel_def, hmap,
    Ideal.length_quotient_map_of_surjective _ e.surjective, hker, sup_bot_eq,
    ← localQuotientHilbertSamuel_def]

theorem localHilbertSamuel_congr {B : Type*} [CommRing B] [IsLocalRing B]
    (e : A ≃+* B) (n : ℕ) :
    localHilbertSamuel B n = localHilbertSamuel A n := by
  rw [localHilbertSamuel_def, localHilbertSamuel_def, ← localQuotientHilbertSamuel_congr e ⊥ n,
    Ideal.map_bot]

/-- Over a quotient local ring `A ⧸ I`, the Hilbert–Samuel function of `(A ⧸ I) ⧸ J (A ⧸ I)` equals
`localQuotientHilbertSamuel A (I ⊔ J)`. -/
theorem localQuotientHilbertSamuel_quotient_map (I J : Ideal A) [IsLocalRing (A ⧸ I)] (n : ℕ) :
    localQuotientHilbertSamuel (A ⧸ I) (J.map (Ideal.Quotient.mk I)) n =
      localQuotientHilbertSamuel A (I ⊔ J) n := by
  have h𝔪 : maximalIdeal (A ⧸ I) = (maximalIdeal A).map (Ideal.Quotient.mk I) :=
    (map_maximalIdeal_of_surjective (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective).symm
  have hmap : J.map (Ideal.Quotient.mk I) ⊔ maximalIdeal (A ⧸ I) ^ (n + 1) =
      (J ⊔ maximalIdeal A ^ (n + 1)).map (Ideal.Quotient.mk I) := by
    rw [h𝔪, ← Ideal.map_pow, ← Ideal.map_sup]
  rw [localQuotientHilbertSamuel_def, hmap,
    Ideal.length_quotient_map_of_surjective _ Ideal.Quotient.mk_surjective, Ideal.mk_ker,
    sup_right_comm, sup_comm J I, ← localQuotientHilbertSamuel_def]

/-- When `A ⧸ I` is a local ring (i.e. `I ≠ ⊤`), its intrinsic Hilbert–Samuel function
`localHilbertSamuel (A ⧸ I)` coincides with `localQuotientHilbertSamuel A I`. -/
@[simp]
theorem localHilbertSamuel_quotient (I : Ideal A) [IsLocalRing (A ⧸ I)] (n : ℕ) :
    localHilbertSamuel (A ⧸ I) n = localQuotientHilbertSamuel A I n := by
  rw [localHilbertSamuel_def, ← Ideal.map_bot (f := Ideal.Quotient.mk I),
    localQuotientHilbertSamuel_quotient_map, sup_bot_eq]

end Basic

end TauCeti

namespace Ideal

/-- Over a Noetherian local ring `A`, `A ⧸ (I ⊔ 𝔪 ^ n)` has finite length for every ideal `I` and
every `n : ℕ`. -/
theorem isFiniteLength_quotient_sup_maximalIdeal_pow {A : Type*} [CommRing A] [IsLocalRing A]
    [IsNoetherianRing A] (I : Ideal A) (n : ℕ) :
    IsFiniteLength A (A ⧸ (I ⊔ IsLocalRing.maximalIdeal A ^ n)) :=
  (TauCeti.isFiniteLength_quotient_maximalIdeal_pow n).of_surjective
    (f := Submodule.factor le_sup_right) (Submodule.factor_surjective le_sup_right)

end Ideal

namespace TauCeti

section Noetherian

open IsLocalRing

variable {A : Type*} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]

theorem localQuotientHilbertSamuel_ne_top (I : Ideal A) (n : ℕ) :
    localQuotientHilbertSamuel A I n ≠ ⊤ :=
  Module.length_ne_top_iff.mpr (I.isFiniteLength_quotient_sup_maximalIdeal_pow (n + 1))

theorem localQuotientHilbertSamuel_lt_top (I : Ideal A) (n : ℕ) :
    localQuotientHilbertSamuel A I n < ⊤ :=
  (localQuotientHilbertSamuel_ne_top I n).lt_top

@[simp]
theorem natCast_toNat_localQuotientHilbertSamuel (I : Ideal A) (n : ℕ) :
    ((localQuotientHilbertSamuel A I n).toNat : ℕ∞) = localQuotientHilbertSamuel A I n :=
  ENat.natCast_toNat (localQuotientHilbertSamuel_ne_top I n)

theorem localHilbertSamuel_ne_top (n : ℕ) : localHilbertSamuel A n ≠ ⊤ :=
  localQuotientHilbertSamuel_ne_top ⊥ n

theorem localHilbertSamuel_lt_top (n : ℕ) : localHilbertSamuel A n < ⊤ :=
  localQuotientHilbertSamuel_lt_top ⊥ n

end Noetherian

section AdicCompletion

open IsLocalRing

variable {A : Type*} [CommRing A] [IsLocalRing A]

/-- If the maximal ideal `𝔪` of a local ring `A` is finitely generated, passing to the `𝔪`-adic
completion `Â = AdicCompletion 𝔪 A` and the extended ideal `I Â` preserves
`localQuotientHilbertSamuel`. -/
theorem localQuotientHilbertSamuel_adicCompletion_of_fg (fg : (maximalIdeal A).FG)
    (I : Ideal A) (n : ℕ) :
    haveI := AdicCompletion.isLocalRing_of_fg fg
    localQuotientHilbertSamuel (AdicCompletion (maximalIdeal A) A)
      (I.map (algebraMap A (AdicCompletion (maximalIdeal A) A))) n =
      localQuotientHilbertSamuel A I n := by
  let _ := AdicCompletion.isLocalRing_of_fg fg
  let φ := algebraMap A (AdicCompletion (maximalIdeal A) A)
  rw [localQuotientHilbertSamuel_def, localQuotientHilbertSamuel_def,
    AdicCompletion.maximalIdeal_eq_map_of_fg fg]
  let J : Ideal A := I ⊔ maximalIdeal A ^ (n + 1)
  let J' : Ideal (AdicCompletion (maximalIdeal A) A) :=
    I.map φ ⊔ ((maximalIdeal A).map φ) ^ (n + 1)
  have hle : J ≤ J'.comap φ := by
    change I ⊔ maximalIdeal A ^ (n + 1) ≤ (I.map φ ⊔ ((maximalIdeal A).map φ) ^ (n + 1)).comap φ
    rw [← Ideal.map_pow, ← Ideal.map_sup]
    exact Ideal.le_comap_map
  let ψ : A ⧸ J →+* AdicCompletion (maximalIdeal A) A ⧸ J' := Ideal.quotientMap J' φ hle
  have hψ : Function.Bijective ψ := AdicCompletion.quotientMap_sup_pow_bijective fg I (n + 1)
  have : RingHomSurjective ψ := ⟨hψ.2⟩
  let f : (A ⧸ J) →ₛₗ[ψ] (AdicCompletion (maximalIdeal A) A ⧸ J') :=
    { toFun := ψ, map_add' := map_add ψ, map_smul' := map_mul ψ }
  rw [Module.length_eq_of_surjective (M := AdicCompletion (maximalIdeal A) A ⧸ J')
      (Ideal.Quotient.mk_surjective (I := J')),
    Module.length_eq_of_surjective (M := A ⧸ J) (Ideal.Quotient.mk_surjective (I := J))]
  exact (LinearMap.length_eq_of_bijective f hψ).symm

/-- Over a Noetherian local ring `A`, `localQuotientHilbertSamuel` is invariant under passing to
the maximal-adic completion `AdicCompletion (maximalIdeal A) A`. -/
@[simp]
theorem localQuotientHilbertSamuel_adicCompletion [IsNoetherianRing A] (I : Ideal A) (n : ℕ) :
    localQuotientHilbertSamuel (AdicCompletion (maximalIdeal A) A)
      (I.map (algebraMap A (AdicCompletion (maximalIdeal A) A))) n =
      localQuotientHilbertSamuel A I n :=
  localQuotientHilbertSamuel_adicCompletion_of_fg (maximalIdeal A).fg_of_isNoetherianRing I n

theorem localHilbertSamuel_adicCompletion_of_fg (fg : (maximalIdeal A).FG) (n : ℕ) :
    haveI := AdicCompletion.isLocalRing_of_fg fg
    localHilbertSamuel (AdicCompletion (maximalIdeal A) A) n = localHilbertSamuel A n := by
  let _ := AdicCompletion.isLocalRing_of_fg fg
  rw [localHilbertSamuel_def, localHilbertSamuel_def,
    ← localQuotientHilbertSamuel_adicCompletion_of_fg fg ⊥ n, Ideal.map_bot]

@[simp]
theorem localHilbertSamuel_adicCompletion [IsNoetherianRing A] (n : ℕ) :
    localHilbertSamuel (AdicCompletion (maximalIdeal A) A) n = localHilbertSamuel A n :=
  localHilbertSamuel_adicCompletion_of_fg (maximalIdeal A).fg_of_isNoetherianRing n

end AdicCompletion

end TauCeti
