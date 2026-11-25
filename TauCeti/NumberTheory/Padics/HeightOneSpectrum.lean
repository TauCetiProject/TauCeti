/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.Padics.HeightOneSpectrum
public import Mathlib.NumberTheory.Padics.ValuativeRel
public import TauCeti.RingTheory.DedekindDomain.AdicValuation.ValuativeRel
import Mathlib.Data.ZMod.QuotientRing
import TauCeti.NumberTheory.LocalField.Padic
import TauCeti.RingTheory.Valuation.ValuativeRel.Basic

/-!
# Valuative and residue-field structure at the height-one primes of `ℚ`

Let `R` be the ring of integers of `ℚ` in the sense of `IsIntegralClosure R ℤ ℚ`, and let `v` be a
height-one prime of `R`, corresponding to the rational prime
`p = Rat.HeightOneSpectrum.primesEquiv v`.
This file records that `ℤ` has infinitely many height-one prime ideals, compares the `v`-adic
valuation with the `p`-adic valuation `padicValRat p`, identifies the height-one prime of `R`
corresponding to a rational prime `p` with the ideal `(p)`, identifies the residue field
`R ⧸ v.asIdeal` with `ZMod p`, and shows that Mathlib's continuous `ℚ`-algebra equivalences
`Rat.HeightOneSpectrum.adicCompletion.padicEquiv` and `Padic.adicCompletionEquiv` preserve and
reflect the valuative relations on `v.adicCompletion ℚ` and `ℚ_[p]`.

## Main definitions

* `Rat.HeightOneSpectrum.quotientEquivZMod`: the ring isomorphism `(R ⧸ v.asIdeal) ≃+* ZMod p`.
* `Rat.HeightOneSpectrum.adicCompletion.padicRingEquiv`,
  `Rat.HeightOneSpectrum.adicCompletion.padicRingEquivOfCharP`, and
  `Padic.adicCompletionRingEquiv`: the underlying ring isomorphisms between `v.adicCompletion ℚ`
  and `ℚ_[p]`.

## Main results

* `Infinite (HeightOneSpectrum ℤ)`: `ℤ` has infinitely many height-one prime ideals.
* `Rat.HeightOneSpectrum.fact_prime_natGenerator`: the rational prime `natGenerator v` of `v` is
  prime, as an instance.
* `Rat.HeightOneSpectrum.valuation_eq_one_iff_padicValRat_eq_zero`: a nonzero rational number is
  a unit at `v` exactly when its `p`-adic valuation vanishes.
* `Rat.HeightOneSpectrum.asIdeal_primesEquiv_symm`: the height-one prime of `R` corresponding to
  the prime `p` is `(p)`.
* `Rat.HeightOneSpectrum.liesOver_asIdeal_primesEquiv_symm_iff`: a proper ideal lies over it
  exactly when it contains `p`.
* `Rat.HeightOneSpectrum.quotientEquivZMod_mk`, `Rat.HeightOneSpectrum.finite_quotient`,
  `Rat.HeightOneSpectrum.natCard_quotient`, `Rat.HeightOneSpectrum.charP_quotient`: action on
  quotient classes, finiteness, cardinality, and characteristic of `R ⧸ v.asIdeal`.
* `Rat.HeightOneSpectrum.adicCompletion.padicEquiv_vle_iff_vle`,
  `Padic.adicCompletionEquiv_vle_iff_vle`,
  `Rat.HeightOneSpectrum.adicCompletion.padicRingEquivOfCharP_primesEquiv`, and
  `Rat.HeightOneSpectrum.adicCompletion.continuous_padicRingEquivOfCharP`: `≤ᵥ`-compatibility,
  agreement at `primesEquiv v`, and continuity of the canonical equivalences between
  `v.adicCompletion ℚ` and `ℚ_[p]`.
-/

public section

open IsDedekindDomain ValuativeRel

local instance (p : Nat.Primes) : Fact (p : ℕ).Prime := ⟨p.property⟩
attribute [local instance high] HeightOneSpectrum.instAlgebraAdicCompletion

namespace TauCeti

/-- `ℤ` has infinitely many height-one prime ideals, in bijection with the rational primes. -/
instance : Infinite (HeightOneSpectrum ℤ) :=
  Infinite.of_surjective _ Rat.HeightOneSpectrum.primesEquiv.surjective

end TauCeti

namespace Rat.HeightOneSpectrum

section IntegralClosure

variable {R : Type*} [CommRing R] [Algebra R ℚ] [IsIntegralClosure R ℤ ℚ]

/-- The rational prime of a height-one prime of the ring of integers of `ℚ` is prime. -/
instance fact_prime_natGenerator (v : HeightOneSpectrum R) : Fact (natGenerator v).Prime :=
  ⟨prime_natGenerator v⟩

/-- The residue ring `R ⧸ v.asIdeal` at a height-one prime `v` of an integral closure `R` of `ℤ`
in `ℚ` is canonically isomorphic to `ZMod (natGenerator v)`. -/
noncomputable def quotientEquivZMod (v : HeightOneSpectrum R) :
    (R ⧸ v.asIdeal) ≃+* ZMod (natGenerator v) :=
  (Ideal.quotientEquiv v.asIdeal (Ideal.span {(natGenerator v : ℤ)})
    (IsIntegralClosure.intEquiv R) (span_natGenerator v)).trans
    (Int.quotientSpanNatEquivZMod (natGenerator v))

/-- `quotientEquivZMod v` sends the residue class of `r` to `IsIntegralClosure.intEquiv R r`
modulo `natGenerator v`. -/
@[simp]
theorem quotientEquivZMod_mk (v : HeightOneSpectrum R) (r : R) :
    quotientEquivZMod v (Ideal.Quotient.mk v.asIdeal r) = IsIntegralClosure.intEquiv R r :=
  (congrArg (Int.quotientSpanNatEquivZMod (natGenerator v))
    (Ideal.quotientEquiv_mk v.asIdeal (Ideal.span {(natGenerator v : ℤ)})
      (IsIntegralClosure.intEquiv R) (span_natGenerator v) r)).trans <|
    DFunLike.congr_fun (Int.quotientSpanNatEquivZMod_comp_Quotient_mk (natGenerator v))
      (IsIntegralClosure.intEquiv R r)

/-- The residue field `R ⧸ v.asIdeal` at a height-one prime of `R` is finite. -/
instance finite_quotient (v : HeightOneSpectrum R) : Finite (R ⧸ v.asIdeal) :=
  Finite.of_equiv _ (quotientEquivZMod v).symm.toEquiv

/-- The residue field `R ⧸ v.asIdeal` has cardinality `natGenerator v`. -/
@[simp]
theorem natCard_quotient (v : HeightOneSpectrum R) :
    Nat.card (R ⧸ v.asIdeal) = natGenerator v := by
  rw [Nat.card_congr (quotientEquivZMod v).toEquiv, Nat.card_zmod]

/-- The residue field `R ⧸ v.asIdeal` has characteristic `natGenerator v`. -/
theorem charP_quotient (v : HeightOneSpectrum R) :
    CharP (R ⧸ v.asIdeal) (natGenerator v) :=
  ((quotientEquivZMod v).toRingHom.charP_iff (quotientEquivZMod v).injective
    (natGenerator v)).mpr inferInstance

/-- The generator `natGenerator v` is the ring characteristic of `R ⧸ v.asIdeal`. -/
theorem natGenerator_eq_ringChar_quotient (v : HeightOneSpectrum R) :
    natGenerator v = ringChar (R ⧸ v.asIdeal) :=
  (@ringChar.eq (R ⧸ v.asIdeal) _ (natGenerator v) (charP_quotient v)).symm

/-- The prime `primesEquiv v` is the ring characteristic of `R ⧸ v.asIdeal`. -/
theorem primesEquiv_eq_ringChar_quotient [IsDedekindDomain R] (v : HeightOneSpectrum R) :
    (primesEquiv v : ℕ) = ringChar (R ⧸ v.asIdeal) :=
  natGenerator_eq_ringChar_quotient v

end IntegralClosure

variable {R : Type*} [CommRing R] [Algebra R ℚ] [IsIntegralClosure R ℤ ℚ] [IsDedekindDomain R]
  [IsFractionRing R ℚ]

/-- A nonzero rational number is a unit at the height-one prime `v` exactly when its `p`-adic
valuation vanishes, for `p` the rational prime corresponding to `v`. -/
theorem valuation_eq_one_iff_padicValRat_eq_zero (v : HeightOneSpectrum R) {x : ℚ}
    (hx : x ≠ 0) : v.valuation ℚ x = 1 ↔ padicValRat (primesEquiv v) x = 0 := by
  rw [(valuation_equiv_padicValuation v).eq_one_iff_eq_one]
  simp [Rat.padicValuation, hx]

omit [IsFractionRing R ℚ] in
/-- The height-one prime of `R` corresponding to the prime `p` under `primesEquiv` is the ideal
`(p)`. -/
@[simp]
theorem asIdeal_primesEquiv_symm (p : Nat.Primes) :
    ((primesEquiv (R := R)).symm p).asIdeal = Ideal.span {((p : ℕ) : R)} := by
  -- Mathlib defines the inverse of `primesEquiv` as the image of `(p)` under `intEquiv.symm`.
  change (Ideal.span {((p : ℕ) : ℤ)}).map (IsIntegralClosure.intEquiv R).symm = _
  rw [Ideal.map_span, Set.image_singleton, map_natCast]

omit [IsFractionRing R ℚ] in
/-- A proper ideal `P` of an `R`-algebra lies over the height-one prime of `R` corresponding to
the prime `p` exactly when `p ∈ P`. -/
theorem liesOver_asIdeal_primesEquiv_symm_iff {S : Type*} [CommRing S] [Algebra R S] {P : Ideal S}
    (hP : P ≠ ⊤) (p : Nat.Primes) :
    P.LiesOver ((primesEquiv (R := R)).symm p).asIdeal ↔ ((p : ℕ) : S) ∈ P := by
  have hp : Prime ((p : ℕ) : R) := by
    rw [← map_natCast (IsIntegralClosure.intEquiv R).symm, MulEquiv.prime_iff]
    exact Nat.prime_iff_prime_int.1 p.property
  rw [asIdeal_primesEquiv_symm, Ideal.liesOver_span_iff hP hp]
  simp

/-- Cast `ℚ_[q]` to `ℚ_[p]` as a continuous `ℚ`-algebra isomorphism along `q = p`. -/
private noncomputable def padicCastEquiv {q p : ℕ} [hq : Fact q.Prime] [hp : Fact p.Prime]
    (h : q = p) : ℚ_[q] ≃A[ℚ] ℚ_[p] := by
  cases h
  exact Subsingleton.elim hq hp ▸ ContinuousAlgEquiv.refl ℚ ℚ_[q]

private theorem padicCastEquiv_elim {q p : ℕ} [hq : Fact q.Prime] [hp : Fact p.Prime] (h : q = p)
    (P : ∀ (r : ℕ) [Fact r.Prime], (ℚ_[q] ≃A[ℚ] ℚ_[r]) → Prop)
    (hrefl : P q (ContinuousAlgEquiv.refl ℚ ℚ_[q])) :
    P p (padicCastEquiv h) := by
  cases h
  obtain rfl : hq = hp := Subsingleton.elim _ _
  exact hrefl

@[simp]
private theorem padicCastEquiv_self {q : ℕ} {hq₁ hq₂ : Fact q.Prime}
    (h : q = q) : padicCastEquiv (hq := hq₁) (hp := hq₂) h = ContinuousAlgEquiv.refl ℚ ℚ_[q] :=
  eq_of_heq <| padicCastEquiv_elim h
    (fun _ _ e ↦ HEq e (ContinuousAlgEquiv.refl ℚ ℚ_[q])) HEq.rfl

private theorem padicCastEquiv_vle_iff_vle {q p : ℕ} [Fact q.Prime] [Fact p.Prime]
    (h : q = p) (a b : ℚ_[q]) :
    padicCastEquiv h a ≤ᵥ padicCastEquiv h b ↔ a ≤ᵥ b :=
  padicCastEquiv_elim h (fun _ _ e ↦ e a ≤ᵥ e b ↔ a ≤ᵥ b) Iff.rfl

/-- The underlying ring isomorphism `v.adicCompletion ℚ ≃+* ℚ_[primesEquiv v]` of
`Rat.HeightOneSpectrum.adicCompletion.padicEquiv`, avoiding `ℚ`-algebra instance synthesis on
`v.adicCompletion ℚ`. -/
noncomputable def adicCompletion.padicRingEquiv (v : HeightOneSpectrum R) :
    v.adicCompletion ℚ ≃+* ℚ_[primesEquiv v] :=
  (adicCompletion.padicEquiv v).toRingEquiv

/-- `padicRingEquiv v` agrees on elements with `padicEquiv v`. -/
@[simp]
theorem adicCompletion.padicRingEquiv_apply (v : HeightOneSpectrum R) (x : v.adicCompletion ℚ) :
    adicCompletion.padicRingEquiv v x = adicCompletion.padicEquiv v x :=
  (rfl)

/-- `padicRingEquiv v` is continuous. -/
theorem adicCompletion.continuous_padicRingEquiv (v : HeightOneSpectrum R) :
    Continuous (adicCompletion.padicRingEquiv v) :=
  (adicCompletion.padicEquiv v).continuous

/-- The inverse of `padicRingEquiv v` is continuous. -/
theorem adicCompletion.continuous_padicRingEquiv_symm (v : HeightOneSpectrum R) :
    Continuous (adicCompletion.padicRingEquiv v).symm :=
  (adicCompletion.padicEquiv v).symm.continuous

/-- The ring isomorphism `v.adicCompletion ℚ ≃+* ℚ_[primesEquiv v]` preserves and reflects the
valuative relation. -/
theorem adicCompletion.padicRingEquiv_vle_iff_vle (v : HeightOneSpectrum R)
    (a b : v.adicCompletion ℚ) :
    adicCompletion.padicRingEquiv v a ≤ᵥ adicCompletion.padicRingEquiv v b ↔ a ≤ᵥ b := by
  refine TauCeti.ValuativeRel.map_vle_map_iff_of_mem_integer_iff (padicRingEquiv v)
    (fun x ↦ ?_) a b
  rw [padicRingEquiv_apply, Padic.integerRing_eq_subring,
    v.integer_eq_adicCompletionIntegers (K := ℚ)]
  refine ⟨fun h ↦ ?_, fun h ↦ (padicEquiv_bijOn v).mapsTo h⟩
  obtain ⟨c, hc, hce⟩ := (padicEquiv_bijOn v).surjOn h
  rwa [← (padicEquiv v).injective hce]

/-- The continuous `ℚ`-algebra equivalence `v.adicCompletion ℚ ≃A[ℚ] ℚ_[primesEquiv v]` preserves
and reflects the valuative relation. -/
@[simp]
theorem adicCompletion.padicEquiv_vle_iff_vle (v : HeightOneSpectrum R)
    (a b : v.adicCompletion ℚ) :
    adicCompletion.padicEquiv v a ≤ᵥ adicCompletion.padicEquiv v b ↔ a ≤ᵥ b :=
  padicRingEquiv_vle_iff_vle v a b

/-- The inverse ring isomorphism `ℚ_[primesEquiv v] ≃+* v.adicCompletion ℚ` preserves and reflects
the valuative relation. -/
@[simp]
theorem adicCompletion.padicRingEquiv_symm_vle_iff_vle (v : HeightOneSpectrum R)
    (a b : ℚ_[primesEquiv v]) :
    (adicCompletion.padicRingEquiv v).symm a ≤ᵥ (adicCompletion.padicRingEquiv v).symm b ↔
      a ≤ᵥ b :=
  (adicCompletion.padicRingEquiv v).symm_vle_iff_vle (padicRingEquiv_vle_iff_vle v) a b

/-- The ring isomorphism `v.adicCompletion ℚ ≃+* ℚ_[p]` when `R ⧸ v.asIdeal` has prime
characteristic `p`. -/
noncomputable def adicCompletion.padicRingEquivOfCharP (v : HeightOneSpectrum R)
    (p : ℕ) [Fact p.Prime] [CharP (R ⧸ v.asIdeal) p] :
    v.adicCompletion ℚ ≃+* ℚ_[p] :=
  (adicCompletion.padicRingEquiv v).trans
    (padicCastEquiv ((primesEquiv_eq_ringChar_quotient v).trans
      (ringChar.eq (R ⧸ v.asIdeal) p))).toRingEquiv

/-- At `p = primesEquiv v`, `padicRingEquivOfCharP v (primesEquiv v)` agrees with
`padicRingEquiv v`. -/
@[simp]
theorem adicCompletion.padicRingEquivOfCharP_primesEquiv (v : HeightOneSpectrum R) :
    letI := charP_quotient v
    adicCompletion.padicRingEquivOfCharP v (primesEquiv v) = adicCompletion.padicRingEquiv v := by
  have := charP_quotient v
  ext x
  simp [padicRingEquivOfCharP]

/-- `padicRingEquivOfCharP v p` is continuous. -/
theorem adicCompletion.continuous_padicRingEquivOfCharP (v : HeightOneSpectrum R)
    (p : ℕ) [Fact p.Prime] [CharP (R ⧸ v.asIdeal) p] :
    Continuous (adicCompletion.padicRingEquivOfCharP v p) :=
  (padicCastEquiv _).continuous.comp (continuous_padicRingEquiv v)

/-- The inverse of `padicRingEquivOfCharP v p` is continuous. -/
theorem adicCompletion.continuous_padicRingEquivOfCharP_symm (v : HeightOneSpectrum R)
    (p : ℕ) [Fact p.Prime] [CharP (R ⧸ v.asIdeal) p] :
    Continuous (adicCompletion.padicRingEquivOfCharP v p).symm :=
  (continuous_padicRingEquiv_symm v).comp (padicCastEquiv _).symm.continuous

/-- `padicRingEquivOfCharP v p` preserves and reflects the valuative relation. -/
@[simp]
theorem adicCompletion.padicRingEquivOfCharP_vle_iff_vle (v : HeightOneSpectrum R)
    (p : ℕ) [Fact p.Prime] [CharP (R ⧸ v.asIdeal) p] (a b : v.adicCompletion ℚ) :
    adicCompletion.padicRingEquivOfCharP v p a ≤ᵥ
      adicCompletion.padicRingEquivOfCharP v p b ↔ a ≤ᵥ b :=
  (padicCastEquiv_vle_iff_vle _ _ _).trans (padicRingEquiv_vle_iff_vle v a b)

/-- The inverse of `padicRingEquivOfCharP v p` preserves and reflects the valuative relation. -/
@[simp]
theorem adicCompletion.padicRingEquivOfCharP_symm_vle_iff_vle (v : HeightOneSpectrum R)
    (p : ℕ) [Fact p.Prime] [CharP (R ⧸ v.asIdeal) p] (a b : ℚ_[p]) :
    (adicCompletion.padicRingEquivOfCharP v p).symm a ≤ᵥ
      (adicCompletion.padicRingEquivOfCharP v p).symm b ↔ a ≤ᵥ b :=
  (adicCompletion.padicRingEquivOfCharP v p).symm_vle_iff_vle
    (padicRingEquivOfCharP_vle_iff_vle v p) a b

end Rat.HeightOneSpectrum

namespace Padic

open Rat.HeightOneSpectrum

variable (R : Type*) [CommRing R] [IsDedekindDomain R] [Algebra R ℚ] [IsFractionRing R ℚ]
  [IsIntegralClosure R ℤ ℚ]

/-- The underlying ring isomorphism `ℚ_[p] ≃+* (primesEquiv.symm p).adicCompletion ℚ` of
`Padic.adicCompletionEquiv`. -/
noncomputable def adicCompletionRingEquiv (p : Nat.Primes) :
    ℚ_[p] ≃+* ((primesEquiv (R := R)).symm p).adicCompletion ℚ :=
  (adicCompletionEquiv R p).toRingEquiv

/-- `adicCompletionRingEquiv R p` agrees on elements with `adicCompletionEquiv R p`. -/
@[simp]
theorem adicCompletionRingEquiv_apply (p : Nat.Primes) (x : ℚ_[p]) :
    adicCompletionRingEquiv R p x = adicCompletionEquiv R p x :=
  (rfl)

/-- The ring isomorphism `ℚ_[p] ≃+* (primesEquiv.symm p).adicCompletion ℚ` preserves and reflects
the valuative relation. -/
theorem adicCompletionRingEquiv_vle_iff_vle (p : Nat.Primes) (a b : ℚ_[p]) :
    adicCompletionRingEquiv R p a ≤ᵥ adicCompletionRingEquiv R p b ↔ a ≤ᵥ b := by
  let v := (primesEquiv (R := R)).symm p
  refine TauCeti.ValuativeRel.map_vle_map_iff_of_mem_integer_iff (adicCompletionRingEquiv R p)
    (fun x ↦ ?_) a b
  rw [adicCompletionRingEquiv_apply, Padic.integerRing_eq_subring,
    v.integer_eq_adicCompletionIntegers (K := ℚ)]
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · let z : ℤ_[p] := (PadicInt.adicCompletionIntegersEquiv R p).symm
      ⟨adicCompletionEquiv R p x, h⟩
    have hz : adicCompletionEquiv R p z = adicCompletionEquiv R p x := by
      rw [← PadicInt.coe_adicCompletionIntegersEquiv_apply]
      simp [z]
    rw [← (adicCompletionEquiv R p).injective hz]
    exact z.property
  · rw [← PadicInt.coe_adicCompletionIntegersEquiv_apply R p ⟨x, h⟩]
    exact ((PadicInt.adicCompletionIntegersEquiv R p) ⟨x, h⟩).property

/-- The continuous `ℚ`-algebra equivalence `ℚ_[p] ≃A[ℚ] (primesEquiv.symm p).adicCompletion ℚ`
preserves and reflects the valuative relation. -/
@[simp]
theorem adicCompletionEquiv_vle_iff_vle (p : Nat.Primes) (a b : ℚ_[p]) :
    adicCompletionEquiv R p a ≤ᵥ adicCompletionEquiv R p b ↔ a ≤ᵥ b :=
  adicCompletionRingEquiv_vle_iff_vle R p a b

/-- The inverse ring isomorphism `(primesEquiv.symm p).adicCompletion ℚ ≃+* ℚ_[p]` preserves and
reflects the valuative relation. -/
@[simp]
theorem adicCompletionRingEquiv_symm_vle_iff_vle (p : Nat.Primes)
    (a b : ((primesEquiv (R := R)).symm p).adicCompletion ℚ) :
    (adicCompletionRingEquiv R p).symm a ≤ᵥ (adicCompletionRingEquiv R p).symm b ↔ a ≤ᵥ b :=
  (adicCompletionRingEquiv R p).symm_vle_iff_vle (adicCompletionRingEquiv_vle_iff_vle R p) a b

end Padic
