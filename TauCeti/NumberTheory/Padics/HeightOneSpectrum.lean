/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.ZMod.QuotientRing
public import Mathlib.NumberTheory.Padics.HeightOneSpectrum
public import TauCeti.NumberTheory.LocalField.AbsoluteRamificationIndex
public import TauCeti.RingTheory.DedekindDomain.AdicValuation.ValuativeRel
import Mathlib.LinearAlgebra.FreeModule.StrongRankCondition
import TauCeti.NumberTheory.LocalField.AlgebraicExtension.Basic
import TauCeti.NumberTheory.LocalField.InertiaDegree

/-!
# Valuative and `p`-adic local-field structure at the height-one primes of `ℚ`

Let `R` be the ring of integers of `ℚ` in the sense of `IsIntegralClosure R ℤ ℚ`, and let `v` be a
height-one prime of `R`, corresponding to the rational prime
`p = Rat.HeightOneSpectrum.primesEquiv v`.
This file compares the `v`-adic valuation with `padicValRat p`, identifies the residue field
`R ⧸ v.asIdeal` with `ZMod p`, shows that Mathlib's continuous `ℚ`-algebra equivalences
`Rat.HeightOneSpectrum.adicCompletion.padicEquiv` and `Padic.adicCompletionEquiv` preserve and
reflect the valuative relations on `v.adicCompletion ℚ` and `ℚ_[p]`, and packages
`v.adicCompletion ℚ` as a degree-one `TauCeti.FinitePadicExtension` over `ℚ_[p]`.

## Main definitions

* `Rat.HeightOneSpectrum.quotientEquivZMod`: the ring isomorphism `(R ⧸ v.asIdeal) ≃+* ZMod p`.
* `Rat.HeightOneSpectrum.adicCompletion.finitePadicExtension`: the `TauCeti.FinitePadicExtension`
  structure on `v.adicCompletion ℚ` over `ℚ_[p]` induced by `(padicEquiv v).symm`.

## Main results

* `Rat.HeightOneSpectrum.valuation_eq_one_iff_padicValRat_eq_zero`: a nonzero rational number is
  a unit at `v` exactly when its `p`-adic valuation vanishes.
* `Rat.HeightOneSpectrum.finite_quotient`, `Rat.HeightOneSpectrum.natCard_quotient`,
  `Rat.HeightOneSpectrum.charP_quotient`: finiteness, cardinality, and characteristic of
  `R ⧸ v.asIdeal`.
* `Rat.HeightOneSpectrum.adicCompletion.padicEquiv_vle_iff_vle` and
  `Padic.adicCompletionEquiv_vle_iff_vle`: the canonical equivalences between `v.adicCompletion ℚ`
  and `ℚ_[p]` preserve and reflect `≤ᵥ`.
* `Rat.HeightOneSpectrum.adicCompletion.finrank_padic` and
  `Rat.HeightOneSpectrum.adicCompletion.absoluteRamificationIndex_eq_one`: the local degree and
  absolute ramification index of `v.adicCompletion ℚ` over `ℚ_[p]` are `1`.
-/

public section

open IsDedekindDomain ValuativeRel

local instance (p : Nat.Primes) : Fact (p : ℕ).Prime := ⟨p.2⟩
local instance (q : ℕ) [Fact q.Prime] : StrongRankCondition ℚ_[q] :=
  let hfield : Field ℚ_[q] := @NormedField.toField _ (Padic.normedField q)
  @commRing_strongRankCondition _ hfield.toCommRing (@Field.toNontrivial _ hfield)
attribute [local instance high] HeightOneSpectrum.instAlgebraAdicCompletion

namespace Rat.HeightOneSpectrum

section IntegralClosure

variable {R : Type*} [CommRing R] [Algebra R ℚ] [IsIntegralClosure R ℤ ℚ]

/-- The residue ring `R ⧸ v.asIdeal` at a height-one prime `v` of an integral closure `R` of `ℤ`
in `ℚ` is canonically isomorphic to `ZMod (natGenerator v)`. -/
noncomputable def quotientEquivZMod (v : HeightOneSpectrum R) :
    (R ⧸ v.asIdeal) ≃+* ZMod (natGenerator v) :=
  (Ideal.quotientEquiv v.asIdeal (Ideal.span {(natGenerator v : ℤ)})
    (IsIntegralClosure.intEquiv R) (span_natGenerator v)).trans
    (Int.quotientSpanNatEquivZMod (natGenerator v))

/-- The residue field `R ⧸ v.asIdeal` at a height-one prime of `R` is finite. -/
instance finite_quotient (v : HeightOneSpectrum R) : Finite (R ⧸ v.asIdeal) :=
  have : NeZero (natGenerator v) := ⟨(prime_natGenerator v).ne_zero⟩
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

/-- On a field equipped with a valuative relation, `x ≤ᵥ y` for `y ≠ 0` is membership of `x / y`
in the ring of integers. -/
private theorem vle_iff_div_mem_integer {F : Type*} [Field F] [ValuativeRel F] {x y : F}
    (hy : y ≠ 0) : x ≤ᵥ y ↔ x / y ∈ 𝒪[F] := by
  rw [Valuation.mem_integer_iff, ← (ValuativeRel.valuation F).vle_one_iff]
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · simpa only [div_eq_mul_inv, mul_inv_cancel₀ hy] using mul_vle_mul_left h y⁻¹
  · simpa only [div_mul_cancel₀ _ hy, one_mul] using mul_vle_mul_left h y

/-- Cast `ℚ_[q]` to `ℚ_[p]` as a ring isomorphism along `q = p`. -/
private noncomputable def padicCastRingEquiv {q p : ℕ} [hq : Fact q.Prime] [hp : Fact p.Prime]
    (h : q = p) : ℚ_[q] ≃+* ℚ_[p] := by
  cases h
  obtain rfl : hq = hp := Subsingleton.elim _ _
  exact RingEquiv.refl ℚ_[q]

private theorem padicCastRingEquiv_vle_iff_vle {q p : ℕ} [hq : Fact q.Prime] [hp : Fact p.Prime]
    (h : q = p) (a b : ℚ_[q]) :
    padicCastRingEquiv h a ≤ᵥ padicCastRingEquiv h b ↔ a ≤ᵥ b := by
  cases h
  obtain rfl : hq = hp := Subsingleton.elim _ _
  rfl

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

/-- The ring isomorphism `v.adicCompletion ℚ ≃+* ℚ_[primesEquiv v]` preserves and reflects the
valuative relation. -/
theorem adicCompletion.padicRingEquiv_vle_iff_vle (v : HeightOneSpectrum R)
    (a b : v.adicCompletion ℚ) :
    adicCompletion.padicRingEquiv v a ≤ᵥ adicCompletion.padicRingEquiv v b ↔ a ≤ᵥ b := by
  let e := padicRingEquiv v
  rcases eq_or_ne b 0 with rfl | hb
  · rw [map_zero, vle_zero_iff, vle_zero_iff, map_eq_zero_iff e e.injective]
  · have heb : e b ≠ 0 := (map_ne_zero_iff e e.injective).mpr hb
    rw [vle_iff_div_mem_integer heb, vle_iff_div_mem_integer hb, ← map_div₀,
      Padic.integerRing_eq_subring, v.integer_eq_adicCompletionIntegers (K := ℚ)]
    refine ⟨fun h ↦ ?_, fun h ↦ (padicEquiv_bijOn v).mapsTo h⟩
    obtain ⟨c, hc, hce⟩ := (padicEquiv_bijOn v).surjOn h
    rwa [← e.injective hce]

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
      a ≤ᵥ b := by
  let e := padicRingEquiv v
  have ha : e (e.symm a) = a := e.apply_symm_apply a
  have hb : e (e.symm b) = b := e.apply_symm_apply b
  conv_rhs => rw [← ha, ← hb]
  exact (padicRingEquiv_vle_iff_vle v (e.symm a) (e.symm b)).symm

/-- The ring isomorphism `v.adicCompletion ℚ ≃+* ℚ_[p]` when `R ⧸ v.asIdeal` has prime
characteristic `p`. -/
noncomputable def adicCompletion.padicRingEquivOfCharP (v : HeightOneSpectrum R)
    (p : ℕ) [Fact p.Prime] [CharP (R ⧸ v.asIdeal) p] :
    v.adicCompletion ℚ ≃+* ℚ_[p] :=
  (adicCompletion.padicRingEquiv v).trans <|
    padicCastRingEquiv ((primesEquiv_eq_ringChar_quotient v).trans
      (ringChar.eq (R ⧸ v.asIdeal) p))

/-- `padicRingEquivOfCharP v p` preserves and reflects the valuative relation. -/
@[simp]
theorem adicCompletion.padicRingEquivOfCharP_vle_iff_vle (v : HeightOneSpectrum R)
    (p : ℕ) [Fact p.Prime] [CharP (R ⧸ v.asIdeal) p] (a b : v.adicCompletion ℚ) :
    adicCompletion.padicRingEquivOfCharP v p a ≤ᵥ
      adicCompletion.padicRingEquivOfCharP v p b ↔ a ≤ᵥ b := by
  simp [padicRingEquivOfCharP, padicCastRingEquiv_vle_iff_vle]

/-- The inverse of `padicRingEquivOfCharP v p` preserves and reflects the valuative relation. -/
@[simp]
theorem adicCompletion.padicRingEquivOfCharP_symm_vle_iff_vle (v : HeightOneSpectrum R)
    (p : ℕ) [Fact p.Prime] [CharP (R ⧸ v.asIdeal) p] (a b : ℚ_[p]) :
    (adicCompletion.padicRingEquivOfCharP v p).symm a ≤ᵥ
      (adicCompletion.padicRingEquivOfCharP v p).symm b ↔ a ≤ᵥ b := by
  let e := padicRingEquivOfCharP v p
  have ha : e (e.symm a) = a := e.apply_symm_apply a
  have hb : e (e.symm b) = b := e.apply_symm_apply b
  conv_rhs => rw [← ha, ← hb]
  exact (padicRingEquivOfCharP_vle_iff_vle v p (e.symm a) (e.symm b)).symm

/-- Equip `v.adicCompletion ℚ` as a finite compatible extension of `ℚ_[p]` when `R ⧸ v.asIdeal`
has prime characteristic `p`. -/
@[instance_reducible]
noncomputable def adicCompletion.finitePadicExtension (v : HeightOneSpectrum R)
    (p : ℕ) [Fact p.Prime] [CharP (R ⧸ v.asIdeal) p] :
    TauCeti.FinitePadicExtension (v.adicCompletion ℚ) p :=
  let e : ℚ_[p] ≃+* v.adicCompletion ℚ := (padicRingEquivOfCharP v p).symm
  letI : Algebra ℚ_[p] (v.adicCompletion ℚ) := e.toRingHom.toAlgebra
  haveI : ValuativeExtension ℚ_[p] (v.adicCompletion ℚ) :=
    ⟨fun {a b} ↦ padicRingEquivOfCharP_symm_vle_iff_vle v p a b⟩
  haveI : Module.Finite ℚ_[p] (v.adicCompletion ℚ) :=
    TauCeti.finite_of_valuativeExtension ℚ_[p] (v.adicCompletion ℚ)
  TauCeti.FinitePadicExtension.ofInstances (v.adicCompletion ℚ) p

scoped[RatAdicCompletionPadic] attribute [instance]
  Rat.HeightOneSpectrum.adicCompletion.finitePadicExtension

section ScopedPadic

open scoped RatAdicCompletionPadic

/-- The `ℚ_[p]`-algebra map of `finitePadicExtension` is `(padicRingEquivOfCharP v p).symm`. -/
@[simp]
theorem adicCompletion.algebraMap_padic (v : HeightOneSpectrum R)
    (p : ℕ) [Fact p.Prime] [CharP (R ⧸ v.asIdeal) p] :
    algebraMap ℚ_[p] (v.adicCompletion ℚ) = (padicRingEquivOfCharP v p).symm.toRingHom :=
  RingHom.algebraMap_toAlgebra _

/-- The local degree `[v.adicCompletion ℚ : ℚ_[p]]` is `1`. -/
@[simp]
theorem adicCompletion.finrank_padic (v : HeightOneSpectrum R)
    (p : ℕ) [Fact p.Prime] [CharP (R ⧸ v.asIdeal) p] :
    Module.finrank ℚ_[p] (v.adicCompletion ℚ) = 1 := by
  let e : ℚ_[p] ≃ₐ[ℚ_[p]] v.adicCompletion ℚ :=
    AlgEquiv.ofRingEquiv (f := (padicRingEquivOfCharP v p).symm) fun _ ↦ rfl
  rw [← e.toLinearEquiv.finrank_eq, Module.finrank_self]

/-- The absolute ramification index of `v.adicCompletion ℚ` over `ℚ_[p]` is `1`. -/
-- Not `@[simp]`: `TauCeti.absoluteRamificationIndex_eq_natCastValuation` already simplifies the
-- left-hand side.
theorem adicCompletion.absoluteRamificationIndex_eq_one (v : HeightOneSpectrum R)
    (p : ℕ) [Fact p.Prime] [CharP (R ⧸ v.asIdeal) p] :
    TauCeti.absoluteRamificationIndex (v.adicCompletion ℚ) p = 1 := by
  have hef := TauCeti.ramificationIndex_mul_inertiaDegree ℚ_[p] (v.adicCompletion ℚ)
  rw [finrank_padic v p] at hef
  have he : TauCeti.ramificationIndex ℚ_[p] (v.adicCompletion ℚ) = 1 :=
    Nat.eq_one_of_mul_eq_one_right hef
  rw [TauCeti.absoluteRamificationIndex_eq_natCastValuation,
    TauCeti.natCastValuation_eq_ramificationIndex_mul (K := ℚ_[p]) p
      (Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero),
    Padic.natCastValuation_self, he, mul_one]

end ScopedPadic

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
  let e := adicCompletionRingEquiv R p
  rcases eq_or_ne b 0 with rfl | hb
  · rw [map_zero, vle_zero_iff, vle_zero_iff, map_eq_zero_iff e e.injective]
  · have heb : e b ≠ 0 := (map_ne_zero_iff e e.injective).mpr hb
    rw [vle_iff_div_mem_integer heb, vle_iff_div_mem_integer hb, ← map_div₀,
      Padic.integerRing_eq_subring, v.integer_eq_adicCompletionIntegers (K := ℚ)]
    refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
    · let z : ℤ_[p] := (PadicInt.adicCompletionIntegersEquiv R p).symm ⟨e (a / b), h⟩
      have hz : e z = e (a / b) := by
        rw [adicCompletionRingEquiv_apply, ← PadicInt.coe_adicCompletionIntegersEquiv_apply]
        simp [z]
      rw [← e.injective hz]
      exact z.2
    · rw [adicCompletionRingEquiv_apply,
        ← PadicInt.coe_adicCompletionIntegersEquiv_apply R p ⟨a / b, h⟩]
      exact ((PadicInt.adicCompletionIntegersEquiv R p) ⟨a / b, h⟩).2

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
    (adicCompletionRingEquiv R p).symm a ≤ᵥ (adicCompletionRingEquiv R p).symm b ↔ a ≤ᵥ b := by
  let e := adicCompletionRingEquiv R p
  have ha : e (e.symm a) = a := e.apply_symm_apply a
  have hb : e (e.symm b) = b := e.apply_symm_apply b
  conv_rhs => rw [← ha, ← hb]
  exact (adicCompletionRingEquiv_vle_iff_vle R p (e.symm a) (e.symm b)).symm

end Padic
