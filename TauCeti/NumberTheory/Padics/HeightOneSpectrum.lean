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
This file records that `ℤ` has infinitely many height-one prime ideals, compares the `v`-adic
valuation with the `p`-adic valuation `padicValRat p`, identifies the residue field
`R ⧸ v.asIdeal` with `ZMod p`, shows that Mathlib's continuous `ℚ`-algebra equivalences
`Rat.HeightOneSpectrum.adicCompletion.padicEquiv` and `Padic.adicCompletionEquiv` preserve and
reflect the valuative relations on `v.adicCompletion ℚ` and `ℚ_[p]`, and packages
`v.adicCompletion ℚ` as a degree-one `TauCeti.FinitePadicExtension` over `ℚ_[p]` in the
`RatAdicCompletionPadic` scope.

## Main definitions

* `Rat.HeightOneSpectrum.quotientEquivZMod`: the ring isomorphism `(R ⧸ v.asIdeal) ≃+* ZMod p`.
* `Rat.HeightOneSpectrum.adicCompletion.padicAlgebra` and
  `Rat.HeightOneSpectrum.adicCompletion.finitePadicExtension`: the `ℚ_[p]`-algebra and
  `TauCeti.FinitePadicExtension` structures on `v.adicCompletion ℚ` over `ℚ_[p]` induced by
  `(padicRingEquivOfCharP v p).symm` (activated as a scoped instance via
  `open scoped RatAdicCompletionPadic`).

## Main results

* `Infinite (HeightOneSpectrum ℤ)`: `ℤ` has infinitely many height-one prime ideals.
* `Rat.HeightOneSpectrum.valuation_eq_one_iff_padicValRat_eq_zero`: a nonzero rational number is
  a unit at `v` exactly when its `p`-adic valuation vanishes.
* `Rat.HeightOneSpectrum.quotientEquivZMod_mk`, `Rat.HeightOneSpectrum.finite_quotient`,
  `Rat.HeightOneSpectrum.natCard_quotient`, `Rat.HeightOneSpectrum.charP_quotient`: action on
  quotient classes, finiteness, cardinality, and characteristic of `R ⧸ v.asIdeal`.
* `Rat.HeightOneSpectrum.adicCompletion.padicEquiv_vle_iff_vle`,
  `Padic.adicCompletionEquiv_vle_iff_vle`,
  `Rat.HeightOneSpectrum.adicCompletion.padicRingEquivOfCharP_primesEquiv`, and
  `Rat.HeightOneSpectrum.adicCompletion.continuous_padicRingEquivOfCharP`: `≤ᵥ`-compatibility,
  agreement at `primesEquiv v`, and continuity of the canonical equivalences between
  `v.adicCompletion ℚ` and `ℚ_[p]`.
* `Rat.HeightOneSpectrum.adicCompletion.finrank_padic`,
  `Rat.HeightOneSpectrum.adicCompletion.ramificationIndex_padic`,
  `Rat.HeightOneSpectrum.adicCompletion.finrank_residueField_padic`, and
  `Rat.HeightOneSpectrum.adicCompletion.absoluteRamificationIndex_eq_one`: in the
  `RatAdicCompletionPadic` scope, the local degree, ramification index, residue degree, and
  absolute ramification index of `v.adicCompletion ℚ` over `ℚ_[p]` are `1`.
-/

public section

open IsDedekindDomain ValuativeRel

local instance (p : Nat.Primes) : Fact (p : ℕ).Prime := ⟨p.property⟩
local instance (q : ℕ) [Fact q.Prime] : StrongRankCondition ℚ_[q] :=
  let hfield : Field ℚ_[q] := @NormedField.toField _ (Padic.normedField q)
  @commRing_strongRankCondition _ hfield.toCommRing (@Field.toNontrivial _ hfield)
attribute [local instance high] HeightOneSpectrum.instAlgebraAdicCompletion

namespace TauCeti

/-- `ℤ` has infinitely many height-one prime ideals, in bijection with the rational primes. -/
instance : Infinite (HeightOneSpectrum ℤ) :=
  Infinite.of_surjective _ Rat.HeightOneSpectrum.primesEquiv.surjective

end TauCeti

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

private theorem continuous_padicCastRingEquiv {q p : ℕ} [hq : Fact q.Prime] [hp : Fact p.Prime]
    (h : q = p) : Continuous (padicCastRingEquiv h) := by
  cases h
  obtain rfl : hq = hp := Subsingleton.elim _ _
  exact continuous_id

private theorem continuous_padicCastRingEquiv_symm {q p : ℕ} [hq : Fact q.Prime]
    [hp : Fact p.Prime] (h : q = p) : Continuous (padicCastRingEquiv h).symm := by
  cases h
  obtain rfl : hq = hp := Subsingleton.elim _ _
  exact continuous_id

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
  (adicCompletion.padicRingEquiv v).trans <|
    padicCastRingEquiv ((primesEquiv_eq_ringChar_quotient v).trans
      (ringChar.eq (R ⧸ v.asIdeal) p))

/-- At `p = primesEquiv v`, `padicRingEquivOfCharP v (primesEquiv v)` agrees with
`padicRingEquiv v`. -/
@[simp]
theorem adicCompletion.padicRingEquivOfCharP_primesEquiv (v : HeightOneSpectrum R) :
    letI := charP_quotient v
    adicCompletion.padicRingEquivOfCharP v (primesEquiv v) = adicCompletion.padicRingEquiv v := by
  have := charP_quotient v
  ext x
  simp [padicRingEquivOfCharP, padicCastRingEquiv]

/-- `padicRingEquivOfCharP v p` is continuous. -/
theorem adicCompletion.continuous_padicRingEquivOfCharP (v : HeightOneSpectrum R)
    (p : ℕ) [Fact p.Prime] [CharP (R ⧸ v.asIdeal) p] :
    Continuous (adicCompletion.padicRingEquivOfCharP v p) :=
  (continuous_padicCastRingEquiv _).comp (continuous_padicRingEquiv v)

/-- The inverse of `padicRingEquivOfCharP v p` is continuous. -/
theorem adicCompletion.continuous_padicRingEquivOfCharP_symm (v : HeightOneSpectrum R)
    (p : ℕ) [Fact p.Prime] [CharP (R ⧸ v.asIdeal) p] :
    Continuous (adicCompletion.padicRingEquivOfCharP v p).symm :=
  (continuous_padicRingEquiv_symm v).comp (continuous_padicCastRingEquiv_symm _)

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
      (adicCompletion.padicRingEquivOfCharP v p).symm b ↔ a ≤ᵥ b :=
  (adicCompletion.padicRingEquivOfCharP v p).symm_vle_iff_vle
    (padicRingEquivOfCharP_vle_iff_vle v p) a b

/-- The `ℚ_[p]`-algebra structure on `v.adicCompletion ℚ` induced by
`(padicRingEquivOfCharP v p).symm` when `R ⧸ v.asIdeal` has prime characteristic `p`.
Marked `@[irreducible]` so unification of `ResidueField` module instances does not unfold
`RingHom.toAlgebra` across distinct `ℚ_[p]`-algebra structures. -/
@[irreducible]
noncomputable def adicCompletion.padicAlgebra (v : HeightOneSpectrum R)
    (p : ℕ) [Fact p.Prime] [CharP (R ⧸ v.asIdeal) p] :
    Algebra ℚ_[p] (v.adicCompletion ℚ) :=
  (adicCompletion.padicRingEquivOfCharP v p).symm.toRingHom.toAlgebra

/-- Equip `v.adicCompletion ℚ` as a finite compatible extension of `ℚ_[p]` via
`(padicRingEquivOfCharP v p).symm` when `R ⧸ v.asIdeal` has prime characteristic `p`.
Registered as a scoped instance in `RatAdicCompletionPadic`. -/
@[instance_reducible]
noncomputable def adicCompletion.finitePadicExtension (v : HeightOneSpectrum R)
    (p : ℕ) [Fact p.Prime] [CharP (R ⧸ v.asIdeal) p] :
    TauCeti.FinitePadicExtension (v.adicCompletion ℚ) p :=
  have hvle : @ValuativeExtension ℚ_[p] (v.adicCompletion ℚ) _ _ _ _
      (adicCompletion.padicAlgebra v p) := by
    unfold adicCompletion.padicAlgebra
    let _ : Algebra ℚ_[p] (v.adicCompletion ℚ) :=
      (padicRingEquivOfCharP v p).symm.toRingHom.toAlgebra
    exact ⟨fun {a b} ↦ padicRingEquivOfCharP_symm_vle_iff_vle v p a b⟩
  { algebra := adicCompletion.padicAlgebra v p
    toValuativeExtension := hvle
    toModuleFinite := by
      let _ : Algebra ℚ_[p] (v.adicCompletion ℚ) := adicCompletion.padicAlgebra v p
      exact TauCeti.finite_of_valuativeExtension ℚ_[p] (v.adicCompletion ℚ) }

scoped[RatAdicCompletionPadic] attribute [instance]
  Rat.HeightOneSpectrum.adicCompletion.finitePadicExtension

section ScopedPadic

open scoped RatAdicCompletionPadic

/-- The `ℚ_[p]`-algebra map of `finitePadicExtension` is `(padicRingEquivOfCharP v p).symm`. -/
@[simp]
theorem adicCompletion.algebraMap_padic (v : HeightOneSpectrum R)
    (p : ℕ) [Fact p.Prime] [CharP (R ⧸ v.asIdeal) p] :
    algebraMap ℚ_[p] (v.adicCompletion ℚ) = (padicRingEquivOfCharP v p).symm.toRingHom := by
  unfold TauCeti.FinitePadicExtension.toAlgebra adicCompletion.finitePadicExtension
    adicCompletion.padicAlgebra
  exact RingHom.algebraMap_toAlgebra _

/-- The local degree `[v.adicCompletion ℚ : ℚ_[p]]` is `1`. -/
@[simp]
theorem adicCompletion.finrank_padic (v : HeightOneSpectrum R)
    (p : ℕ) [Fact p.Prime] [CharP (R ⧸ v.asIdeal) p] :
    Module.finrank ℚ_[p] (v.adicCompletion ℚ) = 1 := by
  let e : ℚ_[p] ≃ₐ[ℚ_[p]] v.adicCompletion ℚ :=
    AlgEquiv.ofRingEquiv (f := (padicRingEquivOfCharP v p).symm) fun x ↦
      (DFunLike.congr_fun (algebraMap_padic v p) x).symm
  rw [← e.toLinearEquiv.finrank_eq, Module.finrank_self]

/-- The ramification index of `v.adicCompletion ℚ` over `ℚ_[p]` is `1`. -/
@[simp]
theorem adicCompletion.ramificationIndex_padic (v : HeightOneSpectrum R)
    (p : ℕ) [Fact p.Prime] [CharP (R ⧸ v.asIdeal) p] :
    TauCeti.ramificationIndex ℚ_[p] (v.adicCompletion ℚ) = 1 := by
  have hef := TauCeti.ramificationIndex_mul_inertiaDegree ℚ_[p] (v.adicCompletion ℚ)
  rw [finrank_padic v p] at hef
  exact Nat.eq_one_of_mul_eq_one_right hef

/-- The residue degree `[𝓀[v.adicCompletion ℚ] : 𝓀[ℚ_[p]]]` is `1`. -/
@[simp]
theorem adicCompletion.finrank_residueField_padic (v : HeightOneSpectrum R)
    (p : ℕ) [Fact p.Prime] [CharP (R ⧸ v.asIdeal) p] :
    Module.finrank 𝓀[ℚ_[p]] 𝓀[v.adicCompletion ℚ] = 1 := by
  rw [← TauCeti.inertiaDegree_def]
  have hef := TauCeti.ramificationIndex_mul_inertiaDegree ℚ_[p] (v.adicCompletion ℚ)
  rw [finrank_padic v p] at hef
  exact Nat.eq_one_of_mul_eq_one_left hef

/-- The absolute ramification index of `v.adicCompletion ℚ` over `ℚ_[p]` is `1`. -/
-- Not `@[simp]`: `TauCeti.absoluteRamificationIndex_eq_natCastValuation` already simplifies the
-- left-hand side.
theorem adicCompletion.absoluteRamificationIndex_eq_one (v : HeightOneSpectrum R)
    (p : ℕ) [Fact p.Prime] [CharP (R ⧸ v.asIdeal) p] :
    TauCeti.absoluteRamificationIndex (v.adicCompletion ℚ) p = 1 := by
  rw [TauCeti.absoluteRamificationIndex_eq_natCastValuation,
    TauCeti.natCastValuation_eq_ramificationIndex_mul (K := ℚ_[p]) p
      (Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero),
    Padic.natCastValuation_self, ramificationIndex_padic, mul_one]

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
