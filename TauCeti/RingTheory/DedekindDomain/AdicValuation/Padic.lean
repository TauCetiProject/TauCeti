/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.Padics.HeightOneSpectrum
public import TauCeti.RingTheory.DedekindDomain.AdicValuation.InertiaDegree
public import TauCeti.RingTheory.DedekindDomain.AdicValuation.RamificationIndex
import TauCeti.NumberTheory.LocalField.AlgebraicExtension.Basic
import TauCeti.RingTheory.DedekindDomain.AdicValuation.LocalDegree
import TauCeti.RingTheory.DedekindDomain.AdicValuation.NatCastValuation
import TauCeti.RingTheory.DedekindDomain.AdicValuation.QuotientCard

/-!
# Mixed-characteristic adic completions as finite `p`-adic extensions

Let `B` be a Dedekind domain with fraction field `K` of characteristic zero, and let `w` be a
height-one prime of `B` with finite residue field `B ⧸ w.asIdeal` of prime characteristic `p`.
Contracting `w` to `ℤ` gives a height-one prime `w.underInt` of `ℤ` whose residue field has
characteristic `p`. Composing the degree-one `p`-adic identification
`ℚ_[p] ≃+* w.underInt.adicCompletion ℚ` with `adicCompletionExtension ℚ K w.underInt w` makes the
completion `K_w = w.adicCompletion K` a finite compatible extension of `ℚ_[p]` in the
`AdicCompletionPadic` scope, without any global finiteness assumption on `[K : ℚ]`.

From this tower `ℚ_[p] → ℚ_(w ∩ ℤ) → K_w` we read off:
* the local degree `[K_w : ℚ_[p]] = e(w ∣ ℤ) · f(w ∣ ℤ)`;
* the absolute ramification index `e(K_w / ℚ_[p]) = e(w ∣ ℤ)`;
* the completed integer quotient cardinality
  `#(𝒪_w ⧸ n 𝒪_w) = p ^ ([K_w : ℚ_[p]] · padicValNat p n)` for every nonzero `n : ℕ`, uniformly
  across places coprime to `n`, tamely ramified places, and wildly ramified places.

## Main definitions

* `IsDedekindDomain.HeightOneSpectrum.underInt`: the height-one prime `w.asIdeal.under ℤ` of `ℤ`
  below a height-one prime `w` with finite residue field.
* `IsDedekindDomain.HeightOneSpectrum.adicCompletion.finitePadicExtension`: the
  `TauCeti.FinitePadicExtension (w.adicCompletion K) p` structure in the `AdicCompletionPadic`
  scope.

## Main results

* `IsDedekindDomain.HeightOneSpectrum.prime_ringChar_quotient`: `ringChar (B ⧸ w.asIdeal)` is prime
  whenever `B ⧸ w.asIdeal` is finite.
* `IsDedekindDomain.HeightOneSpectrum.natCard_quotient_eq_pow_inertiaDeg_int`:
  `Nat.card (B ⧸ w.asIdeal) = p ^ w.asIdeal.inertiaDeg ℤ`.
* `IsDedekindDomain.HeightOneSpectrum.finrank_padic_adicCompletion`:
  `Module.finrank ℚ_[p] (w.adicCompletion K) =
    w.asIdeal.ramificationIdx ℤ * w.asIdeal.inertiaDeg ℤ`.
* `IsDedekindDomain.HeightOneSpectrum.absoluteRamificationIndex_adicCompletion`:
  `TauCeti.absoluteRamificationIndex (w.adicCompletion K) p = w.asIdeal.ramificationIdx ℤ`.
* `HeightOneSpectrum.natCard_quotient_span_natCast_adicCompletionIntegers_eq_pow_finrank` (in
  `IsDedekindDomain`):
  `Nat.card (w.adicCompletionIntegers K ⧸ Ideal.span {(n : w.adicCompletionIntegers K)}) =
    p ^ (Module.finrank ℚ_[p] (w.adicCompletion K) * padicValNat p n)` for `n ≠ 0`.

## References

* [J. Neukirch, *Algebraic Number Theory*][neukirch1999], Chapter II, §6 and §8.
-/

public section

open IsDedekindDomain ValuativeRel

namespace IsDedekindDomain.HeightOneSpectrum

section UnderInt

variable {B : Type*} [CommRing B] [IsDedekindDomain B]

/-- At a height-one prime `w` with finite residue field, `ringChar (B ⧸ w.asIdeal)` is prime. -/
theorem prime_ringChar_quotient (w : HeightOneSpectrum B) [Finite (B ⧸ w.asIdeal)] :
    (ringChar (B ⧸ w.asIdeal)).Prime := by
  have : Ideal.IsMaximal w.asIdeal := w.isMaximal
  let _ : Field (B ⧸ w.asIdeal) := Ideal.Quotient.field w.asIdeal
  exact CharP.prime_ringChar (B ⧸ w.asIdeal)

/-- The height-one prime `w.asIdeal.under ℤ` of `ℤ` lying below a height-one prime `w` with finite
residue field. -/
noncomputable def underInt (w : HeightOneSpectrum B) [Finite (B ⧸ w.asIdeal)] :
    HeightOneSpectrum ℤ where
  asIdeal := w.asIdeal.under ℤ
  isPrime := inferInstance
  ne_bot := by
    let p := ringChar (B ⧸ w.asIdeal)
    have hp : p.Prime := w.prime_ringChar_quotient
    have hpB : (p : B) ∈ w.asIdeal :=
      Ideal.Quotient.eq_zero_iff_mem.mp (CharP.cast_eq_zero (B ⧸ w.asIdeal) p)
    have hpZ : (p : ℤ) ∈ w.asIdeal.under ℤ := by
      rw [Ideal.mem_under, map_natCast]
      exact hpB
    intro hbot
    rw [hbot, Ideal.mem_bot, Nat.cast_eq_zero] at hpZ
    exact hp.ne_zero hpZ

/-- The underlying ideal of `w.underInt` is `w.asIdeal.under ℤ`. -/
@[simp]
theorem asIdeal_underInt (w : HeightOneSpectrum B) [Finite (B ⧸ w.asIdeal)] :
    w.underInt.asIdeal = w.asIdeal.under ℤ :=
  (rfl)

/-- `w.asIdeal` lies over `w.underInt.asIdeal`. -/
instance liesOver_underInt (w : HeightOneSpectrum B) [Finite (B ⧸ w.asIdeal)] :
    w.asIdeal.LiesOver w.underInt.asIdeal :=
  ⟨rfl⟩

/-- If `B ⧸ w.asIdeal` has characteristic `p`, so does `ℤ ⧸ w.underInt.asIdeal`. -/
theorem charP_quotient_underInt (w : HeightOneSpectrum B) [Finite (B ⧸ w.asIdeal)]
    (p : ℕ) [CharP (B ⧸ w.asIdeal) p] :
    CharP (ℤ ⧸ w.underInt.asIdeal) p :=
  ((algebraMap (ℤ ⧸ w.underInt.asIdeal) (B ⧸ w.asIdeal)).charP_iff
    (FaithfulSMul.algebraMap_injective (ℤ ⧸ w.underInt.asIdeal) (B ⧸ w.asIdeal)) p).mpr
    inferInstance

/-- If `B ⧸ w.asIdeal` has characteristic `p`, the residue field `ℤ ⧸ w.underInt.asIdeal` has
cardinality `p`. -/
theorem natCard_quotient_underInt (w : HeightOneSpectrum B) [Finite (B ⧸ w.asIdeal)]
    (p : ℕ) [CharP (B ⧸ w.asIdeal) p] :
    Nat.card (ℤ ⧸ w.underInt.asIdeal) = p := by
  have := w.charP_quotient_underInt p
  rw [Rat.HeightOneSpectrum.natCard_quotient,
    Rat.HeightOneSpectrum.natGenerator_eq_ringChar_quotient, ringChar.eq _ p]

/-- If `B ⧸ w.asIdeal` is finite of characteristic `p`, its cardinality is
`p ^ w.asIdeal.inertiaDeg ℤ`. -/
theorem natCard_quotient_eq_pow_inertiaDeg_int (w : HeightOneSpectrum B) [Finite (B ⧸ w.asIdeal)]
    (p : ℕ) [CharP (B ⧸ w.asIdeal) p] :
    Nat.card (B ⧸ w.asIdeal) = p ^ w.asIdeal.inertiaDeg ℤ := by
  have : Ideal.IsMaximal w.underInt.asIdeal := w.underInt.isMaximal
  have : Ideal.IsMaximal w.asIdeal := w.isMaximal
  let _ : Field (ℤ ⧸ w.underInt.asIdeal) := Ideal.Quotient.field w.underInt.asIdeal
  let _ : Fintype (ℤ ⧸ w.underInt.asIdeal) := .ofFinite _
  let _ : Fintype (B ⧸ w.asIdeal) := .ofFinite _
  rw [Ideal.inertiaDeg_eq_of_isMaximal w.underInt.asIdeal w.asIdeal,
    ← w.natCard_quotient_underInt p, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
  exact Module.card_eq_pow_finrank

end UnderInt

section PadicCompletion

variable {B : Type*} [CommRing B] [IsDedekindDomain B]
  {K : Type*} [Field K] [CharZero K] [Algebra B K] [IsFractionRing B K]

/-- Equip a characteristic-zero adic completion `w.adicCompletion K` with finite residue field of
prime characteristic `p` as a finite compatible extension of `ℚ_[p]`, available in the
`AdicCompletionPadic` scope. -/
@[instance_reducible]
noncomputable def adicCompletion.finitePadicExtension (w : HeightOneSpectrum B) (K : Type*)
    [Field K] [CharZero K] [Algebra B K] [IsFractionRing B K] [Finite (B ⧸ w.asIdeal)]
    (p : ℕ) [Fact p.Prime] [CharP (B ⧸ w.asIdeal) p] :
    TauCeti.FinitePadicExtension (w.adicCompletion K) p :=
  haveI : CharP (ℤ ⧸ w.underInt.asIdeal) p := w.charP_quotient_underInt p
  let e₀ : ℚ_[p] →+* w.underInt.adicCompletion ℚ :=
    (Rat.HeightOneSpectrum.adicCompletion.padicRingEquivOfCharP w.underInt p).symm.toRingHom
  let φ : ℚ_[p] →+* w.adicCompletion K :=
    (adicCompletionExtension ℚ K w.underInt w).comp e₀
  letI : Algebra ℚ_[p] (w.adicCompletion K) := φ.toAlgebra
  haveI : ValuativeExtension ℚ_[p] (w.adicCompletion K) :=
    ⟨fun {a b} ↦
      (adicCompletionExtension_vle_iff_vle ℚ K w.underInt w (e₀ a) (e₀ b)).trans
        (Rat.HeightOneSpectrum.adicCompletion.padicRingEquivOfCharP_symm_vle_iff_vle
          w.underInt p a b)⟩
  haveI : Module.Finite ℚ_[p] (w.adicCompletion K) :=
    TauCeti.finite_of_valuativeExtension ℚ_[p] (w.adicCompletion K)
  TauCeti.FinitePadicExtension.ofInstances (w.adicCompletion K) p

scoped[AdicCompletionPadic] attribute [instance]
  IsDedekindDomain.HeightOneSpectrum.charP_quotient_underInt
  IsDedekindDomain.HeightOneSpectrum.adicCompletion.finitePadicExtension

open scoped RatAdicCompletionPadic AdicCompletionExtension AdicCompletionPadic

/-- The `ℚ_[p]`-algebra map on `w.adicCompletion K` factors through
`w.underInt.adicCompletion ℚ`. -/
@[simp]
theorem algebraMap_padic_adicCompletion (w : HeightOneSpectrum B) [Finite (B ⧸ w.asIdeal)]
    (p : ℕ) [Fact p.Prime] [CharP (B ⧸ w.asIdeal) p] :
    algebraMap ℚ_[p] (w.adicCompletion K) =
      (adicCompletionExtension ℚ K w.underInt w).comp
        (Rat.HeightOneSpectrum.adicCompletion.padicRingEquivOfCharP w.underInt p).symm.toRingHom :=
  RingHom.algebraMap_toAlgebra _

/-- `ℚ_[p] → w.underInt.adicCompletion ℚ → w.adicCompletion K` is a scalar tower. -/
theorem isScalarTower_padic_adicCompletion (w : HeightOneSpectrum B) [Finite (B ⧸ w.asIdeal)]
    (p : ℕ) [Fact p.Prime] [CharP (B ⧸ w.asIdeal) p] :
    IsScalarTower ℚ_[p] (w.underInt.adicCompletion ℚ) (w.adicCompletion K) :=
  IsScalarTower.of_algebraMap_eq' <| by
    rw [w.algebraMap_padic_adicCompletion p, Rat.HeightOneSpectrum.adicCompletion.algebraMap_padic,
      algebraMap_adicCompletionExtensionAlgebra]

scoped[AdicCompletionPadic] attribute [instance]
  IsDedekindDomain.HeightOneSpectrum.isScalarTower_padic_adicCompletion

/-- The local degree `[w.adicCompletion K : ℚ_[p]]` is
`w.asIdeal.ramificationIdx ℤ * w.asIdeal.inertiaDeg ℤ`. -/
@[simp]
theorem finrank_padic_adicCompletion (w : HeightOneSpectrum B) [Finite (B ⧸ w.asIdeal)]
    (p : ℕ) [Fact p.Prime] [CharP (B ⧸ w.asIdeal) p] :
    Module.finrank ℚ_[p] (w.adicCompletion K) =
      w.asIdeal.ramificationIdx ℤ * w.asIdeal.inertiaDeg ℤ := by
  -- State the tower formula over an abstract field `k` so typeclass search does not unfold
  -- `Padic.normedField` to synthesize `Module.Free ℚ_[p]`.
  have htower (k : Type) [Field k] [Algebra k (w.underInt.adicCompletion ℚ)]
      [Algebra k (w.adicCompletion K)]
      [IsScalarTower k (w.underInt.adicCompletion ℚ) (w.adicCompletion K)] :
      Module.finrank k (w.adicCompletion K) =
        Module.finrank k (w.underInt.adicCompletion ℚ) *
          Module.finrank (w.underInt.adicCompletion ℚ) (w.adicCompletion K) :=
    (Module.finrank_mul_finrank k (w.underInt.adicCompletion ℚ) (w.adicCompletion K)).symm
  rw [htower ℚ_[p], Rat.HeightOneSpectrum.adicCompletion.finrank_padic w.underInt p, one_mul,
    finrank_adicCompletion w.underInt w]

/-- The absolute ramification index of `w.adicCompletion K` over `ℚ_[p]` is the global ramification
index `w.asIdeal.ramificationIdx ℤ`. -/
-- Not `@[simp]`: `TauCeti.absoluteRamificationIndex_eq_natCastValuation` already simplifies the
-- left-hand side.
theorem absoluteRamificationIndex_adicCompletion (w : HeightOneSpectrum B) [Finite (B ⧸ w.asIdeal)]
    (p : ℕ) [Fact p.Prime] [CharP (B ⧸ w.asIdeal) p] :
    TauCeti.absoluteRamificationIndex (w.adicCompletion K) p =
      w.asIdeal.ramificationIdx ℤ := by
  rw [TauCeti.absoluteRamificationIndex_tower (w.underInt.adicCompletion ℚ) p (w.adicCompletion K),
    Rat.HeightOneSpectrum.adicCompletion.absoluteRamificationIndex_eq_one w.underInt p, mul_one,
    ramificationIndex_adicCompletion w.underInt w]

/-- For any nonzero natural number `n`, the quotient of `w.adicCompletionIntegers K` by `(n)` has
cardinality `p ^ ([w.adicCompletion K : ℚ_[p]] * padicValNat p n)`. -/
theorem natCard_quotient_span_natCast_adicCompletionIntegers_eq_pow_finrank
    (w : HeightOneSpectrum B) [Finite (B ⧸ w.asIdeal)]
    (p : ℕ) [Fact p.Prime] [CharP (B ⧸ w.asIdeal) p] {n : ℕ} (hn : n ≠ 0) :
    Nat.card (w.adicCompletionIntegers K ⧸ Ideal.span {(n : w.adicCompletionIntegers K)}) =
      p ^ (Module.finrank ℚ_[p] (w.adicCompletion K) * padicValNat p n) := by
  have hnK : (n : w.adicCompletion K) ≠ 0 := Nat.cast_ne_zero.mpr hn
  have hnB : (n : B) ≠ 0 := fun h ↦
    hnK (by rw [← map_natCast (algebraMap B (w.adicCompletion K)), h, map_zero])
  rw [w.natCard_quotient_span_natCast_adicCompletionIntegers_eq_pow hnB,
    w.natCard_quotient_eq_pow_inertiaDeg_int p,
    ← w.natCastValuation_completion_eq_multiplicity_span n hnK,
    TauCeti.natCastValuation_eq_absoluteRamificationIndex_mul_padicValNat (w.adicCompletion K) p n
      hn,
    w.absoluteRamificationIndex_adicCompletion p, ← pow_mul, w.finrank_padic_adicCompletion p]
  exact congrArg (p ^ ·) (by ring)

end PadicCompletion

end IsDedekindDomain.HeightOneSpectrum
