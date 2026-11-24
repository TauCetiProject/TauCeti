/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.Padics.HeightOneSpectrum
public import TauCeti.RingTheory.DedekindDomain.AdicValuation.InertiaDegree
public import TauCeti.RingTheory.DedekindDomain.AdicValuation.RamificationIndex
import Mathlib.LinearAlgebra.FreeModule.StrongRankCondition
import TauCeti.NumberTheory.LocalField.AlgebraicExtension.Basic
import TauCeti.NumberTheory.LocalField.InertiaDegree
import TauCeti.RingTheory.DedekindDomain.AdicValuation.LocalDegree
import TauCeti.RingTheory.RamificationInertia.Inertia

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
* the relative and absolute ramification indices `e(K_w / ℚ_[p]) = e(w ∣ ℤ)` and residue degree
  `[𝓀[K_w] : 𝓀[ℚ_[p]]] = f(w ∣ ℤ)`;
* the completed integer quotient cardinality
  `#(𝒪_w ⧸ n 𝒪_w) = p ^ ([K_w : ℚ_[p]] · padicValNat p n)` for every nonzero `n : ℕ`, uniformly
  across places coprime to `n`, tamely ramified places, and wildly ramified places.

## Main definitions

* `IsDedekindDomain.HeightOneSpectrum.underInt`: the height-one prime `w.asIdeal.under ℤ` of `ℤ`
  below a height-one prime `w` with finite residue field.
* `IsDedekindDomain.HeightOneSpectrum.adicCompletion.padicAlgebra` and
  `IsDedekindDomain.HeightOneSpectrum.adicCompletion.finitePadicExtension`: the `ℚ_[p]`-algebra and
  `TauCeti.FinitePadicExtension (w.adicCompletion K) p` structures in the `AdicCompletionPadic`
  scope.

## Main results

* `IsDedekindDomain.HeightOneSpectrum.prime_ringChar_quotient`: `ringChar (B ⧸ w.asIdeal)` is prime
  whenever `B ⧸ w.asIdeal` is finite.
* `IsDedekindDomain.HeightOneSpectrum.natCard_quotient_eq_pow_inertiaDeg_int`:
  `Nat.card (B ⧸ w.asIdeal) = p ^ w.asIdeal.inertiaDeg ℤ`.
* `IsDedekindDomain.HeightOneSpectrum.isScalarTower_padic_adicCompletion`: the scalar tower
  `ℚ_[p] → w.underInt.adicCompletion ℚ → w.adicCompletion K` in the `AdicCompletionPadic` and
  `AdicCompletionExtension` scopes.
* `IsDedekindDomain.HeightOneSpectrum.finrank_padic_adicCompletion`,
  `IsDedekindDomain.HeightOneSpectrum.ramificationIndex_padic_adicCompletion`,
  `IsDedekindDomain.HeightOneSpectrum.finrank_residueField_padic_adicCompletion`, and
  `IsDedekindDomain.HeightOneSpectrum.absoluteRamificationIndex_adicCompletion`: local degree,
  ramification index, residue degree, and absolute ramification index of `w.adicCompletion K` over
  `ℚ_[p]`.
* `HeightOneSpectrum.natCard_quotient_span_natCast_adicCompletionIntegers_eq_pow_finrank` (in
  `IsDedekindDomain`):
  `Nat.card (w.adicCompletionIntegers K ⧸ Ideal.span {(n : w.adicCompletionIntegers K)}) =
    p ^ (Module.finrank ℚ_[p] (w.adicCompletion K) * padicValNat p n)` for `n ≠ 0`.

## References

* J. Neukirch, *Algebraic Number Theory*, Chapter II, §6 and §8.
-/

public section

open IsDedekindDomain ValuativeRel

local instance (q : ℕ) [Fact q.Prime] : StrongRankCondition ℚ_[q] :=
  let hfield : Field ℚ_[q] := @NormedField.toField _ (Padic.normedField q)
  @commRing_strongRankCondition _ hfield.toCommRing (@Field.toNontrivial _ hfield)

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
theorem underInt_asIdeal (w : HeightOneSpectrum B) [Finite (B ⧸ w.asIdeal)] :
    w.underInt.asIdeal = w.asIdeal.under ℤ :=
  (rfl)

/-- Contracting a height-one prime of `ℤ` to `ℤ` returns the same prime. -/
@[simp]
theorem underInt_self (v : HeightOneSpectrum ℤ) : v.underInt = v :=
  HeightOneSpectrum.ext v.asIdeal.comap_id

/-- `w.asIdeal` lies over `w.underInt.asIdeal`. -/
instance liesOver_underInt (w : HeightOneSpectrum B) [Finite (B ⧸ w.asIdeal)] :
    w.asIdeal.LiesOver w.underInt.asIdeal :=
  ⟨rfl⟩

/-- If `B ⧸ w.asIdeal` has characteristic `p`, so does `ℤ ⧸ w.underInt.asIdeal`.
Registered as a scoped instance in `AdicCompletionPadic`. -/
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
  rw [Ideal.natCard_quotient_eq_pow_inertiaDeg w.underInt.asIdeal w.asIdeal,
    w.natCard_quotient_underInt p]

end UnderInt

section PadicCompletion

variable {B : Type*} [CommRing B] [IsDedekindDomain B]
  {K : Type*} [Field K] [CharZero K] [Algebra B K] [IsFractionRing B K]

/-- The `ℚ_[p]`-algebra structure on a characteristic-zero adic completion `w.adicCompletion K`
with finite residue field of prime characteristic `p`, induced via `w.underInt.adicCompletion ℚ`.
Marked `@[irreducible]` so unification of `ResidueField` module instances does not unfold
`RingHom.toAlgebra` across distinct `ℚ_[p]`-algebra structures. -/
@[irreducible]
noncomputable def adicCompletion.padicAlgebra (w : HeightOneSpectrum B) (K : Type*)
    [Field K] [CharZero K] [Algebra B K] [IsFractionRing B K] [Finite (B ⧸ w.asIdeal)]
    (p : ℕ) [Fact p.Prime] [CharP (B ⧸ w.asIdeal) p] :
    Algebra ℚ_[p] (w.adicCompletion K) :=
  have : CharP (ℤ ⧸ w.underInt.asIdeal) p := w.charP_quotient_underInt p
  ((adicCompletionExtension ℚ K w.underInt w).comp
    (Rat.HeightOneSpectrum.adicCompletion.padicRingEquivOfCharP w.underInt p).symm.toRingHom
  ).toAlgebra

/-- Equip a characteristic-zero adic completion `w.adicCompletion K` with finite residue field of
prime characteristic `p` as a finite compatible extension of `ℚ_[p]`, available in the
`AdicCompletionPadic` scope. -/
@[instance_reducible]
noncomputable def adicCompletion.finitePadicExtension (w : HeightOneSpectrum B) (K : Type*)
    [Field K] [CharZero K] [Algebra B K] [IsFractionRing B K] [Finite (B ⧸ w.asIdeal)]
    (p : ℕ) [Fact p.Prime] [CharP (B ⧸ w.asIdeal) p] :
    TauCeti.FinitePadicExtension (w.adicCompletion K) p :=
  have hvle : @ValuativeExtension ℚ_[p] (w.adicCompletion K) _ _ _ _
      (adicCompletion.padicAlgebra w K p) := by
    unfold adicCompletion.padicAlgebra
    have : CharP (ℤ ⧸ w.underInt.asIdeal) p := w.charP_quotient_underInt p
    let e₀ : ℚ_[p] →+* w.underInt.adicCompletion ℚ :=
      (Rat.HeightOneSpectrum.adicCompletion.padicRingEquivOfCharP w.underInt p).symm.toRingHom
    let _ : Algebra ℚ_[p] (w.adicCompletion K) :=
      ((adicCompletionExtension ℚ K w.underInt w).comp e₀).toAlgebra
    exact ⟨fun {a b} ↦
      (adicCompletionExtension_vle_iff_vle ℚ K w.underInt w (e₀ a) (e₀ b)).trans
        (Rat.HeightOneSpectrum.adicCompletion.padicRingEquivOfCharP_symm_vle_iff_vle
          w.underInt p a b)⟩
  { algebra := adicCompletion.padicAlgebra w K p
    toValuativeExtension := hvle
    toModuleFinite := by
      let _ : Algebra ℚ_[p] (w.adicCompletion K) := adicCompletion.padicAlgebra w K p
      exact TauCeti.finite_of_valuativeExtension ℚ_[p] (w.adicCompletion K) }

scoped[AdicCompletionPadic] attribute [instance]
  IsDedekindDomain.HeightOneSpectrum.charP_quotient_underInt
  IsDedekindDomain.HeightOneSpectrum.adicCompletion.finitePadicExtension

open scoped AdicCompletionExtension AdicCompletionPadic

/-- The `ℚ_[p]`-algebra map on `w.adicCompletion K` factors through
`w.underInt.adicCompletion ℚ`. -/
@[simp]
theorem algebraMap_padic_adicCompletion (w : HeightOneSpectrum B) [Finite (B ⧸ w.asIdeal)]
    (p : ℕ) [Fact p.Prime] [CharP (B ⧸ w.asIdeal) p] :
    algebraMap ℚ_[p] (w.adicCompletion K) =
      (adicCompletionExtension ℚ K w.underInt w).comp
        (Rat.HeightOneSpectrum.adicCompletion.padicRingEquivOfCharP
          w.underInt p).symm.toRingHom := by
  unfold TauCeti.FinitePadicExtension.toAlgebra adicCompletion.finitePadicExtension
    adicCompletion.padicAlgebra
  exact RingHom.algebraMap_toAlgebra _

/-- On a height-one prime `v` of `ℤ`, the `AdicCompletionPadic` algebra map agrees with
`(padicRingEquivOfCharP v p).symm`. -/
private theorem algebraMap_padic_adicCompletion_int (v : HeightOneSpectrum ℤ)
    (p : ℕ) [Fact p.Prime] [hchar : CharP (ℤ ⧸ v.asIdeal) p] :
    algebraMap ℚ_[p] (v.adicCompletion ℚ) =
      (Rat.HeightOneSpectrum.adicCompletion.padicRingEquivOfCharP v p).symm.toRingHom := by
  rw [v.algebraMap_padic_adicCompletion (K := ℚ) p]
  have hgen : ∀ (u : HeightOneSpectrum ℤ) [v.asIdeal.LiesOver u.asIdeal]
      [CharP (ℤ ⧸ u.asIdeal) p], u = v →
      (adicCompletionExtension ℚ ℚ u v).comp
        (Rat.HeightOneSpectrum.adicCompletion.padicRingEquivOfCharP u p).symm.toRingHom =
        (Rat.HeightOneSpectrum.adicCompletion.padicRingEquivOfCharP v p).symm.toRingHom := by
    rintro u hlies hu_char rfl
    obtain rfl : hu_char = hchar := Subsingleton.elim _ _
    have := hlies
    have hid : adicCompletionExtension ℚ ℚ u u = RingHom.id (u.adicCompletion ℚ) :=
      (eq_adicCompletionExtension_of_continuous ℚ ℚ u u (f := RingHom.id (u.adicCompletion ℚ))
        continuous_id fun x ↦ by simp).symm
    rw [hid, RingHom.id_comp]
  exact @hgen v.underInt v.liesOver_underInt (v.charP_quotient_underInt p) v.underInt_self

/-- `ℚ_[p] → w.underInt.adicCompletion ℚ → w.adicCompletion K` is a scalar tower for the
`AdicCompletionPadic` `ℚ_[p]`-algebra structures on both completions and the
`AdicCompletionExtension` algebra structure on `w.adicCompletion K` over
`w.underInt.adicCompletion ℚ`. Registered as a scoped instance in `AdicCompletionPadic`. -/
theorem isScalarTower_padic_adicCompletion (w : HeightOneSpectrum B) [Finite (B ⧸ w.asIdeal)]
    (p : ℕ) [Fact p.Prime] [CharP (B ⧸ w.asIdeal) p] :
    IsScalarTower ℚ_[p] (w.underInt.adicCompletion ℚ) (w.adicCompletion K) :=
  IsScalarTower.of_algebraMap_eq' <| by
    rw [w.algebraMap_padic_adicCompletion p, algebraMap_padic_adicCompletion_int w.underInt p,
      algebraMap_adicCompletionExtensionAlgebra]

scoped[AdicCompletionPadic] attribute [instance]
  IsDedekindDomain.HeightOneSpectrum.isScalarTower_padic_adicCompletion

private theorem finrank_padic_adicCompletion_int (v : HeightOneSpectrum ℤ)
    (p : ℕ) [Fact p.Prime] [CharP (ℤ ⧸ v.asIdeal) p] :
    Module.finrank ℚ_[p] (v.adicCompletion ℚ) = 1 := by
  let e : ℚ_[p] ≃ₐ[ℚ_[p]] v.adicCompletion ℚ :=
    AlgEquiv.ofRingEquiv
      (f := (Rat.HeightOneSpectrum.adicCompletion.padicRingEquivOfCharP v p).symm)
      fun x ↦ (DFunLike.congr_fun (algebraMap_padic_adicCompletion_int v p) x).symm
  rw [← e.toLinearEquiv.finrank_eq, Module.finrank_self]

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
  rw [htower ℚ_[p], finrank_padic_adicCompletion_int w.underInt p, one_mul,
    finrank_adicCompletion w.underInt w]

/-- The ramification index of `w.adicCompletion K` over `ℚ_[p]` is `w.asIdeal.ramificationIdx ℤ`. -/
@[simp]
theorem ramificationIndex_padic_adicCompletion (w : HeightOneSpectrum B) [Finite (B ⧸ w.asIdeal)]
    (p : ℕ) [Fact p.Prime] [CharP (B ⧸ w.asIdeal) p] :
    TauCeti.ramificationIndex ℚ_[p] (w.adicCompletion K) =
      w.asIdeal.ramificationIdx ℤ := by
  have hef := TauCeti.ramificationIndex_mul_inertiaDegree ℚ_[p] (w.underInt.adicCompletion ℚ)
  rw [finrank_padic_adicCompletion_int w.underInt p] at hef
  rw [TauCeti.ramificationIndex_tower (K := ℚ_[p]) (L := w.underInt.adicCompletion ℚ)
      (w.adicCompletion K),
    Nat.eq_one_of_mul_eq_one_right hef, one_mul, ramificationIndex_adicCompletion w.underInt w]

/-- The residue degree `[𝓀[w.adicCompletion K] : 𝓀[ℚ_[p]]]` is `w.asIdeal.inertiaDeg ℤ`. -/
@[simp]
theorem finrank_residueField_padic_adicCompletion (w : HeightOneSpectrum B)
    [Finite (B ⧸ w.asIdeal)] (p : ℕ) [Fact p.Prime] [CharP (B ⧸ w.asIdeal) p] :
    Module.finrank 𝓀[ℚ_[p]] 𝓀[w.adicCompletion K] =
      w.asIdeal.inertiaDeg ℤ := by
  have hef := TauCeti.ramificationIndex_mul_inertiaDegree ℚ_[p] (w.underInt.adicCompletion ℚ)
  rw [finrank_padic_adicCompletion_int w.underInt p] at hef
  rw [← TauCeti.inertiaDegree_def,
    TauCeti.inertiaDegree_tower (K := ℚ_[p]) (L := w.underInt.adicCompletion ℚ)
      (M := w.adicCompletion K),
    Nat.eq_one_of_mul_eq_one_left hef, one_mul, TauCeti.inertiaDegree_def,
    finrank_residueField_adicCompletion w.underInt w]

/-- The absolute ramification index of `w.adicCompletion K` over `ℚ_[p]` is the global ramification
index `w.asIdeal.ramificationIdx ℤ`. -/
-- Not `@[simp]`: `TauCeti.absoluteRamificationIndex_eq_natCastValuation` already simplifies the
-- left-hand side.
theorem absoluteRamificationIndex_adicCompletion (w : HeightOneSpectrum B) [Finite (B ⧸ w.asIdeal)]
    (p : ℕ) [Fact p.Prime] [CharP (B ⧸ w.asIdeal) p] :
    TauCeti.absoluteRamificationIndex (w.adicCompletion K) p =
      w.asIdeal.ramificationIdx ℤ := by
  rw [TauCeti.absoluteRamificationIndex_eq_natCastValuation,
    TauCeti.natCastValuation_eq_ramificationIndex_mul (K := ℚ_[p]) p
      (Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero),
    Padic.natCastValuation_self, w.ramificationIndex_padic_adicCompletion p, mul_one]

/-- For any nonzero natural number `n`, the quotient of `w.adicCompletionIntegers K` by `(n)` has
cardinality `p ^ ([w.adicCompletion K : ℚ_[p]] * padicValNat p n)`. -/
theorem natCard_quotient_span_natCast_adicCompletionIntegers_eq_pow_finrank
    (w : HeightOneSpectrum B) [Finite (B ⧸ w.asIdeal)]
    (p : ℕ) [Fact p.Prime] [CharP (B ⧸ w.asIdeal) p] {n : ℕ} (hn : n ≠ 0) :
    Nat.card (w.adicCompletionIntegers K ⧸ Ideal.span {(n : w.adicCompletionIntegers K)}) =
      p ^ (Module.finrank ℚ_[p] (w.adicCompletion K) * padicValNat p n) := by
  let e := w.integerEquivAdicCompletionIntegers (K := K)
  have hmap : Ideal.map e.toRingHom (Ideal.span {(n : 𝒪[w.adicCompletion K])}) =
      Ideal.span {(n : w.adicCompletionIntegers K)} := by
    rw [Ideal.map_span, Set.image_singleton, RingEquiv.toRingHom_eq_coe, map_natCast]
  rw [← Nat.card_congr (Ideal.quotientEquiv _ _ e hmap.symm).toEquiv,
    TauCeti.natCard_quotient_span_natCast_eq_pow_finrank_mul_padicValNat (w.adicCompletion K) p n
      hn]

end PadicCompletion

end IsDedekindDomain.HeightOneSpectrum
