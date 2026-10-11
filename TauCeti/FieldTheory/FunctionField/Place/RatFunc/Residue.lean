/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.FunctionField.Place.RatFunc.Order
public import TauCeti.FieldTheory.FunctionField.Place.Residue
public import TauCeti.RingTheory.Polynomial.Resultant.AdjoinRoot

/-!
# Local factors at the places of the rational function field

This file computes the norm of the residue of a function at the places of `k(x)`, the local
factor `TauCeti.Place.normResidueOrOne` that enters the evaluation of a function on a divisor.

At the finite place `P_q` of a monic irreducible `q`, the residue field is `k[X] / (q)`, and the
norm of the residue of a polynomial `r` is the norm of `r` in `k[X] / (q)`, which is the resultant
`Res(q, r)` (`AdjoinRoot.norm_mk_eq_resultant`). At the place at infinity the residue field is
`k`, and a function of degree `0` takes the value `lc(f.num)`, its denominator being monic.

## Main results

* `TauCeti.Place.coe_normResidueOrOne_adicOfIrreducible`: at the place of a monic irreducible `q`,
  the local factor of a function `f` regular and nonvanishing there is
  `Res(q, f.num) / Res(q, f.denom)`.
* `TauCeti.Place.coe_normResidueOrOne_infty`: at the place at infinity, the local factor of a
  function of degree `0` is the leading coefficient of its numerator.
-/

public section

noncomputable section

open IsDedekindDomain Polynomial

namespace TauCeti

namespace Place

variable {k : Type*} [Field k]

/-- The norm of the residue of a polynomial `r` at the place of a monic irreducible `q` is the
resultant `Res(q, r)`: the residue field is `k[X] / (q)`, where the norm is a resultant. The place
is written as the place `ofPrime` of the prime `(q)`, which is what `adicOfIrreducible` unfolds
to. -/
private theorem norm_residue_algebraMap_ofIrreducible {q : k[X]} (hq : Irreducible q)
    (hqm : q.Monic) (r : k[X]) :
    Algebra.norm k (algebraMap k[X]
      (ofPrime k (RatFunc k) (HeightOneSpectrum.ofIrreducible hq)).ResidueField r) =
      q.resultant r := by
  rw [← quotientAlgEquivResidueFieldOfPrime_mk, Algebra.norm_eq_of_algEquiv,
    ← Ideal.quotientEquivAlgOfEq_mk k (HeightOneSpectrum.ofIrreducible_asIdeal hq).symm,
    Algebra.norm_eq_of_algEquiv]
  exact AdjoinRoot.norm_mk_eq_resultant hqm r

/-- **The local factor of `k(x)` at a finite place is a quotient of resultants.** If `q` is monic
irreducible and divides neither the numerator nor the denominator of `f`, the norm of the residue
of `f` at the place of `q` is `Res(q, f.num) / Res(q, f.denom)`. -/
theorem coe_normResidueOrOne_adicOfIrreducible {q : k[X]} (hq : Irreducible q) (hqm : q.Monic)
    {f : (RatFunc k)ˣ} (hnum : ¬q ∣ (f : RatFunc k).num) (hden : ¬q ∣ (f : RatFunc k).denom) :
    ((adicOfIrreducible hq).normResidueOrOne f : k) =
      q.resultant (f : RatFunc k).num / q.resultant (f : RatFunc k).denom := by
  have hf := (ord_adicOfIrreducible_eq_zero_iff hq f.ne_zero).2 ⟨hnum, hden⟩
  rw [adicOfIrreducible_def] at hf ⊢
  set P := ofPrime k (RatFunc k) (HeightOneSpectrum.ofIrreducible hq)
  -- `f · f.denom = f.num`, read in the valuation ring of `P`
  have hres : IsLocalRing.residue P.integers ⟨f, P.mem_integers_iff_ord_nonneg.2 hf.ge⟩ *
      algebraMap k[X] P.ResidueField (f : RatFunc k).denom =
      algebraMap k[X] P.ResidueField (f : RatFunc k).num := by
    rw [algebraMap_residueField, algebraMap_residueField, ← map_mul]
    congr 1
    ext
    have hcoe (r : k[X]) : ((algebraMap k[X] P.integers r : P.integers) : RatFunc k) =
        algebraMap k[X] (RatFunc k) r :=
      (IsScalarTower.algebraMap_apply k[X] P.integers (RatFunc k) r).symm
    rw [MulMemClass.coe_mul, hcoe, hcoe, Subtype.coe_mk]
    nth_rw 1 [← RatFunc.num_div_denom (f : RatFunc k)]
    exact div_mul_cancel₀ _ (RatFunc.algebraMap_ne_zero (f : RatFunc k).denom_ne_zero)
  have hden0 : q.resultant (f : RatFunc k).denom ≠ 0 :=
    resultant_ne_zero _ _ ((hq.coprime_iff_not_dvd).2 hden)
  rw [normResidueOrOne_of_ord_eq_zero hf, coe_normResidue, coe_residueUnit, eq_div_iff hden0,
    ← norm_residue_algebraMap_ofIrreducible hq hqm, ← norm_residue_algebraMap_ofIrreducible hq hqm,
    ← map_mul, hres]

/-- **The local factor of `k(x)` at infinity.** A function of degree `0` takes at the place at
infinity the value `lc(f.num)`, the denominator being monic; this is the norm of its residue,
the residue field at infinity being `k`. -/
theorem coe_normResidueOrOne_infty {f : (RatFunc k)ˣ} (hf : (f : RatFunc k).intDegree = 0) :
    ((infty k).normResidueOrOne f : k) = (f : RatFunc k).num.leadingCoeff := by
  have hord : (infty k).ord (f : RatFunc k) = 0 := by rw [ord_infty, hf, neg_zero]
  have hlt := valuation_infty_sub_leadingCoeff_div_lt_one f.ne_zero hf
  rw [(RatFunc.monic_denom _).leadingCoeff, div_one] at hlt
  have hres : IsLocalRing.residue (infty k).integers
      ⟨f, (infty k).mem_integers_iff_ord_nonneg.2 hord.ge⟩ =
        algebraMap k (infty k).ResidueField (f : RatFunc k).num.leadingCoeff := by
    rw [algebraMap_residueField, ← sub_eq_zero, ← map_sub,
      residue_eq_zero_iff_valuation_lt_one]
    exact hlt
  rw [normResidueOrOne_of_ord_eq_zero hord, coe_normResidue, coe_residueUnit, hres,
    Algebra.norm_algebraMap, ← degree_eq_finrank, degree_infty, pow_one]

end Place

end TauCeti
