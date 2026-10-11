/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.FunctionField.Divisor.Eval
public import TauCeti.FieldTheory.FunctionField.Divisor.RatFunc
public import TauCeti.RingTheory.Polynomial.Resultant.AdjoinRoot

/-!
# Weil reciprocity on the rational function field

For nonzero functions `f` and `g` whose divisors have disjoint supports, **Weil reciprocity** is
the identity

`f(div g) = g(div f)`,

where `f(D) = ∏_P N_{k(P)/k}(f(P)) ^ (coeff D P)` is the evaluation of a function on a divisor
(`TauCeti.Divisor.eval`). This file proves it on the rational function field `k(x)`, over an
arbitrary field `k`. This is the base case of Weil reciprocity: on an algebraic function field the
identity is reduced to `k(x)` through norms.

The local factors of `k(x)` are resultants. At the finite place `P_q` of a monic irreducible `q`,
the residue field is `k[X] / (q)`, and the norm of the residue of a polynomial `r` is the norm of
`r` in `k[X] / (q)`, which is the resultant `Res(q, r)` (`AdjoinRoot.norm_mk_eq_resultant`). At the
place at infinity the residue field is `k`, and a function of degree `0` takes the value
`lc(f.num)`, its denominator being monic.

Write `f = a · F₁ / F₂` and `g = b · G₁ / G₂` with `Fᵢ`, `Gᵢ` monic. Multiplying out the local
factors over the places dividing `G₁` and `G₂` gives

`f(div g) = Res(G₁, F₁) · Res(G₂, F₂) / (Res(G₁, F₂) · Res(G₂, F₁))`,

the constants `a` and `b` and the contribution of the place at infinity cancelling because one of
`f` and `g` has degree `0`: the place at infinity cannot lie in both supports. The same formula
with `f` and `g` exchanged computes `g(div f)`, and `Res(A, B) = (-1) ^ (deg A · deg B) Res(B, A)`
turns one into the other, the total sign being `(-1) ^ ((deg F₁ - deg F₂) (deg G₁ - deg G₂)) = 1`.

## Main results

* `TauCeti.Place.coe_normResidueOrOne_adicOfIrreducible`: at the place of a monic irreducible `q`,
  the local factor of a function `f` regular and nonvanishing there is
  `Res(q, f.num) / Res(q, f.denom)`.
* `TauCeti.Place.coe_normResidueOrOne_infty`: at the place at infinity, the local factor of a
  function of degree `0` is the leading coefficient of its numerator.
* `TauCeti.Divisor.eval_principal_comm_ratFunc`: **Weil reciprocity** on `k(x)`,
  `f(div g) = g(div f)` whenever `div f` and `div g` have disjoint supports.

## References

* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], Exercise 2.11.
-/

public section

noncomputable section

open IsDedekindDomain Polynomial

namespace TauCeti

open AlgebraicGeometry

variable {k : Type*} [Field k]

namespace Place

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

namespace Divisor

/-- A nonzero polynomial as a unit of `k(x)`. -/
private abbrev unitOf (p : k[X]) (hp : p ≠ 0) : (RatFunc k)ˣ :=
  Units.mk0 (algebraMap k[X] (RatFunc k) p) (RatFunc.algebraMap_ne_zero hp)

/-- The finite part `div G + deg G · P_∞` of the divisor of a monic polynomial `G`, the sum of the
places of its monic irreducible factors with multiplicity, evaluates `f` to
`Res(G, f.num) / Res(G, f.denom)`: on a single factor this is the local factor
`TauCeti.Place.coe_normResidueOrOne_adicOfIrreducible`, and both sides are multiplicative in `G`. -/
private theorem coe_eval_principal_add_natDegree_smul_infty {G : k[X]} (hG : G.Monic)
    {f : (RatFunc k)ˣ} (hnum : IsCoprime G (f : RatFunc k).num)
    (hden : IsCoprime G (f : RatFunc k).denom) :
    (eval (principal (IsFunctionField.ratFunc k) (unitOf G hG.ne_zero) +
        (G.natDegree : ℤ) • WeilDivisor.ofPoint (Place.infty k)) f : k) =
      G.resultant (f : RatFunc k).num / G.resultant (f : RatFunc k).denom := by
  obtain ⟨n, h⟩ : ∃ n, G.natDegree = n := ⟨_, rfl⟩
  induction n using Nat.strong_induction_on generalizing G with
  | _ n ih =>
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · obtain rfl := eq_one_of_monic_natDegree_zero hG h
    have h1 : unitOf (1 : k[X]) one_ne_zero = 1 := Units.ext (map_one _)
    simp [h1, principal_one]
  obtain ⟨q, hqm, hqi, G', rfl⟩ :=
    exists_monic_irreducible_factor G (not_isUnit_of_natDegree_pos G (h ▸ hn))
  have hG' : G'.Monic := hqm.of_mul_monic_left hG
  have hdeg : (q * G').natDegree = q.natDegree + G'.natDegree := hqm.natDegree_mul hG'
  have hlt : G'.natDegree < n := by
    have := hqi.natDegree_pos
    omega
  have hunit : unitOf (q * G') hG.ne_zero = unitOf q hqm.ne_zero * unitOf G' hG'.ne_zero :=
    Units.ext (map_mul _ _ _)
  have hD : principal (IsFunctionField.ratFunc k) (unitOf (q * G') hG.ne_zero) +
        ((q * G').natDegree : ℤ) • WeilDivisor.ofPoint (Place.infty k) =
      WeilDivisor.ofPoint (Place.adicOfIrreducible hqi) +
        (principal (IsFunctionField.ratFunc k) (unitOf G' hG'.ne_zero) +
          (G'.natDegree : ℤ) • WeilDivisor.ofPoint (Place.infty k)) := by
    rw [hunit, principal_mul, principal_irreducible hqi, hdeg, Nat.cast_add, add_smul,
      natCast_zsmul]
    abel
  have hqnum : ¬q ∣ (f : RatFunc k).num := fun hq ↦
    hqi.not_isUnit ((hnum.of_mul_left_left).isUnit_of_dvd' dvd_rfl hq)
  have hqden : ¬q ∣ (f : RatFunc k).denom := fun hq ↦
    hqi.not_isUnit ((hden.of_mul_left_left).isUnit_of_dvd' dvd_rfl hq)
  have hq0 : q.resultant (f : RatFunc k).denom ≠ 0 :=
    resultant_ne_zero _ _ hden.of_mul_left_left
  have hG'0 : G'.resultant (f : RatFunc k).denom ≠ 0 :=
    resultant_ne_zero _ _ hden.of_mul_left_right
  rw [hD, eval_add, Units.val_mul, eval_ofPoint,
    Place.coe_normResidueOrOne_adicOfIrreducible hqi hqm hqnum hqden,
    ih _ hlt hG' hnum.of_mul_left_right hden.of_mul_left_right rfl, hdeg,
    resultant_mul_left _ _ _ _ le_rfl,
    resultant_mul_left _ _ _ _ le_rfl]
  field_simp

/-- The numerator of `f`, made monic: `f = lc(f.num) · monicNum f / f.denom`. -/
private abbrev monicNum (f : (RatFunc k)ˣ) : k[X] :=
  (f : RatFunc k).num * C ((f : RatFunc k).num.leadingCoeff)⁻¹

private theorem monic_monicNum (f : (RatFunc k)ˣ) : (monicNum f).Monic :=
  monic_mul_leadingCoeff_inv (RatFunc.num_ne_zero f.ne_zero)

private theorem natDegree_monicNum (f : (RatFunc k)ˣ) :
    (monicNum f).natDegree = (f : RatFunc k).num.natDegree :=
  natDegree_mul_leadingCoeff_inv _ (RatFunc.num_ne_zero f.ne_zero)

private theorem num_eq_C_mul_monicNum (f : (RatFunc k)ˣ) :
    (f : RatFunc k).num = C (f : RatFunc k).num.leadingCoeff * monicNum f := by
  rw [mul_left_comm, ← C_mul,
    mul_inv_cancel₀ (leadingCoeff_ne_zero.2 (RatFunc.num_ne_zero f.ne_zero)), C_1, mul_one]

private theorem resultant_num (G : k[X]) (f : (RatFunc k)ˣ) :
    G.resultant (f : RatFunc k).num =
      (f : RatFunc k).num.leadingCoeff ^ G.natDegree * G.resultant (monicNum f) := by
  conv_lhs => rw [num_eq_C_mul_monicNum f]
  rw [natDegree_C_mul (leadingCoeff_ne_zero.2 (RatFunc.num_ne_zero f.ne_zero)),
    resultant_C_mul_right]

private theorem isCoprime_monicNum_left_iff (f : (RatFunc k)ˣ) {Q : k[X]} :
    IsCoprime (monicNum f) Q ↔ IsCoprime (f : RatFunc k).num Q :=
  isCoprime_mul_unit_right_left (isUnit_C.2 (inv_ne_zero
    (leadingCoeff_ne_zero.2 (RatFunc.num_ne_zero f.ne_zero))).isUnit) _ _

/-- A function of degree `0` has numerator and denominator of the same degree. -/
private theorem natDegree_monicNum_of_intDegree_eq_zero {f : (RatFunc k)ˣ}
    (hf : (f : RatFunc k).intDegree = 0) :
    (monicNum f).natDegree = (f : RatFunc k).denom.natDegree := by
  rw [natDegree_monicNum]
  simp only [RatFunc.intDegree] at hf
  omega

/-- The divisor of `g = b · G₁ / G₂`, with `G₁ = monicNum g` and `G₂ = g.denom` monic, split into
the finite parts `div Gᵢ + deg Gᵢ · P_∞` of the divisors of `G₁` and `G₂` and a multiple of the
place at infinity. The constant `b` has trivial divisor. -/
private theorem principal_eq_sub_add (g : (RatFunc k)ˣ) :
    principal (IsFunctionField.ratFunc k) g =
      (principal (IsFunctionField.ratFunc k) (unitOf (monicNum g) (monic_monicNum g).ne_zero) +
          ((monicNum g).natDegree : ℤ) • WeilDivisor.ofPoint (Place.infty k)) -
        (principal (IsFunctionField.ratFunc k)
            (unitOf (g : RatFunc k).denom (RatFunc.monic_denom _).ne_zero) +
          ((g : RatFunc k).denom.natDegree : ℤ) • WeilDivisor.ofPoint (Place.infty k)) +
        (((g : RatFunc k).denom.natDegree : ℤ) - (monicNum g).natDegree) •
          WeilDivisor.ofPoint (Place.infty k) := by
  have hb0 : (g : RatFunc k).num.leadingCoeff ≠ 0 :=
    leadingCoeff_ne_zero.2 (RatFunc.num_ne_zero g.ne_zero)
  have hg : g = unitOf (C (g : RatFunc k).num.leadingCoeff) (C_ne_zero.2 hb0) *
      unitOf (monicNum g) (monic_monicNum g).ne_zero /
        unitOf (g : RatFunc k).denom (RatFunc.monic_denom _).ne_zero := by
    ext
    rw [Units.val_div_eq_div_val, Units.val_mul, Units.val_mk0, Units.val_mk0, Units.val_mk0,
      ← map_mul, ← num_eq_C_mul_monicNum, RatFunc.num_div_denom]
  have hb : principal (IsFunctionField.ratFunc k)
      (unitOf (C (g : RatFunc k).num.leadingCoeff) (C_ne_zero.2 hb0)) = 0 :=
    principal_eq_zero_of_isAlgebraic _ (by
      simpa [RatFunc.algebraMap_C] using
        isAlgebraic_algebraMap (R := k) (A := RatFunc k) (g : RatFunc k).num.leadingCoeff)
  conv_lhs => rw [hg]
  rw [principal_div, principal_mul, hb, zero_add, sub_smul]
  abel

/-- If the divisors of `f` and `g` have disjoint supports, no irreducible polynomial divides both a
numerator or denominator of `g` and a numerator or denominator of `f`: it would put its place in
both supports. -/
private theorem isCoprime_of_disjoint {f g : (RatFunc k)ˣ}
    (h : Disjoint (principal (IsFunctionField.ratFunc k) f).support
      (principal (IsFunctionField.ratFunc k) g).support)
    {P Q : k[X]} (hP : P = (g : RatFunc k).num ∨ P = (g : RatFunc k).denom)
    (hQ : Q = (f : RatFunc k).num ∨ Q = (f : RatFunc k).denom) : IsCoprime P Q := by
  have hmem (u : (RatFunc k)ˣ) {z : k[X]} (hz : Irreducible z) {R : k[X]}
      (hR : R = (u : RatFunc k).num ∨ R = (u : RatFunc k).denom) (hzR : z ∣ R) :
      Place.adicOfIrreducible hz ∈ (principal (IsFunctionField.ratFunc k) u).support := by
    rw [mem_support_principal_iff]
    rcases hR with rfl | rfl
    · exact ((Place.ord_adicOfIrreducible_pos_iff hz u.ne_zero).2 hzR).ne'
    · exact ((Place.ord_adicOfIrreducible_neg_iff hz).2 hzR).ne
  refine isCoprime_of_irreducible_dvd (fun h0 ↦ ?_) fun z hz hzP hzQ ↦
    Finset.disjoint_left.1 h (hmem f hz hQ hzQ) (hmem g hz hP hzP)
  rcases hP with rfl | rfl
  · exact RatFunc.num_ne_zero g.ne_zero h0.1
  · exact (g : RatFunc k).denom_ne_zero h0.1

/-- If the divisors of `f` and `g` have disjoint supports, one of them has degree `0`: otherwise
the place at infinity lies in both supports. -/
private theorem intDegree_eq_zero_or_of_disjoint {f g : (RatFunc k)ˣ}
    (h : Disjoint (principal (IsFunctionField.ratFunc k) f).support
      (principal (IsFunctionField.ratFunc k) g).support) :
    (f : RatFunc k).intDegree = 0 ∨ (g : RatFunc k).intDegree = 0 := by
  by_contra! hfg
  exact Finset.disjoint_left.1 h
    ((mem_support_principal_iff (P := Place.infty k) _).2 (by simpa using hfg.1))
    ((mem_support_principal_iff (P := Place.infty k) _).2 (by simpa using hfg.2))

/-- **The value of `f` on `div g`, as resultants.** Write `f = a · F₁ / F₂` and `g = b · G₁ / G₂`
with `Fᵢ`, `Gᵢ` monic. If `div f` and `div g` have disjoint supports, then
`f(div g) = Res(G₁, F₁) · Res(G₂, F₂) / (Res(G₁, F₂) · Res(G₂, F₁))`. -/
private theorem coe_eval_principal {f g : (RatFunc k)ˣ}
    (h : Disjoint (principal (IsFunctionField.ratFunc k) f).support
      (principal (IsFunctionField.ratFunc k) g).support) :
    (eval (principal (IsFunctionField.ratFunc k) g) f : k) =
      (monicNum g).resultant (monicNum f) * (g : RatFunc k).denom.resultant (f : RatFunc k).denom /
        ((monicNum g).resultant (f : RatFunc k).denom *
          (g : RatFunc k).denom.resultant (monicNum f)) := by
  have ha0 : (f : RatFunc k).num.leadingCoeff ≠ 0 :=
    leadingCoeff_ne_zero.2 (RatFunc.num_ne_zero f.ne_zero)
  -- coprimality of the polynomials involved, from disjointness of the supports
  have h₁₁ : IsCoprime (monicNum g) (f : RatFunc k).num :=
    (isCoprime_monicNum_left_iff g).2 (isCoprime_of_disjoint h (.inl rfl) (.inl rfl))
  have h₁₂ : IsCoprime (monicNum g) (f : RatFunc k).denom :=
    (isCoprime_monicNum_left_iff g).2 (isCoprime_of_disjoint h (.inl rfl) (.inr rfl))
  have h₂₁ : IsCoprime (g : RatFunc k).denom (f : RatFunc k).num :=
    isCoprime_of_disjoint h (.inr rfl) (.inl rfl)
  have h₂₂ : IsCoprime (g : RatFunc k).denom (f : RatFunc k).denom :=
    isCoprime_of_disjoint h (.inr rfl) (.inr rfl)
  -- at infinity, either `f` has value `lc(f.num)` there, or `g` puts no weight there
  have hinf : ((Place.infty k).normResidueOrOne f : k) ^
        (((g : RatFunc k).denom.natDegree : ℤ) - (monicNum g).natDegree) =
      (f : RatFunc k).num.leadingCoeff ^
        (((g : RatFunc k).denom.natDegree : ℤ) - (monicNum g).natDegree) := by
    rcases intDegree_eq_zero_or_of_disjoint h with hf | hg0
    · rw [Place.coe_normResidueOrOne_infty hf]
    · rw [natDegree_monicNum_of_intDegree_eq_zero hg0, sub_self, zpow_zero, zpow_zero]
  rw [principal_eq_sub_add, eval_add, eval_sub, eval_zsmul, eval_ofPoint, Units.val_mul,
    Units.val_div_eq_div_val, Units.val_zpow_eq_zpow_val,
    coe_eval_principal_add_natDegree_smul_infty (monic_monicNum g) h₁₁ h₁₂,
    coe_eval_principal_add_natDegree_smul_infty (RatFunc.monic_denom _) h₂₁ h₂₂, hinf,
    resultant_num, resultant_num, zpow_sub₀ ha0, zpow_natCast, zpow_natCast]
  have := resultant_ne_zero _ _ h₁₂
  have := resultant_ne_zero _ _ h₂₂
  have := resultant_ne_zero _ _ ((isCoprime_monicNum_left_iff f).2 h₂₁.symm).symm
  field_simp

/-- **Weil reciprocity on the rational function field.** If `f` and `g` are nonzero rational
functions whose divisors have disjoint supports, then `f(div g) = g(div f)`. -/
theorem eval_principal_comm_ratFunc {f g : (RatFunc k)ˣ}
    (h : Disjoint (principal (IsFunctionField.ratFunc k) f).support
      (principal (IsFunctionField.ratFunc k) g).support) :
    eval (principal (IsFunctionField.ratFunc k) g) f =
      eval (principal (IsFunctionField.ratFunc k) f) g := by
  ext
  rw [coe_eval_principal h, coe_eval_principal h.symm, resultant_comm (monicNum g),
    resultant_comm (g : RatFunc k).denom, resultant_comm (monicNum g),
    resultant_comm (g : RatFunc k).denom]
  have := resultant_ne_zero _ _
    ((isCoprime_monicNum_left_iff f).2 (isCoprime_of_disjoint h (.inr rfl) (.inl rfl)).symm)
  have := resultant_ne_zero _ _
    ((isCoprime_monicNum_left_iff g).2 (isCoprime_of_disjoint h (.inl rfl) (.inr rfl))).symm
  -- the signs `(-1) ^ (deg · deg)` cancel because `f` or `g` has degree `0`
  rcases intDegree_eq_zero_or_of_disjoint h with hf | hg
  · rw [natDegree_monicNum_of_intDegree_eq_zero hf]
    field_simp
  · rw [natDegree_monicNum_of_intDegree_eq_zero hg]
    field_simp

end Divisor

end TauCeti
