/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

-- `TauCeti.one_div_forty_two_le_hyperbolic_deficit` is the numerical half of the bound.
public import TauCeti.Data.Rat.BranchDeficit
-- `TauCeti.IsFunctionField.fixedField` makes the fixed field a function field over `k`.
public import TauCeti.FieldTheory.FunctionField.Automorphism.FixedField
-- `IntermediateField.finiteDimensional_fixedField` and `IntermediateField.isGalois_fixedField` are
-- what make `F` a finite Galois extension of the fixed field, so that the statement below can speak
-- of the ramification of `F` over it.
public import TauCeti.FieldTheory.Galois.FixedField
-- `TauCeti.Divisor.degree_tameDifferent_eq_finrank_mul_sum` reads the tame different as branch
-- data, and `TauCeti.Place.ramificationIdxIn` is the index it is indexed by.
public import TauCeti.FieldTheory.FunctionField.Different.Galois
-- `TauCeti.two_mul_genus_sub_two_eq_iff_forall_isTame` is the tame Hurwitz genus formula.
public import TauCeti.FieldTheory.FunctionField.Different.Hurwitz

/-!
# The Hurwitz bound on a tame automorphism group

Let `F / k` be an algebraic function field of genus `g ≥ 2` with exact constant field `k`, and let
`G` be a finite group of `k`-automorphisms of `F` every place of which is tame over the fixed field
`F^G`.  Then

`|G| ≤ 84 (g - 1)`.

The proof is the classical one.  The fixed field is a function field over `k`
(`TauCeti.IsFunctionField.fixedField`) with `F / F^G` Galois of degree `|G|` (Artin), so the tame
Hurwitz genus formula reads

`2g - 2 = |G| (2γ - 2) + deg Diff_tame(F / F^G)`

with `γ` the genus of `F^G`, and the tame different is the branch data of the extension
(`TauCeti.Divisor.degree_tameDifferent_eq_finrank_mul_sum`):

`deg Diff_tame(F / F^G) = |G| ∑_P (1 - 1/e_P) deg P`,

the sum over the ramified places `P` of `F^G`.  Dividing by `|G|`, the deficit of the branch data
`(γ; e_P)` is `(2g - 2)/|G| > 0`, so it is at least `1/42`
(`TauCeti.one_div_forty_two_le_hyperbolic_deficit`), which is the bound.

The tameness hypothesis is necessary: in characteristic `p` the bound fails.  It holds automatically
in characteristic zero, and more generally whenever `|G|` is prime to the characteristic and the
residue extensions are separable.

## Main results

* `TauCeti.natCard_le_eighty_four_mul_genus_sub_one`: **the Hurwitz bound**, `|G| ≤ 84 (g - 1)` for
  a finite tame group of automorphisms of a function field of genus at least two.
* `TauCeti.natCard_le_eighty_four_mul_genus_sub_one_of_charZero`: the same with no tameness
  hypothesis, over a constant field of characteristic zero.

## References

* H. Stichtenoth, *Algebraic Function Fields and Codes*, 2nd ed., GTM 254, Springer, 2009,
  Exercise 3.18.
* G. D. Villa Salvador, *Topics in the Theory of Algebraic Function Fields*, Birkhäuser, 2006,
  Chapter 11.
-/

public section

namespace TauCeti

universe u v

variable {k : Type u} {F : Type v} [Field k] [Field F] [Algebra k F]

/-- **The Hurwitz bound** (Stichtenoth, Exercise 3.18): a finite group `G` of automorphisms of a
function field of genus `g ≥ 2`, every place of which is tame over the fixed field, has order at
most `84 (g - 1)`. -/
theorem natCard_le_eighty_four_mul_genus_sub_one (hF : IsFunctionField k F)
    (hex : IsIntegrallyClosedIn k F) (G : Subgroup (F ≃ₐ[k] F)) [Finite G]
    (hgenus : 2 ≤ genus k F)
    (htame : ∀ P : Place k F, Place.IsTame k (IntermediateField.fixedField G) P) :
    Nat.card G ≤ 84 * (genus k F - 1) := by
  classical
  set E := IntermediateField.fixedField G with hE
  have _ : Fintype G := Fintype.ofFinite G
  have hcard : Module.finrank ↥E F = Nat.card G := by
    rw [Nat.card_eq_fintype_card]
    exact FixedPoints.finrank_eq_card G F
  have hGpos : 0 < Nat.card G := Nat.card_pos
  have hfd : FiniteDimensional ↥E F :=
    FiniteDimensional.of_finrank_pos (by rw [hcard]; exact hGpos)
  have hgal : IsGalois ↥E F := IsGalois.of_fixed_field F G
  have hFE : IsFunctionField k ↥E := hF.fixedField G
  have hexE : IsIntegrallyClosedIn k ↥E := isIntegrallyClosedIn_intermediateField hex E
  -- The ramified places of the fixed field form a finite set.
  have hfinite : {P : Place k ↥E | 1 < P.ramificationIdxIn F}.Finite := by
    refine (Place.finite_setOf_exists_differentExponent_ne_zero (k' := k) (F' := F)
      k ↥E hFE).subset ?_
    intro P hP
    obtain ⟨P', hP'⟩ := Place.restrict_surjective_of_finiteDimensional (k' := k) hFE hF P
    refine ⟨P', hP', ?_⟩
    have he : 1 < Place.ramificationIdx ↥E P' := by
      rwa [← Place.ramificationIdxIn_eq_ramificationIdx hP']
    have hdl := Place.ramificationIdx_le_differentExponent_add_one k ↥E P'
    omega
  set s : Finset (Place k ↥E) := hfinite.toFinset with hs
  -- Hurwitz, in its tame form, through the branch data of the extension.
  have hhur : 2 * (genus k F : ℤ) - 2 =
      Module.finrank ↥E F * (2 * (genus k ↥E : ℤ) - 2) +
        Divisor.degree (Divisor.tameDifferent k F hFE) := by
    have := (two_mul_genus_sub_two_eq_iff_forall_isTame hFE hF hexE hex).mpr htame
    rwa [geometricDegree_eq_finrank] at this
  have hbranch : (Divisor.degree (Divisor.tameDifferent k F hFE) : ℚ) =
      Module.finrank ↥E F * ∑ P ∈ s, (1 - 1 / (P.ramificationIdxIn F : ℚ)) * P.degree := by
    refine Divisor.degree_tameDifferent_eq_finrank_mul_sum hFE hF s fun P' hP' ↦ ?_
    refine hfinite.mem_toFinset.mpr ?_
    rwa [Set.mem_ofPred_eq, Place.ramificationIdxIn_eq_ramificationIdx (P' := P') rfl]
  -- The branch data: each ramified place contributes its index, once per degree.
  set e : Multiset ℕ := s.val.bind fun P ↦ Multiset.replicate P.degree (P.ramificationIdxIn F)
    with he
  have hetwo : ∀ n ∈ e, 2 ≤ n := by
    intro n hn
    obtain ⟨P, hP, hn⟩ := Multiset.mem_bind.mp hn
    rw [Multiset.eq_of_mem_replicate hn]
    exact hfinite.mem_toFinset.mp hP
  have hsum : (e.map fun n : ℕ ↦ 1 - 1 / (n : ℚ)).sum =
      ∑ P ∈ s, (1 - 1 / (P.ramificationIdxIn F : ℚ)) * P.degree := by
    rw [he, Multiset.map_bind, Multiset.sum_bind, Finset.sum]
    refine congrArg Multiset.sum (Multiset.map_congr rfl fun P _ ↦ ?_)
    rw [Multiset.map_replicate, Multiset.sum_replicate, nsmul_eq_mul, mul_comm]
  -- The deficit of the branch data is `(2g - 2)/|G|`, which is positive.
  set D : ℚ := 2 * (genus k ↥E : ℚ) - 2 + (e.map fun n : ℕ ↦ 1 - 1 / (n : ℚ)).sum with hD
  have hGQ : (0 : ℚ) < Nat.card G := by exact_mod_cast hGpos
  have hkey : (Nat.card G : ℚ) * D = 2 * (genus k F : ℚ) - 2 := by
    have hcastQ := congrArg (fun n : ℤ ↦ (n : ℚ)) hhur
    push_cast at hcastQ
    rw [hbranch] at hcastQ
    rw [hD, hsum, ← hcard]
    linarith [hcastQ]
  have hgQ : (2 : ℚ) ≤ genus k F := by exact_mod_cast hgenus
  have hDpos : 0 < D := by
    by_contra hcon
    have hle : (Nat.card G : ℚ) * D ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hGQ.le (not_lt.mp hcon)
    rw [hkey] at hle
    linarith
  have hdef :=
    one_div_forty_two_le_hyperbolic_deficit (γ := genus k ↥E) hetwo (by rw [← hD]; exact hDpos)
  -- `|G| · (1/42) ≤ |G| · D = 2g - 2`.
  have hfinal : (Nat.card G : ℚ) ≤ 42 * (2 * (genus k F : ℚ) - 2) := by
    rw [← hkey]
    nlinarith [hdef, hGQ]
  have : (Nat.card G : ℚ) ≤ 84 * ((genus k F : ℚ) - 1) := by linarith
  have hnat : (Nat.card G : ℚ) ≤ ((84 * (genus k F - 1) : ℕ) : ℚ) := by
    push_cast [Nat.cast_sub (by omega : 1 ≤ genus k F)]
    linarith
  exact_mod_cast hnat

/-- **The Hurwitz bound in characteristic zero** (Stichtenoth, Exercise 3.18): a finite group of
automorphisms of a function field of genus `g ≥ 2` with exact constant field of characteristic zero
has order at most `84 (g - 1)`.  No tameness hypothesis is needed: every place is tame
(`TauCeti.Place.isTame_of_charZero`). -/
theorem natCard_le_eighty_four_mul_genus_sub_one_of_charZero [CharZero k] (hF : IsFunctionField k F)
    (hex : IsIntegrallyClosedIn k F) (G : Subgroup (F ≃ₐ[k] F)) [Finite G]
    (hgenus : 2 ≤ genus k F) :
    Nat.card G ≤ 84 * (genus k F - 1) :=
  natCard_le_eighty_four_mul_genus_sub_one hF hex G hgenus fun _ ↦ Place.isTame_of_charZero _ _ _

end TauCeti
