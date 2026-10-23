/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.RootSystem.Weyl.ParabolicQuotient

/-!
# Bonds of covers in the parabolic quotient `W / W_λ`

Let `λ` be a dominant weight for a base `b` of a finite crystallographic reduced root system. The
orbit `W λ` is the parabolic quotient `W / W_λ`, modelled by the minimal coset representatives of
the standard parabolic subgroup `W_λ` (see `TauCeti.existsUnique_isMinimalCosetRep_smul_eq`). This
file attaches to each cover `y ⋖ x` of the Bruhat order of this quotient its **positive root
label** and its **bond**:

* there is a unique positive root `β` with `y λ = s_β (x λ)`;
* the bond `b_λ(x, y) = -⟨x λ, β^∨⟩ = ⟨y λ, β^∨⟩` is strictly positive;
* if `λ` is integral, that is `⟨λ, αᵢ^∨⟩ ∈ ℤ` for every simple root `αᵢ`, the bond is a positive
  integer.

Existence of the label is the Coxeter-group statement that a cover in `W / W_J` is the projection of
a Bruhat edge `t x < x` (`CoxeterSystem.MinimalCosetRepCovBy.exists_isReflection`), together with
the identification of the reflections of the Weyl group with the root reflections. Uniqueness
holds because two reflections moving a weight to the same point have proportional roots, and the
root system is reduced (`TauCeti.eq_of_isPos_of_reflection_eq`). Positivity is the reflection test
on minimal coset representatives (`TauCeti.bruhatLE_and_ne_iff_coroot'_neg_of_isMinimalCosetRep`).

The bond depends only on the two orbit weights, so `TauCeti.reflectionBond` is defined for any two
weights `x` and `y = s_β x` related by a reflection in a positive root. The bonds along a saturated
chain of `W / W_λ` are the integers that the description of Lakshmibai–Seshadri paths by `a`-chains
tests for divisibility by the denominator of `a`.

## Main definitions

* `TauCeti.reflectionBond`: the bond `⟨y, β^∨⟩ = -⟨x, β^∨⟩` of two weights with `y = s_β x` for a
  positive root `β`.

## Main results

* `TauCeti.reflectionBond_eq_coroot'` and `TauCeti.reflectionBond_eq_neg_coroot'`: the bond in terms
  of any positive root label, and `TauCeti.reflectionBond_self`: the bond of a weight with itself
  is `0`.
* `TauCeti.existsUnique_isPos_reflection_smul_eq_of_minimalCosetRepCovBy`: **a cover of `W / W_λ`
  has a unique positive root label**.
* `TauCeti.reflectionBond_pos` and `TauCeti.reflectionBond_pos_of_minimalCosetRepCovBy`: **the bond
  of a cover is strictly positive**.
* `TauCeti.exists_nat_reflectionBond_eq_of_minimalCosetRepCovBy`: **the bond of a cover is a
  positive integer** when `λ` is integral.

## References

* R. Chirivì, X. Fang and P. Littelmann, *LS algebras, valuations and Schubert varieties*,
  arXiv:2203.12992, Definition 2.1.
* P. Littelmann, *Paths and root operators in representation theory*, Ann. of Math. 142 (1995),
  499--525, Section 4.
* A. Björner and F. Brenti, *Combinatorics of Coxeter Groups*, Springer GTM 231 (2005),
  Section 2.5.
-/

public section

namespace TauCeti

open RootPairing

universe u v w x

variable {ι : Type u} {R : Type v} {M : Type w} {N : Type x}
  [CommRing R] [CharZero R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  (P : _root_.RootPairing ι R M N) (b : P.Base)

/-! ### The positive root label and the bond -/

open Classical in
/-- The **bond** of two weights related by a reflection in a positive root: if `y = s_β x` for a
positive root `β`, it is `⟨y, β^∨⟩ = -⟨x, β^∨⟩`. For `y ≠ x` and a reduced root pairing the
positive root `β` is unique (`TauCeti.eq_of_isPos_of_reflection_eq`), so the bond is well defined
(`TauCeti.reflectionBond_eq_coroot'`). If no reflection in a positive root sends `x` to `y`, the
bond is `0`. For a cover `y ⋖ x` of the parabolic quotient `W / W_λ`, the bond of `x λ` and `y λ`
is the positive cover bond `b_λ(x, y)`. -/
noncomputable def reflectionBond (x y : M) : R :=
  if h : ∃ β, b.IsPos β ∧ P.reflection β x = y then P.coroot' h.choose y else 0

variable {P b}

/-- The bond of two weights related by a reflection in a positive root `β` is `⟨y, β^∨⟩`. -/
theorem reflectionBond_eq_coroot' [P.IsReduced] {β : ι} (hβ : b.IsPos β) {x y : M}
    (h : P.reflection β x = y) (hne : y ≠ x) : reflectionBond P b x y = P.coroot' β y := by
  have hex : ∃ β, b.IsPos β ∧ P.reflection β x = y := ⟨β, hβ, h⟩
  obtain ⟨hpos, hspec⟩ := hex.choose_spec
  rw [reflectionBond, dite_eq_left hex,
    eq_of_isPos_of_reflection_eq hpos hβ (hspec.trans h.symm) (by rwa [hspec])]

/-- The bond of two weights related by a reflection in a positive root `β` is `-⟨x, β^∨⟩`. -/
theorem reflectionBond_eq_neg_coroot' [P.IsReduced] {β : ι} (hβ : b.IsPos β) {x y : M}
    (h : P.reflection β x = y) (hne : y ≠ x) : reflectionBond P b x y = -P.coroot' β x := by
  rw [reflectionBond_eq_coroot' hβ h hne, ← h, coroot'_reflection_self]

/-- The bond of two weights not related by any reflection in a positive root is `0`. -/
theorem reflectionBond_eq_zero_of_not_exists {x y : M}
    (h : ¬∃ β, b.IsPos β ∧ P.reflection β x = y) : reflectionBond P b x y = 0 :=
  dite_eq_right h

/-- The bond of a weight with itself is `0`: a reflection fixing `x` has a coroot vanishing on
`x`. -/
@[simp]
theorem reflectionBond_self [NoZeroDivisors R] (x : M) : reflectionBond P b x x = 0 := by
  by_cases h : ∃ β, b.IsPos β ∧ P.reflection β x = x
  · rw [reflectionBond, dite_eq_left h]
    have hc := coroot'_reflection_self P h.choose x
    rw [h.choose_spec.2] at hc
    exact CharZero.eq_neg_self_iff.mp hc
  · exact reflectionBond_eq_zero_of_not_exists h

/-! ### Bonds of covers -/

variable [LinearOrder R] [IsStrictOrderedRing R] [Finite ι] [P.IsCrystallographic]
  [P.IsReduced] [P.flip.IsReduced] {lam : M}

/-- **A cover of `W / W_λ` has a unique positive root label.** If `y` is covered by `x` in the
Bruhat order of the minimal coset representatives of the stabilizer of the dominant weight `λ`,
there is exactly one positive root `β` with `y λ = s_β (x λ)`. -/
theorem existsUnique_isPos_reflection_smul_eq_of_minimalCosetRepCovBy
    (hlam : lam ∈ dominantChamber P b) {x y : P.weylGroup}
    (h : (weylCoxeterSystem P b).MinimalCosetRepCovBy (P.wallIndices b lam) y x) :
    ∃! β, b.IsPos β ∧ P.reflection β (x • lam) = y • lam := by
  have hne : y • lam ≠ x • lam := fun heq ↦ h.ne <|
    eq_of_isMinimalCosetRep_of_smul_eq hlam h.isMinimalCosetRep_left h.isMinimalCosetRep_right heq
  -- The reflection of the cover is the reflection in the root `j = w αᵢ`.
  obtain ⟨t, ⟨w, i, rfl⟩, -, hmem⟩ := h.exists_isReflection
  rw [inv_mul_mem_parabolic_wallIndices_iff hlam, weylCoxeterSystem_simple,
    ← RootPairing.weylGroup.ofIdx_weylGroupToPerm_eq_conj, mul_smul,
    RootPairing.weylGroup.ofIdx_smul, Equiv.reflection_smul] at hmem
  obtain ⟨β, hβ, hβx⟩ : ∃ β, b.IsPos β ∧ P.reflection β (x • lam) = y • lam := by
    let := P.indexNeg
    rcases Base.IsPos.or_neg b (P.weylGroupToPerm w i) with hj | hj
    · exact ⟨_, hj, hmem⟩
    · -- The reflection in `-j` is the reflection in `j`.
      refine ⟨_, hj, ?_⟩
      rw [← hmem, indexNeg_neg, reflection_reflectionPerm, LinearEquiv.mul_apply,
        LinearEquiv.mul_apply, reflection_same]
  exact ⟨β, ⟨hβ, hβx⟩, fun γ ⟨hγ, hγx⟩ ↦
    (eq_of_isPos_of_reflection_eq hβ hγ (hβx.trans hγx.symm) (by rwa [hβx])).symm⟩

/-- **The bond of two comparable cosets is strictly positive.** Let `y < x` be minimal coset
representatives of the stabilizer of the dominant weight `λ` with `y λ = s_β (x λ)` for a positive
root `β`. Then `b_λ(x, y) = -⟨x λ, β^∨⟩ > 0`. -/
theorem reflectionBond_pos (hlam : lam ∈ dominantChamber P b) {x y : P.weylGroup}
    (hx : (weylCoxeterSystem P b).IsMinimalCosetRep (P.wallIndices b lam) x)
    (hy : (weylCoxeterSystem P b).IsMinimalCosetRep (P.wallIndices b lam) y)
    (hyx : (weylCoxeterSystem P b).BruhatLE y x) (hne : y ≠ x) {β : ι} (hβ : b.IsPos β)
    (h : P.reflection β (x • lam) = y • lam) :
    0 < reflectionBond P b (x • lam) (y • lam) := by
  have hne' : y • lam ≠ x • lam := fun heq ↦ hne (eq_of_isMinimalCosetRep_of_smul_eq hlam hy hx heq)
  rw [reflectionBond_eq_neg_coroot' hβ h hne', neg_pos]
  refine (bruhatLE_and_ne_iff_coroot'_neg_of_isMinimalCosetRep hlam hx hy ?_ hβ).mp ⟨hyx, hne⟩
  rw [mul_smul, RootPairing.weylGroup.ofIdx_smul, Equiv.reflection_smul, h]

/-- **The bond of a cover of `W / W_λ` is strictly positive.** -/
theorem reflectionBond_pos_of_minimalCosetRepCovBy (hlam : lam ∈ dominantChamber P b)
    {x y : P.weylGroup}
    (h : (weylCoxeterSystem P b).MinimalCosetRepCovBy (P.wallIndices b lam) y x) :
    0 < reflectionBond P b (x • lam) (y • lam) := by
  obtain ⟨β, ⟨hβ, hβx⟩, -⟩ := existsUnique_isPos_reflection_smul_eq_of_minimalCosetRepCovBy hlam h
  exact reflectionBond_pos hlam h.isMinimalCosetRep_right h.isMinimalCosetRep_left h.bruhatLE h.ne
    hβ hβx

/-- **The bond of a cover of `W / W_λ` is a positive integer** when the dominant weight `λ` is
integral, that is when every simple coroot takes an integer value on `λ`. -/
theorem exists_nat_reflectionBond_eq_of_minimalCosetRepCovBy (hlam : lam ∈ dominantChamber P b)
    (hint : ∀ i ∈ b.support, ∃ z : ℤ, P.coroot' i lam = z) {x y : P.weylGroup}
    (h : (weylCoxeterSystem P b).MinimalCosetRepCovBy (P.wallIndices b lam) y x) :
    ∃ n : ℕ, 0 < n ∧ reflectionBond P b (x • lam) (y • lam) = n := by
  obtain ⟨β, ⟨hβ, hβx⟩, -⟩ := existsUnique_isPos_reflection_smul_eq_of_minimalCosetRepCovBy hlam h
  have hne : y • lam ≠ x • lam := fun heq ↦ h.ne <|
    eq_of_isMinimalCosetRep_of_smul_eq hlam h.isMinimalCosetRep_left h.isMinimalCosetRep_right heq
  have hpos := reflectionBond_pos_of_minimalCosetRepCovBy hlam h
  -- `⟨y λ, β^∨⟩ = ⟨λ, (y⁻¹ β)^∨⟩` is an integer.
  obtain ⟨z, hz⟩ := exists_intCast_eq_coroot'_of_forall_mem_support P b hint
    (P.weylGroupToPerm y⁻¹ β)
  have hc := coroot'_weylGroupToPerm_smul P y⁻¹ β (y • lam)
  rw [inv_smul_smul] at hc
  rw [hc] at hz
  rw [reflectionBond_eq_coroot' hβ hβx hne, hz] at hpos ⊢
  have hz0 : 0 < z := Int.cast_pos.mp hpos
  exact ⟨z.toNat, by omega, by rw [← Int.cast_natCast, Int.toNat_of_nonneg hz0.le]⟩

end TauCeti
