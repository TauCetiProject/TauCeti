/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.RootSystem.ReflectionBond
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

The bond depends only on the two orbit weights, so it is the value of `RootPairing.reflectionBond`
(defined in `TauCeti.LinearAlgebra.RootSystem.ReflectionBond` for any two weights `x` and
`y = s_β x` related by a reflection in a positive root) on `x λ` and `y λ`. The bonds along a
saturated chain of `W / W_λ` are the integers that the description of Lakshmibai–Seshadri paths by
`a`-chains tests for divisibility by the denominator of `a`.

## Main results

* `TauCeti.existsUnique_isPos_reflection_smul_eq_of_minimalCosetRepCovBy`: **a cover of `W / W_λ`
  has a unique positive root label**; `TauCeti.smul_ne_smul_of_minimalCosetRepCovBy` says its two
  orbit weights are distinct.
* `TauCeti.reflectionBond_pos` and `TauCeti.reflectionBond_pos_of_minimalCosetRepCovBy`: **the bond
  of a cover is strictly positive**.
* `TauCeti.exists_nat_reflectionBond_eq_of_minimalCosetRepCovBy`: **the bond of a cover is a
  positive integer** when `λ` is integral.
* `TauCeti.exists_mul_sub_eq_intCast_of_minimalCosetRepCovBy`: for a root datum, if `a` times the
  bond of a cover `y ⋖ x` is an integer, then so is `a (f (x λ) - f (y λ))` for every integral
  linear form `f`.
* `TauCeti.minimalCosetRepCovBy_one_simple_of_coroot'_ne_zero` and
  `TauCeti.reflectionBond_simple_smul_one_smul`: a simple reflection `sᵢ` off the walls through `λ`
  covers the identity, with bond `⟨λ, αᵢ^∨⟩`.
* `TauCeti.reflectionBond_smul_simple_mul_smul`: the bond of `x λ` and `sᵢ x λ` is
  `-⟨x λ, αᵢ^∨⟩`.
* `TauCeti.natAbs_reflectionBond_mul_smul_mul_smul`: left multiplication by a Weyl group element
  preserves the bond of a cover, up to sign.
* `TauCeti.reflectionBond_simple_mul_smul_smul` and
  `TauCeti.reflectionBond_simple_mul_smul_simple_mul_smul`: the bond of `sᵢ u` and `u` is
  `⟨u λ, αᵢ^∨⟩`, and `sᵢ` preserves the bond of a cover `y ⋖ x` unless `y λ = (sᵢ x) λ`.
* `TauCeti.reflectionBond_smul_add`: translating `λ` by a weight killed by the simple coroots
  does not change the bonds between its orbit weights.

## References

* R. Chirivì, X. Fang and P. Littelmann, *LS algebras, valuations and Schubert varieties*,
  arXiv:2203.12992, Definition 2.1.
* P. Littelmann, *Paths and root operators in representation theory*, Ann. of Math. 142 (1995),
  499--525, Section 4.
* A. Björner and F. Brenti, *Combinatorics of Coxeter Groups*, Springer GTM 231 (2005),
  Section 2.5.
-/

public section

universe u v w x

namespace TauCeti

open RootPairing

variable {ι : Type u} {R : Type v} {M : Type w} {N : Type x}

section

variable [CommRing R] [CharZero R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  {P : _root_.RootPairing ι R M N} {b : P.Base}

/-! ### Translating by a weight on every wall -/

/-- **Bonds between orbit weights do not change under translation by a weight on every wall.** If
every simple coroot kills `χ`, as for a central weight, then `χ` is fixed by the Weyl group, so
`x (λ + χ) = x λ + χ`, and the bond of `x λ + χ` and `y λ + χ` is that of `x λ` and `y λ`. -/
theorem reflectionBond_smul_add [IsDomain R] [Finite ι] [P.IsCrystallographic] [P.IsReduced]
    {χ : M} (hχ : ∀ i ∈ b.support, P.coroot' i χ = 0) (lam : M) (x y : P.weylGroup) :
    P.reflectionBond b (x • (lam + χ)) (y • (lam + χ)) =
      P.reflectionBond b (x • lam) (y • lam) := by
  rw [smul_add, smul_add, smul_eq_self_of_forall_coroot'_eq_zero b hχ,
    smul_eq_self_of_forall_coroot'_eq_zero b hχ,
    reflectionBond_add_add (coroot'_eq_zero_of_forall_mem_support P b hχ)]

/-! ### Bonds of covers -/

variable [LinearOrder R] [IsStrictOrderedRing R] [Finite ι] [P.IsCrystallographic]
  [P.IsReduced] [P.flip.IsReduced] {lam : M}

/-- The two orbit weights of a cover `y ⋖ x` of `W / W_λ` are distinct: distinct minimal coset
representatives move `λ` to distinct points. -/
theorem smul_ne_smul_of_minimalCosetRepCovBy (hlam : lam ∈ dominantChamber P b)
    {x y : P.weylGroup}
    (h : (weylCoxeterSystem P b).MinimalCosetRepCovBy (P.wallIndices b lam) y x) :
    y • lam ≠ x • lam := fun heq ↦ h.ne <|
  eq_of_isMinimalCosetRep_of_smul_eq hlam h.isMinimalCosetRep_left h.isMinimalCosetRep_right heq

/-- **A cover of `W / W_λ` has a unique positive root label.** If `y` is covered by `x` in the
Bruhat order of the minimal coset representatives of the stabilizer of the dominant weight `λ`,
there is exactly one positive root `β` with `y λ = s_β (x λ)`. -/
theorem existsUnique_isPos_reflection_smul_eq_of_minimalCosetRepCovBy
    (hlam : lam ∈ dominantChamber P b) {x y : P.weylGroup}
    (h : (weylCoxeterSystem P b).MinimalCosetRepCovBy (P.wallIndices b lam) y x) :
    ∃! β, b.IsPos β ∧ P.reflection β (x • lam) = y • lam := by
  have hne := smul_ne_smul_of_minimalCosetRepCovBy hlam h
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
      rw [← hmem, reflection_indexNeg_neg]
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
    0 < P.reflectionBond b (x • lam) (y • lam) := by
  have hne' : y • lam ≠ x • lam := fun heq ↦ hne (eq_of_isMinimalCosetRep_of_smul_eq hlam hy hx heq)
  rw [reflectionBond_eq_neg_coroot' hβ h hne', neg_pos]
  refine (bruhatLE_and_ne_iff_coroot'_neg_of_isMinimalCosetRep hlam hx hy ?_ hβ).mp ⟨hyx, hne⟩
  rw [mul_smul, RootPairing.weylGroup.ofIdx_smul, Equiv.reflection_smul, h]

/-- **The bond of a cover of `W / W_λ` is strictly positive.** -/
theorem reflectionBond_pos_of_minimalCosetRepCovBy (hlam : lam ∈ dominantChamber P b)
    {x y : P.weylGroup}
    (h : (weylCoxeterSystem P b).MinimalCosetRepCovBy (P.wallIndices b lam) y x) :
    0 < P.reflectionBond b (x • lam) (y • lam) := by
  obtain ⟨β, ⟨hβ, hβx⟩, -⟩ := existsUnique_isPos_reflection_smul_eq_of_minimalCosetRepCovBy hlam h
  exact reflectionBond_pos hlam h.isMinimalCosetRep_right h.isMinimalCosetRep_left h.bruhatLE h.ne
    hβ hβx

/-- **The bond of a cover of `W / W_λ` is a positive integer** when the dominant weight `λ` is
integral, that is when every simple coroot takes an integer value on `λ`. -/
theorem exists_nat_reflectionBond_eq_of_minimalCosetRepCovBy (hlam : lam ∈ dominantChamber P b)
    (hint : ∀ i ∈ b.support, ∃ z : ℤ, P.coroot' i lam = z) {x y : P.weylGroup}
    (h : (weylCoxeterSystem P b).MinimalCosetRepCovBy (P.wallIndices b lam) y x) :
    ∃ n : ℕ, 0 < n ∧ P.reflectionBond b (x • lam) (y • lam) = n := by
  obtain ⟨β, ⟨hβ, hβx⟩, -⟩ := existsUnique_isPos_reflection_smul_eq_of_minimalCosetRepCovBy hlam h
  have hne := smul_ne_smul_of_minimalCosetRepCovBy hlam h
  have hpos := reflectionBond_pos_of_minimalCosetRepCovBy hlam h
  -- `⟨y λ, β^∨⟩ = ⟨λ, (y⁻¹ β)^∨⟩` is an integer.
  obtain ⟨z, hz⟩ := P.exists_intCast_eq_coroot'_of_forall_mem_support b hint
    (P.weylGroupToPerm y⁻¹ β)
  have hc := coroot'_weylGroupToPerm_smul P y⁻¹ β (y • lam)
  rw [inv_smul_smul] at hc
  rw [hc] at hz
  rw [reflectionBond_eq_coroot' hβ hβx hne, hz] at hpos ⊢
  have hz0 : 0 < z := Int.cast_pos.mp hpos
  exact ⟨z.toNat, by omega, by rw [← Int.cast_natCast, Int.toNat_of_nonneg hz0.le]⟩

omit [P.flip.IsReduced] in
/-- **A simple reflection off the walls through `λ` covers the identity in `W / W_λ`**: if
`⟨λ, αᵢ^∨⟩ ≠ 0`, then `1 ⋖ sᵢ`. -/
theorem minimalCosetRepCovBy_one_simple_of_coroot'_ne_zero {i : b.support}
    (hi : P.coroot' i lam ≠ 0) :
    (weylCoxeterSystem P b).MinimalCosetRepCovBy (P.wallIndices b lam) 1
      ((weylCoxeterSystem P b).simple i) := by
  refine (weylCoxeterSystem P b).minimalCosetRepCovBy_one_simple fun hmem ↦ hi ?_
  -- The walls through `λ` generate a subgroup of its stabilizer.
  have hle : (weylCoxeterSystem P b).parabolic (P.wallIndices b lam) ≤
      MulAction.stabilizer P.weylGroup lam :=
    (CoxeterSystem.parabolic_le_iff _).mpr fun j hj ↦ by
      rw [MulAction.mem_stabilizer_iff, weylCoxeterSystem_simple]
      exact ofIdx_smul_eq_self_of_coroot'_eq_zero (mem_wallIndices.mp hj)
  have hfix := MulAction.mem_stabilizer_iff.mp (hle hmem)
  rw [weylCoxeterSystem_simple, weylGroup.ofIdx_smul, Equiv.reflection_smul] at hfix
  have h := coroot'_reflection_self P i lam
  rw [hfix] at h
  exact CharZero.eq_neg_self_iff.mp h

omit [P.flip.IsReduced] in
/-- **The bond of `x λ` and `sᵢ x λ` is `-⟨x λ, αᵢ^∨⟩`**, for a simple root `αᵢ`. When `sᵢ` is a
left descent of the minimal coset representative `x`, this is the bond of the cover `sᵢ x ⋖ x` of
`W / W_λ`. -/
theorem reflectionBond_smul_simple_mul_smul (i : b.support) (x : P.weylGroup) :
    P.reflectionBond b (x • lam) (((weylCoxeterSystem P b).simple i * x) • lam) =
      -P.coroot' i (x • lam) := by
  rw [simple_mul_smul_eq_reflection]
  exact reflectionBond_reflection (b.isPos_of_mem_support i.2) _

omit [P.flip.IsReduced] in
/-- **The bond of `sᵢ λ` and `λ` is `⟨λ, αᵢ^∨⟩`**, for a simple root `αᵢ`. When `⟨λ, αᵢ^∨⟩ ≠ 0`
this is the bond of the cover `1 ⋖ sᵢ` of `W / W_λ`; otherwise `sᵢ λ = λ` and both sides vanish. -/
theorem reflectionBond_simple_smul_one_smul (i : b.support) :
    P.reflectionBond b ((weylCoxeterSystem P b).simple i • lam) ((1 : P.weylGroup) • lam) =
      P.coroot' i lam := by
  have h := reflectionBond_smul_simple_mul_smul (lam := lam) i ((weylCoxeterSystem P b).simple i)
  rw [CoxeterSystem.simple_mul_simple_self] at h
  rw [h, weylCoxeterSystem_simple, weylGroup.ofIdx_smul, Equiv.reflection_smul,
    coroot'_reflection_self, neg_neg]

omit [P.flip.IsReduced] in
/-- **The bond of `(sᵢ u) λ` and `u λ` is `⟨u λ, αᵢ^∨⟩`**, for a simple root `αᵢ` and every `u` in
the Weyl group. When `⟨u λ, αᵢ^∨⟩ > 0` this is the bond of the cover `u ⋖ sᵢ u` of `W / W_λ`
(`TauCeti.minimalCosetRepCovBy_simple_mul_of_coroot'_pos`); when it vanishes, both sides vanish. -/
theorem reflectionBond_simple_mul_smul_smul (i : b.support) (u : P.weylGroup) :
    P.reflectionBond b (((weylCoxeterSystem P b).simple i * u) • lam) (u • lam) =
      P.coroot' i (u • lam) := by
  simpa only [mul_smul, one_smul] using reflectionBond_simple_smul_one_smul (lam := u • lam) i

/-- **A simple reflection preserves the bond of a cover it does not reverse.** If `y ⋖ x` in
`W / W_λ` and `y λ ≠ (sᵢ x) λ`, then the bond of `(sᵢ x) λ` and `(sᵢ y) λ` is the bond
`b_λ(x, y)`. -/
theorem reflectionBond_simple_mul_smul_simple_mul_smul (hlam : lam ∈ dominantChamber P b)
    {x y : P.weylGroup}
    (h : (weylCoxeterSystem P b).MinimalCosetRepCovBy (P.wallIndices b lam) y x) {i : b.support}
    (hne : y • lam ≠ ((weylCoxeterSystem P b).simple i * x) • lam) :
    P.reflectionBond b (((weylCoxeterSystem P b).simple i * x) • lam)
        (((weylCoxeterSystem P b).simple i * y) • lam) =
      P.reflectionBond b (x • lam) (y • lam) := by
  obtain ⟨β, ⟨hβ, hβx⟩, -⟩ := existsUnique_isPos_reflection_smul_eq_of_minimalCosetRepCovBy hlam h
  have hxy := smul_ne_smul_of_minimalCosetRepCovBy hlam h
  -- The positive root label `β` of the cover is not `αᵢ`, so `sᵢ β` is positive.
  have hβi : β ≠ i := by
    rintro rfl
    exact hne (by rw [simple_mul_smul_eq_reflection, hβx])
  -- `(sᵢ y) λ` is the reflection of `(sᵢ x) λ` in the positive root `sᵢ β`.
  have hγ : P.reflection (P.reflectionPerm i β) (P.reflection i (x • lam)) =
      P.reflection i (y • lam) := by
    rw [reflection_reflectionPerm, mul_apply_eq_comp, mul_apply_eq_comp,
      reflection_same, hβx]
  have hne' : P.reflection i (y • lam) ≠ P.reflection i (x • lam) :=
    fun h' ↦ hxy ((P.reflection i).injective h')
  rw [simple_mul_smul_eq_reflection, simple_mul_smul_eq_reflection,
    reflectionBond_eq_coroot' (hβ.reflectionPerm i.2 hβi) hγ hne', ← coroot'_reflection,
    reflection_same, reflectionBond_eq_coroot' hβ hβx hxy]

end

/-! ### Covers of a root datum -/

variable [AddCommGroup M] [AddCommGroup N] {P : _root_.RootPairing ι ℤ M N} {b : P.Base}
  [Finite ι] [P.IsReduced] [P.flip.IsReduced] {lam : M} {a : ℚ}

/-- **A cover with `a`-integral bond changes integral pairings by `a`-integral amounts.** If `y ⋖ x`
is a cover
of `W / W_λ` and `a` times its bond is an integer, then `a (f (x λ) - f (y λ))` is an integer for
every integral linear form `f` on the weight lattice. Indeed `x λ - y λ = -b_λ(x, y) β` for the
positive root label `β` of the cover. -/
theorem exists_mul_sub_eq_intCast_of_minimalCosetRepCovBy (hlam : lam ∈ dominantChamber P b)
    {x y : P.weylGroup}
    (h : (weylCoxeterSystem P b).MinimalCosetRepCovBy (P.wallIndices b lam) y x)
    (ha : ∃ z : ℤ, a * P.reflectionBond b (x • lam) (y • lam) = z) (f : Module.Dual ℤ M) :
    ∃ z : ℤ, a * (f (x • lam) - f (y • lam) : ℤ) = z := by
  obtain ⟨β, ⟨hβ, hβx⟩, -⟩ := existsUnique_isPos_reflection_smul_eq_of_minimalCosetRepCovBy hlam h
  obtain ⟨z, hz⟩ := ha
  obtain ⟨k, hk⟩ := reflectionBond_dvd_sub hβ hβx f
  refine ⟨z * k, ?_⟩
  rw [hk]
  push_cast
  rw [← mul_assoc, hz]

/-- **Left multiplication preserves the bonds of covers.** If `y ⋖ x` is a cover of `W / W_λ`, then
for every element `w` of the Weyl group the bond of `(w x) λ` and `(w y) λ` has the same absolute
value as the bond `b_λ(x, y)`. When `w y ⋖ w x` is again a cover, both bonds are positive and so
they are equal. -/
theorem natAbs_reflectionBond_mul_smul_mul_smul (hlam : lam ∈ dominantChamber P b)
    {x y : P.weylGroup}
    (h : (weylCoxeterSystem P b).MinimalCosetRepCovBy (P.wallIndices b lam) y x)
    (w : P.weylGroup) :
    (P.reflectionBond b ((w * x) • lam) ((w * y) • lam)).natAbs =
      (P.reflectionBond b (x • lam) (y • lam)).natAbs := by
  obtain ⟨β, ⟨hβ, hβx⟩, -⟩ := existsUnique_isPos_reflection_smul_eq_of_minimalCosetRepCovBy hlam h
  rw [mul_smul, mul_smul, ← Int.natAbs_abs, abs_reflectionBond_smul_smul hβ hβx
    (smul_ne_smul_of_minimalCosetRepCovBy hlam h) w, Int.natAbs_abs]

end TauCeti
