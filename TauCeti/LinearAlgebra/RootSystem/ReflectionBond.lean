/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.RootSystem.Positive
public import TauCeti.LinearAlgebra.RootSystem.Weyl.Group

/-!
# The bond of two weights related by a positive reflection

If two weights satisfy `y = s_β x` for a positive root `β` of a root pairing with a base, their
**bond** is `⟨y, β^∨⟩ = -⟨x, β^∨⟩`. For `y ≠ x` in a reduced root pairing the positive root `β` is
unique (`TauCeti.eq_of_isPos_of_reflection_eq`), so the bond depends only on the two weights. For a
cover `y ⋖ x` of the parabolic quotient `W / W_λ`, the bond of `x λ` and `y λ` is the positive
cover bond `b_λ(x, y)` of Chirivì–Fang–Littelmann, studied in
`TauCeti.LinearAlgebra.RootSystem.Weyl.CoverBond`.

## Main definitions

* `RootPairing.reflectionBond` is the bond `⟨y, β^∨⟩ = -⟨x, β^∨⟩` of two weights with
  `y = s_β x` for a positive root `β`.

## Main results

* `RootPairing.reflectionBond_eq_coroot'` and `RootPairing.reflectionBond_eq_neg_coroot'` compute
  the bond in terms of any positive root label.
* `RootPairing.reflectionBond_eq_zero_of_not_exists` says the bond of two weights not related by a
  positive reflection is `0`, and `RootPairing.reflectionBond_self` says the bond of a weight with
  itself is `0`.
* `RootPairing.reflectionBond_reflection`: the bond of `x` and `s_β x` is `-⟨x, β^∨⟩`.
* `RootPairing.reflectionBond_dvd_sub`: when `y = s_β x` for a positive root `β`, the bond of `x`
  and `y` divides `f x - f y` for every linear form `f`.
* `RootPairing.abs_reflectionBond_smul_smul`: the bond is invariant under the Weyl group, up to
  sign.

## References

R. Chirivì, X. Fang, P. Littelmann, *LS algebras, valuations and Schubert varieties*,
arXiv:2203.12992, Definition 2.1.
-/

public section

namespace RootPairing

universe u v w x

variable {ι : Type u} {R : Type v} {M : Type w} {N : Type x}
  [CommRing R] [CharZero R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  (P : RootPairing ι R M N) (b : P.Base)

open Classical in
/-- The **bond** of two weights related by a reflection in a positive root: if `y = s_β x` for a
positive root `β`, it is `⟨y, β^∨⟩ = -⟨x, β^∨⟩`. For `y ≠ x` and a reduced root pairing the
positive root `β` is unique (`TauCeti.eq_of_isPos_of_reflection_eq`), so the bond is well defined
(`RootPairing.reflectionBond_eq_coroot'`). If no reflection in a positive root sends `x` to `y`, the
bond is `0`. For a cover `y ⋖ x` of the parabolic quotient `W / W_λ`, the bond of `x λ` and `y λ`
is the positive cover bond `b_λ(x, y)`. -/
noncomputable def reflectionBond (x y : M) : R :=
  if h : ∃ β, b.IsPos β ∧ P.reflection β x = y then P.coroot' h.choose y else 0

variable {P b}

/-- The bond of two weights related by a reflection in a positive root `β` is `⟨y, β^∨⟩`. -/
theorem reflectionBond_eq_coroot' [P.IsReduced] {β : ι} (hβ : b.IsPos β) {x y : M}
    (h : P.reflection β x = y) (hne : y ≠ x) : P.reflectionBond b x y = P.coroot' β y := by
  have hex : ∃ β, b.IsPos β ∧ P.reflection β x = y := ⟨β, hβ, h⟩
  obtain ⟨hpos, hspec⟩ := hex.choose_spec
  rw [reflectionBond, dite_eq_left hex,
    TauCeti.eq_of_isPos_of_reflection_eq hpos hβ (hspec.trans h.symm) (by rwa [hspec])]

/-- The bond of two weights related by a reflection in a positive root `β` is `-⟨x, β^∨⟩`. -/
theorem reflectionBond_eq_neg_coroot' [P.IsReduced] {β : ι} (hβ : b.IsPos β) {x y : M}
    (h : P.reflection β x = y) (hne : y ≠ x) : P.reflectionBond b x y = -P.coroot' β x := by
  rw [reflectionBond_eq_coroot' hβ h hne, ← h, coroot'_reflection_self]

/-- The bond of two weights not related by any reflection in a positive root is `0`. -/
theorem reflectionBond_eq_zero_of_not_exists {x y : M}
    (h : ¬∃ β, b.IsPos β ∧ P.reflection β x = y) : P.reflectionBond b x y = 0 :=
  dite_eq_right h

/-- The bond of a weight with itself is `0`: a reflection fixing `x` has a coroot vanishing on
`x`. -/
@[simp]
theorem reflectionBond_self [NoZeroDivisors R] (x : M) : P.reflectionBond b x x = 0 := by
  by_cases h : ∃ β, b.IsPos β ∧ P.reflection β x = x
  · rw [reflectionBond, dite_eq_left h]
    have hc := coroot'_reflection_self P h.choose x
    rw [h.choose_spec.2] at hc
    exact CharZero.eq_neg_self_iff.mp hc
  · exact reflectionBond_eq_zero_of_not_exists h

/-- The bond of a weight `x` and its reflection `s_β x` in a positive root `β` is `-⟨x, β^∨⟩`. This
holds also when `s_β x = x`, where both sides vanish. -/
theorem reflectionBond_reflection [P.IsReduced] [NoZeroDivisors R] {β : ι} (hβ : b.IsPos β)
    (x : M) : P.reflectionBond b x (P.reflection β x) = -P.coroot' β x := by
  by_cases hne : P.reflection β x = x
  · have hc := coroot'_reflection_self P β x
    rw [hne] at hc
    rw [hne, reflectionBond_self, CharZero.eq_neg_self_iff.mp hc, neg_zero]
  · exact reflectionBond_eq_neg_coroot' hβ rfl hne

/-- **The bond divides the change of every linear form.** If `y = s_β x` for a positive root `β`,
then `x - y = -⟨y, β^∨⟩ β`, so the bond of `x` and `y` divides `f x - f y` for every linear form
`f`. -/
theorem reflectionBond_dvd_sub [P.IsReduced] {β : ι} (hβ : b.IsPos β) {x y : M}
    (h : P.reflection β x = y) (f : Module.Dual R M) : P.reflectionBond b x y ∣ f x - f y := by
  rcases eq_or_ne y x with rfl | hne
  · rw [sub_self]
    exact dvd_zero _
  rw [reflectionBond_eq_neg_coroot' hβ h hne, ← h, P.reflection_apply, map_sub, sub_sub_cancel,
    map_smul, smul_eq_mul]
  exact ⟨-f (P.root β), by ring⟩

/-- **The bond is invariant under the Weyl group, up to sign.** If `y = s_β x ≠ x` for a positive
root `β`, then `|b(w x, w y)| = |b(x, y)|` for every element `w` of the Weyl group: `w y` is the
reflection of `w x` in the root `w β`, of which either `w β` or `-w β` is positive. -/
theorem abs_reflectionBond_smul_smul [LinearOrder R] [P.IsReduced] {β : ι}
    (hβ : b.IsPos β) {x y : M} (h : P.reflection β x = y) (hne : y ≠ x) (w : P.weylGroup) :
    |P.reflectionBond b (w • x) (w • y)| = |P.reflectionBond b x y| := by
  have hne' : w • y ≠ w • x := fun h' ↦ hne (smul_left_cancel w h')
  -- `w y` is the reflection of `w x` in the root `w β`.
  have hγ : P.reflection (P.weylGroupToPerm w β) (w • x) = w • y := by
    rw [reflection_weylGroupToPerm_smul, h]
  rw [reflectionBond_eq_coroot' hβ h hne]
  let := P.indexNeg
  rcases Base.IsPos.or_neg b (P.weylGroupToPerm w β) with hpos | hneg
  · rw [reflectionBond_eq_coroot' hpos hγ hne', coroot'_weylGroupToPerm_smul]
  · -- The reflection in `-w β` is the reflection in `w β`, and its coroot is `-(w β)^∨`.
    rw [reflectionBond_eq_coroot' hneg (by rwa [reflection_indexNeg_neg]) hne', indexNeg_neg,
      ← coroot'_reflection, coroot'_reflection_self, coroot'_weylGroupToPerm_smul, abs_neg]

/-- Scaling both weights scales their reflection bond. The zero scalar is allowed. -/
theorem reflectionBond_smul [IsDomain R] [P.IsReduced] (c : R) (x y : M) :
    P.reflectionBond b (c • x) (c • y) = c * P.reflectionBond b x y := by
  have : Module.IsReflexive R M := .of_isPerfPair P.toLinearMap
  rcases eq_or_ne c 0 with rfl | hc
  · simp
  rcases eq_or_ne y x with rfl | hyx
  · simp
  have hinj := smul_right_injective (M := M) hc
  by_cases h : ∃ β, b.IsPos β ∧ P.reflection β x = y
  · obtain ⟨β, hβ, hxy⟩ := h
    have hscaled : P.reflection β (c • x) = c • y := by
      rw [map_smul, hxy]
    rw [reflectionBond_eq_coroot' hβ hscaled (fun h ↦ hyx (hinj h)),
      reflectionBond_eq_coroot' hβ hxy hyx, map_smul, smul_eq_mul]
  · rw [reflectionBond_eq_zero_of_not_exists h, mul_zero,
      reflectionBond_eq_zero_of_not_exists]
    rintro ⟨β, hβ, hxy⟩
    exact h ⟨β, hβ, hinj (by simpa only [map_smul] using hxy)⟩

section IntegerScaling

variable (P : RootPairing ι ℤ M N) (b : P.Base)

/-- Scaling the shape by a natural number multiplies each orbit bond by that number. -/
theorem reflectionBond_smul_nsmul [P.IsReduced] (n : ℕ) (lam : M) (x y : P.weylGroup) :
    P.reflectionBond b (x • n • lam) (y • n • lam) =
      (n : ℤ) * P.reflectionBond b (x • lam) (y • lam) := by
  simpa only [Nat.cast_smul_eq_nsmul, smul_comm x n lam, smul_comm y n lam] using
    P.reflectionBond_smul (b := b) (n : ℤ) (x • lam) (y • lam)

end IntegerScaling

/-- **Translating by a weight on every wall leaves bonds unchanged.** If every coroot vanishes on
`χ`, as for a central weight, every reflection fixes `χ`, so `s_β (x + χ) = y + χ` exactly when
`s_β x = y`, with the same pairing `⟨y + χ, β^∨⟩ = ⟨y, β^∨⟩`. -/
theorem reflectionBond_add_add [P.IsReduced] [NoZeroDivisors R] {χ : M}
    (hχ : ∀ i, P.coroot' i χ = 0) (x y : M) :
    P.reflectionBond b (x + χ) (y + χ) = P.reflectionBond b x y := by
  have hrefl (i : ι) (z : M) : P.reflection i (z + χ) = P.reflection i z + χ := by
    rw [reflection_apply, reflection_apply, map_add, hχ, add_zero]
    abel
  by_cases hxy : y = x
  · simp [hxy]
  by_cases h : ∃ β, b.IsPos β ∧ P.reflection β x = y
  · obtain ⟨β, hβ, h⟩ := h
    rw [reflectionBond_eq_coroot' hβ h hxy,
      reflectionBond_eq_coroot' hβ (by rw [hrefl, h]) (by simpa using hxy), map_add, hχ, add_zero]
  · rw [reflectionBond_eq_zero_of_not_exists h, reflectionBond_eq_zero_of_not_exists]
    rintro ⟨β, hβ, h'⟩
    exact h ⟨β, hβ, by simpa [hrefl] using h'⟩

end RootPairing
