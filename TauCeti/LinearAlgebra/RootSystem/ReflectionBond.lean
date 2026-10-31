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

end RootPairing
