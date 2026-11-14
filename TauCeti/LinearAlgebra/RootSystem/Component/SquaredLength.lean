/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.RootSystem.Component.Base
public import TauCeti.LinearAlgebra.RootSystem.Component.InvariantForm
public import TauCeti.LinearAlgebra.RootSystem.InvariantForm.SquaredLength

/-!
# Squared root lengths on the irreducible components

An invariant form on an irreducible root system has exactly two squared root lengths `s` and
`r * s`, where `r` is the lacing number of the Dynkin type (`1` for `A`, `D`, `E`, `2` for `B`, `C`,
`F₄` and `3` for `G₂`). A reducible root system has no such two-length theorem: on `A₁ × A₁ × A₁`
the form `diag(1, 2, 5)` is invariant and has three squared lengths. What survives is the
statement on each irreducible component, with the type read off from the base that a base of the
whole system induces on the component (`RootPairing.Base.componentBase`). Its Cartan matrix is the
block of the Cartan matrix of the whole base on the simple roots of the component
(`RootPairing.Base.cartanMatrix_componentBase`).

## Main results

* `RootPairing.InvariantForm.exists_range_apply_root_root_eq_component`: on the roots of a
  component whose base has valid Cartan type `t`, the squared lengths are exactly `s` and `r * s`
  with `r` the lacing number of `t`.
* `RootPairing.InvariantForm.exists_pos_range_apply_root_root_eq_component`: the same with `0 < s`
  for a positive-definite form.

## References

* J. S. Milne, *Algebraic Groups*, Cambridge University Press (2017), Appendix C(g), table (180),
  and C.56.
* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4-6*, Ch. VI §1, no. 4.
-/

public section

namespace RootPairing.InvariantForm

open TauCeti

variable {ι K M N : Type*} [Finite ι] [Field K] [AddCommGroup M] [Module K M] [AddCommGroup N]
  [Module K N] {P : RootPairing ι K M N} [P.IsRootSystem] [P.IsCrystallographic] [P.IsReduced]

/-- **The squared root lengths on an irreducible component.** If the base induced by `b` on the
component `C` has valid Cartan type `t`, any invariant form has a nonzero scale `s` such that the
squared lengths of the roots of `C` are exactly `s` and `r * s`, with `r` the lacing number of
`t`. -/
theorem exists_range_apply_root_root_eq_component [CharZero K] (B : P.InvariantForm) (b : P.Base)
    (C : P.Component) {t : DynkinType}
    (h : HasCartanType (P.componentPairing C) (b.componentBase C) t) (ht : t.Valid) :
    ∃ s : K, s ≠ 0 ∧ Set.range (fun k : C.supp ↦ B.form (P.root k) (P.root k)) =
      {s, (t.lacingNumber : K) * s} := by
  simpa using (B.restrictComponent C).exists_range_apply_root_root_eq h ht

/-- **The squared root lengths of a positive-definite invariant form on an irreducible component.**
If the base induced by `b` on the component `C` has valid Cartan type `t`, there is a positive `s`
such that the squared lengths of the roots of `C` are exactly `s` and `r * s`, with `r` the lacing
number of `t`. -/
theorem exists_pos_range_apply_root_root_eq_component [LinearOrder K] [IsStrictOrderedRing K]
    (B : P.InvariantForm) (hB : B.form.toQuadraticMap.PosDef) (b : P.Base) (C : P.Component)
    {t : DynkinType} (h : HasCartanType (P.componentPairing C) (b.componentBase C) t)
    (ht : t.Valid) :
    ∃ s : K, 0 < s ∧ Set.range (fun k : C.supp ↦ B.form (P.root k) (P.root k)) =
      {s, (t.lacingNumber : K) * s} := by
  simpa using (B.restrictComponent C).exists_pos_range_apply_root_root_eq
    (posDef_restrictComponent hB C) h ht

end RootPairing.InvariantForm
