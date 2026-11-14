/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.RootSystem.Component.InvariantForm
public import TauCeti.LinearAlgebra.RootSystem.InvariantForm.SquaredLength

/-!
# Squared root lengths on the irreducible components

Let `P` be a finite reduced crystallographic root system over a field of characteristic zero. If
`P` is irreducible and its base has valid Cartan type `t`, the squared lengths of the roots for an
invariant form are `{s, r * s}` for a nonzero scale `s`, where `r` is the lacing number of `t`
(`1` for `A`, `D`, `E`, `2` for `B`, `C`, `F₄` and `3` for `G₂`): so there is one squared length for
the types `A`, `D`, `E` and two for the others. A reducible root system has no such statement: on
`A₁ × A₁ × A₁` the form `diag(1, 2, 5)` is invariant and has three squared lengths. What survives is
the statement on each irreducible component, with the type read off from any base of its component
pairing, for instance the base `RootPairing.Base.componentBase` that a base of the whole system
induces on the component.

## Main results

* `RootPairing.InvariantForm.exists_forall_apply_root_root_supp_eq_mul_rootLength`: the squared
  lengths of the simple roots of a base of a component are one scale times the length table of its
  type.
* `RootPairing.InvariantForm.exists_range_apply_root_root_supp_eq`: on the roots of a component
  whose base has valid Cartan type `t`, the set of squared lengths is `{s, r * s}` with `r` the
  lacing number of `t`.
* `RootPairing.InvariantForm.exists_pos_range_apply_root_root_supp_eq`: the same with `0 < s` for a
  positive-definite form.

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

/-- **The simple roots of a base of an irreducible component have squared lengths proportional to
the length table of its Dynkin type.** -/
theorem exists_forall_apply_root_root_supp_eq_mul_rootLength [CharZero K] (B : P.InvariantForm)
    {C : P.Component} {b : (P.componentPairing C).Base} {t : DynkinType}
    {e : b.support ≃ Fin t.rank} (he : ∀ i j, b.cartanMatrix i j = t.cartanMatrix (e i) (e j)) :
    ∃ s : K, s ≠ 0 ∧ ∀ i : b.support,
      B.form (P.root (i : C.supp)) (P.root (i : C.supp)) = s * (t.rootLength (e i) : K) := by
  have : Nonempty C.supp := C.nonempty_supp.to_subtype
  simpa using (B.restrictComponent C).exists_forall_apply_root_root_eq_mul_rootLength he

/-- **The squared root lengths on an irreducible component.** If a base of the component pairing
of `C` has valid Cartan type `t`, any invariant form has a nonzero scale `s` such that the set of
squared lengths of the roots of `C` is `{s, r * s}`, with `r` the lacing number of `t`. -/
theorem exists_range_apply_root_root_supp_eq [CharZero K] (B : P.InvariantForm) {C : P.Component}
    {b : (P.componentPairing C).Base} {t : DynkinType}
    (h : HasCartanType (P.componentPairing C) b t) (ht : t.Valid) :
    ∃ s : K, s ≠ 0 ∧ Set.range (fun k : C.supp ↦ B.form (P.root k) (P.root k)) =
      {s, (t.lacingNumber : K) * s} := by
  simpa using (B.restrictComponent C).exists_range_apply_root_root_eq h ht

/-- **The squared root lengths of a positive-definite invariant form on an irreducible component.**
If a base of the component pairing of `C` has valid Cartan type `t`, there is a positive `s` such
that the set of squared lengths of the roots of `C` is `{s, r * s}`, with `r` the lacing number of
`t`. -/
theorem exists_pos_range_apply_root_root_supp_eq [LinearOrder K] [IsStrictOrderedRing K]
    (B : P.InvariantForm) (hB : B.form.toQuadraticMap.PosDef) {C : P.Component}
    {b : (P.componentPairing C).Base} {t : DynkinType}
    (h : HasCartanType (P.componentPairing C) b t) (ht : t.Valid) :
    ∃ s : K, 0 < s ∧ Set.range (fun k : C.supp ↦ B.form (P.root k) (P.root k)) =
      {s, (t.lacingNumber : K) * s} := by
  simpa using (B.restrictComponent C).exists_pos_range_apply_root_root_eq
    (posDef_restrictComponent hB C) h ht

end RootPairing.InvariantForm
