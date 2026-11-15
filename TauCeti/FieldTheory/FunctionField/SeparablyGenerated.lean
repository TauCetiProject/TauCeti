/-
Copyright (c) 2026 Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.FunctionField.Basic
public import TauCeti.FieldTheory.Separable.Regular
public import TauCeti.FieldTheory.Separable.TranscendenceDegreeOne

/-!
# Separably generated and regular algebraic function fields

An algebraic function field over a perfect field admits a separating element: a transcendental
element `x` over which the function field is finite and separable.  This supplies the parameter
needed for the differential calculus of an algebraic function field in arbitrary characteristic,
while keeping the more general results over imperfect fields stated with an explicit separating
element.

Over an arbitrary field `k`, a one-variable function field `F / k` has a separating element if and
only if it is geometrically reduced over `k`
(`TauCeti.IsFunctionField.isGeometricallyReduced_iff_exists_transcendental_and_isSeparable_adjoin`).
Combining this with the general regularity criteria of `TauCeti.FieldTheory.Separable.Regular` shows
that `F ⊗[k] L` is a domain for one (equivalently every) algebraically closed field `L` over `k` —
and equivalently `F ⊗[k] K` is a domain for every field extension `K / k` — if and only if `k` is
integrally closed in `F` and `F / k` admits a separating element.

In general a separating element need not exist. An element of `F` outside `k` with a
`p`-power in `k`, such as `t^{1/p}` in `𝔽_p(t^{1/p})(X)` over `𝔽_p(t)`, would be both separable
and purely inseparable over `k(x)` for a separating `x`, hence a constant of `k(x)`, which it is
not.

## Main results

* `TauCeti.IsFunctionField.exists_transcendental_and_isSeparable_adjoin_of_perfectField`: a
  function field over a perfect field has a separating element.
* `TauCeti.IsFunctionField.exists_transcendental_and_isSeparable_adjoin_of_isGeometricallyReduced`:
  a geometrically reduced function field has a separating element.
* `TauCeti.IsFunctionField.isGeometricallyReduced_iff_exists_transcendental_and_isSeparable_adjoin`:
  a function field is geometrically reduced if and only if it has a separating element.
* `TauCeti.IsFunctionField.isDomain_tensorProduct_isAlgClosed_iff`,
  `TauCeti.IsFunctionField.forall_isDomain_tensorProduct_field_iff`: a function field stays a
  domain after tensoring with an algebraically closed field (or with all field extensions) if and
  only if its constants are exact and it has a separating element.
* `TauCeti.not_isSeparable_adjoin_of_pow_mem`: an element outside `k` with a power
  `α ^ q ^ n` in `k` rules out every separating element.

## References

* H. Stichtenoth, *Algebraic Function Fields and Codes*, second edition, Proposition 3.10.2,
  Section III.6, and Section IV.1.
* S. Lang, *Introduction to Algebraic Geometry*, Chapter III, Section 1.
-/

public section

noncomputable section

open scoped IntermediateField TensorProduct

namespace TauCeti

universe u v

variable {k : Type u} {F : Type v} [Field k] [Field F] [Algebra k F]

namespace IsFunctionField

/-- **A function field over a perfect field is separably generated** (Stichtenoth,
Proposition 3.10.2): it has a transcendental element `x` such that `F / k(x)` is separable.
Finiteness over `k(x)` follows separately from
`TauCeti.IsFunctionField.finiteDimensional_adjoin`. -/
theorem exists_transcendental_and_isSeparable_adjoin_of_perfectField [PerfectField k]
    (hF : IsFunctionField k F) :
    ∃ x : F, Transcendental k x ∧ Algebra.IsSeparable k⟮x⟯ F := by
  let : Algebra.EssFiniteType k F := hF.essFiniteType
  exact TauCeti.exists_transcendental_and_isSeparable_adjoin_of_perfectField hF.trdeg_eq_one

/-- **A geometrically reduced function field is separably generated**: if `F` is geometrically
reduced over `k`, then it has a transcendental element `x` such that `F / k(x)` is separable,
whether or not `k` is perfect. Finiteness over `k(x)` follows separately from
`TauCeti.IsFunctionField.finiteDimensional_adjoin`. -/
theorem exists_transcendental_and_isSeparable_adjoin_of_isGeometricallyReduced
    [Algebra.IsGeometricallyReduced k F] (hF : IsFunctionField k F) :
    ∃ x : F, Transcendental k x ∧ Algebra.IsSeparable k⟮x⟯ F := by
  let : Algebra.EssFiniteType k F := hF.essFiniteType
  exact TauCeti.exists_transcendental_and_isSeparable_adjoin_of_isGeometricallyReduced
    hF.trdeg_eq_one

/-- **Separating-element characterization of geometrically reduced function fields**: a one-variable
function field `F / k` is geometrically reduced if and only if it admits a separating element `x`
(transcendental over `k` with `F / k(x)` separable). -/
theorem isGeometricallyReduced_iff_exists_transcendental_and_isSeparable_adjoin
    (hF : IsFunctionField k F) :
    Algebra.IsGeometricallyReduced k F ↔
      ∃ x : F, Transcendental k x ∧ Algebra.IsSeparable k⟮x⟯ F :=
  ⟨fun _ ↦ hF.exists_transcendental_and_isSeparable_adjoin_of_isGeometricallyReduced,
    fun ⟨_, hx, _⟩ ↦ isGeometricallyReduced_of_separating hx⟩

/-- **Separating-element characterization of regular function fields (algebraically closed test)**:
for a one-variable function field `F / k` and an algebraically closed field `L` over `k`,
`F ⊗[k] L` is a domain if and only if `k` is integrally closed in `F` and `F / k` admits a
separating element. -/
theorem isDomain_tensorProduct_isAlgClosed_iff (hF : IsFunctionField k F) (L : Type*) [Field L]
    [Algebra k L] [IsAlgClosed L] :
    IsDomain (F ⊗[k] L) ↔
      IsIntegrallyClosedIn k F ∧ ∃ x : F, Transcendental k x ∧ Algebra.IsSeparable k⟮x⟯ F := by
  rw [TauCeti.isDomain_tensorProduct_isAlgClosed_iff,
    hF.isGeometricallyReduced_iff_exists_transcendental_and_isSeparable_adjoin]

/-- **Separating-element characterization of regular function fields (all field extensions)**:
for a one-variable function field `F / k`, `F ⊗[k] K` is a domain for every field extension
`K / k` (in `Type u`) if and only if `k` is integrally closed in `F` and `F / k` admits a
separating element. -/
theorem forall_isDomain_tensorProduct_field_iff (hF : IsFunctionField k F) :
    (∀ (K : Type u) [Field K] [Algebra k K], IsDomain (F ⊗[k] K)) ↔
      IsIntegrallyClosedIn k F ∧ ∃ x : F, Transcendental k x ∧ Algebra.IsSeparable k⟮x⟯ F := by
  rw [TauCeti.forall_isDomain_tensorProduct_field_iff,
    hF.isGeometricallyReduced_iff_exists_transcendental_and_isSeparable_adjoin]

end IsFunctionField

end TauCeti
