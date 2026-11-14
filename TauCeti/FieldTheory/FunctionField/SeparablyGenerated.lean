/-
Copyright (c) 2026 Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.FunctionField.Basic
public import TauCeti.FieldTheory.Separable.TranscendenceDegreeOne
import TauCeti.FieldTheory.Separable.Regular

/-!
# Separably generated algebraic function fields

An algebraic function field over a perfect field admits a separating element: a transcendental
element `x` over which the function field is finite and separable.  This supplies the parameter
needed for the differential calculus of an algebraic function field in arbitrary characteristic,
while keeping the more general results over imperfect fields stated with an explicit separating
element.

Over an imperfect field a separating element exists if and only if `F` is geometrically reduced over
`k`, for instance when `L ⊗[k] F` is reduced for an algebraically closed field `L` over `k`
(`Algebra.IsGeometricallyReduced.of_isReduced_tensorProduct`). Combining this with the
characterization of regular field extensions shows that `F ⊗[k] L` is a domain (equivalently,
`F ⊗[k] K` is a domain for every field extension `K / k`) if and only if `F` admits a separating
element and `k` is algebraically closed in `F`.

In general a separating element need not exist. An element of `F` outside `k` with a
`p`-power in `k`, such as `t^{1/p}` in `𝔽_p(t^{1/p})(X)` over `𝔽_p(t)`, would be both separable
and purely inseparable over `k(x)` for a separating `x`, hence a constant of `k(x)`, which it is
not. Even with exact constants, `y ^ p = a + b x ^ p` over `𝔽_p(a, b)` admits no separating
element (`TauCeti.not_exists_transcendental_and_isSeparable_adjoin_of_pow_eq_add_mul_X_pow`).

## Main results

* `TauCeti.IsFunctionField.exists_transcendental_and_isSeparable_adjoin_of_perfectField`: a
  function field over a perfect field has a separating element.
* `TauCeti.IsFunctionField.exists_transcendental_and_isSeparable_adjoin_of_isGeometricallyReduced`
  and
  `TauCeti.IsFunctionField.exists_transcendental_and_isSeparable_adjoin_iff_isGeometricallyReduced`:
  a function field has a separating element if and only if it is geometrically reduced.
* `TauCeti.IsFunctionField.exists_separating_and_isIntegrallyClosedIn_iff_isDomain_tensorProduct`:
  a function field has a separating element and exact constants if and only if its tensor product
  with an algebraically closed extension is a domain (and similarly over every field extension,
  `exists_separating_and_isIntegrallyClosedIn_iff_forall_isDomain_tensorProduct`).

## References

* H. Stichtenoth, *Algebraic Function Fields and Codes*, second edition, Proposition 3.10.2 and
  Section IV.1.
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

/-- **An algebraic function field is separably generated if and only if it is geometrically
reduced.** -/
theorem exists_transcendental_and_isSeparable_adjoin_iff_isGeometricallyReduced
    (hF : IsFunctionField k F) :
    (∃ x : F, Transcendental k x ∧ Algebra.IsSeparable k⟮x⟯ F) ↔
      Algebra.IsGeometricallyReduced k F :=
  ⟨fun ⟨_, hx, _⟩ ↦ isGeometricallyReduced_of_separating hx,
    fun _ ↦ hF.exists_transcendental_and_isSeparable_adjoin_of_isGeometricallyReduced⟩

/-- **Regularity criterion for algebraic function fields via an algebraically closed extension.**
For an algebraically closed field `L` over `k`, a function field `F / k` admits a separating element
and has exact constant field `k` if and only if `F ⊗[k] L` is a domain. -/
theorem exists_separating_and_isIntegrallyClosedIn_iff_isDomain_tensorProduct
    (hF : IsFunctionField k F) (L : Type*) [Field L] [Algebra k L] [IsAlgClosed L] :
    (∃ x : F, Transcendental k x ∧ Algebra.IsSeparable k⟮x⟯ F) ∧ IsIntegrallyClosedIn k F ↔
      IsDomain (F ⊗[k] L) := by
  rw [hF.exists_transcendental_and_isSeparable_adjoin_iff_isGeometricallyReduced,
    isGeometricallyReduced_and_isIntegrallyClosedIn_iff_isDomain_tensorProduct L]

/-- **Regularity criterion for algebraic function fields via all scalar extensions.** A function
field `F / k` admits a separating element and has exact constant field `k` if and only if
`F ⊗[k] K` is a domain for every field extension `K / k`. -/
theorem exists_separating_and_isIntegrallyClosedIn_iff_forall_isDomain_tensorProduct
    (hF : IsFunctionField k F) :
    (∃ x : F, Transcendental k x ∧ Algebra.IsSeparable k⟮x⟯ F) ∧ IsIntegrallyClosedIn k F ↔
      ∀ (K : Type u) [Field K] [Algebra k K], IsDomain (F ⊗[k] K) := by
  rw [hF.exists_transcendental_and_isSeparable_adjoin_iff_isGeometricallyReduced,
    isGeometricallyReduced_and_isIntegrallyClosedIn_iff_forall_isDomain_tensorProduct]

end IsFunctionField

end TauCeti
