/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-!
# Adjoining roots of finitely many elements

For finitely many elements of a field `F` and `0 < n`, there is a finite extension of `F` in
which each of them has an `n`-th root: adjoin the roots inside an algebraic closure.

Nothing here is specific to purely inseparable extensions or to a characteristic exponent; the
result is stated for an arbitrary positive power. It supplies the finite extension `k'` of the
coefficient field in `TauCeti.IsIntegralClosure.finite_mvPolynomial_of_isPurelyInseparable`
(`TauCeti/RingTheory/IntegralClosure/PurelyInseparable.lean`).

## Main results

* `TauCeti.exists_finiteDimensional_forall_exists_pow_eq`: a finite extension of `F` containing
  `n`-th roots of finitely many given elements of `F`.

## Provenance

The construction is the finite root-adjoining step appearing in Stacks, Lemma 10.161.13
(tag 032O), in the proof that the normalization of a polynomial ring in a finite purely
inseparable extension of its fraction field is finite.
-/

public section

universe u

namespace TauCeti

/-- For finitely many elements `s` of a field `F` and `0 < n`, there is a finite extension `E` of
`F` in which every `c ∈ s` has an `n`-th root. The extension is obtained by adjoining chosen
`n`-th roots inside an algebraic closure; nothing is asserted about `E / F` beyond finiteness (in
particular it need not be purely inseparable). -/
theorem exists_finiteDimensional_forall_exists_pow_eq (F : Type u) [Field F] (s : Finset F)
    {n : ℕ} (hn : 0 < n) :
    ∃ (E : Type u) (_ : Field E) (_ : Algebra F E),
      FiniteDimensional F E ∧ ∀ c ∈ s, ∃ d : E, d ^ n = algebraMap F E c := by
  classical
  choose d hd using fun c : F ↦
    IsAlgClosed.exists_pow_nat_eq (algebraMap F (AlgebraicClosure F) c) hn
  exact ⟨IntermediateField.adjoin F (s.image d : Set (AlgebraicClosure F)), inferInstance,
    inferInstance, IntermediateField.finiteDimensional_adjoin fun x _ ↦
      Algebra.IsIntegral.isIntegral x,
    fun c hc ↦ ⟨⟨d c, IntermediateField.subset_adjoin F _ (Finset.mem_image_of_mem d hc)⟩,
      Subtype.ext (by simpa using hd c)⟩⟩

end TauCeti
