/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Syntomic.StandardSyntomic
public import TauCeti.RingTheory.CohenMacaulay.Presentation

/-!
# Cohen–Macaulay local rings of standard syntomic algebras over fields

A standard syntomic algebra over a field is a global complete intersection, so its local
rings are Cohen–Macaulay by the presentation criterion in
`TauCeti.RingTheory.CohenMacaulay.Presentation`.

This supplies the fibrewise Cohen–Macaulay input for duality of syntomic curves, in particular
nodal curves. No reducedness or smoothness of the complete intersection is assumed.

## References

* The Stacks Project, Section 10.135, *Local complete intersections* (Tag 00S8).
-/

public section

open scoped TensorProduct

namespace TauCeti.Algebra.IsStandardSyntomicOfRelativeDimension

variable {k A : Type*} [Field k] [CommRing A] [Algebra k A] {n : ℕ}
    [hA : IsStandardSyntomicOfRelativeDimension n k A]

include hA in
/-- Standard syntomic algebras over a field have Cohen–Macaulay local rings, without a
reducedness assumption. In particular this applies to the algebras of affine charts of
syntomic fibres. -/
theorem isCohenMacaulay_localization (p : Ideal A) [p.IsPrime] :
    Module.IsCohenMacaulay (Localization.AtPrime p) (Localization.AtPrime p) := by
  classical
  obtain ⟨ι, σ, _, _, P, hP⟩ := hA.exists_presentation
  have hdim : P.dimension = n := by
    rw [_root_.Algebra.Presentation.dimension, hP, Nat.add_sub_cancel]
  apply P.isCohenMacaulay_localization (by omega)
  rw [hdim]
  cases subsingleton_or_nontrivial A with
  | inl _ => simp [ringKrullDim_eq_bot_of_subsingleton]
  | inr _ =>
    let e := _root_.Algebra.TensorProduct.lid k A
    have : Nontrivial (k ⊗[k] A) := e.toEquiv.nontrivial
    rw [← ringKrullDim_eq_of_ringEquiv e.toRingEquiv,
      hA.ringKrullDim_tensorProduct_of_field k]

end TauCeti.Algebra.IsStandardSyntomicOfRelativeDimension
