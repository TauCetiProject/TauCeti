/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RepresentationTheory.Irreducible
public import TauCeti.LinearAlgebra.CliffordAlgebra.Spin.BaseChange
public import TauCeti.RepresentationTheory.Spin.HalfSpin.Basic
-- Private: the real span theorem is used only to supply the spanning hypotheses.
import TauCeti.LinearAlgebra.CliffordAlgebra.Spin.Real.Span
-- Private: the irreducibility theorems for groups spanning the even Clifford algebra are used only
-- inside proofs.
import TauCeti.RepresentationTheory.Spin.Irreducible

/-!
# Real Spin groups acting on complex spinors

Let `Q` be an anisotropic real quadratic form, for instance the positive-definite form whose Spin
group is the compact group `Spin(n)`. Extending scalars to a field `L` over `ℝ`, such as `ℂ`, and
choosing polarization data `P` for `Q_L`, the real Spin group acts on the spinor module `⋀·W` of
`P` through `CliffordAlgebra.spinGroupBaseChange`, the inclusion `spinGroup Q → spinGroup Q_L`.

This action has the same invariant subspaces and intertwiners as the even Clifford algebra of
`Q_L`: the `L`-linear span of the real Spin group is that whole even algebra
(`QuadraticMap.Anisotropic.span_range_spinGroupBaseChange_eq_even`). Combined with
`AlgHom.mem_invtSubmodule_toMonoidHom_comp_iff_of_span_eq_top` and
`AlgHom.isIntertwiningMap_toMonoidHom_comp_iff_of_span_eq_top`, this span theorem transfers
invariant subspaces and intertwiners between the real group and the even algebra. The
irreducibility theorems for groups spanning the even Clifford algebra therefore apply to it. In
positive even dimension, the two half-spin representations of the real group are irreducible and
inequivalent; in odd dimension, the whole spin representation is irreducible. This is a statement
about the real group, and does not follow from the irreducibility of the complex Spin group: it
says that the compact real form already sees all of the complex spin modules.

The half-spin statements assume polarization data without a line remainder (`P.line = ⊥`), so
that they concern even dimension. There, in dimension zero, the real Spin group is trivial,
`S⁺ = L` and `S⁻ = 0`; the hypothesis `P.W ≠ ⊥` on the odd half excludes exactly this case. In
dimension one the real Spin group is `{±1}`, acting by `±1` on the one-dimensional spinor module.

## Main results

* `TauCeti.isIrreducible_spinPlusSubrep_comp_spinGroupBaseChange` and
  `TauCeti.isIrreducible_spinMinusSubrep_comp_spinGroupBaseChange`: the half-spin representations
  of the real Spin group are irreducible, for `P.line = ⊥` and with `P.W ≠ ⊥` required for the odd
  half.
* `TauCeti.isEmpty_equiv_spinPlusSubrep_spinMinusSubrep_comp_spinGroupBaseChange`: the two
  half-spin representations of the real Spin group are inequivalent, for `P.line = ⊥`.
* `TauCeti.isIrreducible_spinRep_comp_spinGroupBaseChange`: in odd dimension the spin
  representation of the real Spin group is irreducible.

## References

* H. B. Lawson and M.-L. Michelsohn, *Spin Geometry*, Princeton University Press (1989),
  Chapter I, §5.
* W. Fulton and J. Harris, *Representation Theory: A First Course* (1991), §20.1–§20.2.
-/

public section

open CliffordAlgebra Module

namespace TauCeti

variable {V : Type*} [AddCommGroup V] [Module ℝ V] {Q : QuadraticForm ℝ V}
  {L : Type*} [Field L] [Algebra ℝ L] (P : SpinPolarizationData (Q.baseChange L))

section HalfSpin

variable [FiniteDimensional ℝ V]

/-- **The even half-spin representation of an anisotropic real Spin group is irreducible.** For
polarization data of the scalar-extended form without a line remainder (`P.line = ⊥`), the real
group acts on the even half-spinors through `CliffordAlgebra.spinGroupBaseChange`. -/
theorem isIrreducible_spinPlusSubrep_comp_spinGroupBaseChange (hQ : Q.Anisotropic)
    (hline : P.line = ⊥) :
    Representation.IsIrreducible
      ((spinPlusSubrep P hline).toRepresentation.comp (spinGroupBaseChange (A := L) Q)) :=
  isIrreducible_spinPlusSubrep_comp_of_span P _
    hQ.span_range_spinGroupBaseChange_eq_even hline

/-- **The odd half-spin representation of an anisotropic real Spin group is irreducible** for
polarization data without a line remainder (`P.line = ⊥`) whose odd summand is nonzero
(`P.W ≠ ⊥`). In this even-dimensional setting, the second condition excludes exactly dimension
zero. -/
theorem isIrreducible_spinMinusSubrep_comp_spinGroupBaseChange (hQ : Q.Anisotropic)
    (hline : P.line = ⊥) (hW : P.W ≠ ⊥) :
    Representation.IsIrreducible
      ((spinMinusSubrep P hline).toRepresentation.comp (spinGroupBaseChange (A := L) Q)) :=
  isIrreducible_spinMinusSubrep_comp_of_span P _
    hQ.span_range_spinGroupBaseChange_eq_even hline hW

/-- **The two half-spin representations of an anisotropic real Spin group are inequivalent** for
polarization data without a line remainder (`P.line = ⊥`). -/
theorem isEmpty_equiv_spinPlusSubrep_spinMinusSubrep_comp_spinGroupBaseChange
    (hQ : Q.Anisotropic) (hline : P.line = ⊥) :
    IsEmpty (Representation.Equiv
      ((spinPlusSubrep P hline).toRepresentation.comp (spinGroupBaseChange (A := L) Q))
      ((spinMinusSubrep P hline).toRepresentation.comp (spinGroupBaseChange (A := L) Q))) :=
  isEmpty_equiv_spinPlusSubrep_spinMinusSubrep_comp_of_span P _
    hQ.span_range_spinGroupBaseChange_eq_even hline

end HalfSpin

/-- **In odd dimension the spin representation of an anisotropic real Spin group is
irreducible**: the real group acts irreducibly on the whole spinor module of the scalar-extended
form. -/
theorem isIrreducible_spinRep_comp_spinGroupBaseChange (hQ : Q.Anisotropic)
    (hodd : Odd (finrank ℝ V)) :
    Representation.IsIrreducible
      ((spinRep (Q.baseChange L) P).comp (spinGroupBaseChange (A := L) Q)) := by
  have : FiniteDimensional ℝ V := Module.finite_of_finrank_pos hodd.pos
  have : CharZero L := charZero_of_injective_algebraMap (algebraMap ℝ L).injective
  refine isIrreducible_spinRep_comp_of_span_of_surjective P _
    hQ.span_range_spinGroupBaseChange_eq_even (evenSpinAction_surjective P ?_)
  rwa [finrank_baseChange]

end TauCeti
