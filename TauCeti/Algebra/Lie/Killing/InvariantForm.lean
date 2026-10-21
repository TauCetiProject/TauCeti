/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Lie.Killing
public import TauCeti.Algebra.Lie.InvariantForm

/-!
# Invariant bilinear forms on a simple Lie algebra are multiples of the Killing form

Let `L` be a finite-dimensional Lie algebra over an algebraically closed field `K` whose adjoint
module is irreducible (for instance a simple Lie algebra) and whose Killing form is nondegenerate
(`LieAlgebra.IsKilling`). The Killing form is then a nonzero invariant form on the irreducible
module `L`, so by `TauCeti.LieModule.exists_eq_smul_of_lieInvariant` every invariant bilinear form
on `L` is a scalar multiple of it. In particular every invariant form on `L` is symmetric, and the
invariant symmetric forms `TauCeti.LieModule.invariantForms K L L` are the line spanned by the
Killing form.

In characteristic zero a finite-dimensional simple Lie algebra is Killing (Cartan's criterion,
`LieAlgebra.HasTrivialRadical.instIsKilling`), so this covers every finite-dimensional simple Lie
algebra over an algebraically closed field of characteristic zero.

## Main results

* `TauCeti.LieAlgebra.exists_eq_smul_killingForm`: **every invariant bilinear form on `L` is a
  scalar multiple of the Killing form.**
* `TauCeti.LieAlgebra.isSymm_of_lieInvariant`: every invariant bilinear form on `L` is symmetric.
* `TauCeti.LieAlgebra.invariantForms_eq_span_killingForm` and
  `TauCeti.LieAlgebra.finrank_invariantForms_eq_one`: the invariant symmetric forms on `L` are the
  line spanned by the Killing form.

## References

* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, GTM 9, §5.1 for the
  Killing form and §6.1 for Schur's lemma.
-/

public section

open Module (finrank)

namespace TauCeti.LieAlgebra

open _root_.LieAlgebra TauCeti.LieModule

variable {K L : Type*} [Field K] [IsAlgClosed K] [LieRing L] [LieAlgebra K L]
variable [FiniteDimensional K L] [_root_.LieModule.IsIrreducible K L L] [IsKilling K L]

/-- **Every invariant bilinear form on a Lie algebra is a multiple of the Killing form**, for a
finite-dimensional Lie algebra over an algebraically closed field whose adjoint module is
irreducible and whose Killing form is nondegenerate, such as a simple Lie algebra in
characteristic zero. -/
theorem exists_eq_smul_killingForm {Φ : LinearMap.BilinForm K L} (hΦ : Φ.lieInvariant L) :
    ∃ c : K, Φ = c • killingForm K L :=
  have _i := _root_.LieModule.nontrivial_of_isIrreducible K L L
  exists_eq_smul_of_lieInvariant hΦ (_root_.LieModule.traceForm_lieInvariant K L L)
    (IsKilling.killingForm_nondegenerate K L).ne_zero

/-- Every invariant bilinear form on a finite-dimensional Lie algebra over an algebraically closed
field whose adjoint module is irreducible and whose Killing form is nondegenerate is symmetric. -/
theorem isSymm_of_lieInvariant {Φ : LinearMap.BilinForm K L} (hΦ : Φ.lieInvariant L) :
    Φ.IsSymm := by
  obtain ⟨c, rfl⟩ := exists_eq_smul_killingForm hΦ
  exact (mem_invariantForms_iff.mp (traceForm_mem_invariantForms K L L)).2.smul c

variable (K L) in
/-- **The invariant symmetric bilinear forms on a finite-dimensional Lie algebra over an
algebraically closed field whose adjoint module is irreducible and whose Killing form is
nondegenerate are the line spanned by the Killing form.** -/
theorem invariantForms_eq_span_killingForm : invariantForms K L L = K ∙ killingForm K L :=
  have _i := _root_.LieModule.nontrivial_of_isIrreducible K L L
  invariantForms_eq_span_singleton (traceForm_mem_invariantForms K L L)
    (IsKilling.killingForm_nondegenerate K L).ne_zero

variable (K L) in
/-- The invariant symmetric bilinear forms on a finite-dimensional Lie algebra over an
algebraically closed field whose adjoint module is irreducible and whose Killing form is
nondegenerate form a one-dimensional space. -/
theorem finrank_invariantForms_eq_one : finrank K (invariantForms K L L) = 1 := by
  have _i := _root_.LieModule.nontrivial_of_isIrreducible K L L
  rw [invariantForms_eq_span_killingForm K L]
  exact finrank_span_singleton (V := LinearMap.BilinForm K L)
    (IsKilling.killingForm_nondegenerate K L).ne_zero

end TauCeti.LieAlgebra
