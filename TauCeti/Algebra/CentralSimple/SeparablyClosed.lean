/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

-- Public: the central-division-algebra form of Artin--Wedderburn is refined below, and its
-- hypotheses occur in the exported matrix-presentation theorem.
public import TauCeti.Algebra.CentralSimple.Wedderburn
-- `IsSepClosed` occurs throughout the exported signatures; the elementwise result rules out
-- the separable element supplied by Jacobson--Noether.
public import TauCeti.FieldTheory.IsSepClosed
-- Non-public: Jacobson--Noether supplies a separable element outside the centre of any
-- noncommutative algebraic central division algebra.
import Mathlib.FieldTheory.JacobsonNoether

/-!
# Central simple algebras over separably closed fields

A finite-dimensional central simple algebra over a separably closed field is a full matrix
algebra.  This strengthens the algebraically closed case used in the initial splitting-field API
and is the field-theoretic input for refining an arbitrary finite splitting extension to a finite
separable one.

The only extra issue over the algebraically closed proof is the coefficient division algebra in
Artin--Wedderburn.  If an algebraic central division algebra `D` over a separably closed
field `K` were larger than `K`, the Jacobson--Noether theorem would produce an element of `D`
outside `K` that is separable over `K`.  Its irreducible minimal polynomial would have degree one,
because `K` is separably closed, so the element would in fact lie in `K`, a contradiction.

The scalar-extension and splitting consequences live in
`TauCeti/Algebra/CentralSimple/Degree.lean` and
`TauCeti/Algebra/CentralSimple/Splitting.lean`, where they replace the former algebraically closed
special cases.

## Main results

* `TauCeti.baseFieldAlgEquivOfIsSepClosed`: an algebraic central division algebra over a
  separably closed field is the base field.
* `TauCeti.IsSimpleRing.exists_algEquiv_matrix_of_isSepClosed`: a finite-dimensional central simple
  algebra over a separably closed field is a full matrix algebra.

## References

See N. Jacobson, *Basic Algebra II*, 2nd ed., Chapter 15, and P. Gille and T. Szamuely,
*Central Simple Algebras and Galois Cohomology*, Section 2.2.
-/

public section

namespace TauCeti

universe u

/-! ### Central division algebras over a separably closed field -/

section Division

variable (K : Type*) [Field K] [IsSepClosed K]
variable (D : Type u) [DivisionRing D] [Algebra K D]

variable [Algebra.IsCentral K D] [Algebra.IsAlgebraic K D]

/-- The structure map from a separably closed field onto an algebraic central division
algebra is surjective. -/
theorem algebraMap_surjective_of_isSepClosed : Function.Surjective (algebraMap K D) := by
  rw [Algebra.surjective_algebraMap_iff, eq_comm]
  by_contra hne
  obtain ⟨x, hx, hsep⟩ := JacobsonNoether.exists_separable_and_not_isCentral' hne
  exact hx hsep.mem_bot_of_isSepClosed

/-- An algebraic central division algebra over a separably closed field is the base field,
as an equivalence of algebras. -/
noncomputable def baseFieldAlgEquivOfIsSepClosed : D ≃ₐ[K] K :=
  (AlgEquiv.ofBijective (Algebra.ofId K D)
    ⟨RingHom.injective (algebraMap K D), algebraMap_surjective_of_isSepClosed K D⟩).symm

@[simp]
theorem baseFieldAlgEquivOfIsSepClosed_symm_apply (a : K) :
    (baseFieldAlgEquivOfIsSepClosed K D).symm a = algebraMap K D a := by
  simpa using (baseFieldAlgEquivOfIsSepClosed K D).symm.commutes a

@[simp]
theorem algebraMap_baseFieldAlgEquivOfIsSepClosed (x : D) :
    algebraMap K D (baseFieldAlgEquivOfIsSepClosed K D x) = x := by
  rw [← baseFieldAlgEquivOfIsSepClosed_symm_apply, AlgEquiv.symm_apply_apply]

/-- An algebraic central division algebra over a separably closed field is
one-dimensional over that field. -/
@[simp]
theorem finrank_eq_one_of_isSepClosed : Module.finrank K D = 1 := by
  rw [(baseFieldAlgEquivOfIsSepClosed K D).toLinearEquiv.finrank_eq, Module.finrank_self]

end Division

/-! ### Central simple algebras -/

namespace IsSimpleRing

variable (K : Type*) [Field K] [IsSepClosed K]
variable (A : Type u) [Ring A] [Algebra K A] [Algebra.IsCentral K A] [IsSimpleRing A]
  [FiniteDimensional K A]

/-- **Artin--Wedderburn over a separably closed field.** A finite-dimensional central simple
`K`-algebra is a full matrix algebra over `K`. -/
theorem exists_algEquiv_matrix_of_isSepClosed :
    ∃ (n : ℕ) (_ : NeZero n), Module.finrank K A = n ^ 2 ∧
      Nonempty (A ≃ₐ[K] Matrix (Fin n) (Fin n) K) :=
  exists_algEquiv_matrix_of_forall_nonempty_algEquiv K A fun D ↦
    ⟨baseFieldAlgEquivOfIsSepClosed K D⟩

end IsSimpleRing

end TauCeti
