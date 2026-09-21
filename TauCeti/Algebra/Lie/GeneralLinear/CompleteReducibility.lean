/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.GeneralLinear.Fock
import TauCeti.Algebra.Lie.GeneralLinear.Radical
import TauCeti.Algebra.Lie.HighestWeight.CompleteReducibility
import Mathlib.Algebra.Lie.CartanCriterion
import TauCeti.LinearAlgebra.CliffordAlgebra.Dimension

/-!
# Complete reducibility for the general linear Lie algebra and its CAR module

The Killing form of `gl n` is degenerate on the scalar matrices, so Weyl's complete-reducibility
theorem does not apply to it directly. It does apply to `sl n`. This file restricts a `gl n`-module
to `sl n`, and then promotes an `sl n`-stable complement back to `gl n` whenever the identity
matrix acts by a scalar.

The final section applies this transfer to the left-regular CAR module. The normal-ordered lift
sends the identity matrix to the scalar `(card n) ^ 2 / 2`; hence the centre preserves every
`sl n`-submodule, and the CAR module is completely reducible.

## Main results

* `TauCeti.exists_isCompl_gl_of_forall_one_lie_eq_smul`: a finite-dimensional `gl n`-module on
  which the identity acts by a scalar has a complement to every Lie submodule.
* `TauCeti.complementedLattice_lieSubmodule_gl_of_forall_one_lie_eq_smul`: the corresponding
  complemented-lattice statement.
* `TauCeti.complementedLattice_lieSubmodule_car`: complete reducibility of the CAR module.

## References

* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, GTM 9, §6.3, for
  Weyl's complete-reducibility theorem.
* B. Kostant, *Clifford algebra analogue of the Hopf--Koszul--Samelson theorem*, Adv. Math. 125
  (1997), 275--350, for the left-regular Clifford module.
-/

public section

namespace TauCeti

open _root_.LieAlgebra

attribute [local instance 100] LieRing.ofAssociativeRing

universe u v w

/-! ### Complete reducibility for scalar-centre `gl n` modules -/

section GeneralLinear

variable {K : Type u} [Field K] [CharZero K] [IsAlgClosed K]
variable {n : Type v} [Fintype n] [DecidableEq n]
variable {M : Type w} [AddCommGroup M] [Module K M]
variable [LieRingModule (Matrix n n K) M] [LieModule K (Matrix n n K) M]

/-- Extend an `sl n`-submodule to `gl n` when the identity acts by a scalar. -/
private def extendSl (c : K) (hc : ∀ m : M, ⁅(1 : Matrix n n K), m⁆ = c • m)
    (N : LieSubmodule K (SpecialLinear.sl n K) M) : LieSubmodule K (Matrix n n K) M where
  __ := N.toSubmodule
  lie_mem {A m} hm := by
    obtain ⟨X, r, rfl⟩ := exists_sl_add_smul_one_eq
      (fun h ↦ by
        let _ := h
        exact isUnit_iff_ne_zero.mpr (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)) A
    rw [add_lie, smul_lie, hc, smul_smul]
    exact N.add_mem (N.lie_mem hm) (N.smul_mem _ hm)

omit [IsAlgClosed K] in
/-- The scalar-centre extension preserves the underlying submodule. -/
@[simp]
private theorem extendSl_toSubmodule (c : K)
    (hc : ∀ m : M, ⁅(1 : Matrix n n K), m⁆ = c • m)
    (N : LieSubmodule K (SpecialLinear.sl n K) M) :
    (extendSl c hc N).toSubmodule = N.toSubmodule :=
  rfl

/-- **Complete reducibility for a general-linear module with scalar centre.** Every Lie submodule
has a complement when the identity matrix acts by a scalar. Restriction to `sl n` supplies a
complement by Weyl's theorem, and the scalar action makes that complement stable under all of
`gl n`. -/
theorem exists_isCompl_gl_of_forall_one_lie_eq_smul [FiniteDimensional K M] {c : K}
    (hc : ∀ m : M, ⁅(1 : Matrix n n K), m⁆ = c • m)
    (N : LieSubmodule K (Matrix n n K) M) :
    ∃ N' : LieSubmodule K (Matrix n n K) M, IsCompl N N' := by
  obtain ⟨P, hP⟩ := exists_isCompl_of_isKilling (K := K)
    (L := SpecialLinear.sl n K) (N.restr (SpecialLinear.sl n K))
  refine ⟨extendSl c hc P, IsCompl.of_eq ?_ ?_⟩
  · apply LieSubmodule.toSubmodule_injective
    simpa only [LieSubmodule.inf_toSubmodule, extendSl_toSubmodule,
      LieSubmodule.restr_toSubmodule, LieSubmodule.bot_toSubmodule] using
      congrArg LieSubmodule.toSubmodule hP.inf_eq_bot
  · apply LieSubmodule.toSubmodule_injective
    simpa only [LieSubmodule.sup_toSubmodule, extendSl_toSubmodule,
      LieSubmodule.restr_toSubmodule, LieSubmodule.top_toSubmodule] using
      congrArg LieSubmodule.toSubmodule hP.sup_eq_top

variable (K n M) in
/-- The Lie-submodule lattice of a finite-dimensional `gl n`-module is complemented when the
identity matrix acts by a scalar. -/
theorem complementedLattice_lieSubmodule_gl_of_forall_one_lie_eq_smul
    [FiniteDimensional K M] {c : K}
    (hc : ∀ m : M, ⁅(1 : Matrix n n K), m⁆ = c • m) :
    ComplementedLattice (LieSubmodule K (Matrix n n K) M) :=
  ⟨exists_isCompl_gl_of_forall_one_lie_eq_smul hc⟩

end GeneralLinear

/-! ### The CAR module -/

section CAR

attribute [local instance] Classical.decEq
open scoped TauCeti

variable {K n : Type*} [Field K] [Fintype n] [CharZero K] [IsAlgClosed K]

variable (K n) in
/-- **The CAR module is completely reducible.** Its Lie-submodule lattice is complemented because
the normal-ordered action of the identity matrix is scalar. -/
theorem complementedLattice_lieSubmodule_car :
    ComplementedLattice
      (LieSubmodule K (Matrix n n K) (CliffordAlgebra (traceQuadraticForm K n))) :=
  complementedLattice_lieSubmodule_gl_of_forall_one_lie_eq_smul K n _
    CliffordAlgebra.car_one_lie_eq_smul

end CAR

end TauCeti
