/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.NumberTheory.ClassFieldTheory.Global.SIdeles
import TauCeti.NumberTheory.ClassFieldTheory.Global.IdeleClass.HerbrandQuotient

/-!
# Finiteness of the cohomology of cyclic idele-class modules

For a cyclic Galois extension `L/K` of number fields, the Tate cohomology of the idele-class
module `C_L` is finite in every integer degree. In particular its Herbrand quotient is a
ratio of positive orders, rather than the zero value assigned to infinite groups.
This supplies the finiteness needed when comparing that quotient with the extension degree
in the fundamental inequalities.

The Herbrand quotient of `C_L` is the degree `[L : K]`
(`herbrandQuotient_ideleClassRep_eq_finrank`), in particular nonzero, so the Tate groups of
degrees `0` and `-1` are finite. Two-periodicity then gives finiteness in every degree. No global
reciprocity law or global class formation is assumed.

## Main results

* `TauCeti.ClassFieldTheory.finite_tateCohomology_ideleClassRep`: finiteness in every integer
  Tate degree for a cyclic number-field extension.
* `TauCeti.ClassFieldTheory.finite_groupCohomology_ideleClassRep`: finiteness in every positive
  ordinary cohomology degree for the same module.

## References

* J. S. Milne, *Class Field Theory*, Chapter VII, §4, proof of Theorem 4.3.
-/

public noncomputable section

open CategoryTheory IsDedekindDomain NumberField

namespace TauCeti.ClassFieldTheory

variable {K : Type} [Field K] [NumberField K]
  (L : Type) [Field L] [NumberField L] [Algebra K L]

variable [IsGalois K L] [IsCyclic (L ≃ₐ[K] L)]

/-- The idele-class module of a cyclic number-field extension has a nonzero Herbrand quotient,
namely `[L : K]`. -/
private theorem herbrandQuotient_ideleClassRep_ne_zero :
    TateCohomology.herbrandQuotient (ideleClassRep K L) ≠ 0 := by
  rw [herbrandQuotient_ideleClassRep_eq_finrank]
  exact Nat.cast_ne_zero.2 Module.finrank_pos.ne'

/-- **Finiteness of Tate cohomology of cyclic idele-class modules.** For a cyclic Galois
extension `L/K` of number fields, `H-hat^n(Gal(L/K), C_L)` is finite for every integer `n`. -/
instance finite_tateCohomology_ideleClassRep (n : ℤ) :
    Finite (tateCohomology (ideleClassRep K L) n) := by
  obtain ⟨h₀, h₁⟩ := TateCohomology.finite_tateCohomology_of_herbrandQuotient_ne_zero
    (herbrandQuotient_ideleClassRep_ne_zero (K := K) L)
  have := h₀
  have := h₁
  by_cases hn : n % 2 = 0
  · exact Finite.of_equiv _
      (Rep.FiniteCyclicGroup.periodicIso (ideleClassRep K L) n 0
        (by simpa [Int.ModEq] using hn)).toLinearEquiv.toEquiv.symm
  · exact Finite.of_equiv _
      (Rep.FiniteCyclicGroup.periodicIso (ideleClassRep K L) n (-1)
        (by dsimp [Int.ModEq]; omega)).toLinearEquiv.toEquiv.symm

/-- Positive ordinary cohomology of the idele-class module of a cyclic number-field extension
is finite. Degree zero is excluded: the invariant idele classes need not form a finite group. -/
instance finite_groupCohomology_ideleClassRep (n : ℕ) :
    Finite (groupCohomology (ideleClassRep K L) (n + 1)) :=
  Finite.of_equiv _
    (((_root_.TateCohomology.isoGroupCohomology (n + 1)).app
      (ideleClassRep K L)).toLinearEquiv.toEquiv)

end TauCeti.ClassFieldTheory
