/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.SemiDirect.Basic
public import TauCeti.Algebra.Lie.Solvable.Derived

/-!
# Derivations of solvable Lie algebras take values in the nilradical

Over a field of characteristic zero, every derivation of a finite-dimensional solvable Lie
algebra has image in the nilradical. In particular, its nilradical is preserved by all derivations.
This supplies the range containment needed to refine a cofinite enveloping ideal into one stable
under all lifted derivations, without assuming that the original ideal is stable.

Adjoining a derivation as a one-dimensional abelian complement gives a solvable semidirect sum.
The value of the derivation on an element is a bracket in that sum. The derived ideal is
nilpotent by `TauCeti.derivedSeries_le_nilradical_of_isSolvable`; its preimage in the original
algebra is therefore a nilpotent ideal containing every value of the derivation.

## References

* W. Fulton and J. Harris, *Representation Theory: A First Course*, Appendix E, §E.2,
  the derivation argument in the proof of Proposition E.5.
-/

public section

open LieAlgebra

namespace TauCeti

variable {K L : Type*} [Field K] [CharZero K] [LieRing L] [LieAlgebra K L]
  [FiniteDimensional K L] [IsSolvable L]

-- The field is used as a one-dimensional abelian Lie algebra.
attribute [local instance 100] LieRing.ofAssociativeRing

/-- Every derivation of a finite-dimensional solvable Lie algebra in characteristic zero
takes values in its nilradical. -/
theorem _root_.LieDerivation.apply_mem_nilradical_of_isSolvable
    (D : LieDerivation K L L) (x : L) : D x ∈ LieAlgebra.nilradical K L := by
  have : IsLieAbelian K := isMulCommutative_iff_isLieAbelian.mp inferInstance
  let ψ : K →ₗ⁅K⁆ LieDerivation K L L :=
    { toLinearMap := LinearMap.toSpanSingleton K _ D
      map_lie' := fun {a b} ↦ by
        simp [Ring.lie_def, mul_comm, smul_lie, lie_smul] }
  have hψ (a : K) : ψ a = a • D := rfl
  let E := L ⋊⁅ψ⁆ K
  let i : L →ₗ⁅K⁆ E := SemiDirectSum.inl ψ
  let J : LieIdeal K E := derivedSeries K E 1
  have hJ : LieRing.IsNilpotent J :=
    LieIdeal.isNilpotent_of_le (derivedSeries_le_nilradical_of_isSolvable (K := K) (L := E))
      inferInstance
  have hpre : LieRing.IsNilpotent (J.comap i) :=
    J.isNilpotent_comap_of_injective i (SemiDirectSum.inl_injective ψ)
  apply LieIdeal.le_nilradical K L (J.comap i) hpre
  have hbracket : ⁅SemiDirectSum.inr ψ (1 : K), i x⁆ = i (D x) := by
    -- Expand the local names so the semidirect-sum coordinate lemmas match.
    dsimp only [i, E]
    simp only [SemiDirectSum.inl_eq_mk, SemiDirectSum.inr_eq_mk,
      SemiDirectSum.lie_eq_mk]
    ext <;> simp [hψ, Ring.lie_def]
  rw [LieIdeal.mem_comap, ← hbracket]
  exact LieSubmodule.lie_mem_lie Submodule.mem_top Submodule.mem_top

/-- The range of a derivation of a finite-dimensional solvable Lie algebra in characteristic
zero is contained in the underlying submodule of its nilradical. -/
theorem _root_.LieDerivation.range_le_nilradical_of_isSolvable
    (D : LieDerivation K L L) :
    LinearMap.range D.toLinearMap ≤ (LieAlgebra.nilradical K L).toSubmodule := by
  rintro _ ⟨x, rfl⟩
  exact D.apply_mem_nilradical_of_isSolvable x

end TauCeti
