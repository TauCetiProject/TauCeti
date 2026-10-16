/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.CentralSimple.Subfield
import TauCeti.Algebra.Algebra.Subalgebra.Separable
import TauCeti.Algebra.CentralSimple.Centralizer.Simple
import TauCeti.FieldTheory.Separable.Tower
import Mathlib.FieldTheory.JacobsonNoether

/-!
# Separable maximal subfields of central division algebras

A finite-dimensional central division algebra over any field has a separable maximal
subfield. Its degree is the degree of the division algebra, and it splits the algebra.
In particular, the splitting extension can be chosen both separable and embedded in the
division algebra, even when the base field is imperfect.

A separable commutative subalgebra of maximal dimension contains every separable element
of its centralizer. The centralizer is central over this subfield, so Jacobson–Noether and
separability transitivity force it to equal the subfield. The centralizer dimension formula
then determines the subfield's degree.

## References

* R. S. Pierce, *Associative Algebras*, GTM 88, Chapter 13.
* P. Gille and T. Szamuely, *Central Simple Algebras and Galois Cohomology*, Section 2.2.

The proof uses Mathlib's `JacobsonNoether.exists_separable_and_not_isCentral'` and Tau Ceti's
maximal separable commutative subalgebra and centralizer constructions.
-/

public section

open scoped IsMulCommutative

namespace Subalgebra

variable {K D : Type*} [Field K] [DivisionRing D] [Algebra K D]
  [Algebra.IsCentral K D] [FiniteDimensional K D]

/-- In a central division algebra, a separable commutative subalgebra of maximal dimension
is its own centralizer, hence a maximal subfield. -/
theorem centralizer_eq_self_of_isSeparable_forall_finrank_le (L : Subalgebra K D)
    [IsMulCommutative L] [Algebra.IsSeparable K L]
    (hmax : ∀ M : Subalgebra K D, IsMulCommutative M → Algebra.IsSeparable K M →
      Module.finrank K M ≤ Module.finrank K L) :
    centralizer K (L : Set D) = L := by
  let : Field L := (IsField.of_isDomain_of_finite K L).toField
  let C := centralizer K (L : Set D)
  let : DivisionRing C := divisionRingOfFiniteDimensional K C
  let : Algebra.IsCentral L C := L.isCentral_centralizer
  let : Module.Finite L C := Module.Finite.of_restrictScalars_finite K L C
  have hbot : (⊥ : Subalgebra L C) = ⊤ := by
    by_contra hne
    obtain ⟨x, hx, hsep⟩ := JacobsonNoether.exists_separable_and_not_isCentral' hne
    have hxL : (x : D) ∈ L :=
      (L.mem_iff_isSeparable_and_mem_centralizer hmax x).mpr
        ⟨hsep.restrictScalars.map C.val Subtype.val_injective, x.property⟩
    exact hx (Algebra.mem_bot.mpr ⟨⟨x, hxL⟩, Subtype.ext (by simp [C])⟩)
  have heq := congrArg
    (fun T : Subalgebra L C ↦ (L.centralizerSubalgebraOrderIso T).val) hbot
  simpa only [C, centralizerSubalgebraOrderIso_bot, centralizerSubalgebraOrderIso_top]
    using heq.symm

end Subalgebra

namespace TauCeti.Algebra

universe u

variable (K : Type*) [Field K] (D : Type u) [DivisionRing D] [Algebra K D]
  [Algebra.IsCentral K D] [FiniteDimensional K D]

/-- A finite-dimensional central division algebra has a separable maximal subfield of
degree equal to its degree. The subfield is given as a subalgebra with a field structure. -/
theorem exists_subalgebra_isField_isSeparable_finrank_eq_deg :
    ∃ L : Subalgebra K D, IsField L ∧ _root_.Algebra.IsSeparable K L ∧
      Module.finrank K L = deg K D := by
  obtain ⟨L, hcomm, hsep, hmax⟩ :=
    exists_isMulCommutative_isSeparable_forall_finrank_le K D
  let := hcomm
  let := hsep
  have hfield : IsField L := IsField.of_isDomain_of_finite K L
  refine ⟨L, hfield, hsep, ?_⟩
  have hdim := finrank_mul_finrank_centralizer_of_isField L hfield
  rw [L.centralizer_eq_self_of_isSeparable_forall_finrank_le hmax] at hdim
  have hsq : Module.finrank K L ^ 2 = deg K D ^ 2 := by rw [sq, hdim, deg_sq]
  exact Nat.pow_left_injective (by norm_num : 2 ≠ 0) hsq

/-- A central division algebra is split by a finite separable subfield of degree equal to
its degree. The embedding records that the splitting field lies inside the algebra. -/
theorem exists_isSplittingField_isSeparable_finrank_eq_deg :
    ∃ (L : Type u) (_ : Field L) (_ : _root_.Algebra K L) (_ : L →ₐ[K] D),
      FiniteDimensional K L ∧ _root_.Algebra.IsSeparable K L ∧
        Module.finrank K L = deg K D ∧ IsSplittingField K D L := by
  obtain ⟨L, hfield, hsep, hdeg⟩ := exists_subalgebra_isField_isSeparable_finrank_eq_deg K D
  let : Field L := hfield.toField
  exact ⟨L, inferInstance, inferInstance, L.val, inferInstance, hsep, hdeg,
    isSplittingField_of_finrank_eq_deg L.val hdeg⟩

end TauCeti.Algebra
