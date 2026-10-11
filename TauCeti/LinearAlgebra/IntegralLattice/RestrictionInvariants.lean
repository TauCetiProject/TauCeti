/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wentao Li
-/
module

public import TauCeti.LinearAlgebra.IntegralLattice.Restriction
public import TauCeti.LinearAlgebra.IntegralLattice.Ideals
public import TauCeti.LinearAlgebra.IntegralLattice.Gram

/-!
# Invariants under restriction of integral lattices

If one carrier lies inside another and the ambient rational forms agree, inclusion preserves
integral pairings. It follows that both the scale and norm ideals of the smaller lattice lie in
those of the larger lattice. The inclusion matrix `P` also transforms their Gram matrices by
`Pᵀ G P`. Neither statement requires nondegeneracy.

The ideal containments also hold for `restrict`, which builds a lattice in the submodule's own
rational ambient space and does not require full rank. For full sublattices, the determinant
and index formula is already supplied by
`TauCeti.IntegralLattice.determinant_eq_mul_relIndex_sq` in `IntegralLattice/Index`.

## References

* W. Ebeling, *Lattices and Codes*, Chapter 1.
-/

public section

open Module Matrix

namespace TauCeti.IntegralLattice

variable {V : Type*} [AddCommGroup V] [Module ℚ V]

/-- An inclusion of carriers with the same ambient form preserves the integral form. -/
theorem integralForm_inclusion (L M : IntegralLattice V) (hform : M.form = L.form)
    (hle : M.carrier ≤ L.carrier) (x y : M) :
    M.integralForm x y =
      L.integralForm (Submodule.inclusion hle x) (Submodule.inclusion hle y) := by
  apply Int.cast_injective (α := ℚ)
  rw [M.integralForm_cast, L.integralForm_cast, hform]
  rfl

/-- Inclusion of carriers with the same ambient form gives containment of scale ideals. -/
theorem scaleIdeal_le_of_form_eq_of_le (L M : IntegralLattice V) (hform : M.form = L.form)
    (hle : M.carrier ≤ L.carrier) : M.scaleIdeal ≤ L.scaleIdeal := by
  apply (M.integralForm.scaleIdeal_le_iff L.scaleIdeal).mpr
  intro x y
  rw [integralForm_inclusion L M hform hle]
  exact L.integralForm.apply_mem_scaleIdeal _ _

/-- Inclusion of carriers with the same ambient form gives containment of norm ideals. -/
theorem normIdeal_le_of_form_eq_of_le (L M : IntegralLattice V) (hform : M.form = L.form)
    (hle : M.carrier ≤ L.carrier) : M.normIdeal ≤ L.normIdeal := by
  apply (M.normIdeal_le_iff L.normIdeal).mpr
  intro x
  rw [M.integralNorm_apply, integralForm_inclusion L M hform hle,
    ← L.integralNorm_apply]
  exact L.integralNorm_mem_normIdeal _

/-- Restriction to any carrier submodule gives containment of scale ideals. -/
theorem scaleIdeal_restrict_le (L : IntegralLattice V) (S : Submodule ℤ L) :
    (L.restrict S).scaleIdeal ≤ L.scaleIdeal := by
  apply ((L.restrict S).integralForm.scaleIdeal_le_iff L.scaleIdeal).mpr
  intro x y
  obtain ⟨x, rfl⟩ := (L.restrictCarrierEquiv S).surjective x
  obtain ⟨y, rfl⟩ := (L.restrictCarrierEquiv S).surjective y
  rw [integralForm_restrictCarrierEquiv]
  exact L.integralForm.apply_mem_scaleIdeal _ _

/-- Restriction to any carrier submodule gives containment of norm ideals. -/
theorem normIdeal_restrict_le (L : IntegralLattice V) (S : Submodule ℤ L) :
    (L.restrict S).normIdeal ≤ L.normIdeal := by
  apply ((L.restrict S).normIdeal_le_iff L.normIdeal).mpr
  intro x
  obtain ⟨x, rfl⟩ := (L.restrictCarrierEquiv S).surjective x
  rw [integralNorm_restrictCarrierEquiv]
  exact L.integralNorm_mem_normIdeal _

/-- The Gram matrix of a sublattice is obtained by congruence with its inclusion matrix. -/
theorem gramMatrix_eq_congruence_of_form_eq (L M : IntegralLattice V)
    (hform : M.form = L.form) (hle : M.carrier ≤ L.carrier)
    {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ]
    (bL : Basis ι ℤ L) (bM : Basis κ ℤ M) :
    M.gramMatrix bM = (LinearMap.toMatrix bM bL (Submodule.inclusion hle))ᵀ *
      L.gramMatrix bL * LinearMap.toMatrix bM bL (Submodule.inclusion hle) := by
  classical
  have h : M.integralForm = L.integralForm.comp (Submodule.inclusion hle)
      (Submodule.inclusion hle) := by
    ext x y
    exact integralForm_inclusion L M hform hle x y
  rw [M.gramMatrix_eq_toMatrix, L.gramMatrix_eq_toMatrix, h,
    LinearMap.BilinForm.toMatrix_comp bL bM]

end TauCeti.IntegralLattice
