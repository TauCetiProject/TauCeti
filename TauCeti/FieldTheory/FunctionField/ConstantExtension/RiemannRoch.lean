/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.FunctionField.Divisor.Conorm
public import TauCeti.FieldTheory.FunctionField.RiemannRoch.Basic

/-!
# Riemann–Roch spaces under extension of function fields

For an algebraic extension of function fields, the functions in `L(D)` are exactly those
functions from the smaller field whose images belong to `L(Con D)`. This is the intersection
step in the comparison of Riemann–Roch spaces after extending the constants. The stronger
base-change statement, that a basis of `L(D)` over the constants becomes a basis of
`L(Con D)` over the enlarged constants, requires a further spanning argument.

The proof uses the scaling of orders by the ramification index and existence of a place above
every place of the smaller field. No separability or exact-constant-field hypothesis is needed.

## Reference

H. Stichtenoth, *Algebraic Function Fields and Codes*, second edition, Section III.6,
Theorem 3.6.3(d).
-/

public section

namespace TauCeti

open AlgebraicGeometry

universe u u' v v'

variable {k : Type u} {k' : Type u'} {F : Type v} {F' : Type v'}
variable [Field k] [Field k'] [Field F] [Field F']
variable [Algebra k k'] [Algebra k F] [Algebra k' F'] [Algebra F F'] [Algebra k F']
variable [IsScalarTower k k' F'] [IsScalarTower k F F']
variable [Algebra.IsIntegral k k'] [FiniteDimensional F F']

/-- A function from `F` belongs to `L(D)` precisely when its image in `F'` belongs to the
Riemann–Roch space of the conorm of `D`. The converse uses a place of `F'` above each place
of `F`; the ramification index is positive, so it can be cancelled from the order bound. -/
theorem mem_riemannRochSpace_conorm_iff (hF' : IsFunctionField k' F')
    (D : Divisor k F) (f : F) :
    algebraMap F F' f ∈ riemannRochSpace (Divisor.conorm k' F' D) ↔
      f ∈ riemannRochSpace D := by
  rcases eq_or_ne f 0 with rfl | hf
  · simp
  have hf' : algebraMap F F' f ≠ 0 := by
    simpa using (algebraMap F F').injective.ne hf
  rw [mem_riemannRochSpace_iff_neg_le_ord hf',
    mem_riemannRochSpace_iff_neg_le_ord hf]
  constructor
  · intro h P
    obtain ⟨P', hP'⟩ := Place.restrict_surjective (k := k) (F := F) hF' P
    dsimp only at hP'
    have hbound := h P'
    rw [Divisor.coeff_conorm, Place.ord_algebraMap_restrict k F P'] at hbound
    rw [hP'] at hbound
    have he : (0 : ℤ) < Place.ramificationIdx F P' := by
      exact_mod_cast Place.ramificationIdx_pos F P'
    nlinarith
  · intro h P'
    rw [Divisor.coeff_conorm, Place.ord_algebraMap_restrict k F P']
    have he : (0 : ℤ) ≤ Place.ramificationIdx F P' := by positivity
    nlinarith [h (P'.restrict k F)]

/-- The intersection of `L(Con D)` with the image of `F` is `L(D)`, expressed as a
`k`-submodule equality. This form can be used without unfolding either Riemann–Roch space. -/
theorem riemannRochSpace_conorm_comap (hF' : IsFunctionField k' F')
    (D : Divisor k F) :
    Submodule.comap (IsScalarTower.toAlgHom k F F').toLinearMap
      ((riemannRochSpace (Divisor.conorm k' F' D) : Submodule k' F').restrictScalars k) =
        riemannRochSpace D := by
  ext f
  exact mem_riemannRochSpace_conorm_iff hF' D f

end TauCeti
