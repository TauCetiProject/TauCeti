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

For a finite extension of function fields, the functions in `L(D)` are exactly those
functions from the smaller field whose images belong to `L(Con D)`. This gives the
intersection of `L(Con D)` with the smaller field as a submodule equality.

Multiplying a basis of `L(A)` by an `F`-linearly independent family of `r` functions in `L(C)`
gives `r ℓ(A) ≤ [k' : k] ℓ(Con A + C)`
(`TauCeti.Divisor.card_mul_dim_le_finrank_mul_dim_conorm_add`).

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
Riemann–Roch space of the conorm of `D`. -/
-- This equivalence is for targeted rewriting: `simpNF` rejects it as a simp lemma because
-- simplification unfolds Riemann–Roch membership on the left-hand side.
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
    nlinarith [h (P'.restrict k F)]

/-- The intersection of `L(Con D)` with the image of `F` is `L(D)`, expressed as a
`k`-submodule equality. This form can be used without unfolding either Riemann–Roch space. -/
@[simp]
theorem riemannRochSpace_conorm_comap (hF' : IsFunctionField k' F')
    (D : Divisor k F) :
    Submodule.comap (IsScalarTower.toAlgHom k F F').toLinearMap
      ((riemannRochSpace (Divisor.conorm k' F' D) : Submodule k' F').restrictScalars k) =
        riemannRochSpace D := by
  ext f
  exact mem_riemannRochSpace_conorm_iff hF' D f

/-- An `F`-linearly independent family of `r` functions in `L(C)` multiplies the dimension of
the Riemann–Roch space of any divisor `A` of `F`: `r ℓ(A) ≤ [k' : k] ℓ(Con A + C)`, where `ℓ(A)`
is a dimension over `k` and `ℓ(Con A + C)` one over `k'`.  The products of a `k`-basis of `L(A)`
with the family are `k`-linearly independent and lie in `L(Con A + C)`, whose dimension over `k`
is `[k' : k] ℓ(Con A + C)`.  When the constants do not grow, `k' = k`, this reads
`r ℓ(A) ≤ ℓ(Con A + C)`. -/
theorem Divisor.card_mul_dim_le_finrank_mul_dim_conorm_add [FiniteDimensional k k']
    (hF' : IsFunctionField k' F') {ι : Type*} [Fintype ι] {z : ι → F'}
    (hz : LinearIndependent F z) {C : Divisor k' F'} (hzC : ∀ i, z i ∈ riemannRochSpace C)
    (A : Divisor k F) :
    Fintype.card ι * Divisor.dim A ≤
      Module.finrank k k' * Divisor.dim (Divisor.conorm k' F' A + C) := by
  have : Algebra.IsAlgebraic F F' := Algebra.IsAlgebraic.of_finite F F'
  have hF : IsFunctionField k F := (hF'.of_finiteDimensional (k := k)).of_isAlgebraic_top
  set V := riemannRochSpace (Divisor.conorm k' F' A + C)
  have := finiteDimensional_riemannRochSpace hF A
  have := finiteDimensional_riemannRochSpace hF' (Divisor.conorm k' F' A + C)
  have : FiniteDimensional k V := Module.Finite.trans k' V
  let u := Module.finBasis k (riemannRochSpace A)
  have hu : LinearIndependent k fun j ↦ (u j : F) :=
    u.linearIndependent.map' _ (Submodule.ker_subtype _)
  have hmem (p : Fin (Module.finrank k (riemannRochSpace A)) × ι) : (u p.1 : F) • z p.2 ∈ V := by
    rw [Algebra.smul_def]
    exact mul_mem_riemannRochSpace_add
      ((mem_riemannRochSpace_conorm_iff hF' A _).mpr (u p.1).2) (hzC p.2)
  have hv : LinearIndependent k fun p ↦ (⟨_, hmem p⟩ : V) := by
    refine LinearIndependent.of_comp (V.subtype.restrictScalars k) ?_
    simpa [Function.comp_def] using linearIndependent_smul hu hz
  have hcard := hv.fintype_card_le_finrank
  rw [Fintype.card_prod, Fintype.card_fin, ← Module.finrank_mul_finrank k k' V] at hcard
  rw [Divisor.dim_def, Divisor.dim_def, mul_comm]
  exact hcard

end TauCeti
