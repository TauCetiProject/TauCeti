/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.FunctionField.Place.Extension.Eisenstein
public import TauCeti.FieldTheory.FunctionField.Place.Extension.IntegralBasis.Basic

import Mathlib.LinearAlgebra.Basis.Basic

/-!
# Integral generators at totally ramified places

Let `P'` be a totally ramified place of a finite extension `F' / F`.  Every uniformizer at
`P'` generates the integral closure of the valuation ring below `P'`.  Thus its powers form a
local integral basis, not merely a basis of `F' / F`.

The proof uses the distinct orders of the first `[F' : F]` powers of the uniformizer.  If an
integral element is expanded in that basis, its order is the least order of a nonzero term.
Since the order of the whole element is nonnegative, every coefficient is regular at the place
below.  This is the local integral-basis input for computing differents from derivatives.

## References

* H. Stichtenoth, *Algebraic Function Fields and Codes*, 2nd ed., GTM 254, Springer, 2009,
  Proposition 3.1.15 and Theorem 3.5.10.
-/

public section

open scoped IntermediateField

namespace TauCeti.Place

universe u u' v v'

variable {k : Type u} {k' : Type u'} {F : Type v} {F' : Type v'}
variable [Field k] [Field k'] [Field F] [Field F']
variable [Algebra k k'] [Algebra k F] [Algebra k' F'] [Algebra F F'] [Algebra k F']
variable [IsScalarTower k k' F'] [IsScalarTower k F F']
variable [Algebra.IsSeparable F F']

attribute [local instance 10] algebraIntegersExtension isScalarTowerIntegersExtension

variable (k F) {P' : Place k' F'}

/-- The order of a coefficient times a power of a uniformizer, with the coefficient order
rescaled by the ramification index. -/
private theorem ord_algebraMap_mul_pow_uniformizer {z : F'} (hz : P'.ord z = 1)
    {c : F} (hc : c ≠ 0) (j : Fin (ramificationIdx F P')) :
    P'.ord (algebraMap F F' c * z ^ (j : ℕ)) =
      (ramificationIdx F P' : ℤ) * (P'.restrict k F).ord c + (j : ℕ) := by
  have hz0 : z ≠ 0 := by
    intro h
    rw [h, P'.ord_zero] at hz
    omega
  rw [P'.ord_mul ((map_ne_zero (algebraMap F F')).mpr hc) (pow_ne_zero _ hz0),
    ord_algebraMap_restrict k F P', P'.ord_pow, hz, mul_one]

/-- If a sum of coefficient-weighted powers of a uniformizer is regular, then every coefficient
is regular downstairs.  Distinct powers have distinct order residues modulo the ramification
index, so a coefficient with negative order would give the sum negative order. -/
private theorem coeff_mem_integers_of_ord_sum_nonneg {z : F'} (hz : P'.ord z = 1)
    (c : Fin (ramificationIdx F P') → F)
    (hsum : 0 ≤ P'.ord (∑ j, algebraMap F F' (c j) * z ^ (j : ℕ))) :
    ∀ j, c j ∈ (P'.restrict k F).integers := by
  classical
  have hz0 : z ≠ 0 := by
    intro h
    rw [h, P'.ord_zero] at hz
    omega
  let T : Fin (ramificationIdx F P') → F' :=
    fun j ↦ algebraMap F F' (c j) * z ^ (j : ℕ)
  have hTord_eq : ∀ j, T j ≠ 0 →
      P'.ord (T j) =
        (ramificationIdx F P' : ℤ) * (P'.restrict k F).ord (c j) + (j : ℕ) := by
    intro j hj
    apply ord_algebraMap_mul_pow_uniformizer k F (P' := P') hz
    intro hc
    simp [T, hc] at hj
  have hTord : ∀ j, T j ≠ 0 → ∃ m : ℤ,
      P'.ord (T j) = (ramificationIdx F P' : ℤ) * m + (j : ℕ) := by
    intro j hj
    exact ⟨(P'.restrict k F).ord (c j), hTord_eq j hj⟩
  intro j
  rw [(P'.restrict k F).mem_integers_iff_ord_nonneg]
  by_cases hc0 : c j = 0
  · simp [hc0]
  have hT0 : T j ≠ 0 :=
    mul_ne_zero ((map_ne_zero (algebraMap F F')).mpr hc0) (pow_ne_zero _ hz0)
  have hle := ord_sum_le_of_ord_eq_mul_add_natCast P' T hTord hT0
  have hnonneg : 0 ≤
      (ramificationIdx F P' : ℤ) * (P'.restrict k F).ord (c j) + (j : ℕ) := by
    rw [← hTord_eq j hT0]
    exact hsum.trans hle
  have he : (0 : ℤ) < ramificationIdx F P' := by
    exact_mod_cast ramificationIdx_pos F P'
  have hj : (j : ℤ) < ramificationIdx F P' := by
    exact_mod_cast j.2
  by_contra hneg
  have hcneg : (P'.restrict k F).ord (c j) ≤ -1 := by omega
  have hmul : (ramificationIdx F P' : ℤ) * (P'.restrict k F).ord (c j) ≤
      (ramificationIdx F P' : ℤ) * -1 :=
    mul_le_mul_of_nonneg_left hcneg he.le
  linarith

/-- A uniformizer at a totally ramified place generates the integral closure of the valuation
ring below it.  Equivalently, its powers are an integral power basis at that place. -/
theorem algebra_adjoin_integralClosure_eq_top_of_isTotallyRamified
    (htot : IsTotallyRamified F P')
    {z : integralClosure (P'.restrict k F).integers F'}
    (hz : P'.ord (algebraMap (integralClosure (P'.restrict k F).integers F') F' z) = 1) :
    Algebra.adjoin (P'.restrict k F).integers {z} = ⊤ := by
  classical
  let z' : F' := z
  have hz' : P'.ord z' = 1 := hz
  have hind : LinearIndependent F (fun j : Fin (ramificationIdx F P') ↦ z' ^ (j : ℕ)) :=
    linearIndependent_pow_fin_ramificationIdx F P' hz'
  have hcard : Fintype.card (Fin (ramificationIdx F P')) = Module.finrank F F' := by
    rw [Fintype.card_fin]
    exact (isTotallyRamified_iff (F := F) (P' := P')).mp htot
  let _ : Nonempty (Fin (ramificationIdx F P')) :=
    Fin.pos_iff_nonempty.mp (ramificationIdx_pos F P')
  have hspan := hind.span_eq_top_of_card_eq_finrank hcard
  let b : Module.Basis (Fin (ramificationIdx F P')) F F' := Module.Basis.mk hind hspan.ge
  have hb (j : Fin (ramificationIdx F P')) : b j = z' ^ (j : ℕ) := by
    exact Module.Basis.mk_apply hind hspan.ge j
  apply top_unique
  intro x _
  let y : F' := x
  have hymem : y ∈ P'.integers := by
    have hyint : IsIntegral (P'.restrict k F).integers y := by
      simpa only [y] using (mem_integralClosure_iff (P'.restrict k F).integers F').mp x.2
    exact P'.mem_integers_of_isIntegral (fun a : (P'.restrict k F).integers ↦ by
      rw [IsScalarTower.algebraMap_apply (P'.restrict k F).integers F F']
      exact (mem_integers_restrict_iff k F P' (a : F)).mp a.2) hyint
  have hyord : 0 ≤ P'.ord y := P'.mem_integers_iff_ord_nonneg.mp hymem
  let c : Fin (ramificationIdx F P') → F := fun j ↦ b.repr y j
  let T : Fin (ramificationIdx F P') → F' :=
    fun j ↦ algebraMap F F' (c j) * z' ^ (j : ℕ)
  have hsum : ∑ j, T j = y := by
    simpa only [T, c, Algebra.smul_def, hb] using b.sum_repr y
  have hc : ∀ j, c j ∈ (P'.restrict k F).integers := by
    apply coeff_mem_integers_of_ord_sum_nonneg k F (P' := P') hz' c
    have : 0 ≤ P'.ord (∑ j, T j) := by
      rw [hsum]
      exact hyord
    simpa only [T] using this
  have hmem : ∑ j, algebraMap (P'.restrict k F).integers
      (integralClosure (P'.restrict k F).integers F')
        (⟨c j, hc j⟩ : (P'.restrict k F).integers) * z ^ (j : ℕ) ∈
      Algebra.adjoin (P'.restrict k F).integers {z} := by
    apply Subalgebra.sum_mem
    intro j _
    have hzmem : z ∈ Algebra.adjoin (P'.restrict k F).integers {z} :=
      Algebra.subset_adjoin (Set.mem_singleton z)
    exact mul_mem ((Algebra.adjoin (P'.restrict k F).integers {z}).algebraMap_mem _)
      (pow_mem hzmem _)
  have heq : ∑ j, algebraMap (P'.restrict k F).integers
      (integralClosure (P'.restrict k F).integers F')
        (⟨c j, hc j⟩ : (P'.restrict k F).integers) * z ^ (j : ℕ) = x := by
    apply Subtype.ext
    push_cast
    have hcoeff (j : Fin (ramificationIdx F P')) :
        algebraMap (P'.restrict k F).integers F'
            (⟨c j, hc j⟩ : (P'.restrict k F).integers) = algebraMap F F' (c j) := by
      rw [IsScalarTower.algebraMap_apply (P'.restrict k F).integers F F']
      rfl
    simp_rw [hcoeff]
    simpa only [T, y, z'] using hsum
  rwa [heq] at hmem

end TauCeti.Place
