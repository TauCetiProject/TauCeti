/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.FunctionField.ConstantExtension.Unramified

import TauCeti.FieldTheory.FunctionField.ConstantExtension.Algebraic
import TauCeti.FieldTheory.FunctionField.ConstantExtension.Basis
import TauCeti.FieldTheory.FunctionField.Different.Tame
import TauCeti.FieldTheory.FunctionField.Place.Degree
import TauCeti.FieldTheory.FunctionField.Place.Extension.Tower

/-!
# Constant field extensions at places with separable residue field

Let `F / k` be an algebraic function field, let `k' / k` be an algebraic extension, finite or not,
and let `F' = F · k'` be the compositum. When `k' / k` is separable every place of `F` has
ramification index one in `F'`
(`TauCeti.Place.ramificationIdx_eq_one_of_constantCompositum_eq_top`).
Over an imperfect field this fails: a place whose residue field contains a `p`-th root missing
from `k` can ramify (`TauCeti.Place.ramificationIdx_adicOfIrreducible_X_sub_C_of_pow_eq`). This
file proves that the residue field is the only obstruction: **if the residue field `F_P` of a
place `P` is separable over `k`, then every place `P'` of `F'` over `P` has `e(P' ∣ P) = 1`**, for
every algebraic `k' / k`, separable or not.

The heart of the matter is a purely inseparable `k' / k` of finite degree. A `k`-basis of `F_P`
consists of separable elements, so it stays linearly independent over the purely inseparable
`k'` inside `F'_{P'}` (Mathlib's `LinearIndependent.map_of_isPurelyInseparable_of_isSeparable`).
Hence `deg P ≤ deg P'` (`TauCeti.Place.degree_restrict_le_degree_of_isPurelyInseparable`), and
the tower identity `[k' : k] · deg P' = f(P' ∣ P) · deg P` gives `[k' : k] ≤ f(P' ∣ P)`. Since
`e(P' ∣ P) · f(P' ∣ P) ≤ [F' : F] ≤ [k' : k]`, all of these are equal: `e(P' ∣ P) = 1`,
`f(P' ∣ P) = [k' : k]`, and `[F · k' : F] = [k' : k]`, so `F` and `k'` are linearly disjoint
over `k`.

For a general finite `k' / k`, let `k_s` be the separable closure of `k` in `k'`. The finite
separable step `F · k_s / F` is unramified in the full sense, with separable residue extensions
(`TauCeti.Place.isUnramifiedAt_of_constantCompositum_eq_top`), so the residue field of the place
below `P'` in `F · k_s` is separable over `k_s`
(`TauCeti.Place.isSeparable_residueField_of_isSeparable_restrict`), and the purely inseparable
step `F' / F · k_s` applies. An infinite `k' / k` reduces to a finite one, because a uniformizer
of `P'` already lies in `F · L` for a finite subextension `L / k`.

The hypothesis is on the residue field, not on the constant extension: at a rational place it
always holds, and over a perfect `k` it holds at every place. It does not make the residue
extension `F'_{P'} / F_P` separable: at a rational place, a purely inseparable constant outside
`k` makes it inseparable (`TauCeti.Place.not_isSeparable_residueField_of_degree_eq_one`). So
`P'` has index one over `P` without being unramified in the full sense.

## Main results

* `TauCeti.Place.relativeDegree_eq_finrank_of_isPurelyInseparable`: for finite purely
  inseparable `k' / k`, `f(P' ∣ P) = [k' : k]`.
* `TauCeti.finrank_eq_finrank_of_isPurelyInseparable_of_isSeparable_residueField`: for finite
  purely inseparable `k' / k`, a place with residue field separable over `k` forces
  `[F · k' : F] = [k' : k]`.
* `TauCeti.Place.ramificationIdx_eq_one_of_isSeparable_residueField`: **for any algebraic
  `k' / k`, a place with residue field separable over `k` has ramification index one at every
  place above it.**

## References

* H. Stichtenoth, *Algebraic Function Fields and Codes*, 2nd ed., GTM 254, Springer, 2009,
  Theorem 3.6.3, whose parts (a) and (g) assume `k` perfect.
* N. Bourbaki, *Algebra II*, Chapter V, §15, for linear disjointness of separable and purely
  inseparable extensions.
-/

public section

open Module

namespace TauCeti

universe u u' v v'

variable {k : Type u} {k' : Type u'} {F : Type v} {F' : Type v'}
variable [Field k] [Field k'] [Field F] [Field F']
variable [Algebra k k'] [Algebra k F] [Algebra k F'] [Algebra k' F'] [Algebra F F']
variable [IsScalarTower k k' F'] [IsScalarTower k F F']

namespace Place

variable [Algebra.IsIntegral F F']

section PurelyInseparable

variable [FiniteDimensional k k'] [IsPurelyInseparable k k']

/-- The chain of inequalities `e(P' ∣ P) f(P' ∣ P) ≤ [F' : F] ≤ [k' : k] ≤ f(P' ∣ P)` for a
finite purely inseparable `k' / k` and a place `P` with residue field separable over `k`. -/
private theorem ramificationIdx_mul_relativeDegree_le_and
    (hF : IsFunctionField k F) (h : constantCompositum F k' F' = ⊤) (P' : Place k' F')
    [Algebra.IsSeparable k (P'.restrict k F).ResidueField] :
    ramificationIdx F P' * relativeDegree k F P' ≤ finrank F F' ∧
      finrank F F' ≤ finrank k k' ∧ finrank k k' ≤ relativeDegree k F P' := by
  let := finiteDimensional_of_constantCompositum_eq_top (k := k) (k' := k') h
  have hF' := hF.of_constantCompositum_eq_top h
  let := P'.finiteDimensional_residueField hF'
  refine ⟨?_, finrank_le_finrank_of_constantCompositum_eq_top (k := k) h, ?_⟩
  · exact ramificationIdx_mul_relativeDegree_le_finrank k F P'
  · have hdeg := finrank_mul_degree_eq_relativeDegree_mul_degree_restrict k F P'
    have hle := degree_restrict_le_degree_of_isPurelyInseparable k F P'
    have hpos := (P'.restrict k F).one_le_degree_of_isFunctionField hF
    refine Nat.le_of_mul_le_mul_right ?_ hpos
    calc finrank k k' * (P'.restrict k F).degree ≤ finrank k k' * P'.degree :=
          Nat.mul_le_mul_left _ hle
      _ = _ := hdeg

/-- **A purely inseparable constant extension does not ramify a place with separable residue
field**: if `k' / k` is finite and purely inseparable, `F' = F · k'`, and the residue field of the
place `P` below `P'` is separable over `k`, then `e(P' ∣ P) = 1`. -/
theorem ramificationIdx_eq_one_of_isPurelyInseparable (hF : IsFunctionField k F)
    (h : constantCompositum F k' F' = ⊤) (P' : Place k' F')
    [Algebra.IsSeparable k (P'.restrict k F).ResidueField] :
    ramificationIdx F P' = 1 := by
  let := finiteDimensional_of_constantCompositum_eq_top (k := k) (k' := k') h
  obtain ⟨h₁, h₂, h₃⟩ := ramificationIdx_mul_relativeDegree_le_and hF h P'
  have hf := one_le_relativeDegree k F P'
  nlinarith [ramificationIdx_pos F P']

/-- **The residue extension of a purely inseparable constant extension has full degree** at a
place with separable residue field: if `k' / k` is finite and purely inseparable, `F' = F · k'`,
and the residue field of the place below `P'` is separable over `k`, then
`f(P' ∣ P) = [k' : k]`. -/
theorem relativeDegree_eq_finrank_of_isPurelyInseparable (hF : IsFunctionField k F)
    (h : constantCompositum F k' F' = ⊤) (P' : Place k' F')
    [Algebra.IsSeparable k (P'.restrict k F).ResidueField] :
    relativeDegree k F P' = finrank k k' := by
  obtain ⟨h₁, h₂, h₃⟩ := ramificationIdx_mul_relativeDegree_le_and hF h P'
  have := ramificationIdx_pos F P'
  nlinarith

end PurelyInseparable

/-- The finite case of `TauCeti.Place.ramificationIdx_eq_one_of_isSeparable_residueField`: split
`k ⊆ k_s ⊆ k'` at the separable closure `k_s` of `k` in `k'`. -/
private theorem ramificationIdx_eq_one_of_isSeparable_residueField_of_finiteDimensional
    [FiniteDimensional k k'] (hF : IsFunctionField k F) (h : constantCompositum F k' F' = ⊤)
    (P' : Place k' F') [Algebra.IsSeparable k (P'.restrict k F).ResidueField] :
    ramificationIdx F P' = 1 := by
  let S := separableClosure k k'
  let E := constantCompositum F S F'
  let : Algebra S E := constantCompositumAlgebra F S F'
  have : IsScalarTower S E F' := isScalarTower_constantCompositum F S F'
  have : IsScalarTower k S E := isScalarTower_base_constantCompositum k F S F'
  have hE : constantCompositum F S E = ⊤ := (constantCompositum_eq_top_iff F S F' E).mpr rfl
  let : FiniteDimensional F E := finiteDimensional_of_constantCompositum_eq_top (k := k) hE
  let : Algebra.IsSeparable F E := isSeparable_of_constantCompositum_eq_top (k := k) hE
  let Q := P'.restrict S E
  -- The separable step `F · k_s / F` is unramified, with separable residue extensions.
  obtain ⟨hQe, hQsep⟩ := (ramificationIdx_eq_one_and_isSeparable_iff_isUnramifiedAt k F Q).mpr
    (isUnramifiedAt_of_constantCompositum_eq_top (k := k) hE Q)
  have : Algebra.IsSeparable k (Q.restrict k F).ResidueField := by
    rw [restrict_restrict]
    infer_instance
  have := isSeparable_residueField_of_isSeparable_restrict k F Q
  -- The purely inseparable step `F' / F · k_s` does not ramify `Q`.
  have he : ramificationIdx E P' = 1 :=
    ramificationIdx_eq_one_of_isPurelyInseparable (k := S)
      (hF.of_constantCompositum_eq_top hE) (constantCompositum_eq_top_of_eq_top F k' F' E h) P'
  rw [ramificationIdx_restrict_mul (k₁ := S) (F₀ := F) (F₁ := E), he, one_mul]
  exact hQe

/-- **A constant field extension does not ramify a place with separable residue field**: if
`k' / k` is algebraic, finite or not and separable or not, `F' = F · k'`, and the residue field of
the place `P` below `P'` is separable over `k`, then `e(P' ∣ P) = 1`. -/
theorem ramificationIdx_eq_one_of_isSeparable_residueField [Algebra.IsAlgebraic k k']
    (hF : IsFunctionField k F) (h : constantCompositum F k' F' = ⊤) (P' : Place k' F')
    [Algebra.IsSeparable k (P'.restrict k F).ResidueField] :
    ramificationIdx F P' = 1 := by
  -- The index over a finite part `F · L` of the extension is one.
  obtain ⟨L, hL, he⟩ := exists_finiteDimensional_ramificationIdx_constantCompositum_eq_one
    (k := k) h P'
  let : FiniteDimensional k L := hL
  let E := constantCompositum F L F'
  let : Algebra L E := constantCompositumAlgebra F L F'
  have : IsScalarTower L E F' := isScalarTower_constantCompositum F L F'
  have : IsScalarTower k L E := isScalarTower_base_constantCompositum k F L F'
  have hE : constantCompositum F L E = ⊤ := (constantCompositum_eq_top_iff F L F' E).mpr rfl
  let : FiniteDimensional F E := finiteDimensional_of_constantCompositum_eq_top (k := k) hE
  let Q := P'.restrict L E
  have : Algebra.IsSeparable k (Q.restrict k F).ResidueField := by
    rw [restrict_restrict]
    infer_instance
  rw [ramificationIdx_restrict_mul (k₁ := L) (F₀ := F) (F₁ := E), he, one_mul]
  exact ramificationIdx_eq_one_of_isSeparable_residueField_of_finiteDimensional hF hE Q

end Place

/-- **A place with separable residue field makes `F` linearly disjoint from purely inseparable
constants**: if `k' / k` is finite and purely inseparable, `F' = F · k'`, and some place of `F'`
lies over a place of `F` whose residue field is separable over `k`, then `[F · k' : F] = [k' : k]`.
By `TauCeti.linearDisjoint_fieldRange_of_finrank_constantCompositum_eq`, `F` and the image of `k'`
are then linearly disjoint over `k`. -/
theorem finrank_eq_finrank_of_isPurelyInseparable_of_isSeparable_residueField
    [FiniteDimensional k k'] [IsPurelyInseparable k k'] [Algebra.IsIntegral F F']
    (hF : IsFunctionField k F) (h : constantCompositum F k' F' = ⊤) (P' : Place k' F')
    [Algebra.IsSeparable k (P'.restrict k F).ResidueField] :
    finrank F F' = finrank k k' := by
  obtain ⟨h₁, h₂, h₃⟩ := Place.ramificationIdx_mul_relativeDegree_le_and hF h P'
  have := Place.ramificationIdx_pos F P'
  nlinarith

end TauCeti
