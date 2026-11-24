/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.GroupAlgGeom.Lift.Basic
import TauCeti.GroupTheory.FreeGroup.Commuting
import TauCeti.GroupTheory.FreeGroup.Vaught
import TauCeti.GroupTheory.GroupAlgGeom.Irreducible.FreeGroup
import TauCeti.GroupTheory.GroupAlgGeom.SingleEquation

/-!
# Discrimination does not give lifts: the commutator equation

Over a free group `F`, the coordinate group `F_{R(S)}` of the commutator equation
`S : [x, y] = 1`, which is `F ∗ ℤ²` in rank at least two, is discriminated by `F`
(`TauCeti.GroupAlgGeom.isDiscriminatedBy_coordGroup_singleton_commutatorElement`). Nevertheless,
when `F` is nonabelian, the disjunction `x = z² ∨ y = z² ∨ x y = z²`, which is a single equation
`T(x, y, z) = 1` over `F` by Malcev's disjunction word, is compatible with `S`, since for
commuting `x = uᵐ`, `y = uⁿ` one of `m`, `n`, `m + n` is even, but has no lift to the generic
point of `S`: by discrimination, a lift would make one of `x`, `y`, `x y` a square in `F_{R(S)}`,
and none is. So the family of all solutions of `S` is not generic, and a lifting theorem needs
more than the discrimination of the coordinate group.

## Main results

* `TauCeti.GroupAlgGeom.Lift.exists_isCompatible_not_hasLift_commutator`: the square disjunction
  as one equation, compatible with `[x, y] = 1` without a lift.
* `TauCeti.GroupAlgGeom.Lift.not_isGenericFamily_V_commutator`: the family of all solutions of
  `[x, y] = 1` is not generic.

## References

* O. Kharlampovich, A. Myasnikov, *Implicit function theorem over free groups*, J. Algebra 290
  (2005), §3.1 (single equations), §6 (compatibility and lifts) and §7.6 (the coordinate group
  of a commutation system, and Definition 44).
-/

public section

namespace TauCeti.GroupAlgGeom.Lift

open Monoid.Coprod FreeGroup
open scoped commutatorElement

variable {α : Type*}

/- Over a nonabelian free group the square disjunction `x = z² ∨ y = z² ∨ x y = z²` is the
solution set of a single equation, by Malcev's disjunction word. -/
private theorem exists_V_singleton_eq_sq_or [Nontrivial α] :
    ∃ t : GX (FreeGroup α) (Bool ⊕ Fin 1),
      V (.id (FreeGroup α)) {t} = {v | v (.inl false) = v (.inr 0) ^ 2 ∨
        v (.inl true) = v (.inr 0) ^ 2 ∨ v (.inl false) * v (.inl true) = v (.inr 0) ^ 2} := by
  obtain ⟨a, b, hab⟩ := exists_pair_ne α
  have hc : ¬Commute (MonoidHom.id (FreeGroup α) (of a)) (MonoidHom.id _ (of b)) :=
    fun h => hab (eq_of_commute_of_of h)
  let x : GX (FreeGroup α) (Bool ⊕ Fin 1) := inr (of (.inl false))
  let y : GX (FreeGroup α) (Bool ⊕ Fin 1) := inr (of (.inl true))
  let z : GX (FreeGroup α) (Bool ⊕ Fin 1) := inr (of (.inr 0))
  refine ⟨malcevOrWord (inl (of a)) (inl (of b)) (x * (z ^ 2)⁻¹)
    (malcevOrWord (inl (of a)) (inl (of b)) (y * (z ^ 2)⁻¹) (x * y * (z ^ 2)⁻¹)), ?_⟩
  rw [V_singleton_malcevOrWord IsFreeGroup.isVaught IsFreeGroup.isCSA hc,
    V_singleton_malcevOrWord IsFreeGroup.isVaught IsFreeGroup.isCSA hc]
  ext v
  simp [x, y, z, mul_inv_eq_one]

/- An equation whose solutions in `F` form the square disjunction has no lift to the generic point
of `[x, y] = 1`: at the generic point none of `x`, `y`, `x y` is the square of the value of `z`,
and one `F`-homomorphism of the discriminated coordinate group keeps the three quotients
nontrivial, giving a solution in `F` at which none of the three disjuncts holds. -/
private theorem not_hasLift_of_V_eq_sq_or [Nonempty α] {t : GX (FreeGroup α) (Bool ⊕ Fin 1)}
    (ht : V (.id (FreeGroup α)) {t} = {v | v (.inl false) = v (.inr 0) ^ 2 ∨
      v (.inl true) = v (.inr 0) ^ 2 ∨ v (.inl false) * v (.inl true) = v (.inr 0) ^ 2}) :
    ¬HasLift (.id (FreeGroup α))
      {⁅(inr (of false) : GX (FreeGroup α) Bool), inr (of true)⁆} {t} := by
  classical
  intro h
  obtain ⟨w, hw⟩ := hasLift_iff.1 h
  have hsq := not_exists_genericPoint_eq_sq (α := α)
  push Not at hsq
  obtain ⟨φ, hφ⟩ := (isDiscriminatedBy_def _ _).1
    (isDiscriminatedBy_coordGroup_singleton_commutatorElement (α := α))
    {CoordGroup.genericPoint _ _ false * (w 0 ^ 2)⁻¹,
      CoordGroup.genericPoint _ _ true * (w 0 ^ 2)⁻¹,
      CoordGroup.genericPoint _ _ false * CoordGroup.genericPoint _ _ true * (w 0 ^ 2)⁻¹}
    (by simpa [mul_inv_eq_one] using hsq (w 0))
  -- The image under `φ` of the solution at the generic point solves `t` in `F`.
  have hp := ht ▸ φ.comp_mem_V hw
  simp [mul_inv_eq_one] at hφ hp
  tauto

/-- **A compatible equation without a lift.** Over a free group `F(α)` of rank at least two there
is a single equation `T(x, y, z) = 1` with the solutions of `x = z² ∨ y = z² ∨ x y = z²` which is
compatible with `[x, y] = 1` but does not lift to its generic point. -/
theorem exists_isCompatible_not_hasLift_commutator [Nontrivial α] :
    ∃ t : GX (FreeGroup α) (Bool ⊕ Fin 1),
      V (.id (FreeGroup α)) {t} = {v | v (.inl false) = v (.inr 0) ^ 2 ∨
        v (.inl true) = v (.inr 0) ^ 2 ∨ v (.inl false) * v (.inl true) = v (.inr 0) ^ 2} ∧
      IsCompatible (.id (FreeGroup α))
        {⁅(inr (of false) : GX (FreeGroup α) Bool), inr (of true)⁆} {t} ∧
      ¬HasLift (.id (FreeGroup α))
        {⁅(inr (of false) : GX (FreeGroup α) Bool), inr (of true)⁆} {t} := by
  obtain ⟨t, ht⟩ := exists_V_singleton_eq_sq_or (α := α)
  refine ⟨t, ht, isCompatible_iff.2 fun v hv => ?_, not_hasLift_of_V_eq_sq_or ht⟩
  -- Over a commuting pair one of `x`, `y`, `x y` is a square.
  obtain ⟨r, hr⟩ := IsFreeGroup.exists_eq_sq_of_commute (mem_V_commutator_iff.1 hv)
  exact ⟨fun _ => r, by simpa [ht] using hr⟩

/-- **The solutions of `[x, y] = 1` are not a generic family.** Over a free group of rank at least
two, the family of all solutions of `[x, y] = 1` is not generic, although the coordinate group is
discriminated by the free group. -/
theorem not_isGenericFamily_V_commutator [Nontrivial α] :
    ¬IsGenericFamily (.id (FreeGroup α))
      {⁅(inr (of false) : GX (FreeGroup α) Bool), inr (of true)⁆}
      (V (.id (FreeGroup α)) {⁅(inr (of false) : GX (FreeGroup α) Bool), inr (of true)⁆}) := by
  obtain ⟨t, -, ht, hnt⟩ := exists_isCompatible_not_hasLift_commutator (α := α)
  exact fun h => hnt (isGenericFamily_V_iff.1 h 1 t ht).hasLift

end TauCeti.GroupAlgGeom.Lift
