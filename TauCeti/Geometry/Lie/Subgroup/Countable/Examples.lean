/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Lie.Subgroup.Countable.Basic
public import TauCeti.Geometry.Manifold.Algebra.TypeTags
public import Mathlib.Topology.Algebra.Group.Matrix

import Mathlib.Data.Rat.Cast.CharZero
import Mathlib.Data.Rat.Encodable
import Mathlib.Basic.Countable.Basic

/-!
# Rational and integral subgroup controls

The rational additive subgroup of the real line and the integral special-linear subgroup of
SL2 over the reals are nontrivial countable subgroups. Their canonical Lie algebras are zero,
and they have no native connected immersed Lie-subgroup presentations.

The real additive group is written `Multiplicative ℝ` to use the multiplicative subgroup API;
its charts and smooth structure are those of the real line. For SL2 over the reals, the
conclusions hold for every Lie-group atlas on the existing matrix-subspace topology.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Springer GTM 218 (2013), Chapter 7,
  Example 7.3(f), pp.151–152, and Proposition 7.17, pp.157–158.
* Mathlib, `LinearAlgebra/Matrix/SpecialLinearGroup.lean`, the integral map and transvections.
-/

public section

open Set Function
open scoped ContDiff Manifold

noncomputable section

namespace TauCeti.Lie

/-- The image of the rational additive group in the real additive group. -/
def rationalAdditiveSubgroup : Subgroup (Multiplicative ℝ) :=
  (Rat.castHom ℝ).toAddMonoidHom.toMultiplicative.range

/-- Membership in the rational additive subgroup is represented by a rational number. -/
@[simp]
theorem mem_rationalAdditiveSubgroup (x : Multiplicative ℝ) :
    x ∈ rationalAdditiveSubgroup ↔ ∃ q : ℚ, Multiplicative.ofAdd (q : ℝ) = x := by
  rw [rationalAdditiveSubgroup, MonoidHom.mem_range]
  constructor
  · rintro ⟨q, hq⟩
    exact ⟨q.toAdd, hq⟩
  · rintro ⟨q, hq⟩
    exact ⟨Multiplicative.ofAdd q, hq⟩

/-- The rational additive subgroup is countable. -/
theorem countable_rationalAdditiveSubgroup :
    (rationalAdditiveSubgroup : Set (Multiplicative ℝ)).Countable := by
  let _ : Countable (Multiplicative ℚ) := .of_equiv ℚ Multiplicative.ofAdd
  rw [rationalAdditiveSubgroup, MonoidHom.coe_range]
  exact Set.countable_range _

/-- The rational additive subgroup contains a nonidentity element. -/
theorem rationalAdditiveSubgroup_ne_bot : rationalAdditiveSubgroup ≠ ⊥ := by
  have h1 : Multiplicative.ofAdd (1 : ℝ) ∈ rationalAdditiveSubgroup := by
    rw [mem_rationalAdditiveSubgroup]
    exact ⟨(1 : ℚ), by simp⟩
  intro h
  have heq : Multiplicative.ofAdd (1 : ℝ) = (1 : Multiplicative ℝ) := by
    simpa only [h, Subgroup.mem_bot] using h1
  exact one_ne_zero (congrArg Multiplicative.toAdd heq)

/-- The rational additive subgroup has zero canonical Lie algebra. -/
@[simp]
theorem lieSubalgebraOfSubgroup_rationalAdditiveSubgroup_eq_bot :
    TauCeti.Lie.lieSubalgebraOfSubgroup (I := 𝓘(ℝ, ℝ)) rationalAdditiveSubgroup = ⊥ :=
  lieSubalgebraOfSubgroup_eq_bot_of_countable countable_rationalAdditiveSubgroup

/-- The nontrivial rational additive subgroup has no connected immersed presentation. -/
theorem not_isImmersedLieSubgroup_rationalAdditiveSubgroup :
    ¬ TauCeti.Lie.IsImmersedLieSubgroup (I := 𝓘(ℝ, ℝ)) rationalAdditiveSubgroup := by
  intro h
  exact rationalAdditiveSubgroup_ne_bot (h.eq_bot_of_countable countable_rationalAdditiveSubgroup)




open Matrix

/-- The image of SL2 over the integers in SL2 over the reals. -/
def integralSL2Subgroup : Subgroup (SpecialLinearGroup (Fin 2) ℝ) :=
  (SpecialLinearGroup.map (Int.castRingHom ℝ)).range

/-- Membership in the integral special-linear subgroup is represented by an integral matrix. -/
@[simp]
theorem mem_integralSL2Subgroup (g : SpecialLinearGroup (Fin 2) ℝ) :
    g ∈ integralSL2Subgroup ↔ ∃ γ : SpecialLinearGroup (Fin 2) ℤ,
      (γ : SpecialLinearGroup (Fin 2) ℝ) = g := by
  rw [integralSL2Subgroup, MonoidHom.mem_range]

/-- The integral special-linear subgroup is countable. -/
theorem countable_integralSL2Subgroup :
    (integralSL2Subgroup : Set (SpecialLinearGroup (Fin 2) ℝ)).Countable := by
  let _ : Countable (Matrix (Fin 2) (Fin 2) ℤ) :=
    inferInstanceAs (Countable (Fin 2 → Fin 2 → ℤ))
  let _ : Countable (SpecialLinearGroup (Fin 2) ℤ) :=
    inferInstanceAs (Countable {M : Matrix (Fin 2) (Fin 2) ℤ // M.det = 1})
  rw [integralSL2Subgroup, MonoidHom.coe_range]
  exact Set.countable_range _

/-- The integral special-linear subgroup is nontrivial. -/
theorem integralSL2Subgroup_ne_bot : integralSL2Subgroup ≠ ⊥ := by
  let u : SpecialLinearGroup (Fin 2) ℤ :=
    SpecialLinearGroup.transvection (by decide : (0 : Fin 2) ≠ 1) (1 : ℤ)
  have hu : SpecialLinearGroup.map (Int.castRingHom ℝ) u ∈ integralSL2Subgroup := by
    rw [mem_integralSL2Subgroup]
    exact ⟨u, rfl⟩
  intro h
  have heq : SpecialLinearGroup.map (Int.castRingHom ℝ) u = 1 := by
    simpa only [h, Subgroup.mem_bot] using hu
  have hentry := congrArg (fun M : SpecialLinearGroup (Fin 2) ℝ ↦
    (M : Matrix (Fin 2) (Fin 2) ℝ) 0 1) heq
  norm_num [u, SpecialLinearGroup.map_apply_coe, SpecialLinearGroup.transvection_coe,
    Matrix.single] at hentry

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [ChartedSpace H (SpecialLinearGroup (Fin 2) ℝ)] [LieGroup I ∞ (SpecialLinearGroup (Fin 2) ℝ)]

/-- The integral special-linear subgroup has zero canonical Lie algebra. -/
@[simp]
theorem lieSubalgebraOfSubgroup_integralSL2Subgroup_eq_bot :
    TauCeti.Lie.lieSubalgebraOfSubgroup (I := I) integralSL2Subgroup = ⊥ :=
  lieSubalgebraOfSubgroup_eq_bot_of_countable countable_integralSL2Subgroup

omit [FiniteDimensional ℝ E] in
/-- The nontrivial integral special-linear subgroup has no connected immersed presentation. -/
theorem not_isImmersedLieSubgroup_integralSL2Subgroup :
    ¬ TauCeti.Lie.IsImmersedLieSubgroup (I := I) integralSL2Subgroup := by
  intro h
  exact integralSL2Subgroup_ne_bot (h.eq_bot_of_countable countable_integralSL2Subgroup)


end TauCeti.Lie
