/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
public import Mathlib.Analysis.CStarAlgebra.Unitary.Connected
public import Mathlib.Analysis.CStarAlgebra.Unitization
public import Mathlib.Analysis.Normed.Ring.Units
public import Mathlib.Topology.Connected.PathConnected
public import TauCeti.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Polar.Basic
import TauCeti.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Sqrt.Basic

/-!
# Polar unitaries in C⋆-algebras: path-connectedness, norm perturbation, and unitization

For an invertible element `x` of a unital C⋆-algebra `A`, `Units.polarUnitary x` is the unitary
factor `u` of the polar decomposition `x = u |x|`, `|x| = √(x⋆x)` (see
`TauCeti/Analysis/SpecialFunctions/ContinuousFunctionalCalculus/Polar/Basic.lean`).
This file shows:

* `x` is joined to `u` by a path of invertible elements (`Units.joined_polarUnitary`):
  `t ↦ u ((1 - t)|x| + t)` stays invertible, since `(1 - t)|x| + t` is strictly positive for
  `t ∈ [0, 1]`. This straight-line path has the same endpoints as the polar deformation
  `t ↦ x (x⋆x)^(-t/2)` (consequences for matrices are in
  `TauCeti/Analysis/Matrix/GeneralLinearGroup/Polar.lean`).
* Perturbation and unitization bounds for `Units.polarUnitary`:
  `‖(a.polarUnitary : A) - 1‖ ≤ ‖(a : A) - 1‖ ^ 2 + 3 * ‖(a : A) - 1‖`,
  `Joined 1 a.polarUnitary` when `‖(a : A) - 1‖ ≤ 1 / 2`, and scalar-part preservation
  `Units.fst_polarUnitary_eq_one`.

## Main results

* `IsStrictlyPositive.one_sub_smul_add_smul`: `(1 - t) a + t b` is strictly positive for
  strictly positive `a`, `b` and `t ∈ [0, 1]`.
* `Units.joined_polarUnitary`: `x` and its polar unitary lie in one path component of `Aˣ`.
* `Units.exists_unitary_joined`: every invertible element is joined in `Aˣ` to a unitary.
* `Units.norm_polarUnitary_sub_one_le_sq_add`, `Units.norm_polarUnitary_sub_one_le`,
  `Units.joined_one_polarUnitary`, `Units.fst_polarUnitary_eq_one`.
* `IsConj.exists_mem_unitary_mul_mul_star_eq`: similar self-adjoint elements are unitarily
  equivalent.

## References

* B. Blackadar, *K-Theory for Operator Algebras*, 2nd ed., Cambridge University Press (1998),
  §8.1.
* B. Blackadar, *Operator Algebras*, Springer (2006), §§II.3.2–II.3.3, Prop. II.8.3.23.
* K. R. Davidson, *C⋆-Algebras by Example*, Amer. Math. Soc. (1996), §I.5, Lemma III.3.2.
* M. Rørdam, F. Larsen and N. Laustsen, *An Introduction to K-Theory for C⋆-Algebras*,
  Cambridge University Press (2000), §2.1.
-/

public section

open scoped ContinuousFunctionalCalculus NNReal

section Polar

noncomputable section

variable {A : Type*} [CStarAlgebra A]

/-- The straight-line interpolation `(1 - t) a + t b` between strictly positive `a` and `b` is
strictly positive for `t ∈ [0, 1]`. -/
theorem IsStrictlyPositive.one_sub_smul_add_smul [PartialOrder A] [StarOrderedRing A] {a b : A}
    (ha : IsStrictlyPositive a) (hb : IsStrictlyPositive b) (t : unitInterval) :
    IsStrictlyPositive ((1 - (t : ℝ)) • a + (t : ℝ) • b) := by
  obtain ⟨t, ht₀, ht₁⟩ := t
  rcases ht₀.eq_or_lt with rfl | ht₀
  · simpa using ha
  · exact isStrictlyPositive_add <| .inr ⟨smul_nonneg (by simpa using ht₁) ha.nonneg,
      hb.smul ht₀⟩

/-- An invertible element of a unital C⋆-algebra is joined to its polar unitary by a path of
invertible elements: `t ↦ u ((1 - t)|x| + t)`. -/
theorem Units.joined_polarUnitary [PartialOrder A] [StarOrderedRing A] (x : Aˣ) :
    Joined x (Unitary.toUnits x.polarUnitary) := by
  have ha := x.isStrictlyPositive_sqrt_star_mul
  let γ : unitInterval → A := fun t ↦
    (x.polarUnitary : A) * ((1 - (t : ℝ)) • CFC.sqrt (star (x : A) * x) + (t : ℝ) • 1)
  have hγ : ∀ t, IsUnit (γ t) := fun t ↦
    (Unitary.toUnits x.polarUnitary).isUnit.mul
      (ha.one_sub_smul_add_smul isStrictlyPositive_one t).isUnit
  refine ⟨⟨⟨fun t ↦ (hγ t).unit, ?_⟩, ?_, ?_⟩⟩
  · rw [Units.isOpenEmbedding_val.continuous_iff]
    simp only [Function.comp_def, IsUnit.unit_spec, γ]
    fun_prop
  · ext
    simp [γ]
  · ext
    simp [γ]

/-- Every invertible element of a unital C⋆-algebra is joined through invertible elements to a
unitary, namely its polar unitary. Stated without `Units.polarUnitary` and an order on `A`, so
that it applies to `CStarMatrix` without synthesizing a real functional calculus there. -/
theorem Units.exists_unitary_joined (x : Aˣ) : ∃ v : unitary A, Joined x (Unitary.toUnits v) :=
  let : PartialOrder A := CStarAlgebra.spectralOrder A
  let : StarOrderedRing A := CStarAlgebra.spectralOrderedRing A
  ⟨_, x.joined_polarUnitary⟩

/-- **Similar self-adjoint elements are unitarily equivalent.** If an invertible element of a unital
C⋆-algebra conjugates a self-adjoint `x` to a self-adjoint `y`, then so does a unitary, namely its
polar unitary. Stated without `Units.polarUnitary` and an order on `A`, so that it applies to
`CStarMatrix`. -/
theorem IsConj.exists_mem_unitary_mul_mul_star_eq {x y : A} (h : IsConj x y)
    (hx : IsSelfAdjoint x) (hy : IsSelfAdjoint y) : ∃ u ∈ unitary A, u * x * star u = y := by
  let _ : PartialOrder A := CStarAlgebra.spectralOrder A
  let _ : StarOrderedRing A := CStarAlgebra.spectralOrderedRing A
  obtain ⟨a, ha⟩ := h
  refine ⟨a.polarUnitary, a.polarUnitary.property, ?_⟩
  rw [a.polarUnitary_mul_eq_mul_polarUnitary hx hy ha, mul_assoc,
    Unitary.mul_star_self_of_mem a.polarUnitary.property, mul_one]

end

end Polar

namespace Units

section

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

/-- `‖(a.polarUnitary : A) - 1‖ ≤ ‖(a : A) - 1‖ ^ 2 + 3 * ‖(a : A) - 1‖` in a C⋆-algebra. -/
theorem norm_polarUnitary_sub_one_le_sq_add (a : Aˣ) :
    ‖(a.polarUnitary : A) - 1‖ ≤ ‖(a : A) - 1‖ ^ 2 + 3 * ‖(a : A) - 1‖ := by
  set h : A := star (a : A) * a; have hh0 : 0 ≤ h := star_mul_self_nonneg (a : A)
  have hh_eq : h - 1 = star ((a : A) - 1) * ((a : A) - 1) + star ((a : A) - 1) + ((a : A) - 1) := by
    dsimp [h]; simp only [star_sub, star_one, sub_mul, mul_sub, one_mul, mul_one]; abel
  have hh_sub : ‖h - 1‖ ≤ ‖(a : A) - 1‖ ^ 2 + 2 * ‖(a : A) - 1‖ := by
    rw [hh_eq]
    exact norm_add₃_le.trans (by rw [CStarRing.norm_star_mul_self, norm_star, sq]; linarith)
  have hs_sub : ‖CFC.sqrt h - 1‖ ≤ ‖h - 1‖ := CFC.norm_sqrt_sub_one_le hh0
  have hu_eq :
      (a.polarUnitary : A) - 1 = ((a : A) - 1) - (a.polarUnitary : A) * (CFC.sqrt h - 1) := by
    rw [mul_sub, mul_one, a.polarUnitary_mul_sqrt_star_mul]; abel
  have hu_le : ‖(a.polarUnitary : A) - 1‖ ≤ ‖(a : A) - 1‖ + ‖CFC.sqrt h - 1‖ := by
    rw [hu_eq, ← CStarRing.norm_coe_unitary_mul a.polarUnitary (CFC.sqrt h - 1)]
    exact norm_sub_le _ _
  linarith

/-- Distance bound `‖(a.polarUnitary : A) - 1‖ ≤ 4 * ‖(a : A) - 1‖` for `‖(a : A) - 1‖ ≤ 1`. -/
theorem norm_polarUnitary_sub_one_le {a : Aˣ} (ha : ‖(a : A) - 1‖ ≤ 1) :
    ‖(a.polarUnitary : A) - 1‖ ≤ 4 * ‖(a : A) - 1‖ := by
  nlinarith [a.norm_polarUnitary_sub_one_le_sq_add, norm_nonneg ((a : A) - 1)]

/-- When `‖(a : A) - 1‖ ≤ 1 / 2`, `a.polarUnitary` lies in the path component of `1`. -/
theorem joined_one_polarUnitary {a : Aˣ} (ha : ‖(a : A) - 1‖ ≤ 1 / 2) : Joined 1 a.polarUnitary :=
  Unitary.joined 1 a.polarUnitary <|
    a.norm_polarUnitary_sub_one_le_sq_add.trans_lt (by nlinarith [norm_nonneg ((a : A) - 1)])

end

/-- If a unit `a : (Unitization ℂ A)ˣ` has scalar part `1`, then so does `a.polarUnitary`. -/
theorem fst_polarUnitary_eq_one {A : Type*} [NonUnitalCStarAlgebra A]
    [PartialOrder (Unitization ℂ A)] [StarOrderedRing (Unitization ℂ A)]
    {a : (Unitization ℂ A)ˣ} (ha : (a : Unitization ℂ A).fst = 1) :
    (a.polarUnitary : Unitization ℂ A).fst = 1 := by
  let _ := CStarAlgebra.spectralOrder ℂ; let _ := CStarAlgebra.spectralOrderedRing ℂ
  have hmap : Units.map (Unitization.fstHom ℂ A : Unitization ℂ A →* ℂ) a = 1 := by ext; simp [ha]
  simpa [hmap, polarUnitary_one] using (a.coe_polarUnitary_map (Unitization.fstHom ℂ A)).symm

end Units
