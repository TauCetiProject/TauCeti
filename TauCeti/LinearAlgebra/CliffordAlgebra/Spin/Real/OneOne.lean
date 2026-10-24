/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Arsinh
public import TauCeti.LinearAlgebra.CliffordAlgebra.RealForm.OneOne
public import TauCeti.LinearAlgebra.CliffordAlgebra.Spin.Real.Basic
public import TauCeti.LinearAlgebra.CliffordAlgebra.Spin.RootsOfUnity
import TauCeti.RingTheory.RootsOfUnity.Basic
import Mathlib.GroupTheory.NoncommCoprod

/-!
# The real Spin group of signature `(1, 1)`

Let `e₁, e₂` be the coordinate generators of `Cliff(1, 1)`, so that `e₁² = 1`, `e₂² = -1` and
`e₁ e₂ = -e₂ e₁`, and let `z = e₁ e₂` (`CliffordAlgebra.realCliffordOneOneVolume`). Then

`z² = 1`, `reverse z = -z`,

and the even Clifford algebra is the two-dimensional algebra spanned by `1` and `z`, as proved
in `TauCeti.LinearAlgebra.CliffordAlgebra.RealForm.OneOne`. This file computes the Spin group
`Spin(1, 1) = CliffordAlgebra.realCliffordSpinGroup 1 1` explicitly: its
elements are exactly the even elements `a + b z` with `a² - b² = 1`, that is, exactly the elements
`± (cosh t + sinh t z)` for `t : ℝ`. Since `z² = 1`, the hyperbolic rotations
`cosh t + sinh t z` multiply by adding their parameters, so they form a subgroup isomorphic to
`(ℝ, +)`, and with the scalars `±1` they exhaust the group:

`Spin(1, 1) ≅ μ₂(ℝ) × ℝ`.

This is the lowest-rank indefinite real Spin group. It is commutative, and it has two connected
components, the hyperbolic rotations and their negatives
(`TauCeti.Topology.Algebra.CliffordAlgebra.Spin.Real.OneOne`).

Everything is computed in the matrix model `TauCeti.realCliffordOneOneEquivMatrix` of `Cliff(1, 1)`,
in which `a + b z` is the matrix `!![a, b; b, a]` and the even elements are exactly these matrices.

## Main definitions

* `CliffordAlgebra.realCliffordSpinOneOneHyperbolicRotation`: the homomorphism
  `t ↦ cosh t + sinh t z` from `(ℝ, +)` to `Spin(1, 1)`.
* `CliffordAlgebra.realCliffordSpinOneOneEquiv`: the isomorphism `μ₂(ℝ) × ℝ ≃* Spin(1, 1)`,
  `(ζ, t) ↦ ζ (cosh t + sinh t z)`.
* `CliffordAlgebra.realCliffordSpinOneOneSign`: the sign `ζ` of `ζ (cosh t + sinh t z)`, a
  homomorphism `Spin(1, 1) →* μ₂(ℝ)` whose kernel is the group of hyperbolic rotations
  (`CliffordAlgebra.ker_realCliffordSpinOneOneSign`).

## Main results

* `CliffordAlgebra.mem_realCliffordSpinGroup_one_one_iff`: `Spin(1, 1)` consists of the elements
  `a + b z` with `a² - b² = 1`.
* `CliffordAlgebra.mem_realCliffordSpinGroup_one_one_iff_exists_cosh_sinh`: `Spin(1, 1)` consists
  of the elements `± (cosh t + sinh t z)`.

## References

* H. B. Lawson and M.-L. Michelsohn, *Spin Geometry* (1989), Chapter I, §2.
-/

public section

open TauCeti Real

namespace CliffordAlgebra

/-- **The elements of `Spin(1, 1)`.** They are the elements `a + b z` of `Cliff(1, 1)` with
`a² - b² = 1`. -/
theorem mem_realCliffordSpinGroup_one_one_iff {x : CliffordAlgebra (realCliffordForm 1 1)} :
    x ∈ realCliffordSpinGroup 1 1 ↔
      ∃ a b : ℝ, a ^ 2 - b ^ 2 = 1 ∧ x = algebraMap ℝ _ a + b • realCliffordOneOneVolume := by
  constructor
  · -- A Spin element is even, and its norm `(a - b z) (a + b z) = a² - b²` is `1`.
    intro hx
    obtain ⟨a, b, rfl⟩ :=
      exists_eq_algebraMap_add_smul_realCliffordOneOneVolume (spinGroup.mem_even hx)
    refine ⟨a, b, ?_, rfl⟩
    have h := spinGroup.star_mul_self_of_mem hx
    rw [star_algebraMap_add_smul_realCliffordOneOneVolume,
      algebraMap_add_smul_realCliffordOneOneVolume_mul] at h
    have hcoeff := (algebraMap_add_smul_realCliffordOneOneVolume_inj
      (a := a * a + -b * b) (b := a * b + -b * a) (a' := 1) (b' := 0)).mp
        (by simpa using h)
    linear_combination hcoeff.1
  · -- `a + b z = e₁ (a e₁ + b e₂)` is a product of two vectors of norm one.
    rintro ⟨a, b, hab, rfl⟩
    have h : ι (realCliffordForm 1 1) (Pi.single 0 1) * ι _ ![a, b] =
        algebraMap ℝ _ a + b • realCliffordOneOneVolume := by
      apply realCliffordOneOneEquivMatrix.injective
      rw [map_mul, realCliffordOneOneEquivMatrix_ι, realCliffordOneOneEquivMatrix_ι,
        realCliffordOneOneEquivMatrix_algebraMap_add_smul_realCliffordOneOneVolume]
      ext i j
      fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
    rw [← h]
    exact ι_mul_ι_mem_spinGroup_of_norm_mul_norm_eq_one _ _
      (by simp; linear_combination hab)

/-- **The elements of `Spin(1, 1)` as hyperbolic rotations.** They are the elements
`± (cosh t + sinh t z)` for `t : ℝ`. -/
theorem mem_realCliffordSpinGroup_one_one_iff_exists_cosh_sinh
    {x : CliffordAlgebra (realCliffordForm 1 1)} :
    x ∈ realCliffordSpinGroup 1 1 ↔ ∃ t : ℝ,
      x = algebraMap ℝ _ (cosh t) + sinh t • realCliffordOneOneVolume ∨
        x = -(algebraMap ℝ _ (cosh t) + sinh t • realCliffordOneOneVolume) := by
  rw [mem_realCliffordSpinGroup_one_one_iff]
  constructor
  · -- `|a| = √(1 + b²) = cosh (arsinh b)`, and the sign of `a` selects the sign.
    rintro ⟨a, b, hab, rfl⟩
    have ha : a ^ 2 = 1 + b ^ 2 := by linear_combination hab
    have ha_ne : a ≠ 0 := by rintro rfl; nlinarith
    rcases lt_or_gt_of_ne ha_ne with ha0 | ha0
    · refine ⟨arsinh (-b), Or.inr ?_⟩
      rw [cosh_arsinh, sinh_arsinh, neg_sq, ← ha, Real.sqrt_sq_eq_abs, abs_of_neg ha0, map_neg,
        neg_smul, neg_add, neg_neg, neg_neg]
    · refine ⟨arsinh b, Or.inl ?_⟩
      rw [cosh_arsinh, sinh_arsinh, ← ha, Real.sqrt_sq ha0.le]
  · rintro ⟨t, rfl | rfl⟩
    · exact ⟨cosh t, sinh t, cosh_sq_sub_sinh_sq t, rfl⟩
    · refine ⟨-cosh t, -sinh t, by rw [neg_sq, neg_sq, cosh_sq_sub_sinh_sq], ?_⟩
      rw [map_neg, neg_smul, neg_add]

/-- **The hyperbolic rotations in `Spin(1, 1)`**, `t ↦ cosh t + sinh t z`, a homomorphism from
`(ℝ, +)` because `z² = 1`. -/
noncomputable def realCliffordSpinOneOneHyperbolicRotation :
    Multiplicative ℝ →* realCliffordSpinGroup 1 1 where
  toFun t := ⟨algebraMap ℝ _ (cosh t.toAdd) + sinh t.toAdd • realCliffordOneOneVolume,
    mem_realCliffordSpinGroup_one_one_iff.mpr ⟨_, _, cosh_sq_sub_sinh_sq _, rfl⟩⟩
  map_one' := Subtype.ext (by simp)
  map_mul' s t := by
    apply Subtype.ext
    simp only [toAdd_mul, cosh_add, sinh_add, Submonoid.coe_mul,
      algebraMap_add_smul_realCliffordOneOneVolume_mul]
    congr 2; ring

@[simp]
theorem coe_realCliffordSpinOneOneHyperbolicRotation_apply (t : Multiplicative ℝ) :
    (realCliffordSpinOneOneHyperbolicRotation t : CliffordAlgebra (realCliffordForm 1 1)) =
      algebraMap ℝ _ (cosh t.toAdd) + sinh t.toAdd • realCliffordOneOneVolume :=
  (rfl)

/-- The hyperbolic rotations are pairwise distinct. -/
theorem realCliffordSpinOneOneHyperbolicRotation_injective :
    Function.Injective realCliffordSpinOneOneHyperbolicRotation := by
  intro s t h
  have h' := congrArg Subtype.val h
  rw [coe_realCliffordSpinOneOneHyperbolicRotation_apply,
    coe_realCliffordSpinOneOneHyperbolicRotation_apply,
    algebraMap_add_smul_realCliffordOneOneVolume_inj] at h'
  exact Multiplicative.toAdd.injective (sinh_injective h'.2)

private theorem exists_isUnit_realCliffordForm_one_one :
    ∃ v, IsUnit (realCliffordForm 1 1 v) :=
  ⟨Pi.single 0 1, by simp⟩

/-- The map `(ζ, t) ↦ ζ (cosh t + sinh t z)` from `μ₂(ℝ) × ℝ` to `Spin(1, 1)`. -/
private noncomputable def realCliffordSpinOneOneHom :
    rootsOfUnity 2 ℝ × Multiplicative ℝ →* realCliffordSpinGroup 1 1 :=
  (rootsOfUnityToSpin _ exists_isUnit_realCliffordForm_one_one).noncommCoprod
    realCliffordSpinOneOneHyperbolicRotation fun ζ t ↦ by
      rw [Commute, SemiconjBy, Subtype.ext_iff, Submonoid.coe_mul, Submonoid.coe_mul,
        coe_rootsOfUnityToSpin_apply]
      exact Algebra.commutes _ _

private theorem coe_realCliffordSpinOneOneHom_apply (p : rootsOfUnity 2 ℝ × Multiplicative ℝ) :
    (realCliffordSpinOneOneHom p : CliffordAlgebra (realCliffordForm 1 1)) =
      algebraMap ℝ _ (((p.1 : ℝˣ) : ℝ) * cosh p.2.toAdd) +
        (((p.1 : ℝˣ) : ℝ) * sinh p.2.toAdd) • realCliffordOneOneVolume := by
  rw [realCliffordSpinOneOneHom, MonoidHom.noncommCoprod_apply, Submonoid.coe_mul,
    coe_rootsOfUnityToSpin_apply, coe_realCliffordSpinOneOneHyperbolicRotation_apply]
  simp [Algebra.smul_def, mul_add, mul_assoc]

/-- Distinct pairs `(ζ, t)` give distinct elements: compare the coefficients of `1` and of `z`,
using that `cosh` is positive and `sinh` is injective. -/
private theorem realCliffordSpinOneOneHom_injective :
    Function.Injective realCliffordSpinOneOneHom := by
  rintro ⟨ζ, s⟩ ⟨η, t⟩ h
  have h' := congrArg Subtype.val h
  rw [coe_realCliffordSpinOneOneHom_apply, coe_realCliffordSpinOneOneHom_apply,
    algebraMap_add_smul_realCliffordOneOneVolume_inj] at h'
  obtain ⟨hc, hs⟩ := h'
  have hζη : ((ζ : ℝˣ) : ℝ) = ((η : ℝˣ) : ℝ) := by
    rcases eq_one_or_eq_negOneRootsOfUnity ζ with rfl | rfl <;>
      rcases eq_one_or_eq_negOneRootsOfUnity η with rfl | rfl <;>
      simp only [OneMemClass.coe_one, coe_negOneRootsOfUnity, Units.val_neg, Units.val_one,
        one_mul, neg_one_mul] at hc ⊢ <;>
      nlinarith [cosh_pos s.toAdd, cosh_pos t.toAdd]
  rw [← hζη] at hs
  exact Prod.ext (Subtype.ext (Units.ext hζη))
    (Multiplicative.toAdd.injective (sinh_injective (mul_left_cancel₀ (Units.ne_zero _) hs)))

private theorem realCliffordSpinOneOneHom_surjective :
    Function.Surjective realCliffordSpinOneOneHom := by
  rintro ⟨x, hx⟩
  obtain ⟨t, rfl | rfl⟩ := mem_realCliffordSpinGroup_one_one_iff_exists_cosh_sinh.mp hx
  · exact ⟨(1, Multiplicative.ofAdd t), Subtype.ext (by
      simp [coe_realCliffordSpinOneOneHom_apply])⟩
  · refine ⟨(negOneRootsOfUnity, Multiplicative.ofAdd t), Subtype.ext ?_⟩
    simp only [coe_realCliffordSpinOneOneHom_apply, coe_negOneRootsOfUnity, Units.val_neg,
      Units.val_one,
      toAdd_ofAdd, neg_one_mul, map_neg, neg_smul, neg_add]

private theorem realCliffordSpinOneOneHom_bijective :
    Function.Bijective realCliffordSpinOneOneHom :=
  ⟨realCliffordSpinOneOneHom_injective, realCliffordSpinOneOneHom_surjective⟩

/-- **`Spin(1, 1) ≅ μ₂(ℝ) × ℝ`.** Every element of `Spin(1, 1)` is uniquely `ζ (cosh t + sinh t z)`
with `ζ = ±1` and `t : ℝ`. -/
noncomputable def realCliffordSpinOneOneEquiv :
    rootsOfUnity 2 ℝ × Multiplicative ℝ ≃* realCliffordSpinGroup 1 1 :=
  MulEquiv.ofBijective realCliffordSpinOneOneHom realCliffordSpinOneOneHom_bijective

@[simp]
theorem coe_realCliffordSpinOneOneEquiv_apply (p : rootsOfUnity 2 ℝ × Multiplicative ℝ) :
    (realCliffordSpinOneOneEquiv p : CliffordAlgebra (realCliffordForm 1 1)) =
      algebraMap ℝ _ (((p.1 : ℝˣ) : ℝ) * cosh p.2.toAdd) +
        (((p.1 : ℝˣ) : ℝ) * sinh p.2.toAdd) • realCliffordOneOneVolume := by
  rw [realCliffordSpinOneOneEquiv, MulEquiv.ofBijective_apply, coe_realCliffordSpinOneOneHom_apply]

/-- On the second factor, `realCliffordSpinOneOneEquiv` is the hyperbolic rotation. -/
@[simp]
theorem realCliffordSpinOneOneEquiv_one_mk (t : Multiplicative ℝ) :
    realCliffordSpinOneOneEquiv (1, t) = realCliffordSpinOneOneHyperbolicRotation t :=
  Subtype.ext (by simp)

/-- The sign `ζ = ±1` of an element `ζ (cosh t + sinh t z)` of `Spin(1, 1)`. -/
noncomputable def realCliffordSpinOneOneSign : realCliffordSpinGroup 1 1 →* rootsOfUnity 2 ℝ :=
  (MonoidHom.fst _ _).comp realCliffordSpinOneOneEquiv.symm.toMonoidHom

theorem realCliffordSpinOneOneSign_apply (x : realCliffordSpinGroup 1 1) :
    realCliffordSpinOneOneSign x = (realCliffordSpinOneOneEquiv.symm x).1 :=
  (rfl)

@[simp]
theorem realCliffordSpinOneOneSign_realCliffordSpinOneOneEquiv
    (p : rootsOfUnity 2 ℝ × Multiplicative ℝ) :
    realCliffordSpinOneOneSign (realCliffordSpinOneOneEquiv p) = p.1 := by
  simp [realCliffordSpinOneOneSign]

/-- Every hyperbolic rotation has positive sign. -/
@[simp]
theorem realCliffordSpinOneOneSign_realCliffordSpinOneOneHyperbolicRotation
    (t : Multiplicative ℝ) :
    realCliffordSpinOneOneSign (realCliffordSpinOneOneHyperbolicRotation t) = 1 := by
  rw [← realCliffordSpinOneOneEquiv_one_mk,
    realCliffordSpinOneOneSign_realCliffordSpinOneOneEquiv]

/-- The kernel of the sign is the group of hyperbolic rotations. -/
theorem ker_realCliffordSpinOneOneSign :
    realCliffordSpinOneOneSign.ker = realCliffordSpinOneOneHyperbolicRotation.range := by
  ext x
  obtain ⟨⟨ζ, t⟩, rfl⟩ := realCliffordSpinOneOneEquiv.surjective x
  simp only [MonoidHom.mem_ker, realCliffordSpinOneOneSign_realCliffordSpinOneOneEquiv,
    MonoidHom.mem_range, ← realCliffordSpinOneOneEquiv_one_mk,
    realCliffordSpinOneOneEquiv.injective.eq_iff, Prod.ext_iff]
  exact ⟨fun h ↦ ⟨t, h.symm, rfl⟩, fun ⟨_, h, _⟩ ↦ h.symm⟩

/-- Both signs occur in `Spin(1, 1)`. -/
theorem realCliffordSpinOneOneSign_surjective : Function.Surjective realCliffordSpinOneOneSign :=
  fun ζ ↦ ⟨realCliffordSpinOneOneEquiv (ζ, 1), by simp⟩

end CliffordAlgebra
