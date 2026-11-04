/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Fourier.AddCircle
import Mathlib.Algebra.BigOperators.Pi

/-!
# Integer characters of finite-dimensional tori

Every continuous character of `ι → Circle`, for finite `ι`, has a unique expression
`z ↦ ∏ i, z i ^ m i` with `m : ι → ℤ`. Multiplication of characters corresponds to addition
of integer weights. The equivalence `TauCeti.finiteProductCircleCharacters` retains both the
product formula and the recovery of each weight by restriction to its coordinate circle.
It includes the zero-dimensional torus.

The one-circle classification is transported from the Fourier character classification of
`AddCircle 1`, using `AddCircle.homeomorphCircle` and `AddCircle.toCircle_zsmul`. The finite
product step uses `Finset.univ_prod_mulSingle`, so no lifting of a torus character to a chosen
real-valued argument is needed. Integer weights give the scalar character series associated
to torus Euler classes, including negative weights.

## References

* D. Bump, *Lie Groups*, second edition, Chapter 2.
* The Fourier classification in `TauCeti.Analysis.Fourier.AddCircle`.
-/

public section

open scoped BigOperators

namespace ContinuousMonoidHom

/-- A continuous character of the circle is a unique integer power. -/
theorem existsUnique_eq_zpow (χ : Circle →ₜ* Circle) :
    ∃! n : ℤ, ∀ z : Circle, χ z = z ^ n := by
  let ψ : AddChar (AddCircle (1 : ℝ)) ℂ :=
    { toFun := fun x ↦ (χ (AddCircle.toCircle x) : ℂ)
      map_zero_eq_one' := by simp
      map_add_eq_mul' := fun x y ↦ by simp [AddCircle.toCircle_add] }
  have hψ : Continuous ψ :=
    (continuous_induced_dom (f := ((↑) : Circle → ℂ))).comp
      (χ.continuous.comp AddCircle.continuous_toCircle)
  obtain ⟨n, hn⟩ := AddChar.exists_fourierAddChar_eq ψ hψ
  have hn' (z : Circle) : χ z = z ^ n := by
    obtain ⟨x, rfl⟩ := (AddCircle.homeomorphCircle (T := (1 : ℝ)) one_ne_zero).surjective z
    apply Circle.ext
    simpa only [AddCircle.homeomorphCircle_apply, TauCeti.fourierAddChar_apply,
      fourier_apply, AddCircle.toCircle_zsmul, ψ, AddChar.coe_mk] using
      (DFunLike.congr_fun hn x).symm
  refine ⟨n, hn', fun m hm ↦ ?_⟩
  apply TauCeti.fourier_injective (T := (1 : ℝ)) one_ne_zero
  ext x
  simp only [fourier_apply, AddCircle.toCircle_zsmul]
  exact congrArg (fun z : Circle ↦ (z : ℂ)) ((hm _).symm.trans (hn' _))

end ContinuousMonoidHom

namespace TauCeti

variable {ι : Type*} [Fintype ι]

/-- The continuous torus character with integer weight vector `m`. -/
noncomputable def circleProductCharacter (m : ι → ℤ) : PontryaginDual (ι → Circle) where
  toFun z := ∏ i, z i ^ m i
  map_one' := by simp
  map_mul' z w := by
    simp only [Pi.mul_apply, mul_zpow, Finset.prod_mul_distrib]
  continuous_toFun := continuous_finsetProd _ fun i _ ↦ (continuous_apply i).zpow (m i)

/-- The weight vector is evaluated by the product of its coordinate powers. -/
@[simp]
theorem circleProductCharacter_apply (m : ι → ℤ) (z : ι → Circle) :
    circleProductCharacter m z = ∏ i, z i ^ m i := (rfl)

/-- Restricting an integer character to a coordinate circle recovers that coordinate power. -/
@[simp↓]
theorem circleProductCharacter_mulSingle [DecidableEq ι] (m : ι → ℤ) (i : ι) (z : Circle) :
    circleProductCharacter m (Pi.mulSingle i z) = z ^ m i := by
  simp [circleProductCharacter_apply, Pi.mulSingle_apply]

/-- A weight supported on one coordinate gives that coordinate power. -/
@[simp↓]
theorem circleProductCharacter_single [DecidableEq ι] (i : ι) (n : ℤ) (z : ι → Circle) :
    circleProductCharacter (Pi.single i n) z = z i ^ n := by
  simp [circleProductCharacter_apply, Pi.single_apply]

/-- The zero weight is the trivial character. -/
@[simp]
theorem circleProductCharacter_zero : circleProductCharacter (0 : ι → ℤ) = 1 := by
  ext z
  simp

/-- Addition of weights is pointwise multiplication of characters. -/
@[simp]
theorem circleProductCharacter_add (m n : ι → ℤ) :
    circleProductCharacter (m + n) = circleProductCharacter m * circleProductCharacter n := by
  apply PontryaginDual.ext
  intro z
  calc
    circleProductCharacter (m + n) z = (∏ i, z i ^ m i) * ∏ i, z i ^ n i := by
      simp only [circleProductCharacter_apply, Pi.add_apply, zpow_add, Finset.prod_mul_distrib]
    -- The dual group multiplies characters pointwise.
    _ = (circleProductCharacter m * circleProductCharacter n) z := rfl

/-- Negating a weight inverts its character. -/
@[simp]
theorem circleProductCharacter_neg (m : ι → ℤ) :
    circleProductCharacter (-m) = (circleProductCharacter m)⁻¹ := by
  apply PontryaginDual.ext
  intro z
  calc
    circleProductCharacter (-m) z = (∏ i, z i ^ m i)⁻¹ := by
      simp only [circleProductCharacter_apply, Pi.neg_apply, zpow_neg, Finset.prod_inv_distrib]
    -- The dual group inverts characters pointwise.
    _ = (circleProductCharacter m)⁻¹ z := rfl

/-- Integer weight vectors are determined by their characters. -/
theorem circleProductCharacter_injective :
    Function.Injective (circleProductCharacter (ι := ι)) := by
  classical
  intro m n h
  funext i
  obtain ⟨_, -, huniq⟩ := (⟨zpowGroupHom (m i), continuous_zpow (m i)⟩ :
    Circle →ₜ* Circle).existsUnique_eq_zpow
  have hi (z : Circle) : z ^ m i = z ^ n i := by
    simpa only [circleProductCharacter_mulSingle] using DFunLike.congr_fun h (Pi.mulSingle i z)
  exact (huniq (m i) (fun _ ↦ rfl)).trans (huniq (n i) hi).symm

/-- Every continuous torus character is an integer character. -/
theorem circleProductCharacter_surjective :
    Function.Surjective (circleProductCharacter (ι := ι)) := by
  classical
  intro χ
  have h (i : ι) : ∃ n : ℤ, ∀ z : Circle, χ (Pi.mulSingle i z) = z ^ n := by
    -- Restrict the character along the continuous inclusion of this coordinate circle.
    let ψ : Circle →ₜ* Circle := χ.comp
      ⟨MonoidHom.mulSingle (fun _ : ι ↦ Circle) i,
        continuous_mulSingle (A := fun _ : ι ↦ Circle) i⟩
    exact ψ.existsUnique_eq_zpow.exists
  choose m hm using h
  refine ⟨m, PontryaginDual.ext fun z ↦ ?_⟩
  calc
    circleProductCharacter m z = ∏ i, χ (Pi.mulSingle i (z i)) := by
      simp only [circleProductCharacter_apply, hm]
    _ = χ (∏ i, Pi.mulSingle i (z i)) := (map_prod χ _ _).symm
    _ = χ z := congrArg χ (Finset.univ_prod_mulSingle z)

/-- The character group of a finite product of circles is its integer weight lattice.
Multiplicative type tags turn addition of weight vectors into the group law of the dual. -/
noncomputable def finiteProductCircleCharacters :
    Multiplicative (ι → ℤ) ≃* PontryaginDual (ι → Circle) :=
  MulEquiv.ofBijective
    ({ toFun := fun m ↦ circleProductCharacter m.toAdd
       map_one' := circleProductCharacter_zero
       map_mul' := fun m n ↦ circleProductCharacter_add m.toAdd n.toAdd } :
      Multiplicative (ι → ℤ) →* PontryaginDual (ι → Circle))
    ⟨fun m n h ↦ Multiplicative.toAdd.injective (circleProductCharacter_injective h),
      fun χ ↦ by
        obtain ⟨m, hm⟩ := circleProductCharacter_surjective χ
        exact ⟨Multiplicative.ofAdd m, hm⟩⟩

/-- The character associated to a weight has the specified product formula. -/
@[simp]
theorem finiteProductCircleCharacters_apply (m : Multiplicative (ι → ℤ)) (z : ι → Circle) :
    finiteProductCircleCharacters m z = ∏ i, z i ^ m.toAdd i := (rfl)

/-- Reconstructing a character from its weight vector recovers the character. -/
@[simp]
theorem circleProductCharacter_finiteProductCircleCharacters_symm
    (χ : PontryaginDual (ι → Circle)) :
    circleProductCharacter (finiteProductCircleCharacters.symm χ).toAdd = χ :=
  finiteProductCircleCharacters.apply_symm_apply χ

/-- The inverse equivalence recovers the original integer vector. -/
@[simp]
theorem finiteProductCircleCharacters_symm_circleProductCharacter (m : ι → ℤ) :
    (finiteProductCircleCharacters.symm (circleProductCharacter m)).toAdd = m :=
  congrArg Multiplicative.toAdd
    (finiteProductCircleCharacters.symm_apply_apply (Multiplicative.ofAdd m))

/-- Each entry of the inverse weight vector gives the restriction to its coordinate circle. -/
theorem _root_.PontryaginDual.apply_mulSingle_eq_zpow [DecidableEq ι]
    (χ : PontryaginDual (ι → Circle)) (i : ι) (z : Circle) :
    χ (Pi.mulSingle i z) = z ^ (finiteProductCircleCharacters.symm χ).toAdd i := by
  have h := DFunLike.congr_fun (circleProductCharacter_finiteProductCircleCharacters_symm χ)
    (Pi.mulSingle i z)
  exact h.symm.trans (circleProductCharacter_mulSingle _ i z)

end TauCeti
