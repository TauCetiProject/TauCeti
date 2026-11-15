/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.PontryaginDual
public import TauCeti.Topology.Algebra.ContinuousMonoidHom.Polish

/-!
# Topology of Pontryagin duals

Multiplication and inversion of characters are pointwise, as recorded by
`PontryaginDual.mul_apply` and `PontryaginDual.inv_apply`.

The Pontryagin dual of a second-countable locally compact monoid is Polish. For locally compact
abelian groups this ensures that finite Borel measures on the dual are tight and determined by
their Fourier–Stieltjes transforms.

A continuous character of the discrete group `ℤ` is determined by its value at `1`, which may be
any point of the unit circle. This file packages that correspondence as an isomorphism of
topological groups between the unit circle and the Pontryagin dual of `ℤ`. It lets statements
about the dual of `ℤ`, such as Fourier–Stieltjes transforms of measures on it, be read on the
concrete unit circle, where a character becomes the monomial `z ↦ zⁿ`.

## Main definitions

* `TauCeti.circleEquivPontryaginDualInt`: the point `z` of the unit circle corresponds to the
  character `n ↦ zⁿ` of `ℤ`.
* `TauCeti.piCircleEquivPontryaginDualPiInt`: for finite `ι`, the tuple `z : ι → Circle`
  corresponds to the character `m ↦ ∏ i, z i ^ m i` of `ι → ℤ`.

## References

* W. Rudin, *Fourier Analysis on Groups*, Interscience (1962), §1.2 (the dual group).
-/

public section

noncomputable section

namespace PontryaginDual

variable {A : Type*} [Monoid A] [TopologicalSpace A]

/-- Multiplication of characters is pointwise. -/
@[simp]
theorem mul_apply (χ ψ : PontryaginDual A) (a : A) : (χ * ψ) a = χ a * ψ a := (rfl)

/-- Inversion of characters is pointwise. -/
@[simp]
theorem inv_apply (χ : PontryaginDual A) (a : A) : χ⁻¹ a = (χ a)⁻¹ := (rfl)

end PontryaginDual

namespace TauCeti

/-- The Pontryagin dual of a second-countable locally compact monoid is Polish. -/
instance instPolishSpacePontryaginDual {A : Type*} [Monoid A] [TopologicalSpace A]
    [LocallyCompactSpace A] [SecondCountableTopology A] : PolishSpace (PontryaginDual A) :=
  inferInstanceAs (PolishSpace (A →ₜ* Circle))

/-- The unit circle is the Pontryagin dual of `ℤ`: the point `z` corresponds to the character
`n ↦ zⁿ`, and a character corresponds to its value at `1`. -/
def circleEquivPontryaginDualInt : Circle ≃ₜ* PontryaginDual (Multiplicative ℤ) where
  toFun z := (⟨zpowersHom Circle z, continuous_of_discreteTopology⟩ : Multiplicative ℤ →ₜ* Circle)
  invFun χ := χ (Multiplicative.ofAdd 1)
  left_inv z := zpow_one z
  right_inv χ := PontryaginDual.ext fun n ↦
    DFunLike.congr_fun ((zpowersHom Circle).apply_symm_apply χ.toMonoidHom) n
  map_mul' z w := PontryaginDual.ext fun n ↦ mul_zpow z w n.toAdd
  continuous_toFun := ContinuousMonoidHom.continuous_of_continuous_uncurry _ <|
    continuous_prod_of_discrete_right.mpr fun n ↦ continuous_zpow n.toAdd
  continuous_invFun :=
    continuous_eval_const (F := Multiplicative ℤ →ₜ* Circle) (Multiplicative.ofAdd 1)

/-- The character attached to `z` sends `n` to `zⁿ`. -/
@[simp]
theorem circleEquivPontryaginDualInt_apply_apply (z : Circle) (n : Multiplicative ℤ) :
    circleEquivPontryaginDualInt z n = z ^ n.toAdd :=
  (rfl)

/-- The point of the circle attached to a character of `ℤ` is its value at `1`. -/
@[simp]
theorem circleEquivPontryaginDualInt_symm_apply (χ : PontryaginDual (Multiplicative ℤ)) :
    circleEquivPontryaginDualInt.symm χ = χ (Multiplicative.ofAdd 1) :=
  (rfl)

/-- The character of `ι → ℤ` attached to a tuple `z : ι → Circle`. -/
private def piCircleToDual {ι : Type*} [Fintype ι] [TopologicalSpace (ι → ℤ)]
    [DiscreteTopology (ι → ℤ)] (z : ι → Circle) :
    PontryaginDual (Multiplicative (ι → ℤ)) where
  toFun m := ∏ i, z i ^ m.toAdd i
  map_one' := by simp
  map_mul' m n := by simp [zpow_add, Finset.prod_mul_distrib]
  continuous_toFun := continuous_of_discreteTopology

@[simp]
private theorem piCircleToDual_apply {ι : Type*} [Fintype ι] [TopologicalSpace (ι → ℤ)]
    [DiscreteTopology (ι → ℤ)] (z : ι → Circle) (m : Multiplicative (ι → ℤ)) :
    piCircleToDual z m = ∏ i, z i ^ m.toAdd i :=
  rfl

/-- A finite product of unit circles is the Pontryagin dual of the discrete lattice `ι → ℤ`:
the tuple `z` corresponds to the character `m ↦ ∏ i, z i ^ m i`, and a character corresponds to
its values on the standard basis vectors. -/
def piCircleEquivPontryaginDualPiInt {ι : Type*} [Fintype ι] [TopologicalSpace (ι → ℤ)]
    [DiscreteTopology (ι → ℤ)] :
    (ι → Circle) ≃ₜ* PontryaginDual (Multiplicative (ι → ℤ)) where
  toFun := piCircleToDual
  invFun χ i :=
    letI := Classical.decEq ι
    χ (Multiplicative.ofAdd (Pi.single i 1))
  left_inv z := by
    classical
    funext i
    dsimp only
    rw [piCircleToDual_apply, toAdd_ofAdd, Finset.prod_eq_single i]
    · simp
    · intro j _ hji
      simp [Pi.single_eq_of_ne hji]
    · intro hi
      exact (hi (Finset.mem_univ i)).elim
  right_inv χ := by
    classical
    refine PontryaginDual.ext fun m ↦ ?_
    have hm : m = ∏ i, Multiplicative.ofAdd (Pi.single i (1 : ℤ)) ^ m.toAdd i := by
      apply Multiplicative.toAdd.injective
      ext j
      simp [Pi.single_apply]
    rw [piCircleToDual_apply]
    conv_rhs => rw [hm, map_prod]
    exact Finset.prod_congr rfl fun i _ ↦ (map_zpow χ _ _).symm
  map_mul' z w := PontryaginDual.ext fun m ↦ by
    simp [mul_zpow, Finset.prod_mul_distrib]
  continuous_toFun := ContinuousMonoidHom.continuous_of_continuous_uncurry _ <|
    continuous_prod_of_discrete_right.mpr fun m ↦
      continuous_finsetProd _ fun i _ ↦ (continuous_apply i).zpow (m.toAdd i)
  continuous_invFun := by
    classical
    exact continuous_pi fun i ↦ continuous_eval_const
      (F := Multiplicative (ι → ℤ) →ₜ* Circle) (Multiplicative.ofAdd (Pi.single i 1))

/-- The character attached to `z : ι → Circle` sends `m` to `∏ i, z i ^ m i`. -/
@[simp]
theorem piCircleEquivPontryaginDualPiInt_apply_apply {ι : Type*} [Fintype ι]
    [TopologicalSpace (ι → ℤ)] [DiscreteTopology (ι → ℤ)]
    (z : ι → Circle) (m : Multiplicative (ι → ℤ)) :
    piCircleEquivPontryaginDualPiInt z m = ∏ i, z i ^ m.toAdd i :=
  (rfl)

/-- The `i`-th coordinate of the point attached to a character of `ι → ℤ` is its value at the
`i`-th basis vector. -/
@[simp]
theorem piCircleEquivPontryaginDualPiInt_symm_apply {ι : Type*} [Fintype ι] [DecidableEq ι]
    [TopologicalSpace (ι → ℤ)] [DiscreteTopology (ι → ℤ)]
    (χ : PontryaginDual (Multiplicative (ι → ℤ))) (i : ι) :
    piCircleEquivPontryaginDualPiInt.symm χ i = χ (Multiplicative.ofAdd (Pi.single i 1)) := by
  have h := DFunLike.congr_fun (piCircleEquivPontryaginDualPiInt.apply_symm_apply χ)
    (Multiplicative.ofAdd (Pi.single i 1))
  rw [piCircleEquivPontryaginDualPiInt_apply_apply, toAdd_ofAdd, Finset.prod_eq_single i] at h
  · simpa using h
  · intro j _ hji
    simp [Pi.single_eq_of_ne hji]
  · intro hi
    exact (hi (Finset.mem_univ i)).elim

end TauCeti
