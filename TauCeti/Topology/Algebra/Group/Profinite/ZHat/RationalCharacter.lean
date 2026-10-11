/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AddCircle
public import TauCeti.RepresentationTheory.Homological.ContCohomology.CohomologyComparison
public import TauCeti.Topology.Algebra.Group.Profinite.ZHat.Basic

/-!
# Rational characters of the profinite integers

Evaluation at the canonical generator identifies continuous characters of `zHat` with the
rational circle `ℚ/ℤ`, given the discrete topology. Every rational-circle element has finite
order, so its character factors through a finite cyclic quotient of `zHat`. In particular, the
first continuous cohomology of `zHat` with trivial discrete `ℚ/ℤ` coefficients is `ℚ/ℤ`.

This is the degree-one term in the long exact sequence of `0 → ℤ → ℚ → ℚ/ℤ → 0` used to
calculate `H²(zHat, ℤ)`.

## References

* J.-P. Serre, *Local Fields*, Chapter XIII, §1, Propositions 1–2.
-/

public noncomputable section

namespace TauCeti.zHat

universe u

/-- The rational circle with the discrete topology, as a continuous cohomology coefficient. -/
abbrev DiscreteRatCircle := Additive (Multiplicative (AddCircle (1 : ℚ)))

instance : TopologicalSpace DiscreteRatCircle := ⊥
instance : DiscreteTopology DiscreteRatCircle := ⟨rfl⟩
instance : IsTopologicalAddGroup DiscreteRatCircle where
  continuous_add := continuous_of_discreteTopology
  continuous_neg := continuous_of_discreteTopology

/-- The trivial action of the profinite integers on the discrete rational circle. -/
instance : DistribMulAction zHat.{u} DiscreteRatCircle where
  smul _ x := x
  one_smul _ := rfl
  mul_smul _ _ _ := rfl
  smul_zero _ := rfl
  smul_add _ _ _ := rfl

instance : ContinuousSMul zHat.{u} DiscreteRatCircle := ⟨continuous_snd⟩

/-- Forget the discrete topology on the rational circle. -/
def discreteRatCircleEquiv : DiscreteRatCircle ≃+ AddCircle (1 : ℚ) :=
  { toFun := fun x ↦ Multiplicative.toAdd (Additive.toMul x)
    invFun := fun x ↦ Additive.ofMul (Multiplicative.ofAdd x)
    left_inv := fun _ ↦ rfl
    right_inv := fun _ ↦ rfl
    map_add' := fun _ _ ↦ rfl }

private def ratCharacterOfTorsion (n : ℕ) [NeZero n] (a : ZMod n) :
    zHat.{u} →ₜ* Multiplicative DiscreteRatCircle :=
  { toFun := fun g ↦ Multiplicative.ofAdd
      (discreteRatCircleEquiv.symm (ZMod.toRatAddCircle n (Multiplicative.toAdd
        ((lift (Multiplicative.ofAdd a) : zHat.{u} →ₜ* Multiplicative (ZMod n)) g))))
    map_one' := by simp
    map_mul' g h := by
      simp only [map_mul, toAdd_mul, map_add]
      exact ofAdd_add _ _
    continuous_toFun := by
      exact (continuous_of_discreteTopology (f := fun x : Multiplicative (ZMod n) ↦
        Multiplicative.ofAdd (discreteRatCircleEquiv.symm (ZMod.toRatAddCircle n x.toAdd)))).comp
        (lift (Multiplicative.ofAdd a)).continuous }

private theorem ratCharacterOfTorsion_gen (n : ℕ) [NeZero n] (a : ZMod n) :
    (ratCharacterOfTorsion n a) gen =
      Multiplicative.ofAdd (discreteRatCircleEquiv.symm (ZMod.toRatAddCircle n a)) := by
  simp [ratCharacterOfTorsion]

/-- Every element of the discrete rational circle is the value at `zHat.gen` of a continuous
character of `zHat`. -/
theorem exists_ratCharacter_gen (a : DiscreteRatCircle) :
    ∃ χ : zHat.{u} →ₜ* Multiplicative DiscreteRatCircle,
      χ gen = Multiplicative.ofAdd a := by
  obtain ⟨n, hn, ha⟩ := AddCircle.exists_mem_torsionBy_rat (p := (1 : ℚ))
    (discreteRatCircleEquiv a)
  let : NeZero n := ⟨Nat.ne_of_gt hn⟩
  obtain ⟨b, hb⟩ := ZMod.exists_toRatAddCircle_eq_of_nsmul_eq_zero n
    (AddSubgroup.torsionBy.nsmul_iff.mp ha)
  refine ⟨ratCharacterOfTorsion n b, ?_⟩
  rw [ratCharacterOfTorsion_gen, hb, discreteRatCircleEquiv.symm_apply_apply]

/-- Evaluation at the generator identifies continuous rational-circle characters of `zHat`
with `ℚ/ℤ`. The target carries the discrete topology. -/
def ratCharacterEquiv :
    Additive (zHat.{u} →ₜ* Multiplicative DiscreteRatCircle) ≃+
      AddCircle (1 : ℚ) := by
  let f : Additive (zHat.{u} →ₜ* Multiplicative DiscreteRatCircle) →+
      AddCircle (1 : ℚ) :=
    { toFun := fun χ ↦ discreteRatCircleEquiv
        (Multiplicative.toAdd (Additive.toMul χ gen))
      map_zero' := by simp
      map_add' := by intros; simp }
  exact AddEquiv.ofBijective f ⟨by
      intro χ ψ h
      apply Additive.toMul.injective
      apply hom_ext
      exact Multiplicative.toAdd.injective (discreteRatCircleEquiv.injective h),
     by
      intro a
      obtain ⟨χ, hχ⟩ := exists_ratCharacter_gen (discreteRatCircleEquiv.symm a)
      refine ⟨Additive.ofMul χ, ?_⟩
      change discreteRatCircleEquiv (Multiplicative.toAdd (χ gen)) = a
      rw [hχ, toAdd_ofAdd]
      exact discreteRatCircleEquiv.apply_symm_apply a⟩

/-- A continuous rational-circle character is evaluated at the canonical generator. -/
@[simp] theorem ratCharacterEquiv_apply
    (χ : Additive (zHat.{u} →ₜ* Multiplicative DiscreteRatCircle)) :
    ratCharacterEquiv χ = discreteRatCircleEquiv (Multiplicative.toAdd (Additive.toMul χ gen)) :=
  by unfold ratCharacterEquiv; rfl

/-- The unique character taking the value `a` at the generator is the inverse of evaluation. -/
@[simp] theorem ratCharacterEquiv_symm_apply (a : AddCircle (1 : ℚ)) :
    discreteRatCircleEquiv (Multiplicative.toAdd
      (Additive.toMul (ratCharacterEquiv.{u}.symm a) gen)) = a := by
  rw [← ratCharacterEquiv_apply]
  exact ratCharacterEquiv.{u}.apply_symm_apply a

/-- First continuous cohomology of the profinite integers with trivial discrete `ℚ/ℤ`
coefficients is the rational circle, by evaluating the associated character at `gen`. -/
def h1EquivRatCircle :
    continuousCohomology 1
      (ofDiscreteModule ℤ zHat.{0} DiscreteRatCircle) ≃+ AddCircle (1 : ℚ) :=
  ((ContCohomology.explicitH1AddEquivContinuousCohomology zHat.{0}
    DiscreteRatCircle).symm.trans
    (ContCohomology.H1EquivOfSmulEqSelf (fun _ _ ↦ rfl))).trans ratCharacterEquiv.{0}

/-- On a continuous one-cocycle, the cohomology equivalence returns its value at `gen`. -/
@[simp] theorem h1EquivRatCircle_apply_mk (f : ContCohomology.Z1 zHat.{0} DiscreteRatCircle) :
    h1EquivRatCircle
      (ContCohomology.explicitH1AddEquivContinuousCohomology zHat.{0} DiscreteRatCircle
        (f : ContCohomology.H1 zHat.{0} DiscreteRatCircle)) =
      discreteRatCircleEquiv ((f : zHat.{0} → DiscreteRatCircle) gen) := by
  simp [h1EquivRatCircle, ContCohomology.H1EquivOfSmulEqSelf_mk,
    ContCohomology.Z1EquivOfSmulEqSelf_apply]

/-- In particular, discrete `ℚ/ℤ` has nonzero first continuous cohomology over `zHat`. -/
theorem nontrivial_h1RatCircle :
    Nontrivial (continuousCohomology 1
      (ofDiscreteModule ℤ zHat.{0} DiscreteRatCircle)) := by
  have h : (ZMod.toRatAddCircle 2 (1 : ZMod 2)) ≠ 0 := by
    intro heq
    exact one_ne_zero ((ZMod.toRatAddCircle_eq_zero 2).mp heq)
  exact @Equiv.nontrivial _ _ h1EquivRatCircle.toEquiv
    (nontrivial_of_ne 0 (ZMod.toRatAddCircle 2 1) h.symm)

end TauCeti.zHat
