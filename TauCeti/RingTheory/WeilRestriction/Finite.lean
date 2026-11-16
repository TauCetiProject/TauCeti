/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.WeilRestriction.Basic
public import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic

/-!
# Integrality and finiteness of Weil restriction along a split finite algebra

If `B` is a finite product of copies of `A`, Weil restriction along `B/A` takes a finite
`B`-algebra to a finite `A`-algebra, and an integral `B`-algebra to an integral
`A`-algebra. In particular, the scheme of maps from
a finite constant scheme to a finite affine scheme is finite. This gives finiteness of the
schemes of homomorphisms from finite constant monoid schemes to finite
affine monoid schemes, and of Katz–Mazur generator schemes for finite free affine monoid schemes.

The splitting hypothesis matters: restriction along a nonreduced finite free algebra need
not preserve finiteness. Here the coordinate evaluations are algebra maps, so evaluations
of the universal point are integral. Every universal coefficient is a linear combination
of these evaluations.

## References

* N. M. Katz, B. Mazur, *Arithmetic Moduli of Elliptic Curves*, §§1.6 and 1.10.
-/

open scoped TensorProduct

namespace TauCeti.Algebra.WeilRestriction

public noncomputable section

variable {A B C : Type*} [CommRing A] [CommRing B] [CommRing C]
  [Algebra A B] [Algebra B C] [Module.Finite A B] [Module.Projective A B]

/-- A coefficient of the universal point at an integral element is integral when the
coefficient algebra is split. -/
theorem isIntegral_universalCoefficient_of_split {ι : Type*} (e : B ≃ₐ[A] (ι → A))
    (φ : Module.Dual A B) {c : C} (hc : IsIntegral B c) :
    IsIntegral A (universalCoefficient φ c) := by
  classical
  by_cases hA : Nontrivial A
  · let : Algebra A C := ((algebraMap B C).comp (algebraMap A B)).toAlgebra
    have : IsScalarTower A B C := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
    have hcA : IsIntegral A c := isIntegral_trans c hc
    -- Finite generation of a split algebra forces its index set to be finite.
    have : Finite ι := by
      have : Module.Finite A (ι → A) := Module.Finite.equiv e.toLinearEquiv
      exact (Pi.linearIndependent_single_one ι A).finite
    let := Fintype.ofFinite ι
    let W := WeilRestriction A B C
    let ev (i : ι) : B →ₐ[A] A := (Pi.evalAlgHom A (fun _ : ι ↦ A) i).comp e.toAlgHom
    let p (i : ι) : C →ₐ[A] W :=
      (Algebra.TensorProduct.lift ((Algebra.ofId A W).comp (ev i)) (AlgHom.id A W)
        (fun _ _ ↦ Commute.all _ _)).comp ((universalPoint A B C).restrictScalars A)
    have hφ (b : B) : ∑ i, φ (e.symm (Pi.single i 1)) * ev i b = φ b := by
      have hb : ∑ i, ev i b • e.symm (Pi.single i 1) = b := by
        apply e.injective
        ext i
        simp [ev, Pi.single_apply]
      simpa [map_sum, map_smul, mul_comm] using congrArg φ hb
    have hcoeff : universalCoefficient φ c = ∑ i, φ (e.symm (Pi.single i 1)) • p i c := by
      simp only [universalCoefficient_def, p, AlgHom.comp_apply, AlgHom.restrictScalars_apply]
      induction universalPoint A B C c using TensorProduct.inductionOn with
      | tmul b w =>
        simp only [TensorProduct.comm_tmul, LinearMap.tensorComponent_tmul]
        simpa [Algebra.smul_def, Finset.sum_mul, map_sum, map_mul, mul_assoc] using
          congrArg (fun a : A ↦ a • w) (hφ b).symm
      | add z w hz hw =>
        simp only [map_add, hz, hw, smul_add, Finset.sum_add_distrib]
    rw [hcoeff]
    exact IsIntegral.sum _ fun i _ ↦ (hcA.map (p i)).smul _
  · have := not_nontrivial_iff_subsingleton.mp hA
    have := Module.subsingleton A (WeilRestriction A B C)
    simpa only [Subsingleton.elim (universalCoefficient φ c) 0] using
      (isIntegral_zero : IsIntegral A (0 : WeilRestriction A B C))

/-- Weil restriction along a split finite algebra preserves integral algebras. -/
theorem isIntegral_of_split [Algebra.IsIntegral B C]
    {ι : Type*} (e : B ≃ₐ[A] (ι → A)) : Algebra.IsIntegral A (WeilRestriction A B C) := by
  have h : Algebra.adjoin A (Set.range fun p : Module.Dual A B × C ↦
      universalCoefficient p.1 p.2) ≤ integralClosure A (WeilRestriction A B C) := by
    apply Algebra.adjoin_le
    rintro _ ⟨⟨φ, c⟩, rfl⟩
    exact isIntegral_universalCoefficient_of_split e φ (Algebra.IsIntegral.isIntegral c)
  rw [adjoin_range_universalCoefficient] at h
  exact ⟨fun x ↦ h (by trivial)⟩

/-- Weil restriction along a split finite algebra preserves finite
algebras. No noetherianity assumption on the base is required. -/
theorem moduleFinite_of_split [Module.Finite B C]
    {ι : Type*} (e : B ≃ₐ[A] (ι → A)) : Module.Finite A (WeilRestriction A B C) := by
  have : Algebra.IsIntegral A (WeilRestriction A B C) := isIntegral_of_split e
  exact Algebra.IsIntegral.finite

end

end TauCeti.Algebra.WeilRestriction
