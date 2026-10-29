/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.QuadraticForm.OrthogonalGroup.CompactOpen
public import TauCeti.NumberTheory.QuadraticForm.OrthogonalGroup.Integral.CompactSubgroup
import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalBasis
import TauCeti.NumberTheory.Padics.RatCast

/-!
# Eventual integrality of compatible orthogonal reference families

For a nondegenerate rational quadratic space, any compatible compact-open reference family is
contained in the integral family of a rational basis at almost every prime. The family contains
the finitely many coordinate reflections of a rational orthogonal basis at almost every prime.
Outside the prime two and the primes at which a basis value is not a unit, compactness then
forces integrality. Changing rational basis changes the integral subgroup at only finitely many
primes.

This supplies the integrality bound used to isolate rational diagonal points in the full adeles.

## References

* O. T. O'Meara, *Introduction to Quadratic Forms* (1963), §43 and §101.
-/

public section

namespace TauCeti.QuadraticMap.OrthogonalCompactOpens

open Module Filter _root_.QuadraticMap
open scoped TensorProduct

variable {V : Type*} [AddCommGroup V] [Module ℚ V] [FiniteDimensional ℚ V]
  {Q : QuadraticForm ℚ V} (U : OrthogonalCompactOpens Q)

/-- Every compatible compact-open orthogonal reference family for a nondegenerate rational form
is eventually contained in the integral orthogonal family of any rational basis. -/
theorem eventually_orthogonal_le_integralOrthogonalSubgroup (hQ : Q.Nondegenerate)
    {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Basis ι ℚ V) :
    ∀ᶠ p : Nat.Primes in cofinite,
      U.orthogonal p ≤ integralOrthogonalSubgroup (Q.baseChange ℚ_[p]) (b.baseChange ℚ_[p]) := by
  obtain ⟨c, hc, hc0⟩ := hQ.exists_orthogonal_basis
  let (i : Fin (finrank ℚ V)) : Invertible (Q (c i)) := invertibleOfNonzero (hc0 i)
  have hodd : ∀ᶠ p : Nat.Primes in cofinite, (p : ℕ) ≠ 2 :=
    (eventually_cofinite_ne (⟨2, Nat.prime_two⟩ : Nat.Primes)).mono
      fun _ hp h ↦ hp (Subtype.ext h)
  filter_upwards [eventually_integralOrthogonalSubgroup_baseChange_eq Q b c, hodd,
    eventually_all.mpr fun i ↦ Padic.eventually_norm_rat_eq_one (hc0 i),
    eventually_all.mpr fun i ↦ U.eventually_orthogonal (reflectionOrthogonal Q (c i))]
    with p hbc hp hnorm hrefl
  rw [hbc]
  have hcu (i : Fin (finrank ℚ V)) : ‖Q.baseChange ℚ_[p] (c.baseChange ℚ_[p] i)‖ = 1 := by
    rw [Basis.baseChange_apply, QuadraticForm.baseChange_tmul, mul_one, Rat.smul_one_eq_cast]
    exact hnorm i
  refine le_integralOrthogonalSubgroup_of_isCompact_of_reflection_mem _ _ hp
    (fun i j hij ↦ ?_) hcu (U.orthogonal p) (U.isCompact_orthogonal p) (fun i hi ↦ ?_)
  · refine isOrtho_def.mpr ?_
    rw [Basis.baseChange_apply, Basis.baseChange_apply, ← TensorProduct.tmul_add,
      QuadraticForm.baseChange_tmul, QuadraticForm.baseChange_tmul, QuadraticForm.baseChange_tmul,
      isOrtho_def.mp (hc i j hij), add_smul]
  · have heq : reflectionOrthogonal (Q.baseChange ℚ_[p]) (c.baseChange ℚ_[p] i) =
        orthogonalGroupBaseChange (A := ℚ_[p]) Q (reflectionOrthogonal Q (c i)) := by
      rw [orthogonalGroupBaseChange_reflectionOrthogonal]
      -- The vector equation also transports the dependent inverse-of-norm instance.
      congr 1
      · exact Basis.baseChange_apply ℚ_[p] c i
      · exact Subsingleton.helim
          (congrArg (fun v ↦ Invertible (Q.baseChange ℚ_[p] v))
            (Basis.baseChange_apply ℚ_[p] c i)) _ _
    rw [heq]
    exact hrefl i

end TauCeti.QuadraticMap.OrthogonalCompactOpens
