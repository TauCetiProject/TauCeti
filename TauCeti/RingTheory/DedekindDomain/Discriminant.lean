/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.DedekindDomain.Different
public import Mathlib.RingTheory.Ideal.Norm.RelNorm

/-!
# Relative discriminant ideals

For a finite torsion-free extension `A → B` of Dedekind domains, the relative discriminant is the
ideal of `A` obtained by taking the relative norm of Mathlib's different ideal of `B`. This file
introduces that carrier, together with the two defining identities that are valid without a
separability assumption. The later arithmetic theory uses `relDiscr` rather than expanding this
relative norm of the different at each use site.
-/

public section

namespace TauCeti

variable {A B : Type*} [CommRing A] [IsDedekindDomain A]
  [CommRing B] [IsDedekindDomain B] [Algebra A B] [Module.Finite A B]
  [Module.IsTorsionFree A B]

/-- The relative discriminant ideal of the finite torsion-free extension `A → B`. -/
noncomputable def relDiscr (A B : Type*) [CommRing A] [IsDedekindDomain A]
    [CommRing B] [IsDedekindDomain B] [Algebra A B] [Module.Finite A B]
    [Module.IsTorsionFree A B] : Ideal A :=
  Ideal.relNorm A (differentIdeal A B)

/-- The relative discriminant is zero exactly when the different is zero. -/
@[simp]
theorem relDiscr_eq_bot_iff : relDiscr A B = ⊥ ↔ differentIdeal A B = ⊥ := by
  rw [relDiscr, Ideal.relNorm_eq_bot_iff]

/-- The relative discriminant of the identity extension is the unit ideal. -/
@[simp]
theorem relDiscr_self : relDiscr A A = ⊤ := by
  let _ : Algebra (FractionRing A) (FractionRing A) :=
    FractionRing.liftAlgebra A (FractionRing A)
  have hdual :
      Submodule.traceDual A (FractionRing A) (1 : Submodule A (FractionRing A)) = 1 := by
    apply le_antisymm
    · intro x hx
      have hx' := (Submodule.mem_traceDual_iff_isIntegral (A := A)
        (K := FractionRing A) (B := A) (L := FractionRing A)).mp hx 1 (by simp)
      have hmap : algebraMap (FractionRing A) (FractionRing A) x = x := by
        rw [FractionRing.algebraMap_liftAlgebra]
        exact IsLocalization.lift_id x
      have hfin : @Module.finrank (FractionRing A) (FractionRing A)
          _ _ (Algebra.toModule : Module (FractionRing A) (FractionRing A)) = 1 := by
        apply (Algebra.finrank_eq_one_iff_bijective_algebraMap).2
        refine ⟨FaithfulSMul.algebraMap_injective _ _, ?_⟩
        intro y
        exact ⟨y, by
          rw [FractionRing.algebraMap_liftAlgebra]
          exact IsLocalization.lift_id y⟩
      have htrace : Algebra.trace (FractionRing A) (FractionRing A) x = x := by
        rw [← hmap, Algebra.trace_algebraMap, hfin]
        rw [hmap]
        simp
      rw [Submodule.mem_one]
      exact IsIntegrallyClosed.isIntegral_iff.mp
        (by simpa [Algebra.traceForm_apply, htrace] using hx')
    · exact Submodule.one_le_traceDual_one
  have hdiv :
      (1 / (1 : Submodule A (FractionRing A))) = (1 : Submodule A (FractionRing A)) := by
    ext x
    rw [Submodule.mem_div_iff_forall_mul_mem]
    constructor
    · intro h
      simpa using h 1 (by simp)
    · intro hx y hy
      rw [Submodule.mem_one] at hx hy ⊢
      obtain ⟨a, rfl⟩ := hx
      obtain ⟨b, rfl⟩ := hy
      exact ⟨a * b, by simp [map_mul]⟩
  have hdifferent : differentIdeal A A = ⊤ := by
    rw [differentIdeal]
    -- The quotient in `differentIdeal` fixes the ambient submodule, so expose it
    -- before rewriting by the identity-extension trace-dual calculation.
    change Submodule.comap (Algebra.linearMap A (FractionRing A))
      (1 / (Submodule.traceDual A (FractionRing A) 1)) = ⊤
    rw [hdual, hdiv]
    ext x
    simp [Submodule.mem_one]
  simp [relDiscr, hdifferent]

end TauCeti

end
