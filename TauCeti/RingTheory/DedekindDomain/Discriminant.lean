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

This implements Layer 4.1 of the [NumberFieldArithmetic roadmap]
(https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/NumberFieldArithmetic/README.md).
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

/-- The relative discriminant is the relative norm of the different ideal. -/
theorem relDiscr_def : relDiscr A B = Ideal.relNorm A (differentIdeal A B) := by
  rw [relDiscr]

/-- Membership in the relative discriminant is membership in the span of norms from the different.
-/
theorem mem_relDiscr_iff {x : A} :
    x ∈ relDiscr A B ↔
      x ∈ Ideal.span (Algebra.intNorm A B '' (differentIdeal A B : Set B) : Set A) := by
  rw [relDiscr_def, Ideal.relNorm_apply]

/-- The relative discriminant is zero exactly when the different is zero. -/
@[simp]
theorem relDiscr_eq_bot_iff : relDiscr A B = ⊥ ↔ differentIdeal A B = ⊥ := by
  rw [relDiscr_def, Ideal.relNorm_eq_bot_iff]

/-- The trace dual of the unit submodule is the unit submodule for the identity extension of a
Dedekind domain to its fraction field. -/
theorem traceDual_one_fractionRing_self :
    letI : Algebra (FractionRing A) (FractionRing A) :=
      FractionRing.liftAlgebra A (FractionRing A)
    Submodule.traceDual A (FractionRing A) (1 : Submodule A (FractionRing A)) = 1 := by
  let _ : Algebra (FractionRing A) (FractionRing A) :=
    FractionRing.liftAlgebra A (FractionRing A)
  apply le_antisymm
  · intro x hx
    have hx' := (@Submodule.mem_traceDual A (FractionRing A) (FractionRing A) A
      _ _ _ _ _ _ _ (FractionRing.liftAlgebra A (FractionRing A)) _ _ _).mp hx 1 (by simp)
    have htrace : Algebra.trace (FractionRing A) (FractionRing A) x = x := by
      have htrace' := @Algebra.trace_eq_of_equiv_equiv
        (FractionRing A) (FractionRing A) (FractionRing A) (FractionRing A)
        _ _ _ _ (Algebra.id (FractionRing A))
        (FractionRing.liftAlgebra A (FractionRing A)) (RingEquiv.refl _) (RingEquiv.refl _) ?_ x
      · simpa using htrace'.symm
      · ext y
        change algebraMap (FractionRing A) (FractionRing A) y = y
        rw [FractionRing.algebraMap_liftAlgebra]
        exact IsLocalization.lift_id y
    rw [Submodule.mem_one]
    exact (by simpa [Algebra.traceForm_apply, htrace] using hx')
  · exact @Submodule.one_le_traceDual_one A (FractionRing A) (FractionRing A) A
      _ _ _ _ _ _ _ (FractionRing.liftAlgebra A (FractionRing A)) _ _ _ _ _ _ _

/-- The quotient of the unit submodule by itself is the unit submodule. -/
theorem one_div_one_submodule :
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

/-- The relative discriminant of the identity extension is the unit ideal. -/
@[simp]
theorem relDiscr_self : relDiscr A A = ⊤ := by
  let _ : Algebra (FractionRing A) (FractionRing A) :=
    FractionRing.liftAlgebra A (FractionRing A)
  have hdifferent : differentIdeal A A = ⊤ := by
    rw [differentIdeal]
    -- The quotient in `differentIdeal` fixes the ambient submodule, so expose it
    -- before rewriting by the identity-extension trace-dual calculation.
    change Submodule.comap (Algebra.linearMap A (FractionRing A))
      (1 / (Submodule.traceDual A (FractionRing A) 1)) = ⊤
    rw [traceDual_one_fractionRing_self, one_div_one_submodule]
    ext x
    simp [Submodule.mem_one]
  simp [relDiscr_def, hdifferent]

end TauCeti

end
