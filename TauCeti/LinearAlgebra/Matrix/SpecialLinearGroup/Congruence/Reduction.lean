/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
public import Mathlib.RingTheory.DedekindDomain.Basic
public import TauCeti.RingTheory.StableRange
import Mathlib.RingTheory.KrullDimension.Zero
import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Stability.SpecialLinear
import TauCeti.RingTheory.StableRange.ZeroDimensional

/-!
# Surjective reduction of special linear groups

* `RingHom.specialLinearGroup_map_surjective_of_hasStableRangeLE_one` lifts determinant-one
  matrices along a surjective ring homomorphism into a ring of Bass stable range at most one.
  It uses Tau Ceti's elementary generation in stable range one and lifting of elementary matrices.
* `Ideal.specialLinearGroup_map_quotientMk_surjective` gives surjective congruence reduction
  when every nonzero prime ideal is maximal, including over Dedekind domains. It uses stable
  range one of the quotient by a nonzero ideal, which has Krull dimension at most zero.

## References

* H. Bass, *K-theory and stable algebra*, Publ. Math. IHÉS 22 (1964), §4.
-/

public section

open Matrix Matrix.SpecialLinearGroup TauCeti

variable {n : Type*} [Fintype n] [DecidableEq n] {R S : Type*} [CommRing R] [CommRing S]

/-- A surjective ring homomorphism into a commutative ring of Bass stable range at most one
induces a surjection on special linear groups in every finite matrix size. -/
theorem RingHom.specialLinearGroup_map_surjective_of_hasStableRangeLE_one
    {f : R →+* S} (hf : Function.Surjective f) (hS : HasStableRangeLE S 1) :
    Function.Surjective (SpecialLinearGroup.map (n := n) f) := by
  intro A
  have hA : toGL A ∈ elementarySubgroup n S := by
    rw [elementarySubgroup_eq_ker_det_of_hasStableRangeLE_one hS, MonoidHom.mem_ker]
    exact coeToGL_det A
  obtain ⟨B, hB, hmap⟩ := f.exists_mem_elementarySubgroup_unitsMap_mapMatrix_eq hf hA
  have hdet : B ∈ (GeneralLinearGroup.det : GeneralLinearGroup n R →* Rˣ).ker :=
    elementarySubgroup_le_ker_det hB
  rw [← range_toGL_eq_ker_det] at hdet
  obtain ⟨C, rfl⟩ := hdet
  refine ⟨C, Subtype.ext ?_⟩
  have hmat := congrArg Units.val hmap
  simpa only [MonoidHom.coe_ofClass, Units.coe_map, RingHom.toMonoidHom_eq_coe,
    coe_GL_coe_matrix, map_apply_coe, RingHom.mapMatrix_apply] using hmat

/-- Reduction of determinant-one matrices modulo any ideal of a commutative ring in which
every nonzero prime ideal is maximal is surjective. This applies to Dedekind domains. -/
theorem Ideal.specialLinearGroup_map_quotientMk_surjective [Ring.DimensionLEOne R] (I : Ideal R) :
    Function.Surjective (SpecialLinearGroup.map (n := n) (Ideal.Quotient.mk I)) := by
  by_cases hI : I = ⊥
  · subst I
    have h : Ideal.Quotient.mk (⊥ : Ideal R) =
        (↑(RingEquiv.quotientBot R).symm : R →+* R ⧸ (⊥ : Ideal R)) := by
      exact RingHom.ext fun x ↦ (RingEquiv.quotientBot_symm_mk x).symm
    rw [h, ← toMonoidHom_mapEquiv]
    exact (mapEquiv n (RingEquiv.quotientBot R).symm).surjective
  · have : Ring.KrullDimLE 0 (R ⧸ I) :=
      Ideal.krullDimLE_zero_quotient_iff_forall_minimalPrimes_isMaximal.mpr fun P hP ↦
        hP.isPrime.isMaximal (ne_bot_of_le_ne_bot hI hP.le)
    exact RingHom.specialLinearGroup_map_surjective_of_hasStableRangeLE_one
      Ideal.Quotient.mk_surjective (hasStableRangeLE_one_of_krullDimLE_zero _)
