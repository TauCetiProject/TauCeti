/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
public import TauCeti.NumberTheory.ModularForms.AdelicComponentGroup
public import TauCeti.RingTheory.DedekindDomain.FiniteAdeleRing.CongruenceLevel

/-!
# The integral matrices of the `GL₂` component groups

For a compact subgroup `U` of `GL₂(𝔸_f)` and `g ∈ GL₂(𝔸_f)`, the congruence group
`Γ_{g,U} = GL₂(ℚ)^+ ∩ gUg⁻¹` of the component through `g`
(`TauCeti.AdelicExamples.GL2.componentGroup`) meets `SL₂(ℤ)` in a subgroup of finite index of
`Γ_{g,U}` (`TauCeti.AdelicExamples.GL2.relIndex_range_mapGL_componentGroup_ne_zero`).

The argument is topological. The integral points `GL₂(Ô)` form an open subgroup of `GL₂(𝔸_f)`
(`IsDedekindDomain.FiniteAdeleRing.isOpenEmbedding_integralGL`), so they meet the compact group
`gUg⁻¹` in an open subgroup, of finite index in it. Pulling back along the diagonal embedding,
the elements of `Γ_{g,U}` with integral entries have finite index in `Γ_{g,U}`. A rational matrix
whose diagonal image is integral has integral entries, since the integral finite adeles meet `ℚ`
in `ℤ` (`IsDedekindDomain.FiniteAdeleRing.algebraMap_mem_integralAdeles_iff`), and the elements of
`Γ_{g,U}` have determinant `1`, so these are the elements of `SL₂(ℤ)`.

## Main results

* `TauCeti.AdelicExamples.GL2.mem_range_mapGL_of_mem_componentGroup`: an element of `Γ_{g,U}` whose
  diagonal image is integral comes from `SL₂(ℤ)`.
* `TauCeti.AdelicExamples.GL2.relIndex_range_mapGL_componentGroup_ne_zero`: `Γ_{g,U} ∩ SL₂(ℤ)` has
  finite index in `Γ_{g,U}`.

## References

* J. S. Milne, *Introduction to Shimura varieties*, revision of 16 September 2017, Lemma 5.13
  with the remarks after it, pp. 57-58.
-/

public section

open IsDedekindDomain IsDedekindDomain.FiniteAdeleRing Matrix

namespace TauCeti

namespace AdelicExamples.GL2

variable {U : Subgroup (GL (Fin 2) (FiniteAdeleRing ℤ ℚ))} {g : GL (Fin 2) (FiniteAdeleRing ℤ ℚ)}

/-- An element of `Γ_{g,U}`, `U` compact, whose diagonal image in `GL₂(𝔸_f)` lies in `GL₂(Ô)`
comes from `SL₂(ℤ)`. -/
theorem mem_range_mapGL_of_mem_componentGroup
    (hU : IsCompact (U : Set (GL (Fin 2) (FiniteAdeleRing ℤ ℚ)))) {γ : GL (Fin 2) ℚ}
    (hγ : γ ∈ componentGroup U g)
    (hint : GeneralLinearGroup.map (algebraMap ℚ (FiniteAdeleRing ℤ ℚ)) γ ∈
      (integralGL ℚ 2 (R := ℤ)).range) :
    γ ∈ (SpecialLinearGroup.mapGL (n := Fin 2) (R := ℤ) ℚ).range := by
  have hent (i j : Fin 2) : (γ : Matrix (Fin 2) (Fin 2) ℚ) i j ∈ (algebraMap ℤ ℚ).range := by
    rw [← algebraMap_mem_integralAdeles_iff (R := ℤ)]
    simpa using (mem_range_integralGL_iff.mp hint).1 i j
  choose m hm using hent
  have hmat : (Matrix.of m).map (Int.castRingHom ℚ) = (γ : Matrix (Fin 2) (Fin 2) ℚ) := by
    ext i j
    simpa using hm i j
  have hdet : (Matrix.of m).det = 1 := by
    have h := congrArg Units.val (det_eq_one_of_mem_componentGroup hU hγ)
    rw [GeneralLinearGroup.val_det_apply, ← hmat, ← RingHom.mapMatrix_apply, ← RingHom.map_det,
      Units.val_one, eq_intCast, Int.cast_eq_one] at h
    exact h
  refine ⟨(⟨Matrix.of m, hdet⟩ : SpecialLinearGroup (Fin 2) ℤ), ?_⟩
  ext i j
  exact hm i j

/-- **`Γ_{g,U} ∩ SL₂(ℤ)` has finite index in `Γ_{g,U}`** for compact `U`. -/
theorem relIndex_range_mapGL_componentGroup_ne_zero
    (hU : IsCompact (U : Set (GL (Fin 2) (FiniteAdeleRing ℤ ℚ)))) :
    (SpecialLinearGroup.mapGL (n := Fin 2) (R := ℤ) ℚ).range.relIndex (componentGroup U g) ≠ 0 := by
  set φ := GeneralLinearGroup.map (n := Fin 2) (algebraMap ℚ (FiniteAdeleRing ℤ ℚ))
  set V := U.map (MulAut.conj g).toMonoidHom
  set O := (integralGL ℚ 2 (R := ℤ)).range
  -- `GL₂(Ô)` has finite index in the compact group `gUg⁻¹`, since it is open.
  have hV : IsCompact (V : Set (GL (Fin 2) (FiniteAdeleRing ℤ ℚ))) := by
    have hconj : ⇑((MulAut.conj g).toMonoidHom) = fun x ↦ g * x * g⁻¹ :=
      funext fun x ↦ MulAut.conj_apply g x
    rw [Subgroup.coe_map, hconj]
    exact hU.image (by fun_prop)
  have hO : IsOpen (O : Set (GL (Fin 2) (FiniteAdeleRing ℤ ℚ))) :=
    (isOpenEmbedding_integralGL ℚ 2).isOpen_range
  have h1 : O.relIndex V ≠ 0 := by
    have : CompactSpace V := isCompact_iff_compactSpace.mp hV
    have := Subgroup.quotient_finite_of_isOpen (O.subgroupOf V) (Subgroup.subgroupOf_isOpen V O hO)
    exact Subgroup.index_ne_zero_of_finite
  -- The diagonal image of `Γ_{g,U}` lies in `gUg⁻¹`.
  have h2 : (componentGroup U g).map φ ≤ V := by
    rintro _ ⟨γ, hγ, rfl⟩
    rw [Subgroup.mem_map_equiv, MulAut.conj_symm_apply]
    exact (mem_componentGroup_iff.mp hγ).2
  have h3 : (O.comap φ).relIndex (componentGroup U g) ≠ 0 := by
    rw [Subgroup.relIndex_comap]
    exact mt (Subgroup.relIndex_eq_zero_of_le_right h2) h1
  rw [← Subgroup.inf_relIndex_right] at h3
  refine fun h ↦ h3 (Nat.eq_zero_of_zero_dvd ?_)
  rw [← h]
  exact Subgroup.relIndex_dvd_of_le_left _ fun γ hγ ↦
    mem_range_mapGL_of_mem_componentGroup hU hγ.2 hγ.1

end AdelicExamples.GL2

end TauCeti
