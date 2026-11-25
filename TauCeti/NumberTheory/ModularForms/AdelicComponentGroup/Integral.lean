/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
public import TauCeti.NumberTheory.ModularForms.AdelicComponentGroup
public import TauCeti.RingTheory.DedekindDomain.FiniteAdeleRing.CongruenceLevel
import TauCeti.Topology.Algebra.Group.Subgroup

/-!
# The integral matrices of the `GL₂` component groups

For a compact subgroup `U` of `GL₂(𝔸_f)` and `g ∈ GL₂(𝔸_f)`, the congruence group
`Γ_{g,U} = GL₂(ℚ)^+ ∩ gUg⁻¹` of the component through `g`
(`TauCeti.AdelicExamples.GL2.componentGroup`) meets `SL₂(ℤ)` in a subgroup of finite index of
`Γ_{g,U}` (`TauCeti.AdelicExamples.GL2.relIndex_range_mapGL_componentGroup_ne_zero`).

The argument is topological. The integral points `GL₂(Ô)` form an open subgroup of `GL₂(𝔸_f)`
(`IsDedekindDomain.FiniteAdeleRing.isOpenEmbedding_integralGL`), so they meet the compact group
`gUg⁻¹` in an open subgroup, of finite index in it. Pulling back along the diagonal embedding,
the elements of `Γ_{g,U}` with integral entries have finite index in `Γ_{g,U}`. Over any Dedekind
domain `R` with fraction field `K`, a matrix in `GL_n(K)` of determinant `1` whose diagonal image
is integral comes from `SL_n(R)`, since the integral finite adeles meet `K` in `R`
(`IsDedekindDomain.FiniteAdeleRing.algebraMap_mem_integralAdeles_iff`). The elements of `Γ_{g,U}`
have determinant `1`, so those with integral entries are the elements of `SL₂(ℤ)`.

## Main results

* `IsDedekindDomain.FiniteAdeleRing.mem_range_mapGL_of_det_eq_one`: a matrix in `GL_n(K)` of
  determinant `1` whose diagonal image lies in `GL_n(Ô)` comes from `SL_n(R)`.
* `TauCeti.AdelicExamples.GL2.relIndex_range_mapGL_componentGroup_ne_zero`: `Γ_{g,U} ∩ SL₂(ℤ)` has
  finite index in `Γ_{g,U}`.

## References

* J. S. Milne, *Introduction to Shimura varieties*, revision of 16 September 2017, Lemma 5.13
  with the remarks after it, pp. 57-58.
-/

public section

open IsDedekindDomain IsDedekindDomain.FiniteAdeleRing Matrix

namespace IsDedekindDomain.FiniteAdeleRing

variable {R : Type*} [CommRing R] [IsDedekindDomain R]
  {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K] {n : ℕ}

/-- A matrix in `GL_n(K)` of determinant `1` whose diagonal image in `GL_n(𝔸_f)` lies in
`GL_n(Ô)` comes from `SL_n(R)`. -/
theorem mem_range_mapGL_of_det_eq_one {γ : GL (Fin n) K} (hdet : GeneralLinearGroup.det γ = 1)
    (hint : GeneralLinearGroup.map (algebraMap K (FiniteAdeleRing R K)) γ ∈
      (integralGL K n (R := R)).range) :
    γ ∈ (SpecialLinearGroup.mapGL (n := Fin n) (R := R) K).range := by
  have hent (i j : Fin n) : (γ : Matrix (Fin n) (Fin n) K) i j ∈ (algebraMap R K).range := by
    rw [← algebraMap_mem_integralAdeles_iff (R := R)]
    simpa using (mem_range_integralGL_iff.mp hint).1 i j
  choose m hm using hent
  have hmat : (Matrix.of m).map (algebraMap R K) = (γ : Matrix (Fin n) (Fin n) K) := by
    ext i j
    simpa using hm i j
  have hdet' : (Matrix.of m).det = 1 := by
    apply IsFractionRing.injective R K
    simpa [RingHom.map_det, hmat] using congrArg Units.val hdet
  exact ⟨⟨Matrix.of m, hdet'⟩, Units.ext ((SpecialLinearGroup.mapGL_coe_matrix _).trans hmat)⟩

end IsDedekindDomain.FiniteAdeleRing

namespace TauCeti

namespace AdelicExamples.GL2

variable {U : Subgroup (GL (Fin 2) (FiniteAdeleRing ℤ ℚ))} {g : GL (Fin 2) (FiniteAdeleRing ℤ ℚ)}

/-- **`Γ_{g,U} ∩ SL₂(ℤ)` has finite index in `Γ_{g,U}`** for compact `U`. -/
theorem relIndex_range_mapGL_componentGroup_ne_zero
    (hU : IsCompact (U : Set (GL (Fin 2) (FiniteAdeleRing ℤ ℚ)))) :
    (SpecialLinearGroup.mapGL (n := Fin 2) (R := ℤ) ℚ).range.relIndex (componentGroup U g) ≠ 0 := by
  set φ := GeneralLinearGroup.map (n := Fin 2) (algebraMap ℚ (FiniteAdeleRing ℤ ℚ))
  set V := U.map (MulAut.conj g).toMonoidHom
  set O := (integralGL ℚ 2 (R := ℤ)).range
  -- `GL₂(Ô)` has finite index in the compact group `gUg⁻¹`, since it is open.
  have hV : IsCompact (V : Set (GL (Fin 2) (FiniteAdeleRing ℤ ℚ))) :=
    Subgroup.isCompact_conj_smul g hU
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
  have h3 : (O.comap φ ⊓ componentGroup U g).relIndex (componentGroup U g) ≠ 0 := by
    rw [Subgroup.inf_relIndex_right, Subgroup.relIndex_comap]
    exact mt (Subgroup.relIndex_eq_zero_of_le_right h2) h1
  -- An element of `Γ_{g,U}` with integral diagonal image comes from `SL₂(ℤ)`.
  refine mt (Subgroup.relIndex_eq_zero_of_le_left ?_) h3
  rintro γ ⟨hint, hγ⟩
  exact mem_range_mapGL_of_det_eq_one (det_eq_one_of_mem_componentGroup hU hγ) hint

end AdelicExamples.GL2

end TauCeti
