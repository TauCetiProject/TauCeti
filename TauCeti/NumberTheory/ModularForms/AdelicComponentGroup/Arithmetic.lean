/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.ModularForms.ProperlyDiscontinuous
public import TauCeti.NumberTheory.ModularForms.AdelicComponentGroup.Integral
import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Map
import TauCeti.RingTheory.DedekindDomain.AdicValuation.ResidueField
import TauCeti.Topology.Algebra.Group.Subgroup

/-!
# The `GL₂` component groups are arithmetic

For a compact open subgroup `U` of `GL₂(𝔸_f)` and `g ∈ GL₂(𝔸_f)`, the congruence group
`Γ_{g,U} = GL₂(ℚ)^+ ∩ gUg⁻¹` (`TauCeti.AdelicExamples.GL2.componentGroup`) is commensurable with
`SL₂(ℤ)` inside `GL₂(ℚ)`. Hence its image `TauCeti.AdelicExamples.GL2.componentGroupReal U g` in
`GL₂(ℝ)` is arithmetic in Mathlib's sense (`Subgroup.IsArithmetic`), so it is discrete, acts
properly discontinuously on `ℍ`, and the orbit space `Γ_{g,U}\ℍ` is Hausdorff.

One half of the commensurability, finite index of `Γ_{g,U} ∩ SL₂(ℤ)` in `Γ_{g,U}`, is
`TauCeti.AdelicExamples.GL2.relIndex_range_mapGL_componentGroup_ne_zero` and only needs `U`
compact. The other half, finite index in `SL₂(ℤ)`, only needs `U` open: the diagonal image of
`SL₂(ℤ)` lies in the compact group `GL₂(Ô)`, which meets the open subgroup `gUg⁻¹` in a subgroup
of finite index, and every element of `SL₂(ℤ)` has determinant `1 > 0`.

## Main definitions

* `TauCeti.AdelicExamples.GL2.componentGroupReal U g`: the image of `Γ_{g,U}` in `GL₂(ℝ)`, with
  membership lemmas `TauCeti.AdelicExamples.GL2.mem_componentGroupReal_iff` and
  `TauCeti.AdelicExamples.GL2.map_mem_componentGroupReal_iff`, monotonicity in `U`
  (`TauCeti.AdelicExamples.GL2.componentGroupReal_mono`) and the conjugation formula
  `TauCeti.AdelicExamples.GL2.componentGroupReal_mul_mul`.

## Main results

* `TauCeti.AdelicExamples.GL2.relIndex_componentGroup_range_mapGL_ne_zero`: for open `U`,
  `Γ_{g,U} ∩ SL₂(ℤ)` has finite index in `SL₂(ℤ)`.
* `TauCeti.AdelicExamples.GL2.commensurable_componentGroup`: for compact open `U`, `Γ_{g,U}` is
  commensurable with `SL₂(ℤ)` in `GL₂(ℚ)`.
* `TauCeti.AdelicExamples.GL2.isArithmetic_componentGroupReal`: its image in `GL₂(ℝ)` is
  arithmetic.
* `TauCeti.AdelicExamples.GL2.discreteTopology_componentGroupReal`,
  `TauCeti.AdelicExamples.GL2.properlyDiscontinuousSMul_componentGroupReal`,
  `TauCeti.AdelicExamples.GL2.t2Space_quotient_componentGroupReal`: it is discrete, acts properly
  discontinuously on `ℍ`, and has Hausdorff orbit space.

## References

* J. S. Milne, *Introduction to Shimura varieties*, revision of 16 September 2017, Lemma 5.13
  with the remarks after it, pp. 57-58.
-/

public noncomputable section

open IsDedekindDomain IsDedekindDomain.FiniteAdeleRing Matrix
open scoped MatrixGroups UpperHalfPlane

namespace TauCeti

namespace AdelicExamples.GL2

variable {U : Subgroup (GL (Fin 2) (FiniteAdeleRing ℤ ℚ))} {g : GL (Fin 2) (FiniteAdeleRing ℤ ℚ)}

/-- The image in `GL₂(ℝ)` of the congruence group `Γ_{g,U} = GL₂(ℚ)^+ ∩ gUg⁻¹` of the
component through `g`. -/
def componentGroupReal (U : Subgroup (GL (Fin 2) (FiniteAdeleRing ℤ ℚ)))
    (g : GL (Fin 2) (FiniteAdeleRing ℤ ℚ)) : Subgroup (GL (Fin 2) ℝ) :=
  (componentGroup U g).map (GeneralLinearGroup.map (algebraMap ℚ ℝ))

/-- The image of `Γ_{g,U}` in `GL₂(ℝ)` is its image along `GL₂(ℚ) → GL₂(ℝ)`. -/
theorem componentGroupReal_def (U : Subgroup (GL (Fin 2) (FiniteAdeleRing ℤ ℚ)))
    (g : GL (Fin 2) (FiniteAdeleRing ℤ ℚ)) :
    componentGroupReal U g = (componentGroup U g).map (GeneralLinearGroup.map (algebraMap ℚ ℝ)) :=
  (rfl)

/-- Membership in the image of `Γ_{g,U}` in `GL₂(ℝ)`. -/
@[simp]
theorem mem_componentGroupReal_iff {x : GL (Fin 2) ℝ} :
    x ∈ componentGroupReal U g ↔
      ∃ γ ∈ componentGroup U g, GeneralLinearGroup.map (algebraMap ℚ ℝ) γ = x :=
  Subgroup.mem_map

/-- A rational matrix lies in the image of `Γ_{g,U}` in `GL₂(ℝ)` exactly when it lies in
`Γ_{g,U}`, since `GL₂(ℚ) → GL₂(ℝ)` is injective. -/
@[simp 1100]
theorem map_mem_componentGroupReal_iff {γ : GL (Fin 2) ℚ} :
    GeneralLinearGroup.map (algebraMap ℚ ℝ) γ ∈ componentGroupReal U g ↔
      γ ∈ componentGroup U g :=
  Subgroup.mem_map_iff_mem (GeneralLinearGroup.map_injective (algebraMap ℚ ℝ).injective)

/-- The image of `Γ_{g,U}` in `GL₂(ℝ)` is monotone in `U`. -/
theorem componentGroupReal_mono {U U' : Subgroup (GL (Fin 2) (FiniteAdeleRing ℤ ℚ))} (h : U' ≤ U)
    (g : GL (Fin 2) (FiniteAdeleRing ℤ ℚ)) : componentGroupReal U' g ≤ componentGroupReal U g :=
  Subgroup.map_mono (componentGroup_mono h g)

/-- **`Γ_{qgu,U} = qΓ_{g,U}q⁻¹`** in `GL₂(ℝ)`, for `q ∈ GL₂(ℚ)` and `u ∈ U`. -/
theorem componentGroupReal_mul_mul (g : GL (Fin 2) (FiniteAdeleRing ℤ ℚ)) (q : GL (Fin 2) ℚ)
    {u : GL (Fin 2) (FiniteAdeleRing ℤ ℚ)} (hu : u ∈ U) :
    componentGroupReal U (GeneralLinearGroup.map (algebraMap ℚ (FiniteAdeleRing ℤ ℚ)) q * g * u) =
      (componentGroupReal U g).map
        (MulAut.conj (GeneralLinearGroup.map (algebraMap ℚ ℝ) q)).toMonoidHom := by
  rw [componentGroupReal, componentGroupReal, componentGroup_mul_mul g q hu, Subgroup.map_map,
    Subgroup.map_map]
  congr 1
  ext γ : 1
  simp

/-- **`Γ_{g,U} ∩ SL₂(ℤ)` has finite index in `SL₂(ℤ)`** for open `U`. -/
theorem relIndex_componentGroup_range_mapGL_ne_zero
    (hU : IsOpen (U : Set (GL (Fin 2) (FiniteAdeleRing ℤ ℚ)))) :
    (componentGroup U g).relIndex (SpecialLinearGroup.mapGL (n := Fin 2) (R := ℤ) ℚ).range ≠ 0 := by
  set ψ := (GeneralLinearGroup.map (n := Fin 2) (algebraMap ℤ (FiniteAdeleRing ℤ ℚ))).comp
    (SpecialLinearGroup.toGL (n := Fin 2) (R := ℤ))
  set V := U.map (MulAut.conj g).toMonoidHom
  set O := principalLevel ℚ (⊤ : Ideal ℤ)
  -- `gUg⁻¹` is open, so it has finite index in the compact group `GL₂(Ô)`.
  have hV : IsOpen (V : Set (GL (Fin 2) (FiniteAdeleRing ℤ ℚ))) :=
    (Subgroup.isOpen_map_conj_iff g).mpr hU
  have h1 : V.relIndex O ≠ 0 := by
    have : CompactSpace O := isCompact_iff_compactSpace.mp (isCompact_principalLevel ℚ top_ne_bot)
    have := Subgroup.quotient_finite_of_isOpen (V.subgroupOf O) (Subgroup.subgroupOf_isOpen O V hV)
    exact Subgroup.index_ne_zero_of_finite
  -- The diagonal image of `SL₂(ℤ)` lies in `GL₂(Ô)`.
  have h2 : ψ.range ≤ O := by
    rintro _ ⟨γ, rfl⟩
    exact map_algebraMap_mem_principalLevel fun _ _ ↦ Submodule.mem_top
  have h3 : (V.comap ψ).index ≠ 0 := by
    rw [Subgroup.index_comap]
    exact mt (Subgroup.relIndex_eq_zero_of_le_right h2) h1
  -- An element of `SL₂(ℤ)` whose diagonal image lies in `gUg⁻¹` lies in `Γ_{g,U}`.
  have h4 : V.comap ψ ≤ (componentGroup U g).comap (SpecialLinearGroup.mapGL ℚ) :=
    fun _ hγ ↦ mapGL_mem_componentGroup_iff.mpr hγ
  rw [← Subgroup.index_comap]
  exact fun h ↦ h3 (Nat.eq_zero_of_zero_dvd (h ▸ Subgroup.index_dvd_of_le h4))

/-- **`Γ_{g,U}` is commensurable with `SL₂(ℤ)`** inside `GL₂(ℚ)`, for compact open `U`. -/
theorem commensurable_componentGroup
    (hU : IsCompact (U : Set (GL (Fin 2) (FiniteAdeleRing ℤ ℚ))))
    (hU' : IsOpen (U : Set (GL (Fin 2) (FiniteAdeleRing ℤ ℚ)))) :
    (componentGroup U g).Commensurable (SpecialLinearGroup.mapGL (n := Fin 2) (R := ℤ) ℚ).range :=
  ⟨⟨relIndex_componentGroup_range_mapGL_ne_zero hU'⟩,
    ⟨relIndex_range_mapGL_componentGroup_ne_zero hU⟩⟩

/-- **The image of `Γ_{g,U}` in `GL₂(ℝ)` is arithmetic** for compact open `U`. -/
theorem isArithmetic_componentGroupReal
    (hU : IsCompact (U : Set (GL (Fin 2) (FiniteAdeleRing ℤ ℚ))))
    (hU' : IsOpen (U : Set (GL (Fin 2) (FiniteAdeleRing ℤ ℚ)))) :
    (componentGroupReal U g).IsArithmetic := by
  rw [Subgroup.isArithmetic_iff, ← SpecialLinearGroup.map_comp_mapGL_int (algebraMap ℚ ℝ),
    ← MonoidHom.map_range, componentGroupReal,
    Subgroup.Commensurable.map_injective_iff
      (GeneralLinearGroup.map_injective (algebraMap ℚ ℝ).injective)]
  exact commensurable_componentGroup hU hU'

/-- The image of `Γ_{g,U}` in `GL₂(ℝ)` is discrete, for compact open `U`. -/
theorem discreteTopology_componentGroupReal
    (hU : IsCompact (U : Set (GL (Fin 2) (FiniteAdeleRing ℤ ℚ))))
    (hU' : IsOpen (U : Set (GL (Fin 2) (FiniteAdeleRing ℤ ℚ)))) :
    DiscreteTopology (componentGroupReal U g) :=
  have := isArithmetic_componentGroupReal (g := g) hU hU'
  inferInstance

/-- The image of `Γ_{g,U}` in `GL₂(ℝ)` acts properly discontinuously on `ℍ`, for compact open
`U`. -/
theorem properlyDiscontinuousSMul_componentGroupReal
    (hU : IsCompact (U : Set (GL (Fin 2) (FiniteAdeleRing ℤ ℚ))))
    (hU' : IsOpen (U : Set (GL (Fin 2) (FiniteAdeleRing ℤ ℚ)))) :
    ProperlyDiscontinuousSMul (componentGroupReal U g) ℍ :=
  have := isArithmetic_componentGroupReal (g := g) hU hU'
  inferInstance

/-- The orbit space `Γ_{g,U}\ℍ` is Hausdorff, for compact open `U`. -/
theorem t2Space_quotient_componentGroupReal
    (hU : IsCompact (U : Set (GL (Fin 2) (FiniteAdeleRing ℤ ℚ))))
    (hU' : IsOpen (U : Set (GL (Fin 2) (FiniteAdeleRing ℤ ℚ)))) :
    T2Space (Quotient (MulAction.orbitRel (componentGroupReal U g) ℍ)) :=
  have := properlyDiscontinuousSMul_componentGroupReal (g := g) hU hU'
  inferInstance

end AdelicExamples.GL2

end TauCeti
