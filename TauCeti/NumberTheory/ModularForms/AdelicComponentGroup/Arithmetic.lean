/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.ModularForms.ProperlyDiscontinuous
public import TauCeti.NumberTheory.ModularForms.AdelicComponentGroup.Integral
import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Map
import TauCeti.NumberTheory.ModularForms.CongruenceSubgroups.Basic
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

* `TauCeti.AdelicExamples.GL2.componentGroupReal U g`: the image of `Γ_{g,U}` in `GL₂(ℝ)`.

## Main results

* `TauCeti.AdelicExamples.GL2.relIndex_componentGroup_range_mapGL_ne_zero`: for open `U`,
  `Γ_{g,U} ∩ SL₂(ℤ)` has finite index in `SL₂(ℤ)`.
* `TauCeti.AdelicExamples.GL2.mapGL_mem_componentGroup_principalLevel_one_iff`: at principal
  level `N ≠ 0`, the integral matrices of `Γ_{1,K(N)}` form `Γ(N)`.
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

/-- **`Γ_{g,U} ∩ SL₂(ℤ)` has finite index in `SL₂(ℤ)`** for open `U`. -/
theorem relIndex_componentGroup_range_mapGL_ne_zero
    (hU : IsOpen (U : Set (GL (Fin 2) (FiniteAdeleRing ℤ ℚ)))) :
    (componentGroup U g).relIndex (SpecialLinearGroup.mapGL (n := Fin 2) (R := ℤ) ℚ).range ≠ 0 := by
  set φ := GeneralLinearGroup.map (n := Fin 2) (algebraMap ℚ (FiniteAdeleRing ℤ ℚ))
  set ψ := φ.comp (SpecialLinearGroup.mapGL (n := Fin 2) (R := ℤ) ℚ)
  set V := U.map (MulAut.conj g).toMonoidHom
  set O := principalLevel ℚ (⊤ : Ideal ℤ)
  -- `gUg⁻¹` is open, so it has finite index in the compact group `GL₂(Ô)`.
  have hV : IsOpen (V : Set (GL (Fin 2) (FiniteAdeleRing ℤ ℚ))) :=
    (Subgroup.isOpen_map_conj_iff g).mpr hU
  have h1 : V.relIndex O ≠ 0 := by
    have (v : HeightOneSpectrum ℤ) : Finite (ℤ ⧸ v.asIdeal) :=
      Ring.HasFiniteQuotients.finiteQuotient v.ne_bot
    have : CompactSpace O := isCompact_iff_compactSpace.mp (isCompact_principalLevel ℚ top_ne_bot)
    have := Subgroup.quotient_finite_of_isOpen (V.subgroupOf O) (Subgroup.subgroupOf_isOpen O V hV)
    exact Subgroup.index_ne_zero_of_finite
  -- The diagonal image of `SL₂(ℤ)` lies in `GL₂(Ô)`.
  have h2 : ψ.range ≤ O := by
    rintro _ ⟨γ, rfl⟩
    have himage : ψ γ = GeneralLinearGroup.map (algebraMap ℤ (FiniteAdeleRing ℤ ℚ)) γ.toGL := by
      ext i j
      simp [ψ, φ, SpecialLinearGroup.mapGL_coe_matrix]
    rw [himage]
    exact map_algebraMap_mem_principalLevel fun _ _ ↦ Submodule.mem_top
  have h3 : (V.comap ψ).index ≠ 0 := by
    rw [Subgroup.index_comap]
    exact mt (Subgroup.relIndex_eq_zero_of_le_right h2) h1
  -- An element of `SL₂(ℤ)` whose diagonal image lies in `gUg⁻¹` lies in `Γ_{g,U}`.
  have h4 : V.comap ψ ≤ (componentGroup U g).comap (SpecialLinearGroup.mapGL ℚ) := by
    intro γ hγ
    rw [Subgroup.mem_comap, mem_componentGroup_iff, SpecialLinearGroup.det_mapGL]
    refine ⟨zero_lt_one, ?_⟩
    obtain ⟨u, hu, hu'⟩ := Subgroup.mem_map.mp (Subgroup.mem_comap.mp hγ)
    have hu'' : g * u * g⁻¹ = φ (SpecialLinearGroup.mapGL ℚ γ) := by
      simpa [MulAut.conj_apply, ψ] using hu'
    rw [← hu'']
    simpa [mul_assoc] using hu
  rw [← Subgroup.index_comap]
  exact fun h ↦ h3 (Nat.eq_zero_of_zero_dvd (h ▸ Subgroup.index_dvd_of_le h4))

/-- **At principal level `N ≠ 0`, the component of `1` has group `Γ(N)`**: an element of
`SL₂(ℤ)` lies in `Γ_{1,K(N)}` exactly when it lies in the principal congruence subgroup `Γ(N)`. -/
theorem mapGL_mem_componentGroup_principalLevel_one_iff {N : ℕ} [NeZero N] {γ : SL(2, ℤ)} :
    SpecialLinearGroup.mapGL ℚ γ ∈ componentGroup (principalLevel ℚ (Ideal.span {(N : ℤ)})) 1 ↔
      γ ∈ CongruenceSubgroup.Gamma N := by
  refine ⟨fun h ↦ ?_, fun h ↦ map_Gamma_le_componentGroup (fun x hx ↦ ⟨x, hx, by simp⟩)
    ⟨γ, h, rfl⟩⟩
  have himage : GeneralLinearGroup.map (algebraMap ℚ (FiniteAdeleRing ℤ ℚ))
      (SpecialLinearGroup.mapGL ℚ γ) =
        GeneralLinearGroup.map (algebraMap ℤ (FiniteAdeleRing ℤ ℚ)) γ.toGL := by
    ext i j
    simp [SpecialLinearGroup.mapGL_coe_matrix]
  rw [mem_componentGroup_iff, inv_one, one_mul, mul_one, himage] at h
  obtain ⟨hg, -, h⟩ := mem_principalLevel_iff.mp h.2
  have hN : Ideal.span {(N : ℤ)} ≠ ⊥ := by simp [NeZero.ne N]
  have hentry (i j : Fin 2) : (N : ℤ) ∣ γ i j - (1 : Matrix (Fin 2) (Fin 2) ℤ) i j := by
    rw [← Ideal.mem_span_singleton, ← algebraMap_mem_completedIdeal_iff (K := ℚ) hN]
    convert h i j using 1
    refine Subtype.ext ?_
    fin_cases i <;> fin_cases j <;> simp
  simpa using CongruenceSubgroup.mem_Gamma_iff_dvd.mpr
    ⟨hentry 0 0, by simpa using hentry 0 1, by simpa using hentry 1 0, hentry 1 1⟩

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
  have hrange : (SpecialLinearGroup.mapGL (n := Fin 2) (R := ℤ) ℝ).range =
      (SpecialLinearGroup.mapGL (n := Fin 2) (R := ℤ) ℚ).range.map
        (GeneralLinearGroup.map (algebraMap ℚ ℝ)) := by
    rw [MonoidHom.map_range]
    congr 1
    ext γ i j
    simp
  rw [Subgroup.isArithmetic_iff, hrange, componentGroupReal,
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
