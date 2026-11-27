/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.DoubleCoset.Fiber
public import TauCeti.NumberTheory.ModularForms.AdelicComponentGroup.Arithmetic
public import TauCeti.NumberTheory.ModularForms.AdelicComponentGroup.Quotient

/-!
# Holomorphic maps between the quotients `Γ_{g,U}\ℍ`

For a compact open subgroup `U` of `GL₂(𝔸_f)` and `g ∈ GL₂(𝔸_f)`, the image
`TauCeti.AdelicExamples.GL2.componentGroupPSL U g` of `Γ_{g,U} = GL₂(ℚ)^+ ∩ gUg⁻¹` in `PSL₂(ℝ)`
acts properly discontinuously on `ℍ`: it is the image of the arithmetic group
`TauCeti.AdelicExamples.GL2.componentGroupReal U g`, acting through the same Möbius
transformations (`Function.Surjective.properlyDiscontinuousSMul`). So `Γ_{g,U}\ℍ` is a Riemann
surface, and the homeomorphism `Γ_{g,U}\ℍ ≃ₜ Γ_{qgu,U}\ℍ` induced by `z ↦ q • z` is a
biholomorphism (`TauCeti.AdelicExamples.GL2.mdifferentiable_componentQuotientConjHomeomorph` and
its `_symm` form apply). For compact open `U' ≤ U` the map `Γ_{g,U'}\ℍ → Γ_{g,U}\ℍ` induced by
`z ↦ z` is holomorphic, surjective and has finite fibres, since `Γ_{g,U'}` has finite index in
`Γ_{g,U}`.

## Main definitions

* `TauCeti.AdelicExamples.GL2.componentQuotientMap`: for `U' ≤ U`, the map
  `Γ_{g,U'}\ℍ → Γ_{g,U}\ℍ` sending the orbit of `z` to the orbit of `z`.

## Main results

* `TauCeti.AdelicExamples.GL2.properlyDiscontinuousSMul_componentGroupPSL`: for compact open `U`,
  the image of `Γ_{g,U}` in `PSL₂(ℝ)` acts properly discontinuously on `ℍ`.
* `TauCeti.AdelicExamples.GL2.relIndex_componentGroupPSL_ne_zero`: for `U'` open and `U` compact,
  the image of `Γ_{g,U'}` has finite index in that of `Γ_{g,U}`.
* `TauCeti.AdelicExamples.GL2.mdifferentiable_componentQuotientMap`,
  `TauCeti.AdelicExamples.GL2.componentQuotientMap_surjective` and
  `TauCeti.AdelicExamples.GL2.finite_fiber_componentQuotientMap`: for `U'` open, `U` compact and
  `U' ≤ U`, the map `Γ_{g,U'}\ℍ → Γ_{g,U}\ℍ` is holomorphic, surjective and has finite fibres.

## References

* J. S. Milne, *Introduction to Shimura varieties*, revision of 16 September 2017, Lemma 5.13
  with the remarks after it, pp. 57-58.
-/

public noncomputable section

open IsDedekindDomain Matrix MulAction UpperHalfPlane
open scoped ContDiff MatrixGroups Manifold

namespace TauCeti

namespace AdelicExamples.GL2

variable {U U' : Subgroup (GL (Fin 2) (FiniteAdeleRing ℤ ℚ))} {g : GL (Fin 2) (FiniteAdeleRing ℤ ℚ)}

/-- **The image of `Γ_{g,U}` in `PSL₂(ℝ)` acts properly discontinuously on `ℍ`** for compact open
`U`: each of its elements acts as an element of the arithmetic group `componentGroupReal U g`
does. -/
theorem properlyDiscontinuousSMul_componentGroupPSL
    (hU : IsCompact (U : Set (GL (Fin 2) (FiniteAdeleRing ℤ ℚ))))
    (hU' : IsOpen (U : Set (GL (Fin 2) (FiniteAdeleRing ℤ ℚ)))) :
    ProperlyDiscontinuousSMul (componentGroupPSL U g) ℍ := by
  have := properlyDiscontinuousSMul_componentGroupReal (g := g) hU hU'
  have hmem (m : componentGroupReal U g) :
      ∃ γ : GL(2, ℚ)⁺, (γ : GL (Fin 2) ℚ) ∈ componentGroup U g ∧
        GeneralLinearGroup.map (algebraMap ℚ ℝ) (γ : GL (Fin 2) ℚ) = m := by
    obtain ⟨γ, hγ, h⟩ := mem_componentGroupReal_iff.mp m.property
    exact ⟨⟨γ, componentGroup_le_glpos U g hγ⟩, hγ, h⟩
  choose γ hγ hφγ using hmem
  let f : componentGroupReal U g → componentGroupPSL U g := fun m ↦
    ⟨ratPosToPSL2R (γ m), mem_componentGroupPSL_iff.mpr ⟨γ m, hγ m, rfl⟩⟩
  refine Function.Surjective.properlyDiscontinuousSMul (f := f) (fun n ↦ ?_) fun m x ↦ ?_
  · obtain ⟨δ, hδ, hn⟩ := mem_componentGroupPSL_iff.mp n.property
    let m : componentGroupReal U g := ⟨_, map_mem_componentGroupReal_iff.mpr hδ⟩
    have hm : γ m = δ := Subtype.ext
      (GeneralLinearGroup.map_injective (algebraMap ℚ ℝ).injective (hφγ m))
    exact ⟨m, Subtype.ext (by simp only [f, hm, hn])⟩
  · simp only [Subgroup.smul_def, f]
    rw [ratPosToPSL2R_smul, hφγ]

/-- **The image of `Γ_{g,U'}` has finite index in that of `Γ_{g,U}` in `PSL₂(ℝ)`** whenever
`U'` is open and `U` is compact. -/
theorem relIndex_componentGroupPSL_ne_zero
    (hU : IsCompact (U : Set (GL (Fin 2) (FiniteAdeleRing ℤ ℚ))))
    (hU' : IsOpen (U' : Set (GL (Fin 2) (FiniteAdeleRing ℤ ℚ))))
    (g : GL (Fin 2) (FiniteAdeleRing ℤ ℚ)) :
    (componentGroupPSL U' g).relIndex (componentGroupPSL U g) ≠ 0 := by
  have hfin : ((componentGroup U' g).subgroupOf (GLPos _ _)).IsFiniteRelIndex
      ((componentGroup U g).subgroupOf (GLPos _ _)) :=
    ⟨by rw [Subgroup.relIndex_subgroupOf (componentGroup_le_glpos U g)]
        exact relIndex_componentGroup_ne_zero hU hU' g⟩
  rw [componentGroupPSL_def, componentGroupPSL_def]
  exact (hfin.map ratPosToPSL2R).relIndex_ne_zero

/-- **Change of level on the components.** For `U' ≤ U`, the map `Γ_{g,U'}\ℍ → Γ_{g,U}\ℍ`
sending the orbit of `z` to the orbit of `z`. -/
def componentQuotientMap (h : U' ≤ U) (g : GL (Fin 2) (FiniteAdeleRing ℤ ℚ)) :
    orbitRel.Quotient (componentGroupPSL U' g) ℍ → orbitRel.Quotient (componentGroupPSL U g) ℍ :=
  Setoid.map_of_le (MulAction.orbitRel_le_of_subgroup_le (X := ℍ) (componentGroupPSL_mono h g))

@[simp]
theorem componentQuotientMap_mk (h : U' ≤ U) (g : GL (Fin 2) (FiniteAdeleRing ℤ ℚ)) (z : ℍ) :
    componentQuotientMap h g (Quotient.mk _ z) = Quotient.mk _ z :=
  (rfl)

/-- The change-of-level map `Γ_{g,U'}\ℍ → Γ_{g,U}\ℍ` is surjective. -/
theorem componentQuotientMap_surjective (h : U' ≤ U) (g : GL (Fin 2) (FiniteAdeleRing ℤ ℚ)) :
    Function.Surjective (componentQuotientMap h g) :=
  Setoid.map_of_le_surjective _

/-- The change-of-level map `Γ_{g,U'}\ℍ → Γ_{g,U}\ℍ` is continuous. -/
theorem continuous_componentQuotientMap (h : U' ≤ U) (g : GL (Fin 2) (FiniteAdeleRing ℤ ℚ)) :
    Continuous (componentQuotientMap h g) :=
  continuous_map_of_le _

/-- **The change-of-level map `Γ_{g,U'}\ℍ → Γ_{g,U}\ℍ` has finite fibres** for `U'` open and `U`
compact, since `Γ_{g,U'}` then has finite index in `Γ_{g,U}`. -/
theorem finite_fiber_componentQuotientMap
    (hU : IsCompact (U : Set (GL (Fin 2) (FiniteAdeleRing ℤ ℚ))))
    (hU' : IsOpen (U' : Set (GL (Fin 2) (FiniteAdeleRing ℤ ℚ)))) (h : U' ≤ U)
    (g : GL (Fin 2) (FiniteAdeleRing ℤ ℚ)) (p : orbitRel.Quotient (componentGroupPSL U g) ℍ) :
    Finite {p' // componentQuotientMap h g p' = p} :=
  have : (componentGroupPSL U' g).IsFiniteRelIndex (componentGroupPSL U g) :=
    ⟨relIndex_componentGroupPSL_ne_zero hU hU' g⟩
  finite_fiber_orbitRel_map_of_isFiniteRelIndex (componentGroupPSL_mono h g) p

/-- **The change-of-level map `Γ_{g,U'}\ℍ → Γ_{g,U}\ℍ` is holomorphic** for `U'` open, `U`
compact and `U' ≤ U`; then both are compact open, so both groups act properly discontinuously. -/
theorem mdifferentiable_componentQuotientMap
    (hU : IsCompact (U : Set (GL (Fin 2) (FiniteAdeleRing ℤ ℚ))))
    (hU' : IsOpen (U' : Set (GL (Fin 2) (FiniteAdeleRing ℤ ℚ)))) (h : U' ≤ U)
    (g : GL (Fin 2) (FiniteAdeleRing ℤ ℚ)) :
    letI := properlyDiscontinuousSMul_componentGroupPSL (g := g)
      (hU.of_isClosed_subset (U'.isClosed_of_isOpen hU') h) hU'
    letI := properlyDiscontinuousSMul_componentGroupPSL (g := g) hU (U'.isOpen_mono h hU')
    MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (componentQuotientMap h g) :=
  letI := properlyDiscontinuousSMul_componentGroupPSL (g := g)
    (hU.of_isClosed_subset (U'.isClosed_of_isOpen hU') h) hU'
  letI := properlyDiscontinuousSMul_componentGroupPSL (g := g) hU (U'.isOpen_mono h hU')
  Subgroup.mdifferentiable_orbitRel_map_of_le (componentGroupPSL_mono h g)

end AdelicExamples.GL2

end TauCeti
