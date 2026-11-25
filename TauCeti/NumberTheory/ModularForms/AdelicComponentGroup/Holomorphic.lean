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
transformations. So `Γ_{g,U}\ℍ` is a Riemann surface, the homeomorphism
`Γ_{g,U}\ℍ ≃ₜ Γ_{qgu,U}\ℍ` induced by `z ↦ q • z` is a biholomorphism, and for compact open
`U' ≤ U` the map `Γ_{g,U'}\ℍ → Γ_{g,U}\ℍ` induced by `z ↦ z` is holomorphic, surjective and has
finite fibres, since `Γ_{g,U'}` has finite index in `Γ_{g,U}`.

## Main definitions

* `TauCeti.AdelicExamples.GL2.componentQuotientMap`: for `U' ≤ U`, the map
  `Γ_{g,U'}\ℍ → Γ_{g,U}\ℍ` sending the orbit of `z` to the orbit of `z`.

## Main results

* `Function.Surjective.properlyDiscontinuousSMul`: proper discontinuity passes to a surjective
  image of the acting type.
* `Subgroup.mdifferentiable_map_of_le_orbitRel`: for properly discontinuous `Δ ≤ Γ` in
  `PSL₂(ℝ)`, the map `Δ\ℍ → Γ\ℍ` is holomorphic.
* `TauCeti.AdelicExamples.GL2.properlyDiscontinuousSMul_componentGroupPSL`: for compact open `U`,
  the image of `Γ_{g,U}` in `PSL₂(ℝ)` acts properly discontinuously on `ℍ`.
* `TauCeti.AdelicExamples.GL2.relIndex_componentGroupPSL_ne_zero`: for `U'` open and `U` compact,
  the image of `Γ_{g,U'}` has finite index in that of `Γ_{g,U}`.
* `TauCeti.AdelicExamples.GL2.mdifferentiable_componentQuotientConjHomeomorph_of_isCompact` and
  `TauCeti.AdelicExamples.GL2.mdifferentiable_componentQuotientConjHomeomorph_symm`: for compact
  open `U`, `Γ_{g,U}\ℍ ≃ₜ Γ_{qgu,U}\ℍ` and its inverse are holomorphic.
* `TauCeti.AdelicExamples.GL2.mdifferentiable_componentQuotientMap`,
  `TauCeti.AdelicExamples.GL2.surjective_componentQuotientMap` and
  `TauCeti.AdelicExamples.GL2.finite_fiber_componentQuotientMap`: for `U'` open, `U` compact and
  `U' ≤ U`, the map `Γ_{g,U'}\ℍ → Γ_{g,U}\ℍ` is holomorphic, surjective and has finite fibres.

## References

* J. S. Milne, *Introduction to Shimura varieties*, revision of 16 September 2017, Lemma 5.13
  with the remarks after it, pp. 57-58.
-/

public noncomputable section

open IsDedekindDomain Matrix MulAction UpperHalfPlane
open scoped ContDiff MatrixGroups Manifold

/-- **Proper discontinuity pushes forward along surjective maps of acting types.** If
`f : M → N` is surjective, each `f m` acts as `m` does, and `M` acts properly discontinuously on
`X`, then so does `N`: the elements of `N` moving a compact `K` to meet a compact `L` are images
of the finitely many such elements of `M`. -/
@[to_additive
/-- **Proper discontinuity pushes forward along surjective maps of acting types.** If
`f : M → N` is surjective, each `f m` acts as `m` does, and `M` acts properly discontinuously on
`X`, then so does `N`. -/]
theorem Function.Surjective.properlyDiscontinuousSMul {M N X : Type*} [TopologicalSpace X]
    [SMul M X] [SMul N X] [ProperlyDiscontinuousSMul M X] {f : M → N} (hf : Surjective f)
    (hsmul : ∀ (m : M) (x : X), f m • x = m • x) : ProperlyDiscontinuousSMul N X where
  finite_disjoint_inter_image {K L} hK hL := by
    refine ((ProperlyDiscontinuousSMul.finite_disjoint_inter_image (Γ := M) hK hL).image
      f).subset ?_
    intro n hn
    obtain ⟨m, rfl⟩ := hf n
    exact ⟨m, by simpa only [Set.mem_ofPred_eq, hsmul] using hn, rfl⟩

namespace Subgroup

variable {Δ Γ : Subgroup PSL(2, ℝ)}

/-- **The map of coarse quotients for an inclusion of Fuchsian groups is holomorphic.** For
`Δ ≤ Γ` acting properly discontinuously on `ℍ`, the map `Δ\ℍ → Γ\ℍ` sending the orbit of `z`
to the orbit of `z` pulls back along the orbit projection to the holomorphic orbit projection of
`Γ`. -/
theorem mdifferentiable_map_of_le_orbitRel [ProperlyDiscontinuousSMul Δ ℍ]
    [ProperlyDiscontinuousSMul Γ ℍ] (h : Δ ≤ Γ) :
    MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (Setoid.map_of_le
      (TauCeti.MulAction.orbitRel_le_of_subgroup_le (X := ℍ) h) :
        orbitRel.Quotient Δ ℍ → orbitRel.Quotient Γ ℍ) := fun p ↦ by
  induction p using Quotient.inductionOn' with | h z => ?_
  exact mdifferentiableAt_of_eventually_mdifferentiableAt_comp_quotientMk
    (.of_forall fun w ↦ mdifferentiable_quotientMk Γ w)

end Subgroup

namespace TauCeti

namespace AdelicExamples.GL2

variable {U U' : Subgroup (GL (Fin 2) (FiniteAdeleRing ℤ ℚ))} {g : GL (Fin 2) (FiniteAdeleRing ℤ ℚ)}

/-- `Γ_{g,U}` consists of matrices of positive determinant. -/
theorem componentGroup_le_glpos (U : Subgroup (GL (Fin 2) (FiniteAdeleRing ℤ ℚ)))
    (g : GL (Fin 2) (FiniteAdeleRing ℤ ℚ)) : componentGroup U g ≤ GLPos (Fin 2) ℚ :=
  fun _ hγ ↦ (mem_glpos _).mpr (mem_componentGroup_iff.mp hγ).1

/-- The image of `Γ_{g,U}` in `PSL₂(ℝ)` is the image of `Γ_{g,U}`, viewed in `GL₂(ℚ)^+`, along
`GL₂(ℚ)^+ → PSL₂(ℝ)`. -/
theorem componentGroupPSL_eq_map (U : Subgroup (GL (Fin 2) (FiniteAdeleRing ℤ ℚ)))
    (g : GL (Fin 2) (FiniteAdeleRing ℤ ℚ)) :
    componentGroupPSL U g = ((componentGroup U g).subgroupOf (GLPos (Fin 2) ℚ)).map ratPosToPSL2R :=
  by ext; simp [Subgroup.mem_map, Subgroup.mem_subgroupOf]

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
  rw [componentGroupPSL_eq_map, componentGroupPSL_eq_map, ← Subgroup.relIndex_comap]
  intro h
  have hdvd := Subgroup.relIndex_dvd_of_le_left ((componentGroup U g).subgroupOf (GLPos _ _))
    (Subgroup.le_comap_map ratPosToPSL2R ((componentGroup U' g).subgroupOf (GLPos _ _)))
  rw [h, zero_dvd_iff, Subgroup.relIndex_subgroupOf (componentGroup_le_glpos U g)] at hdvd
  exact relIndex_componentGroup_ne_zero hU hU' g hdvd

/-- **The biholomorphism `Γ_{g,U}\ℍ ≃ₜ Γ_{qgu,U}\ℍ`**: for compact open `U`, the homeomorphism
induced by `z ↦ q • z` is holomorphic. -/
theorem mdifferentiable_componentQuotientConjHomeomorph_of_isCompact
    (hU : IsCompact (U : Set (GL (Fin 2) (FiniteAdeleRing ℤ ℚ))))
    (hU' : IsOpen (U : Set (GL (Fin 2) (FiniteAdeleRing ℤ ℚ))))
    (g : GL (Fin 2) (FiniteAdeleRing ℤ ℚ)) (q : GL(2, ℚ)⁺)
    {u : GL (Fin 2) (FiniteAdeleRing ℤ ℚ)} (hu : u ∈ U) :
    letI := properlyDiscontinuousSMul_componentGroupPSL (g := g) hU hU'
    letI := properlyDiscontinuousSMul_componentGroupPSL (g := GeneralLinearGroup.map
      (algebraMap ℚ (FiniteAdeleRing ℤ ℚ)) (q : GL (Fin 2) ℚ) * g * u) hU hU'
    MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (componentQuotientConjHomeomorph g q hu) :=
  letI := properlyDiscontinuousSMul_componentGroupPSL (g := g) hU hU'
  mdifferentiable_componentQuotientConjHomeomorph g q hu

/-- **The inverse of `Γ_{g,U}\ℍ ≃ₜ Γ_{qgu,U}\ℍ` is holomorphic** for compact open `U`; it is
induced by `z ↦ q⁻¹ • z`. -/
theorem mdifferentiable_componentQuotientConjHomeomorph_symm
    (hU : IsCompact (U : Set (GL (Fin 2) (FiniteAdeleRing ℤ ℚ))))
    (hU' : IsOpen (U : Set (GL (Fin 2) (FiniteAdeleRing ℤ ℚ))))
    (g : GL (Fin 2) (FiniteAdeleRing ℤ ℚ)) (q : GL(2, ℚ)⁺)
    {u : GL (Fin 2) (FiniteAdeleRing ℤ ℚ)} (hu : u ∈ U) :
    letI := properlyDiscontinuousSMul_componentGroupPSL (g := g) hU hU'
    letI := properlyDiscontinuousSMul_componentGroupPSL (g := GeneralLinearGroup.map
      (algebraMap ℚ (FiniteAdeleRing ℤ ℚ)) (q : GL (Fin 2) ℚ) * g * u) hU hU'
    MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (componentQuotientConjHomeomorph g q hu).symm := by
  have := properlyDiscontinuousSMul_componentGroupPSL (g := g) hU hU'
  have := properlyDiscontinuousSMul_componentGroupPSL (g := GeneralLinearGroup.map
    (algebraMap ℚ (FiniteAdeleRing ℤ ℚ)) (q : GL (Fin 2) ℚ) * g * u) hU hU'
  intro p
  induction p using Quotient.inductionOn' with | h z => ?_
  refine Subgroup.mdifferentiableAt_of_eventually_mdifferentiableAt_comp_quotientMk
    (.of_forall fun w ↦ ?_)
  have hcomp : (componentQuotientConjHomeomorph g q hu).symm ∘ Quotient.mk _ =
      Quotient.mk (orbitRel (componentGroupPSL U g) ℍ) ∘ (ratPosToPSL2R q⁻¹ • ·) :=
    funext fun z ↦ by
      rw [Function.comp_apply, Function.comp_apply, componentQuotientConjHomeomorph_symm_mk,
        ratPosToPSL2R_smul, Subgroup.coe_inv]
  rw [hcomp]
  exact (Subgroup.mdifferentiable_quotientMk _ _).comp w
    ((contMDiff_const_smul (I := 𝓘(ℂ)) (n := ∞) (M := ℍ) _).mdifferentiable (by simp) w)

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
theorem surjective_componentQuotientMap (h : U' ≤ U) (g : GL (Fin 2) (FiniteAdeleRing ℤ ℚ)) :
    Function.Surjective (componentQuotientMap h g) := fun p ↦
  Quotient.inductionOn' p fun z ↦ ⟨Quotient.mk _ z, rfl⟩

/-- The change-of-level map `Γ_{g,U'}\ℍ → Γ_{g,U}\ℍ` is continuous. -/
theorem continuous_componentQuotientMap (h : U' ≤ U) (g : GL (Fin 2) (FiniteAdeleRing ℤ ℚ)) :
    Continuous (componentQuotientMap h g) :=
  continuous_quot_lift _ continuous_quotient_mk'

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
  Subgroup.mdifferentiable_map_of_le_orbitRel (componentGroupPSL_mono h g)

end AdelicExamples.GL2

end TauCeti
