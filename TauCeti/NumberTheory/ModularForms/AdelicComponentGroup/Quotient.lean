/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Fuchsian.Conj
public import TauCeti.Analysis.Complex.UpperHalfPlane.RatPSLAction
public import TauCeti.NumberTheory.ModularForms.AdelicComponentGroup

/-!
# The quotients `Γ_{g,U}\ℍ` of the `GL₂` components

For a subgroup `U` of `GL₂(𝔸_f)` and `g ∈ GL₂(𝔸_f)`, the group `Γ_{g,U} = GL₂(ℚ)^+ ∩ gUg⁻¹`
(`TauCeti.AdelicExamples.GL2.componentGroup`) acts on the upper half-plane `ℍ` through
`GL₂(ℚ)^+ → PSL₂(ℝ)` (`TauCeti.ratPosToPSL2R`). Its image in `PSL₂(ℝ)` is
`TauCeti.AdelicExamples.GL2.componentGroupPSL U g`, and the component of the adelic quotient
through `g` is the coarse quotient `Γ_{g,U}\ℍ` of `ℍ` by that image.

For `q ∈ GL₂(ℚ)` with `det q > 0` and `u ∈ U`, `Γ_{qgu,U} = qΓ_{g,U}q⁻¹`
(`TauCeti.AdelicExamples.GL2.componentGroup_mul_mul`), so the images in `PSL₂(ℝ)` are conjugate
by the image of `q` (`TauCeti.AdelicExamples.GL2.conjAct_smul_componentGroupPSL`). Hence
`z ↦ q • z` descends to a homeomorphism `Γ_{g,U}\ℍ ≃ₜ Γ_{qgu,U}\ℍ`
(`TauCeti.AdelicExamples.GL2.componentQuotientConjHomeomorph`), which is holomorphic when
`Γ_{g,U}` acts properly discontinuously on `ℍ`.

## Main definitions

* `TauCeti.AdelicExamples.GL2.componentGroupPSL U g`: the image of `Γ_{g,U}` in `PSL₂(ℝ)`.
* `TauCeti.AdelicExamples.GL2.componentQuotientConjHomeomorph`: the homeomorphism
  `Γ_{g,U}\ℍ ≃ₜ Γ_{qgu,U}\ℍ` induced by `z ↦ q • z`.

## Main results

* `TauCeti.AdelicExamples.GL2.componentGroupPSL_mono`: `U' ≤ U` gives an inclusion of images.
* `TauCeti.AdelicExamples.GL2.conjAct_smul_componentGroupPSL`: the image of `Γ_{qgu,U}` in
  `PSL₂(ℝ)` is the conjugate of that of `Γ_{g,U}` by the image of `q`.
* `TauCeti.AdelicExamples.GL2.componentQuotientConjHomeomorph_mk` and
  `TauCeti.AdelicExamples.GL2.componentQuotientConjHomeomorph_symm_mk`: the homeomorphism and
  its inverse act on orbits through `q` and `q⁻¹`.
* `TauCeti.AdelicExamples.GL2.mdifferentiable_componentQuotientConjHomeomorph`: the homeomorphism
  is holomorphic when `Γ_{g,U}` acts properly discontinuously.

## References

* J. S. Milne, *Introduction to Shimura varieties*, revision of 16 September 2017, Lemma 5.13
  with the remarks after it, pp. 57-58.
-/

public noncomputable section

open IsDedekindDomain Matrix MulAction UpperHalfPlane
open scoped MatrixGroups Pointwise Manifold

namespace TauCeti

namespace AdelicExamples.GL2

/-- The image of `Γ_{g,U} = GL₂(ℚ)^+ ∩ gUg⁻¹` in `PSL₂(ℝ)`, through which it acts on the upper
half-plane. -/
def componentGroupPSL (U : Subgroup (GL (Fin 2) (FiniteAdeleRing ℤ ℚ)))
    (g : GL (Fin 2) (FiniteAdeleRing ℤ ℚ)) : Subgroup PSL(2, ℝ) :=
  ((componentGroup U g).subgroupOf (GLPos (Fin 2) ℚ)).map ratPosToPSL2R

/-- Membership in the image of `Γ_{g,U}` in `PSL₂(ℝ)`. -/
@[simp]
theorem mem_componentGroupPSL_iff {U : Subgroup (GL (Fin 2) (FiniteAdeleRing ℤ ℚ))}
    {g : GL (Fin 2) (FiniteAdeleRing ℤ ℚ)} {x : PSL(2, ℝ)} :
    x ∈ componentGroupPSL U g ↔
      ∃ γ : GL(2, ℚ)⁺, (γ : GL (Fin 2) ℚ) ∈ componentGroup U g ∧ ratPosToPSL2R γ = x := by
  simp [componentGroupPSL, Subgroup.mem_map, Subgroup.mem_subgroupOf]

/-- Shrinking `U` shrinks the image of `Γ_{g,U}` in `PSL₂(ℝ)`. -/
theorem componentGroupPSL_mono {U U' : Subgroup (GL (Fin 2) (FiniteAdeleRing ℤ ℚ))} (h : U' ≤ U)
    (g : GL (Fin 2) (FiniteAdeleRing ℤ ℚ)) : componentGroupPSL U' g ≤ componentGroupPSL U g :=
  Subgroup.map_mono (Subgroup.subgroupOf_mono _ (componentGroup_mono h g))

/-- **The images of `Γ_{qgu,U}` and `Γ_{g,U}` in `PSL₂(ℝ)` are conjugate by the image of `q`**,
for `q ∈ GL₂(ℚ)^+` and `u ∈ U`. -/
theorem conjAct_smul_componentGroupPSL {U : Subgroup (GL (Fin 2) (FiniteAdeleRing ℤ ℚ))}
    (g : GL (Fin 2) (FiniteAdeleRing ℤ ℚ)) (q : GL(2, ℚ)⁺)
    {u : GL (Fin 2) (FiniteAdeleRing ℤ ℚ)} (hu : u ∈ U) :
    ConjAct.toConjAct (ratPosToPSL2R q) • componentGroupPSL U g =
      componentGroupPSL U (GeneralLinearGroup.map (algebraMap ℚ (FiniteAdeleRing ℤ ℚ))
        (q : GL (Fin 2) ℚ) * g * u) := by
  ext x
  rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, ConjAct.smul_def, ← map_inv,
    ConjAct.ofConjAct_toConjAct, mem_componentGroupPSL_iff, mem_componentGroupPSL_iff,
    componentGroup_mul_mul g (q : GL (Fin 2) ℚ) hu]
  constructor
  · rintro ⟨γ, hγ, hγx⟩
    refine ⟨q * γ * q⁻¹, ⟨γ, hγ, ?_⟩, ?_⟩
    · simp [MulAut.conj_apply]
    · rw [map_mul, map_mul, hγx, map_inv]
      group
  · rintro ⟨γ, ⟨δ, hδ, hδγ⟩, hγx⟩
    refine ⟨q⁻¹ * γ * q, ?_, ?_⟩
    · have hγ : (γ : GL (Fin 2) ℚ) = (q : GL (Fin 2) ℚ) * δ * (q : GL (Fin 2) ℚ)⁻¹ := by
        simpa [MulAut.conj_apply] using hδγ.symm
      simpa [hγ, mul_assoc] using hδ
    · rw [map_mul, map_mul, hγx, map_inv, inv_inv]

/-- **The quotients of conjugate components are homeomorphic.** For `q ∈ GL₂(ℚ)^+` and `u ∈ U`,
`z ↦ q • z` descends to a homeomorphism `Γ_{g,U}\ℍ ≃ₜ Γ_{qgu,U}\ℍ`. -/
def componentQuotientConjHomeomorph {U : Subgroup (GL (Fin 2) (FiniteAdeleRing ℤ ℚ))}
    (g : GL (Fin 2) (FiniteAdeleRing ℤ ℚ)) (q : GL(2, ℚ)⁺)
    {u : GL (Fin 2) (FiniteAdeleRing ℤ ℚ)} (hu : u ∈ U) :
    orbitRel.Quotient (componentGroupPSL U g) ℍ ≃ₜ
      orbitRel.Quotient (componentGroupPSL U (GeneralLinearGroup.map
        (algebraMap ℚ (FiniteAdeleRing ℤ ℚ)) (q : GL (Fin 2) ℚ) * g * u)) ℍ :=
  Subgroup.quotientConjHomeomorph (conjAct_smul_componentGroupPSL g q hu)

/-- The homeomorphism `Γ_{g,U}\ℍ ≃ₜ Γ_{qgu,U}\ℍ` sends the orbit of `z` to the orbit of `q • z`,
for the action of the real matrix `q`. -/
@[simp]
theorem componentQuotientConjHomeomorph_mk {U : Subgroup (GL (Fin 2) (FiniteAdeleRing ℤ ℚ))}
    (g : GL (Fin 2) (FiniteAdeleRing ℤ ℚ)) (q : GL(2, ℚ)⁺)
    {u : GL (Fin 2) (FiniteAdeleRing ℤ ℚ)} (hu : u ∈ U) (z : ℍ) :
    componentQuotientConjHomeomorph g q hu (Quotient.mk _ z) =
      Quotient.mk _ (GeneralLinearGroup.map (algebraMap ℚ ℝ) (q : GL (Fin 2) ℚ) • z) := by
  rw [componentQuotientConjHomeomorph, Subgroup.quotientConjHomeomorph_mk, ratPosToPSL2R_smul]

/-- The inverse of the homeomorphism `Γ_{g,U}\ℍ ≃ₜ Γ_{qgu,U}\ℍ` sends the orbit of `z` to the
orbit of `q⁻¹ • z`, for the action of the real matrix `q⁻¹`. -/
@[simp]
theorem componentQuotientConjHomeomorph_symm_mk
    {U : Subgroup (GL (Fin 2) (FiniteAdeleRing ℤ ℚ))} (g : GL (Fin 2) (FiniteAdeleRing ℤ ℚ))
    (q : GL(2, ℚ)⁺) {u : GL (Fin 2) (FiniteAdeleRing ℤ ℚ)} (hu : u ∈ U) (z : ℍ) :
    (componentQuotientConjHomeomorph g q hu).symm (Quotient.mk _ z) =
      Quotient.mk _ (GeneralLinearGroup.map (algebraMap ℚ ℝ) (q : GL (Fin 2) ℚ)⁻¹ • z) := by
  rw [componentQuotientConjHomeomorph, Subgroup.quotientConjHomeomorph_symm,
    Subgroup.quotientConjHomeomorph_mk, ← map_inv, ratPosToPSL2R_smul, Subgroup.coe_inv]

/-- **The homeomorphism `Γ_{g,U}\ℍ ≃ₜ Γ_{qgu,U}\ℍ` is holomorphic** when `Γ_{g,U}` acts properly
discontinuously on `ℍ`. Its inverse is induced by `q⁻¹`
(`TauCeti.AdelicExamples.GL2.componentQuotientConjHomeomorph_symm_mk`). -/
theorem mdifferentiable_componentQuotientConjHomeomorph
    {U : Subgroup (GL (Fin 2) (FiniteAdeleRing ℤ ℚ))} (g : GL (Fin 2) (FiniteAdeleRing ℤ ℚ))
    [ProperlyDiscontinuousSMul (componentGroupPSL U g) ℍ] (q : GL(2, ℚ)⁺)
    {u : GL (Fin 2) (FiniteAdeleRing ℤ ℚ)} (hu : u ∈ U) :
    letI := TauCeti.properlyDiscontinuousSMul_of_conjAct_smul_eq (X := ℍ)
      (conjAct_smul_componentGroupPSL g q hu)
    MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (componentQuotientConjHomeomorph g q hu) :=
  Subgroup.mdifferentiable_quotientConjHomeomorph _

end AdelicExamples.GL2

end TauCeti
