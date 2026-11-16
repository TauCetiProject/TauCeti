/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.DeRham.Torus
public import TauCeti.Geometry.Manifold.VectorBundle.Cotangent.Torus
public import TauCeti.Geometry.Symplectic.Cotangent.Bundle.Graph
public import TauCeti.Geometry.Symplectic.Hamiltonian.Manifold

import TauCeti.Geometry.Manifold.MFDeriv.NormedSpace
import TauCeti.Geometry.Manifold.MFDeriv.Pi

/-!
# Symplectic geometry of the cotangent bundle of a torus

For a finite family of positive periods `p i`, let `Tⁿ = ∀ i, AddCircle (p i)` be the torus with
coordinate time forms `dt_i` (`TauCeti.torusTimeForm p i`), and let `α_c = ∑ j, c j • dt_j` be the
closed one-form with constant coefficients `c : ι → ℝ`. This file records the basic symplectic
properties of the cotangent bundle `T*Tⁿ` with its canonical symplectic form `ω = -dλ`.

* The graph of `α_c` is a Lagrangian map for every `c`, since `α_c` is closed
  (`TauCeti.CotangentBundle.isLagrangianMap_section_sum_smul_torusTimeForm`).
* It is an exact Lagrangian map, for the primitive `λ` of `ω` and some primitive on the torus,
  exactly when `c = 0`, that is when it is the zero section
  (`TauCeti.CotangentBundle.exists_isExactLagrangianMap_section_sum_smul_torusTimeForm_iff`). This
  is because `α_c` integrates to `c i * p i` around the `i`-th coordinate circle.
* For `c ≠ 0` the graph of `α_c` meets the zero section nowhere
  (`TauCeti.CotangentBundle.section_sum_smul_torusTimeForm_eq_zeroSection_iff`): the form `α_c`
  vanishes at no point.
* In particular the graph of a single angle form `dt_i` is a Lagrangian section of `T*Tⁿ` that is
  not exact (`TauCeti.CotangentBundle.isLagrangianMap_section_torusTimeForm`,
  `TauCeti.CotangentBundle.not_exists_isExactLagrangianMap_section_torusTimeForm`), and by the last
  item it is disjoint from the zero section.
* Pulling `ω` back along the universal covering map `(θ, I) ↦ (([θᵢ]), ∑ i, I i • dθᵢ)`
  (`TauCeti.CotangentBundle.torusCoverMap`) gives the Darboux form `∑ i, dθᵢ ∧ dIᵢ`
  (`TauCeti.CotangentBundle.eval₂_symplecticForm_mfderiv_torusCoverMap`).
* A Hamiltonian `K ∘ I` depending only on the action coordinates `Iᵢ(z) = z.2 (Pi.single i 1)` has
  horizontal Hamiltonian vector field `(∂K/∂I, 0)`
  (`TauCeti.CotangentBundle.hamiltonianVectorField_torus_comp_action`), whose integral curves
  advance the angles linearly at constant frequencies while preserving the actions
  (`TauCeti.CotangentBundle.isMIntegralCurve_torus_comp_action`).

## References

* V. I. Arnold, *Mathematical Methods of Classical Mechanics*, 2nd ed., Graduate Texts in
  Mathematics 60, Springer, 1989, Sections 49–50.
* A. Cannas da Silva, *Lectures on Symplectic Geometry*, Lecture Notes in Mathematics 1764,
  Springer, 2001, Sections 3 and 18.4.
* D. McDuff, D. Salamon, *Introduction to Symplectic Topology*, 3rd ed., Oxford, 2017,
  Section 3.2.
-/

public section

noncomputable section

open Bundle
open scoped Manifold ContDiff

namespace TauCeti

namespace CotangentBundle

variable {ι : Type*} [Fintype ι] (p : ι → ℝ) [∀ i, Fact (0 < p i)]

/-- **The graph of a constant-coefficient angle form is Lagrangian.** For every `c : ι → ℝ`, the
section of the cotangent bundle of the torus defined by the closed one-form `∑ j, c j • dt_j` is a
Lagrangian map for the canonical symplectic form. -/
theorem isLagrangianMap_section_sum_smul_torusTimeForm (c : ι → ℝ) :
    (isSymplectic_symplecticForm (I := ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ))
        (M := ∀ i, AddCircle (p i))).isNondegenerate.IsLagrangianMap
      (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ))
      (fun x ↦ TotalSpace.mk' ((ι → ℝ) →L[ℝ] ℝ) x
        (SmoothForm.degreeOneEquiv (∑ j, c j • torusTimeForm p j) x)) := by
  exact (isLagrangianMap_section_iff _).2 (isClosed_sum_smul_torusTimeForm p c)

/-- **The graph of a constant-coefficient angle form is exact only when it is the zero section.**
The section of the cotangent bundle of the torus defined by `∑ j, c j • dt_j` is an exact
Lagrangian map, for the primitive `λ` of `ω = -dλ` and some primitive on the torus, if and only if
`c = 0`. -/
theorem exists_isExactLagrangianMap_section_sum_smul_torusTimeForm_iff (c : ι → ℝ) :
    (∃ h : (∀ i, AddCircle (p i)) → ℝ,
      (isSymplectic_symplecticForm (I := ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ))
          (M := ∀ i, AddCircle (p i))).isNondegenerate.IsExactLagrangianMap
        (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) (liouvilleForm _ _)
        (fun x ↦ TotalSpace.mk' ((ι → ℝ) →L[ℝ] ℝ) x
          (SmoothForm.degreeOneEquiv (∑ j, c j • torusTimeForm p j) x)) h) ↔
      c = 0 := by
  rw [exists_isExactLagrangianMap_section_iff, sum_smul_torusTimeForm_mem_exactForms_iff]

/-- **A nonzero constant-coefficient angle form has graph disjoint from the zero section.** At
every point `x` of the torus, the section of the cotangent bundle defined by `∑ j, c j • dt_j`
meets the zero section if and only if `c = 0`. -/
theorem section_sum_smul_torusTimeForm_eq_zeroSection_iff (c : ι → ℝ)
    (x : ∀ i, AddCircle (p i)) :
    TotalSpace.mk' ((ι → ℝ) →L[ℝ] ℝ) x
        (SmoothForm.degreeOneEquiv (∑ j, c j • torusTimeForm p j) x) =
      zeroSection ((ι → ℝ) →L[ℝ] ℝ)
        (fun y : ∀ i, AddCircle (p i) ↦
          TangentSpace (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) y →L[ℝ] ℝ) x ↔
      c = 0 := by
  classical
  rw [zeroSection, TotalSpace.mk_inj]
  refine ⟨fun h ↦ funext fun i ↦ ?_, fun h ↦ ?_⟩
  · -- The form sends every tangent vector `v` to `∑ j, c j * v j`; evaluate on the `i`-th
    -- coordinate vector.
    have hv (v : TangentSpace (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) x) :
        ∑ j, c j * v j = 0 := by
      have hx := SmoothForm.degreeOneEquiv_apply_apply (∑ j, c j • torusTimeForm p j) x v
      rw [h, sum_smul_torusTimeForm_apply, zero_apply] at hx
      exact hx.symm
    simpa [Pi.single_apply] using hv (Pi.single i 1)
  · ext v
    simp [h]

/-- **The graph of an angle form is Lagrangian.** The section of the cotangent bundle of the torus
defined by the coordinate time form `dt_i` is a Lagrangian map for the canonical symplectic form. -/
theorem isLagrangianMap_section_torusTimeForm (i : ι) :
    (isSymplectic_symplecticForm (I := ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ))
        (M := ∀ i, AddCircle (p i))).isNondegenerate.IsLagrangianMap
      (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ))
      (fun x ↦ TotalSpace.mk' ((ι → ℝ) →L[ℝ] ℝ) x
        (SmoothForm.degreeOneEquiv (torusTimeForm p i) x)) :=
  (isLagrangianMap_section_iff _).2 (isClosed_torusTimeForm p i)

/-- **The graph of an angle form is not exact.** The section of the cotangent bundle of the torus
defined by the coordinate time form `dt_i` is not an exact Lagrangian map for the primitive `λ` of
`ω = -dλ`, whatever primitive on the torus is chosen. -/
@[simp]
theorem not_exists_isExactLagrangianMap_section_torusTimeForm (i : ι) :
    ¬∃ h : (∀ i, AddCircle (p i)) → ℝ,
      (isSymplectic_symplecticForm (I := ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ))
          (M := ∀ i, AddCircle (p i))).isNondegenerate.IsExactLagrangianMap
        (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) (liouvilleForm _ _)
        (fun x ↦ TotalSpace.mk' ((ι → ℝ) →L[ℝ] ℝ) x
          (SmoothForm.degreeOneEquiv (torusTimeForm p i) x)) h := by
  rw [exists_isExactLagrangianMap_section_iff]
  exact torusTimeForm_notMem_exactForms p i

/-! ### Darboux form and action-only Hamiltonian flows on `T*Tⁿ` -/

/-- **Darboux formula on `T*Tⁿ`.** Pulling the canonical symplectic form of `T*Tⁿ` back along the
universal covering map `(θ, I) ↦ (([θᵢ]), ∑ i, I i • dθᵢ)` gives the standard coordinate form
`∑ i, dθᵢ ∧ dIᵢ`: evaluated on `(a, b)` and `(a', b')`, it equals
`∑ i, (a i * b' i - a' i * b i)`. -/
theorem eval₂_symplecticForm_mfderiv_torusCoverMap (w : (ι → ℝ) × (ι → ℝ))
    (a a' b b' : ι → ℝ) :
    SmoothBundleForm.eval₂
        (symplecticForm (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) (∀ i, AddCircle (p i)))
        (torusCoverMap p w)
        (mfderiv 𝓘(ℝ, (ι → ℝ) × (ι → ℝ))
          ((ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)).prod 𝓘(ℝ, (ι → ℝ) →L[ℝ] ℝ))
          (torusCoverMap p) w (a, b))
        (mfderiv 𝓘(ℝ, (ι → ℝ) × (ι → ℝ))
          ((ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)).prod 𝓘(ℝ, (ι → ℝ) →L[ℝ] ℝ))
          (torusCoverMap p) w (a', b')) =
      ∑ i, (a i * b' i - a' i * b i) := by
  rw [eval₂_symplecticForm, mfderiv_torusCoverMap_apply, mfderiv_torusCoverMap_apply,
    strongDualCotangentSymplecticForm_apply]
  simp only [sum_apply, smul_apply, ContinuousLinearMap.proj_apply, smul_eq_mul,
    ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ ↦ by ring

/-- **Hamiltonian vector field of a function of the actions on `T*Tⁿ`.** On the cotangent bundle of
a torus with its canonical symplectic form, a Hamiltonian `z ↦ K (fun i ↦ z.2 (Pi.single i 1))`
depending only on the action coordinates has horizontal Hamiltonian vector field `(ω(I), 0)`, where
`ωᵢ(I) = ∂K/∂Iᵢ = fderiv ℝ K I (Pi.single i 1)`. -/
theorem hamiltonianVectorField_torus_comp_action [DecidableEq ι] {K : (ι → ℝ) → ℝ}
    {z : CotangentBundle (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) (∀ i, AddCircle (p i))}
    (hK : DifferentiableAt ℝ K (fun i ↦ z.2 (Pi.single i 1))) :
    (symplecticForm (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ))
        (∀ i, AddCircle (p i))).hamiltonianVectorField
      (fun z ↦ K (fun i ↦ z.2 (Pi.single i 1))) z =
    (fun i ↦ fderiv ℝ K (fun j ↦ z.2 (Pi.single j 1)) (Pi.single i 1), 0) := by
  let I_T := ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)
  let I_C := I_T.prod 𝓘(ℝ, (ι → ℝ) →L[ℝ] ℝ)
  let act : CotangentBundle I_T (∀ i, AddCircle (p i)) → ι → ℝ :=
    fun w ↦ fun i ↦ w.2 (Pi.single i 1)
  let Ω : ι → ℝ := fun i ↦ fderiv ℝ K (act z) (Pi.single i 1)
  let X : TangentSpace I_C z := (Ω, 0)
  have hnondeg := (isSymplectic_symplecticForm (I := I_T)
    (M := ∀ i, AddCircle (p i))).isNondegenerate
  apply (hnondeg.isInvertible_flat z).injective
  rw [hnondeg.flat_hamiltonianVectorField]
  refine ContinuousLinearMap.ext fun v ↦ ?_
  change mvfderiv I_C (K ∘ act) z v =
    (symplecticForm I_T (∀ i, AddCircle (p i))).flat z X v
  rw [SmoothTwoForm.flat_apply, eval₂_symplecticForm]
  let η : StrongDual ℝ (ι → ℝ) := v.2
  change mvfderiv I_C (K ∘ act) z v =
    strongDualCotangentSymplecticForm (V := ι → ℝ) (Ω, 0) (v.1, η)
  rw [strongDualCotangentSymplecticForm_apply, zero_apply, sub_zero,
    mvfderiv_comp_apply_of_differentiableAt hK
      (hasMFDerivAt_torusActionCoord p z).mdifferentiableAt]
  have hact : mvfderiv I_C act z v = fun i ↦ η (Pi.single i 1) :=
    (mvfderiv_apply_eq_mfderiv_apply act z v).trans
      (funext fun i ↦ mfderiv_torusActionCoord_apply p z v i)
  change fderiv ℝ K (act z) (mvfderiv I_C act z v) = η Ω
  rw [hact]
  have hsingle (r : ℝ) (i : ι) :
      Pi.single (M := fun _ : ι ↦ ℝ) i r = r • Pi.single i 1 := by
    funext j
    by_cases hji : j = i <;> simp [hji]
  conv_lhs => rw [← Finset.univ_sum_single (fun i ↦ η (Pi.single i 1))]
  conv_rhs => rw [← Finset.univ_sum_single Ω]
  rw [map_sum, map_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [hsingle (η (Pi.single i 1)), hsingle (Ω i), map_smul, map_smul, smul_eq_mul, smul_eq_mul,
    mul_comm]

/-- **Linear flow of a function of the actions on `T*Tⁿ`.** On the cotangent bundle of a torus, for
a Hamiltonian `z ↦ K (fun i ↦ z.2 (Pi.single i 1))` depending only on the action coordinates, the
curve advancing the `i`-th angle at constant frequency `ωᵢ = ∂K/∂Iᵢ(I₀)` while keeping the action
`I₀` fixed is a global integral curve of the Hamiltonian vector field. -/
theorem isMIntegralCurve_torus_comp_action [DecidableEq ι] {K : (ι → ℝ) → ℝ}
    (z₀ : CotangentBundle (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) (∀ i, AddCircle (p i)))
    (hK : DifferentiableAt ℝ K (fun i ↦ z₀.2 (Pi.single i 1))) :
    IsMIntegralCurve
      (fun t : ℝ ↦ (TotalSpace.mk' ((ι → ℝ) →L[ℝ] ℝ)
        (fun i ↦ z₀.proj i +
          (t * fderiv ℝ K (fun j ↦ z₀.2 (Pi.single j 1)) (Pi.single i 1) : AddCircle (p i)))
        z₀.2 : CotangentBundle (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) (∀ i, AddCircle (p i))))
      ((symplecticForm (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ))
        (∀ i, AddCircle (p i))).hamiltonianVectorField
        (fun z ↦ K (fun i ↦ z.2 (Pi.single i 1)))) := by
  let I_T := ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)
  let I_C := I_T.prod 𝓘(ℝ, (ι → ℝ) →L[ℝ] ℝ)
  let Ω : ι → ℝ := fun i ↦ fderiv ℝ K (fun j ↦ z₀.2 (Pi.single j 1)) (Pi.single i 1)
  let c₀ : (ι → ℝ) →L[ℝ] ℝ := z₀.2
  let γ₀ : ℝ → (∀ i, AddCircle (p i)) × ((ι → ℝ) →L[ℝ] ℝ) :=
    fun t ↦ (fun i ↦ z₀.proj i + (t * Ω i : AddCircle (p i)), c₀)
  have hcomp :
      (fun s : ℝ ↦ (TotalSpace.mk' ((ι → ℝ) →L[ℝ] ℝ)
        (fun i ↦ z₀.proj i + (s * Ω i : AddCircle (p i))) z₀.2 :
        CotangentBundle I_T (∀ i, AddCircle (p i)))) =
      (torusTrivDiffeomorph p 1).symm ∘ γ₀ :=
    funext fun s ↦ (torusTrivDiffeomorph_symm_apply p 1 (γ₀ s)).symm
  intro t
  have hθ : HasMFDerivAt 𝓘(ℝ) I_T
      (fun s : ℝ ↦ fun i ↦ z₀.proj i + (s * Ω i : AddCircle (p i))) t
      (ContinuousLinearMap.pi fun i ↦ (1 : ℝ →L[ℝ] ℝ).smulRight (Ω i)) := by
    refine TauCeti.hasMFDerivAt_pi fun i ↦ ?_
    have hd : HasDerivAt (fun s : ℝ ↦ s * Ω i) (Ω i) t := by
      simpa using (hasDerivAt_id t).mul_const (Ω i)
    exact AddCircle.hasMFDerivAt_add_coe_comp hd (z₀.proj i)
  have hγ₀ : HasMFDerivAt 𝓘(ℝ) I_C γ₀ t
      ((ContinuousLinearMap.pi fun i ↦ (1 : ℝ →L[ℝ] ℝ).smulRight (Ω i)).prod
        (0 : ℝ →L[ℝ] ((ι → ℝ) →L[ℝ] ℝ))) :=
    hθ.prodMk (hasMFDerivAt_const (x := t) (c := c₀))
  have hγ : HasMFDerivAt 𝓘(ℝ) I_C ((torusTrivDiffeomorph p 1).symm ∘ γ₀) t
      ((ContinuousLinearMap.pi fun i ↦ (1 : ℝ →L[ℝ] ℝ).smulRight (Ω i)).prod
        (0 : ℝ →L[ℝ] ((ι → ℝ) →L[ℝ] ℝ))) :=
    ((hasMFDerivAt_torusTrivDiffeomorph_symm p 1 (γ₀ t)).comp t hγ₀).congr_mfderiv
      (ContinuousLinearMap.id_comp _)
  rw [← hcomp] at hγ
  refine hγ.congr_mfderiv ?_
  let zt : CotangentBundle I_T (∀ i, AddCircle (p i)) :=
    TotalSpace.mk' ((ι → ℝ) →L[ℝ] ℝ) (fun i ↦ z₀.proj i + (t * Ω i : AddCircle (p i))) c₀
  have hH : (symplecticForm I_T (∀ i, AddCircle (p i))).hamiltonianVectorField
      (fun z ↦ K (fun i ↦ z.2 (Pi.single i 1))) zt = (Ω, 0) :=
    hamiltonianVectorField_torus_comp_action p (z := zt) hK
  change _ = (1 : ℝ →L[ℝ] ℝ).smulRight
    ((symplecticForm I_T (∀ i, AddCircle (p i))).hamiltonianVectorField
      (fun z ↦ K (fun i ↦ z.2 (Pi.single i 1))) zt)
  rw [hH]
  refine ContinuousLinearMap.ext fun s ↦
    Prod.ext (funext fun i ↦ rfl) (ContinuousLinearMap.ext fun u ↦ ?_)
  let r : ℝ := s
  change (0 : ℝ) = r * 0
  ring

end CotangentBundle

end TauCeti
