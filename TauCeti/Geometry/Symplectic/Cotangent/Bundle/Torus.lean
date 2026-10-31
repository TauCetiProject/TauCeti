/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.DeRham.Torus
public import TauCeti.Geometry.Symplectic.Cotangent.Bundle.Graph

/-!
# Lagrangian sections of the cotangent bundle of a torus

For a finite family of positive periods `p i`, let `Tⁿ = ∀ i, AddCircle (p i)` be the torus with
coordinate time forms `dt_i` (`TauCeti.torusTimeForm p i`), and let `α_c = ∑ j, c j • dt_j` be the
closed one-form with constant coefficients `c : ι → ℝ`. This file records the basic examples of
Lagrangian sections of the cotangent bundle `T*Tⁿ` with its canonical symplectic form `ω = -dλ`.

* The graph of `α_c` is a Lagrangian map for every `c`, since `α_c` is closed
  (`TauCeti.CotangentBundle.isLagrangianMap_section_sum_smul_torusTimeForm`).
* It is an exact Lagrangian map, for the primitive `λ` of `ω` and some primitive on the torus,
  exactly when `c = 0`, that is when it is the zero section
  (`TauCeti.CotangentBundle.exists_isExactLagrangianMap_section_sum_smul_torusTimeForm_iff`). This
  is because `α_c` integrates to `c i * p i` around the `i`-th coordinate circle.
* For `c ≠ 0` the graph of `α_c` meets the zero section nowhere
  (`TauCeti.CotangentBundle.section_sum_smul_torusTimeForm_eq_zeroSection_iff`): the form `α_c`
  vanishes at no point.

In particular the graph of a single angle form `dt_i` is a Lagrangian section of `T*Tⁿ` that is not
exact (`TauCeti.CotangentBundle.isLagrangianMap_section_torusTimeForm`,
`TauCeti.CotangentBundle.not_exists_isExactLagrangianMap_section_torusTimeForm`), and by the last
item it is disjoint from the zero section.

## References

* A. Cannas da Silva, *Lectures on Symplectic Geometry*, Lecture Notes in Mathematics 1764,
  Springer, 2001, Section 3.
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
  refine (isLagrangianMap_section_iff _).2 ((SmoothForm.isClosed_def _).2 ?_)
  rw [← mem_closedForms]
  exact Submodule.sum_mem _ fun j _ ↦ Submodule.smul_mem _ _
    ((mem_closedForms _ _).2 ((SmoothForm.isClosed_def _).1 (isClosed_torusTimeForm p j)))

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

end CotangentBundle

end TauCeti
