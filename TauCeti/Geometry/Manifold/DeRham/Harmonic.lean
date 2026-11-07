/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Codifferential

/-!
# Harmonic forms and de Rham cohomology

On an oriented Riemannian manifold `M` of dimension `m`, the harmonic `k`-forms are the kernel of
the Hodge Laplacian `Δ = d*d + dd*`, and the coexact `k`-forms are the image of the
codifferential `d*` of `(k + 1)`-forms (zero in the top degree).

This file proves the orthogonality half of the Hodge decomposition, which uses only that `d*` is
the formal adjoint of `d`. On a boundaryless manifold closed forms are `L²`-orthogonal to coexact
forms, and coclosed forms to exact forms, for the pairing `∫_M ⟨α, β⟩ vol`. On a compact
boundaryless manifold, where harmonic forms are exactly the closed and coclosed forms,
definiteness of the pairing gives:

* closed forms meet coexact forms only in `0`, and harmonic forms meet exact forms only in `0`;
* the harmonic, exact and coexact forms are independent: `ℋ ⊔ B` is disjoint from `B*`;
* the closed forms in `ℋ ⊔ B ⊔ B*` are exactly `ℋ ⊔ B`;
* harmonic forms are closed, and sending a harmonic form to its de Rham class is injective, so
  each de Rham class has at most one harmonic representative.

The remaining analytic half of the Hodge theorem is that `ℋ ⊔ B ⊔ B*` is every smooth form; by
the identity for closed forms above it makes every closed form harmonic plus exact, so that the
map from harmonic forms to de Rham cohomology is also surjective.

## Main definitions

* `TauCeti.harmonicForms`: the harmonic `k`-forms, the kernel of the Hodge Laplacian.
* `TauCeti.coexactForms`: the coexact `k`-forms, the image of the codifferential.
* `TauCeti.harmonicForms.toDeRhamCohomology`: on a compact boundaryless manifold, the de Rham
  class of a harmonic form.

## Main results

* `TauCeti.SmoothForm.integralTopForm_inner_codifferential_eq_zero_of_mextDeriv_eq_zero`,
  `TauCeti.SmoothForm.integralTopForm_inner_mextDeriv_eq_zero_of_codifferential_eq_zero`: closed
  forms are orthogonal to coexact forms, and exact forms to coclosed forms.
* `TauCeti.mem_harmonicForms_add_one_iff`: on a compact boundaryless manifold a form is harmonic
  exactly when it is closed and coclosed.
* `TauCeti.disjoint_closedForms_coexactForms`, `TauCeti.disjoint_harmonicForms_exactForms`,
  `TauCeti.disjoint_harmonicForms_sup_exactForms_coexactForms`: the Hodge summands are
  independent.
* `TauCeti.closedForms_inf_sup_coexactForms`: `Z ⊓ (ℋ ⊔ B ⊔ B*) = ℋ ⊔ B`.
* `TauCeti.harmonicForms.toDeRhamCohomology_injective`: a harmonic form with exact de Rham class
  vanishes.

## References

* F. W. Warner, *Foundations of Differentiable Manifolds and Lie Groups*, Graduate Texts in
  Mathematics 94, Springer (1983), Chapter 6.
-/

public section

noncomputable section

open Bundle
open scoped Manifold ContDiff

namespace TauCeti

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [FiniteDimensional ℝ E] [IsManifold I ∞ M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
  {m k l : ℕ}

/-! ### Harmonic and coexact forms -/

/-- The harmonic `k`-forms on an oriented Riemannian manifold of dimension `m = k + l`: the
kernel of the Hodge Laplacian `Δ = d*d + dd*`. -/
def harmonicForms (o : Manifold.Orientation I M (Fin m)) (hkl : k + l = m) :
    Submodule ℝ (SmoothForm I M ℝ k) :=
  LinearMap.ker (SmoothForm.hodgeLaplacian o hkl)

/-- A form is harmonic precisely when its Hodge Laplacian vanishes. -/
@[simp]
theorem mem_harmonicForms (o : Manifold.Orientation I M (Fin m)) (hkl : k + l = m)
    (α : SmoothForm I M ℝ k) :
    α ∈ harmonicForms o hkl ↔ SmoothForm.hodgeLaplacian o hkl α = 0 :=
  LinearMap.mem_ker

/-- The harmonic forms do not depend on the orientation. -/
@[simp]
theorem harmonicForms_neg_orientation (o : Manifold.Orientation I M (Fin m)) (hkl : k + l = m) :
    harmonicForms (-o) hkl = harmonicForms o hkl := by
  ext α
  simp

/-- The coexact `k`-forms on an oriented Riemannian manifold of dimension `m = k + l`: the image
of the codifferential `d*` of `(k + 1)`-forms. They are zero in the top degree `k = m`. -/
def coexactForms (o : Manifold.Orientation I M (Fin m)) :
    ∀ {k l : ℕ}, k + l = m → Submodule ℝ (SmoothForm I M ℝ k)
  | _, 0, _ => ⊥
  | k, l + 1, hkl => LinearMap.range (SmoothForm.codifferential o (show k + 1 + l = m by omega))

/-- There are no nonzero coexact forms in the top degree. -/
@[simp]
theorem coexactForms_zero (o : Manifold.Orientation I M (Fin m)) (hkl : k + 0 = m) :
    coexactForms o hkl = ⊥ :=
  (rfl)

/-- Below the top degree, coexact forms are the range of the codifferential. -/
@[simp]
theorem coexactForms_add_one (o : Manifold.Orientation I M (Fin m)) (hkl : k + (l + 1) = m) :
    coexactForms o hkl =
      LinearMap.range (SmoothForm.codifferential o (by omega : k + 1 + l = m)) :=
  (rfl)

/-- Below the top degree, a form is coexact precisely when it is the codifferential of a
form. -/
theorem mem_coexactForms_add_one (o : Manifold.Orientation I M (Fin m)) (hkl : k + (l + 1) = m)
    (α : SmoothForm I M ℝ k) :
    α ∈ coexactForms o hkl ↔
      ∃ β, SmoothForm.codifferential o (by omega : k + 1 + l = m) β = α := by
  rw [coexactForms_add_one o hkl, LinearMap.mem_range]

/-- The coexact forms do not depend on the orientation. -/
@[simp]
theorem coexactForms_neg_orientation (o : Manifold.Orientation I M (Fin m)) (hkl : k + l = m) :
    coexactForms (-o) hkl = coexactForms o hkl := by
  rcases l with _ | l
  · simp
  · ext α
    simp

/-- **Coexact forms are coclosed**: since `d* ∘ d* = 0`, the codifferential of a coexact form
vanishes. -/
theorem codifferential_eq_zero_of_mem_coexactForms (o : Manifold.Orientation I M (Fin m))
    (hkl : k + 1 + l = m) {φ : SmoothForm I M ℝ (k + 1)} (hφ : φ ∈ coexactForms o hkl) :
    SmoothForm.codifferential o hkl φ = 0 := by
  rcases l with _ | l
  · simp_all
  · obtain ⟨β, rfl⟩ := (mem_coexactForms_add_one o hkl φ).1 hφ
    exact SmoothForm.codifferential_codifferential o hkl _ β

/-! ### Orthogonality -/

namespace SmoothForm

variable [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

/-- **Closed forms are orthogonal to coexact forms**: on an oriented boundaryless Riemannian
manifold, if `dα = 0` then `∫_M ⟨α, d*β⟩ vol = 0`, when `α` or `β` is compactly supported. -/
theorem integralTopForm_inner_codifferential_eq_zero_of_mextDeriv_eq_zero
    (o : Manifold.Orientation I M (Fin m)) (hkl : k + 1 + l = m) {α : SmoothForm I M ℝ k}
    (hα : mextDerivₗ I k α = 0) (β : SmoothForm I M ℝ (k + 1))
    (h : α ∈ compactlySupportedForms I M k ∨ β ∈ compactlySupportedForms I M (k + 1)) :
    integralTopForm o (fun x ↦ alternatingFormInner (TangentSpace I x) k
      (α.1 x) ((codifferential o hkl β).1 x) • riemannianVolumeForm o x) = 0 := by
  rw [← integralTopForm_inner_mextDeriv_eq_inner_codifferential o hkl α β h, hα]
  simp only [ZeroMemClass.coe_zero, Pi.zero_apply, LinearMap.map_zero₂, zero_smul]
  exact integralTopForm_zero o

/-- **Coclosed forms are orthogonal to exact forms**: on an oriented boundaryless Riemannian
manifold, if `d*β = 0` then `∫_M ⟨dα, β⟩ vol = 0`, when `α` or `β` is compactly supported. -/
theorem integralTopForm_inner_mextDeriv_eq_zero_of_codifferential_eq_zero
    (o : Manifold.Orientation I M (Fin m)) (hkl : k + 1 + l = m) (α : SmoothForm I M ℝ k)
    {β : SmoothForm I M ℝ (k + 1)} (hβ : codifferential o hkl β = 0)
    (h : α ∈ compactlySupportedForms I M k ∨ β ∈ compactlySupportedForms I M (k + 1)) :
    integralTopForm o (fun x ↦ alternatingFormInner (TangentSpace I x) (k + 1)
      ((mextDerivₗ I k α).1 x) (β.1 x) • riemannianVolumeForm o x) = 0 := by
  rw [integralTopForm_inner_mextDeriv_eq_inner_codifferential o hkl α β h, hβ]
  simp only [ZeroMemClass.coe_zero, Pi.zero_apply, map_zero, zero_smul]
  exact integralTopForm_zero o

end SmoothForm

/-! ### The Hodge summands on a compact manifold -/

section Compact

variable [BoundarylessManifold I M] [T2Space M] [CompactSpace M]

/-- **Harmonic forms are closed and coclosed**: on a compact oriented boundaryless Riemannian
manifold, a `(k + 1)`-form is harmonic exactly when `dα = 0` and `d*α = 0`. -/
theorem mem_harmonicForms_add_one_iff (o : Manifold.Orientation I M (Fin m))
    (hkl : k + 1 + l = m) (α : SmoothForm I M ℝ (k + 1)) :
    α ∈ harmonicForms o hkl ↔
      mextDerivₗ I (k + 1) α = 0 ∧ SmoothForm.codifferential o hkl α = 0 := by
  rw [mem_harmonicForms, SmoothForm.hodgeLaplacian_eq_zero_iff o hkl
    (by simp [compactlySupportedForms_eq_top])]

/-- **Harmonic functions are locally constant**: on a compact oriented boundaryless Riemannian
manifold, a function is harmonic exactly when its differential vanishes. -/
theorem mem_harmonicForms_zero_iff (o : Manifold.Orientation I M (Fin m)) (hl : 0 + l = m)
    (f : SmoothForm I M ℝ 0) :
    f ∈ harmonicForms o hl ↔ mextDerivₗ I 0 f = 0 := by
  rw [mem_harmonicForms, SmoothForm.hodgeLaplacian_eq_zero_iff_mextDeriv_eq_zero o hl
    (by simp [compactlySupportedForms_eq_top])]

/-- On a compact oriented boundaryless Riemannian manifold, harmonic forms are closed. -/
theorem harmonicForms_le_closedForms (o : Manifold.Orientation I M (Fin m)) (hkl : k + l = m) :
    harmonicForms o hkl ≤ closedForms I M k := by
  intro α hα
  rw [mem_closedForms_iff_mextDerivₗ_eq_zero]
  rcases k with _ | k
  · exact (mem_harmonicForms_zero_iff o hkl α).1 hα
  · exact ((mem_harmonicForms_add_one_iff o hkl α).1 hα).1

/-- On a compact oriented boundaryless Riemannian manifold, harmonic `(k + 1)`-forms are
coclosed. -/
theorem codifferential_eq_zero_of_mem_harmonicForms (o : Manifold.Orientation I M (Fin m))
    (hkl : k + 1 + l = m) {α : SmoothForm I M ℝ (k + 1)} (hα : α ∈ harmonicForms o hkl) :
    SmoothForm.codifferential o hkl α = 0 :=
  ((mem_harmonicForms_add_one_iff o hkl α).1 hα).2

/-- **A closed coexact form vanishes**: on a compact oriented boundaryless Riemannian manifold,
closed and coexact forms meet only in `0`. -/
theorem disjoint_closedForms_coexactForms (o : Manifold.Orientation I M (Fin m))
    (hkl : k + l = m) : Disjoint (closedForms I M k) (coexactForms o hkl) := by
  rcases l with _ | l
  · simp
  have : NeZero m := ⟨by omega⟩
  have hkl' : k + 1 + l = m := by omega
  rw [Submodule.disjoint_def]
  rintro φ hφ hφ'
  obtain ⟨β, rfl⟩ := (mem_coexactForms_add_one o hkl φ).1 hφ'
  -- `∫ |d*β|² vol = ∫ ⟨d*β, d*β⟩ vol` vanishes since `d*β` is closed, and the pairing is definite.
  refine (SmoothForm.integralTopForm_inner_self_smul_riemannianVolumeForm_eq_zero_iff o hkl
    (by simp [compactlySupportedForms_eq_top])).1 ?_
  exact SmoothForm.integralTopForm_inner_codifferential_eq_zero_of_mextDeriv_eq_zero o hkl'
    ((mem_closedForms_iff_mextDerivₗ_eq_zero I _).1 hφ) β
    (.inr (by simp [compactlySupportedForms_eq_top]))

/-- **A coclosed exact form vanishes**: on a compact oriented boundaryless Riemannian manifold,
an exact `(k + 1)`-form `φ` with `d*φ = 0` is zero. -/
theorem eq_zero_of_mem_exactForms_of_codifferential_eq_zero
    (o : Manifold.Orientation I M (Fin m)) (hkl : k + 1 + l = m) {φ : SmoothForm I M ℝ (k + 1)}
    (hφ : φ ∈ exactForms I M (k + 1)) (hφ' : SmoothForm.codifferential o hkl φ = 0) : φ = 0 := by
  have : NeZero m := ⟨by omega⟩
  rw [exactForms_succ, LinearMap.mem_range] at hφ
  obtain ⟨α, rfl⟩ := hφ
  -- `∫ |dα|² vol = ∫ ⟨dα, dα⟩ vol` vanishes since `dα` is coclosed, and the pairing is definite.
  refine (SmoothForm.integralTopForm_inner_self_smul_riemannianVolumeForm_eq_zero_iff o hkl
    (by simp [compactlySupportedForms_eq_top])).1 ?_
  exact SmoothForm.integralTopForm_inner_mextDeriv_eq_zero_of_codifferential_eq_zero o hkl α hφ'
    (.inl (by simp [compactlySupportedForms_eq_top]))

/-- **A harmonic exact form vanishes**: on a compact oriented boundaryless Riemannian manifold,
harmonic and exact forms meet only in `0`. -/
theorem disjoint_harmonicForms_exactForms (o : Manifold.Orientation I M (Fin m))
    (hkl : k + l = m) : Disjoint (harmonicForms o hkl) (exactForms I M k) := by
  rcases k with _ | k
  · simp
  rw [Submodule.disjoint_def]
  exact fun φ hφ hφ' ↦ eq_zero_of_mem_exactForms_of_codifferential_eq_zero o hkl hφ'
    (codifferential_eq_zero_of_mem_harmonicForms o hkl hφ)

/-- **The Hodge summands are independent**: on a compact oriented boundaryless Riemannian
manifold, the sum of the harmonic and exact forms meets the coexact forms only in `0`. Together
with `TauCeti.disjoint_harmonicForms_exactForms` this makes the sum `ℋ ⊔ B ⊔ B*` direct. -/
theorem disjoint_harmonicForms_sup_exactForms_coexactForms
    (o : Manifold.Orientation I M (Fin m)) (hkl : k + l = m) :
    Disjoint (harmonicForms o hkl ⊔ exactForms I M k) (coexactForms o hkl) :=
  (disjoint_closedForms_coexactForms o hkl).mono_left
    (sup_le (harmonicForms_le_closedForms o hkl) (exactForms_le_closedForms I k))

/-- **The closed part of the Hodge sum**: on a compact oriented boundaryless Riemannian manifold,
the closed forms in `ℋ ⊔ B ⊔ B*` are exactly `ℋ ⊔ B`. Thus once every form lies in `ℋ ⊔ B ⊔ B*`,
every closed form is a harmonic form plus an exact form. -/
theorem closedForms_inf_sup_coexactForms (o : Manifold.Orientation I M (Fin m))
    (hkl : k + l = m) :
    closedForms I M k ⊓ (harmonicForms o hkl ⊔ exactForms I M k ⊔ coexactForms o hkl) =
      harmonicForms o hkl ⊔ exactForms I M k := by
  rw [inf_comm, sup_inf_assoc_of_le _
      (sup_le (harmonicForms_le_closedForms o hkl) (exactForms_le_closedForms I k)),
    inf_comm, (disjoint_closedForms_coexactForms o hkl).eq_bot, sup_bot_eq]

/-! ### Harmonic representatives of de Rham classes -/

/-- The de Rham class of a harmonic form on a compact oriented boundaryless Riemannian
manifold. -/
def harmonicForms.toDeRhamCohomology (o : Manifold.Orientation I M (Fin m)) (hkl : k + l = m) :
    harmonicForms o hkl →ₗ[ℝ] deRhamCohomology I M k :=
  deRhamCohomology.mk I k ∘ₗ Submodule.inclusion (harmonicForms_le_closedForms o hkl)

/-- A harmonic form is sent to the de Rham class of the underlying closed form. -/
@[simp]
theorem harmonicForms.toDeRhamCohomology_apply (o : Manifold.Orientation I M (Fin m))
    (hkl : k + l = m) (α : harmonicForms o hkl) :
    harmonicForms.toDeRhamCohomology o hkl α =
      deRhamCohomology.mk I k ⟨α.1, harmonicForms_le_closedForms o hkl α.2⟩ :=
  (rfl)

/-- **Harmonic representatives are unique**: on a compact oriented boundaryless Riemannian
manifold, a harmonic form whose de Rham class vanishes is zero, so the de Rham class map on
harmonic forms is injective. -/
theorem harmonicForms.toDeRhamCohomology_injective (o : Manifold.Orientation I M (Fin m))
    (hkl : k + l = m) : Function.Injective (harmonicForms.toDeRhamCohomology o hkl) := by
  -- The difference of two harmonic forms with the same class is harmonic and exact.
  intro α β h
  rw [harmonicForms.toDeRhamCohomology_apply, harmonicForms.toDeRhamCohomology_apply,
    ← sub_eq_zero, ← map_sub, deRhamCohomology.mk_eq_zero_iff] at h
  exact Subtype.ext (sub_eq_zero.1 (Submodule.disjoint_def.1
    (disjoint_harmonicForms_exactForms o hkl) _ (sub_mem α.2 β.2) h))

end Compact

end TauCeti
