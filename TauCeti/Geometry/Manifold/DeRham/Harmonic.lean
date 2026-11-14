/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.DeRham.DegreeZero
public import TauCeti.Geometry.Manifold.DeRham.Integration.Bijective
public import TauCeti.Geometry.Manifold.Riemannian.Codifferential
public import TauCeti.Geometry.Manifold.Riemannian.VolumeForm.Measure
import TauCeti.Geometry.Manifold.DifferentialForm.Integration.Regularity

/-!
# Harmonic forms and de Rham cohomology

On an oriented Riemannian manifold `M` of dimension `m`, the harmonic `k`-forms are the kernel of
the Hodge Laplacian `Δ = d*d + dd*`, and the coexact `k`-forms are the image of the
codifferential `d*` of `(k + 1)`-forms (zero in the top degree).

This file proves the orthogonality half of the Hodge decomposition, which uses only that `d*` is
the formal adjoint of `d`. On a boundaryless manifold a closed form `α` is `L²`-orthogonal to a
coexact form `d*β`, and a coclosed form `β` to an exact form `dα`, for the pairing
`∫_M ⟨α, β⟩ vol`, provided `α` or `β` is compactly supported. On a compact
boundaryless manifold, where harmonic forms are exactly the closed and coclosed forms,
definiteness of the pairing gives:

* closed forms meet coexact forms only in `0`, and harmonic forms meet exact forms only in `0`;
* the harmonic, exact and coexact forms are independent: `ℋ ⊔ B` is disjoint from `B*`;
* the closed forms in `ℋ ⊔ B ⊔ B*` are exactly `ℋ ⊔ B`;
* harmonic forms are closed, and sending a harmonic form to its de Rham class is injective, so
  each de Rham class has at most one harmonic representative.

Since the Hodge star commutes with the Hodge Laplacian, it maps harmonic `k`-forms isomorphically
onto harmonic `(m - k)`-forms. In the two extreme degrees this gives the Hodge theorem without any
elliptic theory. Harmonic functions are the closed `0`-forms, that is the locally constant
functions, so every degree-zero class has exactly one harmonic representative. Harmonic `m`-forms
are the stars `f vol` of locally constant functions `f`. On a preconnected manifold a top form
whose integral vanishes is exact, so the class of a top form `φ` is represented by `c vol`, where
`c` is the integral of `φ` divided by the total volume; thus every top-degree class has exactly one
harmonic representative, and on a connected manifold these form a line.

The remaining analytic half of the Hodge theorem in the intermediate degrees is that
`ℋ ⊔ B ⊔ B*` is every smooth form; by the identity for closed forms above it makes every closed
form harmonic plus exact, so that the map from harmonic forms to de Rham cohomology is also
surjective.

## Main definitions

* `TauCeti.harmonicForms`: the harmonic `k`-forms, the kernel of the Hodge Laplacian.
* `TauCeti.coexactForms`: the coexact `k`-forms, the image of the codifferential.
* `TauCeti.harmonicForms.toDeRhamCohomology`: on a compact boundaryless manifold, the de Rham
  class of a harmonic form.
* `TauCeti.harmonicForms.hodgeStar`: the Hodge star as an isomorphism of harmonic forms.
* `TauCeti.harmonicFormsZeroEquiv`, `TauCeti.harmonicFormsTopEquiv`: on a compact boundaryless
  manifold, harmonic functions and harmonic top forms are the locally constant functions.

## Main results

* `TauCeti.SmoothForm.integralTopForm_inner_codifferential_eq_zero_of_mextDeriv_eq_zero`,
  `TauCeti.SmoothForm.integralTopForm_inner_mextDeriv_eq_zero_of_codifferential_eq_zero`: closed
  forms are orthogonal to coexact forms, and exact forms to coclosed forms, when one of the forms
  or the chosen primitive is compactly supported.
* `TauCeti.mem_harmonicForms_add_one_iff`: on a compact boundaryless manifold a form is harmonic
  exactly when it is closed and coclosed.
* `TauCeti.disjoint_closedForms_coexactForms`, `TauCeti.disjoint_harmonicForms_exactForms`,
  `TauCeti.disjoint_harmonicForms_sup_exactForms_coexactForms`: the Hodge summands are
  independent.
* `TauCeti.closedForms_inf_sup_coexactForms`: `Z ⊓ (ℋ ⊔ B ⊔ B*) = ℋ ⊔ B`.
* `TauCeti.harmonicForms.toDeRhamCohomology_injective`: a harmonic form with exact de Rham class
  vanishes.
* `TauCeti.hodgeStar_mem_harmonicForms_iff`: a form is harmonic exactly when its Hodge star is.
* `TauCeti.harmonicForms.toDeRhamCohomology_bijective_zero`: the Hodge theorem in degree zero.
* `TauCeti.mem_harmonicForms_top_iff`, `TauCeti.mem_harmonicForms_top_iff_of_preconnectedSpace`:
  harmonic top forms are the locally constant multiples of the volume form.
* `TauCeti.harmonicForms.toDeRhamCohomology_bijective_top`: the Hodge theorem in the top degree,
  on a compact preconnected manifold.
* `TauCeti.finrank_harmonicForms_top`: on a compact connected manifold the harmonic top forms
  form a line.

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

/-- **The Hodge star preserves harmonic forms**: since `⋆Δ = Δ⋆`, the Hodge star of a harmonic
`k`-form on an oriented Riemannian manifold of dimension `m = k + l` is a harmonic `l`-form. -/
theorem hodgeStar_mem_harmonicForms (o : Manifold.Orientation I M (Fin m)) (hkl : k + l = m)
    (hlk : l + k = m) {α : SmoothForm I M ℝ k} (hα : α ∈ harmonicForms o hkl) :
    SmoothForm.hodgeStar o hkl α ∈ harmonicForms o hlk := by
  rw [mem_harmonicForms] at hα ⊢
  rw [← SmoothForm.hodgeStar_hodgeLaplacian, hα, map_zero]

/-- A form is harmonic exactly when its Hodge star is harmonic. -/
theorem hodgeStar_mem_harmonicForms_iff (o : Manifold.Orientation I M (Fin m)) (hkl : k + l = m)
    (hlk : l + k = m) (α : SmoothForm I M ℝ k) :
    SmoothForm.hodgeStar o hkl α ∈ harmonicForms o hlk ↔ α ∈ harmonicForms o hkl := by
  refine ⟨fun h ↦ ?_, hodgeStar_mem_harmonicForms o hkl hlk⟩
  -- `α = (-1) ^ (k l) ⋆⋆α`.
  have h' := (harmonicForms o hkl).smul_mem ((-1 : ℝ) ^ (k * l))
    (hodgeStar_mem_harmonicForms o hlk hkl h)
  rwa [SmoothForm.hodgeStar_hodgeStar, smul_smul, ← mul_pow, neg_one_mul, neg_neg, one_pow,
    one_smul] at h'

/-- **The Hodge star on harmonic forms**: on an oriented Riemannian manifold of dimension
`m = k + l`, the Hodge star is a linear isomorphism from the harmonic `k`-forms onto the harmonic
`l`-forms, with inverse `(-1) ^ (k l) ⋆`. -/
def harmonicForms.hodgeStar (o : Manifold.Orientation I M (Fin m)) (hkl : k + l = m)
    (hlk : l + k = m) : harmonicForms o hkl ≃ₗ[ℝ] harmonicForms o hlk where
  toFun α := ⟨SmoothForm.hodgeStar o hkl α, hodgeStar_mem_harmonicForms o hkl hlk α.2⟩
  map_add' α β := Subtype.ext (map_add _ α.1 β.1)
  map_smul' c α := Subtype.ext (map_smul _ c α.1)
  invFun β := (-1 : ℝ) ^ (k * l) •
    ⟨SmoothForm.hodgeStar o hlk β, hodgeStar_mem_harmonicForms o hlk hkl β.2⟩
  left_inv α := Subtype.ext <| by
    simp only [SetLike.val_smul, SmoothForm.hodgeStar_hodgeStar, smul_smul, ← mul_pow,
      neg_one_mul, neg_neg, one_pow, one_smul]
  right_inv β := Subtype.ext <| by
    simp only [SetLike.val_smul, map_smul, SmoothForm.hodgeStar_hodgeStar, smul_smul, ← mul_pow,
      mul_comm l k, neg_one_mul, neg_neg, one_pow, one_smul]

/-- The Hodge star of a harmonic form is the Hodge star of the underlying form. -/
@[simp]
theorem harmonicForms.coe_hodgeStar_apply (o : Manifold.Orientation I M (Fin m))
    (hkl : k + l = m) (hlk : l + k = m) (α : harmonicForms o hkl) :
    (harmonicForms.hodgeStar o hkl hlk α : SmoothForm I M ℝ l) = SmoothForm.hodgeStar o hkl α :=
  (rfl)

/-- The inverse of the Hodge star on harmonic forms is `(-1) ^ (k l) ⋆`. -/
@[simp]
theorem harmonicForms.coe_hodgeStar_symm_apply (o : Manifold.Orientation I M (Fin m))
    (hkl : k + l = m) (hlk : l + k = m) (β : harmonicForms o hlk) :
    ((harmonicForms.hodgeStar o hkl hlk).symm β : SmoothForm I M ℝ k) =
      (-1 : ℝ) ^ (k * l) • SmoothForm.hodgeStar o hlk β :=
  (rfl)

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

/-! ### The Hodge theorem in degree zero -/

/-- On a compact oriented boundaryless Riemannian manifold, the harmonic functions are exactly the
closed `0`-forms. -/
theorem harmonicForms_zero_eq_closedForms (o : Manifold.Orientation I M (Fin m))
    (hl : 0 + l = m) : harmonicForms o hl = closedForms I M 0 := by
  ext f
  rw [mem_harmonicForms_zero_iff, mem_closedForms_iff_mextDerivₗ_eq_zero]

/-- **The Hodge theorem in degree zero**: on a compact oriented boundaryless Riemannian manifold,
every degree-zero de Rham class has exactly one harmonic representative. -/
theorem harmonicForms.toDeRhamCohomology_bijective_zero (o : Manifold.Orientation I M (Fin m))
    (hl : 0 + l = m) : Function.Bijective (harmonicForms.toDeRhamCohomology o hl) := by
  refine ⟨harmonicForms.toDeRhamCohomology_injective o hl, fun c ↦ ?_⟩
  obtain ⟨φ, rfl⟩ := deRhamCohomology.mk_surjective I 0 c
  exact ⟨⟨φ.1, (harmonicForms_zero_eq_closedForms o hl).ge φ.2⟩,
    harmonicForms.toDeRhamCohomology_apply o hl _⟩

/-- **Harmonic functions are the locally constant functions**: on a compact oriented boundaryless
Riemannian manifold, the harmonic functions form the space of locally constant real functions. -/
def harmonicFormsZeroEquiv (o : Manifold.Orientation I M (Fin m)) (hl : 0 + l = m) :
    harmonicForms o hl ≃ₗ[ℝ] LocallyConstant M ℝ :=
  LinearEquiv.ofEq _ _ (harmonicForms_zero_eq_closedForms o hl) ≪≫ₗ closedFormsZeroEquiv I M

/-- The locally constant function of a harmonic function is its value on the empty tuple. -/
@[simp]
theorem harmonicFormsZeroEquiv_apply (o : Manifold.Orientation I M (Fin m)) (hl : 0 + l = m)
    (f : harmonicForms o hl) (x : M) : harmonicFormsZeroEquiv o hl f x = f.1.1 x 0 :=
  closedFormsZeroEquiv_apply I _ x

/-- The harmonic function of a locally constant function is its `0`-form. -/
@[simp]
theorem coe_harmonicFormsZeroEquiv_symm_apply (o : Manifold.Orientation I M (Fin m))
    (hl : 0 + l = m) (f : LocallyConstant M ℝ) :
    ((harmonicFormsZeroEquiv o hl).symm f).1.1 = RoughForm.ofFunction I f :=
  coe_closedFormsZeroEquiv_symm_apply I f

/-! ### The Hodge theorem in the top degree -/

/-- **Harmonic top forms**: on a compact oriented boundaryless Riemannian manifold of dimension
`m`, the Hodge star identifies the harmonic `m`-forms with the locally constant real functions;
the inverse sends `f` to `f vol`. -/
def harmonicFormsTopEquiv (o : Manifold.Orientation I M (Fin m)) (hm : m + 0 = m) :
    harmonicForms o hm ≃ₗ[ℝ] LocallyConstant M ℝ :=
  harmonicForms.hodgeStar o hm (Nat.zero_add m) ≪≫ₗ harmonicFormsZeroEquiv o (Nat.zero_add m)

/-- The locally constant function of a harmonic top form `α` is `⋆α`. -/
@[simp]
theorem harmonicFormsTopEquiv_apply (o : Manifold.Orientation I M (Fin m)) (hm : m + 0 = m)
    (α : harmonicForms o hm) (x : M) :
    harmonicFormsTopEquiv o hm α x = (SmoothForm.hodgeStar o hm α.1).1 x 0 :=
  harmonicFormsZeroEquiv_apply o _ _ x

/-- The harmonic top form of a locally constant function `f` is `f vol`. -/
@[simp]
theorem coe_harmonicFormsTopEquiv_symm_apply (o : Manifold.Orientation I M (Fin m))
    (hm : m + 0 = m) (f : LocallyConstant M ℝ) :
    ((harmonicFormsTopEquiv o hm).symm f).1.1 = fun x ↦ f x • riemannianVolumeForm o x := by
  rw [harmonicFormsTopEquiv, LinearEquiv.symm_trans_apply,
    harmonicForms.coe_hodgeStar_symm_apply, Nat.mul_zero, pow_zero, one_smul,
    SmoothForm.coe_hodgeStar, coe_harmonicFormsZeroEquiv_symm_apply,
    RoughForm.hodgeStar_ofFunction]

/-- **Harmonic top forms are the locally constant multiples of the volume form**: on a compact
oriented boundaryless Riemannian manifold of dimension `m`, an `m`-form is harmonic exactly when it
is `f vol` for a locally constant function `f`. -/
theorem mem_harmonicForms_top_iff (o : Manifold.Orientation I M (Fin m)) (hm : m + 0 = m)
    (α : SmoothForm I M ℝ m) :
    α ∈ harmonicForms o hm ↔
      ∃ f : LocallyConstant M ℝ, α.1 = fun x ↦ f x • riemannianVolumeForm o x := by
  refine ⟨fun hα ↦ ⟨harmonicFormsTopEquiv o hm ⟨α, hα⟩, ?_⟩, fun ⟨f, hf⟩ ↦ ?_⟩
  · rw [← coe_harmonicFormsTopEquiv_symm_apply o hm, LinearEquiv.symm_apply_apply]
  · rw [← coe_harmonicFormsTopEquiv_symm_apply o hm f] at hf
    exact (Subtype.ext hf : α = _) ▸ ((harmonicFormsTopEquiv o hm).symm f).2

/-- **Harmonic top forms on a preconnected manifold**: on a compact preconnected oriented
boundaryless Riemannian manifold of dimension `m`, an `m`-form is harmonic exactly when it is a
constant multiple of the volume form. -/
theorem mem_harmonicForms_top_iff_of_preconnectedSpace [PreconnectedSpace M]
    (o : Manifold.Orientation I M (Fin m)) (hm : m + 0 = m) (α : SmoothForm I M ℝ m) :
    α ∈ harmonicForms o hm ↔ ∃ c : ℝ, α.1 = c • riemannianVolumeForm o := by
  rw [mem_harmonicForms_top_iff]
  refine ⟨fun ⟨f, hf⟩ ↦ ?_, fun ⟨c, hc⟩ ↦ ⟨LocallyConstant.const M c, hc⟩⟩
  obtain ⟨c, rfl⟩ := f.exists_eq_const
  exact ⟨c, hf⟩

/-- **The Hodge theorem in the top degree**: on a compact preconnected oriented boundaryless
Riemannian manifold of dimension `m`, every de Rham class of degree `m` has exactly one harmonic
representative. The representative of the class of `φ` is `c vol`, where `c` is the integral of
`φ` divided by the total volume. -/
theorem harmonicForms.toDeRhamCohomology_bijective_top [PreconnectedSpace M]
    (o : Manifold.Orientation I M (Fin m)) (hm : m + 0 = m) :
    Function.Bijective (harmonicForms.toDeRhamCohomology o hm) := by
  refine ⟨harmonicForms.toDeRhamCohomology_injective o hm, fun c ↦ ?_⟩
  obtain ⟨φ, rfl⟩ := deRhamCohomology.mk_surjective I m c
  rcases isEmpty_or_nonempty M with hM | hM
  · -- On the empty manifold every form vanishes.
    refine ⟨0, ?_⟩
    rw [map_zero, eq_comm, deRhamCohomology.mk_eq_zero_iff, show φ.1 = 0 from
      Subtype.ext (funext isEmptyElim)]
    exact zero_mem _
  borelize M
  have : IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x) :=
    IsContMDiffRiemannianBundle.toIsContinuousRiemannianBundle (IB := I) (n := ∞)
  -- The integral of the volume form is the total volume, which is positive.
  have hV : 0 < integralTopForm o (riemannianVolumeForm o) := by
    rw [integralTopForm_riemannianVolumeForm]
    exact riemannianTotalVolume_pos
  set a := integralTopForm o φ.1.1 / integralTopForm o (riemannianVolumeForm o)
  let h := (harmonicFormsTopEquiv o hm).symm (LocallyConstant.const M a)
  have hh : h.1.1 = a • riemannianVolumeForm o := coe_harmonicFormsTopEquiv_symm_apply o hm _
  refine ⟨h, ?_⟩
  -- The top form `φ - a vol` has integral zero, so it is exact.
  rw [harmonicForms.toDeRhamCohomology_apply, eq_comm, ← sub_eq_zero, ← map_sub,
    deRhamCohomology.mk_eq_zero_iff, Submodule.coe_sub]
  refine exactCompactlySupportedForms_le_exactForms I m
    ((mem_exactCompactlySupportedForms_iff_integralTopForm_eq_zero o
      (by simp [compactlySupportedForms_eq_top])).2 ?_)
  rw [Submodule.coe_sub, sub_eq_add_neg, ← neg_one_smul ℝ h.1.1,
    integralTopForm_add_of_compactSpace o (φ.1.isSmoothForm.of_le (by simp))
      ((h.1.isSmoothForm.of_le (by simp)).smul _),
    integralTopForm_smul, hh, integralTopForm_smul, div_mul_cancel₀ _ hV.ne', neg_one_mul,
    add_neg_cancel]

/-- **Harmonic top forms on a connected manifold form a line**: on a compact connected oriented
boundaryless Riemannian manifold of dimension `m`, the harmonic `m`-forms are one-dimensional. -/
theorem finrank_harmonicForms_top [ConnectedSpace M] (o : Manifold.Orientation I M (Fin m))
    (hm : m + 0 = m) : Module.finrank ℝ (harmonicForms o hm) = 1 :=
  ((harmonicFormsTopEquiv o hm).trans (deRhamCohomologyZeroEquiv I M).symm).finrank_eq.trans
    (finrank_deRhamCohomology_zero I M)

end Compact

end TauCeti
