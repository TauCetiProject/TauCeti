/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.DifferentialForm.Wedge.Leibniz
public import TauCeti.Geometry.Contact.Basic

/-!
# Pointwise contact forms

A rough one-form satisfies `TauCeti.IsContactFormAt` at `x` when it is nonzero there and its
exterior derivative is nondegenerate on its kernel. This pointwise condition imposes no global
regularity. For a smooth one-form it agrees with the canonical contact condition in
`TauCeti.SmoothForm.IsContactForm`, by
`TauCeti.SmoothForm.isContactForm_iff_forall_isContactFormAt`.

For a one-form and a scalar function differentiable at `x`, rescaling by the function preserves
this condition whenever its value at `x` is nonzero
(`TauCeti.isContactFormAt_fun_smul_iff`). Negation reverses the coorientation and preserves the
condition (`TauCeti.isContactFormAt_neg_iff`).

## References

* H. Geiges, *An Introduction to Contact Topology*, Cambridge Studies in Advanced Mathematics 109,
  Cambridge University Press, 2008, Sections 1.1 and 2.1.
* D. McDuff, D. Salamon, *Introduction to Symplectic Topology*, 3rd ed., Oxford, 2017, Section 3.5.
-/

public section

noncomputable section

open Set Filter Bundle
open scoped Manifold Topology

namespace TauCeti

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]

/-- A one-form `α` is a **contact form at `x`** when `α_x ≠ 0` and `dα_x` is nondegenerate on the
hyperplane `ker α_x`: the only vector of `ker α_x` that is `dα_x`-orthogonal to all of
`ker α_x` is zero. This is the pointwise algebraic condition only: it imposes no regularity on `α`,
and is meaningful when `α` is differentiable at `x`. The global notion
`TauCeti.SmoothForm.IsContactForm` is defined on smooth forms. -/
structure IsContactFormAt (α : RoughForm I M ℝ 1) (x : M) : Prop where
  /-- A contact form does not vanish, so its kernel is a hyperplane. -/
  ne_zero : α x ≠ 0
  /-- The exterior derivative of a contact form is nondegenerate on its kernel. -/
  nondegenerate : ∀ v ∈ α.ker x, (∀ w ∈ α.ker x, mextDeriv α x ![v, w] = 0) → v = 0

/-- Reversing the coorientation, `α ↦ -α`, preserves the contact condition. -/
@[simp]
theorem isContactFormAt_neg_iff {α : RoughForm I M ℝ 1} {x : M} :
    IsContactFormAt (-α) x ↔ IsContactFormAt α x := by
  suffices ∀ α : RoughForm I M ℝ 1, IsContactFormAt α x → IsContactFormAt (-α) x from
    ⟨fun h ↦ neg_neg α ▸ this _ h, this α⟩
  intro α h
  refine ⟨by simpa using h.ne_zero, fun v hv hvw ↦ h.nondegenerate v (by simpa using hv)
    fun w hw ↦ ?_⟩
  have := hvw w (by simpa using hw)
  simpa [mextDeriv_neg] using this

section Rescaling

variable [IsManifold I 1 M] {α : RoughForm I M ℝ 1} {f : M → ℝ} {x : M}

/-- **Rescaling a contact form**: for a one-form `α` differentiable at `x` and a function `f`
differentiable at `x` with `f x ≠ 0`, the one-form `f α` is a contact form at `x` exactly when
`α` is. On `ker α_x` the Leibniz rule reads `d(f α)_x = f x • dα_x`. -/
theorem isContactFormAt_fun_smul_iff (hf : MDifferentiableAt I 𝓘(ℝ, ℝ) f x)
    (hα : MDifferentiableAt I (I.prod 𝓘(ℝ, E [⋀^Fin 1]→L[ℝ] ℝ))
      (fun y ↦ TotalSpace.mk' (E [⋀^Fin 1]→L[ℝ] ℝ) y (α y)) x) (hfx : f x ≠ 0) :
    IsContactFormAt (fun y ↦ f y • α y) x ↔ IsContactFormAt α x := by
  have hd : ∀ v ∈ α.ker x, ∀ w ∈ α.ker x,
      mextDeriv (fun y ↦ f y • α y) x ![v, w] = f x * mextDeriv α x ![v, w] := by
    intro v hv w hw
    rw [RoughForm.mem_ker] at hv hw
    rw [mextDeriv_fun_smul_apply hf hα, hv, hw]
    ring
  constructor
  · intro h
    refine ⟨(smul_ne_zero_iff.mp h.ne_zero).2, fun v hv hvw ↦ ?_⟩
    refine h.nondegenerate v (by rwa [RoughForm.ker_fun_smul hfx]) fun w hw ↦ ?_
    rw [RoughForm.ker_fun_smul hfx] at hw
    rw [hd v hv w hw, hvw w hw, mul_zero]
  · intro h
    refine ⟨smul_ne_zero hfx h.ne_zero, fun v hv hvw ↦ ?_⟩
    rw [RoughForm.ker_fun_smul hfx] at hv hvw
    refine h.nondegenerate v hv fun w hw ↦ ?_
    have := hvw w hw
    rw [hd v hv w hw] at this
    exact (mul_eq_zero.mp this).resolve_left hfx

end Rescaling

/-- A smooth one-form is contact exactly when it satisfies the pointwise contact condition
at every point. -/
theorem SmoothForm.isContactForm_iff_forall_isContactFormAt [IsManifold I 2 M]
    {α : SmoothForm I M ℝ 1} : α.IsContactForm ↔ ∀ x, IsContactFormAt α.1 x := by
  rw [SmoothForm.isContactForm_iff]
  refine forall_congr' fun x ↦ ?_
  constructor
  · rintro ⟨⟨v, hv⟩, h⟩
    refine ⟨fun hz ↦ hv (by rw [hz]; rfl), ?_⟩
    simpa only [RoughForm.mem_ker] using h
  · intro h
    refine ⟨?_, ?_⟩
    · by_contra hn
      push Not at hn
      apply h.ne_zero
      ext v
      have hv : ![v 0] = v := by
        ext i
        fin_cases i
        rfl
      simpa only [hv, ContinuousAlternatingMap.coe_zero, Pi.zero_apply] using hn (v 0)
    · simpa only [RoughForm.mem_ker] using h.nondegenerate

end TauCeti
