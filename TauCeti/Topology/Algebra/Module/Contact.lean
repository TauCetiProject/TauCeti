/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.BilinearForm.Contact
public import Mathlib.Topology.Algebra.Ring.Basic
public import Mathlib.Topology.Compactness.Compact
public import Mathlib.Analysis.Normed.Operator.Bilinear
import TauCeti.Topology.Algebra.Module.BilinearForm

/-!
# Openness of the contact condition and the continuous symplectization form

For a continuous family of covectors and bilinear forms on a finite-dimensional space,
the contact condition is open. Continuity of each evaluation suffices. The test is the
determinant of the symplectization form on one extra dimension, using
`Module.Dual.isContact_iff_nondegenerate_symplectizationForm`.

Consequently, if two such pairs agree and are contact along a subset, their affine
interpolation is contact on a neighborhood of that subset, uniformly over any compact
set of interpolation parameters. The subset need not be compact or closed. This is
the neighborhood-shrinking step for contact deformations.

On a normed space, the symplectization form of a continuous covector and a continuous bilinear
form is itself a continuous bilinear map (`ContinuousLinearMap.symplectizationForm`). It is
injective at a contact pair (`ContinuousLinearMap.symplectizationForm_injective`), so local contact
deformations can solve their linear equations with it.

## References

* H. Geiges, *An Introduction to Contact Topology*, Section 2.5.
* A. Kriegl and P. W. Michor, *The Convenient Setting of Global Analysis*,
  Proposition 43.18.
-/

public section

open Set
open scoped Topology

namespace TauCeti

section Openness

variable {𝕜 V X : Type*} [Field 𝕜] [TopologicalSpace 𝕜] [IsTopologicalRing 𝕜]
  [T1Space 𝕜] [AddCommGroup V] [Module 𝕜 V] [FiniteDimensional 𝕜 V] [TopologicalSpace X]

/-- Contactness of a family of covectors and bilinear forms on a finite-dimensional space
is an open condition. Only continuity of their scalar evaluations is required. -/
theorem isOpen_setOf_isContact
    {a : X → Module.Dual 𝕜 V} {B : X → LinearMap.BilinForm 𝕜 V}
    (ha : ∀ v, Continuous fun x ↦ a x v)
    (hB : ∀ v w, Continuous fun x ↦ B x v w) :
    IsOpen {x | (a x).IsContact (B x)} := by
  simpa only [Module.Dual.isContact_iff_nondegenerate_symplectizationForm] using
    (isOpen_setOf_nondegenerate (B := fun x ↦ (a x).symplectizationForm (B x)) fun v w ↦ by
      simp only [Module.Dual.symplectizationForm_apply]
      exact ((continuous_const.mul (ha w.2)).sub
        (continuous_const.mul (ha v.2))).add (hB v.2 w.2))

/-- If two continuous covector/bilinear-form pairs agree and are contact on `S`, their
affine interpolation is contact on an open neighborhood of `S` for all parameters in the
compact set `K`. No compactness or closedness of `S` is needed. -/
theorem exists_isOpen_isContact_affine
    {a₀ a₁ : X → Module.Dual 𝕜 V} {B₀ B₁ : X → LinearMap.BilinForm 𝕜 V}
    (ha₀ : ∀ v, Continuous fun x ↦ a₀ x v)
    (ha₁ : ∀ v, Continuous fun x ↦ a₁ x v)
    (hB₀ : ∀ v w, Continuous fun x ↦ B₀ x v w)
    (hB₁ : ∀ v w, Continuous fun x ↦ B₁ x v w)
    {S : Set X} {K : Set 𝕜} (hK : IsCompact K)
    (ha : ∀ x ∈ S, a₁ x = a₀ x) (hB : ∀ x ∈ S, B₁ x = B₀ x)
    (hcontact : ∀ x ∈ S, (a₀ x).IsContact (B₀ x)) :
    ∃ U : Set X, IsOpen U ∧ S ⊆ U ∧ ∀ x ∈ U, ∀ t ∈ K,
      ((1 - t) • a₀ x + t • a₁ x).IsContact ((1 - t) • B₀ x + t • B₁ x) := by
  let W : Set (𝕜 × X) := {p |
    ((1 - p.1) • a₀ p.2 + p.1 • a₁ p.2).IsContact
      ((1 - p.1) • B₀ p.2 + p.1 • B₁ p.2)}
  have hopen : IsOpen W := isOpen_setOf_isContact
    (fun v ↦ ((continuous_const.sub continuous_fst).mul ((ha₀ v).comp continuous_snd)).add
      (continuous_fst.mul ((ha₁ v).comp continuous_snd)))
    (fun v w ↦ ((continuous_const.sub continuous_fst).mul ((hB₀ v w).comp continuous_snd)).add
      (continuous_fst.mul ((hB₁ v w).comp continuous_snd)))
  let U := {x | ∀ t ∈ K, (t, x) ∈ W}
  have hU : IsOpen U := by
    rw [isOpen_iff_mem_nhds]
    intro x hx
    exact hK.eventually_forall_of_forall_eventually fun t ht ↦
      (hopen.preimage continuous_swap).mem_nhds (hx t ht)
  refine ⟨U, hU, ?_, fun x hx t ht ↦ hx t ht⟩
  intro x hx t ht
  dsimp [W]
  rw [ha x hx, hB x hx, ← add_smul, ← add_smul, sub_add_cancel, one_smul, one_smul]
  exact hcontact x hx

end Openness

/-! ### The continuous symplectization form -/

section Continuous

variable {𝕜 E : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- The symplectization form `((s, v), (t, w)) ↦ s a(w) - a(v) t + b v w` on `𝕜 × E` of a
continuous covector `a` and a continuous bilinear form `b`, as a continuous bilinear map. Its
bilinear form is `Module.Dual.symplectizationForm`
(`ContinuousLinearMap.toBilinForm_symplectizationForm`). -/
noncomputable def _root_.ContinuousLinearMap.symplectizationForm (a : E →L[𝕜] 𝕜)
    (b : E →L[𝕜] E →L[𝕜] 𝕜) : (𝕜 × E) →L[𝕜] (𝕜 × E) →L[𝕜] 𝕜 :=
  (ContinuousLinearMap.fst 𝕜 𝕜 E).smulRight (a.comp (ContinuousLinearMap.snd 𝕜 𝕜 E)) -
    (a.comp (ContinuousLinearMap.snd 𝕜 𝕜 E)).smulRight (ContinuousLinearMap.fst 𝕜 𝕜 E) +
    ((ContinuousLinearMap.compL 𝕜 (𝕜 × E) E 𝕜).flip (ContinuousLinearMap.snd 𝕜 𝕜 E)).comp
      (b.comp (ContinuousLinearMap.snd 𝕜 𝕜 E))

@[simp]
theorem _root_.ContinuousLinearMap.symplectizationForm_apply (a : E →L[𝕜] 𝕜)
    (b : E →L[𝕜] E →L[𝕜] 𝕜) (p q : 𝕜 × E) :
    a.symplectizationForm b p q = p.1 * a q.2 - a p.2 * q.1 + b p.2 q.2 := by
  simp [ContinuousLinearMap.symplectizationForm]

/-- The bilinear form of the continuous symplectization form is the symplectization form of the
underlying covector and bilinear form. -/
theorem _root_.ContinuousLinearMap.toBilinForm_symplectizationForm (a : E →L[𝕜] 𝕜)
    (b : E →L[𝕜] E →L[𝕜] 𝕜) :
    (a.symplectizationForm b).toBilinForm =
      Module.Dual.symplectizationForm (a : Module.Dual 𝕜 E) b.toBilinForm := by
  refine LinearMap.ext₂ fun p q ↦ ?_
  simp only [ContinuousLinearMap.toBilinForm_apply, ContinuousLinearMap.symplectizationForm_apply,
    Module.Dual.symplectizationForm_apply, ContinuousLinearMap.coe_coe]
  ring

/-- At a covector `a` which is contact for `b`, the continuous symplectization form is injective,
so it is invertible in finite dimension. -/
theorem _root_.ContinuousLinearMap.symplectizationForm_injective {a : E →L[𝕜] 𝕜}
    {b : E →L[𝕜] E →L[𝕜] 𝕜} (h : Module.Dual.IsContact (a : Module.Dual 𝕜 E) b.toBilinForm) :
    Function.Injective (a.symplectizationForm b) := by
  rw [← ContinuousLinearMap.separatingLeft_toBilinForm_iff_injective,
    ContinuousLinearMap.toBilinForm_symplectizationForm]
  exact Module.Dual.separatingLeft_symplectizationForm_iff.2 ⟨h.ne_zero, h.nondegenerate_restrict.1⟩

end Continuous

end TauCeti
