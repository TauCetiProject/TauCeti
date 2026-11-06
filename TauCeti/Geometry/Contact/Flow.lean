/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Contact.Contactomorphism
public import TauCeti.Geometry.Contact.Hamiltonian
public import TauCeti.Geometry.Manifold.DifferentialForm.Flow
import TauCeti.Geometry.Manifold.VectorField.Regularity

/-!
# Flows of contact Hamiltonian vector fields

Let `α` be a contact form on a finite-dimensional boundaryless manifold `M` and let `X` be the
contact Hamiltonian vector field of a function `f`, so that `L_X α = (R_α f) α`, where `R_α` is the
Reeb vector field. When `X` is complete, its flow `ψ` rescales `α` by a positive factor:

`(ψₜ^* α)ₓ = exp (∫₀ᵗ (R_α f)(ψₛ x) ds) αₓ`

(`IsContactHamiltonianVectorField.mpullback_globalFlow_apply`). Hence every
time-`t` map of the flow is a cooriented contactomorphism of `α`
(`IsContactHamiltonianVectorField.preservesCoorientation_globalFlowDiffeomorph`),
and so preserves the contact structure `ker α` and its coorientation. The flow consists of strict
contactomorphisms exactly when `f` is invariant under the Reeb vector field, `R_α f = 0`
(`IsContactHamiltonianVectorField.isStrictContactomorphism_globalFlowDiffeomorph_iff`).
In particular the Reeb flow, the flow of the constant Hamiltonian `1`, preserves `α`
(`IsContactForm.isStrictContactomorphism_globalFlowDiffeomorph_reebVectorField`).

Completeness is a hypothesis: the statements concern the globally defined flow, which exists for
instance on a compact manifold (`TauCeti.isCompleteVectorField_of_compactSpace`).

## References

* H. Geiges, *An Introduction to Contact Topology*, Cambridge University Press, 2008,
  Section 2.3.
-/

public section

noncomputable section

open scoped ContDiff Manifold

namespace TauCeti.SmoothForm

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [T2Space M] [IsManifold I ∞ M]
  {α : SmoothForm I M ℝ 1} {f : M → ℝ} {X : (x : M) → TangentSpace I x}

namespace IsContactHamiltonianVectorField

/-- **A contact Hamiltonian flow rescales the contact form.** For a contact form `α` and a
complete contact Hamiltonian vector field `X` of a `C³` function `f`, the time-`t` map of the flow
`ψ` of `X` pulls `α` back at `x` to `exp (∫₀ᵗ (R_α f)(ψₛ x) ds) • α x`. -/
theorem mpullback_globalFlow_apply (hα : α.IsContactForm)
    (hX : α.IsContactHamiltonianVectorField f X) (hf : ContMDiff I 𝓘(ℝ) 3 f)
    (hc : IsCompleteVectorField X) (t : ℝ) (x : M) :
    TauCeti.mpullback I I
        (globalFlow X (hX.contMDiff hα (n := 1) (by simp) (hf.of_le (by norm_num))) hc t) α.1 x =
      Real.exp (∫ s in 0..t,
        mvfderiv I f (globalFlow X (hX.contMDiff hα (n := 1) (by simp) (hf.of_le (by norm_num)))
          hc s x) (α.reebVectorField (globalFlow X
            (hX.contMDiff hα (n := 1) (by simp) (hf.of_le (by norm_num))) hc s x))) • α.1 x := by
  have hX2 : ContMDiff I I.tangent 2 (fun y ↦ (⟨y, X y⟩ : TangentBundle I M)) :=
    hX.contMDiff hα (by simp) (by norm_num [hf])
  have hRf : Continuous fun y ↦ mvfderiv I f y (α.reebVectorField y) :=
    ((ContMDiff.contMDiff_mvfderiv_apply hf (m := 0) (by norm_num)).comp
      (hα.contMDiff_reebVectorField.of_le (by simp))).continuous
  exact mpullback_globalFlow_apply_eq_exp_integral_smul hc hX2 hRf α.mdifferentiable
    (hX.mlieDerivForm_eq (hX2.mdifferentiable two_ne_zero)) t x

/-- **Contact Hamiltonian flows are cooriented contactomorphisms.** For a contact form `α` and a
complete contact Hamiltonian vector field `X` of a smooth function, each time-`t` map of the flow
of `X` pulls `α` back to a positive multiple of `α`. -/
theorem preservesCoorientation_globalFlowDiffeomorph (hα : α.IsContactForm)
    (hX : α.IsContactHamiltonianVectorField f X) (hf : ContMDiff I 𝓘(ℝ) ∞ f)
    (hc : IsCompleteVectorField X) (t : ℝ) :
    (globalFlowDiffeomorph hc le_top (hX.contMDiff hα le_rfl (by simpa using hf))
      t).PreservesCoorientation α α := by
  have hf3 : ContMDiff I 𝓘(ℝ) 3 f := hf.of_le (by simp)
  set ψ := globalFlow X (hX.contMDiff hα (n := 1) (by simp) (hf3.of_le (by norm_num))) hc
  rw [Diffeomorph.preservesCoorientation_def]
  intro x
  refine ⟨Real.exp (∫ s in 0..t, mvfderiv I f (ψ s x) (α.reebVectorField (ψ s x))),
    Real.exp_pos _, ?_⟩
  rw [SmoothForm.coe_mpullback]
  rw [coe_globalFlowDiffeomorph]
  exact hX.mpullback_globalFlow_apply hα hf3 hc t x

/-- **Strict contact Hamiltonian flows.** For a contact form `α` and a complete contact
Hamiltonian vector field `X` of a smooth function `f`, every time-`t` map of the flow of `X`
preserves `α` exactly when `f` is invariant under the Reeb vector field: `R_α f = 0`. -/
theorem isStrictContactomorphism_globalFlowDiffeomorph_iff (hα : α.IsContactForm)
    (hX : α.IsContactHamiltonianVectorField f X) (hf : ContMDiff I 𝓘(ℝ) ∞ f)
    (hc : IsCompleteVectorField X) :
    (∀ t, (globalFlowDiffeomorph hc le_top (hX.contMDiff hα le_rfl (by simpa using hf))
      t).IsStrictContactomorphism α α) ↔ ∀ x, mvfderiv I f x (α.reebVectorField x) = 0 := by
  have hf3 : ContMDiff I 𝓘(ℝ) 3 f := hf.of_le (by simp)
  have hX2 : ContMDiff I I.tangent 2 (fun y ↦ (⟨y, X y⟩ : TangentBundle I M)) :=
    hX.contMDiff hα (by simp) (by norm_num [hf3])
  set ψ := globalFlow X (hX2.of_le one_le_two) hc
  constructor
  · intro h x
    -- The pullbacks `ψₜ^* α` at `x` are constant in `t`, and their velocity at `0` is
    -- `L_X α = (R_α f) α`.
    have hd := hasDerivAt_mpullback_globalFlow_zero hc hX2 x (α.mdifferentiable x)
    have hconst : (fun s ↦ TauCeti.mpullback I I (ψ s) α.1 x) = fun _ ↦ α.1 x :=
      funext fun s ↦ by
        have hs := congrArg (fun (form : SmoothForm I M ℝ 1) ↦ form.1)
          (Diffeomorph.isStrictContactomorphism_def.1 (h s))
        rw [SmoothForm.coe_mpullback] at hs
        rw [coe_globalFlowDiffeomorph] at hs
        exact congrFun hs x
    rw [hconst, hX.mlieDerivForm_eq (hX2.mdifferentiable two_ne_zero)] at hd
    have h0 := hd.unique (hasDerivAt_const (F := E [⋀^Fin 1]→L[ℝ] ℝ) (0 : ℝ) (α.1 x))
    have hα₀ : (α.1 x : E [⋀^Fin 1]→L[ℝ] ℝ) ≠ 0 :=
      (isContactForm_iff_forall_isContactFormAt.mp hα x).ne_zero
    exact (smul_eq_zero.mp h0).resolve_right hα₀
  · intro h t
    rw [Diffeomorph.isStrictContactomorphism_def]
    apply Subtype.ext
    funext x
    rw [SmoothForm.coe_mpullback]
    rw [coe_globalFlowDiffeomorph]
    rw [hX.mpullback_globalFlow_apply hα hf3 hc t x]
    simp [h]

end IsContactHamiltonianVectorField

/-- **The Reeb flow is strict.** The flow of the Reeb vector field of a contact form, when it is
complete, consists of strict contactomorphisms. -/
theorem IsContactForm.isStrictContactomorphism_globalFlowDiffeomorph_reebVectorField
    (hα : α.IsContactForm) (hc : IsCompleteVectorField α.reebVectorField) (t : ℝ) :
    (globalFlowDiffeomorph hc le_top hα.contMDiff_reebVectorField t).IsStrictContactomorphism
      α α := by
  have hX : α.IsContactHamiltonianVectorField 1 α.reebVectorField := by
    rw [← hα.contactHamiltonianVectorField_one]
    exact hα.isContactHamiltonianVectorField_contactHamiltonianVectorField 1
  exact (hX.isStrictContactomorphism_globalFlowDiffeomorph_iff hα contMDiff_const hc).2
    (fun x ↦ by simp [Pi.one_def, mvfderiv_const]) t

end TauCeti.SmoothForm
