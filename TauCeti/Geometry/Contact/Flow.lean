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
Reeb vector field. Wherever the maximal flow `φ` of `X` (`TauCeti.flowOf`) through `x` is defined
at time `t`, it rescales `α` by a positive factor:

`(φₜ^* α)ₓ = exp (∫₀ᵗ (R_α f)(φₛ x) ds) αₓ`

(`IsContactHamiltonianVectorField.mpullback_flowOf_apply`). So each local time-`t` map pulls `α`
back at `x` to a positive multiple of `αₓ`, as a cooriented contactomorphism does
(`IsContactHamiltonianVectorField.exists_pos_mpullback_flowOf_apply_eq_smul`). The
local flow preserves `α` itself exactly when `f` is invariant under the Reeb vector field,
`R_α f = 0` (`IsContactHamiltonianVectorField.mpullback_flowOf_apply_eq_self_iff`). In particular
the local Reeb flow, the flow of the constant Hamiltonian `1`, preserves `α`
(`IsContactForm.mpullback_flowOf_reebVectorField_apply`). None of this needs completeness.

When `X` is complete, which holds for instance on a compact manifold
(`TauCeti.isCompleteVectorField_of_compactSpace`), its maximal flow is the global flow `ψ`, and the
time-`t` maps are diffeomorphisms. They are then cooriented contactomorphisms of `α`
(`IsContactHamiltonianVectorField.preservesCoorientation_globalFlowDiffeomorph`), and strict
contactomorphisms for every `t` exactly when `R_α f = 0`
(`IsContactHamiltonianVectorField.isStrictContactomorphism_globalFlowDiffeomorph_iff`). In
particular a complete Reeb flow consists of strict contactomorphisms
(`IsContactForm.isStrictContactomorphism_globalFlowDiffeomorph_reebVectorField`).

## References

* H. Geiges, *An Introduction to Contact Topology*, Cambridge University Press, 2008,
  Section 2.3.
-/

public section

noncomputable section

open scoped ContDiff Manifold Topology

namespace TauCeti.SmoothForm

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [T2Space M] [IsManifold I ∞ M]
  {α : SmoothForm I M ℝ 1} {f : M → ℝ} {X : (x : M) → TangentSpace I x}

namespace IsContactHamiltonianVectorField

/-! ### Maximal flows -/

/-- **A contact Hamiltonian flow rescales the contact form.** For a contact form `α` and the
contact Hamiltonian vector field `X` of a `C³` function `f`, wherever the maximal flow `φ` of `X`
through `x` is defined at time `t`, the time-`t` map pulls `α` back at `x` to
`exp (∫₀ᵗ (R_α f)(φₛ x) ds) • α x`. -/
theorem mpullback_flowOf_apply (hα : α.IsContactForm)
    (hX : α.IsContactHamiltonianVectorField f X) (hf : ContMDiff I 𝓘(ℝ) 3 f) {t : ℝ} {x : M}
    (hx : (t, x) ∈ flowDomain X) :
    TauCeti.mpullback I I (flowOf X t) α.1 x =
      Real.exp (∫ s in 0..t,
        mvfderiv I f (flowOf X s x) (α.reebVectorField (flowOf X s x))) • α.1 x := by
  have hX2 : ContMDiff I I.tangent 2 (fun y ↦ (⟨y, X y⟩ : TangentBundle I M)) :=
    hX.contMDiff hα (by simp) (by norm_num [hf])
  have hRf : Continuous fun y ↦ mvfderiv I f y (α.reebVectorField y) :=
    ((ContMDiff.contMDiff_mvfderiv_apply hf (m := 0) (by norm_num)).comp
      (hα.contMDiff_reebVectorField.of_le (by simp))).continuous
  exact mpullback_flowOf_apply_eq_exp_integral_smul hX2 hRf α.mdifferentiable
    (hX.mlieDerivForm_eq (hX2.mdifferentiable two_ne_zero)) hx

/-- **Contact Hamiltonian flows preserve the coorientation.** For a contact form `α` and the
contact Hamiltonian vector field `X` of a `C³` function, wherever the maximal flow of `X` through
`x` is defined at time `t`, the time-`t` map pulls `α` back at `x` to a positive multiple of
`α x`. -/
theorem exists_pos_mpullback_flowOf_apply_eq_smul (hα : α.IsContactForm)
    (hX : α.IsContactHamiltonianVectorField f X) (hf : ContMDiff I 𝓘(ℝ) 3 f) {t : ℝ} {x : M}
    (hx : (t, x) ∈ flowDomain X) :
    ∃ c : ℝ, 0 < c ∧ TauCeti.mpullback I I (flowOf X t) α.1 x = c • α.1 x :=
  ⟨_, Real.exp_pos _, hX.mpullback_flowOf_apply hα hf hx⟩

/-- **Strict contact Hamiltonian flows.** For a contact form `α` and the contact Hamiltonian
vector field `X` of a `C³` function `f`, the maximal flow of `X` preserves `α` wherever it is
defined exactly when `f` is invariant under the Reeb vector field: `R_α f = 0`. -/
theorem mpullback_flowOf_apply_eq_self_iff (hα : α.IsContactForm)
    (hX : α.IsContactHamiltonianVectorField f X) (hf : ContMDiff I 𝓘(ℝ) 3 f) :
    (∀ t x, (t, x) ∈ flowDomain X → TauCeti.mpullback I I (flowOf X t) α.1 x = α.1 x) ↔
      ∀ x, mvfderiv I f x (α.reebVectorField x) = 0 := by
  have hX2 : ContMDiff I I.tangent 2 (fun y ↦ (⟨y, X y⟩ : TangentBundle I M)) :=
    hX.contMDiff hα (by simp) (by norm_num [hf])
  have hX1 := hX2.of_le one_le_two
  constructor
  · intro h x
    -- The pullbacks `φₜ^* α` at `x` are constant for small `t`, and their velocity at `0` is
    -- `L_X α = (R_α f) α`.
    have hd := hasDerivAt_mpullback_flowOf_zero hX2 x (α.mdifferentiable x)
    have hconst : (fun s ↦ TauCeti.mpullback I I (flowOf X s) α.1 x) =ᶠ[𝓝 0]
        fun _ ↦ α.1 x := by
      have hopen : {s | (s, x) ∈ flowDomain X} ∈ 𝓝 (0 : ℝ) :=
        ((isOpen_flowDomain hX1).preimage (continuous_id.prodMk continuous_const)).mem_nhds
          (mem_flowDomain_zero hX1 x)
      filter_upwards [hopen] with s hs
      exact h s x hs
    rw [hX.mlieDerivForm_eq (hX2.mdifferentiable two_ne_zero)] at hd
    have h0 := (hd.congr_of_eventuallyEq hconst.symm).unique
      (hasDerivAt_const (F := E [⋀^Fin 1]→L[ℝ] ℝ) (0 : ℝ) (α.1 x))
    have hα₀ : (α.1 x : E [⋀^Fin 1]→L[ℝ] ℝ) ≠ 0 :=
      (isContactForm_iff_forall_isContactFormAt.mp hα x).ne_zero
    exact (smul_eq_zero.mp h0).resolve_right hα₀
  · intro h t x hx
    rw [hX.mpullback_flowOf_apply hα hf hx]
    simp [h]

/-! ### Complete flows -/

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
  rw [← flowOf_eq_globalFlow]
  exact hX.mpullback_flowOf_apply hα hf (hc.mem_flowDomain t x)

/-- **Contact Hamiltonian flows are cooriented contactomorphisms.** For a contact form `α` and a
complete contact Hamiltonian vector field `X` of a smooth function, each time-`t` map of the flow
of `X` pulls `α` back to a positive multiple of `α`. -/
theorem preservesCoorientation_globalFlowDiffeomorph (hα : α.IsContactForm)
    (hX : α.IsContactHamiltonianVectorField f X) (hf : ContMDiff I 𝓘(ℝ) ∞ f)
    (hc : IsCompleteVectorField X) (t : ℝ) :
    (globalFlowDiffeomorph hc le_top (hX.contMDiff hα le_rfl (by simpa using hf))
      t).PreservesCoorientation α α := by
  rw [Diffeomorph.preservesCoorientation_def]
  intro x
  rw [SmoothForm.coe_mpullback, coe_globalFlowDiffeomorph, ← flowOf_eq_globalFlow]
  exact hX.exists_pos_mpullback_flowOf_apply_eq_smul hα (hf.of_le (by simp))
    (hc.mem_flowDomain t x)

/-- **Strict contact Hamiltonian flows.** For a contact form `α` and a complete contact
Hamiltonian vector field `X` of a smooth function `f`, every time-`t` map of the flow of `X`
preserves `α` exactly when `f` is invariant under the Reeb vector field: `R_α f = 0`. -/
theorem isStrictContactomorphism_globalFlowDiffeomorph_iff (hα : α.IsContactForm)
    (hX : α.IsContactHamiltonianVectorField f X) (hf : ContMDiff I 𝓘(ℝ) ∞ f)
    (hc : IsCompleteVectorField X) :
    (∀ t, (globalFlowDiffeomorph hc le_top (hX.contMDiff hα le_rfl (by simpa using hf))
      t).IsStrictContactomorphism α α) ↔ ∀ x, mvfderiv I f x (α.reebVectorField x) = 0 := by
  rw [← hX.mpullback_flowOf_apply_eq_self_iff hα (hf.of_le (by simp))]
  refine forall_congr' fun t ↦ ?_
  rw [Diffeomorph.isStrictContactomorphism_def, Subtype.ext_iff, SmoothForm.coe_mpullback,
    coe_globalFlowDiffeomorph, ← flowOf_eq_globalFlow, funext_iff]
  simp [hc.mem_flowDomain]

end IsContactHamiltonianVectorField

/-- **The local Reeb flow is strict.** Wherever the maximal flow of the Reeb vector field of a
contact form `α` through `x` is defined at time `t`, the time-`t` map pulls `α` back at `x` to
`α x`. -/
theorem IsContactForm.mpullback_flowOf_reebVectorField_apply (hα : α.IsContactForm) {t : ℝ}
    {x : M} (hx : (t, x) ∈ flowDomain α.reebVectorField) :
    TauCeti.mpullback I I (flowOf α.reebVectorField t) α.1 x = α.1 x := by
  have hX : α.IsContactHamiltonianVectorField 1 α.reebVectorField := by
    rw [← hα.contactHamiltonianVectorField_one]
    exact hα.isContactHamiltonianVectorField_contactHamiltonianVectorField 1
  exact (hX.mpullback_flowOf_apply_eq_self_iff hα contMDiff_const).2
    (fun y ↦ by simp [Pi.one_def, mvfderiv_const]) t x hx

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
