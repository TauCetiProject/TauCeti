/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Contact.VectorField
public import TauCeti.Geometry.Manifold.DifferentialForm.Flow
public import TauCeti.Geometry.Manifold.Flow.Basic
import TauCeti.Geometry.Manifold.VectorField.Regularity

/-!
# Contact vector fields are the fields whose local flows preserve the contact structure

A vector field `X` preserves a hyperplane field `ξ` in the sense of
`TauCeti.PreservesDistribution`, an infinitesimal condition on Lie brackets. This file compares it
with invariance of `ξ = ker α` under the maximal local flow `φ` of `X` (`TauCeti.flowOf`, defined
on the open domain `TauCeti.flowDomain`): the differential of every local time-`t` map sends the
hyperplane at `x` into the hyperplane at `φₜ x`,

`dφₜ (ker αₓ) ⊆ ker α_(φₜ x)` whenever `φₜ x` is defined.

No completeness of `X` is assumed: only the local flow on its maximal domain enters.

* For any one-form `α` vanishing nowhere and any `C¹` vector field `X`, flow invariance implies
  that `X` preserves `ker α`
  (`TauCeti.SmoothForm.preservesDistribution_kerDistribution_of_mfderiv_flowOf_mem`): the
  pullbacks `(φₜ^* α)ₓ` vanish on `ker αₓ` for small `t`, and their velocity at `t = 0` is `L_X α`.
* Conversely, if `L_X α = g α` for a continuous function `g`, then the local flow rescales `α`
  pointwise and therefore preserves `ker α`
  (`TauCeti.SmoothForm.mfderiv_flowOf_mem_kerDistribution_of_mlieDerivForm_eq_smul`).
* For a contact form `α`, every `C¹` contact vector field is the contact Hamiltonian vector field
  of `α(X)`, for which `L_X α = (R_α α(X)) α` with a continuous coefficient. Hence a `C¹` vector
  field preserves the contact structure `ker α` exactly when its local flow does
  (`TauCeti.SmoothForm.IsContactForm.preservesDistribution_kerDistribution_iff_mfderiv_flowOf`),
  and a `C¹` vector field whose local flow preserves `ker α` is the contact Hamiltonian vector field
  `X_(α(X))` of its Hamiltonian
  (`TauCeti.SmoothForm.IsContactForm.eq_contactHamiltonianVectorField_iff_mfderiv_flowOf`).

## References

* H. Geiges, *An Introduction to Contact Topology*, Cambridge Studies in Advanced Mathematics 109
  (2008), Section 2.3 (contact vector fields and their flows).
-/

public section

open Filter
open scoped Manifold ContDiff Topology

namespace TauCeti.SmoothForm

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [T2Space M] [IsManifold I ∞ M]
  {α : SmoothForm I M ℝ 1} {X : (x : M) → TangentSpace I x}

/-- **A vector field whose local flow preserves `ker α` preserves `ker α`.** Let `α` be a one-form
vanishing nowhere and `X` a `C¹` vector field whose maximal flow `φ` satisfies
`dφₜ (ker αₓ) ⊆ ker α_(φₜ x)` wherever `φₜ x` is defined. Then `X` preserves the hyperplane field
`ker α`. The form `α` need not be a contact form, and `X` need not be complete. -/
theorem preservesDistribution_kerDistribution_of_mfderiv_flowOf_mem (hα : ∀ x, α.val x ≠ 0)
    (hX : ContMDiff I I.tangent 1 (T% X))
    (h : ∀ t x, (t, x) ∈ flowDomain X → ∀ v ∈ α.kerDistribution x,
      mfderiv I I (flowOf X t) x v ∈ α.kerDistribution (flowOf X t x)) :
    PreservesDistribution I α.kerDistribution X := by
  refine (preservesDistribution_kerDistribution_iff_mlieDerivForm hα).2 fun x v hv ↦ ?_
  -- The pullbacks `(φₛ^* α)ₓ`, evaluated on `v`, have velocity `(L_X α)ₓ v` at `s = 0`.
  have hd : HasDerivAt (fun s ↦ TauCeti.mpullback I I (flowOf X s) α.val x ![v])
      (mlieDerivForm X α.val x ![v]) 0 :=
    (ContinuousAlternatingMap.apply ℝ E ℝ ![v]).hasFDerivAt.comp_hasDerivAt (0 : ℝ)
      (hasDerivAt_mpullback_flowOf_zero hX x (α.mdifferentiable x))
  -- They vanish for small `s`, since `φₛ` is then defined at `x` and maps `v` into `ker α`.
  have hev : (fun _ : ℝ ↦ (0 : ℝ)) =ᶠ[𝓝 0]
      fun s ↦ TauCeti.mpullback I I (flowOf X s) α.val x ![v] := by
    filter_upwards [((isOpen_flowDomain hX).preimage
      (continuous_id.prodMk continuous_const)).mem_nhds (mem_flowDomain_zero hX x)] with s hs
    have hs' := mem_kerDistribution.1 (h s x hs v hv)
    rw [TauCeti.mpullback_apply_one]
    exact hs'.symm
  exact (hd.congr_of_eventuallyEq hev).unique (hasDerivAt_const (0 : ℝ) (0 : ℝ))

/-- **A local flow rescaling `α` preserves `ker α`.** If the Lie derivative of `α` along a `C¹`
vector field `X` is `g α` for a continuous function `g`, then the maximal flow `φ` of `X` satisfies
`dφₜ (ker αₓ) ⊆ ker α_(φₜ x)` wherever `φₜ x` is defined. -/
theorem mfderiv_flowOf_mem_kerDistribution_of_mlieDerivForm_eq_smul
    (hX : ContMDiff I I.tangent 1 (T% X)) {g : M → ℝ} (hg : Continuous g)
    (hL : mlieDerivForm X α.val = fun y ↦ g y • α.val y) {t : ℝ} {x : M}
    (hx : (t, x) ∈ flowDomain X) {v : TangentSpace I x} (hv : v ∈ α.kerDistribution x) :
    mfderiv I I (flowOf X t) x v ∈ α.kerDistribution (flowOf X t x) := by
  have h := congrArg (fun β ↦ β ![v])
    (mpullback_flowOf_apply_eq_exp_integral_smul hX hg α.mdifferentiable hL hx)
  rw [mem_kerDistribution] at hv ⊢
  simpa only [TauCeti.mpullback_apply_one, ContinuousAlternatingMap.smul_apply, hv,
    smul_zero] using h

namespace IsContactForm

variable (hα : α.IsContactForm)
include hα

/-- **Contact vector fields are the fields whose local flows preserve the contact structure.** For
a contact form `α`, a `C¹` vector field `X` preserves `ξ = ker α` exactly when its maximal flow `φ`
satisfies `dφₜ (ξₓ) ⊆ ξ_(φₜ x)` wherever `φₜ x` is defined. Completeness of `X` is not needed. -/
theorem preservesDistribution_kerDistribution_iff_mfderiv_flowOf
    (hX : ContMDiff I I.tangent 1 (T% X)) :
    PreservesDistribution I α.kerDistribution X ↔
      ∀ t x, (t, x) ∈ flowDomain X → ∀ v ∈ α.kerDistribution x,
        mfderiv I I (flowOf X t) x v ∈ α.kerDistribution (flowOf X t x) := by
  refine ⟨fun hpres t x hx v hv ↦ ?_, preservesDistribution_kerDistribution_of_mfderiv_flowOf_mem
    (fun x ↦ (isContactForm_iff_forall_isContactFormAt.1 hα x).ne_zero) hX⟩
  have hXd : MDiff (T% X) := hX.mdifferentiable one_ne_zero
  -- A contact vector field is the contact Hamiltonian vector field of its Hamiltonian `α(X)`, so
  -- `L_X α = (R_α α(X)) α`, with a continuous coefficient since `α(X)` is `C¹`.
  have hH := (hα.preservesDistribution_kerDistribution_iff hXd).1 hpres
  have hg : Continuous fun y ↦ mvfderiv I (fun z ↦ α.val z ![X z]) y (α.reebVectorField y) :=
    ((ContMDiff.contMDiff_mvfderiv_apply (α.contMDiff_apply_vectorField hX) (m := 0)
      (by norm_num)).comp (hα.contMDiff_reebVectorField.of_le (by simp))).continuous
  exact mfderiv_flowOf_mem_kerDistribution_of_mlieDerivForm_eq_smul hX hg
    (hH.mlieDerivForm_eq hXd) hx hv

/-- **A vector field whose local flow preserves the contact structure is a contact Hamiltonian
vector field.** For a contact form `α`, a `C¹` vector field `X` is the contact Hamiltonian vector
field `X_(α(X))` of its Hamiltonian exactly when its maximal flow `φ` satisfies
`dφₜ (ξₓ) ⊆ ξ_(φₜ x)` for `ξ = ker α`, wherever `φₜ x` is defined. -/
theorem eq_contactHamiltonianVectorField_iff_mfderiv_flowOf
    (hX : ContMDiff I I.tangent 1 (T% X)) :
    X = α.contactHamiltonianVectorField (fun y ↦ α.val y ![X y]) ↔
      ∀ t x, (t, x) ∈ flowDomain X → ∀ v ∈ α.kerDistribution x,
        mfderiv I I (flowOf X t) x v ∈ α.kerDistribution (flowOf X t x) :=
  (hα.preservesDistribution_kerDistribution_iff_eq (hX.mdifferentiable one_ne_zero)).symm.trans
    (hα.preservesDistribution_kerDistribution_iff_mfderiv_flowOf hX)

end IsContactForm

end TauCeti.SmoothForm
