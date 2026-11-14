/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Dynamics.Flow.Basic
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
the local Reeb flow, the flow of the constant Hamiltonian `1`, preserves `α`, `ξ = ker α`, and `dα`
(`IsContactForm.mpullback_flowOf_reebVectorField_apply`,
`IsContactForm.mfderiv_flowOf_reebVectorField_mem_kerDistribution`,
`IsContactForm.mextDeriv_mfderiv_flowOf_reebVectorField`, `IsContactForm.flowOfKerEquiv`). None of
this needs completeness.

When `X` is complete, which holds for instance on a compact manifold
(`TauCeti.isCompleteVectorField_of_compactSpace`), its maximal flow is the global flow `ψ`, and the
time-`t` maps are diffeomorphisms. They are then cooriented contactomorphisms of `α`
(`IsContactHamiltonianVectorField.preservesCoorientation_globalFlowDiffeomorph`), and strict
contactomorphisms for every `t` exactly when `R_α f = 0`
(`IsContactHamiltonianVectorField.isStrictContactomorphism_globalFlowDiffeomorph_iff`). In
particular a complete Reeb vector field defines the global **Reeb flow**
(`IsContactForm.reebFlow`), whose time-`t` maps are strict contactomorphisms
(`IsContactForm.isStrictContactomorphism_globalFlowDiffeomorph_reebVectorField`) inducing linear
equivalences `ξ_x ≃ₗ[ℝ] ξ_(φ_t x)` (`IsContactForm.reebFlowKerEquiv`) that preserve `dα`.

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

namespace IsContactForm

/-! ### The local Reeb flow -/

/-- **The local Reeb flow is strict.** Wherever the maximal flow of the Reeb vector field of a
contact form `α` through `x` is defined at time `t`, the time-`t` map pulls `α` back at `x` to
`α x`. -/
theorem mpullback_flowOf_reebVectorField_apply (hα : α.IsContactForm) {t : ℝ}
    {x : M} (hx : (t, x) ∈ flowDomain α.reebVectorField) :
    TauCeti.mpullback I I (flowOf α.reebVectorField t) α.1 x = α.1 x := by
  have hX : α.IsContactHamiltonianVectorField 1 α.reebVectorField := by
    rw [← hα.contactHamiltonianVectorField_one]
    exact hα.isContactHamiltonianVectorField_contactHamiltonianVectorField 1
  exact (hX.mpullback_flowOf_apply_eq_self_iff hα contMDiff_const).2
    (fun y ↦ by simp [Pi.one_def, mvfderiv_const]) t x hx

/-- Wherever the maximal Reeb flow is defined at `(t, x)`, its differential maps the contact
hyperplane `ξ_x = ker α_x` into `ξ_(φ_t x)`. -/
theorem mfderiv_flowOf_reebVectorField_mem_kerDistribution (hα : α.IsContactForm) {t : ℝ} {x : M}
    (ht : (t, x) ∈ flowDomain α.reebVectorField) {v : TangentSpace I x}
    (hv : v ∈ α.kerDistribution x) :
    mfderiv I I (flowOf α.reebVectorField t) x v ∈
      α.kerDistribution (flowOf α.reebVectorField t x) := by
  rw [mem_kerDistribution] at hv ⊢
  have h := DFunLike.congr_fun (hα.mpullback_flowOf_reebVectorField_apply ht) ![v]
  rw [TauCeti.mpullback_apply] at h
  have hv' : (fun i : Fin 1 ↦ mfderiv I I (flowOf α.reebVectorField t) x (![v] i)) =
      ![mfderiv I I (flowOf α.reebVectorField t) x v] := by
    ext i
    fin_cases i
    rfl
  rwa [hv', hv] at h

/-- Wherever the maximal Reeb flow is defined at `(t, x)`, its differential preserves the exterior
derivative `dα` on tangent vectors. -/
theorem mextDeriv_mfderiv_flowOf_reebVectorField (hα : α.IsContactForm) {t : ℝ} {x : M}
    (ht : (t, x) ∈ flowDomain α.reebVectorField) (v w : TangentSpace I x) :
    mextDeriv α.1 (flowOf α.reebVectorField t x)
        ![mfderiv I I (flowOf α.reebVectorField t) x v,
          mfderiv I I (flowOf α.reebVectorField t) x w] =
      mextDeriv α.1 x ![v, w] := by
  have hR := hα.contMDiff_reebVectorField
  have hf : ContMDiffAt I I 2 (flowOf α.reebVectorField t) x :=
    contMDiffAt_flowOf_comp one_le_two (hR.of_le (by simp)) contMDiffAt_const contMDiffAt_id ht
  have hev : ∀ᶠ y in 𝓝 x, TauCeti.mpullback I I (flowOf α.reebVectorField t) α.1 y = α.1 y := by
    filter_upwards [(isOpen_setOf_mem_flowDomain (hR.of_le (by simp)) continuous_const
      continuous_id).mem_nhds ht] with y hy
    exact hα.mpullback_flowOf_reebVectorField_apply hy
  rw [← mpullback_apply_pair, mpullback_mextDeriv_at hf (α.contMDiff.of_le (by simp) _),
    mextDeriv_congr_of_eventuallyEq hev]

/-- Wherever the maximal Reeb flow is defined at `(t, x)`, restricting `d(φ_t)_x` to `ξ = ker α`
gives a linear equivalence `ξ_x ≃ₗ[ℝ] ξ_(φ_t x)` whose inverse is the restriction of `d(φ_{-t})`. -/
def flowOfKerEquiv (hα : α.IsContactForm) {t : ℝ} {x : M}
    (ht : (t, x) ∈ flowDomain α.reebVectorField) :
    α.kerDistribution x ≃ₗ[ℝ] α.kerDistribution (flowOf α.reebVectorField t x) :=
  let hv1 : ContMDiff I I.tangent 1 (fun y ↦ (⟨y, α.reebVectorField y⟩ : TangentBundle I M)) :=
    hα.contMDiff_reebVectorField.of_le (by simp)
  let hnt : (-t, flowOf α.reebVectorField t x) ∈ flowDomain α.reebVectorField :=
    neg_mem_flowDomain_flowOf hv1 ht
  LinearEquiv.ofLinearMap
    ((mfderiv I I (flowOf α.reebVectorField t) x).toLinearMap.restrict
      fun _ hv ↦ hα.mfderiv_flowOf_reebVectorField_mem_kerDistribution ht hv)
    ((mfderiv I I (flowOf α.reebVectorField (-t))
        (flowOf α.reebVectorField t x)).toLinearMap.restrict fun _ hv ↦ by
      have h := hα.mfderiv_flowOf_reebVectorField_mem_kerDistribution hnt hv
      rwa [flowOf_neg_flowOf hv1 ht] at h)
    (LinearMap.ext fun w ↦ Subtype.ext <| by
      have h := mfderiv_flowOf_add_apply_of_eq hv1 hnt ht (flowOf_neg_flowOf hv1 ht) w
      rw [neg_add_cancel] at h
      exact h.symm.trans
        (mfderiv_flowOf_zero_id (flowOf α.reebVectorField t x)
          (w : TangentSpace I (flowOf α.reebVectorField t x))))
    (LinearMap.ext fun w ↦ Subtype.ext <| by
      have h := mfderiv_flowOf_add_apply_of_eq hv1 ht hnt rfl w
      rw [add_neg_cancel] at h
      exact h.symm.trans (mfderiv_flowOf_zero_id x (w : TangentSpace I x)))

/-- `flowOfKerEquiv` acts as `mfderiv I I (flowOf α.reebVectorField t) x` on `ξ_x`. -/
@[simp]
theorem coe_flowOfKerEquiv_apply (hα : α.IsContactForm) {t : ℝ} {x : M}
    (ht : (t, x) ∈ flowDomain α.reebVectorField) (v : α.kerDistribution x) :
    (hα.flowOfKerEquiv ht v : TangentSpace I (flowOf α.reebVectorField t x)) =
      mfderiv I I (flowOf α.reebVectorField t) x v :=
  (rfl)

/-- `(flowOfKerEquiv ht).symm` acts as `mfderiv I I (flowOf α.reebVectorField (-t))` at
`flowOf α.reebVectorField t x`. -/
@[simp]
theorem coe_flowOfKerEquiv_symm_apply (hα : α.IsContactForm) {t : ℝ} {x : M}
    (ht : (t, x) ∈ flowDomain α.reebVectorField)
    (w : α.kerDistribution (flowOf α.reebVectorField t x)) :
    ((hα.flowOfKerEquiv ht).symm w : TangentSpace I x) =
      mfderiv I I (flowOf α.reebVectorField (-t)) (flowOf α.reebVectorField t x) w :=
  (rfl)

/-- `flowOfKerEquiv` preserves the exterior derivative `dα` on `ξ`. -/
theorem mextDeriv_flowOfKerEquiv (hα : α.IsContactForm) {t : ℝ} {x : M}
    (ht : (t, x) ∈ flowDomain α.reebVectorField) (v w : α.kerDistribution x) :
    mextDeriv α.1 (flowOf α.reebVectorField t x)
        ![hα.flowOfKerEquiv ht v, hα.flowOfKerEquiv ht w] =
      mextDeriv α.1 x ![v, w] :=
  hα.mextDeriv_mfderiv_flowOf_reebVectorField ht v w

/-! ### The global Reeb flow -/

/-- **The Reeb flow is strict.** The flow of the Reeb vector field of a contact form, when it is
complete, consists of strict contactomorphisms. -/
theorem isStrictContactomorphism_globalFlowDiffeomorph_reebVectorField
    (hα : α.IsContactForm) (hc : IsCompleteVectorField α.reebVectorField) (t : ℝ) :
    (globalFlowDiffeomorph hc le_top hα.contMDiff_reebVectorField t).IsStrictContactomorphism
      α α := by
  have hX : α.IsContactHamiltonianVectorField 1 α.reebVectorField := by
    rw [← hα.contactHamiltonianVectorField_one]
    exact hα.isContactHamiltonianVectorField_contactHamiltonianVectorField 1
  exact (hX.isStrictContactomorphism_globalFlowDiffeomorph_iff hα contMDiff_const hc).2
    (fun x ↦ by simp [Pi.one_def, mvfderiv_const]) t

/-- On a compact boundaryless contact manifold, the Reeb vector field is complete. -/
theorem isCompleteVectorField_reebVectorField [CompactSpace M] (hα : α.IsContactForm) :
    IsCompleteVectorField α.reebVectorField :=
  isCompleteVectorField_of_compactSpace (hα.contMDiff_reebVectorField.of_le (by simp))

section Complete

variable (hα : α.IsContactForm) (hc : IsCompleteVectorField α.reebVectorField)

/-- The **Reeb flow** of a contact form whose Reeb vector field is complete. -/
def reebFlow : Flow ℝ M :=
  globalFlow α.reebVectorField (hα.contMDiff_reebVectorField.of_le (by simp)) hc

/-- Unfolds `IsContactForm.reebFlow` as `TauCeti.globalFlow` of `α.reebVectorField`. -/
theorem reebFlow_def :
    hα.reebFlow hc =
      globalFlow α.reebVectorField (hα.contMDiff_reebVectorField.of_le (by simp)) hc :=
  (rfl)

/-- The Reeb flow agrees with the maximal flow `TauCeti.flowOf` of `α.reebVectorField`. -/
theorem reebFlow_eq_flowOf (t : ℝ) (x : M) :
    hα.reebFlow hc t x = flowOf α.reebVectorField t x := by
  rw [reebFlow, ← flowOf_eq_globalFlow]

/-- The Reeb flow equals the time-`t` global flow diffeomorphism at every point. -/
theorem reebFlow_eq_globalFlowDiffeomorph (t : ℝ) (x : M) :
    hα.reebFlow hc t x =
      globalFlowDiffeomorph hc le_top hα.contMDiff_reebVectorField t x :=
  (globalFlowDiffeomorph_apply hc le_top hα.contMDiff_reebVectorField t x).symm

/-- As a function, the time-`t` map of `reebFlow` agrees with `globalFlowDiffeomorph`. -/
theorem coe_reebFlow_eq_globalFlowDiffeomorph (t : ℝ) :
    hα.reebFlow hc t = ⇑(globalFlowDiffeomorph hc le_top hα.contMDiff_reebVectorField t) :=
  funext (hα.reebFlow_eq_globalFlowDiffeomorph hc t)

/-- Orbits of the Reeb flow are integral curves of the Reeb vector field. -/
theorem isMIntegralCurve_reebFlow (x : M) :
    IsMIntegralCurve (fun t ↦ hα.reebFlow hc t x) α.reebVectorField :=
  isMIntegralCurve_globalFlow _ hc x

/-- The Reeb flow is jointly smooth in time and space. -/
theorem contMDiff_reebFlow_uncurry :
    ContMDiff (𝓘(ℝ, ℝ).prod I) I ∞ (Function.uncurry (hα.reebFlow hc)) :=
  contMDiff_globalFlow_uncurry hc le_top hα.contMDiff_reebVectorField

/-- The time-`t` map of the Reeb flow is smooth. -/
theorem contMDiff_reebFlow_apply (t : ℝ) :
    ContMDiff I I ∞ (hα.reebFlow hc t) :=
  contMDiff_globalFlow_apply hc le_top hα.contMDiff_reebVectorField t

/-- Each time-`t` map of the Reeb flow pulls `α` back to `α`. -/
theorem mpullback_reebFlow_apply (t : ℝ) (x : M) :
    TauCeti.mpullback I I (hα.reebFlow hc t) α.1 x = α.1 x := by
  have hfun : hα.reebFlow hc t = flowOf α.reebVectorField t :=
    funext (hα.reebFlow_eq_flowOf hc t)
  rw [hfun]
  exact hα.mpullback_flowOf_reebVectorField_apply (hc.mem_flowDomain t x)

/-- The differential of the Reeb flow preserves the Reeb vector field. -/
theorem mfderiv_reebFlow_apply_self (t : ℝ) (x : M) :
    mfderiv I I (hα.reebFlow hc t) x (α.reebVectorField x) =
      α.reebVectorField (hα.reebFlow hc t x) :=
  mfderiv_globalFlow_apply_self _ hc t x

/-- No point is stationary under the Reeb flow, since the Reeb vector field vanishes nowhere. -/
theorem exists_reebFlow_ne_self (x : M) : ∃ t : ℝ, hα.reebFlow hc t x ≠ x := by
  by_contra h
  have hfix : ∀ t, hα.reebFlow hc t x = x := by
    simpa only [not_exists, not_not] using h
  exact hα.reebVectorField_ne_zero x ((forall_globalFlow_eq_self_iff _ hc x).1 hfix)

/-- The differential of the Reeb flow maps the contact distribution `ξ = ker α` to itself. -/
theorem mfderiv_reebFlow_mem_kerDistribution (t : ℝ) {x : M} {v : TangentSpace I x}
    (hv : v ∈ α.kerDistribution x) :
    mfderiv I I (hα.reebFlow hc t) x v ∈ α.kerDistribution (hα.reebFlow hc t x) := by
  have hmem := (Diffeomorph.isContactomorphism_iff.1
    (hα.isStrictContactomorphism_globalFlowDiffeomorph_reebVectorField hc t).isContactomorphism
    x v).2 hv
  rwa [← hα.coe_reebFlow_eq_globalFlowDiffeomorph hc t] at hmem

/-- The Reeb flow preserves the exterior derivative `dα` on tangent vectors. -/
theorem mextDeriv_mfderiv_reebFlow (t : ℝ) (x : M) (v w : TangentSpace I x) :
    mextDeriv α.1 (hα.reebFlow hc t x)
        ![mfderiv I I (hα.reebFlow hc t) x v, mfderiv I I (hα.reebFlow hc t) x w] =
      mextDeriv α.1 x ![v, w] := by
  let Φ := globalFlowDiffeomorph hc le_top hα.contMDiff_reebVectorField t
  have hstrict : SmoothForm.mpullback Φ Φ.contMDiff α = α :=
    Diffeomorph.isStrictContactomorphism_def.1
      (hα.isStrictContactomorphism_globalFlowDiffeomorph_reebVectorField hc t)
  rw [hα.coe_reebFlow_eq_globalFlowDiffeomorph hc t,
    ← SmoothForm.mextDeriv_mpullback_apply_two Φ Φ.contMDiff α x v w, hstrict]

private def reebFlowDiffeomorph (t : ℝ) : M ≃ₘ⟮I, I⟯ M where
  toEquiv := ((hα.reebFlow hc).toHomeomorph t).toEquiv
  contMDiff_toFun := hα.contMDiff_reebFlow_apply hc t
  contMDiff_invFun := hα.contMDiff_reebFlow_apply hc (-t)

/-- The differential of the time-`t` Reeb flow restricted to `ξ = ker α` as a linear equivalence
`ξ_x ≃ₗ[ℝ] ξ_(φ_t x)`. -/
def reebFlowKerEquiv (t : ℝ) (x : M) :
    α.kerDistribution x ≃ₗ[ℝ] α.kerDistribution (hα.reebFlow hc t x) :=
  ((hα.reebFlowDiffeomorph hc t).mfderivToContinuousLinearEquiv
    (by simp) x).toLinearEquiv.ofSubmodules
    (α.kerDistribution x) (α.kerDistribution (hα.reebFlow hc t x)) (by
      have hΦ : hα.reebFlowDiffeomorph hc t =
          globalFlowDiffeomorph hc le_top hα.contMDiff_reebVectorField t :=
        Diffeomorph.ext fun y ↦ hα.reebFlow_eq_globalFlowDiffeomorph hc t y
      have hstrict : (hα.reebFlowDiffeomorph hc t).IsStrictContactomorphism α α :=
        hΦ ▸ hα.isStrictContactomorphism_globalFlowDiffeomorph_reebVectorField hc t
      have hder : ((hα.reebFlowDiffeomorph hc t).mfderivToContinuousLinearEquiv
          (by simp) x).toLinearEquiv.toLinearMap =
          (mfderiv I I (hα.reebFlow hc t) x).toLinearMap :=
        congrArg ContinuousLinearMap.toLinearMap
          ((hα.reebFlowDiffeomorph hc t).mfderivToContinuousLinearEquiv_coe (by simp))
      exact hder.symm ▸ hstrict.isContactomorphism.map_kerDistribution x)

/-- `reebFlowKerEquiv` acts as `mfderiv I I (hα.reebFlow hc t) x` on `ξ_x`. -/
@[simp]
theorem coe_reebFlowKerEquiv_apply (t : ℝ) (x : M) (v : α.kerDistribution x) :
    (hα.reebFlowKerEquiv hc t x v : TangentSpace I (hα.reebFlow hc t x)) =
      mfderiv I I (hα.reebFlow hc t) x v :=
  DFunLike.congr_fun
    ((hα.reebFlowDiffeomorph hc t).mfderivToContinuousLinearEquiv_coe (by simp) (x := x))
    (v : TangentSpace I x)

/-- `(reebFlowKerEquiv ...).symm` acts as `mfderiv I I (hα.reebFlow hc (-t))` at
`hα.reebFlow hc t x`. -/
@[simp]
theorem coe_reebFlowKerEquiv_symm_apply (t : ℝ) (x : M)
    (w : α.kerDistribution (hα.reebFlow hc t x)) :
    ((hα.reebFlowKerEquiv hc t x).symm w : TangentSpace I x) =
      mfderiv I I (hα.reebFlow hc (-t)) (hα.reebFlow hc t x) w := by
  have h1 := hα.coe_reebFlowKerEquiv_apply hc t x ((hα.reebFlowKerEquiv hc t x).symm w)
  rw [LinearEquiv.apply_symm_apply] at h1
  have h2 := congrArg (mfderiv I I (hα.reebFlowDiffeomorph hc t).symm (hα.reebFlow hc t x)) h1
  have hinv := (hα.reebFlowDiffeomorph hc t).mfderiv_symm_apply_mfderiv_apply (by simp) x
    ((hα.reebFlowKerEquiv hc t x).symm w : TangentSpace I x)
  exact hinv.symm.trans h2.symm

/-- `reebFlowKerEquiv` preserves `dα` on `ξ`. -/
theorem mextDeriv_reebFlowKerEquiv (t : ℝ) (x : M) (v w : α.kerDistribution x) :
    mextDeriv α.1 (hα.reebFlow hc t x)
        ![hα.reebFlowKerEquiv hc t x v, hα.reebFlowKerEquiv hc t x w] =
      mextDeriv α.1 x ![v, w] := by
  simp only [coe_reebFlowKerEquiv_apply]
  exact hα.mextDeriv_mfderiv_reebFlow hc t x v w

end Complete

end IsContactForm

end TauCeti.SmoothForm
