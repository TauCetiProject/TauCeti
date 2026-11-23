/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Contact.Contactomorphism
public import TauCeti.Geometry.Contact.Hamiltonian
public import TauCeti.Geometry.Manifold.DifferentialForm.Flow
public import TauCeti.Geometry.Manifold.DifferentialForm.Integration.Path
public import TauCeti.Geometry.Manifold.Flow.Monodromy
public import TauCeti.Geometry.Symplectic.SymplecticTransport
import TauCeti.Geometry.Manifold.VectorField.Regularity
import TauCeti.LinearAlgebra.Charpoly.Quotient

/-!
# Flows of contact Hamiltonian and Reeb vector fields

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
(`IsContactForm.isStrictContactomorphism_globalFlowDiffeomorph_reebVectorField`), and is packaged as
a topological `Flow ℝ M` in `IsContactForm.reebFlow` without rest points
(`IsContactForm.exists_reebFlow_ne`). The complete Reeb flow is jointly smooth
(`IsContactForm.contMDiff_reebFlow_uncurry`) and preserves `α`, `R_α`, `ξ = ker α` and `dα`
(`IsContactForm.mpullback_reebFlow_apply`, `IsContactForm.mfderiv_reebFlow_apply_self`,
`IsContactForm.mfderiv_reebFlow_mem_kerDistribution`, `IsContactForm.mextDeriv_mfderiv_reebFlow`).

## Contact action, symplectic transport, and linearized Reeb return maps

* **Contact action along Reeb integral curves** (`IsContactForm.pathIntegral_of_isMIntegralCurve`,
  `IsContactForm.pathIntegral_zero_of_isMIntegralCurve`): since `α(R_α) = 1`, integrating `α` along
  any Reeb integral curve over `a..b` yields `b - a`.
* **Symplectic transport along the local Reeb flow** (`IsContactForm.kerFlowLinearMap`,
  `IsContactForm.kerFlowEquiv`, `IsContactForm.isSymplectomorphism_kerFlowEquiv`): wherever the
  local Reeb flow `Φ_t` is defined at `p` and sends `p` to `q`, its differential preserves `α` and
  `dα`, hence restricts to a linear symplectomorphism `(ξ_p, dα_p) ≃ₗ[ℝ] (ξ_q, dα_q)`.
* **Linearized Reeb return maps and Poincaré section comparison**
  (`IsContactForm.linearizedReebReturn`, `IsContactForm.linearizedReebReturnEquiv`,
  `IsContactForm.linearizedReebReturn_natCast_mul`,
  `IsContactForm.conj_kerFlowEquiv_linearizedReebReturn`,
  `IsContactForm.charpoly_mfderiv_flowOf_reebVectorField`,
  `IsContactForm.charpoly_normalReturnDerivative_eq`,
  `IsContactForm.hasEigenvalue_returnDerivative_iff`):
  when the maximal flow is defined at `(T, p)` and `Φ_T(p) = p`, restricting `dΦ_T(p)` to
  `ξ_p` yields a linear symplectomorphism whose iterates obey the power law, whose conjugacy
  class is invariant along the trajectory,
  whose full monodromy characteristic polynomial splits as
  `(X - 1)` times its characteristic polynomial, and whose characteristic polynomial and eigenvalues
  agree with those of the normal derivative on a transverse section for the return branch at
  the specified time `T`, including when `T` exceeds the least period.

## References

* F. Bourgeois, Y. Eliashberg, H. Hofer, K. Wysocki, and E. Zehnder,
  *Compactness results in Symplectic Field Theory*, Geom. Topol. 7 (2003), 799–888, Section 2.3.
* H. Geiges, *An Introduction to Contact Topology*, Cambridge University Press, 2008,
  Section 2.3.
-/

public section

noncomputable section

open Function Manifold Module Polynomial Set Filter
open scoped ContDiff Manifold Topology

namespace TauCeti.SmoothForm

section HamiltonianFlow

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
    TauCeti.mpullback I I (flowOf X t) α.val x =
      Real.exp (∫ s in 0..t,
        mvfderiv I f (flowOf X s x) (α.reebVectorField (flowOf X s x))) • α.val x := by
  have hX2 : ContMDiff I I.tangent 2 (fun y ↦ (⟨y, X y⟩ : TangentBundle I M)) :=
    hX.contMDiff hα (by simp) (by norm_num [hf])
  have hRf : Continuous fun y ↦ mvfderiv I f y (α.reebVectorField y) :=
    ((ContMDiff.contMDiff_mvfderiv_apply hf (m := 0) (by norm_num)).comp
      (hα.contMDiff_reebVectorField.of_le (by simp))).continuous
  exact mpullback_flowOf_apply_eq_exp_integral_smul (hX2.of_le one_le_two) hRf α.mdifferentiable
    (hX.mlieDerivForm_eq (hX2.mdifferentiable two_ne_zero)) hx

/-- **Contact Hamiltonian flows preserve the coorientation.** For a contact form `α` and the
contact Hamiltonian vector field `X` of a `C³` function, wherever the maximal flow of `X` through
`x` is defined at time `t`, the time-`t` map pulls `α` back at `x` to a positive multiple of
`α x`. -/
theorem exists_pos_mpullback_flowOf_apply_eq_smul (hα : α.IsContactForm)
    (hX : α.IsContactHamiltonianVectorField f X) (hf : ContMDiff I 𝓘(ℝ) 3 f) {t : ℝ} {x : M}
    (hx : (t, x) ∈ flowDomain X) :
    ∃ c : ℝ, 0 < c ∧ TauCeti.mpullback I I (flowOf X t) α.val x = c • α.val x :=
  ⟨_, Real.exp_pos _, hX.mpullback_flowOf_apply hα hf hx⟩

/-- **Strict contact Hamiltonian flows.** For a contact form `α` and the contact Hamiltonian
vector field `X` of a `C³` function `f`, the maximal flow of `X` preserves `α` wherever it is
defined exactly when `f` is invariant under the Reeb vector field: `R_α f = 0`. -/
theorem mpullback_flowOf_apply_eq_self_iff (hα : α.IsContactForm)
    (hX : α.IsContactHamiltonianVectorField f X) (hf : ContMDiff I 𝓘(ℝ) 3 f) :
    (∀ t x, (t, x) ∈ flowDomain X → TauCeti.mpullback I I (flowOf X t) α.val x = α.val x) ↔
      ∀ x, mvfderiv I f x (α.reebVectorField x) = 0 := by
  have hX2 : ContMDiff I I.tangent 2 (fun y ↦ (⟨y, X y⟩ : TangentBundle I M)) :=
    hX.contMDiff hα (by simp) (by norm_num [hf])
  have hX1 := hX2.of_le one_le_two
  constructor
  · intro h x
    -- The pullbacks `φₜ^* α` at `x` are constant for small `t`, and their velocity at `0` is
    -- `L_X α = (R_α f) α`.
    have hd := hasDerivAt_mpullback_flowOf_zero (hX2.of_le one_le_two) x (α.mdifferentiable x)
    have hconst : (fun s ↦ TauCeti.mpullback I I (flowOf X s) α.val x) =ᶠ[𝓝 0]
        fun _ ↦ α.val x := by
      have hopen : {s | (s, x) ∈ flowDomain X} ∈ 𝓝 (0 : ℝ) :=
        ((isOpen_flowDomain hX1).preimage (continuous_id.prodMk continuous_const)).mem_nhds
          (mem_flowDomain_zero hX1 x)
      filter_upwards [hopen] with s hs
      exact h s x hs
    rw [hX.mlieDerivForm_eq (hX2.mdifferentiable two_ne_zero)] at hd
    have h0 := (hd.congr_of_eventuallyEq hconst.symm).unique
      (hasDerivAt_const (F := E [⋀^Fin 1]→L[ℝ] ℝ) (0 : ℝ) (α.val x))
    have hα₀ : (α.val x : E [⋀^Fin 1]→L[ℝ] ℝ) ≠ 0 :=
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
        (globalFlow X (hX.contMDiff hα (n := 1) (by simp) (hf.of_le (by norm_num))) hc t) α.val x =
      Real.exp (∫ s in 0..t,
        mvfderiv I f (globalFlow X (hX.contMDiff hα (n := 1) (by simp) (hf.of_le (by norm_num)))
          hc s x) (α.reebVectorField (globalFlow X
            (hX.contMDiff hα (n := 1) (by simp) (hf.of_le (by norm_num))) hc s x))) • α.val x := by
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
    TauCeti.mpullback I I (flowOf α.reebVectorField t) α.val x = α.val x := by
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

end HamiltonianFlow

/-! ### Contact action along Reeb integral curves -/

section ReebAction

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I 2 M] {α : SmoothForm I M ℝ 1}

/-- **Contact action along a Reeb integral curve.** Since `α(R_α) = 1`, the line integral of `α`
along any Reeb integral curve `γ` over `a..b` equals the elapsed time `b - a`. -/
theorem IsContactForm.pathIntegral_of_isMIntegralCurve (hα : α.IsContactForm) {γ : ℝ → M}
    (hγ : IsMIntegralCurve γ α.reebVectorField) (a b : ℝ) :
    pathIntegral α.val γ a b = b - a := by
  rw [pathIntegral_def]
  have hint (t : ℝ) : α.val (γ t) (fun _ ↦ Manifold.curveVelocity I γ t) = 1 := by
    have hvel : Manifold.curveVelocity I γ t = α.reebVectorField (γ t) := by
      simpa only [Manifold.curveVelocityWithin_univ] using
        Manifold.curveVelocityWithin_eq_of_hasMFDerivWithinAt (hγ t).hasMFDerivWithinAt
          uniqueDiffWithinAt_univ
    rw [hvel, ← Matrix.vec_single_eq_const, hα.apply_reebVectorField]
  simp_rw [hint]
  exact (intervalIntegral.integral_const (1 : ℝ)).trans (by simp)

/-- The contact action `∫_0^T γ^* α` of a Reeb integral curve over `0..T` is `T`. -/
@[simp]
theorem IsContactForm.pathIntegral_zero_of_isMIntegralCurve (hα : α.IsContactForm)
    {γ : ℝ → M} (hγ : IsMIntegralCurve γ α.reebVectorField) (T : ℝ) :
    pathIntegral α.val γ 0 T = T := by
  rw [hα.pathIntegral_of_isMIntegralCurve hγ, sub_zero]

end ReebAction

/-! ### Symplectic transport along the local Reeb flow -/

section ReebFlow

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [T2Space M] [IsManifold I ∞ M]
  {α : SmoothForm I M ℝ 1}

omit [I.Boundaryless] [T2Space M] in
/-- The Reeb vector field of a contact form is `C¹`. -/
private theorem contMDiff_one_reebVectorField (hα : α.IsContactForm) :
    ContMDiff I I.tangent 1 (fun x ↦ (⟨x, α.reebVectorField x⟩ : TangentBundle I M)) :=
  hα.contMDiff_reebVectorField.of_le (by simp)

/-- Wherever the local Reeb flow is defined, its differential preserves `α` pointwise. -/
@[simp]
theorem IsContactForm.apply_mfderiv_flowOf_reebVectorField (hα : α.IsContactForm) {t : ℝ}
    {x : M} (hx : (t, x) ∈ flowDomain α.reebVectorField) (v : TangentSpace I x) :
    α.val (flowOf α.reebVectorField t x) ![mfderiv I I (flowOf α.reebVectorField t) x v] =
      α.val x ![v] := by
  have h := congrArg (fun β ↦ β ![v]) (hα.mpullback_flowOf_reebVectorField_apply hx)
  simpa only [TauCeti.mpullback_apply, Matrix.cons_val_fin_one,
    ← Matrix.vec_single_eq_const] using h

/-- The differential of the local Reeb flow preserves and reflects membership in `ker α`. -/
theorem IsContactForm.mfderiv_flowOf_reebVectorField_mem_kerDistribution_iff
    (hα : α.IsContactForm) {t : ℝ} {x : M} (hx : (t, x) ∈ flowDomain α.reebVectorField)
    (v : TangentSpace I x) :
    mfderiv I I (flowOf α.reebVectorField t) x v ∈
      α.kerDistribution (flowOf α.reebVectorField t x) ↔ v ∈ α.kerDistribution x := by
  rw [mem_kerDistribution, mem_kerDistribution, hα.apply_mfderiv_flowOf_reebVectorField hx]

/-- Wherever the local Reeb flow is defined, its differential preserves `dα` pointwise. -/
@[simp]
theorem IsContactForm.mextDeriv_mfderiv_flowOf_reebVectorField (hα : α.IsContactForm) {t : ℝ}
    {x : M} (hx : (t, x) ∈ flowDomain α.reebVectorField) (v w : TangentSpace I x) :
    mextDeriv α.val (flowOf α.reebVectorField t x)
      ![mfderiv I I (flowOf α.reebVectorField t) x v,
        mfderiv I I (flowOf α.reebVectorField t) x w] = mextDeriv α.val x ![v, w] := by
  have hinv := mpullback_flowOf_apply_of_mextDeriv_interior_eq_zero
    (hα.contMDiff_reebVectorField.of_le (by simp)) (SmoothForm.isClosed_mextDerivₗ α)
    (by rw [mextDerivₗ_apply, hα.interior_mextDeriv_reebVectorField, mextDeriv_zero]) hx
  rw [mextDerivₗ_apply] at hinv
  exact (TauCeti.mpullback_apply_pair _ _ _ _ _).symm.trans (congrArg (· ![v, w]) hinv)

/-- The differential of the local Reeb flow at `p`, restricted to the contact hyperplane from `ξ_p`
to `ξ_q` when `flowOf α.reebVectorField t p = q`. -/
def IsContactForm.kerFlowLinearMap (hα : α.IsContactForm) {t : ℝ} {p q : M}
    (ht : (t, p) ∈ flowDomain α.reebVectorField) (hq : flowOf α.reebVectorField t p = q) :
    α.kerDistribution p →ₗ[ℝ] α.kerDistribution q := by
  subst hq
  exact (mfderiv I I (flowOf α.reebVectorField t) p).toLinearMap.restrict fun v hv ↦
    (hα.mfderiv_flowOf_reebVectorField_mem_kerDistribution_iff ht v).2 hv

/-- Evaluating `kerFlowLinearMap` agrees with `mfderiv` of the local Reeb flow. -/
@[simp]
theorem IsContactForm.coe_kerFlowLinearMap_apply (hα : α.IsContactForm) {t : ℝ} {p q : M}
    (ht : (t, p) ∈ flowDomain α.reebVectorField) (hq : flowOf α.reebVectorField t p = q)
    (v : α.kerDistribution p) :
    (hα.kerFlowLinearMap ht hq v : TangentSpace I q) =
      mfderiv I I (flowOf α.reebVectorField t) p v := by
  subst hq
  rfl

/-- At time `0`, `kerFlowLinearMap` is the identity of `ξ_p`. -/
@[simp]
theorem IsContactForm.kerFlowLinearMap_zero (hα : α.IsContactForm) {p : M}
    (h0 : ((0 : ℝ), p) ∈ flowDomain α.reebVectorField)
    (hp : flowOf α.reebVectorField 0 p = p) :
    hα.kerFlowLinearMap h0 hp = LinearMap.id := by
  refine LinearMap.ext fun v ↦ Subtype.ext ?_
  rw [hα.coe_kerFlowLinearMap_apply, LinearMap.id_apply]
  exact mfderiv_flowOf_zero_apply_eq_self α.reebVectorField p v.val

/-- Composition law for `kerFlowLinearMap` along the local Reeb flow. -/
theorem IsContactForm.kerFlowLinearMap_comp (hα : α.IsContactForm) {s t : ℝ} {p q r : M}
    (hs : (s, p) ∈ flowDomain α.reebVectorField) (hq : flowOf α.reebVectorField s p = q)
    (ht : (t, q) ∈ flowDomain α.reebVectorField) (hr : flowOf α.reebVectorField t q = r)
    (hst : (s + t, p) ∈ flowDomain α.reebVectorField)
    (hsr : flowOf α.reebVectorField (s + t) p = r) :
    (hα.kerFlowLinearMap ht hr).comp (hα.kerFlowLinearMap hs hq) =
      hα.kerFlowLinearMap hst hsr := by
  refine LinearMap.ext fun v ↦ Subtype.ext ?_
  rw [LinearMap.comp_apply, hα.coe_kerFlowLinearMap_apply, hα.coe_kerFlowLinearMap_apply,
    hα.coe_kerFlowLinearMap_apply]
  exact mfderiv_flowOf_add_apply (contMDiff_one_reebVectorField hα) hs hq ht v.val

/-- The linear equivalence `ξ_p ≃ₗ[ℝ] ξ_q` induced by the differential of the local Reeb
flow when `flowOf α.reebVectorField t p = q`. Its inverse is transport along time `-t`. -/
def IsContactForm.kerFlowEquiv (hα : α.IsContactForm) {t : ℝ} {p q : M}
    (ht : (t, p) ∈ flowDomain α.reebVectorField) (hq : flowOf α.reebVectorField t p = q) :
    α.kerDistribution p ≃ₗ[ℝ] α.kerDistribution q :=
  let hv := contMDiff_one_reebVectorField hα
  have hneg : (-t, q) ∈ flowDomain α.reebVectorField := hq ▸ neg_mem_flowDomain_flowOf hv ht
  have hback : flowOf α.reebVectorField (-t) q = p := hq ▸ flowOf_neg_flowOf hv ht
  LinearEquiv.ofLinearMap (hα.kerFlowLinearMap ht hq) (hα.kerFlowLinearMap hneg hback)
    (LinearMap.ext fun u ↦ Subtype.ext <| by
      rw [LinearMap.comp_apply, hα.coe_kerFlowLinearMap_apply, hα.coe_kerFlowLinearMap_apply,
        LinearMap.id_apply]
      exact (mfderiv_flowOf_add_apply hv hneg hback ht u.val).trans
        (by rw [neg_add_cancel]; exact mfderiv_flowOf_zero_apply_eq_self _ q u.val))
    (LinearMap.ext fun v ↦ Subtype.ext <| by
      rw [LinearMap.comp_apply, hα.coe_kerFlowLinearMap_apply, hα.coe_kerFlowLinearMap_apply,
        LinearMap.id_apply]
      exact (mfderiv_flowOf_add_apply hv ht hq hneg v.val).trans
        (by rw [add_neg_cancel]; exact mfderiv_flowOf_zero_apply_eq_self _ p v.val))

@[simp]
theorem IsContactForm.toLinearMap_kerFlowEquiv (hα : α.IsContactForm) {t : ℝ} {p q : M}
    (ht : (t, p) ∈ flowDomain α.reebVectorField) (hq : flowOf α.reebVectorField t p = q) :
    (hα.kerFlowEquiv ht hq).toLinearMap = hα.kerFlowLinearMap ht hq := by
  unfold IsContactForm.kerFlowEquiv
  rfl

@[simp]
theorem IsContactForm.coe_kerFlowEquiv_apply (hα : α.IsContactForm) {t : ℝ} {p q : M}
    (ht : (t, p) ∈ flowDomain α.reebVectorField) (hq : flowOf α.reebVectorField t p = q)
    (v : α.kerDistribution p) :
    (hα.kerFlowEquiv ht hq v : TangentSpace I q) =
      mfderiv I I (flowOf α.reebVectorField t) p v := by
  unfold IsContactForm.kerFlowEquiv
  exact hα.coe_kerFlowLinearMap_apply ht hq v

@[simp]
theorem IsContactForm.coe_kerFlowEquiv_symm_apply (hα : α.IsContactForm) {t : ℝ} {p q : M}
    (ht : (t, p) ∈ flowDomain α.reebVectorField) (hq : flowOf α.reebVectorField t p = q)
    (u : α.kerDistribution q) :
    ((hα.kerFlowEquiv ht hq).symm u : TangentSpace I p) =
      mfderiv I I (flowOf α.reebVectorField (-t)) q u := by
  let hv := contMDiff_one_reebVectorField hα
  unfold IsContactForm.kerFlowEquiv
  exact hα.coe_kerFlowLinearMap_apply
    (hq ▸ neg_mem_flowDomain_flowOf hv ht) (hq ▸ flowOf_neg_flowOf hv ht) u

/-- **The local Reeb flow acts on the contact distribution by linear symplectomorphisms.** -/
theorem IsContactForm.isSymplectomorphism_kerFlowEquiv (hα : α.IsContactForm) {t : ℝ} {p q : M}
    (ht : (t, p) ∈ flowDomain α.reebVectorField) (hq : flowOf α.reebVectorField t p = q) :
    SymplecticForm.IsSymplectomorphism (hα.kerSymplecticForm p) (hα.kerSymplecticForm q)
      (hα.kerFlowEquiv ht hq) := by
  subst hq
  rw [SymplecticForm.isSymplectomorphism_iff]
  intro v w
  simp only [kerSymplecticForm_apply, coe_kerFlowEquiv_apply,
    hα.mextDeriv_mfderiv_flowOf_reebVectorField ht]

/-! ### The linearized Reeb return map, monodromy and Poincaré sections -/

/-- **The linearized Reeb return map** at a point `p` returning to itself at time `T` under the
Reeb flow: the restriction of `d(flowOf α.reebVectorField T)_p` to `ξ_p`. -/
def IsContactForm.linearizedReebReturn (hα : α.IsContactForm) {T : ℝ} {p : M}
    (hT : (T, p) ∈ flowDomain α.reebVectorField) (hp : flowOf α.reebVectorField T p = p) :
    Module.End ℝ (α.kerDistribution p) :=
  hα.kerFlowLinearMap hT hp

/-- The linearized Reeb return map packaged as a linear equivalence of `ξ_p`. -/
def IsContactForm.linearizedReebReturnEquiv (hα : α.IsContactForm) {T : ℝ} {p : M}
    (hT : (T, p) ∈ flowDomain α.reebVectorField) (hp : flowOf α.reebVectorField T p = p) :
    α.kerDistribution p ≃ₗ[ℝ] α.kerDistribution p :=
  hα.kerFlowEquiv hT hp

@[simp]
theorem IsContactForm.toLinearMap_linearizedReebReturnEquiv (hα : α.IsContactForm) {T : ℝ}
    {p : M} (hT : (T, p) ∈ flowDomain α.reebVectorField)
    (hp : flowOf α.reebVectorField T p = p) :
    (hα.linearizedReebReturnEquiv hT hp).toLinearMap = hα.linearizedReebReturn hT hp := by
  unfold IsContactForm.linearizedReebReturnEquiv IsContactForm.linearizedReebReturn
  exact hα.toLinearMap_kerFlowEquiv hT hp

@[simp]
theorem IsContactForm.coe_linearizedReebReturn_apply (hα : α.IsContactForm) {T : ℝ} {p : M}
    (hT : (T, p) ∈ flowDomain α.reebVectorField) (hp : flowOf α.reebVectorField T p = p)
    (v : α.kerDistribution p) :
    (hα.linearizedReebReturn hT hp v : TangentSpace I p) =
      mfderiv I I (flowOf α.reebVectorField T) p v := by
  unfold IsContactForm.linearizedReebReturn
  exact hα.coe_kerFlowLinearMap_apply hT hp v

/-- Equal return times define the same linearized Reeb return map. -/
theorem IsContactForm.linearizedReebReturn_congr_time (hα : α.IsContactForm) {T₁ T₂ : ℝ}
    {p : M} (hT₁ : (T₁, p) ∈ flowDomain α.reebVectorField)
    (hp₁ : flowOf α.reebVectorField T₁ p = p)
    (hT₂ : (T₂, p) ∈ flowDomain α.reebVectorField)
    (hp₂ : flowOf α.reebVectorField T₂ p = p) (hT : T₁ = T₂) :
    hα.linearizedReebReturn hT₁ hp₁ = hα.linearizedReebReturn hT₂ hp₂ := by
  subst hT
  rfl

/-- At return time `0`, the linearized Reeb return map is `1`. -/
@[simp]
theorem IsContactForm.linearizedReebReturn_zero (hα : α.IsContactForm) {p : M}
    (h0 : ((0 : ℝ), p) ∈ flowDomain α.reebVectorField)
    (hp : flowOf α.reebVectorField 0 p = p) :
    hα.linearizedReebReturn h0 hp = 1 :=
  hα.kerFlowLinearMap_zero h0 hp

/-- **The linearized Reeb return map is a linear symplectomorphism of `(ξ_p, dα_p)`.** -/
theorem IsContactForm.isSymplectomorphism_linearizedReebReturnEquiv (hα : α.IsContactForm)
    {T : ℝ} {p : M} (hT : (T, p) ∈ flowDomain α.reebVectorField)
    (hp : flowOf α.reebVectorField T p = p) :
    SymplecticForm.IsSymplectomorphism (hα.kerSymplecticForm p) (hα.kerSymplecticForm p)
      (hα.linearizedReebReturnEquiv hT hp) :=
  hα.isSymplectomorphism_kerFlowEquiv hT hp

/-- **Iterate formula for the linearized Reeb return map.** At an iterate return time `k * T`, the
linearized Reeb return map is the `k`-th power of the one at time `T`. -/
theorem IsContactForm.linearizedReebReturn_natCast_mul (hα : α.IsContactForm) {T : ℝ} {p : M}
    (hT : (T, p) ∈ flowDomain α.reebVectorField) (hp : flowOf α.reebVectorField T p = p)
    (k : ℕ) (hkT : ((k : ℝ) * T, p) ∈ flowDomain α.reebVectorField)
    (hkp : flowOf α.reebVectorField ((k : ℝ) * T) p = p) :
    hα.linearizedReebReturn hkT hkp = hα.linearizedReebReturn hT hp ^ k := by
  have hv := contMDiff_one_reebVectorField hα
  induction k with
  | zero =>
    simp_rw [Nat.cast_zero, zero_mul, pow_zero] at hkT hkp ⊢
    exact hα.linearizedReebReturn_zero hkT hkp
  | succ k ih =>
    obtain ⟨hkT', hkp'⟩ := flowOf_natCast_mul_of_flowOf_eq hv hT hp k
    have hadd : T + (k : ℝ) * T = ((k + 1 : ℕ) : ℝ) * T := by push_cast; ring
    rw [pow_succ, ← ih hkT' hkp']
    refine LinearMap.ext fun v ↦ Subtype.ext ?_
    rw [mul_apply_eq_comp, hα.coe_linearizedReebReturn_apply, hα.coe_linearizedReebReturn_apply,
      hα.coe_linearizedReebReturn_apply, ← hadd]
    exact (mfderiv_flowOf_add_apply hv hT hp hkT' v.val).symm

/-- **Base-point conjugacy along a Reeb orbit.** Flowing `p` to `q` at time `s` conjugates the
linearized Reeb return map at `p` to that at `q` via `kerFlowEquiv`. -/
theorem IsContactForm.conj_kerFlowEquiv_linearizedReebReturn (hα : α.IsContactForm) {s T : ℝ}
    {p q : M} (hs : (s, p) ∈ flowDomain α.reebVectorField)
    (hq : flowOf α.reebVectorField s p = q) (hT : (T, p) ∈ flowDomain α.reebVectorField)
    (hp : flowOf α.reebVectorField T p = p) (hTq : (T, q) ∈ flowDomain α.reebVectorField)
    (hq' : flowOf α.reebVectorField T q = q) :
    (hα.kerFlowEquiv hs hq).conj (hα.linearizedReebReturn hT hp) =
      hα.linearizedReebReturn hTq hq' := by
  have hv := contMDiff_one_reebVectorField hα
  have hintertwine : ∀ v : α.kerDistribution p,
      hα.kerFlowEquiv hs hq (hα.linearizedReebReturn hT hp v) =
        hα.linearizedReebReturn hTq hq' (hα.kerFlowEquiv hs hq v) := fun v ↦ Subtype.ext <| by
    rw [hα.coe_kerFlowEquiv_apply, hα.coe_linearizedReebReturn_apply,
      hα.coe_linearizedReebReturn_apply, hα.coe_kerFlowEquiv_apply,
      mfderiv_flowOf_add_apply hv hT hp hs v.val, mfderiv_flowOf_add_apply hv hs hq hTq v.val,
          add_comm]
  refine LinearMap.ext fun u ↦ ?_
  rw [LinearEquiv.conj_apply_apply, hintertwine, LinearEquiv.apply_symm_apply]

/-- The characteristic polynomial of the linearized Reeb return map is invariant along the
orbit. -/
theorem IsContactForm.charpoly_linearizedReebReturn_eq_of_flowOf (hα : α.IsContactForm)
    {s T : ℝ} {p q : M} (hs : (s, p) ∈ flowDomain α.reebVectorField)
    (hq : flowOf α.reebVectorField s p = q) (hT : (T, p) ∈ flowDomain α.reebVectorField)
    (hp : flowOf α.reebVectorField T p = p) (hTq : (T, q) ∈ flowDomain α.reebVectorField)
    (hq' : flowOf α.reebVectorField T q = q) :
    (hα.linearizedReebReturn hT hp).charpoly = (hα.linearizedReebReturn hTq hq').charpoly := by
  rw [← hα.conj_kerFlowEquiv_linearizedReebReturn hs hq hT hp hTq hq', LinearEquiv.charpoly_conj]

/-- **Monodromy splitting of a closed Reeb orbit.** Because `T_p M = ξ_p ⊕ ℝ R_α(p)` is
preserved by `dΦ_T(p)` with `dΦ_T(p)(R_α(p)) = R_α(p)`, the characteristic polynomial of the
full monodromy `dΦ_T(p)` is `(X - 1)` times that of the linearized Reeb return map on `ξ_p`. -/
theorem IsContactForm.charpoly_mfderiv_flowOf_reebVectorField (hα : α.IsContactForm) {T : ℝ}
    {p : M} (hT : (T, p) ∈ flowDomain α.reebVectorField)
    (hp : flowOf α.reebVectorField T p = p) :
    (mfderiv I I (flowOf α.reebVectorField T) p).toLinearMap.charpoly =
      (X - 1) * (hα.linearizedReebReturn hT hp).charpoly := by
  have hv := contMDiff_one_reebVectorField hα
  let Mo : Module.End ℝ (TangentSpace I p) :=
    (mfderiv I I (flowOf α.reebVectorField T) p).toLinearMap
  have hfix : Mo (α.reebVectorField p) = α.reebVectorField p :=
    (mfderiv_flowOf_apply_self hv hT).trans (congrArg α.reebVectorField hp)
  set K := α.kerDistribution p
  set L := ℝ ∙ α.reebVectorField p
  have hMo : ∀ v : TangentSpace I p, Mo v = mfderiv I I (flowOf α.reebVectorField T) p v :=
    fun v ↦ congrFun (ContinuousLinearMap.coe_coe (mfderiv I I (flowOf α.reebVectorField T) p)) v
  have hK : K ≤ K.comap Mo := fun v hv' ↦ by
    rw [Submodule.mem_comap, hMo]
    have hm := (hα.mfderiv_flowOf_reebVectorField_mem_kerDistribution_iff hT v).2 hv'
    rwa [hp] at hm
  have hres : Mo.restrict hK = hα.linearizedReebReturn hT hp := by
    refine LinearMap.ext fun v ↦ Subtype.ext ?_
    rw [LinearMap.coe_restrict_apply, hα.coe_linearizedReebReturn_apply, hMo]
  let e := Submodule.quotientEquivOfIsCompl K L (hα.isCompl_kerDistribution_span_reebVectorField p)
  have hQ : e.conj (K.mapQ K Mo hK) = 1 := by
    refine LinearMap.ext fun ⟨u, hu⟩ ↦ ?_
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hu
    simp only [e, LinearEquiv.conj_apply, LinearMap.coe_comp, LinearEquiv.coe_coe, comp_apply,
      Submodule.quotientEquivOfIsCompl_symm_apply, Submodule.mapQ_apply,
      Submodule.quotientEquivOfIsCompl_apply_mk, map_smul, hfix,
      Submodule.projectionOnto_apply_of_mem_left _ hu, one_apply_eq_self]
  have hcharQ : (K.mapQ K Mo hK).charpoly = X - 1 := by
    rw [← LinearEquiv.charpoly_conj e, hQ, LinearMap.charpoly_one,
      finrank_span_singleton (hα.reebVectorField_ne_zero p), pow_one]
  rw [LinearMap.charpoly_eq_charpoly_restrict_mul_charpoly_mapQ K Mo hK, hres, hcharQ, mul_comm]

/-- **Poincaré section comparison.** For any local scalar function `g` at `p` transverse to the
Reeb vector field (`dg_p(R_α(p)) ≠ 0`), the normal return derivative on `ker dg_p` has the exact
same characteristic polynomial as the linearized Reeb return map on `ξ_p`. -/
theorem IsContactForm.charpoly_normalReturnDerivative_eq (hα : α.IsContactForm) {g : M → ℝ}
    {T : ℝ} {p : M} (hT : (T, p) ∈ flowDomain α.reebVectorField)
    (hp : flowOf α.reebVectorField T p = p) (hg : ContMDiffAt I 𝓘(ℝ) 1 g p)
    (hgv : mvfderiv I g p (α.reebVectorField p) ≠ 0)
    {h : LinearMap.range (returnDerivative α.reebVectorField g T p) ≤
      LinearMap.ker (mvfderiv I g p : TangentSpace I p →ₗ[ℝ] ℝ)} :
    (normalReturnDerivative α.reebVectorField g T p h).charpoly =
      (hα.linearizedReebReturn hT hp).charpoly := by
  have hv := contMDiff_one_reebVectorField hα
  have hX : (X - 1 : ℝ[X]) ≠ 0 := by simpa using Polynomial.X_sub_C_ne_zero (1 : ℝ)
  refine mul_left_cancel₀ hX ?_
  rw [← charpoly_mfderiv_flowOf_eq_X_sub_one_mul hv hT hp hg hgv (h := h),
    hα.charpoly_mfderiv_flowOf_reebVectorField hT hp]

/-- Every eigenvalue (including `1`) of the normal return derivative of any transverse section
matches that of the linearized Reeb return map on `ξ_p`. -/
theorem IsContactForm.hasEigenvalue_normalReturnDerivative_iff (hα : α.IsContactForm)
    {g : M → ℝ} {T : ℝ} {p : M} (hT : (T, p) ∈ flowDomain α.reebVectorField)
    (hp : flowOf α.reebVectorField T p = p) (hg : ContMDiffAt I 𝓘(ℝ) 1 g p)
    (hgv : mvfderiv I g p (α.reebVectorField p) ≠ 0)
    {h : LinearMap.range (returnDerivative α.reebVectorField g T p) ≤
      LinearMap.ker (mvfderiv I g p : TangentSpace I p →ₗ[ℝ] ℝ)} (μ : ℝ) :
    (normalReturnDerivative α.reebVectorField g T p h).HasEigenvalue μ ↔
      (hα.linearizedReebReturn hT hp).HasEigenvalue μ := by
  rw [Module.End.hasEigenvalue_iff_isRoot_charpoly, Module.End.hasEigenvalue_iff_isRoot_charpoly,
    hα.charpoly_normalReturnDerivative_eq hT hp hg hgv]

/-- Every nonzero eigenvalue (in particular `μ = 1`) of the full section `returnDerivative` on
`T_p M` matches that of the linearized Reeb return map on `ξ_p`. -/
theorem IsContactForm.hasEigenvalue_returnDerivative_iff (hα : α.IsContactForm) {g : M → ℝ}
    {T : ℝ} {p : M} (hT : (T, p) ∈ flowDomain α.reebVectorField)
    (hp : flowOf α.reebVectorField T p = p) (hg : ContMDiffAt I 𝓘(ℝ) 1 g p)
    (hgv : mvfderiv I g p (α.reebVectorField p) ≠ 0) {μ : ℝ} (hμ : μ ≠ 0) :
    (returnDerivative α.reebVectorField g T p).HasEigenvalue μ ↔
      (hα.linearizedReebReturn hT hp).HasEigenvalue μ := by
  have hv := contMDiff_one_reebVectorField hα
  have hK := range_returnDerivative_le_ker hv hT hp hg hgv
  rw [← hα.hasEigenvalue_normalReturnDerivative_iff hT hp hg hgv (h := hK) μ,
    Module.End.hasEigenvalue_iff_isRoot_charpoly, Module.End.hasEigenvalue_iff_isRoot_charpoly,
    charpoly_returnDerivative_eq_X_mul hgv (h := hK), IsRoot.def, IsRoot.def, eval_mul, eval_X,
    mul_eq_zero, or_iff_right hμ]

namespace IsContactForm

/-- The linearized Reeb return map at a return time `T` has no eigenvalue `1` iff some local
transverse section through `p` has a return derivative without eigenvalue `1` for the branch at
time `T`. The branch uses the specified return time, which need not be the least period. -/
theorem not_hasEigenvalue_one_linearizedReebReturn_iff_exists_not_hasEigenvalue_returnDerivative
    (hα : α.IsContactForm) {T : ℝ} {p : M} (hT : (T, p) ∈ flowDomain α.reebVectorField)
    (hp : flowOf α.reebVectorField T p = p) :
    ¬(hα.linearizedReebReturn hT hp).HasEigenvalue 1 ↔
      ∃ g : M → ℝ, ContMDiffAt I 𝓘(ℝ) 1 g p ∧
        mvfderiv I g p (α.reebVectorField p) ≠ 0 ∧
        ¬(returnDerivative α.reebVectorField g T p).HasEigenvalue 1 := by
  constructor
  · intro hnd
    obtain ⟨g, hg, hgv⟩ := hα.exists_contMDiffAt_and_mvfderiv_reebVectorField_eq_one 1 p
    have hgv0 : mvfderiv I g p (α.reebVectorField p) ≠ 0 := hgv ▸ one_ne_zero
    exact ⟨g, hg, hgv0, mt (hα.hasEigenvalue_returnDerivative_iff hT hp hg hgv0 one_ne_zero).1 hnd⟩
  · rintro ⟨g, hg, hgv, hnd⟩
    exact mt (hα.hasEigenvalue_returnDerivative_iff hT hp hg hgv one_ne_zero).2 hnd

end IsContactForm

/-- **Degeneracy of identity return in dimension at least `3`.** If `2 ≤ finrank ℝ E` (so the
contact manifold has odd dimension `2 n + 1 ≥ 3` and `dim ξ_p ≥ 1`) and `dΦ_T(p) = id`, then
`1` is an eigenvalue of the linearized Reeb return map. -/
theorem IsContactForm.hasEigenvalue_one_linearizedReebReturn_of_mfderiv_eq_id
    (hα : α.IsContactForm) {T : ℝ} {p : M} (hT : (T, p) ∈ flowDomain α.reebVectorField)
    (hp : flowOf α.reebVectorField T p = p) (hdim : 2 ≤ finrank ℝ E)
    (hid : mfderiv I I (flowOf α.reebVectorField T) p =
      ContinuousLinearMap.id ℝ (TangentSpace I p)) :
    (hα.linearizedReebReturn hT hp).HasEigenvalue 1 := by
  have hker : 0 < finrank ℝ (α.kerDistribution p) := by
    have := hα.finrank_kerDistribution_add_one p
    omega
  have : Nontrivial (α.kerDistribution p) := Module.nontrivial_of_finrank_pos hker
  obtain ⟨v, hv0⟩ := exists_ne (0 : α.kerDistribution p)
  refine Module.End.hasEigenvalue_of_hasEigenvector ⟨Module.End.mem_eigenspace_iff.2 ?_, hv0⟩
  apply Subtype.ext
  rw [SetLike.val_smul, one_smul, hα.coe_linearizedReebReturn_apply]
  exact DFunLike.congr_fun hid v.val

/-! ### Complete Reeb flows -/

/-- The global Reeb flow of a contact form whose Reeb vector field is complete. -/
def IsContactForm.reebFlow (hα : α.IsContactForm)
    (hc : IsCompleteVectorField α.reebVectorField) : Flow ℝ M :=
  globalFlow α.reebVectorField (contMDiff_one_reebVectorField hα) hc

@[simp]
theorem IsContactForm.reebFlow_apply (hα : α.IsContactForm)
    (hc : IsCompleteVectorField α.reebVectorField) (t : ℝ) (x : M) :
    hα.reebFlow hc t x = flowOf α.reebVectorField t x := by
  rw [reebFlow, ← flowOf_eq_globalFlow]

/-- The Reeb flow has no rest points, since the Reeb vector field vanishes nowhere. -/
theorem IsContactForm.exists_reebFlow_ne (hα : α.IsContactForm)
    (hc : IsCompleteVectorField α.reebVectorField) (x : M) :
    ∃ t, hα.reebFlow hc t x ≠ x := by
  by_contra h
  have hfix : ∀ t, globalFlow α.reebVectorField (contMDiff_one_reebVectorField hα) hc t x = x :=
    by simpa only [not_exists, not_not, reebFlow] using h
  exact hα.reebVectorField_ne_zero x
    ((forall_globalFlow_eq_self_iff (contMDiff_one_reebVectorField hα) hc x).mp hfix)

/-- Every orbit of `reebFlow` is an integral curve of `α.reebVectorField`. -/
theorem IsContactForm.isMIntegralCurve_reebFlow (hα : α.IsContactForm)
    (hc : IsCompleteVectorField α.reebVectorField) (x : M) :
    IsMIntegralCurve (fun t ↦ hα.reebFlow hc t x) α.reebVectorField :=
  isMIntegralCurve_globalFlow (contMDiff_one_reebVectorField hα) hc x

/-- On a compact boundaryless manifold, the Reeb vector field of any contact form is complete. -/
theorem IsContactForm.isCompleteVectorField_reebVectorField [CompactSpace M]
    (hα : α.IsContactForm) : IsCompleteVectorField α.reebVectorField :=
  isCompleteVectorField_of_compactSpace (contMDiff_one_reebVectorField hα)

namespace IsContactForm

section Complete

variable (hα : α.IsContactForm) (hc : IsCompleteVectorField α.reebVectorField)

/-- Unfolds `IsContactForm.reebFlow` as `TauCeti.globalFlow` of `α.reebVectorField`. -/
theorem reebFlow_def :
    hα.reebFlow hc =
      globalFlow α.reebVectorField (hα.contMDiff_reebVectorField.of_le (by simp)) hc :=
  (rfl)

/-- The Reeb flow equals the time-`t` global flow diffeomorphism at every point. -/
theorem reebFlow_eq_globalFlowDiffeomorph (t : ℝ) (x : M) :
    hα.reebFlow hc t x =
      globalFlowDiffeomorph hc le_top hα.contMDiff_reebVectorField t x :=
  (globalFlowDiffeomorph_apply hc le_top hα.contMDiff_reebVectorField t x).symm

/-- As a function, the time-`t` map of `reebFlow` agrees with `globalFlowDiffeomorph`. -/
theorem reebFlow_eq_coe_globalFlowDiffeomorph (t : ℝ) :
    hα.reebFlow hc t = ⇑(globalFlowDiffeomorph hc le_top hα.contMDiff_reebVectorField t) :=
  funext (hα.reebFlow_eq_globalFlowDiffeomorph hc t)

/-- Every integral curve of the Reeb vector field is an orbit of the Reeb flow. -/
theorem reebFlow_eq_of_isMIntegralCurve {γ : ℝ → M}
    (hγ : IsMIntegralCurve γ α.reebVectorField) (t : ℝ) :
    hα.reebFlow hc t (γ 0) = γ t :=
  globalFlow_eq_of_isMIntegralCurve _ hc hγ t

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
    TauCeti.mpullback I I (hα.reebFlow hc t) α.val x = α.val x := by
  rw [show hα.reebFlow hc t = flowOf α.reebVectorField t from funext (hα.reebFlow_apply hc t)]
  exact hα.mpullback_flowOf_reebVectorField_apply (hc.mem_flowDomain t x)

/-- The differential of the Reeb flow preserves the Reeb vector field. -/
theorem mfderiv_reebFlow_apply_self (t : ℝ) (x : M) :
    mfderiv I I (hα.reebFlow hc t) x (α.reebVectorField x) =
      α.reebVectorField (hα.reebFlow hc t x) :=
  mfderiv_globalFlow_apply_self _ hc t x

/-- The differential of the Reeb flow maps the contact distribution `ξ = ker α` to itself. -/
theorem mfderiv_reebFlow_mem_kerDistribution (t : ℝ) {x : M} {v : TangentSpace I x}
    (hv : v ∈ α.kerDistribution x) :
    mfderiv I I (hα.reebFlow hc t) x v ∈ α.kerDistribution (hα.reebFlow hc t x) := by
  rw [show hα.reebFlow hc t = flowOf α.reebVectorField t from funext (hα.reebFlow_apply hc t)]
  exact (hα.mfderiv_flowOf_reebVectorField_mem_kerDistribution_iff
    (hc.mem_flowDomain t x) v).2 hv

/-- The Reeb flow preserves the exterior derivative `dα` on tangent vectors. -/
theorem mextDeriv_mfderiv_reebFlow (t : ℝ) (x : M) (v w : TangentSpace I x) :
    mextDeriv α.val (hα.reebFlow hc t x)
        ![mfderiv I I (hα.reebFlow hc t) x v, mfderiv I I (hα.reebFlow hc t) x w] =
      mextDeriv α.val x ![v, w] := by
  rw [show hα.reebFlow hc t = flowOf α.reebVectorField t from funext (hα.reebFlow_apply hc t)]
  exact hα.mextDeriv_mfderiv_flowOf_reebVectorField (hc.mem_flowDomain t x) v w

end Complete

end IsContactForm

end ReebFlow

end TauCeti.SmoothForm
