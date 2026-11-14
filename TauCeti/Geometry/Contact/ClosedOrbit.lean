/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Dynamics.Flow.ClosedOrbit
public import TauCeti.Geometry.Contact.Flow
public import TauCeti.Geometry.Manifold.DifferentialForm.AddCircle
public import TauCeti.Geometry.Manifold.DifferentialForm.Integration.Path
public import TauCeti.Geometry.Manifold.Flow.Monodromy
public import TauCeti.Geometry.Manifold.Flow.NondegenerateOrbit
public import TauCeti.Geometry.Manifold.IntegralCurve.GlobalFlow
public import TauCeti.Geometry.Manifold.VectorField.AddCircle
public import TauCeti.Geometry.Manifold.VectorField.Transverse
public import TauCeti.Geometry.Symplectic.SymplecticTransport
import TauCeti.Dynamics.Flow.PeriodBound
import TauCeti.Geometry.Contact.Flat
import TauCeti.LinearAlgebra.Charpoly.Quotient

/-!
# Closed Reeb orbits, linearized return maps and finiteness below an action bound

Let `α` be a contact form on a boundaryless smooth manifold `M`, with contact distribution
`ξ = ker α` (`TauCeti.SmoothForm.kerDistribution`) and Reeb vector field `R_α`
(`TauCeti.SmoothForm.reebVectorField`). This file develops the geometry and dynamics of periodic
Reeb trajectories and unparametrized closed Reeb orbits, culminating in finiteness of nondegenerate
closed Reeb orbits (including multiply covered ones) below any action bound.

## Contact action and symplectic transport along the Reeb flow

* **Symplectic contact hyperplanes** (`IsContactForm.kerSymplecticForm`): at every point `x`, the
  restriction of `dα_x` to `ξ_x = ker α_x` is a `TauCeti.SymplecticForm`.
* **Contact action equals period** (`IsContactForm.pathIntegral_of_isMIntegralCurve`,
  `IsContactForm.pathIntegral_periodicTrajectory`): since `α(R_α) = 1`, integrating `α` along any
  Reeb integral curve over `a..b` yields `b - a`; in particular the contact action `∫_γ α` of a
  periodic Reeb trajectory `γ` of period `T` is `T`.
* **Symplectic transport** (`IsContactForm.kerFlowEquiv`,
  `IsContactForm.isSymplectomorphism_kerFlowEquiv`): wherever the local Reeb flow `Φ_t` is defined
  at `p` and sends `p` to `q`, its differential preserves `α` and `dα`, hence restricts to a
  linear symplectomorphism `(ξ_p, dα_p) ≃ₗ[ℝ] (ξ_q, dα_q)`.

## The linearized Reeb return map and nondegeneracy

When `p` returns to itself at time `T` under the Reeb flow (`Φ_T(p) = p`), the restriction of
`dΦ_T(p)` to the contact hyperplane `ξ_p` is the **linearized Reeb return map**
`IsContactForm.linearizedReebReturn` (packaged as a linear equivalence in
`IsContactForm.linearizedReebReturnEquiv`).

* It is a linear symplectomorphism of `(ξ_p, dα_p)`
  (`IsContactForm.isSymplectomorphism_linearizedReebReturnEquiv`).
* At an iterate time `k * T`, it is the `k`-th power of the return map at time `T`
  (`IsContactForm.linearizedReebReturn_natCast_mul`).
* Flowing `p` to another point `q = Φ_s(p)` of the orbit conjugates the linearized return map by
  `kerFlowEquiv` (`IsContactForm.conj_kerFlowEquiv_linearizedReebReturn`), so its characteristic
  polynomial and eigenvalues are invariants of the unparametrized closed orbit.
* Because `T_p M = ξ_p ⊕ ℝ R_α(p)` is a `dΦ_T(p)`-invariant direct sum with
  `dΦ_T(p)(R_α(p)) = R_α(p)`, the full monodromy `dΦ_T(p)` has characteristic polynomial
  `(X - 1)` times that of the linearized Reeb return map
  (`IsContactForm.charpoly_mfderiv_flowOf_reebVectorField`). Comparing with
  `TauCeti.charpoly_mfderiv_flowOf_eq_X_sub_one_mul` identifies the characteristic polynomial (and
  hence all eigenvalues) of `linearizedReebReturn` with that of the normal return derivative of
  *any* local transverse Poincaré section (`IsContactForm.charpoly_normalReturnDerivative_eq`,
  `IsContactForm.hasEigenvalue_returnDerivative_iff`).

For a complete Reeb vector field, `IsContactForm.reebFlow` packages the Reeb flow as a `Flow ℝ M`,
so periodic Reeb trajectories, unparametrized closed orbits, primitive orbits, covering
multiplicities `κ_γ`, circle parametrizations, cyclic reparametrization groups `ℤ/κ_γ` and the
`κ_γ` asymptotic markers over a basepoint are inherited directly from
`TauCeti.Dynamics.Flow.ClosedOrbit`. A closed Reeb orbit is **nondegenerate**
(`IsContactForm.IsNondegenerateOrbit`) when `1` is not an eigenvalue of its linearized Reeb return
map; its `k`-fold iterate is nondegenerate iff `1` is not an eigenvalue of the `k`-th power
(`IsContactForm.isNondegenerateOrbit_iterate_mk_iff`).

## Edge cases, circle model and finiteness

* **Degeneracy witnesses**: if `dim M ≥ 3` (`2 ≤ finrank ℝ E`) and `dΦ_T(p) = id` (as on Zoll
  or Morse–Bott families such as the Hopf fibration), `1` is an eigenvalue of
  `linearizedReebReturn` (`IsContactForm.hasEigenvalue_one_linearizedReebReturn_of_mfderiv_eq_id`).
  If `-1` is an eigenvalue of the primitive return map, the double cover `γ.iterate 2` is
  degenerate (`IsContactForm.not_isNondegenerateOrbit_iterate_two_of_hasEigenvalue_neg_one`).
* **Circle witness** (`AddCircle.isContactForm_timeForm`,
  `AddCircle.isNondegenerateOrbit_timeForm`): on the `1`-dimensional circle `AddCircle p` (`p > 0`),
  `AddCircle.timeForm p` is a contact form with trivial contact hyperplane `⊥`, Reeb field
  `AddCircle.timeVectorField p`, Reeb flow `AddCircle.translationFlow p`, and every closed Reeb
  orbit (primitive of period `p` and all `k`-fold covers of period `k * p`) is nondegenerate.
* **Finiteness below an action bound**
  (`IsContactForm.finite_closedOrbit_inter_nonempty_and_period_le`,
  `IsContactForm.finite_closedOrbit_period_le`): for a complete Reeb flow and a compact subset `K`,
  if all closed Reeb orbits meeting `K` of period (equivalently, contact action) at most `A` are
  nondegenerate, there are only finitely many of them (including covers); in particular, on a
  compact boundaryless contact manifold there are finitely many nondegenerate closed Reeb orbits of
  period at most `A`.

## References

* F. Bourgeois, Y. Eliashberg, H. Hofer, K. Wysocki, E. Zehnder,
  *Compactness results in Symplectic Field Theory*, Geom. Topol. 7 (2003), 799–888, Section 2.3.
* Y. Eliashberg, A. Givental, H. Hofer, *Introduction to Symplectic Field Theory*,
  GAFA 2000, Visions in Mathematics, Part II, 560–673, Section 1.2.
* H. Geiges, *An Introduction to Contact Topology*, Cambridge University Press, 2008,
  Sections 1.1 and 2.3.
-/

public section

noncomputable section

open Function Manifold Module Polynomial Set Filter
open scoped ContDiff Manifold Topology

namespace TauCeti.SmoothForm

/-! ### Symplectic contact hyperplanes and contact action -/

section ActionAndHyperplane

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 2 M]
  {α : SmoothForm I M ℝ 1}

/-- The linear symplectic form on the contact hyperplane `α.kerDistribution x` induced by `dα_x`:
`(v, w) ↦ dα_x(v, w)`. -/
def IsContactForm.kerSymplecticForm (hα : α.IsContactForm) (x : M) :
    SymplecticForm (α.kerDistribution x) :=
  let B : LinearMap.BilinForm ℝ (α.kerDistribution x) :=
    ((mextDerivₗ I 1 α).bilinFormAt x).domRestrict₁₂
      (α.kerDistribution x) (α.kerDistribution x)
  have hAlt : B.IsAlt := fun v ↦ by
    rw [LinearMap.domRestrict₁₂_apply]
    exact (isAlt_bilinFormAt _ x).self_eq_zero v.1
  have hsep : B.SeparatingLeft := fun v hv ↦ Subtype.ext <|
    (isContactForm_iff.1 hα x).2 v.1 (mem_kerDistribution.1 v.2) fun w hw ↦ by
      have h := hv ⟨w, mem_kerDistribution.2 hw⟩
      rwa [LinearMap.domRestrict₁₂_apply, ← mextDeriv_eq_bilinFormAt] at h
  { toBilinForm := B
    isAlt := hAlt
    nondegenerate := ⟨hsep, fun w hw ↦ hsep w fun v ↦ by
      rw [← hAlt.neg_eq v w, hw v, neg_zero]⟩ }

/-- Evaluating `kerSymplecticForm` on two vectors in `ker α_x` evaluates `dα_x` on them. -/
@[simp]
theorem IsContactForm.kerSymplecticForm_apply (hα : α.IsContactForm) (x : M)
    (v w : α.kerDistribution x) :
    hα.kerSymplecticForm x v w = mextDeriv α.1 x ![v.1, w.1] := by
  unfold IsContactForm.kerSymplecticForm
  dsimp only
  rw [LinearMap.domRestrict₁₂_apply, ← mextDeriv_eq_bilinFormAt]

variable [FiniteDimensional ℝ E]

/-- **Contact action along a Reeb integral curve.** Since `α(R_α) = 1`, the line integral of `α`
along any Reeb integral curve `γ` over `a..b` equals the elapsed time `b - a`. -/
theorem IsContactForm.pathIntegral_of_isMIntegralCurve (hα : α.IsContactForm) {γ : ℝ → M}
    (hγ : IsMIntegralCurve γ α.reebVectorField) (a b : ℝ) :
    pathIntegral α.1 γ a b = b - a := by
  rw [pathIntegral_def]
  have hint (t : ℝ) : α.1 (γ t) (fun _ ↦ Manifold.curveVelocity I γ t) = 1 := by
    have hvel : Manifold.curveVelocity I γ t = α.reebVectorField (γ t) := by
      simpa only [Manifold.curveVelocityWithin_univ] using
        Manifold.curveVelocityWithin_eq_of_hasMFDerivWithinAt (hγ t).hasMFDerivWithinAt
          uniqueDiffWithinAt_univ
    rw [hvel, show (fun _ : Fin 1 ↦ α.reebVectorField (γ t)) = ![α.reebVectorField (γ t)] from
      funext fun i ↦ by fin_cases i; rfl, hα.apply_reebVectorField]
  simp_rw [hint]
  exact (intervalIntegral.integral_const (1 : ℝ)).trans (by simp)

/-- The contact action `∫_0^T γ^* α` of a Reeb integral curve over `0..T` is `T`. -/
@[simp]
theorem IsContactForm.pathIntegral_zero_of_isMIntegralCurve (hα : α.IsContactForm)
    {γ : ℝ → M} (hγ : IsMIntegralCurve γ α.reebVectorField) (T : ℝ) :
    pathIntegral α.1 γ 0 T = T := by
  rw [hα.pathIntegral_of_isMIntegralCurve hγ, sub_zero]

end ActionAndHyperplane

/-! ### Symplectic transport along the local Reeb flow -/

section LocalFlow

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [T2Space M] [IsManifold I ∞ M]
  {α : SmoothForm I M ℝ 1}

omit [I.Boundaryless] [T2Space M] in
/-- The Reeb vector field of a contact form is `C¹`. -/
private theorem contMDiff_one_reebVectorField (hα : α.IsContactForm) :
    ContMDiff I I.tangent 1 (fun x ↦ (⟨x, α.reebVectorField x⟩ : TangentBundle I M)) :=
  hα.contMDiff_reebVectorField.of_le (by simp)

/-- Differential of the composition of two local flow maps along a trajectory. -/
private theorem mfderiv_flowOf_add_apply {v : (x : M) → TangentSpace I x}
    (hv : CMDiff 1 (fun y ↦ (⟨y, v y⟩ : TangentBundle I M))) {s t : ℝ} {p q : M}
    (hs : (s, p) ∈ flowDomain v) (hq : flowOf v s p = q) (ht : (t, q) ∈ flowDomain v)
    (w : TangentSpace I p) :
    @Eq E (mfderiv I I (flowOf v t) q (mfderiv I I (flowOf v s) p w))
      (mfderiv I I (flowOf v (s + t)) p w) := by
  have hΦs := contMDiffAt_flowOf_comp le_rfl hv contMDiffAt_const contMDiffAt_id hs
  have hΦt := contMDiffAt_flowOf_comp le_rfl hv contMDiffAt_const contMDiffAt_id ht
  have hev : (flowOf v t ∘ flowOf v s) =ᶠ[𝓝 p] flowOf v (s + t) := by
    have h₁ : ∀ᶠ z in 𝓝 p, (s, z) ∈ flowDomain v :=
      (isOpen_setOf_mem_flowDomain hv continuous_const continuous_id).mem_nhds hs
    have h₂ : ∀ᶠ z in 𝓝 p, (t, flowOf v s z) ∈ flowDomain v :=
      hΦs.continuousAt.preimage_mem_nhds
        ((isOpen_setOf_mem_flowDomain hv continuous_const continuous_id).mem_nhds (hq ▸ ht))
    filter_upwards [h₁, h₂] with z hsz htz
    exact (flowOf_add hv hsz htz).2
  exact (mfderiv_comp_apply_of_eq p (hΦt.mdifferentiableAt one_ne_zero)
    (hΦs.mdifferentiableAt one_ne_zero) hq w).symm.trans (DFunLike.congr_fun hev.mfderiv_eq w)

omit [FiniteDimensional ℝ E] [I.Boundaryless] [T2Space M] [IsManifold I ∞ M] in
/-- The differential of the time-`0` local flow map is the identity. -/
private theorem mfderiv_flowOf_zero_id_apply {v : (x : M) → TangentSpace I x} (p : M)
    (w : TangentSpace I p) :
    @Eq E (mfderiv I I (flowOf v 0) p w) w := by
  rw [show flowOf v 0 = id from funext (flowOf_zero v), mfderiv_id]
  rfl

/-- Wherever the local Reeb flow is defined, its differential preserves `α` pointwise. -/
@[simp]
theorem IsContactForm.apply_mfderiv_flowOf_reebVectorField (hα : α.IsContactForm) {t : ℝ}
    {x : M} (hx : (t, x) ∈ flowDomain α.reebVectorField) (v : TangentSpace I x) :
    α.1 (flowOf α.reebVectorField t x) ![mfderiv I I (flowOf α.reebVectorField t) x v] =
      α.1 x ![v] := by
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
    mextDeriv α.1 (flowOf α.reebVectorField t x)
      ![mfderiv I I (flowOf α.reebVectorField t) x v,
        mfderiv I I (flowOf α.reebVectorField t) x w] = mextDeriv α.1 x ![v, w] := by
  have hinv := mpullback_flowOf_apply_of_mextDeriv_interior_eq_zero
    (hα.contMDiff_reebVectorField.of_le (by simp)) (SmoothForm.isClosed_mextDerivₗ α)
    (by rw [mextDerivₗ_apply, hα.interior_mextDeriv_reebVectorField, mextDeriv_zero]) hx
  rw [mextDerivₗ_apply] at hinv
  exact (TauCeti.mpullback_apply_pair _ _ _ _ _).symm.trans (congrArg (· ![v, w]) hinv)

/-- The differential of the local Reeb flow at `p`, restricted to the contact hyperplane from `ξ_p`
to `ξ_q` when `flowOf α.reebVectorField t p = q`. -/
def IsContactForm.kerFlowLinearMap (hα : α.IsContactForm) {t : ℝ} {p q : M}
    (ht : (t, p) ∈ flowDomain α.reebVectorField) (hq : flowOf α.reebVectorField t p = q) :
    α.kerDistribution p →ₗ[ℝ] α.kerDistribution q :=
  (show TangentSpace I p →L[ℝ] TangentSpace I q from
    mfderiv I I (flowOf α.reebVectorField t) p).toLinearMap.restrict fun v hv ↦ by
      subst hq
      exact (hα.mfderiv_flowOf_reebVectorField_mem_kerDistribution_iff ht v).2 hv

/-- Evaluating `kerFlowLinearMap` agrees with `mfderiv` of the local Reeb flow. -/
@[simp]
theorem IsContactForm.coe_kerFlowLinearMap_apply (hα : α.IsContactForm) {t : ℝ} {p q : M}
    (ht : (t, p) ∈ flowDomain α.reebVectorField) (hq : flowOf α.reebVectorField t p = q)
    (v : α.kerDistribution p) :
    (hα.kerFlowLinearMap ht hq v : TangentSpace I q) =
      mfderiv I I (flowOf α.reebVectorField t) p v := by
  unfold IsContactForm.kerFlowLinearMap
  rfl

/-- At time `0`, `kerFlowLinearMap` is the identity of `ξ_p`. -/
@[simp]
theorem IsContactForm.kerFlowLinearMap_zero (hα : α.IsContactForm) {p : M}
    (h0 : ((0 : ℝ), p) ∈ flowDomain α.reebVectorField)
    (hp : flowOf α.reebVectorField 0 p = p) :
    hα.kerFlowLinearMap h0 hp = LinearMap.id := by
  refine LinearMap.ext fun v ↦ Subtype.ext ?_
  rw [hα.coe_kerFlowLinearMap_apply, LinearMap.id_apply]
  exact mfderiv_flowOf_zero_id_apply p v.1

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
  exact mfderiv_flowOf_add_apply (contMDiff_one_reebVectorField hα) hs hq ht v.1

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
      exact (mfderiv_flowOf_add_apply hv hneg hback ht u.1).trans
        (by rw [neg_add_cancel]; exact mfderiv_flowOf_zero_id_apply q u.1))
    (LinearMap.ext fun v ↦ Subtype.ext <| by
      rw [LinearMap.comp_apply, hα.coe_kerFlowLinearMap_apply, hα.coe_kerFlowLinearMap_apply,
        LinearMap.id_apply]
      exact (mfderiv_flowOf_add_apply hv ht hq hneg v.1).trans
        (by rw [add_neg_cancel]; exact mfderiv_flowOf_zero_id_apply p v.1))

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
    exact (mfderiv_flowOf_add_apply hv hT hp hkT' v.1).symm

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
      mfderiv_flowOf_add_apply hv hT hp hs v.1, mfderiv_flowOf_add_apply hv hs hq hTq v.1, add_comm]
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
  have hK : K ≤ K.comap Mo := fun v hv' ↦ by
    change mfderiv I I (flowOf α.reebVectorField T) p v ∈ K
    have hm := (hα.mfderiv_flowOf_reebVectorField_mem_kerDistribution_iff hT v).2 hv'
    rwa [hp] at hm
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
  rw [LinearMap.charpoly_eq_charpoly_restrict_mul_charpoly_mapQ K Mo hK, hcharQ, mul_comm]
  rfl

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
  exact DFunLike.congr_fun hid v.1

/-! ### Complete Reeb flows, closed Reeb orbits and finiteness -/

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

/-- **Contact action of a periodic Reeb trajectory equals its period.** -/
theorem IsContactForm.pathIntegral_periodicTrajectory (hα : α.IsContactForm)
    (hc : IsCompleteVectorField α.reebVectorField)
    (γ : Flow.PeriodicTrajectory (hα.reebFlow hc)) :
    pathIntegral α.1 (fun t ↦ hα.reebFlow hc t γ.point) 0 γ.period = γ.period :=
  hα.pathIntegral_zero_of_isMIntegralCurve (hα.isMIntegralCurve_reebFlow hc γ.point) γ.period

/-- The linearized Reeb return map of a parametrized periodic Reeb trajectory `γ`, acting on the
contact hyperplane `ξ_(γ.point)`. -/
def IsContactForm.periodicLinearizedReturn (hα : α.IsContactForm)
    (hc : IsCompleteVectorField α.reebVectorField)
    (γ : Flow.PeriodicTrajectory (hα.reebFlow hc)) :
    Module.End ℝ (α.kerDistribution γ.point) :=
  hα.linearizedReebReturn (hc.mem_flowDomain γ.period γ.point)
    (by rw [← hα.reebFlow_apply hc]; exact γ.apply_period)

/-- The linearized Reeb return map of the `k`-fold iterate `γ.iterate k` has the same
characteristic polynomial as the `k`-th power of that of `γ`. -/
theorem IsContactForm.charpoly_periodicLinearizedReturn_iterate (hα : α.IsContactForm)
    (hc : IsCompleteVectorField α.reebVectorField)
    (γ : Flow.PeriodicTrajectory (hα.reebFlow hc)) (k : ℕ+) :
    (hα.periodicLinearizedReturn hc (γ.iterate k)).charpoly =
      (hα.periodicLinearizedReturn hc γ ^ (k : ℕ)).charpoly := by
  have hpt : flowOf α.reebVectorField 0 (γ.iterate k).point = γ.point :=
    (flowOf_zero _ _).trans (γ.point_iterate k)
  have hper : (γ.iterate k).period = (k : ℕ) * γ.period := γ.period_iterate k
  have hpγ : flowOf α.reebVectorField γ.period γ.point = γ.point := by
    rw [← hα.reebFlow_apply hc]
    exact γ.apply_period
  have hp₂ : flowOf α.reebVectorField (γ.iterate k).period γ.point = γ.point := by
    rw [← γ.point_iterate k, ← hα.reebFlow_apply hc]
    exact (γ.iterate k).apply_period
  have hk₂ : flowOf α.reebVectorField ((k : ℕ) * γ.period) γ.point = γ.point :=
    hper ▸ hp₂
  unfold IsContactForm.periodicLinearizedReturn
  refine (hα.charpoly_linearizedReebReturn_eq_of_flowOf (hc.mem_flowDomain 0 _) hpt _ _
    (hc.mem_flowDomain _ γ.point) hp₂).trans ?_
  refine congrArg LinearMap.charpoly ?_
  refine (hα.linearizedReebReturn_congr_time _ hp₂ (hc.mem_flowDomain _ γ.point) hk₂ hper).trans ?_
  exact hα.linearizedReebReturn_natCast_mul (hc.mem_flowDomain γ.period γ.point) hpγ (k : ℕ) _ hk₂

/-- The eigenvalues of `periodicLinearizedReturn` on `γ.iterate k` are those of the `k`-th power of
`periodicLinearizedReturn` on `γ`. -/
theorem IsContactForm.hasEigenvalue_periodicLinearizedReturn_iterate_iff (hα : α.IsContactForm)
    (hc : IsCompleteVectorField α.reebVectorField)
    (γ : Flow.PeriodicTrajectory (hα.reebFlow hc)) (k : ℕ+) (μ : ℝ) :
    (hα.periodicLinearizedReturn hc (γ.iterate k)).HasEigenvalue μ ↔
      (hα.periodicLinearizedReturn hc γ ^ (k : ℕ)).HasEigenvalue μ := by
  rw [Module.End.hasEigenvalue_iff_isRoot_charpoly, Module.End.hasEigenvalue_iff_isRoot_charpoly,
    hα.charpoly_periodicLinearizedReturn_iterate hc γ k]

/-- Two periodic Reeb trajectories representing the same unparametrized `ClosedOrbit` have
linearized Reeb return maps with the same characteristic polynomial. -/
theorem IsContactForm.charpoly_periodicLinearizedReturn_eq_of_mk_eq (hα : α.IsContactForm)
    (hc : IsCompleteVectorField α.reebVectorField)
    {γ₁ γ₂ : Flow.PeriodicTrajectory (hα.reebFlow hc)}
    (h : Flow.ClosedOrbit.mk γ₁ = Flow.ClosedOrbit.mk γ₂) :
    (hα.periodicLinearizedReturn hc γ₁).charpoly =
      (hα.periodicLinearizedReturn hc γ₂).charpoly := by
  obtain ⟨s, hs⟩ := Flow.ClosedOrbit.mk_eq_mk_iff.1 h
  have hpt : flowOf α.reebVectorField s γ₂.point = γ₁.point := by
    rw [← hα.reebFlow_apply hc]
    simpa using congrArg Flow.PeriodicTrajectory.point hs
  have hper : γ₂.period = γ₁.period := by
    simpa using congrArg Flow.PeriodicTrajectory.period hs
  have h₁ : flowOf α.reebVectorField γ₂.period γ₁.point = γ₁.point := by
    rw [hper, ← hα.reebFlow_apply hc]
    exact γ₁.apply_period
  unfold IsContactForm.periodicLinearizedReturn
  refine (congrArg LinearMap.charpoly
    (hα.linearizedReebReturn_congr_time _ _ (hc.mem_flowDomain γ₂.period γ₁.point) h₁
      hper.symm)).trans ?_
  exact (hα.charpoly_linearizedReebReturn_eq_of_flowOf (hc.mem_flowDomain s γ₂.point) hpt _ _
    (hc.mem_flowDomain γ₂.period γ₁.point) h₁).symm

/-- Two periodic Reeb trajectories representing the same unparametrized `ClosedOrbit` have the same
eigenvalues for their linearized Reeb return maps. -/
theorem IsContactForm.hasEigenvalue_periodicLinearizedReturn_iff_of_mk_eq (hα : α.IsContactForm)
    (hc : IsCompleteVectorField α.reebVectorField)
    {γ₁ γ₂ : Flow.PeriodicTrajectory (hα.reebFlow hc)}
    (h : Flow.ClosedOrbit.mk γ₁ = Flow.ClosedOrbit.mk γ₂) (μ : ℝ) :
    (hα.periodicLinearizedReturn hc γ₁).HasEigenvalue μ ↔
      (hα.periodicLinearizedReturn hc γ₂).HasEigenvalue μ := by
  rw [Module.End.hasEigenvalue_iff_isRoot_charpoly, Module.End.hasEigenvalue_iff_isRoot_charpoly,
    hα.charpoly_periodicLinearizedReturn_eq_of_mk_eq hc h]

/-- An unparametrized closed Reeb orbit is **nondegenerate** when `1` is not an eigenvalue of the
linearized Reeb return map of its representatives on the contact hyperplane. -/
def IsContactForm.IsNondegenerateOrbit (hα : α.IsContactForm)
    (hc : IsCompleteVectorField α.reebVectorField)
    (γ : Flow.ClosedOrbit (hα.reebFlow hc)) : Prop :=
  ∀ δ : Flow.PeriodicTrajectory (hα.reebFlow hc), Flow.ClosedOrbit.mk δ = γ →
    ¬(hα.periodicLinearizedReturn hc δ).HasEigenvalue 1

/-- Nondegeneracy of `ClosedOrbit.mk γ` is the absence of eigenvalue `1` for
`periodicLinearizedReturn` at `γ`. -/
@[simp]
theorem IsContactForm.isNondegenerateOrbit_mk_iff (hα : α.IsContactForm)
    (hc : IsCompleteVectorField α.reebVectorField)
    (γ : Flow.PeriodicTrajectory (hα.reebFlow hc)) :
    hα.IsNondegenerateOrbit hc (Flow.ClosedOrbit.mk γ) ↔
      ¬(hα.periodicLinearizedReturn hc γ).HasEigenvalue 1 :=
  ⟨fun h ↦ h γ rfl, fun h _ hδ ↦
    mt (hα.hasEigenvalue_periodicLinearizedReturn_iff_of_mk_eq hc hδ 1).1 h⟩

/-- **Nondegeneracy of an iterate.** The `k`-fold iterate of a closed Reeb orbit is nondegenerate
iff `1` is not an eigenvalue of the `k`-th power `(A_γ)^k` of its linearized Reeb return map. -/
theorem IsContactForm.isNondegenerateOrbit_iterate_mk_iff (hα : α.IsContactForm)
    (hc : IsCompleteVectorField α.reebVectorField)
    (γ : Flow.PeriodicTrajectory (hα.reebFlow hc)) (k : ℕ+) :
    hα.IsNondegenerateOrbit hc ((Flow.ClosedOrbit.mk γ).iterate k) ↔
      ¬(hα.periodicLinearizedReturn hc γ ^ (k : ℕ)).HasEigenvalue 1 := by
  rw [Flow.ClosedOrbit.iterate_mk, hα.isNondegenerateOrbit_mk_iff,
    hα.hasEigenvalue_periodicLinearizedReturn_iterate_iff]

/-- **Double covers at eigenvalue `-1` are degenerate.** If `-1` is an eigenvalue of the linearized
Reeb return map of `γ`, then its double cover `(ClosedOrbit.mk γ).iterate 2` is degenerate, even
when `γ` itself is nondegenerate. -/
theorem IsContactForm.not_isNondegenerateOrbit_iterate_two_of_hasEigenvalue_neg_one
    (hα : α.IsContactForm) (hc : IsCompleteVectorField α.reebVectorField)
    {γ : Flow.PeriodicTrajectory (hα.reebFlow hc)}
    (hneg : (hα.periodicLinearizedReturn hc γ).HasEigenvalue (-1)) :
    ¬hα.IsNondegenerateOrbit hc ((Flow.ClosedOrbit.mk γ).iterate 2) := by
  rw [hα.isNondegenerateOrbit_iterate_mk_iff, not_not]
  obtain ⟨v, hv⟩ := hneg.exists_hasEigenvector
  refine Module.End.hasEigenvalue_of_hasEigenvector ⟨Module.End.mem_eigenspace_iff.2 ?_, hv.2⟩
  change (hα.periodicLinearizedReturn hc γ ^ 2) v = (1 : ℝ) • v
  have hv1 := hv.apply_eq_smul
  rw [neg_one_smul] at hv1
  rw [sq, mul_apply_eq_comp, hv1, map_neg, hv1, neg_neg, one_smul]

/-- **Finiteness of nondegenerate closed Reeb orbits meeting a compact window below an action
bound.** For any complete Reeb flow and compact subset `K ⊆ M`, if every closed Reeb orbit meeting
`K` of period (equivalently, contact action) at most `A` is nondegenerate, then the set of
unparametrized closed Reeb orbits meeting `K` of period at most `A` (including multiply covered
orbits) is finite. -/
theorem IsContactForm.finite_closedOrbit_inter_nonempty_and_period_le (hα : α.IsContactForm)
    (hc : IsCompleteVectorField α.reebVectorField) {K : Set M} (hK : IsCompact K) (A : ℝ)
    (hnd : ∀ γ : Flow.ClosedOrbit (hα.reebFlow hc),
      (γ.support ∩ K).Nonempty → γ.period ≤ A → hα.IsNondegenerateOrbit hc γ) :
    {γ : Flow.ClosedOrbit (hα.reebFlow hc) |
      (γ.support ∩ K).Nonempty ∧ γ.period ≤ A}.Finite := by
  have hv := contMDiff_one_reebVectorField hα
  obtain ⟨ε, hε, hlow⟩ :=
    (hα.reebFlow hc).exists_pos_period_le_of_isCompact hK fun x _ ↦ hα.exists_reebFlow_ne hc x
  set S : Set (ℝ × M) := Icc ε A ×ˢ K
  have hS : IsCompact S := isCompact_Icc.prod hK
  have hSD : S ⊆ flowDomain α.reebVectorField := fun x _ ↦ hc.mem_flowDomain x.1 x.2
  have hSnd : ∀ x ∈ S, flowOf α.reebVectorField x.1 x.2 = x.2 →
      ∃ g : M → ℝ, ContMDiffAt I 𝓘(ℝ) 1 g x.2 ∧
        mvfderiv I g x.2 (α.reebVectorField x.2) ≠ 0 ∧
        ¬(returnDerivative α.reebVectorField g x.1 x.2).HasEigenvalue 1 := by
    rintro ⟨t, z⟩ ⟨⟨htε, htA⟩, hzK⟩ htz
    let δ : Flow.PeriodicTrajectory (hα.reebFlow hc) :=
      ⟨z, t, hε.trans_le htε, by rw [hα.reebFlow_apply, htz], hα.exists_reebFlow_ne hc z⟩
    have hmeet : ((Flow.ClosedOrbit.mk δ).support ∩ K).Nonempty :=
      ⟨z, Flow.ClosedOrbit.point_mem_support δ, hzK⟩
    have hδ : ¬(hα.periodicLinearizedReturn hc δ).HasEigenvalue 1 :=
      (hα.isNondegenerateOrbit_mk_iff hc δ).1
        (hnd (Flow.ClosedOrbit.mk δ) hmeet (by rw [Flow.ClosedOrbit.period_mk]; exact htA))
    obtain ⟨g, hg, hgv⟩ :=
      exists_contMDiffAt_mvfderiv_ne_zero (I := I) (hα.reebVectorField_ne_zero z) 1
    exact ⟨g, hg, hgv,
      mt (hα.hasEigenvalue_returnDerivative_iff (hc.mem_flowDomain t z) htz hg hgv one_ne_zero).1
        hδ⟩
  obtain ⟨F, -, hF⟩ := exists_finset_forall_fst_eq_and_exists_flowOf_eq_snd hv hS hSD hSnd
  refine Flow.ClosedOrbit.finite_of_exists_finset (F := F) ?_
  rintro γ ⟨⟨p, hpγ, hpK⟩, hγA⟩
  induction γ using Flow.ClosedOrbit.ind with | h γ => ?_
  rw [Flow.ClosedOrbit.period_mk] at hγA ⊢
  rw [Flow.ClosedOrbit.support_mk] at hpγ
  obtain ⟨r, rfl⟩ := (Flow.mem_orbit_iff _).1 hpγ
  let γ' : Flow.PeriodicTrajectory (hα.reebFlow hc) := r +ᵥ γ
  have hεγ : ε ≤ γ.period := hlow γ'.point hpK γ'.period γ'.period_pos γ'.apply_period
  have hper : flowOf α.reebVectorField γ.period γ'.point = γ'.point := by
    rw [← hα.reebFlow_apply hc]
    exact γ'.apply_period
  obtain ⟨y, hyF, hy1, s, -, hsy⟩ :=
    hF (γ.period, γ'.point) ⟨⟨hεγ, hγA⟩, hpK⟩ hper
  refine ⟨y, hyF, hy1, ?_⟩
  rw [← Flow.ClosedOrbit.mk_vadd r γ, Flow.ClosedOrbit.support_mk, Flow.mem_orbit_iff]
  refine ⟨-s, ?_⟩
  have hsy' : hα.reebFlow hc s y.2 = γ'.point := by rwa [hα.reebFlow_apply]
  rw [← hsy', ← Flow.map_add, neg_add_cancel, Flow.map_zero_apply]

/-- **Finiteness of nondegenerate closed Reeb orbits below an action bound.** On a compact
boundaryless contact manifold, if every closed Reeb orbit of period (equivalently, contact action)
at most `A` is nondegenerate, then the set of unparametrized closed Reeb orbits of period at most
`A` (including multiply covered orbits) is finite. -/
theorem IsContactForm.finite_closedOrbit_period_le [CompactSpace M] (hα : α.IsContactForm)
    (hc : IsCompleteVectorField α.reebVectorField) (A : ℝ)
    (hnd : ∀ γ : Flow.ClosedOrbit (hα.reebFlow hc), γ.period ≤ A →
      hα.IsNondegenerateOrbit hc γ) :
    {γ : Flow.ClosedOrbit (hα.reebFlow hc) | γ.period ≤ A}.Finite := by
  refine (hα.finite_closedOrbit_inter_nonempty_and_period_le hc isCompact_univ A
    fun γ _ ↦ hnd γ).subset fun γ hγ ↦ ⟨?_, hγ⟩
  induction γ using Flow.ClosedOrbit.ind with | h γ => ?_
  exact ⟨γ.point, Flow.ClosedOrbit.point_mem_support γ, mem_univ _⟩

/-- When all closed Reeb orbits of `α` are nondegenerate on a compact boundaryless contact
manifold, there are only finitely many closed Reeb orbits of period at most `A` for every `A`. -/
theorem IsContactForm.finite_closedOrbit_period_le_of_forall [CompactSpace M]
    (hα : α.IsContactForm) (hc : IsCompleteVectorField α.reebVectorField)
    (hnd : ∀ γ : Flow.ClosedOrbit (hα.reebFlow hc), hα.IsNondegenerateOrbit hc γ) (A : ℝ) :
    {γ : Flow.ClosedOrbit (hα.reebFlow hc) | γ.period ≤ A}.Finite :=
  hα.finite_closedOrbit_period_le hc A fun γ _ ↦ hnd γ

end LocalFlow

end TauCeti.SmoothForm

/-! ### Non-vacuity model: the contact circle `AddCircle p` -/

namespace AddCircle

open TauCeti TauCeti.SmoothForm

variable (p : ℝ) [Fact (0 < p)]

/-- On the circle `AddCircle p`, the contact hyperplane `ker (timeForm p)` is trivial (`⊥`). -/
@[simp]
theorem kerDistribution_timeForm (x : AddCircle p) :
    (timeForm p).kerDistribution x = ⊥ :=
  Submodule.ext fun v ↦ by
    rw [mem_kerDistribution, Submodule.mem_bot, timeForm_apply, Matrix.cons_val_zero]
    rfl

/-- The time form `dt_p` on `AddCircle p` (`p > 0`) is a contact form in dimension `1`: it vanishes
nowhere, and `d(dt_p) = 0` is vacuously nondegenerate on `ker (dt_p) = ⊥`. -/
theorem isContactForm_timeForm : (timeForm p).IsContactForm :=
  isContactForm_iff.2 fun x ↦ ⟨⟨(1 : ℝ), by simp⟩, fun v hv _ ↦ by
    have hv0 : v ∈ (timeForm p).kerDistribution x := mem_kerDistribution.2 hv
    rwa [kerDistribution_timeForm, Submodule.mem_bot] at hv0⟩

/-- The Reeb vector field of `AddCircle.timeForm p` is the unit vector field `∂_t`. -/
@[simp]
theorem reebVectorField_timeForm : (timeForm p).reebVectorField = timeVectorField p := by
  funext x
  symm
  rw [(isContactForm_timeForm p).eq_reebVectorField_iff_kerDistribution]
  refine ⟨by simp, fun w hw ↦ ?_⟩
  have hw0 : w = 0 := by
    have hm : w ∈ (timeForm p).kerDistribution x := mem_kerDistribution.2 hw
    rwa [kerDistribution_timeForm, Submodule.mem_bot] at hm
  rw [hw0]
  exact ((mextDeriv (timeForm p).1) x).map_coord_zero 1 rfl

/-- The global Reeb flow of `AddCircle.timeForm p` is the translation flow of `AddCircle p`. -/
@[simp]
theorem reebFlow_timeForm (hc : IsCompleteVectorField (timeForm p).reebVectorField) :
    (isContactForm_timeForm p).reebFlow hc = translationFlow p :=
  Flow.ext fun t x ↦ by
    rw [IsContactForm.reebFlow_apply]
    have hγ : IsMIntegralCurve (fun s ↦ translationFlow p s x) (timeForm p).reebVectorField := by
      rw [reebVectorField_timeForm]
      exact isMIntegralCurve_translationFlow p x
    simpa using flowOf_eq_of_isMIntegralCurve
      ((isContactForm_timeForm p).contMDiff_reebVectorField.of_le (by simp)) hγ t

/-- Every closed Reeb orbit of `AddCircle.timeForm p` (primitive and multiply covered alike) is
nondegenerate, since the contact hyperplane `⊥` has no nonzero vectors. -/
theorem isNondegenerateOrbit_timeForm (hc : IsCompleteVectorField (timeForm p).reebVectorField)
    (γ : Flow.ClosedOrbit ((isContactForm_timeForm p).reebFlow hc)) :
    (isContactForm_timeForm p).IsNondegenerateOrbit hc γ := by
  rintro δ rfl h1
  obtain ⟨v, hv⟩ := h1.exists_hasEigenvector
  have hv0 : v.1 ∈ (⊥ : Submodule ℝ (TangentSpace 𝓘(ℝ) δ.point)) :=
    kerDistribution_timeForm p δ.point ▸ v.2
  exact hv.2 (Subtype.ext ((Submodule.mem_bot ℝ).1 hv0))

/-- The canonical primitive periodic trajectory of `AddCircle.translationFlow p` starting at `0`
with period `p`. Together with its iterates `((primitiveTrajectory p).iterate k)`, it witnesses
that closed Reeb orbits of arbitrary multiplicity `k : ℕ+` exist and satisfy
`IsContactForm.finite_closedOrbit_period_le` on `AddCircle p`. -/
def primitiveTrajectory : Flow.PeriodicTrajectory (translationFlow p) where
  point := 0
  period := p
  period_pos := Fact.out
  apply_period := by simp
  exists_apply_ne := ⟨p / 2, by simpa using period_div_two_coe_ne_zero (p := p)⟩

@[simp]
theorem primitiveTrajectory_point : (primitiveTrajectory p).point = 0 := by
  unfold primitiveTrajectory
  rfl

@[simp]
theorem primitiveTrajectory_period : (primitiveTrajectory p).period = p := by
  unfold primitiveTrajectory
  rfl

/-- The canonical trajectory of period `p` on `AddCircle p` has covering multiplicity `1`. -/
@[simp]
theorem multiplicity_mk_primitiveTrajectory :
    (Flow.ClosedOrbit.mk (primitiveTrajectory p)).multiplicity = 1 := by
  have hp0 : (0 : ℝ) < p := Fact.out
  have hmin : (translationFlow p).minimalPeriod (0 : AddCircle p) = p := by
    refine le_antisymm ((translationFlow p).minimalPeriod_le (by simp) hp0) ?_
    obtain ⟨k, hk⟩ := AddSubgroup.mem_zmultiples_iff.1
      ((translationFlow_apply_eq_self_iff p).1 ((translationFlow p).apply_minimalPeriod 0))
    have hmpos : 0 < (translationFlow p).minimalPeriod (0 : AddCircle p) := by
      simpa using (primitiveTrajectory p).minimalPeriod_pos
    have hk1 : 1 ≤ k := by
      by_contra! hk0
      have hk0' : k ≤ 0 := by omega
      have hnonpos := mul_nonpos_of_nonpos_of_nonneg (Int.cast_nonpos.2 hk0') hp0.le
      rw [zsmul_eq_mul] at hk
      linarith
    have hk1' : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk1
    rw [zsmul_eq_mul] at hk
    nlinarith
  have hm := (Flow.ClosedOrbit.mk (primitiveTrajectory p)).multiplicity_mul_minimalPeriod
  rw [Flow.ClosedOrbit.minimalPeriod_mk, Flow.ClosedOrbit.period_mk, primitiveTrajectory_point,
    primitiveTrajectory_period, hmin] at hm
  have hcast : (((Flow.ClosedOrbit.mk (primitiveTrajectory p)).multiplicity : ℕ) : ℝ) = 1 := by
    nlinarith
  exact PNat.coe_injective (by exact_mod_cast hcast)

end AddCircle
