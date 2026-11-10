/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Instances.OnePoint.LineBundle
public import TauCeti.Geometry.Manifold.Instances.OnePoint.Tangent

/-!
# The tangent bundle of the Riemann sphere is `𝒪(2)`

The holomorphic tangent bundle of the Riemann sphere `OnePoint ℂ` is isomorphic to the line bundle
`𝒪(2) = OnePoint.twistCore 2` over the identity. In the affine chart both bundles read a fibre
element as itself, so the isomorphism is `v ↦ v` at the finite points. In the inverted chart a
tangent vector `v` at a finite point `z ≠ 0` reads as `-z⁻² v`
(`OnePoint.trivializationAt_infty_apply_coe`), while a fibre element of `𝒪(2)` reads as `z⁻² v`
(`OnePoint.twistTransition_coe_infty`), so the isomorphism is `v ↦ -v` at `∞`. In both charts the
isomorphism is multiplication by a constant, so it is analytic in both directions.

## Main declarations

* `OnePoint.tangentSpaceEquivTwistFiber x`: the `ℂ`-linear isomorphism from the tangent space of
  the Riemann sphere at `x` to the fibre of `𝒪(2)` at `x`: the identity at the finite points and
  `-1` at `∞`.
* `OnePoint.tangentBundleDiffeomorphTwist`: the tangent bundle of the Riemann sphere and the total
  space of `𝒪(2)` are analytically diffeomorphic through these fibrewise isomorphisms, over the
  identity of `OnePoint ℂ` (`OnePoint.proj_tangentBundleDiffeomorphTwist`).

## References

* Otto Forster, *Lectures on Riemann Surfaces*, Graduate Texts in Mathematics 81,
  Springer, 1981, §29.
* Daniel Huybrechts, *Complex Geometry: An Introduction*, Springer, 2005, Section 2.2.
-/

public noncomputable section

open Bundle
open scoped Manifold ContDiff

namespace OnePoint

/-- **The fibres of `TS² ≅ 𝒪(2)`.** The `ℂ`-linear isomorphism from the tangent space of the
Riemann sphere at `x` to the fibre of `𝒪(2)` at `x`: multiplication by `(-1) ^ twistIndex x`, so
the identity at the finite points (`OnePoint.tangentSpaceEquivTwistFiber_coe`) and `v ↦ -v` at `∞`
(`OnePoint.tangentSpaceEquivTwistFiber_infty`). -/
def tangentSpaceEquivTwistFiber (x : OnePoint ℂ) :
    TangentSpace 𝓘(ℂ) x ≃L[ℂ] (twistCore (𝕜 := ℂ) 2).Fiber x :=
  ContinuousLinearEquiv.unitsEquivAut ℂ ((-1 : ℂˣ) ^ twistIndex x)

theorem tangentSpaceEquivTwistFiber_apply (x : OnePoint ℂ) (v : ℂ) :
    tangentSpaceEquivTwistFiber x v = ((-1 : ℂ) ^ twistIndex x * v : ℂ) := by
  rw [mul_comm]
  exact (ContinuousLinearEquiv.unitsEquivAut_apply _ v).trans (by simp)

theorem tangentSpaceEquivTwistFiber_symm_apply (x : OnePoint ℂ) (v : ℂ) :
    (tangentSpaceEquivTwistFiber x).symm v = ((-1 : ℂ) ^ twistIndex x * v : ℂ) := by
  rw [mul_comm]
  refine (ContinuousLinearEquiv.unitsEquivAut_apply_symm _ v).trans ?_
  induction x using OnePoint.rec <;> simp

/-- At a finite point the isomorphism `TS² ≅ 𝒪(2)` is the identity. -/
@[simp]
theorem tangentSpaceEquivTwistFiber_coe (z : ℂ) (v : ℂ) :
    tangentSpaceEquivTwistFiber (z : OnePoint ℂ) v = v :=
  (tangentSpaceEquivTwistFiber_apply _ v).trans (by simp; rfl)

/-- At `∞` the isomorphism `TS² ≅ 𝒪(2)` is `v ↦ -v`. -/
@[simp]
theorem tangentSpaceEquivTwistFiber_infty (v : ℂ) :
    tangentSpaceEquivTwistFiber (∞ : OnePoint ℂ) v = (-v : ℂ) :=
  (tangentSpaceEquivTwistFiber_apply _ v).trans (by simp; rfl)

@[simp]
theorem tangentSpaceEquivTwistFiber_symm_coe (z : ℂ) (v : ℂ) :
    (tangentSpaceEquivTwistFiber (z : OnePoint ℂ)).symm v = v :=
  (tangentSpaceEquivTwistFiber_symm_apply _ v).trans (by simp; rfl)

@[simp]
theorem tangentSpaceEquivTwistFiber_symm_infty (v : ℂ) :
    (tangentSpaceEquivTwistFiber (∞ : OnePoint ℂ)).symm v = (-v : ℂ) :=
  (tangentSpaceEquivTwistFiber_symm_apply _ v).trans (by simp; rfl)

/-- In the preferred trivialization at `x`, a fibre element `v` of `𝒪(2)` at `p` has the
coordinate `twistTransition 2 p x p * v`. -/
private theorem trivializationAt_twistCore_two_apply (x p : OnePoint ℂ) (v : ℂ) :
    (trivializationAt ℂ (twistCore (𝕜 := ℂ) 2).Fiber x ⟨p, v⟩).2 =
      twistTransition 2 p x p * v := by
  rw [VectorBundleCore.trivializationAt, ← VectorBundleCore.localTrivAt_def, twistCore_indexAt]
  exact twistCore_localTriv_apply 2 x (fun _ ↦ v) p

/-- In the preferred trivializations at `x` of the tangent bundle and of `𝒪(2)`, the isomorphism
`TS² ≅ 𝒪(2)` is multiplication by the constant `(-1) ^ twistIndex x`. -/
private theorem trivializationAt_twistCore_tangentSpaceEquivTwistFiber (x p : OnePoint ℂ)
    (v : ℂ) (hq : p ∈ (chartAt ℂ x).source) :
    (trivializationAt ℂ (twistCore (𝕜 := ℂ) 2).Fiber x ⟨p, tangentSpaceEquivTwistFiber p v⟩).2 =
      (-1 : ℂ) ^ twistIndex x * (trivializationAt ℂ (TangentSpace 𝓘(ℂ)) x ⟨p, v⟩).2 := by
  refine (trivializationAt_twistCore_two_apply x p _).trans ?_
  rw [tangentSpaceEquivTwistFiber_apply]
  induction x using OnePoint.rec with
  | infty =>
    induction p using OnePoint.rec with
    | infty => simp [trivializationAt_infty_apply_infty]
    | coe z =>
      have hz : z ≠ 0 := by simpa using hq
      simp [trivializationAt_infty_apply_coe hz, zpow_neg]
  | coe w =>
    induction p using OnePoint.rec with
    | infty => simp at hq
    | coe z => simp [trivializationAt_coe_apply_coe]

/-- In the preferred trivializations at `x` of `𝒪(2)` and of the tangent bundle, the inverse
isomorphism `𝒪(2) ≅ TS²` is multiplication by the constant `(-1) ^ twistIndex x`. -/
private theorem trivializationAt_tangentSpaceEquivTwistFiber_symm (x p : OnePoint ℂ) (v : ℂ)
    (hq : p ∈ (chartAt ℂ x).source) :
    (trivializationAt ℂ (TangentSpace 𝓘(ℂ)) x
        (⟨p, (tangentSpaceEquivTwistFiber p).symm v⟩ : TangentBundle 𝓘(ℂ) (OnePoint ℂ))).2 =
      (-1 : ℂ) ^ twistIndex x * (trivializationAt ℂ (twistCore (𝕜 := ℂ) 2).Fiber x ⟨p, v⟩).2 := by
  rw [trivializationAt_twistCore_two_apply, tangentSpaceEquivTwistFiber_symm_apply]
  induction x using OnePoint.rec with
  | infty =>
    induction p using OnePoint.rec with
    | infty => simp [trivializationAt_infty_apply_infty]
    | coe z =>
      have hz : z ≠ 0 := by simpa using hq
      simp [trivializationAt_infty_apply_coe hz, zpow_neg]
  | coe w =>
    induction p using OnePoint.rec with
    | infty => simp at hq
    | coe z => simp [trivializationAt_coe_apply_coe]

/-- **The tangent bundle of the Riemann sphere is `𝒪(2)`.** The fibrewise isomorphisms
`OnePoint.tangentSpaceEquivTwistFiber`, `v ↦ v` at the finite points and `v ↦ -v` at `∞`, form an
analytic diffeomorphism from the tangent bundle of `OnePoint ℂ` to the total space of `𝒪(2)`
over the identity (`OnePoint.proj_tangentBundleDiffeomorphTwist`). -/
def tangentBundleDiffeomorphTwist (n : ℕ∞ω) :
    Diffeomorph 𝓘(ℂ).tangent (𝓘(ℂ).prod 𝓘(ℂ)) (TangentBundle 𝓘(ℂ) (OnePoint ℂ))
      (TotalSpace ℂ (twistCore (𝕜 := ℂ) 2).Fiber) n where
  toFun q := ⟨q.proj, tangentSpaceEquivTwistFiber q.proj q.2⟩
  invFun q := ⟨q.proj, (tangentSpaceEquivTwistFiber q.proj).symm q.2⟩
  left_inv q := by simp
  right_inv q := by simp
  contMDiff_toFun := by
    refine ContMDiff.of_le (n := ω) (fun q ↦ ?_) le_top
    have hid := (Bundle.contMDiffAt_totalSpace (n := ω) (IM := 𝓘(ℂ).tangent)
      (f := fun q : TangentBundle 𝓘(ℂ) (OnePoint ℂ) ↦ q) (x₀ := q)).1 contMDiffAt_id
    refine Bundle.contMDiffAt_totalSpace.2 ⟨hid.1, ?_⟩
    refine (((contDiff_const (c := (-1 : ℂ) ^ twistIndex q.proj)).mul
      contDiff_id).contMDiff.contMDiffAt.comp q hid.2).congr_of_eventuallyEq ?_
    filter_upwards [hid.1.continuousAt.preimage_mem_nhds
      ((chartAt ℂ q.proj).open_source.mem_nhds (mem_chart_source ℂ q.proj))] with r hr
    exact trivializationAt_twistCore_tangentSpaceEquivTwistFiber _ r.proj r.2 hr
  contMDiff_invFun := by
    refine ContMDiff.of_le (n := ω) (fun q ↦ ?_) le_top
    have hid := (Bundle.contMDiffAt_totalSpace (n := ω) (IM := 𝓘(ℂ).prod 𝓘(ℂ))
      (f := fun q : TotalSpace ℂ (twistCore (𝕜 := ℂ) 2).Fiber ↦ q) (x₀ := q)).1 contMDiffAt_id
    refine Bundle.contMDiffAt_totalSpace.2 ⟨hid.1, ?_⟩
    refine (((contDiff_const (c := (-1 : ℂ) ^ twistIndex q.proj)).mul
      contDiff_id).contMDiff.contMDiffAt.comp q hid.2).congr_of_eventuallyEq ?_
    filter_upwards [hid.1.continuousAt.preimage_mem_nhds
      ((chartAt ℂ q.proj).open_source.mem_nhds (mem_chart_source ℂ q.proj))] with r hr
    exact trivializationAt_tangentSpaceEquivTwistFiber_symm _ r.proj r.2 hr

@[simp]
theorem tangentBundleDiffeomorphTwist_apply (n : ℕ∞ω)
    (q : TangentBundle 𝓘(ℂ) (OnePoint ℂ)) :
    tangentBundleDiffeomorphTwist n q = ⟨q.proj, tangentSpaceEquivTwistFiber q.proj q.2⟩ :=
  (rfl)

@[simp]
theorem tangentBundleDiffeomorphTwist_symm_apply (n : ℕ∞ω)
    (q : TotalSpace ℂ (twistCore (𝕜 := ℂ) 2).Fiber) :
    (tangentBundleDiffeomorphTwist n).symm q =
      ⟨q.proj, (tangentSpaceEquivTwistFiber q.proj).symm q.2⟩ :=
  (rfl)

/-- The isomorphism `TS² ≅ 𝒪(2)` lies over the identity of the Riemann sphere. -/
theorem proj_tangentBundleDiffeomorphTwist (n : ℕ∞ω)
    (q : TangentBundle 𝓘(ℂ) (OnePoint ℂ)) :
    (tangentBundleDiffeomorphTwist n q).proj = q.proj :=
  (rfl)

theorem proj_tangentBundleDiffeomorphTwist_symm (n : ℕ∞ω)
    (q : TotalSpace ℂ (twistCore (𝕜 := ℂ) 2).Fiber) :
    ((tangentBundleDiffeomorphTwist n).symm q).proj = q.proj :=
  (rfl)

end OnePoint
