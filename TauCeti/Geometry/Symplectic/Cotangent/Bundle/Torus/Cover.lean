/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Instances.AddCircle.Torus
public import TauCeti.Geometry.Manifold.LocalDiffeomorph.Basic
public import TauCeti.Geometry.Symplectic.Cotangent.Bundle.Liouville

import TauCeti.Geometry.Manifold.DifferentialForm.Naturality

/-!
# The covering of the cotangent bundle of a torus by the linear cotangent space

For a finite family of positive periods `p i`, let `Tⁿ = ∀ i, AddCircle (p i)` be the torus, whose
tangent spaces are `ι → ℝ`. A covector at a point of `Tⁿ` is therefore an element of the dual
`(ι → ℝ) →L[ℝ] ℝ`, and every point of `Tⁿ` is the image `[q]` of some `q : ι → ℝ`. The map

`TauCeti.CotangentBundle.torusMk p : (ι → ℝ) × ((ι → ℝ) →L[ℝ] ℝ) → T*Tⁿ`, `(q, ξ) ↦ ξ` at `[q]`,

is the covering of `T*Tⁿ` by the linear cotangent space of `ι → ℝ`: it is the cotangent lift of
the covering `(ι → ℝ) → Tⁿ`, whose derivative is the identity. This file shows that it is a smooth
local diffeomorphism (`TauCeti.CotangentBundle.isLocalDiffeomorph_torusMk`) identifying two points
exactly when their covectors agree and their base points differ by a vector of the period lattice
`∏ i, p i ℤ` (`TauCeti.CotangentBundle.torusMk_eq_torusMk_iff`), and that it pulls the Liouville
form `λ` and the canonical symplectic form `ω = -dλ` of `T*Tⁿ` back to their linear models,
`TauCeti.cotangentLiouvilleForm` and `TauCeti.strongDualCotangentSymplecticForm`
(`TauCeti.CotangentBundle.mpullback_torusMk_liouvilleForm`,
`TauCeti.CotangentBundle.eval₂_mfderiv_torusMk`).

In the coordinates `θ = q` and `I_i = ξ(e_i)`, the actions of the covector, the covering is the
parametrization of `T*Tⁿ` by angles and actions, and the second statement says that the canonical
form is `ω = ∑ i, dθ_i ∧ dI_i` in these coordinates. Maps into `T*Tⁿ` can thus be built and
recognized as symplectic by lifting them to the linear cotangent space.

The smoothness of the covering rests on the fact that the charts of the torus are local lifts of
the covering `(ι → ℝ) → Tⁿ`, so that the trivialization of the tangent bundle of `Tⁿ` in a chart is
the identity of `ι → ℝ` (`AddCircle.symmL_trivializationAt_pi`).

## Main definitions

* `TauCeti.CotangentBundle.torusMk p`: the covering `(q, ξ) ↦ ξ` at `[q]` of `T*Tⁿ`.

## Main results

* `TauCeti.CotangentBundle.torusMk_eq_torusMk_iff`, `TauCeti.CotangentBundle.surjective_torusMk`:
  the covering is surjective, with fibres the translates by the period lattice.
* `TauCeti.CotangentBundle.contMDiff_torusMk`: the covering is smooth.
* `TauCeti.CotangentBundle.mpullback_torusMk_liouvilleForm`: it pulls `λ` back to
  `λ_(q, ξ)(δq, δξ) = ξ(δq)`.
* `TauCeti.CotangentBundle.eval₂_mfderiv_torusMk`: it pulls `ω` back to
  `((δq, δξ), (δq', δξ')) ↦ δξ'(δq) - δξ(δq')`.
* `TauCeti.CotangentBundle.isLocalDiffeomorph_torusMk`: it is a local diffeomorphism.

## References

* V. I. Arnold, *Mathematical Methods of Classical Mechanics*, 2nd ed., Graduate Texts in
  Mathematics 60, Springer, 1989, Section 50 (action–angle variables on `T*Tⁿ`).
* A. Cannas da Silva, *Lectures on Symplectic Geometry*, Lecture Notes in Mathematics 1764,
  Springer, 2001, Section 2.
-/

public section

noncomputable section

open Bundle Set Function Filter
open scoped Manifold ContDiff Topology

namespace TauCeti

namespace CotangentBundle

variable {ι : Type*} [Fintype ι] (p : ι → ℝ) [∀ i, Fact (0 < p i)]

/-- The **covering of the cotangent bundle of a torus** by the linear cotangent space of `ι → ℝ`:
it sends `(q, ξ)` to the covector `ξ` at the point `[q]` of `Tⁿ = ∀ i, AddCircle (p i)`, whose
tangent space is `ι → ℝ`. In the angle coordinates `θ = q` and the actions `I_i = ξ(e_i)`, it is
the action–angle parametrization of `T*Tⁿ`. -/
def torusMk (q : (ι → ℝ) × ((ι → ℝ) →L[ℝ] ℝ)) :
    CotangentBundle (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) (∀ i, AddCircle (p i)) :=
  TotalSpace.mk' ((ι → ℝ) →L[ℝ] ℝ) (fun i ↦ (q.1 i : AddCircle (p i))) q.2

/-- The covering lies over the covering map `q ↦ ([q i])ᵢ` of the torus. -/
@[simp]
theorem proj_torusMk (q : (ι → ℝ) × ((ι → ℝ) →L[ℝ] ℝ)) :
    (torusMk p q).proj = fun i ↦ (q.1 i : AddCircle (p i)) :=
  (rfl)

/-- The covector of `torusMk p (q, ξ)` is `ξ`. -/
@[simp]
theorem torusMk_snd (q : (ι → ℝ) × ((ι → ℝ) →L[ℝ] ℝ)) (v : ι → ℝ) :
    (torusMk p q).2 v = q.2 v :=
  (rfl)

/-- **The covering of `T*Tⁿ` is surjective**: every covector at a point `x` of the torus is the
image of a lift of `x` to `ι → ℝ` together with the same covector. -/
theorem surjective_torusMk : Surjective (torusMk p) := by
  rintro ⟨x, ξ⟩
  choose q hq using fun i ↦ QuotientAddGroup.mk_surjective (x i)
  obtain rfl : (fun i ↦ (q i : AddCircle (p i))) = x := funext hq
  exact ⟨(q, ξ), rfl⟩

/-- **The fibres of the covering of `T*Tⁿ`.** Two points have the same image exactly when their
covectors agree and their base points differ by a vector of the period lattice `∏ i, p i ℤ`. -/
theorem torusMk_eq_torusMk_iff {q q' : (ι → ℝ) × ((ι → ℝ) →L[ℝ] ℝ)} :
    torusMk p q = torusMk p q' ↔ q'.2 = q.2 ∧ ∃ m : ι → ℤ, q'.1 = q.1 + fun i ↦ m i * p i := by
  have hcoe (i : ι) : (q'.1 i : AddCircle (p i)) = q.1 i ↔ ∃ m : ℤ, q'.1 i = q.1 i + m * p i := by
    rw [← sub_eq_zero, ← AddCircle.coe_sub, AddCircle.coe_eq_zero_iff]
    simp only [zsmul_eq_mul, eq_sub_iff_add_eq, eq_comm (a := q'.1 i), add_comm]
  constructor
  · intro h
    refine ⟨ContinuousLinearMap.ext fun v ↦ (congrArg (fun z ↦ z.2 v) h).symm, ?_⟩
    have hp := congrArg TotalSpace.proj h
    choose m hm using fun i ↦ (hcoe i).1 (congrFun hp i).symm
    exact ⟨m, funext hm⟩
  · rintro ⟨h2, m, hm⟩
    refine ext (funext fun i ↦ ((hcoe i).2 ⟨m i, congrFun hm i⟩).symm) fun v ↦ ?_
    exact DFunLike.congr_fun h2.symm v

/-- **The covering of `T*Tⁿ` is smooth.** In the preferred charts of `T*Tⁿ`, the covector of
`torusMk p (q, ξ)` is `ξ` itself, since the tangent bundle of the torus is trivial in its charts. -/
theorem contMDiff_torusMk :
    ContMDiff 𝓘(ℝ, (ι → ℝ) × ((ι → ℝ) →L[ℝ] ℝ))
      ((ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)).prod 𝓘(ℝ, (ι → ℝ) →L[ℝ] ℝ)) ∞ (torusMk p) := by
  intro q₀
  rw [contMDiffAt_hom_bundle]
  refine ⟨contMDiffAt_pi_iff.2 fun i ↦ ((AddCircle.contMDiff_coe (p i) ∞).comp
    (contMDiff_iff_contDiff.2 (by fun_prop :
      ContDiff ℝ ∞ fun q : (ι → ℝ) × ((ι → ℝ) →L[ℝ] ℝ) ↦ q.1 i))).contMDiffAt, ?_⟩
  -- In the trivialization at `[q₀]`, the covector coordinate of `torusMk p (q, ξ)` is `ξ`.
  refine (contMDiff_iff_contDiff.2 (contDiff_snd (𝕜 := ℝ) (E := ι → ℝ)
    (F := (ι → ℝ) →L[ℝ] ℝ))).contMDiffAt.congr_of_eventuallyEq ?_
  have hc : Continuous fun q : (ι → ℝ) × ((ι → ℝ) →L[ℝ] ℝ) ↦ (torusMk p q).proj :=
    continuous_pi fun i ↦ (AddCircle.continuous_mk' (p i)).comp ((continuous_apply i).comp
      continuous_fst)
  filter_upwards [hc.continuousAt.preimage_mem_nhds ((chartAt (ModelPi fun _ : ι ↦ ℝ)
    (torusMk p q₀).proj).open_source.mem_nhds (mem_chart_source _ _))] with q hq
  rw [ContinuousLinearMap.inCoordinates, AddCircle.symmL_trivializationAt_pi hq]
  simp only [Trivial.fiberBundle_trivializationAt', Trivial.continuousLinearMapAt_trivialization]
  exact ContinuousLinearMap.id_comp _

/-- **The covering of `T*Tⁿ` pulls the Liouville form back to its linear model.** At `(q, ξ)` it
evaluates a tangent vector `(δq, δξ)` by `ξ(δq)`, since the covering lies over the covering map
of the torus, whose derivative is the identity. -/
theorem mpullback_torusMk_liouvilleForm :
    mpullback 𝓘(ℝ, (ι → ℝ) × ((ι → ℝ) →L[ℝ] ℝ))
        ((ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)).prod 𝓘(ℝ, (ι → ℝ) →L[ℝ] ℝ)) (torusMk p)
        (liouvilleForm (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) (∀ i, AddCircle (p i))).1 =
      cotangentLiouvilleForm := by
  funext q
  refine ContinuousAlternatingMap.ext fun v ↦ ?_
  have hg : HasMFDerivAt 𝓘(ℝ, (ι → ℝ) × ((ι → ℝ) →L[ℝ] ℝ))
      (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ))
      (fun q : (ι → ℝ) × ((ι → ℝ) →L[ℝ] ℝ) ↦ fun i ↦ (q.1 i : AddCircle (p i))) q
      (ContinuousLinearMap.fst ℝ (ι → ℝ) ((ι → ℝ) →L[ℝ] ℝ)) :=
    ((AddCircle.hasMFDerivAt_coe_pi p q.1).comp q
      (ContinuousLinearMap.fst ℝ (ι → ℝ) ((ι → ℝ) →L[ℝ] ℝ)).hasMFDerivAt).congr_mfderiv
        (by ext; rfl)
  rw [mpullback_liouvilleForm_apply_of_proj_comp_eq (proj_torusMk p)
    (((contMDiff_torusMk p) q).mdifferentiableAt (by simp)), hg.mfderiv]
  exact (cotangentLiouvilleForm_apply q v).symm

/-- **The covering of `T*Tⁿ` is symplectic.** It pulls the canonical symplectic form `ω = -dλ` of
`T*Tⁿ` back to the linear form `TauCeti.strongDualCotangentSymplecticForm`,
`((δq, δξ), (δq', δξ')) ↦ δξ'(δq) - δξ(δq')`. In angles `θ = q` and actions `I_i = ξ(e_i)`, this
is `ω = ∑ i, dθ_i ∧ dI_i`. -/
theorem eval₂_mfderiv_torusMk (q u u' : (ι → ℝ) × ((ι → ℝ) →L[ℝ] ℝ)) :
    SmoothBundleForm.eval₂
        (symplecticForm (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) (∀ i, AddCircle (p i)))
        (torusMk p q)
        (mfderiv 𝓘(ℝ, (ι → ℝ) × ((ι → ℝ) →L[ℝ] ℝ))
          ((ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)).prod 𝓘(ℝ, (ι → ℝ) →L[ℝ] ℝ)) (torusMk p) q u)
        (mfderiv 𝓘(ℝ, (ι → ℝ) × ((ι → ℝ) →L[ℝ] ℝ))
          ((ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)).prod 𝓘(ℝ, (ι → ℝ) →L[ℝ] ℝ)) (torusMk p) q u') =
      strongDualCotangentSymplecticForm u u' := by
  have h : SmoothForm.mpullback (torusMk p) (contMDiff_torusMk p)
      (symplecticForm (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) (∀ i, AddCircle (p i))) =
      -mextDerivₗ 𝓘(ℝ, (ι → ℝ) × ((ι → ℝ) →L[ℝ] ℝ)) 1
        (SmoothForm.mpullback (torusMk p) (contMDiff_torusMk p) (liouvilleForm _ _)) := by
    rw [symplecticForm_eq_neg_mextDerivₗ, map_neg, SmoothForm.mextDerivₗ_mpullback]
  have h' := congrArg (fun φ ↦ φ.1 q ![u, u']) h
  simp only [NegMemClass.coe_neg, Pi.neg_apply, ContinuousAlternatingMap.neg_apply,
    mextDerivₗ_apply, SmoothForm.coe_mpullback, mpullback_torusMk_liouvilleForm] at h'
  rw [TauCeti.mpullback_apply] at h'
  rw [SmoothBundleForm.eval₂_apply]
  refine (congrArg _ ?_).trans (h'.trans ((congrArg
    (fun φ : ((ι → ℝ) × ((ι → ℝ) →L[ℝ] ℝ)) [⋀^Fin 2]→L[ℝ] ℝ ↦ -φ ![u, u'])
    (mextDeriv_eq_extDeriv cotangentLiouvilleForm q)).trans
    (neg_extDeriv_cotangentLiouvilleForm_apply q ![u, u'])))
  funext i
  fin_cases i <;> rfl

/-- **The covering of `T*Tⁿ` is a local diffeomorphism.** Its differential is injective, since it
pulls the nondegenerate form `ω` back to the nondegenerate linear form, and source and target have
the same dimension. -/
theorem isLocalDiffeomorph_torusMk :
    IsLocalDiffeomorph 𝓘(ℝ, (ι → ℝ) × ((ι → ℝ) →L[ℝ] ℝ))
      ((ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)).prod 𝓘(ℝ, (ι → ℝ) →L[ℝ] ℝ)) ∞ (torusMk p) := by
  intro q
  refine isLocalDiffeomorphAt_of_injective_mfderiv (contMDiff_torusMk p).contMDiffOn isOpen_univ
    (mem_univ q) BoundarylessManifold.isInteriorPoint (by simp) ?_ rfl
  rw [injective_iff_map_eq_zero]
  intro u hu
  refine strongDualCotangentSymplecticForm.nondegenerate.1 u fun u' ↦ ?_
  have h := eval₂_mfderiv_torusMk p q u u'
  rw [hu] at h
  have h0 := SmoothBundleForm.eval₂_smul_left
    (symplecticForm (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) (∀ i, AddCircle (p i))) (torusMk p q)
    (0 : ℝ) 0 (mfderiv 𝓘(ℝ, (ι → ℝ) × ((ι → ℝ) →L[ℝ] ℝ))
      ((ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)).prod 𝓘(ℝ, (ι → ℝ) →L[ℝ] ℝ)) (torusMk p) q u')
  rw [smul_zero, zero_smul] at h0
  exact h.symm.trans h0

end CotangentBundle

end TauCeti
