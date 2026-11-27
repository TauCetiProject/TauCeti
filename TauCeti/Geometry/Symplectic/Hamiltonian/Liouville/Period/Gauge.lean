/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
public import Mathlib.Analysis.Convex.Star
public import TauCeti.Geometry.Symplectic.Hamiltonian.Liouville.Period.GlobalActionAngle
import Mathlib.Analysis.Convex.Contractible
import TauCeti.Analysis.Calculus.DifferentialForm.Gradient
import TauCeti.Geometry.Manifold.Instances.AddCircle.Lift
import TauCeti.Geometry.Manifold.Instances.AddCircle.Torus

/-!
# The angle gauge of global action–angle coordinates is a gradient

Let `σ` be a symplectic form on a boundaryless manifold `M`, let `π : M → B` be a regular
Lagrangian torus fibration (`TauCeti.SmoothTwoForm.IsNondegenerate.IsLagrangianTorusFibration`)
and let `p > 0`. Two global action–angle charts `Φ, Φ' : M → T*(ι → ℝ/pℤ)` with actions `a ∘ π`
and `a' ∘ π`, over a preconnected base, differ by an integral affine change of the actions and an
angle gauge: `a' = P a + b₀` with `P ∈ GL(ι, ℤ)`, and at a point with `Φ x = κ(θ, a(π x))`,

`Φ' x = κ(θ P⁻¹ + g(π x), a'(π x))`,

for angles `g` that are smooth modulo `p ℤ^ι` and closed in the actions,
`∑ i, dg_i ∧ da'_i = 0`
(`IsLagrangianTorusFibration.exists_eq_mulVec_add_and_apply_eq_actionAngleCover_of_actionAngle`).
This file removes the two ambiguities left in this statement, the choice of representatives
of the angles `g` and the passage from a closed one-form to an exact one, and proves the
uniqueness statement in the form `(θ, I) ↦ (P⁻ᵀ θ + ∇S(I'), P I + b₀)`.

* **Real gauge.** On a simply connected base the torus-valued map `[g]` lifts to a smooth map
  `g : B → ℝ^ι` (`AddCircle.exists_contMDiff_lift_pi_of_simplyConnectedSpace`), and the closedness
  condition holds for this real lift, since the projection `ℝ^ι → (ℝ/pℤ)^ι` has the identity as
  differential
  (`exists_eq_mulVec_add_and_apply_eq_actionAngleCover_of_actionAngle_of_simplyConnectedSpace`).
* **Gradient gauge.** Over a star-convex set of actions `a'(B)`, a ball of actions for instance,
  the gauge is the gradient of a smooth function `S` of the actions:
  `g(b) = ∇S(a'(b))`, that is, `Φ' x = κ(θ P⁻¹ + ∇S(a'(π x)), a'(π x))`
  (`exists_eq_mulVec_add_and_apply_eq_actionAngleCover_fderiv_of_actionAngle`). The actions `a'`
  are a homeomorphism of the base onto `a'(B)`, with smooth inverse `c ↦ π(Φ'⁻¹(κ(0, c)))`, so the
  base is contractible and the real gauge exists. Read on `a'(B)` through this inverse, the
  closedness condition says that the derivative of `g ∘ a'⁻¹` is symmetric, and the Poincaré
  lemma on the star-convex open set `a'(B)`
  (`StarConvex.exists_contDiffOn_forall_hasFDerivAt_of_fderiv_dotProduct_comm`) gives `S`.

In the conventions of Duistermaat, writing `θ' = P⁻ᵀ (θ + ∇φ(I))` with `φ(I) = S(P I + b₀)`, this
is the change of coordinates `(θ, I) ↦ (P⁻ᵀ (θ + ∇φ(I)), P I + b₀)`: the integral affine change
`TauCeti.CotangentBundle.integralAffineDiffeomorph` composed with the angle gauge of a function of
the actions.

## Main results

All in the namespace `TauCeti.SmoothTwoForm.IsNondegenerate.IsLagrangianTorusFibration`.

* `exists_eq_mulVec_add_and_apply_eq_actionAngleCover_of_actionAngle_of_simplyConnectedSpace`:
  over a simply connected base, two global action–angle charts differ by an integral affine
  change and a smooth real angle gauge `g` with `∑ i, dg_i ∧ da'_i = 0`.
* `exists_eq_mulVec_add_and_apply_eq_actionAngleCover_fderiv_of_actionAngle`: over a
  star-convex set of actions, the angle gauge is the gradient `∇S` of a smooth function `S` of
  the actions.

## References

* J. J. Duistermaat, *On global action-angle coordinates*, Comm. Pure Appl. Math. 33 (1980),
  687–706, Section 2 (the ambiguity of action-angle coordinates).
* V. I. Arnold, *Mathematical Methods of Classical Mechanics*, 2nd ed., Graduate Texts in
  Mathematics 60, Springer, 1989, Section 50 (action-angle variables).
-/

public section

noncomputable section

open Bundle (TotalSpace)
open Function Set
open scoped ContDiff Manifold

namespace TauCeti.SmoothTwoForm.IsNondegenerate.IsLagrangianTorusFibration

open CotangentBundle Matrix

variable {E H M F H' B : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [BoundarylessManifold I M] [I.Boundaryless]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F] [TopologicalSpace H']
  {J : ModelWithCorners ℝ F H'} [TopologicalSpace B] [ChartedSpace H' B] [IsManifold J ∞ B]
  [T2Space B]
  {σ : SmoothTwoForm I M} {hσ : σ.IsNondegenerate} {π : M → B}
  {ι : Type*} [Fintype ι] [DecidableEq ι] (p : ℝ) [Fact (0 < p)] {a a' : B → ι → ℝ}
  {Φ Φ' : M → CotangentBundle (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) (ι → AddCircle p)}

variable (h : hσ.IsLagrangianTorusFibration J π)
  (hΦ : IsLocalDiffeomorph I
    ((ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)).prod 𝓘(ℝ, (ι → ℝ) →L[ℝ] ℝ)) ∞ Φ)
  (hΦσ : SmoothForm.mpullback Φ hΦ.contMDiff
    (CotangentBundle.symplecticForm (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) (ι → AddCircle p)) =
      σ)
  (hΦa : ∀ y, torusActions p (Φ y) = a (π y))
  (hΦ' : IsLocalDiffeomorph I
    ((ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)).prod 𝓘(ℝ, (ι → ℝ) →L[ℝ] ℝ)) ∞ Φ')
  (hΦ'σ : SmoothForm.mpullback Φ' hΦ'.contMDiff
    (CotangentBundle.symplecticForm (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) (ι → AddCircle p)) =
      σ)
  (hΦ'a : ∀ y, torusActions p (Φ' y) = a' (π y))

include h hΦ hΦσ hΦa hΦ' hΦ'σ hΦ'a in
/-- **Uniqueness of global action–angle coordinates over a simply connected base.** Let `Φ` and
`Φ'` be global action–angle coordinates with period `p` for the same fibration over a simply
connected base, with actions `a ∘ π` and `a' ∘ π`. Then there are `P ∈ GL(ι, ℤ)`, `b₀ : ι → ℝ` and
a smooth real angle gauge `g : B → ℝ^ι` such that `a' = P a + b₀`, the gauge is closed in the
actions, `dg(v) ⬝ᵥ da'(w) = dg(w) ⬝ᵥ da'(v)`, that is `∑ i, dg_i ∧ da'_i = 0`, and at every point
with coordinates `Φ x = κ(θ, a(π x))`,

`Φ' x = κ(θ P⁻¹ + g(π x), a'(π x))`. -/
theorem exists_eq_mulVec_add_and_apply_eq_actionAngleCover_of_actionAngle_of_simplyConnectedSpace
    [SimplyConnectedSpace B] (hΦi : Injective Φ) (hΦ'i : Injective Φ') :
    ∃ (P : GL ι ℤ) (b₀ : ι → ℝ) (g : B → ι → ℝ),
      (∀ b, a' b = (P : Matrix ι ι ℤ).map (↑) *ᵥ a b + b₀) ∧
      ContMDiff J 𝓘(ℝ, ι → ℝ) ∞ g ∧
      (∀ b v w,
        mfderiv J 𝓘(ℝ, ι → ℝ) g b v ⬝ᵥ mfderiv J 𝓘(ℝ, ι → ℝ) a' b w =
          mfderiv J 𝓘(ℝ, ι → ℝ) g b w ⬝ᵥ mfderiv J 𝓘(ℝ, ι → ℝ) a' b v) ∧
      ∀ x θ, Φ x = actionAngleCover p (θ, a (π x)) →
        Φ' x = actionAngleCover p
          (θ ᵥ* ((P⁻¹ : GL ι ℤ) : Matrix ι ι ℤ).map (↑) + g (π x), a' (π x)) := by
  obtain ⟨P, b₀, g₀, hP, hg₀, hsym, hΦ'x⟩ :=
    h.exists_eq_mulVec_add_and_apply_eq_actionAngleCover_of_actionAngle p hΦ hΦσ hΦa hΦ' hΦ'σ
      hΦ'a hΦi hΦ'i
  -- Lift the torus-valued gauge to a smooth real one.
  obtain ⟨g, hg, hgg₀⟩ := AddCircle.exists_contMDiff_lift_pi_of_simplyConnectedSpace hg₀
  -- The projection `ℝ^ι → (ℝ/pℤ)^ι` has the identity as differential, so the gauges have the same
  -- differential.
  have hdg (b : B) (v : TangentSpace J b) :
      mfderiv J (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) (fun b i ↦ (g₀ b i : AddCircle p)) b v =
        mfderiv J 𝓘(ℝ, ι → ℝ) g b v := by
    have hd : HasMFDerivAt J (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ))
        (fun b i ↦ (g₀ b i : AddCircle p)) b (mfderiv J 𝓘(ℝ, ι → ℝ) g b) :=
      ((AddCircle.hasMFDerivAt_coe_pi p (g b)).comp b
        ((hg b).mdifferentiableAt (by simp)).hasMFDerivAt).congr_of_eventuallyEq
        (Filter.Eventually.of_forall fun b ↦ (hgg₀ b).symm)
    rw [hd.mfderiv]
    -- The two sides differ only in the point at which the target tangent space is read.
    rfl
  refine ⟨P, b₀, g, hP, hg, fun b v w ↦ by rw [← hdg, ← hdg]; exact hsym b v w,
    fun x θ hx ↦ (hΦ'x x θ hx).trans (actionAngleCover_congr_coe p ?_ _)⟩
  funext i
  simp only [Pi.add_apply, AddCircle.coe_add]
  rw [← congrFun (hgg₀ (π x)) i]

include h hΦ' hΦ'σ hΦ'a in
/-- If the set of actions `a'(B)` of global action–angle coordinates `Φ'` is star-convex, then the
base is contractible: the actions are a homeomorphism of `B` onto `a'(B)`. -/
private theorem contractibleSpace_of_actionAngle [Nonempty B] {c₀ : ι → ℝ}
    (hst : StarConvex ℝ c₀ (range a')) (hΦ'i : Injective Φ') : ContractibleSpace B := by
  obtain ⟨b₁⟩ := (inferInstance : Nonempty B)
  have : Nonempty M := (h.isConnected_preimage_singleton b₁).nonempty.to_subtype.map (↑)
  obtain ⟨-, e, he, hea'⟩ :=
    h.isOpen_range_and_exists_contMDiffOn_apply_eq_of_actionAngle p hΦ' hΦ'σ hΦ'a hΦ'i
  let eB : B ≃ₜ range a' :=
    { toFun := fun b ↦ ⟨a' b, b, rfl⟩
      invFun := fun c ↦ e c
      left_inv := hea'
      right_inv := by
        rintro ⟨_, b, rfl⟩
        exact Subtype.ext (congrArg a' (hea' b))
      continuous_toFun := (h.contMDiff_of_actionAngle p hΦ' hΦ'a).continuous.subtype_mk _
      continuous_invFun := continuousOn_iff_continuous_domRestrict.1 he.continuousOn }
  have : ContractibleSpace (range a') := hst.contractibleSpace ⟨a' b₁, b₁, rfl⟩
  exact eB.contractibleSpace

include h hΦ hΦσ hΦa hΦ' hΦ'σ hΦ'a in
/-- **Uniqueness of global action–angle coordinates over a ball of actions.** Let `Φ` and `Φ'` be
global action–angle coordinates with period `p` for the same fibration, with actions `a ∘ π` and
`a' ∘ π`, such that the set of actions `a'(B)` is star-convex, for instance a ball. Then there are
`P ∈ GL(ι, ℤ)`, `b₀ : ι → ℝ` and a smooth function `S` of the actions such that `a' = P a + b₀`
and, at every point with coordinates `Φ x = κ(θ, a(π x))`,

`Φ' x = κ(θ P⁻¹ + ∇S(a'(π x)), a'(π x))`,

that is, `(θ, I) ↦ (P⁻ᵀ θ + ∇S(I'), P I + b₀)` in action–angle coordinates, where
`∇S(c) = (∂S/∂cᵢ)ᵢ`: an integral affine change of the actions and the angle gauge of a function of
the actions. -/
theorem exists_eq_mulVec_add_and_apply_eq_actionAngleCover_fderiv_of_actionAngle {c₀ : ι → ℝ}
    (hst : StarConvex ℝ c₀ (range a')) (hΦi : Injective Φ) (hΦ'i : Injective Φ') :
    ∃ (P : GL ι ℤ) (b₀ : ι → ℝ) (S : (ι → ℝ) → ℝ),
      (∀ b, a' b = (P : Matrix ι ι ℤ).map (↑) *ᵥ a b + b₀) ∧
      ContDiffOn ℝ ∞ S (range a') ∧
      ∀ x θ, Φ x = actionAngleCover p (θ, a (π x)) →
        Φ' x = actionAngleCover p
          (θ ᵥ* ((P⁻¹ : GL ι ℤ) : Matrix ι ι ℤ).map (↑) +
            (fun i ↦ fderiv ℝ S (a' (π x)) (Pi.single i 1)), a' (π x)) := by
  rcases isEmpty_or_nonempty B with hB | hB
  · exact ⟨1, 0, 0, isEmptyElim, by simp [range_eq_empty], fun x ↦ isEmptyElim (π x)⟩
  have : Nonempty M := (h.isConnected_preimage_singleton hB.some).nonempty.to_subtype.map (↑)
  have ha' := h.contMDiff_of_actionAngle p hΦ' hΦ'a
  obtain ⟨hVo, e, he, hea'⟩ :=
    h.isOpen_range_and_exists_contMDiffOn_apply_eq_of_actionAngle p hΦ' hΦ'σ hΦ'a hΦ'i
  have : ContractibleSpace B :=
    h.contractibleSpace_of_actionAngle p hΦ' hΦ'σ hΦ'a hst hΦ'i
  obtain ⟨P, b₀, g, hP, hg, hsym, hΦ'x⟩ :=
    h.exists_eq_mulVec_add_and_apply_eq_actionAngleCover_of_actionAngle_of_simplyConnectedSpace p
      hΦ hΦσ hΦa hΦ' hΦ'σ hΦ'a hΦi hΦ'i
  -- Read the gauge on `a'(B)` through the inverse of the actions.
  have hge : ContDiffOn ℝ ∞ (g ∘ e) (range a') :=
    contMDiffOn_iff_contDiffOn.1 (hg.comp_contMDiffOn he)
  have hgea' : (g ∘ e) ∘ a' = g := funext fun b ↦ by simp [hea']
  -- Its derivative is symmetric, as `dg = d(g ∘ e) ∘ da'` and `da'` is onto.
  have hdge (b : B) (v : TangentSpace J b) :
      fderiv ℝ (g ∘ e) (a' b) (mfderiv J 𝓘(ℝ, ι → ℝ) a' b v) = mfderiv J 𝓘(ℝ, ι → ℝ) g b v := by
    have hd : DifferentiableAt ℝ (g ∘ e) (a' b) :=
      (hge.differentiableOn (by simp) (a' b) ⟨b, rfl⟩).differentiableAt
        (hVo.mem_nhds ⟨b, rfl⟩)
    have hcomp := mfderiv_comp_apply (I' := 𝓘(ℝ, ι → ℝ)) b hd.mdifferentiableAt
      ((ha' b).mdifferentiableAt (by simp)) v
    rw [hgea', mfderiv_eq_fderiv] at hcomp
    exact hcomp.symm
  have hsym' : ∀ c ∈ range a', ∀ v w,
      fderiv ℝ (g ∘ e) c v ⬝ᵥ w = fderiv ℝ (g ∘ e) c w ⬝ᵥ v := by
    rintro _ ⟨b, rfl⟩ v w
    obtain ⟨v, rfl⟩ := (h.bijective_mfderiv_of_actionAngle p hΦ' hΦ'a b).2 v
    obtain ⟨w, rfl⟩ := (h.bijective_mfderiv_of_actionAngle p hΦ' hΦ'a b).2 w
    rw [hdge, hdge]
    exact hsym b v w
  -- The Poincaré lemma on the star-convex open set `a'(B)`.
  obtain ⟨S, hS, hSd⟩ := hst.exists_contDiffOn_forall_hasFDerivAt_of_fderiv_dotProduct_comm hVo
    (r := ⊤) le_top hge hsym'
  refine ⟨P, b₀, S, hP, by simpa using hS, fun x θ hx ↦ ?_⟩
  have hgrad : (fun i ↦ fderiv ℝ S (a' (π x)) (Pi.single i 1)) = g (π x) := by
    funext i
    rw [(hSd _ ⟨π x, rfl⟩).fderiv]
    simp [Pi.single_apply, hea']
  rw [hgrad]
  exact hΦ'x x θ hx

end TauCeti.SmoothTwoForm.IsNondegenerate.IsLagrangianTorusFibration
