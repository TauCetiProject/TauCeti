/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.Module.Equiv.Pi
public import Mathlib.Topology.EMetricSpace.Lipschitz
public import TauCeti.Analysis.Analytic.Submanifold.Basic
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import TauCeti.Analysis.Calculus.FDeriv.NormComparison
import TauCeti.Analysis.Analytic.Submanifold.Immersion
import TauCeti.Analysis.Analytic.Submanifold.Transport

/-!
# Topographic analytic submanifolds with Lipschitz height

Write points of `𝕜ⁿ⁺¹` in cylinder coordinates `Fin.cons t u`, with height `t = v 0` and base
point `u = Fin.tail v`, as in `TauCeti.IsAnalyticSubmanifold.cylinder`. Following Łojasiewicz, a
subset of `𝕜ⁿ⁺¹` is *topographic* when it is the graph of an analytic function on an analytic
submanifold of the base `𝕜ⁿ`.

Suppose that the heights of the points of a set `ψ ⊆ 𝕜ⁿ⁺¹` satisfy
`dist (v 0) (w 0) ≤ A * dist (Fin.tail v) (Fin.tail w)`. Then `ψ` is the graph of an `A`-Lipschitz
function over its projection `Fin.tail '' ψ`. If `ψ` is moreover a `d`-dimensional analytic
submanifold, then its projection is a `d`-dimensional analytic submanifold of `𝕜ⁿ` and every height
function of `ψ` is analytic on it, so `ψ` is topographic. The horizontal shear
`(t, u) ↦ (t, u + t • z)` preserves the inequality, with the worse constant `A / (1 - A * ‖z‖)`,
as long as `A * ‖z‖ < 1`; so it keeps such submanifolds topographic.

These are the topographic graph and shear statements of Lemma 6 in Łojasiewicz's triangulation of
semianalytic sets, used there to straighten families of graphs by small linear changes of
coordinates.

## Main declarations

* `TauCeti.exists_lipschitzOnWith_eq_graph`: a set satisfying the height inequality is the graph
  of an `A`-Lipschitz function over its projection.
* `TauCeti.IsAnalyticSubmanifold.image_tail`: the projection of an analytic submanifold satisfying
  the height inequality is an analytic submanifold of the same dimension.
* `TauCeti.IsAnalyticSubmanifold.analyticOnSubmanifold_image_tail`: its height functions are
  analytic on the projection.
* `TauCeti.IsAnalyticSubmanifold.exists_topographic`: such a submanifold is the graph of an
  `A`-Lipschitz function which is analytic on its projection, an analytic submanifold.
* `TauCeti.horizontalShear z`: the linear automorphism `(t, u) ↦ (t, u + t • z)` of `𝕜ⁿ⁺¹`.
* `TauCeti.mul_dist_tail_le_dist_tail_horizontalShear`: the shear estimate
  `‖Δu + Δt • z‖ ≥ (1 - A * ‖z‖) * ‖Δu‖`.
* `TauCeti.dist_le_mul_dist_tail_of_mem_image_horizontalShear` and
  `TauCeti.IsAnalyticSubmanifold.image_horizontalShear`: the sheared set satisfies the height
  inequality with constant `A / (1 - A * ‖z‖)` and is again an analytic submanifold.

## References

* S. Łojasiewicz, *Triangulation of semi-analytic sets*, Annali della Scuola Normale Superiore di
  Pisa (3) 18 (1964), 449–474 (topographic sets and Lemma 6).
-/

public section

open Set Filter Topology NNReal

namespace TauCeti

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {n d : ℕ} {ψ : Set (Fin (n + 1) → 𝕜)}
  {A : ℝ≥0}

/-! ### Graphs with Lipschitz height -/

/-- A set of `𝕜ⁿ⁺¹` whose differences of heights are bounded by `A` times the distances of the base
points is the graph of an `A`-Lipschitz function `f` over its projection to the base:
`f (Fin.tail v) = v 0` for `v ∈ ψ`, and `ψ` consists of the points over the projection whose
height is given by `f`. -/
theorem exists_lipschitzOnWith_eq_graph
    (h : ∀ v ∈ ψ, ∀ w ∈ ψ, dist (v 0) (w 0) ≤ A * dist (Fin.tail v) (Fin.tail w)) :
    ∃ f : (Fin n → 𝕜) → 𝕜, LipschitzOnWith A f (Fin.tail '' ψ) ∧
      (∀ v ∈ ψ, f (Fin.tail v) = v 0) ∧
        ψ = {v : Fin (n + 1) → 𝕜 | Fin.tail v ∈ Fin.tail '' ψ ∧ v 0 = f (Fin.tail v)} := by
  let f : (Fin n → 𝕜) → 𝕜 := fun u ↦
    Function.invFunOn (Fin.tail : (Fin (n + 1) → 𝕜) → Fin n → 𝕜) ψ u 0
  have hf (v : Fin (n + 1) → 𝕜) (hv : v ∈ ψ) : f (Fin.tail v) = v 0 := by
    have hv' : ∃ w ∈ ψ, (Fin.tail w : Fin n → 𝕜) = Fin.tail v := ⟨v, hv, rfl⟩
    have := h _ (Function.invFunOn_mem hv') v hv
    rw [Function.invFunOn_eq hv', dist_self, mul_zero] at this
    exact dist_le_zero.1 this
  refine ⟨f, LipschitzOnWith.of_dist_le_mul ?_, hf, ?_⟩
  · rintro _ ⟨v, hv, rfl⟩ _ ⟨w, hw, rfl⟩
    rw [hf v hv, hf w hw]
    exact h v hv w hw
  · ext v
    refine ⟨fun hv ↦ ⟨⟨v, hv, rfl⟩, (hf v hv).symm⟩, ?_⟩
    rintro ⟨⟨w, hw, hwv⟩, hv⟩
    rwa [← Fin.cons_self_tail v, hv, ← hwv, hf w hw, Fin.cons_self_tail]

/-! ### Topographic analytic submanifolds -/

section Analytic

variable [CompleteSpace 𝕜]

/-- Around each point of an analytic submanifold `ψ ⊆ 𝕜ⁿ⁺¹` satisfying the height inequality, its
projection `Fin.tail '' ψ` has an analytic chart `e` in dimension `d`, in which the local
parametrization `u ↦ e.symm (u, 0)` is the projection of an analytic parametrization `φ` of
`ψ`. -/
private theorem exists_isAnalyticChart_image_tail (hψ : IsAnalyticSubmanifold d ψ)
    (h : ∀ v ∈ ψ, ∀ w ∈ ψ, dist (v 0) (w 0) ≤ A * dist (Fin.tail v) (Fin.tail w))
    {v : Fin (n + 1) → 𝕜} (hv : v ∈ ψ) :
    d ≤ n ∧ ∃ (e : OpenPartialHomeomorph (Fin n → 𝕜) (Fin n → 𝕜))
      (φ : (Fin d → 𝕜) → Fin (n + 1) → 𝕜), Fin.tail v ∈ e.source ∧
        IsAnalyticChart d (Fin.tail '' ψ) e ∧ AnalyticAt 𝕜 φ (firstCoords 𝕜 n d (e (Fin.tail v))) ∧
          ∀ᶠ u in 𝓝 (firstCoords 𝕜 n d (e (Fin.tail v))),
            φ u ∈ ψ ∧ e.symm (firstCoords 𝕜 d n u) = Fin.tail (φ u) := by
  obtain ⟨c, hvc, hc⟩ := hψ.exists_isAnalyticChart v hv
  set u₀ := firstCoords 𝕜 (n + 1) d (c v)
  set φ : (Fin d → 𝕜) → Fin (n + 1) → 𝕜 := fun u ↦ c.symm (firstCoords 𝕜 d (n + 1) u)
  have hφ : AnalyticAt 𝕜 φ u₀ := hc.analyticAt_symm_firstCoords hvc hv
  have hφψ : ∀ᶠ u in 𝓝 u₀, φ u ∈ c.source ∩ ψ := hc.eventually_symm_firstCoords_mem hvc hv
  have hφu₀ : φ u₀ = v := hc.symm_firstCoords_firstCoords_apply hvc hv
  let τ : (Fin (n + 1) → 𝕜) →L[𝕜] Fin n → 𝕜 := Pi.compRightL 𝕜 (fun _ ↦ 𝕜) Fin.succ
  have hτ (w : Fin (n + 1) → 𝕜) : τ w = Fin.tail w :=
    funext fun i ↦ Pi.compRightL_apply 𝕜 (fun _ ↦ 𝕜) Fin.succ w i
  set p : (Fin d → 𝕜) → Fin n → 𝕜 := fun u ↦ Fin.tail (φ u)
  have hp : AnalyticAt 𝕜 p u₀ := by
    simpa only [p, Function.comp_def, hτ] using (τ.analyticAt _).comp hφ
  -- The parametrization `φ` is an immersion, since `c ∘ φ` is the inclusion `u ↦ (u, 0)`.
  have hDφ : Function.Injective (fderiv 𝕜 φ u₀) :=
    hc.injective_fderiv_symm_firstCoords hvc hv hψ.le
  -- By the height inequality, so is its projection `p`.
  have hDp : Function.Injective (fderiv 𝕜 p u₀) := by
    have hp' : HasFDerivAt p (τ.comp (fderiv 𝕜 φ u₀)) u₀ := by
      simpa only [p, Function.comp_def, hτ] using
        τ.hasFDerivAt.comp u₀ hφ.differentiableAt.hasFDerivAt
    rw [hp'.fderiv]
    refine (injective_iff_map_eq_zero _).2 fun k hk ↦ hDφ ?_
    rw [ContinuousLinearMap.comp_apply, hτ] at hk
    -- Tangent vectors to `ψ` satisfy the height inequality as well.
    have h0 : ‖fderiv 𝕜 φ u₀ k 0‖ ≤ A * ‖τ (fderiv 𝕜 φ u₀ k)‖ := by
      refine hφ.differentiableAt.hasFDerivAt.norm_apply_le_mul_norm_apply
        (L := ContinuousLinearMap.proj 0) ?_ k
      filter_upwards [hφψ] with u hu
      have := h _ hu.2 _ hφψ.self_of_nhds.2
      rwa [dist_eq_norm, dist_eq_norm, ← hτ, ← hτ, ← map_sub] at this
    rw [hτ, hk, norm_zero, mul_zero, norm_le_zero_iff] at h0
    rw [map_zero]
    funext i
    exact Fin.cases h0 (fun j ↦ congrFun hk j) i
  have hd : d ≤ n := by
    simpa using LinearMap.finrank_le_finrank_of_injective (f := (fderiv 𝕜 p u₀).toLinearMap) hDp
  -- Points of `Fin.tail '' ψ` near `Fin.tail v` lift to points of `ψ` near `v`, since the
  -- height is a Lipschitz function of the base point.
  obtain ⟨f, hf, hfψ', hψf⟩ := exists_lipschitzOnWith_eq_graph h
  have hfψ {w : Fin (n + 1) → 𝕜} (hw : w ∈ ψ) : w 0 = f (Fin.tail w) := (hfψ' w hw).symm
  have hpu₀ : p u₀ = Fin.tail v := by rw [← hφu₀]
  have himage : ∀ V ∈ 𝓝 u₀, p '' V ∈ 𝓝[Fin.tail '' ψ] (p u₀) := by
    intro V hV
    rw [hpu₀]
    let Γ : (Fin n → 𝕜) → Fin (n + 1) → 𝕜 := fun y ↦ Fin.cons (f y) y
    have hΓv : Γ (Fin.tail v) = v := by
      simp only [Γ]
      rw [← hfψ hv, Fin.cons_self_tail]
    have hΓ : ContinuousWithinAt Γ (Fin.tail '' ψ) (Fin.tail v) :=
      (hf.continuousOn _ ⟨v, hv, rfl⟩).finCons continuousWithinAt_id
    have hN : c.source ∩ (fun w ↦ firstCoords 𝕜 (n + 1) d (c w)) ⁻¹' V ∈ 𝓝 (Γ (Fin.tail v)) := by
      rw [hΓv]
      exact inter_mem (c.open_source.mem_nhds hvc)
        (((firstCoords 𝕜 (n + 1) d).continuous.continuousAt.comp
          (c.continuousAt hvc)).preimage_mem_nhds hV)
    filter_upwards [hΓ.preimage_mem_nhdsWithin hN, self_mem_nhdsWithin] with y hyN hyψ
    have hΓy : Γ y ∈ ψ := (Set.ext_iff.1 hψf _).2 ⟨by simpa [Γ] using hyψ, by simp [Γ]⟩
    refine ⟨firstCoords 𝕜 (n + 1) d (c (Γ y)), hyN.2, ?_⟩
    simp only [p, φ, hc.symm_firstCoords_firstCoords_apply hyN.1 hΓy, Γ, Fin.tail_cons]
  have hT : ∀ᶠ u in 𝓝 u₀, p u ∈ Fin.tail '' ψ := hφψ.mono fun u hu ↦ ⟨φ u, hu.2, rfl⟩
  obtain ⟨e, he, hec, heu₀, hesymm⟩ := exists_isAnalyticChart_of_injective_fderiv hp hDp hT himage
  rw [hpu₀] at he heu₀
  refine ⟨hd, e, φ, he, hec, heu₀ ▸ hφ, ?_⟩
  rw [heu₀]
  filter_upwards [hφψ, hesymm] with u hu hu'
  exact ⟨hu.2, hu'⟩

/-- **Lipschitz graphs project to submanifolds.** If a `d`-dimensional analytic submanifold
`ψ ⊆ 𝕜ⁿ⁺¹` satisfies `dist (v 0) (w 0) ≤ A * dist (Fin.tail v) (Fin.tail w)` for all its points,
then its projection `Fin.tail '' ψ` to the base `𝕜ⁿ` is a `d`-dimensional analytic
submanifold. -/
theorem IsAnalyticSubmanifold.image_tail (hψ : IsAnalyticSubmanifold d ψ)
    (h : ∀ v ∈ ψ, ∀ w ∈ ψ, dist (v 0) (w 0) ≤ A * dist (Fin.tail v) (Fin.tail w)) :
    IsAnalyticSubmanifold d (Fin.tail '' ψ) := by
  obtain ⟨v, hv⟩ := hψ.nonempty
  refine ⟨⟨_, v, hv, rfl⟩, (exists_isAnalyticChart_image_tail hψ h hv).1, ?_⟩
  rintro _ ⟨w, hw, rfl⟩
  obtain ⟨-, e, -, he, hec, -⟩ := exists_isAnalyticChart_image_tail hψ h hw
  exact ⟨e, he, hec⟩

/-- **The height of a Lipschitz graph is analytic.** If a `d`-dimensional analytic submanifold
`ψ ⊆ 𝕜ⁿ⁺¹` satisfies `dist (v 0) (w 0) ≤ A * dist (Fin.tail v) (Fin.tail w)` for all its points,
then every function `f` giving the heights of the points of `ψ`, `f (Fin.tail v) = v 0`, is
analytic on the projection `Fin.tail '' ψ`. So `ψ` is topographic: the graph of an analytic
function on an analytic submanifold of the base, which by `TauCeti.exists_lipschitzOnWith_eq_graph`
may be chosen `A`-Lipschitz. -/
theorem IsAnalyticSubmanifold.analyticOnSubmanifold_image_tail (hψ : IsAnalyticSubmanifold d ψ)
    (h : ∀ v ∈ ψ, ∀ w ∈ ψ, dist (v 0) (w 0) ≤ A * dist (Fin.tail v) (Fin.tail w))
    {f : (Fin n → 𝕜) → 𝕜} (hf : ∀ v ∈ ψ, f (Fin.tail v) = v 0) :
    AnalyticOnSubmanifold d f (Fin.tail '' ψ) := by
  refine TauCeti.analyticOnSubmanifold_iff.2 ?_
  rintro _ ⟨v, hv, rfl⟩
  obtain ⟨-, e, φ, he, hec, hφ, hev⟩ := exists_isAnalyticChart_image_tail hψ h hv
  refine ⟨e, he, hec, (((ContinuousLinearMap.proj 0).analyticAt _).comp hφ).congr ?_⟩
  filter_upwards [hev] with u hu
  simp [hu.2, hf _ hu.1]

/-- **Lipschitz analytic submanifolds are topographic** (Łojasiewicz). If a `d`-dimensional
analytic submanifold `ψ ⊆ 𝕜ⁿ⁺¹` satisfies `dist (v 0) (w 0) ≤ A * dist (Fin.tail v) (Fin.tail w)`
for all its points, then it is the graph of an `A`-Lipschitz function `f` which is analytic on
the `d`-dimensional analytic submanifold `Fin.tail '' ψ` of the base. -/
theorem IsAnalyticSubmanifold.exists_topographic (hψ : IsAnalyticSubmanifold d ψ)
    (h : ∀ v ∈ ψ, ∀ w ∈ ψ, dist (v 0) (w 0) ≤ A * dist (Fin.tail v) (Fin.tail w)) :
    ∃ f : (Fin n → 𝕜) → 𝕜, LipschitzOnWith A f (Fin.tail '' ψ) ∧
      AnalyticOnSubmanifold d f (Fin.tail '' ψ) ∧ IsAnalyticSubmanifold d (Fin.tail '' ψ) ∧
        (∀ v ∈ ψ, f (Fin.tail v) = v 0) ∧
          ψ = {v : Fin (n + 1) → 𝕜 | Fin.tail v ∈ Fin.tail '' ψ ∧ v 0 = f (Fin.tail v)} := by
  obtain ⟨f, hfL, hf, hψf⟩ := exists_lipschitzOnWith_eq_graph h
  exact ⟨f, hfL, hψ.analyticOnSubmanifold_image_tail h hf, hψ.image_tail h, hf, hψf⟩

end Analytic

/-! ### Horizontal shears -/

/-- The *horizontal shear* of `𝕜ⁿ⁺¹` with slope `z ∈ 𝕜ⁿ` is the linear automorphism
`(t, u) ↦ (t, u + t • z)` in cylinder coordinates `Fin.cons t u`: it keeps the height and moves
the base point along `z` in proportion to the height. -/
def horizontalShear (z : Fin n → 𝕜) : (Fin (n + 1) → 𝕜) ≃L[𝕜] Fin (n + 1) → 𝕜 :=
  (Fin.consEquivL 𝕜 fun _ ↦ 𝕜).symm.trans <|
    ((ContinuousLinearEquiv.refl 𝕜 𝕜).skewProd (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜))
      ((ContinuousLinearMap.id 𝕜 𝕜).smulRight z)).trans (Fin.consEquivL 𝕜 fun _ ↦ 𝕜)

/-- In cylinder coordinates, the horizontal shear with slope `z` maps `(t, u)` to
`(t, u + t • z)`. -/
theorem horizontalShear_apply (z : Fin n → 𝕜) (v : Fin (n + 1) → 𝕜) :
    horizontalShear z v = Fin.cons (v 0) (Fin.tail v + v 0 • z) := by
  ext i
  simp [horizontalShear, Fin.consEquivL_apply]

@[simp]
theorem horizontalShear_apply_zero (z : Fin n → 𝕜) (v : Fin (n + 1) → 𝕜) :
    horizontalShear z v 0 = v 0 := by
  simp [horizontalShear_apply]

@[simp]
theorem tail_horizontalShear (z : Fin n → 𝕜) (v : Fin (n + 1) → 𝕜) :
    Fin.tail (horizontalShear z v) = Fin.tail v + v 0 • z := by
  simp [horizontalShear_apply]

/-- The inverse of the horizontal shear with slope `z` is the horizontal shear with slope
`-z`. -/
@[simp]
theorem horizontalShear_symm (z : Fin n → 𝕜) :
    (horizontalShear z).symm = horizontalShear (-z) := by
  refine ContinuousLinearEquiv.ext <| funext fun v ↦ (horizontalShear z).symm_apply_eq.2 ?_
  rw [horizontalShear_apply, tail_horizontalShear, horizontalShear_apply_zero, smul_neg,
    neg_add_cancel_right, Fin.cons_self_tail]

/-- A horizontal shear maps analytic submanifolds of `𝕜ⁿ⁺¹` to analytic submanifolds of the same
dimension. -/
theorem IsAnalyticSubmanifold.image_horizontalShear (hψ : IsAnalyticSubmanifold d ψ)
    (z : Fin n → 𝕜) : IsAnalyticSubmanifold d (horizontalShear z '' ψ) := by
  rw [ContinuousLinearEquiv.image_eq_preimage_symm, horizontalShear_symm]
  exact hψ.preimage (horizontalShear (-z)).toHomeomorph
    (fun v _ ↦ (horizontalShear (-z)).analyticAt v)
    (fun v _ ↦ (horizontalShear (-z)).symm.analyticAt v)

/-- **Shears of Lipschitz graphs.** If the heights of two points `v` and `w` satisfy
`dist (v 0) (w 0) ≤ A * dist (Fin.tail v) (Fin.tail w)`, then a horizontal shear with slope `z`
shrinks the distance of their base points by at most the factor `1 - A * ‖z‖`:
`‖Δu + Δt • z‖ ≥ (1 - A * ‖z‖) * ‖Δu‖`. -/
theorem mul_dist_tail_le_dist_tail_horizontalShear (z : Fin n → 𝕜) {v w : Fin (n + 1) → 𝕜}
    (hvw : dist (v 0) (w 0) ≤ A * dist (Fin.tail v) (Fin.tail w)) :
    (1 - A * ‖z‖) * dist (Fin.tail v) (Fin.tail w) ≤
      dist (Fin.tail (horizontalShear z v)) (Fin.tail (horizontalShear z w)) := by
  rw [dist_eq_norm, dist_eq_norm] at hvw ⊢
  have hΔ : Fin.tail v + v 0 • z - (Fin.tail w + w 0 • z) =
      Fin.tail v - Fin.tail w + (v 0 - w 0) • z := by
    rw [sub_smul]
    abel
  rw [tail_horizontalShear, tail_horizontalShear, hΔ]
  have htri := norm_sub_le (Fin.tail v - Fin.tail w + (v 0 - w 0) • z) ((v 0 - w 0) • z)
  rw [add_sub_cancel_right, norm_smul] at htri
  nlinarith [norm_nonneg z, norm_nonneg (Fin.tail v - Fin.tail w)]

/-- **Shears of Lipschitz graphs.** If the heights of the points of `ψ` satisfy
`dist (v 0) (w 0) ≤ A * dist (Fin.tail v) (Fin.tail w)` and `A * ‖z‖ < 1`, then the heights of the
points of the sheared set `horizontalShear z '' ψ` satisfy the same inequality with the constant
`A / (1 - A * ‖z‖)`. -/
theorem dist_le_mul_dist_tail_of_mem_image_horizontalShear
    (h : ∀ v ∈ ψ, ∀ w ∈ ψ, dist (v 0) (w 0) ≤ A * dist (Fin.tail v) (Fin.tail w))
    {z : Fin n → 𝕜} (hz : A * ‖z‖₊ < 1) :
    ∀ v ∈ horizontalShear z '' ψ, ∀ w ∈ horizontalShear z '' ψ,
      dist (v 0) (w 0) ≤ (A / (1 - A * ‖z‖₊) : ℝ≥0) * dist (Fin.tail v) (Fin.tail w) := by
  rintro _ ⟨v, hv, rfl⟩ _ ⟨w, hw, rfl⟩
  have hz' : 0 < 1 - (A : ℝ) * ‖z‖ := by
    rw [sub_pos]
    exact_mod_cast hz
  rw [horizontalShear_apply_zero, horizontalShear_apply_zero, NNReal.coe_div,
    NNReal.coe_sub hz.le, NNReal.coe_mul, coe_nnnorm, NNReal.coe_one, div_mul_eq_mul_div,
    le_div_iff₀ hz']
  calc dist (v 0) (w 0) * (1 - A * ‖z‖)
      ≤ A * dist (Fin.tail v) (Fin.tail w) * (1 - A * ‖z‖) :=
        mul_le_mul_of_nonneg_right (h v hv w hw) hz'.le
    _ = A * ((1 - A * ‖z‖) * dist (Fin.tail v) (Fin.tail w)) := by ring
    _ ≤ A * dist (Fin.tail (horizontalShear z v)) (Fin.tail (horizontalShear z w)) :=
        mul_le_mul_of_nonneg_left
          (mul_dist_tail_le_dist_tail_horizontalShear z (h v hv w hw)) A.2

end TauCeti
