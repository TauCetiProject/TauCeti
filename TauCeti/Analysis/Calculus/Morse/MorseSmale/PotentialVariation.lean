/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.Morse.Fredholm
import TauCeti.Analysis.Calculus.BumpFunction.Path
import TauCeti.Analysis.Calculus.Gradient
import TauCeti.Analysis.Calculus.Morse.GradientFlow
import TauCeti.Analysis.InnerProductSpace.Projection.Completeness
import TauCeti.Analysis.Normed.Group.Basic
import TauCeti.LinearAlgebra.Submodule.Quotient
import TauCeti.MeasureTheory.Function.L2Space

/-!
# Potential variations make the linearized gradient trajectory equation onto

Let `f` be a `C²` function on a finite-dimensional real inner product space `E`, and `γ` a
negative gradient trajectory, `γ' = -∇f(γ)`. Linearizing the trajectory equation at `γ` gives the
trajectory operator `D_γ ξ = ξ' + Hess f(γ) ξ` from `W^{1,2}(ℝ, E)` to `L²(ℝ, E)`
(`TauCeti.WeakDerivStep.trajectoryOperator`). Changing the potential changes the equation as well:
the derivative of `(γ + ξ)' + ∇(f + ε h)(γ + ξ) = 0` in the direction of a potential variation `h`
is the path

`s ↦ ∇h (γ s)`,

so the universal linearization, in the trajectory and the potential together, is
`(ξ, h) ↦ D_γ ξ + ∇h(γ)`. The **potential variations** along `γ` of class `Cⁿ` localized in a set
`U` (`TauCeti.potentialVariations γ n U`) are the span in `L²(ℝ, E)` of the classes of these paths,
for compactly supported `Cⁿ` functions `h` supported in `U` which vanish on the trajectory. Such
an `h` leaves the values of the potential along `γ` unchanged, so `∇h` is normal to `γ` at its
points.

This file proves that these variations make the universal linearization onto as soon as `U` is a
neighbourhood of one point `γ s₀` of the trajectory that is not a critical point of `f`:

* a path orthogonal to the range of `D_γ` and to the potential variations vanishes, when `f` is
  `Cⁿ` with `2 ≤ n` and the gradient is bounded along `γ`
  (`eq_zero_of_mem_orthogonal_range_trajectoryOperator_of_mem_orthogonal_potentialVariations`),
  so the range and the variations span `L²(ℝ, E)` whenever the range is closed of finite
  codimension, as for a Fredholm operator
  (`TauCeti.range_trajectoryOperator_sup_potentialVariations_eq_top_of_isClosed_of_coFG`);
* along a trajectory between nondegenerate critical points
  (`TauCeti.range_trajectoryOperator_sup_potentialVariations_eq_top`), and finitely many variations
  already suffice
  (`TauCeti.exists_finset_subset_potentialVariations_range_trajectoryOperator_sup_span_eq_top`).

The proof goes through the cokernel. A nonzero path `v` orthogonal to the range of `D_γ` agrees
almost everywhere with a solution `u` of the formal adjoint equation `u' = Hess f(γ) u` which
vanishes at no time
(`WeakDerivStep.exists_hasDerivAt_ne_zero_of_mem_orthogonal_range_trajectoryOperator`).

* **The tangential component.** Since `γ'' = -Hess f(γ) γ'` and the Hessian is symmetric, the
  pairing `⟪u, ∇f(γ)⟫` is constant (`TauCeti.hasDerivAt_inner_gradient_comp`). As `u` is square
  integrable and `∇f(γ)` is bounded, the constant is `0`
  (`TauCeti.inner_gradient_comp_eq_zero_of_memLp`): `u` is normal to the trajectory everywhere.
* **The normal component.** Near the regular point `γ s₀`, the level-hitting time `τ(x)`, defined
  by `f (γ (τ x)) = f x`, is a `Cⁿ` function, by the inverse function theorem for `t ↦ f (γ t)`,
  whose derivative `-‖∇f(γ t)‖²` does not vanish near `s₀`. The function
  `g x = ⟪u s₀, x - γ (τ x)⟫` vanishes on the trajectory near `γ s₀`, and its derivative at `γ s`
  is `⟪u s₀, ·⟫` on the vectors normal to `∇f(γ s)`. A bump `ψ` at `γ s₀` so small that the
  trajectory meets it only at times close to `s₀` makes `h = ψ g` a potential variation whose path
  pairs with `u` as `s ↦ ψ (γ s) ⟪u s₀, u s⟫`, positive near `s₀`. So `u (s₀) = 0`, and by
  uniqueness for linear equations `u = 0`.

When the range is closed with finite codimension, as a Fredholm range is, the sum of the range and
the variations is closed, and its orthogonal complement is zero.

The metric variations of `TauCeti.Analysis.Calculus.Morse.MorseSmale.MetricVariation` move the
gradient along `γ` in every direction, including that of the trajectory, so they need no tangential
argument. Potential variations vanishing on `γ` move it only in normal directions, and serve when
the metric is kept fixed and only the function varies; the tangential component of the cokernel is
then excluded by the adjoint identity instead.

## Main definitions

* `TauCeti.potentialVariations γ n U`: the potential variations of class `Cⁿ` along `γ` localized
  in `U`, the smallest submodule containing the paths of these variations
  (`TauCeti.potentialVariations_le_iff`).

## Main results

* `TauCeti.inner_gradient_comp_eq_zero_of_memLp`: a square-integrable solution of the adjoint
  equation is normal to the trajectory.
* `eq_zero_of_mem_orthogonal_range_trajectoryOperator_of_mem_orthogonal_potentialVariations`:
  a path orthogonal to the range of `D_γ` and to the potential variations localized near a regular
  point of `γ` vanishes.
* `TauCeti.range_trajectoryOperator_sup_potentialVariations_eq_top`: the range of `D_γ` and the
  potential variations span `L²(ℝ, E)`.
* `TauCeti.exists_finset_subset_potentialVariations_range_trajectoryOperator_sup_span_eq_top`:
  finitely many potential variations suffice.

## References

* M. Schwarz, *Morse Homology*, Progress in Mathematics **111**, Birkhäuser, 1993, Chapter 2
  (transversality of the universal section through the cokernel of the linearized operator).
* D. Salamon, *Morse theory, the Conley index and Floer homology*, Bull. London Math. Soc. **22**
  (1990), 113--140 (genericity of Morse–Smale data by the Sard–Smale theorem, with the cokernel
  killed by variations and unique continuation for the adjoint equation).
-/

public section

open Filter MeasureTheory Set Topology
open scoped ContDiff ENNReal Gradient RealInnerProductSpace

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  {f : E → ℝ} {γ : ℝ → E}

variable (γ) in
/-- The **potential variations** of class `Cⁿ` along `γ` localized in `U`: the span in `L²(ℝ, E)`
of the classes of the paths `s ↦ ∇h (γ s)`, for compactly supported `Cⁿ` functions `h` with support
in `U` which vanish on the trajectory `γ`. The path `s ↦ ∇h (γ s)` is the derivative at `ε = 0` of
the gradient of `f + ε h` along `γ`, the direction in which varying the potential moves the gradient
trajectory equation at `γ`. -/
noncomputable def potentialVariations (n : ℕ∞) (U : Set E) :
    Submodule ℝ (Lp E 2 (volume.restrict ((⊤ : TopologicalSpace.Opens ℝ) : Set ℝ))) :=
  Submodule.span ℝ {g | ∃ h : E → ℝ, ContDiff ℝ n h ∧ HasCompactSupport h ∧ tsupport h ⊆ U ∧
    (∀ s, h (γ s) = 0) ∧
    g =ᵐ[volume.restrict ((⊤ : TopologicalSpace.Opens ℝ) : Set ℝ)] fun s ↦ ∇ h (γ s)}

/-- The class of the path `s ↦ ∇h (γ s)` of a compactly supported `Cⁿ` function `h` supported in
`U` and vanishing on `γ` is a potential variation. -/
theorem mem_potentialVariations_of_ae_eq {n : ℕ∞} {U : Set E} {h : E → ℝ} (hh : ContDiff ℝ n h)
    (hc : HasCompactSupport h) (hU : tsupport h ⊆ U) (hγ : ∀ s, h (γ s) = 0)
    {g : Lp E 2 (volume.restrict ((⊤ : TopologicalSpace.Opens ℝ) : Set ℝ))}
    (hg : g =ᵐ[volume.restrict ((⊤ : TopologicalSpace.Opens ℝ) : Set ℝ)] fun s ↦ ∇ h (γ s)) :
    g ∈ potentialVariations γ n U :=
  Submodule.subset_span ⟨h, hh, hc, hU, hγ, hg⟩

/-- A submodule contains the potential variations if and only if it contains the class of the
path `s ↦ ∇h (γ s)` of every compactly supported `Cⁿ` function `h` supported in `U` and vanishing
on `γ`: the potential variations are the smallest such submodule. -/
theorem potentialVariations_le_iff {n : ℕ∞} {U : Set E}
    {S : Submodule ℝ (Lp E 2 (volume.restrict ((⊤ : TopologicalSpace.Opens ℝ) : Set ℝ)))} :
    potentialVariations γ n U ≤ S ↔ ∀ h : E → ℝ, ContDiff ℝ n h → HasCompactSupport h →
      tsupport h ⊆ U → (∀ s, h (γ s) = 0) →
      ∀ g : Lp E 2 (volume.restrict ((⊤ : TopologicalSpace.Opens ℝ) : Set ℝ)),
        (g =ᵐ[volume.restrict ((⊤ : TopologicalSpace.Opens ℝ) : Set ℝ)] fun s ↦ ∇ h (γ s)) →
        g ∈ S :=
  Submodule.span_le.trans ⟨fun hS h hh hc hU hγ _ hg ↦ hS ⟨h, hh, hc, hU, hγ, hg⟩,
    fun hS _ ⟨h, hh, hc, hU, hγ, hg⟩ ↦ hS h hh hc hU hγ _ hg⟩

/-- Potential variations localized in a smaller set are potential variations localized in a
larger one. -/
theorem potentialVariations_mono {n : ℕ∞} {U V : Set E} (h : U ⊆ V) :
    potentialVariations γ n U ≤ potentialVariations γ n V :=
  Submodule.span_mono fun _ ⟨k, hk, hc, hU, hγ, hg⟩ ↦ ⟨k, hk, hc, hU.trans h, hγ, hg⟩

/-- Potential variations of a higher class are potential variations of a lower class. -/
theorem potentialVariations_anti {m n : ℕ∞} (hmn : m ≤ n) (U : Set E) :
    potentialVariations γ n U ≤ potentialVariations γ m U :=
  Submodule.span_mono fun _ ⟨k, hk, hc, hU, hγ, hg⟩ ↦
    ⟨k, hk.of_le (WithTop.coe_le_coe.2 hmn), hc, hU, hγ, hg⟩

/-! ### Adjoint solutions are normal to the trajectory -/

/-- **The adjoint identity.** Let `f` be `C²`, `γ` a negative gradient trajectory and `u` a solution
of the adjoint equation `u' = Hess f(γ) u` of the linearized operator. Then `⟪u, ∇f(γ)⟫`, the
pairing of `u` with minus the velocity of `γ`, has derivative `0`. -/
theorem hasDerivAt_inner_gradient_comp (hf : ContDiff ℝ 2 f)
    (hγ : IsIntegralCurve γ (fun _ x ↦ -∇ f x)) {u : ℝ → E}
    (hu : ∀ s, HasDerivAt u (hessianOperator f (γ s) (u s)) s) (s : ℝ) :
    HasDerivAt (fun t ↦ ⟪u t, ∇ f (γ t)⟫) 0 s := by
  convert (hu s).inner ℝ (hf.contDiffAt.hasDerivAt_gradient_comp (hγ s)) using 1
  have hsym :=
    (hf.contDiffAt (x := γ s)).isSelfAdjoint_hessianOperator.isSymmetric (u s) (∇ f (γ s))
  simp only [ContinuousLinearMap.coe_coe] at hsym
  dsimp only
  rw [map_neg, inner_neg_right, hsym, neg_add_cancel]

/-- **Square-integrable adjoint solutions are normal to the trajectory.** Let `f` be `C²`, `γ` a
negative gradient trajectory along which `∇f` is bounded, and `u` a square-integrable solution of
the adjoint equation `u' = Hess f(γ) u`. Then `u s` is orthogonal to `∇f(γ s)`, minus the
velocity of the trajectory, at every time `s`. -/
theorem inner_gradient_comp_eq_zero_of_memLp (hf : ContDiff ℝ 2 f)
    (hγ : IsIntegralCurve γ (fun _ x ↦ -∇ f x)) {u : ℝ → E}
    (hu : ∀ s, HasDerivAt u (hessianOperator f (γ s) (u s)) s) (hu2 : MemLp u 2 volume)
    {C : ℝ} (hC : ∀ s, ‖∇ f (γ s)‖ ≤ C) (s : ℝ) : ⟪u s, ∇ f (γ s)⟫ = 0 := by
  have hd := hasDerivAt_inner_gradient_comp hf hγ hu
  have hconst : (fun t ↦ ⟪u t, ∇ f (γ t)⟫) = fun _ ↦ ⟪u s, ∇ f (γ s)⟫ := funext fun t ↦
    is_const_of_deriv_eq_zero (fun t ↦ (hd t).differentiableAt) (fun t ↦ (hd t).deriv) t s
  have hmem : MemLp (fun t ↦ ⟪u t, ∇ f (γ t)⟫) 2 volume :=
    hu2.of_le_mul (c := C) (continuous_iff_continuousAt.2 fun t ↦
      (hd t).continuousAt).aestronglyMeasurable (.of_forall fun t ↦ by
        rw [Real.norm_eq_abs, mul_comm]
        exact (abs_real_inner_le_norm _ _).trans
          (mul_le_mul_of_nonneg_left (hC t) (norm_nonneg _)))
  rw [hconst, memLp_const_iff two_ne_zero ENNReal.ofNat_ne_top, Real.volume_univ] at hmem
  simpa using hmem

/-! ### A potential variation pairing positively with a normal path -/

/-- **A function vanishing on the trajectory with prescribed normal derivative.** Let `f` be `Cⁿ`,
`n ≠ 0`, and `γ` a negative gradient trajectory with `∇f(γ s₀) ≠ 0`, so that `γ` is `Cⁿ` as well.
For every vector `w` there is a function `g`, of class `Cⁿ` at the points of an open set
`O ∋ γ s₀`, which vanishes on the trajectory at times near `s₀`, and whose derivative at every
point `γ s ∈ O` is `⟪w, ·⟫` on the vectors orthogonal to `∇f(γ s)`: `g x = ⟪w, x - γ (σ (f x))⟫`
for the level-hitting time `σ ∘ f` of `IsIntegralCurve.exists_contDiffAt_levelHittingTime`. -/
private theorem exists_contDiffAt_eventually_eq_zero_fderiv_eq_inner {n : ℕ∞}
    (hf : ContDiff ℝ n f) (hn0 : (n : WithTop ℕ∞) ≠ 0)
    (hγ : IsIntegralCurve γ (fun _ x ↦ -∇ f x)) {s₀ : ℝ} (hcrit : ∇ f (γ s₀) ≠ 0) (w : E) :
    ∃ O : Set E, IsOpen O ∧ γ s₀ ∈ O ∧ ∃ g : E → ℝ, (∀ x ∈ O, ContDiffAt ℝ n g x) ∧
      (∀ᶠ s in 𝓝 s₀, g (γ s) = 0) ∧
      ∀ s, γ s ∈ O → ∀ v, ⟪v, ∇ f (γ s)⟫ = 0 → fderiv ℝ g (γ s) v = ⟪w, v⟫ := by
  have hγn := hγ.contDiff_neg_gradient hf (Order.one_le_iff_ne_zero.2 (by exact_mod_cast hn0))
  obtain ⟨σ, T, hT, hsT, hσ, hσγ⟩ := hγ.exists_contDiffAt_levelHittingTime hf hn0 hcrit
  have hk {x : E} (hx : f x ∈ T) : ContDiffAt ℝ n (fun y ↦ γ (σ (f y))) x :=
    hγn.contDiffAt.comp x ((hσ _ hx).comp x hf.contDiffAt)
  refine ⟨f ⁻¹' T, hT.preimage hf.continuous, hsT, fun x ↦ ⟪w, x - γ (σ (f x))⟫,
    fun x hx ↦ contDiffAt_const.inner ℝ (contDiffAt_id.sub (hk hx)), ?_, fun s hs v hv ↦ ?_⟩
  · filter_upwards [hσγ] with s hs
    rw [hs, sub_self, inner_zero_right]
  -- The derivative of `x ↦ γ (σ (f x))` factors through `fderiv f`, which kills `v`.
  have hfv : fderiv ℝ f (γ s) v = 0 := by rw [← inner_gradient_left, real_inner_comm, hv]
  have hγσ : HasFDerivAt (fun a ↦ γ (σ a)) (fderiv ℝ (fun a ↦ γ (σ a)) (f (γ s))) (f (γ s)) :=
    ((hγn.contDiffAt.comp _ (hσ _ hs)).differentiableAt hn0).hasFDerivAt
  have hg : HasFDerivAt (fun x ↦ ⟪w, x - γ (σ (f x))⟫) ((innerSL ℝ w).comp
      (.id ℝ E - (fderiv ℝ (fun a ↦ γ (σ a)) (f (γ s))).comp (fderiv ℝ f (γ s)))) (γ s) :=
    (innerSL ℝ w).hasFDerivAt.comp _
      ((hasFDerivAt_id _).sub (hγσ.comp _ (hf.differentiable hn0 _).hasFDerivAt))
  simp [hg.fderiv, hfv]

section FiniteDimensional

variable [FiniteDimensional ℝ E]

/-- Near a point `γ s₀` of a negative gradient trajectory which is not a critical point of a `Cⁿ`
function `f`, `2 ≤ n`, a continuous path `u` with `u s₀ ≠ 0` which is normal to the trajectory
pairs positively with the path of some potential variation localized in a given neighbourhood of
`γ s₀`. The variation is `h = ψ g`, for the function `g` of
`TauCeti.exists_contDiffAt_eventually_eq_zero_fderiv_eq_inner` with `w = u s₀`, and a bump `ψ` at
`γ s₀` so small that the trajectory only meets it at times where `g` vanishes on `γ` and
`⟪u s₀, u s⟫ > 0`. -/
private theorem exists_potentialVariation_integral_inner_pos {n : ℕ∞} (hf : ContDiff ℝ n f)
    (hn : 2 ≤ n) (hγ : IsIntegralCurve γ (fun _ x ↦ -∇ f x)) {U : Set E} {s₀ : ℝ}
    (hU : U ∈ 𝓝 (γ s₀)) (hcrit : ∇ f (γ s₀) ≠ 0) {u : ℝ → E} (huc : Continuous u)
    (hu0 : u s₀ ≠ 0) (hnormal : ∀ s, ⟪u s, ∇ f (γ s)⟫ = 0) :
    ∃ h : E → ℝ, ContDiff ℝ n h ∧ HasCompactSupport h ∧ tsupport h ⊆ U ∧ (∀ s, h (γ s) = 0) ∧
      HasCompactSupport (fun s ↦ ∇ h (γ s)) ∧ 0 < ∫ s, ⟪∇ h (γ s), u s⟫ := by
  have hn0 : (n : WithTop ℕ∞) ≠ 0 := by exact_mod_cast (zero_lt_two.trans_le hn).ne'
  obtain ⟨O, hO, hx₀, g, hgO, hg0, hgd⟩ :=
    exists_contDiffAt_eventually_eq_zero_fderiv_eq_inner hf hn0 hγ hcrit (u s₀)
  -- A bump `ψ` at `γ s₀` inside `U ∩ O`, met by `γ` only at times in a unit interval around `s₀`
  -- where `g` vanishes on `γ`.
  have hvisit := hγ.comap_nhds_le_nhds (fun t ↦ hf.differentiable hn0 _) hcrit
  obtain ⟨V, hV, hVs⟩ := mem_comap.1 (hvisit (inter_mem hg0 (Metric.ball_mem_nhds s₀ one_pos)))
  obtain ⟨ψ, hψ, hψc, hψU, -, hpos⟩ := exists_contDiff_tsupport_subset_integral_comp_mul_pos
    hγ.continuous hvisit (inter_mem (inter_mem hU (hO.mem_nhds hx₀)) hV)
    (continuous_const.inner huc) (real_inner_self_pos.2 hu0)
  have hψO {x : E} (hx : x ∈ tsupport ψ) : x ∈ O := (hψU hx).1.2
  have hψs {s : ℝ} (hs : γ s ∈ tsupport ψ) : g (γ s) = 0 ∧ s ∈ Metric.ball s₀ 1 := hVs (hψU hs).2
  have hh0 {x : E} (hx : x ∉ tsupport ψ) : x ∉ tsupport fun y ↦ ψ y * g y :=
    fun h ↦ hx (tsupport_mul_subset_left h)
  refine ⟨fun x ↦ ψ x * g x, ?_, hψc.mul_right, tsupport_mul_subset_left.trans
    fun x hx ↦ (hψU hx).1.1, fun s ↦ ?_, ?_, ?_⟩
  · simpa only [smul_eq_mul] using ContDiffOn.contDiff_smul_of_tsupport_subset
      (fun x hx ↦ (hgO x hx).contDiffWithinAt) hO
      (hψ.of_le (WithTop.coe_le_coe.2 le_top)).contDiffOn fun x hx ↦ hψO hx
  · by_cases hs : γ s ∈ tsupport ψ
    · simp [(hψs hs).1]
    · simp [image_eq_zero_of_notMem_tsupport hs]
  · -- The path of `h` vanishes outside the closed unit ball around `s₀`.
    refine HasCompactSupport.intro (isCompact_closedBall s₀ 1) fun s hs ↦ ?_
    have hs' : γ s ∉ tsupport ψ := fun h ↦ hs (Metric.ball_subset_closedBall (hψs h).2)
    simp [gradient, fderiv_of_notMem_tsupport ℝ (hh0 hs')]
  · -- The path of `h` pairs with `u` as `s ↦ ψ (γ s) ⟪u s₀, u s⟫`.
    refine hpos.trans_eq (integral_congr_ae (.of_forall fun s ↦ ?_))
    dsimp only
    rw [inner_gradient_left]
    by_cases hs : γ s ∈ tsupport ψ
    · rw [fderiv_fun_mul ((hψ.differentiable (by simp)) _)
        ((hgO _ (hψO hs)).differentiableAt hn0)]
      simp [hgd s (hψO hs) (u s) (hnormal s), (hψs hs).1]
    · rw [fderiv_of_notMem_tsupport ℝ (hh0 hs), image_eq_zero_of_notMem_tsupport hs,
        zero_apply, zero_mul]

/-! ### The cokernel is detected by potential variations -/

/-- **Paths orthogonal to the range and to the potential variations vanish.** Let `f` be `Cⁿ`
with `2 ≤ n`, and `γ` a negative gradient trajectory along which `∇f` is bounded, and let `U` be
a neighbourhood of a point `γ s₀` of the trajectory which is not a critical point of `f`. A path
`v ∈ L²(ℝ, E)` orthogonal to the range of the linearized operator `ξ ↦ ξ' + Hess f(γ) ξ` and to the
potential variations of class `Cⁿ` localized in `U` vanishes. -/
theorem eq_zero_of_mem_orthogonal_range_trajectoryOperator_of_mem_orthogonal_potentialVariations
    {n : ℕ∞} (hf : ContDiff ℝ n f) (hn : 2 ≤ n) (hγ : IsIntegralCurve γ (fun _ x ↦ -∇ f x))
    {C : ℝ} (hC : ∀ s, ‖∇ f (γ s)‖ ≤ C)
    {AL : Lp (E →L[ℝ] E) ∞ (volume.restrict ((⊤ : TopologicalSpace.Opens ℝ) : Set ℝ))}
    (hAL : AL =ᵐ[volume.restrict ((⊤ : TopologicalSpace.Opens ℝ) : Set ℝ)]
      fun s ↦ hessianOperator f (γ s))
    {U : Set E} {s₀ : ℝ} (hU : U ∈ 𝓝 (γ s₀)) (hcrit : ∇ f (γ s₀) ≠ 0)
    {v : Lp E 2 (volume.restrict ((⊤ : TopologicalSpace.Opens ℝ) : Set ℝ))}
    (hv : v ∈ (WeakDerivStep.trajectoryOperator (p := 2) AL).rangeᗮ)
    (hvar : v ∈ (potentialVariations γ n U)ᗮ) : v = 0 := by
  have hvol : volume.restrict ((⊤ : TopologicalSpace.Opens ℝ) : Set ℝ) = volume := by simp
  have hf2 : ContDiff ℝ 2 f := hf.of_le (WithTop.coe_le_coe.2 hn)
  have hA : Continuous fun s ↦ hessianOperator f (γ s) :=
    (hf2.contDiff_hessianOperator (m := 0) (by norm_num)).continuous.comp hγ.continuous
  by_contra hv0
  -- `v` is a nowhere vanishing solution of the adjoint equation `u' = Hess f(γ) u`, the Hessian
  -- being symmetric.
  obtain ⟨u, hu, hvu, hu0⟩ :=
    WeakDerivStep.exists_hasDerivAt_ne_zero_of_mem_orthogonal_range_trajectoryOperator hA
      (fun _ ↦ hf2.contDiffAt.isSelfAdjoint_hessianOperator) hAL hv hv0
  have huc : Continuous u := continuous_iff_continuousAt.2 fun s ↦ (hu s).continuousAt
  -- It is square integrable, hence normal to the trajectory.
  have hu2 : MemLp u 2 volume := hvol ▸ (Lp.memLp v).ae_eq hvu
  have hnormal := inner_gradient_comp_eq_zero_of_memLp hf2 hγ hu hu2 hC
  obtain ⟨h, hh, hhc, hhU, hhγ, hpath_supp, hpos⟩ :=
    exists_potentialVariation_integral_inner_pos hf hn hγ hU hcrit huc (hu0 s₀) hnormal
  -- The path of `h` lies in `L²(ℝ, E)`, as a potential variation localized in `U`.
  have hmem : MemLp (fun s ↦ ∇ h (γ s)) 2
      (volume.restrict ((⊤ : TopologicalSpace.Opens ℝ) : Set ℝ)) := by
    rw [hvol]
    exact ((hh.continuous_gradient (by exact_mod_cast (zero_lt_two.trans_le hn).ne')).comp
      hγ.continuous).memLp_of_hasCompactSupport hpath_supp
  have hint : ∫ s, ⟪∇ h (γ s), u s⟫ = ⟪hmem.toLp _, v⟫ := by
    simp only [L2.toLp_inner_of_ae_eq hmem hvu, hvol]
  exact hpos.ne' (hint.trans ((Submodule.mem_orthogonal _ _).1 hvar _
    (mem_potentialVariations_of_ae_eq hh hhc hhU hhγ hmem.coeFn_toLp)))

/-! ### Surjectivity of the universal linearization -/

/-- **Localized potential variations make a linearized operator with closed range of finite
codimension onto.** Let `f` be `Cⁿ` with `2 ≤ n`, `γ` a negative gradient trajectory along which
`∇f` is bounded, and `U` a neighbourhood of a point `γ s₀` of the trajectory which is not a
critical point of `f`. If the linearized operator `ξ ↦ ξ' + Hess f(γ) ξ` from `W^{1,2}(ℝ, E)` to
`L²(ℝ, E)` has closed range of finite codimension, as a Fredholm operator does, then its range and
the potential variations of class `Cⁿ` localized in `U` together span `L²(ℝ, E)`. -/
theorem range_trajectoryOperator_sup_potentialVariations_eq_top_of_isClosed_of_coFG
    {n : ℕ∞} (hf : ContDiff ℝ n f) (hn : 2 ≤ n) (hγ : IsIntegralCurve γ (fun _ x ↦ -∇ f x))
    {C : ℝ} (hC : ∀ s, ‖∇ f (γ s)‖ ≤ C)
    {AL : Lp (E →L[ℝ] E) ∞ (volume.restrict ((⊤ : TopologicalSpace.Opens ℝ) : Set ℝ))}
    (hAL : AL =ᵐ[volume.restrict ((⊤ : TopologicalSpace.Opens ℝ) : Set ℝ)]
      fun s ↦ hessianOperator f (γ s))
    {U : Set E} {s₀ : ℝ} (hU : U ∈ 𝓝 (γ s₀)) (hcrit : ∇ f (γ s₀) ≠ 0)
    (hDc : IsClosed ((WeakDerivStep.trajectoryOperator (p := 2) AL).range :
      Set (Lp E 2 (volume.restrict ((⊤ : TopologicalSpace.Opens ℝ) : Set ℝ)))))
    (hDf : (WeakDerivStep.trajectoryOperator (p := 2) AL).range.CoFG) :
    (WeakDerivStep.trajectoryOperator (p := 2) AL).range ⊔ potentialVariations γ n U = ⊤ :=
  Submodule.sup_eq_top_of_isClosed_of_coFG hDc hDf fun _ ↦
    eq_zero_of_mem_orthogonal_range_trajectoryOperator_of_mem_orthogonal_potentialVariations
      hf hn hγ hC hAL hU hcrit

/-- **Localized potential variations make the linearized operator onto.** Let `f` be a `Cⁿ`
function, `2 ≤ n`, on a finite-dimensional real inner product space and `γ` a negative gradient
trajectory from a nondegenerate critical point `p` at `-∞` to a nondegenerate critical point `q` at
`+∞`. If `U` is a neighbourhood of a point `γ s₀` of the trajectory which is not a critical point
of `f`, the range of the linearized operator `ξ ↦ ξ' + Hess f(γ) ξ` from `W^{1,2}(ℝ, E)` to
`L²(ℝ, E)` and the potential variations of class `Cⁿ` localized in `U` together span `L²(ℝ, E)`.
In other words, the universal linearization `(ξ, h) ↦ D_γ ξ + ∇h(γ)` of the trajectory equation,
in the trajectory and the potential, is onto, already for variations `h` vanishing on `γ`. -/
theorem range_trajectoryOperator_sup_potentialVariations_eq_top
    {n : ℕ∞} (hf : ContDiff ℝ n f) (hn : 2 ≤ n) (hγ : IsIntegralCurve γ (fun _ x ↦ -∇ f x))
    {p q : E} (hp : IsNondegenerateCriticalPoint f p) (hq : IsNondegenerateCriticalPoint f q)
    (hbot : Tendsto γ atBot (𝓝 p)) (htop : Tendsto γ atTop (𝓝 q))
    {AL : Lp (E →L[ℝ] E) ∞ (volume.restrict ((⊤ : TopologicalSpace.Opens ℝ) : Set ℝ))}
    (hAL : AL =ᵐ[volume.restrict ((⊤ : TopologicalSpace.Opens ℝ) : Set ℝ)]
      fun s ↦ hessianOperator f (γ s))
    {U : Set E} {s₀ : ℝ} (hU : U ∈ 𝓝 (γ s₀)) (hcrit : ∇ f (γ s₀) ≠ 0) :
    (WeakDerivStep.trajectoryOperator (p := 2) AL).range ⊔ potentialVariations γ n U = ⊤ := by
  have hf2 : ContDiff ℝ 2 f := hf.of_le (WithTop.coe_le_coe.2 hn)
  have hD := hγ.isFredholm_trajectoryOperator_hessianOperator hf2 hp hq hbot htop hAL
  -- Along a trajectory with limits at both ends, the gradient is bounded.
  have hg := hf2.continuous_gradient (by norm_num)
  obtain ⟨C, hC⟩ := exists_forall_norm_le_of_tendsto (hg.comp hγ.continuous)
    ((hg.tendsto p).comp hbot) ((hg.tendsto q).comp htop)
  exact range_trajectoryOperator_sup_potentialVariations_eq_top_of_isClosed_of_coFG hf hn hγ hC
    hAL hU hcrit hD.isClosed_range hD.finite_coker

/-- **Finitely many localized potential variations make the linearized operator onto.** Under the
hypotheses of `TauCeti.range_trajectoryOperator_sup_potentialVariations_eq_top`, finitely many
potential variations localized in `U` already span `L²(ℝ, E)` together with the range of the
linearized operator `ξ ↦ ξ' + Hess f(γ) ξ`: its cokernel is finite-dimensional. -/
theorem exists_finset_subset_potentialVariations_range_trajectoryOperator_sup_span_eq_top
    {n : ℕ∞} (hf : ContDiff ℝ n f) (hn : 2 ≤ n) (hγ : IsIntegralCurve γ (fun _ x ↦ -∇ f x))
    {p q : E} (hp : IsNondegenerateCriticalPoint f p) (hq : IsNondegenerateCriticalPoint f q)
    (hbot : Tendsto γ atBot (𝓝 p)) (htop : Tendsto γ atTop (𝓝 q))
    {AL : Lp (E →L[ℝ] E) ∞ (volume.restrict ((⊤ : TopologicalSpace.Opens ℝ) : Set ℝ))}
    (hAL : AL =ᵐ[volume.restrict ((⊤ : TopologicalSpace.Opens ℝ) : Set ℝ)]
      fun s ↦ hessianOperator f (γ s))
    {U : Set E} {s₀ : ℝ} (hU : U ∈ 𝓝 (γ s₀)) (hcrit : ∇ f (γ s₀) ≠ 0) :
    ∃ t : Finset (Lp E 2 (volume.restrict ((⊤ : TopologicalSpace.Opens ℝ) : Set ℝ))),
      (t : Set (Lp E 2 (volume.restrict ((⊤ : TopologicalSpace.Opens ℝ) : Set ℝ)))) ⊆
        potentialVariations γ n U ∧
        (WeakDerivStep.trajectoryOperator (p := 2) AL).range ⊔ Submodule.span ℝ t = ⊤ := by
  have := (hγ.isFredholm_trajectoryOperator_hessianOperator (hf.of_le (WithTop.coe_le_coe.2 hn))
    hp hq hbot htop hAL).finite_coker
  refine Submodule.exists_finset_subset_sup_span_eq_top ?_
  rw [Submodule.span_eq]
  exact range_trajectoryOperator_sup_potentialVariations_eq_top hf hn hγ hp hq hbot htop hAL hU
    hcrit

end FiniteDimensional

end TauCeti
