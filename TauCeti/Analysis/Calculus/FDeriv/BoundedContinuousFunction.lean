/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Comp
public import Mathlib.Analysis.Calculus.MeanValue
public import TauCeti.Analysis.Calculus.ContDiff.UniformOn
public import TauCeti.Topology.ContinuousMap.Bounded.Normed

/-!
# Differentiability of superposition operators on bounded continuous functions

Let `G : X → Y` be a map between normed spaces over `ℝ` or `ℂ`. Postcomposition with `G`, when `G`
is Lipschitz, is the *superposition* (or *Nemytskii*) operator `f ↦ G ∘ f` on bounded continuous
functions, `BoundedContinuousFunction.comp G hG : (α →ᵇ X) → (α →ᵇ Y)`, for the sup norm. This
file shows that it is continuously differentiable, and indeed `C^n`, wherever `G` is, in the
following uniform sense. The results are also stated for an operator `Θ` that is only *given* near
`f₀` by `Θ f t = G (f t)`, which needs no global hypothesis on `G`.

Suppose that `G` has derivative `G' x` at every point `x` of a set `s`, that
`G' : X → (X →L[𝕜] Y)` is uniformly continuous on `s`, and that the values of `f₀` stay a fixed
distance `δ > 0` inside `s`. Nothing is assumed about `G'` off `s`. Then the superposition
operator is differentiable at `f₀`, and its derivative is pointwise application of the family of
derivatives, `h ↦ (t ↦ G' (f₀ t) (h t))`, that is `applyCLM Φ` for the bounded continuous family
`Φ t = G' (f₀ t)`; the Lipschitz constant of `G` bounds `G'` on `s`, so this family is bounded.
The derivative is moreover strict, and the operator is `C¹` near `f₀`. The same holds at order
`n`: if `G` is uniformly `C^n` on `s` (`TauCeti.UniformContDiffOn`), a superposition operator is
`C^n` near `f₀`; its derivative at `f` is `applyCLM` of the family `t ↦ G' (f t)`.

Uniform continuity of `G'` is what makes the remainder estimate hold with one constant at all
the points `f₀ t` at once; nothing makes the range of `f₀` compact, for instance for curves on
`[0, ∞)`. The distance `δ` allows `G` to be differentiable only on part of its domain, as when a
smooth map is cut off outside a ball by a merely Lipschitz retraction.

This is the differentiability input to the Lyapunov--Perron construction of stable manifolds.
Its integral operator acts on bounded continuous curves through the superposition by the
nonlinearity of the differential equation, and the implicit function theorem turns a `C^n`
operator into `C^n` dependence of its fixed points on parameters.

## Main declarations

* `BoundedContinuousFunction.exists_eq_comp`: along a function with values in `s`, the
  derivatives `t ↦ G' (f t)` form a bounded continuous family.
* `BoundedContinuousFunction.hasFDerivAt_of_forall_apply_eq`: an operator given near `f₀` by
  `Θ f t = G (f t)` is differentiable at `f₀` (its continuity is
  `BoundedContinuousFunction.continuousAt_of_forall_apply_eq`).
* `BoundedContinuousFunction.hasFDerivAt_comp`: the superposition operator is differentiable at
  `f₀`, with derivative `h ↦ (t ↦ G' (f₀ t) (h t))`.
* `BoundedContinuousFunction.hasStrictFDerivAt_comp`: the derivative is strict.
* `BoundedContinuousFunction.contDiffAt_comp`: the superposition operator is `C¹` near `f₀`.
* `BoundedContinuousFunction.contDiff_comp`: when `G` is differentiable everywhere with a
  derivative uniformly continuous on bounded sets, the superposition operator is `C¹`.
* `BoundedContinuousFunction.contDiffAt_of_forall_apply_eq`: for `n : ℕ`, an operator that is
  given near `f₀` by `f ↦ G ∘ f` with `G` uniformly `C^n` on `s` (`TauCeti.UniformContDiffOn`) is
  `C^n` at `f₀`.
  `BoundedContinuousFunction.contDiffAt_comp_of_uniformContDiffOn` is the case of
  `BoundedContinuousFunction.comp`.

## References

* J. Appell and P. P. Zabrejko, *Nonlinear Superposition Operators*, Cambridge Tracts in
  Mathematics **95**, Cambridge University Press, 1990.
-/

public section

open Filter Metric Set Topology
open scoped NNReal BoundedContinuousFunction

namespace BoundedContinuousFunction

variable {α 𝕜 X Y : Type*} [TopologicalSpace α] [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup X] [NormedSpace 𝕜 X] [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
  {G : X → Y} {C : ℝ≥0} {G' : X → X →L[𝕜] Y} {s : Set X} {f₀ : α →ᵇ X} {δ : ℝ}
  {Φ : α →ᵇ (X →L[𝕜] Y)}

open scoped Classical in
/-- The family of derivatives `t ↦ G' (f t)` along a function `f` with values in `s`, as a bounded
continuous function when `G'` is continuous on `s` and bounded by `C` there, and `0` otherwise. -/
private noncomputable def derivFamily {C : ℝ} (hG' : ContinuousOn G' s) (hC : ∀ x ∈ s, ‖G' x‖ ≤ C)
    (f : α →ᵇ X) : α →ᵇ (X →L[𝕜] Y) :=
  if hf : ∀ t, f t ∈ s then
    ofNormedAddCommGroup (fun t ↦ G' (f t)) (hG'.comp_continuous f.continuous hf) C
      fun t ↦ hC _ (hf t)
  else 0

private theorem derivFamily_apply {C : ℝ} (hG' : ContinuousOn G' s) (hC : ∀ x ∈ s, ‖G' x‖ ≤ C)
    {f : α →ᵇ X} (hf : ∀ t, f t ∈ s) (t : α) : derivFamily hG' hC f t = G' (f t) := by
  simp [derivFamily, hf]

/-- Along a function `f` with values in `s`, the derivatives `t ↦ G' (f t)` form a bounded
continuous family: they are bounded by the Lipschitz constant of `G`. This supplies the family `Φ`
in `BoundedContinuousFunction.hasFDerivAt_comp` and
`BoundedContinuousFunction.hasStrictFDerivAt_comp`. -/
theorem exists_eq_comp (hG : LipschitzWith C G) (hGs : ∀ x ∈ s, HasFDerivAt G (G' x) x)
    (hG' : ContinuousOn G' s) {f : α →ᵇ X} (hf : ∀ t, f t ∈ s) :
    ∃ Φ : α →ᵇ (X →L[𝕜] Y), ∀ t, Φ t = G' (f t) :=
  ⟨derivFamily hG' (fun x hx ↦ (hGs x hx).le_of_lipschitz hG) f,
    derivFamily_apply hG' (fun x hx ↦ (hGs x hx).le_of_lipschitz hG) hf⟩

variable [IsRCLikeNormedField 𝕜]

variable {Θ : (α →ᵇ X) → α →ᵇ Y}

/-- **A locally defined superposition operator is differentiable.** The statement of
`BoundedContinuousFunction.hasFDerivAt_comp` for an operator `Θ` that is merely given, on the ball
of radius `δ` about `f₀`, by `Θ f t = G (f t)`. No global bound on `G` is needed, because `Θ` takes
values in bounded continuous functions by assumption. -/
theorem hasFDerivAt_of_forall_apply_eq (hGs : ∀ x ∈ s, HasFDerivAt G (G' x) x)
    (hG' : UniformContinuousOn G' s) (hδ : 0 < δ) (hf₀ : ∀ t, ball (f₀ t) δ ⊆ s)
    (hΘ : ∀ f ∈ ball f₀ δ, ∀ t, Θ f t = G (f t)) (hΦ : ∀ t, Φ t = G' (f₀ t)) :
    HasFDerivAt Θ (applyCLM Φ) f₀ := by
  let _ : RCLike 𝕜 := IsRCLikeNormedField.rclike 𝕜
  let _ : NormedSpace ℝ X := .restrictScalars ℝ 𝕜 X
  rw [hasFDerivAt_iff_isLittleO_nhds_zero, Asymptotics.isLittleO_iff]
  intro c hc
  -- A modulus of continuity `η` for `G'` at the tolerance `c` controls the remainder of `G` at
  -- every point `f₀ t` simultaneously, on the ball of radius `min δ η`.
  obtain ⟨η, hη, hG'η⟩ := Metric.uniformContinuousOn_iff_le.1 hG' c hc
  have hρ : 0 < min δ η := lt_min hδ hη
  filter_upwards [ball_mem_nhds (0 : α →ᵇ X) hρ] with h hh
  rw [mem_ball_zero_iff] at hh
  have hmemf : f₀ + h ∈ ball f₀ δ := by
    rw [mem_ball, dist_eq_norm, add_sub_cancel_left]
    exact hh.trans_le (min_le_left _ _)
  refine (norm_le (by positivity)).2 fun t ↦ ?_
  have hball : ball (f₀ t) (min δ η) ⊆ s := (ball_subset_ball (min_le_left _ _)).trans (hf₀ t)
  have hmem : f₀ t + h t ∈ ball (f₀ t) (min δ η) := by
    rw [mem_ball, dist_eq_norm, add_sub_cancel_left]
    exact (norm_coe_le_norm h t).trans_lt hh
  have key := (convex_ball (f₀ t) (min δ η)).norm_image_sub_le_of_norm_hasFDerivWithin_le'
    (fun x hx ↦ (hGs x (hball hx)).hasFDerivWithinAt)
    (fun x hx ↦ by
      rw [← dist_eq_norm]
      exact hG'η x (hball hx) (f₀ t) (hf₀ t (mem_ball_self hδ))
        ((mem_ball.1 hx).le.trans (min_le_right _ _)))
    (mem_ball_self hρ) hmem
  rw [add_sub_cancel_left] at key
  simp only [coe_sub, Pi.sub_apply, hΘ _ hmemf, hΘ f₀ (mem_ball_self hδ), applyCLM_apply, hΦ,
    coe_add, Pi.add_apply]
  simpa using key.trans (mul_le_mul_of_nonneg_left (norm_coe_le_norm h t) hc.le)


/-- **The derivative of a superposition operator.** Let `G` be Lipschitz, with derivative `G' x`
at every point `x` of `s`, where `G'` is uniformly continuous on `s`. If the values of `f₀` stay a
distance `δ > 0` inside `s`, then `f ↦ G ∘ f` is differentiable at `f₀` for the sup norm, with
derivative `h ↦ (t ↦ G' (f₀ t) (h t))`, that is `applyCLM Φ` for the bounded continuous family
`Φ t = G' (f₀ t)`. -/
theorem hasFDerivAt_comp (hG : LipschitzWith C G) (hGs : ∀ x ∈ s, HasFDerivAt G (G' x) x)
    (hG' : UniformContinuousOn G' s) (hδ : 0 < δ) (hf₀ : ∀ t, ball (f₀ t) δ ⊆ s)
    (hΦ : ∀ t, Φ t = G' (f₀ t)) : HasFDerivAt (comp G hG) (applyCLM Φ) f₀ :=
  hasFDerivAt_of_forall_apply_eq hGs hG' hδ hf₀ (fun _ _ _ ↦ rfl) hΦ

/-- The superposition operator is differentiable at every function whose values stay a positive
distance inside `s`. -/
private theorem hasFDerivAt_fderiv_comp (hG : LipschitzWith C G)
    (hGs : ∀ x ∈ s, HasFDerivAt G (G' x) x) (hG' : UniformContinuousOn G' s) (hδ : 0 < δ)
    (hf₀ : ∀ t, ball (f₀ t) δ ⊆ s) : HasFDerivAt (comp G hG) (fderiv 𝕜 (comp G hG) f₀) f₀ :=
  have ⟨_, hΦ⟩ := exists_eq_comp hG hGs hG'.continuousOn fun t ↦ hf₀ t (mem_ball_self hδ)
  (hasFDerivAt_comp hG hGs hG' hδ hf₀ hΦ).differentiableAt.hasFDerivAt

/-- The derivative of the superposition operator is continuous at every function whose values
stay a positive distance inside a set where `G'` is uniformly continuous. -/
private theorem continuousAt_fderiv_comp (hG : LipschitzWith C G)
    (hGs : ∀ x ∈ s, HasFDerivAt G (G' x) x) (hG' : UniformContinuousOn G' s) (hδ : 0 < δ)
    (hf₀ : ∀ t, ball (f₀ t) δ ⊆ s) : ContinuousAt (fderiv 𝕜 (comp G hG)) f₀ := by
  have hC : ∀ x ∈ s, ‖G' x‖ ≤ C := fun x hx ↦ (hGs x hx).le_of_lipschitz hG
  -- The derivative is `applyCLM` of the family of derivatives, which is continuous in `f`.
  have hfam : ContinuousAt (derivFamily hG'.continuousOn hC) f₀ :=
    continuousAt_of_forall_apply_eq hG' hδ hf₀ fun f hf t ↦ derivFamily_apply _ _
      (apply_mem_of_mem_ball hf₀ hf) t
  refine (applyCLM.continuous.continuousAt.comp hfam).congr ?_
  filter_upwards [ball_mem_nhds f₀ (half_pos hδ)] with f hf
  have hfs := ball_half_subset_of_mem_ball hf₀ hf
  exact (hasFDerivAt_comp hG hGs hG' (half_pos hδ) hfs fun t ↦ derivFamily_apply _ _
    (fun t ↦ hfs t (mem_ball_self (half_pos hδ))) t).fderiv.symm

/-- **Strict differentiability of a superposition operator.** Under the hypotheses of
`BoundedContinuousFunction.hasFDerivAt_comp`, the derivative
`h ↦ (t ↦ G' (f₀ t) (h t))` of `f ↦ G ∘ f` at `f₀` is strict. -/
theorem hasStrictFDerivAt_comp (hG : LipschitzWith C G) (hGs : ∀ x ∈ s, HasFDerivAt G (G' x) x)
    (hG' : UniformContinuousOn G' s) (hδ : 0 < δ) (hf₀ : ∀ t, ball (f₀ t) δ ⊆ s)
    (hΦ : ∀ t, Φ t = G' (f₀ t)) : HasStrictFDerivAt (comp G hG) (applyCLM Φ) f₀ := by
  let _ : RCLike 𝕜 := IsRCLikeNormedField.rclike 𝕜
  rw [← (hasFDerivAt_comp hG hGs hG' hδ hf₀ hΦ).fderiv]
  exact hasStrictFDerivAt_of_hasFDerivAt_of_continuousAt
    (mem_of_superset (ball_mem_nhds f₀ (half_pos hδ)) fun _ hf ↦
      hasFDerivAt_fderiv_comp hG hGs hG' (half_pos hδ) (ball_half_subset_of_mem_ball hf₀ hf))
    (continuousAt_fderiv_comp hG hGs hG' hδ hf₀)

end BoundedContinuousFunction

universe u v

namespace BoundedContinuousFunction

section Local

variable {α 𝕜 : Type*} {X : Type u} {Y : Type v} [TopologicalSpace α] [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup X] [NormedSpace 𝕜 X] [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
  [IsRCLikeNormedField 𝕜] {G : X → Y} {C : ℝ≥0} {s : Set X} {f₀ : α →ᵇ X} {δ : ℝ}
  {Θ : (α →ᵇ X) → α →ᵇ Y}

-- The induction step only needs the theorem for the derivative target.
private theorem contDiffAt_of_uniformContDiffOn_step {n : ℕ}
    (hG : TauCeti.UniformContDiffOn 𝕜 (n + 1) G s)
    (hδ : 0 < δ) (hf₀ : ∀ t, ball (f₀ t) δ ⊆ s)
    (hΘ : ∀ f ∈ ball f₀ δ, ∀ t, Θ f t = G (f t))
    (hstep : ∀ (G' : X → X →L[𝕜] Y), TauCeti.UniformContDiffOn 𝕜 n G' s →
      ∀ {Θ' : (α →ᵇ X) → α →ᵇ (X →L[𝕜] Y)} {δ' : ℝ}, 0 < δ' →
        (∀ t, ball (f₀ t) δ' ⊆ s) →
        (∀ f ∈ ball f₀ δ', ∀ t, Θ' f t = G' (f t)) → ContDiffAt 𝕜 n Θ' f₀) :
    ContDiffAt 𝕜 (n + 1) Θ f₀ := by
  obtain ⟨-, G', hGs, ⟨C, hC⟩, hG'n⟩ := TauCeti.uniformContDiffOn_succ_iff.1 hG
  have hG'c : ContinuousOn G' s := hG'n.continuousOn
  -- The family of derivatives along a function with values in `s`.
  have hΘ' : ∀ f ∈ ball f₀ (δ / 2), ∀ t, derivFamily hG'c hC f t = G' (f t) := fun f hf t ↦
    derivFamily_apply hG'c hC (fun t ↦ ball_half_subset_of_mem_ball hf₀ hf t
      (mem_ball_self (half_pos hδ))) t
  have hΘ'C : ContDiffAt 𝕜 n (derivFamily hG'c hC) f₀ :=
    hstep G' hG'n (half_pos hδ)
      (fun t ↦ (ball_subset_ball (by linarith)).trans (hf₀ t)) hΘ'
  rw [contDiffAt_succ_iff_hasFDerivAt]
  have hA : ContDiff 𝕜 n (applyCLM : (α →ᵇ (X →L[𝕜] Y)) →L[𝕜] (α →ᵇ X) →L[𝕜] α →ᵇ Y) :=
    ContinuousLinearMap.contDiff _
  refine ⟨fun f ↦ applyCLM (derivFamily hG'c hC f),
    ⟨ball f₀ (δ / 2), ball_mem_nhds f₀ (half_pos hδ), fun f hf ↦ ?_⟩,
    hA.comp_contDiffAt f₀ hΘ'C⟩
  exact hasFDerivAt_of_forall_apply_eq hGs hG'n.uniformContinuousOn (half_pos hδ)
    (ball_half_subset_of_mem_ball hf₀ hf)
    (fun g hg t ↦ hΘ g (Metric.ball_half_subset _ hf hg) t)
    (hΘ' f hf)

private theorem contDiffAt_of_uniformContDiffOn_aux {Z : Type (max u v)}
    [NormedAddCommGroup Z] [NormedSpace 𝕜 Z] {G : X → Z}
    {Θ : (α →ᵇ X) → α →ᵇ Z} {n : ℕ} (hG : TauCeti.UniformContDiffOn 𝕜 n G s)
    (hδ : 0 < δ) (hf₀ : ∀ t, ball (f₀ t) δ ⊆ s)
    (hΘ : ∀ f ∈ ball f₀ δ, ∀ t, Θ f t = G (f t)) : ContDiffAt 𝕜 n Θ f₀ := by
  induction n generalizing Z G Θ f₀ δ with
  | zero =>
    refine contDiffAt_zero.2 ⟨ball f₀ (δ / 2), ball_mem_nhds f₀ (half_pos hδ), fun f hf ↦ ?_⟩
    exact (continuousAt_of_forall_apply_eq (TauCeti.uniformContDiffOn_zero_iff.1 hG)
      (half_pos hδ) (ball_half_subset_of_mem_ball hf₀ hf)
      fun g hg t ↦ hΘ g (Metric.ball_half_subset _ hf hg) t).continuousWithinAt
  | succ n ih =>
    exact contDiffAt_of_uniformContDiffOn_step hG hδ hf₀ hΘ
      (fun G' hG'n {_} {_} hδ' hf₀' hΘ' ↦ ih hG'n hδ' hf₀' hΘ')

/-- **Superposition operators are `C^n`.** Let `G` be uniformly `C^n` on `s`. If the values of `f₀`
stay a distance `δ > 0` inside `s` and `Θ` agrees with the superposition `f ↦ G ∘ f` on the ball
of radius `δ` about `f₀`, then `Θ` is `C^n` at `f₀` for the sup norm. -/
theorem contDiffAt_of_forall_apply_eq {n : ℕ} (hG : TauCeti.UniformContDiffOn 𝕜 n G s)
    (hδ : 0 < δ) (hf₀ : ∀ t, ball (f₀ t) δ ⊆ s) (hΘ : ∀ f ∈ ball f₀ δ, ∀ t, Θ f t = G (f t)) :
    ContDiffAt 𝕜 n Θ f₀ := by
  cases n with
  | zero =>
    refine contDiffAt_zero.2 ⟨ball f₀ (δ / 2), ball_mem_nhds f₀ (half_pos hδ), fun f hf ↦ ?_⟩
    exact (continuousAt_of_forall_apply_eq (TauCeti.uniformContDiffOn_zero_iff.1 hG)
      (half_pos hδ) (ball_half_subset_of_mem_ball hf₀ hf)
      fun g hg t ↦ hΘ g (Metric.ball_half_subset _ hf hg) t).continuousWithinAt
  | succ n =>
    exact contDiffAt_of_uniformContDiffOn_step hG hδ hf₀ hΘ
      (fun G' hG'n {_} {_} hδ' hf₀' hΘ' ↦
        contDiffAt_of_uniformContDiffOn_aux hG'n hδ' hf₀' hΘ')

/-- **A superposition operator is `C^n`.** Let `G` be Lipschitz and uniformly `C^n` on `s`. If the
values of `f₀` stay a distance `δ > 0` inside `s`, then `f ↦ G ∘ f` is `C^n` at `f₀`. -/
theorem contDiffAt_comp_of_uniformContDiffOn (hG : LipschitzWith C G) {n : ℕ}
    (hGn : TauCeti.UniformContDiffOn 𝕜 n G s) (hδ : 0 < δ) (hf₀ : ∀ t, ball (f₀ t) δ ⊆ s) :
    ContDiffAt 𝕜 n (comp G hG) f₀ :=
  contDiffAt_of_forall_apply_eq hGn hδ hf₀ fun _ _ _ ↦ rfl

variable {G' : X → X →L[𝕜] Y}

/-- **A superposition operator is `C¹`.** Let `G` be Lipschitz, with derivative `G' x` at every
point `x` of `s`, where `G'` is uniformly continuous on `s`. If the values of `f₀` stay a distance
`δ > 0` inside `s`, then the map `f ↦ G ∘ f` is continuously differentiable at `f₀`. -/
theorem contDiffAt_comp (hG : LipschitzWith C G) (hGs : ∀ x ∈ s, HasFDerivAt G (G' x) x)
    (hG' : UniformContinuousOn G' s) (hδ : 0 < δ) (hf₀ : ∀ t, ball (f₀ t) δ ⊆ s) :
    ContDiffAt 𝕜 1 (comp G hG) f₀ := by
  exact contDiffAt_comp_of_uniformContDiffOn hG
    (TauCeti.uniformContDiffOn_succ_iff.2
      ⟨hG.uniformContinuous.uniformContinuousOn, G', hGs,
        ⟨C, fun x hx ↦ (hGs x hx).le_of_lipschitz hG⟩,
        TauCeti.uniformContDiffOn_zero_iff.2 hG'⟩) hδ hf₀

/-- **A superposition operator is `C¹`, global form.** If `G` is Lipschitz and differentiable
everywhere, with a derivative `G'` that is uniformly continuous on every ball about `0`, then
`f ↦ G ∘ f` is continuously differentiable on the bounded continuous functions. Since each
bounded continuous `f₀` takes values in a ball, uniform continuity of `G'` on bounded sets
suffices; it holds for instance when `X` is finite-dimensional and `G'` is continuous. -/
theorem contDiff_comp (hG : LipschitzWith C G) (hGs : ∀ x, HasFDerivAt G (G' x) x)
    (hG' : ∀ r, UniformContinuousOn G' (ball 0 r)) :
    ContDiff 𝕜 1 (comp G hG : (α →ᵇ X) → α →ᵇ Y) :=
  contDiff_iff_contDiffAt.2 fun f₀ ↦
    contDiffAt_comp hG (fun x _ ↦ hGs x) (hG' (‖f₀‖ + 1)) one_pos fun t ↦
      ball_subset_ball' <| by rw [dist_zero_right]; linarith [norm_coe_le_norm f₀ t]

end Local

end BoundedContinuousFunction
