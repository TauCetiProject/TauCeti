/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Comp
public import Mathlib.Analysis.Calculus.MeanValue
public import TauCeti.Analysis.Calculus.ContDiff.UniformOn
import Mathlib.Analysis.Calculus.ContDiff.Operations
import TauCeti.Analysis.Calculus.MeanValue
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
* `BoundedContinuousFunction.exists_contDiffAt_forall_apply_eq`: for `G` of class `C^n`, a
  superposition operator near a function whose values stay inside a compact set is `C^n` there.
* `BoundedContinuousFunction.exists_contDiff_apply_eq`: for `G` smooth on a product of proper
  spaces and `ρ` continuous with values in a ball, `c ↦ (t ↦ G (c, ρ t))` is a smooth family of
  bounded continuous functions.

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
/-- The superposition `t ↦ H (f t)` along a function `f` with values in `s`, as a bounded
continuous function when `H` is continuous on `s` and bounded by `C` there, and `0` otherwise. It
is used for the family of derivatives `t ↦ G' (f t)`. -/
private noncomputable def derivFamily {Z : Type*} [NormedAddCommGroup Z] {H : X → Z} {C : ℝ}
    (hH : ContinuousOn H s) (hC : ∀ x ∈ s, ‖H x‖ ≤ C) (f : α →ᵇ X) : α →ᵇ Z :=
  if hf : ∀ t, f t ∈ s then
    ofNormedAddCommGroup (fun t ↦ H (f t)) (hH.comp_continuous f.continuous hf) C
      fun t ↦ hC _ (hf t)
  else 0

private theorem derivFamily_apply {Z : Type*} [NormedAddCommGroup Z] {H : X → Z} {C : ℝ}
    (hH : ContinuousOn H s) (hC : ∀ x ∈ s, ‖H x‖ ≤ C) {f : α →ᵇ X} (hf : ∀ t, f t ∈ s) (t : α) :
    derivFamily hH hC f t = H (f t) := by
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
  rw [hasFDerivAt_iff_isLittleO_nhds_zero, Asymptotics.isLittleO_iff]
  intro c hc
  -- A modulus of continuity `η` for `G'` at the tolerance `c` controls the remainder of `G` at
  -- every point `f₀ t` simultaneously, on the ball of radius `min δ η`.
  obtain ⟨η, hη, hG'η⟩ := hG'.exists_pos_norm_image_sub_sub_le_of_hasFDerivAt hGs hc
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
  have key := hG'η (f₀ t) (min δ η) (min_le_right _ _) hball _ hmem _ (mem_ball_self hρ)
  rw [add_sub_cancel_left] at key
  simp only [FunLike.coe_sub, Pi.sub_apply, hΘ _ hmemf, hΘ f₀ (mem_ball_self hδ), applyCLM_apply,
    hΦ, FunLike.coe_add, Pi.add_apply]
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
  exact contDiffAt_comp_of_uniformContDiffOn hG (hG.uniformContDiffOn_one hGs hG') hδ hf₀

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

namespace BoundedContinuousFunction

section Family

open scoped ContDiff

variable {α 𝕜 : Type*} [TopologicalSpace α] [NontriviallyNormedField 𝕜] [IsRCLikeNormedField 𝕜]

/-- **Superposition by a `C^n` map near a function with values in a compact set.** If `G` is `C^n`
and the values of `f₀` stay a distance `δ > 0` inside a compact set `K`, then an operator on the
bounded continuous functions that is the superposition `f ↦ G ∘ f` on the ball of radius `δ` about
`f₀` is `C^n` at `f₀`. -/
theorem exists_contDiffAt_forall_apply_eq {X Y : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X]
    [NormedAddCommGroup Y] [NormedSpace 𝕜 Y] {G : X → Y} {n : ℕ} (hG : ContDiff 𝕜 n G)
    {K : Set X} (hK : IsCompact K) {f₀ : α →ᵇ X} {δ : ℝ} (hδ : 0 < δ)
    (hf₀ : ∀ t, ball (f₀ t) δ ⊆ K) :
    ∃ Θ : (α →ᵇ X) → α →ᵇ Y, ContDiffAt 𝕜 n Θ f₀ ∧ ∀ f ∈ ball f₀ δ, ∀ t, Θ f t = G (f t) := by
  obtain ⟨D, hD⟩ := hK.exists_bound_of_continuousOn hG.continuous.continuousOn
  have hΘ : ∀ f ∈ ball f₀ δ, ∀ t, derivFamily hG.continuous.continuousOn hD f t = G (f t) :=
    fun f hf ↦ derivFamily_apply _ _ fun t ↦
      hf₀ t ((BoundedContinuousFunction.dist_coe_le_dist t).trans_lt (mem_ball.1 hf))
  exact ⟨_, contDiffAt_of_forall_apply_eq
    (ContDiffOn.uniformContDiffOn isOpen_univ (subset_univ _) hK hG.contDiffOn) hδ hf₀ hΘ, hΘ⟩

variable {X Y Z : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X] [ProperSpace X]
  [NormedAddCommGroup Y] [NormedSpace 𝕜 Y] [ProperSpace Y] [NormedAddCommGroup Z]
  [NormedSpace 𝕜 Z]

/-- **Smooth families of bounded continuous functions.** Let `G : X × Y → Z` be smooth, for proper
spaces `X` and `Y`, and let `ρ : α → Y` be continuous with values in the closed ball of radius `R`.
Then `c ↦ (t ↦ G (c, ρ t))` is a smooth family of bounded continuous functions for the sup norm. -/
theorem exists_contDiff_apply_eq {G : X × Y → Z} (hG : ContDiff 𝕜 ∞ G) {ρ : α → Y}
    (hρ : Continuous ρ) {R : ℝ} (hρR : ∀ t, ‖ρ t‖ ≤ R) :
    ∃ Ψ : X → α →ᵇ Z, ContDiff 𝕜 ∞ Ψ ∧ ∀ c t, Ψ c t = G (c, ρ t) := by
  -- Each member of the family is bounded by the bound of `G` on `{c} × closedBall 0 R`.
  have hb (c : X) : ∃ C, ∀ t, ‖G (c, ρ t)‖ ≤ C := by
    obtain ⟨C, hC⟩ := (isCompact_closedBall (0 : Y) R).exists_bound_of_continuousOn
      (hG.continuous.comp (continuous_const.prodMk continuous_id)).continuousOn
    exact ⟨C, fun t ↦ hC _ (mem_closedBall_zero_iff.2 (hρR t))⟩
  choose C hC using hb
  refine ⟨fun c ↦ .ofNormedAddCommGroup _ (hG.continuous.comp (continuous_const.prodMk hρ)) (C c)
    (hC c), ?_, fun _ _ ↦ rfl⟩
  -- Near each `c₀` the family is a superposition operator applied to the affine family
  -- `c ↦ (t ↦ (c, ρ t))`.
  refine contDiff_infty.2 fun n ↦ contDiff_iff_contDiffAt.2 fun c₀ ↦ ?_
  -- The superposition by `G` near `t ↦ (c₀, ρ t)`, whose values stay inside a compact set.
  set f₀ : α →ᵇ X × Y := .ofNormedAddCommGroup (fun t ↦ (c₀, ρ t))
    (continuous_const.prodMk hρ) (max ‖c₀‖ R) fun t ↦ by
      rw [Prod.norm_def]
      exact max_le_max le_rfl (hρR t)
  have hf₀ (t : α) : ball (f₀ t) (1 / 2) ⊆ closedBall c₀ 1 ×ˢ closedBall 0 (R + 1) := fun p hp ↦ by
    rw [mem_ball, Prod.dist_eq, max_lt_iff] at hp
    refine ⟨mem_closedBall.2 (hp.1.le.trans (by norm_num)), mem_closedBall_zero_iff.2 ?_⟩
    have h := norm_le_norm_add_norm_sub' p.2 (ρ t)
    rw [← dist_eq_norm] at h
    simp only [f₀, BoundedContinuousFunction.coe_ofNormedAddCommGroup] at hp
    linarith [hp.2, hρR t]
  obtain ⟨Θ, hΘc, hΘ⟩ := exists_contDiffAt_forall_apply_eq (hG.of_le (by exact_mod_cast le_top))
    ((isCompact_closedBall _ _).prod (isCompact_closedBall _ _)) (by norm_num) hf₀
  -- The affine family `c ↦ (t ↦ (c, ρ t))`.
  set L : X →L[𝕜] α →ᵇ X × Y := LinearMap.mkContinuous
    { toFun := fun c ↦ BoundedContinuousFunction.const α ((c, 0) : X × Y)
      map_add' := fun _ _ ↦ by ext <;> simp
      map_smul' := fun _ _ ↦ by ext <;> simp } 1 fun c ↦
        (norm_const_le _).trans (by simp [Prod.norm_def])
  set ι : X → α →ᵇ X × Y := fun c ↦ f₀ + L (c - c₀)
  have hι : ContDiff 𝕜 ∞ ι := contDiff_const.add (L.contDiff.comp (contDiff_id.sub contDiff_const))
  have hι₀ : ι c₀ = f₀ := by simp [ι]
  refine ((hι₀ ▸ hΘc).comp c₀
    (hι.contDiffAt.of_le (by exact_mod_cast le_top))).congr_of_eventuallyEq ?_
  filter_upwards [ball_mem_nhds c₀ (by norm_num : (0 : ℝ) < 1 / 2)] with c hc
  have hιc : ι c ∈ ball f₀ (1 / 2) := by
    rw [mem_ball, dist_eq_norm]
    simp only [ι, add_sub_cancel_left]
    calc ‖L (c - c₀)‖ ≤ 1 * ‖c - c₀‖ := L.le_of_opNorm_le (LinearMap.mkContinuous_norm_le _
          zero_le_one _) _
      _ < 1 / 2 := by rw [one_mul, ← dist_eq_norm]; exact mem_ball.1 hc
  ext t
  rw [Function.comp_apply, hΘ _ hιc t]
  simp [ι, L, f₀]

end Family

end BoundedContinuousFunction
