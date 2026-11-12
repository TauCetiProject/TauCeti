/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ApproximatesLinearOn
public import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
# A priori estimates for maps approximating linear maps

An estimate controlling a vector by its image under a continuous linear map and an auxiliary
additive map persists under a nonlinear approximation, with a loss proportional to the
approximation constant. `ApproximatesLinearOn.one_sub_mul_norm_sub_le` records this absorption
estimate. Taking the auxiliary map to be a projection onto the kernel gives the nonlinear form
of the Peetre estimate used in local properness arguments.

Mathlib's local surjectivity and injectivity theorems also locate a unique zero of a map
approximating a linear equivalence on a closed ball:
`ApproximatesLinearOn.exists_eq_zero_of_two_mul_norm_le`.

A map on a convex set `S` with a derivative within `S` that stays close to a linear map `A`
admitting a continuous linear left inverse `P` is injective on `S`, and that derivative is
injective at every point of `S`: `P` of the map approximates the identity
(`Convex.injOn_and_injective_of_norm_hasFDerivWithin_sub_le`).

If the derivative of a function `g` is approximated by a bilinear map `L` near `x`, a critical point
`y` of `g` near `x` has a value within `(‖L‖ + κ) * (2 * ρ) * ρ` of that at `x`
(`ApproximatesLinearOn.norm_sub_le_of_fderiv_eq_zero`).

A map `Φ` on a product `E × F` which vanishes on the zero section near `(a, 0)` and has, at
`(a, 0)`, a strict derivative injective on the fibre directions `{0} × F`, with `F`
finite-dimensional, has no other zeros near `(a, 0)`
(`HasStrictFDerivAt.eventually_apply_eq_zero_iff_snd_eq_zero`): near `(a, 0)` the map
approximates its derivative, and the derivative is bounded below on the fibre directions.
Applied to the derivative of a function, this says that a critical zero section with
nondegenerate normal Hessian is isolated among critical points, as for a Morse–Bott critical
submanifold.
-/

public section

open Filter Set Topology
open scoped NNReal Pointwise

namespace ApproximatesLinearOn

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- An a priori estimate for a linear map on `s - s` persists under a nonlinear approximation,
with its left side scaled by `1 - C * ε`. For `C * ε < 1`, this controls `‖x - y‖` by the images
under `f` and an auxiliary additive map `P`.

Taking `P` to be a projection onto the kernel recovers the nonlinear Peetre estimate; see
Wendl, *Fredholm operators*, Lemma 5.2, for the linear estimate. -/
theorem one_sub_mul_norm_sub_le {f : E → F} {f' : E →L[𝕜] F} {s : Set E} {ε : ℝ≥0}
    (hf : ApproximatesLinearOn f f' s ε) {G 𝓕 : Type*} [SeminormedAddGroup G]
    [FunLike 𝓕 E G] [AddMonoidHomClass 𝓕 E G] {P : 𝓕} {C : ℝ} (hC : 0 ≤ C)
    (hest : ∀ z ∈ s - s, ‖z‖ ≤ C * ‖f' z‖ + ‖P z‖)
    {x : E} (hx : x ∈ s) {y : E} (hy : y ∈ s) :
    (1 - C * (ε : ℝ)) * ‖x - y‖ ≤ C * ‖f x - f y‖ + ‖P x - P y‖ := by
  have hestxy := hest (x - y) (sub_mem_sub hx hy)
  rw [map_sub P x y] at hestxy
  have hnorm : ‖f' (x - y)‖ ≤ ‖f x - f y‖ + (ε : ℝ) * ‖x - y‖ :=
    (norm_le_norm_add_norm_sub (f x - f y) _).trans (by gcongr; exact hf x hx y hy)
  linarith [mul_le_mul_of_nonneg_left hnorm hC]

/-- A map approximating a linear equivalence `f'` on a closed ball around `b`, with constant at most
`(2 * C)⁻¹` for a bound `C` on `‖f'⁻¹‖`, has a zero within `2 * C * ‖f b‖` of `b` as soon as that
radius fits in the ball, and this zero is the only zero of the map in the ball. -/
theorem exists_eq_zero_of_two_mul_norm_le [CompleteSpace E] {f : E → F} {f' : E ≃L[𝕜] F}
    {b : E} {r : ℝ} {c : ℝ≥0}
    (hf : ApproximatesLinearOn f (f' : E →L[𝕜] F) (Metric.closedBall b r) c) {C : ℝ}
    (hf' : ‖(f'.symm : F →L[𝕜] E)‖ ≤ C) (hc : 2 * C * c ≤ 1)
    (hr : 2 * C * ‖f b‖ ≤ r) :
    ∃ a ∈ Metric.closedBall b (2 * C * ‖f b‖), f a = 0 ∧
      ∀ z ∈ Metric.closedBall b r, f z = 0 → z = a := by
  have hbound (v : F) : ‖f'.symm v‖ ≤ C * ‖v‖ :=
    ((f'.symm : F →L[𝕜] E).le_opNorm v).trans (mul_le_mul_of_nonneg_right hf' (norm_nonneg v))
  rcases ((norm_nonneg _).trans hf').eq_or_lt with hC | hC
  · -- `C = 0`: `f'.symm = 0`, so `E` and `F` are trivial.
    subst hC
    have hE : Subsingleton E := subsingleton_of_forall_eq 0 fun x ↦ by simpa using hbound (f' x)
    have hF : Subsingleton F := f'.symm.injective.subsingleton
    exact ⟨b, by simp, Subsingleton.elim _ _, fun z _ _ ↦ Subsingleton.elim _ _⟩
  -- A right inverse of `f'` with the bound `C` in place of `‖f'⁻¹‖`, which may vanish.
  let R : (f' : E →L[𝕜] F).NonlinearRightInverse :=
    { toFun := f'.symm
      nnnorm := ⟨C, hC.le⟩
      bound' := hbound
      right_inv' := f'.apply_symm_apply }
  have hsub := Metric.closedBall_subset_closedBall (x := b) hr
  have hzero : (0 : F) ∈ Metric.closedBall (f b) ((C⁻¹ - c) * (2 * C * ‖f b‖)) := by
    rw [Metric.mem_closedBall, dist_comm, dist_zero_right]
    have hCinv : C⁻¹ * C = 1 := inv_mul_cancel₀ hC.ne'
    nlinarith [norm_nonneg (f b)]
  obtain ⟨a, ha, hfa⟩ := (hf.mono_set hsub).surjOn_closedBall_of_nonlinearRightInverse R
    (by positivity) le_rfl hzero
  have hinj : InjOn f (Metric.closedBall b r) :=
    hf.injOn <| f'.subsingleton_or_nnnorm_symm_pos.imp id fun hpos ↦ by
      -- `c * ‖f'⁻¹‖ ≤ c * C ≤ 1 / 2`.
      rw [NNReal.lt_inv_iff_mul_lt hpos.ne', ← NNReal.coe_lt_coe]
      push_cast
      linarith [mul_le_mul_of_nonneg_left hf' c.coe_nonneg]
  exact ⟨a, ha, hfa, fun z hz hfz ↦ hinj hz (hsub ha) (hfz.trans hfa.symm)⟩

open Metric in
/-- If `fderiv 𝕜 g` is `κ`-approximated by `L` on a set containing the closed ball of radius `ρ`
about `x`, `g` is differentiable on that ball, and `g` has a critical point `y` in the ball, then
`g` changes by at most `(‖L‖ + κ) * (2 * ρ) * ρ` between `x` and `y`. -/
theorem norm_sub_le_of_fderiv_eq_zero [IsRCLikeNormedField 𝕜]
    {g : E → F} {L : E →L[𝕜] E →L[𝕜] F} {s : Set E}
    {κ : ℝ≥0} (happrox : ApproximatesLinearOn (fderiv 𝕜 g) L s κ) {x y : E} {ρ : ℝ}
    (hg : ∀ w ∈ closedBall x ρ, DifferentiableAt 𝕜 g w) (hsub : closedBall x ρ ⊆ s)
    (hy : y ∈ closedBall x ρ) (hy0 : fderiv 𝕜 g y = 0) :
    ‖g y - g x‖ ≤ (‖L‖ + κ) * (2 * ρ) * ρ := by
  have hρ : 0 ≤ ρ := dist_nonneg.trans (mem_closedBall.1 hy)
  have hbound : ∀ w ∈ closedBall x ρ, ‖fderiv 𝕜 g w‖ ≤ (‖L‖ + κ) * (2 * ρ) := fun w hw ↦ by
    have hlip := happrox.lipschitzWith.dist_le_mul ⟨w, hsub hw⟩ ⟨y, hsub hy⟩
    simp only [domRestrict_apply, hy0, dist_zero_right, Subtype.dist_eq] at hlip
    calc ‖fderiv 𝕜 g w‖ ≤ (‖L‖ + κ) * dist w y := hlip
      _ ≤ (‖L‖ + κ) * (2 * ρ) := by
        gcongr
        linarith [dist_triangle_right w y x, mem_closedBall.1 hw, mem_closedBall.1 hy]
  let : RCLike 𝕜 := IsRCLikeNormedField.rclike 𝕜
  let : NormedSpace ℝ E := NormedSpace.restrictScalars ℝ 𝕜 E
  have hval := (convex_closedBall x ρ).norm_image_sub_le_of_norm_fderiv_le hg hbound
    (mem_closedBall_self hρ) hy
  calc ‖g y - g x‖ ≤ (‖L‖ + κ) * (2 * ρ) * ‖y - x‖ := hval
    _ ≤ (‖L‖ + κ) * (2 * ρ) * ρ := by gcongr; exact mem_closedBall_iff_norm.1 hy

end ApproximatesLinearOn

/-- **A map with a derivative within a convex set close to a linear map admitting a continuous
linear left inverse is injective there.**
If `P` is a continuous linear left inverse of `A` and a derivative `h'` of `h` within a convex set
`S` satisfies `‖P‖ * ‖h' u - A‖ ≤ 1 / 2` on `S`, then `h` is injective on `S`, and `h' u` is
injective for every `u ∈ S`. -/
theorem Convex.injOn_and_injective_of_norm_hasFDerivWithin_sub_le {𝕜 E F : Type*}
    [NontriviallyNormedField 𝕜] [IsRCLikeNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    {S : Set E} (hS : Convex ℝ S) {h : E → F} {h' : E → E →L[𝕜] F} {A : E →L[𝕜] F}
    {P : F →L[𝕜] E} (hPA : Function.LeftInverse P A)
    (hh : ∀ u ∈ S, HasFDerivWithinAt h (h' u) S u)
    (hh' : ∀ u ∈ S, ‖P‖ * ‖h' u - A‖ ≤ 1 / 2) :
    InjOn h S ∧ ∀ u ∈ S, Function.Injective (h' u) := by
  have hPA' : P.comp A = ContinuousLinearMap.id 𝕜 E := ContinuousLinearMap.ext hPA
  -- `P ∘ h'` is within `1 / 2` of the identity.
  have hclose (u) (hu : u ∈ S) : ‖P.comp (h' u) - ContinuousLinearMap.id 𝕜 E‖ ≤ 1 / 2 := by
    rw [← hPA', ← ContinuousLinearMap.comp_sub]
    exact (ContinuousLinearMap.opNorm_comp_le _ _).trans (hh' u hu)
  refine ⟨?_, fun u hu => (injective_iff_map_eq_zero _).2 fun w hw => ?_⟩
  · -- `P ∘ h` approximates the identity with constant `1 / 2`, so it is injective on `S`.
    have happ : ApproximatesLinearOn (fun v => P (h v))
        (ContinuousLinearEquiv.refl 𝕜 E : E →L[𝕜] E) S (1 / 2) := by
      intro x hx y hy
      simpa using hS.norm_image_sub_le_of_norm_hasFDerivWithin_le' (f := fun v => P (h v))
        (fun v hv => P.hasFDerivAt.comp_hasFDerivWithinAt v (hh v hv))
        (fun v hv => (hclose v hv).trans_eq (by simp)) hy hx
    refine InjOn.of_comp (g := ⇑P) <| happ.injOn <|
      (subsingleton_or_nontrivial E).imp id fun (_ : Nontrivial E) ↦ ?_
    simpa [ContinuousLinearMap.nnnorm_id] using NNReal.half_lt_self one_ne_zero
  · -- `P ∘ h' u - id` sends `w` to `-w` and has norm at most `1 / 2`, so `w = 0`.
    have h1 := (P.comp (h' u) - ContinuousLinearMap.id 𝕜 E).le_of_opNorm_le (hclose u hu) w
    have hw' : (P.comp (h' u) - ContinuousLinearMap.id 𝕜 E) w = -w := by simp [hw]
    rw [hw', norm_neg] at h1
    have : ‖w‖ = 0 := by linarith [norm_nonneg w]
    exact norm_eq_zero.1 this

/-- **The zeros of a map vanishing on the zero section, near the zero section.** Let `Φ` be
strictly differentiable at `(a, 0)` with derivative `D`, and let `Φ (b, 0) = 0` for every `b` near
`a`. If `F` is finite-dimensional and `v ↦ D (0, v)` is injective, then near `(a, 0)` the zeros of
`Φ` are exactly the points of the zero section. -/
theorem HasStrictFDerivAt.eventually_apply_eq_zero_iff_snd_eq_zero {𝕜 : Type*}
    [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜] {E F G : Type*} [NormedAddCommGroup E]
    [NormedSpace 𝕜 E] [NormedAddCommGroup F] [NormedSpace 𝕜 F] [FiniteDimensional 𝕜 F]
    [NormedAddCommGroup G] [NormedSpace 𝕜 G] {Φ : E × F → G} {D : E × F →L[𝕜] G} {a : E}
    (hΦ : HasStrictFDerivAt Φ D (a, 0)) (hzero : ∀ᶠ b in 𝓝 a, Φ (b, 0) = 0)
    (hD : Function.Injective (D ∘L ContinuousLinearMap.inr 𝕜 E F)) :
    ∀ᶠ z in 𝓝 (a, (0 : F)), Φ z = 0 ↔ z.2 = 0 := by
  -- `D` is bounded below on the fibre directions, by `K⁻¹`.
  obtain ⟨K, hK, hKD⟩ :=
    (D ∘L ContinuousLinearMap.inr 𝕜 E F).toLinearMap.injective_iff_antilipschitz.1 hD
  obtain ⟨s, hs, hΦs⟩ := hΦ.approximates_deriv_on_nhds (c := (2 * K)⁻¹) (.inr (by positivity))
  -- The projection `z ↦ (z.1, 0)` onto the zero section fixes `(a, 0)`.
  have hπ : Tendsto (fun z : E × F ↦ (z.1, (0 : F))) (𝓝 (a, 0)) (𝓝 (a, 0)) :=
    (continuous_fst.prodMk continuous_const).tendsto' _ _ rfl
  filter_upwards [hs, hπ.eventually hs, (continuous_fst.tendsto' _ _ rfl).eventually hzero]
    with z hzs hzs' hz0
  refine ⟨fun hz ↦ ?_, fun hz ↦ by rwa [← Prod.mk.eta (p := z), hz]⟩
  -- Compare `z` with its projection `(z.1, 0)`, which differs from it by `(0, z.2)`.
  have happ := hΦs z hzs (z.1, 0) hzs'
  have hsub : z - (z.1, 0) = ContinuousLinearMap.inr 𝕜 E F z.2 := by ext <;> simp
  have hnorm : ‖ContinuousLinearMap.inr 𝕜 E F z.2‖ = ‖z.2‖ := by simp
  rw [hz, hz0, sub_zero, zero_sub, norm_neg, hsub, hnorm] at happ
  have hbound := ContinuousLinearMap.bound_of_antilipschitz _ hKD z.2
  have hK' : (0 : ℝ) < K := NNReal.coe_pos.2 hK
  have hhalf : (K : ℝ) * ((2 * K : ℝ≥0)⁻¹ * ‖z.2‖) = ‖z.2‖ / 2 := by
    push_cast
    field_simp
  have hle := hbound.trans (mul_le_mul_of_nonneg_left happ K.coe_nonneg)
  rw [hhalf] at hle
  exact norm_le_zero_iff.1 (by linarith)
