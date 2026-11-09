/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ApproximatesLinearOn
public import Mathlib.Analysis.Calculus.MeanValue

/-!
# A priori estimates and straightening for maps approximating linear maps

An estimate controlling a vector by its image under a continuous linear map and an auxiliary
additive map persists under a nonlinear approximation, with a loss proportional to the
approximation constant. `ApproximatesLinearOn.one_sub_mul_norm_sub_le` records this absorption
estimate. Taking the auxiliary map to be a projection onto the kernel gives the nonlinear form
of the Peetre estimate used in local properness arguments.

Mathlib's local surjectivity and injectivity theorems also locate a unique zero of a map
approximating a linear equivalence on a closed ball:
`ApproximatesLinearOn.exists_eq_zero_of_two_mul_norm_le`.

A map on a convex set whose derivative stays close to a linear map `A` with a left inverse `P`
is injective there, with injective derivative: `P` of the map approximates the identity
(`Convex.injOn_and_injective_of_norm_hasFDerivAt_sub_le`).

If the derivative of a function `g` is approximated by a bilinear map `L` near `x`, a critical point
`y` of `g` near `x` has a value within `(‖L‖ + κ) * (2 * ρ) * ρ` of that at `x`
(`ApproximatesLinearOn.norm_sub_le_of_fderiv_eq_zero`).

When `f` approximates a continuous linear map `L` on `s` up to `δ` and `M` is a continuous linear
operator in the opposite direction, the map `h x = x + M (f x - L x)` approximates the identity up
to `δ ‖M‖` (`ApproximatesLinearOn.id_add_comp_sub`). When `δ ‖M‖ < 1`, `h` is bi-Lipschitz on `s`
with a `(1 - δ ‖M‖)⁻¹`-Lipschitz left inverse on `h '' s`
(`ApproximatesLinearOn.exists_lipschitzOnWith_leftInvOn_id_add_comp_sub`), and when `M` is a right
inverse of `L` (`Function.RightInverse.preimage_id_add_comp_sub`,
`Function.RightInverse.image_id_add_comp_sub_inter_preimage`) this left inverse carries the linear
slices `h '' s ∩ L ⁻¹' {y}` onto the fibres `s ∩ f ⁻¹' {y}`
(`ApproximatesLinearOn.exists_lipschitzOnWith_eq_image_inter_preimage`).
-/

public section

open Function Set
open scoped NNReal Pointwise

namespace Function.RightInverse

/-- If `M` is a right inverse of an additive homomorphism `L`, then preimages under `f` agree with
preimages of `L`-preimages under the straightening map `x ↦ x + M (f x - L x)`. -/
theorem preimage_id_add_comp_sub {E F 𝓕 : Type*} [AddMonoid E] [AddCommGroup F] [FunLike 𝓕 E F]
    [AddMonoidHomClass 𝓕 E F] {L : 𝓕} {M : F → E} (hM : RightInverse M L) (f : E → F)
    (u : Set F) :
    f ⁻¹' u = (fun x ↦ x + M (f x - L x)) ⁻¹' (L ⁻¹' u) := by
  ext x
  simp [map_add, hM (f x - L x), add_sub_cancel]

/-- If `M` is a right inverse of an additive homomorphism `L`, then the straightening map
`h x = x + M (f x - L x)` maps `s ∩ f ⁻¹' u` onto `h '' s ∩ L ⁻¹' u`. -/
theorem image_id_add_comp_sub_inter_preimage {E F 𝓕 : Type*} [AddMonoid E] [AddCommGroup F]
    [FunLike 𝓕 E F] [AddMonoidHomClass 𝓕 E F] {L : 𝓕} {M : F → E} (hM : RightInverse M L)
    (s : Set E) (f : E → F) (u : Set F) :
    (fun x ↦ x + M (f x - L x)) '' (s ∩ f ⁻¹' u) =
      (fun x ↦ x + M (f x - L x)) '' s ∩ L ⁻¹' u := by
  rw [hM.preimage_id_add_comp_sub f u, image_inter_preimage]

end Function.RightInverse

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
  have hnorm : ‖f' (x - y)‖ ≤ ‖f x - f y‖ + (ε : ℝ) * ‖x - y‖ :=
    (norm_le_norm_add_norm_sub (f x - f y) _).trans
      (add_le_add le_rfl (hf x hx y hy))
  have hmul := mul_le_mul_of_nonneg_left hnorm hC
  rw [map_sub P x y] at hestxy
  nlinarith

/-- A map approximating a linear equivalence `f'` on a closed ball around `b`, with constant at most
`(2 * C)⁻¹` for a bound `C` on `‖f'⁻¹‖`, has a zero within `2 * C * ‖f b‖` of `b` as soon as that
radius fits in the ball, and this zero is the only zero of the map in the ball. -/
theorem exists_eq_zero_of_two_mul_norm_le [CompleteSpace E] {f : E → F} {f' : E ≃L[𝕜] F}
    {b : E} {r : ℝ} {c : ℝ≥0}
    (hf : ApproximatesLinearOn f (f' : E →L[𝕜] F) (Metric.closedBall b r) c) {C : ℝ}
    (hC : 0 < C) (hf' : ‖(f'.symm : F →L[𝕜] E)‖ ≤ C) (hc : 2 * C * c ≤ 1)
    (hr : 2 * C * ‖f b‖ ≤ r) :
    ∃ a ∈ Metric.closedBall b (2 * C * ‖f b‖), f a = 0 ∧
      ∀ z ∈ Metric.closedBall b r, f z = 0 → z = a := by
  have hbound (v : F) : ‖f'.symm v‖ ≤ C * ‖v‖ :=
    ((f'.symm : F →L[𝕜] E).le_opNorm v).trans (mul_le_mul_of_nonneg_right hf' (norm_nonneg v))
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
  have hinj : InjOn f (Metric.closedBall b r) := by
    apply hf.injOn
    rcases f'.subsingleton_or_nnnorm_symm_pos with hE | hpos
    · exact Or.inl hE
    right
    refine (NNReal.lt_inv_iff_mul_lt hpos.ne').2 ?_
    rw [← NNReal.coe_lt_coe]
    push_cast
    have hmul := mul_le_mul_of_nonneg_left hf' c.coe_nonneg
    nlinarith
  exact ⟨a, ha, hfa, fun z hz hfz ↦ hinj hz (hsub ha) (hfz.trans hfa.symm)⟩

open Metric in
/-- If `fderiv 𝕜 g` is `κ`-approximated by `L` on a set containing the closed ball of radius `ρ`
about `x`, `g` is differentiable on that ball, and `g` has a critical point `y` in the ball, then
`g` changes by at most `(‖L‖ + κ) * (2 * ρ) * ρ` between `x` and `y`. -/
theorem norm_sub_le_of_fderiv_eq_zero [IsRCLikeNormedField 𝕜] [NormedSpace ℝ E]
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
  have hval := (convex_closedBall x ρ).norm_image_sub_le_of_norm_fderiv_le hg hbound
    (mem_closedBall_self hρ) hy
  rw [← dist_eq_norm, ← dist_eq_norm] at hval
  calc ‖g y - g x‖ = dist (g y) (g x) := (dist_eq_norm _ _).symm
    _ ≤ (‖L‖ + κ) * (2 * ρ) * dist y x := hval
    _ ≤ (‖L‖ + κ) * (2 * ρ) * ρ := by gcongr; exact mem_closedBall.1 hy

/-! ### Straightening a map along a continuous linear operator -/

section Straightening

variable {f : E → F} {L : E →L[𝕜] F} {M : F →L[𝕜] E} {s : Set E} {δ : ℝ≥0}

/-- If `f` approximates `L` on `s` up to `δ`, then `x ↦ x + M (f x - L x)` approximates the
identity on `s` up to `δ ‖M‖`. -/
theorem id_add_comp_sub (hf : ApproximatesLinearOn f L s δ) (M : F →L[𝕜] E) :
    ApproximatesLinearOn (fun x ↦ x + M (f x - L x)) (ContinuousLinearMap.id 𝕜 E) s
      (δ * ‖M‖₊) := by
  refine LipschitzOnWith.approximatesLinearOn ?_
  have h : (fun x ↦ x + M (f x - L x)) - ⇑(ContinuousLinearMap.id 𝕜 E) = M ∘ (f - ⇑L) := by
    ext x
    simp
  rw [h, mul_comm]
  exact M.lipschitzWith.comp_lipschitzOnWith hf.lipschitzOnWith

/-- If `f` approximates `L` on `s` up to `δ`, then `x ↦ x + M (f x - L x)` is
`(1 + δ ‖M‖)`-Lipschitz on `s`. -/
theorem lipschitzOnWith_id_add_comp_sub (hf : ApproximatesLinearOn f L s δ) (M : F →L[𝕜] E) :
    LipschitzOnWith (1 + δ * ‖M‖₊) (fun x ↦ x + M (f x - L x)) s := by
  refine lipschitzOnWith_iff_restrict.2 ((hf.id_add_comp_sub M).lipschitzWith.weaken ?_)
  gcongr
  rw [← NNReal.coe_le_coe, coe_nnnorm, NNReal.coe_one]
  exact ContinuousLinearMap.norm_id_le

/-- If `f` approximates `L` on `s` up to `δ` and `δ ‖M‖ < 1`, then `x ↦ x + M (f x - L x)` expands
distances on `s` by at least the factor `1 - δ ‖M‖`. -/
theorem antilipschitzWith_id_add_comp_sub (hf : ApproximatesLinearOn f L s δ)
    (hδ : δ * ‖M‖₊ < 1) :
    AntilipschitzWith (1 - δ * ‖M‖₊)⁻¹ (s.domRestrict fun x ↦ x + M (f x - L x)) := by
  cases subsingleton_or_nontrivial E
  · exact AntilipschitzWith.of_subsingleton
  have hf' : ApproximatesLinearOn (fun x ↦ x + M (f x - L x))
      (ContinuousLinearEquiv.refl 𝕜 E : E →L[𝕜] E) s (δ * ‖M‖₊) := hf.id_add_comp_sub M
  simpa using hf'.antilipschitzWith (Or.inr (by simpa using hδ))

/-- If `f` approximates `L` on `s` up to `δ` and `δ ‖M‖ < 1`, then `x ↦ x + M (f x - L x)` is
injective on `s`. -/
theorem injOn_id_add_comp_sub (hf : ApproximatesLinearOn f L s δ) (hδ : δ * ‖M‖₊ < 1) :
    InjOn (fun x ↦ x + M (f x - L x)) s :=
  injOn_iff_injective.2 (hf.antilipschitzWith_id_add_comp_sub hδ).injective

/-- If `f` approximates `L` on `s` up to `δ` and `δ ‖M‖ < 1`, then the map
`h x = x + M (f x - L x)` admits a `(1 - δ ‖M‖)⁻¹`-Lipschitz left inverse on `h '' s`. -/
theorem exists_lipschitzOnWith_leftInvOn_id_add_comp_sub (hf : ApproximatesLinearOn f L s δ)
    (hδ : δ * ‖M‖₊ < 1) :
    ∃ g : E → E, LipschitzOnWith (1 - δ * ‖M‖₊)⁻¹ g ((fun x ↦ x + M (f x - L x)) '' s) ∧
      LeftInvOn g (fun x ↦ x + M (f x - L x)) s :=
  ⟨invFunOn (fun x ↦ x + M (f x - L x)) s,
    lipschitzOnWith_iff_restrict.2 ((hf.antilipschitzWith_id_add_comp_sub hδ).to_rightInvOn'
      (surjOn_image _ s).mapsTo_invFunOn (surjOn_image _ s).rightInvOn_invFunOn),
    (hf.injOn_id_add_comp_sub hδ).leftInvOn_invFunOn⟩

/-- If `f` is approximated on `s` up to `δ` by a continuous linear map `L` with a continuous linear
right inverse `M` satisfying `δ ‖M‖ < 1`, then there are a set `t` and a `(1 - δ ‖M‖)⁻¹`-Lipschitz
map `g` on `t` that maps each linear slice `t ∩ L ⁻¹' {y}` onto the fibre `s ∩ f ⁻¹' {y}`. -/
theorem exists_lipschitzOnWith_eq_image_inter_preimage (hf : ApproximatesLinearOn f L s δ)
    (hM : RightInverse M L) (hδ : δ * ‖M‖₊ < 1) :
    ∃ (t : Set E) (g : E → E), LipschitzOnWith (1 - δ * ‖M‖₊)⁻¹ g t ∧
      ∀ y, s ∩ f ⁻¹' {y} = g '' (t ∩ L ⁻¹' {y}) := by
  obtain ⟨g, hlip, hg⟩ := hf.exists_lipschitzOnWith_leftInvOn_id_add_comp_sub hδ
  refine ⟨(fun x ↦ x + M (f x - L x)) '' s, g, hlip, fun y ↦ ?_⟩
  rw [← hM.image_id_add_comp_sub_inter_preimage, hg.image_image' inter_subset_left]

end Straightening

end ApproximatesLinearOn

/-- **A map whose derivative is close to an injective linear map is injective on a convex set.**
If `P` is a left inverse of `A` and the derivative of `h` stays within `1 / (2 ‖P‖)` of `A` on a
convex set `S`, then `h` is injective on `S`, and its derivative is injective there. -/
theorem Convex.injOn_and_injective_of_norm_hasFDerivAt_sub_le {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    {S : Set E} (hS : Convex ℝ S) {h : E → F} {h' : E → E →L[ℝ] F} {A : E →L[ℝ] F}
    {P : F →L[ℝ] E} (hPA : Function.LeftInverse P A) (hh : ∀ u ∈ S, HasFDerivAt h (h' u) u)
    (hh' : ∀ u ∈ S, ‖P‖ * ‖h' u - A‖ ≤ 1 / 2) :
    InjOn h S ∧ ∀ u ∈ S, Function.Injective (h' u) := by
  have hPA' : P.comp A = ContinuousLinearMap.id ℝ E := ContinuousLinearMap.ext hPA
  -- `P ∘ h'` is within `1 / 2` of the identity.
  have hclose (u) (hu : u ∈ S) : ‖P.comp (h' u) - ContinuousLinearMap.id ℝ E‖ ≤ 1 / 2 := by
    rw [← hPA', ← ContinuousLinearMap.comp_sub]
    exact (ContinuousLinearMap.opNorm_comp_le _ _).trans (hh' u hu)
  refine ⟨?_, fun u hu => (injective_iff_map_eq_zero _).2 fun w hw => ?_⟩
  · -- `P ∘ h` approximates the identity with constant `1 / 2`, so it is injective on `S`.
    have happ : ApproximatesLinearOn (fun v => P (h v))
        (ContinuousLinearEquiv.refl ℝ E : E →L[ℝ] E) S (1 / 2) := by
      intro x hx y hy
      simpa using hS.norm_image_sub_le_of_norm_hasFDerivWithin_le' (f := fun v => P (h v))
        (fun v hv => (P.hasFDerivAt.comp v (hh v hv)).hasFDerivWithinAt)
        (fun v hv => (hclose v hv).trans_eq (by simp)) hy hx
    refine InjOn.of_comp (g := ⇑P) (happ.injOn ?_)
    rcases subsingleton_or_nontrivial E with hE | hE
    · exact Or.inl hE
    · refine Or.inr ?_
      simpa [ContinuousLinearMap.nnnorm_id] using NNReal.half_lt_self one_ne_zero
  · have h1 := ((P.comp (h' u) - ContinuousLinearMap.id ℝ _).le_opNorm w).trans
      (mul_le_mul_of_nonneg_right (hclose u hu) (norm_nonneg w))
    have hw' : (P.comp (h' u) - ContinuousLinearMap.id ℝ E) w = -w := by simp [hw]
    rw [hw', norm_neg] at h1
    have : ‖w‖ = 0 := by linarith [norm_nonneg w]
    exact norm_eq_zero.1 this
