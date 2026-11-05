/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ApproximatesLinearOn

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

When `f` approximates a continuous linear map `L` on `s` up to `δ` and `M` is a continuous linear
operator in the opposite direction, the map `h x = x + M (f x - L x)` approximates the identity up
to `δ ‖M‖` (`ApproximatesLinearOn.id_add_comp_sub`). When `δ ‖M‖ < 1`, `h` is bi-Lipschitz on `s`
with a `(1 - δ ‖M‖)⁻¹`-Lipschitz left inverse on `h '' s`
(`ApproximatesLinearOn.exists_lipschitzOnWith_leftInvOn_id_add_comp_sub`), and when `M` is a right
inverse of `L` this left inverse carries the linear slices `h '' s ∩ L ⁻¹' {y}` onto the fibres
`s ∩ f ⁻¹' {y}` (`ApproximatesLinearOn.exists_lipschitzOnWith_eq_image_inter_preimage`).
-/

public section

open Function Set
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
  set h : E → E := fun x ↦ x + M (f x - L x)
  obtain ⟨g, hlip, hg⟩ := hf.exists_lipschitzOnWith_leftInvOn_id_add_comp_sub hδ
  refine ⟨h '' s, g, hlip, fun y ↦ ?_⟩
  have hpre : f ⁻¹' {y} = h ⁻¹' (L ⁻¹' {y}) := by
    ext x
    simp only [mem_preimage, h]
    rw [map_add, hM, add_sub_cancel]
  rw [hpre, ← image_inter_preimage, hg.image_image' inter_subset_left]

end Straightening

end ApproximatesLinearOn
