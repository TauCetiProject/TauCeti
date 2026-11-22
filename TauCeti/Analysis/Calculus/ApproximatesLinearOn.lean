/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ApproximatesLinearOn
public import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps

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

A map on a convex set `S` with a derivative within `S` that stays close to a linear map `A`
admitting a continuous linear left inverse `P` is injective on `S`, and that derivative is
injective at every point of `S`: `P` of the map approximates the identity
(`Convex.injOn_and_injective_of_norm_hasFDerivWithin_sub_le`).

By the mean value inequality, a map on a convex set whose derivative stays within `c` of `L`
approximates `L` with constant `c` (`Convex.approximatesLinearOn_of_nnnorm_fderiv_sub_le`).

Combining the last two facts, a zero at which a continuous field of operators `D` is invertible
persists: every map whose derivative stays close to `D` on a small ball around `x`, and which
nearly vanishes at `x`, has a unique zero in the ball, with invertible derivative and at distance
linear in its value at `x` (`ContinuousLinearMap.IsInvertible.exists_eq_zero_perturbation`).

Maps approximating a linear equivalence `L` on one ball with one constant below `‖L⁻¹‖⁻¹` have
targets containing one common ball around any point near their values at the centre
(`TauCeti.exists_ball_subset_toOpenPartialHomeomorph_target`).

If the derivative of a function `g` is approximated by a bilinear map `L` on a convex set, a
critical point `y` of `g` in that set has a value within `(‖L‖ + κ) / 2 * ‖y - x‖ ^ 2` of that at
any other point `x` of the set (`ApproximatesLinearOn.norm_sub_le_of_fderiv_eq_zero`).

When `f` approximates a continuous linear map `L` on `s` up to `δ` and `M` is a continuous linear
operator in the opposite direction, the map `h x = x + M (f x - L x)` approximates the identity up
to `δ ‖M‖` (`ApproximatesLinearOn.id_add_comp_sub`). When `δ ‖M‖ < 1`, `h` is bi-Lipschitz on `s`
with a `(1 - δ ‖M‖)⁻¹`-Lipschitz left inverse on `h '' s`
(`ApproximatesLinearOn.exists_lipschitzOnWith_leftInvOn_id_add_comp_sub`), and when `M` is a right
inverse of `L` (`Function.RightInverse.preimage_id_add_comp_sub`,
`Function.RightInverse.image_id_add_comp_sub_inter_preimage`) this left inverse carries the linear
slices `h '' s ∩ L ⁻¹' {y}` onto the fibres `s ∩ f ⁻¹' {y}`
(`ApproximatesLinearOn.exists_lipschitzOnWith_eq_image_inter_preimage`).

A map `Φ` on a product `E × F` which vanishes on the zero section near `(a, 0)` and has, at
`(a, 0)`, a strict derivative injective on the fibre directions `{0} × F`, with `F`
finite-dimensional, grows linearly away from the zero section: near `(a, 0)`, `‖Φ z‖` is at least
a positive multiple of `‖z.2‖` (`HasStrictFDerivAt.exists_mul_norm_snd_le_norm_apply`), since the
map approximates its derivative and the derivative is bounded below on the fibre directions. In
particular `Φ` has no other zeros near `(a, 0)`
(`HasStrictFDerivAt.eventually_apply_eq_zero_iff_snd_eq_zero`). Applied to the derivative of a
function, this says that a critical zero section with nondegenerate normal Hessian is isolated
among critical points, as for a Morse–Bott critical submanifold, and that the differential
grows at least linearly with the distance to it.
-/

public section

open Filter Function Set Topology
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
      nnNorm := ⟨C, hC.le⟩
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
    hf.injOn <| f'.subsingleton_or_nnNorm_symm_pos.imp id fun hpos ↦ by
      -- `c * ‖f'⁻¹‖ ≤ c * C ≤ 1 / 2`.
      rw [NNReal.lt_inv_iff_mul_lt hpos.ne', ← NNReal.coe_lt_coe]
      push_cast
      linarith [mul_le_mul_of_nonneg_left hf' c.coe_nonneg]
  exact ⟨a, ha, hfa, fun z hz hfz ↦ hinj hz (hsub ha) (hfz.trans hfa.symm)⟩

/-- If `fderiv 𝕜 g` is `κ`-approximated by `L` on a convex set `s` on which `g` is differentiable,
and `g` has a critical point `y` in `s`, then `g` changes by at most
`(‖L‖ + κ) / 2 * ‖y - x‖ ^ 2` between any `x ∈ s` and `y`. -/
theorem norm_sub_le_of_fderiv_eq_zero [IsRCLikeNormedField 𝕜] [NormedSpace ℝ E]
    {g : E → F} {L : E →L[𝕜] E →L[𝕜] F} {s : Set E}
    {κ : ℝ≥0} (happrox : ApproximatesLinearOn (fderiv 𝕜 g) L s κ) (hs : Convex ℝ s)
    (hg : ∀ w ∈ s, DifferentiableAt 𝕜 g w) {x y : E} (hx : x ∈ s) (hy : y ∈ s)
    (hy0 : fderiv 𝕜 g y = 0) :
    ‖g y - g x‖ ≤ (‖L‖ + κ) / 2 * ‖y - x‖ ^ 2 := by
  -- Since `fderiv 𝕜 g y = 0`, the differential of `g` grows at most linearly away from `y`.
  have hbound (w) (hw : w ∈ s) : ‖fderiv 𝕜 g w‖ ≤ (‖L‖ + κ) * ‖w - y‖ := by
    simpa [hy0, Subtype.dist_eq, dist_eq_norm] using
      happrox.lipschitzWith.dist_le_mul ⟨w, hw⟩ ⟨y, hy⟩
  let : RCLike 𝕜 := IsRCLikeNormedField.rclike 𝕜
  let : NormedSpace ℝ F := NormedSpace.restrictScalars ℝ 𝕜 F
  -- Along the segment from `y` to `x`, compare `g (y + t • (x - y)) - g y` with a quadratic in `t`.
  have hmem (t) (ht : t ∈ Icc (0 : ℝ) 1) : y + t • (x - y) ∈ s := hs.add_smul_sub_mem hy hx ht
  have hD (t) (ht : t ∈ Icc (0 : ℝ) 1) : HasDerivAt (fun t ↦ g (y + t • (x - y)) - g y)
      (fderiv 𝕜 g (y + t • (x - y)) (x - y)) t := by
    simpa using HasDerivAt.sub_const (g y) <|
      HasFDerivAt.comp_hasDerivAt t (HasFDerivAt.restrictScalars ℝ (hg _ (hmem t ht)).hasFDerivAt)
        (HasDerivAt.const_add y (HasDerivAt.smul_const (hasDerivAt_id t) (x - y)))
  have hB (t : ℝ) : HasDerivAt (fun t ↦ (‖L‖ + κ) / 2 * ‖x - y‖ ^ 2 * (t * t))
      ((‖L‖ + κ) * ‖x - y‖ ^ 2 * t) t := by
    convert HasDerivAt.const_mul ((‖L‖ + κ) / 2 * ‖x - y‖ ^ 2)
      (HasDerivAt.mul (hasDerivAt_id' t) (hasDerivAt_id' t)) using 1
    ring
  -- The derivative along the segment is at most `(‖L‖ + κ) * ‖x - y‖ ^ 2 * t` in norm.
  have hbound' (t) (ht : t ∈ Ico (0 : ℝ) 1) :
      ‖fderiv 𝕜 g (y + t • (x - y)) (x - y)‖ ≤ (‖L‖ + κ) * ‖x - y‖ ^ 2 * t := by
    have hnorm : ‖y + t • (x - y) - y‖ = t * ‖x - y‖ := by
      rw [add_sub_cancel_left, norm_smul, Real.norm_of_nonneg ht.1]
    calc ‖fderiv 𝕜 g (y + t • (x - y)) (x - y)‖
        ≤ ‖fderiv 𝕜 g (y + t • (x - y))‖ * ‖x - y‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ (‖L‖ + κ) * ‖y + t • (x - y) - y‖ * ‖x - y‖ := by
        gcongr; exact hbound _ (hmem t (Ico_subset_Icc_self ht))
      _ = (‖L‖ + κ) * ‖x - y‖ ^ 2 * t := by rw [hnorm]; ring
  have := image_norm_le_of_norm_deriv_right_le_deriv_boundary
    (fun t ht ↦ (hD t ht).continuousAt.continuousWithinAt)
    (fun t ht ↦ (hD t (Ico_subset_Icc_self ht)).hasDerivWithinAt) (by simp) hB hbound'
    (right_mem_Icc.2 zero_le_one)
  simpa [norm_sub_rev (g y), norm_sub_rev x y, sq] using this

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
  rw [← NNReal.coe_le_coe, coe_nnNorm, NNReal.coe_one]
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
    simpa [ContinuousLinearMap.nnNorm_id] using NNReal.half_lt_self one_ne_zero
  · -- `P ∘ h' u - id` sends `w` to `-w` and has norm at most `1 / 2`, so `w = 0`.
    have h1 := (P.comp (h' u) - ContinuousLinearMap.id 𝕜 E).le_of_opNorm_le (hclose u hu) w
    have hw' : (P.comp (h' u) - ContinuousLinearMap.id 𝕜 E) w = -w := by simp [hw]
    rw [hw', norm_neg] at h1
    have : ‖w‖ = 0 := by linarith [norm_nonneg w]
    exact norm_eq_zero.1 this

/-- On a convex set on which every derivative of `f` is within `c` of `L` in norm, the map `f`
approximates `L` with constant `c`. This is the converse of
`ApproximatesLinearOn.norm_sub_le_of_hasFDerivAt`, by the mean value inequality. -/
theorem Convex.approximatesLinearOn_of_nnnorm_fderiv_sub_le {𝕜 E F : Type*}
    [NontriviallyNormedField 𝕜] [IsRCLikeNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace 𝕜 F] {f : E → F} {L : E →L[𝕜] F}
    {s : Set E} {c : ℝ≥0} (hs : Convex ℝ s) (hd : ∀ x ∈ s, DifferentiableAt 𝕜 f x)
    (hb : ∀ x ∈ s, ‖fderiv 𝕜 f x - L‖₊ ≤ c) :
    ApproximatesLinearOn f L s c :=
  fun _ hx _ hy ↦ hs.norm_image_sub_le_of_norm_fderiv_le' hd (fun z hz ↦ hb z hz) hy hx

namespace ContinuousLinearMap.IsInvertible

open Metric

/-- **Persistence of a zero under perturbations with nearby derivative.**

Let `D` be a field of operators, continuous at `x`, with `D x` invertible. For every sufficiently
small radius `r` there is `δ > 0` with the following property. If `G` is differentiable at every
point of the closed ball of radius `r` around `x`, its derivative stays within `δ` of `D` on the
ball, and `‖G x‖ ≤ δ`, then `G` approximates `D x` on the ball with a constant `c` independent of
`r`, and it has a zero `y` in the ball, which is the only one there. At `y` the derivative of `G`
is invertible, and `y` lies within `K * ‖G x‖` of `x`, for a constant `K` depending only on `D`
and `x`.

Taking `D = fderiv 𝕜 Φ` for a map `Φ` with `Φ x = 0` gives the persistence of a nondegenerate
zero of `Φ` under small `C¹` perturbations. -/
theorem exists_eq_zero_perturbation {𝕜 E F : Type*} [NontriviallyNormedField 𝕜]
    [IsRCLikeNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedSpace ℝ E]
    [CompleteSpace E] [NormedAddCommGroup F] [NormedSpace 𝕜 F] {D : E → E →L[𝕜] F} {x : E}
    (hinv : (D x).IsInvertible) (hD : ContinuousAt D x) :
    ∃ (K : ℝ) (c : ℝ≥0), ∀ᶠ r in 𝓝[>] 0, ∃ δ > 0, ∀ G : E → F,
      (∀ y ∈ closedBall x r, DifferentiableAt 𝕜 G y) →
      (∀ y ∈ closedBall x r, ‖fderiv 𝕜 G y - D y‖ ≤ δ) → ‖G x‖ ≤ δ →
      ApproximatesLinearOn G (D x) (closedBall x r) c ∧
        ∃ y ∈ closedBall x r, G y = 0 ∧ (fderiv 𝕜 G y).IsInvertible ∧
          dist y x ≤ K * ‖G x‖ ∧ ∀ z ∈ closedBall x r, G z = 0 → z = y := by
  -- On a small ball the derivative of `G` stays within `κ` of the invertible operator
  -- `L = D x`, so `G` has a unique zero there by `exists_eq_zero_of_two_mul_norm_le`.
  obtain ⟨L, hL⟩ := hinv
  -- `C` bounds the inverse of `L` and is positive even on the zero space.
  set C : ℝ := ‖(L.symm : F →L[𝕜] E)‖ + 1
  have hLsymm : ‖(L.symm : F →L[𝕜] E)‖ ≤ C := le_add_of_nonneg_right zero_le_one
  obtain ⟨ε₀, hε₀, hinv'⟩ :=
    Metric.eventually_nhds_iff.1 (ContinuousLinearMap.IsInvertible.eventually_nhds ⟨L, hL⟩)
  -- `κ` is the admissible distance from `L` on the ball.
  set κ : ℝ := min (2 * C)⁻¹ (ε₀ / 2)
  have hκ : 0 < κ := by positivity
  have hκC : 2 * C * κ ≤ 1 :=
    calc 2 * C * κ ≤ 2 * C * (2 * C)⁻¹ := by gcongr; exact min_le_left _ _
      _ = 1 := mul_inv_cancel₀ (by positivity)
  have hκε₀ : κ < ε₀ := (min_le_right _ _).trans_lt (half_lt_self hε₀)
  obtain ⟨ρ, hρ, hρD⟩ := Metric.eventually_nhds_iff.1
    (hD.eventually (Metric.ball_mem_nhds _ (half_pos hκ)))
  refine ⟨2 * C, ⟨κ, hκ.le⟩, ?_⟩
  filter_upwards [Ioo_mem_nhdsGT hρ] with r hr
  refine ⟨min (κ / 2) (r / (2 * C)), by have := hr.1; positivity, fun G hG hGD hGx ↦ ?_⟩
  -- On the ball, the derivative of `G` is within `κ` of `L`.
  have hclose (y : E) (hy : y ∈ closedBall x r) : ‖fderiv 𝕜 G y - L‖ ≤ κ :=
    calc ‖fderiv 𝕜 G y - L‖ ≤ ‖fderiv 𝕜 G y - D y‖ + ‖D y - L‖ :=
          norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ ≤ κ / 2 + κ / 2 := by
          gcongr
          · exact (hGD y hy).trans (min_le_left _ _)
          · rw [hL, ← dist_eq_norm]
            exact (hρD (lt_of_le_of_lt (mem_closedBall.1 hy) hr.2)).le
      _ = κ := add_halves κ
  have happrox : ApproximatesLinearOn G (L : E →L[𝕜] F) (closedBall x r) ⟨κ, hκ.le⟩ :=
    (convex_closedBall x r).approximatesLinearOn_of_nnnorm_fderiv_sub_le hG fun y hy ↦ by
      exact_mod_cast hclose y hy
  have hεr : 2 * C * ‖G x‖ ≤ r := by
    have : ‖G x‖ ≤ r / (2 * C) := hGx.trans (min_le_right _ _)
    rwa [le_div_iff₀ (by positivity), mul_comm] at this
  obtain ⟨y, hyε, hy0, huniq⟩ := happrox.exists_eq_zero_of_two_mul_norm_le hLsymm hκC hεr
  have hsub : closedBall x (2 * C * ‖G x‖) ⊆ closedBall x r := closedBall_subset_closedBall hεr
  refine ⟨hL ▸ happrox, y, hsub hyε, hy0, hinv' ?_, mem_closedBall.1 hyε, huniq⟩
  rw [dist_eq_norm, ← hL]
  exact (hclose y (hsub hyε)).trans_lt hκε₀

end ContinuousLinearMap.IsInvertible

/-- **A map vanishing on the zero section grows linearly away from it.** Let `Φ` be strictly
differentiable at `(a, 0)` with derivative `D`, and let `Φ (b, 0) = 0` for every `b` near `a`. If
`F` is finite-dimensional and `v ↦ D (0, v)` is injective, then near `(a, 0)` the norm of `Φ z` is
bounded below by a positive multiple of `‖z.2‖`, the distance from `z` to the zero section in the
fibre direction. -/
theorem HasStrictFDerivAt.exists_mul_norm_snd_le_norm_apply {𝕜 : Type*}
    [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜] {E F G : Type*} [NormedAddCommGroup E]
    [NormedSpace 𝕜 E] [NormedAddCommGroup F] [NormedSpace 𝕜 F] [FiniteDimensional 𝕜 F]
    [NormedAddCommGroup G] [NormedSpace 𝕜 G] {Φ : E × F → G} {D : E × F →L[𝕜] G} {a : E}
    (hΦ : HasStrictFDerivAt Φ D (a, 0)) (hzero : ∀ᶠ b in 𝓝 a, Φ (b, 0) = 0)
    (hD : Function.Injective (D ∘L ContinuousLinearMap.inr 𝕜 E F)) :
    ∃ c > 0, ∀ᶠ z in 𝓝 (a, (0 : F)), c * ‖z.2‖ ≤ ‖Φ z‖ := by
  -- `D` is bounded below on the fibre directions, by `K⁻¹`.
  obtain ⟨K, hK, hKD⟩ :=
    (D ∘L ContinuousLinearMap.inr 𝕜 E F).toLinearMap.injective_iff_antilipschitz.1 hD
  obtain ⟨s, hs, hΦs⟩ := hΦ.approximates_deriv_on_nhds (c := (2 * K)⁻¹) (.inr (by positivity))
  -- The projection `z ↦ (z.1, 0)` onto the zero section fixes `(a, 0)`.
  have hπ : Tendsto (fun z : E × F ↦ (z.1, (0 : F))) (𝓝 (a, 0)) (𝓝 (a, 0)) :=
    (continuous_fst.prodMk continuous_const).tendsto' _ _ rfl
  refine ⟨(2 * K : ℝ)⁻¹, by positivity, ?_⟩
  filter_upwards [hs, hπ.eventually hs, (continuous_fst.tendsto' _ _ rfl).eventually hzero]
    with z hzs hzs' hz0
  -- Compare `z` with its projection `(z.1, 0)`, which differs from it by `(0, z.2)`.
  have happ := hΦs z hzs (z.1, 0) hzs'
  have hsub : z - (z.1, 0) = ContinuousLinearMap.inr 𝕜 E F z.2 := by ext <;> simp
  have hnorm : ‖ContinuousLinearMap.inr 𝕜 E F z.2‖ = ‖z.2‖ := by simp
  rw [hz0, sub_zero, hsub, hnorm] at happ
  -- So `‖z.2‖ ≤ K ‖D (0, z.2)‖ ≤ K ‖Φ z‖ + ‖z.2‖ / 2`.
  have hbound := ContinuousLinearMap.bound_of_antilipschitz _ hKD z.2
  have hD' : ‖(D ∘L ContinuousLinearMap.inr 𝕜 E F) z.2‖ ≤ ‖Φ z‖ + (2 * K : ℝ≥0)⁻¹ * ‖z.2‖ := by
    have := norm_le_norm_add_norm_sub' ((D ∘L ContinuousLinearMap.inr 𝕜 E F) z.2) (Φ z)
    rw [norm_sub_rev] at this
    simp only [ContinuousLinearMap.coe_comp, comp_apply] at this ⊢
    linarith
  have hhalf : (K : ℝ) * ((2 * K : ℝ≥0)⁻¹ * ‖z.2‖) = ‖z.2‖ / 2 := by
    push_cast
    field_simp
  have hle := hbound.trans (mul_le_mul_of_nonneg_left hD' K.coe_nonneg)
  rw [mul_add, hhalf] at hle
  have hK' : (0 : ℝ) < K := by exact_mod_cast hK
  rw [inv_mul_le_iff₀ (by positivity)]
  nlinarith [hK']

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
  obtain ⟨c, hc, hcz⟩ := hΦ.exists_mul_norm_snd_le_norm_apply hzero hD
  filter_upwards [hcz, (continuous_fst.tendsto' _ _ rfl).eventually hzero] with z hz hz0
  refine ⟨fun h ↦ ?_, fun h ↦ by rwa [← Prod.mk.eta (p := z), h]⟩
  rw [h, norm_zero] at hz
  exact norm_le_zero_iff.1 (nonpos_of_mul_nonpos_right hz hc)

namespace TauCeti

open Metric

/-- For the maps approximating `L` on `ball x₀ r` with a constant `c` below `‖L⁻¹‖⁻¹`, there is
one radius `ρ > 0` such that the target of each of their partial homeomorphisms contains
`ball y₀ ρ` as soon as its value at `x₀` lies in that ball. -/
theorem exists_ball_subset_toOpenPartialHomeomorph_target {𝕜 E F : Type*}
    [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F] {L : E ≃L[𝕜] F} {x₀ : E} {r : ℝ} (hr : 0 < r)
    {c : ℝ≥0} (hc : Subsingleton E ∨ c < ‖(L.symm : F →L[𝕜] E)‖₊⁻¹) (y₀ : F) :
    ∃ ρ > 0, ∀ (g : E → F) (hga : ApproximatesLinearOn g (L : E →L[𝕜] F) (ball x₀ r) c),
      dist (g x₀) y₀ < ρ →
        ball y₀ ρ ⊆ (hga.toOpenPartialHomeomorph g (ball x₀ r) hc isOpen_ball).target := by
  by_cases hE : Subsingleton E
  · have hF : Subsingleton F := L.symm.toEquiv.subsingleton
    refine ⟨1, one_pos, fun g hga _ y _ ↦ ?_⟩
    rw [Subsingleton.elim y (g x₀), ApproximatesLinearOn.toOpenPartialHomeomorph_target]
    exact mem_image_of_mem g (mem_ball_self hr)
  have hpos : (0 : ℝ) < ((‖(L.symm : F →L[𝕜] E)‖₊⁻¹ : ℝ≥0) : ℝ) - c :=
    sub_pos.2 (NNReal.coe_lt_coe.2 (hc.resolve_left hE))
  refine ⟨(((‖(L.symm : F →L[𝕜] E)‖₊⁻¹ : ℝ≥0) : ℝ) - c) * (r / 2) / 2, by positivity,
    fun g hga hg y hy ↦ ?_⟩
  refine hga.closedBall_subset_target hc isOpen_ball (b := x₀) (ε := r / 2) (by positivity)
    (closedBall_subset_ball (by linarith)) (mem_closedBall.2 ?_)
  rw [mem_ball] at hy
  linarith [dist_triangle_right y (g x₀) y₀]

end TauCeti
