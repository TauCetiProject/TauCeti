/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Operator.Banach
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Invertible
import Mathlib.Analysis.Normed.Group.InfiniteSum

/-!
# Exact preimages from approximate preimages

Banach's open mapping theorem is proved in two steps. Baire's theorem first shows that every
point of the target is approximately the image of a point of controlled norm; a geometric
series then upgrades these approximate preimages to exact ones, using completeness of the
domain. Mathlib only states the composite theorem
`ContinuousLinearMap.exists_preimage_norm_le`, whose hypothesis is surjectivity.

This file isolates the second step, so that other sources of approximate preimages can be fed
into it. The main application is the case where the closure of the image of every ball contains a
ball, as happens when the adjoint is bounded below; this is how surjectivity is recovered in the
closed-range theorem. The scalar actions need no compatibility with the norms; only additivity
and continuity of the map enter the argument.

The file also records the form of the open mapping theorem used to invert operators pointwise:
a bijective continuous linear map between Banach spaces is invertible. It also identifies
Mathlib's equivalence `ContinuousLinearMap.coprodSubtypeLEquivOfIsCompl`, which the open mapping
theorem builds from an injective map and a complement of its range, with the underlying
coproduct map. Finally, it records the consequence of the closed graph theorem used to turn
regularity statements into estimates: a map between Banach spaces whose values all lie in the
range of an injective bounded map `g` is bounded after composing with `g⁻¹`. For instance, if
every solution of an elliptic equation with data in one Banach space lies in a smaller Banach space
of more regular functions, then the solution is bounded in the smaller space by the data.

## Main declarations

* `ContinuousLinearMap.exists_preimage_norm_le_of_approx`: approximate preimages of norm at most
  `C * ‖y‖` with relative error `r < 1` give exact preimages of norm at most `C / (1 - r) * ‖y‖`.
* `ContinuousLinearMap.exists_preimage_norm_le_of_mem_closure`: if every `y` lies in the closure of
  the image of the closed ball of radius `C * ‖y‖`, then for every `C' > C`, every `y` has a
  preimage of norm at most `C' * ‖y‖`.
* `ContinuousLinearMap.coe_coprodSubtypeLEquivOfIsCompl`: Mathlib's equivalence
  `f.coprodSubtypeLEquivOfIsCompl` of `E × G` with `F`, for an injective `f` whose range has
  the complement `G`, is `f.coprod G.subtypeL` as a continuous linear map.
* `ContinuousLinearMap.isInvertible_iff_bijective`: by the open mapping theorem, a continuous
  linear map between Banach spaces is invertible exactly when it is bijective.
* `ContinuousLinearMap.exists_comp_eq_of_range_le_range`: by the closed graph theorem, if the
  range of `f` lies in the range of an injective `g`, then `f` factors as `g ∘ h` with `h` a
  continuous linear map.
* `ContinuousLinearMap.exists_norm_le_of_range_le_range`: under the same hypotheses, the solutions
  `y` of `g y = f x` are bounded by a constant multiple of `‖x‖`.
* `LinearMap.continuous_of_injective_comp_eq`: by the closed graph theorem, a linear map `e`
  between Banach spaces is continuous when `g ∘ e = f` for continuous maps `f` and `g` into a
  Hausdorff space with `g` injective.
* `ContinuousLinearMap.spectrum_restrictScalars`: realification preserves the spectrum of an
  operator on a Banach space.

## References

* W. Rudin, *Functional Analysis*, 2nd ed., Lemma 4.13.

The series argument follows the second half of the proof of Mathlib's
`ContinuousLinearMap.exists_preimage_norm_le`.
-/

public section

open Function Metric Set Filter Finset Topology

namespace ContinuousLinearMap

variable {𝕜 𝕜' : Type*} [Semiring 𝕜] [Semiring 𝕜'] {σ : 𝕜 →+* 𝕜'}
variable {E : Type*} [SeminormedAddCommGroup E] [Module 𝕜 E] [CompleteSpace E]
variable {F : Type*} [NormedAddCommGroup F] [Module 𝕜' F]

/-- **Approximate preimages give exact preimages.** Let `r < 1`. If every `y` is within
`r * ‖y‖` of the image of a point of norm at most `C * ‖y‖`, then every `y` is the image of a point
of norm at most `C / (1 - r) * ‖y‖`. -/
theorem exists_preimage_norm_le_of_approx (f : E →SL[σ] F) {r C : ℝ} (hr : r < 1)
    (hC : ∀ y, ∃ x, dist (f x) y ≤ r * ‖y‖ ∧ ‖x‖ ≤ C * ‖y‖) (y : F) :
    ∃ x, f x = y ∧ ‖x‖ ≤ C / (1 - r) * ‖y‖ := by
  rcases eq_or_ne y 0 with rfl | hy
  · exact ⟨0, by simp, by simp⟩
  -- The approximate preimage of `y` shows that both constants are nonnegative.
  obtain ⟨x₀, hx₀y, hx₀⟩ := hC y
  have hr0 : 0 ≤ r := nonneg_of_mul_nonneg_left (dist_nonneg.trans hx₀y) (norm_pos_iff.2 hy)
  have hC0 : 0 ≤ C := nonneg_of_mul_nonneg_left ((norm_nonneg _).trans hx₀) (norm_pos_iff.2 hy)
  /- Let `g y` be the approximate preimage of `y`, and `h y = y - f (g y)` the part of `y` that
  is not yet hit. Iterating, `u n = g (h^[n] y)` is a summable series whose sum is a preimage
  of `y`. -/
  choose g hg using hC
  let h y := y - f (g y)
  have hle : ∀ y, ‖h y‖ ≤ r * ‖y‖ := by
    intro y
    rw [← dist_eq_norm, dist_comm]
    exact (hg y).1
  have hnle : ∀ n : ℕ, ‖h^[n] y‖ ≤ r ^ n * ‖y‖ := by
    intro n
    induction n with
    | zero => simp
    | succ n IH =>
      rw [iterate_succ']
      apply (hle _).trans
      rw [pow_succ', mul_assoc]
      gcongr
  let u n := g (h^[n] y)
  have ule : ∀ n, ‖u n‖ ≤ r ^ n * (C * ‖y‖) := fun n ↦
    calc
      ‖u n‖ ≤ C * ‖h^[n] y‖ := (hg _).2
      _ ≤ C * (r ^ n * ‖y‖) := by gcongr; exact hnle n
      _ = r ^ n * (C * ‖y‖) := by ring
  have hgeom := (summable_geometric_of_lt_one hr0 hr).mul_right (C * ‖y‖)
  have sNu : Summable fun n ↦ ‖u n‖ := .of_nonneg_of_le (fun n ↦ norm_nonneg _) ule hgeom
  let x := tsum u
  have x_ineq : ‖x‖ ≤ C / (1 - r) * ‖y‖ :=
    calc
      ‖x‖ ≤ ∑' n, ‖u n‖ := norm_tsum_le_tsum_norm sNu
      _ ≤ ∑' n, r ^ n * (C * ‖y‖) := sNu.tsum_le_tsum ule hgeom
      _ = (∑' n, r ^ n) * (C * ‖y‖) := tsum_mul_right
      _ = C / (1 - r) * ‖y‖ := by rw [tsum_geometric_of_lt_one hr0 hr]; ring
  have fsumeq : ∀ n : ℕ, f (∑ i ∈ range n, u i) = y - h^[n] y := by
    intro n
    induction n with
    | zero => simp
    | succ n IH => rw [sum_range_succ, map_add, IH, iterate_succ_apply', sub_add]
  have L₁ : Tendsto (fun n ↦ f (∑ i ∈ range n, u i)) atTop (𝓝 (f x)) :=
    (f.continuous.tendsto _).comp sNu.of_norm.hasSum.tendsto_sum_nat
  simp only [fsumeq] at L₁
  have L₂ : Tendsto (fun n ↦ h^[n] y) atTop (𝓝 0) :=
    squeeze_zero_norm hnle <| by
      simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hr0 hr).mul_const ‖y‖
  exact ⟨x, by simpa using tendsto_nhds_unique L₁ (tendsto_const_nhds.sub L₂), x_ineq⟩

/-- **Banach's lemma.** If every `y` lies in the closure of the image of the closed ball of radius
`C * ‖y‖`, then for every `C' > C`, every `y` has a preimage of norm at most `C' * ‖y‖`. In
particular, the map is surjective. -/
theorem exists_preimage_norm_le_of_mem_closure (f : E →SL[σ] F) {C : ℝ}
    (hC : ∀ y, y ∈ closure (f '' closedBall 0 (C * ‖y‖))) {C' : ℝ} (hC' : C < C') (y : F) :
    ∃ x, f x = y ∧ ‖x‖ ≤ C' * ‖y‖ := by
  rcases eq_or_ne y 0 with rfl | hy
  · exact ⟨0, by simp, by simp⟩
  -- The closure around `y` is nonempty, so `C` is nonnegative.
  have hC0 : 0 ≤ C := nonneg_of_mul_nonneg_left
    (nonempty_closedBall.1 (closure_nonempty_iff.1 ⟨y, hC y⟩).of_image) (norm_pos_iff.2 hy)
  /- For `C < C₁ < C'`, approximate preimages of norm at most `C₁ * ‖z‖` can be found with
  relative error `r = 1 - C₁ / C'`, and then `C₁ / (1 - r) = C'`. -/
  obtain ⟨C₁, hCC₁, hC₁C'⟩ := exists_between hC'
  have hC₁ : 0 < C₁ := hC0.trans_lt hCC₁
  have hr : 0 < 1 - C₁ / C' := sub_pos.2 <| (div_lt_one (hC₁.trans hC₁C')).2 hC₁C'
  have happrox (z : F) : ∃ x, dist (f x) z ≤ (1 - C₁ / C') * ‖z‖ ∧ ‖x‖ ≤ C₁ * ‖z‖ := by
    rcases eq_or_ne z 0 with rfl | hz
    · exact ⟨0, by simp, by simp⟩
    obtain ⟨_, ⟨x, hx, rfl⟩, hxz⟩ :=
      Metric.mem_closure_iff.mp (hC z) ((1 - C₁ / C') * ‖z‖) (mul_pos hr (norm_pos_iff.2 hz))
    refine ⟨x, by rw [dist_comm]; exact hxz.le, ?_⟩
    calc ‖x‖ ≤ C * ‖z‖ := by simpa using hx
      _ ≤ C₁ * ‖z‖ := by gcongr
  obtain ⟨x, hxy, hx⟩ :=
    f.exists_preimage_norm_le_of_approx (sub_lt_self 1 (div_pos hC₁ (hC₁.trans hC₁C'))) happrox y
  rw [sub_sub_cancel, div_div_cancel₀ hC₁.ne'] at hx
  exact ⟨x, hxy, hx⟩

end ContinuousLinearMap

namespace ContinuousLinearMap

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E F : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] [CompleteSpace F]

/-- The equivalence `f.coprodSubtypeLEquivOfIsCompl h hker` of `E × G` with `F`, given by an
injective `f` whose range has the complement `G`, is `f.coprod G.subtypeL` as a continuous linear
map. -/
@[simp]
theorem coe_coprodSubtypeLEquivOfIsCompl (f : E →L[𝕜] F) {G : Submodule 𝕜 F}
    (h : IsCompl f.range G) [CompleteSpace G] (hker : f.ker = ⊥) :
    (f.coprodSubtypeLEquivOfIsCompl h hker : E × G →L[𝕜] F) = f.coprod G.subtypeL :=
  ContinuousLinearEquiv.coe_ofBijective _ _ _

/-- By the open mapping theorem, a continuous linear map between Banach spaces is invertible, that
is, a continuous linear equivalence, exactly when it is bijective. -/
theorem isInvertible_iff_bijective {f : E →L[𝕜] F} : f.IsInvertible ↔ Bijective f :=
  ⟨IsInvertible.bijective, fun h ↦ ⟨.ofBijective f (LinearMap.ker_eq_bot.2 h.1)
    (LinearMap.range_eq_top.2 h.2), ContinuousLinearEquiv.coe_ofBijective _ _ _⟩⟩

end ContinuousLinearMap

namespace ContinuousLinearMap

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E F G : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] [NormedAddCommGroup G] [NormedSpace 𝕜 G]
  [CompleteSpace G]

/-- **Bounded lift through an injective map.** Let `f : E →L[𝕜] F` and `g : G →L[𝕜] F` be
continuous linear maps out of Banach spaces, with `g` injective and the range of `f` contained in
the range of `g`. Then the induced linear map `g⁻¹ ∘ f : E → G` is bounded, by the closed graph
theorem: there is a continuous linear map `h : E →L[𝕜] G` with `g ∘ h = f`. -/
theorem exists_comp_eq_of_range_le_range (f : E →L[𝕜] F) (g : G →L[𝕜] F) (hg : Injective g)
    (hfg : f.range ≤ g.range) : ∃ h : E →L[𝕜] G, g.comp h = f := by
  let h : E →ₗ[𝕜] G := (LinearEquiv.ofInjective (g : G →ₗ[𝕜] F) hg).symm.toLinearMap ∘ₗ
    (f : E →ₗ[𝕜] F).codRestrict (LinearMap.range (g : G →ₗ[𝕜] F)) fun x ↦ hfg ⟨x, rfl⟩
  have hgh (x : E) : g (h x) = f x :=
    LinearEquiv.ofInjective_symm_apply (f := (g : G →ₗ[𝕜] F)) (h := hg) _
  have hcont : Continuous h := h.continuous_of_seq_closed_graph fun u x y hu hy ↦ hg <| by
    have hy' : Tendsto (f ∘ u) atTop (𝓝 (g y)) := by
      simpa only [comp_def, hgh] using (g.continuous.tendsto y).comp hy
    rw [hgh, tendsto_nhds_unique ((f.continuous.tendsto x).comp hu) hy']
  exact ⟨⟨h, hcont⟩, ext hgh⟩

/-- **Bounded factorization through an injective map.** Let `f : E →L[𝕜] F` and `g : G →L[𝕜] F` be
continuous linear maps out of Banach spaces, with `g` injective and the range of `f` contained in
the range of `g`. Then the solutions `y` of `g y = f x` are bounded: there is a constant `C ≥ 0`
with `‖y‖ ≤ C * ‖x‖` whenever `g y = f x`
(`ContinuousLinearMap.exists_comp_eq_of_range_le_range`). -/
theorem exists_norm_le_of_range_le_range (f : E →L[𝕜] F) (g : G →L[𝕜] F) (hg : Injective g)
    (hfg : f.range ≤ g.range) : ∃ C ≥ 0, ∀ x y, g y = f x → ‖y‖ ≤ C * ‖x‖ := by
  obtain ⟨h, hgh⟩ := exists_comp_eq_of_range_le_range f g hg hfg
  refine ⟨‖h‖, norm_nonneg _, fun x y hxy ↦ ?_⟩
  obtain rfl : y = h x := hg (hxy.trans (DFunLike.congr_fun hgh x).symm)
  exact h.le_opNorm x

end ContinuousLinearMap

namespace LinearMap

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E G X : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
  [NormedAddCommGroup G] [NormedSpace 𝕜 G] [CompleteSpace G] [TopologicalSpace X] [T2Space X]

/-- **Continuity through an injective continuous map.** Let `e : E →ₗ[𝕜] G` be a linear map
between Banach spaces, and let `f : E → X` and `g : G → X` be continuous maps into a Hausdorff
space with `g` injective and `g ∘ e = f`. Then `e` is continuous: its graph is the closed set of
pairs `(x, y)` with `g y = f x`, so the closed graph theorem applies. -/
theorem continuous_of_injective_comp_eq (e : E →ₗ[𝕜] G) {f : E → X} {g : G → X}
    (hf : Continuous f) (hg : Continuous g) (hg_inj : Injective g) (h : ∀ x, g (e x) = f x) :
    Continuous e := by
  refine e.continuous_of_isClosed_graph ?_
  have : (e.graph : Set (E × G)) = {q | g q.2 = f q.1} := by
    ext q
    simp only [SetLike.mem_coe, mem_graph_iff, mem_ofPred_eq, ← h q.1, hg_inj.eq_iff]
  rw [this]
  exact isClosed_eq (hg.comp continuous_snd) (hf.comp continuous_fst)

end LinearMap

namespace ContinuousLinearMap

variable {𝕜 E : Type*} [NontriviallyNormedField 𝕜] [NormedAlgebra ℝ 𝕜] [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] [CompleteSpace E] [Algebra ℝ (E →L[𝕜] E)] [IsScalarTower ℝ 𝕜 (E →L[𝕜] E)]
  [NormedSpace ℝ E] [IsScalarTower ℝ 𝕜 E]

/-- **Realification preserves the spectrum** of a bounded operator on a Banach space over a normed
`ℝ`-algebra `𝕜`, for any real algebra structure on the operators compatible with the `𝕜`-action:
by Banach's inverse mapping theorem an operator is invertible exactly when it is bijective, and the
realification has the same underlying function. -/
theorem spectrum_restrictScalars (T : E →L[𝕜] E) :
    spectrum ℝ (T.restrictScalars ℝ) = spectrum ℝ T := by
  have h (r : ℝ) : ⇑(algebraMap ℝ (E →L[ℝ] E) r - T.restrictScalars ℝ) =
      ⇑(algebraMap ℝ (E →L[𝕜] E) r - T) := by
    ext x
    simp [IsScalarTower.algebraMap_apply ℝ 𝕜 (E →L[𝕜] E), Algebra.algebraMap_eq_smul_one]
  ext r
  simp only [spectrum.mem_iff, isUnit_iff_bijective, h]

end ContinuousLinearMap
