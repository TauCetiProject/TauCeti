/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.QuadraticCorrection
public import TauCeti.Analysis.Sobolev.QuasilinearSection
import Mathlib.Topology.MetricSpace.UniformConvergence
import TauCeti.MeasureTheory.Function.Lp.Norm
import TauCeti.Topology.ContinuousMap.Bounded.Normed

/-!
# Zeros of a quasilinear section near an approximate solution

Let `S = TauCeti.quasilinearSection e A G w b` be the quasilinear section of the operator
`F(u) = ∂s u + A(z, u) ∂t u + G(z, u)` around a reference map `w`, on a space `X` of `Lᵖ(μ)` jets
`x = (ξ, ξ_s, ξ_t)` whose values have the continuous representatives `e`, such as `W^{1,p}` of the
cylinder or of the strip for `p > 2`. When `b = ∂t w`, on jets of differentiable sections it is
`F(w + ξ) - F(w)`. When `w` is only an approximate solution, as a pre-glued map is, the defect
`F(w)` is a small element `c` of `Lᵖ`, and for `b = ∂t w` the maps `w + ξ` solving `F(w + ξ) = 0`
weakly near `w` are the zeros of `x ↦ c + S x`. This file finds them by the Newton iteration,
given a bounded right inverse of the linearization
`D₀ = TauCeti.quasilinearLinearization e A A' G' w b 0` of `S` at the reference map.

**The linearization is Lipschitz in the base point.** If the coefficients `A`, `A'` and `G'` are
Lipschitz in the value `y`, uniformly in the domain point `z`, and `A'` is bounded, then the
linearizations at two points `x₀`, `x₁` of `X` satisfy

`‖D_{x₀} - D_{x₁}‖ ≤ ‖e‖ (K + K' + M B + N + M ‖e‖ ‖x₁‖) ‖x₀ - x₁‖`,

for Lipschitz constants `K` of `A`, `M` of `A'` and `N` of `G'`, a bound `K'` on `A'` and a bound
`B` on `b` (`TauCeti.norm_quasilinearLinearization_sub_le`). The coefficients enter through their
values at `w + ξ₀` and `w + ξ₁`, which are uniformly within `‖e‖ ‖x₀ - x₁‖` of each other, and the
weak derivative `ξ₀_t`, which enters the zeroth-order term of `D_{x₀}`, differs from `ξ₁_t` by at
most `‖x₀ - x₁‖` in `Lᵖ`. In particular `D_x` is within `‖e‖ (K + K' + M B + N) ‖x‖` of `D₀`.

**The Newton step.** By the quadratic mean value inequality this Lipschitz bound turns the
remainder `S x - D₀ x` into a quadratic one, which is what the contraction argument of
`TauCeti.exists_mem_range_norm_le_apply_eq_zero_of_norm_hasFDerivWithin_sub_le` needs. For
coefficients that are moreover `C¹` in `y`, so that `D_x` is the derivative of `S`
(`TauCeti.hasStrictFDerivAt_quasilinearSection`) and `A` is `K`-Lipschitz because its derivative
`A'` is bounded by `K' = K`, let `Q` be a right inverse of `D₀` and write
`Λ = ‖e‖ (2 K + M B + N)`.

* **Existence.** If `X` is complete and `2 ‖Q‖² Λ ‖c‖ < 1`, there is a zero `x` of `c + S` in the
  range of `Q` with `‖x‖ ≤ 2 ‖Q‖ ‖c‖`
  (`TauCeti.exists_mem_range_norm_le_add_quasilinearSection_eq_zero`).
* **Uniqueness.** Two zeros of `c + S` in the range of `Q`, of norm at most `r` with
  `‖Q‖ Λ r < 1`, coincide (`TauCeti.eq_of_add_quasilinearSection_eq_zero`).

So a defect of size `‖c‖` is corrected by a section of size at most `2 ‖Q‖ ‖c‖`. For a family of
approximate solutions, such as pre-glued Floer cylinders with the Floer section
`TauCeti.SymplecticForm.floerSection`, whose coefficient bounds and right inverses are uniform in
the gluing parameter, the correction therefore tends to zero with the defect. The normalization
`x ∈ range Q` singles out one zero near `w` among the zeros of a section whose linearization has a
kernel.

## References

* D. McDuff and D. Salamon, *J-holomorphic curves and symplectic topology*, 2nd ed., AMS
  Colloquium Publications 52 (2012), Section 3.5, on the quadratic estimate and the zeros of the
  nonlinear Cauchy–Riemann section near an approximate solution, and Chapter 10, on gluing.
* D. Salamon, *Lectures on Floer homology*, in *Symplectic geometry and topology*, IAS/Park City
  Math. Ser. 7 (1999), on gluing Floer trajectories.
-/

public section

open MeasureTheory Metric Set
open scoped ENNReal NNReal BoundedContinuousFunction

namespace TauCeti

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  {p : ℝ≥0∞} [Fact (1 ≤ p)] {μ : Measure (ℝ × ℝ)} {X : Submodule ℝ (Lp (V × V × V) p μ)}
  {e : X →L[ℝ] (ℝ × ℝ →ᵇ V)} {A : ℝ × ℝ → V → V →L[ℝ] V} {G : ℝ × ℝ → V → V}
  {A' : ℝ × ℝ → V → V →L[ℝ] V →L[ℝ] V} {G' : ℝ × ℝ → V → V →L[ℝ] V} {w b : ℝ × ℝ → V}
  {B C : ℝ} {K K' L M N : ℝ≥0}

/-! ### The linearization is Lipschitz in the base point -/

/-- The pointwise algebra of the difference of two linearizations. Let `v` be the jet of `h` at a
point, `η` its value read through the continuous representative, `v₀`, `v₁` the jets of `x₀`,
`x₁` there, `vd = v₀ - v₁`, and `u₀`, `u₁` the values `w + ξ₀`, `w + ξ₁`. The difference of the
pointwise expressions of the linearizations at `x₀` and `x₁`, applied to `h`, is the sum of
`(A(u₀) - A(u₁)) v_t`, `((A'(u₀) - A'(u₁)) v) b`, `(G'(u₀) - G'(u₁)) v`, `(A'(u₀) η) vd_t` and
`((A'(u₀) - A'(u₁)) η) v₁_t`; bounding each term gives the stated estimate, for bounds `D` on
`‖u₀ - u₁‖` and `H` on `‖η‖`. -/
private theorem norm_linearization_sub_apply_le (hbB : ∀ z, ‖b z‖ ≤ B)
    (hAL : ∀ z, LipschitzWith K (A z)) (hA'K : ∀ z y, ‖A' z y‖ ≤ K')
    (hA'L : ∀ z, LipschitzWith M (A' z)) (hG'L : ∀ z, LipschitzWith N (G' z)) (z : ℝ × ℝ)
    {u₀ u₁ η : V} {v v₀ v₁ vd : V × V × V} (hvd : vd = v₀ - v₁) {D H : ℝ}
    (hu : ‖u₀ - u₁‖ ≤ D) (hη : ‖η‖ ≤ H) :
    ‖v.2.1 + A z u₀ v.2.2 + A' z u₀ v.1 (b z) + G' z u₀ v.1 + A' z u₀ η v₀.2.2 -
        (v.2.1 + A z u₁ v.2.2 + A' z u₁ v.1 (b z) + G' z u₁ v.1 + A' z u₁ η v₁.2.2)‖ ≤
      D * (K + M * B + N) * ‖v‖ + K' * H * ‖vd‖ + M * D * H * ‖v₁‖ := by
  have hD : 0 ≤ D := (norm_nonneg _).trans hu
  have hH : 0 ≤ H := (norm_nonneg _).trans hη
  have h0 : ‖v.1‖ ≤ ‖v‖ := norm_fst_le v
  have h2 : ‖v.2.2‖ ≤ ‖v‖ := (norm_snd_le v.2).trans (norm_snd_le v)
  have hd2 : ‖v₀.2.2 - v₁.2.2‖ ≤ ‖vd‖ := by
    rw [hvd]
    exact (norm_snd_le (v₀ - v₁).2).trans (norm_snd_le (v₀ - v₁))
  have h₁2 : ‖v₁.2.2‖ ≤ ‖v₁‖ := (norm_snd_le v₁.2).trans (norm_snd_le v₁)
  have hAd : ‖A z u₀ - A z u₁‖ ≤ K * D := ((hAL z).norm_sub_le _ _).trans (by gcongr)
  have hA'd : ‖A' z u₀ - A' z u₁‖ ≤ M * D := ((hA'L z).norm_sub_le _ _).trans (by gcongr)
  have hG'd : ‖G' z u₀ - G' z u₁‖ ≤ N * D := ((hG'L z).norm_sub_le _ _).trans (by gcongr)
  -- The difference is the sum of five terms, each linear in the difference of the coefficients
  -- or in the difference `vd` of the jets.
  have hid : v.2.1 + A z u₀ v.2.2 + A' z u₀ v.1 (b z) + G' z u₀ v.1 + A' z u₀ η v₀.2.2 -
      (v.2.1 + A z u₁ v.2.2 + A' z u₁ v.1 (b z) + G' z u₁ v.1 + A' z u₁ η v₁.2.2) =
      (A z u₀ - A z u₁) v.2.2 + (A' z u₀ - A' z u₁) v.1 (b z) + (G' z u₀ - G' z u₁) v.1 +
        A' z u₀ η (v₀.2.2 - v₁.2.2) + (A' z u₀ - A' z u₁) η v₁.2.2 := by
    simp only [sub_apply, map_sub]
    abel
  have t₁ : ‖(A z u₀ - A z u₁) v.2.2‖ ≤ K * D * ‖v‖ :=
    (ContinuousLinearMap.le_opNorm _ _).trans (mul_le_mul hAd h2 (norm_nonneg _) (by positivity))
  have t₂ : ‖(A' z u₀ - A' z u₁) v.1 (b z)‖ ≤ M * D * ‖v‖ * B :=
    (ContinuousLinearMap.le_opNorm _ _).trans (mul_le_mul
      ((ContinuousLinearMap.le_opNorm _ _).trans
        (mul_le_mul hA'd h0 (norm_nonneg _) (by positivity)))
      (hbB z) (norm_nonneg _) (by positivity))
  have t₃ : ‖(G' z u₀ - G' z u₁) v.1‖ ≤ N * D * ‖v‖ :=
    (ContinuousLinearMap.le_opNorm _ _).trans (mul_le_mul hG'd h0 (norm_nonneg _) (by positivity))
  have t₄ : ‖A' z u₀ η (v₀.2.2 - v₁.2.2)‖ ≤ K' * H * ‖vd‖ :=
    (ContinuousLinearMap.le_opNorm _ _).trans (mul_le_mul
      ((ContinuousLinearMap.le_opNorm _ _).trans
        (mul_le_mul (hA'K z u₀) hη (norm_nonneg _) (by positivity)))
      hd2 (norm_nonneg _) (by positivity))
  have t₅ : ‖(A' z u₀ - A' z u₁) η v₁.2.2‖ ≤ M * D * H * ‖v₁‖ :=
    (ContinuousLinearMap.le_opNorm _ _).trans (mul_le_mul
      ((ContinuousLinearMap.le_opNorm _ _).trans
        (mul_le_mul hA'd hη (norm_nonneg _) (by positivity)))
      h₁2 (norm_nonneg _) (by positivity))
  rw [hid]
  refine ((norm_add_le _ _).trans (add_le_add norm_add₄_le le_rfl)).trans ?_
  linarith

/-- **The linearization of the quasilinear section is Lipschitz in the base point.** Let `b` be
bounded by `B`, let `A` be bounded and `K`-Lipschitz in the value `y` uniformly in `z`, let `A'`
be bounded by `K'` and `M`-Lipschitz in `y`, and let `G'` be bounded and `N`-Lipschitz in `y`, all
three continuous in `(z, y)`. Then the linearizations of the quasilinear section at two points
`x₀`, `x₁` of `X` satisfy
`‖D_{x₀} - D_{x₁}‖ ≤ ‖e‖ (K + K' + M B + N + M ‖e‖ ‖x₁‖) ‖x₀ - x₁‖`, with `e` the continuous
representatives of the values. The functions `A'` and `G'` need not be the derivatives of `A` and
`G`. -/
theorem norm_quasilinearLinearization_sub_le (hAc : Continuous (Function.uncurry A))
    (hA'c : Continuous (Function.uncurry A')) (hG'c : Continuous (Function.uncurry G'))
    (hw : AEStronglyMeasurable w μ) (hb : AEStronglyMeasurable b μ) (hbB : ∀ z, ‖b z‖ ≤ B)
    (hAC : ∀ z y, ‖A z y‖ ≤ C) (hAL : ∀ z, LipschitzWith K (A z)) (hA'K : ∀ z y, ‖A' z y‖ ≤ K')
    (hA'L : ∀ z, LipschitzWith M (A' z)) (hG'K : ∀ z y, ‖G' z y‖ ≤ L)
    (hG'L : ∀ z, LipschitzWith N (G' z)) (x₀ x₁ : X) :
    ‖quasilinearLinearization e A A' G' w b x₀ - quasilinearLinearization e A A' G' w b x₁‖ ≤
      ‖e‖ * (K + K' + M * B + N + M * ‖e‖ * ‖x₁‖) * ‖x₀ - x₁‖ := by
  have hB : 0 ≤ B := (norm_nonneg _).trans (hbB 0)
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun h ↦ ?_
  rw [sub_apply]
  refine (Lp.norm_le_add_add_of_ae_norm_le
    (g := (h : Lp (V × V × V) p μ)) (h := ((x₀ - x₁ : X) : Lp (V × V × V) p μ))
    (k := (x₁ : Lp (V × V × V) p μ)) (a := ‖e‖ * ‖x₀ - x₁‖ * (K + M * B + N))
    (b := K' * (‖e‖ * ‖h‖)) (c := M * (‖e‖ * ‖x₀ - x₁‖) * (‖e‖ * ‖h‖))
    (by positivity) (by positivity) (by positivity) ?_).trans_eq ?_
  · filter_upwards [Lp.coeFn_sub (quasilinearLinearization e A A' G' w b x₀ h)
        (quasilinearLinearization e A A' G' w b x₁ h),
      quasilinearLinearization_apply_ae hAc hA'c hG'c hw hb hbB hAC hA'K hG'K x₀ h,
      quasilinearLinearization_apply_ae hAc hA'c hG'c hw hb hbB hAC hA'K hG'K x₁ h,
      Lp.coeFn_sub (x₀ : Lp (V × V × V) p μ) x₁] with z e₁ e₂ e₃ e₄
    rw [e₁, Pi.sub_apply, e₂, e₃]
    exact norm_linearization_sub_apply_le hbB hAL hA'K hA'L hG'L z
      (by rw [Submodule.coe_sub, e₄, Pi.sub_apply])
      (by rw [add_sub_add_left_eq_sub]; exact e.norm_apply_sub_apply_le x₀ x₁ z)
      (((e h).norm_coe_le_norm z).trans (e.le_opNorm h))
  · simp only [Submodule.norm_coe]
    ring

/-! ### Zeros near an approximate solution -/

/-- The inputs of the contraction theorems for `c + S`: when the coefficients are differentiable in
the value with bounded, Lipschitz derivatives `A'` and `G'`, the map `x ↦ c + S x` has derivative
the linearization `D_x` at every `x`, and `D_x` is within `‖e‖ (2 K + M B + N) ‖x‖` of `D₀`. -/
private theorem hasFDerivAt_add_quasilinearSection_and_norm_sub_le
    (he : ∀ x : X, ∀ᵐ z ∂μ, ((x : Lp (V × V × V) p μ) z).1 = e x z)
    (hAc : Continuous (Function.uncurry A)) (hGc : Continuous (Function.uncurry G))
    (hA'c : Continuous (Function.uncurry A')) (hG'c : Continuous (Function.uncurry G'))
    (hw : AEStronglyMeasurable w μ) (hb : AEStronglyMeasurable b μ) (hbB : ∀ z, ‖b z‖ ≤ B)
    (hAC : ∀ z y, ‖A z y‖ ≤ C) (hA : ∀ z y, HasFDerivAt (A z) (A' z y) y)
    (hA'K : ∀ z y, ‖A' z y‖ ≤ K) (hA'L : ∀ z, LipschitzWith M (A' z))
    (hG : ∀ z y, HasFDerivAt (G z) (G' z y) y) (hG'K : ∀ z y, ‖G' z y‖ ≤ L)
    (hG'L : ∀ z, LipschitzWith N (G' z)) (c : Lp V p μ) :
    (∀ x, HasFDerivAt (fun x ↦ c + quasilinearSection e A G w b x)
      (quasilinearLinearization e A A' G' w b x) x) ∧
    ∀ x, ‖quasilinearLinearization e A A' G' w b x - quasilinearLinearization e A A' G' w b 0‖ ≤
      ‖e‖ * (2 * K + M * B + N) * ‖x‖ := by
  have hAL (z : ℝ × ℝ) : LipschitzWith K (A z) := lipschitzWith_of_nnNorm_fderiv_le
    (fun y ↦ (hA z y).differentiableAt) fun y ↦ by
      rw [(hA z y).fderiv]
      exact NNReal.coe_le_coe.1 (hA'K z y)
  have hS := hasStrictFDerivAt_quasilinearSection he hAc hGc hA'c hG'c hw hb hbB hAC hA hA'K
    (LipschitzWith.uniformEquicontinuous A' M hA'L) hG hG'K
    (LipschitzWith.uniformEquicontinuous G' N hG'L)
  refine ⟨fun x ↦ (hS x).hasFDerivAt.const_add c, fun x ↦ ?_⟩
  simpa [two_mul] using norm_quasilinearLinearization_sub_le hAc hA'c hG'c hw hb hbB hAC hAL hA'K
    hA'L hG'K hG'L x 0

/-- **Zeros of a quasilinear section near an approximate solution.** Let `e` give continuous
representatives of the values of the elements of a complete space `X` of jets, and let `b` be
bounded by `B`. Let the coefficients `A` and `G` be continuous in `(z, y)`, with `A` bounded, and
differentiable in the value `y` with derivatives `A'` and `G'` continuous in `(z, y)`, `A'` bounded
by `K` and `M`-Lipschitz in `y`, `G'` bounded and `N`-Lipschitz in `y`, uniformly in `z`. Let `Q`
be a right inverse of the linearization `D₀` of the quasilinear section `S` at `0`, and let
`c ∈ Lᵖ` satisfy `2 ‖Q‖² Λ ‖c‖ < 1`, where `Λ = ‖e‖ (2 K + M B + N)`. Then there is a zero `x` of
`c + S` in the range of `Q` with `‖x‖ ≤ 2 ‖Q‖ ‖c‖`. For `b = ∂t w` and `c = F(w)`, the defect of an
approximate solution `w`, the map `w + ξ` with `ξ` the value of `x` solves `F(w + ξ) = 0`
weakly. -/
theorem exists_mem_range_norm_le_add_quasilinearSection_eq_zero [CompleteSpace X]
    (he : ∀ x : X, ∀ᵐ z ∂μ, ((x : Lp (V × V × V) p μ) z).1 = e x z)
    (hAc : Continuous (Function.uncurry A)) (hGc : Continuous (Function.uncurry G))
    (hA'c : Continuous (Function.uncurry A')) (hG'c : Continuous (Function.uncurry G'))
    (hw : AEStronglyMeasurable w μ) (hb : AEStronglyMeasurable b μ) (hbB : ∀ z, ‖b z‖ ≤ B)
    (hAC : ∀ z y, ‖A z y‖ ≤ C) (hA : ∀ z y, HasFDerivAt (A z) (A' z y) y)
    (hA'K : ∀ z y, ‖A' z y‖ ≤ K) (hA'L : ∀ z, LipschitzWith M (A' z))
    (hG : ∀ z y, HasFDerivAt (G z) (G' z y) y) (hG'K : ∀ z y, ‖G' z y‖ ≤ L)
    (hG'L : ∀ z, LipschitzWith N (G' z)) {Q : Lp V p μ →L[ℝ] X}
    (hQ : (quasilinearLinearization e A A' G' w b 0).comp Q = ContinuousLinearMap.id ℝ _)
    {c : Lp V p μ} (hc : 2 * ‖Q‖ ^ 2 * (‖e‖ * (2 * K + M * B + N)) * ‖c‖ < 1) :
    ∃ x ∈ range Q, ‖x‖ ≤ 2 * ‖Q‖ * ‖c‖ ∧ c + quasilinearSection e A G w b x = 0 := by
  have hB : 0 ≤ B := (norm_nonneg _).trans (hbB 0)
  obtain ⟨hf, hf'⟩ := hasFDerivAt_add_quasilinearSection_and_norm_sub_le he hAc hGc hA'c hG'c hw
    hb hbB hAC hA hA'K hA'L hG hG'K hG'L c
  obtain ⟨Λ, hΛ⟩ : ∃ Λ : ℝ≥0, (Λ : ℝ) = ‖e‖ * (2 * K + M * B + N) := ⟨⟨_, by positivity⟩, rfl⟩
  obtain ⟨x, hxQ, hx, hxc⟩ := exists_mem_range_norm_le_apply_eq_zero_of_norm_hasFDerivWithin_sub_le
    (f := fun x ↦ c + quasilinearSection e A G w b x)
    (f' := quasilinearLinearization e A A' G' w b) (Q := Q) (C := ‖Q‖₊)
    (L := Λ) (δ := 2 * ‖Q‖ * ‖c‖)
    (fun x _ ↦ (hf x).hasFDerivWithinAt) (fun x _ ↦ by simpa [hΛ] using hf' x)
    (fun y ↦ by simpa using DFunLike.congr_fun hQ y) Q.le_opNorm (by simp)
    (by simpa [hΛ] using hc)
  exact ⟨x, hxQ, by simpa using hx, hxc⟩

/-- **Uniqueness of the zeros near an approximate solution.** Under the hypotheses of
`TauCeti.exists_mem_range_norm_le_add_quasilinearSection_eq_zero`, without completeness of `X`,
two zeros of `c + S` in the range of the right inverse `Q` of `D₀`, both of norm at most `r` with
`‖Q‖ Λ r < 1`, where `Λ = ‖e‖ (2 K + M B + N)`, coincide. -/
theorem eq_of_add_quasilinearSection_eq_zero
    (he : ∀ x : X, ∀ᵐ z ∂μ, ((x : Lp (V × V × V) p μ) z).1 = e x z)
    (hAc : Continuous (Function.uncurry A)) (hGc : Continuous (Function.uncurry G))
    (hA'c : Continuous (Function.uncurry A')) (hG'c : Continuous (Function.uncurry G'))
    (hw : AEStronglyMeasurable w μ) (hb : AEStronglyMeasurable b μ) (hbB : ∀ z, ‖b z‖ ≤ B)
    (hAC : ∀ z y, ‖A z y‖ ≤ C) (hA : ∀ z y, HasFDerivAt (A z) (A' z y) y)
    (hA'K : ∀ z y, ‖A' z y‖ ≤ K) (hA'L : ∀ z, LipschitzWith M (A' z))
    (hG : ∀ z y, HasFDerivAt (G z) (G' z y) y) (hG'K : ∀ z y, ‖G' z y‖ ≤ L)
    (hG'L : ∀ z, LipschitzWith N (G' z)) {Q : Lp V p μ →L[ℝ] X}
    (hQ : (quasilinearLinearization e A A' G' w b 0).comp Q = ContinuousLinearMap.id ℝ _)
    {c : Lp V p μ} {r : ℝ} (hr : ‖Q‖ * (‖e‖ * (2 * K + M * B + N)) * r < 1) {x y : X}
    (hx : ‖x‖ ≤ r) (hy : ‖y‖ ≤ r) (hxQ : x ∈ range Q)
    (hxc : c + quasilinearSection e A G w b x = 0) (hyQ : y ∈ range Q)
    (hyc : c + quasilinearSection e A G w b y = 0) : x = y := by
  have hB : 0 ≤ B := (norm_nonneg _).trans (hbB 0)
  obtain ⟨hf, hf'⟩ := hasFDerivAt_add_quasilinearSection_and_norm_sub_le he hAc hGc hA'c hG'c hw
    hb hbB hAC hA hA'K hA'L hG hG'K hG'L c
  obtain ⟨Λ, hΛ⟩ : ∃ Λ : ℝ≥0, (Λ : ℝ) = ‖e‖ * (2 * K + M * B + N) := ⟨⟨_, by positivity⟩, rfl⟩
  exact eq_of_apply_eq_zero_of_norm_hasFDerivWithin_sub_le
    (f := fun x ↦ c + quasilinearSection e A G w b x)
    (f' := quasilinearLinearization e A A' G' w b) (Q := Q) (C := ‖Q‖₊)
    (L := Λ) (δ := r)
    (fun x _ ↦ (hf x).hasFDerivWithinAt) (fun x _ ↦ by simpa [hΛ] using hf' x)
    (fun y ↦ by simpa using DFunLike.congr_fun hQ y) Q.le_opNorm le_rfl (by simpa [hΛ] using hr)
    hx hy hxQ hxc hyQ hyc

end TauCeti
