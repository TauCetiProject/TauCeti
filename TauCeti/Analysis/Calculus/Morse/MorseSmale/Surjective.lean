/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.Morse.MorseSmale.Perturbation
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
import TauCeti.Analysis.Calculus.BumpFunction.InnerProduct
import TauCeti.Analysis.Calculus.Gradient
import TauCeti.Analysis.Distribution.BumpComp
import TauCeti.Dynamics.Flow.Variational
import TauCeti.Analysis.Calculus.TangentCone.Basic

/-!
# Admissible perturbations move the end of an orbit in every direction transverse to it

Let `f` be a `C²` function with globally Lipschitz gradient on a finite-dimensional real inner
product space `E`, `φ` its negative-gradient flow, `x` a point that is not a critical point of `f`,
and `T > 0`. Perturbing `f` by functions vanishing near its critical points moves the point
`φ_T x` in every direction transverse to the orbit: there is a finite family `h` of admissible
perturbations such that the derivative at `s = 0` of `s ↦ φ^{f + ∑ sᵢ hᵢ}_T x`, together with
the flow direction `∇f(φ_T x)`, spans `E`.

The statement includes the flow direction among the spanning vectors. This costs nothing for the
intended application: the flow direction is tangent to both the unstable and the stable sets of
the critical points joined by the orbit, so this spanning statement is what the transversality of
these sets for a generic perturbation needs.

## Main results

* `TauCeti.exists_admissible_range_fderiv_perturbedFlow_sup_span_eq_top`.
* `TauCeti.exists_admissible_range_fderiv_perturbedFlow_sup_span_tangentConeAt_eq_top`: the range
  of the parameter derivative and the linear span of the tangent cone of any flow-invariant set
  containing `φ_T x` together span `E`. Where that set is a `C¹` submanifold near `φ_T x` (as the
  stable set of a nondegenerate critical point is) and the span is its tangent space, this is
  transversality of the parametrized flow to it.

## References

* M. Audin and M. Damian, *Morse Theory and Floer Homology*, Springer Universitext, 2014
  (transversality of the unstable and stable manifolds of a Morse function by perturbation).
* S. Smale, *On gradient dynamical systems*, Ann. of Math. **74** (1961), 199--206.
-/

public section

open Set Filter Topology InnerProductSpace
open scoped Gradient NNReal RealInnerProductSpace

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {f : E → ℝ} {K : ℝ≥0}


/-- A test perturbation `θ (ψ ∘ f) ⟪w, ·⟫`, with `θ` a bump whose closed support avoids the critical
points of `f`, is admissible. -/
private theorem isAdmissiblePerturbation_bump_mul (hfs : ContDiff ℝ 2 f) {z : E}
    (θ : ContDiffBump z) (hθ : ∀ p ∈ Metric.closedBall z θ.rOut, fderiv ℝ f p ≠ 0) {c : ℝ}
    (ψ : ContDiffBump c) (w : E) :
    IsAdmissiblePerturbation f fun p ↦ θ p * (ψ (f p) * ⟪w, p⟫) :=
  θ.isAdmissiblePerturbation_mul hθ
    ((ψ.contDiff.comp hfs).mul (innerSL ℝ w).contDiff)

/-- The integral `∫₀ᵀ Dφ_{-σ}(φ_σ x) (∇g(φ_σ x)) dσ` that an admissible perturbation `g` contributes
to the parameter derivative of the flow. -/
private noncomputable def contribution (f : E → ℝ) (hf : LipschitzWith K (∇ f)) (x : E) (T : ℝ)
    (g : E → ℝ) : E :=
  ∫ σ in (0 : ℝ)..T,
    fderiv ℝ (negativeGradientFlow f hf (-σ)) (negativeGradientFlow f hf σ x)
      (∇ g (negativeGradientFlow f hf σ x))

/-- **The contributions of admissible perturbations and the gradient span `E`.** -/
private theorem span_insert_gradient_range_contribution_eq_top (hfs : ContDiff ℝ 2 f)
    (hf : LipschitzWith K (∇ f)) {x : E} (hx : ∇ f x ≠ 0) {T : ℝ} (hT : 0 < T) :
    Submodule.span ℝ (insert (∇ f x)
      (range fun g : {g : E → ℝ // IsAdmissiblePerturbation f g} ↦
        contribution f hf x T g.1)) = ⊤ := by
  set φ := negativeGradientFlow f hf
  set N : ℝ → E →L[ℝ] E := fun σ ↦ fderiv ℝ (φ (-σ)) (φ σ x)
  have hφd : ∀ t, Differentiable ℝ (φ t) := differentiable_negativeGradientFlow_apply f hf hfs
  have hγ : Continuous fun σ ↦ φ σ x :=
    (contDiff_negativeGradientFlow f hf hfs).continuous.comp
      (continuous_id.prodMk continuous_const)
  have hN : Continuous N := continuous_fderiv_negativeGradientFlow_neg f hf hfs x
  by_contra hV
  obtain ⟨y, hyV, hy0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot
    fun h0 ↦ hV (Submodule.orthogonal_eq_bot_iff.1 h0)
  have hyx : ⟪∇ f x, y⟫ = 0 :=
    Submodule.inner_right_of_mem_orthogonal (Submodule.subset_span (mem_insert _ _)) hyV
  have hyk : ∀ g : {g : E → ℝ // IsAdmissiblePerturbation f g},
      ⟪contribution f hf x T g.1, y⟫ = 0 := fun g ↦
    Submodule.inner_right_of_mem_orthogonal
      (Submodule.subset_span (mem_insert_of_mem _ (mem_range_self g))) hyV
  -- The covectors `⟪y, N σ ·⟫`, as vectors.
  set m : ℝ → E := fun σ ↦ ContinuousLinearMap.adjoint (N σ) y
  have hm : Continuous m :=
    ((ContinuousLinearMap.adjoint (𝕜 := ℝ)).continuous.comp hN).clm_apply continuous_const
  -- They annihilate the flow direction.
  have hmgrad : ∀ σ, fderiv ℝ f (φ σ x) (m σ) = 0 := fun σ ↦ by
    have hNg : N σ (∇ f (φ σ x)) = ∇ f x := by
      have := fderiv_negativeGradientFlow_apply_gradient f hf hfs (-σ) (φ σ x)
      rwa [← Flow.map_add, neg_add_cancel, Flow.map_zero_apply] at this
    rw [← inner_gradient_left, ContinuousLinearMap.adjoint_inner_right, hNg, hyx]
  -- A bump around a point of the orbit, inside a region without critical points.
  set σ₀ := T / 2 with hσdef
  have hσ₀ : σ₀ ∈ Ioo 0 T := ⟨by rw [hσdef]; positivity, by rw [hσdef]; linarith⟩
  set z := φ σ₀ x
  have hgradc : Continuous (∇ f) := (hfs.gradient_right (m := 1) (by norm_num)).continuous
  obtain ⟨ρ, hρ, hρz⟩ := Metric.eventually_nhds_iff.1
    (hgradc.continuousAt.eventually_ne
      ((gradient_negativeGradientFlow_eq_zero_iff f hf x σ₀).not.2 hx))
  let θ : ContDiffBump z := ⟨ρ / 4, ρ / 2, by positivity, by linarith⟩
  have hθr : θ.rOut = ρ / 2 := rfl
  have hθz : θ z = 1 := θ.one_of_mem_closedBall (Metric.mem_closedBall_self θ.rIn_pos.le)
  have hθcrit : ∀ p ∈ Metric.closedBall z θ.rOut, fderiv ℝ f p ≠ 0 := fun p hp hp0 ↦
    hρz (Metric.mem_closedBall.1 hp |>.trans_lt (by rw [hθr]; linarith)) (by simp [gradient, hp0])
  have hθ'z : fderiv ℝ θ z = 0 := by
    rw [θ.eventuallyEq_one.fderiv_eq]
    exact fderiv_const_apply _
  -- The test perturbations `θ (ψ ∘ f) ⟪w, ·⟫`.
  have hkey : ∀ w : E, ∀ ψ : ContDiffBump (f z),
      ∫ σ in (0 : ℝ)..T, (θ (φ σ x) * ⟪w, m σ⟫ + ⟪w, φ σ x⟫ * fderiv ℝ θ (φ σ x) (m σ)) *
        ψ (f (φ σ x)) = 0 := by
    intro w ψ
    set g : E → ℝ := fun p ↦ θ p * (ψ (f p) * ⟪w, p⟫)
    have hg : IsAdmissiblePerturbation f g := isAdmissiblePerturbation_bump_mul hfs θ hθcrit ψ w
    have hk := hyk ⟨g, hg⟩
    have hint : IntervalIntegrable (fun σ ↦ N σ (∇ g (φ σ x))) MeasureTheory.volume 0 T :=
      (hN.clm_apply (((hg.contDiff.gradient_right (m := 1) (by norm_num)).continuous).comp
        hγ)).intervalIntegrable 0 T
    have hcomm : ∫ σ in (0 : ℝ)..T, ⟪y, N σ (∇ g (φ σ x))⟫ =
        ⟪y, ∫ σ in (0 : ℝ)..T, N σ (∇ g (φ σ x))⟫ := by
      simpa using ContinuousLinearMap.intervalIntegral_comp_comm (innerSL ℝ y) hint
    have hk' : ⟪y, ∫ σ in (0 : ℝ)..T, N σ (∇ g (φ σ x))⟫ = 0 := by
      rw [real_inner_comm]
      exact hk
    refine Eq.trans (intervalIntegral.integral_congr (μ := MeasureTheory.volume)
      (g := fun σ ↦ ⟪y, N σ (∇ g (φ σ x))⟫) fun σ _ ↦ ?_) (hcomm.trans hk')
    dsimp only
    symm
    rw [real_inner_comm _ y, ← ContinuousLinearMap.adjoint_inner_right, inner_gradient_left,
      θ.fderiv_mul_comp_mul_inner_apply ψ w
        ((hfs.differentiable (by norm_num)) _) (hmgrad σ)]
  -- Hence `⟪w, m σ₀⟫ = 0` for every `w`.
  have hm0 : m σ₀ = 0 := by
    have hF : Continuous fun σ ↦ f (φ σ x) := hfs.continuous.comp hγ
    have h0 := eq_zero_of_forall_intervalIntegral_mul_contDiffBump_comp
      (a := fun σ ↦ θ (φ σ x) * ⟪m σ₀, m σ⟫ + ⟪m σ₀, φ σ x⟫ * fderiv ℝ θ (φ σ x) (m σ))
      ((θ.continuous.comp hγ).mul (continuous_const.inner hm) |>.add
        ((continuous_const.inner hγ).mul
          ((((θ.contDiff (n := 1)).continuous_fderiv one_ne_zero).comp hγ).clm_apply
            hm))).continuousOn
      hF.continuousOn ((IsIntegralCurve.strictAnti_comp_neg_gradient
        ((isNegativeGradient_negativeGradientFlow f hf).isIntegralCurve x)
        (fun _ ↦ (hfs.differentiable (by norm_num)) _)
        (fun t ↦ (gradient_negativeGradientFlow_eq_zero_iff f hf x t).not.2 hx)).strictAntiOn _)
      hσ₀ (hkey (m σ₀))
    have hθz' : θ (φ σ₀ x) = 1 := hθz
    have hθ'z' : fderiv ℝ θ (φ σ₀ x) = 0 := hθ'z
    simpa [hθz', hθ'z'] using h0
  -- And so `y = 0`.
  apply hy0
  have hNM : ∀ v, N σ₀ (fderiv ℝ (φ σ₀) x v) = v :=
    Flow.fderiv_neg_apply_fderiv (hφd _ _) (hφd σ₀ x)
  have := ContinuousLinearMap.adjoint_inner_right (N σ₀) (fderiv ℝ (φ σ₀) x y) y
  rw [hNM] at this
  rw [← inner_self_eq_zero (𝕜 := ℝ), ← this]
  simp [m, hm0]

/-- **Admissible perturbations move the end of an orbit in every direction transverse to it.** For
a point `x` that is not critical and a time `T > 0`, there is a finite family `h` of admissible
perturbations of `f` such that the derivative at the parameter `0` of
`s ↦ φ^{f + ∑ sᵢ hᵢ}_T x`, together with the flow direction `∇f(φ_T x)`, spans `E`. -/
theorem exists_admissible_range_fderiv_perturbedFlow_sup_span_eq_top (hfs : ContDiff ℝ 2 f)
    (hf : LipschitzWith K (∇ f)) {x : E} (hx : ∇ f x ≠ 0) {T : ℝ} (hT : 0 < T) :
    ∃ (n : ℕ) (h : Fin n → E → ℝ) (hh : ∀ i, IsAdmissiblePerturbation f (h i)),
      LinearMap.range (((ContinuousLinearMap.fst ℝ E (EuclideanSpace ℝ (Fin n))).comp
          ((fderiv ℝ (perturbedFlow f h hf (fun i ↦ (hh i).contDiff)
              (fun i ↦ (hh i).hasCompactSupport) T) (x, 0)).comp
            (ContinuousLinearMap.inr ℝ E (EuclideanSpace ℝ (Fin n))))) :
            EuclideanSpace ℝ (Fin n) →ₗ[ℝ] E) ⊔
        (ℝ ∙ ∇ f (negativeGradientFlow f hf T x)) = ⊤ := by
  set φ := negativeGradientFlow f hf
  set S := range fun g : {g : E → ℝ // IsAdmissiblePerturbation f g} ↦ contribution f hf x T g.1
  obtain ⟨v, hvS, hvspan, -⟩ := Submodule.exists_fun_fin_finrank_span_eq ℝ S
  choose g hg using hvS
  refine ⟨_, fun i ↦ (g i).1, fun i ↦ (g i).2, ?_⟩
  have hgc : ∀ i, ContDiff ℝ 2 (g i).1 := fun i ↦ (g i).2.contDiff
  have hgs : ∀ i, HasCompactSupport (g i).1 := fun i ↦ (g i).2.hasCompactSupport
  set MT := fderiv ℝ (φ T) x
  set L : EuclideanSpace ℝ (Fin (Module.finrank ℝ (Submodule.span ℝ S))) →ₗ[ℝ] E :=
    ContinuousLinearMap.toLinearMap (((ContinuousLinearMap.fst ℝ E _).comp
      ((fderiv ℝ (perturbedFlow f (fun i ↦ (g i).1) hf hgc hgs T) (x, 0)).comp
        (ContinuousLinearMap.inr ℝ E _))) :
      EuclideanSpace ℝ (Fin (Module.finrank ℝ (Submodule.span ℝ S))) →L[ℝ] E)
  have hφd : ∀ t, Differentiable ℝ (φ t) := differentiable_negativeGradientFlow_apply f hf hfs
  -- `Dφ_T(x)` maps the contributions of the family into the range of the parameter derivative.
  have hv : ∀ i, MT (v i) ∈ LinearMap.range L := fun i ↦ by
    refine ⟨-EuclideanSpace.single i 1, ?_⟩
    have hD := fst_fderiv_perturbedFlow_apply_eq_neg_integral hfs hf hgc hgs x
      (-EuclideanSpace.single i 1) T
    have hsum : ∀ p, ∑ j, (-EuclideanSpace.single i (1 : ℝ)) j • ∇ (g j).1 p = -∇ (g i).1 p :=
      fun p ↦ by simp
    calc L (-EuclideanSpace.single i 1)
        = (fderiv ℝ (perturbedFlow f (fun i ↦ (g i).1) hf hgc hgs T) (x, 0)
            (0, -EuclideanSpace.single i 1)).1 := by simp [L]
      _ = MT (v i) := by
        rw [hD, ← hg i]
        simp only [hsum, map_neg, intervalIntegral.integral_neg, neg_neg, contribution, MT, φ]
  have hS : Submodule.span ℝ S ≤ (LinearMap.range L).comap (MT : E →ₗ[ℝ] E) :=
    hvspan.symm.le.trans (Submodule.span_le.2 (by rintro _ ⟨i, rfl⟩; exact hv i))
  have hgrad : MT (∇ f x) = ∇ f (φ T x) := fderiv_negativeGradientFlow_apply_gradient f hf hfs T x
  have htop := span_insert_gradient_range_contribution_eq_top hfs hf hx hT
  refine top_unique fun w _ ↦ ?_
  have hw : fderiv ℝ (φ (-T)) (φ T x) w ∈ Submodule.span ℝ (insert (∇ f x) S) := by
    rw [htop]
    exact Submodule.mem_top
  rw [Submodule.span_insert, Submodule.mem_sup] at hw
  obtain ⟨a, ha, b, hb, hab⟩ := hw
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 ha
  have hwab : w = MT b + c • ∇ f (φ T x) := by
    rw [← hgrad, ← map_smul, ← map_add, add_comm, hab]
    exact (Flow.fderiv_apply_fderiv_neg (hφd _ _) (hφd T x) w).symm
  rw [hwab]
  exact Submodule.add_mem_sup (hS hb) (Submodule.smul_mem _ c (Submodule.mem_span_singleton_self _))

/-- **Spanning with the tangent cone of an invariant set.** For a point `x` that is not critical,
a time `T > 0` and a set `S` invariant under the negative-gradient flow and containing `φ_T x` (for
instance the stable or unstable set of a point), there is a finite family `h` of admissible
perturbations of `f`, depending on `x` and `T`, such that the range of the derivative at the
parameter `0` of `s ↦ φ^{f + ∑ sᵢ hᵢ}_T x` and the linear span of the tangent cone of `S` at
`φ_T x` together span `E`. The flow direction lies in that tangent cone. When `S` is a `C¹`
submanifold near `φ_T x` and this span is its tangent space, this says the parametrized flow is
transverse to `S` at `(0, x)` through the parameter directions alone. -/
theorem exists_admissible_range_fderiv_perturbedFlow_sup_span_tangentConeAt_eq_top
    (hfs : ContDiff ℝ 2 f) (hf : LipschitzWith K (∇ f)) {x : E} (hx : ∇ f x ≠ 0) {T : ℝ}
    (hT : 0 < T) {S : Set E} (hS : IsInvariant (negativeGradientFlow f hf) S)
    (hTS : negativeGradientFlow f hf T x ∈ S) :
    ∃ (n : ℕ) (h : Fin n → E → ℝ) (hh : ∀ i, IsAdmissiblePerturbation f (h i)),
      LinearMap.range (((ContinuousLinearMap.fst ℝ E (EuclideanSpace ℝ (Fin n))).comp
          ((fderiv ℝ (perturbedFlow f h hf (fun i ↦ (hh i).contDiff)
              (fun i ↦ (hh i).hasCompactSupport) T) (x, 0)).comp
            (ContinuousLinearMap.inr ℝ E (EuclideanSpace ℝ (Fin n))))) :
            EuclideanSpace ℝ (Fin n) →ₗ[ℝ] E) ⊔
        Submodule.span ℝ (tangentConeAt ℝ S (negativeGradientFlow f hf T x)) = ⊤ := by
  obtain ⟨n, h, hh, H⟩ := exists_admissible_range_fderiv_perturbedFlow_sup_span_eq_top hfs hf hx hT
  refine ⟨n, h, hh, top_unique (H ▸ sup_le_sup_left ?_ _)⟩
  set y := negativeGradientFlow f hf T x
  -- The velocity of the orbit of `y`, which stays in `S`, is tangent to `S`.
  have hmem : -∇ f y ∈ tangentConeAt ℝ S y :=
    neg_gradient_mem_tangentConeAt_of_isInvariant f hf hS hTS
  refine Submodule.span_le.2 (Set.singleton_subset_iff.2 ?_)
  simpa using Submodule.neg_mem _ (Submodule.subset_span hmem)

end TauCeti
