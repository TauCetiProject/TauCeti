/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.Morse.BirthDeath
public import TauCeti.Analysis.Calculus.Morse.Fredholm
import TauCeti.Analysis.Normed.Group.Basic
import TauCeti.Analysis.Normed.Lp.ProdLp

/-!
# Fredholm regularity of linearized trajectory operators in the birth–death model

For `s > 0`, this file establishes the `W^{1,2} → L²` Fredholm regularity of the linearized
trajectory operator `D_γ ξ = ξ' + Hess f(γ) ξ` along any newborn connecting trajectory of the
birth–death model. Surjectivity and index-`1` Fredholm regularity of `D_γ` establish transversality
of the unique newborn connecting trajectory in a birth–death bifurcation, supplying the analytic
input for Morse-complex cancellation and continuation.

* **In one dimension (`TauCeti.birthDeathPotential s`):** along any negative gradient trajectory `γ`
  from `-√s` to `√s`, `D_γ` is Fredholm of index `1`, surjective, with one-dimensional kernel
  spanned by `deriv γ`, trivial kernel for `D_{-Hess}` (hence injective formal adjoint
  `-d/dt + Hess f(γ)`), and bijective constant operators at `±√s`.
* **With a transverse function `g : F → ℝ`:** on a finite-dimensional real inner product space `F`,
  above a nondegenerate critical point `y` of `g`, every negative gradient trajectory `z` of
  `separatedSum (birthDeathPotential s) g` from `(-√s, y)` to `(√s, y)` (along which `g` is
  differentiable in the second coordinate) stays at `y` in `F`. Consequently the square-integrable
  solutions of `v' + Hess(z) v = 0` have initial-value space `ℝ ∙ (1, 0)`, and `D_z` is Fredholm of
  index `1`, surjective, with kernel spanned by `deriv z`, trivial kernel for `D_{-Hess}`, and
  bijective constant operators at `(-√s, y)` and `(√s, y)`.

## Main declarations

* `TauCeti.isFredholm_trajectoryOperator_birthDeathPotential`,
  `TauCeti.index_trajectoryOperator_birthDeathPotential`,
  `TauCeti.finrank_ker_trajectoryOperator_birthDeathPotential_eq_one`,
  `TauCeti.exists_ker_trajectoryOperator_birthDeathPotential_eq_span`,
  `TauCeti.surjective_trajectoryOperator_birthDeathPotential`,
  `TauCeti.ker_trajectoryOperator_neg_birthDeathPotential_eq_bot`,
  `TauCeti.squareIntegrableSolutions_neg_hessianOperator_birthDeathPotential_eq_bot`,
  `TauCeti.bijective_trajectoryOperator_birthDeathPotential_neg_sqrt`,
  `TauCeti.bijective_trajectoryOperator_birthDeathPotential_sqrt`.
* `TauCeti.squareIntegrableSolutions_hessianOperator_separatedSum_birthDeathPotential_eq_span`,
  `TauCeti.isFredholm_trajectoryOperator_separatedSum_birthDeathPotential`,
  `TauCeti.index_trajectoryOperator_separatedSum_birthDeathPotential`,
  `TauCeti.finrank_ker_trajectoryOperator_separatedSum_birthDeathPotential_eq_one`,
  `TauCeti.ker_trajectoryOperator_neg_separatedSum_birthDeathPotential_eq_bot`,
  `TauCeti.squareIntegrableSolutions_neg_hessianOperator_separatedSum_birthDeathPotential_eq_bot`,
  `TauCeti.surjective_trajectoryOperator_separatedSum_birthDeathPotential`,
  `TauCeti.exists_ker_trajectoryOperator_separatedSum_birthDeathPotential_eq_span`,
  `TauCeti.bijective_trajectoryOperator_separatedSum_birthDeathPotential_neg_sqrt`,
  `TauCeti.bijective_trajectoryOperator_separatedSum_birthDeathPotential_sqrt`.

## References

* J. Cerf, *La stratification naturelle des espaces de fonctions différentiables réelles et le
  théorème de la pseudo-isotopie*, Publ. Math. IHÉS **39** (1970), 5–173.
* M. Schwarz, *Morse Homology*, Progress in Mathematics **111**, Birkhäuser, 1993, Chapter 2.
* M. Audin and M. Damian, *Morse Theory and Floer Homology*, Springer Universitext, 2014,
  Chapter 10.
-/

public section

open Filter InnerProductSpace MeasureTheory Set TopologicalSpace
open scoped ENNReal Gradient Topology

namespace TauCeti

/-! ### One-dimensional Fredholm regularity -/

section OneDimensional

open TauCeti.WeakDerivStep

variable {s : ℝ} {γ : ℝ → ℝ}
  {AL : Lp (ℝ →L[ℝ] ℝ) ∞ (volume.restrict ((⊤ : Opens ℝ) : Set ℝ))}

/-- Along a negative gradient trajectory of `birthDeathPotential s` (`s > 0`) from `-√s` to `√s`,
the linearized operator `ξ ↦ ξ' + 2 γ ξ` from `W^{1,2}(ℝ, ℝ)` to `L²(ℝ, ℝ)` is Fredholm. -/
theorem isFredholm_trajectoryOperator_birthDeathPotential (hs : 0 < s)
    (hγ : IsIntegralCurve γ (fun _ x ↦ -∇ (birthDeathPotential s) x))
    (hbot : Tendsto γ atBot (𝓝 (-√s))) (htop : Tendsto γ atTop (𝓝 √s))
    (hAL : AL =ᵐ[volume.restrict ((⊤ : Opens ℝ) : Set ℝ)]
      fun t ↦ hessianOperator (birthDeathPotential s) (γ t)) :
    (trajectoryOperator (p := 2) AL).IsFredholm :=
  hγ.isFredholm_trajectoryOperator_hessianOperator (contDiff_birthDeathPotential s)
    (isNondegenerateCriticalPoint_birthDeathPotential_neg_sqrt hs)
    (isNondegenerateCriticalPoint_birthDeathPotential_sqrt hs) hbot htop hAL

/-- **The linearized birth–death trajectory operator has Fredholm index `1`.** -/
theorem index_trajectoryOperator_birthDeathPotential (hs : 0 < s)
    (hγ : IsIntegralCurve γ (fun _ x ↦ -∇ (birthDeathPotential s) x))
    (hbot : Tendsto γ atBot (𝓝 (-√s))) (htop : Tendsto γ atTop (𝓝 √s))
    (hAL : AL =ᵐ[volume.restrict ((⊤ : Opens ℝ) : Set ℝ)]
      fun t ↦ hessianOperator (birthDeathPotential s) (γ t)) :
    (trajectoryOperator (p := 2) AL).index = 1 := by
  rw [hγ.index_trajectoryOperator_hessianOperator (contDiff_birthDeathPotential s)
    (isNondegenerateCriticalPoint_birthDeathPotential_neg_sqrt hs)
    (isNondegenerateCriticalPoint_birthDeathPotential_sqrt hs) hbot htop hAL,
    morseIndex_birthDeathPotential_neg_sqrt hs, morseIndex_birthDeathPotential_sqrt hs]
  simp

/-- **The kernel of the linearized birth–death trajectory operator is one-dimensional.** -/
theorem finrank_ker_trajectoryOperator_birthDeathPotential_eq_one (hs : 0 < s)
    (hγ : IsIntegralCurve γ (fun _ x ↦ -∇ (birthDeathPotential s) x))
    (hbot : Tendsto γ atBot (𝓝 (-√s))) (htop : Tendsto γ atTop (𝓝 √s))
    (hAL : AL =ᵐ[volume.restrict ((⊤ : Opens ℝ) : Set ℝ)]
      fun t ↦ hessianOperator (birthDeathPotential s) (γ t)) :
    Module.finrank ℝ (trajectoryOperator (p := 2) AL).ker = 1 :=
  hγ.finrank_ker_trajectoryOperator_hessianOperator_eq_one (Module.finrank_self ℝ)
    (contDiff_birthDeathPotential s) hbot htop (by linarith [Real.sqrt_pos.2 hs]) hAL

/-- **The kernel of the linearized birth–death trajectory operator is spanned by `γ'`.** -/
theorem exists_ker_trajectoryOperator_birthDeathPotential_eq_span (hs : 0 < s)
    (hγ : IsIntegralCurve γ (fun _ x ↦ -∇ (birthDeathPotential s) x))
    (hbot : Tendsto γ atBot (𝓝 (-√s))) (htop : Tendsto γ atTop (𝓝 √s))
    (hAL : AL =ᵐ[volume.restrict ((⊤ : Opens ℝ) : Set ℝ)]
      fun t ↦ hessianOperator (birthDeathPotential s) (γ t)) :
    ∃ u : WeakDerivStep volume ⊤ 2
        (ContinuousLinearMap.id ℝ (Lp ℝ 2 (volume.restrict ((⊤ : Opens ℝ) : Set ℝ)))),
      ⇑(prev (ContinuousLinearMap.id ℝ (Lp ℝ 2 (volume.restrict ((⊤ : Opens ℝ) : Set ℝ)))) u)
          =ᵐ[volume.restrict ((⊤ : Opens ℝ) : Set ℝ)] deriv γ ∧
        (trajectoryOperator (p := 2) AL).ker = ℝ ∙ u :=
  hγ.exists_ker_trajectoryOperator_hessianOperator_eq_span (Module.finrank_self ℝ)
    (contDiff_birthDeathPotential s) hbot htop (by linarith [Real.sqrt_pos.2 hs]) hAL

/-- **Transversality of the newborn connecting trajectory in one dimension.** -/
theorem surjective_trajectoryOperator_birthDeathPotential (hs : 0 < s)
    (hγ : IsIntegralCurve γ (fun _ x ↦ -∇ (birthDeathPotential s) x))
    (hbot : Tendsto γ atBot (𝓝 (-√s))) (htop : Tendsto γ atTop (𝓝 √s))
    (hAL : AL =ᵐ[volume.restrict ((⊤ : Opens ℝ) : Set ℝ)]
      fun t ↦ hessianOperator (birthDeathPotential s) (γ t)) :
    Function.Surjective (trajectoryOperator (p := 2) AL) :=
  (hγ.surjective_trajectoryOperator_hessianOperator_iff (Module.finrank_self ℝ)
    (contDiff_birthDeathPotential s)
    (isNondegenerateCriticalPoint_birthDeathPotential_neg_sqrt hs)
    (isNondegenerateCriticalPoint_birthDeathPotential_sqrt hs) hbot htop
    (by linarith [Real.sqrt_pos.2 hs]) hAL).2
    (by rw [morseIndex_birthDeathPotential_neg_sqrt hs, morseIndex_birthDeathPotential_sqrt hs])

/-- **Triviality of the kernel of `D_{-Hess}` in one dimension** (formal-adjoint injectivity). -/
theorem ker_trajectoryOperator_neg_birthDeathPotential_eq_bot (hs : 0 < s)
    (hγ : IsIntegralCurve γ (fun _ x ↦ -∇ (birthDeathPotential s) x))
    (hbot : Tendsto γ atBot (𝓝 (-√s))) (htop : Tendsto γ atTop (𝓝 √s))
    (hAL : AL =ᵐ[volume.restrict ((⊤ : Opens ℝ) : Set ℝ)]
      fun t ↦ hessianOperator (birthDeathPotential s) (γ t)) :
    (trajectoryOperator (p := 2) (-AL)).ker = ⊥ := by
  have hadj : ∀ᵐ t ∂volume.restrict ((⊤ : Opens ℝ) : Set ℝ),
      AL t = ContinuousLinearMap.adjoint (AL t) := by
    filter_upwards [hAL] with t ht
    rw [ht]
    exact (contDiff_birthDeathPotential s).contDiffAt.isSelfAdjoint_hessianOperator.isSymmetric
      |>.clm_adjoint_eq.symm
  exact (surjective_trajectoryOperator_iff_ker_neg_eq_bot hadj
    (isFredholm_trajectoryOperator_birthDeathPotential hs hγ hbot htop hAL).isClosed_range).1
    (surjective_trajectoryOperator_birthDeathPotential hs hγ hbot htop hAL)

/-- Along any negative gradient trajectory of `birthDeathPotential s` (`s > 0`) from `-√s` to `√s`,
the adjoint ODE `v' - 2 γ v = 0` has no nonzero square-integrable solution. -/
theorem squareIntegrableSolutions_neg_hessianOperator_birthDeathPotential_eq_bot (hs : 0 < s)
    (hγ : IsIntegralCurve γ (fun _ x ↦ -∇ (birthDeathPotential s) x))
    (hbot : Tendsto γ atBot (𝓝 (-√s))) (htop : Tendsto γ atTop (𝓝 √s)) :
    squareIntegrableSolutions (fun t ↦ -hessianOperator (birthDeathPotential s) (γ t)) = ⊥ := by
  have hmem : MemLp (fun t ↦ hessianOperator (birthDeathPotential s) (γ t)) ∞
      (volume.restrict ((⊤ : Opens ℝ) : Set ℝ)) :=
    (contDiff_birthDeathPotential s).memLp_top_hessianOperator_comp hγ.continuous hbot htop _
  set AL := hmem.toLp _
  have hAL : AL =ᵐ[volume.restrict ((⊤ : Opens ℝ) : Set ℝ)]
      fun t ↦ hessianOperator (birthDeathPotential s) (γ t) := hmem.coeFn_toLp
  have hAneg : Continuous fun t ↦ -hessianOperator (birthDeathPotential s) (γ t) :=
    (((contDiff_birthDeathPotential s (n := 2)).contDiff_hessianOperator (m := 0)
      (by norm_num)).continuous.comp hγ.continuous).neg
  have hALneg : (-AL : Lp (ℝ →L[ℝ] ℝ) ∞ (volume.restrict ((⊤ : Opens ℝ) : Set ℝ)))
      =ᵐ[volume.restrict ((⊤ : Opens ℝ) : Set ℝ)]
      fun t ↦ -hessianOperator (birthDeathPotential s) (γ t) := by
    filter_upwards [Lp.coeFn_neg AL, hAL] with t hneg ht
    simp only [hneg, Pi.neg_apply, ht]
  exact (ker_trajectoryOperator_eq_bot_iff hAneg (-AL) hALneg).1
    (ker_trajectoryOperator_neg_birthDeathPotential_eq_bot hs hγ hbot htop hAL)

/-- At the constant trajectory `-√s` (`s > 0`), the linearized operator is bijective. -/
theorem bijective_trajectoryOperator_birthDeathPotential_neg_sqrt (hs : 0 < s)
    (hAL : AL =ᵐ[volume.restrict ((⊤ : Opens ℝ) : Set ℝ)]
      fun _ ↦ hessianOperator (birthDeathPotential s) (-√s)) :
    Function.Bijective (trajectoryOperator (p := 2) AL) :=
  (isNondegenerateCriticalPoint_birthDeathPotential_neg_sqrt
    hs).bijective_trajectoryOperator_hessianOperator hAL

/-- At the constant trajectory `√s` (`s > 0`), the linearized operator is bijective. -/
theorem bijective_trajectoryOperator_birthDeathPotential_sqrt (hs : 0 < s)
    (hAL : AL =ᵐ[volume.restrict ((⊤ : Opens ℝ) : Set ℝ)]
      fun _ ↦ hessianOperator (birthDeathPotential s) √s) :
    Function.Bijective (trajectoryOperator (p := 2) AL) :=
  (isNondegenerateCriticalPoint_birthDeathPotential_sqrt
    hs).bijective_trajectoryOperator_hessianOperator hAL

end OneDimensional

/-! ### Fredholm regularity with a transverse function -/

section SeparatedSum

open TauCeti.WeakDerivStep

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  {s : ℝ} {g : F → ℝ} {y : F} {z : ℝ → WithLp 2 (ℝ × F)}
  {AL : Lp (WithLp 2 (ℝ × F) →L[ℝ] WithLp 2 (ℝ × F)) ∞ (volume.restrict ((⊤ : Opens ℝ) : Set ℝ))}

/-- At any point `(x, y)` where `g` is `C²` at `y`, the Hessian operator of
`separatedSum (birthDeathPotential s) g` splits as the block sum `(2 x) • P₁ + P₂`. -/
private theorem hessianOperator_separatedSum_birthDeathPotential_eq
    (hy : ContDiffAt ℝ 2 g y) (x : ℝ) :
    hessianOperator (separatedSum (birthDeathPotential s) g) (WithLp.toLp 2 (x, y)) =
      (2 * x) • ((ContinuousLinearMap.id ℝ ℝ).withLpProdMap 2 (0 : F →L[ℝ] F)) +
        (0 : ℝ →L[ℝ] ℝ).withLpProdMap 2 (hessianOperator g y) := by
  ext w
  rw [hessianOperator_separatedSum_apply (contDiff_birthDeathPotential s).contDiffAt hy,
    hessianOperator_real, iteratedDeriv_two_birthDeathPotential]
  refine (WithLp.ext_iff 2).2 (Prod.ext ?_ ?_) <;> simp

/-- Along a connecting trajectory `z` of `separatedSum (birthDeathPotential s) g` from `(-√s, y)`
to `(√s, y)` above a nondegenerate critical point `y` of `g`, the transverse component stays at `y`,
and the Hessian family along `z` is continuous and pointwise symmetric with invertible limits at
`±∞`. -/
private theorem trajectory_data_separatedSum_birthDeathPotential (hs : 0 < s)
    (hg : ∀ t, DifferentiableAt ℝ g (z t).snd) (hy : IsNondegenerateCriticalPoint g y)
    (hz : IsIntegralCurve z (fun _ w ↦ -∇ (separatedSum (birthDeathPotential s) g) w))
    (hbot : Tendsto z atBot (𝓝 (WithLp.toLp 2 (-√s, y))))
    (htop : Tendsto z atTop (𝓝 (WithLp.toLp 2 (√s, y)))) :
    IsIntegralCurve (fun t ↦ (z t).fst) (fun _ x ↦ -∇ (birthDeathPotential s) x) ∧
      (∀ t, (z t).snd = y) ∧
      Continuous (fun t ↦ hessianOperator (separatedSum (birthDeathPotential s) g) (z t)) ∧
      (∀ t,
        (hessianOperator (separatedSum (birthDeathPotential s) g) (z t)).toLinearMap.IsSymmetric) ∧
      (∃ α > 0,
        (∀ v, α * ‖v‖ ≤ ‖hessianOperator (separatedSum (birthDeathPotential s) g)
          (WithLp.toLp 2 (-√s, y)) v‖) ∧
        (∀ v, α * ‖v‖ ≤ ‖hessianOperator (separatedSum (birthDeathPotential s) g)
          (WithLp.toLp 2 (√s, y)) v‖)) ∧
      Tendsto (fun t ↦ hessianOperator (separatedSum (birthDeathPotential s) g) (z t)) atBot
        (𝓝 (hessianOperator (separatedSum (birthDeathPotential s) g) (WithLp.toLp 2 (-√s, y)))) ∧
      Tendsto (fun t ↦ hessianOperator (separatedSum (birthDeathPotential s) g) (z t)) atTop
        (𝓝 (hessianOperator (separatedSum (birthDeathPotential s) g) (WithLp.toLp 2 (√s, y)))) := by
  obtain ⟨h₁, h₂⟩ := (isIntegralCurve_separatedSum_iff
    (fun _ ↦ differentiable_birthDeathPotential s _) hg).1 hz
  have h₁bot : Tendsto (fun t ↦ (z t).fst) atBot (𝓝 (-√s)) :=
    ((WithLp.continuous_fst 2 ℝ F).tendsto' _ _ rfl).comp hbot
  have h₁top : Tendsto (fun t ↦ (z t).fst) atTop (𝓝 √s) :=
    ((WithLp.continuous_fst 2 ℝ F).tendsto' _ _ rfl).comp htop
  have h₂bot : Tendsto (fun t ↦ (z t).snd) atBot (𝓝 y) :=
    ((WithLp.continuous_snd 2 ℝ F).tendsto' _ _ rfl).comp hbot
  have h₂top : Tendsto (fun t ↦ (z t).snd) atTop (𝓝 y) :=
    ((WithLp.continuous_snd 2 ℝ F).tendsto' _ _ rfl).comp htop
  have hsnd : ∀ t, (z t).snd = y :=
    congrFun (h₂.eq_const_of_tendsto hg hy.contDiffAt.continuousAt h₂bot h₂top)
  have hz_eq : ∀ t, z t = WithLp.toLp 2 ((z t).fst, y) := fun t ↦
    (WithLp.ext_iff 2).2 (Prod.ext rfl (hsnd t))
  let P₁ : WithLp 2 (ℝ × F) →L[ℝ] WithLp 2 (ℝ × F) :=
    (ContinuousLinearMap.id ℝ ℝ).withLpProdMap 2 (0 : F →L[ℝ] F)
  let P₂ : WithLp 2 (ℝ × F) →L[ℝ] WithLp 2 (ℝ × F) :=
    (0 : ℝ →L[ℝ] ℝ).withLpProdMap 2 (hessianOperator g y)
  have hH_eq : (fun t ↦ hessianOperator (separatedSum (birthDeathPotential s) g) (z t)) =
      fun t ↦ (2 * (z t).fst) • P₁ + P₂ := funext fun t ↦ by
    conv_lhs => rw [hz_eq t, hessianOperator_separatedSum_birthDeathPotential_eq hy.contDiffAt]
  have hsym : ∀ t,
      (hessianOperator (separatedSum (birthDeathPotential s) g) (z t)).toLinearMap.IsSymmetric := by
    intro t
    have hcd : ContDiffAt ℝ 2 (separatedSum (birthDeathPotential s) g) (z t) := by
      rw [hz_eq t, separatedSum_eq_comp]
      exact (((contDiff_birthDeathPotential s).contDiffAt.comp _ contDiffAt_fst).add
        (hy.contDiffAt.comp _ contDiffAt_snd)).comp _
        (WithLp.prodContinuousLinearEquiv 2 ℝ ℝ F).contDiff.contDiffAt
    exact hcd.isSelfAdjoint_hessianOperator.isSymmetric
  obtain ⟨c₁, hc₁, hgap₁⟩ :=
    ((isNondegenerateCriticalPoint_birthDeathPotential_neg_sqrt hs).separatedSum
      hy).exists_pos_mul_norm_le_hessianOperator
  obtain ⟨c₂, hc₂, hgap₂⟩ :=
    ((isNondegenerateCriticalPoint_birthDeathPotential_sqrt hs).separatedSum
      hy).exists_pos_mul_norm_le_hessianOperator
  refine ⟨h₁, hsnd, ?_, hsym, ⟨min c₁ c₂, lt_min hc₁ hc₂, fun v ↦ ?_, fun v ↦ ?_⟩, ?_, ?_⟩
  · rw [hH_eq]
    exact ((continuous_const.mul h₁.continuous).smul continuous_const).add continuous_const
  · exact (mul_le_mul_of_nonneg_right (min_le_left _ _) (norm_nonneg v)).trans (hgap₁ v)
  · exact (mul_le_mul_of_nonneg_right (min_le_right _ _) (norm_nonneg v)).trans (hgap₂ v)
  · rw [hH_eq, hessianOperator_separatedSum_birthDeathPotential_eq hy.contDiffAt]
    exact ((h₁bot.const_mul 2).smul_const P₁).add tendsto_const_nhds
  · rw [hH_eq, hessianOperator_separatedSum_birthDeathPotential_eq hy.contDiffAt]
    exact ((h₁top.const_mul 2).smul_const P₁).add tendsto_const_nhds

/-- **Initial values of decaying linearized solutions along the newborn connecting trajectory.**
Along any negative gradient trajectory `z` of `separatedSum (birthDeathPotential s) g` (`s > 0`)
from `(-√s, y)` to `(√s, y)` above a nondegenerate critical point `y` of `g`, the initial values of
the square-integrable solutions of `v' + Hess(z) v = 0` form the line `ℝ ∙ (1, 0)`. -/
theorem squareIntegrableSolutions_hessianOperator_separatedSum_birthDeathPotential_eq_span
    (hs : 0 < s) (hg : ∀ t, DifferentiableAt ℝ g (z t).snd) (hy : IsNondegenerateCriticalPoint g y)
    (hz : IsIntegralCurve z (fun _ w ↦ -∇ (separatedSum (birthDeathPotential s) g) w))
    (hbot : Tendsto z atBot (𝓝 (WithLp.toLp 2 (-√s, y))))
    (htop : Tendsto z atTop (𝓝 (WithLp.toLp 2 (√s, y)))) :
    squareIntegrableSolutions
        (fun t ↦ hessianOperator (separatedSum (birthDeathPotential s) g) (z t)) =
      ℝ ∙ WithLp.toLp 2 (1, (0 : F)) := by
  obtain ⟨h₁, hsnd, -⟩ :=
    trajectory_data_separatedSum_birthDeathPotential hs hg hy hz hbot htop
  have h₁bot : Tendsto (fun t ↦ (z t).fst) atBot (𝓝 (-√s)) :=
    ((WithLp.continuous_fst 2 ℝ F).tendsto' _ _ rfl).comp hbot
  have h₁top : Tendsto (fun t ↦ (z t).fst) atTop (𝓝 √s) :=
    ((WithLp.continuous_fst 2 ℝ F).tendsto' _ _ rfl).comp htop
  have hblock : ∀ t (w : WithLp 2 (ℝ × F)),
      hessianOperator (separatedSum (birthDeathPotential s) g) (z t) w =
        WithLp.toLp 2 (hessianOperator (birthDeathPotential s) (z t).fst w.fst,
          hessianOperator g y w.snd) := fun t w ↦ by
    have hgt : ContDiffAt ℝ 2 g (z t).snd := by rw [hsnd t]; exact hy.contDiffAt
    rw [hessianOperator_separatedSum_apply (contDiff_birthDeathPotential s).contDiffAt hgt w,
      hsnd t]
  ext w
  rw [mem_squareIntegrableSolutions_iff_of_apply_eq_toLp hblock,
    h₁.squareIntegrableSolutions_hessianOperator_eq_top (Module.finrank_self ℝ)
      (contDiff_birthDeathPotential s) h₁bot h₁top (by linarith [Real.sqrt_pos.2 hs]),
    hy.squareIntegrableSolutions_hessianOperator_eq_bot, Submodule.mem_span_singleton]
  refine ⟨fun h ↦ ⟨w.fst, ?_⟩, ?_⟩
  · refine (WithLp.ext_iff 2).2 (Prod.ext ?_ ?_) <;> simp [(Submodule.mem_bot ℝ).1 h.2]
  · rintro ⟨a, rfl⟩
    simp

/-- Along any negative gradient trajectory `z` of `separatedSum (birthDeathPotential s) g` (`s > 0`)
from `(-√s, y)` to `(√s, y)` above a nondegenerate critical point `y` of `g`, `D_z` is Fredholm. -/
theorem isFredholm_trajectoryOperator_separatedSum_birthDeathPotential
    (hs : 0 < s) (hg : ∀ t, DifferentiableAt ℝ g (z t).snd) (hy : IsNondegenerateCriticalPoint g y)
    (hz : IsIntegralCurve z (fun _ w ↦ -∇ (separatedSum (birthDeathPotential s) g) w))
    (hbot : Tendsto z atBot (𝓝 (WithLp.toLp 2 (-√s, y))))
    (htop : Tendsto z atTop (𝓝 (WithLp.toLp 2 (√s, y))))
    (hAL : AL =ᵐ[volume.restrict ((⊤ : Opens ℝ) : Set ℝ)]
      fun t ↦ hessianOperator (separatedSum (birthDeathPotential s) g) (z t)) :
    (trajectoryOperator (p := 2) AL).IsFredholm := by
  obtain ⟨-, -, hA, hsym, ⟨α, hα, hminus, hplus⟩, hAbot, hAtop⟩ :=
    trajectory_data_separatedSum_birthDeathPotential hs hg hy hz hbot htop
  exact isFredholm_trajectoryOperator_of_hasLyapunovForm hA
    (ContinuousLinearMap.hasLyapunovForm_of_tendsto_of_isSymmetric hsym hAbot hα hminus)
    (ContinuousLinearMap.hasLyapunovForm_of_tendsto_of_isSymmetric hsym hAtop hα hplus)
    hAbot hAtop AL hAL

/-- **The linearized operator along the newborn connecting trajectory has Fredholm index `1`.** -/
theorem index_trajectoryOperator_separatedSum_birthDeathPotential
    (hs : 0 < s) (hg : ∀ t, DifferentiableAt ℝ g (z t).snd) (hy : IsNondegenerateCriticalPoint g y)
    (hz : IsIntegralCurve z (fun _ w ↦ -∇ (separatedSum (birthDeathPotential s) g) w))
    (hbot : Tendsto z atBot (𝓝 (WithLp.toLp 2 (-√s, y))))
    (htop : Tendsto z atTop (𝓝 (WithLp.toLp 2 (√s, y))))
    (hAL : AL =ᵐ[volume.restrict ((⊤ : Opens ℝ) : Set ℝ)]
      fun t ↦ hessianOperator (separatedSum (birthDeathPotential s) g) (z t)) :
    (trajectoryOperator (p := 2) AL).index = 1 := by
  obtain ⟨-, -, hA, -, ⟨α, hα, hminus, hplus⟩, hAbot, hAtop⟩ :=
    trajectory_data_separatedSum_birthDeathPotential hs hg hy hz hbot htop
  have hp := (isNondegenerateCriticalPoint_birthDeathPotential_neg_sqrt hs).separatedSum hy
  have hq := (isNondegenerateCriticalPoint_birthDeathPotential_sqrt hs).separatedSum hy
  rw [index_trajectoryOperator_eq_finrank_pointSpectralSubspace_sub_finrank hA
      hp.contDiffAt.isSelfAdjoint_hessianOperator.isSymmetric
      hq.contDiffAt.isSelfAdjoint_hessianOperator.isSymmetric
      hα hminus hplus hAbot hAtop AL hAL,
    ← hp.contDiffAt.morseIndex_eq_finrank_pointSpectralSubspace,
    ← hq.contDiffAt.morseIndex_eq_finrank_pointSpectralSubspace,
    morseIndex_separatedSum_birthDeathPotential_neg_sqrt hs hy,
    morseIndex_separatedSum_birthDeathPotential_sqrt hs hy]
  push_cast; ring

/-- **The kernel of `D_z` along the newborn connecting trajectory is one-dimensional.** -/
theorem finrank_ker_trajectoryOperator_separatedSum_birthDeathPotential_eq_one
    (hs : 0 < s) (hg : ∀ t, DifferentiableAt ℝ g (z t).snd) (hy : IsNondegenerateCriticalPoint g y)
    (hz : IsIntegralCurve z (fun _ w ↦ -∇ (separatedSum (birthDeathPotential s) g) w))
    (hbot : Tendsto z atBot (𝓝 (WithLp.toLp 2 (-√s, y))))
    (htop : Tendsto z atTop (𝓝 (WithLp.toLp 2 (√s, y))))
    (hAL : AL =ᵐ[volume.restrict ((⊤ : Opens ℝ) : Set ℝ)]
      fun t ↦ hessianOperator (separatedSum (birthDeathPotential s) g) (z t)) :
    Module.finrank ℝ (trajectoryOperator (p := 2) AL).ker = 1 := by
  obtain ⟨-, -, hA, -⟩ :=
    trajectory_data_separatedSum_birthDeathPotential hs hg hy hz hbot htop
  rw [finrank_ker_trajectoryOperator hA AL hAL,
    squareIntegrableSolutions_hessianOperator_separatedSum_birthDeathPotential_eq_span
      hs hg hy hz hbot htop,
    finrank_span_singleton (fun h ↦ by simpa using congrArg WithLp.fst h)]

/-- **Formal-adjoint injectivity in the birth–death model with transverse directions:** along a
connecting trajectory `z` from `(-√s, y)` to `(√s, y)`, `ξ ↦ ξ' - Hess(z) ξ` (minus the formal
adjoint) has trivial kernel on `W^{1,2}`. -/
theorem ker_trajectoryOperator_neg_separatedSum_birthDeathPotential_eq_bot
    (hs : 0 < s) (hg : ∀ t, DifferentiableAt ℝ g (z t).snd) (hy : IsNondegenerateCriticalPoint g y)
    (hz : IsIntegralCurve z (fun _ w ↦ -∇ (separatedSum (birthDeathPotential s) g) w))
    (hbot : Tendsto z atBot (𝓝 (WithLp.toLp 2 (-√s, y))))
    (htop : Tendsto z atTop (𝓝 (WithLp.toLp 2 (√s, y))))
    (hAL : AL =ᵐ[volume.restrict ((⊤ : Opens ℝ) : Set ℝ)]
      fun t ↦ hessianOperator (separatedSum (birthDeathPotential s) g) (z t)) :
    (trajectoryOperator (p := 2) (-AL)).ker = ⊥ := by
  obtain ⟨-, -, hA, hsym, -⟩ :=
    trajectory_data_separatedSum_birthDeathPotential hs hg hy hz hbot htop
  have hadj : ∀ᵐ t ∂volume.restrict ((⊤ : Opens ℝ) : Set ℝ),
      AL t = ContinuousLinearMap.adjoint (AL t) := by
    filter_upwards [hAL] with t ht
    rw [ht]
    exact (hsym t).clm_adjoint_eq.symm
  have hclosed :=
    (isFredholm_trajectoryOperator_separatedSum_birthDeathPotential hs hg hy hz hbot htop
      hAL).isClosed_range
  have hALneg : (-AL : Lp (WithLp 2 (ℝ × F) →L[ℝ] WithLp 2 (ℝ × F)) ∞
        (volume.restrict ((⊤ : Opens ℝ) : Set ℝ)))
      =ᵐ[volume.restrict ((⊤ : Opens ℝ) : Set ℝ)]
      fun t ↦ -hessianOperator (separatedSum (birthDeathPotential s) g) (z t) := by
    filter_upwards [Lp.coeFn_neg AL, hAL] with t hneg ht
    simp only [hneg, Pi.neg_apply, ht]
  have := finiteDimensional_ker_trajectoryOperator hA.neg (-AL) hALneg
  have hidx := index_trajectoryOperator_separatedSum_birthDeathPotential hs hg hy hz hbot htop hAL
  rw [index_trajectoryOperator_of_isClosed_range hadj hclosed,
    finrank_ker_trajectoryOperator_separatedSum_birthDeathPotential_eq_one hs hg hy hz hbot htop
      hAL] at hidx
  exact Submodule.finrank_eq_zero.1 (by omega)

/-- Along any negative gradient trajectory `z` of `separatedSum (birthDeathPotential s) g` (`s > 0`)
from `(-√s, y)` to `(√s, y)` above a nondegenerate critical point `y` of `g`, the adjoint ODE
`v' - Hess(z) v = 0` has no nonzero square-integrable solution. -/
theorem squareIntegrableSolutions_neg_hessianOperator_separatedSum_birthDeathPotential_eq_bot
    (hs : 0 < s) (hg : ∀ t, DifferentiableAt ℝ g (z t).snd) (hy : IsNondegenerateCriticalPoint g y)
    (hz : IsIntegralCurve z (fun _ w ↦ -∇ (separatedSum (birthDeathPotential s) g) w))
    (hbot : Tendsto z atBot (𝓝 (WithLp.toLp 2 (-√s, y))))
    (htop : Tendsto z atTop (𝓝 (WithLp.toLp 2 (√s, y)))) :
    squareIntegrableSolutions
      (fun t ↦ -hessianOperator (separatedSum (birthDeathPotential s) g) (z t)) = ⊥ := by
  obtain ⟨-, -, hA, -, -, hAbot, hAtop⟩ :=
    trajectory_data_separatedSum_birthDeathPotential hs hg hy hz hbot htop
  obtain ⟨M, hM⟩ := exists_forall_norm_le_of_tendsto hA hAbot hAtop
  have hmem : MemLp (fun t ↦ hessianOperator (separatedSum (birthDeathPotential s) g) (z t)) ∞
      (volume.restrict ((⊤ : Opens ℝ) : Set ℝ)) :=
    memLp_top_of_bound hA.aestronglyMeasurable M (.of_forall hM)
  set AL := hmem.toLp _
  have hAL : AL =ᵐ[volume.restrict ((⊤ : Opens ℝ) : Set ℝ)]
      fun t ↦ hessianOperator (separatedSum (birthDeathPotential s) g) (z t) := hmem.coeFn_toLp
  have hALneg : (-AL : Lp (WithLp 2 (ℝ × F) →L[ℝ] WithLp 2 (ℝ × F)) ∞
        (volume.restrict ((⊤ : Opens ℝ) : Set ℝ)))
      =ᵐ[volume.restrict ((⊤ : Opens ℝ) : Set ℝ)]
      fun t ↦ -hessianOperator (separatedSum (birthDeathPotential s) g) (z t) := by
    filter_upwards [Lp.coeFn_neg AL, hAL] with t hneg ht
    simp only [hneg, Pi.neg_apply, ht]
  exact (ker_trajectoryOperator_eq_bot_iff hA.neg (-AL) hALneg).1
    (ker_trajectoryOperator_neg_separatedSum_birthDeathPotential_eq_bot hs hg hy hz hbot htop hAL)

/-- **Transversality of the newborn connecting trajectory with transverse directions.** -/
theorem surjective_trajectoryOperator_separatedSum_birthDeathPotential
    (hs : 0 < s) (hg : ∀ t, DifferentiableAt ℝ g (z t).snd) (hy : IsNondegenerateCriticalPoint g y)
    (hz : IsIntegralCurve z (fun _ w ↦ -∇ (separatedSum (birthDeathPotential s) g) w))
    (hbot : Tendsto z atBot (𝓝 (WithLp.toLp 2 (-√s, y))))
    (htop : Tendsto z atTop (𝓝 (WithLp.toLp 2 (√s, y))))
    (hAL : AL =ᵐ[volume.restrict ((⊤ : Opens ℝ) : Set ℝ)]
      fun t ↦ hessianOperator (separatedSum (birthDeathPotential s) g) (z t)) :
    Function.Surjective (trajectoryOperator (p := 2) AL) := by
  obtain ⟨-, -, -, hsym, -⟩ :=
    trajectory_data_separatedSum_birthDeathPotential hs hg hy hz hbot htop
  have hadj : ∀ᵐ t ∂volume.restrict ((⊤ : Opens ℝ) : Set ℝ),
      AL t = ContinuousLinearMap.adjoint (AL t) := by
    filter_upwards [hAL] with t ht
    rw [ht]
    exact (hsym t).clm_adjoint_eq.symm
  exact (surjective_trajectoryOperator_iff_ker_neg_eq_bot hadj
    (isFredholm_trajectoryOperator_separatedSum_birthDeathPotential hs hg hy hz hbot htop
      hAL).isClosed_range).2
    (ker_trajectoryOperator_neg_separatedSum_birthDeathPotential_eq_bot hs hg hy hz hbot htop hAL)

/-- **The kernel of `D_z` along the newborn connecting trajectory is spanned by `z'`.** -/
theorem exists_ker_trajectoryOperator_separatedSum_birthDeathPotential_eq_span
    (hs : 0 < s) (hg : ∀ t, DifferentiableAt ℝ g (z t).snd) (hy : IsNondegenerateCriticalPoint g y)
    (hz : IsIntegralCurve z (fun _ w ↦ -∇ (separatedSum (birthDeathPotential s) g) w))
    (hbot : Tendsto z atBot (𝓝 (WithLp.toLp 2 (-√s, y))))
    (htop : Tendsto z atTop (𝓝 (WithLp.toLp 2 (√s, y))))
    (hAL : AL =ᵐ[volume.restrict ((⊤ : Opens ℝ) : Set ℝ)]
      fun t ↦ hessianOperator (separatedSum (birthDeathPotential s) g) (z t)) :
    ∃ u : WeakDerivStep volume ⊤ 2
        (ContinuousLinearMap.id ℝ
          (Lp (WithLp 2 (ℝ × F)) 2 (volume.restrict ((⊤ : Opens ℝ) : Set ℝ)))),
      ⇑(prev (ContinuousLinearMap.id ℝ
          (Lp (WithLp 2 (ℝ × F)) 2 (volume.restrict ((⊤ : Opens ℝ) : Set ℝ)))) u)
          =ᵐ[volume.restrict ((⊤ : Opens ℝ) : Set ℝ)] deriv z ∧
        (trajectoryOperator (p := 2) AL).ker = ℝ ∙ u := by
  obtain ⟨h₁, hsnd, -⟩ :=
    trajectory_data_separatedSum_birthDeathPotential hs hg hy hz hbot htop
  have h₁bot : Tendsto (fun t ↦ (z t).fst) atBot (𝓝 (-√s)) :=
    ((WithLp.continuous_fst 2 ℝ F).tendsto' _ _ rfl).comp hbot
  have h₁top : Tendsto (fun t ↦ (z t).fst) atTop (𝓝 √s) :=
    ((WithLp.continuous_fst 2 ℝ F).tendsto' _ _ rfl).comp htop
  let ι : ℝ →L[ℝ] WithLp 2 (ℝ × F) :=
    (WithLp.prodContinuousLinearEquiv 2 ℝ ℝ F).symm.toContinuousLinearMap ∘L
      ContinuousLinearMap.inl ℝ ℝ F
  have hι : ∀ a : ℝ, ι a = WithLp.toLp 2 (a, (0 : F)) := fun a ↦ by simp [ι]
  let v : ℝ → WithLp 2 (ℝ × F) := fun t ↦ ι (-∇ (birthDeathPotential s) (z t).fst)
  have hv_eq_deriv : v = deriv z := funext fun t ↦ by
    rw [(hz t).deriv]
    dsimp only [v]
    rw [gradient_separatedSum (differentiable_birthDeathPotential s _) (hg t),
      hsnd t, hy.gradient_eq_zero, hι]
    refine (WithLp.ext_iff 2).2 (Prod.ext ?_ ?_) <;> simp
  have hv_deriv : ∀ t,
      HasDerivAt v (-hessianOperator (separatedSum (birthDeathPotential s) g) (z t) (v t)) t := by
    intro t
    have hgt : ContDiffAt ℝ 2 g (z t).snd := by rw [hsnd t]; exact hy.contDiffAt
    have hd₁ : HasDerivAt (fun t ↦ -∇ (birthDeathPotential s) (z t).fst)
        (-hessianOperator (birthDeathPotential s) (z t).fst
          (-∇ (birthDeathPotential s) (z t).fst)) t :=
      ((contDiff_birthDeathPotential s).contDiffAt.hasDerivAt_gradient_comp (h₁ t)).neg
    refine (ι.hasFDerivAt.comp_hasDerivAt t hd₁).congr_deriv ?_
    rw [hessianOperator_separatedSum_apply (contDiff_birthDeathPotential s).contDiffAt hgt]
    simp only [v, hι, WithLp.toLp_fst, WithLp.toLp_snd, map_zero]
    refine (WithLp.ext_iff 2).2 (Prod.ext ?_ ?_) <;> simp
  have hgrad_cont : Continuous fun t ↦ ∇ (birthDeathPotential s) (z t).fst :=
    ((contDiff_birthDeathPotential s (n := 2)).gradient_right (m := 1)
      (by norm_num)).continuous.comp h₁.continuous
  have hgrad_mem : MemLp (fun t ↦ ∇ (birthDeathPotential s) (z t).fst) 2 := by
    rw [memLp_two_iff_integrable_sq_norm hgrad_cont.aestronglyMeasurable]
    exact h₁.integrable_norm_gradient_sq (fun _ ↦ differentiable_birthDeathPotential s _)
      (((differentiable_birthDeathPotential s).continuous.tendsto _).comp h₁bot)
      (((differentiable_birthDeathPotential s).continuous.tendsto _).comp h₁top)
  have hv_mem : MemLp v 2 := hgrad_mem.neg.continuousLinearMap_comp ι
  obtain ⟨u, hu, huv⟩ :=
    exists_trajectoryOperator_eq_zero_of_hasDerivAt (p := 2) hAL hv_deriv hv_mem
  have hu0 : u ≠ 0 := by
    intro h0
    obtain ⟨t, ht⟩ := h₁.exists_gradient_ne_zero h₁bot h₁top (by linarith [Real.sqrt_pos.2 hs])
    rw [h0, prev_zero] at huv
    have hae : v =ᵐ[volume] (0 : ℝ → WithLp 2 (ℝ × F)) := by
      simpa only [Opens.coe_top, Measure.restrict_univ] using
        huv.symm.trans (Lp.coeFn_zero _ _ _)
    have hzero : v = 0 :=
      (Continuous.ae_eq_iff_eq volume (ι.continuous.comp hgrad_cont.neg) continuous_const).1 hae
    have hvt := congrArg WithLp.fst (congrFun hzero t)
    simp only [v, hι, WithLp.toLp_fst, Pi.zero_apply, WithLp.zero_fst, neg_eq_zero] at hvt
    exact ht hvt
  refine ⟨u, ?_, eq_span_singleton_of_mem_of_finrank_eq_one
    (finrank_ker_trajectoryOperator_separatedSum_birthDeathPotential_eq_one hs hg hy hz hbot htop
      hAL)
    hu hu0⟩
  rw [← hv_eq_deriv]
  exact huv

/-- At the constant trajectory `(-√s, y)` (`s > 0`), the linearized operator is bijective. -/
theorem bijective_trajectoryOperator_separatedSum_birthDeathPotential_neg_sqrt
    (hs : 0 < s) (hy : IsNondegenerateCriticalPoint g y)
    (hAL : AL =ᵐ[volume.restrict ((⊤ : Opens ℝ) : Set ℝ)]
      fun _ ↦ hessianOperator (separatedSum (birthDeathPotential s) g) (WithLp.toLp 2 (-√s, y))) :
    Function.Bijective (trajectoryOperator (p := 2) AL) :=
  ((isNondegenerateCriticalPoint_birthDeathPotential_neg_sqrt
    hs).separatedSum hy).bijective_trajectoryOperator_hessianOperator hAL

/-- At the constant trajectory `(√s, y)` (`s > 0`), the linearized operator is bijective. -/
theorem bijective_trajectoryOperator_separatedSum_birthDeathPotential_sqrt
    (hs : 0 < s) (hy : IsNondegenerateCriticalPoint g y)
    (hAL : AL =ᵐ[volume.restrict ((⊤ : Opens ℝ) : Set ℝ)]
      fun _ ↦ hessianOperator (separatedSum (birthDeathPotential s) g) (WithLp.toLp 2 (√s, y))) :
    Function.Bijective (trajectoryOperator (p := 2) AL) :=
  ((isNondegenerateCriticalPoint_birthDeathPotential_sqrt
    hs).separatedSum hy).bijective_trajectoryOperator_hessianOperator hAL

end SeparatedSum

end TauCeti

end
