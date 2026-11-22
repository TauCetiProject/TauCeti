/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Distribution.TemperedDistribution
public import TauCeti.Analysis.Distribution.SchwartzSpace.ChangeOfVariables
public import TauCeti.Analysis.Distribution.TemperateGrowth
public import TauCeti.MeasureTheory.Function.Lp.Precomposition
import TauCeti.Analysis.Calculus.FDeriv.Equiv
import TauCeti.Analysis.Distribution.TemperedDistribution.SmulLeft
import TauCeti.MeasureTheory.Function.Jacobian

/-!
# Pullback of tempered distributions along a change of variables

Let `φ : E ≃ E` be a bijection of a finite-dimensional real normed space such that `φ` and `φ⁻¹`
both have temperate growth, for instance a diffeomorphism whose derivatives of positive order, and
those of its inverse, are bounded. A tempered distribution `T` pulls back along `φ` to

`(φ^* T) f = T (φ_* f)`,

where `(φ_* f)(y) = |det Dφ⁻¹(y)| f(φ⁻¹ y)` is the pushforward of Schwartz densities
`SchwartzMap.pushforwardCLM`. This is `TemperedDistribution.compCLM φ`, a continuous linear map
`𝓢'(E, F) →L[ℂ] 𝓢'(E, F)`. The Jacobian factor makes it extend composition with `φ`: for a Schwartz
function, or a function of temperate growth, `u`, the pullback of the distribution of `u` is the
distribution of `u ∘ φ`, for every additive Haar measure (`compCLM_toTemperedDistributionCLM`,
`compCLM_toTemperedDistribution`). The point mass at `φ x` pulls back to `|det Dφ(x)|⁻¹` times the
point mass at `x` (`compCLM_delta`).

The pullback is contravariantly functorial, `(χ ∘ φ)^* = φ^* ∘ χ^*` (`compCLM_trans`), so pulling
back along `φ⁻¹` inverts it (`compCLM_symm_compCLM`, `compCLM_compCLM_symm`). It turns
multiplication by `g` into multiplication by `g ∘ φ` (`compCLM_smulLeftCLM`). It satisfies the
chain rule: if `Dφ(x) v = ∑ᵢ cᵢ(x) bᵢ` in a basis `b`, then
`∂_v (φ^* T) = ∑ᵢ cᵢ φ^* (∂_{bᵢ} T)` (`lineDerivOp_compCLM`), and conversely
`φ^* (∂_v T) = ∑ᵢ (dᵢ ∘ φ) ∂_{bᵢ} (φ^* T)` for the coordinates `dᵢ` of `Dφ⁻¹ v`
(`compCLM_lineDerivOp`). With the Leibniz rule this moves the derivative off `T`:
`g φ^* (∂_v T) = ∑ᵢ (∂_{bᵢ} ((dᵢ ∘ φ) g φ^* T) - ∂_{bᵢ} ((dᵢ ∘ φ) g) φ^* T)`
(`smulLeftCLM_compCLM_lineDerivOp`, and `compCLM_lineDerivOp_eq_sum_sub` for `g = 1`).

If `φ` pushes `μ` forward to at most a finite multiple of `μ`, the pullback of the distribution of
`u ∈ Lᵖ(μ)` is that of the `Lᵖ` precomposition `Lp.compOfMapLeSmul`
(`compCLM_toTemperedDistribution_eq_compOfMapLeSmul`). If the Jacobian of `φ` is bounded below,
`c ≤ |det Dφ|` with `c > 0`, the pullback maps every `Lᵖ` space to itself, with norm at most
`c^{-1/p}` (`exists_compCLM_toTemperedDistribution_eq_and_norm_le`).

Translates of a Schwartz function escape to infinity: as `a` leaves every compact set, the
distribution of `u (· - a)` tends to `0` in `𝓢'`
(`SchwartzMap.tendsto_toTemperedDistributionCLM_compSubConstCLM`), although translation does not
change its `Lᵖ` norms.

This is the global change of variables on `𝓢'` against which the Bessel-potential spaces `H^s` and
Besov spaces `B^s_{p, q}`, which are subspaces of `𝓢'`, are compared under diffeomorphisms of `E`.
It needs no bound on the derivatives beyond temperate growth: the shear `(x, y) ↦ (x, y + x³)` of
`ℝ²` and its inverse are polynomial, with unbounded derivatives, and they pull back tempered
distributions.

## References

* L. Hörmander, *The Analysis of Linear Partial Differential Operators I*, §6.1 and §7.1.
-/

public noncomputable section

open MeasureTheory
open scoped SchwartzMap LineDeriv

namespace TemperedDistribution

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {φ : E ≃ E}

section TVS

variable [AddCommGroup F] [Module ℂ F] [TopologicalSpace F] [IsTopologicalAddGroup F]
  [ContinuousConstSMul ℂ F]

variable (F) in
/-- The **pullback of tempered distributions** along a bijection `φ` such that `φ` and `φ⁻¹` have
temperate growth: `(φ^* T) f = T (φ_* f)`, the transpose of the pushforward of Schwartz densities
`(φ_* f)(y) = |det Dφ⁻¹(y)| f(φ⁻¹ y)`. On functions it is composition with `φ`
(`TemperedDistribution.compCLM_toTemperedDistribution`). -/
def compCLM (φ : E ≃ E) (hφ : (φ : E → E).HasTemperateGrowth)
    (hψ : (φ.symm : E → E).HasTemperateGrowth) : 𝓢'(E, F) →L[ℂ] 𝓢'(E, F) :=
  PointwiseConvergenceCLM.precomp _ (SchwartzMap.pushforwardCLM ℂ φ hφ hψ)

omit [FiniteDimensional ℝ E] in
@[simp]
theorem compCLM_apply_apply (hφ : (φ : E → E).HasTemperateGrowth)
    (hψ : (φ.symm : E → E).HasTemperateGrowth) (T : 𝓢'(E, F)) (f : 𝓢(E, ℂ)) :
    compCLM F φ hφ hψ T f = T (SchwartzMap.pushforwardCLM ℂ φ hφ hψ f) :=
  (rfl)

/-- **Functoriality of the pullback**: `(χ ∘ φ)^* = φ^* ∘ χ^*`. -/
theorem compCLM_trans {χ : E ≃ E} (hφ : (φ : E → E).HasTemperateGrowth)
    (hψ : (φ.symm : E → E).HasTemperateGrowth) (hχ : (χ : E → E).HasTemperateGrowth)
    (hχs : (χ.symm : E → E).HasTemperateGrowth) (h₁ : (φ.trans χ : E → E).HasTemperateGrowth)
    (h₂ : ((φ.trans χ).symm : E → E).HasTemperateGrowth) :
    compCLM F (φ.trans χ) h₁ h₂ = compCLM F φ hφ hψ ∘L compCLM F χ hχ hχs := by
  ext T f
  simp [SchwartzMap.pushforwardCLM_trans ℂ hφ hψ hχ hχs h₁ h₂]

/-- The pullback along the identity is the identity. -/
@[simp]
theorem compCLM_refl (h₁ : (Equiv.refl E : E → E).HasTemperateGrowth)
    (h₂ : ((Equiv.refl E).symm : E → E).HasTemperateGrowth) :
    compCLM F (Equiv.refl E) h₁ h₂ = ContinuousLinearMap.id ℂ _ := by
  ext T f
  simp

/-- Pulling back along `φ` and then along `φ⁻¹` gives back the distribution. -/
@[simp]
theorem compCLM_symm_compCLM (hφ : (φ : E → E).HasTemperateGrowth)
    (hψ : (φ.symm : E → E).HasTemperateGrowth) (hφ' : (φ.symm.symm : E → E).HasTemperateGrowth)
    (T : 𝓢'(E, F)) : compCLM F φ.symm hψ hφ' (compCLM F φ hφ hψ T) = T := by
  rw [← ContinuousLinearMap.comp_apply, ← compCLM_trans hψ hφ' hφ hψ
    (by simpa using Function.HasTemperateGrowth.id (E := E))
    (by simpa using Function.HasTemperateGrowth.id (E := E))]
  simp only [Equiv.symm_trans_self, compCLM_refl, ContinuousLinearMap.id_apply]

/-- Pulling back along `φ⁻¹` and then along `φ` gives back the distribution. -/
@[simp]
theorem compCLM_compCLM_symm (hφ : (φ : E → E).HasTemperateGrowth)
    (hψ : (φ.symm : E → E).HasTemperateGrowth) (hφ' : (φ.symm.symm : E → E).HasTemperateGrowth)
    (T : 𝓢'(E, F)) : compCLM F φ hφ hψ (compCLM F φ.symm hψ hφ' T) = T := by
  rw [← ContinuousLinearMap.comp_apply, ← compCLM_trans hφ hψ hψ hφ'
    (by simpa using Function.HasTemperateGrowth.id (E := E))
    (by simpa using Function.HasTemperateGrowth.id (E := E))]
  simp only [Equiv.self_trans_symm, compCLM_refl, ContinuousLinearMap.id_apply]

/-- The pullback of `g T` is `(g ∘ φ) φ^* T`. -/
theorem compCLM_smulLeftCLM (hφ : (φ : E → E).HasTemperateGrowth)
    (hψ : (φ.symm : E → E).HasTemperateGrowth) {g : E → ℂ} (hg : g.HasTemperateGrowth)
    (T : 𝓢'(E, F)) :
    compCLM F φ hφ hψ (smulLeftCLM F g T) = smulLeftCLM F (g ∘ φ) (compCLM F φ hφ hψ T) := by
  ext f
  simp [SchwartzMap.pushforwardCLM_smulLeftCLM ℂ hφ hψ hg]

variable {ι : Type*} [Fintype ι]

/-- **The chain rule for the pullback.** If `Dφ(x) v = ∑ᵢ cᵢ(x) bᵢ` in a basis `b`, then
`∂_v (φ^* T) = ∑ᵢ cᵢ φ^* (∂_{bᵢ} T)`. -/
theorem lineDerivOp_compCLM (b : Module.Basis ι ℝ E) (hφ : (φ : E → E).HasTemperateGrowth)
    (hψ : (φ.symm : E → E).HasTemperateGrowth) (T : 𝓢'(E, F)) (v : E) :
    ∂_{v} (compCLM F φ hφ hψ T) = ∑ i, smulLeftCLM F (fun x ↦ ((b.repr (fderiv ℝ φ x v) i : ℝ) : ℂ))
      (compCLM F φ hφ hψ (∂_{b i} T)) := by
  ext g
  simp [SchwartzMap.pushforwardCLM_lineDerivOp ℂ b hφ hψ g v, map_sum]

/-- **The pullback of a derivative.** If `Dφ⁻¹(φ x) v = ∑ᵢ dᵢ(x) bᵢ` in a basis `b`, then
`φ^* (∂_v T) = ∑ᵢ dᵢ ∂_{bᵢ} (φ^* T)`. This is the chain rule `lineDerivOp_compCLM` for `φ⁻¹`,
pulled back along `φ`. -/
theorem compCLM_lineDerivOp (b : Module.Basis ι ℝ E) (hφ : (φ : E → E).HasTemperateGrowth)
    (hψ : (φ.symm : E → E).HasTemperateGrowth) (T : 𝓢'(E, F)) (v : E) :
    compCLM F φ hφ hψ (∂_{v} T) = ∑ i,
      smulLeftCLM F (fun x ↦ ((b.repr (fderiv ℝ φ.symm (φ x) v) i : ℝ) : ℂ))
        (∂_{b i} (compCLM F φ hφ hψ T)) := by
  conv_lhs => rw [← compCLM_symm_compCLM hφ hψ hφ T]
  rw [lineDerivOp_compCLM b hψ hφ, map_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  have hc : (fun x ↦ ((b.repr (fderiv ℝ φ.symm x v) i : ℝ) : ℂ)).HasTemperateGrowth :=
    hψ.basis_repr_fderiv_apply b v i
  rw [compCLM_smulLeftCLM hφ hψ hc, compCLM_compCLM_symm, Function.comp_def]

end TVS

section Leibniz

variable [NormedAddCommGroup F] [NormedSpace ℂ F] {ι : Type*} [Fintype ι]

/-- **The pullback of a derivative, moved off the distribution.** If
`Dφ⁻¹(φ x) v = ∑ᵢ dᵢ(x) bᵢ` in a basis `b`, then by the chain rule and the Leibniz rule
`g φ^* (∂_v T) = ∑ᵢ (∂_{bᵢ} (dᵢ g φ^* T) - ∂_{bᵢ} (dᵢ g) φ^* T)` for every `g` of temperate
growth. -/
theorem smulLeftCLM_compCLM_lineDerivOp (b : Module.Basis ι ℝ E)
    (hφ : (φ : E → E).HasTemperateGrowth) (hψ : (φ.symm : E → E).HasTemperateGrowth) {g : E → ℂ}
    (hg : g.HasTemperateGrowth) (T : 𝓢'(E, F)) (v : E) :
    smulLeftCLM F g (compCLM F φ hφ hψ (∂_{v} T)) = ∑ i,
      (∂_{b i} (smulLeftCLM F
          ((fun x ↦ ((b.repr (fderiv ℝ φ.symm (φ x) v) i : ℝ) : ℂ)) * g)
          (compCLM F φ hφ hψ T)) -
        smulLeftCLM F (fun x ↦ fderiv ℝ
          ((fun x ↦ ((b.repr (fderiv ℝ φ.symm (φ x) v) i : ℝ) : ℂ)) * g) x (b i))
          (compCLM F φ hφ hψ T)) := by
  rw [compCLM_lineDerivOp b hφ hψ, map_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  have hd : (fun x ↦ ((b.repr (fderiv ℝ φ.symm (φ x) v) i : ℝ) : ℂ)).HasTemperateGrowth :=
    (hψ.basis_repr_fderiv_apply b v i).comp hφ
  rw [smulLeftCLM_smulLeftCLM_apply hd hg, lineDerivOp_smulLeftCLM (hd.mul hg)]
  abel

/-- **The pullback of a derivative, moved off the distribution**: the case `g = 1` of
`smulLeftCLM_compCLM_lineDerivOp`. If `Dφ⁻¹(φ x) v = ∑ᵢ dᵢ(x) bᵢ` in a basis `b`, then
`φ^* (∂_v T) = ∑ᵢ (∂_{bᵢ} (dᵢ φ^* T) - (∂_{bᵢ} dᵢ) φ^* T)`. -/
theorem compCLM_lineDerivOp_eq_sum_sub (b : Module.Basis ι ℝ E)
    (hφ : (φ : E → E).HasTemperateGrowth) (hψ : (φ.symm : E → E).HasTemperateGrowth)
    (T : 𝓢'(E, F)) (v : E) :
    compCLM F φ hφ hψ (∂_{v} T) = ∑ i,
      (∂_{b i} (smulLeftCLM F (fun x ↦ ((b.repr (fderiv ℝ φ.symm (φ x) v) i : ℝ) : ℂ))
          (compCLM F φ hφ hψ T)) -
        smulLeftCLM F (fun x ↦ fderiv ℝ
          (fun y ↦ ((b.repr (fderiv ℝ φ.symm (φ y) v) i : ℝ) : ℂ)) x (b i))
          (compCLM F φ hφ hψ T)) := by
  have h := smulLeftCLM_compCLM_lineDerivOp b hφ hψ (g := 1)
    (Function.HasTemperateGrowth.const (1 : ℂ)) T v
  simp only [mul_one] at h
  rw [← h]
  exact ((smulLeftCLM_const 1 _).trans (one_smul ℂ _)).symm

end Leibniz

section Normed

variable [NormedAddCommGroup F] [NormedSpace ℂ F] [MeasurableSpace E] [BorelSpace E]
  (μ : Measure E) [μ.IsAddHaarMeasure]

/-- The pullback of the distribution of a Schwartz function `u` is the distribution of `u ∘ φ`,
for every additive Haar measure. -/
@[simp]
theorem compCLM_toTemperedDistributionCLM (hφ : (φ : E → E).HasTemperateGrowth)
    (hψ : (φ.symm : E → E).HasTemperateGrowth) (u : 𝓢(E, F)) :
    compCLM F φ hφ hψ (SchwartzMap.toTemperedDistributionCLM E F μ u) =
      SchwartzMap.toTemperedDistributionCLM E F μ
        (SchwartzMap.compCLM ℂ hφ (hψ.exists_norm_le_of_leftInverse φ.left_inv) u) := by
  ext f
  simp only [compCLM_apply_apply, SchwartzMap.toTemperedDistributionCLM_apply_apply,
    SchwartzMap.integral_pushforwardCLM_smul, SchwartzMap.compCLM_apply, Function.comp_apply]

/-- The pullback of the distribution of a function `u` of temperate growth is the distribution
of `u ∘ φ`, for every additive Haar measure. -/
@[simp]
theorem compCLM_toTemperedDistribution (hφ : (φ : E → E).HasTemperateGrowth)
    (hψ : (φ.symm : E → E).HasTemperateGrowth) {u : E → F} (hu : u.HasTemperateGrowth) :
    compCLM F φ hφ hψ (hu.toTemperedDistribution μ) = (hu.comp hφ).toTemperedDistribution μ := by
  ext f
  simp only [compCLM_apply_apply, Function.HasTemperateGrowth.toTemperedDistribution_apply,
    SchwartzMap.integral_pushforwardCLM_smul, Function.comp_apply]

open Filter Topology in
omit [μ.IsAddHaarMeasure] in
/-- **Translates of a Schwartz function tend to `0` as tempered distributions**: as `a` leaves
every compact set, `∫ f (x) • u (x - a) dμ → 0` for every Schwartz test function `f`, for every
measure `μ` of temperate growth. -/
theorem _root_.SchwartzMap.tendsto_toTemperedDistributionCLM_compSubConstCLM
    [μ.HasTemperateGrowth] (u : 𝓢(E, F)) :
    Tendsto (fun a : E ↦ SchwartzMap.toTemperedDistributionCLM E F μ (u.compSubConstCLM ℂ a))
      (cocompact E) (𝓝 0) := by
  rw [PointwiseConvergenceCLM.tendsto_iff_forall_tendsto]
  intro f
  simp only [SchwartzMap.toTemperedDistributionCLM_apply_apply, SchwartzMap.compSubConstCLM_apply]
  obtain ⟨C, hC⟩ : ∃ C, ∀ x, ‖u x‖ ≤ C :=
    ⟨_, fun x ↦ u.toBoundedContinuousFunction.norm_coe_le_norm x⟩
  have : (cocompact E).IsCountablyGenerated := by
    rw [← Metric.cobounded_eq_cocompact, ← comap_norm_atTop]
    infer_instance
  -- Dominated convergence, with the bound `‖f x‖ C`.
  have h := tendsto_integral_filter_of_dominated_convergence (F := fun a x ↦ f x • u (x - a))
    (fun x ↦ ‖f x‖ * C)
    (.of_forall fun a ↦ (f.continuous.smul (u.continuous.comp
      (continuous_id.sub continuous_const))).aestronglyMeasurable)
    (.of_forall fun a ↦ .of_forall fun x ↦ by
      rw [norm_smul]
      exact mul_le_mul_of_nonneg_left (hC _) (norm_nonneg _))
    ((f.integrable (μ := μ)).norm.mul_const C) (.of_forall fun x ↦ by
      simpa using (u.tendsto_cocompact.comp
        (Homeomorph.subLeft x).isClosedEmbedding.tendsto_cocompact).const_smul (f x))
  rw [integral_zero] at h
  simpa using h

open scoped ENNReal in
/-- If `φ` pushes `μ` forward to at most `C • μ` with `C < ∞`, pulling back the distribution of
`u ∈ Lᵖ(μ)` along `φ` gives the distribution of the `Lᵖ` precomposition `Lp.compOfMapLeSmul`, for
every `1 ≤ p ≤ ∞`. -/
theorem compCLM_toTemperedDistribution_eq_compOfMapLeSmul [CompleteSpace F] {p : ℝ≥0∞}
    [Fact (1 ≤ p)] {C : ℝ≥0∞} (hφ : (φ : E → E).HasTemperateGrowth)
    (hψ : (φ.symm : E → E).HasTemperateGrowth) (hC : C ≠ ∞) (hmap : μ.map φ ≤ C • μ)
    (u : Lp F p μ) :
    compCLM F φ hφ hψ (u : 𝓢'(E, F)) =
      (Lp.compOfMapLeSmul ℂ hφ.1.continuous.aemeasurable hC hmap u : 𝓢'(E, F)) := by
  ext f
  rw [compCLM_apply_apply, Lp.toTemperedDistribution_apply, Lp.toTemperedDistribution_apply,
    SchwartzMap.integral_pushforwardCLM_smul]
  refine integral_congr_ae
    ((Lp.coeFn_compOfMapLeSmul (𝕜 := ℂ) hφ.1.continuous.aemeasurable hC hmap u).mono fun x hx ↦ ?_)
  dsimp only
  rw [hx, Function.comp_apply]

open scoped ENNReal in
/-- **The pullback on `Lᵖ`.** If `c ≤ |det Dφ|` everywhere, with `c > 0`, the pullback of the
distribution of `f ∈ Lᵖ(μ)` is the distribution of `f ∘ φ ∈ Lᵖ(μ)`, of norm at most
`c^{-1/p} ‖f‖_p`. -/
theorem exists_compCLM_toTemperedDistribution_eq_and_norm_le [CompleteSpace F] {p : ℝ≥0∞}
    [Fact (1 ≤ p)] (hφ : (φ : E → E).HasTemperateGrowth) (hψ : (φ.symm : E → E).HasTemperateGrowth)
    {c : ℝ} (hc : 0 < c) (hdet : ∀ x, c ≤ |(fderiv ℝ φ x).det|) (f : Lp F p μ) :
    ∃ v : Lp F p μ, compCLM F φ hφ hψ (f : 𝓢'(E, F)) = v ∧ v =ᵐ[μ] f ∘ φ ∧
      ‖v‖ ≤ c⁻¹ ^ p.toReal⁻¹ * ‖f‖ := by
  have hdiff : DifferentiableOn ℝ φ Set.univ := (hφ.1.differentiable (by simp)).differentiableOn
  have hle := eLpNorm_comp_restrict_le (μ := μ) (p := p) isOpen_univ hdiff φ.injective.injOn
    subset_rfl MeasurableSet.univ hc (fun x _ ↦ hdet x) f
  have hmem := (Lp.memLp f).restrict (φ '' Set.univ) |>.comp_restrict_of_le_abs_det
    isOpen_univ hdiff φ.injective.injOn subset_rfl MeasurableSet.univ hc (fun x _ ↦ hdet x)
  rw [Set.image_univ_of_surjective φ.surjective, Measure.restrict_univ] at hle
  rw [Measure.restrict_univ] at hmem
  refine ⟨hmem.toLp _, ?_, hmem.coeFn_toLp, ?_⟩
  · ext g
    rw [compCLM_apply_apply, Lp.toTemperedDistribution_apply, Lp.toTemperedDistribution_apply,
      SchwartzMap.integral_pushforwardCLM_smul ℂ μ hφ hψ g f]
    exact integral_congr_ae (hmem.coeFn_toLp.mono fun x hx ↦ by simp only [hx])
  · rw [Lp.norm_toLp, Lp.norm_def]
    refine (ENNReal.toReal_mono (ENNReal.mul_ne_top (ENNReal.rpow_ne_top_of_nonneg
      ENNReal.toReal_nonneg (ENNReal.inv_ne_top.2 (ENNReal.ofReal_pos.2 hc).ne'))
        (Lp.eLpNorm_ne_top f)) hle).trans_eq ?_
    simp [ENNReal.toReal_mul, ← ENNReal.toReal_rpow, hc.le]

end Normed

/-- The point mass at `φ x` pulls back to `|det Dφ(x)|⁻¹` times the point mass at `x`. -/
theorem compCLM_delta (hφ : (φ : E → E).HasTemperateGrowth)
    (hψ : (φ.symm : E → E).HasTemperateGrowth) (x : E) :
    compCLM ℂ φ hφ hψ (delta (φ x)) = ((|(fderiv ℝ φ x).det|⁻¹ : ℝ) : ℂ) • delta x := by
  have h := φ.det_fderiv_symm_mul_det_fderiv (y := φ x) (hφ.1.differentiable (by simp) _)
    (hψ.1.differentiable (by simp) _)
  rw [Equiv.symm_apply_apply] at h
  ext f
  simp [eq_inv_of_mul_eq_one_left h, abs_inv]

end TemperedDistribution
