/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Parabolic.Semigroup
public import TauCeti.Analysis.PDE.HeatKernel.Semigroup
public import TauCeti.MeasureTheory.Function.Lp.CastMeasure
import TauCeti.Analysis.PDE.DirichletProblem.Exhaustion
import TauCeti.Analysis.PDE.HeatKernel.Generator
import TauCeti.Analysis.PDE.WeakLaplacian
import TauCeti.Analysis.Semigroups.TrotterKato

/-!
# The Dirichlet heat flows of an exhaustion of `ℝⁿ`

Let `U k` be a monotone family of open subsets of `ℝⁿ`, indexed by a directed order, that covers
`ℝⁿ`, such as the balls `B(0, k)`. On each `U k` on which the energy form of `-Δ` is coercive, for
instance on a bounded `U k`, the heat equation with the Dirichlet boundary condition is solved by
the Dirichlet semigroup `e^{tΔ_{U k}}` of the variational theory (`TauCeti.PDE.dirichletSemigroup`).
This file proves that these heat flows converge to the heat flow `e^{tΔ}` of `ℝⁿ`, the convolution
with the Gaussian kernel (`TauCeti.heatSemigroup`): for `x ∈ L²(ℝⁿ)`, the solution
`e^{tΔ_{U k}} (x|_{U k})` extended by zero to `ℝⁿ` converges to `e^{tΔ} x` in `L²(ℝⁿ)`, uniformly
for `t` in every interval `[0, τ]`
(`TauCeti.PDE.tendstoUniformlyOn_dirichletSemigroup_heatSemigroup`), and in particular at every
fixed time (`TauCeti.PDE.tendsto_dirichletSemigroup_heatSemigroup`). For initial data `x`
supported in some `U k₀`, the zero extension of the restriction of `x` to `U k` is `x` itself from
`k₀` on, so the variational Dirichlet problems on the bounded domains `U k` approximate the Cauchy
problem on `ℝⁿ` with the same initial value.

## The argument

The evolution is reduced to the stationary problem by the Trotter–Kato approximation theorem
(`tendstoUniformlyOn_realOperator_apply_of_tendsto_resolvent`, in the namespace
`TauCeti.Semigroups.StronglyContinuousSemigroup`), which needs semigroups on one space. With `J` the
extension by zero `L²(U) → L²(ℝⁿ)` and `P` the restriction `L²(ℝⁿ) → L²(U)`, the operators
`J e^{tΔ_U} P + (1 - J P)` form a strongly continuous semigroup on `L²(ℝⁿ)`, since `P J = 1`; it is
the Dirichlet heat flow on functions supported in `U` and the identity on functions vanishing on
`U`. Its resolvent at `1`, a Laplace transform, is `J R_U P + (1 - J P)`, where `R_U z` is the weak
solution `w ∈ H¹₀(U)` of `-Δw + w = z`, since the generator of the Dirichlet semigroup is minus the
Dirichlet realization of `-Δ` (`TauCeti.PDE.dirichletSemigroup_generator`). The resolvent of the
heat semigroup at `1` is the weak solution `u ∈ H¹(ℝⁿ)` of `-Δu + u = x`, since its generator is the
distributional Laplacian (`TauCeti.generator_heatSemigroup_eq_weakLaplacianLp`) and Green's identity
turns the weak equation into the distributional one. The energy form of `-Δ + 1` is coercive on all
of `H¹(ℝⁿ)`, so the stationary comparison along an exhaustion
(`TauCeti.PDE.tendsto_extendByZeroL_of_isWeakSolutionDirichlet`, Céa's lemma) gives `J w_k → u` in
`H¹(ℝⁿ)`. Finally `x - J P x → 0` in `L²(ℝⁿ)`: a compactly supported approximation of `x` is
supported in some `U k`, by compactness and directedness, and is then fixed by `J P`.

## References

* A. Pazy, *Semigroups of Linear Operators and Applications to Partial Differential Equations*,
  Section 3.4 (the Trotter–Kato theorem).
* W. Arendt, *Heat kernels*, ISEM lecture notes 2005/06, Chapter 1 (the Dirichlet Laplacian as
  the operator associated with a coercive form).
* J. Céa, *Approximation variationnelle des problèmes aux limites*, Ann. Inst. Fourier 14 (1964),
  345–444.
-/

public section

noncomputable section

namespace TauCeti

namespace PDE

open Filter MeasureTheory Set TopologicalSpace Topology TauCeti.Semigroups
open scoped ENNReal NNReal

variable {ι : Type*} [Fintype ι]

/-! ### Zero extension and restriction between `L²(U)` and `L²(ℝⁿ)` -/

/-- Extension by zero `L²(U) → L²(ℝⁿ)`. -/
private def extendL (U : Opens (EuclideanSpace ℝ ι)) :
    Lp ℝ 2 (volume.restrict (U : Set (EuclideanSpace ℝ ι))) →L[ℝ]
      Lp ℝ 2 (volume : Measure (EuclideanSpace ℝ ι)) :=
  ((castLpₗᵢ (𝕜 := ℝ) Measure.restrict_univ).toLinearIsometry.comp
    (extendByZeroLpₗᵢ ℝ volume U.isOpen.nullMeasurableSet (subset_univ _))).toContinuousLinearMap

private theorem extendL_apply (U : Opens (EuclideanSpace ℝ ι))
    (y : Lp ℝ 2 (volume.restrict (U : Set (EuclideanSpace ℝ ι)))) :
    extendL U y = castLpₗᵢ (𝕜 := ℝ) Measure.restrict_univ
      (extendByZeroLpₗᵢ ℝ volume U.isOpen.nullMeasurableSet (subset_univ _) y) :=
  (rfl)

/-- Restriction `L²(ℝⁿ) → L²(U)`. -/
private def restrictL (U : Opens (EuclideanSpace ℝ ι)) :
    Lp ℝ 2 (volume : Measure (EuclideanSpace ℝ ι)) →L[ℝ]
      Lp ℝ 2 (volume.restrict (U : Set (EuclideanSpace ℝ ι))) :=
  LpToLpRestrictCLM (EuclideanSpace ℝ ι) ℝ ℝ volume 2 U

private theorem restrictL_apply (U : Opens (EuclideanSpace ℝ ι))
    (x : Lp ℝ 2 (volume : Measure (EuclideanSpace ℝ ι))) :
    restrictL U x = LpToLpRestrictCLM (EuclideanSpace ℝ ι) ℝ ℝ volume 2 U x :=
  (rfl)

private theorem norm_extendL_apply (U : Opens (EuclideanSpace ℝ ι))
    (y : Lp ℝ 2 (volume.restrict (U : Set (EuclideanSpace ℝ ι)))) :
    ‖extendL U y‖ = ‖y‖ :=
  ((castLpₗᵢ (𝕜 := ℝ) Measure.restrict_univ).toLinearIsometry.comp
    (extendByZeroLpₗᵢ ℝ volume U.isOpen.nullMeasurableSet (subset_univ _))).norm_map y

/-- The zero extension of the value of `w ∈ H¹₀(U)` is the value of its zero extension in
`H¹₀(ℝⁿ)`. -/
private theorem extendL_value (U : Opens (EuclideanSpace ℝ ι)) (w : W1p0 volume U 2) :
    extendL U (W1p.value (w : W1p volume U 2)) =
      castLpₗᵢ (𝕜 := ℝ) (Measure.restrict_coe_opens_top _)
        (W1p0.valueL (W1p0.extendByZeroL le_top w)) := by
  refine Lp.ext ?_
  filter_upwards [coeFn_castLpₗᵢ_extendByZeroLpₗᵢ ℝ U.isOpen.nullMeasurableSet
    (W1p.value (w : W1p volume U 2)), W1p0.value_extendByZeroL_top_ae w] with z h1 h2
  rw [extendL_apply, h1, coeFn_castLpₗᵢ, W1p0.valueL_apply, h2]

/-- Integrals over the whole space, as an open set, are integrals against `volume`. -/
private theorem setIntegral_top (F : EuclideanSpace ℝ ι → ℝ) :
    ∫ z in ((⊤ : Opens (EuclideanSpace ℝ ι)) : Set (EuclideanSpace ℝ ι)), F z = ∫ z, F z := by
  rw [Measure.restrict_coe_opens_top]

/-! ### A semigroup on `L²(U)`, extended by the identity off `U` -/

/-- The operator `J D P + (1 - J P)` on `L²(ℝⁿ)`, where `J` is extension by zero from `U`, `P`
restriction to `U` and `D` an operator on `L²(U)`. -/
private def extendOp (U : Opens (EuclideanSpace ℝ ι))
    (D : Lp ℝ 2 (volume.restrict (U : Set (EuclideanSpace ℝ ι))) →L[ℝ]
      Lp ℝ 2 (volume.restrict (U : Set (EuclideanSpace ℝ ι)))) :
    Lp ℝ 2 (volume : Measure (EuclideanSpace ℝ ι)) →L[ℝ]
      Lp ℝ 2 (volume : Measure (EuclideanSpace ℝ ι)) :=
  extendL U ∘L D ∘L restrictL U + (ContinuousLinearMap.id ℝ _ - extendL U ∘L restrictL U)

private theorem extendOp_apply (U : Opens (EuclideanSpace ℝ ι))
    (D : Lp ℝ 2 (volume.restrict (U : Set (EuclideanSpace ℝ ι))) →L[ℝ]
      Lp ℝ 2 (volume.restrict (U : Set (EuclideanSpace ℝ ι))))
    (x : Lp ℝ 2 (volume : Measure (EuclideanSpace ℝ ι))) :
    extendOp U D x = extendL U (D (restrictL U x)) + (x - extendL U (restrictL U x)) :=
  (rfl)

/-- A strongly continuous semigroup `D` on `L²(U)` acts on `L²(ℝⁿ)` as `J D(t) P` on functions
supported in `U` and as the identity on functions vanishing on `U`. This puts the Dirichlet
semigroups of a family of domains on one common space, as the Trotter–Kato theorem requires. -/
private def extendSemigroup (U : Opens (EuclideanSpace ℝ ι))
    (D : StronglyContinuousSemigroup (Lp ℝ 2 (volume.restrict (U : Set (EuclideanSpace ℝ ι))))) :
    StronglyContinuousSemigroup (Lp ℝ 2 (volume : Measure (EuclideanSpace ℝ ι))) where
  toFun t := extendOp U (D t)
  map_zero' := by
    ext1 x
    rw [extendOp_apply, D.map_zero_apply]
    simp
  map_add' s t := by
    ext1 x
    have hPJ (y) : restrictL U (extendL U y) = y :=
      LpToLpRestrictCLM_castLpₗᵢ_extendByZeroLpₗᵢ ℝ U.isOpen.nullMeasurableSet y
    simp only [ContinuousLinearMap.comp_apply, extendOp_apply, map_add, map_sub, hPJ, sub_self,
      add_zero, D.map_add_apply]
    abel
  continuousAt_zero' x := by
    have h := ((extendL U).continuous.continuousAt.comp (D.continuousAt_zero (restrictL U x))).add
      (continuousAt_const (y := x - extendL U (restrictL U x)))
    refine h.congr (Filter.Eventually.of_forall fun t => ?_)
    simp only [Pi.add_apply, Function.comp_apply, extendOp_apply]

private theorem extendSemigroup_apply (U : Opens (EuclideanSpace ℝ ι))
    (D : StronglyContinuousSemigroup (Lp ℝ 2 (volume.restrict (U : Set (EuclideanSpace ℝ ι)))))
    (t : ℝ≥0) (x : Lp ℝ 2 (volume : Measure (EuclideanSpace ℝ ι))) :
    extendSemigroup U D t x =
      extendL U (D t (restrictL U x)) + (x - extendL U (restrictL U x)) :=
  (rfl)

private theorem extendSemigroup_realOperator_apply (U : Opens (EuclideanSpace ℝ ι))
    (D : StronglyContinuousSemigroup (Lp ℝ 2 (volume.restrict (U : Set (EuclideanSpace ℝ ι)))))
    (t : ℝ) (x : Lp ℝ 2 (volume : Measure (EuclideanSpace ℝ ι))) :
    (extendSemigroup U D).realOperator t x =
      extendL U (D.realOperator t (restrictL U x)) + (x - extendL U (restrictL U x)) := by
  rw [StronglyContinuousSemigroup.realOperator_def, StronglyContinuousSemigroup.realOperator_def,
    extendSemigroup_apply]

/-- If `D` is a contraction semigroup, the extended semigroup is bounded by `3`. -/
private theorem hasGrowthBound_extendSemigroup (U : Opens (EuclideanSpace ℝ ι))
    (D : StronglyContinuousSemigroup (Lp ℝ 2 (volume.restrict (U : Set (EuclideanSpace ℝ ι)))))
    (hD : ∀ t, ‖D t‖ ≤ 1) : (extendSemigroup U D).HasGrowthBound 0 3 := by
  refine StronglyContinuousSemigroup.hasGrowthBound_of_bound (by norm_num) fun t _ => ?_
  rw [zero_mul, Real.exp_zero, mul_one, StronglyContinuousSemigroup.realOperator_def]
  refine ContinuousLinearMap.opNorm_le_bound _ (by norm_num) fun x => ?_
  have hP : ‖restrictL U x‖ ≤ ‖x‖ := norm_Lp_toLp_restrict_le _ x
  have hD' := ((D t.toNNReal).le_opNorm (restrictL U x)).trans
    (mul_le_of_le_one_left (norm_nonneg _) (hD t.toNNReal))
  rw [extendSemigroup_apply]
  calc _ ≤ ‖extendL U (D t.toNNReal (restrictL U x))‖ + (‖x‖ + ‖extendL U (restrictL U x)‖) :=
        (norm_add_le _ _).trans (add_le_add_right (norm_sub_le _ _) _)
    _ ≤ 3 * ‖x‖ := by
        rw [norm_extendL_apply, norm_extendL_apply]
        linarith

/-- The resolvent of the extended semigroup at `1`: `J R(1) P + (1 - J P)`. -/
private theorem resolvent_extendSemigroup_apply (U : Opens (EuclideanSpace ℝ ι))
    (D : StronglyContinuousSemigroup (Lp ℝ 2 (volume.restrict (U : Set (EuclideanSpace ℝ ι)))))
    (hD : D.HasGrowthBound 0 1) (hS : (extendSemigroup U D).HasGrowthBound 0 3)
    (x : Lp ℝ 2 (volume : Measure (EuclideanSpace ℝ ι))) :
    (extendSemigroup U D).resolvent hS 1 one_pos x =
      extendL U (D.resolvent hD 1 one_pos (restrictL U x)) + (x - extendL U (restrictL U x)) := by
  have hint := D.integrableOn_resolvent_integrand hD 1 one_pos (restrictL U x)
  have hexp : IntegrableOn (fun t : ℝ => Real.exp (-(1 * t))) (Ioi 0) := by
    simpa only [one_mul] using integrableOn_exp_neg_Ioi 0
  have hfun : (fun t => Real.exp (-(1 * t)) • (extendSemigroup U D).realOperator t x) =
      fun t => extendL U (Real.exp (-(1 * t)) • D.realOperator t (restrictL U x)) +
        Real.exp (-(1 * t)) • (x - extendL U (restrictL U x)) := by
    funext t
    rw [extendSemigroup_realOperator_apply, smul_add, map_smul]
  rw [StronglyContinuousSemigroup.resolvent_apply, StronglyContinuousSemigroup.resolvent_apply,
    hfun, integral_add ((extendL U).integrable_comp hint) (hexp.smul_const _),
    (extendL U).integral_comp_comm hint, integral_smul_const]
  simp only [one_mul, integral_exp_neg_Ioi_zero, one_smul]

/-! ### The resolvents at `1` as weak solutions of `-Δu + u = f` -/

attribute [local instance] W1p0.instNormedAddCommGroup W1p0.instInnerProductSpace

open InnerProductSpace Laplacian
open scoped InnerProductSpace

variable [DecidableEq ι]

/-- The energy form of `-Δ + 1` is that of `-Δ` plus the `L²` pairing. -/
private theorem energyFormH1_one_zero_one {Omega : Opens (EuclideanSpace ℝ ι)}
    (u v : W1p volume Omega 2) :
    energyFormH1 (fun _ => (1 : Matrix ι ι ℝ)) 0 (fun _ => 1) u v =
      energyFormH1 (fun _ => (1 : Matrix ι ι ℝ)) 0 0 u v + ⟪W1p.value u, W1p.value v⟫_ℝ := by
  have h := energyFormH1_mass_sub_const
    (memLp_energyIntegrand_const_zero_zero (mu := volume) (Omega := Omega) 1) (-1) u v
  have hc : (fun x : EuclideanSpace ℝ ι => (0 : EuclideanSpace ℝ ι → ℝ) x - -1) = fun _ => 1 := by
    funext x
    simp
  rw [hc] at h
  rw [h]
  ring

/-- **The resolvent of the Dirichlet semigroup of `-Δ` at `1`.** On an open set `U` where the
energy form of `-Δ` is coercive, `R(1) z` is the value of the weak solution `w ∈ H¹₀(U)` of
`-Δw + w = z`. -/
private theorem exists_value_eq_resolvent_dirichletSemigroup {U : Opens (EuclideanSpace ℝ ι)}
    (hcoercive : IsCoercive (energyFormH1L0
      (memLp_energyIntegrand_const_zero_zero (mu := volume) (Omega := U) (1 : Matrix ι ι ℝ))))
    (z : Lp ℝ 2 (volume.restrict (U : Set (EuclideanSpace ℝ ι)))) :
    ∃ w : W1p0 volume U 2,
      W1p.value (w : W1p volume U 2) =
        LinearPMap.resolvent
          (dirichletSemigroup _ hcoercive).toStronglyContinuousSemigroup.generator 1 z ∧
      IsWeakSolutionDirichlet (fun _ => (1 : Matrix ι ι ℝ)) 0 (fun _ => 1) z w := by
  set L := dirichletOperator _ hcoercive
  rw [dirichletSemigroup_generator]
  have hres : (1 : ℝ) ∈ LinearPMap.resolventSet (-L) := by
    simpa only [dirichletSemigroup_generator] using
      (dirichletSemigroup _ hcoercive).mem_resolventSet_generator one_pos
  set y := LinearPMap.resolvent (-L) 1 z
  have hy : y ∈ L.domain := LinearPMap.resolvent_mem_domain hres z
  -- The generator is `-L`, so `-L y = y - z`, that is `L y = z - y`.
  have hLy : L ⟨y, hy⟩ = z - y := by
    have h := LinearPMap.apply_resolvent hres z
    rw [LinearPMap.neg_apply, one_smul] at h
    rw [← neg_sub, ← h, neg_neg]
  obtain ⟨w, hw, hsol⟩ := (mem_graph_dirichletOperator_iff _ hcoercive).1
    (hLy ▸ L.mem_graph ⟨y, hy⟩)
  refine ⟨w, hw, (isWeakSolutionDirichlet_iff_inner _ _).2 fun v => ?_⟩
  rw [energyFormH1_one_zero_one, (isWeakSolutionDirichlet_iff_inner _ _).1 hsol v, hw,
    inner_sub_left, sub_add_cancel]

/-- **The resolvent of the heat semigroup at `1`.** For `x ∈ L²(ℝⁿ)`, `R(1) x` is the weak
solution `u ∈ H¹(ℝⁿ)` of `-Δu + u = x`; here `f` and `y` are `x` and the value of `u`, read in
`L²` of the whole space as an open set and in `L²(ℝⁿ)` respectively. -/
private theorem resolvent_heatSemigroup_eq (x : Lp ℝ 2 (volume : Measure (EuclideanSpace ℝ ι)))
    {f : Lp ℝ 2 (volume.restrict ((⊤ : Opens (EuclideanSpace ℝ ι)) : Set (EuclideanSpace ℝ ι)))}
    (hfx : ∀ z, f z = x z) {u : W1p0 volume (⊤ : Opens (EuclideanSpace ℝ ι)) 2}
    (hu : IsWeakSolutionDirichlet (fun _ => (1 : Matrix ι ι ℝ)) 0 (fun _ => 1) f u)
    {y : Lp ℝ 2 (volume : Measure (EuclideanSpace ℝ ι))}
    (hyz : ∀ z, y z = W1p.value (u : W1p volume ⊤ 2) z) :
    LinearPMap.resolvent (heatSemigroup (E := EuclideanSpace ℝ ι) (F := ℝ) (p := 2)
      ENNReal.ofNat_ne_top).toStronglyContinuousSemigroup.generator 1 x = y := by
  have hres := (heatSemigroup (E := EuclideanSpace ℝ ι) (F := ℝ) (p := 2)
    ENNReal.ofNat_ne_top).mem_resolventSet_generator one_pos
  rw [generator_heatSemigroup_eq_weakLaplacianLp] at hres ⊢
  -- `u` solves `-Δu = f - u` weakly, hence in the sense of distributions.
  have h0 : IsWeakSolutionDirichlet (fun _ => (1 : Matrix ι ι ℝ)) 0 0
      (f - W1p.value (u : W1p volume ⊤ 2)) u := by
    refine (isWeakSolutionDirichlet_iff_inner _ _).2 fun v => ?_
    have h := (isWeakSolutionDirichlet_iff_inner _ _).1 hu v
    rw [energyFormH1_one_zero_one] at h
    rw [inner_sub_left, ← h, add_sub_cancel_right]
  have hdist := (isWeakSolutionDirichlet_one_zero_zero_iff_forall_neg_setIntegral_laplacian_mul_eq
    _ u).1 h0
  have hgraph : (y, y - x) ∈ (weakLaplacianLp (EuclideanSpace ℝ ι) ℝ 2).graph := by
    refine mem_graph_weakLaplacianLp_iff.2 fun φ => ?_
    have h := hdist φ
    rw [setIntegral_top, setIntegral_top] at h
    have hsub := (Lp.coeFn_sub f (W1p.value (u : W1p volume ⊤ 2))).filter_mono
      Measure.ae_le_ae_restrict_coe_opens_top
    calc ∫ z, Δ (φ : EuclideanSpace ℝ ι → ℝ) z • y z
        = ∫ z, Δ (φ : EuclideanSpace ℝ ι → ℝ) z * W1p.value (u : W1p volume ⊤ 2) z := by
          simp_rw [smul_eq_mul, hyz]
      _ = -∫ z, ⇑(f - W1p.value (u : W1p volume (⊤ : Opens (EuclideanSpace ℝ ι)) 2)) z * φ z := by
          rw [← h, neg_neg]
      _ = ∫ z, φ z • (y - x) z := by
          rw [← integral_neg]
          refine integral_congr_ae ?_
          filter_upwards [hsub, Lp.coeFn_sub y x] with z h1 h2
          rw [h1, h2, Pi.sub_apply, Pi.sub_apply, smul_eq_mul, hyz, hfx]
          ring
  obtain ⟨y', hy', hAy'⟩ := (LinearPMap.mem_graph_iff _).1 hgraph
  have h := LinearPMap.resolvent_smul_sub_apply hres y'
  rwa [hAy', hy', one_smul, sub_sub_cancel] at h

/-! ### The heat flows of an exhaustion -/

/-- The resolvent at `1` of the extended Dirichlet semigroup of `U` is `J w + (y - J P y)`, where
`w ∈ H¹₀(U)` is the weak solution of `-Δw + w = P y`, read through its zero extension to `ℝⁿ`. -/
private theorem resolvent_extendSemigroup_dirichletSemigroup {U : Opens (EuclideanSpace ℝ ι)}
    (hcoercive : IsCoercive (energyFormH1L0
      (memLp_energyIntegrand_const_zero_zero (mu := volume) (Omega := U) (1 : Matrix ι ι ℝ))))
    (y : Lp ℝ 2 (volume : Measure (EuclideanSpace ℝ ι))) :
    ∃ w : W1p0 volume U 2,
      IsWeakSolutionDirichlet (fun _ => (1 : Matrix ι ι ℝ)) 0 (fun _ => 1) (restrictL U y) w ∧
      LinearPMap.resolvent (extendSemigroup U
        (dirichletSemigroup _ hcoercive).toStronglyContinuousSemigroup).generator 1 y =
        castLpₗᵢ (𝕜 := ℝ) (Measure.restrict_coe_opens_top _)
          (W1p0.valueL (W1p0.extendByZeroL le_top w)) +
          (y - extendL U (restrictL U y)) := by
  obtain ⟨w, hw, hsol⟩ := exists_value_eq_resolvent_dirichletSemigroup hcoercive (restrictL U y)
  refine ⟨w, hsol, ?_⟩
  have hD := (dirichletSemigroup _ hcoercive).hasGrowthBound
  have hS := hasGrowthBound_extendSemigroup U _ (dirichletSemigroup _ hcoercive).contracting
  rw [StronglyContinuousSemigroup.generator_resolvent_eq _ hS one_pos,
    resolvent_extendSemigroup_apply _ _ hD, ← StronglyContinuousSemigroup.generator_resolvent_eq,
    ← hw, extendL_value]

/-- The energy form of `-Δ + 1` is coercive on `H¹(ℝⁿ)`. -/
private theorem exists_isCoercive_laplacian_add_one_top :
    ∃ hcoeff : MemLp (fun x => energyIntegrand ((fun _ => (1 : Matrix ι ι ℝ)) x)
        ((0 : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι) x) ((fun _ => (1 : ℝ)) x)) ⊤
        (volume.restrict ((⊤ : Opens (EuclideanSpace ℝ ι)) : Set (EuclideanSpace ℝ ι))),
      IsCoercive (energyFormH1L0 hcoeff) :=
  ⟨memLp_top_const (energyIntegrand (1 : Matrix ι ι ℝ) 0 1),
    UniformlyEllipticOn.isCoercive_energyFormH1L0_of_mass_lower_bound
      (uniformlyEllipticOn_const_one_one _) aestronglyMeasurable_const aestronglyMeasurable_const
      aestronglyMeasurable_const (beta := 0) (gamma := 1) (delta := 1) (by simp) (by simp)
      (by simp) (by norm_num) _⟩

/-- **The resolvents converge along the exhaustion.** The resolvents at `1` of the extended
Dirichlet semigroups of the `U k` converge strongly to the resolvent of the heat semigroup. This
is the stationary comparison `TauCeti.PDE.tendsto_extendByZeroL_of_isWeakSolutionDirichlet` for
`-Δ + 1`, together with the exhaustion of `L²(ℝⁿ)`. -/
private theorem tendsto_resolvent_extendSemigroup {κ : Type*} [Preorder κ] [IsDirectedOrder κ]
    [Nonempty κ] {U : κ → Opens (EuclideanSpace ℝ ι)} (hmono : Monotone U)
    (hcover : ⋃ k, (U k : Set (EuclideanSpace ℝ ι)) = univ)
    (hcoercive : ∀ k, IsCoercive (energyFormH1L0
      (memLp_energyIntegrand_const_zero_zero (mu := volume) (Omega := U k) (1 : Matrix ι ι ℝ))))
    (y : Lp ℝ 2 (volume : Measure (EuclideanSpace ℝ ι))) :
    Tendsto (fun k => LinearPMap.resolvent (extendSemigroup (U k)
        (dirichletSemigroup _ (hcoercive k)).toStronglyContinuousSemigroup).generator 1 y) atTop
      (𝓝 (LinearPMap.resolvent (heatSemigroup (E := EuclideanSpace ℝ ι) (F := ℝ) (p := 2)
        ENNReal.ofNat_ne_top).toStronglyContinuousSemigroup.generator 1 y)) := by
  choose w hsol hres using fun k =>
    resolvent_extendSemigroup_dirichletSemigroup (hcoercive k) y
  simp_rw [hres]
  -- The solutions `w k` converge in `H¹` to the solution `u` of `-Δu + u = y` on `ℝⁿ`.
  obtain ⟨hcoeff, hcoercive₁⟩ := exists_isCoercive_laplacian_add_one_top (ι := ι)
  have htop := Measure.restrict_coe_opens_top (volume : Measure (EuclideanSpace ℝ ι))
  set f := castLpₗᵢ (𝕜 := ℝ) htop.symm y
  have hfy : ∀ z, f z = y z := coeFn_castLpₗᵢ (𝕜 := ℝ) htop.symm y
  obtain ⟨u, hu, -⟩ := existsUnique_isWeakSolutionDirichlet hcoeff hcoercive₁ f
  have hlim := tendsto_extendByZeroL_of_isWeakSolutionDirichlet hcoeff hcoercive₁ hu hmono
    (fun k => le_top) (by rw [hcover]; exact subset_univ _) (w := w) fun k v => by
      rw [(isWeakSolutionDirichlet_iff _ _).1 (hsol k) v]
      refine integral_congr_ae ?_
      filter_upwards [LpToLpRestrictCLM_coeFn (𝕜 := ℝ) (U k : Set (EuclideanSpace ℝ ι)) y]
        with z hz
      rw [restrictL_apply, hz, hfy]
  have h := ((((castLpₗᵢ (𝕜 := ℝ) htop).continuous.comp
    (W1p0.valueL (mu := volume) (Omega := ⊤) (p := 2)).continuous).tendsto u).comp hlim).add
      (tendsto_sub_castLpₗᵢ_extendByZeroLpₗᵢ_LpToLpRestrictCLM ℝ ENNReal.ofNat_ne_top
      (fun k => (U k).isOpen) (fun _ _ h => hmono h) hcover y)
  rw [add_zero] at h
  rwa [resolvent_heatSemigroup_eq y hfy hu
    (y := castLpₗᵢ (𝕜 := ℝ) (Measure.restrict_coe_opens_top _) (W1p0.valueL u)) fun z => by
      rw [W1p0.valueL_apply]
      exact coeFn_castLpₗᵢ (𝕜 := ℝ) (Measure.restrict_coe_opens_top _) _ z]

/-- **The Dirichlet heat flows of an exhaustion converge to the heat flow of `ℝⁿ`.** Let `U k` be
a monotone family of open subsets of `ℝⁿ`, indexed by a directed order, that covers `ℝⁿ`, such
that the energy form of `-Δ` is coercive on each `H¹₀(U k)`, as it is for bounded `U k`
(`TauCeti.PDE.exists_isCoercive_laplacian_of_isBounded`). For `x ∈ L²(ℝⁿ)`, solve the heat
equation on `U k` with the Dirichlet boundary condition and initial value the restriction of `x`
to `U k`, by the Dirichlet semigroup `e^{tΔ_{U k}}`, and extend the solution by zero. Then, as `k`
grows, these extended solutions converge in `L²(ℝⁿ)` to the solution `e^{tΔ} x` of the heat
equation on `ℝⁿ`, uniformly for `t` in every interval `[0, τ]`. -/
theorem tendstoUniformlyOn_dirichletSemigroup_heatSemigroup {κ : Type*} [Preorder κ]
    [IsDirectedOrder κ] [Nonempty κ] {U : κ → Opens (EuclideanSpace ℝ ι)} (hmono : Monotone U)
    (hcover : ⋃ k, (U k : Set (EuclideanSpace ℝ ι)) = univ)
    (hcoercive : ∀ k, IsCoercive (energyFormH1L0
      (memLp_energyIntegrand_const_zero_zero (mu := volume) (Omega := U k) (1 : Matrix ι ι ℝ))))
    (x : Lp ℝ 2 (volume : Measure (EuclideanSpace ℝ ι))) (τ : ℝ≥0) :
    TendstoUniformlyOn
      (fun k (t : ℝ≥0) => castLpₗᵢ (𝕜 := ℝ) Measure.restrict_univ
        (extendByZeroLpₗᵢ ℝ volume (U k).isOpen.nullMeasurableSet (subset_univ _)
          (dirichletSemigroup _ (hcoercive k) t
            (LpToLpRestrictCLM (EuclideanSpace ℝ ι) ℝ ℝ volume 2 (U k) x))))
      (fun t => heatSemigroup (E := EuclideanSpace ℝ ι) (F := ℝ) (p := 2) ENNReal.ofNat_ne_top t x)
      atTop (Iic τ) := by
  have hS := fun k => hasGrowthBound_extendSemigroup (U k) _
    (dirichletSemigroup _ (hcoercive k)).contracting
  have hT := (heatSemigroup (E := EuclideanSpace ℝ ι) (F := ℝ) (p := 2)
    ENNReal.ofNat_ne_top).hasGrowthBound_of_one_le_const (M := 3) (by norm_num)
  have h := StronglyContinuousSemigroup.tendstoUniformlyOn_realOperator_apply_of_tendsto_resolvent
    hS hT one_pos (tendsto_resolvent_extendSemigroup hmono hcover hcoercive) x τ
  -- Remove the part of `x` outside `U k`, which does not depend on the time.
  have h' := (h.comp ((↑) : ℝ≥0 → ℝ)).sub
    ((tendsto_sub_castLpₗᵢ_extendByZeroLpₗᵢ_LpToLpRestrictCLM ℝ ENNReal.ofNat_ne_top
      (fun k => (U k).isOpen) (fun _ _ h => hmono h) hcover x).tendstoUniformlyOn_const
      (((↑) : ℝ≥0 → ℝ) ⁻¹' Icc 0 τ))
  refine ((h'.mono (s' := Iic τ) fun t ht => ⟨t.coe_nonneg, NNReal.coe_le_coe.mpr ht⟩).congr_right
    fun t _ => ?_).congr (Eventually.of_forall fun k t _ => ?_)
  · simp only [Pi.sub_apply, Function.comp_apply, StronglyContinuousSemigroup.realOperator_coe,
      sub_zero, ContractionSemigroup.toStronglyContinuousSemigroup_apply]
  · simp only [Pi.sub_apply, Function.comp_apply, StronglyContinuousSemigroup.realOperator_coe,
      extendSemigroup_apply, extendL_apply, restrictL_apply, add_sub_cancel_right,
      ContractionSemigroup.toStronglyContinuousSemigroup_apply]

/-- **The Dirichlet heat flows of an exhaustion converge to the heat flow of `ℝⁿ`**, at a fixed
time `t`: the zero extensions of `e^{tΔ_{U k}} (x|_{U k})` converge to `e^{tΔ} x` in `L²(ℝⁿ)`. This
is `TauCeti.PDE.tendstoUniformlyOn_dirichletSemigroup_heatSemigroup` at a single time. -/
theorem tendsto_dirichletSemigroup_heatSemigroup {κ : Type*} [Preorder κ]
    [IsDirectedOrder κ] [Nonempty κ] {U : κ → Opens (EuclideanSpace ℝ ι)} (hmono : Monotone U)
    (hcover : ⋃ k, (U k : Set (EuclideanSpace ℝ ι)) = univ)
    (hcoercive : ∀ k, IsCoercive (energyFormH1L0
      (memLp_energyIntegrand_const_zero_zero (mu := volume) (Omega := U k) (1 : Matrix ι ι ℝ))))
    (x : Lp ℝ 2 (volume : Measure (EuclideanSpace ℝ ι))) (t : ℝ≥0) :
    Tendsto
      (fun k => castLpₗᵢ (𝕜 := ℝ) Measure.restrict_univ
        (extendByZeroLpₗᵢ ℝ volume (U k).isOpen.nullMeasurableSet (subset_univ _)
          (dirichletSemigroup _ (hcoercive k) t
            (LpToLpRestrictCLM (EuclideanSpace ℝ ι) ℝ ℝ volume 2 (U k) x))))
      atTop
      (𝓝 (heatSemigroup (E := EuclideanSpace ℝ ι) (F := ℝ) (p := 2) ENNReal.ofNat_ne_top t x)) :=
  (tendstoUniformlyOn_dirichletSemigroup_heatSemigroup hmono hcover hcoercive x t).tendsto_at
    (le_refl t)

end PDE

end TauCeti
