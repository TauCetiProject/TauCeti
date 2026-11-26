/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Pseudodifferential.Manifold.Smoothing
import TauCeti.Analysis.Pseudodifferential.SmoothKernel
import TauCeti.Geometry.Manifold.ContMDiff.ParametricIntegral.Basic

/-!
# Integral operators with smooth kernels on a manifold

Let `M` be a manifold modelled on `ℝⁿ` and `μ` a measure on `M` with a smooth density in every
chart `e` of the maximal smooth atlas: there is a function `ρ`, smooth on the chart target, with

`∫ f dμ = ∫_{e.target} ρ(y) f(e⁻¹ y) dy`

for every continuous compactly supported `f` supported in the chart source. Measures given by
smooth densities, such as Riemannian volumes, are of this kind. This file shows that an operator
`P` on the complex-valued smooth functions on `M` given by a smooth compactly supported kernel,

`P u (x) = ∫ K(x, y) u(y) dμ(y)`,

is an operator of order `-∞` (`TauCeti.smoothingPseudodifferentialOperators`), as in Hörmander
(III, §18.1). Such operators are the remainders of the pseudodifferential calculus, and the
finite-rank projections of elliptic theory, onto spans of smooth compactly supported functions,
are of this form. For a measure that is also finite on compact sets the file constructs the
operator itself (`TauCeti.integralOperator`).

* `TauCeti.isProperlySupported_of_forall_apply_eq_integral`: an operator with a compactly supported
  kernel is properly supported: its outputs are supported in the first projection of the support
  of the kernel, and it only sees its input on the second projection. No smoothness and no density
  are needed here.
* `TauCeti.mem_smoothingPseudodifferentialOperators_of_forall_apply_eq_integral`: **an operator
  with a smooth compactly supported kernel has order `-∞`.** In a chart `e`, with cutoffs `φ` and
  `ψ`, its compression is the Euclidean integral operator with kernel
  `φ(x) ψ(y) ρ(y) K(e⁻¹ x, e⁻¹ y)`, a smooth compactly supported function on `ℝⁿ × ℝⁿ`, so it is
  the quantization of the smoothing symbol `TauCeti.Symbol.ofKernel` of that kernel.
* `TauCeti.mem_smoothingPseudodifferentialOperators_of_forall_apply_eq_integral_smul`: the
  rank-one operators `u ↦ (∫ g u dμ) f`, with smooth compactly supported `f` and `g`, have
  order `-∞`.
* `TauCeti.integralOperator`: for a measure that is finite on compact sets, the operator
  `u ↦ (x ↦ ∫ K(x, y) u(y) dμ(y))`; the integral is smooth in `x` because `K(x, ·)` vanishes off a
  fixed compact set. When `μ` has smooth chart densities it has order `-∞`
  (`TauCeti.integralOperator_mem_smoothingPseudodifferentialOperators`).

## References

* L. Hörmander, *The Analysis of Linear Partial Differential Operators III*, §18.1 (the operators
  of order `-∞` are those with smooth kernels).
* M. Taylor, *Pseudodifferential Operators: Four Lectures at MSRI* (2008), Lecture I, §8.
-/

public section

open MeasureTheory Set Filter
open scoped ContDiff Manifold Distributions SchwartzMap Topology

namespace TauCeti

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (CoordinateSpace n) M]
  [T2Space M] [MeasurableSpace M] {μ : Measure M} {K : M × M → ℂ}
  {P : C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯ →ₗ[ℂ]
    C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯}

/-- **Operators with compactly supported kernels are properly supported.** If
`P u (x) = ∫ K(x, y) u(y) dμ(y)` for a kernel `K` with compact support, then `P u` is supported in
the first projection of the support of `K`, and `P u` vanishes as soon as `u` vanishes on the second
projection. -/
theorem isProperlySupported_of_forall_apply_eq_integral (hKc : HasCompactSupport K)
    (hP : ∀ u x, P u x = ∫ y, K (x, y) * u y ∂μ) : IsProperlySupported P := by
  -- The kernel vanishes at `(x, y)` unless `x ∈ A` and `y ∈ B`, the projections of its support.
  set A := Prod.fst '' tsupport K
  set B := Prod.snd '' tsupport K
  have hA : IsCompact A := hKc.isCompact.image continuous_fst
  have hB : IsCompact B := hKc.isCompact.image continuous_snd
  have hK {x y : M} (h : x ∉ A ∨ y ∉ B) : K (x, y) = 0 :=
    image_eq_zero_of_notMem_tsupport fun hxy ↦ h.elim (· ⟨_, hxy, rfl⟩) (· ⟨_, hxy, rfl⟩)
  refine isProperlySupported_iff.2 fun _ _ ↦ ⟨A ∪ B, hA.union hB, fun f _ ↦ ?_, fun f hf x _ ↦ ?_⟩
  · refine (closure_minimal (fun x hx ↦ ?_) hA.isClosed).trans subset_union_left
    by_contra hxA
    exact hx (by simp [hP, hK (.inl hxA)])
  · rw [hP, ← integral_zero M ℂ]
    refine integral_congr_ae (.of_forall fun y ↦ ?_)
    by_cases hy : y ∈ B
    · simp [hf.self_of_nhdsSet y (mem_union_right A hy)]
    · simp [hK (.inr hy)]

omit [T2Space M] [MeasurableSpace M] in
/-- A smooth kernel `K` on `M × M`, read in two charts `e`, `e'` of the maximal atlas and
localized by cutoffs `φ`, `ψ` in their targets and a function `ρ` smooth on the target of `e'`, is
a smooth function on `ℝⁿ × ℝⁿ`. -/
private theorem contDiff_chartKernel {e e' : OpenPartialHomeomorph M (CoordinateSpace n)}
    (he : e ∈ IsManifold.maximalAtlas 𝓘(ℝ, CoordinateSpace n) ∞ M)
    (he' : e' ∈ IsManifold.maximalAtlas 𝓘(ℝ, CoordinateSpace n) ∞ M)
    (φ : 𝓓(⟨e.target, e.open_target⟩, ℝ)) (ψ : 𝓓(⟨e'.target, e'.open_target⟩, ℝ))
    {ρ : CoordinateSpace n → ℝ} (hρ : ContDiffOn ℝ ∞ ρ e'.target)
    (hK : ContMDiff (𝓘(ℝ, CoordinateSpace n).prod 𝓘(ℝ, CoordinateSpace n)) 𝓘(ℝ, ℂ) ∞ K) :
    ContDiff ℝ ∞ fun p : CoordinateSpace n × CoordinateSpace n ↦
      ((φ p.1 * (ψ p.2 * ρ p.2) : ℝ) : ℂ) * K (e.symm p.1, e'.symm p.2) := by
  -- On the product of the chart targets, the kernel read in the charts is smooth.
  have hKe : ContDiffOn ℝ ∞ (fun p : CoordinateSpace n × CoordinateSpace n ↦
      K (e.symm p.1, e'.symm p.2)) (e.target ×ˢ e'.target) := by
    have h := hK.comp_contMDiffOn ((contMDiffOn_symm_of_mem_maximalAtlas he).prodMap
      (contMDiffOn_symm_of_mem_maximalAtlas he'))
    rw [← modelWithCornersSelf_prod, chartedSpaceSelf_prod] at h
    exact contMDiffOn_iff_contDiffOn.1 h
  have hc : ContDiffOn ℝ ∞ (fun p : CoordinateSpace n × CoordinateSpace n ↦
      φ p.1 * (ψ p.2 * ρ p.2)) (e.target ×ˢ e'.target) :=
    (φ.contDiff.comp contDiff_fst).contDiffOn.mul ((ψ.contDiff.comp contDiff_snd).contDiffOn.mul
      (hρ.comp contDiff_snd.contDiffOn fun _ hp ↦ hp.2))
  refine contDiff_iff_contDiffAt.2 fun p ↦ ?_
  by_cases hp : p ∈ e.target ×ˢ e'.target
  · exact ((Complex.ofRealCLM.contDiff.comp_contDiffOn hc).mul hKe).contDiffAt
      ((e.open_target.prod e'.open_target).mem_nhds hp)
  -- Off the product of the chart targets, `p` lies outside the product of the supports of the
  -- cutoffs, a closed set off which the function vanishes.
  have hp' : p ∉ tsupport φ ×ˢ tsupport ψ := fun h ↦
    hp ⟨φ.tsupport_subset h.1, ψ.tsupport_subset h.2⟩
  refine (contDiffAt_const (c := (0 : ℂ))).congr_of_eventuallyEq (Filter.mem_of_superset
    (((isClosed_tsupport φ).prod (isClosed_tsupport ψ)).isOpen_compl.mem_nhds hp') fun q hq ↦ ?_)
  rcases not_and_or.1 hq with hq | hq
  · simp [image_eq_zero_of_notMem_tsupport hq]
  · simp [image_eq_zero_of_notMem_tsupport hq]

omit [ChartedSpace (CoordinateSpace n) M] [T2Space M] [MeasurableSpace M] in
/-- The kernel of `TauCeti.contDiff_chartKernel` has compact support, in the product of the
supports of the cutoffs. -/
private theorem hasCompactSupport_chartKernel {e e' : OpenPartialHomeomorph M (CoordinateSpace n)}
    (φ : 𝓓(⟨e.target, e.open_target⟩, ℝ)) (ψ : 𝓓(⟨e'.target, e'.open_target⟩, ℝ))
    (ρ : CoordinateSpace n → ℝ) :
    HasCompactSupport fun p : CoordinateSpace n × CoordinateSpace n ↦
      ((φ p.1 * (ψ p.2 * ρ p.2) : ℝ) : ℂ) * K (e.symm p.1, e'.symm p.2) := by
  refine HasCompactSupport.intro (φ.hasCompactSupport.isCompact.prod ψ.hasCompactSupport.isCompact)
    fun p hp ↦ ?_
  rcases not_and_or.1 hp with hp | hp
  · simp [image_eq_zero_of_notMem_tsupport hp]
  · simp [image_eq_zero_of_notMem_tsupport hp]

/-- Against a measure that is finite on compact sets, `y ↦ K(x, y) u(y)` is integrable for a
continuous compactly supported kernel `K` and a continuous `u`. -/
private theorem integrable_mul [OpensMeasurableSpace M] [IsFiniteMeasureOnCompacts μ]
    (hK : Continuous K) (hKc : HasCompactSupport K) {u : M → ℂ} (hu : Continuous u) (x : M) :
    Integrable (fun y ↦ K (x, y) * u y) μ :=
  Continuous.integrable_of_hasCompactSupport (f := fun y ↦ K (x, y) * u y)
    ((hK.comp (continuous_const.prodMk continuous_id)).mul hu)
    (HasCompactSupport.intro (hKc.isCompact.image continuous_snd) fun y hy ↦ by
      rw [image_eq_zero_of_notMem_tsupport fun h ↦ hy ⟨_, h, rfl⟩, zero_mul])

/-! ### The integral operator of a smooth kernel -/

section IntegralOperator

variable [IsManifold 𝓘(ℝ, CoordinateSpace n) ∞ M] [OpensMeasurableSpace M]

/-- The integral `x ↦ ∫ K(x, y) u(y) dμ(y)` of a smooth compactly supported kernel against a
smooth function is smooth, since `K(x, ·)` vanishes off the second projection of the support of
`K`, a compact set of finite measure. -/
private theorem contMDiff_integral_mul (μ : Measure M) [IsFiniteMeasureOnCompacts μ]
    (hK : ContMDiff (𝓘(ℝ, CoordinateSpace n).prod 𝓘(ℝ, CoordinateSpace n)) 𝓘(ℝ, ℂ) ∞ K)
    (hKc : HasCompactSupport K) (u : C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯) :
    ContMDiff 𝓘(ℝ, CoordinateSpace n) 𝓘(ℝ, ℂ) ∞ fun x ↦ ∫ y, K (x, y) * u y ∂μ := fun _ ↦
  (hKc.isCompact.image continuous_snd).contMDiffAt_parametric_integral
    (hKc.isCompact.image continuous_snd).measure_lt_top.ne
    (fun _ _ ↦ (hK.mul (u.contMDiff.comp contMDiff_snd)) _)
    (.of_forall fun x y hy ↦ by
      rw [image_eq_zero_of_notMem_tsupport fun h ↦ hy ⟨(x, y), h, rfl⟩, zero_mul])

/-- **The integral operator of a smooth kernel.** For a measure `μ` that is finite on compact sets
and a smooth compactly supported kernel `K` on `M × M`, the operator
`u ↦ (x ↦ ∫ K(x, y) u(y) dμ(y))` on the complex-valued smooth functions on `M`. When `μ` has
smooth chart densities it has order `-∞`
(`TauCeti.integralOperator_mem_smoothingPseudodifferentialOperators`). -/
noncomputable def integralOperator (μ : Measure M) [IsFiniteMeasureOnCompacts μ]
    (hK : ContMDiff (𝓘(ℝ, CoordinateSpace n).prod 𝓘(ℝ, CoordinateSpace n)) 𝓘(ℝ, ℂ) ∞ K)
    (hKc : HasCompactSupport K) :
    C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯ →ₗ[ℂ]
      C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯ where
  toFun u := ⟨fun x ↦ ∫ y, K (x, y) * u y ∂μ, contMDiff_integral_mul μ hK hKc u⟩
  map_add' u v := by
    ext x
    simp only [ContMDiffMap.coeFn_mk, ContMDiffMap.coe_add, Pi.add_apply, mul_add]
    exact integral_add (integrable_mul hK.continuous hKc u.contMDiff.continuous x)
      (integrable_mul hK.continuous hKc v.contMDiff.continuous x)
  map_smul' a u := by
    ext x
    -- `ContMDiffMap.complex_smul_apply` rewrites `a • _` once the integral is a bundled map.
    refine (integral_congr_ae (.of_forall fun y ↦ ?_)).trans ((integral_const_mul a _).trans
      (ContMDiffMap.complex_smul_apply a ⟨fun x ↦ ∫ y, K (x, y) * u y ∂μ, 
        contMDiff_integral_mul μ hK hKc u⟩ x).symm)
    simp only [ContMDiffMap.complex_smul_apply]
    ring

@[simp]
theorem integralOperator_apply (μ : Measure M) [IsFiniteMeasureOnCompacts μ]
    (hK : ContMDiff (𝓘(ℝ, CoordinateSpace n).prod 𝓘(ℝ, CoordinateSpace n)) 𝓘(ℝ, ℂ) ∞ K)
    (hKc : HasCompactSupport K) (u : C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯) (x : M) :
    integralOperator μ hK hKc u x = ∫ y, K (x, y) * u y ∂μ :=
  (rfl)

end IntegralOperator

section Density

/-! ### Measures with smooth chart densities -/

variable (hμ : ∀ e : OpenPartialHomeomorph M (CoordinateSpace n),
  e ∈ IsManifold.maximalAtlas 𝓘(ℝ, CoordinateSpace n) ∞ M →
    ∃ ρ : CoordinateSpace n → ℝ, ContDiffOn ℝ ∞ ρ e.target ∧
      ∀ f : M → ℂ, Continuous f → HasCompactSupport f → tsupport f ⊆ e.source →
        ∫ x, f x ∂μ = ∫ y in e.target, (ρ y : ℂ) * f (e.symm y))

/-- **The kernel read in a chart.** If `μ` has the density `ρ` in the chart `c`, then integrating
`K(x, ·)` against a function `(θ g) ∘ c` pulled back from the chart is integrating
`θ(w) ρ(w) K(x, c⁻¹ w) g(w)` over `ℝⁿ`. -/
private theorem integral_mul_complexCutoffPullback {c : OpenPartialHomeomorph M (CoordinateSpace n)}
    (hc : c ∈ IsManifold.maximalAtlas 𝓘(ℝ, CoordinateSpace n) ∞ M) {ρ : CoordinateSpace n → ℝ}
    (hint : ∀ f : M → ℂ, Continuous f → HasCompactSupport f → tsupport f ⊆ c.source →
      ∫ x, f x ∂μ = ∫ y in c.target, (ρ y : ℂ) * f (c.symm y))
    (hK : Continuous K) (θ : 𝓓(⟨c.target, c.open_target⟩, ℝ))
    (g : C^∞⟮𝓘(ℝ, CoordinateSpace n), CoordinateSpace n; 𝓘(ℝ, ℂ), ℂ⟯) (x : M) :
    ∫ y, K (x, y) * c.complexCutoffPullback hc θ g y ∂μ =
      ∫ w, ((θ w * ρ w : ℝ) : ℂ) * K (x, c.symm w) * g w := by
  set v := c.complexCutoffPullback hc θ g
  -- The integrand on `M` is supported in the compact set `c⁻¹ (supp θ)` inside the chart source.
  have hS : IsCompact (c.symm '' tsupport θ) := θ.hasCompactSupport.isCompact.image_of_continuousOn
    (c.continuousOn_symm.mono θ.tsupport_subset)
  have hv : ∀ y, y ∉ c.symm '' tsupport θ → K (x, y) * v y = 0 := fun y hy ↦ by
    rw [image_eq_zero_of_notMem_tsupport fun h ↦ hy
      (OpenPartialHomeomorph.tsupport_complexCutoffPullback_subset hc θ g h), mul_zero]
  have hsupp : tsupport (fun y ↦ K (x, y) * v y) ⊆ c.source :=
    (closure_minimal (Function.support_subset_iff'.2 hv) hS.isClosed).trans
      (image_subset_iff.2 fun y hy ↦ c.map_target (θ.tsupport_subset hy))
  rw [hint (fun y ↦ K (x, y) * v y)
      ((hK.comp (continuous_const.prodMk continuous_id)).mul v.contMDiff.continuous)
      (HasCompactSupport.intro hS hv) hsupp,
    setIntegral_congr_fun c.open_target.measurableSet fun w hw ↦ by
      rw [OpenPartialHomeomorph.complexCutoffPullback_apply_of_mem hc _ _ (c.map_target hw),
        c.right_inv hw],
    setIntegral_eq_integral_of_forall_compl_eq_zero fun w hw ↦ by
      rw [image_eq_zero_of_notMem_tsupport fun h ↦ hw (θ.tsupport_subset h)]
      simp]
  refine integral_congr_ae (.of_forall fun w ↦ ?_)
  simp only [Complex.real_smul]
  push_cast
  ring

include hμ

/-- **Operators with smooth kernels have order `-∞`.** Let `μ` be a measure on `M` with a smooth
density `ρ` in every chart `e` of the maximal atlas, in the sense that
`∫ f dμ = ∫_{e.target} ρ(y) f(e⁻¹ y) dy` for continuous compactly supported functions `f`
supported in the chart source. If `K` is a smooth compactly supported function on `M × M` and
`P u (x) = ∫ K(x, y) u(y) dμ(y)` for every smooth `u`, then `P` is an operator of order `-∞`. -/
theorem mem_smoothingPseudodifferentialOperators_of_forall_apply_eq_integral
    (hK : ContMDiff (𝓘(ℝ, CoordinateSpace n).prod 𝓘(ℝ, CoordinateSpace n)) 𝓘(ℝ, ℂ) ∞ K)
    (hKc : HasCompactSupport K) (hP : ∀ u x, P u x = ∫ y, K (x, y) * u y ∂μ) :
    P ∈ smoothingPseudodifferentialOperators := by
  refine (mem_smoothingPseudodifferentialOperators_iff_isSmoothing 0).2
    ⟨isProperlySupported_of_forall_apply_eq_integral hKc hP, fun e he φ ψ ↦ ?_⟩
  obtain ⟨ρ, hρ, hint⟩ := hμ e he
  -- The compression is the integral operator with kernel `φ(x) ψ(y) ρ(y) K(e⁻¹ x, e⁻¹ y)`.
  refine ⟨Symbol.ofKernel (fun p ↦ (((φ p.1 * (ψ p.2 * ρ p.2) : ℝ) : ℂ) *
      K (e.symm p.1, e.symm p.2)) • ContinuousLinearMap.id ℂ ℂ)
    ((contDiff_chartKernel he he φ ψ hρ hK).smul contDiff_const)
    (hasCompactSupport_chartKernel φ ψ ρ).smul_right, Symbol.isSmoothing_ofKernel _ _,
    fun u x ↦ ?_⟩
  rw [Symbol.quantizeSchwartzValue_ofKernel, OpenPartialHomeomorph.complexChartCompression_apply,
    hP, integral_mul_complexCutoffPullback he hint hK.continuous, Complex.real_smul,
    ← integral_const_mul]
  refine integral_congr_ae (.of_forall fun w ↦ ?_)
  simp only [smul_apply, ContinuousLinearMap.id_apply, smul_eq_mul, ContMDiffMap.coe_ofContDiff]
  push_cast
  ring

/-- **Rank-one operators with smooth compactly supported factors have order `-∞`.** For a measure
`μ` with smooth chart densities as in
`TauCeti.mem_smoothingPseudodifferentialOperators_of_forall_apply_eq_integral`, and smooth
compactly supported functions `f` and `g`, an operator `P` with `P u = (∫ g u dμ) f` for every
smooth `u` has order `-∞`. -/
theorem mem_smoothingPseudodifferentialOperators_of_forall_apply_eq_integral_smul
    {f g : C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯} (hf : HasCompactSupport f)
    (hg : HasCompactSupport g) (hP : ∀ u, P u = (∫ y, g y * u y ∂μ) • f) :
    P ∈ smoothingPseudodifferentialOperators := by
  refine mem_smoothingPseudodifferentialOperators_of_forall_apply_eq_integral (K := fun p ↦
    f p.1 * g p.2) hμ ((f.contMDiff.comp contMDiff_fst).mul (g.contMDiff.comp contMDiff_snd))
    ?_ fun u x ↦ ?_
  · refine HasCompactSupport.intro (hf.isCompact.prod hg.isCompact) fun p hp ↦ ?_
    rcases not_and_or.1 hp with hp | hp
    · simp [image_eq_zero_of_notMem_tsupport hp]
    · simp [image_eq_zero_of_notMem_tsupport hp]
  · rw [hP, ContMDiffMap.complex_smul_apply, ← integral_mul_const]
    exact integral_congr_ae (.of_forall fun y ↦ by dsimp only; ring)

/-- **The integral operator of a smooth kernel has order `-∞`.** For a measure `μ` with smooth
chart densities that is finite on compact sets, and a smooth compactly supported kernel `K` on
`M × M`, the operator `u ↦ (x ↦ ∫ K(x, y) u(y) dμ(y))` has order `-∞`. -/
theorem integralOperator_mem_smoothingPseudodifferentialOperators
    [IsManifold 𝓘(ℝ, CoordinateSpace n) ∞ M] [OpensMeasurableSpace M]
    [IsFiniteMeasureOnCompacts μ]
    (hK : ContMDiff (𝓘(ℝ, CoordinateSpace n).prod 𝓘(ℝ, CoordinateSpace n)) 𝓘(ℝ, ℂ) ∞ K)
    (hKc : HasCompactSupport K) :
    integralOperator μ hK hKc ∈ smoothingPseudodifferentialOperators :=
  mem_smoothingPseudodifferentialOperators_of_forall_apply_eq_integral hμ hK hKc
    (integralOperator_apply μ hK hKc)

end Density

end TauCeti
