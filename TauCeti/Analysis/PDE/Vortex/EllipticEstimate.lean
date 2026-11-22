/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Vortex.ExponentialRegularity
import TauCeti.Analysis.Normed.Operator.Banach
import TauCeti.MeasureTheory.Function.L2Space

/-!
# Elliptic estimates on the Sobolev scale for the gauge-fixed vortex operator

At a field `x`, the gauge-fixed vortex operator `L_x = d₀* ⊕ d₁` (`gaugeFixedOperator`) is a
first-order elliptic operator on fields `ℂ → ℝ⁴`, with formal adjoint `L_x*`
(`gaugeFixedAdjoint`). When `x` is smooth with bounded derivatives through order `k`, weak `L²`
solutions of `L_x y = f + A y` gain one derivative: `f ∈ H^k` implies `y ∈ H^(k+1)`, for every
matrix `A` of smooth coefficients with bounded derivatives through order `k`
(`mem_sobolevFields_natCast_add_one_of_integral_inner_gaugeFixedAdjoint_eq_add`). This file turns
that regularity statement into the corresponding estimate

`‖y‖_(H^(k+1)) ≤ K (‖f‖_(H^k) + ‖y‖_(L²))`

(`exists_norm_le_mul_add_of_integral_inner_gaugeFixedAdjoint_eq_add`), with Sobolev norms measured
on the coordinates in Mathlib's Bessel-potential spaces `H^s(ℂ)`. The argument is the closed graph
theorem. The triples `(y, f, v)` of an `L²` solution `y`, its right side `f ∈ L²` and the
coordinates `v ∈ H^k(ℂ)⁴` of `f` form a closed subspace of a Banach space: both the weak equation,
tested against one smooth compactly supported field, and the coordinate condition are kernels of
bounded maps. By regularity, the coordinates of `y` lie in the range of the injective inclusion
`H^(k+1)(ℂ)⁴ → L²(ℂ)⁴`, so they depend boundedly on the triple
(`ContinuousLinearMap.exists_norm_le_of_range_le_range`). The same argument, with the roles of
`L_x` and `L_x*` exchanged, gives the estimate
`‖η‖_(H^(k+1)) ≤ K (‖g‖_(H^k) + ‖η‖_(L²))` for weak solutions of `L_x* η = g + A η`
(`exists_norm_le_mul_add_of_integral_inner_gaugeFixedOperator_eq_add`).

The main application is to the weak right inverse `Q` of `L_x` at a plane vortex `x` with
`|α| → 1`: `Q f` is the weak solution of `L_x y = f` orthogonal to the weak kernel
(`exists_continuousLinearMap_integral_inner_gaugeFixedAdjoint_eq`). With `ρ(z) = √(1 + |z|²)` and
`|c| < 1/2`, the field `Y = exp(c ρ) Q f` is a weak solution of `L_x Y = exp(c ρ) f + A Y`, where
`A = expWeightCoeff c` is the commutator of `L_x` with the weight
(`integral_inner_exp_mul_smul_gaugeFixedAdjoint_eq`), and its `L²` norm is bounded by
`‖exp(c ρ) f‖_(L²)` (`exists_eLpNorm_exp_mul_smul_le_of_integral_inner_gaugeFixedAdjoint_eq`).
The elliptic estimate then gives the weighted Sobolev estimate

`‖exp(c ρ) Q f‖_(H^(k+1)) ≤ K ‖exp(c ρ) f‖_(H^k)`

for every `k` (`exists_norm_exp_mul_smul_le_mul_norm_of_integral_inner_gaugeFixedAdjoint_eq`).
For `c > 0` it bounds the decay, with `k + 1` derivatives, of the correction `Q f` to an error `f`
that decays like `exp(-c ρ)` with `k` derivatives. These are the estimates used to correct
approximate solutions built from plane vortices, whose errors decay exponentially away from the
vortex cores.

The Hilbert space adjoint `Q†` of the right inverse is the left inverse of `L_x*` vanishing on
the weak kernel of `L_x`. On the `L²`-orthogonal complement of that kernel, `Q† g` is a weak
solution of `L_x* η = g` (`integral_inner_adjoint_apply_gaugeFixedOperator_eq`), so
`H = exp(c ρ) Q† g` is a weak solution of `L_x* H = exp(c ρ) g - Aᵀ H`
(`integral_inner_exp_mul_smul_gaugeFixedOperator_eq`), and its weighted `L²` norm is bounded by
`‖exp(c ρ) g‖_(L²)` (`exists_eLpNorm_exp_mul_smul_adjoint_apply_le`). The elliptic estimate for
`L_x*` then gives

`‖exp(c ρ) Q† g‖_(H^(k+1)) ≤ K ‖exp(c ρ) g‖_(H^k)`

for every `k` and every `g` orthogonal to the weak kernel
(`exists_norm_exp_mul_smul_adjoint_apply_le_mul_norm`). On the weak kernel itself `Q†` vanishes.

## Main results

* `exists_norm_le_mul_add_of_integral_inner_gaugeFixedAdjoint_eq_add`: the elliptic estimate for
  `L_x - A` from `H^(k+1)` to `H^k`, up to the `L²` norm.
* `exists_norm_exp_mul_smul_le_mul_norm_of_integral_inner_gaugeFixedAdjoint_eq`: the weighted
  Sobolev estimate for the right inverse at a smooth plane vortex with `|α| → 1`.
* `exists_norm_exp_mul_smul_le_mul_norm_of_forall_mem_framedFieldSpace`: the same at a continuous
  plane vortex lying in `A_m^k` for every `k`.
* `exists_norm_le_mul_add_of_integral_inner_gaugeFixedOperator_eq_add`: the elliptic estimate
  for `L_x* - A` from `H^(k+1)` to `H^k`, up to the `L²` norm.
* `exists_norm_exp_mul_smul_adjoint_apply_le_mul_norm`,
  `exists_norm_exp_mul_smul_adjoint_apply_le_mul_norm_of_forall_mem_framedFieldSpace`: the
  weighted Sobolev estimate for the adjoint of the right inverse on the complement of the weak
  kernel, at a smooth plane vortex with `|α| → 1` and at a continuous vortex of every `A_m^k`.

## References

* A. Jaffe and C. H. Taubes, *Vortices and Monopoles*, Progress in Physics 2, Birkhäuser, 1980,
  Chapter III.
* C. H. Taubes, *Gr ⇒ SW: From pseudo-holomorphic curves to Seiberg–Witten solutions*,
  J. Differential Geom. 51 (1999), 203–334.
-/

public section

noncomputable section

namespace TauCeti.Vortex

open Complex MeasureTheory Filter BesselPotentialSpace
open scoped Topology RealInnerProductSpace ContDiff BesselPotentialSpace

/-! ### The closed space of weak solutions -/

section Estimate

variable {x : ℂ → EuclideanSpace ℝ (Fin 4)} {A : Fin 4 → Fin 4 → ℂ → ℝ}

/-- The transpose `Aᵀ η` of a matrix of functions acting on a field. -/
private def transposeMulVec (A : Fin 4 → Fin 4 → ℂ → ℝ) (η : ℂ → EuclideanSpace ℝ (Fin 4))
    (z : ℂ) : EuclideanSpace ℝ (Fin 4) :=
  (Matrix.of fun i j ↦ A i j z).transpose.toEuclideanLin (η z)

/-- Pointwise, `⟪A y, η⟫ = ⟪y, Aᵀ η⟫`. -/
private theorem inner_mulVec_eq_inner_transposeMulVec (A : Fin 4 → Fin 4 → ℂ → ℝ)
    (y η : ℂ → EuclideanSpace ℝ (Fin 4)) (z : ℂ) :
    ⟪WithLp.toLp 2 (fun i ↦ ∑ j : Fin 4, A i j z * y z j), η z⟫ =
      ⟪y z, transposeMulVec A η z⟫ := by
  rw [transposeMulVec, ← Matrix.conjTranspose_eq_transpose_of_trivial,
    Matrix.toEuclideanLin_conjTranspose_eq_adjoint, LinearMap.adjoint_inner_right,
    Matrix.toLpLin_apply, funext (Matrix.mulVec_apply_eq_sum _ _)]
  simp only [Matrix.of_apply]

/-- `Aᵀ η` is smooth with compact support when `A` is smooth and `η` is a test field. -/
private theorem memLp_transposeMulVec (hA : ∀ i j, ContDiff ℝ ∞ (A i j))
    {η : ℂ → EuclideanSpace ℝ (Fin 4)} (hη : ContDiff ℝ ∞ η) (hηc : HasCompactSupport η) :
    MemLp (transposeMulVec A η) 2 volume := by
  have hc : ContDiff ℝ ∞ (transposeMulVec A η) := contDiff_euclidean.2 fun j ↦ by
    simpa [transposeMulVec, Matrix.toLpLin_apply, Matrix.mulVec, dotProduct] using
      ContDiff.sum (s := Finset.univ) fun i _ ↦ (hA i j).mul (contDiff_euclidean.1 hη i)
  refine hc.continuous.memLp_of_hasCompactSupport
    (hηc.mono (Function.support_subset_iff'.2 fun z hz ↦ ?_))
  simp [transposeMulVec, Function.notMem_support.1 hz]

variable (k : ℕ)

/-- The complexified coordinate `a` of a real `L²` field. -/
private def coordL (a : Fin 4) :
    Lp (EuclideanSpace ℝ (Fin 4)) 2 (volume : Measure ℂ) →L[ℝ] Lp ℂ 2 (volume : Measure ℂ) :=
  (Complex.ofRealCLM.comp (EuclideanSpace.proj a)).compLpL 2 volume

/-- Almost everywhere, `coordL a Y` is the complexified coordinate `a` of `Y`. -/
private theorem coeFn_coordL (a : Fin 4)
    (Y : Lp (EuclideanSpace ℝ (Fin 4)) 2 (volume : Measure ℂ)) :
    coordL a Y =ᵐ[volume] fun z ↦ (Y z a : ℂ) :=
  (ContinuousLinearMap.coeFn_compLpL (Complex.ofRealCLM.comp (EuclideanSpace.proj a)) Y).mono
    fun z hz ↦ by rw [coordL, hz]; simp

/-- The triples `(Y, F, v)` of two real `L²` fields and four `H^k` functions, among which the weak
solutions `Y` of `L_x Y = F + A Y` with coordinates `v` of `F` form a closed subspace. -/
private abbrev Triple : Type :=
  Lp (EuclideanSpace ℝ (Fin 4)) 2 (volume : Measure ℂ) ×
    Lp (EuclideanSpace ℝ (Fin 4)) 2 (volume : Measure ℂ) × (Fin 4 → H^{(k : ℝ)}(ℂ))

/-- The defect of `v a` from being the complexified coordinate `a` of `F`. -/
private def reprCLM (a : Fin 4) : Triple k →L[ℝ] Lp ℂ 2 (volume : Measure ℂ) :=
  ((inclusionLp (Nat.cast_nonneg k)).restrictScalars ℝ).comp
      ((ContinuousLinearMap.proj a).comp
        ((ContinuousLinearMap.snd ℝ _ _).comp (ContinuousLinearMap.snd ℝ _ _))) -
    (coordL a).comp ((ContinuousLinearMap.fst ℝ _ _).comp (ContinuousLinearMap.snd ℝ _ _))

variable {k} in
/-- The defect `⟪Y, P η - Aᵀ η⟫ - ⟪F, η⟫` of the weak equation `L Y = F + A Y`, tested against
`η`, where `P` is the formal adjoint of `L` on test fields. -/
private def testCLM {P : (ℂ → EuclideanSpace ℝ (Fin 4)) → ℂ → EuclideanSpace ℝ (Fin 4)}
    {η : ℂ → EuclideanSpace ℝ (Fin 4)}
    (h₁ : MemLp (P η) 2 volume) (h₂ : MemLp (transposeMulVec A η) 2 volume)
    (h₃ : MemLp η 2 volume) : Triple k →L[ℝ] ℝ :=
  (innerSL ℝ (h₁.toLp _ - h₂.toLp _)).comp (ContinuousLinearMap.fst ℝ _ _) -
    (innerSL ℝ (h₃.toLp _)).comp
      ((ContinuousLinearMap.fst ℝ _ _).comp (ContinuousLinearMap.snd ℝ _ _))

variable {P : (ℂ → EuclideanSpace ℝ (Fin 4)) → ℂ → EuclideanSpace ℝ (Fin 4)}

variable {k} in
/-- The weak solutions among the triples: `v` is the family of complexified coordinates of `F`,
and `L Y = F + A Y` weakly, where `P` is the formal adjoint of `L` on test fields. -/
private def weakSolutions
    (hP : ∀ η, ContDiff ℝ ∞ η → HasCompactSupport η → MemLp (P η) 2 volume)
    (hA : ∀ i j, ContDiff ℝ ∞ (A i j)) :
    Submodule ℝ (Triple k) :=
  (⨅ a, (reprCLM k a).ker) ⊓
    ⨅ (η : ℂ → EuclideanSpace ℝ (Fin 4)) (hη : ContDiff ℝ ∞ η) (hηc : HasCompactSupport η),
      (testCLM (k := k) (hP η hη hηc) (memLp_transposeMulVec hA hη hηc)
        (hη.continuous.memLp_of_hasCompactSupport hηc)).ker

private theorem isClosed_weakSolutions
    (hP : ∀ η, ContDiff ℝ ∞ η → HasCompactSupport η → MemLp (P η) 2 volume)
    (hA : ∀ i j, ContDiff ℝ ∞ (A i j)) :
    IsClosed (weakSolutions (k := k) hP hA : Set (Triple k)) := by
  simp only [weakSolutions, Submodule.coe_inf, Submodule.coe_iInf]
  exact (isClosed_iInter fun a ↦ (reprCLM k a).isClosed_ker).inter
    (isClosed_iInter fun _ ↦ isClosed_iInter fun _ ↦ isClosed_iInter fun _ ↦
      ContinuousLinearMap.isClosed_ker _)

variable {k} in
/-- The tested defect of the weak equation, as integrals of the pointwise representatives. -/
private theorem testCLM_apply
    (hP : ∀ η, ContDiff ℝ ∞ η → HasCompactSupport η → MemLp (P η) 2 volume)
    (hA : ∀ i j, ContDiff ℝ ∞ (A i j))
    {η : ℂ → EuclideanSpace ℝ (Fin 4)} (hη : ContDiff ℝ ∞ η) (hηc : HasCompactSupport η)
    (p : Triple k) :
    testCLM (k := k) (hP η hη hηc) (memLp_transposeMulVec hA hη hηc)
        (hη.continuous.memLp_of_hasCompactSupport hηc) p =
      (∫ z, ⟪p.1 z, P η z⟫) -
        ∫ z, ⟪p.2.1 z + WithLp.toLp 2 (fun i ↦ ∑ j : Fin 4, A i j z * p.1 z j), η z⟫ := by
  have h₁ := hP η hη hηc
  have h₂ := memLp_transposeMulVec hA hη hηc
  have h₃ := hη.continuous.memLp_of_hasCompactSupport (μ := volume) (p := 2) hηc
  have hY := Lp.memLp p.1
  have hF := Lp.memLp p.2.1
  have e₁ : ∫ z, ⟪(h₁.toLp _ - h₂.toLp _ : Lp (EuclideanSpace ℝ (Fin 4)) 2 volume) z, p.1 z⟫ =
      (∫ z, ⟪p.1 z, P η z⟫) - ∫ z, ⟪p.1 z, transposeMulVec A η z⟫ := by
    rw [← integral_sub (hY.integrable_inner (𝕜 := ℝ) h₁) (hY.integrable_inner (𝕜 := ℝ) h₂)]
    refine integral_congr_ae ?_
    filter_upwards [Lp.coeFn_sub (h₁.toLp _) (h₂.toLp _), h₁.coeFn_toLp, h₂.coeFn_toLp]
      with z hz hz₁ hz₂
    rw [hz, Pi.sub_apply, hz₁, hz₂, inner_sub_left, real_inner_comm, real_inner_comm (p.1 z)]
  have e₂ : ∫ z, ⟪h₃.toLp η z, p.2.1 z⟫ = ∫ z, ⟪p.2.1 z, η z⟫ :=
    integral_congr_ae (h₃.coeFn_toLp.mono fun z hz ↦ by simp only [hz, real_inner_comm])
  have e₃ : ∫ z, ⟪p.2.1 z + WithLp.toLp 2 (fun i ↦ ∑ j : Fin 4, A i j z * p.1 z j), η z⟫ =
      (∫ z, ⟪p.2.1 z, η z⟫) + ∫ z, ⟪p.1 z, transposeMulVec A η z⟫ := by
    rw [← integral_add (hF.integrable_inner (𝕜 := ℝ) h₃) (hY.integrable_inner (𝕜 := ℝ) h₂)]
    exact integral_congr_ae (.of_forall fun z ↦ by
      simp only [inner_add_left, inner_mulVec_eq_inner_transposeMulVec])
  simp only [testCLM, sub_apply, ContinuousLinearMap.comp_apply, innerSL_apply_apply,
    ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd', L2.inner_def]
  rw [e₁, e₂, e₃]
  ring

variable {k} in
/-- Membership in the space of weak solutions, unfolded. -/
private theorem mem_weakSolutions_iff
    (hP : ∀ η, ContDiff ℝ ∞ η → HasCompactSupport η → MemLp (P η) 2 volume)
    (hA : ∀ i j, ContDiff ℝ ∞ (A i j)) {p : Triple k} :
    p ∈ weakSolutions hP hA ↔ (∀ a, inclusionLp (Nat.cast_nonneg k) (p.2.2 a) = coordL a p.2.1) ∧
      ∀ η : ℂ → EuclideanSpace ℝ (Fin 4), ContDiff ℝ ∞ η → HasCompactSupport η →
        ∫ z, ⟪p.1 z, P η z⟫ =
          ∫ z, ⟪p.2.1 z + WithLp.toLp 2 (fun i ↦ ∑ j : Fin 4, A i j z * p.1 z j), η z⟫ := by
  simp only [weakSolutions, Submodule.mem_inf, Submodule.mem_iInf, LinearMap.mem_ker,
    ContinuousLinearMap.coe_coe, sub_eq_zero, reprCLM, sub_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_restrictScalars',
    ContinuousLinearMap.proj_apply, ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd']
  refine and_congr Iff.rfl (forall_congr' fun η ↦ forall_congr' fun hη ↦ forall_congr' fun hηc ↦ ?_)
  rw [testCLM_apply hP hA hη hηc, sub_eq_zero]

/-- **Regularity on the space of weak solutions.** If weak solutions `Y` of `L Y = F + A Y` with
`F ∈ H^k` lie in `H^(k+1)`, then the first component `Y` of a weak solution has coordinates in
`H^(k+1)`. -/
private theorem exists_inclusionLp_eq_of_mem_weakSolutions
    (hP : ∀ η, ContDiff ℝ ∞ η → HasCompactSupport η → MemLp (P η) 2 volume)
    (hA : ∀ i j, ContDiff ℝ ∞ (A i j))
    (hreg : ∀ y f : ℂ → EuclideanSpace ℝ (Fin 4), MemLp y 2 volume → f ∈ sobolevFields k →
      (∀ η : ℂ → EuclideanSpace ℝ (Fin 4), ContDiff ℝ ∞ η → HasCompactSupport η →
        ∫ z, ⟪y z, P η z⟫ =
          ∫ z, ⟪f z + WithLp.toLp 2 (fun i ↦ ∑ j : Fin 4, A i j z * y z j), η z⟫) →
      y ∈ sobolevFields (k + 1))
    {p : Triple k} (hp : p ∈ weakSolutions hP hA) :
    ∃ u : Fin 4 → H^{(k : ℝ) + 1}(ℂ), ∀ a, inclusionLp (by positivity) (u a) = coordL a p.1 := by
  obtain ⟨hrepr, hweak⟩ := (mem_weakSolutions_iff hP hA).1 hp
  have hF : (p.2.1 : ℂ → EuclideanSpace ℝ (Fin 4)) ∈ sobolevFields k :=
    (mem_sobolevFields_iff_exists_inclusionLp_ae_eq (Nat.cast_nonneg k)).2
      ⟨p.2.2, fun a ↦ by rw [hrepr a]; exact coeFn_coordL a _⟩
  have hY := hreg _ _ (Lp.memLp p.1) hF hweak
  obtain ⟨u, hu⟩ := (mem_sobolevFields_iff_exists_inclusionLp_ae_eq (by positivity)).1 hY
  exact ⟨u, fun a ↦ Lp.ext ((hu a).trans (coeFn_coordL a _).symm)⟩

/-- **The closed graph step.** On the space of weak solutions, the `H^(k+1)` coordinates of the
first component are bounded by the norm of the triple. -/
private theorem exists_norm_le_of_mem_weakSolutions
    (hP : ∀ η, ContDiff ℝ ∞ η → HasCompactSupport η → MemLp (P η) 2 volume)
    (hA : ∀ i j, ContDiff ℝ ∞ (A i j))
    (hreg : ∀ y f : ℂ → EuclideanSpace ℝ (Fin 4), MemLp y 2 volume → f ∈ sobolevFields k →
      (∀ η : ℂ → EuclideanSpace ℝ (Fin 4), ContDiff ℝ ∞ η → HasCompactSupport η →
        ∫ z, ⟪y z, P η z⟫ =
          ∫ z, ⟪f z + WithLp.toLp 2 (fun i ↦ ∑ j : Fin 4, A i j z * y z j), η z⟫) →
      y ∈ sobolevFields (k + 1)) :
    ∃ C ≥ 0, ∀ p ∈ weakSolutions (k := k) hP hA, ∀ u : Fin 4 → H^{(k : ℝ) + 1}(ℂ),
      (∀ a, inclusionLp (by positivity) (u a) = coordL a p.1) → ‖u‖ ≤ C * ‖p‖ := by
  set D := weakSolutions (k := k) hP hA
  have : CompleteSpace D := (isClosed_weakSolutions k hP hA).completeSpace_coe
  let f' : D →L[ℝ] Fin 4 → Lp ℂ 2 (volume : Measure ℂ) :=
    (ContinuousLinearMap.pi fun a ↦ (coordL a).comp (ContinuousLinearMap.fst ℝ _ _)).comp
      D.subtypeL
  let g : (Fin 4 → H^{(k : ℝ) + 1}(ℂ)) →L[ℝ] Fin 4 → Lp ℂ 2 (volume : Measure ℂ) :=
    ContinuousLinearMap.pi fun a ↦
      ((inclusionLp (by positivity)).restrictScalars ℝ).comp (ContinuousLinearMap.proj a)
  have hg : Function.Injective g := fun u u' h ↦
    funext fun a ↦ inclusionLp_injective _ (congr_fun h a)
  have hfg : f'.range ≤ g.range := by
    rintro _ ⟨p, rfl⟩
    obtain ⟨u, hu⟩ := exists_inclusionLp_eq_of_mem_weakSolutions k hP hA hreg p.property
    exact ⟨u, funext hu⟩
  obtain ⟨C, hC, hCb⟩ := ContinuousLinearMap.exists_norm_le_of_range_le_range f' g hg hfg
  exact ⟨C, hC, fun p hp u hu ↦ hCb ⟨p, hp⟩ u (funext hu)⟩

variable {k} in
/-- A weak solution `y` of `L y = f + A y` with coordinates `v` of `f` gives a triple in the
space of weak solutions. -/
private theorem mem_weakSolutions_of_forall_inclusionLp_ae_eq
    (hP : ∀ η, ContDiff ℝ ∞ η → HasCompactSupport η → MemLp (P η) 2 volume)
    (hA : ∀ i j, ContDiff ℝ ∞ (A i j)) {y f : ℂ → EuclideanSpace ℝ (Fin 4)}
    (hy : MemLp y 2 volume) (hf : MemLp f 2 volume) {v : Fin 4 → H^{(k : ℝ)}(ℂ)}
    (hv : ∀ a, ⇑(inclusionLp (Nat.cast_nonneg k) (v a)) =ᵐ[volume] fun z ↦ (f z a : ℂ))
    (hweak : ∀ η : ℂ → EuclideanSpace ℝ (Fin 4), ContDiff ℝ ∞ η → HasCompactSupport η →
      ∫ z, ⟪y z, P η z⟫ =
        ∫ z, ⟪f z + WithLp.toLp 2 (fun i ↦ ∑ j : Fin 4, A i j z * y z j), η z⟫) :
    (hy.toLp y, hf.toLp f, v) ∈ weakSolutions hP hA := by
  refine (mem_weakSolutions_iff hP hA).2 ⟨fun a ↦ Lp.ext ?_, fun η hη hηc ↦ ?_⟩
  · filter_upwards [hv a, coeFn_coordL a (hf.toLp f), hf.coeFn_toLp] with z h₁ h₂ h₃
    simp only [h₁, h₂, h₃]
  · calc ∫ z, ⟪hy.toLp y z, P η z⟫
        = ∫ z, ⟪y z, P η z⟫ :=
          integral_congr_ae (hy.coeFn_toLp.mono fun z hz ↦ by simp only [hz])
      _ = ∫ z, ⟪f z + WithLp.toLp 2 (fun i ↦ ∑ j : Fin 4, A i j z * y z j), η z⟫ :=
          hweak η hη hηc
      _ = ∫ z, ⟪hf.toLp f z + WithLp.toLp 2
            (fun i ↦ ∑ j : Fin 4, A i j z * hy.toLp y z j), η z⟫ := by
          refine integral_congr_ae ?_
          filter_upwards [hy.coeFn_toLp, hf.coeFn_toLp] with z h₁ h₂
          simp only [h₁, h₂]

/-! ### The elliptic estimate -/

/-- **The elliptic estimate from regularity**, for a first-order operator `L` with formal adjoint
`P` on test fields and a zeroth-order term `A`: if weak solutions `y` of `L y = f + A y` with
`f ∈ H^k` lie in `H^(k+1)`, then `‖y‖_(H^(k+1)) ≤ K (‖f‖_(H^k) + ‖y‖_(L²))`. -/
private theorem exists_norm_le_mul_add_of_integral_inner_eq_add
    (hP : ∀ η, ContDiff ℝ ∞ η → HasCompactSupport η → MemLp (P η) 2 volume)
    (hA : ∀ i j, ContDiff ℝ ∞ (A i j))
    (hreg : ∀ y f : ℂ → EuclideanSpace ℝ (Fin 4), MemLp y 2 volume → f ∈ sobolevFields k →
      (∀ η : ℂ → EuclideanSpace ℝ (Fin 4), ContDiff ℝ ∞ η → HasCompactSupport η →
        ∫ z, ⟪y z, P η z⟫ =
          ∫ z, ⟪f z + WithLp.toLp 2 (fun i ↦ ∑ j : Fin 4, A i j z * y z j), η z⟫) →
      y ∈ sobolevFields (k + 1)) :
    ∃ K ≥ 0, ∀ (y f : ℂ → EuclideanSpace ℝ (Fin 4)) (u : Fin 4 → H^{(k : ℝ) + 1}(ℂ))
      (v : Fin 4 → H^{(k : ℝ)}(ℂ)),
      (∀ a, ⇑(inclusionLp (by positivity) (u a)) =ᵐ[volume] fun z ↦ (y z a : ℂ)) →
      (∀ a, ⇑(inclusionLp (Nat.cast_nonneg k) (v a)) =ᵐ[volume] fun z ↦ (f z a : ℂ)) →
      (∀ η : ℂ → EuclideanSpace ℝ (Fin 4), ContDiff ℝ ∞ η → HasCompactSupport η →
        ∫ z, ⟪y z, P η z⟫ =
          ∫ z, ⟪f z + WithLp.toLp 2 (fun i ↦ ∑ j : Fin 4, A i j z * y z j), η z⟫) →
      ‖u‖ ≤ K * (‖v‖ + (eLpNorm y 2 volume).toReal) := by
  obtain ⟨C, hC, hCb⟩ := exists_norm_le_of_mem_weakSolutions k hP hA hreg
  refine ⟨5 * C, by positivity, fun y f u v hu hv hweak ↦ ?_⟩
  have hy : MemLp y 2 volume := memLp_of_mem_sobolevFields
    ((mem_sobolevFields_iff_exists_inclusionLp_ae_eq (by positivity)).2 ⟨u, hu⟩)
  have hf : MemLp f 2 volume := memLp_of_mem_sobolevFields
    ((mem_sobolevFields_iff_exists_inclusionLp_ae_eq (Nat.cast_nonneg k)).2 ⟨v, hv⟩)
  have hp := mem_weakSolutions_of_forall_inclusionLp_ae_eq hP hA hy hf hv hweak
  have hgu (a : Fin 4) : inclusionLp (by positivity) (u a) = coordL a (hy.toLp y) :=
    Lp.ext <| (hu a).trans <| by
      filter_upwards [coeFn_coordL a (hy.toLp y), hy.coeFn_toLp] with z h₁ h₂
      simp only [h₁, h₂]
  -- The norm of the triple is at most `‖y‖_(L²) + ‖f‖_(L²) + ‖v‖ ≤ ‖y‖_(L²) + 5 ‖v‖`.
  have hF : ‖hf.toLp f‖ ≤ 4 * ‖v‖ := by
    rw [Lp.norm_toLp]
    exact ENNReal.toReal_le_of_le_ofReal (by positivity)
      (eLpNorm_le_of_forall_inclusionLp_ae_eq (Nat.cast_nonneg k) hv)
  have hnorm : ‖(hy.toLp y, hf.toLp f, v)‖ ≤ (eLpNorm y 2 volume).toReal + 4 * ‖v‖ + ‖v‖ := by
    rw [Prod.norm_def, Prod.norm_def, Lp.norm_toLp]
    refine max_le ?_ (max_le ?_ ?_) <;> linarith [norm_nonneg (hf.toLp f), norm_nonneg v,
      ENNReal.toReal_nonneg (a := eLpNorm y 2 volume)]
  calc ‖u‖ ≤ C * ‖(hy.toLp y, hf.toLp f, v)‖ := hCb _ hp u hgu
    _ ≤ C * ((eLpNorm y 2 volume).toReal + 4 * ‖v‖ + ‖v‖) := by gcongr
    _ ≤ 5 * C * (‖v‖ + (eLpNorm y 2 volume).toReal) := by
        nlinarith [ENNReal.toReal_nonneg (a := eLpNorm y 2 volume), norm_nonneg v]

/-- **The elliptic estimate for the gauge-fixed operator with a zeroth-order term.** Let `x` be a
smooth field whose coordinates have bounded derivatives through order `k`, and let `A` be a `4 × 4`
matrix of smooth real functions with bounded derivatives through order `k`. There is a constant
`K` such that every square-integrable weak solution `y` of `L_x y = f + A y`, tested against
smooth compactly supported fields, satisfies

`‖y‖_(H^(k+1)) ≤ K (‖f‖_(H^k) + ‖y‖_(L²))`.

The Sobolev norms are those of the coordinates `u : Fin 4 → H^(k+1)(ℂ)` of `y` and
`v : Fin 4 → H^k(ℂ)` of `f`. By the elliptic bootstrap
(`mem_sobolevFields_natCast_add_one_of_integral_inner_gaugeFixedAdjoint_eq_add`) such
coordinates `u` exist as soon as those of `f` do. -/
theorem exists_norm_le_mul_add_of_integral_inner_gaugeFixedAdjoint_eq_add
    (hx : ContDiff ℝ ∞ x)
    (hbound : ∀ i, ∀ n ≤ k, ∃ C, ∀ z, ‖iteratedFDeriv ℝ n (fun z ↦ x z i) z‖ ≤ C)
    (hA : ∀ i j, ContDiff ℝ ∞ (A i j))
    (hAbound : ∀ i j, ∃ M ≥ 0, ∀ n ≤ k, ∀ z, ‖iteratedFDeriv ℝ n (A i j) z‖ ≤ M) :
    ∃ K ≥ 0, ∀ (y f : ℂ → EuclideanSpace ℝ (Fin 4)) (u : Fin 4 → H^{(k : ℝ) + 1}(ℂ))
      (v : Fin 4 → H^{(k : ℝ)}(ℂ)),
      (∀ a, ⇑(inclusionLp (by positivity) (u a)) =ᵐ[volume] fun z ↦ (y z a : ℂ)) →
      (∀ a, ⇑(inclusionLp (Nat.cast_nonneg k) (v a)) =ᵐ[volume] fun z ↦ (f z a : ℂ)) →
      (∀ η : ℂ → EuclideanSpace ℝ (Fin 4), ContDiff ℝ ∞ η → HasCompactSupport η →
        ∫ z, ⟪y z, gaugeFixedAdjoint x η z⟫ =
          ∫ z, ⟪f z + WithLp.toLp 2 (fun i ↦ ∑ j : Fin 4, A i j z * y z j), η z⟫) →
      ‖u‖ ≤ K * (‖v‖ + (eLpNorm y 2 volume).toReal) :=
  exists_norm_le_mul_add_of_integral_inner_eq_add k
    (fun _ hη hηc ↦ memLp_gaugeFixedAdjoint hx.continuous (hη.of_le (by simp)) hηc) hA
    fun _ _ hy hf hweak ↦
      mem_sobolevFields_natCast_add_one_of_integral_inner_gaugeFixedAdjoint_eq_add k hx hbound
        hA hAbound hy hf hweak

/-- **The elliptic estimate for the adjoint with a zeroth-order term.** Let `x` be a smooth field
whose coordinates have bounded derivatives through order `k`, and let `A` be a `4 × 4` matrix of
smooth real functions with bounded derivatives through order `k`. There is a constant `K` such
that every square-integrable weak solution `η` of `L_x* η = g + A η`, in the sense that
`∫ ⟪η, L_x v⟫ = ∫ ⟪g + A η, v⟫` for every smooth compactly supported field `v`, satisfies

`‖η‖_(H^(k+1)) ≤ K (‖g‖_(H^k) + ‖η‖_(L²))`.

The Sobolev norms are those of the coordinates `u : Fin 4 → H^(k+1)(ℂ)` of `η` and
`v : Fin 4 → H^k(ℂ)` of `g`, which exist together by the elliptic bootstrap
(`mem_sobolevFields_natCast_add_one_of_integral_inner_gaugeFixedOperator_eq_add`). -/
theorem exists_norm_le_mul_add_of_integral_inner_gaugeFixedOperator_eq_add
    (hx : ContDiff ℝ ∞ x)
    (hbound : ∀ i, ∀ n ≤ k, ∃ C, ∀ z, ‖iteratedFDeriv ℝ n (fun z ↦ x z i) z‖ ≤ C)
    (hA : ∀ i j, ContDiff ℝ ∞ (A i j))
    (hAbound : ∀ i j, ∃ M ≥ 0, ∀ n ≤ k, ∀ z, ‖iteratedFDeriv ℝ n (A i j) z‖ ≤ M) :
    ∃ K ≥ 0, ∀ (η g : ℂ → EuclideanSpace ℝ (Fin 4)) (u : Fin 4 → H^{(k : ℝ) + 1}(ℂ))
      (v : Fin 4 → H^{(k : ℝ)}(ℂ)),
      (∀ a, ⇑(inclusionLp (by positivity) (u a)) =ᵐ[volume] fun z ↦ (η z a : ℂ)) →
      (∀ a, ⇑(inclusionLp (Nat.cast_nonneg k) (v a)) =ᵐ[volume] fun z ↦ (g z a : ℂ)) →
      (∀ w : ℂ → EuclideanSpace ℝ (Fin 4), ContDiff ℝ ∞ w → HasCompactSupport w →
        ∫ z, ⟪η z, gaugeFixedOperator x w z⟫ =
          ∫ z, ⟪g z + WithLp.toLp 2 (fun i ↦ ∑ j : Fin 4, A i j z * η z j), w z⟫) →
      ‖u‖ ≤ K * (‖v‖ + (eLpNorm η 2 volume).toReal) :=
  exists_norm_le_mul_add_of_integral_inner_eq_add k
    (fun _ hw hwc ↦ (continuous_gaugeFixedOperator hx.continuous
      (hw.of_le (by simp))).memLp_of_hasCompactSupport (hasCompactSupport_gaugeFixedOperator hwc))
    hA fun _ _ hη hg hweak ↦
      mem_sobolevFields_natCast_add_one_of_integral_inner_gaugeFixedOperator_eq_add k hx hbound
        hA hAbound hη hg hweak

end Estimate

/-! ### The weighted estimate for the right inverse -/

variable {x : ℂ → EuclideanSpace ℝ (Fin 4)}

/-- **The weighted Sobolev estimate for the right inverse at a plane vortex.** Let `x` be a smooth
solution of the plane vortex equations with `|α| → 1` at infinity whose coordinates have bounded
derivatives through order `k`, let `ρ(z) = √(1 + |z|²)` and `|c| < 1/2`. There is a constant `K`
with the following property. Let `y` be the square-integrable weak solution of `L_x y = f`
orthogonal to the weak kernel of `L_x`, that is the value at `f` of the weak right inverse `Q` of
`exists_continuousLinearMap_integral_inner_gaugeFixedAdjoint_eq`. If the coordinates of
`exp(c ρ) f` are given by `v : Fin 4 → H^k(ℂ)`, then those of `exp(c ρ) y` are given by some
`u : Fin 4 → H^(k+1)(ℂ)` with `‖u‖ ≤ K ‖v‖`. That is,

`‖exp(c ρ) Q f‖_(H^(k+1)) ≤ K ‖exp(c ρ) f‖_(H^k)`. -/
theorem exists_norm_exp_mul_smul_le_mul_norm_of_integral_inner_gaugeFixedAdjoint_eq (k : ℕ)
    (hx : ContDiff ℝ ∞ x) (hsol : ∀ z, equation x z = 0)
    (hlim : Tendsto (fun z ↦ 4 * (x z 2 ^ 2 + x z 3 ^ 2)) (cocompact ℂ) (𝓝 1))
    (hbound : ∀ i, ∀ n ≤ k, ∃ C, ∀ z, ‖iteratedFDeriv ℝ n (fun z ↦ x z i) z‖ ≤ C)
    {c : ℝ} (hc : |c| < 1 / 2) :
    ∃ K ≥ 0, ∀ f y : Lp (EuclideanSpace ℝ (Fin 4)) 2 volume,
      (∀ η, ContDiff ℝ 2 η → HasCompactSupport η →
        ∫ z, ⟪y z, gaugeFixedAdjoint x η z⟫ = ∫ z, ⟪f z, η z⟫) →
      (∀ w : Lp (EuclideanSpace ℝ (Fin 4)) 2 volume,
        (∀ η, ContDiff ℝ 2 η → HasCompactSupport η →
          ∫ z, ⟪w z, gaugeFixedAdjoint x η z⟫ = 0) →
        ∫ z, ⟪y z, w z⟫ = 0) →
      ∀ v : Fin 4 → H^{(k : ℝ)}(ℂ),
      (∀ a, ⇑(inclusionLp (Nat.cast_nonneg k) (v a)) =ᵐ[volume]
        fun z ↦ ((Real.exp (c * √(1 + ‖z‖ ^ 2)) • f z) a : ℂ)) →
      ∃ u : Fin 4 → H^{(k : ℝ) + 1}(ℂ),
        (∀ a, ⇑(inclusionLp (by positivity) (u a)) =ᵐ[volume]
          fun z ↦ ((Real.exp (c * √(1 + ‖z‖ ^ 2)) • y z) a : ℂ)) ∧ ‖u‖ ≤ K * ‖v‖ := by
  -- `exp(c ρ) y` solves `L_x Y = exp(c ρ) f + A Y` for the weight commutator `A`, so the elliptic
  -- estimate bounds it by `‖exp(c ρ) f‖_(H^k)` and its weighted `L²` norm, which the weighted
  -- `L²` estimate bounds by `‖exp(c ρ) f‖_(L²)`.
  obtain ⟨K₀, hK₀⟩ := exists_eLpNorm_exp_mul_smul_le_of_integral_inner_gaugeFixedAdjoint_eq
    (μ := volume) (hx.of_le (by exact_mod_cast le_top)) hsol hlim hc
  obtain ⟨K₁, hK₁, hK₁b⟩ := exists_norm_le_mul_add_of_integral_inner_gaugeFixedAdjoint_eq_add k
    hx hbound (contDiff_expWeightCoeff c)
    (fun i j ↦ exists_norm_iteratedFDeriv_expWeightCoeff_le c i j k)
  refine ⟨K₁ * (1 + 4 * K₀), by positivity, fun f y hweak horth v hv ↦ ?_⟩
  have hwf : (fun z ↦ Real.exp (c * √(1 + ‖z‖ ^ 2)) • f z) ∈ sobolevFields k :=
    (mem_sobolevFields_iff_exists_inclusionLp_ae_eq (Nat.cast_nonneg k)).2 ⟨v, hv⟩
  obtain ⟨u, hu⟩ := (mem_sobolevFields_iff_exists_inclusionLp_ae_eq (by positivity)).1
    (exp_mul_smul_mem_sobolevFields_natCast_add_one_of_integral_inner_gaugeFixedAdjoint_eq k hx
      hsol hlim hbound hc hweak horth hwf)
  refine ⟨u, hu, ?_⟩
  have hL2 : (eLpNorm (fun z ↦ Real.exp (c * √(1 + ‖z‖ ^ 2)) • y z) 2 volume).toReal ≤
      4 * K₀ * ‖v‖ := by
    refine ENNReal.toReal_le_of_le_ofReal (by positivity) ((hK₀ f y hweak horth).trans ?_)
    rw [show (4 : ℝ) * K₀ * ‖v‖ = K₀ * (4 * ‖v‖) by ring, ENNReal.ofReal_mul K₀.coe_nonneg,
      ENNReal.ofReal_coe_nnreal]
    gcongr
    exact eLpNorm_le_of_forall_inclusionLp_ae_eq (Nat.cast_nonneg k) hv
  calc ‖u‖ ≤ K₁ * (‖v‖ + (eLpNorm (fun z ↦ Real.exp (c * √(1 + ‖z‖ ^ 2)) • y z) 2 volume).toReal) :=
        hK₁b _ _ u v hu hv fun _ hη hηc ↦ integral_inner_exp_mul_smul_gaugeFixedAdjoint_eq
          hx.continuous (Lp.memLp y) (Lp.memLp f)
          (fun η hη hηc ↦ hweak η (hη.of_le (by norm_cast)) hηc) hη hηc
    _ ≤ K₁ * (‖v‖ + 4 * K₀ * ‖v‖) := by gcongr
    _ = K₁ * (1 + 4 * K₀) * ‖v‖ := by ring

/-- **The weighted Sobolev estimate for the right inverse at a vortex of every `A_m^k`.** Let `x`
be a continuous solution of the plane vortex equations lying in the affine field space `A_m^k` for
every `k`, and let `ρ(z) = √(1 + |z|²)` and `|c| < 1/2`. For every `k` there is a constant `K`
such that, if `y` is the square-integrable weak solution of `L_x y = f` orthogonal to the weak
kernel, then `‖exp(c ρ) y‖_(H^(k+1)) ≤ K ‖exp(c ρ) f‖_(H^k)`, in the sense of
`exists_norm_exp_mul_smul_le_mul_norm_of_integral_inner_gaugeFixedAdjoint_eq`. -/
theorem exists_norm_exp_mul_smul_le_mul_norm_of_forall_mem_framedFieldSpace
    {b : ContDiffBump (0 : ℝ)} {m : ℕ} (hx : Continuous x)
    (hmem : ∀ k : ℕ, x ∈ framedFieldSpace b m k) (hsol : ∀ z, equation x z = 0) {c : ℝ}
    (hc : |c| < 1 / 2) (k : ℕ) :
    ∃ K ≥ 0, ∀ f y : Lp (EuclideanSpace ℝ (Fin 4)) 2 volume,
      (∀ η, ContDiff ℝ 2 η → HasCompactSupport η →
        ∫ z, ⟪y z, gaugeFixedAdjoint x η z⟫ = ∫ z, ⟪f z, η z⟫) →
      (∀ w : Lp (EuclideanSpace ℝ (Fin 4)) 2 volume,
        (∀ η, ContDiff ℝ 2 η → HasCompactSupport η →
          ∫ z, ⟪w z, gaugeFixedAdjoint x η z⟫ = 0) →
        ∫ z, ⟪y z, w z⟫ = 0) →
      ∀ v : Fin 4 → H^{(k : ℝ)}(ℂ),
      (∀ a, ⇑(inclusionLp (Nat.cast_nonneg k) (v a)) =ᵐ[volume]
        fun z ↦ ((Real.exp (c * √(1 + ‖z‖ ^ 2)) • f z) a : ℂ)) →
      ∃ u : Fin 4 → H^{(k : ℝ) + 1}(ℂ),
        (∀ a, ⇑(inclusionLp (by positivity) (u a)) =ᵐ[volume]
          fun z ↦ ((Real.exp (c * √(1 + ‖z‖ ^ 2)) • y z) a : ℂ)) ∧ ‖u‖ ≤ K * ‖v‖ :=
  exists_norm_exp_mul_smul_le_mul_norm_of_integral_inner_gaugeFixedAdjoint_eq k
    (contDiff_of_forall_mem_framedFieldSpace hx hmem) hsol
    (tendsto_normSq_of_mem_framedFieldSpace one_lt_two (by exact_mod_cast hmem 2) hx)
    (fun i n _ ↦ exists_norm_iteratedFDeriv_le_of_mem_framedFieldSpace hx i n (hmem (n + 2))) hc

/-! ### The weighted estimate for the adjoint of the right inverse -/

/-- **The weighted Sobolev estimate for the adjoint of the right inverse at a plane vortex.** Let
`x` be a smooth solution of the plane vortex equations with `|α| → 1` at infinity whose
coordinates have bounded derivatives through order `k`, let `ρ(z) = √(1 + |z|²)` and
`|c| < 1/2`. There is a constant `K` with the following property. Let `Q` be a bounded operator on
`L²(ℂ; ℝ⁴)` such that `Q f` is a weak solution of `L_x y = f` orthogonal to the weak kernel of
`L_x` for every `f`, for instance the weak right inverse of
`exists_continuousLinearMap_integral_inner_gaugeFixedAdjoint_eq`, and let `g ∈ L²` be orthogonal
to the weak kernel of `L_x`. If the coordinates of `exp(c ρ) g` are given by
`v : Fin 4 → H^k(ℂ)`, then those of `exp(c ρ) Q† g` are given by some
`u : Fin 4 → H^(k+1)(ℂ)` with `‖u‖ ≤ K ‖v‖`. That is,

`‖exp(c ρ) Q† g‖_(H^(k+1)) ≤ K ‖exp(c ρ) g‖_(H^k)`

on the `L²`-orthogonal complement of the weak kernel, where the Hilbert space adjoint `Q†` is the
left inverse of `L_x*` vanishing on the weak kernel. -/
theorem exists_norm_exp_mul_smul_adjoint_apply_le_mul_norm (k : ℕ)
    (hx : ContDiff ℝ ∞ x) (hsol : ∀ z, equation x z = 0)
    (hlim : Tendsto (fun z ↦ 4 * (x z 2 ^ 2 + x z 3 ^ 2)) (cocompact ℂ) (𝓝 1))
    (hbound : ∀ i, ∀ n ≤ k, ∃ C, ∀ z, ‖iteratedFDeriv ℝ n (fun z ↦ x z i) z‖ ≤ C)
    {c : ℝ} (hc : |c| < 1 / 2) :
    ∃ K ≥ 0, ∀ Q : Lp (EuclideanSpace ℝ (Fin 4)) 2 volume →L[ℝ]
        Lp (EuclideanSpace ℝ (Fin 4)) 2 volume,
      (∀ f η, ContDiff ℝ 2 η → HasCompactSupport η →
        ∫ z, ⟪Q f z, gaugeFixedAdjoint x η z⟫ = ∫ z, ⟪f z, η z⟫) →
      (∀ f w : Lp (EuclideanSpace ℝ (Fin 4)) 2 volume,
        (∀ η, ContDiff ℝ 2 η → HasCompactSupport η →
          ∫ z, ⟪w z, gaugeFixedAdjoint x η z⟫ = 0) →
        ∫ z, ⟪Q f z, w z⟫ = 0) →
      ∀ g : Lp (EuclideanSpace ℝ (Fin 4)) 2 volume,
      (∀ w : Lp (EuclideanSpace ℝ (Fin 4)) 2 volume,
        (∀ η, ContDiff ℝ 2 η → HasCompactSupport η →
          ∫ z, ⟪w z, gaugeFixedAdjoint x η z⟫ = 0) →
        ∫ z, ⟪g z, w z⟫ = 0) →
      ∀ v : Fin 4 → H^{(k : ℝ)}(ℂ),
      (∀ a, ⇑(inclusionLp (Nat.cast_nonneg k) (v a)) =ᵐ[volume]
        fun z ↦ ((Real.exp (c * √(1 + ‖z‖ ^ 2)) • g z) a : ℂ)) →
      ∃ u : Fin 4 → H^{(k : ℝ) + 1}(ℂ),
        (∀ a, ⇑(inclusionLp (by positivity) (u a)) =ᵐ[volume]
          fun z ↦ ((Real.exp (c * √(1 + ‖z‖ ^ 2)) • ContinuousLinearMap.adjoint Q g z) a : ℂ)) ∧
        ‖u‖ ≤ K * ‖v‖ := by
  -- `H = exp(c ρ) Q† g` solves `L_x* H = exp(c ρ) g - Aᵀ H` for the weight commutator
  -- `A = expWeightCoeff c`, so the elliptic estimate for `L_x*` bounds it by
  -- `‖exp(c ρ) g‖_(H^k)` and its weighted `L²` norm, which the weighted `L²` estimate for `Q†`
  -- bounds by `‖exp(c ρ) g‖_(L²)`.
  have hA (i j : Fin 4) : ContDiff ℝ ∞ (fun z ↦ -expWeightCoeff c j i z) :=
    (contDiff_expWeightCoeff c j i).neg
  have hAbound (i j : Fin 4) : ∃ M ≥ 0, ∀ n ≤ k, ∀ z,
      ‖iteratedFDeriv ℝ n (fun z ↦ -expWeightCoeff c j i z) z‖ ≤ M := by
    obtain ⟨M, hM, hMb⟩ := exists_norm_iteratedFDeriv_expWeightCoeff_le c j i k
    refine ⟨M, hM, fun n hn z ↦ ?_⟩
    rw [← Pi.neg_def, iteratedFDeriv_neg_apply, norm_neg]
    exact hMb n hn z
  obtain ⟨K₀, hK₀⟩ := exists_eLpNorm_exp_mul_smul_adjoint_apply_le (μ := volume)
    (hx.of_le (by exact_mod_cast le_top)) hsol hlim hc
  obtain ⟨K₁, hK₁, hK₁b⟩ :=
    exists_norm_le_mul_add_of_integral_inner_gaugeFixedOperator_eq_add k hx hbound hA hAbound
  refine ⟨K₁ * (1 + 4 * K₀), by positivity, fun Q hweak horth g hg v hv ↦ ?_⟩
  have hwg : (fun z ↦ Real.exp (c * √(1 + ‖z‖ ^ 2)) • g z) ∈ sobolevFields k :=
    (mem_sobolevFields_iff_exists_inclusionLp_ae_eq (Nat.cast_nonneg k)).2 ⟨v, hv⟩
  have hHweak (w : ℂ → EuclideanSpace ℝ (Fin 4)) (hw : ContDiff ℝ ∞ w)
      (hwc : HasCompactSupport w) :=
    integral_inner_exp_mul_smul_gaugeFixedOperator_eq (c := c) hx.continuous (Lp.memLp _)
      (Lp.memLp g) (fun w hw hwc ↦ integral_inner_adjoint_apply_gaugeFixedOperator_eq
        hx.continuous hweak hg (hw.of_le (by exact_mod_cast le_top)) hwc) hw hwc
  have hH : MemLp
      (fun z ↦ Real.exp (c * √(1 + ‖z‖ ^ 2)) • ContinuousLinearMap.adjoint Q g z) 2 volume :=
    memLp_iff.2 <| (hK₀ Q hweak horth g).trans_lt
      (ENNReal.mul_lt_top ENNReal.coe_lt_top (memLp_of_mem_sobolevFields hwg).eLpNorm_lt_top)
  obtain ⟨u, hu⟩ := (mem_sobolevFields_iff_exists_inclusionLp_ae_eq (by positivity)).1
    (mem_sobolevFields_natCast_add_one_of_integral_inner_gaugeFixedOperator_eq_add k hx hbound
      hA hAbound hH hwg hHweak)
  refine ⟨u, hu, ?_⟩
  have hL2 : (eLpNorm (fun z ↦ Real.exp (c * √(1 + ‖z‖ ^ 2)) •
      ContinuousLinearMap.adjoint Q g z) 2 volume).toReal ≤ 4 * K₀ * ‖v‖ := by
    refine ENNReal.toReal_le_of_le_ofReal (by positivity) ((hK₀ Q hweak horth g).trans ?_)
    rw [show (4 : ℝ) * K₀ * ‖v‖ = K₀ * (4 * ‖v‖) by ring, ENNReal.ofReal_mul K₀.coe_nonneg,
      ENNReal.ofReal_coe_nnreal]
    gcongr
    exact eLpNorm_le_of_forall_inclusionLp_ae_eq (Nat.cast_nonneg k) hv
  calc ‖u‖ ≤ K₁ * (‖v‖ + (eLpNorm (fun z ↦ Real.exp (c * √(1 + ‖z‖ ^ 2)) •
        ContinuousLinearMap.adjoint Q g z) 2 volume).toReal) := hK₁b _ _ u v hu hv hHweak
    _ ≤ K₁ * (‖v‖ + 4 * K₀ * ‖v‖) := by gcongr
    _ = K₁ * (1 + 4 * K₀) * ‖v‖ := by ring

/-- **The weighted Sobolev estimate for the adjoint of the right inverse at a vortex of every
`A_m^k`.** Let `x` be a continuous solution of the plane vortex equations lying in the affine
field space `A_m^k` for every `k`, and let `ρ(z) = √(1 + |z|²)` and `|c| < 1/2`. For every `k`
there is a constant `K` such that, if `Q` is a weak right inverse of `L_x` with values orthogonal
to the weak kernel and `g ∈ L²` is orthogonal to the weak kernel, then
`‖exp(c ρ) Q† g‖_(H^(k+1)) ≤ K ‖exp(c ρ) g‖_(H^k)`, in the sense of
`exists_norm_exp_mul_smul_adjoint_apply_le_mul_norm`. -/
theorem exists_norm_exp_mul_smul_adjoint_apply_le_mul_norm_of_forall_mem_framedFieldSpace
    {b : ContDiffBump (0 : ℝ)} {m : ℕ} (hx : Continuous x)
    (hmem : ∀ k : ℕ, x ∈ framedFieldSpace b m k) (hsol : ∀ z, equation x z = 0) {c : ℝ}
    (hc : |c| < 1 / 2) (k : ℕ) :
    ∃ K ≥ 0, ∀ Q : Lp (EuclideanSpace ℝ (Fin 4)) 2 volume →L[ℝ]
        Lp (EuclideanSpace ℝ (Fin 4)) 2 volume,
      (∀ f η, ContDiff ℝ 2 η → HasCompactSupport η →
        ∫ z, ⟪Q f z, gaugeFixedAdjoint x η z⟫ = ∫ z, ⟪f z, η z⟫) →
      (∀ f w : Lp (EuclideanSpace ℝ (Fin 4)) 2 volume,
        (∀ η, ContDiff ℝ 2 η → HasCompactSupport η →
          ∫ z, ⟪w z, gaugeFixedAdjoint x η z⟫ = 0) →
        ∫ z, ⟪Q f z, w z⟫ = 0) →
      ∀ g : Lp (EuclideanSpace ℝ (Fin 4)) 2 volume,
      (∀ w : Lp (EuclideanSpace ℝ (Fin 4)) 2 volume,
        (∀ η, ContDiff ℝ 2 η → HasCompactSupport η →
          ∫ z, ⟪w z, gaugeFixedAdjoint x η z⟫ = 0) →
        ∫ z, ⟪g z, w z⟫ = 0) →
      ∀ v : Fin 4 → H^{(k : ℝ)}(ℂ),
      (∀ a, ⇑(inclusionLp (Nat.cast_nonneg k) (v a)) =ᵐ[volume]
        fun z ↦ ((Real.exp (c * √(1 + ‖z‖ ^ 2)) • g z) a : ℂ)) →
      ∃ u : Fin 4 → H^{(k : ℝ) + 1}(ℂ),
        (∀ a, ⇑(inclusionLp (by positivity) (u a)) =ᵐ[volume]
          fun z ↦ ((Real.exp (c * √(1 + ‖z‖ ^ 2)) • ContinuousLinearMap.adjoint Q g z) a : ℂ)) ∧
        ‖u‖ ≤ K * ‖v‖ :=
  exists_norm_exp_mul_smul_adjoint_apply_le_mul_norm k
    (contDiff_of_forall_mem_framedFieldSpace hx hmem) hsol
    (tendsto_normSq_of_mem_framedFieldSpace one_lt_two (by exact_mod_cast hmem 2) hx)
    (fun i n _ ↦ exists_norm_iteratedFDeriv_le_of_mem_framedFieldSpace hx i n (hmem (n + 2))) hc

end TauCeti.Vortex
