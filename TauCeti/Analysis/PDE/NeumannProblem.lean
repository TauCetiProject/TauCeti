/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Operator.Compact.Basic
public import TauCeti.Analysis.InnerProductSpace.LaxMilgram
public import TauCeti.Analysis.PDE.EnergyForm.Sobolev
public import TauCeti.Analysis.Sobolev.LipschitzDomain.RellichKondrachov
public import TauCeti.Analysis.Sobolev.LipschitzDomain.Trace.Frontier
public import TauCeti.Analysis.Sobolev.W1p.MeasurePreserving
import TauCeti.Analysis.Normed.Operator.Compact.Estimate
import TauCeti.Analysis.Sobolev.Poincare.Wirtinger.W1p
import TauCeti.MeasureTheory.Function.Lp.Restriction
import TauCeti.MeasureTheory.Measure.Haar.InnerProductSpace

/-!
# The pure Neumann problem

Let `Ω ⊆ ℝⁿ` be open, preconnected and of finite measure, and let `a` be a principal coefficient
with essentially bounded energy density and an almost-everywhere lower quadratic bound
`λ‖ξ‖² ≤ ξ ⬝ a(x) ξ`, `λ > 0`; no symmetry of `a` is assumed. The weak form of the Neumann
problem

`-∂ᵢ(aⁱʲ ∂ⱼu) = f` in `Ω`, with conormal derivative `aⁱʲ ∂ⱼu νᵢ = 0` on `∂Ω`,

asks for `u ∈ H¹(Ω)` with `∫_Ω ⟨a ∇u, ∇v⟩ = ∫_Ω f v` for **every** `v ∈ H¹(Ω)`. Testing against all
of `H¹(Ω)`, rather than `H¹₀(Ω)` as for the Dirichlet problem, is what imposes the natural
boundary condition; no trace and no boundary regularity is needed to state it. More generally the
right-hand side is any `ℓ ∈ H¹(Ω)*`.

Testing with the constant `1`, whose gradient vanishes, shows that a solution can only exist when
`ℓ(1) = 0`; for `ℓ = ∫_Ω f ·` this is the compatibility condition `∫_Ω f = 0`. When the value map
`H¹(Ω) → L²(Ω)` is compact (Rellich), the condition is also sufficient, and solutions are unique
up to an additive constant. With `m(u) = ∫_Ω u`, the perturbed form

`B'(u, v) = ∫_Ω ⟨a ∇u, ∇v⟩ + m(u) m(v)`

is coercive on all of `H¹(Ω)`: the map `u ↦ (∇u, m(u))` is injective, since on a preconnected
domain a function with vanishing gradient is constant and a constant of mean zero vanishes, and
together with the compact value map it controls the `H¹` norm, so Peetre's compact-error estimate
`ContinuousLinearMap.exists_pos_mul_norm_le_of_compact_estimate` bounds it below. This is the
Poincaré–Wirtinger inequality in the form the Lax–Milgram theorem needs. The Lax–Milgram solution
`u` of `B'(u, ·) = ℓ` has `m(u) |Ω| = ℓ(1) = 0`, obtained by testing with `1`, so it solves the
Neumann problem and has mean zero.

On a bounded Lipschitz domain the compactness hypothesis is Rellich–Kondrachov
(`TauCeti.W1p.isCompactOperator_valueL_of_isLipschitzDomainWith`). Lipschitz domains are set in
the product `ℝ × E` of their boundary charts while the energy form lives on `EuclideanSpace ℝ ι`;
as in `TauCeti/Analysis/PDE/DirichletProblem/Trace.lean` the two are matched by an affine
isometry, along which compactness transfers
(`TauCeti.W1p.isCompactOperator_valueL_of_affineIsometryEquiv`).

Connectedness cannot be dropped: on `Ω = (0, 1) ∪ (2, 3)` the function equal to `0` on the first
interval and `1` on the second solves the homogeneous problem, so solutions are not unique up to
one constant, and the datum `f` equal to `1` on the first interval and `-1` on the second has
`∫_Ω f = 0` but no solution, since testing with the locally constant `f` itself gives `0 = 2`.

## Main declarations

* `TauCeti.PDE.exists_eq_add_const_of_forall_energyFormH1_eq`: two solutions of the Neumann
  problem with the same datum differ by a constant.
* `TauCeti.PDE.existsUnique_setIntegral_eq_zero_forall_energyFormH1_eq`: under `ℓ(1) = 0` there is
  exactly one solution of mean zero.
* `TauCeti.PDE.exists_forall_energyFormH1_eq_iff`: the Neumann problem with datum
  `ℓ ∈ H¹(Ω)*` is solvable exactly when `ℓ(1) = 0`.
* `TauCeti.PDE.exists_forall_energyFormH1_eq_setIntegral_iff`: with an `L²` datum `f`, it is
  solvable exactly when `∫_Ω f = 0`.
* `TauCeti.PDE.exists_forall_energyFormH1_eq_setIntegral_iff_of_isLipschitzDomainWith`: the same
  on a bounded connected Lipschitz domain.
* `TauCeti.PDE.exists_forall_energyFormH1_eq_setIntegral_add_frontierTrace_iff`: with a boundary
  datum `h` for the conormal derivative, the condition is `∫_Ω f + ∫_{∂Ω} h = 0`.

## References

* H. Brezis, *Functional Analysis, Sobolev Spaces and Partial Differential Equations*,
  Proposition 9.24 (the weak Neumann problem for `-Δu + u = f`) and Problem 47, part B (the
  compatibility condition `∫ f = 0` for `-u'' = f` with Neumann conditions).
* L. C. Evans, *Partial Differential Equations*, 2nd ed., §5.8.1, Theorem 1 (the
  Poincaré–Wirtinger inequality by compactness).
-/

public section

noncomputable section

open Bornology MeasureTheory Module Set TopologicalSpace
open scoped InnerProductSpace Matrix NNReal

namespace TauCeti

namespace PDE

variable {ι : Type*} [Fintype ι] {mu : Measure (EuclideanSpace ℝ ι)} [mu.IsAddHaarMeasure]
  {Omega : Opens (EuclideanSpace ℝ ι)} {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ} {lam : ℝ}

section FiniteMeasure

variable [IsFiniteMeasure (mu.restrict (Omega : Set (EuclideanSpace ℝ ι)))]

/-- The integral `∫_Ω u` as a continuous linear functional on `H¹(Ω)`. -/
private def integralL : W1p mu Omega 2 →L[ℝ] ℝ :=
  (setIntegralLp (μ := mu.restrict Omega) (𝕜 := ℝ) univ (measure_lt_top _ _)).comp W1p.valueL

private theorem integralL_apply (u : W1p mu Omega 2) :
    integralL u = ∫ x in Omega, W1p.value u x ∂mu := by
  rw [integralL, ContinuousLinearMap.comp_apply, setIntegralLp_apply, Measure.restrict_univ,
    W1p.valueL_apply]

private theorem integralL_const (δ : ℝ) :
    integralL (W1p.const δ : W1p mu Omega 2) = mu.real Omega * δ := by
  rw [integralL_apply, ← smul_eq_mul, ← setIntegral_const]
  refine integral_congr_ae ?_
  filter_upwards [Lp.coeFn_const 2 (mu.restrict (Omega : Set (EuclideanSpace ℝ ι))) δ] with x hx
  rw [W1p.value_const, hx, Function.const_apply]

/-- A constant whose integral over `Ω` vanishes is zero in `H¹(Ω)`: either the constant is `0`, or
`Ω` is a null set and `H¹(Ω)` is trivial. -/
private theorem const_eq_zero_of_integralL_eq_zero {δ : ℝ}
    (h : integralL (W1p.const δ : W1p mu Omega 2) = 0) : (W1p.const δ : W1p mu Omega 2) = 0 := by
  rw [integralL_const] at h
  have hδ : ∀ᵐ _x ∂mu.restrict Omega, δ = 0 := by
    rcases mul_eq_zero.1 h with h0 | h0
    · simp [Measure.restrict_eq_zero.2
        ((measureReal_eq_zero_iff (isFiniteMeasure_restrict.1 inferInstance)).1 h0)]
    · exact ae_of_all _ fun _ => h0
  apply W1p.ext_value
  rw [← W1p.valueL_apply, ← W1p.valueL_apply, map_zero, W1p.valueL_apply, W1p.value_const]
  refine Lp.ext ?_
  filter_upwards [hδ, Lp.coeFn_const 2 (mu.restrict (Omega : Set (EuclideanSpace ℝ ι))) δ,
    Lp.coeFn_zero ℝ 2 (mu.restrict (Omega : Set (EuclideanSpace ℝ ι)))] with x h0 h1 h2
  rw [h1, h2, Function.const_apply, h0, Pi.zero_apply]

/-- Shortcut seminormed group instance on `W^{1,2}(Ω)`, to aid instance search for continuous
bilinear forms on it. -/
local instance instSeminormedAddCommGroupW1pNeumann :
    SeminormedAddCommGroup (W1p mu Omega 2) := inferInstance

/-- Shortcut normed space instance on `W^{1,2}(Ω)`, to aid instance search for continuous
bilinear forms on it. -/
local instance instNormedSpaceW1pNeumann : NormedSpace ℝ (W1p mu Omega 2) := inferInstance

/-- **Coercivity of the mean-corrected energy form.** If the value map `H¹(Ω) → L²(Ω)` is compact
and `Ω` is preconnected, the form `∫_Ω ⟨a ∇u, ∇v⟩ + (∫_Ω u)(∫_Ω v)` is coercive on `H¹(Ω)`. -/
private theorem isCoercive_energyFormH1L_add_integralL
    (hK : IsCompactOperator (W1p.valueL (mu := mu) (Omega := Omega) (p := 2)))
    (hconn : IsPreconnected (Omega : Set (EuclideanSpace ℝ ι)))
    (hcoeff : MemLp (fun x => energyIntegrand (a x) 0 0) ⊤ (mu.restrict Omega)) (hlam : 0 < lam)
    (ha : ∀ᵐ x ∂mu.restrict Omega, ∀ ξ : EuclideanSpace ℝ ι, lam * ‖ξ‖ ^ 2 ≤ ξ ⬝ᵥ (a x *ᵥ ξ)) :
    IsCoercive (energyFormH1L (b := 0) (c := 0) hcoeff +
      (ContinuousLinearMap.mul ℝ ℝ).bilinearComp (integralL (mu := mu) (Omega := Omega))
        (integralL (mu := mu) (Omega := Omega))) := by
  -- The gradient together with the mean is injective on a preconnected domain.
  let T := (W1p.gradientL (mu := mu) (Omega := Omega) (p := 2)).prod
    (integralL (mu := mu) (Omega := Omega))
  have hdisj : Disjoint T.ker (⊤ : Submodule ℝ (W1p mu Omega 2)) := by
    rw [Submodule.disjoint_def]
    intro u hu _
    rw [LinearMap.mem_ker, ContinuousLinearMap.coe_coe, ContinuousLinearMap.prod_apply,
      Prod.mk_eq_zero, W1p.gradientL_apply] at hu
    obtain ⟨δ, rfl⟩ := W1p.exists_eq_const_of_gradient_eq_zero hconn hu.1
    exact const_eq_zero_of_integralL_eq_zero hu.2
  -- With the compact value map it bounds the `H¹` norm below (Peetre).
  obtain ⟨c, hc, hcT⟩ := T.exists_pos_mul_norm_le_of_compact_estimate (C := 1) hK
    (fun u => by
      have h1 := W1p.norm_le_norm_value_add_norm_gradient u
      have h2 : ‖W1p.gradient u‖ ≤ ‖T u‖ := by simp [T, Prod.norm_def]
      rw [one_mul, W1p.valueL_apply]
      linarith)
    (by simp) hdisj
  refine ⟨min lam 1 * c ^ 2, by positivity, fun u => ?_⟩
  have hT : c * ‖u‖ ≤ max ‖W1p.gradient u‖ |integralL u| := by
    simpa [T, Prod.norm_def] using hcT u Submodule.mem_top
  have hsq : (c * ‖u‖) ^ 2 ≤ ‖W1p.gradient u‖ ^ 2 + integralL u ^ 2 := by
    have h0 : 0 ≤ c * ‖u‖ := by positivity
    rcases le_total ‖W1p.gradient u‖ |integralL u| with hle | hle
    · rw [max_eq_right hle] at hT
      nlinarith [sq_abs (integralL u), sq_nonneg ‖W1p.gradient u‖]
    · rw [max_eq_left hle] at hT
      nlinarith [sq_nonneg (integralL u)]
  have hE := mul_norm_gradient_sq_le_energyFormH1_self (c := 0) hcoeff ha
    (ae_of_all _ fun _ => le_rfl) u
  have hmin : min lam 1 * (‖W1p.gradient u‖ ^ 2 + integralL u ^ 2) ≤
      lam * ‖W1p.gradient u‖ ^ 2 + integralL u ^ 2 := by
    nlinarith [min_le_left lam 1, min_le_right lam 1, sq_nonneg ‖W1p.gradient u‖,
      sq_nonneg (integralL u)]
  simp only [add_apply, energyFormH1L_apply,
    ContinuousLinearMap.bilinearComp_apply, ContinuousLinearMap.mul_apply']
  nlinarith [mul_le_mul_of_nonneg_left hsq (le_min hlam.le zero_le_one)]

/-- **Uniqueness for the Neumann problem up to constants.** Let `Ω` be preconnected and of finite
measure, and let `a` have essentially bounded energy density and satisfy `λ‖ξ‖² ≤ ξ ⬝ a(x) ξ`
almost everywhere on `Ω`, with `λ > 0`. If `∫_Ω ⟨a ∇u₁, ∇v⟩ = ∫_Ω ⟨a ∇u₂, ∇v⟩` for every
`v ∈ H¹(Ω)`, then `u₁ - u₂` is a constant. No compactness is needed. -/
theorem exists_eq_add_const_of_forall_energyFormH1_eq
    (hconn : IsPreconnected (Omega : Set (EuclideanSpace ℝ ι)))
    (hcoeff : MemLp (fun x => energyIntegrand (a x) 0 0) ⊤ (mu.restrict Omega)) (hlam : 0 < lam)
    (ha : ∀ᵐ x ∂mu.restrict Omega, ∀ ξ : EuclideanSpace ℝ ι, lam * ‖ξ‖ ^ 2 ≤ ξ ⬝ᵥ (a x *ᵥ ξ))
    {u₁ u₂ : W1p mu Omega 2}
    (h : ∀ v : W1p mu Omega 2, energyFormH1 a 0 0 u₁ v = energyFormH1 a 0 0 u₂ v) :
    ∃ δ : ℝ, u₁ = u₂ + W1p.const δ := by
  have hE := mul_norm_gradient_sq_le_energyFormH1_self (c := 0) hcoeff ha
    (ae_of_all _ fun _ => le_rfl) (u₁ - u₂)
  rw [energyFormH1_sub_left (b := 0) (c := 0) hcoeff, h, sub_self] at hE
  have hg : W1p.gradient (u₁ - u₂) = 0 := by
    have hsq : ‖W1p.gradient (u₁ - u₂)‖ ^ 2 = 0 :=
      le_antisymm (nonpos_of_mul_nonpos_right hE hlam) (sq_nonneg _)
    exact norm_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1 hsq)
  obtain ⟨δ, hδ⟩ := W1p.exists_eq_const_of_gradient_eq_zero hconn hg
  exact ⟨δ, by rw [← hδ, add_sub_cancel]⟩

/-- **The Neumann problem: existence and uniqueness of the solution of mean zero.** Let `Ω` be
preconnected and of finite measure with compact value map `H¹(Ω) → L²(Ω)`, and let `a` have
essentially bounded energy density and satisfy `λ‖ξ‖² ≤ ξ ⬝ a(x) ξ` almost everywhere on `Ω`, with
`λ > 0`. If `ℓ ∈ H¹(Ω)*` vanishes on the constant `1`, there is exactly one `u ∈ H¹(Ω)` with
`∫_Ω u = 0` and

`∫_Ω ⟨a ∇u, ∇v⟩ = ℓ v` for every `v ∈ H¹(Ω)`,

the weak solution of `-∂ᵢ(aⁱʲ ∂ⱼu) = ℓ` with homogeneous conormal boundary condition. -/
theorem existsUnique_setIntegral_eq_zero_forall_energyFormH1_eq
    (hK : IsCompactOperator (W1p.valueL (mu := mu) (Omega := Omega) (p := 2)))
    (hconn : IsPreconnected (Omega : Set (EuclideanSpace ℝ ι)))
    (hcoeff : MemLp (fun x => energyIntegrand (a x) 0 0) ⊤ (mu.restrict Omega)) (hlam : 0 < lam)
    (ha : ∀ᵐ x ∂mu.restrict Omega, ∀ ξ : EuclideanSpace ℝ ι, lam * ‖ξ‖ ^ 2 ≤ ξ ⬝ᵥ (a x *ᵥ ξ))
    {ℓ : StrongDual ℝ (W1p mu Omega 2)} (hℓ : ℓ (W1p.const 1) = 0) :
    ∃! u : W1p mu Omega 2, ∫ x in Omega, W1p.value u x ∂mu = 0 ∧
      ∀ v : W1p mu Omega 2, energyFormH1 a 0 0 u v = ℓ v := by
  obtain ⟨u, hu⟩ :=
    (isCoercive_energyFormH1L_add_integralL hK hconn hcoeff hlam ha).exists_forall_eq ℓ
  have hB (v : W1p mu Omega 2) : energyFormH1 a 0 0 u v + integralL u * integralL v = ℓ v := by
    simpa using hu v
  -- Testing with the constant `1` shows that `u` has mean zero.
  have hm : integralL u = 0 := by
    have h1 := hB (W1p.const 1)
    rw [energyFormH1_const_right, zero_add, hℓ, integralL_const, mul_one] at h1
    rcases mul_eq_zero.1 h1 with h0 | h0
    · exact h0
    · rw [integralL_apply]
      exact setIntegral_measure_zero _
        ((measureReal_eq_zero_iff (isFiniteMeasure_restrict.1 inferInstance)).1 h0)
  refine ⟨u, ⟨(integralL_apply u).symm.trans hm, fun v => ?_⟩, fun w hw => ?_⟩
  · simpa [hm] using hB v
  -- Two solutions of mean zero differ by a constant of mean zero, which vanishes.
  obtain ⟨δ, hδ⟩ := exists_eq_add_const_of_forall_energyFormH1_eq hconn hcoeff hlam ha
    (u₁ := w) (u₂ := u) fun v => (hw.2 v).trans (by simpa [hm] using (hB v).symm)
  have hint : integralL (W1p.const δ : W1p mu Omega 2) = 0 := by
    have h := congrArg integralL hδ
    rw [map_add, integralL_apply, integralL_apply, hw.1, hm.symm.trans (integralL_apply u)] at h
    linarith
  rw [hδ, const_eq_zero_of_integralL_eq_zero hint, add_zero]

/-- **Solvability of the Neumann problem.** Under the hypotheses of
`TauCeti.PDE.existsUnique_setIntegral_eq_zero_forall_energyFormH1_eq`, the problem
`∫_Ω ⟨a ∇u, ∇v⟩ = ℓ v` for every `v ∈ H¹(Ω)` has a solution `u ∈ H¹(Ω)` exactly when `ℓ`
vanishes on the constant `1`. Necessity holds because constants have zero gradient. -/
theorem exists_forall_energyFormH1_eq_iff
    (hK : IsCompactOperator (W1p.valueL (mu := mu) (Omega := Omega) (p := 2)))
    (hconn : IsPreconnected (Omega : Set (EuclideanSpace ℝ ι)))
    (hcoeff : MemLp (fun x => energyIntegrand (a x) 0 0) ⊤ (mu.restrict Omega)) (hlam : 0 < lam)
    (ha : ∀ᵐ x ∂mu.restrict Omega, ∀ ξ : EuclideanSpace ℝ ι, lam * ‖ξ‖ ^ 2 ≤ ξ ⬝ᵥ (a x *ᵥ ξ))
    (ℓ : StrongDual ℝ (W1p mu Omega 2)) :
    (∃ u : W1p mu Omega 2, ∀ v : W1p mu Omega 2, energyFormH1 a 0 0 u v = ℓ v) ↔
      ℓ (W1p.const 1) = 0 :=
  ⟨fun ⟨u, hu⟩ => (hu _).symm.trans (energyFormH1_const_right a u 1), fun hℓ =>
    (existsUnique_setIntegral_eq_zero_forall_energyFormH1_eq hK hconn hcoeff hlam ha
      hℓ).exists.imp fun _ h => h.2⟩

/-- **The compatibility condition of the Neumann problem.** Under the hypotheses of
`TauCeti.PDE.existsUnique_setIntegral_eq_zero_forall_energyFormH1_eq`, for `f ∈ L²(Ω)` the weak
Neumann problem `-∂ᵢ(aⁱʲ ∂ⱼu) = f` in `Ω`, `aⁱʲ ∂ⱼu νᵢ = 0` on `∂Ω`, that is

`∫_Ω ⟨a ∇u, ∇v⟩ = ∫_Ω f v` for every `v ∈ H¹(Ω)`,

has a solution `u ∈ H¹(Ω)` exactly when `∫_Ω f = 0`. -/
theorem exists_forall_energyFormH1_eq_setIntegral_iff
    (hK : IsCompactOperator (W1p.valueL (mu := mu) (Omega := Omega) (p := 2)))
    (hconn : IsPreconnected (Omega : Set (EuclideanSpace ℝ ι)))
    (hcoeff : MemLp (fun x => energyIntegrand (a x) 0 0) ⊤ (mu.restrict Omega)) (hlam : 0 < lam)
    (ha : ∀ᵐ x ∂mu.restrict Omega, ∀ ξ : EuclideanSpace ℝ ι, lam * ‖ξ‖ ^ 2 ≤ ξ ⬝ᵥ (a x *ᵥ ξ))
    (f : Lp ℝ 2 (mu.restrict Omega)) :
    (∃ u : W1p mu Omega 2, ∀ v : W1p mu Omega 2,
        energyFormH1 a 0 0 u v = ∫ x in Omega, f x * W1p.value v x ∂mu) ↔
      ∫ x in Omega, f x ∂mu = 0 := by
  let ℓ : StrongDual ℝ (W1p mu Omega 2) := (innerSL ℝ f).comp W1p.valueL
  have hℓ (v : W1p mu Omega 2) : ℓ v = ∫ x in Omega, f x * W1p.value v x ∂mu := by
    simp only [ℓ, ContinuousLinearMap.comp_apply, innerSL_apply_apply, W1p.valueL_apply,
      L2.inner_def, RCLike.inner_apply, conj_trivial]
    exact integral_congr_ae (ae_of_all _ fun _ => mul_comm _ _)
  have h1 : ℓ (W1p.const 1) = ∫ x in Omega, f x ∂mu := by
    rw [hℓ]
    refine integral_congr_ae ?_
    filter_upwards [Lp.coeFn_const 2 (mu.restrict (Omega : Set (EuclideanSpace ℝ ι))) (1 : ℝ)]
      with x hx
    rw [W1p.value_const, hx, Function.const_apply, mul_one]
  have key := exists_forall_energyFormH1_eq_iff hK hconn hcoeff hlam ha ℓ
  rw [h1] at key
  simpa only [hℓ] using key

end FiniteMeasure

section LipschitzDomain

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {V : Opens (WithLp 2 (ℝ × E))} {L : ℝ≥0}
  {Ω : Opens (EuclideanSpace ℝ ι)}

/-- An isometric copy `Ω` of a bounded Lipschitz domain has finite measure, and its value map
`H¹(Ω) → L²(Ω)` is compact. -/
private theorem isFiniteMeasure_and_isCompactOperator_valueL
    (hV : (V : Set (WithLp 2 (ℝ × E))).IsLipschitzDomainWith L)
    (hVb : IsBounded (V : Set (WithLp 2 (ℝ × E))))
    (e : EuclideanSpace ℝ ι ≃ᵃⁱ[ℝ] WithLp 2 (ℝ × E))
    (hVΩ : (V : Set (WithLp 2 (ℝ × E))) = e.symm ⁻¹' Ω) :
    IsFiniteMeasure (volume.restrict (Ω : Set (EuclideanSpace ℝ ι))) ∧
      IsCompactOperator (W1p.valueL (mu := volume) (Omega := Ω) (p := 2)) := by
  have hΩV : (Ω : Set (EuclideanSpace ℝ ι)) = e ⁻¹' V := by
    rw [hVΩ, ← preimage_comp]
    ext x
    simp
  have hΩb : IsBounded (Ω : Set (EuclideanSpace ℝ ι)) := by
    rw [hΩV]
    exact e.isometry.antilipschitzWith.isBounded_preimage hVb
  exact ⟨isFiniteMeasure_restrict.2 hΩb.measure_lt_top.ne,
    W1p.isCompactOperator_valueL_of_affineIsometryEquiv e hΩV
      (W1p.isCompactOperator_valueL_of_isLipschitzDomainWith hV hVb)⟩

/-- **The Neumann problem on a bounded Lipschitz domain.** Let an affine isometry `e` carry
`Ω ⊆ EuclideanSpace ℝ ι` onto a bounded Lipschitz domain `V`, and let `Ω` be connected. Let `a`
have essentially bounded energy density and satisfy `λ‖ξ‖² ≤ ξ ⬝ a(x) ξ` almost everywhere on `Ω`,
with `λ > 0`, as an inverse-coercive coefficient does (`TauCeti.PDE.IsUniformlyEllipticAE`). For
`f ∈ L²(Ω)` the weak Neumann problem

`∫_Ω ⟨a ∇u, ∇v⟩ = ∫_Ω f v` for every `v ∈ H¹(Ω)`

has a solution `u ∈ H¹(Ω)` exactly when `∫_Ω f = 0`; by
`TauCeti.PDE.exists_eq_add_const_of_forall_energyFormH1_eq` it is then unique up to an additive
constant. -/
theorem exists_forall_energyFormH1_eq_setIntegral_iff_of_isLipschitzDomainWith
    (hV : (V : Set (WithLp 2 (ℝ × E))).IsLipschitzDomainWith L)
    (hVb : IsBounded (V : Set (WithLp 2 (ℝ × E))))
    (e : EuclideanSpace ℝ ι ≃ᵃⁱ[ℝ] WithLp 2 (ℝ × E))
    (hVΩ : (V : Set (WithLp 2 (ℝ × E))) = e.symm ⁻¹' Ω)
    (hconn : IsPreconnected (Ω : Set (EuclideanSpace ℝ ι)))
    (hcoeff : MemLp (fun x => energyIntegrand (a x) 0 0) ⊤ (volume.restrict Ω))
    (hlam : 0 < lam)
    (ha : ∀ᵐ x ∂volume.restrict Ω, ∀ ξ : EuclideanSpace ℝ ι, lam * ‖ξ‖ ^ 2 ≤ ξ ⬝ᵥ (a x *ᵥ ξ))
    (f : Lp ℝ 2 (volume.restrict Ω)) :
    (∃ u : W1p volume Ω 2, ∀ v : W1p volume Ω 2,
        energyFormH1 a 0 0 u v = ∫ x in Ω, f x * W1p.value v x) ↔
      ∫ x in Ω, f x = 0 := by
  obtain ⟨_, hK⟩ := isFiniteMeasure_and_isCompactOperator_valueL hV hVb e hVΩ
  exact exists_forall_energyFormH1_eq_setIntegral_iff hK hconn hcoeff hlam ha f

/-- **The Neumann problem with a boundary datum.** Under the hypotheses of
`TauCeti.PDE.exists_forall_energyFormH1_eq_setIntegral_iff_of_isLipschitzDomainWith`, let
`f ∈ L²(Ω)` and let `h ∈ L²(∂V)` for the surface measure `μHE` of the frontier of `V`. Writing `T`
for the trace on `∂V` (`TauCeti.W1p.frontierTrace`), the problem

`∫_Ω ⟨a ∇u, ∇v⟩ = ∫_Ω f v + ∫_{∂V} h · T(v ∘ e⁻¹) dμHE` for every `v ∈ H¹(Ω)`,

the weak form of `-∂ᵢ(aⁱʲ ∂ⱼu) = f` in `Ω` with conormal derivative `aⁱʲ ∂ⱼu νᵢ = h ∘ e` on `∂Ω`
for the outer normal `ν`, has a solution `u ∈ H¹(Ω)` exactly when
`∫_Ω f + ∫_{∂V} h dμHE = 0`. The constant `1` has trace `1`, which gives the boundary term. -/
theorem exists_forall_energyFormH1_eq_setIntegral_add_frontierTrace_iff
    (hV : (V : Set (WithLp 2 (ℝ × E))).IsLipschitzDomainWith L)
    (hVb : IsBounded (V : Set (WithLp 2 (ℝ × E))))
    (e : EuclideanSpace ℝ ι ≃ᵃⁱ[ℝ] WithLp 2 (ℝ × E))
    (hVΩ : (V : Set (WithLp 2 (ℝ × E))) = e.symm ⁻¹' Ω)
    (hconn : IsPreconnected (Ω : Set (EuclideanSpace ℝ ι)))
    (hcoeff : MemLp (fun x => energyIntegrand (a x) 0 0) ⊤ (volume.restrict Ω))
    (hlam : 0 < lam)
    (ha : ∀ᵐ x ∂volume.restrict Ω, ∀ ξ : EuclideanSpace ℝ ι, lam * ‖ξ‖ ^ 2 ≤ ξ ⬝ᵥ (a x *ᵥ ξ))
    (f : Lp ℝ 2 (volume.restrict Ω))
    (h : Lp ℝ 2 ((μHE[finrank ℝ E] : Measure (WithLp 2 (ℝ × E))).restrict
      (frontier (V : Set (WithLp 2 (ℝ × E)))))) :
    (∃ u : W1p volume Ω 2, ∀ v : W1p volume Ω 2,
        energyFormH1 a 0 0 u v = (∫ x in Ω, f x * W1p.value v x) +
          ∫ y in frontier (V : Set (WithLp 2 (ℝ × E))), h y *
            W1p.frontierTrace ENNReal.ofNat_ne_top hV hVb
              (W1p.compAffineIsometryEquivL e.symm hVΩ v) y ∂μHE[finrank ℝ E]) ↔
      (∫ x in Ω, f x) +
        ∫ y in frontier (V : Set (WithLp 2 (ℝ × E))), h y ∂μHE[finrank ℝ E] = 0 := by
  obtain ⟨_, hK⟩ := isFiniteMeasure_and_isCompactOperator_valueL hV hVb e hVΩ
  let ℓ : StrongDual ℝ (W1p volume Ω 2) := (innerSL ℝ f).comp W1p.valueL +
    (innerSL ℝ h).comp ((W1p.frontierTrace (p := 2) ENNReal.ofNat_ne_top hV hVb).comp
      (W1p.compAffineIsometryEquivL e.symm hVΩ))
  have hℓ (v : W1p volume Ω 2) : ℓ v = (∫ x in Ω, f x * W1p.value v x) +
      ∫ y in frontier (V : Set (WithLp 2 (ℝ × E))), h y *
        W1p.frontierTrace ENNReal.ofNat_ne_top hV hVb
          (W1p.compAffineIsometryEquivL e.symm hVΩ v) y ∂μHE[finrank ℝ E] := by
    simp only [ℓ, add_apply, ContinuousLinearMap.comp_apply, innerSL_apply_apply,
      W1p.valueL_apply, L2.inner_def, RCLike.inner_apply, conj_trivial]
    congr 1 <;> exact integral_congr_ae (ae_of_all _ fun _ => mul_comm _ _)
  -- The constant `1` has value `1` on `V` after the change of coordinates, hence trace `1`.
  have hv1 : W1p.value (W1p.compAffineIsometryEquivL e.symm hVΩ (W1p.const 1 : W1p volume Ω 2))
      =ᵐ[volume.restrict (V : Set (WithLp 2 (ℝ × E)))] fun _ => (1 : ℝ) := by
    have hmp : MeasurePreserving e.symm (volume.restrict (V : Set (WithLp 2 (ℝ × E))))
        (volume.restrict (Ω : Set (EuclideanSpace ℝ ι))) := by
      rw [hVΩ]
      exact e.symm.measurePreserving.restrict_preimage Ω.isOpen.measurableSet
    filter_upwards [W1p.value_compAffineIsometryEquivL_ae e.symm hVΩ
      (W1p.const 1 : W1p volume Ω 2),
      hmp.quasiMeasurePreserving.ae
        (Lp.coeFn_const 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ ι))) (1 : ℝ))]
      with y h1 h2
    rw [h1, W1p.value_const, h2, Function.const_apply]
  have hT1 := W1p.frontierTrace_ae_eq_of_continuousOn ENNReal.ofNat_ne_top hV hVb
    continuousOn_const hv1
  have h1 : ℓ (W1p.const 1) = (∫ x in Ω, f x) +
      ∫ y in frontier (V : Set (WithLp 2 (ℝ × E))), h y ∂μHE[finrank ℝ E] := by
    rw [hℓ]
    congr 1
    · refine integral_congr_ae ?_
      filter_upwards [Lp.coeFn_const 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ ι))) (1 : ℝ)]
        with x hx
      rw [W1p.value_const, hx, Function.const_apply, mul_one]
    · exact integral_congr_ae (hT1.mono fun y hy => by simp only [hy, mul_one])
  have key := exists_forall_energyFormH1_eq_iff hK hconn hcoeff hlam ha ℓ
  rw [h1] at key
  simpa only [hℓ] using key

end LipschitzDomain

end PDE

end TauCeti
