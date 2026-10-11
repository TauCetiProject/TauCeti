/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import TauCeti.Analysis.InnerProductSpace.GelfandTriple
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import TauCeti.Analysis.InnerProductSpace.Lions

/-!
# Existence for linear parabolic equations

Let `V ↪ H ↪ V*` be a Gelfand triple, given by a continuous linear map `ι : V →L[ℝ] H` from a
real Hilbert space `V` into a real inner product space `H` (`ContinuousLinearMap.gelfandDual`),
and consider on a time interval `(a, b)` the abstract linear parabolic problem

`u' + A(t) u = f`, `u(a) = u₀`,

with `A(t) : V →L[ℝ] V*` bounded and satisfying Gårding's inequality
`α ‖v‖² - β ‖ι v‖² ≤ A(t) v v`, `f ∈ L²(a, b; V*)` and `u₀ ∈ H`. Testing the equation against a
`C¹` function `φ : ℝ → V` with `φ(b) = 0` and integrating the time derivative by parts turns it
into the **variational formulation**

`∫ₐᵇ (A(t) u(t) φ(t) - ⟪ι u(t), ι φ'(t)⟫) dt = ∫ₐᵇ f(t) φ(t) dt + ⟪u₀, ι φ(a)⟫`,

in which neither the time derivative of `u` nor its value at `t = a` appears: the initial
condition is carried by the boundary term `⟪u₀, ι φ(a)⟫`. This file proves that the variational
formulation has a solution `u ∈ L²(a, b; V)`
(`TauCeti.exists_memLp_forall_setIntegral_eq_add_inner`).

That `u` is then a weak solution in the sense of
`TauCeti.HasWeakLineDerivOn.ae_eq_of_gelfandDual`, with weak time derivative
`u' = f - A u ∈ L²(a, b; V*)` and a continuous representative equal to `u₀` at `t = a`, is not
proved here.

## The proof

For coercive `A(t)` (the case `β = 0`) this is an application of Lions' representation theorem
(`LinearMap.exists_forall_apply_eq_and_norm_le_of_coercive`), with the Hilbert space
`L²(a, b; V)` for the solution and the `C¹` functions `φ` with `φ(b) = 0` for the test
functions. The left-hand side `E(φ, u)` is continuous in `u ∈ L²(a, b; V)`, being the `L²`
inner product of `u` with the Riesz representative of `t ↦ A(t)ᵀ φ(t) - ι* ι φ'(t)`. On the
diagonal, the fundamental theorem of calculus for `t ↦ ‖ι φ(t)‖²` and `φ(b) = 0` give

`E(φ, φ) = ∫ₐᵇ A(t) φ φ + ½ ‖ι φ(a)‖² ≥ α ‖φ‖²_{L²(V)} + ½ ‖ι φ(a)‖²`,

so `c p(φ)² ≤ E(φ, φ)` for `p(φ) = (‖φ‖²_{L²(V)} + ‖ι φ(a)‖²)^{1/2}` and `c = min α ½`, and the
right-hand side is bounded by `(‖f‖_{L²(V*)} + ‖u₀‖) p(φ)` by Cauchy–Schwarz.

In general, `u = e^{β (t - a)} w` solves the problem exactly when `w` solves it for the coercive
operator `A(t) + β ι* ι` and the right-hand side `e^{-β (t - a)} f`.

The coefficient `A` is assumed strongly measurable as a map into `V →L[ℝ] V*` and essentially
bounded by `Λ`.

## Main declarations

* `TauCeti.exists_memLp_forall_setIntegral_eq_add_inner`: the variational formulation of
  `u' + A(t) u = f`, `u(a) = u₀`, has a solution in `L²(a, b; V)`.

## References

* J.-L. Lions, *Équations différentielles opérationnelles et problèmes aux limites*,
  Grundlehren **111**, Springer, 1961.
* R. E. Showalter, *Monotone Operators in Banach Space and Nonlinear Partial Differential
  Equations*, Mathematical Surveys and Monographs **49**, AMS, 1997, Chapter III, Section 2.
* L. C. Evans, *Partial Differential Equations*, 2nd ed., §7.1.2, which constructs weak solutions
  of second-order parabolic equations by the Galerkin method instead.
-/

public section

open MeasureTheory Set
open scoped InnerProductSpace

namespace TauCeti

variable {V H : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] {A : ℝ → V →L[ℝ] StrongDual ℝ V}
  {f : ℝ → StrongDual ℝ V} {a b α β Λ : ℝ}

/-- The Riesz representative of `v ↦ A(t) v φ(t) - ⟪ι φ'(t), ι v⟫` is square integrable in time.
This is the vector against which `E(φ, ·)` pairs a solution in `L²(a, b; V)`. -/
private theorem memLp_toDual_symm_flip_sub [CompleteSpace V] (ι : V →L[ℝ] H)
    (hA : AEStronglyMeasurable A (volume.restrict (Ioo a b)))
    (hA_bound : ∀ᵐ t ∂volume.restrict (Ioo a b), ‖A t‖ ≤ Λ) {φ : ℝ → V}
    (hφ : ContDiff ℝ 1 φ) :
    MemLp (fun t => (InnerProductSpace.toDual ℝ V).symm
      ((A t).flip (φ t) - ι.gelfandDual (ι (deriv φ t)))) 2 (volume.restrict (Ioo a b)) := by
  set R := (InnerProductSpace.toDual ℝ V).symm
  have hφ' : Continuous (deriv φ) := hφ.continuous_deriv le_rfl
  obtain ⟨C₁, hC₁⟩ := isCompact_Icc.exists_bound_of_continuousOn (hφ.continuous.continuousOn
    (s := Icc a b))
  obtain ⟨C₂, hC₂⟩ := isCompact_Icc.exists_bound_of_continuousOn (hφ'.continuousOn (s := Icc a b))
  -- `t ↦ A(t)ᵀ φ(t)` is strongly measurable because `A` is and `φ` is continuous.
  have hflip : AEStronglyMeasurable (fun t => (A t).flip (φ t)) (volume.restrict (Ioo a b)) :=
    isBoundedBilinearMap_apply.continuous.comp_aestronglyMeasurable
      (((ContinuousLinearMap.flipₗᵢ ℝ V V ℝ).continuous.comp_aestronglyMeasurable hA).prodMk
        hφ.continuous.aestronglyMeasurable)
  have hmeas : AEStronglyMeasurable (fun t => (A t).flip (φ t) - ι.gelfandDual (ι (deriv φ t)))
      (volume.restrict (Ioo a b)) :=
    hflip.sub ((ι.gelfandDual.comp ι).continuous.comp hφ').aestronglyMeasurable
  have hmem : MemLp (fun t => (A t).flip (φ t) - ι.gelfandDual (ι (deriv φ t))) 2
      (volume.restrict (Ioo a b)) := by
    refine MemLp.of_bound hmeas (Λ * C₁ + ‖ι.gelfandDual.comp ι‖ * C₂) ?_
    filter_upwards [hA_bound, ae_restrict_mem measurableSet_Ioo] with t hAt ht
    have hΛ : 0 ≤ Λ := (norm_nonneg (A t)).trans hAt
    have h₁ := hC₁ t (Ioo_subset_Icc_self ht)
    have h₂ := hC₂ t (Ioo_subset_Icc_self ht)
    calc ‖(A t).flip (φ t) - ι.gelfandDual (ι (deriv φ t))‖
        ≤ ‖(A t).flip (φ t)‖ + ‖(ι.gelfandDual.comp ι) (deriv φ t)‖ := norm_sub_le _ _
      _ ≤ ‖A t‖ * ‖φ t‖ + ‖ι.gelfandDual.comp ι‖ * ‖deriv φ t‖ := by
          gcongr
          · exact ((A t).flip.le_opNorm _).trans (by rw [ContinuousLinearMap.opNorm_flip])
          · exact (ι.gelfandDual.comp ι).le_opNorm _
      _ ≤ Λ * C₁ + ‖ι.gelfandDual.comp ι‖ * C₂ := by gcongr
  exact hmem.of_le (R.continuous.comp_aestronglyMeasurable hmem.aestronglyMeasurable)
    (Filter.Eventually.of_forall fun t => (R.norm_map _).le)

/-- **The energy inequality behind coercivity.** For a `C¹` function `φ` with `φ(b) = 0`,
integrating `d/dt ‖ι φ‖² = 2 ⟪ι φ, ι φ'⟫` by parts and using coercivity of `A` gives

`α ∫ₐᵇ ‖φ‖² + ‖ι φ(a)‖² / 2 ≤ ∫ₐᵇ (A(t) φ φ - ⟪ι φ', ι φ⟫)`. -/
private theorem mul_setIntegral_norm_sq_add_le (ι : V →L[ℝ] H) (hab : a ≤ b)
    (hA : AEStronglyMeasurable A (volume.restrict (Ioo a b)))
    (hA_bound : ∀ᵐ t ∂volume.restrict (Ioo a b), ‖A t‖ ≤ Λ)
    (hA_coercive : ∀ᵐ t ∂volume.restrict (Ioo a b), ∀ v, α * ‖v‖ ^ 2 ≤ A t v v) {φ : ℝ → V}
    (hφ : ContDiff ℝ 1 φ) (hφb : φ b = 0) :
    α * (∫ t in Ioo a b, ‖φ t‖ ^ 2) + ‖ι (φ a)‖ ^ 2 / 2 ≤
      ∫ t in Ioo a b, (A t (φ t) (φ t) - ⟪ι (deriv φ t), ι (φ t)⟫_ℝ) := by
  have hφ' : Continuous (deriv φ) := hφ.continuous_deriv le_rfl
  have hint : ∀ {g : ℝ → ℝ}, Continuous g → Integrable g (volume.restrict (Ioo a b)) :=
    fun hg => (hg.integrableOn_Icc (a := a) (b := b)).mono_set Ioo_subset_Icc_self
  have hcont₁ : Continuous fun t => α * ‖φ t‖ ^ 2 := continuous_const.mul (hφ.continuous.norm.pow 2)
  have hcont₂ : Continuous fun t => ⟪ι (deriv φ t), ι (φ t)⟫_ℝ :=
    (ι.continuous.comp hφ').inner (ι.continuous.comp hφ.continuous)
  -- The fundamental theorem of calculus for `‖ι φ‖²`, with `φ(b) = 0`.
  have hftc : ∫ t in Ioo a b, ⟪ι (deriv φ t), ι (φ t)⟫_ℝ = -(‖ι (φ a)‖ ^ 2 / 2) := by
    have hderiv : ∀ t, HasDerivAt (fun s => ‖ι (φ s)‖ ^ 2)
        (2 * ⟪ι (deriv φ t), ι (φ t)⟫_ℝ) t := fun t => by
      rw [real_inner_comm]
      exact (ι.hasFDerivAt.comp_hasDerivAt t
        ((hφ.differentiable one_ne_zero t).hasDerivAt)).norm_sq
    have h := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := a) (b := b)
      (fun t _ => hderiv t) ((continuous_const.mul hcont₂).intervalIntegrable a b)
    rw [hφb, map_zero, norm_zero, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_of_le hab, integral_Ioc_eq_integral_Ioo] at h
    linarith
  -- `t ↦ A(t) φ(t) φ(t)` is bounded and strongly measurable, hence integrable.
  have hAφφ : Integrable (fun t => A t (φ t) (φ t)) (volume.restrict (Ioo a b)) := by
    obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn (hφ.continuous.continuousOn
      (s := Icc a b))
    have hmeas : AEStronglyMeasurable (fun t => A t (φ t) (φ t)) (volume.restrict (Ioo a b)) :=
      isBoundedBilinearMap_apply.continuous.comp_aestronglyMeasurable
        ((isBoundedBilinearMap_apply.continuous.comp_aestronglyMeasurable
          (hA.prodMk hφ.continuous.aestronglyMeasurable)).prodMk
            hφ.continuous.aestronglyMeasurable)
    refine (MemLp.of_bound hmeas (Λ * C * C) ?_).integrable le_rfl
    filter_upwards [hA_bound, ae_restrict_mem measurableSet_Ioo] with t hAt ht
    have hΛ : 0 ≤ Λ := (norm_nonneg (A t)).trans hAt
    have hφt := hC t (Ioo_subset_Icc_self ht)
    have hC0 : 0 ≤ C := (norm_nonneg _).trans hφt
    calc ‖A t (φ t) (φ t)‖ ≤ ‖A t‖ * ‖φ t‖ * ‖φ t‖ := (A t).le_opNorm₂ _ _
      _ ≤ Λ * C * C := by gcongr
  calc α * (∫ t in Ioo a b, ‖φ t‖ ^ 2) + ‖ι (φ a)‖ ^ 2 / 2
      = ∫ t in Ioo a b, (α * ‖φ t‖ ^ 2 - ⟪ι (deriv φ t), ι (φ t)⟫_ℝ) := by
        rw [integral_sub (hint hcont₁) (hint hcont₂), integral_const_mul, hftc]
        ring
    _ ≤ ∫ t in Ioo a b, (A t (φ t) (φ t) - ⟪ι (deriv φ t), ι (φ t)⟫_ℝ) := by
        refine integral_mono_ae (hint (hcont₁.sub hcont₂)) (hAφφ.sub (hint hcont₂)) ?_
        filter_upwards [hA_coercive] with t ht
        linarith [ht (φ t)]

/-- The variational formulation of `u' + A(t) u = f`, `u(a) = u₀`, has a solution when `A(t)` is
coercive. This is the case `β = 0` of `TauCeti.exists_memLp_forall_setIntegral_eq_add_inner`,
to which the general case is reduced by an exponential change of the unknown. -/
private theorem exists_memLp_forall_setIntegral_eq_add_inner_of_coercive [CompleteSpace V]
    (ι : V →L[ℝ] H) (hab : a ≤ b)
    (hA : AEStronglyMeasurable A (volume.restrict (Ioo a b)))
    (hA_bound : ∀ᵐ t ∂volume.restrict (Ioo a b), ‖A t‖ ≤ Λ) (hα : 0 < α)
    (hA_coercive : ∀ᵐ t ∂volume.restrict (Ioo a b), ∀ v, α * ‖v‖ ^ 2 ≤ A t v v)
    (hf : MemLp f 2 (volume.restrict (Ioo a b))) (u₀ : H) :
    ∃ u : ℝ → V, MemLp u 2 (volume.restrict (Ioo a b)) ∧
      ∀ φ : ℝ → V, ContDiff ℝ 1 φ → φ b = 0 →
        ∫ t in Ioo a b, (A t (u t) (φ t) - ⟪ι (u t), ι (deriv φ t)⟫_ℝ) =
          (∫ t in Ioo a b, f t (φ t)) + ⟪u₀, ι (φ a)⟫_ℝ := by
  set μ := volume.restrict (Ioo a b)
  set R := (InnerProductSpace.toDual ℝ V).symm
  have hR : ∀ (g : StrongDual ℝ V) (v : V), ⟪R g, v⟫_ℝ = g v := fun g v =>
    InnerProductSpace.toDual_symm_apply
  -- The test space: `C¹` functions vanishing at the final time.
  let Φ : Submodule ℝ (ℝ → V) :=
    { carrier := {φ | ContDiff ℝ 1 φ ∧ φ b = 0}
      add_mem' := fun hφ hψ => ⟨hφ.1.add hψ.1, by simp [hφ.2, hψ.2]⟩
      zero_mem' := ⟨contDiff_const, rfl⟩
      smul_mem' := fun c _ hφ => ⟨hφ.1.const_smul c, by simp [hφ.2]⟩ }
  have hΦ : ∀ φ : Φ, ContDiff ℝ 1 (φ : ℝ → V) ∧ (φ : ℝ → V) b = 0 := fun φ => φ.2
  have hdiff : ∀ (φ : Φ) t, DifferentiableAt ℝ (φ : ℝ → V) t := fun φ t =>
    (hΦ φ).1.differentiable one_ne_zero t
  -- The test functions as elements of `L²(a, b; V)`.
  have hφ_mem : ∀ φ : Φ, MemLp (φ : ℝ → V) 2 μ := fun φ => by
    obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn
      ((hΦ φ).1.continuous.continuousOn (s := Icc a b))
    exact MemLp.of_bound (hΦ φ).1.continuous.aestronglyMeasurable C
      ((ae_restrict_mem measurableSet_Ioo).mono fun t ht => hC t (Ioo_subset_Icc_self ht))
  let j : Φ →ₗ[ℝ] Lp V 2 μ :=
    { toFun := fun φ => (hφ_mem φ).toLp φ
      map_add' := fun φ ψ => MemLp.toLp_add (hφ_mem φ) (hφ_mem ψ)
      map_smul' := fun c φ => MemLp.toLp_const_smul c (hφ_mem φ) }
  have hj : ∀ φ : Φ, (j φ : ℝ → V) =ᵐ[μ] φ := fun φ => (hφ_mem φ).coeFn_toLp
  -- The form `E(φ, u) = ⟪k φ, u⟫_{L²}`, where `k φ` represents `A(·)ᵀ φ - ι* ι φ'`.
  let k : (ℝ → V) → ℝ → V := fun φ t =>
    R ((A t).flip (φ t) - ι.gelfandDual (ι (deriv φ t)))
  have hk_inner : ∀ φ t v, ⟪k φ t, v⟫_ℝ = A t v (φ t) - ⟪ι (deriv φ t), ι v⟫_ℝ := by
    intro φ t v
    simp only [k, hR, sub_apply, ContinuousLinearMap.flip_apply,
      ContinuousLinearMap.gelfandDual_apply]
  have hk_mem : ∀ φ : Φ, MemLp (k φ) 2 μ := fun φ =>
    memLp_toDual_symm_flip_sub ι hA hA_bound (hΦ φ).1
  let G : Φ →ₗ[ℝ] Lp V 2 μ :=
    { toFun := fun φ => (hk_mem φ).toLp (k φ)
      map_add' := fun φ ψ => by
        rw [← MemLp.toLp_add]
        refine MemLp.toLp_congr _ _ (Filter.Eventually.of_forall fun t => ?_)
        simp only [k, Submodule.coe_add, Pi.add_apply, deriv_add (hdiff φ t) (hdiff ψ t),
          map_add]
        rw [← map_add R]
        congr 1
        abel
      map_smul' := fun c φ => by
        rw [RingHom.id_apply, ← MemLp.toLp_const_smul]
        refine MemLp.toLp_congr _ _ (Filter.Eventually.of_forall fun t => ?_)
        simp only [k, Submodule.coe_smul, Pi.smul_apply, deriv_const_smul c (hdiff φ t),
          map_smul]
        rw [← smul_sub, map_smulₛₗ, RCLike.conj_to_real] }
  let E : Φ →ₗ[ℝ] StrongDual ℝ (Lp V 2 μ) :=
    { toFun := fun φ => innerSL ℝ (G φ)
      map_add' := fun φ ψ => by rw [map_add, map_add]
      map_smul' := fun c φ => by
        rw [map_smul, map_smulₛₗ, RingHom.id_apply, RCLike.conj_to_real] }
  have hG : ∀ φ : Φ, G φ = (hk_mem φ).toLp (k φ) := fun _ => rfl
  have hE_inner : ∀ (φ : Φ) (v : Lp V 2 μ), E φ v = ⟪G φ, v⟫_ℝ := fun _ _ =>
    innerSL_apply_apply ℝ _ _
  have hE : ∀ (φ : Φ) (v : Lp V 2 μ),
      E φ v = ∫ t in Ioo a b,
        (A t (v t) ((φ : ℝ → V) t) - ⟪ι (deriv (φ : ℝ → V) t), ι (v t)⟫_ℝ) := by
    intro φ v
    rw [hE_inner, L2.inner_def, hG]
    refine integral_congr_ae ?_
    filter_upwards [(hk_mem φ).coeFn_toLp] with t ht
    rw [ht, hk_inner]
  -- The right-hand side `ℓ(φ) = ⟪R f, φ⟫_{L²} + ⟪u₀, ι φ(a)⟫`.
  have hRf : MemLp (fun t => R (f t)) 2 μ :=
    hf.of_le (R.continuous.comp_aestronglyMeasurable hf.aestronglyMeasurable)
      (Filter.Eventually.of_forall fun t => by simp [R])
  set F : Lp V 2 μ := hRf.toLp (fun t => R (f t))
  let ℓ : Φ →ₗ[ℝ] ℝ :=
    { toFun := fun φ => ⟪F, j φ⟫_ℝ + ⟪u₀, ι ((φ : ℝ → V) a)⟫_ℝ
      map_add' := fun φ ψ => by
        simp only [map_add, inner_add_right, Submodule.coe_add, Pi.add_apply]
        ring
      map_smul' := fun c φ => by
        simp only [map_smul, inner_smul_right, Submodule.coe_smul, Pi.smul_apply,
          RingHom.id_apply, smul_eq_mul]
        ring }
  have hℓ_def : ∀ φ : Φ, ℓ φ = ⟪F, j φ⟫_ℝ + ⟪u₀, ι ((φ : ℝ → V) a)⟫_ℝ := fun _ => rfl
  have hℓ_apply : ∀ φ : Φ,
      ℓ φ = (∫ t in Ioo a b, f t ((φ : ℝ → V) t)) + ⟪u₀, ι ((φ : ℝ → V) a)⟫_ℝ := by
    intro φ
    rw [hℓ_def, L2.inner_def]
    congr 1
    refine integral_congr_ae ?_
    filter_upwards [hRf.coeFn_toLp, hj φ] with t hFt hjt
    rw [hFt, hjt, hR]
  -- `p(φ) = (‖φ‖²_{L²(V)} + ‖ι φ(a)‖²)^{1/2}` controls `j φ` and `ι φ(a)`.
  let p : Φ → ℝ := fun φ => √(‖j φ‖ ^ 2 + ‖ι ((φ : ℝ → V) a)‖ ^ 2)
  have hp_sq : ∀ φ : Φ, p φ ^ 2 = ‖j φ‖ ^ 2 + ‖ι ((φ : ℝ → V) a)‖ ^ 2 := fun φ =>
    Real.sq_sqrt (by positivity)
  have hjp : ∀ φ : Φ, ‖j φ‖ ≤ p φ := fun φ =>
    Real.le_sqrt_of_sq_le (by nlinarith [sq_nonneg ‖ι ((φ : ℝ → V) a)‖])
  have hιp : ∀ φ : Φ, ‖ι ((φ : ℝ → V) a)‖ ≤ p φ := fun φ =>
    Real.le_sqrt_of_sq_le (by nlinarith [sq_nonneg ‖j φ‖])
  -- Coercivity of `E` with respect to `p`, from the energy inequality.
  have hcoer : ∀ φ : Φ, min α (1 / 2) * p φ ^ 2 ≤ E φ (j φ) := by
    intro φ
    have hnorm : ∫ t in Ioo a b, ‖(φ : ℝ → V) t‖ ^ 2 = ‖j φ‖ ^ 2 := by
      rw [← real_inner_self_eq_norm_sq, L2.inner_def]
      refine integral_congr_ae ?_
      filter_upwards [hj φ] with t ht
      rw [ht, real_inner_self_eq_norm_sq]
    have hdiag : E φ (j φ) = ∫ t in Ioo a b, (A t ((φ : ℝ → V) t) ((φ : ℝ → V) t)
        - ⟪ι (deriv (φ : ℝ → V) t), ι ((φ : ℝ → V) t)⟫_ℝ) := by
      rw [hE]
      refine integral_congr_ae ?_
      filter_upwards [hj φ] with t ht
      rw [ht]
    have hlow := mul_setIntegral_norm_sq_add_le ι hab hA hA_bound hA_coercive (hΦ φ).1 (hΦ φ).2
    rw [hnorm, ← hdiag] at hlow
    have hmin₁ : min α (1 / 2) ≤ α := min_le_left _ _
    have hmin₂ : min α (1 / 2) ≤ 1 / 2 := min_le_right _ _
    rw [hp_sq]
    nlinarith [sq_nonneg ‖j φ‖, sq_nonneg ‖ι ((φ : ℝ → V) a)‖]
  -- The right-hand side is bounded by `p`.
  have hbound : ∀ φ : Φ, |ℓ φ| ≤ (‖F‖ + ‖u₀‖) * p φ := by
    intro φ
    calc |ℓ φ| = |⟪F, j φ⟫_ℝ + ⟪u₀, ι ((φ : ℝ → V) a)⟫_ℝ| := by rw [hℓ_def]
      _ ≤ ‖F‖ * ‖j φ‖ + ‖u₀‖ * ‖ι ((φ : ℝ → V) a)‖ :=
          (abs_add_le _ _).trans
            (add_le_add (abs_real_inner_le_norm _ _) (abs_real_inner_le_norm _ _))
      _ ≤ ‖F‖ * p φ + ‖u₀‖ * p φ := by gcongr <;> [exact hjp φ; exact hιp φ]
      _ = (‖F‖ + ‖u₀‖) * p φ := by ring
  -- Lions' theorem produces the solution.
  obtain ⟨u, hu, -⟩ := LinearMap.exists_forall_apply_eq_and_norm_le_of_coercive E (fun φ => j φ)
    p ℓ (lt_min hα one_half_pos) (by positivity) hcoer hjp hbound
  refine ⟨u, Lp.memLp u, fun φ hφ hφb => ?_⟩
  have h := hu ⟨φ, hφ, hφb⟩
  rw [hE, hℓ_apply] at h
  simpa only [real_inner_comm (ι (deriv φ _))] using h

/-- **Existence for linear parabolic equations, in variational form.** Let `ι : V →L[ℝ] H`
define a Gelfand triple with `V` a Hilbert space, and let `A(t) : V →L[ℝ] V*` be strongly
measurable in `t`, bounded by `Λ` and satisfy **Gårding's inequality**
`α ‖v‖² - β ‖ι v‖² ≤ A(t) v v` with `α > 0`, for almost every `t ∈ (a, b)`. Then for every
`f ∈ L²(a, b; V*)` and `u₀ ∈ H` there is `u ∈ L²(a, b; V)` with

`∫ₐᵇ (A(t) u(t) φ(t) - ⟪ι u(t), ι φ'(t)⟫) dt = ∫ₐᵇ f(t) φ(t) dt + ⟪u₀, ι φ(a)⟫`

for every `C¹` function `φ : ℝ → V` with `φ(b) = 0`. This is the weak formulation of
`u' + A(t) u = f` with initial value `u(a) = u₀`, obtained by integrating `⟪u', φ⟫` by parts.
No sign is imposed on `β`. -/
theorem exists_memLp_forall_setIntegral_eq_add_inner [CompleteSpace V] {ι : V →L[ℝ] H}
    (hab : a ≤ b)
    (hA : AEStronglyMeasurable A (volume.restrict (Ioo a b)))
    (hA_bound : ∀ᵐ t ∂volume.restrict (Ioo a b), ‖A t‖ ≤ Λ) (hα : 0 < α)
    (hA_garding : ∀ᵐ t ∂volume.restrict (Ioo a b), ∀ v, α * ‖v‖ ^ 2 - β * ‖ι v‖ ^ 2 ≤ A t v v)
    (hf : MemLp f 2 (volume.restrict (Ioo a b))) (u₀ : H) :
    ∃ u : ℝ → V, MemLp u 2 (volume.restrict (Ioo a b)) ∧
      ∀ φ : ℝ → V, ContDiff ℝ 1 φ → φ b = 0 →
        ∫ t in Ioo a b, (A t (u t) (φ t) - ⟪ι (u t), ι (deriv φ t)⟫_ℝ) =
          (∫ t in Ioo a b, f t (φ t)) + ⟪u₀, ι (φ a)⟫_ℝ := by
  -- Writing `u = e w` with `e(t) = exp (β (t - a))`, the unknown `w` solves the problem for the
  -- coercive operator `A + β ι* ι` with right-hand side `e⁻¹ f`.
  set e : ℝ → ℝ := fun t => Real.exp (β * (t - a)) with he
  set C : ℝ := Real.exp (|β| * (b - a))
  have he_pos : ∀ t, 0 < e t := fun t => Real.exp_pos _
  have he_cont : Continuous e :=
    Real.continuous_exp.comp (continuous_const.mul (continuous_id.sub continuous_const))
  have he_deriv : ∀ t, HasDerivAt e (β * e t) t := fun t => by
    simpa [he, mul_comm] using (((hasDerivAt_id t).sub_const a).const_mul β).exp
  have he_le : ∀ t ∈ Ioo a b, e t ≤ C ∧ (e t)⁻¹ ≤ C := by
    intro t ht
    have h₁ : |β * (t - a)| ≤ |β| * (b - a) := by
      rw [abs_mul, abs_of_pos (sub_pos.2 ht.1)]
      exact mul_le_mul_of_nonneg_left (by linarith [ht.2]) (abs_nonneg β)
    refine ⟨Real.exp_le_exp.2 ((le_abs_self _).trans h₁), ?_⟩
    rw [he, ← Real.exp_neg]
    exact Real.exp_le_exp.2 ((neg_le_abs _).trans h₁)
  have hC : 0 ≤ C := (Real.exp_pos _).le
  set B : V →L[ℝ] StrongDual ℝ V := ι.gelfandDual.comp ι
  have hB : ∀ v w, B v w = ⟪ι v, ι w⟫_ℝ := fun v w => ι.gelfandDual_apply _ _
  have hshift_bound : ∀ᵐ t ∂volume.restrict (Ioo a b), ‖A t + β • B‖ ≤ Λ + |β| * ‖B‖ := by
    filter_upwards [hA_bound] with t ht
    exact (ContinuousLinearMap.opNorm_add_le _ _).trans
      (add_le_add ht ((ContinuousLinearMap.opNorm_smul_le β B).trans_eq
        (by rw [Real.norm_eq_abs])))
  have hshift_coercive : ∀ᵐ t ∂volume.restrict (Ioo a b), ∀ v,
      α * ‖v‖ ^ 2 ≤ (A t + β • B) v v := by
    filter_upwards [hA_garding] with t ht v
    simp only [add_apply, smul_apply, hB, real_inner_self_eq_norm_sq, smul_eq_mul]
    linarith [ht v]
  have hf' : MemLp (fun t => (e t)⁻¹ • f t) 2 (volume.restrict (Ioo a b)) := by
    refine (hf.const_smul C).of_le ((he_cont.inv₀ fun t => (he_pos t).ne').aestronglyMeasurable.smul
      hf.aestronglyMeasurable) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    rw [Pi.smul_apply, norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_pos (inv_pos.2 (he_pos t)), abs_of_nonneg hC]
    exact mul_le_mul_of_nonneg_right (he_le t ht).2 (norm_nonneg _)
  obtain ⟨w, hw, hweq⟩ := exists_memLp_forall_setIntegral_eq_add_inner_of_coercive
    (A := fun t => A t + β • B) ι hab
    ((IsometryEquiv.addRight (β • B)).continuous.comp_aestronglyMeasurable hA) hshift_bound hα
    hshift_coercive hf' u₀
  refine ⟨fun t => e t • w t, ?_, fun φ hφ hφb => ?_⟩
  · refine (hw.const_smul C).of_le (he_cont.aestronglyMeasurable.smul hw.aestronglyMeasurable) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    rw [Pi.smul_apply, norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_pos (he_pos t), abs_of_nonneg hC]
    exact mul_le_mul_of_nonneg_right (he_le t ht).1 (norm_nonneg _)
  -- Test the equation for `w` against `e φ`.
  have hψ : ContDiff ℝ 1 (fun t => e t • φ t) :=
    (Real.contDiff_exp.comp (contDiff_const.mul (contDiff_id.sub contDiff_const))).smul hφ
  have hψ_deriv : ∀ t, deriv (fun s => e s • φ s) t = (β * e t) • φ t + e t • deriv φ t :=
    fun t => ((he_deriv t).smul ((hφ.differentiable one_ne_zero t).hasDerivAt)).deriv.trans
      (add_comm _ _)
  have h := hweq (fun t => e t • φ t) hψ (by simp [hφb])
  have hea : e a = 1 := by simp [he]
  simp only [hea, one_smul] at h
  -- Pointwise, the two weak formulations have the same integrands.
  have hlhs : ∀ t, A t (e t • w t) (φ t) - ⟪ι (e t • w t), ι (deriv φ t)⟫_ℝ =
      (A t + β • B) (w t) (e t • φ t) - ⟪ι (w t), ι (deriv (fun s => e s • φ s) t)⟫_ℝ := by
    intro t
    simp only [hψ_deriv, map_add, map_smul, add_apply, smul_apply, hB, inner_add_right,
      inner_smul_left, inner_smul_right, smul_eq_mul, RCLike.conj_to_real]
    ring
  have hrhs : ∀ t, f t (φ t) = ((e t)⁻¹ • f t) (e t • φ t) := by
    intro t
    simp only [map_smul, smul_apply, smul_eq_mul]
    field_simp [(he_pos t).ne']
  simp only [hlhs, hrhs]
  exact h

end TauCeti
