/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
public import Mathlib.Analysis.CStarAlgebra.Hom
public import Mathlib.MeasureTheory.Group.Measure
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
public import Mathlib.MeasureTheory.Integral.CompactlySupported
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Vector-valued integration along Hilbert-space representations

Let `π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)` be a (possibly degenerate) Hilbert-space `⋆`-representation of a
possibly nonunital C⋆-algebra `A`. Because `π` is automatically norm-continuous and contractive,
vector evaluation `a ↦ π a w` commutes with Bochner integration
(`NonUnitalStarAlgHom.integral_apply_apply`).

Given a topological measurable space `X` with `[OpensMeasurableSpace X]`, a measure `μ` finite on
compacts, and a strongly continuous uniformly bounded operator family `U : X → H →L[ℂ] H`, every
compactly supported continuous function `f : C_c(X, A)` integrates pointwise in `H` to a bounded
linear operator

`π.integratedOperator U hU hbdd μ f v = ∫ x, π (f x) (U x v) ∂μ`,

with `‖π.integratedOperator U hU hbdd μ f‖ ≤ C * ∫ x, ‖f x‖ ∂μ` whenever `‖U x‖ ≤ C` for all `x`.
Integrating in `H` rather than `H →L[ℂ] H` requires only strong continuity of `U` and needs no
group structure on `X`, no covariance or multiplicativity of `U`, and no separability, second
countability, or σ-finiteness. On a topological group with a left-invariant measure finite on
compacts, compact-support Fubini and left-translation invariance turn a convolution-type integral
`h s = ∫ r, F r (r⁻¹ * s) ∂μ` satisfying `π (f r) * U r * (π (g t) * U t) = π (F r t) * U (r * t)`
into the operator product of the integrated forms of `f` and `g`
(`NonUnitalStarAlgHom.integratedOperator_eq_mul`), still without σ-finiteness. Both untwisted
(`CovariantRepresentation.integratedOperator`) and cocycle-twisted
(`CentralCovariantPair.integratedOperator`) covariant integrated forms specialize this
construction.

## Main definitions and results

* `NonUnitalStarAlgHom.integral_apply_apply`: `∫ x, π (F x) w ∂ν = π (∫ x, F x ∂ν) w` for
  integrable `F : X → A`.
* `NonUnitalStarAlgHom.integratedOperator`: the vector-valued integrated form
  `C_c(X, A) →ₗ[ℂ] (H →L[ℂ] H)` of `π` and a strongly continuous bounded family `U : X → H →L[ℂ] H`.
* `NonUnitalStarAlgHom.norm_integratedOperator_le`: operator-norm bound by `C * ∫ x, ‖f x‖ ∂μ`.
* `NonUnitalStarAlgHom.inner_integratedOperator_apply`,
  `NonUnitalStarAlgHom.integratedOperator_smul`, and
  `NonUnitalStarAlgHom.integratedOperator_apply_apply`: matrix-coefficient, left-multiplier, and
  right-covariance formulas.
* `NonUnitalStarAlgHom.integratedOperator_eq_mul`: multiplicativity for convolution-type integrals
  against a left-invariant measure.

## References

* Dana Williams, *Crossed Products of C*-Algebras*, Chapter 2.
-/

public section

noncomputable section

open MeasureTheory
open scoped CompactlySupported InnerProductSpace CStarAlgebra

namespace NonUnitalStarAlgHom

section Bochner

variable {X A H : Type*} [MeasurableSpace X] [NonUnitalCStarAlgebra A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Vector evaluation of a Hilbert-space `⋆`-representation commutes with Bochner integration. -/
theorem integral_apply_apply (π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)) {ν : Measure X} {F : X → A}
    (hF : Integrable F ν) (w : H) :
    ∫ x, π (F x) w ∂ν = π (∫ x, F x ∂ν) w := by
  let L : A →L[ℂ] H := (ContinuousLinearMap.apply ℂ H w).comp
    { toLinearMap := (π : A →ₗ[ℂ] (H →L[ℂ] H)), cont := map_continuous π }
  have hL (a : A) : L a = π a w := rfl
  simpa only [hL] using L.integral_comp_comm hF

end Bochner

section Integrated

variable {X A H : Type*} [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
  [NonUnitalCStarAlgebra A] [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)) {U : X → H →L[ℂ] H}

omit [MeasurableSpace X] [OpensMeasurableSpace X] in
/-- For a strongly continuous operator family `U : X → H →L[ℂ] H` and `f : C_c(X, A)`, the vector
integrand `x ↦ π (f x) (U x v)` is continuous. -/
@[fun_prop]
theorem continuous_integrand (hU : ∀ v : H, Continuous fun x => U x v) (f : C_c(X, A)) (v : H) :
    Continuous fun x => π (f x) (U x v) :=
  (map_continuous π |>.comp f.continuous).clm_apply (hU v)

omit [MeasurableSpace X] [OpensMeasurableSpace X] in
/-- The vector integrand `x ↦ π (f x) (U x v)` vanishes outside the support of `f`, hence has
compact support. -/
theorem hasCompactSupport_integrand (U : X → H →L[ℂ] H) (f : C_c(X, A)) (v : H) :
    HasCompactSupport fun x => π (f x) (U x v) :=
  f.hasCompactSupport.mono fun _ hf hzero => hf (by simp [hzero])

/-- Against any measure finite on compact sets, the vector integrand `x ↦ π (f x) (U x v)` of a
strongly continuous operator family is integrable. -/
theorem integrable_integrand (hU : ∀ v : H, Continuous fun x => U x v) (μ : Measure X)
    [IsFiniteMeasureOnCompacts μ] (f : C_c(X, A)) (v : H) :
    Integrable (fun x => π (f x) (U x v)) μ :=
  (π.continuous_integrand hU f v).integrable_of_hasCompactSupport
    (π.hasCompactSupport_integrand U f v)

private theorem norm_integral_le {C : ℝ} (hC : ∀ x, ‖U x‖ ≤ C) (μ : Measure X)
    [IsFiniteMeasureOnCompacts μ] (f : C_c(X, A)) (v : H) :
    ‖∫ x, π (f x) (U x v) ∂μ‖ ≤ max C 0 * (∫ x, ‖f x‖ ∂μ) * ‖v‖ := by
  calc ‖∫ x, π (f x) (U x v) ∂μ‖
      ≤ ∫ x, ‖f x‖ * (max C 0 * ‖v‖) ∂μ := by
        refine norm_integral_le_of_norm_le (f.integrable.norm.mul_const _) (.of_forall fun x => ?_)
        calc ‖π (f x) (U x v)‖
            ≤ ‖π (f x)‖ * ‖U x v‖ := (π (f x)).le_opNorm _
          _ ≤ ‖f x‖ * (max C 0 * ‖v‖) :=
            mul_le_mul (NonUnitalStarAlgHom.norm_apply_le π _)
              ((U x).le_of_opNorm_le ((hC x).trans (le_max_left C 0)) v)
              (norm_nonneg _) (norm_nonneg _)
    _ = max C 0 * (∫ x, ‖f x‖ ∂μ) * ‖v‖ := by rw [integral_mul_const]; ring

variable (U) in
/-- Vector-valued integrated form `v ↦ ∫ x, π (f x) (U x v) ∂μ` on `C_c(X, A)` for a
`⋆`-representation `π` and a strongly continuous uniformly bounded operator family
`U : X → H →L[ℂ] H`. -/
def integratedOperator (hU : ∀ v : H, Continuous fun x => U x v) (hbdd : ∃ C, ∀ x, ‖U x‖ ≤ C)
    (μ : Measure X) [IsFiniteMeasureOnCompacts μ] : C_c(X, A) →ₗ[ℂ] (H →L[ℂ] H) where
  toFun f := LinearMap.mkContinuous
    { toFun v := ∫ x, π (f x) (U x v) ∂μ
      map_add' v w := by
        simp_rw [map_add]
        exact integral_add (π.integrable_integrand hU μ f v) (π.integrable_integrand hU μ f w)
      map_smul' c v := by
        simp_rw [map_smul]
        exact integral_smul c _ }
    (max hbdd.choose 0 * ∫ x, ‖f x‖ ∂μ) (π.norm_integral_le hbdd.choose_spec μ f)
  map_add' f g := by
    ext v
    simp only [LinearMap.mkContinuous_apply, CompactlySupportedContinuousMap.add_apply, map_add,
      add_apply]
    exact integral_add (π.integrable_integrand hU μ f v) (π.integrable_integrand hU μ g v)
  map_smul' c f := by
    ext v
    simp only [LinearMap.mkContinuous_apply, CompactlySupportedContinuousMap.smul_apply, map_smul,
      smul_apply, RingHom.id_apply]
    exact integral_smul c _

variable {π}

/-- Defining vector formula for `NonUnitalStarAlgHom.integratedOperator`. -/
theorem integratedOperator_apply (hU : ∀ v : H, Continuous fun x => U x v)
    (hbdd : ∃ C, ∀ x, ‖U x‖ ≤ C) (μ : Measure X) [IsFiniteMeasureOnCompacts μ]
    (f : C_c(X, A)) (v : H) :
    π.integratedOperator U hU hbdd μ f v = ∫ x, π (f x) (U x v) ∂μ :=
  (rfl)

/-- If `‖U x‖ ≤ C` for every `x`, then `‖π.integratedOperator U hU hbdd μ f‖ ≤ C * ∫ x, ‖f x‖ ∂μ`.
-/
theorem norm_integratedOperator_le (hU : ∀ v : H, Continuous fun x => U x v)
    (hbdd : ∃ C, ∀ x, ‖U x‖ ≤ C) (μ : Measure X) [IsFiniteMeasureOnCompacts μ]
    {C : ℝ} (hC : ∀ x, ‖U x‖ ≤ C) (f : C_c(X, A)) :
    ‖π.integratedOperator U hU hbdd μ f‖ ≤ C * ∫ x, ‖f x‖ ∂μ := by
  by_cases hX : Nonempty X
  · obtain ⟨x₀⟩ := hX
    have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC x₀)
    refine ContinuousLinearMap.opNorm_le_bound _
      (mul_nonneg hC0 (integral_nonneg fun _ => norm_nonneg _)) fun v => ?_
    simpa [max_eq_left hC0, integratedOperator_apply] using π.norm_integral_le hC μ f v
  · have : IsEmpty X := not_nonempty_iff.1 hX
    refine ContinuousLinearMap.opNorm_le_bound _ (by simp [integral_of_isEmpty]) fun v => ?_
    simp [integratedOperator_apply, integral_of_isEmpty]

/-- Matrix coefficients of `π.integratedOperator` are integrals of pointwise matrix coefficients. -/
theorem inner_integratedOperator_apply (hU : ∀ v : H, Continuous fun x => U x v)
    (hbdd : ∃ C, ∀ x, ‖U x‖ ≤ C) (μ : Measure X) [IsFiniteMeasureOnCompacts μ]
    (f : C_c(X, A)) (w v : H) :
    ⟪w, π.integratedOperator U hU hbdd μ f v⟫_ℂ = ∫ x, ⟪w, π (f x) (U x v)⟫_ℂ ∂μ := by
  rw [integratedOperator_apply]
  simpa using ((innerSL ℂ w).integral_comp_comm (π.integrable_integrand hU μ f v)).symm

/-- Left multiplication of `f` by `a : A` becomes left multiplication by `π a`. -/
@[simp]
theorem integratedOperator_smul (hU : ∀ v : H, Continuous fun x => U x v)
    (hbdd : ∃ C, ∀ x, ‖U x‖ ≤ C) (μ : Measure X) [IsFiniteMeasureOnCompacts μ]
    (a : A) (f : C_c(X, A)) :
    π.integratedOperator U hU hbdd μ (a • f) = π a * π.integratedOperator U hU hbdd μ f := by
  ext v
  simp only [integratedOperator_apply, CompactlySupportedContinuousMap.smul_apply, smul_eq_mul,
    map_mul, mul_apply_eq_comp]
  exact (π a).integral_comp_comm (π.integrable_integrand hU μ f v)

/-- Whenever `U x (π a v) = π (b x) (U x v)` for all `x`, applying `π.integratedOperator` to
`π a v` moves `b x` inside the coefficient product. -/
theorem integratedOperator_apply_apply (hU : ∀ v : H, Continuous fun x => U x v)
    (hbdd : ∃ C, ∀ x, ‖U x‖ ≤ C) (μ : Measure X) [IsFiniteMeasureOnCompacts μ]
    {b : X → A} {a : A} {v : H} (hcov : ∀ x, U x (π a v) = π (b x) (U x v)) (f : C_c(X, A)) :
    π.integratedOperator U hU hbdd μ f (π a v) = ∫ x, π (f x * b x) (U x v) ∂μ := by
  simp_rw [integratedOperator_apply, hcov, map_mul, mul_apply_eq_comp]

end Integrated

section Group

variable {G A H : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [MeasurableSpace G] [OpensMeasurableSpace G] [MeasurableMul G]
  [NonUnitalCStarAlgebra A] [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)} {U : G → H →L[ℂ] H}

/-- On a topological group with a left-invariant measure finite on compacts, if `h : C_c(G, A)` is
given pointwise by `h s = ∫ r, F r (r⁻¹ * s) ∂μ` for a jointly continuous compactly supported
kernel `F : G → G → A` satisfying `π (f r) * U r * (π (g t) * U t) = π (F r t) * U (r * t)`, then
`π.integratedOperator U hU hbdd μ h` is the operator product of the integrated forms of `f` and `g`.
Compact-support Fubini exchanges the integrals without assuming σ-finiteness. -/
theorem integratedOperator_eq_mul (hU : ∀ v : H, Continuous fun g => U g v)
    (hbdd : ∃ C, ∀ g, ‖U g‖ ≤ C) (μ : Measure G) [IsFiniteMeasureOnCompacts μ]
    [μ.IsMulLeftInvariant] {f g h : C_c(G, A)} {F : G → G → A}
    (hF_cont : Continuous (Function.uncurry F))
    (hF_supp : HasCompactSupport (Function.uncurry F))
    (hh : ∀ s, h s = ∫ r, F r (r⁻¹ * s) ∂μ)
    (hmul : ∀ r t, π (f r) * U r * (π (g t) * U t) = π (F r t) * U (r * t)) :
    π.integratedOperator U hU hbdd μ h =
      π.integratedOperator U hU hbdd μ f * π.integratedOperator U hU hbdd μ g := by
  ext v
  have hF_int (s : G) : Integrable (fun r => F r (r⁻¹ * s)) μ :=
    (hF_cont.comp (continuous_id.prodMk
      (continuous_inv.mul continuous_const))).integrable_of_hasCompactSupport
      ((hF_supp.image continuous_fst).closure_of_subset fun r hr =>
        ⟨(r, r⁻¹ * s), subset_tsupport _ hr, rfl⟩)
  -- The integrand on `G × G` obtained by expanding `h s` inside the Hilbert-space integral.
  set Ψ : G → G → H := fun s r => π (F r (r⁻¹ * s)) (U s v)
  have hcont : Continuous (Function.uncurry Ψ) :=
    ((map_continuous π).comp (hF_cont.comp
      (continuous_snd.prodMk (continuous_snd.inv.mul continuous_fst)))).clm_apply
      ((hU v).comp continuous_fst)
  have hsupp : HasCompactSupport (Function.uncurry Ψ) :=
    (hF_supp.image ((continuous_fst.mul continuous_snd).prodMk
      continuous_fst)).closure_of_subset fun p hp =>
        ⟨(p.2, p.2⁻¹ * p.1), subset_tsupport _ fun h0 => hp <| by
          simp only [Function.uncurry_apply_pair] at h0
          simp [Function.uncurry, Ψ, h0],
          Prod.ext (mul_inv_cancel_left p.2 p.1) rfl⟩
  calc π.integratedOperator U hU hbdd μ h v
      = ∫ s, ∫ r, Ψ s r ∂μ ∂μ := by
        rw [integratedOperator_apply]
        congr 1 with s
        rw [hh s, ← π.integral_apply_apply (hF_int s)]
    _ = ∫ r, ∫ s, Ψ s r ∂μ ∂μ := integral_integral_swap_of_hasCompactSupport hcont hsupp
    _ = ∫ r, (π (f r) * U r) (π.integratedOperator U hU hbdd μ g v) ∂μ := by
        congr 1 with r
        -- Substitute `s ↦ r * t`, then use `hmul` to pull `π (f r) * U r` out of the integral.
        rw [← integral_mul_left_eq_self (Ψ · r) r, integratedOperator_apply,
          ← ContinuousLinearMap.integral_comp_comm _ (π.integrable_integrand hU μ g v)]
        congr 1 with t
        simpa [Ψ, inv_mul_cancel_left, mul_apply_eq_comp] using congr($((hmul r t).symm) v)
    _ = (π.integratedOperator U hU hbdd μ f * π.integratedOperator U hU hbdd μ g) v := by
        simp [integratedOperator_apply]

end Group

end NonUnitalStarAlgHom
