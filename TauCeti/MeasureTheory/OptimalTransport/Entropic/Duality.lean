/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Data.Matrix.Scaling.Basic
public import TauCeti.InformationTheory.KullbackLeibler.Variational
public import TauCeti.MeasureTheory.OptimalTransport.Entropic.SchroedingerSystem

/-!
# Duality for entropic optimal transport

The entropically regularised transport problem `TauCeti.entropicTransportCost c ε μ ν` minimises
`∫ c dπ + ε * klDiv π (μ ⊗ ν)` over the couplings `π` of `μ` and `ν`. Its dual problem maximises,
over pairs of real potentials `φ` on `X` and `ψ` on `Y`, the value

`∫ φ dμ + ∫ ψ dν - ε * ∫ (exp ((φ(x) + ψ(y) - c(x, y)) / ε) - 1) d(μ ⊗ ν)`,

which is `TauCeti.entropicDualValue c ε μ ν φ ψ`. The Gibbs factor
`exp ((φ(x) + ψ(y) - c(x, y)) / ε)`, which is `TauCeti.entropicGibbsFactor c ε φ ψ`, is read with
`exp (-∞) = 0`, so it vanishes where the cost is infinite. Unlike the Kantorovich dual problem,
the dual problem has no constraint: the condition `φ(x) + ψ(y) ≤ c(x, y)` is replaced by an
exponential penalty.

Weak duality is the integrated Fenchel–Young inequality for relative entropy
(`TauCeti.ofReal_integral_sub_integral_indicator_exp_sub_one_le_klDiv`), applied to the coupling
`π` and the Gibbs exponent `(φ(x) + ψ(y) - c(x, y)) / ε`, which is finite `π`-almost everywhere
when `π` has finite cost. Its equality case says that a coupling of finite regularised cost and a
pair of potentials have the same value exactly when the Gibbs factor is the density of the
coupling against `μ ⊗ ν`, that is, when the potentials solve the Schrödinger system and the
coupling is the corresponding Gibbs plan. For a bounded cost,
`TauCeti.exists_isCoupling_lintegral_add_mul_klDiv_eq_entropicTransportCost` solves that system,
so the dual problem is attained with no duality gap, and its maximisers are unique up to one
additive constant.

## Main definitions

* `TauCeti.entropicGibbsFactor c ε φ ψ`: the Gibbs factor `exp ((φ(x) + ψ(y) - c(x, y)) / ε)`,
  read as `0` where the cost is infinite.
* `TauCeti.entropicGibbsKernel c ε`: the Gibbs kernel `exp (-c(x, y) / ε)`, read as `0` where
  the cost is infinite; every Gibbs factor is this kernel multiplied by the exponentials of the
  two potentials.
* `TauCeti.entropicDualValue c ε μ ν φ ψ`: the value of the dual problem at the potentials `φ`
  and `ψ`.

## Main statements

* `TauCeti.IsCoupling.ofReal_entropicDualValue_le_lintegral_add_mul_klDiv` and
  `TauCeti.ofReal_entropicDualValue_le_entropicTransportCost`: weak duality, for a finite source
  measure and an almost everywhere measurable cost.
* `TauCeti.IsCoupling.entropicDualValue_eq_toReal_lintegral_add_mul_klDiv_iff`: complementary
  slackness; a coupling of finite regularised cost and a pair of potentials have the same value
  exactly when the coupling has the Gibbs factor as density against `μ ⊗ ν`.
* `TauCeti.IsCoupling.exists_ae_eq_add_const_of_entropicDualValue_eq`: for a cost finite
  `μ ⊗ ν`-almost everywhere, two pairs of potentials whose values equal the regularised cost of a
  common coupling differ by one additive constant.
* `TauCeti.exists_entropicDualValue_eq_toReal_entropicTransportCost` and
  `TauCeti.isGreatest_entropicDualValue_integrable`: strong duality with dual attainment by bounded
  measurable potentials, for a bounded measurable cost and probability measures.
* `TauCeti.exists_ae_eq_add_const_of_entropicDualValue_eq_toReal_entropicTransportCost`: for a
  bounded measurable cost, the dual maximisers are unique up to one additive constant.

## Implementation notes

The cost is extended-nonnegative, as for `TauCeti.entropicTransportCost`. The Gibbs factor is the
indicator of the set `{z | c z ≠ ∞}` applied to `exp ((φ(x) + ψ(y) - (c z).toReal) / ε)`, which
is the extended-real value `exp ((φ(x) + ψ(y) - c(x, y)) / ε)` everywhere. Both integrals in the
dual value are Bochner integrals, so the theorems assume that the potentials are integrable and
that the Gibbs factor is integrable against `μ ⊗ ν`.

The uniqueness of the potentials needs the cost to be finite `μ ⊗ ν`-almost everywhere: where the
cost is infinite the Gibbs factor carries no information about the potentials.

## References

* M. Nutz, *Introduction to Entropic Optimal Transport*, lecture notes, Columbia University, 2021,
  for the dual problem of entropic optimal transport and its relation to the Schrödinger
  potentials.
* G. Peyré and M. Cuturi, *Computational Optimal Transport*, Found. Trends Mach. Learn. 11
  (2019), Chapter 4, for the dual of the regularised problem with reference `μ ⊗ ν`.
-/

public section

noncomputable section

open MeasureTheory InformationTheory
open scoped ENNReal NNReal

namespace TauCeti

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
  {c : X × Y → ℝ≥0∞} {ε : ℝ≥0} {π : Measure (X × Y)} {μ : Measure X} {ν : Measure Y}
  {φ φ' : X → ℝ} {ψ ψ' : Y → ℝ}

/-! ### The Gibbs factor -/

/-- The Gibbs factor `exp ((φ(x) + ψ(y) - c(x, y)) / ε)` of the potentials `φ` and `ψ`, read with
`exp (-∞) = 0`: it is `0` where the cost is infinite. A coupling and a pair of potentials close
the entropic duality gap exactly when the Gibbs factor is the density of the coupling against
`μ ⊗ ν`. -/
def entropicGibbsFactor (c : X × Y → ℝ≥0∞) (ε : ℝ≥0) (φ : X → ℝ) (ψ : Y → ℝ) : X × Y → ℝ :=
  {z | c z ≠ ∞}.indicator fun z ↦ Real.exp ((φ z.1 + ψ z.2 - (c z).toReal) / ε)

omit [MeasurableSpace X] [MeasurableSpace Y] in
/-- The Gibbs factor is the indicator of the finite-cost set applied to the real exponential. The
definition's body is not exposed, so this is the lemma downstream modules should rewrite with. -/
theorem entropicGibbsFactor_def :
    entropicGibbsFactor c ε φ ψ =
      {z | c z ≠ ∞}.indicator fun z ↦ Real.exp ((φ z.1 + ψ z.2 - (c z).toReal) / ε) :=
  (rfl)

omit [MeasurableSpace X] [MeasurableSpace Y] in
/-- Where the cost is finite, the Gibbs factor is the real exponential of the Gibbs exponent. -/
@[simp]
theorem entropicGibbsFactor_of_ne_top {z : X × Y} (hz : c z ≠ ∞) :
    entropicGibbsFactor c ε φ ψ z = Real.exp ((φ z.1 + ψ z.2 - (c z).toReal) / ε) :=
  Set.indicator_of_mem hz _

end TauCeti

namespace Matrix

variable {X Y : Type*}

/-- At a nonnegative entry of a real-valued matrix cost, the generic Gibbs factor splits into its
row potential, Gibbs kernel, and column potential factors. -/
theorem entropicGibbsFactor_ofReal_eq_mul_exp_mul_exp (C : Matrix X Y ℝ) (ε : ℝ≥0)
    (φ : X → ℝ) (ψ : Y → ℝ) (i : X) (j : Y) (hC : 0 ≤ C i j) :
    TauCeti.entropicGibbsFactor (fun q ↦ ENNReal.ofReal (C q.1 q.2)) ε φ ψ (i, j) =
      Real.exp (φ i / ε) * Real.exp (-C i j / ε) * Real.exp (ψ j / ε) := by
  rw [TauCeti.entropicGibbsFactor_of_ne_top ENNReal.ofReal_ne_top,
    ENNReal.toReal_ofReal hC, ← Real.exp_add, ← Real.exp_add]
  congr 1
  ring

/-- For a pointwise nonnegative real cost, a matrix is a diagonal scaling of the product-weighted
Gibbs kernel exactly when its entries are the product of the row and column weights multiplied by
the generic Gibbs factor. -/
theorem isDiagonalScaling_gibbs_iff (P C : Matrix X Y ℝ) (a : X → ℝ) (b : Y → ℝ)
    (ε : ℝ≥0) (φ : X → ℝ) (ψ : Y → ℝ) (hC : ∀ i j, 0 ≤ C i j) :
    IsDiagonalScaling P
        (of fun i j ↦ a i * b j * Real.exp (-C i j / ε))
        (fun i ↦ Real.exp (φ i / ε)) (fun j ↦ Real.exp (ψ j / ε)) ↔
      ∀ i j, P i j = a i * b j *
        TauCeti.entropicGibbsFactor (fun q ↦ ENNReal.ofReal (C q.1 q.2)) ε φ ψ (i, j) := by
  rw [isDiagonalScaling_def]
  constructor <;> intro h i j
  · rw [h i j, of_apply,
      entropicGibbsFactor_ofReal_eq_mul_exp_mul_exp C ε φ ψ i j (hC i j)]
    ring
  · rw [h i j, of_apply,
      entropicGibbsFactor_ofReal_eq_mul_exp_mul_exp C ε φ ψ i j (hC i j)]
    ring

end Matrix

namespace TauCeti

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
  {c : X × Y → ℝ≥0∞} {ε : ℝ≥0} {π : Measure (X × Y)} {μ : Measure X} {ν : Measure Y}
  {φ φ' : X → ℝ} {ψ ψ' : Y → ℝ}

omit [MeasurableSpace X] [MeasurableSpace Y] in
/-- Where the cost is infinite, the Gibbs factor vanishes. -/
@[simp]
theorem entropicGibbsFactor_of_eq_top {z : X × Y} (hz : c z = ∞) :
    entropicGibbsFactor c ε φ ψ z = 0 :=
  Set.indicator_of_notMem (not_not.2 hz) _

omit [MeasurableSpace X] [MeasurableSpace Y] in
/-- For a cost that is finite everywhere, the Gibbs factor is the real exponential. -/
theorem entropicGibbsFactor_eq_exp_of_forall_ne_top (hc : ∀ z, c z ≠ ∞) :
    entropicGibbsFactor c ε φ ψ = fun z ↦ Real.exp ((φ z.1 + ψ z.2 - (c z).toReal) / ε) :=
  funext fun z ↦ entropicGibbsFactor_of_ne_top (hc z)

omit [MeasurableSpace X] [MeasurableSpace Y] in
/-- The Gibbs factor is nonnegative. -/
theorem entropicGibbsFactor_nonneg (z : X × Y) : 0 ≤ entropicGibbsFactor c ε φ ψ z :=
  Set.indicator_nonneg (fun _ _ ↦ (Real.exp_pos _).le) z

omit [MeasurableSpace X] [MeasurableSpace Y] in
/-- Opposite additive shifts of the potentials do not change the Gibbs factor. -/
@[simp]
theorem entropicGibbsFactor_add_const_sub_const (a : ℝ) :
    entropicGibbsFactor c ε (fun x ↦ φ x + a) (fun y ↦ ψ y - a) = entropicGibbsFactor c ε φ ψ := by
  simp only [entropicGibbsFactor_def, add_add_sub_cancel]

/-- Replacing the potentials by `μ`- and `ν`-almost everywhere equal ones changes the Gibbs
factor only on a `μ ⊗ ν`-null set. -/
theorem entropicGibbsFactor_congr_ae (hφ : φ =ᵐ[μ] φ') (hψ : ψ =ᵐ[ν] ψ') :
    entropicGibbsFactor c ε φ ψ =ᵐ[μ.prod ν] entropicGibbsFactor c ε φ' ψ' := by
  filter_upwards [Measure.quasiMeasurePreserving_fst.ae hφ,
    Measure.quasiMeasurePreserving_snd.ae hψ] with z h₁ h₂
  by_cases hz : c z = ∞
  · simp only [entropicGibbsFactor_of_eq_top hz]
  · simp only [entropicGibbsFactor_of_ne_top hz, h₁, h₂]

omit [MeasurableSpace X] [MeasurableSpace Y] in
/-- Exchanging the factors exchanges the two Gibbs potentials. -/
@[simp]
theorem entropicGibbsFactor_comp_swap :
    entropicGibbsFactor (c ∘ Prod.swap) ε ψ φ =
      (entropicGibbsFactor c ε φ ψ) ∘ Prod.swap := by
  funext z
  by_cases hz : c z.swap = ∞ <;>
    simp [entropicGibbsFactor_def, Function.comp_def, hz, add_comm]

/-- The Gibbs factor of measurable potentials for a measurable cost is measurable. -/
theorem measurable_entropicGibbsFactor (hc : Measurable c) (hφ : Measurable φ)
    (hψ : Measurable ψ) : Measurable (entropicGibbsFactor c ε φ ψ) :=
  Measurable.indicator (by fun_prop) (hc (measurableSet_singleton ∞).compl)

/-- For finite measures, a measurable cost and measurable potentials bounded above by `Cφ` and
`Cψ`, the Gibbs factor is integrable against `μ ⊗ ν`: it is at most `exp ((Cφ + Cψ) / ε)`, since
the cost is nonnegative. -/
theorem integrable_entropicGibbsFactor_of_le [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hc : Measurable c) {Cφ Cψ : ℝ} (hφ : Measurable φ) (hψ : Measurable ψ)
    (hφC : ∀ x, φ x ≤ Cφ) (hψC : ∀ y, ψ y ≤ Cψ) :
    Integrable (entropicGibbsFactor c ε φ ψ) (μ.prod ν) := by
  refine Integrable.of_bound (measurable_entropicGibbsFactor hc hφ hψ).aestronglyMeasurable
    (Real.exp ((Cφ + Cψ) / ε)) <| ae_of_all _ fun z ↦ ?_
  rw [Real.norm_eq_abs, abs_of_nonneg (entropicGibbsFactor_nonneg z)]
  by_cases hz : c z = ∞
  · rw [entropicGibbsFactor_of_eq_top hz]
    exact (Real.exp_pos _).le
  rw [entropicGibbsFactor_of_ne_top hz, Real.exp_le_exp]
  refine div_le_div_of_nonneg_right ?_ ε.coe_nonneg
  linarith [hφC z.1, hψC z.2, (c z).toReal_nonneg]

/-! ### The Gibbs kernel -/

/-- The Gibbs kernel `exp (-c(x, y) / ε)` of the cost `c` at temperature `ε`, read with
`exp (-∞) = 0`: it is `0` where the cost is infinite. It is the Gibbs factor of the zero
potentials, and every Gibbs factor is the Gibbs kernel multiplied by the exponentials of the two
potentials (`TauCeti.entropicGibbsFactor_apply`). -/
def entropicGibbsKernel (c : X × Y → ℝ≥0∞) (ε : ℝ≥0) (x : X) (y : Y) : ℝ :=
  entropicGibbsFactor c ε 0 0 (x, y)

omit [MeasurableSpace X] [MeasurableSpace Y] in
/-- The Gibbs kernel is the Gibbs factor of the zero potentials. The definition's body is not
exposed, so this is the lemma downstream modules should rewrite with. -/
theorem entropicGibbsKernel_def (x : X) (y : Y) :
    entropicGibbsKernel c ε x y = entropicGibbsFactor c ε 0 0 (x, y) :=
  (rfl)

omit [MeasurableSpace X] [MeasurableSpace Y] in
/-- Where the cost is finite, the Gibbs kernel is `exp (-c(x, y) / ε)`. -/
@[simp]
theorem entropicGibbsKernel_of_ne_top {x : X} {y : Y} (hz : c (x, y) ≠ ∞) :
    entropicGibbsKernel c ε x y = Real.exp (-(c (x, y)).toReal / ε) := by
  rw [entropicGibbsKernel_def, entropicGibbsFactor_of_ne_top hz, Pi.zero_apply, Pi.zero_apply,
    zero_add, zero_sub]

omit [MeasurableSpace X] [MeasurableSpace Y] in
/-- Where the cost is infinite, the Gibbs kernel vanishes. -/
@[simp]
theorem entropicGibbsKernel_of_eq_top {x : X} {y : Y} (hz : c (x, y) = ∞) :
    entropicGibbsKernel c ε x y = 0 :=
  entropicGibbsFactor_of_eq_top hz

omit [MeasurableSpace X] [MeasurableSpace Y] in
/-- The Gibbs kernel is nonnegative. -/
theorem entropicGibbsKernel_nonneg (x : X) (y : Y) : 0 ≤ entropicGibbsKernel c ε x y :=
  entropicGibbsFactor_nonneg _

omit [MeasurableSpace X] [MeasurableSpace Y] in
/-- The Gibbs factor of the potentials `φ` and `ψ` is the Gibbs kernel multiplied by
`exp (φ(x) / ε)` and `exp (ψ(y) / ε)`. -/
theorem entropicGibbsFactor_apply (φ : X → ℝ) (ψ : Y → ℝ) (x : X) (y : Y) :
    entropicGibbsFactor c ε φ ψ (x, y) =
      Real.exp (φ x / ε) * entropicGibbsKernel c ε x y * Real.exp (ψ y / ε) := by
  by_cases hz : c (x, y) = ∞
  · simp [hz]
  rw [entropicGibbsFactor_of_ne_top hz, entropicGibbsKernel_of_ne_top hz, ← Real.exp_add,
    ← Real.exp_add]
  congr 1
  ring

/-- The Gibbs kernel of a measurable cost is jointly measurable. -/
theorem measurable_entropicGibbsKernel (hc : Measurable c) :
    Measurable (Function.uncurry (entropicGibbsKernel c ε)) := by
  have h : Function.uncurry (entropicGibbsKernel c ε) = entropicGibbsFactor c ε 0 0 :=
    funext fun z ↦ entropicGibbsKernel_def z.1 z.2
  rw [h]
  exact measurable_entropicGibbsFactor hc measurable_const measurable_const

omit [MeasurableSpace X] [MeasurableSpace Y] in
/-- The Gibbs kernel of a continuous finite cost is jointly continuous. -/
theorem continuous_entropicGibbsKernel [TopologicalSpace X] [TopologicalSpace Y]
    (hc : Continuous c) (hfin : ∀ z, c z ≠ ∞) :
    Continuous (Function.uncurry (entropicGibbsKernel c ε)) := by
  have h : Function.uncurry (entropicGibbsKernel c ε) =
      fun z ↦ Real.exp (-(c z).toReal / ε) :=
    funext fun z ↦ entropicGibbsKernel_of_ne_top (hfin z)
  rw [h]
  exact ((ENNReal.continuousOn_toReal.comp_continuous hc hfin).neg.div_const _).rexp

/-! ### The dual value -/

/-- The value of the dual problem of entropic optimal transport at the potentials `φ` and `ψ`:
`∫ φ dμ + ∫ ψ dν - ε * ∫ (exp ((φ(x) + ψ(y) - c(x, y)) / ε) - 1) d(μ ⊗ ν)`, where the Gibbs factor
`exp ((φ(x) + ψ(y) - c(x, y)) / ε)` is `TauCeti.entropicGibbsFactor c ε φ ψ`, which is `0` where
the cost is infinite. The duality theorems assume a positive temperature `ε` and require both
potentials and the Gibbs factor to be integrable. -/
def entropicDualValue (c : X × Y → ℝ≥0∞) (ε : ℝ≥0) (μ : Measure X) (ν : Measure Y) (φ : X → ℝ)
    (ψ : Y → ℝ) : ℝ :=
  kantorovichDualValue μ ν φ ψ - ε * ∫ z, (entropicGibbsFactor c ε φ ψ z - 1) ∂μ.prod ν

/-- The entropic dual value is the Kantorovich dual value minus the exponential penalty. The
definition's body is not exposed, so this is the lemma downstream modules should rewrite with. -/
theorem entropicDualValue_def :
    entropicDualValue c ε μ ν φ ψ =
      kantorovichDualValue μ ν φ ψ - ε * ∫ z, (entropicGibbsFactor c ε φ ψ z - 1) ∂μ.prod ν :=
  (rfl)

/-- The entropic dual value only depends on the `μ`- and `ν`-almost everywhere classes of the
potentials. -/
theorem entropicDualValue_congr_ae (hφ : φ =ᵐ[μ] φ') (hψ : ψ =ᵐ[ν] ψ') :
    entropicDualValue c ε μ ν φ ψ = entropicDualValue c ε μ ν φ' ψ' := by
  rw [entropicDualValue_def, entropicDualValue_def, kantorovichDualValue_def,
    kantorovichDualValue_def, integral_congr_ae hφ, integral_congr_ae hψ,
    integral_congr_ae <| (entropicGibbsFactor_congr_ae (c := c) (ε := ε) hφ hψ).mono
      fun _ hz ↦ congrArg (· - 1) hz]

/-- Opposite additive shifts of the potentials do not change the entropic dual value when the
first marginal is finite and the two marginals have the same mass. -/
theorem entropicDualValue_add_const_sub_const [IsFiniteMeasure μ] (hφ : Integrable φ μ)
    (hψ : Integrable ψ ν) (hmass : μ Set.univ = ν Set.univ) (a : ℝ) :
    entropicDualValue c ε μ ν (fun x ↦ φ x + a) (fun y ↦ ψ y - a) =
      entropicDualValue c ε μ ν φ ψ := by
  simp only [entropicDualValue_def, kantorovichDualValue_add_const_sub_const hφ hψ hmass,
    entropicGibbsFactor_add_const_sub_const]

/-- Exchanging the marginals, cost coordinates and potentials preserves the entropic dual value.
No integrability assumptions are needed for this symmetry of the defining integrals. -/
@[simp]
theorem entropicDualValue_comp_swap [SFinite μ] [SFinite ν] :
    entropicDualValue (c ∘ Prod.swap) ε ν μ ψ φ = entropicDualValue c ε μ ν φ ψ := by
  simp only [entropicDualValue_def, kantorovichDualValue_def, entropicGibbsFactor_comp_swap,
    Function.comp_apply]
  rw [integral_prod_swap (fun z ↦ entropicGibbsFactor c ε φ ψ z - 1)]
  ring

/-- The Gibbs factor of a Gibbs coupling of probability laws is a probability density against
`μ ⊗ ν`: its integral is `1`. -/
theorem IsCoupling.integral_entropicGibbsFactor_eq_one [IsProbabilityMeasure μ]
    (hπ : IsCoupling π μ ν)
    (hπeq : π = (μ.prod ν).withDensity fun z ↦
      ENNReal.ofReal (entropicGibbsFactor c ε φ ψ z))
    (hexp : Integrable (entropicGibbsFactor c ε φ ψ) (μ.prod ν)) :
    ∫ z, entropicGibbsFactor c ε φ ψ z ∂μ.prod ν = 1 := by
  have := hπ.isProbabilityMeasure
  have hmass : ∫⁻ z, ENNReal.ofReal (entropicGibbsFactor c ε φ ψ z) ∂μ.prod ν = 1 := by
    rw [← setLIntegral_univ, ← withDensity_apply _ MeasurableSet.univ, ← hπeq]
    exact measure_univ
  rw [integral_eq_lintegral_of_nonneg_ae
    (ae_of_all _ entropicGibbsFactor_nonneg) hexp.aestronglyMeasurable, hmass]
  simp

/-- For a Gibbs coupling of probability laws, the exponential penalty in the entropic dual
value vanishes. Its dual value is therefore just the sum of the two marginal integrals. -/
theorem IsCoupling.entropicDualValue_eq_of_eq_withDensity [IsProbabilityMeasure μ]
    (hπ : IsCoupling π μ ν)
    (hπeq : π = (μ.prod ν).withDensity fun z ↦
      ENNReal.ofReal (entropicGibbsFactor c ε φ ψ z))
    (hexp : Integrable (entropicGibbsFactor c ε φ ψ) (μ.prod ν)) :
    entropicDualValue c ε μ ν φ ψ = kantorovichDualValue μ ν φ ψ := by
  have := hπ.isProbabilityMeasure
  have : IsProbabilityMeasure ν := hπ.snd_eq ▸ inferInstance
  rw [entropicDualValue_def, integral_sub hexp (integrable_const _),
    hπ.integral_entropicGibbsFactor_eq_one hπeq hexp]
  simp

/-! ### Weak duality and complementary slackness -/

/-- Against a coupling `π`, the entropic dual value is `ε` times the variational objective
`∫ f dπ - ∫ (exp f - 1) d(μ ⊗ ν)` of the Gibbs exponent `f = (φ ⊕ ψ - c) / ε`, plus the cost
of `π`. -/
private theorem IsCoupling.entropicDualValue_eq (hπ : IsCoupling π μ ν) (hε : ε ≠ 0)
    (hφ : Integrable φ μ) (hψ : Integrable ψ ν) (hc : Integrable (fun z ↦ (c z).toReal) π) :
    entropicDualValue c ε μ ν φ ψ =
      ε * (∫ z, (φ z.1 + ψ z.2 - (c z).toReal) / ε ∂π -
        ∫ z, (entropicGibbsFactor c ε φ ψ z - 1) ∂μ.prod ν) + ∫ z, (c z).toReal ∂π := by
  have hε' : (ε : ℝ) ≠ 0 := NNReal.coe_ne_zero.2 hε
  rw [entropicDualValue_def, kantorovichDualValue_eq_integral hπ hφ hψ, integral_div,
    integral_sub (hπ.integrable_add_split hφ hψ) hc]
  field_simp
  ring

/-- **Weak duality for entropic optimal transport, against a fixed coupling.** For a finite source
measure, an almost everywhere measurable cost and a positive temperature, the positive part of the
entropic dual value of integrable potentials is at most the regularised cost of every coupling. -/
theorem IsCoupling.ofReal_entropicDualValue_le_lintegral_add_mul_klDiv [IsFiniteMeasure μ]
    (hπ : IsCoupling π μ ν) (hc : AEMeasurable c (μ.prod ν)) (hε : ε ≠ 0) (hφ : Integrable φ μ)
    (hψ : Integrable ψ ν) (hexp : Integrable (entropicGibbsFactor c ε φ ψ) (μ.prod ν)) :
    ENNReal.ofReal (entropicDualValue c ε μ ν φ ψ) ≤ ∫⁻ z, c z ∂π + ε * klDiv π (μ.prod ν) := by
  have := hπ.isFiniteMeasure
  have : IsFiniteMeasure ν := hπ.snd_eq ▸ inferInstance
  by_cases hKL : klDiv π (μ.prod ν) = ∞
  · simp [hKL, ENNReal.mul_top (ENNReal.coe_ne_zero.2 hε)]
  by_cases hcost : ∫⁻ z, c z ∂π = ∞
  · simp [hcost]
  have hcπ : AEMeasurable c π := hc.mono_ac (klDiv_ne_top_iff.1 hKL).1
  have hci := integrable_toReal_of_lintegral_ne_top hcπ hcost
  have hf : Integrable (fun z ↦ (φ z.1 + ψ z.2 - (c z).toReal) / ε) π :=
    ((hπ.integrable_add_split hφ hψ).sub hci).div_const _
  rw [hπ.entropicDualValue_eq hε hφ hψ hci, integral_toReal hcπ (ae_lt_top' hcπ hcost), add_comm]
  refine ENNReal.ofReal_add_le.trans ?_
  rw [ENNReal.ofReal_toReal hcost, ENNReal.ofReal_mul ε.coe_nonneg, ENNReal.ofReal_coe_nnreal]
  gcongr
  exact ofReal_integral_sub_integral_indicator_exp_sub_one_le_klDiv
    ((ae_lt_top' hcπ hcost).mono fun _ hz ↦ hz.ne) hf hexp

/-- **Weak duality for entropic optimal transport.** For a finite source measure, an almost
everywhere measurable cost and a positive temperature, the positive part of the entropic dual
value of integrable potentials is at most the regularised transport cost. -/
theorem ofReal_entropicDualValue_le_entropicTransportCost [IsFiniteMeasure μ]
    (hc : AEMeasurable c (μ.prod ν)) (hε : ε ≠ 0) (hφ : Integrable φ μ) (hψ : Integrable ψ ν)
    (hexp : Integrable (entropicGibbsFactor c ε φ ψ) (μ.prod ν)) :
    ENNReal.ofReal (entropicDualValue c ε μ ν φ ψ) ≤ entropicTransportCost c ε μ ν :=
  le_entropicTransportCost fun _ hπ ↦
    hπ.ofReal_entropicDualValue_le_lintegral_add_mul_klDiv hc hε hφ hψ hexp

/-- **Weak duality for entropic optimal transport, in real form.** When the regularised transport
cost is finite, it bounds the entropic dual value of integrable potentials. -/
theorem entropicDualValue_le_toReal_entropicTransportCost [IsFiniteMeasure μ]
    (h : entropicTransportCost c ε μ ν ≠ ∞) (hc : AEMeasurable c (μ.prod ν)) (hε : ε ≠ 0)
    (hφ : Integrable φ μ) (hψ : Integrable ψ ν)
    (hexp : Integrable (entropicGibbsFactor c ε φ ψ) (μ.prod ν)) :
    entropicDualValue c ε μ ν φ ψ ≤ (entropicTransportCost c ε μ ν).toReal :=
  (ENNReal.ofReal_le_iff_le_toReal h).1
    (ofReal_entropicDualValue_le_entropicTransportCost hc hε hφ hψ hexp)

/-- **Complementary slackness for entropic optimal transport.** Let `π` be a coupling of finite
regularised cost, and `φ`, `ψ` integrable potentials with integrable Gibbs factor. Then the
entropic dual value of `φ` and `ψ` equals the regularised cost of `π` exactly when `π` has density
`exp ((φ(x) + ψ(y) - c(x, y)) / ε)` against `μ ⊗ ν`, read as `0` where the cost is infinite. By
weak duality, `π` is then an optimal plan and `(φ, ψ)` a maximiser of the dual problem. -/
theorem IsCoupling.entropicDualValue_eq_toReal_lintegral_add_mul_klDiv_iff [IsFiniteMeasure μ]
    (hπ : IsCoupling π μ ν) (hc : AEMeasurable c (μ.prod ν)) (hε : ε ≠ 0) (hφ : Integrable φ μ)
    (hψ : Integrable ψ ν) (hexp : Integrable (entropicGibbsFactor c ε φ ψ) (μ.prod ν))
    (hfin : ∫⁻ z, c z ∂π + ε * klDiv π (μ.prod ν) ≠ ∞) :
    entropicDualValue c ε μ ν φ ψ = (∫⁻ z, c z ∂π + ε * klDiv π (μ.prod ν)).toReal ↔
      π = (μ.prod ν).withDensity fun z ↦ ENNReal.ofReal (entropicGibbsFactor c ε φ ψ z) := by
  have := hπ.isFiniteMeasure
  have : IsFiniteMeasure ν := hπ.snd_eq ▸ inferInstance
  obtain ⟨hcost, hεKL⟩ := ENNReal.add_ne_top.1 hfin
  have hKL : klDiv π (μ.prod ν) ≠ ∞ := fun h ↦
    hεKL (by rw [h, ENNReal.mul_top (ENNReal.coe_ne_zero.2 hε)])
  have hcπ : AEMeasurable c π := hc.mono_ac (klDiv_ne_top_iff.1 hKL).1
  have hci := integrable_toReal_of_lintegral_ne_top hcπ hcost
  have hf : Integrable (fun z ↦ (φ z.1 + ψ z.2 - (c z).toReal) / ε) π :=
    ((hπ.integrable_add_split hφ hψ).sub hci).div_const _
  rw [entropicGibbsFactor_def,
    ← integral_sub_integral_indicator_exp_sub_one_eq_toReal_klDiv_iff (s := {z | c z ≠ ∞})
      ((ae_lt_top' hcπ hcost).mono fun _ hz ↦ hz.ne) hf hexp hKL,
    hπ.entropicDualValue_eq hε hφ hψ hci, entropicGibbsFactor_def,
    integral_toReal hcπ (ae_lt_top' hcπ hcost), ENNReal.toReal_add hcost hεKL, ENNReal.toReal_mul,
    ENNReal.coe_toReal]
  have hε' : (ε : ℝ) ≠ 0 := NNReal.coe_ne_zero.2 hε
  constructor
  · intro h
    exact mul_left_cancel₀ hε' (by linarith)
  · intro h
    rw [h]
    ring

/-- **Uniqueness of the entropic potentials.** For a nonzero finite source measure and a cost
finite `μ ⊗ ν`-almost everywhere, two pairs of potentials whose entropic dual values both equal
the finite regularised cost of a common coupling `π` differ by one additive constant, `μ`- and
`ν`-almost everywhere: `φ = φ' + a` and `ψ = ψ' - a`. -/
theorem IsCoupling.exists_ae_eq_add_const_of_entropicDualValue_eq
    [IsFiniteMeasure μ] (hμ : μ ≠ 0) (hπ : IsCoupling π μ ν) (hc : AEMeasurable c (μ.prod ν))
    (hcfin : ∀ᵐ z ∂μ.prod ν, c z ≠ ∞) (hε : ε ≠ 0)
    (hfin : ∫⁻ z, c z ∂π + ε * klDiv π (μ.prod ν) ≠ ∞)
    (hφ : Integrable φ μ) (hψ : Integrable ψ ν)
    (hexp : Integrable (entropicGibbsFactor c ε φ ψ) (μ.prod ν))
    (h : entropicDualValue c ε μ ν φ ψ = (∫⁻ z, c z ∂π + ε * klDiv π (μ.prod ν)).toReal)
    (hφ' : Integrable φ' μ) (hψ' : Integrable ψ' ν)
    (hexp' : Integrable (entropicGibbsFactor c ε φ' ψ') (μ.prod ν))
    (h' : entropicDualValue c ε μ ν φ' ψ' = (∫⁻ z, c z ∂π + ε * klDiv π (μ.prod ν)).toReal) :
    ∃ a, φ =ᵐ[μ] (fun x ↦ φ' x + a) ∧ ψ =ᵐ[ν] (fun y ↦ ψ' y - a) := by
  have := hπ.isFiniteMeasure
  have : IsFiniteMeasure ν := hπ.snd_eq ▸ inferInstance
  have hν : ν ≠ 0 := by
    rwa [Ne, ← Measure.measure_univ_eq_zero, ← hπ.measure_univ_eq, Measure.measure_univ_eq_zero]
  have hdens :=
    ((hπ.entropicDualValue_eq_toReal_lintegral_add_mul_klDiv_iff hc hε hφ hψ hexp hfin).1
      h).symm.trans
    ((hπ.entropicDualValue_eq_toReal_lintegral_add_mul_klDiv_iff hc hε hφ' hψ' hexp' hfin).1 h')
  rw [withDensity_eq_iff_of_sigmaFinite hexp.aemeasurable.ennreal_ofReal
    hexp'.aemeasurable.ennreal_ofReal] at hdens
  have hε' : (ε : ℝ) ≠ 0 := NNReal.coe_ne_zero.2 hε
  -- Equal Gibbs densities have equal exponents where the cost is finite, so `φ - φ'` and
  -- `ψ' - ψ` agree on `μ ⊗ ν`.
  obtain ⟨a, hφa, hψa⟩ := exists_ae_eq_const_of_ae_prod_eq (f := fun x ↦ φ x - φ' x)
    (g := fun y ↦ ψ' y - ψ y) hμ hν <| (hdens.and hcfin).mono fun z ⟨hz, hcz⟩ ↦ by
      simp only [entropicGibbsFactor_of_ne_top hcz] at hz
      have := Real.exp_injective <|
        (ENNReal.ofReal_eq_ofReal_iff (Real.exp_pos _).le (Real.exp_pos _).le).1 hz
      rw [div_left_inj' hε'] at this
      linarith
  exact ⟨a, hφa.mono fun x hx ↦ by simp only at hx; linarith,
    hψa.mono fun y hy ↦ by simp only at hy; linarith⟩

/-! ### Strong duality for a bounded cost -/

section Bounded

variable [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] {B : ℝ≥0}

/-- **Strong entropic duality for a bounded cost, with attainment.** For probability measures, a
bounded measurable cost and a positive temperature, the dual problem is attained by bounded
measurable potentials, with value the regularised transport cost. -/
theorem exists_entropicDualValue_eq_toReal_entropicTransportCost (hc : Measurable c)
    (hcB : ∀ z, c z ≤ B) (hε : ε ≠ 0) :
    ∃ (φ : X → ℝ) (ψ : Y → ℝ) (C : ℝ), Measurable φ ∧ Measurable ψ ∧ (∀ x, |φ x| ≤ C) ∧
      (∀ y, |ψ y| ≤ C) ∧
        entropicDualValue c ε μ ν φ ψ = (entropicTransportCost c ε μ ν).toReal := by
  obtain ⟨π, hπ, hopt, φ, ψ, C, hφ, hψ, hφC, hψC, hπeq⟩ :=
    exists_isCoupling_lintegral_add_mul_klDiv_eq_entropicTransportCost (μ := μ) (ν := ν) hc hcB
      hε
  refine ⟨φ, ψ, C, hφ, hψ, hφC, hψC, ?_⟩
  rw [← hopt]
  refine (hπ.entropicDualValue_eq_toReal_lintegral_add_mul_klDiv_iff hc.aemeasurable hε
    (.of_bound hφ.aestronglyMeasurable C (ae_of_all _ hφC))
    (.of_bound hψ.aestronglyMeasurable C (ae_of_all _ hψC))
    (integrable_entropicGibbsFactor_of_le hc hφ hψ (fun x ↦ le_of_abs_le (hφC x))
      (fun y ↦ le_of_abs_le (hψC y)))
    (hopt ▸ entropicTransportCost_ne_top_of_forall_le hcB ε)).2 ?_
  rwa [entropicGibbsFactor_eq_exp_of_forall_ne_top fun z ↦
    ne_top_of_le_ne_top ENNReal.coe_ne_top (hcB z)]

/-- **Strong entropic duality for a bounded cost.** For probability measures, a bounded
measurable cost and a positive temperature, the regularised transport cost is the greatest
entropic dual value of integrable potentials with integrable Gibbs factor. -/
theorem isGreatest_entropicDualValue_integrable (hc : Measurable c) (hcB : ∀ z, c z ≤ B)
    (hε : ε ≠ 0) :
    IsGreatest {r : ℝ | ∃ (φ : X → ℝ) (ψ : Y → ℝ), Integrable φ μ ∧ Integrable ψ ν ∧
        Integrable (entropicGibbsFactor c ε φ ψ) (μ.prod ν) ∧
        entropicDualValue c ε μ ν φ ψ = r}
      (entropicTransportCost c ε μ ν).toReal := by
  obtain ⟨φ, ψ, C, hφ, hψ, hφC, hψC, h⟩ :=
    exists_entropicDualValue_eq_toReal_entropicTransportCost (μ := μ) (ν := ν) hc hcB hε
  refine ⟨⟨φ, ψ, .of_bound hφ.aestronglyMeasurable C (ae_of_all _ hφC),
    .of_bound hψ.aestronglyMeasurable C (ae_of_all _ hψC),
    integrable_entropicGibbsFactor_of_le hc hφ hψ (fun x ↦ le_of_abs_le (hφC x))
      (fun y ↦ le_of_abs_le (hψC y)), h⟩, ?_⟩
  rintro r ⟨φ', ψ', hφ', hψ', hexp', rfl⟩
  exact entropicDualValue_le_toReal_entropicTransportCost
    (entropicTransportCost_ne_top_of_forall_le hcB ε) hc.aemeasurable hε hφ' hψ' hexp'

/-- **Uniqueness of the entropic dual maximisers for a bounded cost.** For probability measures,
a bounded measurable cost and a positive temperature, two pairs of integrable potentials whose
entropic dual values both equal the regularised transport cost differ by one additive constant,
`μ`- and `ν`-almost everywhere. -/
theorem exists_ae_eq_add_const_of_entropicDualValue_eq_toReal_entropicTransportCost
    (hc : Measurable c) (hcB : ∀ z, c z ≤ B) (hε : ε ≠ 0) (hφ : Integrable φ μ)
    (hψ : Integrable ψ ν) (hexp : Integrable (entropicGibbsFactor c ε φ ψ) (μ.prod ν))
    (h : entropicDualValue c ε μ ν φ ψ = (entropicTransportCost c ε μ ν).toReal)
    (hφ' : Integrable φ' μ) (hψ' : Integrable ψ' ν)
    (hexp' : Integrable (entropicGibbsFactor c ε φ' ψ') (μ.prod ν))
    (h' : entropicDualValue c ε μ ν φ' ψ' = (entropicTransportCost c ε μ ν).toReal) :
    ∃ a, φ =ᵐ[μ] (fun x ↦ φ' x + a) ∧ ψ =ᵐ[ν] (fun y ↦ ψ' y - a) := by
  obtain ⟨π, hπ, hopt, -⟩ :=
    exists_isCoupling_lintegral_add_mul_klDiv_eq_entropicTransportCost (μ := μ) (ν := ν) hc hcB
      hε
  rw [← hopt] at h h'
  exact hπ.exists_ae_eq_add_const_of_entropicDualValue_eq
    (IsProbabilityMeasure.ne_zero μ) hc.aemeasurable
    (ae_of_all _ fun z ↦ ne_top_of_le_ne_top ENNReal.coe_ne_top (hcB z)) hε
    (hopt ▸ entropicTransportCost_ne_top_of_forall_le hcB ε) hφ hψ hexp h hφ' hψ' hexp' h'

end Bounded

end TauCeti
