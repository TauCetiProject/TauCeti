/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.HeisenbergModel.Basic
public import Mathlib.MeasureTheory.Function.L1Space.Integrable
public import Mathlib.MeasureTheory.Function.LpSpace.Complete
public import Mathlib.MeasureTheory.Measure.Haar.Basic
public import Mathlib.Analysis.Normed.Operator.Bilinear
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.Topology.Metrizable.Urysohn
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Function.LpSpace.InfiniteSum
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Normed.Ring.Lemmas
import Mathlib.Analysis.Normed.Group.Completeness
import TauCeti.MeasureTheory.Integral.Bochner.PointwiseOperator

/-!
# The reproducing model of a vacuum

Let `β` be a Heisenberg datum on a second countable abelian topological group `W` with a Haar
measure `μ`, and `e` a vacuum for `β` and `μ`. The *reproducing model* `M(β, e)` is the space of
integrable functions `v : W → ℂ` with
`v x = ∫ v y * (β y x * e (x - y)) dμ(y)` for every `x`, with the `L¹` norm. It is a Banach space
of continuous functions bounded by their norm, on which `W` acts by the Heisenberg operators
`(ϱ y v) x = β y x * v (x - y)`; it contains `e` (the *vacuum vector*), and carries the bounded
sesquilinear form `⟨v, w⟩ = ∫ conj (v x) * w x dμ(x)`.

The model is the image of a single vector under the Heisenberg operators, in the following
sense. *Superposition*: every bounded map `T` out of the model satisfies
`T v = ∫ v y • T (ϱ y e) dμ(y)`, so it is determined by its values on the translates `ϱ y e`.
*Schur's lemma*: a bounded operator commuting with every `ϱ y` is a scalar, and a bounded
sesquilinear form invariant under every `ϱ y` is a multiple of `⟨·, ·⟩`.

## Main definitions

* `TauCeti.ReproducingModel β μ e`: the reproducing model, a complex Banach space.
* `TauCeti.ReproducingModel.heisenbergRep`: its Heisenberg representation.
* `TauCeti.ReproducingModel.vacuum`: the vacuum vector `e`.
* `TauCeti.ReproducingModel.innerSL`: the sesquilinear form `⟨v, w⟩`.
* `TauCeti.HeisenbergDatum.Representation.integrated`: the integrated action
  `(v, f) ↦ ∫ v y • ϱ y f dμ(y)` of the model on any representation of `β` on a Banach space.

## Main results

* `TauCeti.ReproducingModel.norm_apply_le`, `TauCeti.ReproducingModel.continuous`: elements of
  the model are continuous and bounded by their norm.
* `TauCeti.ReproducingModel.innerSL_heisenbergRep_vacuum`: `⟨ϱ x e, v⟩ = v x`.
* `TauCeti.ReproducingModel.map_eq_integral`, `TauCeti.ReproducingModel.hom_ext`,
  `TauCeti.ReproducingModel.integrated_eq_smul`, `TauCeti.ReproducingModel.exists_lift`:
  superposition.
* `TauCeti.ReproducingModel.eq_smul_one_of_commute`,
  `TauCeti.ReproducingModel.integral_form_eq_mul_innerSL`,
  `TauCeti.ReproducingModel.form_eq_mul_innerSL`: Schur's lemma.

## Provenance

Adapted from grh-lean (https://github.com/lsernau/grh-lean, Apache 2.0, Copyright 2026
Anthropic, PBC), file `src/Lib/Weil/Construction/HeisenbergModel.lean`
(`New.Heisenberg.IsVacuum.Model`, `New.Heisenberg.IsVacuum.heisenbergRep`,
`New.Heisenberg.IsVacuum.vacElem`, `New.Heisenberg.IsVacuum.modelInner`,
`New.Heisenberg.Rep.integrated`, `New.Heisenberg.IsVacuum.map_eq_integral`,
`New.Heisenberg.IsVacuum.hom_ext`, `New.Heisenberg.IsVacuum.integrated_eq_smul`,
`New.Heisenberg.IsVacuum.exists_lift`, `New.Heisenberg.IsVacuum.eq_smul_one_of_commute`,
`New.Heisenberg.IsVacuum.integral_form_eq_mul_modelInner`,
`New.Heisenberg.IsVacuum.form_eq_mul_modelInner`), including the proof of strong continuity of
the Heisenberg operators by Scheffé's argument.

## References

* J. von Neumann, *Die Eindeutigkeit der Schrödingerschen Operatoren*, Math. Ann. 104 (1931),
  570–578.
* G. B. Folland, *Harmonic analysis in phase space*, Annals of Mathematics Studies 122, Princeton
  University Press (1989), Chapter 1.
-/

public noncomputable section

open MeasureTheory Filter Topology
open scoped ComplexConjugate

namespace TauCeti

variable {W : Type*} [AddCommGroup W] [TopologicalSpace W] [MeasurableSpace W]
  {β : HeisenbergDatum W} {μ : Measure W} {e : W → ℂ}

namespace HeisenbergDatum.IsVacuum

variable [IsTopologicalAddGroup W] [BorelSpace W]

/-- The product of an integrable function with the reproducing kernel `β y x * e (x - y)` of a
vacuum is integrable. -/
theorem integrable_mul_kernel (he : β.IsVacuum μ e) (x : W) {f : W → ℂ} (hf : Integrable f μ) :
    Integrable (fun y ↦ f y * (β y x * e (x - y))) μ := by
  have h_cont : Continuous fun y ↦ β y x * e (x - y) := by
    have := he.continuous
    fun_prop
  refine hf.mul_bdd h_cont.aestronglyMeasurable (c := 1) (.of_forall fun y ↦ ?_)
  exact he.norm_kernel_le_one x y

end HeisenbergDatum.IsVacuum

variable (β μ e) in
/-- The submodule of the functions `v : W → ℂ` that are integrable and reproduced by the kernel
of the vacuum `e`: `v x = ∫ v y * (β y x * e (x - y)) dμ(y)` for every `x`. -/
def reproducingSubmodule [IsTopologicalAddGroup W] [BorelSpace W] [he : β.IsVacuum μ e] :
    Submodule ℂ (W → ℂ) where
  carrier := {v | Integrable v μ ∧ ∀ x, ∫ y, v y * (β y x * e (x - y)) ∂μ = v x}
  add_mem' {v w} hv hw := by
    refine ⟨hv.1.add hw.1, fun x ↦ ?_⟩
    simp only [Pi.add_apply, add_mul]
    rw [integral_add (he.integrable_mul_kernel x hv.1) (he.integrable_mul_kernel x hw.1), hv.2,
      hw.2]
  zero_mem' := by simp
  smul_mem' c v hv := by
    refine ⟨hv.1.smul c, fun x ↦ ?_⟩
    simp only [Pi.smul_apply, smul_eq_mul, mul_assoc, integral_const_mul, hv.2]

variable [IsTopologicalAddGroup W] [BorelSpace W]

variable (β μ e) in
/-- The *reproducing model* `M(β, e)` of a vacuum `e` for a Heisenberg datum `β` and a measure
`μ`: the integrable functions `v : W → ℂ` with `v x = ∫ v y * (β y x * e (x - y)) dμ(y)` for
every `x`, with the `L¹` norm. -/
@[expose] def ReproducingModel [β.IsVacuum μ e] : Type _ := reproducingSubmodule β μ e

namespace ReproducingModel

variable [he : β.IsVacuum μ e]

instance : AddCommGroup (ReproducingModel β μ e) :=
  inferInstanceAs (AddCommGroup (reproducingSubmodule β μ e))

instance : Module ℂ (ReproducingModel β μ e) :=
  inferInstanceAs (Module ℂ (reproducingSubmodule β μ e))

instance : FunLike (ReproducingModel β μ e) W ℂ where
  coe v := (v : reproducingSubmodule β μ e).val
  coe_injective _ _ h := Subtype.ext h

variable (v w : ReproducingModel β μ e) (x y : W)

@[simp]
theorem add_apply : (v + w) x = v x + w x := (rfl)

@[simp]
theorem smul_apply (c : ℂ) : (c • v) x = c * v x := (rfl)

@[simp]
theorem zero_apply : (0 : ReproducingModel β μ e) x = 0 := (rfl)

@[simp]
theorem neg_apply : (-v) x = -v x := (rfl)

@[simp]
theorem sub_apply : (v - w) x = v x - w x := (rfl)

@[ext]
theorem ext {v w : ReproducingModel β μ e} (h : ∀ x, v x = w x) : v = w :=
  DFunLike.ext _ _ h

theorem integrable : Integrable v μ := (v : reproducingSubmodule β μ e).property.1

/-- The reproducing identity `∫ v y * (β y x * e (x - y)) dμ(y) = v x`. -/
theorem integral_mul_kernel : ∫ y, v y * (β y x * e (x - y)) ∂μ = v x :=
  (v : reproducingSubmodule β μ e).property.2 x

/-- The element of the model given by an integrable function with the reproducing identity. -/
def mk (f : W → ℂ) (hf : Integrable f μ) (h : ∀ x, ∫ y, f y * (β y x * e (x - y)) ∂μ = f x) :
    ReproducingModel β μ e :=
  (⟨f, hf, h⟩ : reproducingSubmodule β μ e)

@[simp]
theorem mk_apply (f : W → ℂ) (hf : Integrable f μ)
    (h : ∀ x, ∫ y, f y * (β y x * e (x - y)) ∂μ = f x) : mk f hf h x = f x := (rfl)

/-- The class in `L¹(μ)` of an element of the model, a complex-linear map. -/
def toL1 : ReproducingModel β μ e →ₗ[ℂ] W →₁[μ] ℂ where
  toFun v := v.integrable.toL1
  map_add' v w := Integrable.toL1_add _ _ v.integrable w.integrable
  map_smul' c v := Integrable.toL1_smul _ v.integrable c

theorem toL1_injective : Function.Injective (toL1 (β := β) (μ := μ) (e := e)) := fun v w h ↦ by
  -- Functions that agree almost everywhere have the same reproducing integrals.
  have h_ae : (v : W → ℂ) =ᵐ[μ] w := by
    simpa [toL1] using (Integrable.toL1_eq_toL1_iff _ _ v.integrable w.integrable).1 h
  ext x
  rw [← v.integral_mul_kernel, ← w.integral_mul_kernel]
  exact integral_congr_ae (h_ae.mono fun y hy ↦ by simp only [hy])

/-- The `L¹` norm on the model. -/
instance : NormedAddCommGroup (ReproducingModel β μ e) :=
  .induced _ _ toL1 toL1_injective

instance : NormedSpace ℂ (ReproducingModel β μ e) := .induced ℂ _ _ toL1

theorem norm_eq_integral_norm : ‖v‖ = ∫ x, ‖v x‖ ∂μ :=
  L1.norm_of_fun_eq_integral_norm v.integrable

theorem norm_toL1 : ‖toL1 v‖ = ‖v‖ := rfl

/-- An element of the model is bounded by its norm. -/
theorem norm_apply_le : ‖v x‖ ≤ ‖v‖ := by
  calc ‖v x‖ = ‖∫ y, v y * (β y x * e (x - y)) ∂μ‖ := by rw [v.integral_mul_kernel]
    _ ≤ ∫ y, ‖v y‖ ∂μ := norm_integral_le_of_norm_le v.integrable.norm
        (.of_forall fun y ↦ by
          rw [norm_mul]
          exact mul_le_of_le_one_right (norm_nonneg _) (he.norm_kernel_le_one x y))
    _ = ‖v‖ := (norm_eq_integral_norm v).symm

/-- An element of the model is a continuous function. -/
@[fun_prop]
theorem continuous [FirstCountableTopology W] : Continuous v := by
  -- Dominated convergence in the reproducing identity, whose kernel is continuous in `x`.
  have h_cont : Continuous e := he.continuous
  refine (continuous_of_dominated (fun x ↦ (he.integrable_mul_kernel x v.integrable).1)
    (fun x ↦ .of_forall fun y ↦ ?_) v.integrable.norm (.of_forall fun y ↦ by fun_prop)).congr
    v.integral_mul_kernel
  rw [norm_mul]
  exact mul_le_of_le_one_right (norm_nonneg _) (he.norm_kernel_le_one x y)

/-- The model is complete: the pointwise sum of an absolutely summable series lies in the model
and is its sum in `L¹`. -/
instance : CompleteSpace (ReproducingModel β μ e) := by
  refine NormedAddCommGroup.completeSpace_of_summable_imp_tendsto fun u hu ↦ ?_
  have h_ae : ⇑(∑' n, toL1 (u n)) =ᵐ[μ] fun x ↦ ∑' n, u n x :=
    (Lp.coeFn_tsum (tsum_eNorm_ne_top_iff_summable_norm.mpr hu)).trans
      ((ae_all_iff.mpr fun n ↦ (u n).integrable.coeFn_toL1).mono fun _ ↦ tsum_congr)
  have h_int : Integrable (fun x ↦ ∑' n, u n x) μ := .congr (L1.integrable_coeFn _) h_ae
  have h_repr (x : W) : ∫ y, (∑' n, u n y) * (β y x * e (x - y)) ∂μ = ∑' n, u n x := by
    -- Exchange the sum and the integral, then use the reproducing identity of each `u n`.
    have h_int_n (n : ℕ) := he.integrable_mul_kernel x (u n).integrable
    have h_le (n : ℕ) : ∫ y, ‖u n y * (β y x * e (x - y))‖ ∂μ ≤ ‖u n‖ := by
      rw [norm_eq_integral_norm (u n)]
      refine integral_mono (h_int_n n).norm (u n).integrable.norm fun y ↦ ?_
      rw [norm_mul]
      exact mul_le_of_le_one_right (norm_nonneg _) (he.norm_kernel_le_one x y)
    have h_sum : Summable fun n ↦ ∫ y, ‖u n y * (β y x * e (x - y))‖ ∂μ :=
      .of_nonneg_of_le (fun n ↦ integral_nonneg fun y ↦ norm_nonneg _) h_le hu
    simp_rw [← tsum_mul_right]
    rw [← integral_tsum_of_summable_integral_norm h_int_n h_sum]
    exact tsum_congr fun n ↦ (u n).integral_mul_kernel x
  let v : ReproducingModel β μ e := mk _ h_int h_repr
  have h_tsum : ∑' n, toL1 (u n) = toL1 v := Lp.ext (h_ae.trans h_int.coeFn_toL1.symm)
  have h_has : HasSum (fun n ↦ toL1 (u n)) (toL1 v) := by
    rw [← h_tsum]
    exact (Summable.of_norm (f := fun n ↦ toL1 (u n)) hu).hasSum
  -- The topology of the model is induced from `L¹`.
  exact ⟨v, ((Topology.IsInducing.hasSum_iff ⟨rfl⟩ u v).mp h_has).tendsto_sum_nat⟩

/-! ### The Heisenberg operators -/

section HeisenbergOperators

variable [μ.IsAddLeftInvariant]

/-- The twisted translate `x ↦ β y x * v (x - y)` of an element of the model satisfies the
reproducing identity. -/
private theorem integral_translate_mul_kernel :
    ∫ z, β y z * v (z - y) * (β z x * e (x - z)) ∂μ = β y x * v (x - y) := by
  rw [← integral_add_right_eq_self _ y, ← v.integral_mul_kernel (x - y), ← integral_const_mul]
  refine integral_congr_ae (.of_forall fun z ↦ ?_)
  have h_arg : x - (z + y) = x - y - z := by abel
  have h_beta : β z (x - y) = β z x * β y z := by
    rw [sub_eq_add_neg, β.map_add_right, β.apply_neg]
  simp only [add_sub_cancel_right, β.map_add_right, β.map_add_left, β.apply_self, h_arg, h_beta]
  ring

private theorem integrable_translate :
    Integrable (fun z ↦ β y z * v (z - y)) μ := by
  refine (v.integrable.comp_sub_right y).bdd_mul (c := 1) ?_ (.of_forall fun z ↦ by simp)
  exact (by fun_prop : Continuous fun z ↦ β y z).aestronglyMeasurable

/-- The Heisenberg operator `ϱ y` on the model, `(ϱ y v) x = β y x * v (x - y)`, as a linear
isometry. -/
private def translate : ReproducingModel β μ e :=
  mk _ (integrable_translate v y) fun x ↦ integral_translate_mul_kernel v x y

private theorem translate_apply : translate v y x = β y x * v (x - y) := mk_apply _ _ _ _

/-- The twisted translation preserves the `L¹` norm, since `μ` is translation invariant. -/
private theorem norm_translate : ‖translate v y‖ = ‖v‖ := by
  rw [norm_eq_integral_norm, norm_eq_integral_norm]
  simp only [translate_apply, norm_mul, β.norm_apply, one_mul]
  exact integral_sub_right_eq_self (fun x ↦ ‖v x‖) y

private def heisenbergIsometry : ReproducingModel β μ e →ₗᵢ[ℂ] ReproducingModel β μ e where
  toFun v := translate v y
  map_add' v w := ext fun x ↦ by simp only [translate_apply, add_apply, mul_add]
  map_smul' c v := ext fun x ↦ by
    rw [translate_apply, smul_apply, smul_apply, translate_apply, RingHom.id_apply, mul_left_comm]
  norm_map' v := norm_translate v y

private theorem heisenbergIsometry_apply : heisenbergIsometry y v x = β y x * v (x - y) :=
  translate_apply v x y

omit [μ.IsAddLeftInvariant] in
/-- *Scheffé's argument* for a family of elements of the model of constant norm: if
`t ↦ ϱ t x` is continuous for every `x`, then `t ↦ ϱ t` is continuous at `a`. The integral of
`‖ϱ t x‖ - ‖ϱ t x - ϱ a x‖` is dominated by `‖ϱ a x‖` and continuous in `t`, and it equals
`‖ϱ a‖ - ‖ϱ t - ϱ a‖`. -/
private theorem tendsto_of_norm_eq [FirstCountableTopology W] (ϱ : W → ReproducingModel β μ e)
    (a : W) (h_norm : ∀ t, ‖ϱ t‖ = ‖ϱ a‖) (h_cont : ∀ x, Continuous fun t ↦ ϱ t x) :
    Tendsto ϱ (𝓝 a) (𝓝 (ϱ a)) := by
  refine tendsto_iff_norm_sub_tendsto_zero.2 ?_
  have h_int (w : ReproducingModel β μ e) : Integrable (fun x ↦ ‖w x‖) μ := w.integrable.norm
  have h_dom : Continuous fun t ↦ ∫ x, ‖ϱ t x‖ - ‖(ϱ t - ϱ a) x‖ ∂μ := by
    refine continuous_of_dominated (fun t ↦ (h_int (ϱ t)).1.sub (h_int (ϱ t - ϱ a)).1)
      (fun t ↦ .of_forall fun x ↦ ?_) (h_int (ϱ a)) (.of_forall fun x ↦ ?_)
    · simpa [Real.norm_eq_abs, sub_apply] using abs_norm_sub_norm_le (ϱ t x) (ϱ t x - ϱ a x)
    · have := h_cont x
      simp only [sub_apply]
      fun_prop
  have h_eq (t : W) : ∫ x, ‖ϱ t x‖ - ‖(ϱ t - ϱ a) x‖ ∂μ = ‖ϱ a‖ - ‖ϱ t - ϱ a‖ := by
    rw [integral_sub (h_int _) (h_int _), ← norm_eq_integral_norm, ← norm_eq_integral_norm,
      h_norm]
  have h := (h_dom.tendsto a).const_sub ‖ϱ a‖
  simp only [h_eq] at h
  simpa only [sub_self, norm_zero, sub_zero, sub_sub_cancel] using h

private theorem continuous_heisenbergIsometry [SecondCountableTopology W] :
    Continuous fun t ↦ heisenbergIsometry (β := β) (μ := μ) (e := e) t v := by
  refine continuous_iff_continuousAt.2 fun a ↦ tendsto_of_norm_eq _ a (fun t ↦ ?_) fun x ↦ ?_
  · simp only [LinearIsometry.norm_map]
  · have := v.continuous
    simp only [heisenbergIsometry_apply]
    fun_prop

variable [SecondCountableTopology W]

/-- The Heisenberg representation of `β` on the model: `(ϱ y v) x = β y x * v (x - y)`. -/
def heisenbergRep : β.Representation (ReproducingModel β μ e) where
  toFun y := (heisenbergIsometry y).toContinuousLinearMap
  apply_apply' x y v := ext fun z ↦ by
    have h_arg : z - x - y = z - (x + y) := by abel
    have h_beta : β y (z - x) = β y z * β x y := by
      rw [sub_eq_add_neg, β.map_add_right, β.apply_neg]
    simp only [LinearIsometry.coe_toContinuousLinearMap, heisenbergIsometry_apply, smul_apply,
      h_arg, h_beta, β.map_add_left]
    ring
  norm_apply' y v := (heisenbergIsometry y).norm_map v
  continuous_uncurry' :=
    continuous_prod_of_continuous_lipschitzWith' _ 1
      (fun y ↦ (heisenbergIsometry y).lipschitzWith) fun v ↦ continuous_heisenbergIsometry v

@[simp]
theorem heisenbergRep_apply : heisenbergRep y v x = β y x * v (x - y) :=
  (rfl)

end HeisenbergOperators

/-! ### The vacuum vector and the evaluations -/

/-- The *vacuum vector*: the vacuum `e` as an element of the model. -/
def vacuum : ReproducingModel β μ e :=
  mk e he.integrable fun x ↦ by simpa [he.apply_zero] using he.integral_mul_apply 0 x

@[simp]
theorem vacuum_apply : (vacuum : ReproducingModel β μ e) x = e x := (rfl)

/-- Evaluation at a point `x`, a bounded linear functional of norm at most one on the model. -/
def evalCLM : ReproducingModel β μ e →L[ℂ] ℂ :=
  LinearMap.mkContinuous { toFun v := v x, map_add' _ _ := rfl, map_smul' _ _ := rfl } 1
    fun v ↦ by rw [one_mul]; exact norm_apply_le v x

@[simp]
theorem evalCLM_apply : evalCLM x v = v x := (rfl)

/-! ### Kernel integrals and the inner product -/

section KernelIntegral

variable [SecondCountableTopology W] {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]
  [NormedAddCommGroup Y] [NormedSpace ℂ Y]

/-- For an isometric ring endomorphism `σ` of `ℂ` and a strongly continuous family of contractions
`K y : X →L[ℂ] Y`, the bounded `σ`-semilinear map `v ↦ (f ↦ ∫ σ (v y) • K y f dμ(y))`. -/
private def kernelIntegral (σ : ℂ →+* ℂ) [RingHomIsometric σ] (K : W → X →L[ℂ] Y)
    (hK : ∀ f, Continuous (K · f)) (hK_le : ∀ y f, ‖K y f‖ ≤ ‖f‖) :
    ReproducingModel β μ e →SL[σ] X →L[ℂ] Y :=
  have h_meas (v : ReproducingModel β μ e) (f : X) :
      AEStronglyMeasurable (fun y ↦ σ (v y) • K y f) μ :=
    (σ.isometry.continuous.comp_aestronglyMeasurable
      v.integrable.1).smul (hK f).aestronglyMeasurable
  have h_le (v : ReproducingModel β μ e) (f : X) (y : W) : ‖σ (v y) • K y f‖ ≤ ‖v y‖ * ‖f‖ := by
    rw [norm_smul, RingHomIsometric.norm_map]
    exact mul_le_mul_of_nonneg_left (hK_le y f) (norm_nonneg _)
  have h_int (v : ReproducingModel β μ e) (f : X) : Integrable (fun y ↦ σ (v y) • K y f) μ :=
    (v.integrable.norm.mul_const ‖f‖).mono' (h_meas v f) (.of_forall (h_le v f))
  LinearMap.mkContinuous₂
    (LinearMap.mk₂'ₛₗ σ (RingHom.id ℂ) (fun v f ↦ ∫ y, σ (v y) • K y f ∂μ)
      (fun v w f ↦ by simp [add_smul, integral_add (h_int v f) (h_int w f)])
      (fun c v f ↦ by simp [← integral_smul, smul_smul])
      (fun v f f' ↦ by simp [integral_add (h_int v f) (h_int v f')])
      (fun c v f ↦ by simp [← integral_smul, smul_comm c]))
    1 fun v f ↦ by
      simpa [norm_eq_integral_norm, integral_mul_const] using
        norm_integral_le_of_norm_le (v.integrable.norm.mul_const ‖f‖) (.of_forall (h_le v f))

private theorem kernelIntegral_apply (σ : ℂ →+* ℂ) [RingHomIsometric σ] (K : W → X →L[ℂ] Y)
    (hK : ∀ f, Continuous (K · f)) (hK_le : ∀ y f, ‖K y f‖ ≤ ‖f‖) (v : ReproducingModel β μ e)
    (f : X) : kernelIntegral σ K hK hK_le v f = ∫ y, σ (v y) • K y f ∂μ := (rfl)

private theorem norm_kernelIntegral_le (σ : ℂ →+* ℂ) [RingHomIsometric σ] (K : W → X →L[ℂ] Y)
    (hK : ∀ f, Continuous (K · f)) (hK_le : ∀ y f, ‖K y f‖ ≤ ‖f‖) (v : ReproducingModel β μ e) :
    ‖kernelIntegral σ K hK hK_le v‖ ≤ ‖v‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg v) fun f ↦ ?_
  rw [kernelIntegral_apply, norm_eq_integral_norm, ← integral_mul_const]
  refine norm_integral_le_of_norm_le (v.integrable.norm.mul_const ‖f‖) (.of_forall fun y ↦ ?_)
  rw [norm_smul, RingHomIsometric.norm_map]
  exact mul_le_mul_of_nonneg_left (hK_le y f) (norm_nonneg _)

end KernelIntegral

variable [SecondCountableTopology W]

/-- The bounded sesquilinear form `⟨v, w⟩ = ∫ conj (v x) * w x dμ(x)` on the model, conjugate-linear
in the first argument. -/
def innerSL : ReproducingModel β μ e →L⋆[ℂ] ReproducingModel β μ e →L[ℂ] ℂ :=
  kernelIntegral (starRingEnd ℂ) evalCLM (fun v ↦ by simpa using v.continuous)
    fun y v ↦ by simpa using norm_apply_le v y

theorem innerSL_apply : innerSL v w = ∫ x, conj (v x) * w x ∂μ := by
  simp [innerSL, kernelIntegral_apply]

theorem conj_innerSL : conj (innerSL v w) = innerSL w v := by
  simp [innerSL_apply, ← integral_conj, mul_comm]

theorem innerSL_self : innerSL v v = ((∫ x, ‖v x‖ ^ 2 ∂μ : ℝ) : ℂ) := by
  simp only [innerSL_apply, RCLike.conj_mul]
  norm_cast

/-- The function `‖v ·‖ ^ 2` is integrable: `v` is integrable and bounded by its norm. -/
theorem integrable_norm_sq : Integrable (fun x ↦ ‖v x‖ ^ 2) μ := by
  refine (v.integrable.norm.mul_const ‖v‖).mono' (by fun_prop) (.of_forall fun y ↦ ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), sq]
  exact mul_le_mul_of_nonneg_left (norm_apply_le v y) (norm_nonneg _)

/-- The form `⟨·, ·⟩` is definite. -/
theorem eq_zero_of_innerSL_self {v : ReproducingModel β μ e} (h : innerSL v v = 0) : v = 0 := by
  -- `v` vanishes almost everywhere, hence everywhere by the reproducing identity.
  have h_int : ∫ y, ‖v y‖ ^ 2 ∂μ = 0 := by exact_mod_cast (innerSL_self v).symm.trans h
  have h_ae : (v : W → ℂ) =ᵐ[μ] 0 :=
    ((integral_eq_zero_iff_of_nonneg (fun y ↦ sq_nonneg ‖v y‖) (integrable_norm_sq v)).1
      h_int).mono fun y hy ↦ by simpa using hy
  ext x
  rw [← v.integral_mul_kernel, zero_apply]
  exact (integral_congr_ae (h_ae.mono fun y hy ↦ by simp [hy])).trans (integral_zero W ℂ)

section Inner

variable [μ.IsAddLeftInvariant]

/-- The Heisenberg operators preserve `⟨·, ·⟩`. -/
theorem innerSL_heisenbergRep :
    innerSL (heisenbergRep x v) (heisenbergRep x w) = innerSL v w := by
  have h_point (y : W) : conj (β x y * v (y - x)) * (β x y * w (y - x)) =
      conj (v (y - x)) * w (y - x) := by
    rw [map_mul, β.conj_apply, mul_mul_mul_comm, β.apply_mul_apply_swap, one_mul]
  simp only [innerSL_apply, heisenbergRep_apply, h_point]
  exact integral_sub_right_eq_self (fun y ↦ conj (v y) * w y) x

/-- The reproducing property `⟨ϱ x e, v⟩ = v x`. -/
@[simp]
theorem innerSL_heisenbergRep_vacuum : innerSL (heisenbergRep x vacuum) v = v x := by
  have h_point (y : W) : conj (β x y * e (y - x)) * v y = v y * (β y x * e (x - y)) := by
    rw [map_mul, β.conj_apply, he.conj_apply, ← he.apply_neg (y - x), neg_sub]
    ring
  simp only [innerSL_apply, heisenbergRep_apply, vacuum_apply, h_point]
  exact v.integral_mul_kernel x

/-- The pairing of the vacuum vector with `v` is `v 0`. -/
@[simp]
theorem innerSL_vacuum : innerSL vacuum v = v 0 := by
  simpa using innerSL_heisenbergRep_vacuum v 0

end Inner

end ReproducingModel

/-! ### The integrated action -/

namespace HeisenbergDatum.Representation

variable [SecondCountableTopology W] [he : β.IsVacuum μ e]
  {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
  [NormedAddCommGroup Y] [NormedSpace ℂ Y] [CompleteSpace Y]
  (ϱ : β.Representation X) (T : X →L[ℂ] Y) (v : ReproducingModel β μ e) (f : X) (x : W)

variable (μ e) in
/-- The *integrated action* of the reproducing model on a representation `ϱ` of `β` on a Banach
space `X`: the bounded bilinear map `(v, f) ↦ ∫ v y • ϱ y f dμ(y)`. -/
def integrated : ReproducingModel β μ e →L[ℂ] X →L[ℂ] X :=
  ReproducingModel.kernelIntegral (RingHom.id ℂ) ϱ (fun f ↦ by fun_prop)
    fun y f ↦ (ϱ.norm_apply y f).le

omit [CompleteSpace X] in
theorem integrated_apply : ϱ.integrated μ e v f = ∫ y, v y • ϱ y f ∂μ :=
  ReproducingModel.kernelIntegral_apply _ _ _ _ v f

omit [CompleteSpace X] in
theorem norm_integrated_le : ‖ϱ.integrated μ e v‖ ≤ ‖v‖ :=
  ReproducingModel.norm_kernelIntegral_le _ _ _ _ v

omit [CompleteSpace X] in
theorem integrable_smul_apply : Integrable (fun y ↦ v y • ϱ y f) μ :=
  v.integrable.smul_bdd ‖f‖ (by fun_prop) (.of_forall fun y ↦ (ϱ.norm_apply y f).le)

/-- A bounded operator passes under the integral that defines the integrated action. -/
theorem map_integrated : T (ϱ.integrated μ e v f) = ∫ y, v y • T (ϱ y f) ∂μ := by
  simp_rw [integrated_apply, ← T.integral_comp_comm (ϱ.integrable_smul_apply v f), map_smul]

/-- A bounded operator that intertwines two representations intertwines their integrated
actions. -/
theorem map_integrated_of_intertwines {ϱ' : β.Representation Y}
    (hT : ∀ y f, T (ϱ y f) = ϱ' y (T f)) :
    T (ϱ.integrated μ e v f) = ϱ'.integrated μ e v (T f) := by
  simp_rw [map_integrated, hT, integrated_apply]

/-- The integrated action turns the Heisenberg operator `ϱ x` of the model into `ϱ x`. -/
@[simp]
theorem integrated_heisenbergRep [μ.IsAddLeftInvariant] :
    ϱ.integrated μ e (ReproducingModel.heisenbergRep x v) f = ϱ x (ϱ.integrated μ e v f) := by
  have h_point (y : W) : ReproducingModel.heisenbergRep x v (x + y) • ϱ (x + y) f =
      v y • ϱ x (ϱ y f) := by
    rw [ReproducingModel.heisenbergRep_apply, add_sub_cancel_left, ϱ.apply_apply, smul_smul,
      β.map_add_right, β.apply_self, one_mul, mul_comm]
  rw [map_integrated, integrated_apply, ← integral_add_left_eq_self _ x]
  exact integral_congr_ae (.of_forall h_point)

end HeisenbergDatum.Representation

namespace ReproducingModel

variable [SecondCountableTopology W] [he : β.IsVacuum μ e]
  {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
  (v w : ReproducingModel β μ e) (x : W)

open HeisenbergDatum.Representation

/-- For a representation on the model itself, the value at `x` of the integrated action of `v`
on `w` is `∫ v y * (ϱ y w) x dμ(y)`. -/
theorem integrated_apply_apply (ϱ : β.Representation (ReproducingModel β μ e)) :
    ϱ.integrated μ e v w x = ∫ y, v y * ϱ y w x ∂μ :=
  ϱ.map_integrated (evalCLM x) v w

section Invariant

variable [μ.IsAddLeftInvariant]

/-- The integrated action of `v` on the vacuum vector is `v`: the reproducing identity in operator
form. -/
theorem integrated_vacuum :
    (heisenbergRep (β := β) (μ := μ) (e := e)).integrated μ e v vacuum = v := by
  ext x
  simpa [integrated_apply_apply] using v.integral_mul_kernel x

/-- *Superposition*: every bounded linear map `T` out of the model satisfies
`T v = ∫ v y • T (ϱ y e) dμ(y)`. -/
theorem map_eq_integral (T : ReproducingModel β μ e →L[ℂ] X) :
    T v = ∫ y, v y • T (heisenbergRep y vacuum) ∂μ := by
  rw [← map_integrated, integrated_vacuum]

/-- Two bounded linear maps out of the model that agree on the translates `ϱ y e` of the vacuum
vector are equal. -/
theorem hom_ext {L L' : ReproducingModel β μ e →L[ℂ] X}
    (h : ∀ y, L (heisenbergRep y vacuum) = L' (heisenbergRep y vacuum)) : L = L' := by
  ext v
  simp_rw [map_eq_integral v, h]

/-- The integrated action of the model on itself: `∫ v y • ϱ y w dμ(y) = w 0 • v`. This is a
special case of the orthogonality relations of the Heisenberg representation. -/
@[simp]
theorem integrated_eq_smul :
    (heisenbergRep (β := β) (μ := μ) (e := e)).integrated μ e v w = w 0 • v := by
  -- Both sides are bounded and bilinear, so it suffices to take translates of the vacuum for
  -- `v` and `w`; then the value is the twisted convolution identity of the vacuum.
  have h_vac (y : W) : (heisenbergRep (β := β) (μ := μ) (e := e)).integrated μ e
      (heisenbergRep y vacuum) = (evalCLM 0).smulRight (heisenbergRep y vacuum) := by
    refine hom_ext fun z ↦ ext fun x ↦ ?_
    rw [integrated_apply_apply, ContinuousLinearMap.smulRight_apply, evalCLM_apply, smul_apply]
    simp only [heisenbergRep_apply, vacuum_apply, β.apply_zero, one_mul, zero_sub, he.apply_neg]
    rw [mul_left_comm, ← he.integral_mul_apply z (x - y), ← integral_const_mul,
      ← integral_add_right_eq_self _ y]
    refine integral_congr_ae (.of_forall fun w ↦ ?_)
    have h_arg : x - (w + y) - z = x - y - (w + z) := by abel
    simp only [add_sub_cancel_right, h_arg, β.map_sub_right, β.map_add_left, β.map_add_right,
      β.apply_self]
    ring
  have h : ((heisenbergRep (β := β) (μ := μ) (e := e)).integrated μ e).flip w =
      w 0 • ContinuousLinearMap.id ℂ _ := hom_ext fun y ↦ by
    rw [ContinuousLinearMap.flip_apply, h_vac]
    simp
  simpa using congr($h v)

/-- *Schur's lemma*: a bounded operator on the model that commutes with every Heisenberg operator
is the scalar `(T e) 0`. -/
theorem eq_smul_one_of_commute (T : ReproducingModel β μ e →L[ℂ] ReproducingModel β μ e)
    (hT : ∀ y, Commute T (heisenbergRep y)) : T = T vacuum 0 • 1 := by
  ext1 v
  calc T v = T ((heisenbergRep (β := β) (μ := μ) (e := e)).integrated μ e v vacuum) := by
        rw [integrated_vacuum]
    _ = (heisenbergRep (β := β) (μ := μ) (e := e)).integrated μ e v (T vacuum) :=
        map_integrated_of_intertwines _ T v vacuum fun y f ↦ DFunLike.congr_fun (hT y).eq f
    _ = T vacuum 0 • v := integrated_eq_smul v (T vacuum)

/-- *Superposition*: a bounded continuous map `K : W → X` defines a bounded linear map `L` out of
the model that behaves as if it sent `ϱ y e` to `K y`: if bounded maps `A` on `X` and `B` on the
model satisfy `A (K y) = B (ϱ y e)` for every `y`, then `A ∘ L = B`. (In the proof,
`L v = ∫ v y • K y dμ(y)`.) -/
theorem exists_lift {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℂ Y] [CompleteSpace Y]
    {K : W → X} (hK : Continuous K) {C : ℝ} (hC : ∀ y, ‖K y‖ ≤ C) :
    ∃ L : ReproducingModel β μ e →L[ℂ] X, ∀ (A : X →L[ℂ] Y) (B : ReproducingModel β μ e →L[ℂ] Y),
      (∀ y, A (K y) = B (heisenbergRep y vacuum)) → ∀ v, A (L v) = B v := by
  have h_int (v : ReproducingModel β μ e) :
      Integrable (fun y ↦ (evalCLM y).smulRight (K y) v) μ := by
    refine (v.integrable.smul_bdd C hK.aestronglyMeasurable (.of_forall hC)).congr
      (.of_forall fun y ↦ ?_)
    simp
  obtain ⟨L, hL⟩ := ContinuousLinearMap.exists_apply_eq_integral h_int
  refine ⟨L, fun A B hAB v ↦ ?_⟩
  rw [hL, ← A.integral_comp_comm (h_int v), map_eq_integral v B]
  refine integral_congr_ae (.of_forall fun y ↦ ?_)
  simp [hAB]

/-- Moving a Heisenberg operator from the second argument of an invariant integral of forms to
the first. -/
private theorem integral_form_heisenbergRep_right {Z : Type*} [MeasurableSpace Z] {ν : Measure Z}
    (B : Z → ReproducingModel β μ e →L⋆[ℂ] ReproducingModel β μ e →L[ℂ] ℂ)
    (hB_inv : ∀ x f g, ∫ z, B z (heisenbergRep x f) (heisenbergRep x g) ∂ν = ∫ z, B z f g ∂ν)
    (f u : ReproducingModel β μ e) (x : W) :
    ∫ z, B z f (heisenbergRep x u) ∂ν = ∫ z, B z (heisenbergRep (-x) f) u ∂ν := by
  simpa using hB_inv x (heisenbergRep (-x) f) u

end Invariant

section Forms

variable [LocallyCompactSpace W] [μ.IsAddHaarMeasure]

/-- The key step of Schur's lemma for an invariant integral of forms: its value against the vacuum
vector in the second argument is `(∫ B z e e dν(z)) * conj (f 0)`. -/
private theorem integral_form_vacuum {Z : Type*} [MeasurableSpace Z] {ν : Measure Z}
    (B : Z → ReproducingModel β μ e →L⋆[ℂ] ReproducingModel β μ e →L[ℂ] ℂ)
    (hB_int : ∀ v w, Integrable (fun z ↦ B z v w) ν)
    (hB_inv : ∀ x f g, ∫ z, B z (heisenbergRep x f) (heisenbergRep x g) ∂ν = ∫ z, B z f g ∂ν)
    (f : ReproducingModel β μ e) :
    ∫ z, B z f vacuum ∂ν = (∫ z, B z vacuum vacuum ∂ν) * conj (f 0) := by
  -- `f ↦ conj (∫ B z f e dν(z))` is a bounded linear functional `T`.
  obtain ⟨T, hT⟩ := ContinuousLinearMap.exists_apply_eq_integral
    (F := fun z ↦ ((starL ℂ : ℂ ≃L⋆[ℂ] ℂ) : ℂ →L⋆[ℂ] ℂ).comp ((B z).flip vacuum)) fun f ↦ by
      simpa using Complex.conjCLE.toContinuousLinearMap.integrable_comp (hB_int f vacuum)
  have hT' (f : ReproducingModel β μ e) : T f = conj (∫ z, B z f vacuum ∂ν) := by
    simp [hT, integral_conj]
  obtain ⟨S, hS⟩ := ContinuousLinearMap.exists_apply_eq_integral (hB_int f)
  apply (starRingEnd ℂ).injective
  calc conj (∫ z, B z f vacuum ∂ν)
    _ = conj (∫ y, e y * ∫ z, B z (heisenbergRep y f) vacuum ∂ν ∂μ) := by
      rw [← hS, map_eq_integral vacuum S, ← integral_neg_eq_self]
      simp [hS, integral_form_heisenbergRep_right B hB_inv, he.apply_neg]
    _ = T ((heisenbergRep (β := β) (μ := μ) (e := e)).integrated μ e vacuum f) := by
      rw [HeisenbergDatum.Representation.map_integrated, ← integral_conj]
      simp [hT', he.conj_apply]
    _ = conj ((∫ z, B z vacuum vacuum ∂ν) * conj (f 0)) := by
      simp [hT', mul_comm, integral_const_mul]

/-- *Schur's lemma* for an integral of forms: if `B z` (`z ∈ Z`) are bounded sesquilinear forms on
the model with each `z ↦ B z v w` integrable and `∫ B z dν(z)` invariant under the Heisenberg
operators, then `∫ B z v w dν(z) = (∫ B z e e dν(z)) * ⟨v, w⟩`. -/
theorem integral_form_eq_mul_innerSL {Z : Type*} [MeasurableSpace Z] {ν : Measure Z}
    (B : Z → ReproducingModel β μ e →L⋆[ℂ] ReproducingModel β μ e →L[ℂ] ℂ)
    (hB_int : ∀ v w, Integrable (fun z ↦ B z v w) ν)
    (hB_inv : ∀ x f g, ∫ z, B z (heisenbergRep x f) (heisenbergRep x g) ∂ν = ∫ z, B z f g ∂ν)
    (v w : ReproducingModel β μ e) :
    ∫ z, B z v w ∂ν = (∫ z, B z vacuum vacuum ∂ν) * innerSL v w := by
  obtain ⟨S, hS⟩ := ContinuousLinearMap.exists_apply_eq_integral (hB_int v)
  have h : S = (∫ z, B z vacuum vacuum ∂ν) • innerSL v := hom_ext fun y ↦ by
    rw [hS, integral_form_heisenbergRep_right B hB_inv, integral_form_vacuum B hB_int hB_inv,
      _root_.smul_apply, smul_eq_mul, ← conj_innerSL, innerSL_heisenbergRep_vacuum]
    simp
  rw [← hS, h, _root_.smul_apply, smul_eq_mul]

/-- *Schur's lemma* for a form: a bounded sesquilinear form `B` on the model that is invariant
under the Heisenberg operators is `B e e * ⟨·, ·⟩`. -/
theorem form_eq_mul_innerSL (B : ReproducingModel β μ e →L⋆[ℂ] ReproducingModel β μ e →L[ℂ] ℂ)
    (hB_inv : ∀ x f g, B (heisenbergRep x f) (heisenbergRep x g) = B f g)
    (v w : ReproducingModel β μ e) : B v w = B vacuum vacuum * innerSL v w := by
  simpa using integral_form_eq_mul_innerSL (ν := .dirac ()) (fun _ : Unit ↦ B)
    (fun f g ↦ integrable_const (B f g)) (by simpa using hB_inv) v w

end Forms

end ReproducingModel

end TauCeti
