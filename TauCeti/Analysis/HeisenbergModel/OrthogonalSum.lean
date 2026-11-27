/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.HeisenbergModel.WeilOperators
public import Mathlib.Topology.Algebra.ContinuousMonoidHom
import Mathlib.MeasureTheory.Integral.Prod
import TauCeti.MeasureTheory.Measure.Haar.IntegralUnique
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Analysis.Complex.Basic

/-!
# Orthogonal sums and transport of reproducing models

An *orthogonal sum* of Heisenberg data with vacua is an isomorphism of topological groups
`φ : W₁ × W₂ ≃ W` under which the Heisenberg datum and the vacuum of `W` are the products of those
of `W₁` and `W₂`. Then `e` is a vacuum for the image of `μ₁ × μ₂`, which is the Haar measure for
which `e` is a vacuum, and the tensor product `(v ⊗ w) (φ (x₁, x₂)) = v x₁ * w x₂` is a bounded
bilinear map `M(β₁, e₁) × M(β₂, e₂) → M(β, e)`, multiplicative for norms and for `⟨·, ·⟩`,
compatible with the Heisenberg operators and with the Weil representations of product actions.

Along an isomorphism `φ : W' ≃ W` that matches the vacua and, up to the identity or complex
conjugation `σ`, the Heisenberg data, `v ↦ σ ∘ v ∘ φ` is a norm-preserving `σ`-semilinear map of
reproducing models (`TauCeti.ReproducingModel.transport`).

## Main definitions

* `TauCeti.HeisenbergDatum.OrthogonalSum`: an orthogonal sum of Heisenberg data with vacua.
* `TauCeti.HeisenbergDatum.OrthogonalSum.tmul`: the tensor product of model vectors.
* `TauCeti.ReproducingModel.transport`: transport of the model along an isomorphism.

## Main results

* `TauCeti.HeisenbergDatum.OrthogonalSum.isVacuum`,
  `TauCeti.HeisenbergDatum.OrthogonalSum.measurePreserving_equiv`: the product vacuum and its
  measure.
* `TauCeti.HeisenbergDatum.OrthogonalSum.tmul_apply`,
  `TauCeti.HeisenbergDatum.OrthogonalSum.norm_tmul`,
  `TauCeti.HeisenbergDatum.OrthogonalSum.innerSL_tmul`,
  `TauCeti.HeisenbergDatum.OrthogonalSum.tmul_vacuum`,
  `TauCeti.HeisenbergDatum.OrthogonalSum.heisenbergRep_tmul`,
  `TauCeti.HeisenbergDatum.OrthogonalSum.weilRep_tmul`,
  `TauCeti.HeisenbergDatum.OrthogonalSum.exists_restriction`: the tensor product.
* `TauCeti.ReproducingModel.norm_transport`: transport preserves norms.

## Provenance

Adapted from grh-lean (https://github.com/lsernau/grh-lean, Apache 2.0, Copyright 2026
Anthropic, PBC), file `src/Lib/Weil/Construction/WeilOperators.lean`
(`New.Heisenberg.OrthogonalSum` with `isVacuum`, `measurePreserving_equiv`, `tmul`, `tmul_apply`,
`modelInner_tmul`, `norm_tmul`, `weilRep_tmul`, `tmul_vacElem`, `heisenbergOp_tmul`,
`exists_restriction`, `New.Heisenberg.Rep.integrated_tmul`, `New.Heisenberg.IsVacuum.transport`,
`New.Heisenberg.IsVacuum.norm_transport`). The Haar normalisation step
(`New.addHaar_eq_of_integral_eq_one` in `src/Lib/General/Measure/HaarNormalisation.lean`) is
`MeasureTheory.Measure.eq_addHaar_of_integral_eq` in
`TauCeti/MeasureTheory/Measure/Haar/IntegralUnique.lean`.
-/

public noncomputable section

open MeasureTheory Measure
open scoped ComplexConjugate

namespace TauCeti

namespace HeisenbergDatum

variable {W W₁ W₂ : Type*} [AddCommGroup W] [TopologicalSpace W] [AddCommGroup W₁]
  [TopologicalSpace W₁] [AddCommGroup W₂] [TopologicalSpace W₂]

/-- An *orthogonal sum* of Heisenberg data with vacua: an isomorphism of topological groups
`φ : W₁ × W₂ ≃ W` with `β (φ x) (φ y) = β₁ x.1 y.1 * β₂ x.2 y.2` and
`e (φ x) = e₁ x.1 * e₂ x.2`. -/
structure OrthogonalSum (β : HeisenbergDatum W) (β₁ : HeisenbergDatum W₁)
    (β₂ : HeisenbergDatum W₂) (e : W → ℂ) (e₁ : W₁ → ℂ) (e₂ : W₂ → ℂ) where
  /-- The isomorphism `W₁ × W₂ ≃ W`. -/
  equiv : W₁ × W₂ ≃ₜ+ W
  apply_equiv_equiv (x y : W₁ × W₂) : β (equiv x) (equiv y) = β₁ x.1 y.1 * β₂ x.2 y.2
  vacuum_equiv (x : W₁ × W₂) : e (equiv x) = e₁ x.1 * e₂ x.2

namespace Representation

variable {β : HeisenbergDatum W} {β₁ : HeisenbergDatum W₁} {β₂ : HeisenbergDatum W₂}
  {e : W → ℂ} {e₁ : W₁ → ℂ} {e₂ : W₂ → ℂ} {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]
  (ϱ : β.Representation X) (S : β.OrthogonalSum β₁ β₂ e e₁ e₂)

/-- The restriction `x ↦ ϱ (φ (x, 0))` of a representation to the first summand. -/
def restrictLeft : β₁.Representation X where
  toFun x := ϱ (S.equiv (x, 0))
  apply_apply' x y v := by
    rw [ϱ.apply_apply, S.apply_equiv_equiv, β₂.apply_self, mul_one, ← map_add, Prod.mk_add_mk,
      add_zero]
  norm_apply' x v := ϱ.norm_apply _ v
  continuous_uncurry' := by fun_prop

/-- The restriction `x ↦ ϱ (φ (0, x))` of a representation to the second summand. -/
def restrictRight : β₂.Representation X where
  toFun x := ϱ (S.equiv (0, x))
  apply_apply' x y v := by
    rw [ϱ.apply_apply, S.apply_equiv_equiv, β₁.apply_self, one_mul, ← map_add, Prod.mk_add_mk,
      add_zero]
  norm_apply' x v := ϱ.norm_apply _ v
  continuous_uncurry' := by fun_prop

@[simp]
theorem restrictLeft_apply (x : W₁) (v : X) : ϱ.restrictLeft S x v = ϱ (S.equiv (x, 0)) v := (rfl)

@[simp]
theorem restrictRight_apply (x : W₂) (v : X) : ϱ.restrictRight S x v = ϱ (S.equiv (0, x)) v :=
  (rfl)

theorem restrictLeft_apply_restrictRight_apply (a : W₁) (b : W₂) (v : X) :
    ϱ.restrictLeft S a (ϱ.restrictRight S b v) = ϱ (S.equiv (a, b)) v := by
  rw [restrictLeft_apply, restrictRight_apply, ϱ.apply_apply, S.apply_equiv_equiv, ← map_add,
    Prod.mk_add_mk, add_zero, zero_add]
  simp

end Representation

namespace OrthogonalSum

variable [MeasurableSpace W] [IsTopologicalAddGroup W] [BorelSpace W] [SecondCountableTopology W]
  [MeasurableSpace W₁] [IsTopologicalAddGroup W₁] [BorelSpace W₁] [SecondCountableTopology W₁]
  [MeasurableSpace W₂] [IsTopologicalAddGroup W₂] [BorelSpace W₂] [SecondCountableTopology W₂]
  {β : HeisenbergDatum W} {β₁ : HeisenbergDatum W₁} {β₂ : HeisenbergDatum W₂}
  {μ : Measure W} {μ₁ : Measure W₁} {μ₂ : Measure W₂} {e : W → ℂ} {e₁ : W₁ → ℂ} {e₂ : W₂ → ℂ}
  (S : β.OrthogonalSum β₁ β₂ e e₁ e₂)

omit [IsTopologicalAddGroup W₁] [SecondCountableTopology W₁] [IsTopologicalAddGroup W₂] in
/-- The product of two vacua is a vacuum for the image of the product measure. -/
theorem isVacuum [SFinite μ₁] [SFinite μ₂] (h₁ : β₁.IsVacuum μ₁ e₁) (h₂ : β₂.IsVacuum μ₂ e₂) :
    β.IsVacuum ((μ₁.prod μ₂).map S.equiv) e := by
  have he_eq : e = (fun x : W₁ × W₂ ↦ e₁ x.1 * e₂ x.2) ∘ S.equiv.symm :=
    funext fun x ↦ by rw [Function.comp_apply, ← S.vacuum_equiv, S.equiv.apply_symm_apply]
  have h_cont₁ := h₁.continuous
  have h_cont₂ := h₂.continuous
  have h_cont : Continuous e := by rw [he_eq]; fun_prop
  refine
    { continuous := h_cont
      apply_zero := by simp [he_eq, h₁.apply_zero, h₂.apply_zero]
      apply_neg := by simp [he_eq, h₁.apply_neg, h₂.apply_neg]
      conj_apply := by simp [he_eq, h₁.conj_apply, h₂.conj_apply]
      integrable := ?_
      integral_mul_apply := S.equiv.surjective.forall₂.mpr fun y x ↦ ?_ }
  · rw [integrable_map_measure (by fun_prop) (by fun_prop)]
    simpa [Function.comp_def, S.vacuum_equiv] using h₁.integrable.mul_prod h₂.integrable
  · -- The twisted convolution over the product is the product of the two convolutions.
    rw [integral_map (by fun_prop) (by fun_prop), S.vacuum_equiv, S.vacuum_equiv,
      mul_mul_mul_comm, ← h₁.integral_mul_apply, ← h₂.integral_mul_apply, ← integral_prod_mul]
    refine integral_congr_ae (.of_forall fun z ↦ ?_)
    simp only [← map_sub, ← map_add, S.vacuum_equiv, S.apply_equiv_equiv, Prod.fst_add,
      Prod.snd_add, Prod.fst_sub, Prod.snd_sub]
    ring

section Haar

variable [LocallyCompactSpace W] [LocallyCompactSpace W₁] [LocallyCompactSpace W₂]
  [μ.IsAddHaarMeasure] [μ₁.IsAddHaarMeasure] [μ₂.IsAddHaarMeasure]

/-- A vacuum fixes the normalisation of the Haar measure, so the isomorphism of an orthogonal sum
carries `μ₁ × μ₂` to `μ`. -/
theorem measurePreserving_equiv [he : β.IsVacuum μ e] [h₁ : β₁.IsVacuum μ₁ e₁]
    [h₂ : β₂.IsVacuum μ₂ e₂] : MeasurePreserving S.equiv (μ₁.prod μ₂) μ where
  measurable := by fun_prop
  map_eq := eq_addHaar_of_integral_eq
    ((S.isVacuum h₁ h₂).integral_norm_sq_eq_one.trans he.integral_norm_sq_eq_one.symm)
    (by rw [he.integral_norm_sq_eq_one]; exact one_ne_zero)

theorem integral_eq_integral_prod [β.IsVacuum μ e] [β₁.IsVacuum μ₁ e₁] [β₂.IsVacuum μ₂ e₂]
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] (f : W → X) :
    ∫ x, f x ∂μ = ∫ x : W₁ × W₂, f (S.equiv x) ∂μ₁.prod μ₂ :=
  (S.measurePreserving_equiv.integral_comp' (f := S.equiv.toMeasurableEquiv) f).symm

end Haar

/-! ### The tensor product -/

section TensorProduct

open ReproducingModel HeisenbergDatum.Representation

variable [μ.IsAddHaarMeasure] [μ₁.IsAddHaarMeasure] [μ₂.IsAddHaarMeasure] [he : β.IsVacuum μ e]
  [h₁ : β₁.IsVacuum μ₁ e₁] [h₂ : β₂.IsVacuum μ₂ e₂] (v v' : ReproducingModel β₁ μ₁ e₁)
  (w w' : ReproducingModel β₂ μ₂ e₂)

variable (μ) in
/-- The *tensor product* of model vectors along an orthogonal sum, the bounded bilinear map
`(v, w) ↦ ∫∫ v y₁ * w y₂ • ϱ (φ (y₁, y₂)) e dμ₂(y₂) dμ₁(y₁)`. As a function it is
`φ (x₁, x₂) ↦ v x₁ * w x₂` (`TauCeti.HeisenbergDatum.OrthogonalSum.tmul_apply`). The measure `μ`
of the target model is explicit. -/
def tmul :
    ReproducingModel β₁ μ₁ e₁ →L[ℂ] ReproducingModel β₂ μ₂ e₂ →L[ℂ] ReproducingModel β μ e :=
  ((((heisenbergRep (β := β) (μ := μ) (e := e)).restrictLeft S).integrated μ₁ e₁).flip ∘L
    (((heisenbergRep (β := β) (μ := μ) (e := e)).restrictRight S).integrated μ₂ e₂).flip
      vacuum).flip

omit [μ₁.IsAddHaarMeasure] [μ₂.IsAddHaarMeasure] in
private theorem tmul_eq : S.tmul μ v w =
    ((heisenbergRep (β := β) (μ := μ) (e := e)).restrictLeft S).integrated μ₁ e₁ v
      (((heisenbergRep (β := β) (μ := μ) (e := e)).restrictRight S).integrated μ₂ e₂ w vacuum) :=
  (rfl)

omit [μ₁.IsAddHaarMeasure] [μ₂.IsAddHaarMeasure] in
/-- The tensor product is the product of functions: `(v ⊗ w) (φ (x₁, x₂)) = v x₁ * w x₂`. -/
theorem tmul_apply (x : W) : S.tmul μ v w x = v (S.equiv.symm x).1 * w (S.equiv.symm x).2 := by
  obtain ⟨⟨a, b⟩, rfl⟩ := S.equiv.surjective x
  rw [S.equiv.symm_apply_apply]
  set ϱ := heisenbergRep (β := β) (μ := μ) (e := e)
  -- A translate of the vacuum by `φ (y₁, y₂)` is the product of the two reproducing kernels.
  have h_kernel (y₁ : W₁) (y₂ : W₂) :
      ϱ.restrictLeft S y₁ (ϱ.restrictRight S y₂ vacuum) (S.equiv (a, b)) =
        β₁ y₁ a * e₁ (a - y₁) * (β₂ y₂ b * e₂ (b - y₂)) := by
    rw [restrictLeft_apply_restrictRight_apply, heisenbergRep_apply, vacuum_apply, ← map_sub,
      S.apply_equiv_equiv, S.vacuum_equiv]
    simp only [Prod.mk_sub_mk]
    ring
  have h_inner (y₂ : W₂) :
      (ϱ.restrictLeft S).integrated μ₁ e₁ v (ϱ.restrictRight S y₂ vacuum) (S.equiv (a, b)) =
        v a * (β₂ y₂ b * e₂ (b - y₂)) := by
    rw [← evalCLM_apply, map_integrated, ← v.integral_mul_kernel a, ← integral_mul_const]
    simp_rw [evalCLM_apply, h_kernel, smul_eq_mul, mul_assoc]
  calc S.tmul μ v w (S.equiv (a, b))
    _ = ∫ y₂, w y₂ * (ϱ.restrictLeft S).integrated μ₁ e₁ v
          (ϱ.restrictRight S y₂ vacuum) (S.equiv (a, b)) ∂μ₂ := by
      rw [tmul_eq, ← evalCLM_apply,
        ← ContinuousLinearMap.comp_apply (evalCLM _) ((ϱ.restrictLeft S).integrated μ₁ e₁ v),
        map_integrated]
      simp only [evalCLM_apply, ContinuousLinearMap.comp_apply, smul_eq_mul, restrictRight_apply]
      rfl
    _ = v a * ∫ y₂, w y₂ * (β₂ y₂ b * e₂ (b - y₂)) ∂μ₂ := by
      simp_rw [h_inner, ← integral_const_mul, mul_left_comm (v a)]
    _ = v a * w b := by rw [w.integral_mul_kernel b]

omit [μ₁.IsAddHaarMeasure] [μ₂.IsAddHaarMeasure] in
/-- The tensor product of the two vacuum vectors is the vacuum vector. -/
@[simp]
theorem tmul_vacuum :
    S.tmul μ (vacuum : ReproducingModel β₁ μ₁ e₁) (vacuum : ReproducingModel β₂ μ₂ e₂) =
      (vacuum : ReproducingModel β μ e) := by
  ext x
  obtain ⟨y, rfl⟩ := S.equiv.surjective x
  simp [tmul_apply, S.vacuum_equiv]

/-- The Heisenberg operators act factorwise on tensor products:
`ϱ x (v ⊗ w) = ϱ (φ⁻¹ x).1 v ⊗ ϱ (φ⁻¹ x).2 w`. -/
theorem heisenbergRep_tmul (x : W) :
    heisenbergRep x (S.tmul μ v w) =
      S.tmul μ (heisenbergRep (S.equiv.symm x).1 v) (heisenbergRep (S.equiv.symm x).2 w) := by
  ext z
  obtain ⟨⟨a, b⟩, rfl⟩ := S.equiv.surjective x
  obtain ⟨⟨c, d⟩, rfl⟩ := S.equiv.surjective z
  simp only [heisenbergRep_apply, tmul_apply, ← map_sub, S.equiv.symm_apply_apply,
    S.apply_equiv_equiv, Prod.mk_sub_mk]
  ring

/-- A translate of the vacuum vector is the tensor product of translates of the two vacua. -/
theorem heisenbergRep_equiv_vacuum (a : W₁) (b : W₂) :
    heisenbergRep (S.equiv (a, b)) (vacuum : ReproducingModel β μ e) =
      S.tmul μ (heisenbergRep a (vacuum : ReproducingModel β₁ μ₁ e₁))
        (heisenbergRep b (vacuum : ReproducingModel β₂ μ₂ e₂)) := by
  rw [← S.tmul_vacuum (μ := μ) (μ₁ := μ₁) (μ₂ := μ₂), heisenbergRep_tmul, S.equiv.symm_apply_apply]

/-- *Restriction to the second summand*: `r u b = u (φ (0, b))` is a bounded map from the model of
`e` to the model of `e₂`, and `∫ v y • ϱ (φ (y, 0)) u dμ₁(y) = v ⊗ r u`. -/
theorem exists_restriction :
    ∃ r : ReproducingModel β μ e →L[ℂ] ReproducingModel β₂ μ₂ e₂,
      (∀ u b, r u b = u (S.equiv (0, b))) ∧
      ∀ v u, ((heisenbergRep (β := β) (μ := μ) (e := e)).restrictLeft S).integrated μ₁ e₁ v u =
        S.tmul μ v (r u) := by
  -- Translates of the vacuum are tensor products, so their restrictions `K y` are bounded, and
  -- superposition gives `r`. On tensor products the formula is `integrated_eq_smul`.
  let K (y : W) : ReproducingModel β₂ μ₂ e₂ :=
    (heisenbergRep (S.equiv.symm y).1 (vacuum : ReproducingModel β₁ μ₁ e₁)) 0 •
      heisenbergRep (S.equiv.symm y).2 vacuum
  have hK_bound (y : W) : ‖K y‖ ≤
      ‖(vacuum : ReproducingModel β₁ μ₁ e₁)‖ * ‖(vacuum : ReproducingModel β₂ μ₂ e₂)‖ := by
    simp only [K, norm_smul, Representation.norm_apply]
    exact mul_le_mul_of_nonneg_right
      ((norm_apply_le _ 0).trans (Representation.norm_apply _ _ _).le) (norm_nonneg _)
  have h_cont : Continuous e₁ := h₁.continuous
  have hK_cont : Continuous K := by
    simp only [K, heisenbergRep_apply, vacuum_apply]
    fun_prop
  obtain ⟨r, hr⟩ := exists_lift (β := β) (μ := μ) (e := e) (Y := ℂ) hK_cont hK_bound
  have h_apply (u : ReproducingModel β μ e) (b : W₂) : r u b = u (S.equiv (0, b)) := by
    have h := hr (evalCLM b) (evalCLM (S.equiv (0, b))) (S.equiv.surjective.forall.mpr
      fun ⟨a, c⟩ ↦ by
        simp only [K, S.heisenbergRep_equiv_vacuum (μ₁ := μ₁) (μ₂ := μ₂), evalCLM_apply,
          ReproducingModel.smul_apply, tmul_apply, S.equiv.symm_apply_apply]) u
    simpa using h
  refine ⟨r, h_apply, fun v u ↦ ?_⟩
  -- Both sides are bounded and linear in `u`; compare them on translates of the vacuum.
  suffices h_eq : ((heisenbergRep (β := β) (μ := μ) (e := e)).restrictLeft S).integrated μ₁ e₁ v =
      S.tmul μ v ∘L r by rw [h_eq, ContinuousLinearMap.comp_apply]
  refine hom_ext (S.equiv.surjective.forall.mpr ?_)
  rintro ⟨a, b⟩
  set f₁ : ReproducingModel β₁ μ₁ e₁ := heisenbergRep a vacuum
  set f₂ : ReproducingModel β₂ μ₂ e₂ := heisenbergRep b vacuum
  have h_restrict : r (S.tmul μ f₁ f₂) = f₁ 0 • f₂ := by
    ext c
    rw [h_apply, tmul_apply, S.equiv.symm_apply_apply, ReproducingModel.smul_apply]
  have h_intertwine (y : W₁) (f : ReproducingModel β₁ μ₁ e₁) :
      (S.tmul μ).flip f₂ (heisenbergRep y f) =
        (heisenbergRep (β := β) (μ := μ) (e := e)).restrictLeft S y ((S.tmul μ).flip f₂ f) := by
    simpa using (S.heisenbergRep_tmul f f₂ (S.equiv (y, 0))).symm
  rw [S.heisenbergRep_equiv_vacuum (μ₁ := μ₁) (μ₂ := μ₂), ContinuousLinearMap.comp_apply,
    h_restrict, map_smul]
  have h := map_integrated_of_intertwines (heisenbergRep (β := β₁) (μ := μ₁) (e := e₁))
    ((S.tmul μ).flip f₂) v f₁ h_intertwine
  rw [ContinuousLinearMap.flip_apply, ContinuousLinearMap.flip_apply, integrated_eq_smul,
    map_smul, _root_.smul_apply] at h
  exact h.symm

variable [LocallyCompactSpace W] [LocallyCompactSpace W₁] [LocallyCompactSpace W₂]

/-- The norm of a tensor product is the product of the norms. -/
theorem norm_tmul : ‖S.tmul μ v w‖ = ‖v‖ * ‖w‖ := by
  rw [norm_eq_integral_norm, S.integral_eq_integral_prod (μ₁ := μ₁) (μ₂ := μ₂),
    norm_eq_integral_norm, norm_eq_integral_norm, ← integral_prod_mul]
  simp [tmul_apply]

/-- The tensor product is multiplicative for `⟨·, ·⟩`. -/
theorem innerSL_tmul :
    innerSL (S.tmul μ v w) (S.tmul μ v' w') = innerSL v v' * innerSL w w' := by
  rw [innerSL_apply, S.integral_eq_integral_prod (μ₁ := μ₁) (μ₂ := μ₂), innerSL_apply,
    innerSL_apply, ← integral_prod_mul]
  refine integral_congr_ae (.of_forall fun x ↦ ?_)
  simp only [tmul_apply, S.equiv.symm_apply_apply, map_mul]
  ring

/-- The Weil representation of an action that is a product along the orthogonal sum is the tensor
product of the Weil representations of the factors: if `g` acts as `(g₁, g₂)` and
`Δ g = Δ₁ g₁ * Δ₂ g₂`, then `ω(g) (v ⊗ w) = ω(g₁) v ⊗ ω(g₂) w`. -/
theorem weilRep_tmul {G G₁ G₂ : Type*} [Group G] [TopologicalSpace G] [DistribMulAction G W]
    [ContinuousSMul G W] [Group G₁] [TopologicalSpace G₁] [DistribMulAction G₁ W₁]
    [ContinuousSMul G₁ W₁] [Group G₂] [TopologicalSpace G₂] [DistribMulAction G₂ W₂]
    [ContinuousSMul G₂ W₂] (Δ : β.Multiplier μ G) (Δ₁ : β₁.Multiplier μ₁ G₁)
    (Δ₂ : β₂.Multiplier μ₂ G₂) (hc : ∀ g h, Δ.cocycle e g h = 1)
    (hc₁ : ∀ g h, Δ₁.cocycle e₁ g h = 1) (hc₂ : ∀ g h, Δ₂.cocycle e₂ g h = 1) {g : G} {g₁ : G₁}
    {g₂ : G₂} (hΔ : Δ g = Δ₁ g₁ * Δ₂ g₂)
    (h_smul : ∀ x : W₁ × W₂, g • S.equiv x = S.equiv (g₁ • x.1, g₂ • x.2)) :
    weilRep e Δ hc g (S.tmul μ v w) =
      S.tmul μ (weilRep e₁ Δ₁ hc₁ g₁ v) (weilRep e₂ Δ₂ hc₂ g₂ w) := by
  ext x
  obtain ⟨⟨a, b⟩, rfl⟩ := S.equiv.surjective x
  let F₁ (y : W₁) : ℂ := v y * (β₁ (g₁ • y) a * e₁ (a - g₁ • y))
  let F₂ (y : W₂) : ℂ := w y * (β₂ (g₂ • y) b * e₂ (b - g₂ • y))
  have h_split (y : W₁ × W₂) :
      S.tmul μ v w (S.equiv y) * (β (g • S.equiv y) (S.equiv (a, b)) *
        e (S.equiv (a, b) - g • S.equiv y)) = F₁ y.1 * F₂ y.2 := by
    simp only [F₁, F₂, h_smul, ← map_sub, S.apply_equiv_equiv, S.vacuum_equiv, tmul_apply,
      S.equiv.symm_apply_apply, Prod.mk_sub_mk]
    ring
  calc weilRep e Δ hc g (S.tmul μ v w) (S.equiv (a, b))
    _ = Δ g * ∫ y : W₁ × W₂, F₁ y.1 * F₂ y.2 ∂μ₁.prod μ₂ := by
      rw [weilRep_apply, S.integral_eq_integral_prod (μ₁ := μ₁) (μ₂ := μ₂)]
      simp_rw [h_split]
    _ = (Δ₁ g₁ * ∫ y, F₁ y ∂μ₁) * (Δ₂ g₂ * ∫ y, F₂ y ∂μ₂) := by
      rw [integral_prod_mul, hΔ, mul_mul_mul_comm]
    _ = S.tmul μ (weilRep e₁ Δ₁ hc₁ g₁ v) (weilRep e₂ Δ₂ hc₂ g₂ w) (S.equiv (a, b)) := by
      rw [tmul_apply, S.equiv.symm_apply_apply, weilRep_apply, weilRep_apply]

end TensorProduct

end OrthogonalSum

end HeisenbergDatum

/-! ### Transport along isomorphisms -/

namespace ReproducingModel

/-- An isometric ring endomorphism of `ℂ` (the identity or complex conjugation) fixes the values
of a vacuum. -/
private theorem map_vacuum_comp {W W' : Type*} [AddCommGroup W'] [TopologicalSpace W']
    [MeasurableSpace W'] {β' : HeisenbergDatum W'} {μ' : Measure W'} {e : W → ℂ} {e' : W' → ℂ}
    (he' : β'.IsVacuum μ' e') {σ : ℂ →+* ℂ} [RingHomIsometric σ] {φ : W' → W}
    (hφ : ∀ x, e (φ x) = e' x) (x : W') : σ (e (φ x)) = e' x := by
  rcases Complex.ringHom_eq_id_or_conj_of_continuous σ.isometry.continuous with rfl | rfl
  · simp [hφ]
  · simp [hφ, he'.conj_apply]

variable {W W' : Type*} [AddCommGroup W] [TopologicalSpace W] [MeasurableSpace W]
  [IsTopologicalAddGroup W] [BorelSpace W] [SecondCountableTopology W] [LocallyCompactSpace W]
  [AddCommGroup W'] [TopologicalSpace W'] [MeasurableSpace W'] [IsTopologicalAddGroup W']
  [BorelSpace W'] {β : HeisenbergDatum W} {μ : Measure W} {e : W → ℂ} {β' : HeisenbergDatum W'}
  {μ' : Measure W'} {e' : W' → ℂ} [μ.IsAddHaarMeasure] [μ'.IsAddHaarMeasure]
  [he : β.IsVacuum μ e] [he' : β'.IsVacuum μ' e'] {σ : ℂ →+* ℂ} [RingHomIsometric σ]
  {φ : W' ≃ₜ+ W}

variable (μ μ') in
include he he' in
/-- An isomorphism of topological groups that matches two vacua carries the Haar measure of the
second to that of the first: both give `‖e‖ ^ 2` the integral `1`. -/
theorem measurePreserving_of_vacuum (hφ : ∀ x, e (φ x) = e' x) : MeasurePreserving φ μ' μ := by
  have h_cont := he.continuous
  have h_one : ∫ x, ‖e x‖ ^ 2 ∂(map φ μ') = 1 := by
    rw [integral_map (by fun_prop) (by fun_prop)]
    simp_rw [hφ]
    exact he'.integral_norm_sq_eq_one
  exact ⟨by fun_prop, eq_addHaar_of_integral_eq (h_one.trans he.integral_norm_sq_eq_one.symm)
    (by rw [he.integral_norm_sq_eq_one]; exact one_ne_zero)⟩

variable (μ μ') in
/-- The function `σ ∘ v ∘ φ` transported along an isomorphism lies in the model. -/
private def transportFun (hβ : ∀ x y, σ (β (φ x) (φ y)) = β' x y) (hφ : ∀ x, e (φ x) = e' x)
    (v : ReproducingModel β μ e) : ReproducingModel β' μ' e' :=
  mk (fun x ↦ σ (v (φ x)))
    (by
      have h_int := (measurePreserving_of_vacuum (β := β) (β' := β') μ μ'
        hφ).integrable_comp_of_integrable v.integrable
      exact h_int.norm.mono' (σ.isometry.continuous.comp_aestronglyMeasurable h_int.1)
        (.of_forall fun x ↦ by simp [RingHomIsometric.norm_map]))
    fun x ↦ by
      -- Apply `σ` to the reproducing identity of `v` at `φ x` and substitute `φ`.
      have h_pt (y : W') : σ (v (φ y) * (β (φ y) (φ x) * e (φ x - φ y))) =
          σ (v (φ y)) * (β' y x * e' (x - y)) := by
        rw [map_mul, map_mul, hβ, ← map_sub, map_vacuum_comp he' hφ]
      simp_rw [← h_pt]
      rw [← v.integral_mul_kernel (φ x), ← (measurePreserving_of_vacuum (β := β) (β' := β') μ μ'
        hφ).integral_comp φ.toHomeomorph.measurableEmbedding]
      rcases Complex.ringHom_eq_id_or_conj_of_continuous σ.isometry.continuous with rfl | rfl
      · simp
      · exact integral_conj

private theorem transportFun_apply (hβ : ∀ x y, σ (β (φ x) (φ y)) = β' x y)
    (hφ : ∀ x, e (φ x) = e' x) (v : ReproducingModel β μ e) (x : W') :
    transportFun μ μ' hβ hφ v x = σ (v (φ x)) := by
  rw [transportFun, mk_apply]

variable (μ μ') in
/-- *Transport* of the model along an isomorphism `φ : W' ≃ W` of topological groups with
`σ (β (φ x) (φ y)) = β' x y` and `e (φ x) = e' x`, where `σ` is the identity or complex
conjugation: the norm-preserving `σ`-semilinear map `v ↦ σ ∘ v ∘ φ`. -/
def transport (hβ : ∀ x y, σ (β (φ x) (φ y)) = β' x y) (hφ : ∀ x, e (φ x) = e' x) :
    ReproducingModel β μ e →SL[σ] ReproducingModel β' μ' e' :=
  LinearMap.mkContinuous
    { toFun := transportFun μ μ' hβ hφ
      map_add' v w := ext fun x ↦ by simp [transportFun_apply]
      map_smul' c v := ext fun x ↦ by simp [transportFun_apply] }
    1 fun v ↦ by
      refine le_of_eq ?_
      rw [one_mul, norm_eq_integral_norm, norm_eq_integral_norm,
        ← (measurePreserving_of_vacuum (β := β) (β' := β') μ μ' hφ).integral_comp
          φ.toHomeomorph.measurableEmbedding]
      simp [transportFun_apply, RingHomIsometric.norm_map]

@[simp]
theorem transport_apply (hβ : ∀ x y, σ (β (φ x) (φ y)) = β' x y) (hφ : ∀ x, e (φ x) = e' x)
    (v : ReproducingModel β μ e) (x : W') : transport μ μ' hβ hφ v x = σ (v (φ x)) :=
  transportFun_apply hβ hφ v x

/-- Transport preserves the norm. -/
theorem norm_transport (hβ : ∀ x y, σ (β (φ x) (φ y)) = β' x y) (hφ : ∀ x, e (φ x) = e' x)
    (v : ReproducingModel β μ e) : ‖transport μ μ' hβ hφ v‖ = ‖v‖ := by
  rw [norm_eq_integral_norm, norm_eq_integral_norm,
    ← (measurePreserving_of_vacuum (β := β) (β' := β') μ μ' hφ).integral_comp
      φ.toHomeomorph.measurableEmbedding]
  simp [RingHomIsometric.norm_map]

end ReproducingModel

end TauCeti
