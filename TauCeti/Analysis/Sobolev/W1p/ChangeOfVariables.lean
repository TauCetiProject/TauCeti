/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.W1p.MeyersSerrin
public import TauCeti.MeasureTheory.Function.Jacobian
public import TauCeti.MeasureTheory.Function.LpSeminorm.Comp
public import TauCeti.MeasureTheory.Measure.AbsolutelyContinuous
public import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
# Change of variables in `W^{1,p}`

Let `U` and `V` be open subsets of a finite-dimensional real inner product space `E` and let
`Φ : E → E` map `U` injectively into `V`. Suppose that `Φ` is differentiable on `U`, that its
derivative is bounded, `‖DΦ‖ ≤ L` on `U`, and that its Jacobian is bounded below,
`c ≤ |det DΦ|` on `U` with `c > 0`. Then for `1 ≤ p < ∞`, precomposition with `Φ` maps
`W^{1,p}(V)` to `W^{1,p}(U)`, with the chain rule

`∇(u ∘ Φ)(x) = DΦ(x)* (∇u)(Φ x)` almost everywhere on `U`,

where `DΦ(x)*` is the adjoint of the derivative. It is a bounded linear operator
`TauCeti.W1p.compL`, of norm at most `max 1 L * c ^ (-1/p)`.

The Jacobian bound makes precomposition bounded on `Lᵖ`
(`MeasureTheory.map_restrict_le_smul_restrict_of_differentiableOn`,
`MeasureTheory.eLpNorm_comp_le_of_map_le_smul`), and with the bound on `DΦ` the pair
`(u ∘ Φ, DΦ* (∇u ∘ Φ))` is a bounded linear function of the value-gradient jet `(u, ∇u)`. For `u`
smooth on `V` this pair is the classical value and gradient of `u ∘ Φ`, so it lies in
`W^{1,p}(U)`. Since `W^{1,p}(U)` is closed in the space of jets and the smooth elements are dense
in `W^{1,p}(V)` (Meyers–Serrin, `TauCeti.W1p.dense_contDiffOn_representatives`), the same holds
for every `u ∈ W^{1,p}(V)`. Neither continuity of `DΦ` nor differentiability of the inverse map
is needed.

Such changes of variables are the standard tool for flattening the boundary of a domain that is
locally the region above a graph, which reduces trace and extension problems there to the
half-space, where `TauCeti.W1p.halfSpaceTrace` and `TauCeti.W1p.extendByReflectionL` apply.

## Main declarations

* `TauCeti.W1p.compL`: precomposition with `Φ` as a bounded operator
  `W^{1,p}(V) →L[ℝ] W^{1,p}(U)`.
* `TauCeti.W1p.value_compL_ae`, `TauCeti.W1p.gradient_compL_ae`: its value is `u ∘ Φ` and its
  weak gradient is `DΦ* (∇u ∘ Φ)`, almost everywhere on `U`.
* `TauCeti.W1p.norm_compL_le`, `TauCeti.W1p.opNorm_compL_le`: the norm bound.

## References

* H. Brezis, *Functional Analysis, Sobolev Spaces and Partial Differential Equations*,
  Proposition 9.6, which assumes `Φ` to be a `C¹` diffeomorphism with bounded Jacobian matrices.
* L. C. Evans, *Partial Differential Equations*, Chapter 5, §5.4, proof of Theorem 1, where such a
  change of variables flattens the boundary.
-/

public section

noncomputable section

open MeasureTheory Set Filter TopologicalSpace
open scoped ContDiff InnerProductSpace Topology

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {mu : Measure E}
  {U V : Opens E} {p : ENNReal} [Fact (1 ≤ p)] {Φ : E → E} {L c : ℝ}

/-! ### The pullback of value-gradient jets -/

/-- The action of a linear map `A` on a value-gradient jet: the value is kept and the gradient is
mapped by the adjoint `A*`. At `A = DΦ(x)` it records the chain rule for `u ∘ Φ`. -/
private def adjointJet (A : E →L[ℝ] E) (J : Sobolev1Jet E) : Sobolev1Jet E :=
  WithLp.toLp 2 (J.fst, A.adjoint J.snd)

omit [MeasurableSpace E] [BorelSpace E] in
private theorem adjointJet_fst (A : E →L[ℝ] E) (J : Sobolev1Jet E) :
    (adjointJet A J).fst = J.fst :=
  rfl

omit [MeasurableSpace E] [BorelSpace E] in
private theorem adjointJet_snd (A : E →L[ℝ] E) (J : Sobolev1Jet E) :
    (adjointJet A J).snd = A.adjoint J.snd :=
  rfl

omit [MeasurableSpace E] [BorelSpace E] in
private theorem adjointJet_add (A : E →L[ℝ] E) (J K : Sobolev1Jet E) :
    adjointJet A (J + K) = adjointJet A J + adjointJet A K := by
  simp only [adjointJet, WithLp.add_fst, WithLp.add_snd, map_add, ← WithLp.toLp_add,
    Prod.mk_add_mk]

omit [MeasurableSpace E] [BorelSpace E] in
private theorem adjointJet_smul (A : E →L[ℝ] E) (a : ℝ) (J : Sobolev1Jet E) :
    adjointJet A (a • J) = a • adjointJet A J := by
  simp only [adjointJet, WithLp.smul_fst, WithLp.smul_snd, map_smul, ← WithLp.toLp_smul,
    Prod.smul_mk]

omit [MeasurableSpace E] [BorelSpace E] in
private theorem continuous_adjointJet :
    Continuous fun q : (E →L[ℝ] E) × Sobolev1Jet E => adjointJet q.1 q.2 := by
  unfold adjointJet
  fun_prop

omit [MeasurableSpace E] [BorelSpace E] in
private theorem norm_adjointJet_le {A : E →L[ℝ] E} (hA : ‖A‖ ≤ L) (J : Sobolev1Jet E) :
    ‖adjointJet A J‖ ≤ max 1 L * ‖J‖ := by
  have hM : 0 ≤ max 1 L := zero_le_one.trans (le_max_left _ _)
  have hsnd : ‖A.adjoint J.snd‖ ≤ max 1 L * ‖J.snd‖ := by
    refine (A.adjoint.le_opNorm _).trans ?_
    rw [LinearIsometryEquiv.norm_map]
    gcongr
    exact hA.trans (le_max_right _ _)
  have hfst : ‖J.fst‖ ≤ max 1 L * ‖J.fst‖ :=
    le_mul_of_one_le_left (norm_nonneg _) (le_max_left _ _)
  refine le_of_pow_le_pow_left₀ two_ne_zero (mul_nonneg hM (norm_nonneg _)) ?_
  have h1 := pow_le_pow_left₀ (norm_nonneg _) hfst 2
  have h2 := pow_le_pow_left₀ (norm_nonneg _) hsnd 2
  rw [mul_pow] at h1 h2 ⊢
  rw [WithLp.prod_norm_sq_eq_of_L2, WithLp.prod_norm_sq_eq_of_L2 J, adjointJet_fst,
    adjointJet_snd]
  linarith

/-! ### The pullback operator on `Lᵖ` jets -/

section Operator

variable {C : ENNReal} (hm : AEMeasurable Φ (mu.restrict U))
  (hmap : (mu.restrict U).map Φ ≤ C • mu.restrict V) (hC : C ≠ ⊤)
  (hL : ∀ x ∈ (U : Set E), ‖fderiv ℝ Φ x‖ ≤ L)

omit [Fact (1 ≤ p)] in
include hm hmap hL in
private theorem eLpNorm_adjointJet_comp_le (J : Sobolev1JetLp mu V p) :
    eLpNorm (fun x => adjointJet (fderiv ℝ Φ x) (J (Φ x))) p (mu.restrict U) ≤
      ENNReal.ofReal (max 1 L) * (C ^ (1 / p).toReal * eLpNorm J p (mu.restrict V)) := by
  have hJ := (Lp.aestronglyMeasurable J).comp_aemeasurable_of_map_absolutelyContinuous hm
    (Measure.absolutelyContinuous_of_le_smul hmap)
  have hmeas : AEStronglyMeasurable (fun x => adjointJet (fderiv ℝ Φ x) (J (Φ x)))
      (mu.restrict U) := continuous_adjointJet.comp_aestronglyMeasurable
    ((measurable_fderiv ℝ Φ).aestronglyMeasurable.prodMk hJ)
  calc eLpNorm (fun x => adjointJet (fderiv ℝ Φ x) (J (Φ x))) p (mu.restrict U)
      ≤ ENNReal.ofReal (max 1 L) * eLpNorm (fun x => J (Φ x)) p (mu.restrict U) :=
        eLpNorm_le_mul_eLpNorm_of_ae_le_mul hmeas ((ae_restrict_mem U.isOpen.measurableSet).mono
          fun x hx => norm_adjointJet_le (hL x hx) _) p
    _ ≤ ENNReal.ofReal (max 1 L) * (C ^ (1 / p).toReal * eLpNorm J p (mu.restrict V)) := by
        gcongr
        exact eLpNorm_comp_le_of_map_le_smul hm hmap (Lp.aestronglyMeasurable J) p

omit [Fact (1 ≤ p)] in
include hm hmap hC hL in
private theorem memLp_adjointJet_comp (J : Sobolev1JetLp mu V p) :
    MemLp (fun x => adjointJet (fderiv ℝ Φ x) (J (Φ x))) p (mu.restrict U) :=
  (eLpNorm_adjointJet_comp_le hm hmap hL J).trans_lt (ENNReal.mul_lt_top ENNReal.ofReal_lt_top
    (ENNReal.mul_lt_top (ENNReal.rpow_lt_top_of_nonneg ENNReal.toReal_nonneg hC)
      (Lp.eLpNorm_lt_top J)))

/-- The pullback `(a, g) ↦ (a ∘ Φ, DΦ* (g ∘ Φ))` of `Lᵖ` value-gradient jets on `V` to jets on
`U`, a bounded linear operator. -/
private def pullbackJetL : Sobolev1JetLp mu V p →L[ℝ] Sobolev1JetLp mu U p :=
  LinearMap.mkContinuous
    { toFun := fun J => (memLp_adjointJet_comp hm hmap hC hL J).toLp _
      map_add' := fun J K => by
        rw [← MemLp.toLp_add]
        refine MemLp.toLp_congr _ _ ?_
        filter_upwards [ae_comp_of_map_absolutelyContinuous hm
          (Measure.absolutelyContinuous_of_le_smul hmap) (Lp.coeFn_add J K)] with x hx
        rw [hx, Pi.add_apply, adjointJet_add, Pi.add_apply]
      map_smul' := fun a J => by
        rw [RingHom.id_apply, ← MemLp.toLp_const_smul]
        refine MemLp.toLp_congr _ _ ?_
        filter_upwards [ae_comp_of_map_absolutelyContinuous hm
          (Measure.absolutelyContinuous_of_le_smul hmap) (Lp.coeFn_smul a J)] with x hx
        rw [hx, Pi.smul_apply, adjointJet_smul, Pi.smul_apply] }
    (max 1 L * (C ^ (1 / p).toReal).toReal) fun J => by
      rw [LinearMap.coe_mk, AddHom.coe_mk, Lp.norm_toLp, mul_assoc, Lp.norm_def,
        ← ENNReal.toReal_mul, ← ENNReal.toReal_ofReal (zero_le_one.trans (le_max_left 1 L)),
        ← ENNReal.toReal_mul]
      exact ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ENNReal.mul_ne_top
        (ENNReal.rpow_ne_top_of_nonneg ENNReal.toReal_nonneg hC) (Lp.eLpNorm_ne_top J)))
        (eLpNorm_adjointJet_comp_le hm hmap hL J)

private theorem norm_pullbackJetL_le (J : Sobolev1JetLp mu V p) :
    ‖pullbackJetL hm hmap hC hL J‖ ≤ max 1 L * (C ^ (1 / p).toReal).toReal * ‖J‖ :=
  (pullbackJetL hm hmap hC hL).le_of_opNorm_le (LinearMap.mkContinuous_norm_le _
    (by positivity) _) J

private theorem pullbackJetL_ae (J : Sobolev1JetLp mu V p) :
    pullbackJetL hm hmap hC hL J =ᵐ[mu.restrict U]
      fun x => adjointJet (fderiv ℝ Φ x) (J (Φ x)) :=
  (memLp_adjointJet_comp hm hmap hC hL J).coeFn_toLp

variable [mu.IsAddHaarMeasure]

/-- The smooth case: if the value of `u ∈ W^{1,p}(V)` is represented by a `C¹` function `f` on
`V`, the pulled-back jet is the classical value and gradient of `f ∘ Φ`, so it lies in
`W^{1,p}(U)`. -/
private theorem pullbackJetL_mem_of_contDiffOn (hΦ : DifferentiableOn ℝ Φ U)
    (hmaps : MapsTo Φ U V) (u : W1p mu V p) {f : E → ℝ} (hf : ContDiffOn ℝ 1 f V)
    (hu : (W1p.value u : E → ℝ) =ᵐ[mu.restrict V] f) :
    pullbackJetL hm hmap hC hL (u : Sobolev1JetLp mu V p) ∈ w1pSubmodule mu U p := by
  set T := pullbackJetL hm hmap hC hL (u : Sobolev1JetLp mu V p)
  have hac := Measure.absolutelyContinuous_of_le_smul hmap
  have hΦx : ∀ x ∈ (U : Set E), DifferentiableAt ℝ Φ x := fun x hx =>
    (hΦ x hx).differentiableAt (U.isOpen.mem_nhds hx)
  have hfy : ∀ y ∈ (V : Set E), DifferentiableAt ℝ f y := fun y hy =>
    (hf.differentiableOn one_ne_zero y hy).differentiableAt (V.isOpen.mem_nhds hy)
  -- The weak gradient of `u` is the classical derivative of `f`.
  have hgrad : ∀ᵐ y ∂mu.restrict V, innerSL ℝ (W1p.gradient u y) = fderiv ℝ f y :=
    ((W1p.hasWeakFDerivOn u).congr_ae hu).ae_eq_fderiv
      ((hf.continuousOn_fderiv_of_isOpen V.isOpen le_rfl).locallyIntegrableOn
        V.isOpen.measurableSet) hfy
  have hval : Sobolev1JetLp.value T =ᵐ[mu.restrict U] f ∘ Φ := by
    filter_upwards [Sobolev1JetLp.value_apply_ae T,
      pullbackJetL_ae hm hmap hC hL (u : Sobolev1JetLp mu V p),
      ae_comp_of_map_absolutelyContinuous hm hac (W1p.value_apply_ae u),
      ae_comp_of_map_absolutelyContinuous hm hac hu] with x h1 h2 h3 h4
    rw [h1, h2, adjointJet_fst, ← h3, Function.comp_apply, h4]
  have hder : Sobolev1JetLp.candidateWeakFDeriv T =ᵐ[mu.restrict U] fderiv ℝ (f ∘ Φ) := by
    filter_upwards [Sobolev1JetLp.gradient_apply_ae T,
      pullbackJetL_ae hm hmap hC hL (u : Sobolev1JetLp mu V p),
      ae_comp_of_map_absolutelyContinuous hm hac (W1p.gradient_apply_ae u),
      ae_comp_of_map_absolutelyContinuous hm hac hgrad,
      ae_restrict_mem U.isOpen.measurableSet] with x h1 h2 h3 h4 hx
    ext v
    rw [Sobolev1JetLp.candidateWeakFDeriv_apply, h1, h2, adjointJet_snd, ← h3,
      ContinuousLinearMap.adjoint_inner_right, fderiv_comp x (hfy _ (hmaps hx)) (hΦx x hx),
      ContinuousLinearMap.comp_apply, ← h4, innerSL_apply_apply, real_inner_comm]
  have hTloc : LocallyIntegrableOn (Sobolev1JetLp.candidateWeakFDeriv T) U mu := by
    have hcand : Sobolev1JetLp.candidateWeakFDeriv T =
        fun x => innerSL ℝ (Sobolev1JetLp.gradient T x) := by
      ext x v
      rw [Sobolev1JetLp.candidateWeakFDeriv_apply, innerSL_apply_apply, real_inner_comm]
    rw [hcand]
    exact (innerSL ℝ : E →L[ℝ] E →L[ℝ] ℝ).locallyIntegrableOn_comp
      (locallyIntegrableOn_of_locallyIntegrable_restrict
        ((Lp.memLp (Sobolev1JetLp.gradient T)).locallyIntegrable Fact.out))
  rw [mem_w1pSubmodule_iff_hasWeakFDerivOn]
  refine ((hasWeakFDerivOn_of_differentiableOn ?_ ((locallyIntegrableOn_congr hder).1 hTloc)
    fun x hx => (hfy _ (hmaps hx)).comp x (hΦx x hx)).congr_ae hval.symm).congr_ae_deriv
      hder.symm
  exact (hf.continuousOn.comp hΦ.continuousOn hmaps).locallyIntegrableOn U.isOpen.measurableSet

/-- For `p < ∞` the pulled-back jet of every `u ∈ W^{1,p}(V)` lies in `W^{1,p}(U)`: the set of
`u` for which it does is closed, and contains the smooth elements, which are dense. -/
private theorem pullbackJetL_mem (hp : p ≠ ⊤) (hΦ : DifferentiableOn ℝ Φ U)
    (hmaps : MapsTo Φ U V) (u : W1p mu V p) :
    pullbackJetL hm hmap hC hL (u : Sobolev1JetLp mu V p) ∈ w1pSubmodule mu U p := by
  have hclosed : IsClosed {u : W1p mu V p |
      pullbackJetL hm hmap hC hL (u : Sobolev1JetLp mu V p) ∈ w1pSubmodule mu U p} :=
    (w1pSubmodule mu U p).isClosed.preimage
      ((pullbackJetL hm hmap hC hL).continuous.comp continuous_subtype_val)
  refine closure_minimal ?_ hclosed (W1p.dense_contDiffOn_representatives hp u)
  rintro v ⟨f, hf, hv⟩
  exact pullbackJetL_mem_of_contDiffOn hm hmap hC hL hΦ hmaps v (hf.of_le (by simp)) hv

end Operator

/-! ### Precomposition with a change of variables -/

section ChangeOfVariables

variable [mu.IsAddHaarMeasure]

variable (Φ) (hp : p ≠ ⊤) (hΦ : DifferentiableOn ℝ Φ U) (hinj : InjOn Φ U) (hmaps : MapsTo Φ U V)
  (hL : ∀ x ∈ (U : Set E), ‖fderiv ℝ Φ x‖ ≤ L) (hc : 0 < c)
  (hdet : ∀ x ∈ (U : Set E), c ≤ |(fderiv ℝ Φ x).det|)

/-- **Change of variables in `W^{1,p}`.** Let `Φ` be differentiable and injective on `U`, mapping
`U` into `V`, with `‖DΦ‖ ≤ L` and `c ≤ |det DΦ|` on `U` for some `c > 0`. For `1 ≤ p < ∞`,
precomposition with `Φ` is a bounded linear operator `W^{1,p}(V) →L[ℝ] W^{1,p}(U)`, with value
`u ∘ Φ` (`TauCeti.W1p.value_compL_ae`) and weak gradient `DΦ* (∇u ∘ Φ)`
(`TauCeti.W1p.gradient_compL_ae`). -/
def W1p.compL : W1p mu V p →L[ℝ] W1p mu U p :=
  ContinuousLinearMap.codRestrict
    ((pullbackJetL (hΦ.continuousOn.aemeasurable U.isOpen.measurableSet)
      (map_restrict_le_smul_restrict_of_differentiableOn mu U.isOpen hΦ hinj hmaps hc hdet)
      (ENNReal.inv_ne_top.2 (ENNReal.ofReal_pos.2 hc).ne') hL).comp
        (w1pSubmodule mu V p).toSubmodule.subtypeL)
    (w1pSubmodule mu U p).toSubmodule
    (fun u => pullbackJetL_mem (hΦ.continuousOn.aemeasurable U.isOpen.measurableSet)
      (map_restrict_le_smul_restrict_of_differentiableOn mu U.isOpen hΦ hinj hmaps hc hdet)
      (ENNReal.inv_ne_top.2 (ENNReal.ofReal_pos.2 hc).ne') hL hp hΦ hmaps u)

/-- The ambient jet of `W1p.compL Φ … u` is the pulled-back jet of `u`. -/
private theorem coe_compL (u : W1p mu V p) :
    ((W1p.compL Φ hp hΦ hinj hmaps hL hc hdet u : W1p mu U p) : Sobolev1JetLp mu U p) =
      pullbackJetL (hΦ.continuousOn.aemeasurable U.isOpen.measurableSet)
        (map_restrict_le_smul_restrict_of_differentiableOn mu U.isOpen hΦ hinj hmaps hc hdet)
        (ENNReal.inv_ne_top.2 (ENNReal.ofReal_pos.2 hc).ne') hL (u : Sobolev1JetLp mu V p) :=
  rfl

private theorem coe_compL_ae (u : W1p mu V p) :
    ((W1p.compL Φ hp hΦ hinj hmaps hL hc hdet u : W1p mu U p) : Sobolev1JetLp mu U p)
      =ᵐ[mu.restrict U] fun x =>
        adjointJet (fderiv ℝ Φ x) ((u : Sobolev1JetLp mu V p) (Φ x)) :=
  pullbackJetL_ae (hΦ.continuousOn.aemeasurable U.isOpen.measurableSet)
    (map_restrict_le_smul_restrict_of_differentiableOn mu U.isOpen hΦ hinj hmaps hc hdet)
    (ENNReal.inv_ne_top.2 (ENNReal.ofReal_pos.2 hc).ne') hL _

/-- The value of `W1p.compL Φ … u` is `u ∘ Φ`, almost everywhere on `U`. -/
theorem W1p.value_compL_ae (u : W1p mu V p) :
    W1p.value (W1p.compL Φ hp hΦ hinj hmaps hL hc hdet u) =ᵐ[mu.restrict U]
      fun x => W1p.value u (Φ x) := by
  filter_upwards [W1p.value_apply_ae (W1p.compL Φ hp hΦ hinj hmaps hL hc hdet u),
    coe_compL_ae Φ hp hΦ hinj hmaps hL hc hdet u,
    ae_comp_of_map_absolutelyContinuous (hΦ.continuousOn.aemeasurable U.isOpen.measurableSet)
      (Measure.absolutelyContinuous_of_le_smul
        (map_restrict_le_smul_restrict_of_differentiableOn mu U.isOpen hΦ hinj hmaps hc hdet))
      (W1p.value_apply_ae u)]
    with x h1 h2 h3
  rw [h1, h2, adjointJet_fst, h3]

/-- **The chain rule for weak gradients.** The weak gradient of `W1p.compL Φ … u` is
`DΦ(x)* (∇u)(Φ x)`, almost everywhere on `U`. -/
theorem W1p.gradient_compL_ae (u : W1p mu V p) :
    W1p.gradient (W1p.compL Φ hp hΦ hinj hmaps hL hc hdet u) =ᵐ[mu.restrict U]
      fun x => (fderiv ℝ Φ x).adjoint (W1p.gradient u (Φ x)) := by
  filter_upwards [W1p.gradient_apply_ae (W1p.compL Φ hp hΦ hinj hmaps hL hc hdet u),
    coe_compL_ae Φ hp hΦ hinj hmaps hL hc hdet u,
    ae_comp_of_map_absolutelyContinuous (hΦ.continuousOn.aemeasurable U.isOpen.measurableSet)
      (Measure.absolutelyContinuous_of_le_smul
        (map_restrict_le_smul_restrict_of_differentiableOn mu U.isOpen hΦ hinj hmaps hc hdet))
      (W1p.gradient_apply_ae u)]
    with x h1 h2 h3
  rw [h1, h2, adjointJet_snd, h3]

/-- `W1p.compL Φ …` has operator norm at most `max 1 L * c ^ (-1/p)`. -/
theorem W1p.norm_compL_le (u : W1p mu V p) :
    ‖W1p.compL Φ hp hΦ hinj hmaps hL hc hdet u‖ ≤ max 1 L * c⁻¹ ^ (1 / p).toReal * ‖u‖ := by
  have h := norm_pullbackJetL_le (hΦ.continuousOn.aemeasurable U.isOpen.measurableSet)
    (map_restrict_le_smul_restrict_of_differentiableOn mu U.isOpen hΦ hinj hmaps hc hdet)
    (ENNReal.inv_ne_top.2 (ENNReal.ofReal_pos.2 hc).ne') hL (u : Sobolev1JetLp mu V p)
  rw [← ENNReal.toReal_rpow, ENNReal.toReal_inv, ENNReal.toReal_ofReal hc.le] at h
  rwa [← Submodule.norm_coe, coe_compL, ← Submodule.norm_coe u]

/-- `W1p.compL Φ …` has operator norm at most `max 1 L * c ^ (-1/p)`. -/
theorem W1p.opNorm_compL_le :
    ‖(W1p.compL Φ hp hΦ hinj hmaps hL hc hdet : W1p mu V p →L[ℝ] W1p mu U p)‖ ≤
      max 1 L * c⁻¹ ^ (1 / p).toReal :=
  ContinuousLinearMap.opNorm_le_bound _ (by positivity)
    (W1p.norm_compL_le Φ hp hΦ hinj hmaps hL hc hdet)

end ChangeOfVariables

end TauCeti
