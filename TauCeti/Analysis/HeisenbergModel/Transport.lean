/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.HeisenbergModel.WeilOperators
public import Mathlib.Topology.Algebra.ContinuousMonoidHom
import TauCeti.Analysis.Complex.RingHomIsometric
import TauCeti.MeasureTheory.Measure.Haar.IntegralUnique

/-!
# Transport and intertwining in reproducing models

Along an isomorphism `φ : W' ≃ W` of topological groups that matches the vacua and, up to an
isometric ring endomorphism `σ` of `ℂ` (the identity or complex conjugation), the Heisenberg data,
`v ↦ σ ∘ v ∘ φ` is a norm-preserving `σ`-semilinear map of reproducing models
(`TauCeti.ReproducingModel.transport`).

Transport respects the vacuum, the Heisenberg operators, and the sesquilinear form. Transport
along `φ.symm` is a two-sided inverse, so transport is bijective.

For actions intertwined by `φ`, transport also intertwines the Weil operators up to any scalar `c`
with `σ (Δ g) = c * Δ' g'`, which is `σ (Δ g) / Δ' g'` when `Δ' g' ≠ 0`. This statement does not
require trivial cocycles; it applies to the Weil representations when their cocycles are trivial.
These identities allow a change of coordinates, including conjugation, in a reproducing model
without unfolding its construction.

## Main definitions

* `TauCeti.ReproducingModel.transport`: transport of the model along an isomorphism.

## Main results

* `TauCeti.ReproducingModel.norm_transport`: transport preserves norms.
* `TauCeti.ReproducingModel.transport_vacuum`,
  `TauCeti.ReproducingModel.transport_heisenbergRep`,
  `TauCeti.ReproducingModel.innerSL_transport`: transport respects the vacuum, the Heisenberg
  operators and the sesquilinear form.
* `TauCeti.ReproducingModel.transport_symm_transport`,
  `TauCeti.ReproducingModel.transport_transport_symm`,
  `TauCeti.ReproducingModel.transport_bijective`: transport along `φ.symm` is the inverse; its
  matching conditions come from `TauCeti.ReproducingModel.symm_matching_heisenberg` and
  `TauCeti.ReproducingModel.symm_matching_vacuum`.
* `TauCeti.ReproducingModel.transport_weilOp`, `TauCeti.ReproducingModel.transport_weilRep`:
  transport intertwines the Weil operators and representations.

## Provenance

Adapted from grh-lean (https://github.com/lsernau/grh-lean, Apache 2.0, Copyright 2026
Anthropic, PBC). The construction of transport and its norm formula follow
`src/Lib/Weil/Construction/WeilOperators.lean` (`New.Heisenberg.IsVacuum.transport`,
`New.Heisenberg.IsVacuum.norm_transport`). The intertwining laws follow
`src/Lib/Weil/Construction/ProductsAndTransport.lean` (`New.CoordChange.map_rho`,
`New.CoordChange.map_vacElem`, `New.CoordChange.map_omega`), stated here for arbitrary reproducing
models rather than for the adelic coordinate changes.

## References

* A. Weil, *Sur certains groupes d'opérateurs unitaires*, Acta Math. 111 (1964), 143–211.
-/

public noncomputable section

open MeasureTheory Measure
open scoped ComplexConjugate

namespace TauCeti.ReproducingModel

/-- An isometric ring endomorphism of `ℂ` (the identity or complex conjugation) fixes the values
of a vacuum. -/
theorem map_vacuum_comp {W W' : Type*} [AddCommGroup W'] [TopologicalSpace W']
    [MeasurableSpace W'] {β' : HeisenbergDatum W'} {μ' : Measure W'} {e : W → ℂ} {e' : W' → ℂ}
    (he' : β'.IsVacuum μ' e') {σ : ℂ →+* ℂ} [RingHomIsometric σ] {φ : W' → W}
    (hφ : ∀ x, e (φ x) = e' x) (x : W') : σ (e (φ x)) = e' x := by
  rcases Complex.ringHom_eq_id_or_conj_of_continuous σ.isometry.continuous with rfl | rfl
  · simp [hφ]
  · simp [hφ, he'.conj_apply]

/-- The Heisenberg matching condition for `φ` gives the matching condition for `φ.symm`, as
needed for transport along `φ.symm`. -/
theorem symm_matching_heisenberg {W W' : Type*} [AddCommGroup W] [TopologicalSpace W]
    [AddCommGroup W'] [TopologicalSpace W'] {β : HeisenbergDatum W} {β' : HeisenbergDatum W'}
    {σ : ℂ →+* ℂ} [RingHomIsometric σ] {φ : W' ≃ₜ+ W}
    (hβ : ∀ x y, σ (β (φ x) (φ y)) = β' x y) (x y : W) :
    σ (β' (φ.symm x) (φ.symm y)) = β x y := by
  rw [← hβ, φ.apply_symm_apply, φ.apply_symm_apply, Complex.map_map_of_isometric]

/-- The vacuum matching condition for `φ` gives the matching condition for `φ.symm`, as needed
for transport along `φ.symm`. -/
theorem symm_matching_vacuum {W W' : Type*} [AddCommGroup W] [TopologicalSpace W]
    [AddCommGroup W'] [TopologicalSpace W'] {e : W → ℂ} {e' : W' → ℂ} {φ : W' ≃ₜ+ W}
    (hφ : ∀ x, e (φ x) = e' x) (x : W) : e' (φ.symm x) = e x := by
  rw [← hφ, φ.apply_symm_apply]

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
        hφ).integral_comp φ.toHomeomorph.measurableEmbedding, Complex.map_integral_of_isometric]

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

variable [SecondCountableTopology W']
  (hβ : ∀ x y, σ (β (φ x) (φ y)) = β' x y) (hφ : ∀ x, e (φ x) = e' x)

omit [SecondCountableTopology W'] in
/-- Transport carries the vacuum to the vacuum. -/
@[simp]
theorem transport_vacuum : transport μ μ' hβ hφ vacuum = vacuum := by
  ext x
  rw [transport_apply, vacuum_apply, vacuum_apply]
  exact map_vacuum_comp he' hφ x

/-- Transport intertwines Heisenberg translation by `φ y` with translation by `y`. -/
@[simp]
theorem transport_heisenbergRep (y : W') (v : ReproducingModel β μ e) :
    transport μ μ' hβ hφ (heisenbergRep (φ y) v) =
      heisenbergRep y (transport μ μ' hβ hφ v) := by
  ext x
  simp only [transport_apply, heisenbergRep_apply, map_mul, hβ, ← map_sub]

/-- The sesquilinear form transforms by the scalar automorphism of transport. -/
@[simp]
theorem innerSL_transport (v w : ReproducingModel β μ e) :
    innerSL (transport μ μ' hβ hφ v) (transport μ μ' hβ hφ w) = σ (innerSL v w) := by
  rw [innerSL_apply, innerSL_apply,
    ← (measurePreserving_of_vacuum (β := β) (β' := β') μ μ' hφ).integral_comp
      φ.toHomeomorph.measurableEmbedding, Complex.map_integral_of_isometric]
  simp only [transport_apply, map_mul, Complex.map_conj_of_isometric]

/-- Transport along `φ.symm` undoes transport along `φ`. -/
@[simp]
theorem transport_symm_transport [LocallyCompactSpace W']
    (hβ' : ∀ x y, σ (β' (φ.symm x) (φ.symm y)) = β x y) (hφ' : ∀ x, e' (φ.symm x) = e x)
    (v : ReproducingModel β μ e) :
    transport μ' μ hβ' hφ' (transport μ μ' hβ hφ v) = v := by
  ext x
  simp only [transport_apply, φ.apply_symm_apply, Complex.map_map_of_isometric]

/-- Transport along `φ` undoes transport along `φ.symm`. -/
@[simp]
theorem transport_transport_symm [LocallyCompactSpace W']
    (hβ' : ∀ x y, σ (β' (φ.symm x) (φ.symm y)) = β x y) (hφ' : ∀ x, e' (φ.symm x) = e x)
    (v : ReproducingModel β' μ' e') :
    transport μ μ' hβ hφ (transport μ' μ hβ' hφ' v) = v := by
  ext x
  simp only [transport_apply, φ.symm_apply_apply, Complex.map_map_of_isometric]

omit [SecondCountableTopology W'] in
/-- Transport is bijective; its inverse is transport along `φ.symm`. -/
theorem transport_bijective : Function.Bijective (transport μ μ' hβ hφ) := by
  let : SecondCountableTopology W' := φ.toHomeomorph.secondCountableTopology
  let : LocallyCompactSpace W' := φ.toHomeomorph.isClosedEmbedding.locallyCompactSpace
  exact ⟨Function.LeftInverse.injective (transport_symm_transport hβ hφ
      (symm_matching_heisenberg hβ) (symm_matching_vacuum hφ)),
    Function.RightInverse.surjective (transport_transport_symm hβ hφ
      (symm_matching_heisenberg hβ) (symm_matching_vacuum hφ))⟩

omit [SecondCountableTopology W'] in
/-- Every vector in the target model is the transport of a vector in the source model. -/
theorem transport_surjective : Function.Surjective (transport μ μ' hβ hφ) :=
  (transport_bijective hβ hφ).surjective

/-- The identity change of coordinates induces the identity operator. -/
@[simp]
theorem transport_refl :
    transport (β := β) (β' := β) (e := e) (e' := e) μ μ
      (σ := RingHom.id ℂ) (φ := .refl W) (fun _ _ ↦ rfl) (fun _ ↦ rfl) =
      ContinuousLinearMap.id ℂ (ReproducingModel β μ e) := by
  ext v x
  refine (transport_apply (β := β) (β' := β) (e := e) (e' := e) (σ := RingHom.id ℂ)
    (φ := .refl W) (fun _ _ ↦ rfl) (fun _ ↦ rfl) v x).trans ?_
  simp

section WeilOperators

variable {G G' : Type*} [Group G] [TopologicalSpace G] [DistribMulAction G W] [ContinuousSMul G W]
  [Group G'] [TopologicalSpace G'] [DistribMulAction G' W'] [ContinuousSMul G' W']
  (Δ : β.Multiplier μ G) (Δ' : β'.Multiplier μ' G') (g : G) (g' : G')
  (hact : ∀ y, g • φ y = φ (g' • y))

omit [SecondCountableTopology W'] [TopologicalSpace G] [ContinuousSMul G W]
  [TopologicalSpace G'] [ContinuousSMul G' W'] in
include hact in
/-- The integral kernel of a Weil operator commutes with coordinate transport. The multipliers
are omitted here so the formula is also usable when a multiplier vanishes. -/
private theorem integral_kernel_transport (v : ReproducingModel β μ e) (x : W') :
    σ (∫ y, v y * (β (g • y) (φ x) * e (φ x - g • y)) ∂μ) =
      ∫ y, transport μ μ' hβ hφ v y * (β' (g' • y) x * e' (x - g' • y)) ∂μ' := by
  rw [← (measurePreserving_of_vacuum (β := β) (β' := β') μ μ' hφ).integral_comp
    φ.toHomeomorph.measurableEmbedding, Complex.map_integral_of_isometric]
  simp only [map_mul, hact, hβ, ← map_sub, map_vacuum_comp he' hφ, transport_apply]

include hact in
/-- Transport intertwines Weil operators up to any scalar `c` with `σ (Δ g) = c * Δ' g'`, which is
`σ (Δ g) / Δ' g'` when `Δ' g' ≠ 0`. Neither triviality of the cocycles nor nonvanishing of either
multiplier is assumed. -/
theorem transport_weilOp {c : ℂ} (hΔ : σ (Δ g) = c * Δ' g')
    (v : ReproducingModel β μ e) :
    transport μ μ' hβ hφ (weilOp e Δ g v) =
      c • weilOp e' Δ' g' (transport μ μ' hβ hφ v) := by
  ext x
  simp only [transport_apply, weilOp_apply, map_mul, smul_apply]
  rw [hΔ, integral_kernel_transport (μ' := μ') hβ hφ g g' hact, mul_assoc]
  simp only [transport_apply]

include hact in
/-- For trivial cocycles the same transport formula holds for the Weil representations. -/
theorem transport_weilRep (hc : ∀ g h, Δ.cocycle e g h = 1)
    (hc' : ∀ g h, Δ'.cocycle e' g h = 1) {c : ℂ} (hΔ : σ (Δ g) = c * Δ' g')
    (v : ReproducingModel β μ e) :
    transport μ μ' hβ hφ (weilRep e Δ hc g v) =
      c • weilRep e' Δ' hc' g' (transport μ μ' hβ hφ v) := by
  simpa only [weilRep_apply_eq] using transport_weilOp hβ hφ Δ Δ' g g' hact hΔ v

end WeilOperators

end TauCeti.ReproducingModel
