/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.HeisenbergModel.OrthogonalSum
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
# Transport and intertwining in reproducing models

The transport `v ↦ σ ∘ v ∘ φ` along a vacuum-preserving additive homeomorphism respects the
vacuum, the Heisenberg operators, and the sesquilinear form. Here `σ` is an isometric ring
endomorphism of `ℂ`, hence either the identity or conjugation. Transport is bijective and
has an inverse given by the inverse coordinate change.

For actions intertwined by `φ`, transport also intertwines the Weil operators, with precisely
the scalar coming from the two multipliers. This statement does not require trivial cocycles;
it applies to the Weil representations when their cocycles are trivial. These identities
allow a change of coordinates, including conjugation, in a reproducing model without unfolding
its construction.
-/

public noncomputable section

open MeasureTheory
open scoped ComplexConjugate

namespace TauCeti.ReproducingModel

variable {W W' : Type*} [AddCommGroup W] [TopologicalSpace W] [MeasurableSpace W]
  [IsTopologicalAddGroup W] [BorelSpace W] [SecondCountableTopology W] [LocallyCompactSpace W]
  [AddCommGroup W'] [TopologicalSpace W'] [MeasurableSpace W'] [IsTopologicalAddGroup W']
  [BorelSpace W'] [SecondCountableTopology W'] {β : HeisenbergDatum W} {β' : HeisenbergDatum W'}
  {μ : Measure W} {μ' : Measure W'} {e : W → ℂ} {e' : W' → ℂ}
  [μ.IsAddHaarMeasure] [μ'.IsAddHaarMeasure] [he : β.IsVacuum μ e] [he' : β'.IsVacuum μ' e']
  {σ : ℂ →+* ℂ} [RingHomIsometric σ] {φ : W' ≃ₜ+ W}
  (hβ : ∀ x y, σ (β (φ x) (φ y)) = β' x y) (hφ : ∀ x, e (φ x) = e' x)

omit [SecondCountableTopology W'] in
/-- Transport carries the vacuum to the vacuum. -/
@[simp]
theorem transport_vacuum : transport μ μ' hβ hφ vacuum = vacuum := by
  ext x
  rw [transport_apply, vacuum_apply, vacuum_apply, hφ]
  rcases Complex.ringHom_eq_id_or_conj_of_continuous σ.isometry.continuous with rfl | rfl
  · rfl
  · exact he'.conj_apply x

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
      φ.toHomeomorph.measurableEmbedding]
  simp only [transport_apply]
  rcases Complex.ringHom_eq_id_or_conj_of_continuous σ.isometry.continuous with rfl | rfl
  · rfl
  · simp only [← map_mul, ← integral_conj]

omit [SecondCountableTopology W'] in
/-- Every vector in the target model is the transport of a vector in the source model. -/
theorem surjective_transport : Function.Surjective (transport μ μ' hβ hφ) := by
  let : SecondCountableTopology W' := φ.toHomeomorph.secondCountableTopology
  let : LocallyCompactSpace W' := φ.toHomeomorph.isClosedEmbedding.locallyCompactSpace
  have hσ (z : ℂ) : σ (σ z) = z := by
    rcases Complex.ringHom_eq_id_or_conj_of_continuous σ.isometry.continuous with rfl | rfl
    · rfl
    · exact Complex.conj_conj z
  have hβ' (x y : W) : σ (β' (φ.symm x) (φ.symm y)) = β x y := by
    rw [← hβ, φ.apply_symm_apply, φ.apply_symm_apply, hσ]
  have hφ' (x : W) : e' (φ.symm x) = e x := by
    rw [← hφ, φ.apply_symm_apply]
  intro v
  refine ⟨transport μ' μ hβ' hφ' v, ?_⟩
  ext x
  simp only [transport_apply, φ.symm_apply_apply, hσ]

/-- The identity change of coordinates induces the identity operator. -/
@[simp]
theorem transport_refl :
    transport (β := β) (β' := β) (e := e) (e' := e) μ μ
      (σ := RingHom.id ℂ) (φ := .refl W) (fun _ _ ↦ rfl) (fun _ ↦ rfl) =
      ContinuousLinearMap.id ℂ (ReproducingModel β μ e) := by
  ext v x
  exact transport_apply (β := β) (β' := β) (e := e) (e' := e)
    (σ := RingHom.id ℂ) (φ := .refl W) (fun _ _ ↦ rfl) (fun _ ↦ rfl) v x

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
    φ.toHomeomorph.measurableEmbedding]
  have hpoint (y : W') :
      σ (v (φ y) * (β (g • φ y) (φ x) * e (φ x - g • φ y))) =
        transport μ μ' hβ hφ v y * (β' (g' • y) x * e' (x - g' • y)) := by
    rw [map_mul, map_mul, hact, hβ, ← map_sub, hφ, transport_apply]
    congr 2
    rcases Complex.ringHom_eq_id_or_conj_of_continuous σ.isometry.continuous with rfl | rfl
    · rfl
    · exact he'.conj_apply _
  simp_rw [← hpoint]
  rcases Complex.ringHom_eq_id_or_conj_of_continuous σ.isometry.continuous with rfl | rfl
  · rfl
  · exact integral_conj.symm

include hact in
/-- Transport intertwines Weil operators up to the ratio of their multipliers. Neither
triviality of the cocycles nor nonvanishing of either multiplier is assumed. -/
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
