/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Compact.Integrated
import Mathlib.Analysis.Normed.Operator.BanachSteinhaus

/-!
# The integrated operator of a strongly continuous Banach representation

Let `π` be a strongly continuous representation of a compact group `G` on a Banach space `V` over
`ℝ` or `ℂ`: every orbit `g ↦ π g v` is continuous, while `g ↦ π g` need not be continuous in the
operator norm. A continuous function `f` on `G` acts on `V` by the **strong integrated operator**

`π(f) v = ∫ g, f g • π g v ∂(haarProb G)`,

a bounded operator by the Banach–Steinhaus theorem. When `π` is continuous in the operator norm it
is `ContRepresentation.integratedOperator`. It is linear in `f`, for a class function it commutes
with the action, and it is natural with respect to continuous intertwiners.

## Main definitions

* `ContRepresentation.strongIntegratedOperator π hπ f`: the operator `v ↦ ∫ g, f g • π g v`.
* `ContRepresentation.strongIntegratedOperatorₗ`: the same, linear in the acting function.

## Main results

* `ContRepresentation.strongIntegratedOperator_eq_integratedOperator`: for an operator-norm
  continuous representation the strong integrated operator is `integratedOperator`.
* `ContRepresentation.strongIntegratedOperator_comp`: a class function acts by an intertwiner.
* `ContRepresentation.comp_strongIntegratedOperator`: naturality in continuous intertwiners.
* `ContRepresentation.apply_strongIntegratedOperator`: translating the output left-translates the
  acting function.

## References

* T. Bröcker and T. tom Dieck, *Representations of Compact Lie Groups*, Springer GTM 98 (1985),
  Chapter III.
* J. Bernstein, B. Krötz, *Smooth Fréchet globalizations of Harish-Chandra modules*, §4.1.
-/

public section

noncomputable section

open MeasureTheory TauCeti

namespace ContRepresentation

variable {k G V : Type*} [RCLike k] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [MeasurableSpace G] [BorelSpace G]
  [NormedAddCommGroup V] [NormedSpace k V] [NormedSpace ℝ V] [SMulCommClass ℝ k V]
  (π : ContRepresentation k G V) (hπ : ∀ v, Continuous fun g ↦ π g v)

/-- The continuous map `g ↦ f g • π g v` integrated by the strong integrated operator. -/
private def weightedOrbit (f : C(G, k)) (v : V) : C(G, V) :=
  ⟨fun g ↦ f g • π g v, f.continuous.smul (hπ v)⟩

omit [IsTopologicalGroup G] [CompactSpace G] [MeasurableSpace G] [BorelSpace G]
  [NormedSpace ℝ V] [SMulCommClass ℝ k V] in
private theorem weightedOrbit_apply (f : C(G, k)) (v : V) (g : G) :
    weightedOrbit π hπ f v g = f g • π g v :=
  (rfl)

variable [CompleteSpace V]

/-- The **strong integrated operator** `π(f) v = ∫ g, f g • π g v` of a continuous function `f` on
a strongly continuous Banach representation of a compact group. It is bounded because the
operators `π g` are uniformly bounded, by the Banach–Steinhaus theorem. -/
def strongIntegratedOperator (f : C(G, k)) : V →L[k] V :=
  LinearMap.mkContinuousOfExistsBound
    { toFun v := haarAverage G (𝕜 := k) (weightedOrbit π hπ f v)
      map_add' v w := by
        rw [← map_add]
        congr 1
        ext g
        simp [weightedOrbit_apply]
      map_smul' c v := by
        rw [RingHom.id_apply, ← map_smul]
        congr 1
        ext g
        simp [weightedOrbit_apply, smul_comm (f g) c] } <| by
    obtain ⟨C, hC⟩ := banach_steinhaus (g := fun g : G ↦ (π g : V →L[k] V)) fun v ↦ by
      obtain ⟨C, hC⟩ := isCompact_univ.exists_bound_of_continuousOn (hπ v).continuousOn
      exact ⟨C, fun g ↦ hC g (Set.mem_univ g)⟩
    refine ⟨‖f‖ * C, fun v ↦ (norm_haarAverage_apply_le G _).trans ?_⟩
    refine ContinuousMap.norm_le _ (by
      have := (norm_nonneg _).trans (hC 1)
      positivity) |>.2 fun g ↦ ?_
    rw [weightedOrbit_apply, norm_smul, mul_assoc]
    exact mul_le_mul (f.norm_coe_le_norm g) (((π g : V →L[k] V).le_opNorm v).trans
      (mul_le_mul_of_nonneg_right (hC g) (norm_nonneg v))) (norm_nonneg _) (norm_nonneg _)

/-- The strong integrated operator is the Haar average of the weighted orbit. -/
private theorem strongIntegratedOperator_apply_eq_haarAverage (f : C(G, k)) (v : V) :
    strongIntegratedOperator π hπ f v = haarAverage G (𝕜 := k) (weightedOrbit π hπ f v) :=
  (rfl)

/-- The strong integrated operator is the Haar integral of the weighted orbit. -/
theorem strongIntegratedOperator_apply (f : C(G, k)) (v : V) :
    strongIntegratedOperator π hπ f v = ∫ g, f g • π g v ∂haarProb G :=
  haarAverage_apply G _

/-! ### Linearity in the acting function -/

@[simp]
theorem strongIntegratedOperator_zero : strongIntegratedOperator π hπ (0 : C(G, k)) = 0 := by
  ext v
  have hzero : weightedOrbit π hπ (0 : C(G, k)) v = 0 := by
    ext g
    simp [weightedOrbit_apply]
  rw [strongIntegratedOperator_apply_eq_haarAverage, hzero, map_zero,
    zero_apply]

@[simp]
theorem strongIntegratedOperator_add (f₁ f₂ : C(G, k)) :
    strongIntegratedOperator π hπ (f₁ + f₂) =
      strongIntegratedOperator π hπ f₁ + strongIntegratedOperator π hπ f₂ := by
  ext v
  have hadd : weightedOrbit π hπ (f₁ + f₂) v =
      weightedOrbit π hπ f₁ v + weightedOrbit π hπ f₂ v := by
    ext g
    simp [weightedOrbit_apply, add_smul]
  rw [add_apply, strongIntegratedOperator_apply_eq_haarAverage,
    strongIntegratedOperator_apply_eq_haarAverage, strongIntegratedOperator_apply_eq_haarAverage,
    hadd, map_add]

@[simp]
theorem strongIntegratedOperator_smul (c : k) (f : C(G, k)) :
    strongIntegratedOperator π hπ (c • f) = c • strongIntegratedOperator π hπ f := by
  ext v
  have hsmul : weightedOrbit π hπ (c • f) v = c • weightedOrbit π hπ f v := by
    ext g
    simp [weightedOrbit_apply, mul_smul]
  rw [smul_apply, strongIntegratedOperator_apply_eq_haarAverage,
    strongIntegratedOperator_apply_eq_haarAverage, hsmul, map_smul]

/-- The strong integrated operator, bundled as a linear map in the acting function. Bundling
supplies the remaining additive identities (`map_neg`, `map_sub`, `map_sum`) through the
`LinearMap` API. -/
def strongIntegratedOperatorₗ : C(G, k) →ₗ[k] V →L[k] V where
  toFun := strongIntegratedOperator π hπ
  map_add' := strongIntegratedOperator_add π hπ
  map_smul' := strongIntegratedOperator_smul π hπ

@[simp]
theorem strongIntegratedOperatorₗ_apply (f : C(G, k)) :
    strongIntegratedOperatorₗ π hπ f = strongIntegratedOperator π hπ f :=
  (rfl)

/-! ### Comparison, intertwining and naturality -/

/-- For a representation that is continuous in the operator norm, the strong integrated operator
is `integratedOperator`. -/
theorem strongIntegratedOperator_eq_integratedOperator (hπ' : Continuous π) (f : C(G, k)) :
    strongIntegratedOperator π hπ f = integratedOperator π hπ' f := by
  ext v
  rw [strongIntegratedOperator_apply, integratedOperator_apply]

/-- **A class function acts by an intertwiner.** -/
theorem strongIntegratedOperator_comp {f : C(G, k)} (hf : ∀ g h : G, f (h * g * h⁻¹) = f g)
    (h : G) :
    (strongIntegratedOperator π hπ f).comp (π h) =
      (π h : V →L[k] V).comp (strongIntegratedOperator π hπ f) := by
  ext v
  have hint : Integrable (fun g ↦ f g • π g v) (haarProb G) :=
    integrable_continuousMap G (weightedOrbit π hπ f v)
  have hclass (g : G) : f (g * h⁻¹) = f (h⁻¹ * g) := by
    simpa [mul_assoc] using (hf (g * h⁻¹) h⁻¹).symm
  simp only [ContinuousLinearMap.comp_apply]
  rw [strongIntegratedOperator_apply, strongIntegratedOperator_apply,
    ← (π h : V →L[k] V).integral_comp_comm hint]
  calc ∫ g, f g • π g (π h v) ∂haarProb G
      = ∫ g, f (g * h⁻¹) • π g v ∂haarProb G := by
        rw [← integral_mul_right_eq_self (fun g ↦ f g • π g (π h v)) h⁻¹]
        congr 1 with g
        simp only [← mul_apply_eq_comp, ← map_mul, inv_mul_cancel_right]
    _ = ∫ g, f (h⁻¹ * g) • π g v ∂haarProb G := by simp only [hclass]
    _ = ∫ g, (π h : V →L[k] V) (f g • π g v) ∂haarProb G := by
        rw [← integral_mul_left_eq_self (fun g ↦ (π h : V →L[k] V) (f g • π g v)) h⁻¹]
        congr 1 with g
        rw [map_smul, ← mul_apply_eq_comp, ← map_mul, mul_inv_cancel_left]

/-- **Translating the output translates the function.** `π h (π(f) v) = π(f(h⁻¹ ·)) v`: applying
`π h` after the strong integrated operator left-translates the acting function. -/
theorem apply_strongIntegratedOperator (f : C(G, k)) (h : G) (v : V) :
    π h (strongIntegratedOperator π hπ f v) =
      strongIntegratedOperator π hπ (f.comp (ContinuousMap.mulLeft h⁻¹)) v := by
  have hint : Integrable (fun g ↦ f g • π g v) (haarProb G) :=
    integrable_continuousMap G (weightedOrbit π hπ f v)
  rw [strongIntegratedOperator_apply, strongIntegratedOperator_apply,
    ← (π h : V →L[k] V).integral_comp_comm hint,
    ← integral_mul_left_eq_self (fun g ↦ (f.comp (ContinuousMap.mulLeft h⁻¹)) g • π g v) h]
  congr 1 with g
  simp only [ContinuousMap.comp_apply, ContinuousMap.coe_mulLeft, inv_mul_cancel_left, map_smul,
    map_mul, mul_apply_eq_comp]

/-- **Naturality.** A continuous intertwiner between strongly continuous Banach representations
commutes with the strong integrated operators of the same function. -/
theorem comp_strongIntegratedOperator {W : Type*} [NormedAddCommGroup W] [NormedSpace k W]
    [NormedSpace ℝ W] [SMulCommClass ℝ k W] [CompleteSpace W] (ρ : ContRepresentation k G W)
    (hρ : ∀ w, Continuous fun g ↦ ρ g w) (T : ContIntertwiningMap π ρ) (f : C(G, k)) :
    T.toContinuousLinearMap.comp (strongIntegratedOperator π hπ f) =
      (strongIntegratedOperator ρ hρ f).comp T.toContinuousLinearMap := by
  ext v
  have hint : Integrable (fun g ↦ f g • π g v) (haarProb G) :=
    integrable_continuousMap G (weightedOrbit π hπ f v)
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
    strongIntegratedOperator_apply, strongIntegratedOperator_apply,
    ← T.toContinuousLinearMap.integral_comp_comm hint]
  refine integral_congr_ae (Filter.Eventually.of_forall fun g ↦ ?_)
  simp only [map_smul]
  congr 1
  exact T.isIntertwining g v

end ContRepresentation
