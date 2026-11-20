/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Distribution.TemperedDistribution
import TauCeti.Analysis.Distribution.TemperedDistribution.SmulLeft

/-!
# Operator fields acting on tempered distributions

Let `F` and `G` be finite-dimensional complex normed spaces and let `A : E → (F →L[ℂ] G)` be a
smooth operator field of temperate growth, for instance a change of frame of a trivialized vector
bundle. This file defines the action `u ↦ A u` of `A` on `F`-valued tempered distributions,
`TemperedDistribution.applyLeftCLM A : 𝓢'(E, F) →L[ℂ] 𝓢'(E, G)`. On the tempered distribution
of a Schwartz function `f` it is the tempered distribution of `x ↦ A x (f x)`
(`TemperedDistribution.applyLeftCLM_toTemperedDistributionCLM_eq`), so it extends pointwise
application, and it is the operator-valued analogue of Mathlib's scalar multiplication
`TemperedDistribution.smulLeftCLM`.

A tempered distribution `u ∈ 𝓢'(E, F)` is a map from scalar test functions to `F`, so a varying
operator cannot be moved onto the test function. Instead, `A u` is defined from the coordinates of
`A` in a basis `(Lᵢ)` of `F →L[ℂ] G`: if `A x = ∑ᵢ aᵢ x • Lᵢ`, then `A u = ∑ᵢ Lᵢ (aᵢ u)`, where
`aᵢ u` is Mathlib's multiplication by a scalar function and `Lᵢ` acts on the values of `aᵢ u`. The
result does not depend on the decomposition: any finite family of scalar functions `aᵢ` of
temperate growth and operators `Lᵢ` with `A x = ∑ᵢ aᵢ x • Lᵢ` gives the same operator
(`TemperedDistribution.applyLeftCLM_eq_sum`). The fixed basis only serves to make the definition.

The action is multiplicative: `A (B u) = (A B) u` for the pointwise composition `A B` of two
operator fields of temperate growth (`TemperedDistribution.applyLeftCLM_applyLeftCLM`), and a
constant field acts through its values (`TemperedDistribution.applyLeftCLM_const`). An operator
field with a pointwise inverse of temperate growth therefore acts invertibly.

## Main declarations

* `TemperedDistribution.applyLeftCLM`: the action of an operator field on tempered distributions.
* `TemperedDistribution.applyLeftCLM_eq_sum`: its expression through any decomposition of the
  operator field into scalar functions times constant operators.
* `TemperedDistribution.applyLeftCLM_toTemperedDistributionCLM_eq`: on Schwartz functions it is
  pointwise application.
* `TemperedDistribution.applyLeftCLM_applyLeftCLM`: it is multiplicative.
-/

public section

noncomputable section

open MeasureTheory
open scoped SchwartzMap

namespace TemperedDistribution

variable {ι E F G H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [NormedAddCommGroup G] [NormedSpace ℂ G]
  [NormedAddCommGroup H] [NormedSpace ℂ H]

/-! ### Operator fields -/

section ApplyLeft

variable [FiniteDimensional ℂ F] [FiniteDimensional ℂ G] [FiniteDimensional ℂ H]

/-- The action `u ↦ A u` of an operator field `A : E → (F →L[ℂ] G)` on `F`-valued tempered
distributions. If `A x = ∑ᵢ aᵢ x • Lᵢ` for scalar functions `aᵢ` of temperate growth, then
`A u = ∑ᵢ Lᵢ (aᵢ u)` (`TemperedDistribution.applyLeftCLM_eq_sum`); on the tempered distribution of
a Schwartz function `f` it is that of `x ↦ A x (f x)`
(`TemperedDistribution.applyLeftCLM_toTemperedDistributionCLM_eq`). If `A` does not have
temperate growth, the value is not meaningful. -/
def applyLeftCLM (A : E → F →L[ℂ] G) : 𝓢'(E, F) →L[ℂ] 𝓢'(E, G) :=
  ∑ i, PointwiseConvergenceCLM.postcomp _ (Module.finBasis ℂ (F →L[ℂ] G) i) ∘L
    smulLeftCLM F (fun x ↦ (Module.finBasis ℂ (F →L[ℂ] G)).repr (A x) i)

/-- **Independence of the decomposition.** If `A x = ∑ᵢ aᵢ x • Lᵢ` for a finite family of scalar
functions `aᵢ` of temperate growth and operators `Lᵢ`, then `A u = ∑ᵢ Lᵢ (aᵢ u)`. -/
theorem applyLeftCLM_eq_sum {s : Finset ι} {a : ι → E → ℂ}
    (ha : ∀ i ∈ s, (a i).HasTemperateGrowth) (L : ι → F →L[ℂ] G) {A : E → F →L[ℂ] G}
    (hA : ∀ x, A x = ∑ i ∈ s, a i x • L i) :
    applyLeftCLM A =
      ∑ i ∈ s, PointwiseConvergenceCLM.postcomp _ (L i) ∘L smulLeftCLM F (a i) := by
  rw [applyLeftCLM]
  set b := Module.finBasis ℂ (F →L[ℂ] G)
  -- The `k`-th coordinate of `A` is the combination `∑ᵢ bₖ(Lᵢ) aᵢ` of the scalar functions.
  have hcoord (k : Fin (Module.finrank ℂ (F →L[ℂ] G))) :
      (fun x ↦ b.repr (A x) k) = fun x ↦ ∑ i ∈ s, b.repr (L i) k * a i x := by
    ext x
    simp [hA, mul_comm]
  have hc (k : Fin (Module.finrank ℂ (F →L[ℂ] G))) :
      (fun x ↦ b.repr (A x) k).HasTemperateGrowth := by
    rw [hcoord]
    exact .sum fun i hi ↦ by have := ha i hi; fun_prop
  -- Hence the test function `bₖ(A) φ` is the same combination of the test functions `aᵢ φ`.
  have hφ (φ : 𝓢(E, ℂ)) (k : Fin (Module.finrank ℂ (F →L[ℂ] G))) :
      SchwartzMap.smulLeftCLM ℂ (fun x ↦ b.repr (A x) k) φ =
        ∑ i ∈ s, b.repr (L i) k • SchwartzMap.smulLeftCLM ℂ (a i) φ := by
    ext x
    rw [SchwartzMap.smulLeftCLM_apply_apply (hc k), congrFun (hcoord k) x]
    simp only [smul_eq_mul, Finset.sum_mul, mul_assoc, sum_apply, smul_apply]
    refine Finset.sum_congr rfl fun i hi ↦ ?_
    rw [SchwartzMap.smulLeftCLM_apply_apply (ha i hi), smul_eq_mul]
  ext u φ
  -- A constant operator acts on the values of a tempered distribution.
  have hpost (L : F →L[ℂ] G) (T : 𝓢'(E, F)) :
      PointwiseConvergenceCLM.postcomp _ L T φ = L (T φ) :=
    (rfl)
  simp only [sum_apply, ContinuousLinearMap.comp_apply, hpost, smulLeftCLM_apply_apply, hφ,
    map_sum, map_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  conv_rhs => rw [← b.sum_repr (L i)]
  simp only [sum_apply, smul_apply]

/-- The definition of `TemperedDistribution.applyLeftCLM` through the coordinates in a basis:
an operator field of temperate growth acts through its expansion `A x = ∑ₖ aₖ x • Lₖ` in any basis
`(Lₖ)` of `F →L[ℂ] G`. -/
theorem applyLeftCLM_eq_sum_basis {κ : Type*} [Fintype κ] (b : Module.Basis κ ℂ (F →L[ℂ] G))
    {A : E → F →L[ℂ] G} (hA : A.HasTemperateGrowth) :
    applyLeftCLM A =
      ∑ k, PointwiseConvergenceCLM.postcomp _ (b k) ∘L smulLeftCLM F (fun x ↦ b.repr (A x) k) :=
  applyLeftCLM_eq_sum (fun k _ ↦
    ((b.coord k).toContinuousLinearMap.restrictScalars ℝ).hasTemperateGrowth.comp hA) b
    fun x ↦ (b.sum_repr (A x)).symm

/-- A scalar function times a constant operator acts as the multiplication by the function
followed by the operator. -/
theorem applyLeftCLM_smul_const {g : E → ℂ} (hg : g.HasTemperateGrowth) (L : F →L[ℂ] G) :
    applyLeftCLM (fun x ↦ g x • L) = PointwiseConvergenceCLM.postcomp _ L ∘L smulLeftCLM F g := by
  simpa using applyLeftCLM_eq_sum (s := {()}) (fun _ _ ↦ hg) (fun _ ↦ L) (A := fun x ↦ g x • L)
    (fun x ↦ by simp)

/-- A constant operator field acts on the values of a tempered distribution. -/
@[simp]
theorem applyLeftCLM_const (L : F →L[ℂ] G) :
    applyLeftCLM (fun _ : E ↦ L) = PointwiseConvergenceCLM.postcomp _ L := by
  ext1 u
  simpa using congrArg (· u)
    (applyLeftCLM_smul_const (Function.HasTemperateGrowth.const (E := E) (1 : ℂ)) L)

/-- The identity operator field acts as the identity. -/
theorem applyLeftCLM_id :
    applyLeftCLM (fun _ : E ↦ ContinuousLinearMap.id ℂ F) =
      ContinuousLinearMap.id ℂ 𝓢'(E, F) := by
  rw [applyLeftCLM_const]
  -- Applying the identity to the values does not change a tempered distribution.
  rfl

/-- **Multiplicativity.** For operator fields `A` and `B` of temperate growth, `A (B u) = (A B) u`
for the pointwise composition `A B`. -/
theorem applyLeftCLM_applyLeftCLM {A : E → G →L[ℂ] H} {B : E → F →L[ℂ] G}
    (hA : A.HasTemperateGrowth) (hB : B.HasTemperateGrowth) (u : 𝓢'(E, F)) :
    applyLeftCLM A (applyLeftCLM B u) = applyLeftCLM (fun x ↦ A x ∘L B x) u := by
  set a := Module.finBasis ℂ (G →L[ℂ] H)
  set b := Module.finBasis ℂ (F →L[ℂ] G)
  have ha k : (fun x ↦ a.repr (A x) k).HasTemperateGrowth :=
    ((a.coord k).toContinuousLinearMap.restrictScalars ℝ).hasTemperateGrowth.comp hA
  have hb k : (fun x ↦ b.repr (B x) k).HasTemperateGrowth :=
    ((b.coord k).toContinuousLinearMap.restrictScalars ℝ).hasTemperateGrowth.comp hB
  -- Expand `A B` through the products of the coordinates of `A` and `B`.
  rw [applyLeftCLM_eq_sum (ι := Fin (Module.finrank ℂ (G →L[ℂ] H)) ×
      Fin (Module.finrank ℂ (F →L[ℂ] G))) (s := Finset.univ)
      (a := fun kl x ↦ a.repr (A x) kl.1 * b.repr (B x) kl.2)
      (fun kl _ ↦ (ha kl.1).mul (hb kl.2)) (fun kl ↦ a kl.1 ∘L b kl.2) (fun x ↦ by
        ext v
        conv_lhs => rw [ContinuousLinearMap.comp_apply, ← a.sum_repr (A x), ← b.sum_repr (B x)]
        simp only [sum_apply, smul_apply, map_sum, map_smul, Fintype.sum_prod_type,
          Finset.smul_sum, smul_smul, ContinuousLinearMap.comp_apply]
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun _ _ ↦ Finset.sum_congr rfl fun _ _ ↦ by rw [mul_comm]),
    applyLeftCLM_eq_sum_basis a hA, applyLeftCLM_eq_sum_basis b hB, Fintype.sum_prod_type]
  simp only [sum_apply, ContinuousLinearMap.comp_apply, map_sum, postcomp_smulLeftCLM,
    smulLeftCLM_smulLeftCLM_apply (hb _) (ha _)]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ ↦ Finset.sum_congr rfl fun l _ ↦ ?_
  rw [mul_comm]
  -- Two constant operators act on the values one after the other.
  rfl

variable [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] {μ : Measure E}
  [μ.HasTemperateGrowth]

/-- **Pointwise application.** On the tempered distribution of a Schwartz function `f`, an operator
field `A` of temperate growth acts as the pointwise application `x ↦ A x (f x)`. -/
theorem applyLeftCLM_toTemperedDistributionCLM_eq {A : E → F →L[ℂ] G}
    (hA : A.HasTemperateGrowth) (f : 𝓢(E, F)) :
    applyLeftCLM A (SchwartzMap.toTemperedDistributionCLM E F μ f) =
      SchwartzMap.toTemperedDistributionCLM E G μ
        (SchwartzMap.bilinLeftCLM (ContinuousLinearMap.apply ℂ G) hA f) := by
  have := FiniteDimensional.completeSpace ℂ F
  have := FiniteDimensional.completeSpace ℂ G
  set b := Module.finBasis ℂ (F →L[ℂ] G)
  have hb k : (fun x ↦ b.repr (A x) k).HasTemperateGrowth :=
    ((b.coord k).toContinuousLinearMap.restrictScalars ℝ).hasTemperateGrowth.comp hA
  -- A constant operator `L` commutes with the embedding of Schwartz functions.
  have hpost (L : F →L[ℂ] G) (g : 𝓢(E, F)) :
      PointwiseConvergenceCLM.postcomp _ L (SchwartzMap.toTemperedDistributionCLM E F μ g) =
        SchwartzMap.toTemperedDistributionCLM E G μ (g.postcompCLM L) := by
    ext φ
    simp only [PointwiseConvergenceCLM.postcomp_apply,
      SchwartzMap.toTemperedDistributionCLM_apply_apply, SchwartzMap.postcompCLM_apply,
      ← map_smul]
    exact (L.integral_comp_comm
      ((φ.integrable (μ := μ)).smul_of_top_left (g.memLp_top μ))).symm
  -- On Schwartz functions, `A` is the sum of its coordinates times the basis operators.
  have hsum : SchwartzMap.bilinLeftCLM (ContinuousLinearMap.apply ℂ G) hA f =
      ∑ k, (SchwartzMap.smulLeftCLM F (fun x ↦ b.repr (A x) k) f).postcompCLM (b k) := by
    ext x
    simp only [SchwartzMap.bilinLeftCLM_apply, ContinuousLinearMap.apply_apply, sum_apply,
      SchwartzMap.postcompCLM_apply, SchwartzMap.smulLeftCLM_apply_apply (hb _), map_smul]
    conv_lhs => rw [← b.sum_repr (A x)]
    simp only [sum_apply, smul_apply]
  simp only [applyLeftCLM_eq_sum_basis b hA, sum_apply, ContinuousLinearMap.comp_apply,
    smulLeftCLM_toTemperedDistributionCLM_eq, hpost, hsum, map_sum]

end ApplyLeft

end TemperedDistribution
