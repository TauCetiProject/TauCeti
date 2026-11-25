/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Distribution.TemperedDistribution
public import Mathlib.Topology.Algebra.Module.FiniteDimension
public import TauCeti.Topology.Algebra.Module.FiniteDimension
import TauCeti.Analysis.Distribution.SchwartzSpace.Basic
import TauCeti.Analysis.Distribution.TemperateGrowth
import TauCeti.Analysis.Distribution.TemperedDistribution.Lp
import TauCeti.Analysis.Distribution.TemperedDistribution.SmulLeft
import TauCeti.Topology.Algebra.Module.Spaces.PointwiseConvergenceCLM

/-!
# Multiplication of vector-valued tempered distributions by matrix-valued functions

Let `F` and `G` be finite-dimensional complex normed spaces and `A : E → (F →L[ℂ] G)` a function of
temperate growth, for instance a smooth matrix-valued function with bounded derivatives. For an
`F`-valued tempered distribution `u`, the product `A u` is the `G`-valued tempered distribution
`TemperedDistribution.mulLeftCLM A u`. On the distribution of a Schwartz function `f` it is the
distribution of the pointwise product `x ↦ A x (f x)`
(`TemperedDistribution.mulLeftCLM_toTemperedDistributionCLM_eq`). These are the changes of frame
of the coefficients of vector-valued distributions, the operations under which Sobolev and Besov
norms of sections of vector bundles have to be compared.

A tempered distribution pairs only with scalar test functions, so `A u` cannot be defined by
transposing `A` on test functions as for a scalar function `g`
(`TemperedDistribution.smulLeftCLM`). Instead, whenever `A x = ∑ i ∈ s, c i x • L i` with
scalar functions `c i` of temperate growth and fixed operators `L i : F →L[ℂ] G`,

`A u = ∑ i ∈ s, L i (c i u)`

(`TemperedDistribution.mulLeftCLM_eq_sum`), where `L i` acts on the values of the distribution
`c i u`. The definition uses the coordinates `Module.Basis.coord` of `A` in the basis
`Module.finBasis ℂ (F →L[ℂ] G)`, and this formula shows that the result does not depend on the
basis. It reduces statements about `A u` to the scalar multiplication and to constant operators.

## Main declarations

* `TemperedDistribution.mulLeftCLM A`: multiplication by `A`, a continuous linear map
  `𝓢'(E, F) →L[ℂ] 𝓢'(E, G)`.
* `TemperedDistribution.mulLeftCLM_apply_apply`: the action of `A u` on test functions, through
  the coordinates of `A` in the basis `Module.finBasis ℂ (F →L[ℂ] G)`.
* `TemperedDistribution.mulLeftCLM_apply_apply_of_eq_sum`, `TemperedDistribution.mulLeftCLM_eq_sum`:
  the action of `A u` on test functions, for any decomposition `A x = ∑ i ∈ s, c i x • L i`.
* `TemperedDistribution.mulLeftCLM_smul_const`: the case `A x = c x • L` of a single term; in
  particular a constant `A` acts on the values (`TemperedDistribution.mulLeftCLM_const`), and
  `A x = g x • id` is the scalar multiplication `TemperedDistribution.smulLeftCLM`
  (`TemperedDistribution.mulLeftCLM_smul_id`).
* `TemperedDistribution.mulLeftCLM_add`, `TemperedDistribution.mulLeftCLM_sum`,
  `TemperedDistribution.mulLeftCLM_smul`: linearity in multipliers of temperate growth.
* `TemperedDistribution.mulLeftCLM_compL_mulLeftCLM`,
  `TemperedDistribution.mulLeftCLM_mulLeftCLM_apply`: `B (A u) = (B A) u`, so that a pointwise
  invertible `A` whose inverse is again of temperate growth acts invertibly; the identity acts as
  the identity (`TemperedDistribution.mulLeftCLM_id_apply`).
* `TemperedDistribution.mulLeftCLM_toTemperedDistributionCLM_eq`: on Schwartz functions `A u` is
  the pointwise product, for the embedding against any measure of temperate growth.
-/

public section

noncomputable section

open MeasureTheory
open scoped SchwartzMap

namespace TemperedDistribution

variable {E F G H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [NormedAddCommGroup G] [NormedSpace ℂ G]
  [NormedAddCommGroup H] [NormedSpace ℂ H]

variable [FiniteDimensional ℂ F] [FiniteDimensional ℂ G]

/-- **Multiplication by a matrix-valued function.** For `A : E → (F →L[ℂ] G)` of temperate growth,
the product `A u` of an `F`-valued tempered distribution `u` with `A`, a `G`-valued tempered
distribution. It is defined as `∑ k, L k (c k u)` over the basis `L k` of
`Module.finBasis ℂ (F →L[ℂ] G)` and the coordinates `c k` of `A` in this basis
(`Module.Basis.coord`). If `A` does not have temperate growth, this is a junk value that may
depend on the basis, since `TemperedDistribution.smulLeftCLM` is `0` for coordinates without
temperate growth. If `A x = ∑ i ∈ s, c i x • L i` with scalar functions `c i` of temperate
growth, then `A u = ∑ i ∈ s, L i (c i u)` (`TemperedDistribution.mulLeftCLM_eq_sum`); on Schwartz
functions it is the pointwise product
(`TemperedDistribution.mulLeftCLM_toTemperedDistributionCLM_eq`). -/
def mulLeftCLM (A : E → F →L[ℂ] G) : 𝓢'(E, F) →L[ℂ] 𝓢'(E, G) :=
  ∑ k, PointwiseConvergenceCLM.postcomp _ (Module.finBasis ℂ (F →L[ℂ] G) k) ∘L
    smulLeftCLM F
      (LinearMap.toContinuousLinearMap ((Module.finBasis ℂ (F →L[ℂ] G)).coord k) ∘ A)

/-- The product `A u` is `∑ k, L k (c k u)`, for the basis `L k` of
`Module.finBasis ℂ (F →L[ℂ] G)` and the coordinates `c k` of `A` in it. -/
theorem mulLeftCLM_def (A : E → F →L[ℂ] G) :
    mulLeftCLM A = ∑ k, PointwiseConvergenceCLM.postcomp _ (Module.finBasis ℂ (F →L[ℂ] G) k) ∘L
      smulLeftCLM F
        (LinearMap.toContinuousLinearMap ((Module.finBasis ℂ (F →L[ℂ] G)).coord k) ∘ A) := by
  rw [mulLeftCLM]

/-- The action of the product `A u` on a test function, through the coordinates of `A` in the
basis `Module.finBasis ℂ (F →L[ℂ] G)`. -/
theorem mulLeftCLM_apply_apply (A : E → F →L[ℂ] G) (u : 𝓢'(E, F)) (φ : 𝓢(E, ℂ)) :
    mulLeftCLM A u φ = ∑ k, Module.finBasis ℂ (F →L[ℂ] G) k
      (u (SchwartzMap.smulLeftCLM ℂ
        (LinearMap.toContinuousLinearMap ((Module.finBasis ℂ (F →L[ℂ] G)).coord k) ∘ A) φ)) := by
  simp only [mulLeftCLM, sum_apply, ContinuousLinearMap.comp_apply,
    PointwiseConvergenceCLM.postcomp_apply_apply, smulLeftCLM_apply_apply]

/-- **The product with a decomposed function.** If `A x = ∑ i ∈ s, c i x • L i` for scalar
functions `c i` of temperate growth and operators `L i`, then `A u` pairs with a test function
`φ` as `∑ i ∈ s, L i (u (c i φ))`. -/
theorem mulLeftCLM_apply_apply_of_eq_sum {ι : Type*} (s : Finset ι) {c : ι → E → ℂ}
    (hc : ∀ i ∈ s, (c i).HasTemperateGrowth) (L : ι → F →L[ℂ] G) {A : E → F →L[ℂ] G}
    (hA : ∀ x, A x = ∑ i ∈ s, c i x • L i) (u : 𝓢'(E, F)) (φ : 𝓢(E, ℂ)) :
    mulLeftCLM A u φ = ∑ i ∈ s, L i (u (SchwartzMap.smulLeftCLM ℂ (c i) φ)) := by
  rw [mulLeftCLM_apply_apply]
  set b := Module.finBasis ℂ (F →L[ℂ] G)
  -- The coordinates of `A` are combinations of the `c i` with constant coefficients.
  have hcoord (k) : SchwartzMap.smulLeftCLM ℂ (LinearMap.toContinuousLinearMap (b.coord k) ∘ A) φ
      = ∑ i ∈ s, b.equivFun (L i) k • SchwartzMap.smulLeftCLM ℂ (c i) φ := by
    have hk : LinearMap.toContinuousLinearMap (b.coord k) ∘ A =
        fun x ↦ ∑ i ∈ s, (b.equivFun (L i) k • c i) x := by
      ext x
      simp [hA x, map_sum, map_smul, mul_comm]
    rw [hk, SchwartzMap.smulLeftCLM_sum (g := fun i ↦ b.equivFun (L i) k • c i)
      fun i hi ↦ (Function.HasTemperateGrowth.const _).mul (hc i hi), sum_apply]
    refine Finset.sum_congr rfl fun i hi ↦ ?_
    rw [SchwartzMap.smulLeftCLM_smul (hc i hi), smul_apply]
  simp_rw [hcoord, map_sum, map_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  conv_rhs => rw [← b.sum_equivFun (L i)]
  simp only [sum_apply, smul_apply, b]

/-- **The product with a decomposed function.** If `A x = ∑ i ∈ s, c i x • L i` for scalar
functions `c i` of temperate growth and operators `L i`, then `A u = ∑ i ∈ s, L i (c i u)`. In
particular `TemperedDistribution.mulLeftCLM` does not depend on the basis of `F →L[ℂ] G` used to
define it. -/
theorem mulLeftCLM_eq_sum {ι : Type*} (s : Finset ι) {c : ι → E → ℂ}
    (hc : ∀ i ∈ s, (c i).HasTemperateGrowth) (L : ι → F →L[ℂ] G) {A : E → F →L[ℂ] G}
    (hA : ∀ x, A x = ∑ i ∈ s, c i x • L i) :
    mulLeftCLM A = ∑ i ∈ s, PointwiseConvergenceCLM.postcomp _ (L i) ∘L smulLeftCLM F (c i) := by
  ext u φ
  rw [mulLeftCLM_apply_apply_of_eq_sum s hc L hA]
  simp only [sum_apply, ContinuousLinearMap.comp_apply,
    PointwiseConvergenceCLM.postcomp_apply_apply, smulLeftCLM_apply_apply]

/-- **A single term.** Multiplication by `x ↦ c x • L` applies `L` to the values of `c u`. -/
theorem mulLeftCLM_smul_const {c : E → ℂ} (hc : c.HasTemperateGrowth) (L : F →L[ℂ] G) :
    mulLeftCLM (fun x ↦ c x • L) =
      PointwiseConvergenceCLM.postcomp _ L ∘L smulLeftCLM F c := by
  simpa using mulLeftCLM_eq_sum {()} (c := fun _ ↦ c) (by simpa using hc) (fun _ ↦ L)
    (fun x ↦ by simp)

/-- **Constant operators.** Multiplication by a constant `L` applies `L` to the values of `u`. -/
@[simp]
theorem mulLeftCLM_const (L : F →L[ℂ] G) :
    mulLeftCLM (fun _ : E ↦ L) = PointwiseConvergenceCLM.postcomp _ L := by
  have h := mulLeftCLM_smul_const (E := E) (Function.HasTemperateGrowth.const (1 : ℂ)) L
  simp only [one_smul] at h
  rw [h]
  ext u φ
  simp only [ContinuousLinearMap.comp_apply, smulLeftCLM_const, one_smul]

/-- **The identity.** Multiplication by the constant identity is the identity. -/
theorem mulLeftCLM_id_apply (u : 𝓢'(E, F)) :
    mulLeftCLM (fun _ : E ↦ ContinuousLinearMap.id ℂ F) u = u := by
  ext φ
  rw [mulLeftCLM_const, PointwiseConvergenceCLM.postcomp_apply_apply,
    ContinuousLinearMap.id_apply]

/-- **Scalar functions.** Multiplication by `x ↦ g x • id` is the multiplication by the scalar
function `g`. -/
theorem mulLeftCLM_smul_id {g : E → ℂ} (hg : g.HasTemperateGrowth) :
    mulLeftCLM (fun x ↦ g x • ContinuousLinearMap.id ℂ F) = smulLeftCLM F g := by
  rw [mulLeftCLM_smul_const hg]
  ext u φ
  simp only [ContinuousLinearMap.comp_apply, PointwiseConvergenceCLM.postcomp_apply_apply,
    ContinuousLinearMap.id_apply]

/-- **Additivity.** For `A` and `B` of temperate growth, `(A + B) u = A u + B u`. -/
theorem mulLeftCLM_add {A B : E → F →L[ℂ] G} (hA : A.HasTemperateGrowth)
    (hB : B.HasTemperateGrowth) :
    mulLeftCLM (A + B) = mulLeftCLM A + mulLeftCLM B := by
  unfold mulLeftCLM
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  set c := LinearMap.toContinuousLinearMap ((Module.finBasis ℂ (F →L[ℂ] G)).coord k)
  have hcomp : c ∘ (A + B) = c ∘ A + c ∘ B := by
    ext x
    simp
  rw [hcomp, smulLeftCLM_add (hA.continuousLinearMap_comp c) (hB.continuousLinearMap_comp c),
    ContinuousLinearMap.comp_add]

/-- **Finite sums.** For `A i` of temperate growth, `(∑ i ∈ s, A i) u = ∑ i ∈ s, A i u`. -/
theorem mulLeftCLM_sum {ι : Type*} {A : ι → E → F →L[ℂ] G} {s : Finset ι}
    (hA : ∀ i ∈ s, (A i).HasTemperateGrowth) :
    mulLeftCLM (fun x ↦ ∑ i ∈ s, A i x) = ∑ i ∈ s, mulLeftCLM (A i) := by
  simp only [mulLeftCLM_def]
  set b := Module.finBasis ℂ (F →L[ℂ] G)
  have h (k) : smulLeftCLM F
      (LinearMap.toContinuousLinearMap (b.coord k) ∘ fun x ↦ ∑ i ∈ s, A i x) =
      ∑ i ∈ s, smulLeftCLM F (LinearMap.toContinuousLinearMap (b.coord k) ∘ A i) := by
    have hk : (LinearMap.toContinuousLinearMap (b.coord k) ∘ fun x ↦ ∑ i ∈ s, A i x) =
        fun x ↦ ∑ i ∈ s, (LinearMap.toContinuousLinearMap (b.coord k) ∘ A i) x := by
      funext x
      simp [map_sum]
    rw [hk]
    exact smulLeftCLM_sum fun i hi ↦ (hA i hi).continuousLinearMap_comp _
  simp only [h, ContinuousLinearMap.comp_finsetSum]
  exact Finset.sum_comm

/-- **Scalar multiples.** For `A` of temperate growth, `(c • A) u = c • A u`. -/
theorem mulLeftCLM_smul {A : E → F →L[ℂ] G} (hA : A.HasTemperateGrowth) (c : ℂ) :
    mulLeftCLM (c • A) = c • mulLeftCLM A := by
  simp only [mulLeftCLM_def, Finset.smul_sum]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  set ℓ := LinearMap.toContinuousLinearMap ((Module.finBasis ℂ (F →L[ℂ] G)).coord k)
  have hk : ℓ ∘ (c • A) = c • (ℓ ∘ A) := by
    ext x
    simp
  rw [hk, smulLeftCLM_smul (hA.continuousLinearMap_comp ℓ), ContinuousLinearMap.comp_smul]

/-- **Composition.** For `A : E → (F →L[ℂ] G)` and `B : E → (G →L[ℂ] H)` of temperate growth,
`B (A u) = (B A) u`, where `B A` is the pointwise composition `x ↦ B x ∘ A x`. -/
theorem mulLeftCLM_compL_mulLeftCLM [FiniteDimensional ℂ H] {A : E → F →L[ℂ] G}
    {B : E → G →L[ℂ] H} (hA : A.HasTemperateGrowth) (hB : B.HasTemperateGrowth) :
    mulLeftCLM B ∘L mulLeftCLM A = mulLeftCLM (fun x ↦ (B x).comp (A x)) := by
  ext u φ
  rw [ContinuousLinearMap.comp_apply, mulLeftCLM_apply_apply]
  set a := Module.finBasis ℂ (F →L[ℂ] G)
  set b := Module.finBasis ℂ (G →L[ℂ] H)
  have hca (k) := hA.continuousLinearMap_comp (LinearMap.toContinuousLinearMap (a.coord k))
  have hcb (l) := hB.continuousLinearMap_comp (LinearMap.toContinuousLinearMap (b.coord l))
  rw [mulLeftCLM_apply_apply_of_eq_sum (Finset.univ : Finset (_ × _))
      (c := fun lk x ↦ b.coord lk.1 (B x) * a.coord lk.2 (A x))
      (fun lk _ ↦ (hcb lk.1).mul (hca lk.2)) (fun lk ↦ (b lk.1).comp (a lk.2))
      (fun x ↦ (B x).comp_eq_sum_coord a b (A x)), Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun l _ ↦ ?_
  rw [mulLeftCLM_apply_apply, map_sum]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  -- Multiplying by the coordinates of `B` and then of `A` is multiplying by their product.
  have hφ : SchwartzMap.smulLeftCLM ℂ (LinearMap.toContinuousLinearMap (a.coord k) ∘ A)
        (SchwartzMap.smulLeftCLM ℂ (LinearMap.toContinuousLinearMap (b.coord l) ∘ B) φ) =
      SchwartzMap.smulLeftCLM ℂ (fun x ↦ b.coord l (B x) * a.coord k (A x)) φ := by
    rw [SchwartzMap.smulLeftCLM_smulLeftCLM_apply (hca k) (hcb l)]
    congr 2
    funext x
    simp only [Pi.mul_apply, Function.comp_apply, LinearMap.coe_toContinuousLinearMap']
    ring
  rw [hφ, ContinuousLinearMap.comp_apply]

/-- **Composition**, applied to a distribution: `B (A u) = (B A) u` for `A` and `B` of temperate
growth. -/
@[simp]
theorem mulLeftCLM_mulLeftCLM_apply [FiniteDimensional ℂ H] {A : E → F →L[ℂ] G}
    {B : E → G →L[ℂ] H} (hA : A.HasTemperateGrowth) (hB : B.HasTemperateGrowth) (u : 𝓢'(E, F)) :
    mulLeftCLM B (mulLeftCLM A u) = mulLeftCLM (fun x ↦ (B x).comp (A x)) u := by
  rw [← mulLeftCLM_compL_mulLeftCLM hA hB, ContinuousLinearMap.comp_apply]

section InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [CompleteSpace F] [CompleteSpace G]

/-- **Products of Schwartz functions.** On the tempered distribution of a Schwartz function `f`,
embedded against any measure `μ` of temperate growth, multiplication by `A` is the tempered
distribution of the pointwise product `x ↦ A x (f x)`. -/
theorem mulLeftCLM_toTemperedDistributionCLM_eq {μ : Measure E} [μ.HasTemperateGrowth]
    {A : E → F →L[ℂ] G} (hA : A.HasTemperateGrowth) (f : 𝓢(E, F)) :
    mulLeftCLM A (SchwartzMap.toTemperedDistributionCLM E F μ f) =
      SchwartzMap.toTemperedDistributionCLM E G μ
        (SchwartzMap.bilinLeftCLM (ContinuousLinearMap.apply ℂ G) hA f) := by
  -- Expand `A` in the basis `Module.finBasis ℂ (F →L[ℂ] G)` on both sides.
  set b := Module.finBasis ℂ (F →L[ℂ] G)
  have hc (k) := hA.continuousLinearMap_comp (LinearMap.toContinuousLinearMap (b.coord k))
  have hexp (x) : A x = ∑ k, (LinearMap.toContinuousLinearMap (b.coord k) ∘ A) x • b k := by
    simp
  rw [mulLeftCLM_eq_sum Finset.univ (fun k _ ↦ hc k) b hexp,
    SchwartzMap.bilinLeftCLM_apply_eq_sum Finset.univ (fun k _ ↦ hc k) b hA hexp]
  ext φ
  simp only [sum_apply, ContinuousLinearMap.comp_apply, map_sum,
    smulLeftCLM_toTemperedDistributionCLM_eq, PointwiseConvergenceCLM.postcomp_apply_apply]
  exact Finset.sum_congr rfl fun k _ ↦
    (SchwartzMap.toTemperedDistributionCLM_postcompCLM_apply _ _ _).symm

end InnerProductSpace

end TemperedDistribution
