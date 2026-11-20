/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Distribution.TemperedDistribution
import TauCeti.Analysis.Distribution.SchwartzSpace.Basic
import TauCeti.Analysis.Distribution.TemperateGrowth
import TauCeti.Analysis.Distribution.TemperedDistribution.Lp
import TauCeti.Analysis.Distribution.TemperedDistribution.SmulLeft
import TauCeti.Topology.Algebra.Module.Spaces.PointwiseConvergenceCLM

/-!
# Multiplication of vector-valued tempered distributions by operator-valued functions

Let `F` and `G` be finite-dimensional complex normed spaces and `A : E → (F →L[ℂ] G)` a function
of temperate growth. On `F`-valued Schwartz functions, multiplication by `A` is Mathlib's
`SchwartzMap.bilinLeftCLM (ContinuousLinearMap.apply ℂ G) hA`, sending `u` to
`x ↦ A x (u x)`. This file extends it to `F`-valued tempered distributions
(`TemperedDistribution.applyLeftCLM A : 𝓢'(E, F) →L[ℂ] 𝓢'(E, G)`). This is how a change of frame
of a vector bundle, given in a chart by a matrix-valued function, acts on the local
representatives of distributional sections.

Writing `A x = ∑ᵢ gᵢ(x) • Lᵢ` with scalar functions `gᵢ` of temperate growth and constant maps
`Lᵢ : F →L[ℂ] G`, multiplication by `A` is `u ↦ ∑ᵢ Lᵢ (gᵢ u)`, where `gᵢ u` is Mathlib's
`TemperedDistribution.smulLeftCLM` and `Lᵢ` acts on the values of the distribution. The
definition uses the coordinates of `A` in one basis of `F →L[ℂ] G`, and
`TemperedDistribution.applyLeftCLM_eq_sum` shows that every such expansion gives the same operator.
Scalar multiples of the identity and constant maps are the two basic cases, and multiplication by
`A` followed by multiplication by `B` is multiplication by `x ↦ B x ∘L A x`.

## Main declarations

* `TemperedDistribution.applyLeftCLM`: multiplication by an operator-valued function.
* `TemperedDistribution.applyLeftCLM_of_not_hasTemperateGrowth`: it is `0` for `A` without
  temperate growth.
* `TemperedDistribution.applyLeftCLM_eq_sum`: its expansion along any finite decomposition
  `A x = ∑ᵢ gᵢ(x) • Lᵢ`, and `TemperedDistribution.applyLeftCLM_apply_apply` its value on a test
  function.
* `TemperedDistribution.applyLeftCLM_add`, `TemperedDistribution.applyLeftCLM_smul`,
  `TemperedDistribution.applyLeftCLM_sum`: it is linear in multipliers of temperate growth.
* `TemperedDistribution.applyLeftCLM_toTemperedDistributionCLM_eq`: on Schwartz functions it is
  `SchwartzMap.bilinLeftCLM (ContinuousLinearMap.apply ℂ G) hA`.
* `TemperedDistribution.applyLeftCLM_smul_id`, `TemperedDistribution.applyLeftCLM_const`,
  `TemperedDistribution.applyLeftCLM_id_apply`: scalar functions times the identity act as
  `smulLeftCLM`, constant maps act on the values, and the identity acts as the identity.
* `TemperedDistribution.applyLeftCLM_applyLeftCLM_apply`: multiplications compose.
-/

public section

noncomputable section

open scoped SchwartzMap

namespace TemperedDistribution

variable {E F G H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [FiniteDimensional ℂ F]
  [NormedAddCommGroup G] [NormedSpace ℂ G] [FiniteDimensional ℂ G]
  [NormedAddCommGroup H] [NormedSpace ℂ H] [FiniteDimensional ℂ H]

/-- **Multiplication of a tempered distribution by an operator-valued function**
`A : E → (F →L[ℂ] G)`, for finite-dimensional `F` and `G`. With the coordinates `gᵢ = bᵢ* ∘ A` of
`A` in a basis `(bᵢ)` of `F →L[ℂ] G`, it sends `u` to `∑ᵢ bᵢ (gᵢ u)`. Any other expansion of `A`
gives the same operator (`TemperedDistribution.applyLeftCLM_eq_sum`); on Schwartz functions it is
`u ↦ (x ↦ A x (u x))` (`TemperedDistribution.applyLeftCLM_toTemperedDistributionCLM_eq`).
If `A` does not have temperate growth, it is `0`
(`TemperedDistribution.applyLeftCLM_of_not_hasTemperateGrowth`), as Mathlib's `smulLeftCLM` is. -/
def applyLeftCLM (A : E → F →L[ℂ] G) : 𝓢'(E, F) →L[ℂ] 𝓢'(E, G) :=
  open Classical in
  if A.HasTemperateGrowth then
    let b := Module.finBasis ℂ (F →L[ℂ] G)
    ∑ i, PointwiseConvergenceCLM.postcomp _ (b i) ∘L smulLeftCLM F fun x ↦ b.coord i (A x)
  else 0

/-- For `A` of temperate growth, `applyLeftCLM A` sends `u` to `∑ᵢ bᵢ (gᵢ u)`, for the coordinates
`gᵢ = bᵢ* ∘ A` of `A` in the basis `Module.finBasis ℂ (F →L[ℂ] G)`. -/
theorem applyLeftCLM_def {A : E → F →L[ℂ] G} (hA : A.HasTemperateGrowth) :
    applyLeftCLM A = ∑ i, PointwiseConvergenceCLM.postcomp _ (Module.finBasis ℂ (F →L[ℂ] G) i) ∘L
      smulLeftCLM F fun x ↦ (Module.finBasis ℂ (F →L[ℂ] G)).coord i (A x) := by
  simp [applyLeftCLM, hA]

/-- Multiplication by a function without temperate growth is `0` by convention. -/
theorem applyLeftCLM_of_not_hasTemperateGrowth {A : E → F →L[ℂ] G}
    (hA : ¬A.HasTemperateGrowth) : applyLeftCLM A = 0 := by
  simp [applyLeftCLM, hA]

/-- **Expansion of `applyLeftCLM`.** If `A x = ∑ᵢ gᵢ(x) • Lᵢ` for finitely many scalar functions
`gᵢ` of temperate growth and constant maps `Lᵢ`, then multiplication by `A` sends `u` to
`∑ᵢ Lᵢ (gᵢ u)`. -/
theorem applyLeftCLM_eq_sum {ι : Type*} (s : Finset ι) (L : ι → F →L[ℂ] G) {g : ι → E → ℂ}
    (hg : ∀ i ∈ s, (g i).HasTemperateGrowth) {A : E → F →L[ℂ] G}
    (hA : ∀ x, A x = ∑ i ∈ s, g i x • L i) :
    applyLeftCLM A =
      ∑ i ∈ s, PointwiseConvergenceCLM.postcomp _ (L i) ∘L smulLeftCLM F (g i) := by
  -- Each coordinate of `A` is a combination of the `gᵢ`, with the coordinates of `Lᵢ`.
  have hcoord (j) : smulLeftCLM F (fun x ↦ (Module.finBasis ℂ (F →L[ℂ] G)).coord j (A x)) =
      ∑ i ∈ s, (Module.finBasis ℂ (F →L[ℂ] G)).coord j (L i) • smulLeftCLM F (g i) := by
    have h : (fun x ↦ (Module.finBasis ℂ (F →L[ℂ] G)).coord j (A x)) =
        fun x ↦ ∑ i ∈ s, ((Module.finBasis ℂ (F →L[ℂ] G)).coord j (L i) • g i) x := by
      funext x
      simp [hA, mul_comm]
    rw [h, smulLeftCLM_sum (g := fun i ↦ (Module.finBasis ℂ (F →L[ℂ] G)).coord j (L i) • g i)
      fun i hi ↦ (Function.HasTemperateGrowth.const _).smul (hg i hi)]
    exact Finset.sum_congr rfl fun i hi ↦ smulLeftCLM_smul (hg i hi) _
  have hA' : A.HasTemperateGrowth := by
    rw [show A = fun x ↦ ∑ i ∈ s, g i x • L i from funext hA]
    exact Function.HasTemperateGrowth.sum fun i hi ↦ (hg i hi).smul (.const (L i))
  ext u φ
  simp only [applyLeftCLM_def hA', hcoord]
  simp only [sum_apply, ContinuousLinearMap.comp_apply, smul_apply,
    PointwiseConvergenceCLM.postcomp_apply_apply, map_sum, map_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  -- Expand `Lᵢ` in the basis.
  have h := congrArg (fun T : F →L[ℂ] G ↦ T (smulLeftCLM F (g i) u φ))
    ((Module.finBasis ℂ (F →L[ℂ] G)).sum_repr (L i))
  simp only [sum_apply, smul_apply] at h
  simpa only [Module.Basis.coord_apply] using h

/-- The value of `applyLeftCLM A u` on a test function, for any finite expansion
`A x = ∑ᵢ gᵢ(x) • Lᵢ` with scalar `gᵢ` of temperate growth. -/
theorem applyLeftCLM_apply_apply {ι : Type*} (s : Finset ι) (L : ι → F →L[ℂ] G) {g : ι → E → ℂ}
    (hg : ∀ i ∈ s, (g i).HasTemperateGrowth) {A : E → F →L[ℂ] G}
    (hA : ∀ x, A x = ∑ i ∈ s, g i x • L i) (u : 𝓢'(E, F)) (φ : 𝓢(E, ℂ)) :
    applyLeftCLM A u φ = ∑ i ∈ s, L i (u (SchwartzMap.smulLeftCLM ℂ (g i) φ)) := by
  rw [applyLeftCLM_eq_sum s L hg hA]
  simp only [sum_apply, ContinuousLinearMap.comp_apply,
    PointwiseConvergenceCLM.postcomp_apply_apply, smulLeftCLM_apply_apply]

/-- Multiplication by a finite sum of operator-valued functions of temperate growth is the sum of
the multiplications. -/
theorem applyLeftCLM_sum {ι : Type*} {A : ι → E → F →L[ℂ] G} {s : Finset ι}
    (hA : ∀ i ∈ s, (A i).HasTemperateGrowth) :
    applyLeftCLM (fun x ↦ ∑ i ∈ s, A i x) = ∑ i ∈ s, applyLeftCLM (A i) := by
  rw [applyLeftCLM_def (Function.HasTemperateGrowth.sum hA),
    Finset.sum_congr rfl fun i hi ↦ applyLeftCLM_def (hA i hi)]
  set b := Module.finBasis ℂ (F →L[ℂ] G)
  have h (j) : smulLeftCLM F (fun x ↦ b.coord j (∑ i ∈ s, A i x)) =
      ∑ i ∈ s, smulLeftCLM F fun x ↦ b.coord j (A i x) := by
    simp only [map_sum]
    exact smulLeftCLM_sum fun i hi ↦ (hA i hi).basis_coord b j
  simp only [h, ContinuousLinearMap.comp_finsetSum]
  exact Finset.sum_comm

/-- Multiplication by a sum of two operator-valued functions of temperate growth is the sum of the
multiplications. -/
theorem applyLeftCLM_add {A₁ A₂ : E → F →L[ℂ] G} (hA₁ : A₁.HasTemperateGrowth)
    (hA₂ : A₂.HasTemperateGrowth) :
    applyLeftCLM (A₁ + A₂) = applyLeftCLM A₁ + applyLeftCLM A₂ := by
  have h := applyLeftCLM_sum (A := ![A₁, A₂]) (s := Finset.univ)
    (by simp [Fin.forall_fin_two, hA₁, hA₂])
  simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one] at h
  exact h

/-- Multiplication by a scalar multiple of an operator-valued function of temperate growth is the
scalar multiple of the multiplication. -/
theorem applyLeftCLM_smul {A : E → F →L[ℂ] G} (hA : A.HasTemperateGrowth) (c : ℂ) :
    applyLeftCLM (c • A) = c • applyLeftCLM A := by
  rw [applyLeftCLM_def (A := c • A) ((Function.HasTemperateGrowth.const c).smul hA),
    applyLeftCLM_def hA]
  simp only [Pi.smul_apply, map_smul, Finset.smul_sum]
  set b := Module.finBasis ℂ (F →L[ℂ] G)
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [← ContinuousLinearMap.comp_smul, ← smulLeftCLM_smul (hA.basis_coord b j)]
  rfl

/-- A scalar function times the identity acts as `smulLeftCLM`. -/
@[simp]
theorem applyLeftCLM_smul_id {g : E → ℂ} (hg : g.HasTemperateGrowth) :
    applyLeftCLM (fun x ↦ g x • ContinuousLinearMap.id ℂ F) = smulLeftCLM F g := by
  rw [applyLeftCLM_eq_sum {()} (fun _ ↦ ContinuousLinearMap.id ℂ F) (g := fun _ ↦ g)
    (fun _ _ ↦ hg) fun x ↦ by simp]
  ext u φ
  simp only [Finset.sum_singleton, ContinuousLinearMap.comp_apply,
    PointwiseConvergenceCLM.postcomp_apply_apply, ContinuousLinearMap.id_apply]

/-- A constant map `L` acts on the values of the distribution. -/
@[simp]
theorem applyLeftCLM_const (L : F →L[ℂ] G) :
    applyLeftCLM (fun _ : E ↦ L) = PointwiseConvergenceCLM.postcomp _ L := by
  rw [applyLeftCLM_eq_sum {()} (fun _ ↦ L) (g := fun _ _ ↦ 1)
    (fun _ _ ↦ Function.HasTemperateGrowth.const 1) fun _ ↦ by simp]
  ext u φ
  simp only [Finset.sum_singleton, ContinuousLinearMap.comp_apply, smulLeftCLM_const, one_smul]

/-- The identity acts as the identity. (Not `@[simp]`: `applyLeftCLM_const` rewrites its left side
first, and `PointwiseConvergenceCLM.postcomp_id` then finishes.) -/
theorem applyLeftCLM_id_apply (u : 𝓢'(E, F)) :
    applyLeftCLM (fun _ : E ↦ ContinuousLinearMap.id ℂ F) u = u := by
  ext φ
  rw [applyLeftCLM_const, PointwiseConvergenceCLM.postcomp_apply_apply,
    ContinuousLinearMap.id_apply]

/-- **Multiplications compose**: multiplying by `A` and then by `B` is multiplying by
`x ↦ B x ∘L A x`, for `A` and `B` of temperate growth. -/
@[simp]
theorem applyLeftCLM_applyLeftCLM_apply {A : E → F →L[ℂ] G} {B : E → G →L[ℂ] H}
    (hA : A.HasTemperateGrowth) (hB : B.HasTemperateGrowth) (u : 𝓢'(E, F)) :
    applyLeftCLM B (applyLeftCLM A u) = applyLeftCLM (fun x ↦ B x ∘L A x) u := by
  set a := Module.finBasis ℂ (F →L[ℂ] G)
  set b := Module.finBasis ℂ (G →L[ℂ] H)
  have hga := hA.basis_coord a
  have hgb := hB.basis_coord b
  have hBA (x) : B x ∘L A x = ∑ ij ∈ Finset.univ ×ˢ Finset.univ,
      (fun x ↦ a.coord ij.1 (A x) * b.coord ij.2 (B x)) x • (b ij.2 ∘L a ij.1) := by
    ext v
    conv_lhs => rw [← a.sum_repr (A x), ← b.sum_repr (B x)]
    simp only [ContinuousLinearMap.comp_apply, sum_apply, smul_apply, map_sum, map_smul,
      Finset.sum_product, Finset.smul_sum, smul_smul, Module.Basis.coord_apply]
  rw [applyLeftCLM_eq_sum _ _ (fun ij _ ↦ (hga ij.1).mul (hgb ij.2)) hBA]
  ext φ
  rw [applyLeftCLM_apply_apply Finset.univ b (fun j _ ↦ hgb j) fun x ↦ (b.sum_repr _).symm]
  simp only [applyLeftCLM_apply_apply Finset.univ a (fun i _ ↦ hga i)
    (fun x ↦ (a.sum_repr (A x)).symm), map_sum, Finset.sum_product, sum_apply,
    ContinuousLinearMap.comp_apply, PointwiseConvergenceCLM.postcomp_apply_apply,
    smulLeftCLM_apply_apply, SchwartzMap.smulLeftCLM_smulLeftCLM_apply (hga _) (hgb _),
    Pi.mul_def]
  exact Finset.sum_comm

end TemperedDistribution

namespace TemperedDistribution

variable {E F G : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [FiniteDimensional ℂ F]
  [NormedAddCommGroup G] [NormedSpace ℂ G] [FiniteDimensional ℂ G]

/-- On Schwartz functions, multiplication by `A` is `u ↦ (x ↦ A x (u x))`. -/
theorem applyLeftCLM_toTemperedDistributionCLM_eq {A : E → F →L[ℂ] G}
    (hA : A.HasTemperateGrowth) (u : 𝓢(E, F)) :
    applyLeftCLM A (u : 𝓢'(E, F)) =
      ((SchwartzMap.bilinLeftCLM (ContinuousLinearMap.apply ℂ G) hA u : 𝓢(E, G)) : 𝓢'(E, G)) := by
  -- Expand `A` in a basis of `F →L[ℂ] G` on both sides.
  set b := Module.finBasis ℂ (F →L[ℂ] G)
  have hg := hA.basis_coord b
  have hexp (x) : A x = ∑ i, b.coord i (A x) • b i := (b.sum_repr (A x)).symm
  rw [applyLeftCLM_eq_sum Finset.univ b (fun i _ ↦ hg i) hexp,
    SchwartzMap.bilinLeftCLM_apply_eq_sum Finset.univ b (fun i _ ↦ hg i) hA hexp]
  ext φ
  simp only [sum_apply, ContinuousLinearMap.comp_apply, map_sum,
    smulLeftCLM_toTemperedDistributionCLM_eq, PointwiseConvergenceCLM.postcomp_apply_apply]
  have := FiniteDimensional.completeSpace ℂ F
  have := FiniteDimensional.completeSpace ℂ G
  exact Finset.sum_congr rfl fun i _ ↦
    (SchwartzMap.toTemperedDistributionCLM_postcompCLM_apply _ _ _).symm

end TemperedDistribution
