/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.ContDiff.Matrix
public import TauCeti.Analysis.Sobolev.Wkp.SmoothMultiplication

/-!
# Multiplication by smooth matrix and operator coefficients on `W^{k,p}(Ω)`

Let `Ω` be an open set whose closure is compact and contained in a set `U` of unique
differentiability, for instance an open set. A tuple
`(u l)_{l ∈ ι}` of scalar Sobolev functions on `Ω` is multiplied by a matrix `(a m l)` of functions
smooth on `U` by `(a u) m = ∑ l, a m l * u l`. This is a continuous linear map
`(ι → W^{k,p}(Ω)) →L[ℝ] (κ → W^{k,p}(Ω))` for every order `k` and every `1 ≤ p ≤ ∞`
(`TauCeti.Wkp.contDiffOnMatrixSMulL`), assembled from scalar smooth multiplication
`TauCeti.Wkp.contDiffOnSMulL`.

A smooth operator-valued coefficient `g : E → F →L[ℝ] F'` between finite-dimensional spaces acts in
the same way on the components of `F`-valued Sobolev maps in a basis `b` of `F`, with the matrix of
`g` in the bases `b` and `b'` (`TauCeti.Wkp.contDiffOnOperatorSMulL`): the components of the
product are the components in `b'` of `g x` applied to the vector with components `u l x`
(`TauCeti.Wkp.value_contDiffOnOperatorSMulL_ae`). These are the multiplications by the coordinate
changes of a vector bundle that relate the chart data of a Sobolev section in two charts. The
smoothness of the matrix entries of `g` follows from `Module.Basis.contDiffOn_repr_apply`. Both
multiplications commute with forgetting the highest weak derivative.

## Main declarations

* `TauCeti.Wkp.contDiffOnMatrixSMulL`: multiplication by a smooth matrix of functions.
* `TauCeti.Wkp.value_contDiffOnMatrixSMulL_ae`: its components are the pointwise matrix products.
* `TauCeti.Wkp.contDiffOnOperatorSMulL`: multiplication by a smooth operator-valued coefficient in
  bases of the source and target spaces.
* `TauCeti.Wkp.value_contDiffOnOperatorSMulL_ae`: its components are those of the pointwise image.
* `TauCeti.Wkp.lowerOrder_contDiffOnMatrixSMulL`, `TauCeti.Wkp.lowerOrder_contDiffOnOperatorSMulL`:
  compatibility with forgetting the highest weak derivative.
-/

public section

noncomputable section

open MeasureTheory Module TopologicalSpace
open scoped ContDiff

namespace TauCeti

namespace Wkp

variable {E : Type*} [MeasurableSpace E] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [BorelSpace E] {mu : Measure E} [mu.IsAddHaarMeasure]
  {Omega : Opens E} {p : ENNReal} [Fact (1 ≤ p)] {U : Set E} {ι κ : Type*} [Fintype ι]

section Matrix

variable {a : κ → ι → E → ℝ}

/-- **Smooth matrix multiplication on tuples in `W^{k,p}(Ω)`.** If `Ω` has compact closure inside
a set `U` of unique differentiability, for instance an open set, and every entry `a m l` is smooth
on `U`, the tuple with entries `∑ l, a m l * u l` depends continuously and linearly on the tuple
`u`. -/
def contDiffOnMatrixSMulL (hU : UniqueDiffOn ℝ U) (hΩ : IsCompact (closure (Omega : Set E)))
    (hΩU : closure (Omega : Set E) ⊆ U) (k : ℕ) (ha : ∀ m l, ContDiffOn ℝ ∞ (a m l) U) :
    (ι → Wkp mu Omega p k) →L[ℝ] (κ → Wkp mu Omega p k) :=
  ContinuousLinearMap.pi fun m ↦
    ∑ l, (contDiffOnSMulL hU hΩ hΩU k (ha m l)).comp (ContinuousLinearMap.proj l)

@[simp]
theorem contDiffOnMatrixSMulL_apply (hU : UniqueDiffOn ℝ U)
    (hΩ : IsCompact (closure (Omega : Set E)))
    (hΩU : closure (Omega : Set E) ⊆ U) (k : ℕ) (ha : ∀ m l, ContDiffOn ℝ ∞ (a m l) U)
    (u : ι → Wkp mu Omega p k) (m : κ) :
    contDiffOnMatrixSMulL hU hΩ hΩU k ha u m =
      ∑ l, contDiffOnSMulL hU hΩ hΩU k (ha m l) (u l) := by
  simp [contDiffOnMatrixSMulL]

/-- The components of a smooth matrix product are the pointwise matrix products, almost
everywhere on `Ω`. -/
theorem value_contDiffOnMatrixSMulL_ae (hU : UniqueDiffOn ℝ U)
    (hΩ : IsCompact (closure (Omega : Set E))) (hΩU : closure (Omega : Set E) ⊆ U) (k : ℕ)
    (ha : ∀ m l, ContDiffOn ℝ ∞ (a m l) U) (u : ι → Wkp mu Omega p k) (m : κ) :
    (value k (contDiffOnMatrixSMulL hU hΩ hΩU k ha u m) : E → ℝ) =ᵐ[mu.restrict Omega]
      fun x ↦ ∑ l, a m l x * value k (u l) x := by
  rw [contDiffOnMatrixSMulL_apply]
  filter_upwards [value_finsetSum_ae k Finset.univ fun l ↦
      contDiffOnSMulL hU hΩ hΩU k (ha m l) (u l),
    ae_all_iff.2 fun l ↦ value_contDiffOnSMulL_ae hU hΩ hΩU k (ha m l) (u l)] with x hx hl
  rw [hx]
  exact Finset.sum_congr rfl fun l _ ↦ hl l

/-- Smooth matrix multiplication commutes with forgetting the highest weak derivative. -/
theorem lowerOrder_contDiffOnMatrixSMulL (hU : UniqueDiffOn ℝ U)
    (hΩ : IsCompact (closure (Omega : Set E))) (hΩU : closure (Omega : Set E) ⊆ U) (k : ℕ)
    (ha : ∀ m l, ContDiffOn ℝ ∞ (a m l) U) (u : ι → Wkp mu Omega p (k + 1)) (m : κ) :
    lowerOrder k (contDiffOnMatrixSMulL hU hΩ hΩU (k + 1) ha u m) =
      contDiffOnMatrixSMulL hU hΩ hΩU k ha (fun l ↦ lowerOrder k (u l)) m := by
  rw [contDiffOnMatrixSMulL_apply, contDiffOnMatrixSMulL_apply, ← lowerOrderL_apply, map_sum]
  exact Finset.sum_congr rfl fun l _ ↦ by
    rw [lowerOrderL_apply, lowerOrder_contDiffOnSMulL]

end Matrix

section Operator

variable {F F' : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup F']
  [NormedSpace ℝ F'] {g : E → F →L[ℝ] F'}

/-- **Smooth operator coefficients on `W^{k,p}(Ω)`.** If `Ω` has compact closure inside a set
`U` of unique differentiability, for instance an open set, and `g : E → F →L[ℝ] F'` is smooth on
`U`, then multiplication by the matrix of `g` in bases `b` of `F` and `b'` of `F'` is a continuous
linear map on tuples of Sobolev functions. Read as the components of `F`-valued maps, it sends `u`
to `x ↦ g x (u x)` (`TauCeti.Wkp.value_contDiffOnOperatorSMulL_ae`). -/
def contDiffOnOperatorSMulL (hU : UniqueDiffOn ℝ U) (hΩ : IsCompact (closure (Omega : Set E)))
    (hΩU : closure (Omega : Set E) ⊆ U) (k : ℕ) (b : Basis ι ℝ F) (b' : Basis κ ℝ F')
    [FiniteDimensional ℝ F'] (hg : ContDiffOn ℝ ∞ g U) :
    (ι → Wkp mu Omega p k) →L[ℝ] (κ → Wkp mu Omega p k) :=
  contDiffOnMatrixSMulL hU hΩ hΩU k fun m l ↦
    b'.contDiffOn_repr_apply (hg.clm_apply (contDiffOn_const (c := b l))) m

@[simp]
theorem contDiffOnOperatorSMulL_apply (hU : UniqueDiffOn ℝ U)
    (hΩ : IsCompact (closure (Omega : Set E))) (hΩU : closure (Omega : Set E) ⊆ U) (k : ℕ)
    (b : Basis ι ℝ F) (b' : Basis κ ℝ F') [FiniteDimensional ℝ F'] (hg : ContDiffOn ℝ ∞ g U)
    (u : ι → Wkp mu Omega p k) (m : κ) :
    contDiffOnOperatorSMulL hU hΩ hΩU k b b' hg u m =
      ∑ l, contDiffOnSMulL hU hΩ hΩU k
        (b'.contDiffOn_repr_apply (hg.clm_apply (contDiffOn_const (c := b l))) m) (u l) := by
  rw [contDiffOnOperatorSMulL, contDiffOnMatrixSMulL_apply]

/-- The components in `b'` of a product with a smooth operator coefficient are, almost everywhere
on `Ω`, the components of `g x` applied to the vector whose components in `b` are the values of
the factors. -/
theorem value_contDiffOnOperatorSMulL_ae (hU : UniqueDiffOn ℝ U)
    (hΩ : IsCompact (closure (Omega : Set E))) (hΩU : closure (Omega : Set E) ⊆ U) (k : ℕ)
    (b : Basis ι ℝ F) (b' : Basis κ ℝ F') [FiniteDimensional ℝ F'] (hg : ContDiffOn ℝ ∞ g U)
    (u : ι → Wkp mu Omega p k) (m : κ) :
    (value k (contDiffOnOperatorSMulL hU hΩ hΩU k b b' hg u m) : E → ℝ) =ᵐ[mu.restrict Omega]
      fun x ↦ b'.repr (g x (∑ l, value k (u l) x • b l)) m := by
  rw [contDiffOnOperatorSMulL]
  filter_upwards [value_contDiffOnMatrixSMulL_ae hU hΩ hΩU k _ u m] with x hx
  rw [hx]
  simp [mul_comm]

/-- Multiplication by a smooth operator coefficient commutes with forgetting the highest weak
derivative. -/
theorem lowerOrder_contDiffOnOperatorSMulL (hU : UniqueDiffOn ℝ U)
    (hΩ : IsCompact (closure (Omega : Set E))) (hΩU : closure (Omega : Set E) ⊆ U) (k : ℕ)
    (b : Basis ι ℝ F) (b' : Basis κ ℝ F') [FiniteDimensional ℝ F'] (hg : ContDiffOn ℝ ∞ g U)
    (u : ι → Wkp mu Omega p (k + 1)) (m : κ) :
    lowerOrder k (contDiffOnOperatorSMulL hU hΩ hΩU (k + 1) b b' hg u m) =
      contDiffOnOperatorSMulL hU hΩ hΩU k b b' hg (fun l ↦ lowerOrder k (u l)) m := by
  rw [contDiffOnOperatorSMulL, contDiffOnOperatorSMulL]
  exact lowerOrder_contDiffOnMatrixSMulL hU hΩ hΩU k _ u m

end Operator

end Wkp

end TauCeti
