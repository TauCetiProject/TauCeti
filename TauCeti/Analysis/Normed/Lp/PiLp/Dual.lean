/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Lp.BoundedContinuous
public import TauCeti.Analysis.Normed.Lp.PiLp.Basic

/-!
# Coordinate dual representation for finite `Lᵖ` products of `ℓ¹` spaces

Pulling back a continuous linear functional `Λ` on a product
`PiLp p (fun i ↦ lp (fun _ : α i ↦ 𝕜) 1)` along the coordinate inclusions `PiLp.singleCLM`
produces coordinate bounded continuous functions `Λ.piLpCoordBCF i : α i →ᵇ 𝕜` whenever each
coordinate space `α i` carries the discrete topology and `𝕜` is a complete nontrivially normed
field.

When the index type `ι` is finite, `Λ` is recovered as the sum of the `ℓ¹`-pairings
`lp.bcfPairing 𝕜 (α i) 𝕜 (v i) (Λ.piLpCoordBCF i)` (`StrongDual.apply_eq_sum_bcfPairing`).
Conversely, on arbitrary topological coordinate spaces `α i` over a complete nontrivially normed
field `𝕜`, `StrongDual.ofPiLpCoordBCF` assembles a continuous linear functional from any family of
bounded continuous coordinate functions by summing the coordinate pairings composed with
`PiLp.proj`. For discrete coordinate spaces over a complete nontrivially normed field, these two
constructions form the linear equivalence `StrongDual.piLpCoordBCFEquiv`.

## Main definitions

* `StrongDual.piLpCoordBCF`: for discrete coordinate spaces `α i` over a complete nontrivially
  normed field `𝕜`, the coordinate bounded functions `y ↦ Λ (PiLp.single p i (lp.single 1 y 1))`
  associated to `Λ : StrongDual 𝕜 (PiLp p (fun i ↦ lp (fun _ : α i ↦ 𝕜) 1))`.
* `StrongDual.ofPiLpCoordBCF`: for finite `ι`, assemble a continuous linear functional on
  `PiLp p (fun i ↦ lp (fun _ : α i ↦ 𝕜) 1)` from a family `f : ∀ i, α i →ᵇ 𝕜`.
* `StrongDual.piLpCoordBCFEquiv`: for finite `ι` and discrete coordinate spaces `α i` over a
  complete nontrivially normed field `𝕜`, the linear equivalence
  `StrongDual 𝕜 (PiLp p (fun i ↦ lp (fun _ : α i ↦ 𝕜) 1)) ≃ₗ[𝕜] (∀ i, α i →ᵇ 𝕜)`.

## Main results

* `StrongDual.apply_piLpSingle_eq_bcfPairing`: single-coordinate pairing formula on
  `PiLp.single p i u` for discrete coordinate spaces over a complete nontrivially normed field `𝕜`.
* `StrongDual.norm_piLpCoordBCF_le`: `‖Λ.piLpCoordBCF i‖ ≤ ‖Λ‖` when `ι` is finite and `1 ≤ p`.
* `StrongDual.apply_eq_sum_bcfPairing`: finite-product coordinate pairing decomposition for discrete
  coordinate spaces over a complete nontrivially normed field `𝕜`.
* `StrongDual.ofPiLpCoordBCF_piLpSingle`: single-coordinate pairing formula for
  `StrongDual.ofPiLpCoordBCF` on arbitrary topological coordinate spaces.
* `StrongDual.piLpCoordBCF_ofPiLpCoordBCF`, `StrongDual.piLpCoordBCF_injective`,
  `StrongDual.ext_piLpCoordBCF`: coordinate recovery, uniqueness, and extensionality for
  `StrongDual.piLpCoordBCF`.
-/

public section

noncomputable section

open scoped ENNReal BoundedContinuousFunction

namespace StrongDual

section PiLpCoordBCF

variable {ι : Type*} {α : ι → Type*} {𝕜 : Type*}
  [∀ i, TopologicalSpace (α i)] [∀ i, DiscreteTopology (α i)]
  [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜] {p : ℝ≥0∞}

/-- For discrete coordinate spaces `α i` over a complete nontrivially normed field `𝕜`, the `i`-th
coordinate bounded function `y ↦ Λ (PiLp.single p i (lp.single 1 y 1))` of a continuous linear
functional `Λ` on `PiLp p (fun i ↦ lp (fun _ : α i ↦ 𝕜) 1)`. -/
def piLpCoordBCF (Λ : StrongDual 𝕜 (PiLp p (fun i ↦ lp (fun _ : α i ↦ 𝕜) 1))) (i : ι) :
    α i →ᵇ 𝕜 :=
  letI := Classical.decEq ι
  (lp.bcfDualEquiv 𝕜 (α i)).symm
    (Λ.comp (PiLp.singleCLM p 𝕜 (fun i ↦ lp (fun _ : α i ↦ 𝕜) 1) i))

/-- For discrete coordinate spaces `α i` over a complete nontrivially normed field `𝕜`, evaluating
`Λ` on a single coordinate vector `PiLp.single p i u` agrees with the `ℓ¹`-pairing of `u` against
`Λ.piLpCoordBCF i`. -/
theorem apply_piLpSingle_eq_bcfPairing [inst : DecidableEq ι]
    (Λ : StrongDual 𝕜 (PiLp p (fun i ↦ lp (fun _ : α i ↦ 𝕜) 1))) (i : ι)
    (u : lp (fun _ : α i ↦ 𝕜) 1) :
    Λ (PiLp.single p i u) = lp.bcfPairing 𝕜 (α i) 𝕜 u (Λ.piLpCoordBCF i) := by
  simp only [piLpCoordBCF, lp.bcfPairing_bcfDualEquiv_symm, ContinuousLinearMap.comp_apply,
    PiLp.singleCLM_apply]
  rw [Subsingleton.elim inst (Classical.decEq ι)]

/-- The `i`-th coordinate bounded function of `Λ` evaluates at `y` to
`Λ (PiLp.single p i (lp.single 1 y 1))`. -/
@[simp]
theorem piLpCoordBCF_apply [DecidableEq ι]
    (Λ : StrongDual 𝕜 (PiLp p (fun i ↦ lp (fun _ : α i ↦ 𝕜) 1))) (i : ι)
    [DecidableEq (α i)] (y : α i) :
    Λ.piLpCoordBCF i y = Λ (PiLp.single p i (lp.single 1 y 1)) := by
  rw [Λ.apply_piLpSingle_eq_bcfPairing, lp.bcfPairing_single, one_smul]

@[simp]
theorem piLpCoordBCF_zero :
    piLpCoordBCF (ι := ι) (α := α) (𝕜 := 𝕜) (p := p) 0 = 0 := by
  classical
  ext i y
  simp [piLpCoordBCF_apply]

@[simp]
theorem piLpCoordBCF_add
    (Λ₁ Λ₂ : StrongDual 𝕜 (PiLp p (fun i ↦ lp (fun _ : α i ↦ 𝕜) 1))) :
    (Λ₁ + Λ₂).piLpCoordBCF = Λ₁.piLpCoordBCF + Λ₂.piLpCoordBCF := by
  classical
  ext i y
  simp [piLpCoordBCF_apply]

@[simp]
theorem piLpCoordBCF_neg
    (Λ : StrongDual 𝕜 (PiLp p (fun i ↦ lp (fun _ : α i ↦ 𝕜) 1))) :
    (-Λ).piLpCoordBCF = -Λ.piLpCoordBCF := by
  classical
  ext i y
  simp [piLpCoordBCF_apply]

@[simp]
theorem piLpCoordBCF_sub
    (Λ₁ Λ₂ : StrongDual 𝕜 (PiLp p (fun i ↦ lp (fun _ : α i ↦ 𝕜) 1))) :
    (Λ₁ - Λ₂).piLpCoordBCF = Λ₁.piLpCoordBCF - Λ₂.piLpCoordBCF := by
  classical
  ext i y
  simp [piLpCoordBCF_apply]

@[simp]
theorem piLpCoordBCF_smul (c : 𝕜)
    (Λ : StrongDual 𝕜 (PiLp p (fun i ↦ lp (fun _ : α i ↦ 𝕜) 1))) :
    (c • Λ).piLpCoordBCF = c • Λ.piLpCoordBCF := by
  classical
  ext i y
  simp [piLpCoordBCF_apply]

/-- When the coordinate index type `ι` is finite and `1 ≤ p`, each coordinate bounded function of
`Λ` has supremum norm at most `‖Λ‖`. -/
theorem norm_piLpCoordBCF_le [Fintype ι] [Fact (1 ≤ p)]
    (Λ : StrongDual 𝕜 (PiLp p (fun i ↦ lp (fun _ : α i ↦ 𝕜) 1))) (i : ι) :
    ‖Λ.piLpCoordBCF i‖ ≤ ‖Λ‖ := by
  classical
  rw [piLpCoordBCF, LinearIsometryEquiv.norm_map]
  exact (Λ.opNorm_comp_le _).trans
    (mul_le_of_le_one_right (norm_nonneg Λ) (PiLp.norm_singleCLM_le i))

/-- When `ι` is finite and each coordinate space `α i` is discrete over a complete nontrivially
normed field `𝕜`, a continuous linear functional `Λ` on `PiLp p (fun i ↦ lp (fun _ : α i ↦ 𝕜) 1)`
is the sum over `i` of the `ℓ¹`-pairings with its coordinate bounded functions
`Λ.piLpCoordBCF i`. -/
theorem apply_eq_sum_bcfPairing [Fintype ι]
    (Λ : StrongDual 𝕜 (PiLp p (fun i ↦ lp (fun _ : α i ↦ 𝕜) 1)))
    (v : PiLp p (fun i ↦ lp (fun _ : α i ↦ 𝕜) 1)) :
    Λ v = ∑ i : ι, lp.bcfPairing 𝕜 (α i) 𝕜 (v i) (Λ.piLpCoordBCF i) := by
  classical
  rw [← Λ.sum_comp_piLpSingleCLM v]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  simpa only [ContinuousLinearMap.comp_apply, PiLp.singleCLM_apply] using
    Λ.apply_piLpSingle_eq_bcfPairing i (v i)

end PiLpCoordBCF

section OfPiLpCoordBCF

variable {ι : Type*} [Fintype ι] {α : ι → Type*} {𝕜 : Type*}
  [∀ i, TopologicalSpace (α i)] [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]

/-- Assemble a continuous linear functional on the finite `Lᵖ` product
`PiLp p (fun i ↦ lp (fun _ : α i ↦ 𝕜) 1)` from a family of bounded continuous coordinate functions
`f : ∀ i, α i →ᵇ 𝕜`, by summing the coordinate `ℓ¹`-pairings composed with the projections
`PiLp.proj`. -/
def ofPiLpCoordBCF (p : ℝ≥0∞) (f : ∀ i, α i →ᵇ 𝕜) :
    StrongDual 𝕜 (PiLp p (fun i ↦ lp (fun _ : α i ↦ 𝕜) 1)) :=
  ∑ i : ι, ((lp.bcfPairing 𝕜 (α i) 𝕜).flip (f i)).comp
    (PiLp.proj p (fun j ↦ lp (fun _ : α j ↦ 𝕜) 1) i)

/-- Evaluating `ofPiLpCoordBCF p f` at `v` equals the sum of the `ℓ¹`-pairings of `v i` with
`f i`. -/
@[simp]
theorem ofPiLpCoordBCF_apply (p : ℝ≥0∞) (f : ∀ i, α i →ᵇ 𝕜)
    (v : PiLp p (fun i ↦ lp (fun _ : α i ↦ 𝕜) 1)) :
    ofPiLpCoordBCF p f v = ∑ i : ι, lp.bcfPairing 𝕜 (α i) 𝕜 (v i) (f i) := by
  simp [ofPiLpCoordBCF]

@[simp]
theorem ofPiLpCoordBCF_zero (p : ℝ≥0∞) :
    ofPiLpCoordBCF (ι := ι) (α := α) (𝕜 := 𝕜) p 0 = 0 := by
  ext v
  simp

@[simp]
theorem ofPiLpCoordBCF_add (p : ℝ≥0∞) (f g : ∀ i, α i →ᵇ 𝕜) :
    ofPiLpCoordBCF p (f + g) = ofPiLpCoordBCF p f + ofPiLpCoordBCF p g := by
  ext v
  simp [Finset.sum_add_distrib]

@[simp]
theorem ofPiLpCoordBCF_neg (p : ℝ≥0∞) (f : ∀ i, α i →ᵇ 𝕜) :
    ofPiLpCoordBCF p (-f) = -ofPiLpCoordBCF p f := by
  ext v
  simp

@[simp]
theorem ofPiLpCoordBCF_sub (p : ℝ≥0∞) (f g : ∀ i, α i →ᵇ 𝕜) :
    ofPiLpCoordBCF p (f - g) = ofPiLpCoordBCF p f - ofPiLpCoordBCF p g := by
  ext v
  simp [Finset.sum_sub_distrib]

@[simp]
theorem ofPiLpCoordBCF_smul (p : ℝ≥0∞) (c : 𝕜) (f : ∀ i, α i →ᵇ 𝕜) :
    ofPiLpCoordBCF p (c • f) = c • ofPiLpCoordBCF p f := by
  ext v
  simp [Finset.mul_sum]

/-- Evaluating `ofPiLpCoordBCF p f` on a single coordinate vector `PiLp.single p i u` yields the
`ℓ¹`-pairing of `u` with `f i`. -/
@[simp high]
theorem ofPiLpCoordBCF_piLpSingle [DecidableEq ι] (p : ℝ≥0∞) (f : ∀ i, α i →ᵇ 𝕜)
    (i : ι) (u : lp (fun _ : α i ↦ 𝕜) 1) :
    ofPiLpCoordBCF p f (PiLp.single p i u) = lp.bcfPairing 𝕜 (α i) 𝕜 u (f i) := by
  rw [ofPiLpCoordBCF_apply, Fintype.sum_eq_single i]
  · simp
  · intro j hj
    simp [hj]

end OfPiLpCoordBCF

section PiLpCoordBCFEquiv

variable {ι : Type*} {α : ι → Type*} {𝕜 : Type*}
  [∀ i, TopologicalSpace (α i)] [∀ i, DiscreteTopology (α i)]
  [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]

/-- For discrete coordinate spaces `α i` over a complete nontrivially normed field `𝕜`, extracting
the coordinate bounded functions of `ofPiLpCoordBCF p f` recovers `f`. -/
@[simp]
theorem piLpCoordBCF_ofPiLpCoordBCF [Fintype ι] {p : ℝ≥0∞} (f : ∀ i, α i →ᵇ 𝕜) (i : ι) :
    (ofPiLpCoordBCF p f).piLpCoordBCF i = f i := by
  classical
  ext y
  simp

/-- For discrete coordinate spaces `α i` over a complete nontrivially normed field `𝕜`,
reassembling a continuous linear functional `Λ` from `Λ.piLpCoordBCF` recovers `Λ`. -/
@[simp]
theorem ofPiLpCoordBCF_piLpCoordBCF [Fintype ι] {p : ℝ≥0∞}
    (Λ : StrongDual 𝕜 (PiLp p (fun i ↦ lp (fun _ : α i ↦ 𝕜) 1))) :
    ofPiLpCoordBCF p Λ.piLpCoordBCF = Λ := by
  ext v
  rw [ofPiLpCoordBCF_apply, ← Λ.apply_eq_sum_bcfPairing]

/-- For finite `ι` and discrete coordinate spaces `α i` over a complete nontrivially normed field
`𝕜`, a continuous linear functional on `PiLp p (fun i ↦ lp (fun _ : α i ↦ 𝕜) 1)` is uniquely
determined by its coordinate bounded functions `StrongDual.piLpCoordBCF`. -/
theorem piLpCoordBCF_injective [Finite ι] {p : ℝ≥0∞} :
    Function.Injective (piLpCoordBCF (ι := ι) (α := α) (𝕜 := 𝕜) (p := p)) := by
  have := Fintype.ofFinite ι
  intro Λ₁ Λ₂ h
  rw [← ofPiLpCoordBCF_piLpCoordBCF Λ₁, ← ofPiLpCoordBCF_piLpCoordBCF Λ₂, h]

/-- For finite `ι` and discrete coordinate spaces `α i` over a complete nontrivially normed field
`𝕜`, two continuous linear functionals on `PiLp p (fun i ↦ lp (fun _ : α i ↦ 𝕜) 1)` are equal if
all their coordinate bounded functions `StrongDual.piLpCoordBCF` are equal. -/
@[ext]
theorem ext_piLpCoordBCF [Finite ι] {p : ℝ≥0∞}
    {Λ₁ Λ₂ : StrongDual 𝕜 (PiLp p (fun i ↦ lp (fun _ : α i ↦ 𝕜) 1))}
    (h : ∀ i, Λ₁.piLpCoordBCF i = Λ₂.piLpCoordBCF i) : Λ₁ = Λ₂ :=
  piLpCoordBCF_injective (funext h)

end PiLpCoordBCFEquiv

section Equiv

/-- For finite `ι` and discrete coordinate spaces `α i` over a complete nontrivially normed field
`𝕜`, the linear equivalence identifying `StrongDual 𝕜 (PiLp p (fun i ↦ lp (fun _ : α i ↦ 𝕜) 1))`
with families of bounded continuous functions `(i : ι) → (α i →ᵇ 𝕜)` via
`StrongDual.piLpCoordBCF`. -/
def piLpCoordBCFEquiv (p : ℝ≥0∞) (𝕜 : Type*) {ι : Type*} (α : ι → Type*)
    [Fintype ι] [∀ i, TopologicalSpace (α i)] [∀ i, DiscreteTopology (α i)]
    [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜] :
    StrongDual 𝕜 (PiLp p (fun i ↦ lp (fun _ : α i ↦ 𝕜) 1)) ≃ₗ[𝕜] (∀ i, α i →ᵇ 𝕜) where
  toFun := piLpCoordBCF
  map_add' := piLpCoordBCF_add
  map_smul' := piLpCoordBCF_smul
  invFun := ofPiLpCoordBCF p
  left_inv := ofPiLpCoordBCF_piLpCoordBCF
  right_inv f := funext (piLpCoordBCF_ofPiLpCoordBCF f)

@[simp]
theorem piLpCoordBCFEquiv_apply {p : ℝ≥0∞} {𝕜 : Type*} {ι : Type*} {α : ι → Type*}
    [Fintype ι] [∀ i, TopologicalSpace (α i)] [∀ i, DiscreteTopology (α i)]
    [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
    (Λ : StrongDual 𝕜 (PiLp p (fun i ↦ lp (fun _ : α i ↦ 𝕜) 1))) :
    piLpCoordBCFEquiv p 𝕜 α Λ = Λ.piLpCoordBCF := by
  rfl

@[simp]
theorem piLpCoordBCFEquiv_symm_apply {p : ℝ≥0∞} {𝕜 : Type*} {ι : Type*} {α : ι → Type*}
    [Fintype ι] [∀ i, TopologicalSpace (α i)] [∀ i, DiscreteTopology (α i)]
    [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜] (f : ∀ i, α i →ᵇ 𝕜) :
    (piLpCoordBCFEquiv p 𝕜 α).symm f = ofPiLpCoordBCF p f := by
  rfl

end Equiv

end StrongDual
