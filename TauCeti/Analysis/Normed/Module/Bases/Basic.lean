/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Module.Bases
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Topology.Algebra.InfiniteSum.ContinuousEval

/-!
# Basic facts about generalized Schauder bases

The basis vectors of a generalized Schauder basis span a dense subspace whenever its summation
filter is nontrivial, since every vector is a limit of finite coordinate projections.

The coordinate functionals recover the coefficients of a finite sum of basis vectors, and of a
basis series converging along any nontrivial summation filter below `atTop`, not only along the
filter of the basis. Precomposing a continuous functional with a finite projection, or with an
initial projection of a classical Schauder basis, gives a finite linear combination of
coordinate functionals.

An unconditional basis indexed by `ℕ` is also a classical Schauder basis: convergence along the
net of all finite sets implies convergence along initial segments. The conversion
`UnconditionalSchauderBasis.toSchauderBasis` keeps the basis vectors and coordinate functionals,
so the classical theory of shrinking and boundedly complete bases applies to unconditional bases
such as the coordinate bases of `c₀` and `ℓᵖ`.

The conversion follows Mathlib's `HilbertBasis.toSchauderBasis`.
-/

public section

open Filter Set Topology

namespace GeneralSchauderBasis

variable {β 𝕜 X : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup X] [NormedSpace 𝕜 X]
  {L : SummationFilter β} (b : GeneralSchauderBasis β 𝕜 X L)

/-- The basis vectors of a generalized Schauder basis span a dense subspace. -/
theorem dense_span [L.NeBot] : Dense (Submodule.span 𝕜 (range b) : Set X) := fun x ↦
  mem_closure_of_tendsto (b.tendsto_proj x) (Eventually.of_forall fun A ↦ by
    rw [SetLike.mem_coe, proj_apply]
    exact Submodule.sum_mem _ fun i _ ↦
      Submodule.smul_mem _ _ (Submodule.subset_span (mem_range_self i)))

/-- A coordinate of a finite sum over a set containing `i` is the prescribed coefficient of `i`. -/
-- Normalize before the generic map-of-sum simp lemma expands the coordinate application.
@[simp 1100]
theorem coord_sum (a : β → 𝕜) {i : β} {s : Finset β} (hi : i ∈ s) :
    b.coord i (∑ j ∈ s, a j • b j) = a i := by
  classical
  simp [map_sum, b.ortho, Pi.single_apply, hi]

/-- Precomposition with a finite projection is a finite linear combination of coordinates. -/
theorem comp_proj_eq_sum (f : StrongDual 𝕜 X) (A : Finset β) :
    f.comp (b.proj A) = ∑ i ∈ A, f (b i) • b.coord i := by
  ext x
  simp [proj_apply, mul_comm]

/-- Coordinates of a convergent basis series are its coefficients. The series may converge
along any nontrivial summation filter `L'` below `atTop`, which need not be the filter `L` of the
basis. -/
theorem coord_eq_of_hasSum {L' : SummationFilter β} [L'.NeBot] [L'.LeAtTop] {a : β → 𝕜}
    {x : X} (h : HasSum (fun i ↦ a i • b i) x L') (i : β) : b.coord i x = a i := by
  classical
  have h2 : HasSum (fun j ↦ b.coord i (a j • b j)) (a i) L' := by
    have : (fun j ↦ b.coord i (a j • b j)) = Pi.single i (a i) := by
      ext j; by_cases hj : j = i <;> simp [b.ortho, hj]
    rw [this]; exact (hasSum_pi_single i (a i)).mono_left SummationFilter.le_atTop
  exact (h.map (b.coord i) (b.coord i).continuous).unique h2

section CoordinateSeries

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- The series of rank-one maps built from basis coordinates has norm bounded by the
sum of the coordinate norms times the vector norms. -/
theorem norm_tsum_coord_smulRight_le (v : β → F)
    (hs : Summable (fun i ↦ ‖b.coord i‖ * ‖v i‖)) :
    ‖∑' i, (b.coord i).smulRight (v i)‖ ≤ ∑' i, ‖b.coord i‖ * ‖v i‖ :=
  tsum_of_norm_bounded hs.hasSum fun i ↦
    (ContinuousLinearMap.norm_smulRight_apply (b.coord i) (v i)).le

/-- A summable weighted vector family gives a norm-convergent series of rank-one
maps built from the basis coordinates. -/
theorem summable_coord_smulRight [CompleteSpace F] (v : β → F)
    (hs : Summable (fun i ↦ ‖b.coord i‖ * ‖v i‖)) :
    Summable (fun i ↦ (b.coord i).smulRight (v i)) :=
  hs.of_norm_bounded fun i ↦
    (ContinuousLinearMap.norm_smulRight_apply (b.coord i) (v i)).le

/-- The sum of rank-one coordinate maps takes each basis vector to its prescribed vector. -/
theorem tsum_coord_smulRight_apply_basis [CompleteSpace F] (v : β → F)
    (hs : Summable (fun i ↦ ‖b.coord i‖ * ‖v i‖)) (i : β) :
    (∑' k, (b.coord k).smulRight (v k)) (b i) = v i := by
  classical
  rw [tsum_apply (b.summable_coord_smulRight v hs), tsum_eq_single i]
  · simp [b.ortho]
  · intro k hki
    simp [b.ortho, hki.symm]

end CoordinateSeries

end GeneralSchauderBasis

namespace SchauderBasis

variable {𝕜 X : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup X] [NormedSpace 𝕜 X]
  (b : SchauderBasis 𝕜 X)

/-- Precomposition with an initial projection is a finite linear combination of coordinates. -/
theorem comp_proj_eq_sum (f : StrongDual 𝕜 X) (n : ℕ) :
    f.comp (b.proj n) = ∑ i ∈ Finset.range n, f (b i) • b.coord i := by
  rw [proj, GeneralSchauderBasis.comp_proj_eq_sum]

end SchauderBasis

namespace UnconditionalSchauderBasis

variable {𝕜 X : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup X] [NormedSpace 𝕜 X]
  (b : UnconditionalSchauderBasis ℕ 𝕜 X)

/-- An unconditional basis indexed by `ℕ` is a classical Schauder basis, with the same basis
vectors and coordinate functionals. -/
protected def toSchauderBasis : SchauderBasis 𝕜 X where
  basis := b
  coord := b.coord
  ortho := b.ortho
  expansion x := (b.expansion x).mono_left SummationFilter.le_atTop

/-- The basis vectors of the classical basis are the original basis vectors. -/
@[simp]
theorem coe_toSchauderBasis : ⇑b.toSchauderBasis = ⇑b :=
  (rfl)

/-- The coordinate functionals of the classical basis are the original coordinate functionals. -/
@[simp]
theorem toSchauderBasis_coord : b.toSchauderBasis.coord = b.coord :=
  (rfl)

/-- The initial projections of the classical basis are the projections of the unconditional basis
onto initial segments. -/
@[simp]
theorem toSchauderBasis_proj (n : ℕ) :
    b.toSchauderBasis.proj n = b.proj (Finset.range n) :=
  (rfl)

end UnconditionalSchauderBasis
