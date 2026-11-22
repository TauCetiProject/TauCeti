/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Module.Bases
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Topology.Algebra.InfiniteSum.ContinuousEval
import TauCeti.Analysis.Normed.Operator.Dense

/-!
# Basic facts about generalized Schauder bases

The basis vectors of a generalized Schauder basis span a dense subspace whenever its summation
filter is nontrivial, since every vector is a limit of finite coordinate projections.

The coordinate functionals recover the coefficients of a finite sum of basis vectors, and of a
basis series converging along any nontrivial summation filter whose support contains the queried
index, not only along the filter of the basis. Precomposing a continuous functional with a finite
projection, or with an initial projection of a classical Schauder basis, gives a finite linear
combination of coordinate functionals.

An unconditional basis indexed by `ℕ` is also a classical Schauder basis: convergence along the
net of all finite sets implies convergence along initial segments. Conversely, any generalized
Schauder basis whose expansion converges unconditionally defines an unconditional basis; a uniform
bound on finite coordinate projections suffices for unconditional convergence whenever the summation
filter is nontrivial, and characterizes it in a Banach space
(`GeneralSchauderBasis.forall_hasSum_iff_exists_forall_norm_proj_le`). The conversions
`UnconditionalSchauderBasis.toSchauderBasis` and
`GeneralSchauderBasis.toUnconditionalSchauderBasis` keep the basis vectors and coordinate
functionals, so the classical theory of shrinking and boundedly complete bases applies to
unconditional bases such as the coordinate bases of `c₀` and `ℓᵖ` and the Haar basis of `Lᵖ`.

The conversion follows Mathlib's `HilbertBasis.toSchauderBasis`.
-/

public section

open Filter Set Topology

namespace GeneralSchauderBasis

variable {β 𝕜 X : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup X] [NormedSpace 𝕜 X]
  {L : SummationFilter β} (b : GeneralSchauderBasis β 𝕜 X L)

/-- The basis vectors of a generalized Schauder basis span a dense subspace. -/
theorem dense_span [L.NeBot] : Dense (Submodule.span 𝕜 (range b) : Set X) := fun x ↦
  mem_closure_of_tendsto (b.tendsto_proj x) (Eventually.of_forall fun A ↦
    Submodule.span_mono (image_subset_range b A)
      (b.range_proj_eq_span A ▸ (b.proj A).toLinearMap.mem_range_self x))

/-- A finite coordinate projection fixes every linear combination supported in its index set. -/
theorem proj_sum_of_subset (a : β → 𝕜) {A B : Finset β} (hBA : B ⊆ A) :
    b.proj A (∑ i ∈ B, a i • b i) = ∑ i ∈ B, a i • b i := by
  classical
  rw [map_sum]
  refine Finset.sum_congr rfl fun i hi ↦ ?_
  rw [map_smul, b.proj_apply_basis_mem, ite_eq_left (hBA hi)]

/-- If the finite coordinate projections of a generalized Schauder basis with nontrivial summation
filter are uniformly bounded, then the basis expansion of every vector converges unconditionally. -/
theorem hasSum_of_forall_norm_proj_le [L.NeBot] {C : ℝ} (hC : ∀ A : Finset β, ‖b.proj A‖ ≤ C)
    (x : X) : HasSum (fun i ↦ b.coord i x • b i) x := by
  -- The projections are uniformly bounded and converge to the identity on the span of the basis
  -- vectors, which is dense, so they converge to the identity everywhere.
  have hspan : ∀ y ∈ (Submodule.span 𝕜 (range b) : Set X),
      Tendsto (fun A : Finset β ↦ b.proj A y) atTop (𝓝 ((1 : X →L[𝕜] X) y)) := fun y hy ↦ by
    obtain ⟨c, rfl⟩ := Finsupp.mem_span_range_iff_exists_finsupp.1 hy
    exact tendsto_atTop_of_eventually_const fun A hA ↦ by
      rw [Finsupp.sum, b.proj_sum_of_subset c hA, one_apply_eq_self]
  rw [HasSum, SummationFilter.unconditional_filter]
  simpa only [proj_apply, one_apply_eq_self] using
    ContinuousLinearMap.tendsto_apply_of_dense b.dense_span (.of_forall hC) hspan x

/-- A generalized Schauder basis whose expansion converges unconditionally is an unconditional
Schauder basis, with the same basis vectors and coordinate functionals. -/
protected def toUnconditionalSchauderBasis
    (hexp : ∀ x, HasSum (fun i ↦ b.coord i x • b i) x) :
    UnconditionalSchauderBasis β 𝕜 X where
  basis := b
  coord := b.coord
  ortho := b.ortho
  expansion := hexp

/-- The basis vectors of `toUnconditionalSchauderBasis` are the original basis vectors. -/
@[simp]
theorem coe_toUnconditionalSchauderBasis (hexp : ∀ x, HasSum (fun i ↦ b.coord i x • b i) x) :
    ⇑(b.toUnconditionalSchauderBasis hexp) = ⇑b :=
  (rfl)

/-- The coordinate functionals of `toUnconditionalSchauderBasis` are the original coordinate
functionals. -/
@[simp]
theorem toUnconditionalSchauderBasis_coord (hexp : ∀ x, HasSum (fun i ↦ b.coord i x • b i) x) :
    (b.toUnconditionalSchauderBasis hexp).coord = b.coord :=
  (rfl)

/-- The finite coordinate projections of `toUnconditionalSchauderBasis` are the original finite
coordinate projections. -/
@[simp]
theorem toUnconditionalSchauderBasis_proj (hexp : ∀ x, HasSum (fun i ↦ b.coord i x • b i) x)
    (A : Finset β) :
    (b.toUnconditionalSchauderBasis hexp).proj A = b.proj A :=
  (rfl)

/-- In a Banach space, the expansions of a generalized Schauder basis with nontrivial summation
filter converge unconditionally if and only if its finite coordinate projections are uniformly
bounded. -/
theorem forall_hasSum_iff_exists_forall_norm_proj_le [L.NeBot] [CompleteSpace X] :
    (∀ x, HasSum (fun i ↦ b.coord i x • b i) x) ↔ ∃ C, ∀ A : Finset β, ‖b.proj A‖ ≤ C :=
  ⟨fun h ↦ by simpa using (b.toUnconditionalSchauderBasis h).exists_norm_proj_le,
    fun ⟨_, hC⟩ ↦ b.hasSum_of_forall_norm_proj_le hC⟩

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

/-- The `i`-th coordinate of a convergent basis series is its `i`-th coefficient. The series may
converge along any nontrivial summation filter `L'` whose partial sums eventually contain `i`
(that is, `i ∈ L'.support`), which need not be the filter `L` of the basis. For `L'` below `atTop`,
such as `SummationFilter.conditional`, every index lies in the support by `simp`. -/
theorem coord_eq_of_hasSum {L' : SummationFilter β} [L'.NeBot] {a : β → 𝕜} {x : X}
    (h : HasSum (fun i ↦ a i • b i) x L') (i : β) (hi : i ∈ L'.support) :
    b.coord i x = a i :=
  -- Once the partial sums contain `i`, their `i`-th coordinate is constantly `a i`.
  tendsto_nhds_unique (((b.coord i).continuous.tendsto x).comp h)
    (tendsto_const_nhds.congr' (Eventually.mono hi fun _ hs ↦ (b.coord_sum a hs).symm))

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

/-- A summable series of rank-one coordinate maps takes each basis vector to its prescribed
vector. -/
theorem tsum_coord_smulRight_apply_basis (v : β → F)
    (hs : Summable (fun k ↦ (b.coord k).smulRight (v k))) (i : β) :
    (∑' k, (b.coord k).smulRight (v k)) (b i) = v i := by
  rw [tsum_apply hs, tsum_eq_single i fun k hki ↦ by simp [b.ortho, hki.symm]]
  simp [b.ortho]

end CoordinateSeries

end GeneralSchauderBasis

namespace UnconditionalSchauderBasis

section General

variable {β 𝕜 X : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup X] [NormedSpace 𝕜 X]
  (b : UnconditionalSchauderBasis β 𝕜 X)

/-- A uniform bound on the finite projections bounds the basis constant of an unconditional
basis. -/
theorem nnNormProjBound_le {C : NNReal} (hC : ∀ A : Finset β, ‖b.proj A‖ ≤ C) :
    b.nnNormProjBound ≤ C :=
  ciSup_le fun A ↦ by exact_mod_cast hC A

/-- A real uniform bound on the finite projections bounds the basis constant of an unconditional
basis. -/
theorem coe_nnNormProjBound_le {C : ℝ} (hC : ∀ A : Finset β, ‖b.proj A‖ ≤ C) :
    (b.nnNormProjBound : ℝ) ≤ C := by
  lift C to NNReal using (norm_nonneg (b.proj ∅)).trans (hC ∅)
  exact NNReal.coe_le_coe.2 (b.nnNormProjBound_le hC)

end General

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

/-- The finite coordinate projections of the classical basis agree with those of the unconditional
basis. -/
@[simp]
theorem proj_toSchauderBasis (A : Finset ℕ) :
    GeneralSchauderBasis.proj b.toSchauderBasis A = b.proj A :=
  (rfl)

/-- Converting an `ℕ`-indexed unconditional basis to a classical Schauder basis and back recovers
the unconditional basis. -/
@[simp]
theorem toUnconditionalSchauderBasis_toSchauderBasis
    (hexp : ∀ x, HasSum (fun i ↦ b.toSchauderBasis.coord i x • b.toSchauderBasis i) x) :
    b.toSchauderBasis.toUnconditionalSchauderBasis hexp = b :=
  (rfl)

end UnconditionalSchauderBasis

namespace SchauderBasis

variable {𝕜 X : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup X] [NormedSpace 𝕜 X]
  (b : SchauderBasis 𝕜 X)

/-- Precomposition with an initial projection is a finite linear combination of coordinates. -/
theorem comp_proj_eq_sum (f : StrongDual 𝕜 X) (n : ℕ) :
    f.comp (b.proj n) = ∑ i ∈ Finset.range n, f (b i) • b.coord i := by
  rw [proj, GeneralSchauderBasis.comp_proj_eq_sum]

/-- Converting a classical Schauder basis with unconditionally convergent expansions to an
unconditional basis and back recovers the classical basis. -/
@[simp]
theorem toSchauderBasis_toUnconditionalSchauderBasis
    (hexp : ∀ x, HasSum (fun i ↦ b.coord i x • b i) x) :
    (b.toUnconditionalSchauderBasis hexp).toSchauderBasis = b :=
  (rfl)

end SchauderBasis
