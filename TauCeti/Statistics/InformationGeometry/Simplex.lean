/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Basic.Real.Basic
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.Analysis.Calculus.FDeriv.Linear
public import Mathlib.LinearAlgebra.Pi
public import Mathlib.Topology.Algebra.Module.FiniteDimension
public import TauCeti.Analysis.Convex.StdSimplex.Boundary
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Tactic.LinearCombination

/-!
# The Fisher–Rao metric and the Amari–Chentsov tensor on probability simplices

The open probability simplex is `TauCeti.openStdSimplex ℝ (Fin m)`, the set of `p : Fin m → ℝ`
with positive coordinates summing to `1` (`TauCeti.mem_openStdSimplex_iff_sum_eq_one`); its
tangent space `simplexTangent m` is the submodule of vectors with coordinate sum `0`.

The **Fisher–Rao metric** at `p` is the bilinear form `fisherRao p u v = ∑ uᵢ vᵢ / pᵢ` and the
**Amari–Chentsov tensor** is the trilinear form `amariChentsov p u v w = ∑ uᵢ vᵢ wᵢ / pᵢ²`. Both
are defined for vectors indexed by any finite type and at every `p`, with Lean's `x / 0 = 0` at
vanishing coordinates.

A **congruent embedding** `e : CongruentEmbedding m n` (Chentsov's Markov congruent embedding of
`S_m` into `S_n`) is a surjection `e.block : Fin n → Fin m` onto the blocks together with positive
weights `e.q` summing to `1` on each block. Its linear map `e.toLinearMap`,
`p ↦ (p (block j) · q j)ⱼ`, is injective and maps the open simplex on `Fin m` into the open
simplex on `Fin n` and `simplexTangent m` into `simplexTangent n`; being linear, it is its own
derivative (`CongruentEmbedding.hasFDerivAt_toLinearMap`). Every permutation of `Fin m`, with
unit weights, is a congruent embedding (`CongruentEmbedding.ofPerm`), and every congruent
self-embedding with unit weights arises in this way (`CongruentEmbedding.exists_eq_ofPerm`).

## Main definitions

* `TauCeti.simplexTangent`: the tangent space of the simplex.
* `TauCeti.fisherRao`, `TauCeti.amariChentsov`: the Fisher–Rao metric and the Amari–Chentsov
  tensor.
* `TauCeti.CongruentEmbedding`, `TauCeti.CongruentEmbedding.toLinearMap`: congruent embeddings of
  simplices and their linear maps; `TauCeti.CongruentEmbedding.mk'` builds one without the
  surjectivity field, which follows from the weight condition; `TauCeti.CongruentEmbedding.ofPerm`
  is the embedding of a permutation.

## Main results

* `TauCeti.fisherRao_add_left`, `TauCeti.fisherRao_smul_left`, `TauCeti.amariChentsov_add_left`,
  `TauCeti.amariChentsov_smul_left`, their `_right` versions and the `_middle` versions for
  `amariChentsov`: the two forms are additive and homogeneous in each vector argument; the
  `_zero_left`, `_zero_middle` and `_zero_right` lemmas are `@[simp]`.
* `TauCeti.fisherRao_comm`, `TauCeti.amariChentsov_comm_left`,
  `TauCeti.amariChentsov_comm_right`: the two forms are symmetric in their vector arguments.
* `TauCeti.fisherRao_self_pos`: the Fisher–Rao form is positive definite at every point with
  positive coordinates, in particular on `simplexTangent m` at every point of the open simplex.
* `TauCeti.continuousOn_fisherRao`, `TauCeti.continuousOn_amariChentsov`: both forms are
  continuous in the base point on the open simplex, for fixed vector arguments.
* `TauCeti.finrank_simplexTangent`: the tangent space has dimension `m - 1`.
* `TauCeti.CongruentEmbedding.injective_toLinearMap`: the map of a congruent embedding is
  injective.
* `TauCeti.CongruentEmbedding.toLinearMap_mem_openStdSimplex`,
  `TauCeti.CongruentEmbedding.toLinearMap_mem_simplexTangent`: congruent embeddings preserve the
  open simplex and its tangent space.
* `TauCeti.fisherRao_congruentEmbedding`, `TauCeti.amariChentsov_congruentEmbedding`: the
  Fisher–Rao metric and the Amari–Chentsov tensor are invariant under congruent embeddings, at
  every `p` and for all vectors `u`, `v`, `w`; both are `@[simp]` (Chentsov, proof of Thm 11.1,
  pp. 159–160, for the Fisher–Rao form on tangent vectors at points of the open simplex).

## Attribution

Adapted from lean-CKSD (<https://github.com/bjbraams/lean-CKSD>),
`CKSD/Asymptotics/InformationGeometry.lean` (`fisherRaoMetric`, `amariChentsovTensor`,
`openProbabilitySimplex`, `simplexTangentSpace`, `CongruentSimplexEmbedding`,
`CongruentSimplexEmbedding.surjective_block`, `fisherRaoMetric_congruent_embedding`), with AI
assistance (Claude); restated for `Fin m` with the weight condition over the fibres of `block`.
The Amari–Chentsov invariance, positivity, dimension and permutation statements are new.

## References

* N. N. Čencov (Chentsov), *Statistical Decision Rules and Optimal Inference*, Translations of
  Mathematical Monographs 53, American Mathematical Society, 1982.
-/

public section

noncomputable section

namespace TauCeti

open Finset

/-! ### The tangent space of the simplex -/

/-- The tangent space of the simplex: the vectors of `Fin m → ℝ` with coordinate sum `0`. -/
def simplexTangent (m : ℕ) : Submodule ℝ (Fin m → ℝ) :=
  LinearMap.ker (∑ i, LinearMap.proj (R := ℝ) (φ := fun _ : Fin m ↦ ℝ) i)

/-- Membership in the tangent space: coordinate sum `0`. -/
@[simp]
theorem mem_simplexTangent {m : ℕ} {u : Fin m → ℝ} : u ∈ simplexTangent m ↔ ∑ i, u i = 0 := by
  simp [simplexTangent, LinearMap.sum_apply]

/-- On one coordinate the tangent space is trivial. -/
@[simp]
theorem simplexTangent_one : simplexTangent 1 = ⊥ := by
  ext u
  simp only [mem_simplexTangent, Fin.sum_univ_one, Submodule.mem_bot]
  exact ⟨fun h ↦ funext fun i ↦ by simpa [Subsingleton.elim i 0] using h, fun h ↦ by simp [h]⟩

/-- The tangent space of `S_m` has dimension `m - 1`; for `m = 0` both sides are `0`. -/
theorem finrank_simplexTangent (m : ℕ) : Module.finrank ℝ (simplexTangent m) = m - 1 := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp [Module.finrank_zero_of_subsingleton]
  have h := LinearMap.finrank_range_add_finrank_ker
    (∑ i, LinearMap.proj (R := ℝ) (φ := fun _ : Fin m ↦ ℝ) i)
  -- The coordinate sum is surjective: `c` is the sum of `Pi.single 0 c`.
  rw [LinearMap.range_eq_top.2 fun c ↦ ⟨Pi.single ⟨0, hm⟩ c, by
    simp [LinearMap.sum_apply, Pi.single_apply]⟩, finrank_top, Module.finrank_self,
    Module.finrank_fin_fun] at h
  rw [simplexTangent]
  omega

/-! ### The Fisher–Rao metric and the Amari–Chentsov tensor -/

section Forms

variable {ι : Type*} [Fintype ι]

/-- The Fisher–Rao metric `∑ uᵢ vᵢ / pᵢ` at `p`. -/
def fisherRao (p u v : ι → ℝ) : ℝ := ∑ i, u i * v i / p i

/-- The defining formula of `fisherRao`. -/
theorem fisherRao_def (p u v : ι → ℝ) : fisherRao p u v = ∑ i, u i * v i / p i := (rfl)

/-- The Amari–Chentsov tensor `∑ uᵢ vᵢ wᵢ / pᵢ²` at `p`. -/
def amariChentsov (p u v w : ι → ℝ) : ℝ := ∑ i, u i * v i * w i / p i ^ 2

/-- The defining formula of `amariChentsov`. -/
theorem amariChentsov_def (p u v w : ι → ℝ) :
    amariChentsov p u v w = ∑ i, u i * v i * w i / p i ^ 2 := (rfl)

/-! #### Multilinearity in the vector arguments -/

/-- The Fisher–Rao form vanishes when its first vector is `0`. -/
@[simp]
theorem fisherRao_zero_left (p v : ι → ℝ) : fisherRao p 0 v = 0 := by
  simp [fisherRao_def]

/-- The Fisher–Rao form vanishes when its second vector is `0`. -/
@[simp]
theorem fisherRao_zero_right (p u : ι → ℝ) : fisherRao p u 0 = 0 := by
  simp [fisherRao_def]

/-- The Fisher–Rao form is additive in its first vector. -/
theorem fisherRao_add_left (p u₁ u₂ v : ι → ℝ) :
    fisherRao p (u₁ + u₂) v = fisherRao p u₁ v + fisherRao p u₂ v := by
  simp only [fisherRao_def, Pi.add_apply, add_mul, add_div, sum_add_distrib]

/-- The Fisher–Rao form is additive in its second vector. -/
theorem fisherRao_add_right (p u v₁ v₂ : ι → ℝ) :
    fisherRao p u (v₁ + v₂) = fisherRao p u v₁ + fisherRao p u v₂ := by
  simp only [fisherRao_def, Pi.add_apply, mul_add, add_div, sum_add_distrib]

/-- The Fisher–Rao form is homogeneous in its first vector. -/
theorem fisherRao_smul_left (p : ι → ℝ) (c : ℝ) (u v : ι → ℝ) :
    fisherRao p (c • u) v = c * fisherRao p u v := by
  simp only [fisherRao_def, Pi.smul_apply, smul_eq_mul, mul_sum, mul_assoc, mul_div_assoc]

/-- The Fisher–Rao form is homogeneous in its second vector. -/
theorem fisherRao_smul_right (p : ι → ℝ) (c : ℝ) (u v : ι → ℝ) :
    fisherRao p u (c • v) = c * fisherRao p u v := by
  simp only [fisherRao_def, Pi.smul_apply, smul_eq_mul, mul_sum, mul_div_assoc]
  exact sum_congr rfl fun i _ ↦ by ring

/-- The Amari–Chentsov tensor vanishes when its first vector is `0`. -/
@[simp]
theorem amariChentsov_zero_left (p v w : ι → ℝ) : amariChentsov p 0 v w = 0 := by
  simp [amariChentsov_def]

/-- The Amari–Chentsov tensor vanishes when its second vector is `0`. -/
@[simp]
theorem amariChentsov_zero_middle (p u w : ι → ℝ) : amariChentsov p u 0 w = 0 := by
  simp [amariChentsov_def]

/-- The Amari–Chentsov tensor vanishes when its third vector is `0`. -/
@[simp]
theorem amariChentsov_zero_right (p u v : ι → ℝ) : amariChentsov p u v 0 = 0 := by
  simp [amariChentsov_def]

/-- The Amari–Chentsov tensor is additive in its first vector. -/
theorem amariChentsov_add_left (p u₁ u₂ v w : ι → ℝ) :
    amariChentsov p (u₁ + u₂) v w = amariChentsov p u₁ v w + amariChentsov p u₂ v w := by
  simp only [amariChentsov_def, Pi.add_apply, add_mul, add_div, sum_add_distrib]

/-- The Amari–Chentsov tensor is additive in its second vector. -/
theorem amariChentsov_add_middle (p u v₁ v₂ w : ι → ℝ) :
    amariChentsov p u (v₁ + v₂) w = amariChentsov p u v₁ w + amariChentsov p u v₂ w := by
  simp only [amariChentsov_def, Pi.add_apply, mul_add, add_mul, add_div, sum_add_distrib]

/-- The Amari–Chentsov tensor is additive in its third vector. -/
theorem amariChentsov_add_right (p u v w₁ w₂ : ι → ℝ) :
    amariChentsov p u v (w₁ + w₂) = amariChentsov p u v w₁ + amariChentsov p u v w₂ := by
  simp only [amariChentsov_def, Pi.add_apply, mul_add, add_div, sum_add_distrib]

/-- The Amari–Chentsov tensor is homogeneous in its first vector. -/
theorem amariChentsov_smul_left (p : ι → ℝ) (c : ℝ) (u v w : ι → ℝ) :
    amariChentsov p (c • u) v w = c * amariChentsov p u v w := by
  simp only [amariChentsov_def, Pi.smul_apply, smul_eq_mul, mul_sum, mul_assoc, mul_div_assoc]

/-- The Amari–Chentsov tensor is homogeneous in its second vector. -/
theorem amariChentsov_smul_middle (p : ι → ℝ) (c : ℝ) (u v w : ι → ℝ) :
    amariChentsov p u (c • v) w = c * amariChentsov p u v w := by
  simp only [amariChentsov_def, Pi.smul_apply, smul_eq_mul, mul_sum, mul_div_assoc]
  exact sum_congr rfl fun i _ ↦ by ring

/-- The Amari–Chentsov tensor is homogeneous in its third vector. -/
theorem amariChentsov_smul_right (p : ι → ℝ) (c : ℝ) (u v w : ι → ℝ) :
    amariChentsov p u v (c • w) = c * amariChentsov p u v w := by
  simp only [amariChentsov_def, Pi.smul_apply, smul_eq_mul, mul_sum, mul_div_assoc]
  exact sum_congr rfl fun i _ ↦ by ring

/-! #### Symmetry and positivity -/

/-- The Fisher–Rao form is symmetric. -/
theorem fisherRao_comm (p u v : ι → ℝ) : fisherRao p u v = fisherRao p v u := by
  simp only [fisherRao_def, mul_comm (u _)]

/-- The Amari–Chentsov tensor is symmetric in its first two vectors. -/
theorem amariChentsov_comm_left (p u v w : ι → ℝ) :
    amariChentsov p u v w = amariChentsov p v u w := by
  simp only [amariChentsov_def, mul_comm (u _)]

/-- The Amari–Chentsov tensor is symmetric in its last two vectors; with
`amariChentsov_comm_left`, it is symmetric under every permutation of its vectors. -/
theorem amariChentsov_comm_right (p u v w : ι → ℝ) :
    amariChentsov p u v w = amariChentsov p u w v := by
  simp only [amariChentsov_def, mul_right_comm (u _)]

/-- The Fisher–Rao form is positive semidefinite at every `p` with nonnegative coordinates. -/
theorem fisherRao_self_nonneg {p : ι → ℝ} (hp : ∀ i, 0 ≤ p i) (u : ι → ℝ) :
    0 ≤ fisherRao p u u :=
  sum_nonneg fun i _ ↦ div_nonneg (mul_self_nonneg (u i)) (hp i)

/-- The Fisher–Rao form is positive definite at every `p` with positive coordinates, in
particular on the tangent space at every point of the open simplex. -/
theorem fisherRao_self_pos {p : ι → ℝ} (hp : ∀ i, 0 < p i) {u : ι → ℝ} (hu : u ≠ 0) :
    0 < fisherRao p u u := by
  obtain ⟨i, hi⟩ := Function.ne_iff.1 hu
  exact sum_pos' (fun j _ ↦ div_nonneg (mul_self_nonneg (u j)) (hp j).le)
    ⟨i, mem_univ i, div_pos (mul_self_pos.2 hi) (hp i)⟩

/-! #### Continuity in the base point -/

/-- For fixed vectors, the Fisher–Rao form is continuous in the base point on the open simplex. -/
theorem continuousOn_fisherRao (u v : ι → ℝ) :
    ContinuousOn (fun p ↦ fisherRao p u v) (openStdSimplex ℝ ι) := by
  simp only [fisherRao_def]
  exact continuousOn_finsetSum _ fun i _ ↦
    continuousOn_const.div (continuous_apply i).continuousOn
      fun p hp ↦ ((mem_openStdSimplex_iff.1 hp).2 i).ne'

/-- For fixed vectors, the Amari–Chentsov tensor is continuous in the base point on the open
simplex. -/
theorem continuousOn_amariChentsov (u v w : ι → ℝ) :
    ContinuousOn (fun p ↦ amariChentsov p u v w) (openStdSimplex ℝ ι) := by
  simp only [amariChentsov_def]
  exact continuousOn_finsetSum _ fun i _ ↦
    continuousOn_const.div ((continuous_apply i).pow 2).continuousOn
      fun p hp ↦ pow_ne_zero 2 ((mem_openStdSimplex_iff.1 hp).2 i).ne'

end Forms

/-! ### Congruent embeddings -/

/-- A congruent embedding of `S_m` into `S_n` (Chentsov's Markov congruent embedding): a
surjection `block : Fin n → Fin m` onto the blocks and positive weights `q` summing to `1` on each
block. -/
structure CongruentEmbedding (m n : ℕ) where
  /-- The block `block j` of the output coordinate `j`. -/
  block : Fin n → Fin m
  /-- Every block is nonempty; this also follows from `sum_q` (see `CongruentEmbedding.mk'`). -/
  surjective : Function.Surjective block
  /-- The weight of each output coordinate within its block. -/
  q : Fin n → ℝ
  /-- The weights are positive. -/
  q_pos : ∀ j, 0 < q j
  /-- The weights sum to `1` on each block. -/
  sum_q : ∀ i, ∑ j ∈ Finset.univ.filter (fun j ↦ block j = i), q j = 1

namespace CongruentEmbedding

variable {m n : ℕ}

/-- A congruent embedding from its blocks and weights alone: surjectivity of `block` follows
from the weight condition, since a sum over an empty block is `0`. -/
def mk' (block : Fin n → Fin m) (q : Fin n → ℝ) (q_pos : ∀ j, 0 < q j)
    (sum_q : ∀ i, ∑ j ∈ Finset.univ.filter (fun j ↦ block j = i), q j = 1) :
    CongruentEmbedding m n where
  block := block
  surjective i := by
    have h : ∑ j ∈ univ.filter (fun j ↦ block j = i), q j ≠ 0 := by
      rw [sum_q i]
      exact one_ne_zero
    obtain ⟨j, hj, -⟩ := exists_ne_zero_of_sum_ne_zero h
    exact ⟨j, (mem_filter.1 hj).2⟩
  q := q
  q_pos := q_pos
  sum_q := sum_q

/-- The blocks of `CongruentEmbedding.mk'`. -/
@[simp]
theorem mk'_block (block : Fin n → Fin m) (q : Fin n → ℝ) (q_pos) (sum_q) :
    (mk' block q q_pos sum_q).block = block := (rfl)

/-- The weights of `CongruentEmbedding.mk'`. -/
@[simp]
theorem mk'_q (block : Fin n → Fin m) (q : Fin n → ℝ) (q_pos) (sum_q) :
    (mk' block q q_pos sum_q).q = q := (rfl)

variable (e : CongruentEmbedding m n)

/-- Summing a function of the blocks against the weights gives the sum over the blocks. -/
theorem sum_comp_block_mul_q (a : Fin m → ℝ) : ∑ j, a (e.block j) * e.q j = ∑ i, a i := by
  rw [← sum_fiberwise univ e.block]
  refine sum_congr rfl fun i _ ↦ ?_
  calc ∑ j ∈ univ.filter (fun j ↦ e.block j = i), a (e.block j) * e.q j
      = ∑ j ∈ univ.filter (fun j ↦ e.block j = i), a i * e.q j :=
        sum_congr rfl fun j hj ↦ by rw [(mem_filter.1 hj).2]
    _ = a i := by rw [← mul_sum, e.sum_q, mul_one]

/-- The linear map `p ↦ (p (block j) · q j)ⱼ` of a congruent embedding. -/
def toLinearMap : (Fin m → ℝ) →ₗ[ℝ] (Fin n → ℝ) where
  toFun p j := p (e.block j) * e.q j
  map_add' p p' := by ext j; simp [add_mul]
  map_smul' c p := by ext j; simp [mul_assoc]

/-- The coordinates of the image under a congruent embedding. -/
@[simp]
theorem toLinearMap_apply (p : Fin m → ℝ) (j : Fin n) :
    e.toLinearMap p j = p (e.block j) * e.q j := (rfl)

/-- A congruent embedding preserves coordinate sums. -/
theorem sum_toLinearMap_apply (p : Fin m → ℝ) : ∑ j, e.toLinearMap p j = ∑ i, p i := by
  simpa using e.sum_comp_block_mul_q p

/-- The map of a congruent embedding is injective: every block is nonempty and the weights are
nonzero. -/
theorem injective_toLinearMap : Function.Injective e.toLinearMap := by
  intro p p' h
  funext i
  obtain ⟨j, rfl⟩ := e.surjective i
  exact mul_right_cancel₀ (e.q_pos j).ne' (congrFun h j)

/-- The map of a congruent embedding is linear, so it is its own derivative. -/
theorem hasFDerivAt_toLinearMap (p : Fin m → ℝ) :
    HasFDerivAt e.toLinearMap (LinearMap.toContinuousLinearMap e.toLinearMap) p :=
  (LinearMap.toContinuousLinearMap e.toLinearMap).hasFDerivAt

/-- A congruent embedding maps the open simplex on `Fin m` into the open simplex on `Fin n`. -/
theorem toLinearMap_mem_openStdSimplex {p : Fin m → ℝ} (hp : p ∈ openStdSimplex ℝ (Fin m)) :
    e.toLinearMap p ∈ openStdSimplex ℝ (Fin n) := by
  rw [mem_openStdSimplex_iff_sum_eq_one] at hp ⊢
  exact ⟨fun j ↦ mul_pos (hp.1 _) (e.q_pos j), (e.sum_toLinearMap_apply p).trans hp.2⟩

/-- A congruent embedding maps tangent vectors of `S_m` to tangent vectors of `S_n`. -/
theorem toLinearMap_mem_simplexTangent {u : Fin m → ℝ} (hu : u ∈ simplexTangent m) :
    e.toLinearMap u ∈ simplexTangent n := by
  rw [mem_simplexTangent] at hu ⊢
  rw [e.sum_toLinearMap_apply, hu]

/-- `CongruentEmbedding.toLinearMap_mem_openStdSimplex` as a `Set.MapsTo` statement. -/
theorem mapsTo_toLinearMap_openStdSimplex :
    Set.MapsTo e.toLinearMap (openStdSimplex ℝ (Fin m)) (openStdSimplex ℝ (Fin n)) :=
  fun _ ↦ e.toLinearMap_mem_openStdSimplex

/-- `CongruentEmbedding.toLinearMap_mem_simplexTangent` as a submodule inclusion. -/
theorem simplexTangent_le_comap_toLinearMap :
    simplexTangent m ≤ (simplexTangent n).comap e.toLinearMap :=
  fun _ ↦ e.toLinearMap_mem_simplexTangent

/-- The congruent embedding of a permutation `σ` of `Fin m`, with unit weights. -/
def ofPerm (σ : Equiv.Perm (Fin m)) : CongruentEmbedding m m where
  block := σ
  surjective := σ.surjective
  q _ := 1
  q_pos _ := one_pos
  sum_q i := by
    rw [sum_const, nsmul_one, Nat.cast_eq_one, card_eq_one]
    exact ⟨σ.symm i, by ext j; simp [Equiv.eq_symm_apply]⟩

/-- The blocks of the embedding of a permutation. -/
@[simp]
theorem ofPerm_block (σ : Equiv.Perm (Fin m)) : (ofPerm σ).block = σ := (rfl)

/-- The weights of the embedding of a permutation. -/
@[simp]
theorem ofPerm_q (σ : Equiv.Perm (Fin m)) : (ofPerm σ).q = 1 := (rfl)

/-- The embedding of a permutation `σ` permutes the coordinates: `p ↦ p ∘ σ`. -/
@[simp]
theorem toLinearMap_ofPerm_apply (σ : Equiv.Perm (Fin m)) (p : Fin m → ℝ) :
    (ofPerm σ).toLinearMap p = p ∘ σ := by
  ext j
  simp [ofPerm]

/-- Every congruent self-embedding with unit weights is the embedding of a permutation: its
block map is a surjection of `Fin m` onto itself, hence a bijection. -/
theorem exists_eq_ofPerm (e : CongruentEmbedding m m) (he : e.q = 1) :
    ∃ σ : Equiv.Perm (Fin m), e = ofPerm σ := by
  refine ⟨Equiv.ofBijective e.block ⟨Finite.injective_iff_surjective.2 e.surjective,
    e.surjective⟩, ?_⟩
  cases e
  subst he
  rfl

/-- The congruent embedding of the identity permutation has the identity map. -/
@[simp]
theorem toLinearMap_ofPerm_refl : (ofPerm (Equiv.refl (Fin m))).toLinearMap = LinearMap.id :=
  LinearMap.ext fun p ↦ by simp

end CongruentEmbedding

/-! ### Invariance -/

/-- **Invariance of the Fisher–Rao metric** under congruent embeddings, at every `p` and for all
`u`, `v`. -/
@[simp]
theorem fisherRao_congruentEmbedding {m n : ℕ} (e : CongruentEmbedding m n) (p u v : Fin m → ℝ) :
    fisherRao (e.toLinearMap p) (e.toLinearMap u) (e.toLinearMap v) = fisherRao p u v := by
  -- The summand at `j` is the summand at `block j` times `q j`, also where `p (block j) = 0`.
  have h (j : Fin n) : u (e.block j) * e.q j * (v (e.block j) * e.q j) / (p (e.block j) * e.q j) =
      u (e.block j) * v (e.block j) / p (e.block j) * e.q j := by
    simp only [div_eq_mul_inv, mul_inv]
    linear_combination u (e.block j) * v (e.block j) * (p (e.block j))⁻¹ * e.q j *
      mul_inv_cancel₀ (e.q_pos j).ne'
  simp only [fisherRao_def, CongruentEmbedding.toLinearMap_apply, h]
  exact e.sum_comp_block_mul_q fun i ↦ u i * v i / p i

/-- **Invariance of the Amari–Chentsov tensor** under congruent embeddings, at every `p` and for
all `u`, `v`, `w`. -/
@[simp]
theorem amariChentsov_congruentEmbedding {m n : ℕ} (e : CongruentEmbedding m n)
    (p u v w : Fin m → ℝ) :
    amariChentsov (e.toLinearMap p) (e.toLinearMap u) (e.toLinearMap v) (e.toLinearMap w) =
      amariChentsov p u v w := by
  -- The summand at `j` is the summand at `block j` times `q j`, also where `p (block j) = 0`.
  have h (j : Fin n) : u (e.block j) * e.q j * (v (e.block j) * e.q j) * (w (e.block j) * e.q j) /
      (p (e.block j) * e.q j) ^ 2 =
        u (e.block j) * v (e.block j) * w (e.block j) / p (e.block j) ^ 2 * e.q j := by
    simp only [div_eq_mul_inv, mul_pow, mul_inv]
    linear_combination u (e.block j) * v (e.block j) * w (e.block j) * (p (e.block j) ^ 2)⁻¹ *
      e.q j * (e.q j * (e.q j)⁻¹ + 1) * mul_inv_cancel₀ (e.q_pos j).ne'
  simp only [amariChentsov_def, CongruentEmbedding.toLinearMap_apply, h]
  exact e.sum_comp_block_mul_q fun i ↦ u i * v i * w i / p i ^ 2

end TauCeti
