/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.GeneralLinear.Casimir
public import TauCeti.Algebra.Lie.GeneralLinear.Embedding
public import TauCeti.Algebra.Lie.UniversalEnveloping.Functoriality
public import Mathlib.LinearAlgebra.Matrix.Trace

import TauCeti.Algebra.Lie.Matrix.Single

/-!
# The Gelfand invariants of `gl n`

Let `𝔼` be the square matrix over the universal enveloping algebra `U(gl n)` whose `(i, j)` entry
is the canonical generator `Eᵢⱼ = ι(Eᵢⱼ)` of the matrix unit. The **Gelfand invariants** are the
traces of its powers,

`Cᵣ = trace (𝔼 ^ r) = ∑ i₁, …, ∑ iᵣ, Eᵢ₁ᵢ₂ Eᵢ₂ᵢ₃ ⋯ Eᵢᵣᵢ₁ ∈ U(gl n)`.

They are central in `U(gl n)` over every commutative ring. The engine is the commutator identity

`⁅Eₐb, (𝔼 ^ r)ᵢⱼ⁆ = δ_{b i} (𝔼 ^ r)ₐⱼ - δ_{j a} (𝔼 ^ r)ᵢb`,

proved by induction on `r` from the case `r = 1`, which is the bracket of two matrix units. Taking
`i = j` and summing over `i`, the two terms cancel, so `Cᵣ` commutes with every matrix-unit
generator and hence with all of `U(gl n)`. In degree two `C₂` is the trace-form Casimir element
`TauCeti.glCasimir`, and in degree one `C₁` is the image of the identity matrix.

An injection `f : m ↪ n` embeds `gl m` in `gl n` (`TauCeti.glEmbedding`), and the induced map of
enveloping algebras sends `𝔼` for `gl m` to the submatrix of `𝔼` for `gl n` on the range of `f`.
For the chain of upper-left corners `gl 1 ⊆ gl 2 ⊆ ⋯ ⊆ gl n` the images of the Gelfand invariants
of all the corners are the **Gelfand-Tsetlin generators** of `U(gl n)`. They pairwise commute: the
generator of a smaller corner lies in the image of the enveloping algebra of a larger corner, whose
Gelfand invariants are central there.

## Main definitions

* `TauCeti.glGeneratorMatrix`: the matrix `𝔼` of matrix-unit generators of `U(gl n)`.
* `TauCeti.gelfandInvariant`: the Gelfand invariant `Cᵣ = trace (𝔼 ^ r)`.
* `TauCeti.gelfandTsetlinGenerator`: the image in `U(gl (Fin n))` of the Gelfand invariant of the
  upper-left corner `gl (Fin k)`.

## Main results

* `TauCeti.lie_ι_single_glGeneratorMatrix_pow_apply`: the commutator identity above.
* `TauCeti.gelfandInvariant_mem_center`: the Gelfand invariants are central in `U(gl n)`.
* `TauCeti.gelfandInvariant_zero`, `TauCeti.gelfandInvariant_one` and
  `TauCeti.gelfandInvariant_two`: the invariants of degree at most two are the rank, the image of
  the identity matrix and the trace-form Casimir element.
* `TauCeti.map_glEmbedding_gelfandInvariant`: the image of a Gelfand invariant along a corner
  embedding is the trace of a power of the corresponding submatrix of `𝔼`.
* `TauCeti.commute_map_glEmbedding_gelfandInvariant`: images of Gelfand invariants along nested
  corner embeddings commute.
* `TauCeti.commute_gelfandTsetlinGenerator_map_glEmbedding`: a Gelfand-Tsetlin generator at level
  `k` commutes with the image of `U(gl (Fin k))`.
* `TauCeti.commute_gelfandTsetlinGenerator`: the Gelfand-Tsetlin generators pairwise commute.

## References

* I. M. Gelfand, *The center of an infinitesimal group ring*, Mat. Sbornik N.S. 26(68) (1950),
  103-112.
* A. Molev, *Yangians and Classical Lie Algebras*, Mathematical Surveys and Monographs 143,
  American Mathematical Society (2007), Chapter 7.
-/

public section

open Finset Matrix UniversalEnvelopingAlgebra

namespace TauCeti

attribute [local instance 100] LieRing.ofAssociativeRing

variable (K : Type*) [CommRing K]

section Invariant

variable (n : Type*) [Fintype n] [DecidableEq n]

local notation "Ugl" => UniversalEnvelopingAlgebra K (Matrix n n K)

/-- The matrix `𝔼` of matrix-unit generators of `U(gl n)`: its `(i, j)` entry is the canonical
generator `ι(Eᵢⱼ)` of the matrix unit `Eᵢⱼ`. -/
noncomputable def glGeneratorMatrix : Matrix n n Ugl :=
  Matrix.of fun i j => ι K (single i j (1 : K))

@[simp]
theorem glGeneratorMatrix_apply (i j : n) :
    glGeneratorMatrix K n i j = ι K (single i j (1 : K)) :=
  (rfl)

/-- The **Gelfand invariant** `Cᵣ = trace (𝔼 ^ r) = ∑ Eᵢ₁ᵢ₂ Eᵢ₂ᵢ₃ ⋯ Eᵢᵣᵢ₁` of degree `r` in the
universal enveloping algebra of `gl n`. -/
noncomputable def gelfandInvariant (r : ℕ) : Ugl :=
  trace (glGeneratorMatrix K n ^ r)

theorem gelfandInvariant_def (r : ℕ) :
    gelfandInvariant K n r = trace (glGeneratorMatrix K n ^ r) :=
  (rfl)

/-- The Gelfand invariant of degree zero is the rank. -/
@[simp]
theorem gelfandInvariant_zero : gelfandInvariant K n 0 = Fintype.card n := by
  rw [gelfandInvariant_def, pow_zero, trace_one]

/-- The Gelfand invariant of degree one is the image of the identity matrix. -/
@[simp]
theorem gelfandInvariant_one : gelfandInvariant K n 1 = ι K (1 : Matrix n n K) := by
  simp only [gelfandInvariant_def, pow_one, trace, diag_apply, glGeneratorMatrix_apply,
    ← map_sum, sum_single_one]

/-- The Gelfand invariant of degree two is the trace-form Casimir element. -/
theorem gelfandInvariant_two : gelfandInvariant K n 2 = glCasimir K n := by
  simp only [gelfandInvariant_def, glCasimir_def, sq, trace, diag_apply, mul_apply,
    glGeneratorMatrix_apply]

/-- The bracket of a matrix-unit generator with an entry of `𝔼 ^ r`:
`⁅Eₐb, (𝔼 ^ r)ᵢⱼ⁆ = δ_{b i} (𝔼 ^ r)ₐⱼ - δ_{j a} (𝔼 ^ r)ᵢb`. -/
theorem lie_ι_single_glGeneratorMatrix_pow_apply (a b i j : n) (r : ℕ) :
    ⁅ι K (single a b (1 : K)), (glGeneratorMatrix K n ^ r) i j⁆ =
      (if b = i then (glGeneratorMatrix K n ^ r) a j else 0) -
        if j = a then (glGeneratorMatrix K n ^ r) i b else 0 := by
  induction r generalizing i j with
  | zero =>
    simp only [pow_zero, one_apply, LieRing.of_associative_ring_bracket, mul_ite, ite_mul,
      mul_one, one_mul, mul_zero, zero_mul]
    split_ifs <;> subst_vars <;> simp_all
  | succ r ih =>
    have hleib (x y z : Ugl) : ⁅x, y * z⁆ = ⁅x, y⁆ * z + y * ⁅x, z⁆ := by
      simp only [LieRing.of_associative_ring_bracket]
      noncomm_ring
    have hgen (k : n) : ⁅ι K (single a b (1 : K)), glGeneratorMatrix K n k j⁆ =
        (if b = k then glGeneratorMatrix K n a j else 0) -
          if j = a then glGeneratorMatrix K n k b else 0 := by
      rw [glGeneratorMatrix_apply, ← LieHom.map_lie, Matrix.lie_single_single]
      split_ifs <;> simp
    simp only [pow_succ, mul_apply]
    rw [lie_sum]
    simp_rw [hleib, ih, hgen]
    simp only [sub_mul, mul_sub, ite_mul, mul_ite, zero_mul, mul_zero, sum_add_distrib,
      sum_sub_distrib, sum_ite_eq, sum_ite_eq', mem_univ, ite_true]
    by_cases hbi : b = i <;> by_cases hja : j = a <;>
      simp only [hbi, hja, ite_true, ite_false, sub_zero, zero_sub, sum_const_zero] <;>
      abel

/-- A matrix-unit generator commutes with every Gelfand invariant. -/
private theorem lie_ι_single_gelfandInvariant (a b : n) (r : ℕ) :
    ⁅ι K (single a b (1 : K)), gelfandInvariant K n r⁆ = 0 := by
  simp only [gelfandInvariant_def, trace, diag_apply, lie_sum,
    lie_ι_single_glGeneratorMatrix_pow_apply, sum_sub_distrib, sum_ite_eq, sum_ite_eq',
    mem_univ, ite_true, sub_self]

/-- **The Gelfand invariants are central** in the universal enveloping algebra of `gl n`. -/
theorem gelfandInvariant_mem_center (r : ℕ) :
    gelfandInvariant K n r ∈ Subalgebra.center K Ugl := by
  refine (UniversalEnvelopingAlgebra.mem_center_iff_forall_lie_ι K (Matrix n n K)).mpr ?_
  intro X
  rw [← lie_skew, neg_eq_zero, matrix_eq_sum_single X]
  simp only [map_sum, sum_lie]
  refine sum_eq_zero fun a _ => sum_eq_zero fun b _ => ?_
  rw [← mul_one (X a b), ← smul_eq_mul, ← smul_single, map_smul, smul_lie,
    lie_ι_single_gelfandInvariant, smul_zero]

/-- Any two Gelfand invariants commute. -/
theorem commute_gelfandInvariant (r s : ℕ) :
    Commute (gelfandInvariant K n r) (gelfandInvariant K n s) :=
  Subalgebra.mem_center_iff.mp (gelfandInvariant_mem_center K n s) _

end Invariant

section Embedding

variable {K}
variable {l m n : Type*} [Fintype l] [DecidableEq l] [Fintype m]
  [DecidableEq m] [Fintype n] [DecidableEq n]

/-- The enveloping-algebra map of a corner embedding sends the generator matrix of `gl m` to the
submatrix of the generator matrix of `gl n` on the range of the embedding. -/
theorem map_glEmbedding_glGeneratorMatrix (f : m ↪ n) :
    (glGeneratorMatrix K m).map (UniversalEnvelopingAlgebra.map K (glEmbedding K f)) =
      (glGeneratorMatrix K n).submatrix f f := by
  ext a b
  simp only [map_apply, glGeneratorMatrix_apply, submatrix_apply,
    UniversalEnvelopingAlgebra.map_ι, glEmbedding_single]

/-- The image of the Gelfand invariant of `gl m` along a corner embedding `f : m ↪ n` is the
trace of the `r`-th power of the submatrix of `𝔼` on the range of `f`. -/
theorem map_glEmbedding_gelfandInvariant (f : m ↪ n) (r : ℕ) :
    UniversalEnvelopingAlgebra.map K (glEmbedding K f) (gelfandInvariant K m r) =
      trace ((glGeneratorMatrix K n).submatrix f f ^ r) := by
  rw [gelfandInvariant_def, AddMonoidHom.map_trace, ← map_glEmbedding_glGeneratorMatrix,
    ← AlgHom.mapMatrix_apply, ← AlgHom.mapMatrix_apply, map_pow]

/-- Images of Gelfand invariants along nested corner embeddings `l ↪ m ↪ n` commute: the image
of an invariant of `gl l` lies in the image of `U(gl m)`, where the invariants of `gl m` are
central. -/
theorem commute_map_glEmbedding_gelfandInvariant (f : l ↪ m) (g : m ↪ n) (r s : ℕ) :
    Commute
      (UniversalEnvelopingAlgebra.map K (glEmbedding K (f.trans g)) (gelfandInvariant K l r))
      (UniversalEnvelopingAlgebra.map K (glEmbedding K g) (gelfandInvariant K m s)) := by
  rw [glEmbedding_trans, UniversalEnvelopingAlgebra.map_comp, AlgHom.comp_apply]
  exact Commute.map (Subalgebra.mem_center_iff.mp (gelfandInvariant_mem_center K m s) _) _

end Embedding

section Chain

variable {n : ℕ}

/-- The **Gelfand-Tsetlin generator** of degree `r` at level `k ≤ n`: the image in `U(gl (Fin n))`
of the Gelfand invariant `Cᵣ` of the upper-left corner `gl (Fin k)`. -/
noncomputable def gelfandTsetlinGenerator {k : ℕ} (hk : k ≤ n) (r : ℕ) :
    UniversalEnvelopingAlgebra K (Matrix (Fin n) (Fin n) K) :=
  UniversalEnvelopingAlgebra.map K (glEmbedding K (Fin.castLEEmb hk))
    (gelfandInvariant K (Fin k) r)

theorem gelfandTsetlinGenerator_def {k : ℕ} (hk : k ≤ n) (r : ℕ) :
    gelfandTsetlinGenerator K hk r =
      UniversalEnvelopingAlgebra.map K (glEmbedding K (Fin.castLEEmb hk))
        (gelfandInvariant K (Fin k) r) :=
  (rfl)

/-- The Gelfand-Tsetlin generator of degree `r` at level `k` is the trace of the `r`-th power of
the upper-left `k × k` corner of the generator matrix. -/
theorem gelfandTsetlinGenerator_eq_trace {k : ℕ} (hk : k ≤ n) (r : ℕ) :
    gelfandTsetlinGenerator K hk r =
      trace ((glGeneratorMatrix K (Fin n)).submatrix (Fin.castLE hk) (Fin.castLE hk) ^ r) :=
  map_glEmbedding_gelfandInvariant _ r

/-- At the top level the Gelfand-Tsetlin generators are the Gelfand invariants of `gl (Fin n)`. -/
@[simp]
theorem gelfandTsetlinGenerator_self (r : ℕ) :
    gelfandTsetlinGenerator K le_rfl r = gelfandInvariant K (Fin n) r := by
  rw [gelfandTsetlinGenerator_eq_trace, gelfandInvariant_def, Fin.castLE_rfl, submatrix_id_id]

/-- A Gelfand-Tsetlin generator at level `k` commutes with the image of `U(gl (Fin k))`. -/
theorem commute_gelfandTsetlinGenerator_map_glEmbedding {k : ℕ} (hk : k ≤ n) (r : ℕ)
    (u : UniversalEnvelopingAlgebra K (Matrix (Fin k) (Fin k) K)) :
    Commute (gelfandTsetlinGenerator K hk r)
      (UniversalEnvelopingAlgebra.map K (glEmbedding K (Fin.castLEEmb hk)) u) :=
  (Commute.map (Subalgebra.mem_center_iff.mp (gelfandInvariant_mem_center K (Fin k) r) u) _).symm

/-- **The Gelfand-Tsetlin generators pairwise commute**, across all levels and degrees. -/
theorem commute_gelfandTsetlinGenerator {k k' : ℕ} (hk : k ≤ n) (hk' : k' ≤ n) (r s : ℕ) :
    Commute (gelfandTsetlinGenerator K hk r) (gelfandTsetlinGenerator K hk' s) := by
  wlog h : k ≤ k' generalizing k k' r s
  · exact (this hk' hk s r (le_of_not_ge h)).symm
  have hemb : Fin.castLEEmb hk = (Fin.castLEEmb h).trans (Fin.castLEEmb hk') := by
    ext; simp
  rw [gelfandTsetlinGenerator_def, gelfandTsetlinGenerator_def, hemb]
  exact commute_map_glEmbedding_gelfandInvariant _ _ r s

end Chain

end TauCeti
