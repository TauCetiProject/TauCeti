/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.ConstantMultiplication.Generators
public import TauCeti.Algebra.Lie.D4.Tripled.GroupScheme
public import TauCeti.Algebra.Lie.D4.Tripled.TrilinearForm
public import TauCeti.Algebra.Lie.UniversalEnveloping.Kostant.RootSubgroup.Scheme.ToralClosure.ConstantMultiplication

/-!
# The triality product on the tripled type-D₄ module

The three eight-dimensional blocks `8ᵥ`, `8ₛ`, `8꜀` of the tripled type-`D₄` module carry the
triality trilinear form `TauCeti.D4Tripled.trialityCoefficient`. Reading its third argument
through the pairing of each weight vector `e_a` with the weight vector `e_{a*}` of the opposite
weight, with the signs `TauCeti.D4Tripled.pairingSign`, turns the symmetrized form into a
commutative bilinear product on the whole twenty-four-dimensional module:

```text
e_k * e_j = ∑ᵢ ε(i) t(k, j, i*) eᵢ,
```

where `t` is the triality coefficient extended symmetrically to all orderings of the three blocks
and `ε` is `pairingSign`. The product of two vectors from different blocks lies in the third block,
the product of two vectors of one block vanishes
(`TauCeti.D4Tripled.symmetricTrialityCoefficient_eq_zero_of_d4TripledSummand_eq`), and every
structure constant is `-1`, `0` or `1`.

The main result is that the tripled carrier `TauCeti.D4Tripled.groupScheme` preserves this product,
as a group scheme: every matrix-valued point over every commutative ring is multiplicative for it.
It suffices to check the generators. A numbered root subgroup has points `1 + uX` with `X` a raising
or lowering matrix, and `X` is a derivation of the product whose second-order terms vanish; a
weight-torus point is diagonal, and the product is homogeneous for the weights. Both are verified
on the integral structure constants by kernel computation.

The product is a tool for controlling the carrier's points: a diagonal carrier point is forced to
be multiplicative along every nonzero structure constant, which pins it to the weight torus.

## Main declarations

* `TauCeti.D4Tripled.oppositeIndex`: the basis index of the opposite weight.
* `TauCeti.D4Tripled.symmetricTrialityCoefficient`: the triality coefficient on all orderings of
  the three blocks.
* `TauCeti.D4Tripled.trialityProductMatrix`: the structure matrices of the product.
* `TauCeti.D4Tripled.trialityProductMatrix_apply_eq_zero_of_weight_ne`: the product is
  homogeneous for the weights.
* `TauCeti.D4Tripled.eq_of_eq_mul_of_trialityProductMatrix_ne_zero`: a function multiplicative
  along the product is determined by its values at four basis indices.
* `TauCeti.D4Tripled.preserves_trialityProductMatrix_rootSubgroupPoints` and
  `TauCeti.D4Tripled.preserves_trialityProductMatrix_weightTorusPoints`: the generators preserve
  the product.
* `TauCeti.D4Tripled.constantMultiplicationDefiningHopfIdeal_le_definingIdeal`: the carrier is a
  closed subgroup scheme of the stabilizer of the product.
* `TauCeti.D4Tripled.preserves_trialityProductMatrix_of_mem_points`: every carrier point
  preserves the product.

## References

* J. F. Adams, *Lectures on Exceptional Lie Groups*, Chapter 3.
* T. A. Springer and F. D. Veldkamp, *Octonions, Jordan Algebras and Exceptional Groups*, Chapter 3.
* The reduction to generators follows the tensor-invariance argument for the short-root `G₂`
  carrier in `TauCeti.Algebra.Lie.G2.ShortRoot.PrimeField.PreservesTensors`.
-/

public section

open scoped Matrix

namespace TauCeti.D4Tripled

open TauCeti.DynkinType

universe v

/-! ## The product -/

/-- The basis index whose tripled weight is the negative of the weight at `a`. Each block lists
its eight weights so that opposite weights sit at local positions `ℓ` and `7 - ℓ`. -/
def oppositeIndex (a : Fin 24) : Fin 24 :=
  ⟨8 * (a.val / 8) + (7 - a.val % 8), by omega⟩

/-- The weight at the opposite index is the negative weight. -/
@[simp]
theorem d4TripledWeight_oppositeIndex (a : Fin 24) :
    d4TripledWeight (oppositeIndex a) = -d4TripledWeight a := by
  revert a
  decide +kernel

/-- The opposite index lies in the same block. -/
@[simp]
theorem d4TripledSummand_oppositeIndex (a : Fin 24) :
    d4TripledSummand (oppositeIndex a) = d4TripledSummand a := by
  revert a
  decide +kernel

/-- Taking the opposite index twice returns the original index. -/
@[simp]
theorem oppositeIndex_oppositeIndex (a : Fin 24) : oppositeIndex (oppositeIndex a) = a := by
  revert a
  decide +kernel

/-- The sign with which the product reads the basis vector at `a` against the basis vector of the
opposite weight. It depends only on the position of `a` inside its block, and agrees at `a` and at
`oppositeIndex a`. -/
def pairingSign (a : Fin 24) : ℤ :=
  ![1, -1, 1, -1, -1, 1, -1, 1] ⟨a.val % 8, by omega⟩

/-- The pairing sign takes the same value at a basis index and at its opposite. -/
@[simp]
theorem pairingSign_oppositeIndex (a : Fin 24) : pairingSign (oppositeIndex a) = pairingSign a := by
  revert a
  decide +kernel

/-- The triality coefficient of three basis indices read in block order: the coefficient when `a`,
`b`, `c` lie in the blocks `8ᵥ`, `8ₛ`, `8꜀` respectively, and zero otherwise. -/
private def blockTrialityCoefficient (a b c : Fin 24) : ℤ :=
  if h : d4TripledSummand a = (0 : Fin 3) ∧ d4TripledSummand b = (1 : Fin 3) ∧
      d4TripledSummand c = (2 : Fin 3) then
    trialityCoefficient ⟨a, h.1⟩ ⟨b, h.2.1⟩ ⟨c, h.2.2⟩
  else 0

/-- **The triality coefficient on all orderings of the three blocks.** It is the triality
coefficient of the three indices rearranged into block order when they lie in three different
blocks, and zero otherwise. -/
def symmetricTrialityCoefficient (a b c : Fin 24) : ℤ :=
  blockTrialityCoefficient a b c + blockTrialityCoefficient a c b +
    blockTrialityCoefficient b a c + blockTrialityCoefficient b c a +
      blockTrialityCoefficient c a b + blockTrialityCoefficient c b a

/-- On three indices in block order the symmetric coefficient is the triality coefficient. -/
@[simp]
theorem symmetricTrialityCoefficient_coe (a : Block 0) (b : Block 1) (c : Block 2) :
    symmetricTrialityCoefficient a b c = trialityCoefficient a b c := by
  obtain ⟨a, ha⟩ := a
  obtain ⟨b, hb⟩ := b
  obtain ⟨c, hc⟩ := c
  simp [symmetricTrialityCoefficient, blockTrialityCoefficient, ha, hb, hc]

/-- The symmetric coefficient is symmetric in its first two arguments. -/
theorem symmetricTrialityCoefficient_swap_left (a b c : Fin 24) :
    symmetricTrialityCoefficient a b c = symmetricTrialityCoefficient b a c := by
  simp only [symmetricTrialityCoefficient]
  ring

/-- The symmetric coefficient is symmetric in its last two arguments. -/
theorem symmetricTrialityCoefficient_swap_right (a b c : Fin 24) :
    symmetricTrialityCoefficient a b c = symmetricTrialityCoefficient a c b := by
  simp only [symmetricTrialityCoefficient]
  ring

/-- The symmetric coefficient vanishes when its first two indices lie in the same block. -/
theorem symmetricTrialityCoefficient_eq_zero_of_d4TripledSummand_eq {a b : Fin 24}
    (h : d4TripledSummand a = d4TripledSummand b) (c : Fin 24) :
    symmetricTrialityCoefficient a b c = 0 := by
  revert a b c
  simp only [symmetricTrialityCoefficient, blockTrialityCoefficient, trialityCoefficient_apply]
  decide +kernel

/-- **The structure matrices of the triality product.** The entry `(i, j)` of the matrix at `k` is
the coefficient of `eᵢ` in `e_k * e_j`, namely `pairingSign i` times the symmetric triality
coefficient of `k`, `j` and the index opposite to `i`. -/
def trialityProductMatrix (k : Fin 24) : Matrix (Fin 24) (Fin 24) ℤ :=
  Matrix.of fun i j => pairingSign i * symmetricTrialityCoefficient k j (oppositeIndex i)

/-- The entries of the triality product's structure matrices. -/
@[simp]
theorem trialityProductMatrix_apply (k i j : Fin 24) :
    trialityProductMatrix k i j =
      pairingSign i * symmetricTrialityCoefficient k j (oppositeIndex i) :=
  (rfl)

/-- The triality product is commutative. -/
theorem trialityProductMatrix_apply_comm (k i j : Fin 24) :
    trialityProductMatrix k i j = trialityProductMatrix j i k := by
  rw [trialityProductMatrix_apply, trialityProductMatrix_apply,
    symmetricTrialityCoefficient_swap_left]

/-! The finite checks below are kernel computations on the integral structure constants. The
triality coefficient is unfolded first through `trialityCoefficient_apply`, its computation lemma,
since its body is not exposed outside its defining module. -/

/-- Every nonzero structure constant of the product is homogeneous for the weights. -/
private theorem weight_eq_add_of_trialityProductMatrix_apply_ne_zero :
    ∀ k i j : Fin 24, trialityProductMatrix k i j ≠ 0 →
      d4TripledWeight i = d4TripledWeight k + d4TripledWeight j := by
  simp only [trialityProductMatrix_apply, symmetricTrialityCoefficient,
    blockTrialityCoefficient, trialityCoefficient_apply]
  decide +kernel

/-- **The triality product is homogeneous for the weights**: the coefficient of `eᵢ` in
`e_k * e_j` vanishes unless the weight of `i` is the sum of the weights of `k` and `j`. -/
theorem trialityProductMatrix_apply_eq_zero_of_weight_ne {k i j : Fin 24}
    (h : d4TripledWeight i ≠ d4TripledWeight k + d4TripledWeight j) :
    trialityProductMatrix k i j = 0 :=
  not_not.mp fun hne => h (weight_eq_add_of_trialityProductMatrix_apply_ne_zero k i j hne)

/-- Every structure constant of the triality product is `-1`, `0` or `1`. -/
theorem trialityProductMatrix_apply_eq_neg_one_or_eq_zero_or_eq_one (k i j : Fin 24) :
    trialityProductMatrix k i j = -1 ∨ trialityProductMatrix k i j = 0 ∨
      trialityProductMatrix k i j = 1 := by
  revert k i j
  simp only [trialityProductMatrix_apply, symmetricTrialityCoefficient,
    blockTrialityCoefficient, trialityCoefficient_apply]
  decide +kernel

/-! ## Functions multiplicative along the product

A function `t` on the basis indices is multiplicative along the product when `tᵢ = tₖ tⱼ` whenever
`eᵢ` occurs in `e_k * e_j`. Starting from the four indices `0`, `1`, `8`, `16`, whose weights
`ϖ₁`, `ϖ₂ - ϖ₁`, `ϖ₃`, `ϖ₄` form a basis of the weight lattice, every other index is reached in two
rounds, each new index occurring in a nonzero structure constant together with two indices
already reached. -/

/-- The four basis indices from which multiplicativity along the product propagates. -/
private def seedIndices : Finset (Fin 24) := {0, 1, 8, 16}

/-- The basis indices reached from `seedIndices` in one round. -/
private def firstIndices : Finset (Fin 24) := {0, 1, 3, 4, 8, 10, 11, 12, 13, 16, 18, 19, 20, 21}

private theorem firstIndices_reached : ∀ x ∈ firstIndices, x ∈ seedIndices ∨
    ∃ k ∈ seedIndices, ∃ j ∈ seedIndices, trialityProductMatrix k x j ≠ 0 ∨
      trialityProductMatrix x k j ≠ 0 ∨ trialityProductMatrix k j x ≠ 0 := by
  simp only [trialityProductMatrix_apply, symmetricTrialityCoefficient,
    blockTrialityCoefficient, trialityCoefficient_apply]
  decide +kernel

private theorem all_reached : ∀ x : Fin 24, x ∈ firstIndices ∨
    ∃ k ∈ firstIndices, ∃ j ∈ firstIndices, trialityProductMatrix k x j ≠ 0 ∨
      trialityProductMatrix x k j ≠ 0 ∨ trialityProductMatrix k j x ≠ 0 := by
  simp only [trialityProductMatrix_apply, symmetricTrialityCoefficient,
    blockTrialityCoefficient, trialityCoefficient_apply]
  decide +kernel

/-- **A function multiplicative along the triality product is determined by its values at the
indices `0`, `1`, `8` and `16`.** Here `t` and `u` take values in a commutative group and satisfy
`tᵢ = tₖ tⱼ` and `uᵢ = uₖ uⱼ` whenever the coefficient of `eᵢ` in `e_k * e_j` is nonzero. -/
theorem eq_of_eq_mul_of_trialityProductMatrix_ne_zero {G : Type*} [CommGroup G]
    {t u : Fin 24 → G}
    (ht : ∀ k i j, trialityProductMatrix k i j ≠ 0 → t i = t k * t j)
    (hu : ∀ k i j, trialityProductMatrix k i j ≠ 0 → u i = u k * u j)
    (h₀ : t 0 = u 0) (h₁ : t 1 = u 1) (h₈ : t 8 = u 8) (h₁₆ : t 16 = u 16) : t = u := by
  -- The quotient `t / u` is multiplicative along the product and trivial at the seeds.
  have hd : ∀ k i j, trialityProductMatrix k i j ≠ 0 → t i / u i = t k / u k * (t j / u j) :=
    fun k i j h => by rw [ht k i j h, hu k i j h, div_mul_div_comm]
  have hstep : ∀ S : Finset (Fin 24), (∀ a ∈ S, t a / u a = 1) → ∀ x,
      (∃ k ∈ S, ∃ j ∈ S, trialityProductMatrix k x j ≠ 0 ∨
        trialityProductMatrix x k j ≠ 0 ∨ trialityProductMatrix k j x ≠ 0) →
      t x / u x = 1 := by
    rintro S hS x ⟨k, hk, j, hj, h | h | h⟩
    · rw [hd k x j h, hS k hk, hS j hj, one_mul]
    · have hx := hd x k j h
      rw [hS k hk, hS j hj, mul_one] at hx
      exact hx.symm
    · have hx := hd k j x h
      rw [hS k hk, hS j hj, one_mul] at hx
      exact hx.symm
  have hseed : ∀ a ∈ seedIndices, t a / u a = 1 := by
    simp only [seedIndices, Finset.mem_insert, Finset.mem_singleton]
    rintro a (rfl | rfl | rfl | rfl) <;> simp [h₀, h₁, h₈, h₁₆]
  have hfirst : ∀ a ∈ firstIndices, t a / u a = 1 := fun a ha =>
    (firstIndices_reached a ha).elim (hseed a) (hstep _ hseed a)
  funext a
  exact div_eq_one.mp ((all_reached a).elim (hfirst a) (hstep _ hfirst a))

/-! ## Products with a raising or lowering matrix

A raising or lowering matrix has a single entry `1` in each column on which its simple root acts,
placed at the reflected index. The three lemmas below evaluate the matrix products in the
derivation equation for such a matrix. -/

section Edge

variable {X : Matrix (Fin 24) (Fin 24) ℤ} {p : Fin 24 → Prop} [DecidablePred p]
  {σ : Fin 24 → Fin 24}

private theorem edge_mul_apply (hσ : ∀ a, σ (σ a) = a)
    (hX : ∀ a b, X a b = if p b ∧ a = σ b then 1 else 0) (N : Matrix (Fin 24) (Fin 24) ℤ)
    (a b : Fin 24) : (X * N) a b = if p (σ a) then N (σ a) b else 0 := by
  rw [Matrix.mul_apply, Finset.sum_eq_single (σ a)]
  · simp [hX, hσ]
  · intro l _ hl
    rw [hX]
    split_ifs with h
    · exact absurd (by rw [h.2, hσ]) hl
    · exact zero_mul _
  · simp

private theorem mul_edge_apply (hX : ∀ a b, X a b = if p b ∧ a = σ b then 1 else 0)
    (N : Matrix (Fin 24) (Fin 24) ℤ) (a b : Fin 24) :
    (N * X) a b = if p b then N a (σ b) else 0 := by
  rw [Matrix.mul_apply, Finset.sum_eq_single (σ b)]
  · simp [hX]
  · intro l _ hl
    rw [hX]
    split_ifs with h
    · exact absurd h.2 hl
    · exact mul_zero _
  · simp

private theorem sum_edge_smul_apply
    (hX : ∀ a b, X a b = if p b ∧ a = σ b then 1 else 0) (N : Fin 24 → Matrix (Fin 24) (Fin 24) ℤ)
    (c a b : Fin 24) : (∑ d, X d c • N d) a b = if p c then N (σ c) a b else 0 := by
  rw [Matrix.sum_apply, Finset.sum_eq_single (σ c)]
  · simp [hX]
  · intro d _ hd
    rw [Matrix.smul_apply, hX]
    split_ifs with h
    · exact absurd h.2 hd
    · exact zero_smul _ _
  · simp

/-- Entrywise form of the derivation equation for such a matrix. -/
private theorem edge_derivation (hσ : ∀ a, σ (σ a) = a)
    (hX : ∀ a b, X a b = if p b ∧ a = σ b then 1 else 0)
    (h : ∀ c a b : Fin 24,
      (if p (σ a) then trialityProductMatrix c (σ a) b else 0) =
        (if p b then trialityProductMatrix c a (σ b) else 0) +
          if p c then trialityProductMatrix (σ c) a b else 0)
    (c : Fin 24) :
    X * trialityProductMatrix c =
      ∑ d, X d c • trialityProductMatrix d + trialityProductMatrix c * X := by
  ext a b
  rw [Matrix.add_apply, edge_mul_apply hσ hX, sum_edge_smul_apply hX, mul_edge_apply hX, h,
    add_comm]

/-- Entrywise form of the vanishing of the second-order terms for such a matrix. -/
private theorem edge_secondOrder
    (hX : ∀ a b, X a b = if p b ∧ a = σ b then 1 else 0)
    (h : ∀ c a b : Fin 24, p b → p c → trialityProductMatrix (σ c) a (σ b) = 0) (c : Fin 24) :
    (∑ d, X d c • trialityProductMatrix d) * X = 0 := by
  ext a b
  rw [mul_edge_apply hX, sum_edge_smul_apply hX, Matrix.zero_apply]
  split_ifs with hb hc
  · exact h c a b hb hc
  · rfl
  · rfl

end Edge

/-! ## Invariance under the generators -/

private theorem raising_derivation_apply : ∀ (i : Fin 4) (c a b : Fin 24),
    (if d4TripledWeight (d4TripledReflection i a) i = -1 then
        trialityProductMatrix c (d4TripledReflection i a) b else 0) =
      (if d4TripledWeight b i = -1 then
          trialityProductMatrix c a (d4TripledReflection i b) else 0) +
        if d4TripledWeight c i = -1 then
          trialityProductMatrix (d4TripledReflection i c) a b else 0 := by
  simp only [trialityProductMatrix_apply, symmetricTrialityCoefficient,
    blockTrialityCoefficient, trialityCoefficient_apply]
  decide +kernel

private theorem lowering_derivation_apply : ∀ (i : Fin 4) (c a b : Fin 24),
    (if d4TripledWeight (d4TripledReflection i a) i = 1 then
        trialityProductMatrix c (d4TripledReflection i a) b else 0) =
      (if d4TripledWeight b i = 1 then
          trialityProductMatrix c a (d4TripledReflection i b) else 0) +
        if d4TripledWeight c i = 1 then
          trialityProductMatrix (d4TripledReflection i c) a b else 0 := by
  simp only [trialityProductMatrix_apply, symmetricTrialityCoefficient,
    blockTrialityCoefficient, trialityCoefficient_apply]
  decide +kernel

private theorem raising_secondOrder_apply : ∀ (i : Fin 4) (c a b : Fin 24),
    d4TripledWeight b i = -1 → d4TripledWeight c i = -1 →
      trialityProductMatrix (d4TripledReflection i c) a (d4TripledReflection i b) = 0 := by
  simp only [trialityProductMatrix_apply, symmetricTrialityCoefficient,
    blockTrialityCoefficient, trialityCoefficient_apply]
  decide +kernel

private theorem lowering_secondOrder_apply : ∀ (i : Fin 4) (c a b : Fin 24),
    d4TripledWeight b i = 1 → d4TripledWeight c i = 1 →
      trialityProductMatrix (d4TripledReflection i c) a (d4TripledReflection i b) = 0 := by
  simp only [trialityProductMatrix_apply, symmetricTrialityCoefficient,
    blockTrialityCoefficient, trialityCoefficient_apply]
  decide +kernel

/-- Every numbered root generator matrix is a derivation of the triality product. -/
private theorem rootMatrix_mul_trialityProductMatrix (k : Fin 4 ⊕ Fin 4) (c : Fin 24) :
    rootMatrix k * trialityProductMatrix c =
      ∑ d, rootMatrix k d c • trialityProductMatrix d + trialityProductMatrix c * rootMatrix k := by
  rcases k with i | i
  · rw [rootMatrix_inl]
    exact edge_derivation (d4TripledReflection_apply_apply i) (raisingMatrix_apply i)
      (raising_derivation_apply i) c
  · rw [rootMatrix_inr]
    exact edge_derivation (d4TripledReflection_apply_apply i) (loweringMatrix_apply i)
      (lowering_derivation_apply i) c

/-- The second-order terms of a numbered root generator matrix on the triality product vanish. -/
private theorem sum_smul_trialityProductMatrix_mul_rootMatrix (k : Fin 4 ⊕ Fin 4) (c : Fin 24) :
    (∑ d, rootMatrix k d c • trialityProductMatrix d) * rootMatrix k = 0 := by
  rcases k with i | i
  · rw [rootMatrix_inl]
    exact edge_secondOrder (raisingMatrix_apply i)
      (raising_secondOrder_apply i) c
  · rw [rootMatrix_inr]
    exact edge_secondOrder (loweringMatrix_apply i)
      (lowering_secondOrder_apply i) c

/-- **A numbered root-subgroup point preserves the triality product.** -/
theorem preserves_trialityProductMatrix_rootSubgroupPoints (k : Fin 4 ⊕ Fin 4) (A : Type v)
    [CommRing A] (u : Multiplicative A) :
    ConstantMultiplication.Preserves ℤ 24 trialityProductMatrix
      ((rootSubgroupPoints k A u : Matrix.GeneralLinearGroup (Fin 24) A) :
        Matrix (Fin 24) (Fin 24) A) := by
  have hmap : (rootMatrix k).map (Int.cast : ℤ → A) = (rootMatrix k).map (algebraMap ℤ A) := by
    ext a b
    simp
  have hpoint : ((rootSubgroupPoints k A u : Matrix.GeneralLinearGroup (Fin 24) A) :
      Matrix (Fin 24) (Fin 24) A) =
        1 + Multiplicative.toAdd u • (rootMatrix k).map (Int.cast : ℤ → A) := by
    rcases k with i | i
    · rw [rootMatrix_inl]
      exact coe_rootSubgroupPoints_inl i A u
    · rw [rootMatrix_inr]
      exact coe_rootSubgroupPoints_inr i A u
  rw [hpoint, hmap]
  exact ConstantMultiplication.preserves_one_add_smul trialityProductMatrix
    (rootMatrix_mul_trialityProductMatrix k) (sum_smul_trialityProductMatrix_mul_rootMatrix k) _

/-- **A weight-torus point preserves the triality product**, because the product is homogeneous
for the weights. -/
theorem preserves_trialityProductMatrix_weightTorusPoints (A : Type v) [CommRing A]
    (s : Fin 4 → Aˣ) :
    ConstantMultiplication.Preserves ℤ 24 trialityProductMatrix
      ((weightTorusPoints A s : Matrix.GeneralLinearGroup (Fin 24) A) :
        Matrix (Fin 24) (Fin 24) A) := by
  rw [coe_weightTorusPoints, UniversalEnvelopingAlgebra.kostantTorusMatrix_apply, diagGL_coe,
    ConstantMultiplication.preserves_diagonal_iff]
  intro k i j
  by_cases h : d4TripledWeight i = d4TripledWeight k + d4TripledWeight j
  · rw [h, torusCharacter_add, Units.val_mul]
    ring
  · rw [trialityProductMatrix_apply_eq_zero_of_weight_ne h, map_zero, mul_zero, mul_zero,
      zero_mul]

/-- **The tripled carrier is a closed subgroup scheme of the stabilizer of the triality
product.** The Hopf ideal cutting out the subgroup scheme of `GL₂₄` preserving the product is
contained in the defining ideal of the carrier. -/
theorem constantMultiplicationDefiningHopfIdeal_le_definingIdeal :
    ConstantMultiplication.definingHopfIdeal ℤ 24 trialityProductMatrix ≤ definingIdeal := by
  rw [definingIdeal_def]
  open TauCeti.UniversalEnvelopingAlgebra in
  refine constantMultiplicationDefiningHopfIdeal_le_kostantToralDefiningIdeal_of_generators
    _ _ _ _ _ _ _ _ _ (fun k A _ q => ?_) (fun A _ s => ?_)
  · have h := coe_rootSubgroupPoints k A (AdditiveGroup.gaPointsMulEquiv (R := ℤ) (A := A) q)
    rw [MulEquiv.symm_apply_apply] at h
    rw [← h]
    exact preserves_trialityProductMatrix_rootSubgroupPoints k A _
  · -- The generic criterion states the torus matrix with the `Fintype` instance obtained from
    -- `Finite`; `convert` identifies it with the standard instance on `Fin 4`.
    convert preserves_trialityProductMatrix_weightTorusPoints A s using 2
    rw [coe_weightTorusPoints]
    congr
    exact Subsingleton.elim _ _

/-- **Every point of the tripled carrier preserves the triality product**, over every commutative
ring, including nonreduced ones. -/
theorem preserves_trialityProductMatrix_of_mem_points {A : Type v} [CommRing A]
    {g : Matrix.GeneralLinearGroup (Fin 24) A} (hg : g ∈ points A) :
    ConstantMultiplication.Preserves ℤ 24 trialityProductMatrix
      (g : Matrix (Fin 24) (Fin 24) A) := by
  rw [points_def] at hg
  have hsub := GeneralLinear.hopfIdealPointsSubgroup_le_of_le 24
    constantMultiplicationDefiningHopfIdeal_le_definingIdeal A hg
  rw [GeneralLinear.mem_hopfIdealPointsSubgroup_iff] at hsub
  have hmem : (GeneralLinear.pointsMulEquiv (R := ℤ) 24).symm g ∈
      CommHopfAlgCat.quotientPointsSubgroup (GeneralLinear.coordinateHopfAlgebra ℤ 24)
        (ConstantMultiplication.definingHopfIdeal ℤ 24 trialityProductMatrix)
        (CommAlgCat.of ℤ A) :=
    (CommHopfAlgCat.mem_quotientPointsSubgroup_iff _ _ _ _).mpr hsub
  rwa [ConstantMultiplication.mem_definingPointsSubgroup_iff, MulEquiv.apply_symm_apply] at hmem

end TauCeti.D4Tripled
