/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.Block

/-!
# Leading minors of matrices permuting blocks

Let `b : n → α` label the blocks of a square matrix, and let `σ` permute their labels.
The support condition `M i j ≠ 0 → b i = σ (b j)` means that `M` carries the block at `a`
into the block at `σ a`. The maps inside these blocks are arbitrary: no permutation of
the individual basis vectors is assumed.

When the block labels are partially ordered and all occur, nonvanishing of every leading
block minor forces `σ = 1`. Consequently, for an invertible matrix over a nontrivial
commutative ring, every leading block minor is a unit exactly when the block permutation
is trivial. This criterion detects which weight-block permutations can occur in the
open set admitting block lower-diagonal-upper factorization.

The version `eqOn_range_of_det_toSquareBlockProp_le_ne_zero` starts with an injective map
on a family of weights rather than a permutation of the block labels. Nonzero leading minors
force the occurring weights to be stable under this map, so it induces a permutation of them.

The weight-space application is the big-cell argument in R. Steinberg, *Lectures on
Chevalley Groups*, Chapter 5, Theorem 7: a Weyl representative permutes weight spaces,
and its leading weight-block minors can all be invertible only if it fixes every weight.
-/

public section

namespace Matrix

variable {n α R : Type*} [Fintype n] [DecidableEq n] [CommRing R]

/-- If a matrix carries each block into the block prescribed by `f`, a principal minor
on a set of blocks vanishes whenever one of its source blocks is carried outside the set. -/
theorem det_toSquareBlockProp_eq_zero_of_block_maps_out
    (M : Matrix n n R) (b : n → α) (f : α → α)
    (hsupport : ∀ i j, b i ≠ f (b j) → M i j = 0)
    (p : α → Prop) [DecidablePred p] (j : n) (hj : p (b j)) (hfj : ¬p (f (b j))) :
    (M.toSquareBlockProp fun i => p (b i)).det = 0 := by
  apply det_eq_zero_of_column_eq_zero ⟨j, hj⟩
  intro i
  exact hsupport i j fun h => hfj (h ▸ i.property)

/-- Nonvanishing of the leading block minors forces a supported block map to send each
occurring label to a label no larger than itself. -/
theorem apply_le_of_det_toSquareBlockProp_le_ne_zero [Preorder α] [DecidableLE α]
    (M : Matrix n n R) (b : n → α) (f : α → α)
    (hsupport : ∀ i j, b i ≠ f (b j) → M i j = 0)
    (hminor : ∀ a, (M.toSquareBlockProp fun i => b i ≤ a).det ≠ 0) (j : n) :
    f (b j) ≤ b j := by
  by_contra hj
  exact hminor (b j) (det_toSquareBlockProp_eq_zero_of_block_maps_out M b f hsupport
    (· ≤ b j) j le_rfl hj)

variable [PartialOrder α] [DecidableLE α]

/-- A permutation of the occurring blocks is trivial if every leading block minor is
nonzero. The blocks may have arbitrary sizes and arbitrary internal matrices. -/
theorem eq_one_of_det_toSquareBlockProp_le_ne_zero
    (M : Matrix n n R) (b : n → α) (hb : Function.Surjective b) (σ : Equiv.Perm α)
    (hsupport : ∀ i j, b i ≠ σ (b j) → M i j = 0)
    (hminor : ∀ a, (M.toSquareBlockProp fun i => b i ≤ a).det ≠ 0) :
    σ = 1 := by
  have : Finite α := Finite.of_surjective b hb
  have hle (a : α) : σ a ≤ a := by
    obtain ⟨j, rfl⟩ := hb a
    exact apply_le_of_det_toSquareBlockProp_le_ne_zero M b σ hsupport hminor j
  ext a
  induction a using WellFoundedLT.induction with
  | ind a ih =>
    rcases (hle a).eq_or_lt with h | h
    · exact h
    · exact σ.injective (ih (σ a) h)

/-- For an invertible matrix permuting a partially ordered family of nonempty blocks,
all leading block minors are units if and only if the block permutation is trivial. -/
theorem isUnit_det_toSquareBlockProp_le_iff_eq_one [Nontrivial R]
    (M : Matrix n n R) (hM : IsUnit M.det) (b : n → α) (hb : Function.Surjective b)
    (σ : Equiv.Perm α) (hsupport : ∀ i j, b i ≠ σ (b j) → M i j = 0) :
    (∀ a, IsUnit (M.toSquareBlockProp fun i => b i ≤ a).det) ↔ σ = 1 := by
  refine ⟨fun h => eq_one_of_det_toSquareBlockProp_le_ne_zero M b hb σ hsupport
    (fun a => (h a).ne_zero), ?_⟩
  rintro rfl a
  have hdet := M.twoBlockTriangular_det (fun i => b i ≤ a) (by
    intro i hi j hj
    exact hsupport i j fun hij => hi (hij ▸ hj))
  rw [hdet] at hM
  exact isUnit_of_mul_isUnit_left hM

/-- A map injective on the occurring weights fixes every occurring weight if all leading
weight-block minors are nonzero and `M i j = 0` whenever `wt i ≠ f (wt j)`. Thus `M` carries
the weight-`μ` block into the weight-`f μ` block. The equivalence `r` supplies an ordering
of the distinct weights, not of the individual basis vectors. -/
theorem eqOn_range_of_det_toSquareBlockProp_le_ne_zero {W : Type*}
    (M : Matrix n n R) (wt : n → W) (f : W → W)
    (hf : Set.InjOn f (Set.range wt)) (r : Set.range wt ≃ α)
    (hsupport : ∀ i j, wt i ≠ f (wt j) → M i j = 0)
    (hminor : ∀ a, (M.toSquareBlockProp fun i => r ⟨wt i, Set.mem_range_self i⟩ ≤ a).det ≠ 0) :
    Set.EqOn f id (Set.range wt) := by
  classical
  have hstable : Set.MapsTo f (Set.range wt) (Set.range wt) := by
    rintro _ ⟨j, rfl⟩
    by_contra h
    exact hminor (r ⟨wt j, Set.mem_range_self j⟩)
      (det_eq_zero_of_column_eq_zero ⟨j, le_rfl⟩ fun i =>
        hsupport i j fun hij => h ⟨i, hij⟩)
  let g : Set.range wt → Set.range wt := fun w => ⟨f w, hstable w.property⟩
  have hg : Function.Injective g := fun x y hxy =>
    Subtype.ext (hf x.property y.property (congrArg Subtype.val hxy))
  let σ : Equiv.Perm α := r.symm.trans
    ((Equiv.ofBijective g ⟨hg, Finite.surjective_of_injective hg⟩).trans r)
  have hσ_apply (w : Set.range wt) : σ (r w) = r (g w) := by
    simp only [σ, Equiv.trans_apply, Equiv.symm_apply_apply]
    rfl
  have hσ : σ = 1 := eq_one_of_det_toSquareBlockProp_le_ne_zero M
    (fun i => r ⟨wt i, Set.mem_range_self i⟩)
    (r.surjective.comp Set.rangeFactorization_surjective) σ (fun i j hij => by
      apply hsupport i j
      intro hw
      apply hij
      rw [hσ_apply]
      exact congrArg r (Subtype.ext hw)) hminor
  intro w hw
  have heq : r (g ⟨w, hw⟩) = r ⟨w, hw⟩ := by
    rw [← hσ_apply, hσ]
    rfl
  exact congrArg Subtype.val (r.injective heq)

/-- For an invertible matrix with `M i j = 0` whenever `wt i ≠ f (wt j)`, where `f` is
injective on the occurring weights, all leading weight-block minors are units exactly when
`f` fixes every occurring weight. The equivalence `r` orders the distinct weights. -/
theorem isUnit_det_toSquareBlockProp_le_iff_eqOn_range [Nontrivial R] {W : Type*}
    (M : Matrix n n R) (hM : IsUnit M.det) (wt : n → W) (f : W → W)
    (hf : Set.InjOn f (Set.range wt)) (r : Set.range wt ≃ α)
    (hsupport : ∀ i j, wt i ≠ f (wt j) → M i j = 0) :
    (∀ a, IsUnit (M.toSquareBlockProp fun i => r ⟨wt i, Set.mem_range_self i⟩ ≤ a).det) ↔
      Set.EqOn f id (Set.range wt) := by
  refine ⟨fun h => eqOn_range_of_det_toSquareBlockProp_le_ne_zero M wt f hf r hsupport
    (fun a => (h a).ne_zero), ?_⟩
  intro hfix
  exact (isUnit_det_toSquareBlockProp_le_iff_eq_one M hM
    (fun i => r ⟨wt i, Set.mem_range_self i⟩)
    (r.surjective.comp Set.rangeFactorization_surjective) 1 (fun i j hij => by
      apply hsupport i j
      rw [hfix (Set.mem_range_self j)]
      exact fun h => hij (congrArg r (Subtype.ext h)))).mpr rfl

end Matrix
