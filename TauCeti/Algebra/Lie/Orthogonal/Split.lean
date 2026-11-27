/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.CartanInvolution.RestrictedRoot.Split
public import TauCeti.Algebra.Lie.Orthogonal.Cartan

/-!
# `𝔰𝔬(n, n)` and `𝔰𝔬(n, n + 1)` are split

On `𝔰𝔬(p, q) = LieAlgebra.Orthogonal.so' p q ℝ`, skew-adjoint for `diag(1_p, -1_q)`, with the
Cartan involution `θ X = -Xᵀ`, let `e : p → q` be injective and put
`H_i = E_(i, e i) + E_(e i, i)` for `i ∈ p` (`LieAlgebra.Orthogonal.splitCartanElement`). These
symmetric matrices commute (their `2 × 2` blocks are disjoint), so they span an abelian subspace
`𝔞` of `𝔭` (`LieAlgebra.Orthogonal.splitCartanSubmodule`).

If every index of `q` outside the range of `e` is the only one, that is for `𝔰𝔬(n, n)` and
`𝔰𝔬(n, n + 1)`, an element of `𝔰𝔬(p, q)` commuting with every `H_i` is a combination of the `H_i`
(`LieAlgebra.Orthogonal.eq_sum_smul_splitCartanElement`): commuting with `H_i` forces it to
preserve the block `{i, e i}`, to be symmetric under exchanging `i` and `e i` there, and, being
skew-adjoint, to vanish on the diagonal. So the centralizer `𝔤_0` of `𝔞` is `𝔞`, `𝔞` is maximal
abelian in `𝔭`, `𝔪 = 0`, and `𝔞` is a Cartan subalgebra: **`𝔰𝔬(n, n)` and `𝔰𝔬(n, n + 1)` are
split** (`LieAlgebra.Orthogonal.isCartanSubalgebra_splitCartanSubalgebra`, with the two cases
`isCartanSubalgebra_splitCartanSubalgebra_so_n_n` and
`isCartanSubalgebra_splitCartanSubalgebra_so_n_succ`). With two or more indices outside the range
of `e`, the centralizer also contains a copy of `𝔰𝔬(q - p)` and `𝔞` is not a Cartan subalgebra.

## Main results

* `LieAlgebra.Orthogonal.splitCartanSubmodule_le_cartanP`: `𝔞 ⊆ 𝔭`.
* `LieAlgebra.Orthogonal.restrictedRootSpace_zero_splitCartanSubmodule`: `𝔤_0 = 𝔞`.
* `LieAlgebra.Orthogonal.isMaximalAbelianInP_splitCartanSubmodule`: `𝔞` is maximal abelian in `𝔭`.
* `LieAlgebra.Orthogonal.restrictedRootSpace_zero_inf_fixedSubalgebra_splitCartanSubmodule`:
  `𝔪 = 0`.
* `LieAlgebra.Orthogonal.isCartanSubalgebra_splitCartanSubalgebra`: `𝔞` is a Cartan subalgebra.

## References

* A. W. Knapp, *Lie Groups Beyond an Introduction*, 2nd ed., Chapter VI, §§5–6.
-/

public section

open LieAlgebra Matrix Module Submodule

attribute [local instance 100] LieRing.ofAssociativeRing

namespace LieAlgebra.Orthogonal

variable {p q : Type*} [Fintype p] [Fintype q] [DecidableEq p] [DecidableEq q]

private theorem single_one_mul_apply {n : Type*} [Fintype n] [DecidableEq n] (x y : n)
    (M : Matrix n n ℝ) (a b : n) :
    (single x y (1 : ℝ) * M) a b = if a = x then M y b else 0 := by
  split_ifs with h
  · subst h
    simp [single_mul_apply_same]
  · exact single_mul_apply_of_ne (h := h) ..

private theorem mul_single_one_apply {n : Type*} [Fintype n] [DecidableEq n] (x y : n)
    (M : Matrix n n ℝ) (a b : n) :
    (M * single x y (1 : ℝ)) a b = if b = y then M a x else 0 := by
  split_ifs with h
  · subst h
    simp [mul_single_apply_same]
  · exact mul_single_apply_of_ne (hbj := h) ..

variable (e : p → q)

/-- The matrix `H_i = E_(i, e i) + E_(e i, i)`. -/
private def splitCartanMatrix (i : p) : Matrix (p ⊕ q) (p ⊕ q) ℝ :=
  single (.inl i) (.inr (e i)) 1 + single (.inr (e i)) (.inl i) 1

omit [Fintype p] [Fintype q] in
private theorem splitCartanMatrix_apply (i : p) (a b : p ⊕ q) :
    splitCartanMatrix e i a b =
      (if a = .inl i ∧ b = .inr (e i) then 1 else 0) +
        if a = .inr (e i) ∧ b = .inl i then 1 else 0 := by
  simp only [splitCartanMatrix, Matrix.add_apply, single_apply]
  congr 1 <;> grind

private theorem splitCartanMatrix_mem (i : p) : splitCartanMatrix e i ∈ so' p q ℝ := by
  rw [mem_so'_iff_forall]
  intro a b
  simp only [splitCartanMatrix_apply, indefiniteDiagonal, diagonal_apply_eq]
  rcases a with a | a <;> rcases b with b | b <;> simp <;> grind

/-- The element `H_i = E_(i, e i) + E_(e i, i)` of `𝔰𝔬(p, q)`. -/
def splitCartanElement (i : p) : so' p q ℝ :=
  ⟨splitCartanMatrix e i, splitCartanMatrix_mem e i⟩

/-- The span `𝔞` of the `H_i = E_(i, e i) + E_(e i, i)`. -/
def splitCartanSubmodule : Submodule ℝ (so' p q ℝ) :=
  span ℝ (Set.range (splitCartanElement e))

variable {e}

private theorem coe_splitCartanElement (i : p) :
    (splitCartanElement e i : Matrix (p ⊕ q) (p ⊕ q) ℝ) = splitCartanMatrix e i :=
  rfl

variable (e) in
/-- `𝔞` lies in the `-1`-eigenspace `𝔭` of `θ X = -Xᵀ`: the `H_i` are symmetric. -/
theorem splitCartanSubmodule_le_cartanP :
    splitCartanSubmodule e ≤ ((so' p q ℝ).restrictNegConjTranspose
      fun _ ↦ conjTranspose_mem_so').cartanP := by
  refine span_le.mpr ?_
  rintro _ ⟨i, rfl⟩
  rw [SetLike.mem_coe, LieSubalgebra.mem_cartanP_restrictNegConjTranspose_iff,
    conjTranspose_eq_transpose_of_trivial, coe_splitCartanElement, splitCartanMatrix,
    transpose_add, transpose_single, transpose_single, add_comm]

/-- The commutation of `X` with `H_i`, entrywise. -/
private theorem splitCartanMatrix_mul_apply (i : p) (X : Matrix (p ⊕ q) (p ⊕ q) ℝ)
    (a b : p ⊕ q) :
    (splitCartanMatrix e i * X) a b =
      (if a = .inl i then X (.inr (e i)) b else 0) + if a = .inr (e i) then X (.inl i) b else 0 :=
  by rw [splitCartanMatrix, add_mul, Matrix.add_apply, single_one_mul_apply, single_one_mul_apply]

private theorem mul_splitCartanMatrix_apply (i : p) (X : Matrix (p ⊕ q) (p ⊕ q) ℝ)
    (a b : p ⊕ q) :
    (X * splitCartanMatrix e i) a b =
      (if b = .inr (e i) then X a (.inl i) else 0) + if b = .inl i then X a (.inr (e i)) else 0 :=
  by rw [splitCartanMatrix, mul_add, Matrix.add_apply, mul_single_one_apply, mul_single_one_apply]

/-- The `H_i` commute. -/
theorem lie_splitCartanElement_splitCartanElement (he : Function.Injective e) (i j : p) :
    ⁅splitCartanElement e i, splitCartanElement e j⁆ = 0 := by
  refine Subtype.ext (Matrix.ext fun a b ↦ ?_)
  rw [LieSubalgebra.coe_bracket, Ring.lie_def, coe_splitCartanElement, coe_splitCartanElement,
    ZeroMemClass.coe_zero, Matrix.zero_apply, Matrix.sub_apply, splitCartanMatrix_mul_apply,
    mul_splitCartanMatrix_apply, sub_eq_zero]
  simp only [splitCartanMatrix_apply]
  rcases a with a | a <;> rcases b with b | b <;> simp [he.eq_iff] <;> grind

/-- `𝔞` is abelian. -/
theorem lie_eq_zero_of_mem_splitCartanSubmodule (he : Function.Injective e) {x y : so' p q ℝ}
    (hx : x ∈ splitCartanSubmodule e) (hy : y ∈ splitCartanSubmodule e) : ⁅x, y⁆ = 0 := by
  induction hx using span_induction with
  | mem x hx =>
    obtain ⟨i, rfl⟩ := hx
    induction hy using span_induction with
    | mem y hy =>
      obtain ⟨j, rfl⟩ := hy
      exact lie_splitCartanElement_splitCartanElement he i j
    | zero => exact lie_zero _
    | add y z _ _ hy hz => rw [lie_add, hy, hz, add_zero]
    | smul c y _ hy => rw [lie_smul, hy, smul_zero]
  | zero => exact zero_lie _
  | add x z _ _ hx hz => rw [add_lie, hx, hz, add_zero]
  | smul c x _ hx => rw [smul_lie, hx, smul_zero]

/-- The diagonal entries of an element of `𝔰𝔬(p, q)` vanish. -/
private theorem diag_eq_zero_of_mem_so' {X : Matrix (p ⊕ q) (p ⊕ q) ℝ} (hX : X ∈ so' p q ℝ)
    (a : p ⊕ q) : X a a = 0 := by
  have h := (mem_so'_iff_forall X).mp hX a a
  rcases a with a | a <;> simp [indefiniteDiagonal] at h <;> linarith

/-- The off-diagonal symmetry of `𝔰𝔬(p, q)`: the `(e, i)` entry is the `(i, e)` entry. -/
private theorem apply_inr_inl_of_mem_so' {X : Matrix (p ⊕ q) (p ⊕ q) ℝ} (hX : X ∈ so' p q ℝ)
    (i : p) (j : q) : X (.inr j) (.inl i) = X (.inl i) (.inr j) := by
  have h := (mem_so'_iff_forall X).mp hX (.inl i) (.inr j)
  simpa [indefiniteDiagonal] using h

/-- Skew-symmetry of the diagonal blocks of `𝔰𝔬(p, q)`. -/
private theorem apply_inr_inr_of_mem_so' {X : Matrix (p ⊕ q) (p ⊕ q) ℝ} (hX : X ∈ so' p q ℝ)
    (j j' : q) : X (.inr j') (.inr j) = -X (.inr j) (.inr j') := by
  have h := (mem_so'_iff_forall X).mp hX (.inr j) (.inr j')
  simp [indefiniteDiagonal] at h
  linarith

/-- The entries of an element `M` of `𝔰𝔬(p, q)` commuting with every `H_i` vanish outside the
`(i, e i)` and `(e i, i)` positions, when at most one index of `q` lies outside the range of
`e`. -/
private theorem entries_eq_zero_of_commute
    (hc : ∀ j j', j ∉ Set.range e → j' ∉ Set.range e → j = j')
    {M : Matrix (p ⊕ q) (p ⊕ q) ℝ} (hM : M ∈ so' p q ℝ)
    (hcomm : ∀ i a b, (splitCartanMatrix e i * M) a b = (M * splitCartanMatrix e i) a b) :
    (∀ j j', M (.inr j) (.inr j') = 0) ∧ (∀ i i', M (.inl i) (.inl i') = 0) ∧
      ∀ i j, j ≠ e i → M (.inl i) (.inr j) = 0 := by
  -- the entries of `M` in rows of a block `{i, e i}` and columns outside it vanish
  have hrow (i : p) (b : p ⊕ q) (hb1 : b ≠ .inl i) (hb2 : b ≠ .inr (e i)) :
      M (.inr (e i)) b = 0 ∧ M (.inl i) b = 0 := by
    have h1 := hcomm i (.inl i) b
    have h2 := hcomm i (.inr (e i)) b
    rw [splitCartanMatrix_mul_apply, mul_splitCartanMatrix_apply] at h1 h2
    exact ⟨by simpa [hb1, hb2] using h1, by simpa [hb1, hb2] using h2⟩
  have hinr (j j' : q) : M (.inr j) (.inr j') = 0 := by
    by_cases hj : j ∈ Set.range e
    · obtain ⟨i, rfl⟩ := hj
      by_cases hj' : j' = e i
      · rw [hj']
        exact diag_eq_zero_of_mem_so' hM _
      · exact (hrow i (.inr j') Sum.inr_ne_inl (by simpa using hj')).1
    by_cases hj' : j' ∈ Set.range e
    · obtain ⟨i, rfl⟩ := hj'
      rw [apply_inr_inr_of_mem_so' hM, neg_eq_zero]
      by_cases hji : j = e i
      · rw [hji]
        exact diag_eq_zero_of_mem_so' hM _
      · exact (hrow i (.inr j) Sum.inr_ne_inl (by simpa using hji)).1
    rw [hc j j' hj hj']
    exact diag_eq_zero_of_mem_so' hM _
  have hinl (i i' : p) : M (.inl i) (.inl i') = 0 := by
    by_cases hii : i' = i
    · rw [hii]
      exact diag_eq_zero_of_mem_so' hM _
    · exact (hrow i (.inl i') (by simpa using hii) Sum.inl_ne_inr).2
  have hinlr (i : p) (j : q) (hj : j ≠ e i) : M (.inl i) (.inr j) = 0 :=
    (hrow i (.inr j) Sum.inr_ne_inl (by simpa using hj)).2
  exact ⟨hinr, hinl, hinlr⟩

/-- **The centralizer of the `H_i`.** If `e` is injective and at most one index of `q` lies
outside its range, an element `X` of `𝔰𝔬(p, q)` commuting with every `H_i` is
`∑ᵢ X_(i, e i) H_i`. -/
theorem eq_sum_smul_splitCartanElement (he : Function.Injective e)
    (hc : ∀ j j', j ∉ Set.range e → j' ∉ Set.range e → j = j') {X : so' p q ℝ}
    (hX : ∀ i, ⁅splitCartanElement e i, X⁆ = 0) :
    X = ∑ i, (X : Matrix (p ⊕ q) (p ⊕ q) ℝ) (.inl i) (.inr (e i)) • splitCartanElement e i := by
  obtain ⟨M, hM⟩ := X
  have hcomm (i : p) (a b : p ⊕ q) :
      (splitCartanMatrix e i * M) a b = (M * splitCartanMatrix e i) a b := by
    have := congrArg (fun Y : so' p q ℝ ↦ (Y : Matrix (p ⊕ q) (p ⊕ q) ℝ) a b) (hX i)
    simp only [LieSubalgebra.coe_bracket, Ring.lie_def, coe_splitCartanElement,
      ZeroMemClass.coe_zero, Matrix.zero_apply, Matrix.sub_apply, sub_eq_zero] at this
    exact this
  obtain ⟨hinr, hinl, hinlr⟩ := entries_eq_zero_of_commute hc hM hcomm
  refine Subtype.ext (Matrix.ext fun a b ↦ ?_)
  simp only [AddSubmonoidClass.coe_finsetSum, SetLike.val_smul, Matrix.sum_apply,
    Matrix.smul_apply, coe_splitCartanElement, splitCartanMatrix_apply, smul_eq_mul]
  rcases a with i | j <;> rcases b with i' | j'
  · simp [hinl]
  · by_cases hj : j' = e i
    · subst hj
      rw [Finset.sum_eq_single i (fun k _ hk ↦ by simp [Ne.symm hk])
        (by simp)]
      simp
    · rw [hinlr i j' hj, eq_comm]
      exact Finset.sum_eq_zero fun k _ ↦ by
        by_cases hk : k = i
        · subst hk; simp [hj]
        · simp [Ne.symm hk]
  · rw [apply_inr_inl_of_mem_so' hM]
    by_cases hj : j = e i'
    · subst hj
      rw [Finset.sum_eq_single i' (fun k _ hk ↦ by simp [Ne.symm hk, he.ne (Ne.symm hk)])
        (by simp)]
      simp
    · rw [hinlr i' j hj, eq_comm]
      exact Finset.sum_eq_zero fun k _ ↦ by
        by_cases hk : k = i'
        · subst hk; simp [hj]
        · simp [Ne.symm hk]
  · simp [hinr]

/-- **The centralizer `𝔤_0` of `𝔞` is `𝔞`** when `e` is injective and at most one index of `q`
lies outside its range. -/
theorem restrictedRootSpace_zero_splitCartanSubmodule (he : Function.Injective e)
    (hc : ∀ j j', j ∉ Set.range e → j' ∉ Set.range e → j = j') :
    (splitCartanSubmodule e).restrictedRootSpace 0 = splitCartanSubmodule e := by
  refine le_antisymm (fun X hX ↦ ?_) (Submodule.le_restrictedRootSpace_zero
    fun _ hx _ hy ↦ lie_eq_zero_of_mem_splitCartanSubmodule he hx hy)
  rw [mem_restrictedRootSpace_zero] at hX
  rw [eq_sum_smul_splitCartanElement he hc fun i ↦ hX ⟨_, subset_span ⟨i, rfl⟩⟩]
  exact sum_mem fun i _ ↦ smul_mem _ _ (subset_span ⟨i, rfl⟩)

/-- **`𝔞` is a maximal abelian subspace of `𝔭`** when `e` is injective and at most one index of
`q` lies outside its range. -/
theorem isMaximalAbelianInP_splitCartanSubmodule (he : Function.Injective e)
    (hc : ∀ j j', j ∉ Set.range e → j' ∉ Set.range e → j = j') :
    ((so' p q ℝ).restrictNegConjTranspose fun _ ↦ conjTranspose_mem_so').IsMaximalAbelianInP
      (splitCartanSubmodule e) := by
  refine LieEquiv.isMaximalAbelianInP_iff.mpr ⟨⟨splitCartanSubmodule_le_cartanP e,
    fun _ hx _ hy ↦ lie_eq_zero_of_mem_splitCartanSubmodule he hx hy⟩, fun 𝔟 h𝔟 hle Y hY ↦ ?_⟩
  rw [← restrictedRootSpace_zero_splitCartanSubmodule he hc, mem_restrictedRootSpace_zero]
  exact fun H ↦ h𝔟.2 _ (hle H.property) Y hY

/-- **`𝔪 = 0`** when `e` is injective and at most one index of `q` lies outside its range. -/
theorem restrictedRootSpace_zero_inf_fixedSubalgebra_splitCartanSubmodule
    (he : Function.Injective e) (hc : ∀ j j', j ∉ Set.range e → j' ∉ Set.range e → j = j') :
    (splitCartanSubmodule e).restrictedRootSpace 0 ⊓
      ((so' p q ℝ).restrictNegConjTranspose
        fun _ ↦ conjTranspose_mem_so').toLieHom.fixedSubalgebra.toSubmodule = ⊥ := by
  rw [restrictedRootSpace_zero_splitCartanSubmodule he hc, ← disjoint_iff]
  exact (LieEquiv.isCompl_fixedSubalgebra_cartanP _ two_ne_zero.isUnit
    (LieSubalgebra.restrictNegConjTranspose_involutive _ _)).disjoint.symm.mono_left
      (splitCartanSubmodule_le_cartanP e)

variable (e) in
/-- `𝔞` as a Lie subalgebra of `𝔰𝔬(p, q)`. -/
def splitCartanSubalgebra (he : Function.Injective e) : LieSubalgebra ℝ (so' p q ℝ) :=
  { splitCartanSubmodule e with
    lie_mem' := fun hx hy ↦ by
      rw [lie_eq_zero_of_mem_splitCartanSubmodule he hx hy]
      exact (splitCartanSubmodule e).zero_mem }

/-- The underlying submodule of `splitCartanSubalgebra` is `splitCartanSubmodule`. -/
@[simp]
theorem splitCartanSubalgebra_toSubmodule (he : Function.Injective e) :
    (splitCartanSubalgebra e he).toSubmodule = splitCartanSubmodule e := by
  ext
  simp [splitCartanSubalgebra]

/-- **`𝔰𝔬(p, q)` is split** when `p + q ≥ 3`, `e` is injective and at most one index of `q` lies
outside its range: `𝔞` is a Cartan subalgebra. -/
theorem isCartanSubalgebra_splitCartanSubalgebra
    (hpq : 3 ≤ Fintype.card p + Fintype.card q) (he : Function.Injective e)
    (hc : ∀ j j', j ∉ Set.range e → j' ∉ Set.range e → j = j') :
    (splitCartanSubalgebra e he).IsCartanSubalgebra :=
  (LieEquiv.IsMaximalAbelianInP.isCartanSubalgebra_iff
    (isCartanInvolution_restrictNegConjTranspose_so' hpq)
    (by rw [splitCartanSubalgebra_toSubmodule]
        exact isMaximalAbelianInP_splitCartanSubmodule he hc)).mpr
    (by rw [splitCartanSubalgebra_toSubmodule]
        exact restrictedRootSpace_zero_inf_fixedSubalgebra_splitCartanSubmodule he hc)

/-- **`𝔰𝔬(n, n)` is split** for `n ≥ 2`. -/
theorem isCartanSubalgebra_splitCartanSubalgebra_so_n_n (hp : 2 ≤ Fintype.card p) :
    (splitCartanSubalgebra (id : p → p) Function.injective_id).IsCartanSubalgebra :=
  isCartanSubalgebra_splitCartanSubalgebra (by omega) Function.injective_id
    fun j _ hj ↦ absurd ⟨j, rfl⟩ hj

/-- **`𝔰𝔬(n, n + 1)` is split** for `n ≥ 1`. -/
theorem isCartanSubalgebra_splitCartanSubalgebra_so_n_succ {n : ℕ} (hn : 1 ≤ n) :
    (splitCartanSubalgebra (Fin.castSucc : Fin n → Fin (n + 1))
      (Fin.castSucc_injective n)).IsCartanSubalgebra :=
  isCartanSubalgebra_splitCartanSubalgebra (by simp; omega) (Fin.castSucc_injective n)
    fun j j' hj hj' ↦ by
      rw [Fin.range_castSucc] at hj hj'
      simp only [Set.mem_ofPred_eq, not_lt] at hj hj'
      exact Fin.ext (by have := j.isLt; have := j'.isLt; omega)

end LieAlgebra.Orthogonal
