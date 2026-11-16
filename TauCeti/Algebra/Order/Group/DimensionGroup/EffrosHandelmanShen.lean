/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Order.Group.DimensionGroup.SimplicialPresentation
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.GroupWithZero.Action
import Mathlib.Algebra.BigOperators.Pi
import Mathlib.Algebra.Order.Group.Basic
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Int.Interval
import Mathlib.Tactic.Abel

/-!
# The Effros–Handelman–Shen theorem

This file proves the countable Effros–Handelman–Shen theorem: a partially ordered abelian group `G`
is a countable dimension group if and only if it admits a `TauCeti.SimplicialPresentation`, i.e.,
is the sequential positive inductive limit of simplicial groups `Fin (rank n) → ℤ`.

The key step in the forward direction is the finite positive-factorization lemma (also called the
*Triangle Lemma* or *Shen's criterion*): if `G` is unperforated with Riesz interpolation, then any
positive homomorphism `f : (Fin r → ℤ) →+ G` and any element `x` (or finite set of elements) in
`ker f` factor positively through a simplicial group `Fin s → ℤ` in which `x` vanishes. Iterating
this factorization over an enumeration of the positive cone and all bounded kernel elements from
earlier stages constructs a simplicial presentation of any countable dimension group.

## Main results

* `TauCeti.exists_positive_factorization`: the Triangle Lemma for a single kernel element, requiring
  only `IsUnperforated G` and `HasRieszInterpolation G` (no directedness or countability).
* `TauCeti.exists_positive_factorization_finset`: simultaneous positive factorization killing a
  finite subset of the kernel.
* `TauCeti.IsDimensionGroup.nonempty_simplicialPresentation`: every countable dimension group
  admits a simplicial presentation.
* `TauCeti.effros_handelman_shen`: `(IsDimensionGroup G ∧ Countable G) ↔
  Nonempty (SimplicialPresentation G)`.

## References

* E. G. Effros, D. E. Handelman and C.-L. Shen, *Dimension groups and their affine
  representations*, American Journal of Mathematics 102 (1980), 385–407, Lemma 2.1 and
  Theorem 2.2.
* K. R. Goodearl, *Partially ordered abelian groups with interpolation*, Mathematical Surveys and
  Monographs 20, AMS, 1986, Chapter 3, Lemma 3.17 and Theorem 3.18.
* K. R. Goodearl and F. Wehrung, *Representations of distributive semilattices in ideal lattices of
  various algebraic structures*, Algebra Universalis 45 (2001), 71–102, §3, Theorem 3.3.
* M. Rørdam, *Classification of nuclear C⋆-algebras*, Encyclopaedia of Mathematical Sciences
  126, Springer, 2002, §1.4, Theorem 1.4.4.
-/

public section

namespace TauCeti

section SimplicialHelpers

variable {G : Type*} [AddCommGroup G]

/-- Expanding a homomorphism out of `Fin r → ℤ` on the standard basis. -/
private theorem addMonoidHom_fin_apply {r : ℕ} (f : (Fin r → ℤ) →+ G) (v : Fin r → ℤ) :
    f v = ∑ i : Fin r, v i • f (Pi.single i 1) := by
  have hv : v = ∑ i : Fin r, v i • Pi.single i (1 : ℤ) := by
    ext j
    simp [Pi.single_apply]
  conv_lhs => rw [hv]
  simp only [map_sum, map_zsmul]

/-- The additive homomorphism `(Fin r → ℤ) →+ G` sending the `i`-th basis vector to `a i`. -/
private def simplicialHom (r : ℕ) (a : ℕ → G) : (Fin r → ℤ) →+ G where
  toFun v := ∑ i : Fin r, v i • a i
  map_zero' := by simp
  map_add' u v := by simp [add_zsmul, Finset.sum_add_distrib]

private theorem simplicialHom_apply (r : ℕ) (a : ℕ → G) (v : Fin r → ℤ) :
    simplicialHom r a v = ∑ i : Fin r, v i • a i :=
  rfl

private theorem simplicialHom_single (r : ℕ) (a : ℕ → G) (i : Fin r) :
    simplicialHom r a (Pi.single i 1) = a i := by
  simp [simplicialHom_apply, Pi.single_apply]

private theorem simplicialHom_mono [PartialOrder G] [IsOrderedAddMonoid G]
    (r : ℕ) {a : ℕ → G} (ha : ∀ i < r, 0 ≤ a i) : Monotone (simplicialHom r a) := by
  intro u v huv
  rw [simplicialHom_apply, simplicialHom_apply]
  exact Finset.sum_le_sum fun (i : Fin r) _ ↦ zsmul_le_zsmul_left (ha i.1 i.isLt) (huv i)

/-- The positive homomorphism `(Fin r → ℤ) →+ (Fin s → ℤ)` induced by a nonnegative integer
matrix `M`. -/
private def natMatrixHom (r s : ℕ) (M : ℕ → ℕ → ℕ) : (Fin r → ℤ) →+ (Fin s → ℤ) where
  toFun v j := ∑ i : Fin r, (M i j : ℤ) * v i
  map_zero' := by ext j; simp
  map_add' u v := by ext j; simp [mul_add, Finset.sum_add_distrib]

private theorem natMatrixHom_apply (r s : ℕ) (M : ℕ → ℕ → ℕ) (v : Fin r → ℤ) (j : Fin s) :
    natMatrixHom r s M v j = ∑ i : Fin r, (M i j : ℤ) * v i :=
  rfl

private theorem natMatrixHom_mono (r s : ℕ) (M : ℕ → ℕ → ℕ) : Monotone (natMatrixHom r s M) := by
  intro u v huv j
  rw [natMatrixHom_apply, natMatrixHom_apply]
  exact Finset.sum_le_sum fun i _ ↦ Int.mul_le_mul_of_nonneg_left (huv i) (Int.natCast_nonneg _)

end SimplicialHelpers

section TriangleLemma

/-- Maximum absolute value of coordinates of `x : Fin r → ℤ`. -/
private def maxAbs {r : ℕ} (x : Fin r → ℤ) : ℕ :=
  Finset.univ.sup fun i ↦ (x i).natAbs

/-- Number of coordinates of `x : Fin r → ℤ` attaining `maxAbs x`. -/
private def maxAbsCount {r : ℕ} (x : Fin r → ℤ) : ℕ :=
  (Finset.univ.filter fun i ↦ (x i).natAbs = maxAbs x).card

private theorem natAbs_le_maxAbs {r : ℕ} (x : Fin r → ℤ) (i : Fin r) :
    (x i).natAbs ≤ maxAbs x :=
  Finset.le_sup (f := fun i ↦ (x i).natAbs) (Finset.mem_univ i)

private theorem maxAbs_eq_zero_iff {r : ℕ} (x : Fin r → ℤ) : maxAbs x = 0 ↔ x = 0 := by
  constructor
  · intro h
    ext i
    exact Int.natAbs_eq_zero.mp (Nat.eq_zero_of_le_zero (h ▸ natAbs_le_maxAbs x i))
  · rintro rfl
    simp [maxAbs]

private theorem maxAbs_neg {r : ℕ} (x : Fin r → ℤ) : maxAbs (-x) = maxAbs x := by
  simp [maxAbs]

private theorem maxAbsCount_neg {r : ℕ} (x : Fin r → ℤ) : maxAbsCount (-x) = maxAbsCount x := by
  simp [maxAbsCount, maxAbs_neg]

private theorem exists_natAbs_eq_maxAbs {r : ℕ} {x : Fin r → ℤ} (hx : x ≠ 0) :
    ∃ j₀ : Fin r, (x j₀).natAbs = maxAbs x := by
  have hne : (Finset.univ : Finset (Fin r)).Nonempty := by
    by_contra hempty
    rw [Finset.not_nonempty_iff_eq_empty] at hempty
    exact hx (funext fun i ↦ absurd (Finset.mem_univ i) (hempty ▸ Finset.notMem_empty i))
  obtain ⟨j₀, -, hj₀⟩ := Finset.exists_mem_eq_sup Finset.univ hne fun i ↦ (x i).natAbs
  exact ⟨j₀, hj₀.symm⟩

/-- In an unperforated ordered abelian group, if `f x = 0` for a positive map `f : ℤʳ →+ G` and
`x j₀ = -maxAbs x < 0`, then `f (e_{j₀})` is bounded above by the sum of `f (eᵢ)` over the
positive coordinates of `x`. -/
private theorem single_le_sum_pos_of_ker {G : Type*} [AddCommGroup G] [PartialOrder G]
    [IsOrderedAddMonoid G] (hU : IsUnperforated G) {r : ℕ} (f : (Fin r → ℤ) →+ G)
    (hf : Monotone f) {x : Fin r → ℤ} (hx : f x = 0) {j₀ : Fin r}
    (hj₀ : x j₀ = -(maxAbs x : ℤ)) (hM : 0 < maxAbs x) :
    f (Pi.single j₀ 1) ≤
      ∑ i ∈ Finset.univ.filter fun i : Fin r ↦ 0 < x i, f (Pi.single i 1) := by
  classical
  let a : Fin r → G := fun i ↦ f (Pi.single i 1)
  have ha : ∀ i, 0 ≤ a i := fun i ↦ by
    simpa [a] using hf (Pi.single_nonneg.2 zero_le_one : 0 ≤ Pi.single i (1 : ℤ))
  let I : Finset (Fin r) := Finset.univ.filter fun i ↦ 0 < x i
  have hsum : ∑ i ∈ I, x i • a i + ∑ i ∈ Iᶜ, x i • a i = 0 := by
    rw [Finset.sum_add_sum_compl, ← addMonoidHom_fin_apply, hx]
  have hupper : ∑ i ∈ I, x i • a i ≤ maxAbs x • ∑ i ∈ I, a i := by
    rw [Finset.smul_sum]
    refine Finset.sum_le_sum fun i _ ↦ ?_
    have hxi : x i ≤ (maxAbs x : ℤ) :=
      le_trans Int.le_natAbs (Int.ofNat_le.mpr (natAbs_le_maxAbs x i))
    simpa only [natCast_zsmul] using zsmul_le_zsmul_left (ha i) hxi
  have hj₀_mem : j₀ ∈ Iᶜ := by
    simp only [I, Finset.mem_compl, Finset.mem_filter, Finset.mem_univ, true_and, not_lt, hj₀]
    omega
  have hlower : maxAbs x • a j₀ ≤ ∑ i ∈ Iᶜ, (-x i) • a i := by
    have hle := Finset.single_le_sum (f := fun i ↦ (-x i) • a i)
      (fun i hi ↦ by
        simp only [I, Finset.mem_compl, Finset.mem_filter, Finset.mem_univ, true_and, not_lt] at hi
        exact zsmul_nonneg (ha i) (neg_nonneg.mpr hi))
      hj₀_mem
    simpa only [hj₀, neg_neg, natCast_zsmul] using hle
  have hneg : ∑ i ∈ Iᶜ, (-x i) • a i = ∑ i ∈ I, x i • a i := by
    have : ∑ i ∈ Iᶜ, (-x i) • a i = -(∑ i ∈ Iᶜ, x i • a i) := by
      simp [Finset.sum_neg_distrib]
    rw [this, eq_neg_of_add_eq_zero_right hsum, neg_neg]
  have hnsmul : 0 ≤ maxAbs x • (∑ i ∈ I, a i - a j₀) := by
    rw [nsmul_sub, sub_nonneg]
    exact hlower.trans (hneg.trans_le hupper)
  exact sub_nonneg.mp (hU.nonneg_of_nsmul_nonneg hM.ne' hnsmul)

/-- The index type for a single Triangle Lemma reduction step splitting coordinate `j₀`. -/
private abbrev StepIdx {r : ℕ} (x : Fin r → ℤ) (j₀ : Fin r) : Type :=
  {k : Fin r // k ≠ j₀} ⊕ {i : Fin r // 0 < x i}

/-- The first factor `(Fin r → ℤ) →+ (StepIdx x j₀ → ℤ)` of a Triangle Lemma reduction step. -/
private def stepAlpha {r : ℕ} (x : Fin r → ℤ) (j₀ : Fin r) :
    (Fin r → ℤ) →+ (StepIdx x j₀ → ℤ) where
  toFun v t := Sum.elim (fun k ↦ v k.1) (fun i ↦ v i.1 + v j₀) t
  map_zero' := by ext t; cases t <;> simp
  map_add' u v := by ext t; cases t <;> simp [add_add_add_comm]

private theorem stepAlpha_inl {r : ℕ} (x : Fin r → ℤ) (j₀ : Fin r) (v : Fin r → ℤ)
    (k : {k : Fin r // k ≠ j₀}) : stepAlpha x j₀ v (Sum.inl k) = v k.1 :=
  rfl

private theorem stepAlpha_inr {r : ℕ} (x : Fin r → ℤ) (j₀ : Fin r) (v : Fin r → ℤ)
    (i : {i : Fin r // 0 < x i}) : stepAlpha x j₀ v (Sum.inr i) = v i.1 + v j₀ :=
  rfl

private theorem stepAlpha_mono {r : ℕ} (x : Fin r → ℤ) (j₀ : Fin r) :
    Monotone (stepAlpha x j₀) := by
  intro u v huv t
  cases t with
  | inl k => exact huv k.1
  | inr i => exact add_le_add (huv i.1) (huv j₀)

/-- The second factor `(StepIdx x j₀ → ℤ) →+ G` of a Triangle Lemma reduction step. -/
private def stepBeta {G : Type*} [AddCommGroup G] {r : ℕ} (x : Fin r → ℤ) (j₀ : Fin r)
    (a z' : Fin r → G) : (StepIdx x j₀ → ℤ) →+ G where
  toFun w :=
    (∑ k : {k : Fin r // k ≠ j₀}, w (Sum.inl k) • (a k.1 - z' k.1)) +
      ∑ i : {i : Fin r // 0 < x i}, w (Sum.inr i) • z' i.1
  map_zero' := by simp
  map_add' u v := by
    simp only [Pi.add_apply, add_zsmul, Finset.sum_add_distrib]
    abel

private theorem stepBeta_apply {G : Type*} [AddCommGroup G] {r : ℕ} (x : Fin r → ℤ) (j₀ : Fin r)
    (a z' : Fin r → G) (w : StepIdx x j₀ → ℤ) :
    stepBeta x j₀ a z' w =
      (∑ k : {k : Fin r // k ≠ j₀}, w (Sum.inl k) • (a k.1 - z' k.1)) +
        ∑ i : {i : Fin r // 0 < x i}, w (Sum.inr i) • z' i.1 :=
  rfl

private theorem stepBeta_mono {G : Type*} [AddCommGroup G] [PartialOrder G] [IsOrderedAddMonoid G]
    {r : ℕ} (x : Fin r → ℤ) (j₀ : Fin r) {a z' : Fin r → G}
    (hz0 : ∀ i, 0 ≤ z' i) (hza : ∀ i, z' i ≤ a i) : Monotone (stepBeta x j₀ a z') := by
  intro u v huv
  refine add_le_add ?_ ?_
  · exact Finset.sum_le_sum fun k _ ↦
      zsmul_le_zsmul_left (sub_nonneg.mpr (hza k.1)) (huv (Sum.inl k))
  · exact Finset.sum_le_sum fun i _ ↦
      zsmul_le_zsmul_left (hz0 i.1) (huv (Sum.inr i))

/-- Factorization identity `stepBeta ∘ stepAlpha = f` for a Riesz decomposition `z'` of `a j₀`. -/
private theorem stepBeta_comp_stepAlpha {G : Type*} [AddCommGroup G] {r : ℕ}
    (f : (Fin r → ℤ) →+ G) (x : Fin r → ℤ) (j₀ : Fin r) (hj₀_neg : x j₀ < 0) {z' : Fin r → G}
    (hz'_zero : ∀ i, ¬ 0 < x i → z' i = 0)
    (hz'_sum : ∑ i ∈ Finset.univ.filter fun i : Fin r ↦ 0 < x i, z' i = f (Pi.single j₀ 1)) :
    (stepBeta x j₀ (fun i ↦ f (Pi.single i 1)) z').comp (stepAlpha x j₀) = f := by
  classical
  let a : Fin r → G := fun i ↦ f (Pi.single i 1)
  let I : Finset (Fin r) := Finset.univ.filter fun i ↦ 0 < x i
  refine AddMonoidHom.ext fun v ↦ ?_
  simp only [AddMonoidHom.comp_apply, stepBeta_apply, stepAlpha_inl, stepAlpha_inr]
  have hsum1 :
      ∑ k : {k : Fin r // k ≠ j₀}, v k.1 • (a k.1 - z' k.1) =
        (∑ k ∈ Finset.univ.erase j₀, v k • a k) - ∑ k ∈ Finset.univ.erase j₀, v k • z' k := by
    simp_rw [zsmul_sub, Finset.sum_sub_distrib]
    congr 1
    · exact (Finset.sum_subtype (p := fun k ↦ k ≠ j₀) (Finset.univ.erase j₀)
        (fun k ↦ by simp) (fun k ↦ v k • a k)).symm
    · exact (Finset.sum_subtype (p := fun k ↦ k ≠ j₀) (Finset.univ.erase j₀)
        (fun k ↦ by simp) (fun k ↦ v k • z' k)).symm
  have hsum2 :
      ∑ i : {i : Fin r // 0 < x i}, (v i.1 + v j₀) • z' i.1 =
        (∑ i ∈ I, v i • z' i) + v j₀ • ∑ i ∈ I, z' i := by
    simp_rw [add_zsmul, Finset.sum_add_distrib, ← Finset.smul_sum]
    congr 1
    · exact (Finset.sum_subtype (p := fun i ↦ 0 < x i) I (fun i ↦ by simp [I])
        (fun i ↦ v i • z' i)).symm
    · congr 1
      exact (Finset.sum_subtype (p := fun i ↦ 0 < x i) I (fun i ↦ by simp [I]) z').symm
  have hcancel : ∑ k ∈ Finset.univ.erase j₀, v k • z' k = ∑ i ∈ I, v i • z' i := by
    have hsub : I ⊆ Finset.univ.erase j₀ := fun i hi ↦ by
      refine Finset.mem_erase.mpr ⟨?_, Finset.mem_univ i⟩
      rintro rfl
      have : 0 < x i := (Finset.mem_filter.mp hi).2
      omega
    refine (Finset.sum_subset hsub fun k _ hkI ↦ ?_).symm
    have hnotpos : ¬ 0 < x k := fun hpos ↦ hkI (Finset.mem_filter.mpr ⟨Finset.mem_univ k, hpos⟩)
    simp [hz'_zero k hnotpos]
  have huniv : ∑ k : Fin r, v k • a k = (∑ k ∈ Finset.univ.erase j₀, v k • a k) + v j₀ • a j₀ :=
    (Finset.add_sum_erase Finset.univ (fun k ↦ v k • a k) (Finset.mem_univ j₀)).symm.trans
      (add_comm _ _)
  rw [hsum1, hsum2, hz'_sum, hcancel, addMonoidHom_fin_apply f v, huniv]
  abel

/-- Every `inr` coordinate of `stepAlpha x j₀ x` has absolute value strictly smaller than
`maxAbs x`. -/
private theorem stepAlpha_inr_natAbs_lt {r : ℕ} {x : Fin r → ℤ} {j₀ : Fin r}
    (hj₀ : x j₀ = -(maxAbs x : ℤ)) (i : {i : Fin r // 0 < x i}) :
    (stepAlpha x j₀ x (Sum.inr i)).natAbs < maxAbs x := by
  have _ : 0 < x i.1 := i.2
  have hi_le : (x i.1).natAbs ≤ maxAbs x := natAbs_le_maxAbs x i.1
  rw [stepAlpha_inr, hj₀]
  omega

/-- When `maxAbs` does not drop after reindexing `stepAlpha x j₀ x`, the number of coordinates
attaining `maxAbs x` strictly decreases because coordinate `j₀` is removed. -/
private theorem stepAlpha_maxAbsCount_lt {r s : ℕ} {x : Fin r → ℤ} {j₀ : Fin r}
    (hj₀ : x j₀ = -(maxAbs x : ℤ)) (e : StepIdx x j₀ ≃ Fin s)
    (heq : maxAbs (AddEquiv.arrowCongr e (AddEquiv.refl ℤ) (stepAlpha x j₀ x)) = maxAbs x) :
    maxAbsCount (AddEquiv.arrowCongr e (AddEquiv.refl ℤ) (stepAlpha x j₀ x)) < maxAbsCount x := by
  classical
  let y : Fin s → ℤ := AddEquiv.arrowCongr e (AddEquiv.refl ℤ) (stepAlpha x j₀ x)
  let Sy : Finset (Fin s) := Finset.univ.filter fun j ↦ (y j).natAbs = maxAbs x
  let Sx : Finset (Fin r) := Finset.univ.filter fun k ↦ (x k).natAbs = maxAbs x
  let proj : StepIdx x j₀ → Fin r := Sum.elim Subtype.val Subtype.val
  have hcard_le : Sy.card ≤ (Sx.erase j₀).card := by
    refine Finset.card_le_card_of_injOn (fun j ↦ proj (e.symm j)) ?_ ?_
    · intro j hj
      have hjabs : (stepAlpha x j₀ x (e.symm j)).natAbs = maxAbs x :=
        (Finset.mem_filter.mp (Finset.mem_coe.mp hj)).2
      cases ht : e.symm j with
      | inl k =>
        rw [ht, stepAlpha_inl] at hjabs
        simp [ht, proj, Sx, k.2, hjabs]
      | inr i => exact absurd (ht ▸ hjabs) (stepAlpha_inr_natAbs_lt hj₀ i).ne
    · intro j₁ hj₁ j₂ hj₂ hproj
      have h1 : (stepAlpha x j₀ x (e.symm j₁)).natAbs = maxAbs x :=
        (Finset.mem_filter.mp (Finset.mem_coe.mp hj₁)).2
      have h2 : (stepAlpha x j₀ x (e.symm j₂)).natAbs = maxAbs x :=
        (Finset.mem_filter.mp (Finset.mem_coe.mp hj₂)).2
      apply e.symm.injective
      cases ht₁ : e.symm j₁ with
      | inr i => exact absurd (ht₁ ▸ h1) (stepAlpha_inr_natAbs_lt hj₀ i).ne
      | inl k₁ =>
        cases ht₂ : e.symm j₂ with
        | inr i => exact absurd (ht₂ ▸ h2) (stepAlpha_inr_natAbs_lt hj₀ i).ne
        | inl k₂ =>
          simp only [ht₁, ht₂, proj, Sum.elim_inl] at hproj
          exact congrArg Sum.inl (Subtype.ext hproj)
  have hj₀_mem : j₀ ∈ Sx := by simp [Sx, hj₀]
  rw [maxAbsCount, heq]
  exact lt_of_le_of_lt hcard_le (Finset.card_erase_lt_of_mem hj₀_mem)

/-- Reindexing `stepAlpha x j₀ x` along `e : StepIdx x j₀ ≃ Fin s` strictly decreases the pair
`(maxAbs, maxAbsCount)` lexicographically. -/
private theorem stepAlpha_measure_lt {r s : ℕ} {x : Fin r → ℤ} {j₀ : Fin r}
    (hj₀ : x j₀ = -(maxAbs x : ℤ)) (e : StepIdx x j₀ ≃ Fin s) :
    let y : Fin s → ℤ := AddEquiv.arrowCongr e (AddEquiv.refl ℤ) (stepAlpha x j₀ x)
    maxAbs y < maxAbs x ∨ (maxAbs y = maxAbs x ∧ maxAbsCount y < maxAbsCount x) := by
  intro y
  have hmax_le : maxAbs y ≤ maxAbs x := by
    refine Finset.sup_le fun j _ ↦ ?_
    have hy : y j = stepAlpha x j₀ x (e.symm j) := rfl
    rw [hy]
    cases e.symm j with
    | inl k => exact natAbs_le_maxAbs x k.1
    | inr i => exact (stepAlpha_inr_natAbs_lt hj₀ i).le
  rcases lt_or_eq_of_le hmax_le with hlt | heq
  · exact Or.inl hlt
  · exact Or.inr ⟨heq, stepAlpha_maxAbsCount_lt hj₀ e heq⟩

/-- Single reduction step for the Triangle Lemma: given a negative coordinate `j₀` achieving
`maxAbs x > 0`, factor `f = β ∘ α` positively through a simplicial group so that `(maxAbs,
maxAbsCount)` strictly decreases on `α x`. -/
private theorem positive_factorization_step {G : Type*} [AddCommGroup G] [PartialOrder G]
    [IsOrderedAddMonoid G] (hU : IsUnperforated G) (hR : HasRieszInterpolation G) {r : ℕ}
    (f : (Fin r → ℤ) →+ G) (hf : Monotone f) {x : Fin r → ℤ} (hx : f x = 0) {j₀ : Fin r}
    (hj₀ : x j₀ = -(maxAbs x : ℤ)) (hM : 0 < maxAbs x) :
    ∃ (s : ℕ) (α : (Fin r → ℤ) →+ (Fin s → ℤ)) (β : (Fin s → ℤ) →+ G),
      Monotone α ∧ Monotone β ∧ β.comp α = f ∧
        (maxAbs (α x) < maxAbs x ∨
          (maxAbs (α x) = maxAbs x ∧ maxAbsCount (α x) < maxAbsCount x)) := by
  classical
  let a : Fin r → G := fun i ↦ f (Pi.single i 1)
  have ha : ∀ i, 0 ≤ a i := fun i ↦ by
    simpa [a] using hf (Pi.single_nonneg.2 zero_le_one : 0 ≤ Pi.single i (1 : ℤ))
  let I : Finset (Fin r) := Finset.univ.filter fun i ↦ 0 < x i
  have hle : a j₀ ≤ ∑ i ∈ I, a i := single_le_sum_pos_of_ker hU f hf hx hj₀ hM
  obtain ⟨z, hz, hzsum⟩ := hR.exists_decomposition_sum I (fun i _ ↦ ha i) (ha j₀) hle
  let z' : Fin r → G := fun i ↦ if 0 < x i then z i else 0
  have hz'_nonneg : ∀ i, 0 ≤ z' i := fun i ↦ by
    by_cases hi : 0 < x i
    · simpa [z', hi] using (hz i (by simp [I, hi])).1
    · simp [z', hi]
  have hz'_le : ∀ i, z' i ≤ a i := fun i ↦ by
    by_cases hi : 0 < x i
    · simpa [z', hi] using (hz i (by simp [I, hi])).2
    · simpa [z', hi] using ha i
  have hz'_sum : ∑ i ∈ I, z' i = a j₀ := by
    rw [← hzsum]
    exact Finset.sum_congr rfl fun i hi ↦ by simp [z', (Finset.mem_filter.mp hi).2]
  have hcomp₀ := stepBeta_comp_stepAlpha f x j₀ (by omega) (fun i hi ↦ by simp [z', hi]) hz'_sum
  let e : StepIdx x j₀ ≃ Fin (Fintype.card (StepIdx x j₀)) := Fintype.equivFin (StepIdx x j₀)
  let eAdd : (StepIdx x j₀ → ℤ) ≃+ (Fin (Fintype.card (StepIdx x j₀)) → ℤ) :=
    AddEquiv.arrowCongr e (AddEquiv.refl ℤ)
  have heAdd_mono : Monotone eAdd := fun _ _ huv j ↦ huv (e.symm j)
  have heAdd_symm_mono : Monotone eAdd.symm := fun _ _ huv t ↦ huv (e t)
  refine ⟨Fintype.card (StepIdx x j₀), eAdd.toAddMonoidHom.comp (stepAlpha x j₀),
    (stepBeta x j₀ a z').comp eAdd.symm.toAddMonoidHom, heAdd_mono.comp (stepAlpha_mono x j₀),
    (stepBeta_mono x j₀ hz'_nonneg hz'_le).comp heAdd_symm_mono, ?_, ?_⟩
  · refine AddMonoidHom.ext fun v ↦ ?_
    simpa [eAdd] using DFunLike.congr_fun hcomp₀ v
  · exact stepAlpha_measure_lt hj₀ e

/-- Variant of `positive_factorization_step` without assuming the maximizing coordinate is negative
(negating `x` when necessary). -/
private theorem positive_factorization_step_ne_zero {G : Type*} [AddCommGroup G] [PartialOrder G]
    [IsOrderedAddMonoid G] (hU : IsUnperforated G) (hR : HasRieszInterpolation G) {r : ℕ}
    (f : (Fin r → ℤ) →+ G) (hf : Monotone f) {x : Fin r → ℤ} (hx : f x = 0) (hx0 : x ≠ 0) :
    ∃ (s : ℕ) (α : (Fin r → ℤ) →+ (Fin s → ℤ)) (β : (Fin s → ℤ) →+ G),
      Monotone α ∧ Monotone β ∧ β.comp α = f ∧
        (maxAbs (α x) < maxAbs x ∨
          (maxAbs (α x) = maxAbs x ∧ maxAbsCount (α x) < maxAbsCount x)) := by
  have hM : 0 < maxAbs x := Nat.pos_of_ne_zero (mt (maxAbs_eq_zero_iff x).mp hx0)
  obtain ⟨j₀, hj₀⟩ := exists_natAbs_eq_maxAbs hx0
  rcases Int.natAbs_eq (x j₀) with hpos | hneg
  · have hj₀' : (-x) j₀ = -(maxAbs (-x) : ℤ) := by
      rw [Pi.neg_apply, maxAbs_neg, ← hj₀, ← hpos]
    have hM' : 0 < maxAbs (-x) := by simpa only [maxAbs_neg] using hM
    obtain ⟨s, α, β, hα, hβ, hcomp, hlt⟩ :=
      positive_factorization_step hU hR f hf (x := -x) (by simp [hx]) hj₀' hM'
    refine ⟨s, α, β, hα, hβ, hcomp, ?_⟩
    simpa only [map_neg, maxAbs_neg, maxAbsCount_neg] using hlt
  · have hj₀' : x j₀ = -(maxAbs x : ℤ) := by rw [hneg, hj₀]
    exact positive_factorization_step hU hR f hf hx hj₀' hM

/-- **The Triangle Lemma (positive factorization lemma)**: in an unperforated partially ordered
abelian group with Riesz interpolation, any positive homomorphism `f : (Fin r → ℤ) →+ G` and any
`x ∈ ker f` factor through a simplicial group `Fin s → ℤ` via positive homomorphisms `α` and `β`
with `β.comp α = f` and `α x = 0`. Directedness and countability are not needed. -/
theorem exists_positive_factorization {G : Type*} [AddCommGroup G] [PartialOrder G]
    [IsOrderedAddMonoid G] (hU : IsUnperforated G) (hR : HasRieszInterpolation G) {r : ℕ}
    (f : (Fin r → ℤ) →+ G) (hf : Monotone f) {x : Fin r → ℤ} (hx : f x = 0) :
    ∃ (s : ℕ) (α : (Fin r → ℤ) →+ (Fin s → ℤ)) (β : (Fin s → ℤ) →+ G),
      Monotone α ∧ Monotone β ∧ β.comp α = f ∧ α x = 0 := by
  suffices ∀ (M c r : ℕ) (f : (Fin r → ℤ) →+ G), Monotone f →
      ∀ (x : Fin r → ℤ), f x = 0 → maxAbs x = M → maxAbsCount x = c →
        ∃ (s : ℕ) (α : (Fin r → ℤ) →+ (Fin s → ℤ)) (β : (Fin s → ℤ) →+ G),
          Monotone α ∧ Monotone β ∧ β.comp α = f ∧ α x = 0 from
    this (maxAbs x) (maxAbsCount x) r f hf x hx rfl rfl
  intro M
  induction M using Nat.strong_induction_on with
  | ind M ihM =>
    intro c
    induction c using Nat.strong_induction_on with
    | ind c ihc =>
      intro r f hf x hx hM hc
      by_cases hx0 : x = 0
      · exact ⟨r, AddMonoidHom.id _, f, monotone_id, hf, AddMonoidHom.comp_id f, by simp [hx0]⟩
      · obtain ⟨s₁, α₁, β₁, hα₁, hβ₁, hcomp₁, hlt⟩ :=
          positive_factorization_step_ne_zero hU hR f hf hx hx0
        have hx₁ : β₁ (α₁ x) = 0 := by
          simpa [AddMonoidHom.comp_apply, hx] using DFunLike.congr_fun hcomp₁ x
        have htail :
            ∃ (s : ℕ) (α₂ : (Fin s₁ → ℤ) →+ (Fin s → ℤ)) (β : (Fin s → ℤ) →+ G),
              Monotone α₂ ∧ Monotone β ∧ β.comp α₂ = β₁ ∧ α₂ (α₁ x) = 0 := by
          rcases hlt with hltM | ⟨heqM, hltc⟩
          · exact ihM (maxAbs (α₁ x)) (hM ▸ hltM) (maxAbsCount (α₁ x)) s₁ β₁ hβ₁ (α₁ x) hx₁
              rfl rfl
          · exact ihc (maxAbsCount (α₁ x)) (hc ▸ hltc) s₁ β₁ hβ₁ (α₁ x) hx₁ (heqM.trans hM) rfl
        obtain ⟨s, α₂, β, hα₂, hβ, hcomp₂, hα₂x⟩ := htail
        refine ⟨s, α₂.comp α₁, β, hα₂.comp hα₁, hβ, ?_, by simpa using hα₂x⟩
        rw [← AddMonoidHom.comp_assoc, hcomp₂, hcomp₁]

/-- Simultaneous positive factorization killing a finite subset of the kernel of a positive
homomorphism `f : (Fin r → ℤ) →+ G`. -/
theorem exists_positive_factorization_finset {G : Type*} [AddCommGroup G] [PartialOrder G]
    [IsOrderedAddMonoid G] (hU : IsUnperforated G) (hR : HasRieszInterpolation G) {r : ℕ}
    (f : (Fin r → ℤ) →+ G) (hf : Monotone f) (K : Finset (Fin r → ℤ))
    (hK : ∀ x ∈ K, f x = 0) :
    ∃ (s : ℕ) (α : (Fin r → ℤ) →+ (Fin s → ℤ)) (β : (Fin s → ℤ) →+ G),
      Monotone α ∧ Monotone β ∧ β.comp α = f ∧ ∀ x ∈ K, α x = 0 := by
  classical
  suffices ∀ (n r : ℕ) (f : (Fin r → ℤ) →+ G), Monotone f →
      ∀ (K : Finset (Fin r → ℤ)), K.card ≤ n → (∀ x ∈ K, f x = 0) →
        ∃ (s : ℕ) (α : (Fin r → ℤ) →+ (Fin s → ℤ)) (β : (Fin s → ℤ) →+ G),
          Monotone α ∧ Monotone β ∧ β.comp α = f ∧ ∀ x ∈ K, α x = 0 from
    this K.card r f hf K le_rfl hK
  intro n
  induction n with
  | zero =>
    intro r f hf K hcard _
    have hKe : K = ∅ := Finset.card_eq_zero.mp (Nat.eq_zero_of_le_zero hcard)
    exact ⟨r, AddMonoidHom.id _, f, monotone_id, hf, AddMonoidHom.comp_id f, by simp [hKe]⟩
  | succ n ih =>
    intro r f hf K hcard hK
    by_cases hKe : K = ∅
    · exact ⟨r, AddMonoidHom.id _, f, monotone_id, hf, AddMonoidHom.comp_id f, by simp [hKe]⟩
    · obtain ⟨x, hxK⟩ := Finset.nonempty_iff_ne_empty.mpr hKe
      obtain ⟨s₁, α₁, β₁, hα₁, hβ₁, hcomp₁, hα₁x⟩ :=
        exists_positive_factorization hU hR f hf (hK x hxK)
      let K' : Finset (Fin s₁ → ℤ) := (K.erase x).image α₁
      have hK'card : K'.card ≤ n := by
        have h1 : K'.card ≤ (K.erase x).card := Finset.card_image_le
        have h2 : (K.erase x).card = K.card - 1 := Finset.card_erase_of_mem hxK
        omega
      have hK' : ∀ y ∈ K', β₁ y = 0 := by
        intro y hy
        obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hy
        have hfz : f z = 0 := hK z (Finset.mem_of_mem_erase hz)
        simpa [AddMonoidHom.comp_apply, hfz] using DFunLike.congr_fun hcomp₁ z
      obtain ⟨s, α₂, β, hα₂, hβ, hcomp₂, hα₂K⟩ := ih s₁ β₁ hβ₁ K' hK'card hK'
      refine ⟨s, α₂.comp α₁, β, hα₂.comp hα₁, hβ, ?_, ?_⟩
      · rw [← AddMonoidHom.comp_assoc, hcomp₂, hcomp₁]
      · intro y hy
        by_cases hyx : y = x
        · simp [hyx, hα₁x]
        · exact hα₂K (α₁ y) (Finset.mem_image_of_mem α₁ (Finset.mem_erase.mpr ⟨hyx, hy⟩))

end TriangleLemma

section Construction

/-- Non-dependent stage record used to build a simplicial presentation by recursion on `ℕ`. -/
private structure RawStage (G : Type*) where
  rank : ℕ
  gen : ℕ → G
  mat : ℕ → ℕ → ℕ

/-- Bundled witness of a single finite positive factorization step. -/
private structure StageStep (G : Type*) [AddCommGroup G] [PartialOrder G] {r : ℕ}
    (f : (Fin r → ℤ) →+ G) (K : Finset (Fin r → ℤ)) where
  rank : ℕ
  α : (Fin r → ℤ) →+ (Fin rank → ℤ)
  β : (Fin rank → ℤ) →+ G
  α_mono : Monotone α
  β_mono : Monotone β
  comp_eq : β.comp α = f
  kills : ∀ z ∈ K, α z = 0

/-- Choose a `StageStep` via `exists_positive_factorization_finset`. -/
private noncomputable def chooseStageStep {G : Type*} [AddCommGroup G] [PartialOrder G]
    [IsOrderedAddMonoid G] (hU : IsUnperforated G) (hR : HasRieszInterpolation G) {r : ℕ}
    (f : (Fin r → ℤ) →+ G) (hf : Monotone f) (K : Finset (Fin r → ℤ))
    (hK : ∀ z ∈ K, f z = 0) : StageStep G f K :=
  let hex := exists_positive_factorization_finset hU hR f hf K hK
  { rank := hex.choose
    α := hex.choose_spec.choose
    β := hex.choose_spec.choose_spec.choose
    α_mono := hex.choose_spec.choose_spec.choose_spec.1
    β_mono := hex.choose_spec.choose_spec.choose_spec.2.1
    comp_eq := hex.choose_spec.choose_spec.choose_spec.2.2.1
    kills := hex.choose_spec.choose_spec.choose_spec.2.2.2 }

/-- Build the next `RawStage` from a `StageStep` by adjoining a new generator `g`. -/
private def rawStageOfStep {G : Type*} [AddCommGroup G] [PartialOrder G] {r : ℕ}
    {f : (Fin r → ℤ) →+ G} {K : Finset (Fin r → ℤ)}
    (st : StageStep G f K) (g : G) : RawStage G where
  rank := st.rank + 1
  gen j := if hj : j < st.rank then st.β (Pi.single ⟨j, hj⟩ 1) else if j = st.rank then g else 0
  mat i j :=
    if hi : i < r then
      if hj : j < st.rank then (st.α (Pi.single ⟨i, hi⟩ 1) ⟨j, hj⟩).toNat else 0
    else 0

private theorem rawStageOfStep_mat_castSucc {G : Type*} [AddCommGroup G] [PartialOrder G] {r : ℕ}
    {f : (Fin r → ℤ) →+ G} {K : Finset (Fin r → ℤ)} (st : StageStep G f K) (g : G)
    (v : Fin r → ℤ) (j : Fin st.rank) :
    natMatrixHom r (st.rank + 1) (rawStageOfStep st g).mat v j.castSucc = st.α v j := by
  rw [natMatrixHom_apply, addMonoidHom_fin_apply st.α v, Finset.sum_apply]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  have hnonneg : 0 ≤ st.α (Pi.single i 1) j := by
    simpa using st.α_mono (Pi.single_nonneg.2 zero_le_one) j
  simp only [rawStageOfStep, i.isLt, j.isLt, ↓reduceDIte, Fin.val_castSucc, Pi.smul_apply,
    smul_eq_mul, Int.toNat_of_nonneg hnonneg, mul_comm]

private theorem rawStageOfStep_mat_last {G : Type*} [AddCommGroup G] [PartialOrder G] {r : ℕ}
    {f : (Fin r → ℤ) →+ G} {K : Finset (Fin r → ℤ)} (st : StageStep G f K) (g : G)
    (v : Fin r → ℤ) :
    natMatrixHom r (st.rank + 1) (rawStageOfStep st g).mat v (Fin.last st.rank) = 0 := by
  simp [natMatrixHom_apply, rawStageOfStep]

private theorem rawStageOfStep_gen_nonneg {G : Type*} [AddCommGroup G] [PartialOrder G] {r : ℕ}
    {f : (Fin r → ℤ) →+ G} {K : Finset (Fin r → ℤ)} (st : StageStep G f K) {g : G} (hg : 0 ≤ g)
    {j : ℕ} (hj : j < (rawStageOfStep st g).rank) :
    0 ≤ (rawStageOfStep st g).gen j := by
  dsimp only [rawStageOfStep] at hj ⊢
  by_cases hjs : j < st.rank
  · simp only [hjs, ↓reduceDIte]
    have h0 : (0 : Fin st.rank → ℤ) ≤ Pi.single ⟨j, hjs⟩ 1 := Pi.single_nonneg.2 zero_le_one
    simpa using st.β_mono h0
  · have hjeq : j = st.rank := by omega
    simp [hjeq, hg]

private theorem rawStageOfStep_comp {G : Type*} [AddCommGroup G] [PartialOrder G] {r : ℕ}
    {f : (Fin r → ℤ) →+ G} {K : Finset (Fin r → ℤ)} (st : StageStep G f K) (g : G) :
    (simplicialHom (rawStageOfStep st g).rank (rawStageOfStep st g).gen).comp
        (natMatrixHom r (rawStageOfStep st g).rank (rawStageOfStep st g).mat) = f := by
  refine AddMonoidHom.ext fun v ↦ ?_
  have hsum :
      ∑ j : Fin (st.rank + 1),
        natMatrixHom r (st.rank + 1) (rawStageOfStep st g).mat v j •
          (rawStageOfStep st g).gen j =
      ∑ j : Fin st.rank, st.α v j • st.β (Pi.single j 1) := by
    rw [Fin.sum_univ_castSucc, rawStageOfStep_mat_last, zero_zsmul, add_zero]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [rawStageOfStep_mat_castSucc]
    simp [rawStageOfStep, j.isLt]
  exact hsum.trans
    ((addMonoidHom_fin_apply st.β (st.α v)).symm.trans (DFunLike.congr_fun st.comp_eq v))

private theorem rawStageOfStep_hits {G : Type*} [AddCommGroup G] [PartialOrder G] {r : ℕ}
    {f : (Fin r → ℤ) →+ G} {K : Finset (Fin r → ℤ)} (st : StageStep G f K) (g : G) :
    ∃ x : Fin (rawStageOfStep st g).rank → ℤ,
      0 ≤ x ∧ simplicialHom (rawStageOfStep st g).rank (rawStageOfStep st g).gen x = g := by
  refine ⟨(Pi.single (Fin.last st.rank) 1 : Fin (st.rank + 1) → ℤ),
    Pi.single_nonneg.2 zero_le_one, ?_⟩
  exact (simplicialHom_single (st.rank + 1) (rawStageOfStep st g).gen (Fin.last st.rank)).trans
    (by simp [rawStageOfStep])

private theorem rawStageOfStep_kills {G : Type*} [AddCommGroup G] [PartialOrder G] {r : ℕ}
    {f : (Fin r → ℤ) →+ G} {K : Finset (Fin r → ℤ)} (st : StageStep G f K) (g : G)
    {z : Fin r → ℤ} (hz : z ∈ K) :
    natMatrixHom r (rawStageOfStep st g).rank (rawStageOfStep st g).mat z = 0 := by
  ext j
  refine Fin.lastCases ?_ (fun j' ↦ ?_) (j : Fin (st.rank + 1))
  · exact rawStageOfStep_mat_last st g z
  · exact (rawStageOfStep_mat_castSucc st g z j').trans (by rw [st.kills z hz]; rfl)

/-- Extend `v : Fin r → ℤ` by `0` outside `Fin r`. -/
private def extendZero {r : ℕ} (v : Fin r → ℤ) : ℕ → ℤ :=
  fun i ↦ if h : i < r then v ⟨i, h⟩ else 0

/-- Apply a nonnegative matrix `M` of input width `r` to a sequence `v : ℕ → ℤ`. -/
private def evalMat (r : ℕ) (M : ℕ → ℕ → ℕ) (v : ℕ → ℤ) : ℕ → ℤ :=
  fun j ↦ ∑ i ∈ Finset.range r, (M i j : ℤ) * v i

/-- Iterate the raw matrix maps of `S` for `k` steps starting at stage `m`. -/
private def pushRaw {G : Type*} (S : ℕ → RawStage G) (m : ℕ) : ℕ → (ℕ → ℤ) → (ℕ → ℤ)
  | 0, v => v
  | k + 1, v => evalMat (S (m + k)).rank (S (m + k + 1)).mat (pushRaw S m k v)

private theorem pushRaw_congr {G : Type*} {S T : ℕ → RawStage G} {m k : ℕ}
    (h : ∀ j ≤ m + k, S j = T j) (v : ℕ → ℤ) :
    pushRaw S m k v = pushRaw T m k v := by
  induction k with
  | zero => rfl
  | succ k ih =>
    have h₁ : ∀ j ≤ m + k, S j = T j := fun j hj ↦ h j (Nat.le_succ_of_le hj)
    have h₂ : S (m + k) = T (m + k) := h (m + k) (Nat.le_succ (m + k))
    have h₃ : S (m + k + 1) = T (m + k + 1) := h (m + k + 1) le_rfl
    simp only [pushRaw, ih h₁, h₂, h₃]

/-- All `ℕ → ℤ` vectors supported on `{0, ..., r - 1}` with entries in `[-n, n]`. -/
private noncomputable def boundedVecs (r n : ℕ) : Finset (ℕ → ℤ) :=
  open Classical in
  (Fintype.piFinset fun _ : Fin r ↦ Finset.Icc (-(n : ℤ)) (n : ℤ)).image extendZero

private theorem extendZero_mem_boundedVecs {r n : ℕ} (v : Fin r → ℤ)
    (hv : ∀ i, -(n : ℤ) ≤ v i ∧ v i ≤ (n : ℤ)) : extendZero v ∈ boundedVecs r n := by
  classical
  unfold boundedVecs
  refine Finset.mem_image_of_mem extendZero ?_
  rw [Fintype.mem_piFinset]
  intro i
  exact Finset.mem_Icc.mpr (hv i)

/-- The finite set of kernel vectors at stage `n` obtained by pushing forward all bounded vectors
from stages `m ≤ n`. -/
private noncomputable def stageKernelFinset {G : Type*} [AddCommGroup G]
    (S : ℕ → RawStage G) (n : ℕ) : Finset (Fin (S n).rank → ℤ) :=
  open Classical in
  let pushed : Finset (ℕ → ℤ) :=
    (Finset.range (n + 1)).biUnion fun m ↦
      (boundedVecs (S m).rank n).image (pushRaw S m (n - m))
  let restricted : Finset (Fin (S n).rank → ℤ) :=
    pushed.image fun w (j : Fin (S n).rank) ↦ w j
  restricted.filter fun z ↦ simplicialHom (S n).rank (S n).gen z = 0

private theorem mem_stageKernelFinset_ker {G : Type*} [AddCommGroup G]
    {S : ℕ → RawStage G} {n : ℕ} {z : Fin (S n).rank → ℤ}
    (hz : z ∈ stageKernelFinset S n) :
    simplicialHom (S n).rank (S n).gen z = 0 := by
  classical
  unfold stageKernelFinset at hz
  exact (Finset.mem_filter.mp hz).2

private theorem mem_stageKernelFinset_of_pushRaw {G : Type*} [AddCommGroup G]
    {S : ℕ → RawStage G} {m n : ℕ} (hmn : m ≤ n) {w : ℕ → ℤ}
    (hw : w ∈ boundedVecs (S m).rank n) {z : Fin (S n).rank → ℤ}
    (hz_eq : ∀ j : Fin (S n).rank, pushRaw S m (n - m) w j = z j)
    (hz_ker : simplicialHom (S n).rank (S n).gen z = 0) :
    z ∈ stageKernelFinset S n := by
  classical
  unfold stageKernelFinset
  refine Finset.mem_filter.mpr ⟨Finset.mem_image.mpr ?_, hz_ker⟩
  refine ⟨pushRaw S m (n - m) w, Finset.mem_biUnion.mpr ?_, funext hz_eq⟩
  exact ⟨m, Finset.mem_range.mpr (Nat.lt_succ_of_le hmn), Finset.mem_image_of_mem _ hw⟩

/-- Construct stage `n + 1` from the stages `0, ..., n` stored in `S`. -/
private noncomputable def nextRawStage {G : Type*} [AddCommGroup G] [PartialOrder G]
    [IsOrderedAddMonoid G] (hU : IsUnperforated G) (hR : HasRieszInterpolation G)
    (posSeq : ℕ → G) (n : ℕ) (S : ℕ → RawStage G) : RawStage G :=
  open Classical in
  if hgen : ∀ i < (S n).rank, 0 ≤ (S n).gen i then
    rawStageOfStep
      (chooseStageStep hU hR (simplicialHom (S n).rank (S n).gen) (simplicialHom_mono _ hgen)
        (stageKernelFinset S n) (fun _ hz ↦ mem_stageKernelFinset_ker hz))
      (posSeq n)
  else
    ⟨0, fun _ ↦ 0, fun _ _ ↦ 0⟩

/-- Recursive sequence of stage tables `stageSeq n : ℕ → RawStage G`, updated only at `n + 1`. -/
private noncomputable def stageSeq {G : Type*} [AddCommGroup G] [PartialOrder G]
    [IsOrderedAddMonoid G] (hU : IsUnperforated G) (hR : HasRieszInterpolation G)
    (posSeq : ℕ → G) : ℕ → ℕ → RawStage G
  | 0 => fun _ ↦ ⟨0, fun _ ↦ 0, fun _ _ ↦ 0⟩
  | n + 1 =>
    Function.update (stageSeq hU hR posSeq n) (n + 1)
      (nextRawStage hU hR posSeq n (stageSeq hU hR posSeq n))

private theorem stageSeq_eq_self {G : Type*} [AddCommGroup G] [PartialOrder G]
    [IsOrderedAddMonoid G] (hU : IsUnperforated G) (hR : HasRieszInterpolation G)
    (posSeq : ℕ → G) {m n : ℕ} (hmn : m ≤ n) :
    stageSeq hU hR posSeq n m = stageSeq hU hR posSeq m m := by
  induction n, hmn using Nat.le_induction with
  | base => rfl
  | succ n hmn ih =>
    rw [stageSeq, Function.update_of_ne (Nat.ne_of_lt (Nat.lt_succ_of_le hmn)), ih]

private theorem nextRawStage_eq_rawStageOfStep {G : Type*} [AddCommGroup G] [PartialOrder G]
    [IsOrderedAddMonoid G] (hU : IsUnperforated G) (hR : HasRieszInterpolation G)
    (posSeq : ℕ → G) (n : ℕ) (S : ℕ → RawStage G)
    (hgen : ∀ i < (S n).rank, 0 ≤ (S n).gen i) :
    nextRawStage hU hR posSeq n S =
      rawStageOfStep
        (chooseStageStep hU hR (simplicialHom (S n).rank (S n).gen) (simplicialHom_mono _ hgen)
          (stageKernelFinset S n) (fun _ hz ↦ mem_stageKernelFinset_ker hz))
        (posSeq n) := by
  unfold nextRawStage
  exact dite_eq_left hgen

/-- Compatibility between non-dependent `pushRaw` and `bondIter`. -/
private theorem pushRaw_extendZero {G : Type*} (stage : ℕ → RawStage G) (m k : ℕ)
    (y : Fin (stage m).rank → ℤ) (j : Fin (stage (m + k)).rank) :
    pushRaw stage m k (extendZero y) j =
      bondIter (fun n ↦ natMatrixHom (stage n).rank (stage (n + 1)).rank (stage (n + 1)).mat)
        m k y j := by
  induction k with
  | zero =>
    simp [pushRaw, extendZero]
  | succ k ih =>
    simp only [pushRaw, evalMat, bondIter_succ_apply, natMatrixHom_apply]
    rw [← Fin.sum_univ_eq_sum_range]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [ih i]

private theorem toLimit_cast {G : Type*} [AddCommGroup G] {rank : ℕ → ℕ}
    {toLimit : ∀ n, (Fin (rank n) → ℤ) →+ G} {m n : ℕ} (h : m = n) (x : Fin (rank m) → ℤ) :
    toLimit n (h ▸ x) = toLimit m x := by
  subst h
  rfl

/-- Iterated compatibility of `toLimit` with `bondIter` for any compatible sequential system. -/
private theorem toLimit_bondIter_of_comp {G : Type*} [AddCommGroup G] {rank : ℕ → ℕ}
    {bond : ∀ n, (Fin (rank n) → ℤ) →+ (Fin (rank (n + 1)) → ℤ)}
    {toLimit : ∀ n, (Fin (rank n) → ℤ) →+ G}
    (hcomp : ∀ n, (toLimit (n + 1)).comp (bond n) = toLimit n)
    (n k : ℕ) (x : Fin (rank n) → ℤ) :
    toLimit (n + k) (bondIter bond n k x) = toLimit n x := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [bondIter_succ_apply]
    have h1 : toLimit (n + (k + 1)) (bond (n + k) (bondIter bond n k x)) =
        toLimit (n + k) (bondIter bond n k x) :=
      DFunLike.congr_fun (hcomp (n + k)) _
    rw [h1, ih]

/-- In a directed ordered abelian group, exhausting the positive cone of a compatible sequential
system implies exhausting the whole group. -/
private theorem exhausts_of_exhausts_pos {G : Type*} [AddCommGroup G] [PartialOrder G]
    [IsOrderedAddMonoid G] [IsDirectedOrder G] {rank : ℕ → ℕ}
    {bond : ∀ n, (Fin (rank n) → ℤ) →+ (Fin (rank (n + 1)) → ℤ)}
    {toLimit : ∀ n, (Fin (rank n) → ℤ) →+ G}
    (hcomp : ∀ n, (toLimit (n + 1)).comp (bond n) = toLimit n)
    (hpos : ∀ g : G, 0 ≤ g → ∃ n x, 0 ≤ x ∧ toLimit n x = g) (g : G) :
    ∃ n x, toLimit n x = g := by
  obtain ⟨u, hu0, hgu⟩ := exists_ge_ge (0 : G) g
  obtain ⟨n₁, x₁, -, hx₁⟩ := hpos u hu0
  obtain ⟨n₂, x₂, -, hx₂⟩ := hpos (u - g) (sub_nonneg.mpr hgu)
  let N := max n₁ n₂
  have hN₁ : n₁ + (N - n₁) = N := Nat.add_sub_cancel' (le_max_left n₁ n₂)
  have hN₂ : n₂ + (N - n₂) = N := Nat.add_sub_cancel' (le_max_right n₁ n₂)
  refine ⟨N, (hN₁ ▸ bondIter bond n₁ (N - n₁) x₁) - (hN₂ ▸ bondIter bond n₂ (N - n₂) x₂), ?_⟩
  rw [map_sub, toLimit_cast hN₁, toLimit_cast hN₂,
    toLimit_bondIter_of_comp hcomp, toLimit_bondIter_of_comp hcomp, hx₁, hx₂, sub_sub_cancel]

/-- The diagonal sequence of raw stages constructed from `posSeq`. -/
private noncomputable def diagStage {G : Type*} [AddCommGroup G] [PartialOrder G]
    [IsOrderedAddMonoid G] (hU : IsUnperforated G) (hR : HasRieszInterpolation G)
    (posSeq : ℕ → G) (n : ℕ) : RawStage G :=
  stageSeq hU hR posSeq n n

private theorem diagStage_succ {G : Type*} [AddCommGroup G] [PartialOrder G]
    [IsOrderedAddMonoid G] (hU : IsUnperforated G) (hR : HasRieszInterpolation G)
    (posSeq : ℕ → G) (n : ℕ) :
    diagStage hU hR posSeq (n + 1) =
      nextRawStage hU hR posSeq n (stageSeq hU hR posSeq n) := by
  simp [diagStage, stageSeq]

private theorem diagStage_gen_nonneg {G : Type*} [AddCommGroup G] [PartialOrder G]
    [IsOrderedAddMonoid G] (hU : IsUnperforated G) (hR : HasRieszInterpolation G)
    {posSeq : ℕ → G} (hpos : ∀ n, 0 ≤ posSeq n) (n : ℕ) :
    ∀ i < (diagStage hU hR posSeq n).rank, 0 ≤ (diagStage hU hR posSeq n).gen i := by
  induction n with
  | zero =>
    intro i hi
    exact absurd hi (Nat.not_lt_zero i)
  | succ n ih =>
    intro i hi
    rw [diagStage_succ,
      nextRawStage_eq_rawStageOfStep hU hR posSeq n (stageSeq hU hR posSeq n) ih] at hi ⊢
    exact rawStageOfStep_gen_nonneg _ (hpos n) hi

private theorem diagStage_comp {G : Type*} [AddCommGroup G] [PartialOrder G]
    [IsOrderedAddMonoid G] (hU : IsUnperforated G) (hR : HasRieszInterpolation G)
    {posSeq : ℕ → G} (hpos : ∀ n, 0 ≤ posSeq n) (n : ℕ) :
    (simplicialHom (diagStage hU hR posSeq (n + 1)).rank (diagStage hU hR posSeq (n + 1)).gen).comp
        (natMatrixHom (diagStage hU hR posSeq n).rank (diagStage hU hR posSeq (n + 1)).rank
          (diagStage hU hR posSeq (n + 1)).mat) =
      simplicialHom (diagStage hU hR posSeq n).rank (diagStage hU hR posSeq n).gen := by
  have hgen := diagStage_gen_nonneg hU hR hpos n
  rw [diagStage_succ,
    nextRawStage_eq_rawStageOfStep hU hR posSeq n (stageSeq hU hR posSeq n) hgen]
  exact rawStageOfStep_comp _ _

private theorem diagStage_hits {G : Type*} [AddCommGroup G] [PartialOrder G]
    [IsOrderedAddMonoid G] (hU : IsUnperforated G) (hR : HasRieszInterpolation G)
    {posSeq : ℕ → G} (hpos : ∀ n, 0 ≤ posSeq n) (n : ℕ) :
    ∃ x : Fin (diagStage hU hR posSeq (n + 1)).rank → ℤ,
      0 ≤ x ∧
        simplicialHom (diagStage hU hR posSeq (n + 1)).rank
          (diagStage hU hR posSeq (n + 1)).gen x = posSeq n := by
  have hgen := diagStage_gen_nonneg hU hR hpos n
  rw [diagStage_succ,
    nextRawStage_eq_rawStageOfStep hU hR posSeq n (stageSeq hU hR posSeq n) hgen]
  exact rawStageOfStep_hits _ _

private theorem diagStage_kills {G : Type*} [AddCommGroup G] [PartialOrder G]
    [IsOrderedAddMonoid G] (hU : IsUnperforated G) (hR : HasRieszInterpolation G)
    {posSeq : ℕ → G} (hpos : ∀ n, 0 ≤ posSeq n) (n : ℕ)
    (z : Fin (diagStage hU hR posSeq n).rank → ℤ)
    (hz : z ∈ stageKernelFinset (stageSeq hU hR posSeq n) n) :
    natMatrixHom (diagStage hU hR posSeq n).rank (diagStage hU hR posSeq (n + 1)).rank
      (diagStage hU hR posSeq (n + 1)).mat z = 0 := by
  have hgen := diagStage_gen_nonneg hU hR hpos n
  have hT := (diagStage_succ hU hR posSeq n).trans
    (nextRawStage_eq_rawStageOfStep hU hR posSeq n (stageSeq hU hR posSeq n) hgen)
  generalize diagStage hU hR posSeq (n + 1) = T at hT ⊢
  subst hT
  exact rawStageOfStep_kills _ _ hz

private theorem diagStage_eventually_zero {G : Type*} [AddCommGroup G] [PartialOrder G]
    [IsOrderedAddMonoid G] (hU : IsUnperforated G) (hR : HasRieszInterpolation G)
    {posSeq : ℕ → G} (hpos : ∀ n, 0 ≤ posSeq n) (m : ℕ)
    (x : Fin (diagStage hU hR posSeq m).rank → ℤ)
    (hx : simplicialHom (diagStage hU hR posSeq m).rank (diagStage hU hR posSeq m).gen x = 0) :
    ∃ k,
      bondIter (fun n ↦ natMatrixHom (diagStage hU hR posSeq n).rank
        (diagStage hU hR posSeq (n + 1)).rank (diagStage hU hR posSeq (n + 1)).mat) m k x = 0 := by
  let stage := diagStage hU hR posSeq
  let bond : ∀ n, (Fin (stage n).rank → ℤ) →+ (Fin (stage (n + 1)).rank → ℤ) :=
    fun n ↦ natMatrixHom (stage n).rank (stage (n + 1)).rank (stage (n + 1)).mat
  let k := maxAbs x
  let N := m + k
  refine ⟨k + 1, ?_⟩
  rw [bondIter_succ_apply]
  have hmN : m ≤ N := Nat.le_add_right m k
  have hS_eq : ∀ {a b : ℕ}, a ≤ b → stageSeq hU hR posSeq b a = stage a :=
    fun hab ↦ stageSeq_eq_self hU hR posSeq hab
  have hbd : extendZero x ∈ boundedVecs (stageSeq hU hR posSeq N m).rank N := by
    rw [hS_eq hmN]
    refine extendZero_mem_boundedVecs x fun i ↦ ?_
    have hi : (x i).natAbs ≤ k := natAbs_le_maxAbs x i
    omega
  have heq : ∀ j : Fin (stageSeq hU hR posSeq N N).rank,
      pushRaw (stageSeq hU hR posSeq N) m (N - m) (extendZero x) j = bondIter bond m k x j := by
    intro j
    have hcongr : pushRaw (stageSeq hU hR posSeq N) m (N - m) (extendZero x) =
        pushRaw stage m k (extendZero x) := by
      rw [Nat.add_sub_cancel_left m k]
      exact pushRaw_congr (fun t ht ↦ hS_eq ht) (extendZero x)
    rw [hcongr]
    exact pushRaw_extendZero stage m k x j
  have hker : simplicialHom (stageSeq hU hR posSeq N N).rank (stageSeq hU hR posSeq N N).gen
      (bondIter bond m k x) = 0 :=
    (toLimit_bondIter_of_comp (toLimit := fun n ↦ simplicialHom (stage n).rank (stage n).gen)
      (diagStage_comp hU hR hpos) m k x).trans hx
  have hz_mem : bondIter bond m k x ∈ stageKernelFinset (stageSeq hU hR posSeq N) N :=
    mem_stageKernelFinset_of_pushRaw hmN hbd heq hker
  exact diagStage_kills hU hR hpos N _ hz_mem

/-- Every countable dimension group admits a simplicial presentation. -/
theorem IsDimensionGroup.nonempty_simplicialPresentation {G : Type*} [AddCommGroup G]
    [PartialOrder G] [IsOrderedAddMonoid G] (hG : IsDimensionGroup G) [Countable G] :
    Nonempty (SimplicialPresentation G) := by
  have : Nonempty {g : G // 0 ≤ g} := ⟨⟨0, le_rfl⟩⟩
  obtain ⟨enumPos, henumPos⟩ := exists_surjective_nat {g : G // 0 ≤ g}
  let posSeq : ℕ → G := fun n ↦ (enumPos n).1
  have hpos : ∀ n, 0 ≤ posSeq n := fun n ↦ (enumPos n).2
  let hU := hG.isUnperforated
  let hR := hG.hasRieszInterpolation
  have : IsDirectedOrder G := hG.isDirectedOrder
  let stage := diagStage hU hR posSeq
  let bond : ∀ n, (Fin (stage n).rank → ℤ) →+ (Fin (stage (n + 1)).rank → ℤ) :=
    fun n ↦ natMatrixHom (stage n).rank (stage (n + 1)).rank (stage (n + 1)).mat
  let toLimit : ∀ n, (Fin (stage n).rank → ℤ) →+ G :=
    fun n ↦ simplicialHom (stage n).rank (stage n).gen
  have hcomp : ∀ n, (toLimit (n + 1)).comp (bond n) = toLimit n :=
    diagStage_comp hU hR hpos
  have hexhausts_pos : ∀ g : G, 0 ≤ g → ∃ n x, 0 ≤ x ∧ toLimit n x = g := fun g hg ↦ by
    obtain ⟨n, hn⟩ := henumPos ⟨g, hg⟩
    obtain ⟨x, hx0, hxeq⟩ := diagStage_hits hU hR hpos n
    exact ⟨n + 1, x, hx0, hxeq.trans (congrArg Subtype.val hn)⟩
  exact ⟨{
    rank := fun n ↦ (stage n).rank
    bond := bond
    bond_mono := fun n ↦ natMatrixHom_mono _ _ _
    toLimit := toLimit
    toLimit_mono := fun n ↦ simplicialHom_mono _ (diagStage_gen_nonneg hU hR hpos n)
    toLimit_comp_bond := hcomp
    exhausts := exhausts_of_exhausts_pos hcomp hexhausts_pos
    exhausts_pos := hexhausts_pos
    eventually_zero := diagStage_eventually_zero hU hR hpos
  }⟩

/-- **The Effros–Handelman–Shen theorem** (countable form): a partially ordered abelian group is a
countable dimension group if and only if it admits a simplicial presentation, i.e., is the
sequential positive inductive limit of simplicial groups `Fin (rank n) → ℤ`. -/
theorem effros_handelman_shen (G : Type*) [AddCommGroup G] [PartialOrder G]
    [IsOrderedAddMonoid G] :
    (IsDimensionGroup G ∧ Countable G) ↔ Nonempty (SimplicialPresentation G) :=
  ⟨fun ⟨hG, hC⟩ ↦ @IsDimensionGroup.nonempty_simplicialPresentation G _ _ _ hG hC,
    fun ⟨P⟩ ↦ ⟨P.isDimensionGroup, P.countable⟩⟩

end Construction

end TauCeti
