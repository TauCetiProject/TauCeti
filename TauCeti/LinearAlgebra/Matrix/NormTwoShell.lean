/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Algebra.Order.Group.PosPart
import TauCeti.LinearAlgebra.Matrix.DotProduct
import TauCeti.LinearAlgebra.Matrix.Gram
import TauCeti.LinearAlgebra.Matrix.Symmetric
import TauCeti.LinearAlgebra.Matrix.ToQuadraticForm
import TauCeti.LinearAlgebra.Matrix.ZMatrix
import TauCeti.LinearAlgebra.QuadraticForm.PosDef

/-!
# The norm-two shell of a simply laced Gram matrix

Let `B` be an integer matrix indexed by a finite type `I`, read as the Gram matrix of the lattice
`Q = I → ℤ` with the pairing `⟪a, b⟫ = a ⬝ᵥ B *ᵥ b`. Its **norm-two shell** is the set
`Φ = {a | ⟪a, a⟫ = 2}` (`Matrix.normTwoShell`). When `B` is the Cartan matrix of a simply laced
Dynkin diagram, possibly disconnected, `Q` is the root lattice in simple-root coordinates and `Φ` is
its set of roots; the coordinate vector `Pi.single i 1` is the simple root `αᵢ`.

The file develops the elementary theory of `Φ` in three layers of hypotheses.

* For symmetric `B`, `⟪a + b, a + b⟫ = ⟪a, a⟫ + ⟪b, b⟫ + 2⟪a, b⟫`, so for `a, b ∈ Φ` the sum
  `a + b` lies in `Φ` exactly when `⟪a, b⟫ = -1`, and `a - b` exactly when `⟪a, b⟫ = 1`;
  likewise the reflection `x ↦ x - ⟪x, a⟫ a` in a vector of `Φ` preserves `Φ`.
* For positive definite `B` with even diagonal, every nonzero vector has norm at least two. Two
  vectors of `Φ` then pair to `2` exactly when they are equal and to `-2` exactly when they are
  opposite, and otherwise to `-1`, `0` or `1`. The shell is finite.
* If in addition the off-diagonal entries are nonpositive, as for a simply laced Cartan matrix,
  every vector of `Φ` has coefficients of one sign: writing `a = a⁺ - a⁻` with disjointly
  supported nonnegative parts, `⟪a⁺, a⁻⟫ ≤ 0`, so two nonzero parts would give `⟪a, a⟫ ≥ 4`.
  With diagonal `2`, a nonnegative vector of `Φ` that is not simple pairs to `1` with some simple
  root `αᵢ`, and `a - αᵢ` is again a nonnegative vector of `Φ`, of height one less. This is the
  height induction `Matrix.PosDef.normTwoShell_nonneg_induction`: every positive root is reached
  from a simple root by adding simple roots one at a time without leaving `Φ`.

These are the facts about the root set that the integral Chevalley lattice of a simply laced
diagram is built on: its root vectors are indexed by `Φ`, and its bracket on root vectors is
nonzero exactly in the cases `a + b ∈ Φ` and `a = -b` isolated here.

## Main definitions

* `Matrix.normTwoShell`: the vectors of norm two of an integer Gram matrix.
* `Matrix.normTwoShellCongr`: the bijection of norm-two shells induced by a relabelling of the
  vertices.

## Main results

* `Matrix.IsSymm.add_mem_normTwoShell_iff`: for `a, b ∈ Φ`, `a + b ∈ Φ ↔ ⟪a, b⟫ = -1`.
* `Matrix.PosDef.dotProduct_mulVec_eq_two_iff` and
  `Matrix.PosDef.dotProduct_mulVec_eq_neg_two_iff`: for `a, b ∈ Φ`, `⟪a, b⟫ = 2 ↔ a = b` and
  `⟪a, b⟫ = -2 ↔ a = -b`.
* `Matrix.PosDef.dotProduct_mulVec_le_one` and `Matrix.PosDef.neg_one_le_dotProduct_mulVec`: for
  an even diagonal, two vectors of `Φ` that are neither equal nor opposite pair into `{-1, 0, 1}`.
* `Matrix.PosDef.finite_normTwoShell`: the shell of a positive definite matrix is finite.
* `Matrix.PosDef.nonneg_or_nonpos_of_mem_normTwoShell`: with nonpositive off-diagonal entries,
  every vector of `Φ` is nonnegative or nonpositive.
* `Matrix.PosDef.exists_sub_single_mem_normTwoShell`: a positive root that is not simple has a
  simple root whose subtraction leaves a positive root.
* `Matrix.PosDef.normTwoShell_nonneg_induction`: the height induction principle for positive roots.

## References

* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4--6*, Chapter VI, §1.6 and §4.
* V. G. Kac, *Infinite dimensional Lie algebras*, third edition, Proposition 5.10 and §7.8.
* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, §10.2.
-/

public section

namespace Matrix

open Finset

variable {I : Type*} [Fintype I]

/-- The **norm-two shell** of an integer Gram matrix `B`: the integer vectors `a` with
`a ⬝ᵥ B *ᵥ a = 2`. For the Cartan matrix of a simply laced Dynkin diagram, read in simple-root
coordinates, these are the roots. -/
def normTwoShell (B : Matrix I I ℤ) : Set (I → ℤ) :=
  {a | a ⬝ᵥ B *ᵥ a = 2}

variable {B : Matrix I I ℤ} {a b x : I → ℤ}

theorem mem_normTwoShell : a ∈ B.normTwoShell ↔ a ⬝ᵥ B *ᵥ a = 2 :=
  Iff.rfl

/-- The norm-two shell is symmetric under negation. -/
@[simp]
theorem neg_mem_normTwoShell : -a ∈ B.normTwoShell ↔ a ∈ B.normTwoShell := by
  simp [mem_normTwoShell, mulVec_neg]

/-- A vector of the norm-two shell is nonzero. -/
theorem ne_zero_of_mem_normTwoShell (ha : a ∈ B.normTwoShell) : a ≠ 0 := by
  rintro rfl
  simp [mem_normTwoShell] at ha

/-- A coordinate vector lies in the norm-two shell exactly when the diagonal entry is `2`. -/
@[simp]
theorem single_mem_normTwoShell_iff [DecidableEq I] {i : I} :
    Pi.single i 1 ∈ B.normTwoShell ↔ B i i = 2 := by
  rw [mem_normTwoShell, single_one_dotProduct, mulVec_single_one, col_apply]

/-- A coordinate vector lies in the norm-two shell when the diagonal entry is `2`. -/
theorem single_mem_normTwoShell [DecidableEq I] {i : I} (hi : B i i = 2) :
    Pi.single i 1 ∈ B.normTwoShell :=
  single_mem_normTwoShell_iff.mpr hi

/-! ### Symmetric Gram matrices -/

namespace IsSymm

/-- **The sum of two vectors of the norm-two shell lies in it exactly when they pair to `-1`.** -/
theorem add_mem_normTwoShell_iff (hB : B.IsSymm) (ha : a ∈ B.normTwoShell)
    (hb : b ∈ B.normTwoShell) : a + b ∈ B.normTwoShell ↔ a ⬝ᵥ B *ᵥ b = -1 := by
  rw [mem_normTwoShell, hB.add_dotProduct_mulVec_add, ha.out, hb.out]
  omega

/-- The difference of two vectors of the norm-two shell lies in it exactly when they pair to
`1`. -/
theorem sub_mem_normTwoShell_iff (hB : B.IsSymm) (ha : a ∈ B.normTwoShell)
    (hb : b ∈ B.normTwoShell) : a - b ∈ B.normTwoShell ↔ a ⬝ᵥ B *ᵥ b = 1 := by
  rw [mem_normTwoShell, hB.sub_dotProduct_mulVec_sub, ha.out, hb.out]
  omega

/-- The reflection in a vector of the norm-two shell maps the shell to itself. -/
theorem sub_smul_mem_normTwoShell (hB : B.IsSymm) (ha : a ∈ B.normTwoShell)
    (hx : x ∈ B.normTwoShell) : x - (x ⬝ᵥ B *ᵥ a) • a ∈ B.normTwoShell := by
  have h := TauCeti.reflect_vecMul_dotProduct_self hB (u := a)
    (by rw [← dotProduct_mulVec]; exact ha) x
  simp only [← dotProduct_mulVec] at h
  rw [mem_normTwoShell, h]
  exact hx

end IsSymm

/-! ### Positive definite Gram matrices -/

namespace PosDef

/-- **For an even diagonal, every nonzero vector has norm at least two.** -/
theorem two_le_dotProduct_mulVec_self (hB : B.PosDef) (hev : ∀ i, Even (B i i)) (ha : a ≠ 0) :
    2 ≤ a ⬝ᵥ B *ᵥ a := by
  have heven : Even (a ⬝ᵥ B *ᵥ a) :=
    (hB.isHermitian.isSymm.even_sum_mul_diag_iff_even_dotProduct_mulVec a).1
      (Finset.even_sum _ fun i _ ↦ (hev i).mul_left (a i))
  have hpos : 0 < a ⬝ᵥ B *ᵥ a := by simpa using hB.dotProduct_mulVec_pos ha
  obtain ⟨k, hk⟩ := heven
  omega

/-- **Two vectors of the norm-two shell pair to `2` exactly when they are equal.** -/
theorem dotProduct_mulVec_eq_two_iff (hB : B.PosDef) (ha : a ∈ B.normTwoShell)
    (hb : b ∈ B.normTwoShell) : a ⬝ᵥ B *ᵥ b = 2 ↔ a = b := by
  refine ⟨fun h ↦ ?_, fun h ↦ h ▸ ha⟩
  by_contra hne
  have hpos : 0 < (a - b) ⬝ᵥ B *ᵥ (a - b) := by
    simpa using hB.dotProduct_mulVec_pos (sub_ne_zero.mpr hne)
  rw [hB.isHermitian.isSymm.sub_dotProduct_mulVec_sub, ha.out, hb.out, h] at hpos
  omega

/-- **Two vectors of the norm-two shell pair to `-2` exactly when they are opposite.** -/
theorem dotProduct_mulVec_eq_neg_two_iff (hB : B.PosDef) (ha : a ∈ B.normTwoShell)
    (hb : b ∈ B.normTwoShell) : a ⬝ᵥ B *ᵥ b = -2 ↔ a = -b := by
  have h := hB.dotProduct_mulVec_eq_two_iff ha (neg_mem_normTwoShell.mpr hb)
  rw [mulVec_neg, dotProduct_neg, neg_eq_iff_eq_neg] at h
  exact h

/-- For an even diagonal, two distinct vectors of the norm-two shell pair to at most `1`. -/
theorem dotProduct_mulVec_le_one (hB : B.PosDef) (hev : ∀ i, Even (B i i))
    (ha : a ∈ B.normTwoShell) (hb : b ∈ B.normTwoShell) (hab : a ≠ b) : a ⬝ᵥ B *ᵥ b ≤ 1 := by
  have h := hB.two_le_dotProduct_mulVec_self hev (sub_ne_zero.mpr hab)
  rw [hB.isHermitian.isSymm.sub_dotProduct_mulVec_sub, ha.out, hb.out] at h
  omega

/-- For an even diagonal, two non-opposite vectors of the norm-two shell pair to at least
`-1`. -/
theorem neg_one_le_dotProduct_mulVec (hB : B.PosDef) (hev : ∀ i, Even (B i i))
    (ha : a ∈ B.normTwoShell) (hb : b ∈ B.normTwoShell) (hab : a ≠ -b) :
    -1 ≤ a ⬝ᵥ B *ᵥ b := by
  have h := hB.dotProduct_mulVec_le_one hev ha (neg_mem_normTwoShell.mpr hb) hab
  rw [mulVec_neg, dotProduct_neg] at h
  omega

/-- **The norm-two shell of a positive definite integer matrix is finite.** -/
theorem finite_normTwoShell (hB : B.PosDef) : B.normTwoShell.Finite := by
  classical
  refine (hB.toQuadraticForm'.finite_setOf_apply_eq 2).subset fun a ha ↦ ?_
  rw [Set.mem_ofPred_eq, toQuadraticForm'_apply]
  exact ha

/-! ### Nonpositive off-diagonal entries -/

/-- **Every vector of the norm-two shell has coefficients of one sign**, for a positive definite
Gram matrix with even diagonal and nonpositive off-diagonal entries, such as a simply laced Cartan
matrix. -/
theorem nonneg_or_nonpos_of_mem_normTwoShell (hB : B.PosDef) (hev : ∀ i, Even (B i i))
    (hoff : ∀ i j, i ≠ j → B i j ≤ 0) (ha : a ∈ B.normTwoShell) : 0 ≤ a ∨ a ≤ 0 := by
  by_contra h
  push Not at h
  have hp : a⁺ ≠ 0 := fun h' ↦ h.2 (posPart_eq_zero.mp h')
  have hn : a⁻ ≠ 0 := fun h' ↦ h.1 (negPart_eq_zero.mp h')
  have hpn := posPart_dotProduct_mulVec_negPart_nonpos hoff a
  have h2p := hB.two_le_dotProduct_mulVec_self hev hp
  have h2n := hB.two_le_dotProduct_mulVec_self hev hn
  have hnorm := ha.out
  rw [← posPart_sub_negPart a, hB.isHermitian.isSymm.sub_dotProduct_mulVec_sub] at hnorm
  omega

/-- **A positive root that is not simple has a simple root whose subtraction leaves a positive
root.** For a positive definite Gram matrix with diagonal `2` and nonpositive off-diagonal entries,
a nonnegative vector `a` of the norm-two shell other than every coordinate vector pairs to `1` with
some coordinate vector `αᵢ`, and `a - αᵢ` is again a nonnegative vector of the shell. -/
theorem exists_sub_single_mem_normTwoShell [DecidableEq I] (hB : B.PosDef)
    (hdiag : ∀ i, B i i = 2) (hoff : ∀ i j, i ≠ j → B i j ≤ 0) (ha : a ∈ B.normTwoShell)
    (hpos : 0 ≤ a) (hsimple : ∀ i, a ≠ Pi.single i 1) :
    ∃ i, a ⬝ᵥ B *ᵥ Pi.single i 1 = 1 ∧ a - Pi.single i 1 ∈ B.normTwoShell ∧
      0 ≤ a - Pi.single i 1 := by
  have hev : ∀ i, Even (B i i) := fun i ↦ ⟨1, by rw [hdiag i]; rfl⟩
  -- Some coordinate is positive and pairs positively with `a`, since `⟪a, a⟫ = 2 > 0`.
  obtain ⟨i, hai, hpair⟩ : ∃ i, 0 < a i ∧ 0 < a ⬝ᵥ B *ᵥ Pi.single i 1 := by
    by_contra hcon
    push Not at hcon
    have hnorm : a ⬝ᵥ B *ᵥ a ≤ 0 := by
      rw [hB.isHermitian.isSymm.dotProduct_mulVec_comm]
      refine Finset.sum_nonpos fun i _ ↦ ?_
      have hi : (B *ᵥ a) i = a ⬝ᵥ B *ᵥ Pi.single i 1 := by
        rw [hB.isHermitian.isSymm.dotProduct_mulVec_comm, single_one_dotProduct]
      rw [hi]
      rcases (hpos i).lt_or_eq with h | h
      · exact mul_nonpos_of_nonneg_of_nonpos (hpos i) (hcon i h)
      · rw [← h, Pi.zero_apply, zero_mul]
    rw [ha.out] at hnorm
    omega
  have hαi := single_mem_normTwoShell (hdiag i)
  have hone : a ⬝ᵥ B *ᵥ Pi.single i 1 = 1 :=
    le_antisymm (hB.dotProduct_mulVec_le_one hev ha hαi (hsimple i)) hpair
  have hsub := (hB.isHermitian.isSymm.sub_mem_normTwoShell_iff ha hαi).mpr hone
  refine ⟨i, hone, hsub, ?_⟩
  rcases hB.nonneg_or_nonpos_of_mem_normTwoShell hev hoff hsub with h | h
  · exact h
  · -- Otherwise `a ≤ αᵢ ≤ a`, so `a` would be the simple root `αᵢ`.
    refine absurd (le_antisymm (sub_nonpos.mp h) fun j ↦ ?_) (hsimple i)
    rcases eq_or_ne j i with rfl | hji
    · simpa using Int.add_one_le_iff.mpr hai
    · simpa [Pi.single_apply, hji] using hpos j

/-- **Height induction on positive roots.** Let `B` be a positive definite Gram matrix with
diagonal `2` and nonpositive off-diagonal entries, such as the Cartan matrix of a simply laced
Dynkin diagram. A property holding at every simple root `Pi.single i 1`, and passing from a
nonnegative vector `a` of the norm-two shell to `a + Pi.single i 1` whenever the latter is again in
the shell, holds at every nonnegative vector of the shell. -/
@[elab_as_elim]
theorem normTwoShell_nonneg_induction [DecidableEq I] (hB : B.PosDef) (hdiag : ∀ i, B i i = 2)
    (hoff : ∀ i j, i ≠ j → B i j ≤ 0) {motive : (I → ℤ) → Prop}
    (simple : ∀ i, motive (Pi.single i 1))
    (add : ∀ a i, a ∈ B.normTwoShell → 0 ≤ a → a + Pi.single i 1 ∈ B.normTwoShell →
      motive a → motive (a + Pi.single i 1))
    (ha : a ∈ B.normTwoShell) (hpos : 0 ≤ a) : motive a := by
  -- Strong induction on the height `∑ i, a i`.
  induction h : (∑ i, a i).toNat using Nat.strong_induction_on generalizing a with
  | _ n ih =>
    by_cases hsimple : ∃ i, a = Pi.single i 1
    · obtain ⟨i, rfl⟩ := hsimple
      exact simple i
    push Not at hsimple
    obtain ⟨i, -, hsub, hsubpos⟩ :=
      hB.exists_sub_single_mem_normTwoShell hdiag hoff ha hpos hsimple
    have hheight : ∑ j, (a - Pi.single i 1 : I → ℤ) j = ∑ j, a j - 1 := by
      simp [Finset.sum_sub_distrib]
    have hnonneg : 0 ≤ ∑ j, (a - Pi.single i 1 : I → ℤ) j :=
      Finset.sum_nonneg fun j _ ↦ hsubpos j
    have hlt : (∑ j, (a - Pi.single i 1 : I → ℤ) j).toNat < n := by
      rw [← h, hheight]
      omega
    have := add _ i hsub hsubpos (by rwa [sub_add_cancel]) (ih _ hlt hsub hsubpos rfl)
    rwa [sub_add_cancel] at this

end PosDef

section Reindex

variable {J : Type*} [Fintype J] (e : I ≃ J)

/-- A relabelled vector lies in the norm-two shell of the relabelled matrix exactly when the vector
lies in the norm-two shell of the matrix. -/
theorem comp_equiv_symm_mem_normTwoShell_reindex_iff :
    a ∘ e.symm ∈ (B.reindex e e).normTwoShell ↔ a ∈ B.normTwoShell := by
  rw [mem_normTwoShell, mem_normTwoShell, comp_equiv_symm_dotProduct_reindex_mulVec]

variable {e} {B' : Matrix J J ℤ}

/-- **The norm-two shell of a relabelled Gram matrix**: for a relabelling `e : I ≃ J` of the
vertices of `B` with `B.reindex e e = B'`, the bijection `a ↦ a ∘ e.symm` from the norm-two
shell of `B` to that of `B'`. -/
def normTwoShellCongr (he : B.reindex e e = B') : B.normTwoShell ≃ B'.normTwoShell :=
  (e.arrowCongr (Equiv.refl ℤ)).subtypeEquiv fun a => by
    have ha : e.arrowCongr (Equiv.refl ℤ) a = a ∘ e.symm := by
      ext j
      simp
    rw [ha, ← he, comp_equiv_symm_mem_normTwoShell_reindex_iff]

@[simp]
theorem coe_normTwoShellCongr_apply (he : B.reindex e e = B') (a : B.normTwoShell) :
    (normTwoShellCongr he a : J → ℤ) = a ∘ e.symm := by
  ext j
  simp [normTwoShellCongr]

@[simp]
theorem coe_normTwoShellCongr_symm_apply (he : B.reindex e e = B') (b : B'.normTwoShell) :
    ((normTwoShellCongr he).symm b : I → ℤ) = b ∘ e := by
  ext i
  simp [normTwoShellCongr]

end Reindex

end Matrix
