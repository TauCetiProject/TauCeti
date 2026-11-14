/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Stable
import Mathlib.Algebra.Group.Pi.Lemmas

/-!
# The Dieudonné determinant over a division ring

Over a possibly noncommutative division ring `D`, the ordinary polynomial determinant fails to be
multiplicative, because entries do not commute. Dieudonné (1943) showed that passing to the
abelianization `Group.Abelianization Dˣ` of the multiplicative group of units restores a canonical
multiplicative determinant
`Matrix.GeneralLinearGroup.dieudonneDet : GL n D →* Group.Abelianization Dˣ`
that vanishes on elementary matrices and sends a single-coordinate diagonal matrix
`diag(1, …, d, …, 1)` to `Group.Abelianization.of d`.

This file constructs `dieudonneDet` directly over an arbitrary division ring and arbitrary finite
index type, following Artin's inductive Schur-complement presentation on `GL (Fin m) D`:

1. **Bruhat–Gaussian elementary decomposition.** Over a division ring `D`, every invertible matrix
   on a nonempty finite index type `n` factors as `e * diagGL (Pi.mulSingle i d)` with
   `e ∈ TauCeti.elementarySubgroup n D` and `d : Dˣ`
   (`TauCeti.exists_mem_elementarySubgroup_mul_diagGL_mulSingle`).
2. **Artin's Schur-complement induction.** For `A : GL (Fin (m + 1)) D` and any row `r` with
   `A r 0 ≠ 0`, eliminating the first column except at `(r, 0)` produces an invertible `m × m`
   Schur complement `B_r`. Weighting the inductive invariant of `B_r` by
   `Group.Abelianization.of (-1 : Dˣ) ^ (r : ℕ) * Group.Abelianization.of (Units.mk0 (A r 0) hr)`
   gives a value independent of the chosen pivot row `r`, invariant under left multiplication by
   elementary matrices, and equivariant under left multiplication by single-coordinate diagonal
   matrices.
3. **Multiplicativity, uniqueness, and exact kernel.** Combining the elementary-diagonal
   factorization with the Artin axioms yields multiplicativity, uniqueness among homomorphisms
   vanishing on `E n D` with prescribed single-coordinate diagonal values, naturality under index
   equivalences, block sums, stabilization, and division-ring homomorphisms, surjectivity for
   nonempty `n`, and the exact kernel theorem `ker dieudonneDet = TauCeti.elementarySubgroup n D`
   whenever `n` has at least two elements (`[Nontrivial n]`).

Consequently, when `n` is nontrivial, `TauCeti.elementarySubgroup n D` is normal in `GL n D` with
quotient canonically isomorphic to `Group.Abelianization Dˣ`; when `3 ≤ Fintype.card n`, it equals
the commutator subgroup `commutator (GL n D)`. Over a field `F`, `dieudonneDet` agrees with
`Group.Abelianization.of ∘ Matrix.GeneralLinearGroup.det`.

## Main definitions

* `Matrix.GeneralLinearGroup.dieudonneDet`: the Dieudonné determinant
  `GL n D →* Group.Abelianization Dˣ` over a division ring `D`.
* `Matrix.GeneralLinearGroup.quotientElementarySubgroupEquivAbelianization`: for `[Nontrivial n]`,
  the canonical isomorphism `GL n D ⧸ TauCeti.elementarySubgroup n D ≃* Group.Abelianization Dˣ`.

## Main results

* `TauCeti.exists_mem_elementarySubgroup_mul_diagGL_mulSingle` and
  `TauCeti.exists_diagGL_mulSingle_mul_mem_elementarySubgroup`: every invertible matrix on a
  nonempty finite index type over a division ring factors into an elementary matrix and a
  single-coordinate diagonal matrix.
* `Matrix.GeneralLinearGroup.eq_dieudonneDet_of_elementarySubgroup_le_ker`: uniqueness of the
  Dieudonné determinant from vanishing on `E n D` and single-coordinate diagonal values.
* `Matrix.GeneralLinearGroup.dieudonneDet_diagGL`, `Matrix.GeneralLinearGroup.dieudonneDet_scalar`,
  `Matrix.GeneralLinearGroup.dieudonneDet_reindexGL`,
  `Matrix.GeneralLinearGroup.dieudonneDet_fromBlocksGL`,
  `Matrix.GeneralLinearGroup.dieudonneDet_stabilizeGL`, and
  `Matrix.GeneralLinearGroup.dieudonneDet_mapMatrix`: diagonal, block-diagonal, stabilization, and
  functoriality formulas.
* `Matrix.GeneralLinearGroup.dieudonneDet_surjective`: surjectivity when `n` is nonempty.
* `Matrix.GeneralLinearGroup.ker_dieudonneDet`: for `[Nontrivial n]`, the kernel of `dieudonneDet`
  is `TauCeti.elementarySubgroup n D`.
* `TauCeti.elementarySubgroup_normal_of_divisionRing` and
  `TauCeti.commutator_eq_elementarySubgroup_of_divisionRing`: normality for `[Nontrivial n]` and
  identification with `commutator (GL n D)` for `3 ≤ Fintype.card n`.
* `Matrix.GeneralLinearGroup.dieudonneDet_eq_of_det`: compatibility with the classical determinant
  over a field.

## References

* J. Dieudonné, *Les déterminants sur un corps non commutatif*, Bull. Soc. Math. France 71 (1943),
  27–45.
* E. Artin, *Geometric Algebra*, Interscience (1957), Chapter IV, §1.
* J. Milnor, *Introduction to Algebraic K-Theory*, Annals of Mathematics Studies 72 (1971), §3.
* C. A. Weibel, *The K-book: An Introduction to Algebraic K-Theory*, GSM 145 (2013), Chapter III,
  §1.2.
-/

public section

noncomputable section

open Matrix

open scoped commutatorElement

namespace TauCeti

section Decomposition

variable {D : Type*} [DivisionRing D]

/-- The first column of an invertible matrix on `Fin (m + 1)` over a division ring has a nonzero
entry. -/
private theorem exists_col_zero_ne_zero {m : ℕ} (A : GL (Fin (m + 1)) D) :
    ∃ r : Fin (m + 1), A r 0 ≠ 0 := by
  by_contra! h
  have h1 : (A⁻¹.val * A.val) 0 0 = (1 : D) := by
    rw [Units.inv_mul]
    rfl
  have h0 : (A⁻¹.val * A.val) 0 0 = 0 := by
    rw [Matrix.mul_apply]
    exact Finset.sum_eq_zero fun r _ ↦ by simp [h r]
  exact one_ne_zero (h1.symm.trans h0)

/-- On `Fin (m + 2)` over a division ring, left multiplication by at most two transvections sets
the `(0, 0)` entry of an invertible matrix to `1`. -/
private theorem exists_elementary_mul_entry_zero_zero_eq_one {m : ℕ}
    (A : GL (Fin (m + 2)) D) :
    ∃ e ∈ elementarySubgroup (Fin (m + 2)) D, (e * A) 0 0 = 1 := by
  obtain ⟨r, hr⟩ := exists_col_zero_ne_zero A
  have h01 : (0 : Fin (m + 2)) ≠ 1 := Fin.zero_ne_one
  by_cases hr1 : r = 1
  · subst hr1
    refine ⟨transvectionUnit h01 ((1 - A 0 0) * (A 1 0)⁻¹),
      transvectionUnit_mem_elementarySubgroup _ _, ?_⟩
    change ((transvectionUnit h01 ((1 - A 0 0) * (A 1 0)⁻¹)).val * A.val) 0 0 = 1
    rw [coe_transvectionUnit_mul_apply]
    simp only [↓reduceIte]
    rw [mul_assoc, inv_mul_cancel₀ hr, mul_one, add_sub_cancel]
  · set e₁ := transvectionUnit (Ne.symm hr1) ((1 - A 1 0) * (A r 0)⁻¹)
    have hA₁ : (e₁ * A) 1 0 = 1 := by
      change (e₁.val * A.val) 1 0 = 1
      rw [coe_transvectionUnit_mul_apply]
      simp only [↓reduceIte]
      rw [mul_assoc, inv_mul_cancel₀ hr, mul_one, add_sub_cancel]
    set e₂ := transvectionUnit h01 (1 - (e₁ * A) 0 0)
    refine ⟨e₂ * e₁, mul_mem (transvectionUnit_mem_elementarySubgroup _ _)
      (transvectionUnit_mem_elementarySubgroup _ _), ?_⟩
    rw [mul_assoc]
    change (e₂.val * (e₁ * A).val) 0 0 = 1
    rw [coe_transvectionUnit_mul_apply]
    simp only [↓reduceIte]
    rw [hA₁, mul_one, add_sub_cancel]

/-- Extracting the lower-right invertible block from an invertible block matrix of the form
`fromBlocks 1 0 0 S`. -/
private def lowerRightBlockOfFromBlocks {m k : Type*} [DecidableEq m] [Fintype m]
    [DecidableEq k] [Fintype k] {A : Type*} [Ring A] (M : GL (m ⊕ k) A) (S : Matrix k k A)
    (hM : M.val = fromBlocks 1 0 0 S) : GL k A where
  val := S
  inv := M⁻¹.val.toBlocks₂₂
  val_inv := by
    ext i j
    have h := congr_fun₂ M.val_inv (Sum.inr i) (Sum.inr j)
    simpa [hM, Matrix.mul_apply, Fintype.sum_sum_type, Matrix.toBlocks₂₂, Matrix.one_apply] using h
  inv_val := by
    ext i j
    have h := congr_fun₂ M.inv_val (Sum.inr i) (Sum.inr j)
    simpa [hM, Matrix.mul_apply, Fintype.sum_sum_type, Matrix.toBlocks₂₂, Matrix.one_apply] using h

/-- Reindexing `diagGL (Pi.mulSingle i d)` along `σ : m ≃ n` moves the diagonal entry to `σ i`. -/
private theorem reindexGL_diagGL_mulSingle {m n : Type*} [DecidableEq m] [Fintype m]
    [DecidableEq n] [Fintype n] {A : Type*} [Ring A] (σ : m ≃ n) (i : m) (d : Aˣ) :
    σ.reindexGL A (diagGL (Pi.mulSingle i d)) = diagGL (Pi.mulSingle (σ i) d) := by
  ext a b
  simp only [Equiv.coe_reindexGL, diagGL_apply, submatrix_apply, σ.symm_apply_eq]
  by_cases ha : a = σ i
  · subst ha
    simp
  · have ha' : σ.symm a ≠ i := by rwa [Ne, σ.symm_apply_eq]
    simp [ha, ha']

/-- Placing `diagGL (Pi.mulSingle i d)` in the lower-right block gives
`diagGL (Pi.mulSingle (Sum.inr i) d)`. -/
private theorem fromBlocksGL_one_diagGL_mulSingle {m k : Type*} [DecidableEq m] [Fintype m]
    [DecidableEq k] [Fintype k] {A : Type*} [Ring A] (i : k) (d : Aˣ) :
    fromBlocksGL ((1 : GL m A), diagGL (Pi.mulSingle i d)) =
      diagGL (Pi.mulSingle (Sum.inr i) d) := by
  ext (a | a) (b | b) <;>
    simp [Matrix.diagonal_apply, Pi.mulSingle_apply, Matrix.one_apply]

/-- Inductive Gaussian decomposition on `GL (Fin (m + 1)) D`. -/
private theorem exists_mem_elementarySubgroup_mul_diagGL_mulSingle_fin :
    ∀ (m : ℕ) (A : GL (Fin (m + 1)) D),
      ∃ e ∈ elementarySubgroup (Fin (m + 1)) D, ∃ d : Dˣ,
        A = e * diagGL (Pi.mulSingle 0 d)
  | 0, A => by
    let d : Dˣ :=
      { val := A 0 0
        inv := A⁻¹ 0 0
        val_inv := by simpa [Matrix.mul_apply] using congr_fun₂ A.val_inv 0 0
        inv_val := by simpa [Matrix.mul_apply] using congr_fun₂ A.inv_val 0 0 }
    refine ⟨1, one_mem _, d, ?_⟩
    ext i j
    fin_cases i
    fin_cases j
    simp [d]
  | m + 1, A => by
    obtain ⟨e₀, he₀, hA₀⟩ := exists_elementary_mul_entry_zero_zero_eq_one A
    let σ : Fin 1 ⊕ Fin (m + 1) ≃ Fin (m + 2) :=
      finSumFinEquiv.trans (finCongr (Nat.add_comm 1 (m + 1)))
    have hσ0 : σ (Sum.inl 0) = 0 := rfl
    set M : GL (Fin 1 ⊕ Fin (m + 1)) D := σ.symm.reindexGL D (e₀ * A)
    let b : Matrix (Fin 1) (Fin (m + 1)) D := fun _ j ↦ M (Sum.inl 0) (Sum.inr j)
    let c : Matrix (Fin (m + 1)) (Fin 1) D := fun i _ ↦ M (Sum.inr i) (Sum.inl 0)
    let C : Matrix (Fin (m + 1)) (Fin (m + 1)) D := fun i j ↦ M (Sum.inr i) (Sum.inr j)
    have hM_blocks : M.val = fromBlocks 1 b c C := by
      ext (i | i) (j | j)
      · fin_cases i; fin_cases j
        simpa [M, hσ0] using hA₀
      · fin_cases i; rfl
      · fin_cases j; rfl
      · rfl
    set M' : GL (Fin 1 ⊕ Fin (m + 1)) D := lowerBlockGL (-c) * M * upperBlockGL (-b)
    have hM' : M'.val = fromBlocks 1 0 0 (C - c * b) := by
      simp only [M', Units.val_mul, coe_lowerBlockGL, coe_upperBlockGL, hM_blocks,
        fromBlocks_multiply, Matrix.mul_one, Matrix.one_mul, Matrix.mul_zero, Matrix.zero_mul,
        add_zero, zero_add, neg_add_cancel, Matrix.neg_mul]
      congr 1
      abel
    let B : GL (Fin (m + 1)) D := lowerRightBlockOfFromBlocks M' (C - c * b) hM'
    have hM'_eq : M' = fromBlocksGL (1, B) :=
      Units.ext (by simp [B, lowerRightBlockOfFromBlocks, hM'])
    obtain ⟨eB, heB, d, hB⟩ := exists_mem_elementarySubgroup_mul_diagGL_mulSingle_fin m B
    set t : Fin 1 ⊕ Fin (m + 1) → Dˣ := Pi.mulSingle (Sum.inr 0) d
    have hM_decomp : M = (lowerBlockGL c * fromBlocksGL (1, eB) *
        (diagGL t * upperBlockGL b * (diagGL t)⁻¹)) * diagGL t := by
      have h1 : M = lowerBlockGL c * M' * upperBlockGL b := by
        simp only [M', ← lowerBlockGL_inv, ← upperBlockGL_inv]
        group
      rw [h1, hM'_eq, hB]
      have hfb : fromBlocksGL ((1 : GL (Fin 1) D), eB * diagGL (Pi.mulSingle 0 d)) =
          fromBlocksGL (1, eB) * diagGL t := by
        rw [← fromBlocksGL_one_diagGL_mulSingle, ← map_mul]
        simp
      rw [hfb]
      group
    have heM : lowerBlockGL c * fromBlocksGL (1, eB) *
        (diagGL t * upperBlockGL b * (diagGL t)⁻¹) ∈
          elementarySubgroup (Fin 1 ⊕ Fin (m + 1)) D :=
      mul_mem (mul_mem (lowerBlockGL_mem_elementarySubgroup c)
        (fromBlocksGL_mem_elementarySubgroup (one_mem _) heB))
        (conj_diagGL_mem_elementarySubgroup t (upperBlockGL_mem_elementarySubgroup b))
    set eM := lowerBlockGL c * fromBlocksGL (1, eB) *
      (diagGL t * upperBlockGL b * (diagGL t)⁻¹)
    have he₀A : e₀ * A = σ.reindexGL D eM * diagGL (Pi.mulSingle (σ (Sum.inr 0)) d) := by
      have h2 := congrArg (σ.reindexGL D) hM_decomp
      simpa only [M, Equiv.reindexGL_apply_symm_reindexGL, map_mul, t,
        reindexGL_diagGL_mulSingle] using h2
    have hne : σ (Sum.inr 0) ≠ 0 := by
      rw [← hσ0]
      exact σ.injective.ne Sum.inr_ne_inl
    refine ⟨e₀⁻¹ * σ.reindexGL D eM *
      (diagGL (Pi.mulSingle (σ (Sum.inr 0)) d) * (diagGL (Pi.mulSingle 0 d))⁻¹),
      mul_mem (mul_mem (inv_mem he₀)
        (σ.map_reindexGL_elementarySubgroup (A := D) ▸ ⟨eM, heM, rfl⟩))
        (diagGL_mulSingle_mul_diagGL_mulSingle_inv_mem_elementarySubgroup hne d), d, ?_⟩
    have hA : A = e₀⁻¹ * (e₀ * A) := by group
    rw [hA, he₀A]
    group

/-- **Bruhat–Gaussian elementary decomposition over a division ring.** Every invertible matrix on a
nonempty finite index type `n` over a division ring `D`, at any chosen index `i : n`, factors as
`e * diagGL (Pi.mulSingle i d)` with `e ∈ E n D` and `d : Dˣ`. -/
theorem exists_mem_elementarySubgroup_mul_diagGL_mulSingle
    {n : Type*} [Fintype n] [DecidableEq n] (g : GL n D) (i : n) :
    ∃ e ∈ elementarySubgroup n D, ∃ d : Dˣ, g = e * diagGL (Pi.mulSingle i d) := by
  have hpos : 0 < Fintype.card n := Fintype.card_pos_iff.2 ⟨i⟩
  let σ : n ≃ Fin (Fintype.card n - 1 + 1) :=
    (Fintype.equivFin n).trans (finCongr (Nat.sub_add_cancel hpos).symm)
  obtain ⟨e₀, he₀, d, hg₀⟩ :=
    exists_mem_elementarySubgroup_mul_diagGL_mulSingle_fin (Fintype.card n - 1) (σ.reindexGL D g)
  have hg₁ : g = σ.symm.reindexGL D e₀ * diagGL (Pi.mulSingle (σ.symm 0) d) := by
    have h := congrArg (σ.symm.reindexGL D) hg₀
    simpa only [Equiv.reindexGL_symm_apply_reindexGL, map_mul, reindexGL_diagGL_mulSingle] using h
  have he₁ : σ.symm.reindexGL D e₀ ∈ elementarySubgroup n D :=
    σ.symm.map_reindexGL_elementarySubgroup (A := D) ▸ ⟨e₀, he₀, rfl⟩
  by_cases hij : σ.symm 0 = i
  · exact ⟨σ.symm.reindexGL D e₀, he₁, d, hij ▸ hg₁⟩
  · refine ⟨σ.symm.reindexGL D e₀ *
        (diagGL (Pi.mulSingle (σ.symm 0) d) * (diagGL (Pi.mulSingle i d))⁻¹),
      mul_mem he₁ (diagGL_mulSingle_mul_diagGL_mulSingle_inv_mem_elementarySubgroup hij d), d, ?_⟩
    rw [hg₁]
    group

/-- Right-elementary form of `TauCeti.exists_mem_elementarySubgroup_mul_diagGL_mulSingle`: every
invertible matrix on a nonempty finite index type over a division ring factors as
`diagGL (Pi.mulSingle i d) * e` with `e ∈ E n D`. -/
theorem exists_diagGL_mulSingle_mul_mem_elementarySubgroup
    {n : Type*} [Fintype n] [DecidableEq n] (g : GL n D) (i : n) :
    ∃ d : Dˣ, ∃ e ∈ elementarySubgroup n D, g = diagGL (Pi.mulSingle i d) * e := by
  obtain ⟨e, he, d, rfl⟩ := exists_mem_elementarySubgroup_mul_diagGL_mulSingle g i
  refine ⟨d, (diagGL (Pi.mulSingle i d))⁻¹ * e * diagGL (Pi.mulSingle i d), ?_, by group⟩
  simpa [← map_inv] using conj_diagGL_mem_elementarySubgroup (Pi.mulSingle i d)⁻¹ he

end Decomposition

/-! ## Artin's Schur-complement induction on `GL (Fin m) D` -/

section ArtinInduction

variable {D : Type*} [DivisionRing D]

/-- The inductive Artin axioms characterizing the Dieudonné determinant on `GL (Fin m) D`:
normalization at `1`, invariance under left multiplication by elementary transvections, and
equivariance under left multiplication by single-coordinate diagonal matrices. -/
private structure IsDieudonneDetFin (m : ℕ)
    (f : GL (Fin m) D → Group.Abelianization Dˣ) : Prop where
  map_one : f 1 = 1
  map_transvectionUnit_mul : ∀ {i j : Fin m} (hij : i ≠ j) (c : D) (A : GL (Fin m) D),
    f (transvectionUnit hij c * A) = f A
  map_diagGL_mulSingle_mul : ∀ (i : Fin m) (d : Dˣ) (A : GL (Fin m) D),
    f (diagGL (Pi.mulSingle i d) * A) = Group.Abelianization.of d * f A

/-- Any function satisfying `IsDieudonneDetFin` is invariant under left multiplication by arbitrary
elements of `elementarySubgroup (Fin m) D`. -/
private theorem IsDieudonneDetFin.map_elementary_mul {m : ℕ}
    {f : GL (Fin m) D → Group.Abelianization Dˣ} (hf : IsDieudonneDetFin m f)
    {e : GL (Fin m) D} (he : e ∈ elementarySubgroup (Fin m) D) (A : GL (Fin m) D) :
    f (e * A) = f A := by
  let H : Subgroup (GL (Fin m) D) :=
    { carrier := {g | ∀ B, f (g * B) = f B}
      one_mem' := fun B ↦ by simp
      mul_mem' := fun {g₁ g₂} h₁ h₂ B ↦ by rw [mul_assoc, h₁, h₂]
      inv_mem' := fun {g} hg B ↦ by rw [← hg (g⁻¹ * B), mul_inv_cancel_left] }
  have hle : elementarySubgroup (Fin m) D ≤ H :=
    elementarySubgroup_le_iff.2 fun _ _ hij c B ↦ hf.map_transvectionUnit_mul hij c B
  exact hle he A

/-- Unsigned row-swap matrix exchanging rows `p` and `q`, obtained by scaling row `q` of the Weyl
representative `w_{p,q}` by `-1`. -/
private def rowSwapGL {m : ℕ} {p q : Fin m} (hpq : p ≠ q) : GL (Fin m) D :=
  diagGL (Pi.mulSingle q (-1 : Dˣ)) * transvectionWeylElement hpq

private theorem coe_rowSwapGL_mul_apply {m : ℕ} {p q : Fin m} (hpq : p ≠ q)
    (M : Matrix (Fin m) (Fin m) D) (a b : Fin m) :
    ((rowSwapGL (D := D) hpq).val * M) a b = M (Equiv.swap p q a) b := by
  have hdiag : ∀ (N : Matrix (Fin m) (Fin m) D),
      ((diagGL (Pi.mulSingle (M := fun _ : Fin m ↦ Dˣ) q (-1 : Dˣ))).val * N) a b =
        ((Pi.mulSingle (M := fun _ : Fin m ↦ Dˣ) q (-1 : Dˣ) a : Dˣ) : D) * N a b := fun N ↦ by
    rw [diagGL_coe, Matrix.diagonal_mul]
  rw [rowSwapGL, Units.val_mul, mul_assoc, hdiag, coe_transvectionWeylElement_mul_apply]
  by_cases hap : a = p
  · subst hap
    simp [hpq]
  · by_cases haq : a = q
    · subst haq
      simp [hpq.symm]
    · simp [hap, haq, Equiv.swap_apply_of_ne_of_ne hap haq]

private theorem IsDieudonneDetFin.map_rowSwapGL_mul {m : ℕ}
    {f : GL (Fin m) D → Group.Abelianization Dˣ} (hf : IsDieudonneDetFin m f)
    {p q : Fin m} (hpq : p ≠ q) (X : GL (Fin m) D) :
    f (rowSwapGL hpq * X) = Group.Abelianization.of (-1 : Dˣ) * f X := by
  rw [rowSwapGL, mul_assoc, hf.map_diagGL_mulSingle_mul,
    hf.map_elementary_mul (transvectionWeylElement_mem_elementarySubgroup hpq)]

/-- Cyclic index map shifting `a, a + 1, …, a + d` by one step. -/
private def cycleIndex {m : ℕ} (a d : ℕ) (had : a + d < m) (i : Fin m) : Fin m :=
  if (i : ℕ) < a then i
  else if h2 : (i : ℕ) < a + d then ⟨(i : ℕ) + 1, by omega⟩
  else if (i : ℕ) = a + d then ⟨a, by omega⟩
  else i

/-- Cycling row `a` upward across `d` adjacent positions multiplies an `IsDieudonneDetFin`
invariant by `Group.Abelianization.of (-1 : Dˣ) ^ d`. -/
private theorem exists_cycle_rows {m : ℕ} {f : GL (Fin m) D → Group.Abelianization Dˣ}
    (hf : IsDieudonneDetFin m f) (a : ℕ) :
    ∀ (d : ℕ) (had : a + d < m) (X : GL (Fin m) D),
      ∃ Y : GL (Fin m) D,
        f Y = Group.Abelianization.of (-1 : Dˣ) ^ d * f X ∧
        ∀ (i j : Fin m), Y i j = X (cycleIndex a d had i) j
  | 0, had, X => by
    refine ⟨X, by simp, fun i j ↦ ?_⟩
    have hidx : cycleIndex a 0 had i = i := by
      ext
      simp only [cycleIndex]
      split_ifs <;> simp_all; omega
    rw [hidx]
  | d + 1, had, X => by
    have had' : a + d < m := by omega
    obtain ⟨Y, hY_f, hY_apply⟩ := exists_cycle_rows hf a d had' X
    let p : Fin m := ⟨a + d, by omega⟩
    let q : Fin m := ⟨a + d + 1, by omega⟩
    have hpq : p ≠ q := by simp [p, q, Fin.ext_iff]
    refine ⟨rowSwapGL hpq * Y, ?_, fun i j ↦ ?_⟩
    · rw [hf.map_rowSwapGL_mul hpq Y, hY_f, ← mul_assoc, ← pow_succ']
    · have hidx : cycleIndex a d had' (Equiv.swap p q i) = cycleIndex a (d + 1) had i := by
        by_cases hip : i = p
        · subst hip
          rw [Equiv.swap_apply_left]
          ext
          simp only [cycleIndex, p, q]
          split_ifs <;> simp_all; omega
        · by_cases hiq : i = q
          · subst hiq
            rw [Equiv.swap_apply_right]
            ext
            simp only [cycleIndex, p, q]
            split_ifs <;> simp_all <;> omega
          · rw [Equiv.swap_apply_of_ne_of_ne hip hiq]
            have hp_val : (i : ℕ) ≠ a + d := fun h ↦ hip (Fin.ext h)
            have hq_val : (i : ℕ) ≠ a + d + 1 := fun h ↦ hiq (Fin.ext h)
            ext
            simp only [cycleIndex]
            split_ifs <;> simp_all <;> omega
      have hmul : (rowSwapGL (D := D) hpq * Y) i j = Y (Equiv.swap p q i) j :=
        coe_rowSwapGL_mul_apply hpq Y.val i j
      rw [hmul, hY_apply, hidx]

private theorem mul_inv_mul_assoc_cancel {x y z : D} (hy : y ≠ 0) :
    (x * y⁻¹) * (y * z) = x * z := by
  rw [mul_assoc x y⁻¹, ← mul_assoc y⁻¹ y z, inv_mul_cancel₀ hy, one_mul]

private theorem mul_mul_inv_assoc_cancel {x y z : D} (hy : y ≠ 0) :
    (x * y) * (y⁻¹ * z) = x * z := by
  rw [mul_assoc x y, ← mul_assoc y y⁻¹ z, mul_inv_cancel₀ hy, one_mul]

/-- The `m × m` Schur complement obtained by eliminating column `0` of `A : GL (Fin (m + 1)) D`
using pivot `(r, 0)` with `A r 0 ≠ 0`. Its inverse is the complementary submatrix of `A⁻¹`. -/
private def pivotMinor {m : ℕ} (A : GL (Fin (m + 1)) D) (r : Fin (m + 1))
    (hr : A r 0 ≠ 0) : GL (Fin m) D where
  val i j := A (r.succAbove i) j.succ - A (r.succAbove i) 0 * (A r 0)⁻¹ * A r j.succ
  inv j k := A⁻¹ j.succ (r.succAbove k)
  val_inv := by
    ext i k
    have hdiag : (A.val * A⁻¹.val) (r.succAbove i) (r.succAbove k) =
        (1 : Matrix (Fin m) (Fin m) D) i k := by
      rw [Units.mul_inv, Matrix.one_apply, Matrix.one_apply]
      simp only [Fin.succAbove_right_inj]
    have hoff : (A.val * A⁻¹.val) r (r.succAbove k) = 0 := by
      rw [Units.mul_inv, Matrix.one_apply_ne (r.succAbove_ne k).symm]
    rw [Matrix.mul_apply, Fin.sum_univ_succ] at hdiag hoff
    have h1 : ∑ x : Fin m, A (r.succAbove i) x.succ * A⁻¹ x.succ (r.succAbove k) =
        (1 : Matrix (Fin m) (Fin m) D) i k -
          A (r.succAbove i) 0 * A⁻¹ 0 (r.succAbove k) :=
      eq_sub_of_add_eq' hdiag
    have h2 : ∑ x : Fin m, A r x.succ * A⁻¹ x.succ (r.succAbove k) =
        -(A r 0 * A⁻¹ 0 (r.succAbove k)) :=
      eq_neg_of_add_eq_zero_right hoff
    change (∑ x : Fin m,
      (A (r.succAbove i) x.succ - A (r.succAbove i) 0 * (A r 0)⁻¹ * A r x.succ) *
        A⁻¹ x.succ (r.succAbove k)) = (1 : Matrix (Fin m) (Fin m) D) i k
    calc
      ∑ x : Fin m,
          (A (r.succAbove i) x.succ - A (r.succAbove i) 0 * (A r 0)⁻¹ * A r x.succ) *
            A⁻¹ x.succ (r.succAbove k)
        = (∑ x : Fin m, A (r.succAbove i) x.succ * A⁻¹ x.succ (r.succAbove k)) -
            (A (r.succAbove i) 0 * (A r 0)⁻¹) *
              ∑ x : Fin m, A r x.succ * A⁻¹ x.succ (r.succAbove k) := by
          rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
          refine Finset.sum_congr rfl fun x _ ↦ ?_
          simp only [sub_mul, mul_assoc]
      _ = (1 : Matrix (Fin m) (Fin m) D) i k := by
          rw [h1, h2, mul_neg, mul_inv_mul_assoc_cancel hr]
          abel
  inv_val := by
    ext j k
    have hdiag : (A⁻¹.val * A.val) j.succ k.succ =
        (1 : Matrix (Fin m) (Fin m) D) j k := by
      rw [Units.inv_mul, Matrix.one_apply, Matrix.one_apply]
      simp only [Fin.succ_inj]
    have hoff : (A⁻¹.val * A.val) j.succ 0 = 0 := by
      rw [Units.inv_mul, Matrix.one_apply_ne (Fin.succ_ne_zero j)]
    rw [Matrix.mul_apply, Fin.sum_univ_succAbove _ r] at hdiag hoff
    have h1 : ∑ x : Fin m, A⁻¹ j.succ (r.succAbove x) * A (r.succAbove x) k.succ =
        (1 : Matrix (Fin m) (Fin m) D) j k - A⁻¹ j.succ r * A r k.succ :=
      eq_sub_of_add_eq' hdiag
    have h2 : ∑ x : Fin m, A⁻¹ j.succ (r.succAbove x) * A (r.succAbove x) 0 =
        -(A⁻¹ j.succ r * A r 0) :=
      eq_neg_of_add_eq_zero_right hoff
    change ∑ x : Fin m, A⁻¹ j.succ (r.succAbove x) *
      (A (r.succAbove x) k.succ - A (r.succAbove x) 0 * (A r 0)⁻¹ * A r k.succ) =
        (1 : Matrix (Fin m) (Fin m) D) j k
    calc
      ∑ x : Fin m, A⁻¹ j.succ (r.succAbove x) *
          (A (r.succAbove x) k.succ - A (r.succAbove x) 0 * (A r 0)⁻¹ * A r k.succ)
        = (∑ x : Fin m, A⁻¹ j.succ (r.succAbove x) * A (r.succAbove x) k.succ) -
            (∑ x : Fin m, A⁻¹ j.succ (r.succAbove x) * A (r.succAbove x) 0) *
              ((A r 0)⁻¹ * A r k.succ) := by
          rw [Finset.sum_mul, ← Finset.sum_sub_distrib]
          refine Finset.sum_congr rfl fun x _ ↦ ?_
          simp only [mul_sub, mul_assoc]
      _ = (1 : Matrix (Fin m) (Fin m) D) j k := by
          rw [h1, h2, neg_mul, mul_mul_inv_assoc_cancel hr]
          abel

@[simp]
private theorem coe_pivotMinor_apply {m : ℕ} (A : GL (Fin (m + 1)) D) (r : Fin (m + 1))
    (hr : A r 0 ≠ 0) (i j : Fin m) :
    (pivotMinor A r hr) i j =
      A (r.succAbove i) j.succ - A (r.succAbove i) 0 * (A r 0)⁻¹ * A r j.succ :=
  (rfl)

/-- Candidate Dieudonné determinant at pivot row `r`. -/
private def pivotVal {m : ℕ} (f : GL (Fin m) D → Group.Abelianization Dˣ)
    (A : GL (Fin (m + 1)) D) (r : Fin (m + 1)) (hr : A r 0 ≠ 0) : Group.Abelianization Dˣ :=
  Group.Abelianization.of (-1 : Dˣ) ^ (r : ℕ) *
    Group.Abelianization.of (Units.mk0 (A r 0) hr) * f (pivotMinor A r hr)

/-- Adding multiples `c i` of row `r'` to every other row `i ≠ r'` via a reindexed lower block
unipotent matrix. -/
private def addRowMultiplesGL {m : ℕ} (r' : Fin m) (c : Fin m → D) : GL (Fin m) D :=
  (Equiv.sumCompl (· = r')).reindexGL D
    (Matrix.lowerBlockGL
      (Matrix.of fun (i : {x : Fin m // ¬(x = r')}) (_ : {x : Fin m // x = r'}) ↦ c i.1))

private theorem addRowMultiplesGL_mem_elementarySubgroup {m : ℕ} (r' : Fin m) (c : Fin m → D) :
    addRowMultiplesGL r' c ∈ elementarySubgroup (Fin m) D :=
  (Equiv.sumCompl (· = r')).map_reindexGL_elementarySubgroup (A := D) ▸
    ⟨_, Matrix.lowerBlockGL_mem_elementarySubgroup _, rfl⟩

private theorem val_addRowMultiplesGL_apply {m : ℕ} (r' : Fin m) (c : Fin m → D) (p q : Fin m) :
    (addRowMultiplesGL r' c).val p q =
      (1 : Matrix (Fin m) (Fin m) D) p q + if p ≠ r' ∧ q = r' then c p else 0 := by
  obtain ⟨p, rfl⟩ := (Equiv.sumCompl (· = r')).surjective p
  obtain ⟨q, rfl⟩ := (Equiv.sumCompl (· = r')).surjective q
  rw [addRowMultiplesGL, Equiv.coe_reindexGL, Matrix.coe_lowerBlockGL, submatrix_apply,
    Equiv.symm_apply_apply, Equiv.symm_apply_apply, Matrix.one_apply]
  rcases p with ⟨p, hp⟩ | ⟨p, hp⟩ <;> rcases q with ⟨q, hq⟩ | ⟨q, hq⟩
  · subst hp; subst hq
    simp
  · subst hp
    simp [Ne.symm hq]
  · subst hq
    simp [hp]
  · by_cases hpq : p = q
    · subst hpq
      simp [hq]
    · have hpq' : (⟨p, hp⟩ : {x : Fin m // ¬(x = r')}) ≠ ⟨q, hq⟩ :=
        fun h ↦ hpq (congrArg Subtype.val h)
      simp [hpq, hpq', hq]

private theorem coe_addRowMultiplesGL_mul_apply {m : ℕ} (r' : Fin m) (c : Fin m → D)
    (M : Matrix (Fin m) (Fin m) D) (i j : Fin m) :
    ((addRowMultiplesGL r' c).val * M) i j =
      if i = r' then M r' j else M i j + c i * M r' j := by
  rw [Matrix.mul_apply]
  simp only [val_addRowMultiplesGL_apply, add_mul, Finset.sum_add_distrib, Matrix.one_apply,
    ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]
  by_cases hi : i = r'
  · subst hi
    simp
  · simp [hi]

private theorem schur_elim_other {x y r₀ s₀ rj sj : D} (hr : r₀ ≠ 0) :
    (x - y * s₀⁻¹ * sj) + -(y * r₀⁻¹) * (rj - r₀ * s₀⁻¹ * sj) = x - y * r₀⁻¹ * rj := by
  have h : (y * r₀⁻¹) * (r₀ * s₀⁻¹ * sj) = y * s₀⁻¹ * sj := by
    rw [mul_assoc y r₀⁻¹, ← mul_assoc r₀⁻¹ (r₀ * s₀⁻¹) sj, ← mul_assoc r₀⁻¹ r₀ s₀⁻¹,
      inv_mul_cancel₀ hr, one_mul, ← mul_assoc y s₀⁻¹ sj]
  rw [neg_mul, mul_sub, h]
  abel

private theorem schur_elim_pivot {r₀ s₀ rj sj : D} (hr : r₀ ≠ 0) (hs : s₀ ≠ 0) :
    -(s₀ * r₀⁻¹) * (rj - r₀ * s₀⁻¹ * sj) = sj - s₀ * r₀⁻¹ * rj := by
  have h : (s₀ * r₀⁻¹) * (r₀ * s₀⁻¹ * sj) = sj := by
    rw [mul_assoc s₀ r₀⁻¹, ← mul_assoc r₀⁻¹ (r₀ * s₀⁻¹) sj, ← mul_assoc r₀⁻¹ r₀ s₀⁻¹,
      inv_mul_cancel₀ hr, one_mul, ← mul_assoc s₀ s₀⁻¹ sj, mul_inv_cancel₀ hs, one_mul]
  rw [neg_mul, mul_sub, h]
  abel

/-- Key Artin lemma: `pivotVal` is independent of the choice of nonzero pivot row `r < s`. -/
private theorem pivotVal_eq_of_lt {m : ℕ} {f : GL (Fin m) D → Group.Abelianization Dˣ}
    (hf : IsDieudonneDetFin m f) (A : GL (Fin (m + 1)) D) {r s : Fin (m + 1)} (hrs : r < s)
    (hr : A r 0 ≠ 0) (hs : A s 0 ≠ 0) :
    pivotVal f A r hr = pivotVal f A s hs := by
  let r' : Fin m := ⟨r.1, by omega⟩
  have hsr' : s.succAbove r' = r := by
    rw [Fin.succAbove]
    split_ifs <;>
      simp only [Fin.ext_iff, Fin.lt_def, Fin.val_castSucc, Fin.val_succ, r'] at *; omega
  let u : Dˣ := Units.mk0 (-(A s 0 * (A r 0)⁻¹))
    (neg_ne_zero.2 (mul_ne_zero hs (inv_ne_zero hr)))
  let E : GL (Fin m) D := addRowMultiplesGL r' fun i ↦ -(A (s.succAbove i) 0 * (A r 0)⁻¹)
  let M₀ : GL (Fin m) D := diagGL (Pi.mulSingle r' u) * (E * pivotMinor A s hs)
  have hfM₀ : f M₀ = Group.Abelianization.of (-1 : Dˣ) *
      Group.Abelianization.of (Units.mk0 (A s 0) hs) *
      (Group.Abelianization.of (Units.mk0 (A r 0) hr))⁻¹ * f (pivotMinor A s hs) := by
    have hu : u = (-1 : Dˣ) * Units.mk0 (A s 0) hs * (Units.mk0 (A r 0) hr)⁻¹ := by
      ext
      simp [u]
    rw [hf.map_diagGL_mulSingle_mul,
      hf.map_elementary_mul (addRowMultiplesGL_mem_elementarySubgroup _ _),
      hu, map_mul, map_mul, map_inv, mul_assoc, mul_assoc]
  have hM₀_other : ∀ (i j : Fin m), i ≠ r' → M₀ i j =
      A (s.succAbove i) j.succ - A (s.succAbove i) 0 * (A r 0)⁻¹ * A r j.succ := by
    intro i j hi
    change ((diagGL (Pi.mulSingle r' u)).val * (E.val * (pivotMinor A s hs).val)) i j = _
    rw [diagGL_coe, Matrix.diagonal_mul, coe_addRowMultiplesGL_mul_apply]
    simp only [hi, ↓reduceIte, Pi.mulSingle_eq_of_ne hi, Units.val_one, one_mul,
      coe_pivotMinor_apply, hsr']
    exact schur_elim_other hr
  have hM₀_r' : ∀ j : Fin m, M₀ r' j =
      A s j.succ - A s 0 * (A r 0)⁻¹ * A r j.succ := by
    intro j
    change ((diagGL (Pi.mulSingle r' u)).val * (E.val * (pivotMinor A s hs).val)) r' j = _
    rw [diagGL_coe, Matrix.diagonal_mul, coe_addRowMultiplesGL_mul_apply]
    simp only [↓reduceIte, Pi.mulSingle_eq_same]
    change -(A s 0 * (A r 0)⁻¹) * (pivotMinor A s hs) r' j = _
    simp only [coe_pivotMinor_apply, hsr']
    exact schur_elim_pivot hr hs
  have had : r.1 + (s.1 - 1 - r.1) < m := by omega
  obtain ⟨Y, hY_f, hY_apply⟩ := exists_cycle_rows hf r.1 (s.1 - 1 - r.1) had M₀
  have hBr_eq_Y : pivotMinor A r hr = Y := by
    ext i j
    rw [hY_apply, coe_pivotMinor_apply]
    simp only [cycleIndex]
    by_cases h1 : (i : ℕ) < r.1
    · simp only [h1, ↓reduceIte]
      have hi_ne : i ≠ r' := by simp [r', Fin.ext_iff]; omega
      rw [hM₀_other i j hi_ne]
      have hs_eq : s.succAbove i = r.succAbove i := by
        rw [Fin.succAbove, Fin.succAbove]
        split_ifs <;>
          simp only [Fin.ext_iff, Fin.lt_def, Fin.val_castSucc, Fin.val_succ] at * <;> omega
      rw [hs_eq]
    · simp only [h1, ↓reduceIte]
      by_cases h2 : (i : ℕ) < r.1 + (s.1 - 1 - r.1)
      · simp only [h2, ↓reduceDIte]
        set i' : Fin m := ⟨(i : ℕ) + 1, by omega⟩
        have hi'_ne : i' ≠ r' := by simp [i', r', Fin.ext_iff]; omega
        rw [hM₀_other i' j hi'_ne]
        have hs_eq : s.succAbove i' = r.succAbove i := by
          rw [Fin.succAbove, Fin.succAbove]
          split_ifs <;>
            simp only [Fin.ext_iff, Fin.lt_def, Fin.val_castSucc, Fin.val_succ, i'] at * <;> omega
        rw [hs_eq]
      · simp only [h2, ↓reduceDIte]
        by_cases h3 : (i : ℕ) = r.1 + (s.1 - 1 - r.1)
        · simp only [h3, ↓reduceIte]
          change _ = M₀ r' j
          rw [hM₀_r']
          have hr_eq : r.succAbove i = s := by
            rw [Fin.succAbove]
            split_ifs <;>
              simp only [Fin.ext_iff, Fin.lt_def, Fin.val_castSucc, Fin.val_succ] at * <;> omega
          rw [hr_eq]
        · simp only [h3, ↓reduceIte]
          have hi_ne : i ≠ r' := by simp [r', Fin.ext_iff]; omega
          rw [hM₀_other i j hi_ne]
          have hs_eq : s.succAbove i = r.succAbove i := by
            rw [Fin.succAbove, Fin.succAbove]
            split_ifs <;>
              simp only [Fin.ext_iff, Fin.lt_def, Fin.val_castSucc, Fin.val_succ] at * <;> omega
          rw [hs_eq]
  rw [pivotVal, pivotVal, hBr_eq_Y, hY_f, hfM₀]
  set ε := Group.Abelianization.of (-1 : Dˣ)
  set ur := Group.Abelianization.of (Units.mk0 (A r 0) hr)
  set us := Group.Abelianization.of (Units.mk0 (A s 0) hs)
  have hexp : ε ^ (r : ℕ) * (ε ^ (s.1 - 1 - r.1) * ε) = ε ^ (s : ℕ) := by
    rw [← pow_succ, ← pow_add]
    congr 1
    omega
  calc
    ε ^ (r : ℕ) * ur * (ε ^ (s.1 - 1 - r.1) * (ε * us * ur⁻¹ * f (pivotMinor A s hs)))
      = (ε ^ (r : ℕ) * (ε ^ (s.1 - 1 - r.1) * ε)) * (ur * ur⁻¹) * us * f (pivotMinor A s hs) := by
        ac_rfl
    _ = ε ^ (s : ℕ) * us * f (pivotMinor A s hs) := by
        rw [hexp, mul_inv_cancel, mul_one]

/-- `pivotVal` is independent of the choice of nonzero pivot row. -/
private theorem pivotVal_eq {m : ℕ} {f : GL (Fin m) D → Group.Abelianization Dˣ}
    (hf : IsDieudonneDetFin m f) (A : GL (Fin (m + 1)) D) (r s : Fin (m + 1))
    (hr : A r 0 ≠ 0) (hs : A s 0 ≠ 0) :
    pivotVal f A r hr = pivotVal f A s hs := by
  rcases lt_trichotomy r s with hrs | rfl | hsr
  · exact pivotVal_eq_of_lt hf A hrs hr hs
  · rfl
  · exact (pivotVal_eq_of_lt hf A hsr hs hr).symm

/-- Inductive step function on `GL (Fin (m + 1)) D` built from `f` on `GL (Fin m) D`. -/
private def stepFun {m : ℕ} (f : GL (Fin m) D → Group.Abelianization Dˣ)
    (A : GL (Fin (m + 1)) D) : Group.Abelianization Dˣ :=
  pivotVal f A (Classical.choose (exists_col_zero_ne_zero A))
    (Classical.choose_spec (exists_col_zero_ne_zero A))

private theorem stepFun_eq_pivotVal {m : ℕ} {f : GL (Fin m) D → Group.Abelianization Dˣ}
    (hf : IsDieudonneDetFin m f) (A : GL (Fin (m + 1)) D) (r : Fin (m + 1))
    (hr : A r 0 ≠ 0) :
    stepFun f A = pivotVal f A r hr :=
  pivotVal_eq hf A _ r _ hr

private theorem stepFun_one {m : ℕ} {f : GL (Fin m) D → Group.Abelianization Dˣ}
    (hf : IsDieudonneDetFin m f) : stepFun f 1 = 1 := by
  have hr : (1 : GL (Fin (m + 1)) D) 0 0 ≠ 0 := one_ne_zero
  rw [stepFun_eq_pivotVal hf 1 0 hr, pivotVal]
  have hminor : pivotMinor (1 : GL (Fin (m + 1)) D) 0 hr = 1 := by
    ext i j
    change (pivotMinor (1 : GL (Fin (m + 1)) D) 0 hr) i j = (1 : Matrix (Fin m) (Fin m) D) i j
    rw [coe_pivotMinor_apply]
    change (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) D) i.succ j.succ -
      (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) D) i.succ 0 * (1 : D)⁻¹ *
        (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) D) 0 j.succ = _
    simp [Matrix.one_apply, Fin.succ_inj]
  have hu : Units.mk0 ((1 : GL (Fin (m + 1)) D) 0 0) hr = 1 := by
    ext
    rfl
  rw [hminor, hu, Fin.val_zero, pow_zero, map_one, hf.map_one, mul_one, mul_one]

private theorem stepFun_transvectionUnit_mul {m : ℕ} {f : GL (Fin m) D → Group.Abelianization Dˣ}
    (hf : IsDieudonneDetFin m f) {p q : Fin (m + 1)} (hpq : p ≠ q) (c : D)
    (A : GL (Fin (m + 1)) D) :
    stepFun f (transvectionUnit hpq c * A) = stepFun f A := by
  set A' := transvectionUnit hpq c * A
  have hA'_apply : ∀ a b : Fin (m + 1),
      A' a b = if a = p then A p b + c * A q b else A a b :=
    fun a b ↦ coe_transvectionUnit_mul_apply hpq c A.val a b
  by_cases h : ∃ r : Fin (m + 1), r ≠ p ∧ A r 0 ≠ 0
  · obtain ⟨r, hrp, hr⟩ := h
    have hr'_eq : A' r 0 = A r 0 := by simp [hA'_apply, hrp]
    have hr' : A' r 0 ≠ 0 := hr'_eq ▸ hr
    rw [stepFun_eq_pivotVal hf A' r hr', stepFun_eq_pivotVal hf A r hr, pivotVal, pivotVal]
    have hu : Units.mk0 (A' r 0) hr' = Units.mk0 (A r 0) hr := Units.ext hr'_eq
    rw [hu]
    congr 1
    obtain ⟨p', hp'⟩ := Fin.exists_succAbove_eq hrp.symm
    by_cases hqr : q = r
    · subst hqr
      have hminor : pivotMinor A' q hr' = pivotMinor A q hr := by
        ext i j
        simp only [coe_pivotMinor_apply, hA'_apply, hrp, ↓reduceIte]
        by_cases hip : q.succAbove i = p
        · simp only [hip, ↓reduceIte]
          rw [add_mul, add_mul, mul_assoc c (A q 0), mul_inv_cancel₀ hr, mul_one]
          abel
        · simp [hip]
      rw [hminor]
    · obtain ⟨q', hq'⟩ := Fin.exists_succAbove_eq hqr
      have hp'q' : p' ≠ q' := fun h ↦ hpq (by rw [← hp', ← hq', h])
      have hminor : pivotMinor A' r hr' = transvectionUnit hp'q' c * pivotMinor A r hr := by
        ext i j
        change (pivotMinor A' r hr') i j =
          ((transvectionUnit hp'q' c).val * (pivotMinor A r hr).val) i j
        rw [coe_transvectionUnit_mul_apply]
        simp only [coe_pivotMinor_apply, hA'_apply, hrp, ↓reduceIte]
        by_cases hip' : i = p'
        · subst hip'
          simp only [↓reduceIte, hp', hq']
          rw [add_mul, add_mul, mul_sub]
          simp only [mul_assoc]
          abel
        · have hip : r.succAbove i ≠ p := by
            rw [← hp', Ne, Fin.succAbove_right_inj]
            exact hip'
          simp only [hip', hip, ↓reduceIte]
      rw [hminor, hf.map_transvectionUnit_mul]
  · simp only [not_exists, not_and, not_not] at h
    obtain ⟨s, hs⟩ := exists_col_zero_ne_zero A
    have hsp : s = p := by_contra fun hsp ↦ hs (h s hsp)
    subst hsp
    have hq0 : A q 0 = 0 := h q hpq.symm
    have hp'_eq : A' s 0 = A s 0 := by simp [hA'_apply, hq0]
    have hs' : A' s 0 ≠ 0 := hp'_eq ▸ hs
    rw [stepFun_eq_pivotVal hf A' s hs', stepFun_eq_pivotVal hf A s hs, pivotVal, pivotVal]
    have hu : Units.mk0 (A' s 0) hs' = Units.mk0 (A s 0) hs := Units.ext hp'_eq
    have hminor : pivotMinor A' s hs' = pivotMinor A s hs := by
      ext i j
      have hne : s.succAbove i ≠ s := s.succAbove_ne i
      have hi0 : A (s.succAbove i) 0 = 0 := h _ hne
      simp [coe_pivotMinor_apply, hA'_apply, hne, hi0]
    rw [hu, hminor]

private theorem mul_inv_mul_cancel_inner {y u z w : D} (hu : u ≠ 0) :
    y * (u * z)⁻¹ * (u * w) = y * z⁻¹ * w := by
  rw [_root_.mul_inv_rev, ← mul_assoc y z⁻¹ u⁻¹, mul_assoc (y * z⁻¹) u⁻¹ (u * w),
    ← mul_assoc u⁻¹ u w, inv_mul_cancel₀ hu, one_mul]

private theorem comm_helper₁ {M : Type*} [CommMonoid M] (a b c d : M) :
    a * (b * c) * d = b * (a * c * d) := by
  ac_rfl

private theorem comm_helper₂ {M : Type*} [CommMonoid M] (a b c d : M) :
    a * c * (b * d) = b * (a * c * d) := by
  ac_rfl

private theorem stepFun_diagGL_mulSingle_mul {m : ℕ} {f : GL (Fin m) D → Group.Abelianization Dˣ}
    (hf : IsDieudonneDetFin m f) (p : Fin (m + 1)) (d : Dˣ) (A : GL (Fin (m + 1)) D) :
    stepFun f (diagGL (Pi.mulSingle p d) * A) = Group.Abelianization.of d * stepFun f A := by
  set A' := diagGL (Pi.mulSingle p d) * A
  have hA'_apply : ∀ a b : Fin (m + 1),
      A' a b = if a = p then (d : D) * A p b else A a b := by
    intro a b
    change ((diagGL (Pi.mulSingle p d)).val * A.val) a b = _
    rw [diagGL_coe, Matrix.diagonal_mul]
    by_cases hap : a = p
    · subst hap; simp
    · simp [hap]
  obtain ⟨r, hr⟩ := exists_col_zero_ne_zero A
  by_cases hpr : p = r
  · subst hpr
    have hr' : A' p 0 ≠ 0 := by
      rw [hA'_apply]
      simp only [↓reduceIte]
      exact mul_ne_zero d.ne_zero hr
    rw [stepFun_eq_pivotVal hf A' p hr', stepFun_eq_pivotVal hf A p hr, pivotVal, pivotVal]
    have hu : Units.mk0 (A' p 0) hr' = d * Units.mk0 (A p 0) hr := by
      ext
      simp [hA'_apply]
    have hminor : pivotMinor A' p hr' = pivotMinor A p hr := by
      ext i j
      have hne : p.succAbove i ≠ p := p.succAbove_ne i
      simp only [coe_pivotMinor_apply, hA'_apply, hne, ↓reduceIte]
      rw [mul_inv_mul_cancel_inner d.ne_zero]
    rw [hu, hminor, map_mul]
    exact comm_helper₁ _ _ _ _
  · have hr'_eq : A' r 0 = A r 0 := by simp [hA'_apply, Ne.symm hpr]
    have hr' : A' r 0 ≠ 0 := hr'_eq ▸ hr
    rw [stepFun_eq_pivotVal hf A' r hr', stepFun_eq_pivotVal hf A r hr, pivotVal, pivotVal]
    have hu : Units.mk0 (A' r 0) hr' = Units.mk0 (A r 0) hr := Units.ext hr'_eq
    obtain ⟨p', hp'⟩ := Fin.exists_succAbove_eq hpr
    have hminor : pivotMinor A' r hr' = diagGL (Pi.mulSingle p' d) * pivotMinor A r hr := by
      ext i j
      change (pivotMinor A' r hr') i j =
        ((diagGL (Pi.mulSingle p' d)).val * (pivotMinor A r hr).val) i j
      rw [diagGL_coe, Matrix.diagonal_mul]
      simp only [coe_pivotMinor_apply, hA'_apply, Ne.symm hpr, ↓reduceIte]
      by_cases hip' : i = p'
      · subst hip'
        simp only [↓reduceIte, hp', Pi.mulSingle_eq_same, mul_sub, mul_assoc]
      · have hip : r.succAbove i ≠ p := by
          rw [← hp', Ne, Fin.succAbove_right_inj]
          exact hip'
        simp only [hip, ↓reduceIte, Pi.mulSingle_eq_of_ne hip', Units.val_one, one_mul]
    rw [hu, hminor, hf.map_diagGL_mulSingle_mul]
    exact comm_helper₂ _ _ _ _

/-- Inductive construction of the Dieudonné determinant function and its Artin axioms on
`GL (Fin m) D` for all `m : ℕ`. -/
private def dieudonneDetFinAux :
    ∀ m : ℕ, {f : GL (Fin m) D → Group.Abelianization Dˣ // IsDieudonneDetFin m f}
  | 0 => ⟨fun _ ↦ 1, ⟨rfl, fun _ _ _ ↦ rfl, fun i ↦ i.elim0⟩⟩
  | m + 1 =>
    let ⟨f, hf⟩ := dieudonneDetFinAux m
    ⟨stepFun f, ⟨stepFun_one hf, stepFun_transvectionUnit_mul hf,
      stepFun_diagGL_mulSingle_mul hf⟩⟩

/-- Bundled Dieudonné determinant homomorphism on `GL (Fin m) D`. -/
private def dieudonneDetFinHom (m : ℕ) : GL (Fin m) D →* Group.Abelianization Dˣ where
  toFun := (dieudonneDetFinAux (D := D) m).1
  map_one' := (dieudonneDetFinAux (D := D) m).2.map_one
  map_mul' := by
    rcases m with _ | k
    · intro A B
      rw [Subsingleton.elim (A * B) 1, Subsingleton.elim A 1, Subsingleton.elim B 1,
        (dieudonneDetFinAux (D := D) 0).2.map_one, mul_one]
    · intro A B
      obtain ⟨e, he, d, hA⟩ := exists_mem_elementarySubgroup_mul_diagGL_mulSingle_fin k A
      have hfA : (dieudonneDetFinAux (D := D) (k + 1)).1 A = Group.Abelianization.of d := by
        rw [hA, ← mul_one (diagGL (Pi.mulSingle 0 d)),
          (dieudonneDetFinAux (D := D) (k + 1)).2.map_elementary_mul he,
          (dieudonneDetFinAux (D := D) (k + 1)).2.map_diagGL_mulSingle_mul,
          (dieudonneDetFinAux (D := D) (k + 1)).2.map_one, mul_one]
      rw [hfA]
      conv_lhs => rw [hA, mul_assoc]
      rw [(dieudonneDetFinAux (D := D) (k + 1)).2.map_elementary_mul he,
        (dieudonneDetFinAux (D := D) (k + 1)).2.map_diagGL_mulSingle_mul]

end ArtinInduction

end TauCeti

/-! ## The Dieudonné determinant on `GL n D` -/

namespace Matrix.GeneralLinearGroup

variable {n m k : Type*} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]
  [Fintype k] [DecidableEq k] {D : Type*} [DivisionRing D]

/-- **The Dieudonné determinant** over a division ring `D`: the unique group homomorphism
`GL n D →* Group.Abelianization Dˣ` that vanishes on `TauCeti.elementarySubgroup n D` and sends
each `diagGL (Pi.mulSingle i d)` to `Group.Abelianization.of d`. -/
def dieudonneDet : GL n D →* Group.Abelianization Dˣ :=
  (TauCeti.dieudonneDetFinHom (D := D) (Fintype.card n)).comp
    ((Fintype.equivFin n).reindexGL D).toMonoidHom

/-- The Dieudonné determinant kills elementary transvections. -/
@[simp]
theorem dieudonneDet_transvectionUnit {i j : n} (hij : i ≠ j) (c : D) :
    dieudonneDet (TauCeti.transvectionUnit hij c) = 1 := by
  simp only [dieudonneDet, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    Equiv.reindexGL_transvectionUnit]
  let hf := (TauCeti.dieudonneDetFinAux (D := D) (Fintype.card n)).2
  change (TauCeti.dieudonneDetFinAux (D := D) (Fintype.card n)).1 _ = 1
  rw [← mul_one (TauCeti.transvectionUnit _ c), hf.map_transvectionUnit_mul, hf.map_one]

/-- The elementary subgroup lies in the kernel of the Dieudonné determinant. -/
theorem elementarySubgroup_le_ker_dieudonneDet :
    TauCeti.elementarySubgroup n D ≤ (dieudonneDet (n := n) (D := D)).ker :=
  TauCeti.elementarySubgroup_le_iff.2 fun _ _ hij c ↦ dieudonneDet_transvectionUnit hij c

/-- The Dieudonné determinant of an elementary matrix is `1`. -/
theorem dieudonneDet_eq_one_of_mem_elementarySubgroup {g : GL n D}
    (hg : g ∈ TauCeti.elementarySubgroup n D) : dieudonneDet g = 1 :=
  elementarySubgroup_le_ker_dieudonneDet hg

/-- On a diagonal matrix with `d` at coordinate `i` and `1` elsewhere, the Dieudonné determinant is
`Group.Abelianization.of d`. -/
@[simp]
theorem dieudonneDet_diagGL_mulSingle (i : n) (d : Dˣ) :
    dieudonneDet (TauCeti.diagGL (Pi.mulSingle i d)) = Group.Abelianization.of d := by
  simp only [dieudonneDet, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    TauCeti.reindexGL_diagGL_mulSingle]
  let hf := (TauCeti.dieudonneDetFinAux (D := D) (Fintype.card n)).2
  change (TauCeti.dieudonneDetFinAux (D := D) (Fintype.card n)).1 _ = _
  rw [← mul_one (TauCeti.diagGL _), hf.map_diagGL_mulSingle_mul, hf.map_one, mul_one]

/-- If the underlying matrix of `g : GL n D` is `diagonal (Function.update 1 i d)`, then
`dieudonneDet g = Group.Abelianization.of d`. -/
theorem dieudonneDet_of_coe_eq_diagonal_update (g : GL n D) (i : n) (d : Dˣ)
    (hg : (g : Matrix n n D) = Matrix.diagonal (Function.update (1 : n → D) i (d : D))) :
    dieudonneDet g = Group.Abelianization.of d := by
  have h : g = TauCeti.diagGL (Pi.mulSingle i d) := by
    ext a b
    by_cases ha : a = i
    · subst ha
      simp [hg, Matrix.diagonal_apply]
    · simp [hg, Matrix.diagonal_apply, ha]
  rw [h, dieudonneDet_diagGL_mulSingle]

/-- **Uniqueness of the Dieudonné determinant.** Any group homomorphism
`GL n D →* Group.Abelianization Dˣ` that vanishes on `TauCeti.elementarySubgroup n D` and sends
each `diagGL (Pi.mulSingle i d)` to `Group.Abelianization.of d` equals `dieudonneDet`. -/
theorem eq_dieudonneDet_of_elementarySubgroup_le_ker
    (φ : GL n D →* Group.Abelianization Dˣ)
    (hker : TauCeti.elementarySubgroup n D ≤ φ.ker)
    (hdiag : ∀ (i : n) (d : Dˣ),
      φ (TauCeti.diagGL (Pi.mulSingle i d)) = Group.Abelianization.of d) :
    φ = dieudonneDet := by
  ext g
  by_cases hn : Nonempty n
  · obtain ⟨i⟩ := hn
    obtain ⟨e, he, d, rfl⟩ := TauCeti.exists_mem_elementarySubgroup_mul_diagGL_mulSingle g i
    rw [map_mul, map_mul, MonoidHom.mem_ker.1 (hker he),
      dieudonneDet_eq_one_of_mem_elementarySubgroup he, hdiag, dieudonneDet_diagGL_mulSingle]
  · have : IsEmpty n := not_nonempty_iff.1 hn
    have hg : g = 1 := Subsingleton.elim g 1
    simp [hg]

/-- The Dieudonné determinant of a diagonal matrix is the product of the classes of its diagonal
entries. -/
@[simp low]
theorem dieudonneDet_diagGL (t : n → Dˣ) :
    dieudonneDet (TauCeti.diagGL t) = ∏ i : n, Group.Abelianization.of (t i) := by
  suffices ∀ s : Finset n,
      dieudonneDet (TauCeti.diagGL fun j : n ↦ if j ∈ s then t j else 1) =
        ∏ i ∈ s, Group.Abelianization.of (t i) by
    simpa using this Finset.univ
  intro s
  induction s using Finset.induction_on with
  | empty =>
    have h1 : (fun _ : n ↦ (1 : Dˣ)) = 1 := rfl
    simp [h1]
  | insert a s ha ih =>
    have hmul : (fun j : n ↦ if j ∈ insert a s then t j else 1) =
        Pi.mulSingle (M := fun _ : n ↦ Dˣ) a (t a) * fun j : n ↦ if j ∈ s then t j else 1 := by
      ext j
      by_cases hja : j = a
      · subst hja
        simp [ha]
      · simp [hja]
    rw [hmul, map_mul, map_mul, dieudonneDet_diagGL_mulSingle, ih, Finset.prod_insert ha]

/-- The Dieudonné determinant of a scalar matrix `d · 1` is `Group.Abelianization.of d ^ card n`. -/
@[simp]
theorem dieudonneDet_scalar (d : Dˣ) :
    dieudonneDet (scalar n d) = Group.Abelianization.of d ^ Fintype.card n := by
  rw [← TauCeti.diagGL_const, dieudonneDet_diagGL, Finset.prod_const, Finset.card_univ]

/-- The Dieudonné determinant is invariant under relabelling the index type along an equivalence. -/
@[simp]
theorem dieudonneDet_reindexGL (σ : m ≃ n) (g : GL m D) :
    dieudonneDet (σ.reindexGL D g) = dieudonneDet g := by
  have h := eq_dieudonneDet_of_elementarySubgroup_le_ker
    (dieudonneDet.comp (σ.reindexGL D).toMonoidHom)
    (fun e he ↦ dieudonneDet_eq_one_of_mem_elementarySubgroup
      (σ.map_reindexGL_elementarySubgroup (A := D) ▸ ⟨e, he, rfl⟩))
    (fun i d ↦ by
      simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
        TauCeti.reindexGL_diagGL_mulSingle, dieudonneDet_diagGL_mulSingle])
  exact DFunLike.congr_fun h g

/-- The Dieudonné determinant is multiplicative on block diagonal matrices. -/
@[simp]
theorem dieudonneDet_fromBlocksGL (u : GL m D) (v : GL k D) :
    dieudonneDet (TauCeti.fromBlocksGL (u, v)) = dieudonneDet u * dieudonneDet v := by
  have hinl := eq_dieudonneDet_of_elementarySubgroup_le_ker
    (dieudonneDet.comp (TauCeti.fromBlocksGL.comp (MonoidHom.inl (GL m D) (GL k D))))
    (fun e he ↦ dieudonneDet_eq_one_of_mem_elementarySubgroup
      (TauCeti.map_elementarySubgroup_le_elementarySubgroup ⟨e, he, rfl⟩))
    (fun i d ↦ by
      have h : TauCeti.fromBlocksGL (TauCeti.diagGL (Pi.mulSingle i d), (1 : GL k D)) =
          TauCeti.diagGL (Pi.mulSingle (Sum.inl i) d) := by
        ext (a | a) (b | b) <;>
          simp [Matrix.diagonal_apply, Pi.mulSingle_apply, Matrix.one_apply]
      simp only [MonoidHom.comp_apply, MonoidHom.inl_apply, h, dieudonneDet_diagGL_mulSingle])
  have hinr := eq_dieudonneDet_of_elementarySubgroup_le_ker
    (dieudonneDet.comp (TauCeti.fromBlocksGL.comp (MonoidHom.inr (GL m D) (GL k D))))
    (fun e he ↦ dieudonneDet_eq_one_of_mem_elementarySubgroup
      (TauCeti.map_inr_elementarySubgroup_le_elementarySubgroup ⟨e, he, rfl⟩))
    (fun j d ↦ by
      simp only [MonoidHom.comp_apply, MonoidHom.inr_apply,
        TauCeti.fromBlocksGL_one_diagGL_mulSingle, dieudonneDet_diagGL_mulSingle])
  have huv : (u, v) = (u, 1) * (1, v) := by simp
  rw [huv, map_mul, map_mul]
  exact congr_arg₂ (· * ·) (DFunLike.congr_fun hinl u) (DFunLike.congr_fun hinr v)

/-- Upper block unipotent matrices have Dieudonné determinant `1`. -/
@[simp]
theorem dieudonneDet_upperBlockGL (X : Matrix m k D) :
    dieudonneDet (Matrix.upperBlockGL X) = 1 :=
  dieudonneDet_eq_one_of_mem_elementarySubgroup (Matrix.upperBlockGL_mem_elementarySubgroup X)

/-- Lower block unipotent matrices have Dieudonné determinant `1`. -/
@[simp]
theorem dieudonneDet_lowerBlockGL (Y : Matrix k m D) :
    dieudonneDet (Matrix.lowerBlockGL Y) = 1 :=
  dieudonneDet_eq_one_of_mem_elementarySubgroup (Matrix.lowerBlockGL_mem_elementarySubgroup Y)

/-- Stabilization preserves the Dieudonné determinant. -/
@[simp]
theorem dieudonneDet_stabilizeGL {p q : ℕ} (h : p ≤ q) (u : GL (Fin p) D) :
    dieudonneDet (TauCeti.stabilizeGL D h u) = dieudonneDet u := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
  rw [TauCeti.stabilizeGL_eq_reindexGL_fromBlocksGL, dieudonneDet_reindexGL,
    dieudonneDet_fromBlocksGL, map_one, mul_one]

/-- Naturality of the Dieudonné determinant with respect to homomorphisms of division rings. -/
theorem dieudonneDet_mapMatrix {E : Type*} [DivisionRing E] (f : D →+* E) (g : GL n D) :
    dieudonneDet (Units.map (f.mapMatrix (m := n)).toMonoidHom g) =
      Group.Abelianization.map (Units.map f.toMonoidHom) (dieudonneDet g) := by
  by_cases hn : Nonempty n
  · obtain ⟨i⟩ := hn
    obtain ⟨e, he, d, rfl⟩ := TauCeti.exists_mem_elementarySubgroup_mul_diagGL_mulSingle g i
    have hd : Units.map (f.mapMatrix (m := n)).toMonoidHom
        (TauCeti.diagGL (Pi.mulSingle i d)) =
        TauCeti.diagGL (Pi.mulSingle i (Units.map f.toMonoidHom d)) := by
      ext a b
      change f (TauCeti.diagGL (Pi.mulSingle i d) a b) =
        TauCeti.diagGL (Pi.mulSingle i (Units.map f.toMonoidHom d)) a b
      rw [TauCeti.diagGL_apply, TauCeti.diagGL_apply]
      by_cases hab : a = b
      · subst hab
        by_cases hai : a = i
        · subst hai; simp
        · simp [hai]
      · simp [hab]
    rw [map_mul, map_mul, map_mul,
      dieudonneDet_eq_one_of_mem_elementarySubgroup
        (TauCeti.mapMatrix_elementarySubgroup_le f ⟨e, he, rfl⟩),
      dieudonneDet_eq_one_of_mem_elementarySubgroup he, one_mul, one_mul,
      hd, dieudonneDet_diagGL_mulSingle, dieudonneDet_diagGL_mulSingle,
      Group.Abelianization.map_of]
  · have : IsEmpty n := not_nonempty_iff.1 hn
    rw [Subsingleton.elim g 1]
    simp

/-- When `n` is nonempty, the Dieudonné determinant is surjective. -/
theorem dieudonneDet_surjective [Nonempty n] :
    Function.Surjective (dieudonneDet (n := n) (D := D)) := by
  intro x
  obtain ⟨d, rfl⟩ := QuotientGroup.mk'_surjective _ x
  obtain ⟨i⟩ := ‹Nonempty n›
  exact ⟨TauCeti.diagGL (Pi.mulSingle i d), dieudonneDet_diagGL_mulSingle i d⟩

/-- **Dieudonné's kernel theorem.** When `n` has at least two elements (`[Nontrivial n]`), the
kernel of the Dieudonné determinant on `GL n D` is `TauCeti.elementarySubgroup n D`. -/
theorem ker_dieudonneDet [Nontrivial n] :
    (dieudonneDet (n := n) (D := D)).ker = TauCeti.elementarySubgroup n D := by
  refine le_antisymm ?_ elementarySubgroup_le_ker_dieudonneDet
  intro g hg
  obtain ⟨i, j, hij⟩ := exists_pair_ne n
  obtain ⟨e, he, d, rfl⟩ := TauCeti.exists_mem_elementarySubgroup_mul_diagGL_mulSingle g i
  rw [MonoidHom.mem_ker, map_mul, dieudonneDet_eq_one_of_mem_elementarySubgroup he, one_mul,
    dieudonneDet_diagGL_mulSingle, ← MonoidHom.mem_ker, Group.Abelianization.ker_of] at hg
  let φ : Dˣ →* GL n D :=
    { toFun := fun u ↦ TauCeti.diagGL (Pi.mulSingle i u)
      map_one' := by
        rw [Pi.mulSingle_one, map_one]
      map_mul' := fun u v ↦ by
        rw [← map_mul]
        congr 1
        ext a
        by_cases ha : a = i
        · subst ha; simp
        · simp [ha] }
  have hcomm : commutator Dˣ ≤ (TauCeti.elementarySubgroup n D).comap φ :=
    Subgroup.commutator_le.2 fun u _ v _ ↦
      TauCeti.diagGL_mulSingle_commutatorElement_mem_elementarySubgroup hij u v
  exact mul_mem he (hcomm hg)

end Matrix.GeneralLinearGroup

namespace TauCeti

variable {n : Type*} [Fintype n] [DecidableEq n] {D : Type*} [DivisionRing D]

/-- Over a division ring, the elementary subgroup is normal in `GL n D` whenever `n` has at least
two elements. -/
instance elementarySubgroup_normal_of_divisionRing [Nontrivial n] :
    (elementarySubgroup n D).Normal :=
  Matrix.GeneralLinearGroup.ker_dieudonneDet (n := n) (D := D) ▸
    (Matrix.GeneralLinearGroup.dieudonneDet (n := n) (D := D)).normal_ker

/-- Over a division ring, in size at least three, the elementary subgroup equals the commutator
subgroup of `GL n D`. -/
theorem commutator_eq_elementarySubgroup_of_divisionRing (hn : 3 ≤ Fintype.card n) :
    commutator (GL n D) = elementarySubgroup n D := by
  have : Nontrivial n := Fintype.one_lt_card_iff_nontrivial.1 (by omega)
  refine le_antisymm ?_ (elementarySubgroup_le_commutator hn)
  rw [← Matrix.GeneralLinearGroup.ker_dieudonneDet]
  refine Subgroup.commutator_le.2 fun g _ h _ ↦ ?_
  rw [MonoidHom.mem_ker, commutatorElement_def, map_mul, map_mul, map_mul, map_inv, map_inv]
  calc
    Matrix.GeneralLinearGroup.dieudonneDet g * Matrix.GeneralLinearGroup.dieudonneDet h *
        (Matrix.GeneralLinearGroup.dieudonneDet g)⁻¹ *
        (Matrix.GeneralLinearGroup.dieudonneDet h)⁻¹
      = (Matrix.GeneralLinearGroup.dieudonneDet g *
          (Matrix.GeneralLinearGroup.dieudonneDet g)⁻¹) *
        (Matrix.GeneralLinearGroup.dieudonneDet h *
          (Matrix.GeneralLinearGroup.dieudonneDet h)⁻¹) := by ac_rfl
    _ = 1 := by simp

end TauCeti

namespace Matrix.GeneralLinearGroup

variable {n : Type*} [Fintype n] [DecidableEq n] {D : Type*} [DivisionRing D]

/-- When `n` has at least two elements, the Dieudonné determinant induces a canonical isomorphism
`GL n D ⧸ TauCeti.elementarySubgroup n D ≃* Group.Abelianization Dˣ`. -/
def quotientElementarySubgroupEquivAbelianization [Nontrivial n] :
    GL n D ⧸ TauCeti.elementarySubgroup n D ≃* Group.Abelianization Dˣ :=
  (QuotientGroup.quotientMulEquivOfEq (ker_dieudonneDet (n := n) (D := D)).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective dieudonneDet dieudonneDet_surjective)

/-- Evaluating `quotientElementarySubgroupEquivAbelianization` on the coset of `g` gives
`dieudonneDet g`. -/
@[simp]
theorem quotientElementarySubgroupEquivAbelianization_mk [Nontrivial n] (g : GL n D) :
    quotientElementarySubgroupEquivAbelianization (QuotientGroup.mk g) = dieudonneDet g :=
  (rfl)

/-- Over a field `F`, the Dieudonné determinant agrees with the classical determinant followed by
`Group.Abelianization.of`. -/
@[simp]
theorem dieudonneDet_eq_of_det {F : Type*} [Field F] (g : GL n F) :
    dieudonneDet g = Group.Abelianization.of (det g) := by
  have h := eq_dieudonneDet_of_elementarySubgroup_le_ker
    (Group.Abelianization.of.comp (det (n := n) (R := F)))
    (fun e he ↦ by
      simp [MonoidHom.mem_ker.1 (TauCeti.elementarySubgroup_le_ker_det he)])
    (fun i d ↦ by
      have hd : det (TauCeti.diagGL (Pi.mulSingle (M := fun _ : n ↦ Fˣ) i d)) = d := by
        ext
        simp [Pi.mulSingle_apply]
      simp [hd])
  exact (DFunLike.congr_fun h g).symm

end Matrix.GeneralLinearGroup
