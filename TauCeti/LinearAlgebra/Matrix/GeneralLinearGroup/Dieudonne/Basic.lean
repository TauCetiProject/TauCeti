/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Dieudonne.GaussJordan
import Mathlib.GroupTheory.Perm.Fin

/-!
# The Dieudonné determinant over a division ring

Over a noncommutative division ring `D`, the polynomial determinant no longer defines a group
homomorphism on `GL n D`, because row operations only commute up to commutators of nonzero
scalars. Dieudonné (1943) constructed a canonical replacement valued in the abelianized unit group
`Group.Abelianization Dˣ = Dˣ / [Dˣ, Dˣ]`, sending every elementary matrix to `1` and every
invertible diagonal matrix `diag(d₁, …, dₙ)` to `∏ᵢ Group.Abelianization.of dᵢ`.

This file constructs `Matrix.GeneralLinearGroup.dieudonneDet : GL n D →* Group.Abelianization Dˣ`
for arbitrary finite index types:

* **Inductive Schur-complement construction.** In rank at least two, Whitehead's lemma places
  `[Dˣ, Dˣ]` inside `TauCeti.elementarySubgroup n D`, and Gauss–Jordan factorization gives a
  surjective homomorphism `Group.Abelianization Dˣ →* GL n D ⧸ TauCeti.elementarySubgroup n D`.
  Its injectivity—that a single-entry diagonal matrix `diag(1, …, u)` lies in `E n D` only when
  `Group.Abelianization.of u = 1`—is proved inductively by building a left-transvection-invariant
  map via the Schur complement along a nonzero column-zero pivot and `Fin.cycleRange` pivot
  independence. Inverting the resulting bijection yields `dieudonneDet` without expanding
  `det(A * B)` by hand.
* **Sharpness of rank bounds.** In rank `0`, `dieudonneDet` is trivial. In rank `1`, `E₁(D) = ⊥`
  while the kernel of `GL₁(D) ≃* Dˣ →* Group.Abelianization Dˣ` corresponds to `[Dˣ, Dˣ]`, so the
  hypothesis `2 ≤ Fintype.card n` in `Matrix.GeneralLinearGroup.ker_dieudonneDet` cannot be dropped
  for noncommutative `D`. Conversely, `ker_dieudonneDet` holds even for `GL₂(𝔽₂) ≅ S₃`, where
  `E₂(𝔽₂) = ⊤` while `[GL₂(𝔽₂), GL₂(𝔽₂)]` has index `2`, so the kernel in rank `2` is `Eₙ(D)`
  rather than `[GLₙ(D), GLₙ(D)]` in general.

For stabilization invariance and the induced isomorphism on algebraic `K₁`, see
`TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Dieudonne.AlgebraicK1`.

## Main definitions

* `Matrix.GeneralLinearGroup.dieudonneDet`: the Dieudonné determinant
  `GL n D →* Group.Abelianization Dˣ` over a division ring `D`.
* `TauCeti.quotientElementarySubgroupDieudonneEquiv`: the canonical isomorphism
  `GL n D ⧸ TauCeti.elementarySubgroup n D ≃* Group.Abelianization Dˣ` for `2 ≤ Fintype.card n`.

## Main results

* `Matrix.GeneralLinearGroup.ker_dieudonneDet`: for `2 ≤ Fintype.card n`, the kernel of
  `dieudonneDet` is `TauCeti.elementarySubgroup n D`.
* `Matrix.GeneralLinearGroup.dieudonneDet_diagGL`,
  `Matrix.GeneralLinearGroup.dieudonneDet_permutationGL`,
  `Matrix.GeneralLinearGroup.dieudonneDet_fromBlocksGL`,
  `Matrix.GeneralLinearGroup.dieudonneDet_unitsMap_mapMatrix`: values on diagonal, permutation,
  block-diagonal, and ring-mapped matrices.
* `Matrix.GeneralLinearGroup.eq_dieudonneDet`: characterization of `dieudonneDet` by vanishing on
  `TauCeti.elementarySubgroup n D` and its values on single-entry diagonal matrices.
* `Matrix.GeneralLinearGroup.dieudonneDet_eq_of_det`: over a field, `dieudonneDet` is
  `Group.Abelianization.of ∘ det`.

## References

* J. Dieudonné, *Les déterminants sur un corps non commutatif*, Bull. Soc. Math. France **71**
  (1943), 27–45.
* E. Artin, *Geometric Algebra*, Interscience (1957), Chapter IV, §3–§4.
* J. Rosenberg, *Algebraic K-Theory and Its Applications*, GTM 147 (1994), §2.2.
* C. A. Weibel, *The K-book: An Introduction to Algebraic K-Theory*, GSM 145 (2013), Chapter III,
  Example 1.3.5.
-/

public section

noncomputable section

open Matrix
open scoped commutatorElement

namespace TauCeti

/-! ## Inductive Schur-complement construction on `Fin m` -/

section SchurInduction

variable {D : Type*} [DivisionRing D]

/-- The equivalence `Fin 1 ⊕ Fin m ≃ Fin (m + 1)` sending `inl 0` to `0` and `inr i` to
`i.succ`. -/
private def finOneSumEquiv (m : ℕ) : Fin 1 ⊕ Fin m ≃ Fin (m + 1) :=
  finSumFinEquiv.trans (finCongr (Nat.one_add m))

@[simp]
private theorem finOneSumEquiv_inl (m : ℕ) (i : Fin 1) :
    finOneSumEquiv m (Sum.inl i) = 0 := by
  fin_cases i; ext; simp [finOneSumEquiv]

@[simp]
private theorem finOneSumEquiv_inr (m : ℕ) (i : Fin m) :
    finOneSumEquiv m (Sum.inr i) = i.succ := by
  ext; simp [finOneSumEquiv]

/-- In rank at least two, a commutator of units placed in the last diagonal coordinate lies in the
elementary subgroup. -/
private theorem diagGL_mulSingle_last_commutatorElement_mem (k : ℕ) (u v : Dˣ) :
    diagGL (Pi.mulSingle (Fin.last (k + 1)) ⁅u, v⁆) ∈
      elementarySubgroup (Fin (k + 2)) D := by
  let u₁ : GL (Fin 1) D := diagGL fun _ ↦ u
  let v₁ : GL (Fin 1) D := diagGL fun _ ↦ v
  have hmem₁ : fromBlocksGL (fromBlocksGL (⁅u₁, v₁⁆, (1 : GL (Fin 1) D)), (1 : GL (Fin k) D)) ∈
      elementarySubgroup ((Fin 1 ⊕ Fin 1) ⊕ Fin k) D :=
    map_elementarySubgroup_le_elementarySubgroup
      ⟨_, fromBlocksGL_commutatorElement_mem_elementarySubgroup u₁ v₁, rfl⟩
  let eqv : (Fin 1 ⊕ Fin 1) ⊕ Fin k ≃ Fin (k + 2) :=
    (Equiv.sumAssoc (Fin 1) (Fin 1) (Fin k)).trans
      (((Equiv.refl (Fin 1)).sumCongr (finOneSumEquiv k)).trans
        ((finOneSumEquiv (k + 1)).trans (Equiv.swap 0 (Fin.last (k + 1)))))
  have heqv_inl : eqv (Sum.inl (Sum.inl 0)) = Fin.last (k + 1) := by simp [eqv]
  have hmem₂ : eqv.reindexGL D
      (fromBlocksGL (fromBlocksGL (⁅u₁, v₁⁆, (1 : GL (Fin 1) D)), (1 : GL (Fin k) D))) ∈
      elementarySubgroup (Fin (k + 2)) D := by
    rw [← eqv.map_reindexGL_elementarySubgroup]; exact ⟨_, hmem₁, rfl⟩
  convert hmem₂ using 1
  ext a b
  obtain ⟨a, rfl⟩ := eqv.surjective a
  obtain ⟨b, rfl⟩ := eqv.surjective b
  simp only [diagGL_apply, Equiv.coe_reindexGL, submatrix_apply, Equiv.symm_apply_apply,
    eqv.apply_eq_iff_eq, ← heqv_inl, Pi.mulSingle_apply]
  rcases a with (a | a) | a <;> rcases b with (b | b) | b
  · fin_cases a; fin_cases b; simp [u₁, v₁, ← map_commutatorElement]
  · simp
  · simp
  · simp
  · fin_cases a; fin_cases b; simp
  · simp
  · simp
  · simp
  · simp [Matrix.one_apply]

/-- The canonical surjection
`Group.Abelianization Dˣ →* GL (Fin (k + 2)) D ⧸ E (Fin (k + 2)) D` sending
`Group.Abelianization.of u` to the coset of `diag(1, …, 1, u)`. -/
private def abelianizationToQuotientFin (k : ℕ) :
    Group.Abelianization Dˣ →* GL (Fin (k + 2)) D ⧸ elementarySubgroup (Fin (k + 2)) D :=
  QuotientGroup.lift (commutator Dˣ)
    ((QuotientGroup.mk' (elementarySubgroup (Fin (k + 2)) D)).comp
      (diagGL.comp (MonoidHom.mulSingle (fun _ : Fin (k + 2) ↦ Dˣ) (Fin.last (k + 1)))))
    fun x hx ↦ by
      refine Subgroup.commutator_le.2 (fun u _ v _ ↦ ?_) hx
      rw [MonoidHom.mem_ker, MonoidHom.comp_apply, MonoidHom.comp_apply, MonoidHom.mulSingle_apply,
        QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
      exact diagGL_mulSingle_last_commutatorElement_mem k u v

@[simp]
private theorem abelianizationToQuotientFin_of (k : ℕ) (u : Dˣ) :
    abelianizationToQuotientFin k (Group.Abelianization.of u) =
      QuotientGroup.mk (diagGL (Pi.mulSingle (Fin.last (k + 1)) u)) :=
  rfl

private theorem abelianizationToQuotientFin_surjective (k : ℕ) :
    Function.Surjective (abelianizationToQuotientFin (D := D) k) := by
  intro q
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
  obtain ⟨e, he, u, rfl⟩ :=
    exists_mem_elementarySubgroup_mul_diagGL_mulSingle (Fin.last (k + 1)) g
  refine ⟨Group.Abelianization.of u, ?_⟩
  rw [abelianizationToQuotientFin_of, QuotientGroup.eq]
  have hinv : (diagGL (Pi.mulSingle (Fin.last (k + 1)) u))⁻¹ *
      (e * diagGL (Pi.mulSingle (Fin.last (k + 1)) u)) =
      (diagGL (Pi.mulSingle (Fin.last (k + 1)) u))⁻¹ * e *
        ((diagGL (Pi.mulSingle (Fin.last (k + 1)) u))⁻¹)⁻¹ := by group
  rw [hinv]
  exact elementarySubgroup_normal.conj_mem e he _

/-- The `m × m` Schur complement obtained from `A : Matrix (Fin (m + 1)) (Fin (m + 1)) D` by
eliminating column `0` using pivot row `p`. -/
private def schurBlock {m : ℕ} (A : Matrix (Fin (m + 1)) (Fin (m + 1)) D) (p : Fin (m + 1)) :
    Matrix (Fin m) (Fin m) D :=
  fun r s ↦ A (p.succAbove r) s.succ - A (p.succAbove r) 0 * (A p 0)⁻¹ * A p s.succ

/-- When `A ∈ GL (Fin (m + 1)) D` has `A p 0 ≠ 0`, `schurBlock A p` is invertible in
`Matrix (Fin m) (Fin m) D`. -/
private theorem exists_coe_eq_schurBlock {m : ℕ} (A : GL (Fin (m + 1)) D) (p : Fin (m + 1))
    (hp : A p 0 ≠ 0) : ∃ S : GL (Fin m) D, (S : Matrix (Fin m) (Fin m) D) = schurBlock A p := by
  let d₀ : GL (Fin 1) D := GeneralLinearGroup.scalar (Fin 1) (Units.mk0 (A p 0) hp)⁻¹
  have hd₀ : (d₀ : Matrix (Fin 1) (Fin 1) D) = Matrix.scalar (Fin 1) (A p 0)⁻¹ := by
    rw [GeneralLinearGroup.coe_scalar]; simp
  let B : GL (Fin 1 ⊕ Fin m) D :=
    (finOneSumEquiv m).symm.reindexGL D (permutationGL p.cycleRange * A)
  have hB_11 : (B : Matrix (Fin 1 ⊕ Fin m) (Fin 1 ⊕ Fin m) D).toBlocks₁₁ =
      Matrix.scalar (Fin 1) (A p 0) := by
    ext i j; fin_cases i; fin_cases j; simp [B, Matrix.toBlocks₁₁, Equiv.Perm.inv_def]
  let B₁ : GL (Fin 1 ⊕ Fin m) D := fromBlocksGL (d₀, 1) * B
  have hB₁_blocks : (B₁ : Matrix (Fin 1 ⊕ Fin m) (Fin 1 ⊕ Fin m) D) =
      fromBlocks (Matrix.scalar (Fin 1) (A p 0)⁻¹ *
          (B : Matrix (Fin 1 ⊕ Fin m) (Fin 1 ⊕ Fin m) D).toBlocks₁₁)
        (Matrix.scalar (Fin 1) (A p 0)⁻¹ *
          (B : Matrix (Fin 1 ⊕ Fin m) (Fin 1 ⊕ Fin m) D).toBlocks₁₂)
        (B : Matrix (Fin 1 ⊕ Fin m) (Fin 1 ⊕ Fin m) D).toBlocks₂₁
        (B : Matrix (Fin 1 ⊕ Fin m) (Fin 1 ⊕ Fin m) D).toBlocks₂₂ := by
    have := Units.val_mul (fromBlocksGL (d₀, 1)) B
    rw [coe_fromBlocksGL, hd₀,
      ← Matrix.fromBlocks_toBlocks (B : Matrix (Fin 1 ⊕ Fin m) (Fin 1 ⊕ Fin m) D),
      Matrix.fromBlocks_multiply] at this
    simpa [B₁] using this
  have hB₁_11 : (B₁ : Matrix (Fin 1 ⊕ Fin m) (Fin 1 ⊕ Fin m) D).toBlocks₁₁ = 1 := by
    rw [hB₁_blocks, Matrix.toBlocks_fromBlocks₁₁, hB_11, ← map_mul (Matrix.scalar (Fin 1)),
      inv_mul_cancel₀ hp, map_one]
  let c : Matrix (Fin m) (Fin 1) D := (B₁ : Matrix (Fin 1 ⊕ Fin m) (Fin 1 ⊕ Fin m) D).toBlocks₂₁
  let U : GL (Fin 1 ⊕ Fin m) D := lowerBlockGL (-c) * B₁
  have hU_blocks : (U : Matrix (Fin 1 ⊕ Fin m) (Fin 1 ⊕ Fin m) D) =
      fromBlocks 1 (B₁ : Matrix (Fin 1 ⊕ Fin m) (Fin 1 ⊕ Fin m) D).toBlocks₁₂ 0
        (-c * (B₁ : Matrix (Fin 1 ⊕ Fin m) (Fin 1 ⊕ Fin m) D).toBlocks₁₂ +
          (B₁ : Matrix (Fin 1 ⊕ Fin m) (Fin 1 ⊕ Fin m) D).toBlocks₂₂) := by
    have := Units.val_mul (lowerBlockGL (-c)) B₁
    rw [coe_lowerBlockGL,
      ← Matrix.fromBlocks_toBlocks (B₁ : Matrix (Fin 1 ⊕ Fin m) (Fin 1 ⊕ Fin m) D), hB₁_11,
      Matrix.fromBlocks_multiply] at this
    simpa [U, c] using this
  have hU_11 : (U : Matrix (Fin 1 ⊕ Fin m) (Fin 1 ⊕ Fin m) D).toBlocks₁₁ = 1 := by
    rw [hU_blocks, Matrix.toBlocks_fromBlocks₁₁]
  have hU_21 : (U : Matrix (Fin 1 ⊕ Fin m) (Fin 1 ⊕ Fin m) D).toBlocks₂₁ = 0 := by
    rw [hU_blocks, Matrix.toBlocks_fromBlocks₂₁]
  refine ⟨upperTriangularToBlocks₂₂GL U hU_11 hU_21, ?_⟩
  rw [coe_upperTriangularToBlocks₂₂GL, hU_blocks, Matrix.toBlocks_fromBlocks₂₂]
  dsimp only [c]
  rw [hB₁_blocks, Matrix.toBlocks_fromBlocks₂₁, Matrix.toBlocks_fromBlocks₁₂,
    Matrix.toBlocks_fromBlocks₂₂]
  ext r s
  rw [Matrix.add_apply, Matrix.mul_apply, Fin.sum_univ_one]
  simp [schurBlock, B, Matrix.toBlocks₂₁, Matrix.toBlocks₁₂, Matrix.toBlocks₂₂,
    Matrix.diagonal_mul, Equiv.Perm.inv_def, sub_eq_add_neg, add_comm, mul_assoc]

/-- The Schur complement `schurBlock A p` packaged as an element of `GL (Fin m) D`. -/
private def schurGL {m : ℕ} (A : GL (Fin (m + 1)) D) (p : Fin (m + 1)) (hp : A p 0 ≠ 0) :
    GL (Fin m) D :=
  (exists_coe_eq_schurBlock A p hp).choose

@[simp]
private theorem coe_schurGL {m : ℕ} (A : GL (Fin (m + 1)) D) (p : Fin (m + 1)) (hp : A p 0 ≠ 0) :
    (schurGL A p hp : Matrix (Fin m) (Fin m) D) = schurBlock A p :=
  (exists_coe_eq_schurBlock A p hp).choose_spec

/-- Column-clearing elementary matrix in `GL (Fin (k + 1)) D` adding `w q` times row `p` to each
row `p.succAbove q`. -/
private def colElimGL {k : ℕ} (p : Fin (k + 1)) (w : Fin k → D) : GL (Fin (k + 1)) D :=
  ((finOneSumEquiv k).trans p.cycleRange.symm).reindexGL D
    (lowerBlockGL (Matrix.of fun q _ ↦ w q))

private theorem colElimGL_mem_elementarySubgroup {k : ℕ} (p : Fin (k + 1)) (w : Fin k → D) :
    colElimGL p w ∈ elementarySubgroup (Fin (k + 1)) D := by
  rw [colElimGL, ← ((finOneSumEquiv k).trans p.cycleRange.symm).map_reindexGL_elementarySubgroup]
  exact ⟨_, lowerBlockGL_mem_elementarySubgroup _, rfl⟩

private theorem coe_colElimGL_eqv_apply {k : ℕ} (p : Fin (k + 1)) (w : Fin k → D)
    (a b : Fin 1 ⊕ Fin k) :
    (colElimGL p w : Matrix (Fin (k + 1)) (Fin (k + 1)) D)
      (((finOneSumEquiv k).trans p.cycleRange.symm) a)
      (((finOneSumEquiv k).trans p.cycleRange.symm) b) =
      fromBlocks (1 : Matrix (Fin 1) (Fin 1) D) 0 (Matrix.of fun q _ ↦ w q) 1 a b := by
  have hmat : (colElimGL p w : Matrix (Fin (k + 1)) (Fin (k + 1)) D) =
      (fromBlocks (1 : Matrix (Fin 1) (Fin 1) D) 0 (Matrix.of fun q _ ↦ w q) 1).submatrix
        ((finOneSumEquiv k).trans p.cycleRange.symm).symm
        ((finOneSumEquiv k).trans p.cycleRange.symm).symm := by
    rw [colElimGL, Equiv.coe_reindexGL, coe_lowerBlockGL]
  simpa only [Matrix.submatrix_apply, Equiv.symm_apply_apply] using
    congrFun (congrFun hmat (((finOneSumEquiv k).trans p.cycleRange.symm) a))
      (((finOneSumEquiv k).trans p.cycleRange.symm) b)

private theorem coe_colElimGL_mul_apply_self {k : ℕ} (p : Fin (k + 1)) (w : Fin k → D)
    (M : Matrix (Fin (k + 1)) (Fin (k + 1)) D) (s : Fin (k + 1)) :
    ((colElimGL p w : Matrix (Fin (k + 1)) (Fin (k + 1)) D) * M) p s = M p s := by
  let eqv : Fin 1 ⊕ Fin k ≃ Fin (k + 1) := (finOneSumEquiv k).trans p.cycleRange.symm
  have hp_eq : eqv (Sum.inl 0) = p := by simp [eqv]
  have hmain : ((colElimGL p w : Matrix (Fin (k + 1)) (Fin (k + 1)) D) * M) (eqv (Sum.inl 0)) s =
      M (eqv (Sum.inl 0)) s := by
    rw [Matrix.mul_apply, ← eqv.sum_comp]
    have hterm (x : Fin 1 ⊕ Fin k) :
        (colElimGL p w : Matrix _ _ D) (eqv (Sum.inl 0)) (eqv x) * M (eqv x) s =
          if x = Sum.inl 0 then M (eqv (Sum.inl 0)) s else 0 := by
      dsimp only [eqv]; rw [coe_colElimGL_eqv_apply]
      rcases x with x | x
      · fin_cases x; simp
      · simp
    simp [hterm]
  simpa only [hp_eq] using hmain

private theorem coe_colElimGL_mul_apply_succAbove {k : ℕ} (p : Fin (k + 1)) (w : Fin k → D)
    (M : Matrix (Fin (k + 1)) (Fin (k + 1)) D) (q : Fin k) (s : Fin (k + 1)) :
    ((colElimGL p w : Matrix (Fin (k + 1)) (Fin (k + 1)) D) * M) (p.succAbove q) s =
      M (p.succAbove q) s + w q * M p s := by
  let eqv : Fin 1 ⊕ Fin k ≃ Fin (k + 1) := (finOneSumEquiv k).trans p.cycleRange.symm
  have hq_eq : eqv (Sum.inr q) = p.succAbove q := by simp [eqv]
  have hp_eq : eqv (Sum.inl 0) = p := by simp [eqv]
  have hmain : ((colElimGL p w : Matrix (Fin (k + 1)) (Fin (k + 1)) D) * M) (eqv (Sum.inr q)) s =
      M (eqv (Sum.inr q)) s + w q * M (eqv (Sum.inl 0)) s := by
    rw [Matrix.mul_apply, ← eqv.sum_comp, Fintype.sum_sum_type]
    have hleft : ∑ x : Fin 1,
        (colElimGL p w : Matrix _ _ D) (eqv (Sum.inr q)) (eqv (Sum.inl x)) *
          M (eqv (Sum.inl x)) s = w q * M (eqv (Sum.inl 0)) s := by
      rw [Fin.sum_univ_one]; dsimp only [eqv]; rw [coe_colElimGL_eqv_apply]; simp
    have hright : ∑ x : Fin k,
        (colElimGL p w : Matrix _ _ D) (eqv (Sum.inr q)) (eqv (Sum.inr x)) *
          M (eqv (Sum.inr x)) s = M (eqv (Sum.inr q)) s := by
      rw [Fintype.sum_eq_single q]
      · dsimp only [eqv]; rw [coe_colElimGL_eqv_apply]; simp
      · intro x hx; dsimp only [eqv]; rw [coe_colElimGL_eqv_apply]; simp [Ne.symm hx]
    rw [hleft, hright, add_comm]
  simpa only [hq_eq, hp_eq] using hmain

/-- Any homomorphism on `GL n D` that kills transvections and sends `diagGL d` to
`∏ i, Group.Abelianization.of (d i)` sends `permutationGL σ` to the cast of
`Equiv.Perm.sign σ`. -/
private theorem map_permutationGL_of_ih {n : Type*} [Fintype n] [DecidableEq n]
    (f : GL n D →* Group.Abelianization Dˣ)
    (hf_transv : ∀ {i j : n} (hij : i ≠ j) (c : D), f (transvectionUnit hij c) = 1)
    (hf_diag : ∀ d : n → Dˣ, f (diagGL d) = ∏ i, Group.Abelianization.of (d i))
    (σ : Equiv.Perm n) :
    f (permutationGL (k := D) σ) =
      Group.Abelianization.of
        (Units.map (Int.castRingHom D).toMonoidHom (Equiv.Perm.sign σ)) := by
  induction σ using Equiv.Perm.swap_induction_on with
  | one => simp
  | swap_mul τ i j hij ih =>
    have hneg1 : Units.map (Int.castRingHom D).toMonoidHom (-1 : ℤˣ) = -1 := Units.ext (by simp)
    rw [map_mul, map_mul, ih, ← diagGL_mul_transvectionWeylElement_eq_permutationGL_swap hij,
      map_mul, hf_diag, Fintype.prod_eq_single j (fun x hx ↦ by simp [Pi.mulSingle_eq_of_ne hx]),
      Pi.mulSingle_eq_same, transvectionWeylElement_def, map_mul, map_mul,
      hf_transv, hf_transv, mul_one, mul_one, mul_one, map_mul, Equiv.Perm.sign_swap hij, map_mul,
      hneg1, Group.Abelianization.of.map_mul]

/-- Candidate Dieudonné value of `A ∈ GL (Fin (m + 1)) D` computed using pivot row `p`. -/
private def pivotVal {m : ℕ} (f : GL (Fin m) D →* Group.Abelianization Dˣ)
    (A : GL (Fin (m + 1)) D) (p : Fin (m + 1)) (hp : A p 0 ≠ 0) : Group.Abelianization Dˣ :=
  Group.Abelianization.of ((-1 : Dˣ) ^ (p : ℕ) * Units.mk0 (A p 0) hp) * f (schurGL A p hp)

/-- Off-pivot transvection invariance: left-multiplying `A` by `transvectionUnit hij c` with
`i ≠ p` leaves `pivotVal` at `p` unchanged. -/
private theorem pivotVal_transvectionUnit_mul_of_ne {m : ℕ}
    (f : GL (Fin m) D →* Group.Abelianization Dˣ)
    (hf_transv : ∀ {i j : Fin m} (hij : i ≠ j) (c : D), f (transvectionUnit hij c) = 1)
    (A : GL (Fin (m + 1)) D) {i j p : Fin (m + 1)} (hij : i ≠ j) (hip : i ≠ p) (c : D)
    (hp : A p 0 ≠ 0) :
    pivotVal f (transvectionUnit hij c * A) p
      (by rw [transvectionUnit_mul_apply]; simpa [hip.symm] using hp) =
      pivotVal f A p hp := by
  have hp' : (transvectionUnit hij c * A : GL (Fin (m + 1)) D) p 0 ≠ 0 := by
    rw [transvectionUnit_mul_apply]; simpa [hip.symm] using hp
  have hp_eq : (transvectionUnit hij c * A : GL (Fin (m + 1)) D) p 0 = A p 0 := by
    rw [transvectionUnit_mul_apply]; simp [hip.symm]
  have hu_eq : Units.mk0 ((transvectionUnit hij c * A : GL (Fin (m + 1)) D) p 0) hp' =
      Units.mk0 (A p 0) hp := Units.ext hp_eq
  simp only [pivotVal, hu_eq]; congr 1
  obtain ⟨i₀, rfl⟩ := Fin.exists_succAbove_eq hip
  by_cases hjp : j = p
  · subst hjp; congr 1; apply Units.ext; ext r s
    simp only [coe_schurGL, schurBlock]
    rw [transvectionUnit_mul_apply, transvectionUnit_mul_apply,
      transvectionUnit_mul_apply, transvectionUnit_mul_apply]
    simp only [hip.symm, ite_false, add_zero]
    by_cases hri : r = i₀
    · subst hri; simp only [ite_true]
      rw [add_mul, add_mul, mul_assoc c (A j 0) (A j 0)⁻¹, mul_inv_cancel₀ hp, mul_one]; abel
    · simp [Fin.succAbove_right_injective.ne hri]
  · obtain ⟨j₀, rfl⟩ := Fin.exists_succAbove_eq hjp
    have hi₀j₀ : i₀ ≠ j₀ := fun h ↦ hij (congrArg p.succAbove h)
    have hschur : schurGL (transvectionUnit hij c * A) p hp' =
        transvectionUnit hi₀j₀ c * schurGL A p hp := by
      apply Units.ext; ext r s
      rw [transvectionUnit_mul_apply]
      simp only [coe_schurGL, schurBlock]
      rw [transvectionUnit_mul_apply, transvectionUnit_mul_apply,
        transvectionUnit_mul_apply, transvectionUnit_mul_apply]
      simp only [hip.symm, ite_false, add_zero]
      by_cases hri : r = i₀
      · subst hri; simp only [ite_true]
        rw [add_mul, add_mul, mul_assoc c, mul_assoc c, mul_sub]; abel
      · simp [hri, Fin.succAbove_right_injective.ne hri]
    rw [hschur, map_mul, hf_transv, one_mul]

/-- Sole-pivot transvection invariance: when `A r 0 = 0` for all `r ≠ i`, left-multiplying by
`transvectionUnit hij c` leaves `pivotVal` at `i` unchanged. -/
private theorem pivotVal_transvectionUnit_mul_of_forall_eq_zero {m : ℕ}
    (f : GL (Fin m) D →* Group.Abelianization Dˣ)
    (A : GL (Fin (m + 1)) D) {i j : Fin (m + 1)} (hij : i ≠ j) (c : D)
    (hzero : ∀ r : Fin (m + 1), r ≠ i → A r 0 = 0) (hi : A i 0 ≠ 0) :
    pivotVal f (transvectionUnit hij c * A) i
      (by rw [transvectionUnit_mul_apply]; simpa [hzero j hij.symm] using hi) =
      pivotVal f A i hi := by
  have hj0 : A j 0 = 0 := hzero j hij.symm
  have hi' : (transvectionUnit hij c * A : GL (Fin (m + 1)) D) i 0 ≠ 0 := by
    rw [transvectionUnit_mul_apply]; simpa [hj0] using hi
  have hi_eq : (transvectionUnit hij c * A : GL (Fin (m + 1)) D) i 0 = A i 0 := by
    rw [transvectionUnit_mul_apply]; simp [hj0]
  have hu_eq : Units.mk0 ((transvectionUnit hij c * A : GL (Fin (m + 1)) D) i 0) hi' =
      Units.mk0 (A i 0) hi := Units.ext hi_eq
  simp only [pivotVal, hu_eq]; congr 2; apply Units.ext; ext r s
  have hr_ne : i.succAbove r ≠ i := Fin.succAbove_ne i r
  simp only [coe_schurGL, schurBlock]
  rw [transvectionUnit_mul_apply, transvectionUnit_mul_apply,
    transvectionUnit_mul_apply, transvectionUnit_mul_apply]
  simp [hr_ne, hzero _ hr_ne]

/-- Explicit matrix relation between the Schur complements of `A ∈ GL (Fin (k + 2)) D` at pivot `0`
and at pivot `p.succ`. -/
private theorem schurGL_zero_eq_mul_schurGL_succ {k : ℕ} (A : GL (Fin (k + 2)) D) (p : Fin (k + 1))
    (h0 : A 0 0 ≠ 0) (hp : A p.succ 0 ≠ 0) :
    schurGL A 0 h0 =
      diagGL (Pi.mulSingle p (-Units.mk0 (A p.succ 0) hp * (Units.mk0 (A 0 0) h0)⁻¹)) *
        colElimGL p (fun q ↦ -A (p.succAbove q).succ 0 * (A 0 0)⁻¹) *
        permutationGL (k := D) (Fin.cycleRange p)⁻¹ * schurGL A p.succ hp := by
  symm
  let cr : Equiv.Perm (Fin (k + 1)) := Fin.cycleRange p
  apply Units.ext; ext j s
  simp only [Units.val_mul, diagGL_coe, Matrix.diagonal_mul, mul_assoc]
  by_cases hjp : j = p
  · rw [hjp, Pi.mulSingle_eq_same, coe_colElimGL_mul_apply_self, coe_permutationGL_mul_apply]
    have hcr : cr⁻¹.symm p = p.cycleRange p := rfl
    have hswap : p.succ.succAbove (p.cycleRange p) = 0 := by
      rw [Fin.succAbove_cycleRange, Equiv.swap_apply_right]
    rw [hcr]; simp only [coe_schurGL, schurBlock, Fin.zero_succAbove]; rw [hswap]
    simp only [Units.val_mul, Units.val_neg, Units.val_mk0, Units.val_inv_eq_inv_val]
    have hy_cancel : A p.succ 0 * (A 0 0)⁻¹ * (A 0 0) * (A p.succ 0)⁻¹ = 1 := by
      rw [mul_assoc (A p.succ 0), inv_mul_cancel₀ h0, mul_one, mul_inv_cancel₀ hp]
    calc
      (-A p.succ 0 * (A 0 0)⁻¹) * (A 0 s.succ - A 0 0 * (A p.succ 0)⁻¹ * A p.succ s.succ)
        = -(A p.succ 0 * (A 0 0)⁻¹ * A 0 s.succ) +
            (A p.succ 0 * (A 0 0)⁻¹ * (A 0 0) * (A p.succ 0)⁻¹) * A p.succ s.succ := by
          noncomm_ring
      _ = A p.succ s.succ - A p.succ 0 * (A 0 0)⁻¹ * A 0 s.succ := by
          rw [hy_cancel, one_mul, sub_eq_add_neg, add_comm]
  · obtain ⟨q, rfl⟩ := Fin.exists_succAbove_eq hjp
    rw [Pi.mulSingle_eq_of_ne hjp, Units.val_one, one_mul, coe_colElimGL_mul_apply_succAbove,
      coe_permutationGL_mul_apply, coe_permutationGL_mul_apply]
    have hcr1 : cr⁻¹.symm (p.succAbove q) = p.cycleRange (p.succAbove q) := rfl
    have hcr2 : cr⁻¹.symm p = p.cycleRange p := rfl
    have hswap_q : p.succ.succAbove (p.cycleRange (p.succAbove q)) = (p.succAbove q).succ := by
      rw [Fin.succAbove_cycleRange, Equiv.swap_apply_of_ne_of_ne (Fin.succ_ne_zero _)
        ((Fin.succ_injective _).ne hjp)]
    have hswap_p : p.succ.succAbove (p.cycleRange p) = 0 := by
      rw [Fin.succAbove_cycleRange, Equiv.swap_apply_right]
    rw [hcr1, hcr2]; simp only [coe_schurGL, schurBlock, Fin.zero_succAbove]; rw [hswap_q, hswap_p]
    have hx_cancel :
        A (p.succAbove q).succ 0 * (A 0 0)⁻¹ * (A 0 0) * (A p.succ 0)⁻¹ =
          A (p.succAbove q).succ 0 * (A p.succ 0)⁻¹ := by
      rw [mul_assoc (A (p.succAbove q).succ 0), inv_mul_cancel₀ h0, mul_one]
    calc
      (A (p.succAbove q).succ s.succ -
          A (p.succAbove q).succ 0 * (A p.succ 0)⁻¹ * A p.succ s.succ) +
        (-A (p.succAbove q).succ 0 * (A 0 0)⁻¹) *
          (A 0 s.succ - A 0 0 * (A p.succ 0)⁻¹ * A p.succ s.succ)
        = A (p.succAbove q).succ s.succ -
            A (p.succAbove q).succ 0 * (A p.succ 0)⁻¹ * A p.succ s.succ -
            A (p.succAbove q).succ 0 * (A 0 0)⁻¹ * A 0 s.succ +
            (A (p.succAbove q).succ 0 * (A 0 0)⁻¹ * (A 0 0) * (A p.succ 0)⁻¹) *
              A p.succ s.succ := by noncomm_ring
      _ = A (p.succAbove q).succ s.succ -
            A (p.succAbove q).succ 0 * (A 0 0)⁻¹ * A 0 s.succ := by rw [hx_cancel]; abel

/-- Pivot comparison between row `0` and row `p.succ` in `GL (Fin (k + 2)) D`. -/
private theorem pivotVal_zero_eq_pivotVal_succ {k : ℕ}
    (f : GL (Fin (k + 1)) D →* Group.Abelianization Dˣ)
    (hf_transv : ∀ {i j : Fin (k + 1)} (hij : i ≠ j) (c : D), f (transvectionUnit hij c) = 1)
    (hf_diag : ∀ d : Fin (k + 1) → Dˣ, f (diagGL d) = ∏ i, Group.Abelianization.of (d i))
    (A : GL (Fin (k + 2)) D) (p : Fin (k + 1)) (h0 : A 0 0 ≠ 0) (hp : A p.succ 0 ≠ 0) :
    pivotVal f A 0 h0 = pivotVal f A p.succ hp := by
  have hf_ker : elementarySubgroup (Fin (k + 1)) D ≤ f.ker :=
    elementarySubgroup_le_iff.2 fun _ _ hij c ↦ hf_transv hij c
  let ux : Dˣ := Units.mk0 (A 0 0) h0
  let uy : Dˣ := Units.mk0 (A p.succ 0) hp
  let cr : Equiv.Perm (Fin (k + 1)) := Fin.cycleRange p
  have hf_rel := congrArg f (schurGL_zero_eq_mul_schurGL_succ A p h0 hp)
  rw [map_mul, map_mul, map_mul, hf_diag,
    Fintype.prod_eq_single p (fun x hx ↦ by simp [Pi.mulSingle_eq_of_ne hx]),
    Pi.mulSingle_eq_same, hf_ker (colElimGL_mem_elementarySubgroup p _), mul_one,
    map_permutationGL_of_ih f hf_transv hf_diag] at hf_rel
  have hsign : Units.map (Int.castRingHom D).toMonoidHom (Equiv.Perm.sign cr⁻¹) =
      (-1 : Dˣ) ^ (p : ℕ) := by rw [map_inv, Fin.sign_cycleRange]; ext; simp
  rw [hsign] at hf_rel
  rw [pivotVal, pivotVal, hf_rel, Fin.val_zero, pow_zero, one_mul, Fin.val_succ, ← mul_assoc]
  refine congrArg (· * f (schurGL A p.succ hp)) ?_
  have hneg : (-uy * ux⁻¹ : Dˣ) = (-1 : Dˣ) * uy * ux⁻¹ := Units.ext (by simp)
  dsimp only [ux, uy] at hneg ⊢
  rw [← mul_assoc, hneg, pow_succ, Group.Abelianization.of.map_mul,
    Group.Abelianization.of.map_mul, Group.Abelianization.of.map_inv,
    Group.Abelianization.of.map_mul, Group.Abelianization.of.map_mul]
  calc
    Group.Abelianization.of (Units.mk0 (A 0 0) h0) *
        (Group.Abelianization.of (-1 : Dˣ) *
          Group.Abelianization.of (Units.mk0 (A p.succ 0) hp) *
          (Group.Abelianization.of (Units.mk0 (A 0 0) h0))⁻¹) *
        Group.Abelianization.of ((-1 : Dˣ) ^ (p : ℕ))
      = Group.Abelianization.of ((-1 : Dˣ) ^ (p : ℕ)) * Group.Abelianization.of (-1 : Dˣ) *
          Group.Abelianization.of (Units.mk0 (A p.succ 0) hp) *
          (Group.Abelianization.of (Units.mk0 (A 0 0) h0) *
            (Group.Abelianization.of (Units.mk0 (A 0 0) h0))⁻¹) := by ac_rfl
    _ = Group.Abelianization.of ((-1 : Dˣ) ^ (p : ℕ)) * Group.Abelianization.of (-1 : Dˣ) *
          Group.Abelianization.of (Units.mk0 (A p.succ 0) hp) := by rw [mul_inv_cancel, mul_one]

/-- **Pivot independence.** For any two nonzero entries in column `0` of `A ∈ GL (Fin (k + 2)) D`,
`pivotVal` yields the same element of `Group.Abelianization Dˣ`. -/
private theorem pivotVal_eq_pivotVal {k : ℕ}
    (f : GL (Fin (k + 1)) D →* Group.Abelianization Dˣ)
    (hf_transv : ∀ {i j : Fin (k + 1)} (hij : i ≠ j) (c : D), f (transvectionUnit hij c) = 1)
    (hf_diag : ∀ d : Fin (k + 1) → Dˣ, f (diagGL d) = ∏ i, Group.Abelianization.of (d i))
    (A : GL (Fin (k + 2)) D) {p₁ p₂ : Fin (k + 2)} (hp₁ : A p₁ 0 ≠ 0) (hp₂ : A p₂ 0 ≠ 0) :
    pivotVal f A p₁ hp₁ = pivotVal f A p₂ hp₂ := by
  have haux (B : GL (Fin (k + 2)) D) (hB0 : B 0 0 ≠ 0) (p : Fin (k + 2)) (hp : B p 0 ≠ 0) :
      pivotVal f B 0 hB0 = pivotVal f B p hp :=
    Fin.cases (by simp) (fun q hq ↦ pivotVal_zero_eq_pivotVal_succ f hf_transv hf_diag B q hB0 hq)
      p hp
  by_cases hA0 : A 0 0 ≠ 0
  · exact (haux A hA0 p₁ hp₁).symm.trans (haux A hA0 p₂ hp₂)
  push Not at hA0
  have hp₁0 : (0 : Fin (k + 2)) ≠ p₁ := fun h ↦ hp₁ (h ▸ hA0)
  have hp₂0 : (0 : Fin (k + 2)) ≠ p₂ := fun h ↦ hp₂ (h ▸ hA0)
  let A' : GL (Fin (k + 2)) D := transvectionUnit hp₁0 1 * A
  have hA'0 : A' 0 0 ≠ 0 := by
    dsimp only [A']; rw [transvectionUnit_mul_apply]; simpa [hA0] using hp₁
  have hA'p₁ : A' p₁ 0 ≠ 0 := by
    dsimp only [A']; rw [transvectionUnit_mul_apply]; simpa [hp₁0.symm] using hp₁
  have hA'p₂ : A' p₂ 0 ≠ 0 := by
    dsimp only [A']; rw [transvectionUnit_mul_apply]; simpa [hp₂0.symm] using hp₂
  calc
    pivotVal f A p₁ hp₁ = pivotVal f A' p₁ hA'p₁ :=
      (pivotVal_transvectionUnit_mul_of_ne f hf_transv A hp₁0 hp₁0 1 hp₁).symm
    _ = pivotVal f A' 0 hA'0 := (haux A' hA'0 p₁ hA'p₁).symm
    _ = pivotVal f A' p₂ hA'p₂ := haux A' hA'0 p₂ hA'p₂
    _ = pivotVal f A p₂ hp₂ := pivotVal_transvectionUnit_mul_of_ne f hf_transv A hp₁0 hp₂0 1 hp₂

/-- Bare pivot-independent Dieudonné map on `GL (Fin (k + 2)) D` induced by `f` on
`GL (Fin (k + 1)) D`. -/
private def bareDieudonne {k : ℕ} (f : GL (Fin (k + 1)) D →* Group.Abelianization Dˣ)
    (A : GL (Fin (k + 2)) D) : Group.Abelianization Dˣ :=
  pivotVal f A (Classical.choose (exists_apply_ne_zero_col A 0))
    (Classical.choose_spec (exists_apply_ne_zero_col A 0))

private theorem bareDieudonne_eq_pivotVal {k : ℕ}
    (f : GL (Fin (k + 1)) D →* Group.Abelianization Dˣ)
    (hf_transv : ∀ {i j : Fin (k + 1)} (hij : i ≠ j) (c : D), f (transvectionUnit hij c) = 1)
    (hf_diag : ∀ d : Fin (k + 1) → Dˣ, f (diagGL d) = ∏ i, Group.Abelianization.of (d i))
    (A : GL (Fin (k + 2)) D) (p : Fin (k + 2)) (hp : A p 0 ≠ 0) :
    bareDieudonne f A = pivotVal f A p hp :=
  pivotVal_eq_pivotVal f hf_transv hf_diag A _ hp

private theorem bareDieudonne_transvectionUnit_mul {k : ℕ}
    (f : GL (Fin (k + 1)) D →* Group.Abelianization Dˣ)
    (hf_transv : ∀ {i j : Fin (k + 1)} (hij : i ≠ j) (c : D), f (transvectionUnit hij c) = 1)
    (hf_diag : ∀ d : Fin (k + 1) → Dˣ, f (diagGL d) = ∏ i, Group.Abelianization.of (d i))
    {i j : Fin (k + 2)} (hij : i ≠ j) (c : D) (A : GL (Fin (k + 2)) D) :
    bareDieudonne f (transvectionUnit hij c * A) = bareDieudonne f A := by
  by_cases hex : ∃ p : Fin (k + 2), p ≠ i ∧ A p 0 ≠ 0
  · obtain ⟨p, hpi, hp⟩ := hex
    have hp' : (transvectionUnit hij c * A : GL (Fin (k + 2)) D) p 0 ≠ 0 := by
      rw [transvectionUnit_mul_apply]; simpa [hpi] using hp
    rw [bareDieudonne_eq_pivotVal f hf_transv hf_diag _ p hp',
      bareDieudonne_eq_pivotVal f hf_transv hf_diag A p hp]
    exact pivotVal_transvectionUnit_mul_of_ne f hf_transv A hij hpi.symm c hp
  · push Not at hex
    obtain ⟨p, hp⟩ := exists_apply_ne_zero_col A 0
    have hpi : p = i := by by_contra hne; exact hp (hex p hne)
    subst hpi
    have hp' : (transvectionUnit hij c * A : GL (Fin (k + 2)) D) p 0 ≠ 0 := by
      rw [transvectionUnit_mul_apply]; simpa [hex j hij.symm] using hp
    rw [bareDieudonne_eq_pivotVal f hf_transv hf_diag _ p hp',
      bareDieudonne_eq_pivotVal f hf_transv hf_diag A p hp]
    exact pivotVal_transvectionUnit_mul_of_forall_eq_zero f A hij c hex hp

private theorem bareDieudonne_elementary_mul {k : ℕ}
    (f : GL (Fin (k + 1)) D →* Group.Abelianization Dˣ)
    (hf_transv : ∀ {i j : Fin (k + 1)} (hij : i ≠ j) (c : D), f (transvectionUnit hij c) = 1)
    (hf_diag : ∀ d : Fin (k + 1) → Dˣ, f (diagGL d) = ∏ i, Group.Abelianization.of (d i))
    {e : GL (Fin (k + 2)) D} (he : e ∈ elementarySubgroup (Fin (k + 2)) D)
    (A : GL (Fin (k + 2)) D) :
    bareDieudonne f (e * A) = bareDieudonne f A := by
  rw [elementarySubgroup_def] at he
  induction he using Subgroup.closure_induction generalizing A with
  | mem x hx =>
    obtain ⟨i, j, hij, c, rfl⟩ := hx
    exact bareDieudonne_transvectionUnit_mul f hf_transv hf_diag hij c A
  | one => simp
  | mul x y _ _ ihx ihy => rw [mul_assoc, ihx, ihy]
  | inv x _ ih => rw [← ih (x⁻¹ * A), mul_inv_cancel_left]

private theorem bareDieudonne_diagGL {k : ℕ}
    (f : GL (Fin (k + 1)) D →* Group.Abelianization Dˣ)
    (hf_transv : ∀ {i j : Fin (k + 1)} (hij : i ≠ j) (c : D), f (transvectionUnit hij c) = 1)
    (hf_diag : ∀ d : Fin (k + 1) → Dˣ, f (diagGL d) = ∏ i, Group.Abelianization.of (d i))
    (d : Fin (k + 2) → Dˣ) :
    bareDieudonne f (diagGL d) = ∏ i, Group.Abelianization.of (d i) := by
  have h0 : (diagGL d : GL (Fin (k + 2)) D) 0 0 ≠ 0 := by simp
  rw [bareDieudonne_eq_pivotVal f hf_transv hf_diag (diagGL d) 0 h0, pivotVal]
  have hu0 : Units.mk0 ((diagGL d : GL (Fin (k + 2)) D) 0 0) h0 = d 0 := Units.ext (by simp)
  have hschur : schurGL (diagGL d) 0 h0 = diagGL (fun i ↦ d i.succ) := by
    apply Units.ext; ext r s
    simp [coe_schurGL, schurBlock, diagGL_apply, Fin.zero_succAbove, Fin.succ_ne_zero]
  rw [Fin.val_zero, pow_zero, one_mul, hu0, hschur, hf_diag]
  conv_rhs => rw [Fin.prod_univ_succ]

/-- Packaged inductive Dieudonné homomorphism on `GL (Fin m) D` together with its values on
transvections and diagonal matrices and its kernel in rank at least two. -/
private structure DieudonneFinData (D : Type*) [DivisionRing D] (m : ℕ) where
  hom : GL (Fin m) D →* Group.Abelianization Dˣ
  map_transvection : ∀ {i j : Fin m} (hij : i ≠ j) (c : D), hom (transvectionUnit hij c) = 1
  map_diag : ∀ d : Fin m → Dˣ, hom (diagGL d) = ∏ i, Group.Abelianization.of (d i)
  ker_eq : 2 ≤ m → hom.ker = elementarySubgroup (Fin m) D

private theorem abelianizationToQuotientFin_injective {k : ℕ}
    (prev : DieudonneFinData D (k + 1)) :
    Function.Injective (abelianizationToQuotientFin (D := D) k) := by
  refine (MonoidHom.ker_eq_bot_iff _).1 ((Subgroup.eq_bot_iff_forall _).2 fun x hx ↦ ?_)
  rw [MonoidHom.mem_ker] at hx
  refine QuotientGroup.induction_on x (fun u hu ↦ ?_) hx
  have hmk : (QuotientGroup.mk u : Group.Abelianization Dˣ) = Group.Abelianization.of u := rfl
  rw [hmk] at hu ⊢
  rw [abelianizationToQuotientFin_of, QuotientGroup.eq_one_iff] at hu
  have h1 : bareDieudonne prev.hom (diagGL (Pi.mulSingle (Fin.last (k + 1)) u)) =
      bareDieudonne prev.hom 1 := by
    simpa using bareDieudonne_elementary_mul prev.hom prev.map_transvection prev.map_diag hu 1
  have hval_u : bareDieudonne prev.hom (diagGL (Pi.mulSingle (Fin.last (k + 1)) u)) =
      Group.Abelianization.of u := by
    rw [bareDieudonne_diagGL prev.hom prev.map_transvection prev.map_diag,
      Fintype.prod_eq_single (Fin.last (k + 1))
        (fun i hi ↦ by simp [Pi.mulSingle_eq_of_ne hi]),
      Pi.mulSingle_eq_same]
  have hval_one : bareDieudonne prev.hom 1 = 1 := by
    rw [← map_one diagGL, bareDieudonne_diagGL prev.hom prev.map_transvection prev.map_diag]
    simp
  rwa [hval_u, hval_one] at h1

private def dieudonneFinSuccSucc {k : ℕ} (prev : DieudonneFinData D (k + 1)) :
    DieudonneFinData D (k + 2) :=
  let bij := MulEquiv.ofBijective (abelianizationToQuotientFin (D := D) k)
    ⟨abelianizationToQuotientFin_injective prev, abelianizationToQuotientFin_surjective k⟩
  let φ : GL (Fin (k + 2)) D →* Group.Abelianization Dˣ :=
    bij.symm.toMonoidHom.comp (QuotientGroup.mk' (elementarySubgroup (Fin (k + 2)) D))
  have hφ_eq_bare (A : GL (Fin (k + 2)) D) : φ A = bareDieudonne prev.hom A := by
    obtain ⟨e, he, u, rfl⟩ :=
      exists_mem_elementarySubgroup_mul_diagGL_mulSingle (Fin.last (k + 1)) A
    have hmk : QuotientGroup.mk' (elementarySubgroup (Fin (k + 2)) D)
        (e * diagGL (Pi.mulSingle (Fin.last (k + 1)) u)) =
        abelianizationToQuotientFin k (Group.Abelianization.of u) := by
      rw [map_mul, QuotientGroup.mk'_apply, (QuotientGroup.eq_one_iff e).2 he, one_mul,
        abelianizationToQuotientFin_of, QuotientGroup.mk'_apply]
    have hφ_lhs :
        φ (e * diagGL (Pi.mulSingle (Fin.last (k + 1)) u)) = Group.Abelianization.of u := by
      dsimp only [φ]
      rw [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, hmk]
      exact bij.symm_apply_apply (Group.Abelianization.of u)
    rw [hφ_lhs, bareDieudonne_elementary_mul prev.hom prev.map_transvection prev.map_diag he,
      bareDieudonne_diagGL prev.hom prev.map_transvection prev.map_diag,
      Fintype.prod_eq_single (Fin.last (k + 1))
        (fun i hi ↦ by simp [Pi.mulSingle_eq_of_ne hi]),
      Pi.mulSingle_eq_same]
  { hom := φ
    map_transvection := fun hij c ↦ by
      dsimp only [φ]
      rw [MonoidHom.comp_apply, QuotientGroup.mk'_apply,
        (QuotientGroup.eq_one_iff _).2 (transvectionUnit_mem_elementarySubgroup hij c), map_one]
    map_diag := fun d ↦ (hφ_eq_bare _).trans
      (bareDieudonne_diagGL prev.hom prev.map_transvection prev.map_diag d)
    ker_eq := fun _ ↦ by ext g; simp [φ] }

private def dieudonneFinData (D : Type*) [DivisionRing D] : ∀ m : ℕ, DieudonneFinData D m
  | 0 =>
    { hom := 1
      map_transvection := fun {_} _ _ _ ↦ rfl
      map_diag := fun _ ↦ by simp
      ker_eq := fun h ↦ absurd h (by decide) }
  | 1 =>
    { hom :=
        { toFun A := Group.Abelianization.of
            ⟨A 0 0, (A⁻¹ : GL (Fin 1) D) 0 0,
              by simpa [Matrix.mul_apply] using congrFun (congrFun A.mul_inv 0) 0,
              by simpa [Matrix.mul_apply] using congrFun (congrFun A.inv_mul 0) 0⟩
          map_one' := by
            rw [← Group.Abelianization.of.map_one]
            exact congrArg Group.Abelianization.of (Units.ext (by simp))
          map_mul' A B := by
            rw [← Group.Abelianization.of.map_mul]
            exact congrArg Group.Abelianization.of (Units.ext (by simp [Matrix.mul_apply])) }
      map_transvection := fun {i j} hij _ ↦ absurd (Subsingleton.elim i j) hij
      map_diag := fun d ↦ by
        rw [Fin.prod_univ_one]
        exact congrArg Group.Abelianization.of (Units.ext (by simp))
      ker_eq := fun h ↦ absurd h (by decide) }
  | k + 2 => dieudonneFinSuccSucc (dieudonneFinData D (k + 1))

end SchurInduction

end TauCeti

/-! ## The Dieudonné determinant over an arbitrary finite index type -/

namespace Matrix.GeneralLinearGroup

section DivisionRing

variable {n : Type*} [Fintype n] [DecidableEq n] {D : Type*} [DivisionRing D]

private theorem dieudonneFinData_hom_reindexGL_perm {m : ℕ} (σ : Equiv.Perm (Fin m))
    (A : GL (Fin m) D) :
    (TauCeti.dieudonneFinData D m).hom (σ.reindexGL D A) =
      (TauCeti.dieudonneFinData D m).hom A := by
  rw [← TauCeti.permutationGL_mul_mul_inv, map_mul, map_mul, map_inv]
  calc
    (TauCeti.dieudonneFinData D m).hom (TauCeti.permutationGL σ) *
        (TauCeti.dieudonneFinData D m).hom A *
        ((TauCeti.dieudonneFinData D m).hom (TauCeti.permutationGL σ))⁻¹
      = (TauCeti.dieudonneFinData D m).hom A *
          ((TauCeti.dieudonneFinData D m).hom (TauCeti.permutationGL σ) *
            ((TauCeti.dieudonneFinData D m).hom (TauCeti.permutationGL σ))⁻¹) := by ac_rfl
    _ = (TauCeti.dieudonneFinData D m).hom A := by rw [mul_inv_cancel, mul_one]

private theorem dieudonneFinData_hom_finCongr {m k : ℕ} (h : m = k) (A : GL (Fin m) D) :
    (TauCeti.dieudonneFinData D k).hom ((finCongr h).reindexGL D A) =
      (TauCeti.dieudonneFinData D m).hom A := by
  subst h
  exact congrArg (TauCeti.dieudonneFinData D m).hom (by ext i j; simp)

/-- The **Dieudonné determinant** over a division ring `D`, taking values in the abelianized unit
group `Group.Abelianization Dˣ = Dˣ / [Dˣ, Dˣ]`. -/
def dieudonneDet : GL n D →* Group.Abelianization Dˣ :=
  (TauCeti.dieudonneFinData D (Fintype.card n)).hom.comp
    ((Fintype.equivFin n).reindexGL D).toMonoidHom

/-- Reindexing rows and columns simultaneously along an equivalence of index types preserves the
Dieudonné determinant. -/
@[simp]
theorem dieudonneDet_reindexGL {m : Type*} [Fintype m] [DecidableEq m] (e : n ≃ m) (g : GL n D) :
    dieudonneDet (e.reindexGL D g) = dieudonneDet g := by
  let hcard : Fintype.card n = Fintype.card m := Fintype.card_congr e
  let e₁ := Fintype.equivFin n
  let e₂ := Fintype.equivFin m
  let σ : Equiv.Perm (Fin (Fintype.card m)) :=
    (finCongr hcard).symm.trans (e₁.symm.trans (e.trans e₂))
  have heq : e₁.trans ((finCongr hcard).trans σ) = e.trans e₂ := by ext x; simp [σ]
  have hreindex : e₂.reindexGL D (e.reindexGL D g) =
      σ.reindexGL D ((finCongr hcard).reindexGL D (e₁.reindexGL D g)) := by
    rw [← MulEquiv.trans_apply, ← MulEquiv.trans_apply, ← MulEquiv.trans_apply,
      Equiv.reindexGL_trans_reindexGL, Equiv.reindexGL_trans_reindexGL,
      Equiv.reindexGL_trans_reindexGL, heq]
  dsimp only [dieudonneDet, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
  rw [hreindex, dieudonneFinData_hom_reindexGL_perm, dieudonneFinData_hom_finCongr]

/-- Every elementary transvection has Dieudonné determinant `1`. -/
@[simp]
theorem dieudonneDet_transvectionUnit {i j : n} (hij : i ≠ j) (c : D) :
    dieudonneDet (TauCeti.transvectionUnit hij c) = 1 := by
  dsimp only [dieudonneDet, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
  rw [Equiv.reindexGL_transvectionUnit]
  exact (TauCeti.dieudonneFinData D (Fintype.card n)).map_transvection _ c

/-- The elementary subgroup is contained in the kernel of the Dieudonné determinant. -/
theorem elementarySubgroup_le_ker_dieudonneDet :
    TauCeti.elementarySubgroup n D ≤ (dieudonneDet (n := n) (D := D)).ker :=
  TauCeti.elementarySubgroup_le_iff.2 fun _ _ hij c ↦ dieudonneDet_transvectionUnit hij c

/-- Every matrix in the elementary subgroup has Dieudonné determinant `1`. -/
theorem dieudonneDet_of_mem_elementarySubgroup {g : GL n D}
    (hg : g ∈ TauCeti.elementarySubgroup n D) : dieudonneDet g = 1 :=
  elementarySubgroup_le_ker_dieudonneDet hg

/-- In rank at least two, the kernel of the Dieudonné determinant is precisely the elementary
subgroup. -/
theorem ker_dieudonneDet (hn : 2 ≤ Fintype.card n) :
    (dieudonneDet (n := n) (D := D)).ker = TauCeti.elementarySubgroup n D := by
  ext g
  rw [MonoidHom.mem_ker, dieudonneDet, MonoidHom.comp_apply, ← MonoidHom.mem_ker,
    (TauCeti.dieudonneFinData D (Fintype.card n)).ker_eq hn,
    ← (Fintype.equivFin n).map_reindexGL_elementarySubgroup]
  exact ⟨fun ⟨x, hx, hxeq⟩ ↦ ((Fintype.equivFin n).reindexGL D).injective hxeq ▸ hx,
    fun hg ↦ ⟨g, hg, rfl⟩⟩

/-- In rank at least two, an invertible matrix over a division ring has Dieudonné determinant `1`
if and only if it belongs to the elementary subgroup. -/
theorem dieudonneDet_eq_one_iff (hn : 2 ≤ Fintype.card n) {g : GL n D} :
    dieudonneDet g = 1 ↔ g ∈ TauCeti.elementarySubgroup n D := by
  rw [← MonoidHom.mem_ker, ker_dieudonneDet hn]

/-- The Dieudonné determinant of an invertible diagonal matrix is the product of the classes of its
diagonal entries in `Group.Abelianization Dˣ`. -/
@[simp]
theorem dieudonneDet_diagGL (d : n → Dˣ) :
    dieudonneDet (TauCeti.diagGL d) = ∏ i, Group.Abelianization.of (d i) := by
  let e := Fintype.equivFin n
  have hreindex : e.reindexGL D (TauCeti.diagGL d) = TauCeti.diagGL (d ∘ e.symm) := by
    ext a b; simp [Matrix.diagonal_apply, e.symm.apply_eq_iff_eq]
  dsimp only [dieudonneDet, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
  rw [hreindex, (TauCeti.dieudonneFinData D (Fintype.card n)).map_diag]
  exact e.symm.prod_comp (fun i ↦ Group.Abelianization.of (d i))

/-- A diagonal matrix with `u` at entry `i` and `1` elsewhere has Dieudonné determinant
`Group.Abelianization.of u`. -/
theorem dieudonneDet_diagGL_mulSingle (i : n) (u : Dˣ) :
    dieudonneDet (TauCeti.diagGL (Pi.mulSingle i u)) = Group.Abelianization.of u := by
  rw [dieudonneDet_diagGL,
    Fintype.prod_eq_single i (fun x hx ↦ by simp [Pi.mulSingle_eq_of_ne hx]),
    Pi.mulSingle_eq_same]

/-- A scalar matrix `scalar n u` has Dieudonné determinant
`Group.Abelianization.of u ^ Fintype.card n`. -/
@[simp]
theorem dieudonneDet_scalar (u : Dˣ) :
    dieudonneDet (scalar n u) = Group.Abelianization.of u ^ Fintype.card n := by
  rw [← TauCeti.diagGL_const, dieudonneDet_diagGL, Finset.prod_const, Finset.card_univ]

/-- Over a nonempty index type, the Dieudonné determinant is surjective. -/
theorem dieudonneDet_surjective [Nonempty n] :
    Function.Surjective (dieudonneDet (n := n) (D := D)) := by
  obtain ⟨i⟩ := ‹Nonempty n›
  intro x
  refine QuotientGroup.induction_on x (fun u ↦ ⟨TauCeti.diagGL (Pi.mulSingle i u), ?_⟩)
  exact dieudonneDet_diagGL_mulSingle i u

/-- **Uniqueness of the Dieudonné determinant.** A homomorphism
`GL n D →* Group.Abelianization Dˣ` that vanishes on `TauCeti.elementarySubgroup n D` and sends
`diagGL (Pi.mulSingle i u)` to `Group.Abelianization.of u` at some index `i : n` equals
`dieudonneDet`. -/
theorem eq_dieudonneDet {φ : GL n D →* Group.Abelianization Dˣ}
    (hker : TauCeti.elementarySubgroup n D ≤ φ.ker) (i : n)
    (hdiag : ∀ u : Dˣ, φ (TauCeti.diagGL (Pi.mulSingle i u)) = Group.Abelianization.of u) :
    φ = dieudonneDet :=
  hom_ext_of_elementarySubgroup_le_ker hker elementarySubgroup_le_ker_dieudonneDet i fun u ↦
    (hdiag u).trans (dieudonneDet_diagGL_mulSingle i u).symm

/-- In rank at least three, `TauCeti.elementarySubgroup n D` is perfect, so `dieudonneDet` is the
unique homomorphism `GL n D →* Group.Abelianization Dˣ` sending `diagGL (Pi.mulSingle i u)` to
`Group.Abelianization.of u` at some index `i : n`. -/
theorem eq_dieudonneDet_of_three_le_card (hn : 3 ≤ Fintype.card n)
    {φ : GL n D →* Group.Abelianization Dˣ} (i : n)
    (hdiag : ∀ u : Dˣ, φ (TauCeti.diagGL (Pi.mulSingle i u)) = Group.Abelianization.of u) :
    φ = dieudonneDet :=
  eq_dieudonneDet
    ((TauCeti.elementarySubgroup_le_commutator hn).trans
      (Group.Abelianization.commutator_le_ker φ))
    i hdiag

/-- The Dieudonné determinant of a permutation matrix is the image of `Equiv.Perm.sign σ`. -/
@[simp]
theorem dieudonneDet_permutationGL (σ : Equiv.Perm n) :
    dieudonneDet (TauCeti.permutationGL (k := D) σ) =
      Group.Abelianization.of (Units.map (Int.castRingHom D).toMonoidHom (Equiv.Perm.sign σ)) :=
  TauCeti.map_permutationGL_of_ih dieudonneDet
    (fun hij c ↦ dieudonneDet_transvectionUnit hij c) dieudonneDet_diagGL σ

/-- Every upper block-unipotent matrix has Dieudonné determinant `1`. -/
@[simp]
theorem dieudonneDet_upperBlockGL {m : Type*} [Fintype m] [DecidableEq m] (X : Matrix n m D) :
    dieudonneDet (Matrix.upperBlockGL X) = 1 :=
  dieudonneDet_of_mem_elementarySubgroup (Matrix.upperBlockGL_mem_elementarySubgroup X)

/-- Every lower block-unipotent matrix has Dieudonné determinant `1`. -/
@[simp]
theorem dieudonneDet_lowerBlockGL {m : Type*} [Fintype m] [DecidableEq m] (Y : Matrix m n D) :
    dieudonneDet (Matrix.lowerBlockGL Y) = 1 :=
  dieudonneDet_of_mem_elementarySubgroup (Matrix.lowerBlockGL_mem_elementarySubgroup Y)

/-- The Dieudonné determinant is multiplicative across block-diagonal sums `u ⊕ v`. -/
@[simp]
theorem dieudonneDet_fromBlocksGL {m : Type*} [Fintype m] [DecidableEq m]
    (u : GL n D) (v : GL m D) :
    dieudonneDet (TauCeti.fromBlocksGL (u, v)) = dieudonneDet u * dieudonneDet v := by
  obtain ⟨eu, heu, d₁, rfl⟩ := TauCeti.exists_mem_elementarySubgroup_mul_diagGL u
  obtain ⟨ev, hev, d₂, rfl⟩ := TauCeti.exists_mem_elementarySubgroup_mul_diagGL v
  have hprod : (eu * TauCeti.diagGL d₁, ev * TauCeti.diagGL d₂) =
      (eu, (1 : GL m D)) * ((1 : GL n D), ev) * (TauCeti.diagGL d₁, TauCeti.diagGL d₂) := by
    ext <;> simp
  have hdiag : TauCeti.fromBlocksGL (TauCeti.diagGL d₁, TauCeti.diagGL d₂) =
      TauCeti.diagGL (Sum.elim d₁ d₂) := by
    apply Units.ext
    rw [TauCeti.coe_fromBlocksGL, TauCeti.diagGL_coe, TauCeti.diagGL_coe, TauCeti.diagGL_coe]
    ext (a | a) (b | b) <;> simp [Matrix.diagonal_apply]
  have heu' : TauCeti.fromBlocksGL (eu, (1 : GL m D)) ∈
      TauCeti.elementarySubgroup (n ⊕ m) D :=
    TauCeti.map_elementarySubgroup_le_elementarySubgroup ⟨eu, heu, rfl⟩
  have hev' : TauCeti.fromBlocksGL ((1 : GL n D), ev) ∈
      TauCeti.elementarySubgroup (n ⊕ m) D :=
    TauCeti.map_inr_elementarySubgroup_le_elementarySubgroup ⟨ev, hev, rfl⟩
  rw [hprod, map_mul, map_mul, map_mul, map_mul, map_mul, map_mul,
    dieudonneDet_of_mem_elementarySubgroup heu', dieudonneDet_of_mem_elementarySubgroup hev',
    dieudonneDet_of_mem_elementarySubgroup heu, dieudonneDet_of_mem_elementarySubgroup hev,
    one_mul, one_mul, one_mul, one_mul, hdiag, dieudonneDet_diagGL, dieudonneDet_diagGL,
    dieudonneDet_diagGL, Fintype.prod_sum_type]
  rfl

/-- The Dieudonné determinant is natural with respect to ring homomorphisms `D →+* E` between
division rings. -/
@[simp]
theorem dieudonneDet_unitsMap_mapMatrix {E : Type*} [DivisionRing E] (f : D →+* E) (g : GL n D) :
    dieudonneDet (Units.map (f.mapMatrix (m := n) : Matrix n n D →* Matrix n n E) g) =
      Group.Abelianization.map (Units.map (f : D →* E)) (dieudonneDet g) := by
  obtain ⟨e, he, d, rfl⟩ := TauCeti.exists_mem_elementarySubgroup_mul_diagGL g
  have hle : TauCeti.elementarySubgroup n D ≤
      (TauCeti.elementarySubgroup n E).comap
        (Units.map (f.mapMatrix (m := n) : Matrix n n D →* Matrix n n E)) := by
    refine TauCeti.elementarySubgroup_le_iff.2 fun i j hij c ↦ ?_
    rw [Subgroup.mem_comap]
    convert TauCeti.transvectionUnit_mem_elementarySubgroup hij (f c)
    ext a b
    simp [TauCeti.coe_transvectionUnit_eq_one_add_single, Matrix.single_apply, Matrix.one_apply,
      apply_ite f]
  have hmap_diag :
      Units.map (f.mapMatrix (m := n) : Matrix n n D →* Matrix n n E) (TauCeti.diagGL d) =
        TauCeti.diagGL (fun i ↦ Units.map (f : D →* E) (d i)) := by
    ext a b; simp [Matrix.diagonal_apply, apply_ite f]
  rw [map_mul, map_mul, map_mul, dieudonneDet_of_mem_elementarySubgroup (hle he),
    dieudonneDet_of_mem_elementarySubgroup he, one_mul, one_mul, hmap_diag,
    dieudonneDet_diagGL, dieudonneDet_diagGL, map_prod]
  simp

end DivisionRing

section Field

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Naturality of the Dieudonné determinant under `Matrix.GeneralLinearGroup.map` over fields. -/
@[simp]
theorem dieudonneDet_map {F K : Type*} [Field F] [Field K] (f : F →+* K) (g : GL n F) :
    dieudonneDet (map f g) =
      Group.Abelianization.map (Units.map (f : F →* K)) (dieudonneDet g) :=
  dieudonneDet_unitsMap_mapMatrix f g

/-- Over a field `F`, the Dieudonné determinant agrees with the ordinary determinant followed by
`Group.Abelianization.of : Fˣ →* Group.Abelianization Fˣ`. -/
theorem dieudonneDet_eq_of_det {F : Type*} [Field F] (g : GL n F) :
    dieudonneDet g = Group.Abelianization.of g.det := by
  obtain ⟨e, he, d, rfl⟩ := TauCeti.exists_mem_elementarySubgroup_mul_diagGL g
  have hdet_e : e.det = 1 :=
    (TauCeti.elementarySubgroup_le_iff (H := det.ker).2
      fun _ _ hij c ↦ TauCeti.det_transvectionUnit hij c) he
  rw [map_mul, dieudonneDet_of_mem_elementarySubgroup he, one_mul, dieudonneDet_diagGL,
    map_mul, hdet_e, one_mul, TauCeti.det_diagGL, map_prod]

end Field

end Matrix.GeneralLinearGroup

/-! ## Finite-rank quotient by the elementary subgroup -/

namespace TauCeti

/-- In rank at least two, the Dieudonné determinant descends to a canonical isomorphism
`GL n D ⧸ elementarySubgroup n D ≃* Group.Abelianization Dˣ`. -/
def quotientElementarySubgroupDieudonneEquiv (n : Type*) [Fintype n] [DecidableEq n]
    (D : Type*) [DivisionRing D] (hn : 2 ≤ Fintype.card n) :
    GL n D ⧸ elementarySubgroup n D ≃* Group.Abelianization Dˣ :=
  haveI : Nonempty n := Fintype.card_pos_iff.mp (by omega)
  (QuotientGroup.quotientMulEquivOfEq
    (GeneralLinearGroup.ker_dieudonneDet (n := n) (D := D) hn).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective GeneralLinearGroup.dieudonneDet
      GeneralLinearGroup.dieudonneDet_surjective)

/-- `TauCeti.quotientElementarySubgroupDieudonneEquiv` evaluates on a coset `QuotientGroup.mk g` as
`g.dieudonneDet`. -/
@[simp]
theorem quotientElementarySubgroupDieudonneEquiv_mk {n : Type*} [Fintype n] [DecidableEq n]
    {D : Type*} [DivisionRing D] (hn : 2 ≤ Fintype.card n) (g : GL n D) :
    quotientElementarySubgroupDieudonneEquiv n D hn (QuotientGroup.mk g) =
      GeneralLinearGroup.dieudonneDet g :=
  (rfl)

/-- The inverse of `TauCeti.quotientElementarySubgroupDieudonneEquiv` sends
`Group.Abelianization.of u` to the coset of `diagGL (Pi.mulSingle i u)` at any index `i : n`. -/
theorem quotientElementarySubgroupDieudonneEquiv_symm_of {n : Type*} [Fintype n] [DecidableEq n]
    {D : Type*} [DivisionRing D] (hn : 2 ≤ Fintype.card n) (i : n) (u : Dˣ) :
    (quotientElementarySubgroupDieudonneEquiv n D hn).symm (Group.Abelianization.of u) =
      QuotientGroup.mk (diagGL (Pi.mulSingle i u)) := by
  rw [← GeneralLinearGroup.dieudonneDet_diagGL_mulSingle i u,
    ← quotientElementarySubgroupDieudonneEquiv_mk hn, MulEquiv.symm_apply_apply]

end TauCeti

end
