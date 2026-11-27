/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.LinearAlgebra.Matrix.Rank
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.RingTheory.Idempotents
public import TauCeti.Combinatorics.AssociationScheme.Basic

import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.Tactic.FieldSimp
import TauCeti.LinearAlgebra.Matrix.Rank
import TauCeti.LinearAlgebra.Trace.Idempotent
import TauCeti.RingTheory.Idempotents.LinearIndependent

/-!
# Primitive idempotents of a symmetric association scheme

A family of primitive idempotents of a symmetric association scheme `rel : X → X → Fin (d + 1)`
is a complete family `E : Fin (d + 1) → Matrix X X ℝ` of nonzero orthogonal idempotents in the
Bose–Mesner algebra `bmAlgebra rel` with `E 0 = |X|⁻¹ J`.

Since `bmAlgebra rel` is a `(d + 1)`-dimensional commutative algebra of real symmetric matrices
containing `I` and `J`, every scheme admits such a family, uniquely up to permuting indices
`1, …, d`. Every `E i` is symmetric and positive semidefinite of rank `tr (E i) > 0`, the column
spaces of the `E i` form a pairwise orthogonal decomposition of `X → ℝ` into common eigenspaces
of the Bose–Mesner algebra, and `E` is a basis of `bmAlgebra rel`.

## Main definitions

* `TauCeti.IsPrimitiveIdempotents`: predicate characterizing a family of primitive idempotents.
* `TauCeti.IsPrimitiveIdempotents.basis`: the basis of `bmAlgebra rel` formed by `E`.

## Main results

* `TauCeti.exists_isPrimitiveIdempotents`: every symmetric association scheme admits a family of
  primitive idempotents.
* `TauCeti.IsPrimitiveIdempotents.exists_perm`: primitive idempotents are unique up to a
  permutation fixing `0`.
* `TauCeti.IsPrimitiveIdempotents.mul_eq_smul`: every `M ∈ bmAlgebra rel` acts on the column
  space of `E i` by the scalar `tr (M * E i) / tr (E i)`.

## References

* A. E. Brouwer and W. H. Haemers, *Spectra of Graphs*, Universitext, Springer, 2012, §§11.2.
* C. Godsil, *Association Schemes*, lecture notes, 2010, §§1.4–1.5.
-/

public section

namespace TauCeti

open Finset Matrix
open scoped Matrix

section Definition

variable {X : Type*} [Fintype X] [DecidableEq X] {d : ℕ}

/-- A family of primitive idempotents of a symmetric association scheme: a complete family of
orthogonal idempotents, all nonzero and all in the Bose–Mesner algebra, the one of index `0`
being `|X|⁻¹ J`. -/
structure IsPrimitiveIdempotents (rel : X → X → Fin (d + 1))
    (E : Fin (d + 1) → Matrix X X ℝ) : Prop where
  /-- The matrices form a complete family of orthogonal idempotents. -/
  complete : CompleteOrthogonalIdempotents E
  /-- Each idempotent is nonzero. -/
  ne_zero : ∀ i, E i ≠ 0
  /-- Each idempotent lies in the Bose–Mesner algebra. -/
  mem_bmAlgebra : ∀ i, E i ∈ bmAlgebra rel
  /-- The idempotent of index `0` is `|X|⁻¹ J`. -/
  eq_zero : E 0 = (Fintype.card X : ℝ)⁻¹ • Matrix.of fun _ _ => 1

end Definition

section Helpers

variable {X : Type*} [Fintype X] {d : ℕ} {rel : X → X → Fin (d + 1)}

private theorem isIdempotentElem_allOnes_inv (h : IsAssocScheme rel) :
    IsIdempotentElem ((Fintype.card X : ℝ)⁻¹ • Matrix.of fun _ _ : X => (1 : ℝ)) := by
  have hpos : (Fintype.card X : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr h.card_pos.ne'
  rw [IsIdempotentElem]
  ext x y
  simp [Matrix.mul_apply, hpos]

private theorem allOnes_inv_ne_zero (h : IsAssocScheme rel) :
    ((Fintype.card X : ℝ)⁻¹ • Matrix.of fun _ _ : X => (1 : ℝ)) ≠ 0 := by
  obtain ⟨x⟩ := h.nonempty
  have hpos : (Fintype.card X : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr h.card_pos.ne'
  intro h0
  have hx := congrArg (fun M : Matrix X X ℝ => M x x) h0
  simp [hpos] at hx

private theorem allOnes_inv_mem_bmAlgebra (rel : X → X → Fin (d + 1)) :
    ((Fintype.card X : ℝ)⁻¹ • Matrix.of fun _ _ : X => (1 : ℝ)) ∈ bmAlgebra rel :=
  Submodule.smul_mem _ _ (allOnes_mem_bmAlgebra rel)

private theorem adjMat_mul_allOnes_inv (h : IsAssocScheme rel) (i : Fin (d + 1)) :
    adjMat rel i * ((Fintype.card X : ℝ)⁻¹ • Matrix.of fun _ _ : X => (1 : ℝ)) =
      valency rel i • ((Fintype.card X : ℝ)⁻¹ • Matrix.of fun _ _ : X => (1 : ℝ)) := by
  ext x y
  rw [Matrix.mul_smul]
  simp only [Matrix.smul_apply, Matrix.mul_apply, of_apply, mul_one, h.sum_adjMat_row i x,
    smul_eq_mul]
  rw [mul_comm]

private theorem exists_mul_allOnes_inv_eq_smul (h : IsAssocScheme rel) {M : Matrix X X ℝ}
    (hM : M ∈ bmAlgebra rel) :
    ∃ c : ℝ, M * ((Fintype.card X : ℝ)⁻¹ • Matrix.of fun _ _ : X => (1 : ℝ)) =
      c • ((Fintype.card X : ℝ)⁻¹ • Matrix.of fun _ _ : X => (1 : ℝ)) := by
  rw [mem_bmAlgebra_iff] at hM
  induction hM using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨i, rfl⟩ := hx
    exact ⟨valency rel i, adjMat_mul_allOnes_inv h i⟩
  | zero => exact ⟨0, by simp⟩
  | add _ _ _ _ h1 h2 =>
    obtain ⟨c1, hc1⟩ := h1
    obtain ⟨c2, hc2⟩ := h2
    exact ⟨c1 + c2, by rw [Matrix.add_mul, hc1, hc2, add_smul]⟩
  | smul a _ _ h1 =>
    obtain ⟨c, hc⟩ := h1
    exact ⟨a * c, by rw [Matrix.smul_mul, hc, smul_smul]⟩

end Helpers

section Splitting

variable {X : Type*} [Fintype X] {d : ℕ} {rel : X → X → Fin (d + 1)}

private theorem exists_eigen_ne_of_not_mul_eq_smul [DecidableEq X] {p A : Matrix X X ℝ}
    (hM_herm : (A * p).IsHermitian) (hp_ne : p ≠ 0) (hpM : p * (A * p) = A * p)
    (hnot : ∀ c : ℝ, A * p ≠ c • p) :
    ∃ x₀ y₀ : X, p *ᵥ ⇑(hM_herm.eigenvectorBasis x₀) ≠ 0 ∧
      p *ᵥ ⇑(hM_herm.eigenvectorBasis y₀) ≠ 0 ∧
      hM_herm.eigenvalues y₀ ≠ hM_herm.eigenvalues x₀ := by
  have hzero : ∀ {B : Matrix X X ℝ},
      (∀ j, B *ᵥ ⇑(hM_herm.eigenvectorBasis j) = 0) → B = 0 := by
    intro B hB
    apply Matrix.toEuclideanLin.injective
    apply hM_herm.eigenvectorBasis.toBasis.ext
    intro j
    exact PiLp.ext fun x => by simpa [Matrix.toLpLin_apply] using congrFun (hB j) x
  obtain ⟨x₀, hx₀⟩ : ∃ x₀ : X, p *ᵥ ⇑(hM_herm.eigenvectorBasis x₀) ≠ 0 := by
    by_contra! hall
    exact hp_ne (hzero hall)
  obtain ⟨y₀, hy₀_p, hy₀_ev⟩ : ∃ y₀ : X,
      p *ᵥ ⇑(hM_herm.eigenvectorBasis y₀) ≠ 0 ∧
      hM_herm.eigenvalues y₀ ≠ hM_herm.eigenvalues x₀ := by
    by_contra! hall
    refine hnot (hM_herm.eigenvalues x₀) (sub_eq_zero.mp (hzero fun j => ?_))
    rw [Matrix.sub_mulVec, Matrix.smul_mulVec]
    by_cases hpj : p *ᵥ ⇑(hM_herm.eigenvectorBasis j) = 0
    · rw [← Matrix.mulVec_mulVec, hpj, Matrix.mulVec_zero, smul_zero, sub_zero]
    · have hevj : hM_herm.eigenvalues j = hM_herm.eigenvalues x₀ := hall j hpj
      rcases eq_or_ne (hM_herm.eigenvalues x₀) 0 with hμ0 | hμ0
      · rw [hM_herm.mulVec_eigenvectorBasis j, hevj, hμ0, zero_smul, zero_smul, sub_zero]
      · have hpb : p *ᵥ ⇑(hM_herm.eigenvectorBasis j) = ⇑(hM_herm.eigenvectorBasis j) := by
          calc p *ᵥ ⇑(hM_herm.eigenvectorBasis j)
              = p *ᵥ ((hM_herm.eigenvalues x₀)⁻¹ •
                  ((A * p) *ᵥ ⇑(hM_herm.eigenvectorBasis j))) := by
                rw [hM_herm.mulVec_eigenvectorBasis j, hevj, smul_smul, inv_mul_cancel₀ hμ0,
                  one_smul]
            _ = (hM_herm.eigenvalues x₀)⁻¹ •
                  ((p * (A * p)) *ᵥ ⇑(hM_herm.eigenvectorBasis j)) := by
                rw [Matrix.mulVec_smul, Matrix.mulVec_mulVec]
            _ = ⇑(hM_herm.eigenvectorBasis j) := by
                rw [hpM, hM_herm.mulVec_eigenvectorBasis j, hevj, smul_smul,
                  inv_mul_cancel₀ hμ0, one_smul]
        rw [hM_herm.mulVec_eigenvectorBasis j, hevj, hpb, sub_self]
  exact ⟨x₀, y₀, hx₀, hy₀_p, hy₀_ev⟩

private theorem exists_spectral_proj [DecidableEq X] (h : IsAssocScheme rel)
    {M : Matrix X X ℝ} (hM_mem : M ∈ bmAlgebra rel) (hM_herm : M.IsHermitian)
    (x₀ y₀ : X) (hne : hM_herm.eigenvalues y₀ ≠ hM_herm.eigenvalues x₀) :
    ∃ Q ∈ bmAlgebra rel, IsIdempotentElem Q ∧
      Q *ᵥ ⇑(hM_herm.eigenvectorBasis x₀) = ⇑(hM_herm.eigenvectorBasis x₀) ∧
      Q *ᵥ ⇑(hM_herm.eigenvectorBasis y₀) = 0 := by
  set μ : ℝ := hM_herm.eigenvalues x₀
  let S_ev : Finset ℝ := (Finset.univ.image hM_herm.eigenvalues).erase μ
  let fac (ν : ℝ) : Matrix X X ℝ := (μ - ν)⁻¹ • (M - ν • 1)
  set Q : Matrix X X ℝ := (S_ev.toList.map fac).prod
  have hQ_mem : ∀ l : List ℝ, (l.map fac).prod ∈ bmAlgebra rel := fun l => by
    induction l with
    | nil => exact h.one_mem_bmAlgebra
    | cons ν l ih =>
      exact h.mul_mem_bmAlgebra (Submodule.smul_mem _ _
        (Submodule.sub_mem _ hM_mem (Submodule.smul_mem _ _ h.one_mem_bmAlgebra))) ih
  have hQ_mulVec : ∀ (l : List ℝ) (j : X),
      (l.map fac).prod *ᵥ ⇑(hM_herm.eigenvectorBasis j) =
        (l.map fun ν => (μ - ν)⁻¹ * (hM_herm.eigenvalues j - ν)).prod •
          ⇑(hM_herm.eigenvectorBasis j) := fun l j => by
    induction l with
    | nil => simp
    | cons ν l ih =>
      rw [List.map_cons, List.prod_cons, ← Matrix.mulVec_mulVec, ih, Matrix.mulVec_smul]
      simp only [fac, Matrix.smul_mulVec, Matrix.sub_mulVec, Matrix.one_mulVec,
        hM_herm.mulVec_eigenvectorBasis j, ← sub_smul, smul_smul, List.map_cons, List.prod_cons]
      rw [mul_comm _ ((List.map _ l).prod)]
  have hQ_eval : ∀ j : X, (S_ev.toList.map fun ν =>
      (μ - ν)⁻¹ * (hM_herm.eigenvalues j - ν)).prod =
      if hM_herm.eigenvalues j = μ then 1 else 0 := fun j => by
    split_ifs with hj
    · refine List.prod_eq_one fun x hx => ?_
      obtain ⟨ν, hν, rfl⟩ := List.mem_map.mp hx
      have hne' : μ - ν ≠ 0 :=
        sub_ne_zero.mpr (Finset.ne_of_mem_erase (Finset.mem_toList.mp hν)).symm
      rw [hj, inv_mul_cancel₀ hne']
    · exact List.prod_eq_zero (List.mem_map.mpr ⟨hM_herm.eigenvalues j,
        Finset.mem_toList.mpr (Finset.mem_erase.mpr
          ⟨hj, Finset.mem_image_of_mem _ (Finset.mem_univ _)⟩), by simp⟩)
  have hQ_idem : IsIdempotentElem Q := by
    rw [IsIdempotentElem, ← sub_eq_zero]
    apply Matrix.toEuclideanLin.injective
    refine hM_herm.eigenvectorBasis.toBasis.ext fun j => PiLp.ext fun x => ?_
    have h0 : (Q * Q - Q) *ᵥ ⇑(hM_herm.eigenvectorBasis j) = 0 := by
      rw [Matrix.sub_mulVec, ← Matrix.mulVec_mulVec, hQ_mulVec S_ev.toList j,
        Matrix.mulVec_smul, hQ_mulVec S_ev.toList j, smul_smul, hQ_eval j]
      split_ifs <;> simp
    rw [Matrix.sub_mulVec] at h0
    simpa [Matrix.toLpLin_apply] using congrFun h0 x
  refine ⟨Q, hQ_mem S_ev.toList, hQ_idem, ?_, ?_⟩
  · simp [Q, hQ_mulVec S_ev.toList x₀, hQ_eval x₀, μ]
  · simp [Q, hQ_mulVec S_ev.toList y₀, hQ_eval y₀, μ, hne]

private theorem split_alg_of_comm [DecidableEq X] (h : IsAssocScheme rel)
    {p Q : Matrix X X ℝ} (hp_mem : p ∈ bmAlgebra rel) (hQ_mem : Q ∈ bmAlgebra rel)
    (hp_idem : IsIdempotentElem p) (hQ_idem : IsIdempotentElem Q) (hcomm : Q * p = p * Q) :
    (Q * p) ∈ bmAlgebra rel ∧ ((1 - Q) * p) ∈ bmAlgebra rel ∧
      IsIdempotentElem (Q * p) ∧ IsIdempotentElem ((1 - Q) * p) ∧
      (Q * p) * ((1 - Q) * p) = 0 ∧ ((1 - Q) * p) * (Q * p) = 0 ∧
      Q * p + (1 - Q) * p = p := by
  have h1Q : (1 - Q) * p = p * (1 - Q) := by
    rw [sub_mul, one_mul, mul_sub, mul_one, hcomm]
  refine ⟨h.mul_mem_bmAlgebra hQ_mem hp_mem, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [sub_mul] using Submodule.sub_mem _ hp_mem (h.mul_mem_bmAlgebra hQ_mem hp_mem)
  · rw [IsIdempotentElem, mul_assoc, ← mul_assoc p, ← hcomm, mul_assoc Q p p, hp_idem.eq,
      ← mul_assoc, hQ_idem.eq]
  · calc ((1 - Q) * p) * ((1 - Q) * p)
        = (1 - Q) * (p * (1 - Q)) * p := by simp only [Matrix.mul_assoc]
      _ = ((1 - Q) * (1 - Q)) * (p * p) := by rw [← h1Q]; simp only [Matrix.mul_assoc]
      _ = (1 - Q) * p := by rw [hQ_idem.one_sub.eq, hp_idem.eq]
  · calc (Q * p) * ((1 - Q) * p)
        = Q * (p * (1 - Q)) * p := by simp only [Matrix.mul_assoc]
      _ = (Q * (1 - Q)) * (p * p) := by rw [← h1Q]; simp only [Matrix.mul_assoc]
      _ = 0 := by rw [mul_sub, mul_one, hQ_idem.eq, sub_self, Matrix.zero_mul]
  · calc ((1 - Q) * p) * (Q * p)
        = (1 - Q) * (p * Q) * p := by simp only [Matrix.mul_assoc]
      _ = ((1 - Q) * Q) * (p * p) := by rw [← hcomm]; simp only [Matrix.mul_assoc]
      _ = 0 := by rw [sub_mul, one_mul, hQ_idem.eq, sub_self, Matrix.zero_mul]
  · rw [← add_mul, add_sub_cancel, one_mul]

private theorem exists_split_of_not_mul_eq_smul (h : IsAssocScheme rel) {p A : Matrix X X ℝ}
    (hp_mem : p ∈ bmAlgebra rel) (hp_idem : IsIdempotentElem p) (hp_ne : p ≠ 0)
    (hA_mem : A ∈ bmAlgebra rel) (hnot : ∀ c : ℝ, A * p ≠ c • p) :
    ∃ p₁ p₂ : Matrix X X ℝ, p₁ ∈ bmAlgebra rel ∧ p₂ ∈ bmAlgebra rel ∧
      IsIdempotentElem p₁ ∧ IsIdempotentElem p₂ ∧ p₁ * p₂ = 0 ∧ p₂ * p₁ = 0 ∧
      p₁ ≠ 0 ∧ p₂ ≠ 0 ∧ p₁ + p₂ = p := by
  classical
  set M : Matrix X X ℝ := A * p
  have hM_mem : M ∈ bmAlgebra rel := h.mul_mem_bmAlgebra hA_mem hp_mem
  have hM_herm : M.IsHermitian := by
    rw [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial]
    exact h.transpose_eq_of_mem_bmAlgebra hM_mem
  have hpM : p * M = M := by
    rw [h.mul_comm_of_mem_bmAlgebra hp_mem hM_mem]
    simp [M, Matrix.mul_assoc, hp_idem.eq]
  obtain ⟨x₀, y₀, hx₀, hy₀, hne⟩ :=
    exists_eigen_ne_of_not_mul_eq_smul hM_herm hp_ne hpM hnot
  obtain ⟨Q, hQ_mem, hQ_idem, hQx₀, hQy₀⟩ :=
    exists_spectral_proj h hM_mem hM_herm x₀ y₀ hne
  have hcomm : Q * p = p * Q := h.mul_comm_of_mem_bmAlgebra hQ_mem hp_mem
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ :=
    split_alg_of_comm h hp_mem hQ_mem hp_idem hQ_idem hcomm
  refine ⟨Q * p, (1 - Q) * p, h1, h2, h3, h4, h5, h6, ?_, ?_, h7⟩
  · intro h0
    have hmul := congrArg (fun B : Matrix X X ℝ => B *ᵥ ⇑(hM_herm.eigenvectorBasis x₀)) h0
    rw [Matrix.zero_mulVec, hcomm, ← Matrix.mulVec_mulVec, hQx₀] at hmul
    exact hx₀ hmul
  · intro h0
    have hmul := congrArg (fun B : Matrix X X ℝ => B *ᵥ ⇑(hM_herm.eigenvectorBasis y₀)) h0
    rw [Matrix.zero_mulVec, sub_mul, one_mul, Matrix.sub_mulVec, hcomm,
      ← Matrix.mulVec_mulVec, hQy₀, Matrix.mulVec_zero, sub_zero] at hmul
    exact hy₀ hmul

end Splitting

section Existence

variable {X : Type*} [Fintype X] [DecidableEq X] {d : ℕ} {rel : X → X → Fin (d + 1)}

private structure IsOrthoFamily (rel : X → X → Fin (d + 1)) (P : Finset (Matrix X X ℝ)) :
    Prop where
  mem_bmAlgebra : ∀ p ∈ P, p ∈ bmAlgebra rel
  idem : ∀ p ∈ P, IsIdempotentElem p
  ne_zero : ∀ p ∈ P, p ≠ 0
  ortho : ∀ p ∈ P, ∀ q ∈ P, p ≠ q → p * q = 0
  sum_eq_one : ∑ p ∈ P, p = 1
  zero_mem : ((Fintype.card X : ℝ)⁻¹ • Matrix.of fun _ _ : X => (1 : ℝ)) ∈ P

private theorem exists_isOrthoFamily (h : IsAssocScheme rel) :
    ∃ P : Finset (Matrix X X ℝ), IsOrthoFamily rel P := by
  let e₀ : Matrix X X ℝ := (Fintype.card X : ℝ)⁻¹ • Matrix.of fun _ _ => 1
  have he₀_mem : e₀ ∈ bmAlgebra rel := allOnes_inv_mem_bmAlgebra rel
  have he₀_idem : IsIdempotentElem e₀ := isIdempotentElem_allOnes_inv h
  have he₀_ne : e₀ ≠ 0 := allOnes_inv_ne_zero h
  by_cases h1 : 1 - e₀ = 0
  · refine ⟨{e₀}, ?_⟩
    refine ⟨fun p hp => ?_, fun p hp => ?_, fun p hp => ?_, fun p hp q hq hne => ?_, ?_, ?_⟩
    · simp only [Finset.mem_singleton] at hp; exact hp ▸ he₀_mem
    · simp only [Finset.mem_singleton] at hp; exact hp ▸ he₀_idem
    · simp only [Finset.mem_singleton] at hp; exact hp ▸ he₀_ne
    · simp only [Finset.mem_singleton] at hp hq; exact absurd (hp.trans hq.symm) hne
    · simp [sub_eq_zero.mp h1]
    · simp [e₀]
  · have hne : e₀ ≠ 1 - e₀ := by
      intro heq
      have h0 : e₀ * e₀ = e₀ * (1 - e₀) := congrArg (e₀ * ·) heq
      rw [he₀_idem.eq, mul_sub, mul_one, he₀_idem.eq, sub_self] at h0
      exact he₀_ne h0
    refine ⟨{e₀, 1 - e₀}, ?_⟩
    refine ⟨fun p hp => ?_, fun p hp => ?_, fun p hp => ?_, fun p hp q hq hne' => ?_, ?_, ?_⟩
    · simp only [Finset.mem_insert, Finset.mem_singleton] at hp
      rcases hp with rfl | rfl
      · exact he₀_mem
      · exact Submodule.sub_mem _ h.one_mem_bmAlgebra he₀_mem
    · simp only [Finset.mem_insert, Finset.mem_singleton] at hp
      rcases hp with rfl | rfl
      · exact he₀_idem
      · exact he₀_idem.one_sub
    · simp only [Finset.mem_insert, Finset.mem_singleton] at hp
      rcases hp with rfl | rfl
      · exact he₀_ne
      · exact h1
    · simp only [Finset.mem_insert, Finset.mem_singleton] at hp hq
      rcases hp with rfl | rfl <;> rcases hq with rfl | rfl
      · exact absurd rfl hne'
      · rw [mul_sub, mul_one, he₀_idem.eq, sub_self]
      · rw [sub_mul, one_mul, he₀_idem.eq, sub_self]
      · exact absurd rfl hne'
    · rw [Finset.sum_pair hne, add_sub_cancel]
    · simp [e₀]

private theorem isOrthoFamily_card_le (h : IsAssocScheme rel) {P : Finset (Matrix X X ℝ)}
    (hP : IsOrthoFamily rel P) : P.card ≤ d + 1 := by
  have hortho : OrthogonalIdempotents (Subtype.val : P → Matrix X X ℝ) :=
    ⟨fun ⟨p, hp⟩ => hP.idem p hp, fun ⟨p, hp⟩ ⟨q, hq⟩ hne =>
      hP.ortho p hp q hq (fun h => hne (Subtype.ext h))⟩
  have hli : LinearIndependent ℝ (Subtype.val : P → Matrix X X ℝ) :=
    hortho.linearIndependent fun ⟨p, hp⟩ => hP.ne_zero p hp
  have hli_sub :
      LinearIndependent ℝ (fun x : P => (⟨x.val, hP.mem_bmAlgebra x.val x.property⟩ :
        bmAlgebra rel)) :=
    LinearIndependent.of_comp (bmAlgebra rel).subtype hli
  have hcard := hli_sub.fintype_card_le_finrank
  rwa [Fintype.card_coe, h.finrank_bmAlgebra] at hcard

private theorem ortho_split_of_mem {P : Finset (Matrix X X ℝ)} (hP : IsOrthoFamily rel P)
    {p p₁ p₂ s : Matrix X X ℝ} (hp : p ∈ P) (hs : s ∈ P.erase p)
    (hp₁_idem : IsIdempotentElem p₁) (hp₂_idem : IsIdempotentElem p₂)
    (hp₁₂ : p₁ * p₂ = 0) (hp₂₁ : p₂ * p₁ = 0) (hadd : p₁ + p₂ = p) :
    s * p₁ = 0 ∧ p₁ * s = 0 ∧ s * p₂ = 0 ∧ p₂ * s = 0 := by
  have hsp : s * p = 0 := hP.ortho s (Finset.mem_of_mem_erase hs) p hp
    (Finset.ne_of_mem_erase hs)
  have hps : p * s = 0 := hP.ortho p hp s (Finset.mem_of_mem_erase hs)
    (Finset.ne_of_mem_erase hs).symm
  have hp_p₁ : p * p₁ = p₁ := by rw [← hadd, add_mul, hp₁_idem.eq, hp₂₁, add_zero]
  have hp₁_p : p₁ * p = p₁ := by rw [← hadd, mul_add, hp₁_idem.eq, hp₁₂, add_zero]
  have hp_p₂ : p * p₂ = p₂ := by rw [← hadd, add_mul, hp₁₂, hp₂_idem.eq, zero_add]
  have hp₂_p : p₂ * p = p₂ := by rw [← hadd, mul_add, hp₂₁, hp₂_idem.eq, zero_add]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← hp_p₁, ← Matrix.mul_assoc, hsp, Matrix.zero_mul]
  · rw [← hp₁_p, Matrix.mul_assoc, hps, Matrix.mul_zero]
  · rw [← hp_p₂, ← Matrix.mul_assoc, hsp, Matrix.zero_mul]
  · rw [← hp₂_p, Matrix.mul_assoc, hps, Matrix.mul_zero]

private theorem isOrthoFamily_replace_split
    {P : Finset (Matrix X X ℝ)} (hP : IsOrthoFamily rel P) {p p₁ p₂ : Matrix X X ℝ}
    (hp : p ∈ P)
    (hp_ne_e₀ : p ≠ (Fintype.card X : ℝ)⁻¹ • Matrix.of fun _ _ : X => (1 : ℝ))
    (hp₁_mem : p₁ ∈ bmAlgebra rel) (hp₂_mem : p₂ ∈ bmAlgebra rel)
    (hp₁_idem : IsIdempotentElem p₁) (hp₂_idem : IsIdempotentElem p₂)
    (hp₁₂ : p₁ * p₂ = 0) (hp₂₁ : p₂ * p₁ = 0)
    (hp₁_ne : p₁ ≠ 0) (hp₂_ne : p₂ ≠ 0) (hadd : p₁ + p₂ = p) :
    ∃ Q : Finset (Matrix X X ℝ), IsOrthoFamily rel Q ∧ Q.card = P.card + 1 := by
  have hp₁_notMem : p₁ ∉ P.erase p := fun hmem =>
    hp₁_ne (by
      have hmul := hP.ortho p hp p₁ (Finset.mem_of_mem_erase hmem)
        (Finset.ne_of_mem_erase hmem).symm
      rwa [← hadd, add_mul, hp₁_idem.eq, hp₂₁, add_zero] at hmul)
  have hp₂_notMem : p₂ ∉ insert p₁ (P.erase p) := by
    intro hmem
    rcases Finset.mem_insert.mp hmem with rfl | hmem'
    · rw [hp₁_idem.eq] at hp₁₂; exact hp₂_ne hp₁₂
    · have hmul := hP.ortho p hp p₂ (Finset.mem_of_mem_erase hmem')
        (Finset.ne_of_mem_erase hmem').symm
      rw [← hadd, add_mul, hp₁₂, hp₂_idem.eq, zero_add] at hmul
      exact hp₂_ne hmul
  have hQ_prop : ∀ q ∈ insert p₂ (insert p₁ (P.erase p)),
      q ∈ bmAlgebra rel ∧ IsIdempotentElem q ∧ q ≠ 0 := by
    intro q hq
    simp only [Finset.mem_insert] at hq
    rcases hq with rfl | rfl | hq''
    · exact ⟨hp₂_mem, hp₂_idem, hp₂_ne⟩
    · exact ⟨hp₁_mem, hp₁_idem, hp₁_ne⟩
    · have hqP := Finset.mem_of_mem_erase hq''
      exact ⟨hP.mem_bmAlgebra q hqP, hP.idem q hqP, hP.ne_zero q hqP⟩
  refine ⟨insert p₂ (insert p₁ (P.erase p)),
    ⟨fun q hq => (hQ_prop q hq).1, fun q hq => (hQ_prop q hq).2.1,
      fun q hq => (hQ_prop q hq).2.2, fun q hq r hr hne => ?_, ?_, ?_⟩, ?_⟩
  · have hs : ∀ s ∈ P.erase p,
        s * p₁ = 0 ∧ p₁ * s = 0 ∧ s * p₂ = 0 ∧ p₂ * s = 0 :=
      fun _ hs' => ortho_split_of_mem hP hp hs' hp₁_idem hp₂_idem hp₁₂ hp₂₁ hadd
    simp only [Finset.mem_insert] at hq hr
    rcases hq with rfl | rfl | hq'' <;> rcases hr with rfl | rfl | hr''
    · exact absurd rfl hne
    · exact hp₂₁
    · exact (hs r hr'').2.2.2
    · exact hp₁₂
    · exact absurd rfl hne
    · exact (hs r hr'').2.1
    · exact (hs q hq'').2.2.1
    · exact (hs q hq'').1
    · exact hP.ortho q (Finset.mem_of_mem_erase hq'') r
        (Finset.mem_of_mem_erase hr'') hne
  · rw [Finset.sum_insert hp₂_notMem, Finset.sum_insert hp₁_notMem, ← add_assoc,
      add_comm p₂ p₁, hadd, Finset.add_sum_erase P (fun x => x) hp, hP.sum_eq_one]
  · exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
      (Finset.mem_erase.mpr ⟨hp_ne_e₀.symm, hP.zero_mem⟩))
  · rw [Finset.card_insert_of_notMem hp₂_notMem, Finset.card_insert_of_notMem hp₁_notMem,
      Finset.card_erase_of_mem hp, Nat.sub_add_cancel (Finset.card_pos.mpr ⟨p, hp⟩)]

private theorem isOrthoFamily_maximal_minimal (h : IsAssocScheme rel)
    {P : Finset (Matrix X X ℝ)} (hP : IsOrthoFamily rel P)
    (hmax : ∀ Q : Finset (Matrix X X ℝ), IsOrthoFamily rel Q → Q.card ≤ P.card)
    {p : Matrix X X ℝ} (hp : p ∈ P) {A : Matrix X X ℝ} (hA : A ∈ bmAlgebra rel) :
    ∃ c : ℝ, A * p = c • p := by
  by_contra! hnot
  obtain ⟨p₁, p₂, hp₁_mem, hp₂_mem, hp₁_idem, hp₂_idem,
      hp₁₂, hp₂₁, hp₁_ne, hp₂_ne, hadd⟩ :=
    exists_split_of_not_mul_eq_smul h (hP.mem_bmAlgebra p hp) (hP.idem p hp)
      (hP.ne_zero p hp) hA hnot
  have hp_ne_e₀ : p ≠ (Fintype.card X : ℝ)⁻¹ • Matrix.of fun _ _ : X => (1 : ℝ) := by
    intro hpe₀
    subst hpe₀
    obtain ⟨c, hc⟩ := exists_mul_allOnes_inv_eq_smul h hA
    exact hnot c hc
  obtain ⟨Q, hQ_ortho, hQ_card⟩ := isOrthoFamily_replace_split hP hp hp_ne_e₀
    hp₁_mem hp₂_mem hp₁_idem hp₂_idem hp₁₂ hp₂₁ hp₁_ne hp₂_ne hadd
  have hcard_le := hmax Q hQ_ortho
  omega

private theorem exists_maximal_isOrthoFamily (h : IsAssocScheme rel) :
    ∃ P : Finset (Matrix X X ℝ), IsOrthoFamily rel P ∧
      ∀ Q : Finset (Matrix X X ℝ), IsOrthoFamily rel Q → Q.card ≤ P.card := by
  classical
  let S : Finset ℕ := (Finset.range (d + 2)).filter fun n =>
    ∃ P : Finset (Matrix X X ℝ), IsOrthoFamily rel P ∧ P.card = n
  have hS_ne : S.Nonempty := by
    obtain ⟨P, hP⟩ := exists_isOrthoFamily h
    exact ⟨P.card, Finset.mem_filter.mpr
      ⟨Finset.mem_range.mpr (Nat.lt_succ_of_le (isOrthoFamily_card_le h hP)), P, hP, rfl⟩⟩
  obtain ⟨P, hP, hP_card⟩ := (Finset.mem_filter.mp (Finset.max'_mem S hS_ne)).2
  refine ⟨P, hP, fun Q hQ => ?_⟩
  rw [hP_card]
  exact Finset.le_max' S Q.card (Finset.mem_filter.mpr
    ⟨Finset.mem_range.mpr (Nat.lt_succ_of_le (isOrthoFamily_card_le h hQ)), Q, hQ, rfl⟩)

/-- **Existence of primitive idempotents.** Every symmetric association scheme with `d` classes
admits a family `E : Fin (d + 1) → Matrix X X ℝ` of primitive idempotents with
`E 0 = |X|⁻¹ J`. -/
theorem exists_isPrimitiveIdempotents (h : IsAssocScheme rel) :
    ∃ E, IsPrimitiveIdempotents rel E := by
  classical
  obtain ⟨P, hP, hmax⟩ := exists_maximal_isOrthoFamily h
  have hspan : bmAlgebra rel ≤ Submodule.span ℝ (P : Set (Matrix X X ℝ)) := by
    intro A hA
    rw [← mul_one A, ← hP.sum_eq_one, Finset.mul_sum]
    refine Submodule.sum_mem _ fun p hp => ?_
    obtain ⟨c, hc⟩ := isOrthoFamily_maximal_minimal h hP hmax hp hA
    rw [hc]
    exact Submodule.smul_mem _ c (Submodule.subset_span hp)
  have hcard : P.card = d + 1 := by
    refine le_antisymm (isOrthoFamily_card_le h hP) ?_
    have hsub : bmAlgebra rel = Submodule.span ℝ (P : Set (Matrix X X ℝ)) :=
      le_antisymm hspan (Submodule.span_le.mpr fun p hp => hP.mem_bmAlgebra p hp)
    have hfin := congrArg (fun M : Submodule ℝ (Matrix X X ℝ) => Module.finrank ℝ M) hsub
    rw [h.finrank_bmAlgebra] at hfin
    rw [hfin]
    simpa [Set.finrank] using finrank_span_le_card (R := ℝ) (s := (P : Set (Matrix X X ℝ)))
  let e₀ : Matrix X X ℝ := (Fintype.card X : ℝ)⁻¹ • Matrix.of fun _ _ => 1
  let P' := P.erase e₀
  have hP'_card : Fintype.card P' = d := by
    rw [Fintype.card_coe, Finset.card_erase_of_mem hP.zero_mem, hcard]; simp
  let equiv' : Fin d ≃ P' := (finCongr hP'_card.symm).trans (Fintype.equivFin P').symm
  let E : Fin (d + 1) → Matrix X X ℝ := Fin.cases e₀ fun k => (equiv' k).val
  have hE_mem : ∀ i, E i ∈ P := Fin.cases hP.zero_mem fun k =>
    Finset.mem_of_mem_erase (equiv' k).property
  have hE_inj : Function.Injective E := by
    intro i j hij
    refine Fin.cases (Fin.cases (fun _ => rfl) (fun k hk => ?_) j)
      (fun k => Fin.cases (fun hk => ?_) (fun l hl => ?_) j) i hij
    · exact absurd hk.symm (Finset.ne_of_mem_erase (equiv' k).property)
    · exact absurd hk (Finset.ne_of_mem_erase (equiv' k).property)
    · exact congrArg Fin.succ (equiv'.injective (Subtype.ext hl))
  refine ⟨E, ⟨⟨fun i => hP.idem _ (hE_mem i), fun i j hij =>
      hP.ortho _ (hE_mem i) _ (hE_mem j) (fun heq => hij (hE_inj heq))⟩, ?_⟩,
      fun i => hP.ne_zero _ (hE_mem i), fun i => hP.mem_bmAlgebra _ (hE_mem i), rfl⟩
  rw [Fin.sum_univ_succ E]
  simp only [E, Fin.cases_zero, Fin.cases_succ]
  rw [Fintype.sum_equiv equiv' _ (fun p : P' => p.val) (fun _ => rfl),
    Finset.univ_eq_attach, Finset.sum_attach P' (fun x => x),
    Finset.add_sum_erase P (fun x => x) hP.zero_mem, hP.sum_eq_one]

end Existence

namespace IsPrimitiveIdempotents

variable {X : Type*} [Fintype X] [DecidableEq X] {d : ℕ} {rel : X → X → Fin (d + 1)}
  {E : Fin (d + 1) → Matrix X X ℝ}

/-- Every primitive idempotent is symmetric. -/
theorem transpose_eq (h : IsAssocScheme rel) (hE : IsPrimitiveIdempotents rel E)
    (i : Fin (d + 1)) : (E i)ᵀ = E i :=
  h.transpose_eq_of_mem_bmAlgebra (hE.mem_bmAlgebra i)

/-- Every primitive idempotent is Hermitian. -/
theorem isHermitian (h : IsAssocScheme rel) (hE : IsPrimitiveIdempotents rel E)
    (i : Fin (d + 1)) : (E i).IsHermitian := by
  rw [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial]
  exact hE.transpose_eq h i

/-- Every primitive idempotent is positive semidefinite. -/
theorem posSemidef (h : IsAssocScheme rel) (hE : IsPrimitiveIdempotents rel E)
    (i : Fin (d + 1)) : (E i).PosSemidef := by
  have hsq : (E i)ᴴ * E i = E i := by
    rw [Matrix.conjTranspose_eq_transpose_of_trivial, hE.transpose_eq h i,
      (hE.complete.idem i).eq]
  rw [← hsq]
  exact Matrix.posSemidef_conjTranspose_mul_self (E i)

/-- Any family of primitive idempotents is linearly independent over `ℝ`. -/
theorem linearIndependent (hE : IsPrimitiveIdempotents rel E) : LinearIndependent ℝ E :=
  hE.complete.toOrthogonalIdempotents.linearIndependent hE.ne_zero

/-- The primitive idempotents span the Bose–Mesner algebra. -/
theorem span_eq_bmAlgebra (hE : IsPrimitiveIdempotents rel E) :
    Submodule.span ℝ (Set.range E) = bmAlgebra rel := by
  have hle : Submodule.span ℝ (Set.range E) ≤ bmAlgebra rel :=
    Submodule.span_le.mpr fun _ ⟨i, hi⟩ => hi ▸ hE.mem_bmAlgebra i
  have hfin_le : Module.finrank ℝ (bmAlgebra rel) ≤ d + 1 := by
    calc Module.finrank ℝ (bmAlgebra rel)
        ≤ (Set.range (adjMat rel)).toFinset.card := by
          rw [bmAlgebra_eq_span]
          simpa [Set.finrank] using finrank_span_le_card (R := ℝ) (s := Set.range (adjMat rel))
      _ ≤ Fintype.card (Fin (d + 1)) := by
          rw [Set.toFinset_range]
          exact Finset.card_image_le
      _ = d + 1 := Fintype.card_fin _
  refine Submodule.eq_of_le_of_finrank_eq hle (le_antisymm (Submodule.finrank_mono hle) ?_)
  rw [finrank_span_eq_card hE.linearIndependent, Fintype.card_fin]
  exact hfin_le

/-- The basis of the Bose–Mesner algebra formed by a family of primitive idempotents. -/
noncomputable def basis (hE : IsPrimitiveIdempotents rel E) :
    Module.Basis (Fin (d + 1)) ℝ (bmAlgebra rel) :=
  Module.Basis.mk
    (v := fun i => ⟨E i, hE.mem_bmAlgebra i⟩)
    (LinearIndependent.of_comp (bmAlgebra rel).subtype hE.linearIndependent)
    (by
      rintro ⟨M, hM⟩ _
      have hmem : M ∈ Submodule.span ℝ (Set.range E) := hE.span_eq_bmAlgebra.symm ▸ hM
      rw [Submodule.mem_span_range_iff_exists_fun] at hmem
      obtain ⟨c, rfl⟩ := hmem
      have hsum : (⟨∑ i, c i • E i, hM⟩ : bmAlgebra rel) =
          ∑ i, c i • ⟨E i, hE.mem_bmAlgebra i⟩ := by
        ext1
        simp
      rw [hsum]
      exact Submodule.sum_mem _ fun i _ =>
        Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩))

@[simp]
theorem coe_basis (hE : IsPrimitiveIdempotents rel E)
    (i : Fin (d + 1)) : (hE.basis i : Matrix X X ℝ) = E i := by
  simp [basis]

/-- The multiplicity `tr (E i)` equals the rank of `E i`. -/
theorem trace_eq_rank (hE : IsPrimitiveIdempotents rel E) (i : Fin (d + 1)) :
    (E i).trace = ((E i).rank : ℝ) :=
  (hE.complete.idem i).trace_eq_rank

/-- Every primitive idempotent has nonzero trace. -/
theorem trace_ne_zero (hE : IsPrimitiveIdempotents rel E) (i : Fin (d + 1)) :
    (E i).trace ≠ 0 :=
  fun htr => hE.ne_zero i
    (Matrix.IsIdempotentElem.eq_zero_of_trace_eq_zero (K := ℝ) (hE.complete.idem i) htr)

/-- Every primitive idempotent has strictly positive rank. -/
theorem rank_pos (hE : IsPrimitiveIdempotents rel E) (i : Fin (d + 1)) :
    0 < (E i).rank := by
  by_contra h0
  have hr : (E i).rank = 0 := Nat.eq_zero_of_not_pos h0
  have htr : (E i).trace = 0 := by rw [hE.trace_eq_rank i, hr, Nat.cast_zero]
  exact hE.trace_ne_zero i htr

/-- Every primitive idempotent has strictly positive trace. -/
theorem trace_pos (hE : IsPrimitiveIdempotents rel E) (i : Fin (d + 1)) :
    0 < (E i).trace := by
  rw [hE.trace_eq_rank i]
  exact Nat.cast_pos.mpr (hE.rank_pos i)

/-- The zeroth primitive idempotent `E 0 = |X|⁻¹ J` has trace `1`. -/
theorem trace_zero (hE : IsPrimitiveIdempotents rel E) :
    (E 0).trace = 1 := by
  have hpos : (Fintype.card X : ℝ) ≠ 0 := fun h0 =>
    hE.ne_zero 0 (by rw [hE.eq_zero, h0, _root_.inv_zero, zero_smul])
  rw [hE.eq_zero, Matrix.trace_smul, Matrix.trace]
  simp [hpos]

/-- The zeroth primitive idempotent has rank `1`. -/
theorem rank_zero (hE : IsPrimitiveIdempotents rel E) :
    (E 0).rank = 1 := by
  have h1 := hE.trace_eq_rank 0
  rw [hE.trace_zero] at h1
  exact_mod_cast h1.symm

/-- The ranks of the primitive idempotents sum to `|X|`. -/
theorem sum_rank (hE : IsPrimitiveIdempotents rel E) :
    ∑ i, (E i).rank = Fintype.card X := by
  rw [← hE.complete.toOrthogonalIdempotents.rank_sum Finset.univ, hE.complete.complete,
    Matrix.rank_one]

/-- The traces (multiplicities) of the primitive idempotents sum to `|X|`. -/
theorem sum_trace (hE : IsPrimitiveIdempotents rel E) :
    ∑ i, (E i).trace = Fintype.card X := by
  simp_rw [hE.trace_eq_rank]
  rw [← Nat.cast_sum, hE.sum_rank]

/-- Expansion of any element of `bmAlgebra rel` in the basis `E`. -/
theorem eq_sum_smul (hE : IsPrimitiveIdempotents rel E)
    {M : Matrix X X ℝ} (hM : M ∈ bmAlgebra rel) :
    M = ∑ i, ((M * E i).trace / (E i).trace) • E i := by
  have hmem : M ∈ Submodule.span ℝ (Set.range E) := hE.span_eq_bmAlgebra.symm ▸ hM
  rw [Submodule.mem_span_range_iff_exists_fun] at hmem
  obtain ⟨c, hc⟩ := hmem
  have hcoeff : ∀ i, c i = (M * E i).trace / (E i).trace := by
    intro i
    have hmul : M * E i = c i • E i := by
      calc M * E i = (∑ j, c j • E j) * E i := by rw [hc]
        _ = ∑ j, c j • (E j * E i) := by simp [Finset.sum_mul]
        _ = c i • E i := by
          rw [Finset.sum_eq_single i]
          · rw [(hE.complete.idem i).eq]
          · intro j _ hji
            rw [hE.complete.ortho hji, smul_zero]
          · simp
    have htr := congrArg Matrix.trace hmul
    rw [Matrix.trace_smul, smul_eq_mul] at htr
    exact (eq_div_iff (hE.trace_ne_zero i)).mpr htr.symm
  conv_lhs => rw [← hc]
  exact Finset.sum_congr rfl fun i _ => by rw [hcoeff i]

/-- Every matrix `M` in the Bose–Mesner algebra acts on the range of `E i` by the scalar
`tr (M * E i) / tr (E i)`. -/
theorem mul_eq_smul (hE : IsPrimitiveIdempotents rel E)
    {M : Matrix X X ℝ} (hM : M ∈ bmAlgebra rel) (i : Fin (d + 1)) :
    M * E i = ((M * E i).trace / (E i).trace) • E i := by
  conv_lhs => rw [hE.eq_sum_smul hM]
  rw [Finset.sum_mul, Finset.sum_eq_single i]
  · rw [Matrix.smul_mul, (hE.complete.idem i).eq]
  · intro j _ hji
    rw [Matrix.smul_mul, hE.complete.ortho hji, smul_zero]
  · simp

/-- Every adjacency matrix `A_j` satisfies `A_j * E_i = (tr (A_j * E_i) / tr (E_i)) • E_i`. -/
theorem adjMat_mul (hE : IsPrimitiveIdempotents rel E)
    (i j : Fin (d + 1)) :
    adjMat rel j * E i = ((adjMat rel j * E i).trace / (E i).trace) • E i :=
  hE.mul_eq_smul (adjMat_mem_bmAlgebra rel j) i

/-- The column space of `E i` is a common eigenspace for every `M ∈ bmAlgebra rel`. -/
theorem mulVec_of_mem_range (hE : IsPrimitiveIdempotents rel E)
    {M : Matrix X X ℝ} (hM : M ∈ bmAlgebra rel) (i : Fin (d + 1)) {v : X → ℝ}
    (hv : v ∈ LinearMap.range (E i).mulVecLin) :
    M *ᵥ v = ((M * E i).trace / (E i).trace) • v := by
  obtain ⟨w, rfl⟩ := hv
  rw [Matrix.mulVecLin_apply, Matrix.mulVec_mulVec]
  conv_lhs => rw [hE.mul_eq_smul hM i]
  rw [Matrix.smul_mulVec]

/-- Vectors in the column spaces of distinct primitive idempotents are orthogonal. -/
theorem dotProduct_eq_zero_of_mem_range (h : IsAssocScheme rel) (hE : IsPrimitiveIdempotents rel E)
    {i j : Fin (d + 1)} (hij : i ≠ j) {u v : X → ℝ}
    (hu : u ∈ LinearMap.range (E i).mulVecLin)
    (hv : v ∈ LinearMap.range (E j).mulVecLin) :
    u ⬝ᵥ v = 0 := by
  obtain ⟨x, rfl⟩ := hu
  obtain ⟨y, rfl⟩ := hv
  have hT : E i *ᵥ x = x ᵥ* E i := by
    rw [← Matrix.vecMul_transpose, hE.transpose_eq h i]
  rw [Matrix.mulVecLin_apply, Matrix.mulVecLin_apply, hT, ← Matrix.dotProduct_mulVec,
    Matrix.mulVec_mulVec, hE.complete.ortho hij, Matrix.zero_mulVec, dotProduct_zero]

/-- The column spaces of distinct primitive idempotents have trivial intersection. -/
theorem disjoint_range (hE : IsPrimitiveIdempotents rel E) {i j : Fin (d + 1)} (hij : i ≠ j) :
    Disjoint (LinearMap.range (E i).mulVecLin) (LinearMap.range (E j).mulVecLin) := by
  rw [Submodule.disjoint_def]
  rintro v ⟨x, rfl⟩ ⟨y, hy⟩
  simp only [Matrix.mulVecLin_apply] at hy ⊢
  have h1 : E i *ᵥ (E i *ᵥ x) = E i *ᵥ x := by
    rw [Matrix.mulVec_mulVec, (hE.complete.idem i).eq]
  have h2 : E i *ᵥ (E j *ᵥ y) = 0 := by
    rw [Matrix.mulVec_mulVec, hE.complete.ortho hij, Matrix.zero_mulVec]
  rw [hy] at h2
  exact h1.symm.trans h2

/-- The column spaces of the primitive idempotents span `X → ℝ`. -/
theorem iSup_range_eq_top (hE : IsPrimitiveIdempotents rel E) :
    ⨆ i, LinearMap.range (E i).mulVecLin = ⊤ := by
  rw [eq_top_iff]
  intro v _
  have hv : v = ∑ i, (E i).mulVecLin v := by
    simp_rw [Matrix.mulVecLin_apply]
    rw [← Matrix.sum_mulVec, hE.complete.complete, Matrix.one_mulVec]
  rw [hv]
  exact Submodule.sum_mem _ fun i _ => Submodule.mem_iSup_of_mem i ⟨v, rfl⟩

private theorem eq_of_mul_ne_zero (hE : IsPrimitiveIdempotents rel E)
    {E' : Fin (d + 1) → Matrix X X ℝ} (hE' : IsPrimitiveIdempotents rel E')
    {i k : Fin (d + 1)} (hk : E' i * E k ≠ 0) : E' i = E k := by
  have hcomm : E k * E' i = E' i * E k := by
    have hmem := hE'.mem_bmAlgebra i
    rw [← hE.span_eq_bmAlgebra, Submodule.mem_span_range_iff_exists_fun] at hmem
    obtain ⟨c, hc⟩ := hmem
    rw [← hc, Finset.mul_sum, Finset.sum_mul, Finset.sum_eq_single k, Finset.sum_eq_single k]
    · simp only [Matrix.mul_smul, Matrix.smul_mul, (hE.complete.idem k).eq]
    · intro j _ hjk
      rw [Matrix.smul_mul, hE.complete.ortho hjk, smul_zero]
    · simp
    · intro j _ hjk
      rw [Matrix.mul_smul, hE.complete.ortho hjk.symm, smul_zero]
    · simp
  have hidem_eq : ∀ {A B : Matrix X X ℝ}, A ≠ 0 → B ≠ 0 → IsIdempotentElem A →
      ∀ c : ℝ, A * B = c • B → A * B ≠ 0 → A * B = B := by
    intro A B _ hB hA c hc hne
    have hsq : A * (A * B) = A * B := by rw [← Matrix.mul_assoc, hA.eq]
    rw [hc, Matrix.mul_smul, hc, smul_smul] at hsq
    have hc0 : c ≠ 0 := fun h0 => hne (by rw [hc, h0, zero_smul])
    have hcc : c * c = c := by
      by_contra hneq
      apply hB
      have h0 : (c * c - c) • B = 0 := by rw [sub_smul, hsq, sub_self]
      exact (smul_eq_zero.mp h0).resolve_left (sub_ne_zero.mpr hneq)
    rw [hc, (mul_eq_right₀ hc0).mp hcc, one_smul]
  have hEk : E' i * E k = E k := hidem_eq (hE'.ne_zero i) (hE.ne_zero k)
    (hE'.complete.idem i) _ (hE.mul_eq_smul (hE'.mem_bmAlgebra i) k) hk
  have hEi : E k * E' i = E' i := hidem_eq (hE.ne_zero k) (hE'.ne_zero i)
    (hE.complete.idem k) _ (hE'.mul_eq_smul (hE.mem_bmAlgebra k) i) (hcomm ▸ hk)
  exact hEi.symm.trans (hcomm.trans hEk)

/-- **Uniqueness of primitive idempotents.** Any two families of primitive idempotents of the same
scheme differ by a permutation of `Fin (d + 1)` fixing `0`. -/
theorem exists_perm (hE : IsPrimitiveIdempotents rel E)
    {E' : Fin (d + 1) → Matrix X X ℝ} (hE' : IsPrimitiveIdempotents rel E') :
    ∃ σ : Equiv.Perm (Fin (d + 1)), σ 0 = 0 ∧ ∀ i, E' i = E (σ i) := by
  have hex : ∀ i, ∃ k, E' i = E k := by
    intro i
    have hsum : ∑ k, E' i * E k = E' i := by
      rw [← Finset.mul_sum, hE.complete.complete, mul_one]
    have hne : ∃ k, E' i * E k ≠ 0 := by
      by_contra! hall
      exact hE'.ne_zero i (by simpa [hall] using hsum.symm)
    obtain ⟨k, hk⟩ := hne
    exact ⟨k, eq_of_mul_ne_zero hE hE' hk⟩
  choose f hf using hex
  have hf_inj : Function.Injective f := by
    intro i j hij
    have heq : E' i = E' j := by rw [hf i, hf j, hij]
    by_contra hne
    have h0 : E' i * E' j = 0 := hE'.complete.ortho hne
    rw [heq, (hE'.complete.idem j).eq] at h0
    exact hE'.ne_zero j h0
  let σ : Equiv.Perm (Fin (d + 1)) :=
    Equiv.ofBijective f (Finite.injective_iff_bijective.mp hf_inj)
  have hσ0 : σ 0 = 0 := by
    have h0 : E (σ 0) = E 0 := by
      simp only [σ, Equiv.ofBijective_apply]
      rw [← hf 0, hE'.eq_zero, hE.eq_zero]
    by_contra hne
    have hmul : E (σ 0) * E 0 = 0 := hE.complete.ortho hne
    rw [h0, (hE.complete.idem 0).eq] at hmul
    exact hE.ne_zero 0 hmul
  exact ⟨σ, hσ0, hf⟩

end IsPrimitiveIdempotents

end TauCeti
