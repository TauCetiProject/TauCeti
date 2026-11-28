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
import Mathlib.LinearAlgebra.Dimension.Finrank
import TauCeti.Algebra.Ring.Idempotent.Basic
import TauCeti.Analysis.Matrix.Spectrum
import TauCeti.Data.Matrix.Mul
import TauCeti.LinearAlgebra.End.Idempotent
import TauCeti.LinearAlgebra.Matrix.Rank
import TauCeti.LinearAlgebra.Trace.Idempotent
import TauCeti.RingTheory.Idempotents.Eigenvalue
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
  apply_zero : E 0 = (Fintype.card X : ℝ)⁻¹ • Matrix.of fun _ _ => 1

end Definition

section Helpers

variable {X : Type*} [Fintype X] {d : ℕ} {rel : X → X → Fin (d + 1)}

private theorem allOnes_inv_mem_bmAlgebra (rel : X → X → Fin (d + 1)) :
    ((Fintype.card X : ℝ)⁻¹ • Matrix.of fun _ _ : X => (1 : ℝ)) ∈ bmAlgebra rel :=
  Submodule.smul_mem _ _ (allOnes_mem_bmAlgebra rel)

private theorem adjMat_mul_allOnes_inv (h : IsAssocScheme rel) (i : Fin (d + 1)) :
    adjMat rel i * ((Fintype.card X : ℝ)⁻¹ • Matrix.of fun _ _ : X => (1 : ℝ)) =
      valency rel i • ((Fintype.card X : ℝ)⁻¹ • Matrix.of fun _ _ : X => (1 : ℝ)) := by
  rw [Matrix.mul_smul, h.adjMat_mul_allOnes i, smul_comm]

private theorem exists_mul_allOnes_inv_eq_smul (h : IsAssocScheme rel) {M : Matrix X X ℝ}
    (hM : M ∈ bmAlgebra rel) :
    ∃ c : ℝ, M * ((Fintype.card X : ℝ)⁻¹ • Matrix.of fun _ _ : X => (1 : ℝ)) =
      c • ((Fintype.card X : ℝ)⁻¹ • Matrix.of fun _ _ : X => (1 : ℝ)) := by
  rw [bmAlgebra_eq_span] at hM
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
  have he₀_idem : IsIdempotentElem e₀ := Matrix.isIdempotentElem_card_inv_smul_allOnes
  have he₀_ne : e₀ ≠ 0 := haveI := h.nonempty; Matrix.card_inv_smul_allOnes_ne_zero
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
      rw [he₀_idem.eq, he₀_idem.mul_one_sub_self] at h0
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
      · exact he₀_idem.mul_one_sub_self
      · exact he₀_idem.one_sub_mul_self
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

private theorem isOrthoFamily_replace_split
    {P : Finset (Matrix X X ℝ)} (hP : IsOrthoFamily rel P) {p p₁ p₂ : Matrix X X ℝ}
    (hp : p ∈ P)
    (hp_ne_e₀ : p ≠ (Fintype.card X : ℝ)⁻¹ • Matrix.of fun _ _ : X => (1 : ℝ))
    (hp₁_mem : p₁ ∈ bmAlgebra rel) (hp₂_mem : p₂ ∈ bmAlgebra rel)
    (hp₁_idem : IsIdempotentElem p₁) (hp₂_idem : IsIdempotentElem p₂)
    (hp₁₂ : p₁ * p₂ = 0) (hp₂₁ : p₂ * p₁ = 0)
    (hp₁_ne : p₁ ≠ 0) (hp₂_ne : p₂ ≠ 0) (hadd : p₁ + p₂ = p) :
    ∃ Q : Finset (Matrix X X ℝ), IsOrthoFamily rel Q ∧ Q.card = P.card + 1 := by
  have hp₁_notMem : p₁ ∉ P.erase p := fun hmem => hp₁_ne <| by
    have hmul := hP.ortho p hp p₁ (Finset.mem_of_mem_erase hmem) (Finset.ne_of_mem_erase hmem).symm
    rwa [← hadd, hp₁_idem.add_mul_self_of_mul_eq_zero hp₂₁] at hmul
  have hp₂_notMem : p₂ ∉ insert p₁ (P.erase p) := by
    intro hmem
    rcases Finset.mem_insert.mp hmem with rfl | hmem'
    · rw [hp₁_idem.eq] at hp₁₂; exact hp₂_ne hp₁₂
    · have hmul := hP.ortho p hp p₂ (Finset.mem_of_mem_erase hmem')
        (Finset.ne_of_mem_erase hmem').symm
      rw [← hadd, add_comm p₁ p₂, hp₂_idem.add_mul_self_of_mul_eq_zero hp₁₂] at hmul
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
  · have hsp : ∀ s ∈ P.erase p, s * (p₁ + p₂) = 0 := fun s hs' =>
      hadd ▸ hP.ortho s (Finset.mem_of_mem_erase hs') p hp (Finset.ne_of_mem_erase hs')
    have hsp₂ : ∀ s ∈ P.erase p, s * (p₂ + p₁) = 0 := fun s hs' => add_comm p₁ p₂ ▸ hsp s hs'
    have hps : ∀ s ∈ P.erase p, (p₁ + p₂) * s = 0 := fun s hs' =>
      hadd ▸ hP.ortho p hp s (Finset.mem_of_mem_erase hs') (Finset.ne_of_mem_erase hs').symm
    have hps₂ : ∀ s ∈ P.erase p, (p₂ + p₁) * s = 0 := fun s hs' => add_comm p₁ p₂ ▸ hps s hs'
    simp only [Finset.mem_insert] at hq hr
    rcases hq with rfl | rfl | hq'' <;> rcases hr with rfl | rfl | hr''
    · exact absurd rfl hne
    · exact hp₂₁
    · exact hp₂_idem.mul_right_eq_zero_of_add_mul_eq_zero hp₂₁ (hps₂ r hr'')
    · exact hp₁₂
    · exact absurd rfl hne
    · exact hp₁_idem.mul_right_eq_zero_of_add_mul_eq_zero hp₁₂ (hps r hr'')
    · exact hp₂_idem.mul_left_eq_zero_of_mul_add_eq_zero hp₁₂ (hsp₂ q hq'')
    · exact hp₁_idem.mul_left_eq_zero_of_mul_add_eq_zero hp₂₁ (hsp q hq'')
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
    h.bmSubalgebra.exists_split_idempotent_of_isHermitian
      (fun M hM => Matrix.isHermitian_iff_isSymm.mpr
        (h.transpose_eq_of_mem_bmAlgebra (h.mem_bmSubalgebra_iff.mp hM)))
      (h.mem_bmSubalgebra_iff.mpr (hP.mem_bmAlgebra p hp)) (hP.idem p hp)
      (h.mem_bmSubalgebra_iff.mpr hA) hnot
  have hp_ne_e₀ : p ≠ (Fintype.card X : ℝ)⁻¹ • Matrix.of fun _ _ : X => (1 : ℝ) := by
    intro hpe₀
    subst hpe₀
    obtain ⟨c, hc⟩ := exists_mul_allOnes_inv_eq_smul h hA
    exact hnot c hc
  obtain ⟨Q, hQ_ortho, hQ_card⟩ := isOrthoFamily_replace_split hP hp hp_ne_e₀
    (h.mem_bmSubalgebra_iff.mp hp₁_mem) (h.mem_bmSubalgebra_iff.mp hp₂_mem)
    hp₁_idem hp₂_idem hp₁₂ hp₂₁ hp₁_ne hp₂_ne hadd
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
    (i : Fin (d + 1)) : (E i).IsHermitian :=
  Matrix.isHermitian_iff_isSymm.mpr (hE.transpose_eq h i)

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

/-- A family of primitive idempotents is injective. -/
theorem injective (hE : IsPrimitiveIdempotents rel E) : Function.Injective E :=
  hE.linearIndependent.injective

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
  (Module.Basis.span hE.linearIndependent).map
    (LinearEquiv.ofEq _ _ hE.span_eq_bmAlgebra)

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
theorem trace_apply_zero (hE : IsPrimitiveIdempotents rel E) :
    (E 0).trace = 1 := by
  have hpos : (Fintype.card X : ℝ) ≠ 0 := fun h0 =>
    hE.ne_zero 0 (by rw [hE.apply_zero, h0, _root_.inv_zero, zero_smul])
  rw [hE.apply_zero, Matrix.trace_smul, Matrix.trace]
  simp [hpos]

/-- The zeroth primitive idempotent has rank `1`. -/
theorem rank_apply_zero (hE : IsPrimitiveIdempotents rel E) :
    (E 0).rank = 1 := by
  have h1 := hE.trace_eq_rank 0
  rw [hE.trace_apply_zero] at h1
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

/-- Every matrix `M` in the Bose–Mesner algebra acts on the range of `E i` by the scalar
`tr (M * E i) / tr (E i)`. -/
theorem mul_eq_smul (hE : IsPrimitiveIdempotents rel E)
    {M : Matrix X X ℝ} (hM : M ∈ bmAlgebra rel) (i : Fin (d + 1)) :
    M * E i = ((M * E i).trace / (E i).trace) • E i := by
  have hmem : M ∈ Submodule.span ℝ (Set.range E) := hE.span_eq_bmAlgebra.symm ▸ hM
  rw [Submodule.mem_span_range_iff_exists_fun] at hmem
  obtain ⟨c, rfl⟩ := hmem
  have hmul := sum_smul_mul_eq_smul_of_pairwise_mul_eq_zero_of_sum_eq_one
    (fun _ _ _ _ hne => hE.complete.ortho hne) hE.complete.complete c (Finset.mem_univ i)
  have htr := congrArg Matrix.trace hmul
  rw [Matrix.trace_smul, smul_eq_mul] at htr
  have hc : c i = ((∑ j, c j • E j) * E i).trace / (E i).trace :=
    (eq_div_iff (hE.trace_ne_zero i)).mpr htr.symm
  conv_lhs => rw [hmul, hc]

/-- Every primitive idempotent is minimal among nonzero idempotents in the Bose–Mesner algebra:
if `p ∈ bmAlgebra rel` is a nonzero idempotent with `p * E i = p`, then `p = E i`. -/
theorem eq_of_isIdempotentElem_of_mul_eq (hE : IsPrimitiveIdempotents rel E)
    {p : Matrix X X ℝ} (hp_mem : p ∈ bmAlgebra rel) (hp_idem : IsIdempotentElem p)
    (hp_ne : p ≠ 0) {i : Fin (d + 1)} (hpE : p * E i = p) : p = E i :=
  hpE.symm.trans (hp_idem.mul_eq_right_of_mul_eq_smul (hE.mul_eq_smul hp_mem i) (hpE.symm ▸ hp_ne))

/-- Expansion of any element of `bmAlgebra rel` in the basis `E`. -/
theorem eq_sum_smul (hE : IsPrimitiveIdempotents rel E)
    {M : Matrix X X ℝ} (hM : M ∈ bmAlgebra rel) :
    M = ∑ i, ((M * E i).trace / (E i).trace) • E i := by
  calc M = M * 1 := (Matrix.mul_one M).symm
    _ = M * ∑ i, E i := by rw [hE.complete.complete]
    _ = ∑ i, M * E i := Finset.mul_sum _ _ _
    _ = ∑ i, ((M * E i).trace / (E i).trace) • E i :=
      Finset.sum_congr rfl fun i _ => hE.mul_eq_smul hM i

/-- The `basis`-coordinate of `M ∈ bmAlgebra rel` at `i` is `tr (M * E i) / tr (E i)`. -/
@[simp]
theorem basis_repr (hE : IsPrimitiveIdempotents rel E) (M : bmAlgebra rel)
    (i : Fin (d + 1)) :
    hE.basis.repr M i = ((M : Matrix X X ℝ) * E i).trace / (E i).trace := by
  have hM : M = ∑ j, (((M : Matrix X X ℝ) * E j).trace / (E j).trace) • hE.basis j := by
    apply Subtype.ext
    simpa [Submodule.coe_sum, SetLike.val_smul, coe_basis] using hE.eq_sum_smul M.property
  conv_lhs => rw [hM]
  simp [Finsupp.single_apply]

/-- Every adjacency matrix `A_j` satisfies `A_j * E_i = (tr (A_j * E_i) / tr (E_i)) • E_i`. -/
theorem adjMat_mul_eq_smul (hE : IsPrimitiveIdempotents rel E)
    (i j : Fin (d + 1)) :
    adjMat rel j * E i = ((adjMat rel j * E i).trace / (E i).trace) • E i :=
  hE.mul_eq_smul (adjMat_mem_bmAlgebra rel j) i

/-- The column space of `E i` is a common eigenspace for every `M ∈ bmAlgebra rel`. -/
theorem mulVec_eq_smul_of_mem_range (hE : IsPrimitiveIdempotents rel E)
    {M : Matrix X X ℝ} (hM : M ∈ bmAlgebra rel) (i : Fin (d + 1)) {v : X → ℝ}
    (hv : v ∈ LinearMap.range (E i).mulVecLin) :
    M *ᵥ v = ((M * E i).trace / (E i).trace) • v := by
  obtain ⟨w, rfl⟩ := hv
  rw [Matrix.mulVecLin_apply, Matrix.mulVec_mulVec]
  conv_lhs => rw [hE.mul_eq_smul hM i]
  rw [Matrix.smul_mulVec]

/-- The column space of `E i` is precisely the simultaneous eigenspace of the adjacency
matrices with eigenvalues `tr (A_j * E i) / tr (E i)`. -/
theorem mem_range_iff_forall_adjMat_mulVec (hE : IsPrimitiveIdempotents rel E)
    (i : Fin (d + 1)) {v : X → ℝ} :
    v ∈ LinearMap.range (E i).mulVecLin ↔
      ∀ j, adjMat rel j *ᵥ v = ((adjMat rel j * E i).trace / (E i).trace) • v := by
  refine ⟨fun hv j => hE.mulVec_eq_smul_of_mem_range (adjMat_mem_bmAlgebra rel j) i hv,
    fun hv => ?_⟩
  obtain ⟨c, hc⟩ := (mem_bmAlgebra_iff rel).mp (hE.mem_bmAlgebra i)
  have hEi : E i *ᵥ v = ((E i * E i).trace / (E i).trace) • v := by
    calc E i *ᵥ v
        = (∑ j, c j • adjMat rel j) *ᵥ v := by rw [← hc]
      _ = (∑ j, c j * ((adjMat rel j * E i).trace / (E i).trace)) • v := by
          simp_rw [Matrix.sum_mulVec, Matrix.smul_mulVec, hv, smul_smul, ← Finset.sum_smul]
      _ = (((∑ j, c j • adjMat rel j) * E i).trace / (E i).trace) • v := by
          simp only [Matrix.sum_mul, Matrix.smul_mul, Matrix.trace_sum, Matrix.trace_smul,
            smul_eq_mul, Finset.sum_div, mul_div_assoc]
      _ = ((E i * E i).trace / (E i).trace) • v := by rw [hc]
  rw [(hE.complete.idem i).eq, div_self (hE.trace_ne_zero i), one_smul] at hEi
  exact ⟨v, hEi⟩

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
    Disjoint (LinearMap.range (E i).mulVecLin) (LinearMap.range (E j).mulVecLin) :=
  IsIdempotentElem.disjoint_range_of_mul_eq_zero
    (by rw [IsIdempotentElem, Module.End.mul_eq_comp, ← Matrix.mulVecLin_mul,
      (hE.complete.idem i).eq])
    (by rw [Module.End.mul_eq_comp, ← Matrix.mulVecLin_mul, hE.complete.ortho hij,
      Matrix.mulVecLin_zero])

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
    conv_lhs => rw [hE.eq_sum_smul (hE'.mem_bmAlgebra i)]
    rw [mul_sum_smul_eq_smul_of_pairwise_mul_eq_zero_of_sum_eq_one
        (fun _ _ _ _ hne => hE.complete.ortho hne) hE.complete.complete _ (Finset.mem_univ k),
      ← hE.mul_eq_smul (hE'.mem_bmAlgebra i) k]
  have hEk : E' i * E k = E k := (hE'.complete.idem i).mul_eq_right_of_mul_eq_smul
    (hE.mul_eq_smul (hE'.mem_bmAlgebra i) k) hk
  have hEi : E k * E' i = E' i := (hE.complete.idem k).mul_eq_right_of_mul_eq_smul
    (hE'.mul_eq_smul (hE.mem_bmAlgebra k) i) (hcomm ▸ hk)
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
  have hf_inj : Function.Injective f := fun i j hij =>
    hE'.injective (by rw [hf i, hf j, hij])
  let σ : Equiv.Perm (Fin (d + 1)) :=
    Equiv.ofBijective f (Finite.injective_iff_bijective.mp hf_inj)
  have hσ0 : σ 0 = 0 := hE.injective <| by
    simp only [σ, Equiv.ofBijective_apply]
    rw [← hf 0, hE'.apply_zero, hE.apply_zero]
  exact ⟨σ, hσ0, hf⟩

end IsPrimitiveIdempotents

end TauCeti
