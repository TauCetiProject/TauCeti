/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.Nonsingular

import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Mathlib.LinearAlgebra.StdBasis

/-!
# Families of vectors in general position

A family of vectors in an `n`-dimensional coordinate space is in general position when every
subfamily of cardinality `n` is linearly independent.  This file gives equivalent finset and
determinant formulations and records invariance under the operations used for families of linear
forms: restriction, rescaling, extension of scalars, and invertible changes of coordinates.

The final result verifies that the coordinate vectors together with their sum are in general
position.  This is the basic family of linear forms used in applications of the Subspace Theorem.

The terminology and motivating family follow J.-H. Evertse, *Diophantine Approximation*, lecture
notes (2019), Chapter 7, Section 7.1.
-/

public section

open Function Matrix

namespace TauCeti

variable {K K' ι κ : Type*} {n : ℕ}

/-- A family of vectors in `Fin n → K` is in general position if every subfamily indexed by an
injection from `Fin n` is linearly independent.  In particular, a family with fewer than `n`
members is in general position. -/
def InGeneralPosition [Field K] (L : ι → Fin n → K) : Prop :=
  ∀ e : Fin n → ι, Injective e → LinearIndependent K (L ∘ e)

namespace InGeneralPosition

variable [Field K] {L : ι → Fin n → K}

/-- Every subfamily of the dimension's cardinality is linearly independent. -/
theorem linearIndependent (hL : InGeneralPosition L) (s : Finset ι) (hs : s.card = n) :
    LinearIndependent K (fun i : s ↦ L i) := by
  classical
  let e : Fin n ≃ s := (s.equivFinOfCardEq hs).symm
  exact (linearIndependent_equiv e).mp
    (hL (Subtype.val ∘ e) (Subtype.val_injective.comp e.injective))

/-- General position is equivalent to nonvanishing of every maximal minor. -/
theorem _root_.TauCeti.inGeneralPosition_iff_det_ne_zero :
    InGeneralPosition L ↔
      ∀ (e : Fin n → ι), Injective e → (Matrix.of fun i j ↦ L (e i) j).det ≠ 0 := by
  simp only [InGeneralPosition]
  apply forall_congr'
  intro e
  apply forall_congr'
  intro _
  exact (Matrix.linearIndependent_row_iff
    (A := Matrix.of fun i j ↦ L (e i) j)).trans Matrix.nonsingular_iff_det_ne_zero

/-- For a family of exactly `n` vectors, general position is ordinary linear independence. -/
theorem _root_.TauCeti.inGeneralPosition_iff_linearIndependent [Fintype ι]
    (hcard : Fintype.card ι = n) :
    InGeneralPosition L ↔ LinearIndependent K L := by
  constructor
  · intro hL
    let e : Fin n ≃ ι := (Fintype.equivFinOfCardEq hcard).symm
    exact (linearIndependent_equiv e).mp (hL e e.injective)
  · intro hL e he
    exact hL.comp e he

/-- Restricting a family in general position along an injection preserves general position. -/
theorem comp_injective (hL : InGeneralPosition L) (f : κ → ι) (hf : Injective f) :
    InGeneralPosition (L ∘ f) := by
  intro e he
  simpa only [Function.comp_def] using hL (f ∘ e) (hf.comp he)

/-- Rescaling each vector by a nonzero scalar preserves general position. -/
theorem smul (hL : InGeneralPosition L) (c : ι → K) (hc : ∀ i, c i ≠ 0) :
    InGeneralPosition (fun i ↦ c i • L i) := by
  intro e he
  let u : Fin n → Kˣ := fun i ↦ Units.mk0 (c (e i)) (hc (e i))
  have hu := (hL e he).units_smul u
  convert hu using 1
  ext i j
  simp [Function.comp_apply, u]

/-- Applying a field homomorphism coefficientwise preserves general position. -/
theorem map [Field K'] (hL : InGeneralPosition L) (σ : K →+* K') :
    InGeneralPosition (fun i j ↦ σ (L i j)) := by
  rw [inGeneralPosition_iff_det_ne_zero] at hL ⊢
  intro e he
  have hB : Matrix.of (fun i j ↦ σ (L (e i) j)) =
      σ.mapMatrix (Matrix.of fun i j ↦ L (e i) j) := by
    ext i j
    simp
  rw [hB, ← σ.map_det]
  exact (map_ne_zero σ).mpr (hL e he)

/-- An invertible linear change of coordinates preserves general position.  A row vector `L i`
is transformed to `Aᵀ *ᵥ L i`, equivalently to right multiplication by `A`. -/
theorem comp_matrix (hL : InGeneralPosition L) (A : Matrix (Fin n) (Fin n) K)
    (hA : A.det ≠ 0) : InGeneralPosition (fun i ↦ Aᵀ *ᵥ L i) := by
  rw [inGeneralPosition_iff_det_ne_zero] at hL ⊢
  intro e he
  let B : Matrix (Fin n) (Fin n) K := Matrix.of fun i j ↦ L (e i) j
  have hBA : Matrix.of (fun i j ↦ (Aᵀ *ᵥ L (e i)) j) = B * A := by
    ext i j
    simp only [Matrix.of_apply, Matrix.mul_apply, Matrix.mulVec, dotProduct, transpose_apply, B]
    exact Finset.sum_congr rfl fun k _ ↦ by rw [mul_comm]
  rw [hBA, Matrix.det_mul]
  exact mul_ne_zero (hL e he) hA

/-- In dimension two, general position says exactly that no two distinct members of the family
are linearly dependent. -/
theorem _root_.TauCeti.inGeneralPosition_two_iff {L : ι → Fin 2 → K} :
    InGeneralPosition L ↔
      ∀ i j, i ≠ j → LinearIndependent K ![L i, L j] := by
  constructor
  · intro hL i j hij
    have h := hL ![i, j] (Matrix.injective_pair_iff_ne.mpr hij)
    convert h using 1
    ext k
    fin_cases k <;> rfl
  · intro h e he
    have hij : e 0 ≠ e 1 := he.ne (by decide)
    have h' := h (e 0) (e 1) hij
    convert h' using 1
    ext k
    fin_cases k <;> rfl

end InGeneralPosition

section CoordinateForms

variable [Field K]

/-- Omitting the `k`th coordinate vector, the remaining coordinate vectors together with the
all-ones vector are linearly independent.  The index `none` labels the all-ones vector and
`some j` labels the `j`th coordinate vector. -/
theorem linearIndependent_one_option_piSingle_ne (k : Fin n) :
    LinearIndependent K (fun o : Option {j : Fin n // j ≠ k} ↦
      o.casesOn' (fun _ ↦ (1 : K)) (fun j ↦ Pi.single j.1 (1 : K))) := by
  rw [linearIndependent_option']
  constructor
  · have h := (Pi.basisFun K (Fin n)).linearIndependent.comp
      (fun j : {j : Fin n // j ≠ k} ↦ j.1) Subtype.val_injective
    convert h using 1
    ext j i
    simp
  · intro hmem
    have hspan : Submodule.span K
        (Set.range fun j : {j : Fin n // j ≠ k} ↦
          (Pi.single j.1 (1 : K) : Fin n → K)) ≤
        LinearMap.ker (LinearMap.proj k) := by
      rw [Submodule.span_le]
      rintro _ ⟨j, rfl⟩
      simp [LinearMap.mem_ker, j.2]
    have hone := hspan hmem
    simp [LinearMap.mem_ker] at hone

/-- The `n` coordinate vectors together with their sum are in general position.  The index `none`
labels the sum and `some i` labels the `i`th coordinate vector. -/
theorem inGeneralPosition_coords_add_sum :
    InGeneralPosition (fun o : Option (Fin n) ↦
      o.casesOn' (fun _ ↦ 1 : Fin n → K) (fun i ↦ Pi.single i 1)) := by
  intro e he
  have hns : ¬Surjective e := by
    intro hsurj
    have hcard := Fintype.card_le_of_surjective e hsurj
    simp only [Fintype.card_option, Fintype.card_fin] at hcard
    omega
  simp only [Surjective] at hns
  push Not at hns
  obtain ⟨z, hz⟩ := hns
  cases z with
  | none =>
      have hex (i : Fin n) : ∃ j : Fin n, some j = e i := by
        cases hi : e i with
        | none => exact (hz i hi).elim
        | some j => exact ⟨j, rfl⟩
      choose f hf using hex
      have hf_inj : Injective f := by
        intro i j hij
        apply he
        rw [← hf i, ← hf j, hij]
      have hli := (Pi.basisFun K (Fin n)).linearIndependent.comp f hf_inj
      convert hli using 1
      ext i j
      rw [Function.comp_apply, ← hf i]
      simp
  | some k =>
      let emb : Option {j : Fin n // j ≠ k} → Option (Fin n) := Option.map Subtype.val
      have hex (i : Fin n) : ∃ q, emb q = e i := by
        cases hi : e i with
        | none => exact ⟨none, by simp [emb]⟩
        | some j =>
            have hjk : j ≠ k := by
              intro hjk
              subst j
              exact hz i hi
            exact ⟨some ⟨j, hjk⟩, by simp [emb]⟩
      choose f hf using hex
      have hf_inj : Injective f := by
        intro i j hij
        apply he
        rw [← hf i, ← hf j, hij]
      have hli := (linearIndependent_one_option_piSingle_ne (K := K) k).comp f hf_inj
      convert hli using 1
      ext i j
      rw [Function.comp_apply, ← hf i]
      cases hfi : f i <;> simp [emb, hfi]

end CoordinateForms

end TauCeti
