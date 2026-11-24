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
determinant formulations and shows that general position is unchanged by the operations used for
families of linear forms: rescaling, extension of scalars, and invertible changes of coordinates.
It is also preserved by restriction along an injection.

The final result verifies that the coordinate vectors together with their sum are in general
position.  This is the basic family of linear forms used in applications of the Subspace Theorem.

The terminology and motivating family follow J.-H. Evertse, *Diophantine Approximation*, lecture
notes (2019), Chapter 7, Section 7.1.
-/

public section

open Function Matrix

namespace TauCeti

variable {K ι κ : Type*} {n : ℕ}

/-- A family of vectors in `Fin n → K` is in general position if every subfamily indexed by an
injection from `Fin n` is linearly independent.  In particular, a family with fewer than `n`
members is in general position. -/
def InGeneralPosition [Field K] (L : ι → Fin n → K) : Prop :=
  ∀ e : Fin n → ι, Injective e → LinearIndependent K (L ∘ e)

variable [Field K] {L : ι → Fin n → K}

namespace InGeneralPosition

/-- Every subfamily of the dimension's cardinality is linearly independent. -/
theorem linearIndepOn (hL : InGeneralPosition L) (s : Finset ι) (hs : s.card = n) :
    LinearIndepOn K L (s : Set ι) := by
  classical
  -- Enumerate `s` by `Fin n`.
  let σ : Fin n → ι := Subtype.val ∘ (s.equivFinOfCardEq hs).symm
  have hσ : Injective σ := Subtype.val_injective.comp (Equiv.injective _)
  have hrange : Set.range σ = s := by simp [σ, Set.range_comp]
  rw [← hrange, linearIndepOn_range_iff hσ]
  exact hL σ hσ

/-- Restricting a family in general position along an injection preserves general position. -/
theorem comp_injective (hL : InGeneralPosition L) (f : κ → ι) (hf : Injective f) :
    InGeneralPosition (L ∘ f) := by
  intro e he
  simpa only [Function.comp_def] using hL (f ∘ e) (hf.comp he)

end InGeneralPosition

/-- General position is equivalent to nonvanishing of every maximal minor. -/
theorem inGeneralPosition_iff_det_ne_zero :
    InGeneralPosition L ↔
      ∀ (e : Fin n → ι), Injective e → (Matrix.of fun i j ↦ L (e i) j).det ≠ 0 :=
  forall₂_congr fun e _ ↦ by
    rw [← nonsingular_iff_det_ne_zero, ← linearIndependent_row_iff, row_of, comp_def]

/-- For a family of exactly `n` vectors, general position is ordinary linear independence. -/
theorem inGeneralPosition_iff_linearIndependent [Fintype ι] (hcard : Fintype.card ι = n) :
    InGeneralPosition L ↔ LinearIndependent K L :=
  ⟨fun hL ↦ (linearIndependent_equiv (Fintype.equivFinOfCardEq hcard).symm).mp
    (hL _ (Equiv.injective _)), fun hL e he ↦ hL.comp e he⟩

/-- Rescaling each vector by a nonzero scalar does not change general position. -/
@[simp]
theorem inGeneralPosition_smul_iff {c : ι → K} (hc : ∀ i, c i ≠ 0) :
    InGeneralPosition (fun i ↦ c i • L i) ↔ InGeneralPosition L := by
  refine forall₂_congr fun e _ ↦ ?_
  -- Rescaling by the nonzero scalars `c (e i)` is rescaling by units.
  have hu : (fun i ↦ c i • L i) ∘ e = (fun i ↦ Units.mk0 (c (e i)) (hc (e i))) • (L ∘ e) := by
    ext
    simp
  rw [hu, LinearIndependent.units_smul_iff]

/-- An invertible linear change of coordinates does not change general position: the row vectors
`L i` are multiplied on the right by a matrix `A` of nonzero determinant. -/
@[simp]
theorem inGeneralPosition_vecMul_iff {A : Matrix (Fin n) (Fin n) K} (hA : A.det ≠ 0) :
    InGeneralPosition (fun i ↦ L i ᵥ* A) ↔ InGeneralPosition L := by
  rw [inGeneralPosition_iff_det_ne_zero, inGeneralPosition_iff_det_ne_zero]
  refine forall₂_congr fun e _ ↦ ?_
  -- Each maximal minor is multiplied by `det A`.
  have hBA : Matrix.of (fun i j ↦ (L (e i) ᵥ* A) j) = Matrix.of (fun i j ↦ L (e i) j) * A := by
    ext i j
    simp [vecMul, dotProduct, Matrix.mul_apply]
  rw [hBA, det_mul, mul_ne_zero_iff_right hA]

/-- In dimension two, general position says exactly that no two distinct members of the family
are linearly dependent. -/
theorem inGeneralPosition_two_iff {L : ι → Fin 2 → K} :
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

section CoordinateForms

/-- Omitting the `k`th coordinate vector, the remaining coordinate vectors together with the
all-ones vector are linearly independent.  The index `none` labels the all-ones vector and
`some j` labels the `j`th coordinate vector. -/
theorem linearIndependent_one_option_piSingle_ne (k : Fin n) :
    LinearIndependent K (fun o : Option {j : Fin n // j ≠ k} ↦
      o.casesOn' (fun _ ↦ (1 : K)) (fun j ↦ Pi.single j.val (1 : K))) := by
  rw [linearIndependent_option']
  refine ⟨(Pi.linearIndependent_single_one (Fin n) K).comp _ Subtype.val_injective, ?_⟩
  intro hmem
  -- The remaining coordinate vectors all vanish at `k`, while the all-ones vector does not.
  have hspan : Submodule.span K
      (Set.range fun j : {j : Fin n // j ≠ k} ↦
        (Pi.single j.val (1 : K) : Fin n → K)) ≤
      LinearMap.ker (LinearMap.proj k) := by
    rw [Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    simp [LinearMap.mem_ker, j.property]
  simpa [LinearMap.mem_ker] using hspan hmem

/-- The `n` coordinate vectors together with their sum are in general position.  The index `none`
labels the sum and `some i` labels the `i`th coordinate vector. -/
theorem inGeneralPosition_coords_add_sum :
    InGeneralPosition (fun o : Option (Fin n) ↦
      o.casesOn' (fun _ ↦ 1 : Fin n → K) (fun i ↦ Pi.single i 1)) := by
  intro e he
  -- An injection from `Fin n` misses some index `z` of `Option (Fin n)`, which has `n + 1`.
  obtain ⟨z, hz⟩ : ∃ z, z ∉ Set.range e := by
    by_contra! h
    simpa using Fintype.card_le_of_surjective e fun z ↦ Set.mem_range.mp (h z)
  rw [← linearIndepOn_range_iff he]
  refine LinearIndepOn.mono ?_ (Set.subset_compl_singleton_iff.mpr hz)
  cases z with
  | none =>
      -- Without the sum, only the coordinate vectors remain.
      rw [← Set.compl_range_some, compl_compl, linearIndepOn_range_iff (Option.some_injective _)]
      simpa only [comp_def, Option.casesOn'_some] using Pi.linearIndependent_single_one (Fin n) K
  | some k =>
      -- Without the `k`th coordinate vector, use `linearIndependent_one_option_piSingle_ne`.
      have hrange : Set.range (Option.map (Subtype.val : {j : Fin n // j ≠ k} → Fin n)) =
          {some k}ᶜ := by
        ext (_ | j)
        · simp
        · simp only [Set.mem_range, Option.map_eq_some_iff]
          simp [eq_comm]
      rw [← hrange, linearIndepOn_range_iff (Option.map_injective Subtype.val_injective)]
      convert linearIndependent_one_option_piSingle_ne (K := K) k using 1
      ext (_ | j) <;> simp

end CoordinateForms

end TauCeti

namespace RingHom

open TauCeti

variable {K K' ι : Type*} {n : ℕ} [Field K] [Field K'] {L : ι → Fin n → K}

/-- Applying a field homomorphism coefficientwise does not change general position. -/
@[simp]
theorem inGeneralPosition_map_iff (σ : K →+* K') :
    InGeneralPosition (fun i j ↦ σ (L i j)) ↔ InGeneralPosition L := by
  rw [inGeneralPosition_iff_det_ne_zero, inGeneralPosition_iff_det_ne_zero]
  refine forall₂_congr fun e _ ↦ ?_
  have hB : Matrix.of (fun i j ↦ σ (L (e i) j)) =
      σ.mapMatrix (Matrix.of fun i j ↦ L (e i) j) := by
    ext i j
    simp
  rw [hB, ← σ.map_det, map_ne_zero]

end RingHom
