/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
public import Mathlib.LinearAlgebra.Matrix.Trace

import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination

/-!
# The conjugation action of `SL₂` on trace-zero matrices

The group `SL₂(F)` acts by conjugation on the trace-zero `2 × 2` matrices `𝔰𝔩₂(F)`, the adjoint
representation. Over a field in which `2 ≠ 0` this representation is irreducible: a nonzero
subspace of trace-zero matrices stable under conjugation by `SL₂(F)` is all of `𝔰𝔩₂(F)`.

Conjugating a nonzero trace-zero matrix by the upper unipotent matrices `[[1, ±1], [0, 1]]` and
subtracting produces a nonzero multiple of `E = [[0, 1], [0, 0]]`; this is where `2 ≠ 0` enters.
Conjugating `E` by `[[0, 1], [-1, 0]]` and by `[[1, 0], [1, 1]]` then produces
`F = [[0, 0], [1, 0]]` and `H = [[1, 0], [0, -1]]`, which together with `E` span `𝔰𝔩₂(F)`.

Over `𝔽_ℓ` this irreducibility drives Serre's lifting lemma for closed subgroups of `SL₂(ℤ_ℓ)`:
the successive layers `Γ(ℓᵏ) / Γ(ℓᵏ⁺¹)` of a subgroup of `SL₂(ℤ_ℓ)` that surjects onto
`SL₂(𝔽_ℓ)` are subspaces of `𝔰𝔩₂(𝔽_ℓ)` stable under `SL₂(𝔽_ℓ)`-conjugation. In characteristic
`2` the statement fails, since the scalar matrices are then trace-zero and conjugation-invariant.

## Main results

* `TauCeti.eq_ker_traceLinearMap_of_conj_mem`: over a field with `2 ≠ 0`, a nonzero subspace of
  trace-zero `2 × 2` matrices stable under conjugation by `SL₂(F)` is the space of all trace-zero
  matrices.

## References

* J.-P. Serre, *Abelian ℓ-adic representations and elliptic curves*, IV-23, Lemma 3 (the
  irreducibility of the adjoint representation of `SL₂(𝔽_ℓ)` for odd `ℓ`).
-/

public section

namespace TauCeti

open Matrix

open scoped MatrixGroups

variable {F : Type*} [Field F]

/-- Conjugating by a determinant-one matrix `M`, written with its adjugate as inverse, keeps a
conjugation-stable subspace. -/
private theorem mul_mul_adjugate_mem {V : Submodule F (Matrix (Fin 2) (Fin 2) F)}
    (hconj : ∀ (g : SL(2, F)) (X : Matrix (Fin 2) (Fin 2) F), X ∈ V →
      (g : Matrix (Fin 2) (Fin 2) F) * X * ((g⁻¹ : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) ∈ V)
    {M : Matrix (Fin 2) (Fin 2) F} (hM : M.det = 1) {X : Matrix (Fin 2) (Fin 2) F} (hX : X ∈ V) :
    M * X * M.adjugate ∈ V := by
  simpa [SpecialLinearGroup.coe_inv] using hconj (.mk M hM) X hX

/-- A nonzero subspace of trace-zero `2 × 2` matrices over a field with `2 ≠ 0` that is stable
under conjugation by `SL₂(F)` contains `E = [[0, 1], [0, 0]]`: conjugating a nonzero element by
`[[1, ±1], [0, 1]]` and subtracting it produces a nonzero multiple of `E`. -/
private theorem upper_mem_of_conj_mem (h2 : (2 : F) ≠ 0)
    {V : Submodule F (Matrix (Fin 2) (Fin 2) F)}
    (hV : V ≤ LinearMap.ker (traceLinearMap (Fin 2) F F)) (hV0 : V ≠ ⊥)
    (hconj : ∀ (g : SL(2, F)) (X : Matrix (Fin 2) (Fin 2) F), X ∈ V →
      (g : Matrix (Fin 2) (Fin 2) F) * X * ((g⁻¹ : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) ∈ V) :
    !![0, 1; 0, 0] ∈ V := by
  obtain ⟨X, hXV, hX0⟩ := (Submodule.ne_bot_iff V).mp hV0
  obtain ⟨a, b, c, d, rfl⟩ : ∃ a b c d : F, X = !![a, b; c, d] := ⟨_, _, _, _, eta_fin_two X⟩
  obtain rfl : d = -a := by
    have := hV hXV
    simp only [LinearMap.mem_ker, traceLinearMap_apply, trace_fin_two_of] at this
    linear_combination this
  -- The conjugate of `X` by `[[1, t], [0, 1]]`, minus `X`.
  have hD : ∀ t : F, !![t * c, -(2 * t * a) - t ^ 2 * c; 0, -(t * c)] ∈ V := by
    intro t
    have hu : (!![1, t; 0, 1] : Matrix (Fin 2) (Fin 2) F).det = 1 := by simp [det_fin_two]
    convert V.sub_mem (mul_mul_adjugate_mem hconj hu hXV) hXV using 1
    ext i j
    fin_cases i <;> fin_cases j <;> simp [adjugate_fin_two_of] <;> ring
  by_cases hc0 : c = 0
  · subst hc0
    by_cases ha0 : a = 0
    · subst ha0
      have hb0 : b ≠ 0 := by
        rintro rfl
        exact hX0 (by ext i j; fin_cases i <;> fin_cases j <;> simp)
      convert V.smul_mem b⁻¹ hXV using 1
      ext i j
      fin_cases i <;> fin_cases j <;> simp [hb0]
    · convert V.smul_mem (-(2 * a))⁻¹ (hD 1) using 1
      ext i j
      fin_cases i <;> fin_cases j <;> simp [mul_assoc, ha0, h2]
  · convert V.smul_mem (-(2 * c))⁻¹ (V.add_mem (hD 1) (hD (-1))) using 1
    ext i j
    fin_cases i <;> fin_cases j
    · simp
    · simp
      field_simp
      ring
    · simp
    · simp

/-- **The adjoint representation of `SL₂` is irreducible** away from characteristic `2`: over a
field `F` with `2 ≠ 0`, a nonzero subspace `V` of trace-zero `2 × 2` matrices that is stable under
conjugation by `SL₂(F)` is the space of all trace-zero matrices. -/
theorem eq_ker_traceLinearMap_of_conj_mem (h2 : (2 : F) ≠ 0)
    {V : Submodule F (Matrix (Fin 2) (Fin 2) F)}
    (hV : V ≤ LinearMap.ker (traceLinearMap (Fin 2) F F)) (hV0 : V ≠ ⊥)
    (hconj : ∀ (g : SL(2, F)) (X : Matrix (Fin 2) (Fin 2) F), X ∈ V →
      (g : Matrix (Fin 2) (Fin 2) F) * X * ((g⁻¹ : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) ∈ V) :
    V = LinearMap.ker (traceLinearMap (Fin 2) F F) := by
  have hc := fun {M : Matrix (Fin 2) (Fin 2) F} (hM : M.det = 1) {X} (hX : X ∈ V) ↦
    mul_mul_adjugate_mem hconj hM hX
  have hE := upper_mem_of_conj_mem h2 hV hV0 hconj
  -- `F = [[0, 0], [1, 0]]` and `H = [[1, 0], [0, -1]]` lie in `V`.
  have hw : (!![0, 1; -1, 0] : Matrix (Fin 2) (Fin 2) F).det = 1 := by simp [det_fin_two]
  have hl : (!![1, 0; 1, 1] : Matrix (Fin 2) (Fin 2) F).det = 1 := by simp [det_fin_two]
  have hF : !![0, 0; 1, 0] ∈ V := by
    convert V.neg_mem (hc hw hE) using 1
    ext i j
    fin_cases i <;> fin_cases j <;> simp [adjugate_fin_two_of]
  have hH : !![1, 0; 0, -1] ∈ V := by
    convert V.sub_mem (V.sub_mem hE hF) (hc hl hE) using 1
    ext i j
    fin_cases i <;> fin_cases j <;> simp [adjugate_fin_two_of]
  -- `E`, `F` and `H` span the trace-zero matrices.
  refine le_antisymm hV fun Y hY ↦ ?_
  simp only [LinearMap.mem_ker, traceLinearMap_apply, trace_fin_two] at hY
  have hY' : Y 1 1 = -Y 0 0 := by linear_combination hY
  convert V.add_mem (V.add_mem (V.smul_mem (Y 0 0) hH) (V.smul_mem (Y 0 1) hE))
    (V.smul_mem (Y 1 0) hF) using 1
  ext i j
  fin_cases i <;> fin_cases j <;> simp [hY']

end TauCeti
