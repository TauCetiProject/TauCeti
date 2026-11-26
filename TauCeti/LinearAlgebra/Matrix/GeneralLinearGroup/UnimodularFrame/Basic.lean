/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import TauCeti.LinearAlgebra.Unimodular
import TauCeti.LinearAlgebra.Matrix.Submatrix

/-!
# Unimodular frames and their faces

A unimodular `k`-frame of `Rⁿ` is an `n × k` matrix `A` with a left inverse `B * A = 1`: its
columns form a basis of a free direct summand of `Rⁿ` (van der Kallen's unimodular sequences of
length `p` are the `Fin p`-frames). The general linear group `GL n R` acts on the `n × k` matrices
by left multiplication and preserves frames, `B * g⁻¹` being a left inverse of `g • A`; the frames
form the sub-`GL n R`-set `TauCeti.unimodularFrames R n k`. A frame with a single column is a
unimodular vector in the sense of `Module.IsUnimodular`
(`TauCeti.mem_unimodularFrames_iff_isUnimodular`). Deleting the `i`-th column of a `(p + 1)`-frame
gives a `p`-frame (`TauCeti.frameFace`), equivariantly, and these faces satisfy the
semi-simplicial identities (`TauCeti.frameFace_comp_frameFace`).

## Main definitions

* `TauCeti.unimodularFrames R n k`: the unimodular `k`-frames of `Rⁿ`, as a sub-`GL n R`-set of
  the `n × k` matrices.
* `TauCeti.frameFace R n i`: the equivariant map deleting the `i`-th column of a frame.

## Main results

* `TauCeti.submatrix_one_mem_unimodularFrames`: the standard frame of an injective `f : k → n`
  is a frame.
* `TauCeti.mem_unimodularFrames_iff_isUnimodular`: the frames with one column are the unimodular
  vectors.
* `TauCeti.frameFace_comp_frameFace`: the semi-simplicial identities between the faces.

## References

* W. van der Kallen, *Homology stability for linear groups*, Invent. Math. 60 (1980), 269–295,
  2.4 (unimodular sequences).
-/

public section

noncomputable section

open Matrix

namespace TauCeti

variable (R : Type*) [CommRing R] (n : Type*) [Fintype n] [DecidableEq n]

/-- The unimodular `k`-frames of `Rⁿ`: the `n × k` matrices `A` with a left inverse `B * A = 1`,
whose columns form a basis of a free direct summand of `Rⁿ`. They form a sub-`GL n R`-set of the
`n × k` matrices, `B * g⁻¹` being a left inverse of `g • A`. -/
def unimodularFrames (k : Type*) [DecidableEq k] : SubMulAction (GL n R) (Matrix n k R) where
  carrier := {A | ∃ B : Matrix k n R, B * A = 1}
  smul_mem' g A := by
    rintro ⟨B, hB⟩
    exact ⟨B * ((g⁻¹ : GL n R) : Matrix n n R), by simp [Matrix.mul_assoc, hB]⟩

variable {R n} {k l : Type*} [DecidableEq k] [DecidableEq l]

@[simp]
theorem mem_unimodularFrames_iff {A : Matrix n k R} :
    A ∈ unimodularFrames R n k ↔ ∃ B : Matrix k n R, B * A = 1 :=
  Iff.rfl

/-- The standard frame `(e_(f a))_a` of an injective `f : k → n`, the columns `f` of the identity
matrix, is a unimodular frame. -/
theorem submatrix_one_mem_unimodularFrames {f : k → n} (hf : Function.Injective f) :
    (1 : Matrix n n R).submatrix id f ∈ unimodularFrames R n k :=
  ⟨(1 : Matrix n n R).submatrix f id, submatrix_one_mul_submatrix_one ⟨f, hf⟩⟩

/-- A frame with a single column is a unimodular vector: an `n × 1` matrix has a left inverse if
and only if its entries generate the unit ideal, which `TauCeti.Module.isUnimodular_pi_iff`
identifies with unimodularity of its column. -/
theorem mem_unimodularFrames_iff_isUnimodular [Unique k] {A : Matrix n k R} :
    A ∈ unimodularFrames R n k ↔ Module.IsUnimodular R fun i ↦ A i default := by
  rw [TauCeti.Module.isUnimodular_pi_iff]
  refine ⟨fun ⟨B, hB⟩ ↦ ⟨fun i ↦ B default i, ?_⟩, fun ⟨b, hb⟩ ↦
    ⟨Matrix.of fun _ j ↦ b j, Matrix.ext fun i j ↦ ?_⟩⟩
  · simpa [Matrix.mul_apply, mul_comm] using congrFun₂ hB default default
  · rw [Subsingleton.elim i default, Subsingleton.elim j default, one_apply_eq, ← hb]
    simp [Matrix.mul_apply, mul_comm]

/-- Deleting some columns of a frame leaves a frame. -/
theorem submatrix_mem_unimodularFrames {A : Matrix n k R} (hA : A ∈ unimodularFrames R n k)
    {f : l → k} (hf : Function.Injective f) : A.submatrix id f ∈ unimodularFrames R n l := by
  obtain ⟨B, hB⟩ := hA
  exact ⟨B.submatrix f id, by
    rw [← submatrix_mul _ _ _ _ _ Function.bijective_id, hB, submatrix_one _ hf]⟩

/-- There is exactly one frame with no columns, the empty matrix. -/
instance [IsEmpty k] : Unique (unimodularFrames R n k) where
  default := ⟨0, mem_unimodularFrames_iff.2 ⟨0, Subsingleton.elim _ _⟩⟩
  uniq _ := Subtype.ext (Subsingleton.elim _ _)

variable (R n) in
/-- The `i`-th face of a `(p + 1)`-frame: the `p`-frame obtained by deleting its `i`-th column.
It is equivariant for `GL n R`, which acts on frames by left multiplication. -/
def frameFace {p : ℕ} (i : Fin (p + 1)) :
    unimodularFrames R n (Fin (p + 1)) →[GL n R] unimodularFrames R n (Fin p) where
  toFun A := ⟨(A : Matrix n (Fin (p + 1)) R).submatrix id i.succAbove,
    submatrix_mem_unimodularFrames A.property Fin.succAbove_right_injective⟩
  map_smul' g A := Subtype.ext <| by
    simp only [SubMulAction.val_smul, GeneralLinearGroup.smul_def, id_eq]
    rw [submatrix_mul _ _ _ _ _ Function.bijective_id, submatrix_id_id]

@[simp]
theorem coe_frameFace_apply {p : ℕ} (i : Fin (p + 1)) (A : unimodularFrames R n (Fin (p + 1))) :
    (frameFace R n i A : Matrix n (Fin p) R) =
      (A : Matrix n (Fin (p + 1)) R).submatrix id i.succAbove :=
  (rfl)

/-- The semi-simplicial identities: for `i ≤ j`, deleting the column `j + 1` and then the
column `i` is the same as deleting the column `i` and then the column `j`. -/
theorem frameFace_comp_frameFace {p : ℕ} {i j : Fin (p + 1)} (hij : i ≤ j)
    (A : unimodularFrames R n (Fin (p + 2))) :
    frameFace R n i (frameFace R n j.succ A) = frameFace R n j (frameFace R n i.castSucc A) := by
  refine Subtype.ext <| Matrix.ext fun r c ↦ ?_
  have h := congrFun (Fin.removeNth_removeNth_eq_swap (fun c ↦ (A : Matrix _ _ R) r c) i j.succ) c
  rw [Fin.predAbove_succ_of_le _ _ hij, Fin.succAbove_succ_of_le _ _ hij] at h
  simpa [Fin.removeNth] using h

end TauCeti
