/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.Unimodular

/-!
# Unimodular frames and their faces

A unimodular `p`-frame of `Rⁿ` is an `n × p` matrix `A` with a left inverse `B * A = 1`: its
columns form a basis of a free direct summand of `Rⁿ` (van der Kallen's unimodular sequences of
length `p`). The general linear group `GL n R` acts on the `n × p` matrices by left multiplication
and preserves frames, `B * g⁻¹` being a left inverse of `g • A`; the frames form the
sub-`GL n R`-set `TauCeti.unimodularFrames R n p`. A `1`-frame is a unimodular vector in the sense
of `Module.IsUnimodular` (`TauCeti.mem_unimodularFrames_one_iff`). Deleting the `i`-th column of a
`(p + 1)`-frame gives a `p`-frame (`TauCeti.frameFace`), equivariantly, and these faces satisfy the
semi-simplicial identities (`TauCeti.frameFace_comp_frameFace`).

## Main definitions

* `TauCeti.unimodularFrames R n p`: the unimodular `p`-frames of `Rⁿ`, as a sub-`GL n R`-set of
  the `n × p` matrices.
* `TauCeti.frameFace R n i`: the equivariant map deleting the `i`-th column of a frame.

## Main results

* `TauCeti.submatrix_one_mem_unimodularFrames`: the standard frame of an injective `f : Fin p → n`
  is a frame.
* `TauCeti.mem_unimodularFrames_one_iff`: the `1`-frames are the unimodular vectors.
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

/-- The unimodular `p`-frames of `Rⁿ`: the `n × p` matrices `A` with a left inverse `B * A = 1`,
whose columns form a basis of a free direct summand of `Rⁿ`. They form a sub-`GL n R`-set of the
`n × p` matrices, `B * g⁻¹` being a left inverse of `g • A`. -/
def unimodularFrames (p : ℕ) : SubMulAction (GL n R) (Matrix n (Fin p) R) where
  carrier := {A | ∃ B : Matrix (Fin p) n R, B * A = 1}
  smul_mem' g A := by
    rintro ⟨B, hB⟩
    refine ⟨B * ((g⁻¹ : GL n R) : Matrix n n R), ?_⟩
    rw [GeneralLinearGroup.smul_def, Matrix.mul_assoc, ← Matrix.mul_assoc _ (g : Matrix n n R),
      ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mul, hB]

variable {R n}

@[simp]
theorem mem_unimodularFrames_iff {p : ℕ} {A : Matrix n (Fin p) R} :
    A ∈ unimodularFrames R n p ↔ ∃ B : Matrix (Fin p) n R, B * A = 1 :=
  Iff.rfl

/-- The standard frame `(e_(f 0), …, e_(f (p - 1)))` of an injective `f : Fin p → n`, the
columns `f` of the identity matrix, is a unimodular frame. -/
theorem submatrix_one_mem_unimodularFrames {p : ℕ} {f : Fin p → n} (hf : Function.Injective f) :
    (1 : Matrix n n R).submatrix id f ∈ unimodularFrames R n p :=
  ⟨(1 : Matrix n n R).submatrix f id, by
    rw [← submatrix_mul _ _ _ _ _ Function.bijective_id, Matrix.one_mul, submatrix_one _ hf]⟩

/-- A `1`-frame is a unimodular vector: an `n × 1` matrix has a left inverse if and only if some
linear functional on `Rⁿ` takes the value `1` at its column. -/
theorem mem_unimodularFrames_one_iff {A : Matrix n (Fin 1) R} :
    A ∈ unimodularFrames R n 1 ↔ Module.IsUnimodular R fun i ↦ A i 0 := by
  rw [Module.isUnimodular_iff]
  refine ⟨fun ⟨B, hB⟩ ↦ ⟨LinearMap.proj 0 ∘ₗ B.mulVecLin, ?_⟩, fun ⟨f, hf⟩ ↦ ?_⟩
  · simpa [mulVec, dotProduct, Matrix.mul_apply] using congrFun (congrFun hB 0) 0
  · refine ⟨Matrix.of fun _ j ↦ f fun l ↦ if j = l then 1 else 0, Matrix.ext fun i j ↦ ?_⟩
    rw [Subsingleton.elim i 0, Subsingleton.elim j 0, one_apply_eq]
    refine Eq.trans ?_ hf
    rw [f.pi_apply_eq_sum_univ fun i ↦ A i 0]
    simp [Matrix.mul_apply, mul_comm]

/-- Deleting some columns of a frame leaves a frame. -/
theorem submatrix_mem_unimodularFrames {p q : ℕ} {A : Matrix n (Fin p) R}
    (hA : A ∈ unimodularFrames R n p) {f : Fin q → Fin p} (hf : Function.Injective f) :
    A.submatrix id f ∈ unimodularFrames R n q := by
  obtain ⟨B, hB⟩ := hA
  exact ⟨B.submatrix f id, by
    rw [← submatrix_mul _ _ _ _ _ Function.bijective_id, hB, submatrix_one _ hf]⟩

/-- There is exactly one `0`-frame, the empty matrix. -/
instance : Unique (unimodularFrames R n 0) where
  default := ⟨0, mem_unimodularFrames_iff.2 ⟨0, Subsingleton.elim _ _⟩⟩
  uniq _ := Subtype.ext (Subsingleton.elim _ _)

variable (R n) in
/-- The `i`-th face of a `(p + 1)`-frame: the `p`-frame obtained by deleting its `i`-th column.
It is equivariant for `GL n R`, which acts on frames by left multiplication. -/
def frameFace {p : ℕ} (i : Fin (p + 1)) :
    unimodularFrames R n (p + 1) →[GL n R] unimodularFrames R n p where
  toFun A := ⟨(A : Matrix n (Fin (p + 1)) R).submatrix id i.succAbove,
    submatrix_mem_unimodularFrames A.property Fin.succAbove_right_injective⟩
  map_smul' g A := Subtype.ext <| by
    simp only [SubMulAction.val_smul, GeneralLinearGroup.smul_def, id_eq]
    rw [submatrix_mul _ _ _ _ _ Function.bijective_id, submatrix_id_id]

@[simp]
theorem coe_frameFace_apply {p : ℕ} (i : Fin (p + 1)) (A : unimodularFrames R n (p + 1)) :
    (frameFace R n i A : Matrix n (Fin p) R) =
      (A : Matrix n (Fin (p + 1)) R).submatrix id i.succAbove :=
  (rfl)

/-- The semi-simplicial identities: for `i ≤ j`, deleting the column `j + 1` and then the
column `i` is the same as deleting the column `i` and then the column `j`. -/
theorem frameFace_comp_frameFace {p : ℕ} {i j : Fin (p + 1)} (hij : i ≤ j)
    (A : unimodularFrames R n (p + 2)) :
    frameFace R n i (frameFace R n j.succ A) = frameFace R n j (frameFace R n i.castSucc A) := by
  refine Subtype.ext <| Matrix.ext fun r c ↦ ?_
  have h := congrFun (Fin.removeNth_removeNth_eq_swap (fun c ↦ (A : Matrix _ _ R) r c) i j.succ) c
  rw [Fin.predAbove_succ_of_le _ _ hij, Fin.succAbove_succ_of_le _ _ hij] at h
  simpa [Fin.removeNth] using h

end TauCeti
