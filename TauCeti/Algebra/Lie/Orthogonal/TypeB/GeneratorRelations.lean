/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.Orthogonal.TypeB.RootGenerators
public import Mathlib.Algebra.Lie.Sl2
public import Mathlib.LinearAlgebra.Matrix.Cartan.Basic

/-!
# Cartan action on the split type-B root generators

This file records the coordinates of the Bourbaki simple coroots in the split diagonal Cartan and
uses them to compute their action on both signs of every simple root. If `dᵢ` is the coordinate
vector of the `i`th simple coroot, the formulas are

```text
[hᵢ, eⱼ] = dᵢ(j) eⱼ                         (j the short node),
[hᵢ, eⱼ] = (dᵢ(j) - dᵢ(j+1)) eⱼ            (j a long node),
```

with the negatives of these scalars on the negative-root generators. The results below identify
these scalars uniformly with entries of Mathlib's type-`B` Cartan matrix; the transpose appears
because the coroot index comes first in the Lie bracket. The mixed and higher Serre relations are
subsequent steps.

## Main results

* `TauCeti.typeBSimpleCorootCoordinate`: the diagonal coordinate of a simple coroot.
* `TauCeti.typeBSimpleCorootGenerator_eq_diagonal`: the corresponding matrix identity.
* `TauCeti.typeBSimpleCorootGenerator_lie_eq_zero`: simple coroots commute.
* `TauCeti.typeBSimpleCorootGenerator_lie_root_last` and
  `TauCeti.typeBSimpleCorootGenerator_lie_root_castSucc`: Cartan action on positive generators.
* `TauCeti.typeBSimpleCorootGenerator_lie_negativeRoot_last` and
  `TauCeti.typeBSimpleCorootGenerator_lie_negativeRoot_castSucc`: Cartan action on negative
  generators.
* `TauCeti.typeBSimpleCorootGenerator_lie_root` and
  `TauCeti.typeBSimpleCorootGenerator_lie_negativeRoot`: the uniform integral
  Cartan-action relations.
* `TauCeti.isSl2Triple_typeBSimpleRootGenerator`: the simple generators at each node form an
  `sl₂` triple.

## References

* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4--6*, Plate II.
* R. W. Carter, *Simple Groups of Lie Type*, Section 4.2.

These relations supply matrix-model input both to the Chevalley--Demazure construction and to a
Chevalley-style basis of the split type-`B` Lie algebra.
-/

public section

namespace TauCeti

universe u

variable {K : Type u} [CommRing K]
variable {n : ℕ}

/-- The coordinate vector of a Bourbaki simple coroot of `Bₙ₊₁` in the split diagonal Cartan.
The first `n` nodes are `εᵢ - εᵢ₊₁`, while the final short node has coroot `2εₙ`. -/
def typeBSimpleCorootCoordinate (i : Fin (n + 1)) : Fin (n + 1) → K :=
  Fin.lastCases (2 • Pi.single (Fin.last n) 1)
    (fun j => Pi.single j.castSucc 1 - Pi.single j.succ 1) i

@[simp]
theorem typeBSimpleCorootCoordinate_last :
    typeBSimpleCorootCoordinate (K := K) (Fin.last n) =
      2 • Pi.single (Fin.last n) 1 := by
  simp [typeBSimpleCorootCoordinate]

@[simp]
theorem typeBSimpleCorootCoordinate_castSucc (i : Fin n) :
    typeBSimpleCorootCoordinate (K := K) i.castSucc =
      Pi.single i.castSucc 1 - Pi.single i.succ 1 := by
  simp [typeBSimpleCorootCoordinate]

/-- A simple coroot generator is the split diagonal element with the corresponding coordinate
vector. -/
theorem typeBSimpleCorootGenerator_eq_diagonal (i : Fin (n + 1)) :
    typeBSimpleCorootGenerator (K := K) i =
      ((typeBDiagonalEquiv (K := K) (ι := Fin (n + 1))
        (typeBSimpleCorootCoordinate i) : typeBDiagonalCartan K (Fin (n + 1))) :
          LieAlgebra.Orthogonal.typeB (Fin (n + 1)) K) := by
  refine Fin.lastCases ?_ (fun i₀ => ?_) i
  · simp [typeBShortCorootGenerator_eq_diagonal]
  · simp [typeBDifferenceCorootGenerator_eq_diagonal]

/-- The simple coroot generators in the standard split type-`B` model commute. -/
@[simp]
theorem typeBSimpleCorootGenerator_lie_eq_zero (i j : Fin (n + 1)) :
    ⁅typeBSimpleCorootGenerator (K := K) i, typeBSimpleCorootGenerator (K := K) j⁆ = 0 := by
  rw [typeBSimpleCorootGenerator_eq_diagonal,
    typeBSimpleCorootGenerator_eq_diagonal]
  have h : ⁅typeBDiagonalEquiv (K := K) (ι := Fin (n + 1))
      (typeBSimpleCorootCoordinate i),
      typeBDiagonalEquiv (K := K) (ι := Fin (n + 1))
        (typeBSimpleCorootCoordinate j)⁆ = 0 :=
    LieModule.IsTrivial.trivial _ _
  exact congrArg Subtype.val h

/-- The action of a simple coroot on the positive generator at the final short node. -/
@[simp]
theorem typeBSimpleCorootGenerator_lie_root_last (i : Fin (n + 1)) :
    ⁅typeBSimpleCorootGenerator (K := K) i,
      typeBShortRootGenerator (K := K) (Fin.last n)⁆ =
        typeBSimpleCorootCoordinate (K := K) i (Fin.last n) •
          typeBShortRootGenerator (K := K) (Fin.last n) := by
  rw [typeBSimpleCorootGenerator_eq_diagonal]
  simpa only [coe_typeBDiagonalEquiv_apply] using
    (typeBDiagonalMatrix_lie_shortRootGenerator
      (typeBSimpleCorootCoordinate (K := K) i) (Fin.last n))

/-- The action of a simple coroot on a positive generator at a long node. -/
@[simp]
theorem typeBSimpleCorootGenerator_lie_root_castSucc (i : Fin (n + 1)) (j : Fin n) :
    ⁅typeBSimpleCorootGenerator (K := K) i,
      typeBDifferenceRootGenerator (K := K) j.castSucc j.succ
        (ne_of_lt j.castSucc_lt_succ)⁆ =
        (typeBSimpleCorootCoordinate (K := K) i j.castSucc -
          typeBSimpleCorootCoordinate (K := K) i j.succ) •
            typeBDifferenceRootGenerator (K := K) j.castSucc j.succ
              (ne_of_lt j.castSucc_lt_succ) := by
  rw [typeBSimpleCorootGenerator_eq_diagonal]
  simpa only [coe_typeBDiagonalEquiv_apply] using
    (typeBDiagonalMatrix_lie_differenceRootGenerator
      (typeBSimpleCorootCoordinate (K := K) i) j.castSucc j.succ
        (ne_of_lt j.castSucc_lt_succ))

/-- The action of a simple coroot on the negative generator at the final short node. -/
@[simp]
theorem typeBSimpleCorootGenerator_lie_negativeRoot_last (i : Fin (n + 1)) :
    ⁅typeBSimpleCorootGenerator (K := K) i,
      typeBShortNegativeRootGenerator (K := K) (Fin.last n)⁆ =
        -(typeBSimpleCorootCoordinate (K := K) i (Fin.last n)) •
          typeBShortNegativeRootGenerator (K := K) (Fin.last n) := by
  rw [typeBSimpleCorootGenerator_eq_diagonal]
  simpa only [coe_typeBDiagonalEquiv_apply] using
    (typeBDiagonalMatrix_lie_shortNegativeRootGenerator
      (typeBSimpleCorootCoordinate (K := K) i) (Fin.last n))

/-- The action of a simple coroot on a negative generator at a long node. -/
@[simp]
theorem typeBSimpleCorootGenerator_lie_negativeRoot_castSucc (i : Fin (n + 1)) (j : Fin n) :
    ⁅typeBSimpleCorootGenerator (K := K) i,
      typeBDifferenceRootGenerator (K := K) j.succ j.castSucc
        (ne_of_gt j.castSucc_lt_succ)⁆ =
        (typeBSimpleCorootCoordinate (K := K) i j.succ -
          typeBSimpleCorootCoordinate (K := K) i j.castSucc) •
            typeBDifferenceRootGenerator (K := K) j.succ j.castSucc
              (ne_of_gt j.castSucc_lt_succ) := by
  rw [typeBSimpleCorootGenerator_eq_diagonal]
  simpa only [coe_typeBDiagonalEquiv_apply] using
    (typeBDiagonalMatrix_lie_differenceRootGenerator
      (typeBSimpleCorootCoordinate (K := K) i) j.succ j.castSucc
        (ne_of_gt j.castSucc_lt_succ))

private theorem typeBSimpleCorootCoordinate_last_eq_cartan_transpose (i : Fin (n + 1)) :
    typeBSimpleCorootCoordinate (K := K) i (Fin.last n) =
      ((CartanMatrix.B (n + 1)).transpose i (Fin.last n) : ℤ) := by
  rw [Matrix.transpose_apply]
  refine Fin.lastCases ?_ (fun i₀ => ?_) i
  · simp [CartanMatrix.B, Matrix.of_apply]
  · rw [typeBSimpleCorootCoordinate_castSucc]
    rcases i₀ with ⟨i, hi⟩
    simp [CartanMatrix.B, Matrix.of_apply]
    split_ifs <;> simp_all [Pi.single_apply, Fin.ext_iff]
    all_goals omega

private theorem typeBSimpleCorootCoordinate_sub_eq_cartan_transpose
    (i : Fin (n + 1)) (j : Fin n) :
    typeBSimpleCorootCoordinate (K := K) i j.castSucc -
        typeBSimpleCorootCoordinate i j.succ =
      ((CartanMatrix.B (n + 1)).transpose i j.castSucc : ℤ) := by
  rw [Matrix.transpose_apply]
  refine Fin.lastCases ?_ (fun i₀ => ?_) i
  · rw [typeBSimpleCorootCoordinate_last]
    rcases j with ⟨j, hj⟩
    simp only [Fin.castSucc_mk, Fin.succ_mk, CartanMatrix.B,
      Matrix.of_apply, Fin.ext_iff]
    split_ifs <;> simp_all [Pi.single_apply, Fin.ext_iff]
    all_goals omega
  · rw [typeBSimpleCorootCoordinate_castSucc]
    rcases i₀ with ⟨i, hi⟩
    rcases j with ⟨j, hj⟩
    simp only [Fin.castSucc_mk, Fin.succ_mk, Pi.sub_apply, CartanMatrix.B,
      Matrix.of_apply, Fin.ext_iff]
    split_ifs <;> simp_all [Pi.single_apply, Fin.ext_iff, one_add_one_eq_two]
    all_goals omega

/-- The Cartan action on positive simple-root generators, in Serre's integral convention. -/
@[simp]
theorem typeBSimpleCorootGenerator_lie_root (i j : Fin (n + 1)) :
    ⁅typeBSimpleCorootGenerator (K := K) i, typeBSimpleRootGenerator (K := K) j⁆ =
      CartanMatrix.B (n + 1) j i • typeBSimpleRootGenerator j := by
  rw [← (CartanMatrix.B (n + 1)).transpose_apply i j]
  refine Fin.lastCases ?_ (fun j₀ => ?_) j
  · rw [typeBSimpleRootGenerator_last, typeBSimpleCorootGenerator_lie_root_last,
      typeBSimpleCorootCoordinate_last_eq_cartan_transpose, Int.cast_smul_eq_zsmul]
  · rw [typeBSimpleRootGenerator_castSucc, typeBSimpleCorootGenerator_lie_root_castSucc,
      typeBSimpleCorootCoordinate_sub_eq_cartan_transpose, Int.cast_smul_eq_zsmul]

/-- The Cartan action on negative simple-root generators, in Serre's integral convention. -/
@[simp]
theorem typeBSimpleCorootGenerator_lie_negativeRoot (i j : Fin (n + 1)) :
    ⁅typeBSimpleCorootGenerator (K := K) i,
      typeBSimpleNegativeRootGenerator (K := K) j⁆ =
        -(CartanMatrix.B (n + 1) j i • typeBSimpleNegativeRootGenerator j) := by
  rw [← (CartanMatrix.B (n + 1)).transpose_apply i j]
  refine Fin.lastCases ?_ (fun j₀ => ?_) j
  · rw [typeBSimpleNegativeRootGenerator_last,
      typeBSimpleCorootGenerator_lie_negativeRoot_last,
      typeBSimpleCorootCoordinate_last_eq_cartan_transpose, neg_smul, Int.cast_smul_eq_zsmul]
  · rw [typeBSimpleNegativeRootGenerator_castSucc,
      typeBSimpleCorootGenerator_lie_negativeRoot_castSucc, ← neg_sub,
      typeBSimpleCorootCoordinate_sub_eq_cartan_transpose, neg_smul, Int.cast_smul_eq_zsmul]

/-- Each simple coroot generator is nonzero away from characteristic two. -/
theorem typeBSimpleCorootGenerator_ne_zero [NeZero (2 : K)]
    (i : Fin (n + 1)) :
    typeBSimpleCorootGenerator (K := K) i ≠ 0 := by
  refine Fin.lastCases ?_ (fun j => ?_) i
  · intro h
    have h' : (2 : K) = 0 := by
      simpa [typeBSimpleCorootGenerator_last, typeBShortCorootGenerator_eq_diagonal,
        typeBDiagonalMatrix_apply] using congrArg
        (fun x : LieAlgebra.Orthogonal.typeB (Fin (n + 1)) K =>
          (x : Matrix (Unit ⊕ Fin (n + 1) ⊕ Fin (n + 1))
            (Unit ⊕ Fin (n + 1) ⊕ Fin (n + 1)) K)
            (.inr (.inl (Fin.last n))) (.inr (.inl (Fin.last n)))) h
    exact NeZero.ne 2 h'
  · intro h
    have h' : (1 : K) = 0 := by
      simpa [typeBSimpleCorootGenerator_castSucc, typeBDifferenceCorootGenerator_eq_diagonal,
        typeBDiagonalMatrix_apply, Fin.castSucc_lt_succ.ne] using congrArg
        (fun x : LieAlgebra.Orthogonal.typeB (Fin (n + 1)) K =>
          (x : Matrix (Unit ⊕ Fin (n + 1) ⊕ Fin (n + 1))
            (Unit ⊕ Fin (n + 1) ⊕ Fin (n + 1)) K)
            (.inr (.inl j.castSucc)) (.inr (.inl j.castSucc))) h
    apply NeZero.ne (2 : K)
    rw [← one_add_one_eq_two, h', zero_add]

/-- The positive and negative simple-root generators at each type-`B` node, together with the
simple coroot generator, form an `sl₂` triple. -/
theorem isSl2Triple_typeBSimpleRootGenerator [NeZero (2 : K)]
    (i : Fin (n + 1)) :
    _root_.IsSl2Triple
      (typeBSimpleCorootGenerator (K := K) i)
      (typeBSimpleRootGenerator (K := K) i)
      (typeBSimpleNegativeRootGenerator (K := K) i) where
  h_ne_zero := typeBSimpleCorootGenerator_ne_zero i
  lie_e_f := typeBSimpleRootGenerator_lie_negative i
  lie_h_e_nsmul := by
    rw [typeBSimpleCorootGenerator_lie_root, CartanMatrix.B_diag]
    simp only [two_zsmul, two_nsmul]
  lie_h_f_nsmul := by
    rw [typeBSimpleCorootGenerator_lie_negativeRoot, CartanMatrix.B_diag]
    simp only [two_zsmul, two_nsmul]

end TauCeti
