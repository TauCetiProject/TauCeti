/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.G2.ShortRoot.PrimeField.Root.Subgroup
public import TauCeti.Algebra.Lie.G2.ShortRoot.CrossProduct.Unitriangular

/-!
# Nonsimple positive short-root subgroups of the short-root G₂ carrier

The roots `α₁ + α₂` and `2α₁ + α₂` have closed additive subgroup maps in the carrier
generated over `𝔽₃`. They are conjugates of the positive short simple-root map by explicit
rank-one words. Their matrices have the existing `crossUnipotentMatrix` normal form,
including its quadratic terms, over arbitrary commutative `𝔽₃`-algebras.

The construction concerns the explicit seven-dimensional carrier. It does not identify that
carrier with an independently pinned simply connected group scheme. These constructions
transfer to that group only along such an identification, once one is proved.

## References

* R. W. Carter, *Simple Groups of Lie Type*, §§4.4 and 6.4.
* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4--6*, Plate IX.

The coordinate construction follows the Weyl-transported closed subgroups in
`TauCeti.Algebra.Lie.F4.ShortRoot.PrimeField.Root.Subgroup`.
-/

public section

namespace TauCeti.G2ShortRoot.PrimeField

universe v w

noncomputable section

private def rankOneWord (j : Fin 2) (A : Type v) [CommRing A] [Algebra (ZMod 3) A] :
    points A :=
  rootSubgroupPoints (.inl j) A (Multiplicative.ofAdd 1) *
    rootSubgroupPoints (.inr j) A (Multiplicative.ofAdd (-1)) *
      rootSubgroupPoints (.inl j) A (Multiplicative.ofAdd 1)

private def conjugator (i : Fin 2) (A : Type v) [CommRing A] [Algebra (ZMod 3) A] :
    points A :=
  if i = 0 then rankOneWord 1 A else rankOneWord 0 A * rankOneWord 1 A

private theorem pointsMap_conjugator {A : Type v} {B : Type w} [CommRing A] [CommRing B]
    [Algebra (ZMod 3) A] [Algebra (ZMod 3) B] (f : A →ₐ[ZMod 3] B) (i : Fin 2) :
    pointsMap f (conjugator i A) = conjugator i B := by
  unfold conjugator
  split_ifs <;> simp [rankOneWord, pointsMap_rootSubgroupPoints]

/-- The prime-field conjugator selecting either nonsimple positive short root. -/
def nonsimpleShortRootConjugator (i : Fin 2) : points (ZMod 3) :=
  conjugator i (ZMod 3)

/-- The selected conjugators are the rank-one word at node one and the product of the
words at nodes zero and one, respectively. -/
theorem nonsimpleShortRootConjugator_def (i : Fin 2) :
    let n := fun j : Fin 2 =>
      rootSubgroupPoints (.inl j) (ZMod 3) (Multiplicative.ofAdd 1) *
        rootSubgroupPoints (.inr j) (ZMod 3) (Multiplicative.ofAdd (-1)) *
          rootSubgroupPoints (.inl j) (ZMod 3) (Multiplicative.ofAdd 1)
    nonsimpleShortRootConjugator i = if i = 0 then n 1 else n 0 * n 1 :=
  (rfl)

/-- The subgroup at `α₁ + α₂` (index zero) or `2α₁ + α₂` (index one), with normalization
specified by the displayed rank-one words. -/
abbrev nonsimpleShortRootSubgroupPoints (i : Fin 2) (A : Type v) [CommRing A]
    [Algebra (ZMod 3) A] : Multiplicative A →* points A :=
  conjugateRootSubgroupPoints (nonsimpleShortRootConjugator i) (.inl 0) A

/-- The point parametrization is conjugation of the positive short simple-root subgroup. -/
theorem nonsimpleShortRootSubgroupPoints_apply (i : Fin 2) (A : Type v) [CommRing A]
    [Algebra (ZMod 3) A] (u : Multiplicative A) :
    let n := fun j : Fin 2 =>
      rootSubgroupPoints (.inl j) A (Multiplicative.ofAdd 1) *
        rootSubgroupPoints (.inr j) A (Multiplicative.ofAdd (-1)) *
          rootSubgroupPoints (.inl j) A (Multiplicative.ofAdd 1)
    nonsimpleShortRootSubgroupPoints i A u =
      (if i = 0 then n 1 else n 0 * n 1) * rootSubgroupPoints (.inl 0) A u *
        (if i = 0 then n 1 else n 0 * n 1)⁻¹ := by
  rw [conjugateRootSubgroupPoints_apply, nonsimpleShortRootConjugator, pointsMap_conjugator]
  rfl

/-- The coordinate pullback of either nonsimple positive short-root subgroup. Its
surjectivity and point comparison are supplied by `conjugateRootSubgroupCoordinateMap`. -/
abbrev nonsimpleShortRootSubgroupCoordinateMap (i : Fin 2) :=
  conjugateRootSubgroupCoordinateMap (nonsimpleShortRootConjugator i) (.inl 0)

/-- The closed additive subgroup at either nonsimple positive short root. Closed immersion
is supplied by `isClosedImmersion_conjugateRootSubgroup`. -/
abbrev nonsimpleShortRootSubgroup (i : Fin 2) :=
  conjugateRootSubgroup (nonsimpleShortRootConjugator i) (.inl 0)

/-- The integral torus character of `α₁ + α₂` (index zero) or `2α₁ + α₂` (index one),
in the fundamental-weight coordinates of `weight`. -/
def nonsimpleShortRootWeight (i : Fin 2) : Fin 2 → ℤ :=
  if i = 0 then ![-1, 1] else ![1, 0]

/-- The first nonsimple positive short root has fundamental-weight coordinates `(-1,1)`. -/
@[simp] theorem nonsimpleShortRootWeight_zero : nonsimpleShortRootWeight 0 = ![-1, 1] := by
  simp [nonsimpleShortRootWeight]

/-- The second nonsimple positive short root has fundamental-weight coordinates `(1,0)`. -/
@[simp] theorem nonsimpleShortRootWeight_one : nonsimpleShortRootWeight 1 = ![1, 0] := by
  simp [nonsimpleShortRootWeight]

-- The coefficient split is private proof machinery for the normal form and its torus action.
private def linearMatrix (i : Fin 2) : Matrix (Fin 7) (Fin 7) (ZMod 3) :=
  if i = 0 then
    Matrix.single 0 2 (-1) + Matrix.single 1 3 2 + Matrix.single 3 5 (-1) +
      Matrix.single 4 6 1
  else
    Matrix.single 0 3 (-2) + Matrix.single 1 4 1 + Matrix.single 2 5 1 +
      Matrix.single 3 6 (-1)

private def dividedSquareMatrix (i : Fin 2) : Matrix (Fin 7) (Fin 7) (ZMod 3) :=
  if i = 0 then Matrix.single 1 5 (-1) else Matrix.single 0 6 1

private theorem conjugator_coefficients (i : Fin 2) :
    let W := ((conjugator i (ZMod 3) : Matrix.GeneralLinearGroup (Fin 7) (ZMod 3)) :
      Matrix (Fin 7) (Fin 7) (ZMod 3))
    let V := (((conjugator i (ZMod 3))⁻¹).val :
      Matrix (Fin 7) (Fin 7) (ZMod 3))
    W * (rootMatrix (.inl 0)).map (Int.cast : ℤ → ZMod 3) * V = linearMatrix i ∧
      W * (rootDividedSquareMatrix (.inl 0)).map (Int.cast : ℤ → ZMod 3) * V =
        dividedSquareMatrix i := by
  dsimp only
  unfold conjugator
  split_ifs <;>
    simp only [rankOneWord, Subgroup.coe_mul, Units.val_mul,
      mul_inv_rev, ← map_inv (rootSubgroupPoints _ (ZMod 3)), ← ofAdd_neg, neg_neg,
      coe_rootSubgroupPoints, IntegralToralClosure.coe_rootSubgroupPoints, toAdd_ofAdd]
  all_goals simp_all only [linearMatrix, dividedSquareMatrix, rootMatrix_inl,
    rootDividedSquareMatrix_inl, rootMatrix_inr, rootDividedSquareMatrix_inr]
  all_goals decide +kernel

private theorem coe_nonsimpleShortRootSubgroupPoints_polynomial (i : Fin 2) (A : Type v)
    [CommRing A] [Algebra (ZMod 3) A] (t : A) :
    ((nonsimpleShortRootSubgroupPoints i A (Multiplicative.ofAdd t) :
      Matrix.GeneralLinearGroup (Fin 7) A) : Matrix (Fin 7) (Fin 7) A) =
        1 + t • (linearMatrix i).map (algebraMap (ZMod 3) A) +
          t ^ 2 • (dividedSquareMatrix i).map (algebraMap (ZMod 3) A) := by
  let f : ZMod 3 →ₐ[ZMod 3] A := Algebra.ofId (ZMod 3) A
  let W := ((conjugator i (ZMod 3) : Matrix.GeneralLinearGroup (Fin 7) (ZMod 3)) :
    Matrix (Fin 7) (Fin 7) (ZMod 3))
  let V := (((conjugator i (ZMod 3))⁻¹).val :
    Matrix (Fin 7) (Fin 7) (ZMod 3))
  have hW : ((conjugator i A : Matrix.GeneralLinearGroup (Fin 7) A) :
      Matrix (Fin 7) (Fin 7) A) = W.map f := by
    rw [← pointsMap_conjugator f i, coe_pointsMap]
    ext a b
    exact Matrix.GeneralLinearGroup.map_apply ..
  have hV : (((conjugator i A)⁻¹).val :
      Matrix (Fin 7) (Fin 7) A) = V.map f := by
    rw [← pointsMap_conjugator f i, ← map_inv, coe_pointsMap]
    ext a b
    exact Matrix.GeneralLinearGroup.map_apply ..
  have hWV : W * V = 1 := by
    exact congrArg (fun g : points (ZMod 3) => (g.val : Matrix (Fin 7) (Fin 7) (ZMod 3)))
      (mul_inv_cancel (conjugator i (ZMod 3)))
  have hlin := congrArg (fun M : Matrix (Fin 7) (Fin 7) (ZMod 3) => M.map f)
    (conjugator_coefficients i).1
  have hquad := congrArg (fun M : Matrix (Fin 7) (Fin 7) (ZMod 3) => M.map f)
    (conjugator_coefficients i).2
  have hcast (M : Matrix (Fin 7) (Fin 7) ℤ) :
      (M.map (Int.cast : ℤ → ZMod 3)).map f = M.map (Int.cast : ℤ → A) := by
    ext a b
    exact map_intCast f _
  simp only [Matrix.map_mul, hcast] at hlin hquad
  dsimp only [W, V] at hW hV hWV
  simp only [nonsimpleShortRootSubgroupPoints, conjugateRootSubgroupPoints_apply,
    nonsimpleShortRootConjugator, pointsMap_conjugator, Subgroup.coe_mul, Units.val_mul]
  rw [hW, hV, coe_rootSubgroupPoints, IntegralToralClosure.coe_rootSubgroupPoints]
  simp only [toAdd_ofAdd, mul_add, add_mul, Matrix.mul_smul, Matrix.smul_mul, mul_one]
  rw [hlin, hquad, ← Matrix.map_mul, hWV, Matrix.map_one _ (map_zero f) (map_one f)]
  have hf : (f : ZMod 3 → A) = algebraMap (ZMod 3) A := by
    ext x
    exact Algebra.ofId_apply ..
  rw [hf]

/-- The matrix at `α₁ + α₂` is the canonical cross-product unipotent normal form.
Its quadratic term is retained over arbitrary coefficient algebras. -/
@[simp]
theorem coe_nonsimpleShortRootSubgroupPoints_zero (A : Type v) [CommRing A]
    [Algebra (ZMod 3) A] (t : A) :
    ((nonsimpleShortRootSubgroupPoints 0 A (Multiplicative.ofAdd t) :
      Matrix.GeneralLinearGroup (Fin 7) A) : Matrix (Fin 7) (Fin 7) A) =
        crossUnipotentMatrix 0 0 (-t) 0 0 0 := by
  rw [coe_nonsimpleShortRootSubgroupPoints_polynomial]
  ext a b
  simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.map_apply, smul_eq_mul]
  fin_cases a <;> fin_cases b <;>
    norm_num [linearMatrix, dividedSquareMatrix, crossUnipotentMatrix_def]
  rw [map_ofNat, mul_comm]

/-- The matrix at `2α₁ + α₂` is the canonical cross-product unipotent normal form.
Its quadratic term is retained over arbitrary coefficient algebras. -/
@[simp]
theorem coe_nonsimpleShortRootSubgroupPoints_one (A : Type v) [CommRing A]
    [Algebra (ZMod 3) A] (t : A) :
    ((nonsimpleShortRootSubgroupPoints 1 A (Multiplicative.ofAdd t) :
      Matrix.GeneralLinearGroup (Fin 7) A) : Matrix (Fin 7) (Fin 7) A) =
        crossUnipotentMatrix 0 0 0 (-t) 0 0 := by
  rw [coe_nonsimpleShortRootSubgroupPoints_polynomial]
  ext a b
  simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.map_apply, smul_eq_mul]
  fin_cases a <;> fin_cases b <;>
    norm_num [linearMatrix, dividedSquareMatrix, crossUnipotentMatrix_def]
  rw [map_ofNat, mul_comm]

private theorem coefficient_weight (i d : Fin 2) (a b : Fin 7) :
    let M := if d = 0 then linearMatrix i else dividedSquareMatrix i
    M a b ≠ 0 → ∀ j : Fin 2, weight a j = (weight b +
      (d.val + 1) • nonsimpleShortRootWeight i) j := by
  dsimp only
  fin_cases i <;> fin_cases d <;> fin_cases a <;> fin_cases b <;>
    norm_num [linearMatrix, dividedSquareMatrix, nonsimpleShortRootWeight, Matrix.single_apply]

private theorem torus_mul_coefficient (i d : Fin 2) (A : Type v) [CommRing A]
    [Algebra (ZMod 3) A] (s : Fin 2 → Aˣ) :
    let M := if d = 0 then linearMatrix i else dividedSquareMatrix i
    let D := Matrix.diagonal fun a : Fin 7 => (torusCharacter s (weight a) : A)
    D * M.map (algebraMap (ZMod 3) A) =
      (torusCharacter s (nonsimpleShortRootWeight i) : A) ^ (d.val + 1) •
        (M.map (algebraMap (ZMod 3) A) * D) := by
  dsimp only
  ext a b
  by_cases h : (if d = 0 then linearMatrix i else dividedSquareMatrix i) a b = 0
  · simp [Matrix.diagonal_mul, Matrix.mul_diagonal, h]
  · rw [Matrix.smul_apply, smul_eq_mul, Matrix.diagonal_mul, Matrix.mul_diagonal,
      funext (coefficient_weight i d a b h), torusCharacter_add, torusCharacter_nsmul,
      Units.val_mul, Units.val_pow_eq_pow_val]
    ac_rfl

/-- The torus acts through the integral characters `α₁ + α₂ = (-1,1)` and
`2α₁ + α₂ = (1,0)`, respectively. -/
@[simp]
theorem weightTorusPoints_conj_nonsimpleShortRootSubgroupPoints (i : Fin 2) (A : Type v)
    [CommRing A] [Algebra (ZMod 3) A] (s : Fin 2 → Aˣ) (t : A) :
    weightTorusPoints A s * nonsimpleShortRootSubgroupPoints i A (Multiplicative.ofAdd t) *
        (weightTorusPoints A s)⁻¹ =
      nonsimpleShortRootSubgroupPoints i A (Multiplicative.ofAdd
        ((torusCharacter s (nonsimpleShortRootWeight i) : A) * t)) := by
  apply (mul_inv_eq_iff_eq_mul).2
  apply Subtype.ext
  apply Units.ext
  simp only [Subgroup.coe_mul, Units.val_mul, coe_weightTorusPoints,
    IntegralToralClosure.coe_weightTorusPoints_eq_diagonal,
    coe_nonsimpleShortRootSubgroupPoints_polynomial,
    mul_add, add_mul, mul_one, one_mul, Matrix.mul_smul, Matrix.smul_mul]
  have hlinear := torus_mul_coefficient i 0 A s
  have hquadratic := torus_mul_coefficient i 1 A s
  simp only [Fin.val_zero, Fin.val_one, zero_add, pow_one, Fin.isValue, ↓reduceIte,
    Fin.reduceEq, Nat.reduceAdd] at hlinear hquadratic
  rw [hlinear, hquadratic, smul_smul, smul_smul, mul_pow, mul_comm t, mul_comm (t ^ 2)]

end

end TauCeti.G2ShortRoot.PrimeField
