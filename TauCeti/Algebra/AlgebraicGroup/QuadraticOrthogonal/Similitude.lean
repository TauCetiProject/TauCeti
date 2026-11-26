/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.ConstantForm.Similitude
public import TauCeti.Algebra.AlgebraicGroup.QuadraticOrthogonal.Basic
public import TauCeti.LinearAlgebra.QuadraticForm.DiscrNondegenerate
import TauCeti.LinearAlgebra.Matrix.Congruence

/-!
# The orthogonal similitude group scheme of a quadratic form

For a commutative ring `R`, `n : ℕ` and a quadratic form `q` on `Rⁿ = Fin n → R`, the
*orthogonal similitude group scheme* `GO(q)` is the closed subgroup scheme of `GLₙ × 𝔾_m` whose
points over a commutative `R`-algebra `A` are the pairs `(g, c)` of an invertible matrix and a unit
with `q_A(g x) = c · q_A(x)` for all `x ∈ Aⁿ`, where `q_A` is the form with the same coefficients
(`QuadraticForm.baseChangeForm`). The unit `c` is the *multiplier*; the pairs with multiplier `1`
are the points of the orthogonal group scheme `O(q)` (`TauCeti.QuadraticOrthogonal`), so `O(q)` is
the kernel of the multiplier on points
(`TauCeti.QuadraticSimilitude.kerMultiplierPointsMulEquiv`).
Nothing here assumes `2` invertible, and nothing is assumed of `q` except, for the uniqueness of
the multiplier, nondegeneracy in positive rank (`QuadraticForm.IsDiscrNondegenerate`).

Its coordinate Hopf algebra is the quotient of the coordinate Hopf algebra `O(GLₙ) ⊗[R] R[T;T⁻¹]`
of `GLₙ × 𝔾_m` (`TauCeti.ConstantFormSimilitude.ambientHopfAlgebra`) by the coefficients of the
polynomial identity `q(X x) - r q(x) = xᵀ (Xᵀ M X - r M) x` in the coordinates of `x`, for `X` the
generic matrix, `r` the multiplier coordinate and `M` the coefficient matrix of `q`: the diagonal
entries and the symmetric sums of `N = Xᵀ M X - r M` (`Matrix.altRelationSet`), as for
`TauCeti.QuadraticOrthogonal`. The three Hopf-ideal closure conditions follow from `N` being
alternating modulo the ideal (`Matrix.IsAltMod`), through the framing identities

```text
(Y Z)ᵀ M (Y Z) - r₁ r₂ M = Zᵀ (Yᵀ M Y - r₁ M) Z + r₁ (Zᵀ M Z - r₂ M),
Wᵀ M W - s M = -(s Wᵀ (Xᵀ M X - r M) W)    (W X = 1, s r = 1).
```

## Main declarations

* `TauCeti.QuadraticSimilitude.definingHopfIdeal`: the Hopf ideal of `GO(q)` in `O(GLₙ × 𝔾_m)`.
* `TauCeti.QuadraticSimilitude.groupScheme` and `TauCeti.QuadraticSimilitude.inclusion`: the
  orthogonal similitude group scheme and its closed immersion into `GLₙ × 𝔾_m`.
* `TauCeti.QuadraticSimilitude.multiplier`: the multiplier character `GO(q) → 𝔾_m`.
* `TauCeti.QuadraticSimilitude.pointsSubgroup` and `TauCeti.QuadraticSimilitude.pointsMulEquiv`:
  the points are the pairs `(g, c)` with `q_A(g x) = c · q_A(x)`, with `pointsMulEquiv_fst`,
  `pointsMulEquiv_snd` and the naturality `pointsMulEquiv_mapValue`, all instances of the
  general `TauCeti.ConstantFormSimilitude.quotientPointsMulEquiv` at the membership criterion
  `mem_definingPointsSubgroup_iff`.
* `TauCeti.QuadraticSimilitude.coordinateMap_eq_zero_of_mem_relationSet` and
  `TauCeti.QuadraticSimilitude.isAltMod_map_coordinateMap`: the relations hold in the coordinate
  Hopf algebra of `GO(q)`.
* `TauCeti.QuadraticSimilitude.multiplierPoints`: the multiplier on points, `(g, c) ↦ c`, which is
  the multiplier character under the points identification (`multiplierPoints_pointsMulEquiv`).
* `TauCeti.QuadraticSimilitude.snd_eq_of_fst_eq` and `TauCeti.QuadraticSimilitude.fst_injective`:
  for a nondegenerate form of positive rank, `g` determines the multiplier `c`.
* `TauCeti.QuadraticSimilitude.kerMultiplierPointsMulEquiv`: the kernel of the multiplier on points
  is the group of points of `O(q)`, a pair `(g, 1)` being a similitude exactly when `g` is a point
  of `O(q)` (`mk_one_mem_pointsSubgroup_iff`).

## References

* B. Conrad, *Reductive group schemes*, Appendix C, for orthogonal group schemes of quadratic
  spaces over rings in every characteristic.
-/

public section

open CategoryTheory Matrix WithConv TensorProduct QuadraticForm
open scoped LaurentPolynomial

namespace TauCeti.QuadraticSimilitude

open ConstantFormSimilitude

universe u w

variable (R : Type u) [CommRing R] (n : ℕ) (q : QuadraticForm R (Fin n → R))

/-! ### The defining relations -/

/-- **The matrix of defining relations** of `GO(q)`: `Xᵀ M X - r M` over the coordinate Hopf
algebra of `GLₙ × 𝔾_m`, for `M` the coefficient matrix of `q`. -/
noncomputable def relationMatrix : Matrix (Fin n) (Fin n) (ambientHopfAlgebra R n) :=
  (matrixCoord R n)ᵀ *
      (coefficientMatrix q (Pi.basisFun R (Fin n))).map (algebraMap R (ambientHopfAlgebra R n)) *
      matrixCoord R n -
    multiplierCoord R n •
      (coefficientMatrix q (Pi.basisFun R (Fin n))).map (algebraMap R (ambientHopfAlgebra R n))

/-- The relation matrix is `Xᵀ M X - r M`. -/
theorem relationMatrix_def :
    relationMatrix R n q =
      (matrixCoord R n)ᵀ *
          (coefficientMatrix q (Pi.basisFun R (Fin n))).map
            (algebraMap R (ambientHopfAlgebra R n)) *
          matrixCoord R n -
        multiplierCoord R n •
          (coefficientMatrix q (Pi.basisFun R (Fin n))).map
            (algebraMap R (ambientHopfAlgebra R n)) := by
  rw [relationMatrix]

/-- **The defining relations** of `GO(q)`: the coefficients of `q(X x) - r q(x)`, namely the
diagonal entries `N i i` and the symmetric sums `N i j + N j i` of the relation matrix `N`. The
sums with `i ≥ j` are redundant. -/
noncomputable def relationSet : Set (ambientHopfAlgebra R n) :=
  (relationMatrix R n q).altRelationSet

/-- The defining relations are the alternating relations of the relation matrix: its diagonal
entries and its symmetric sums. -/
theorem relationSet_def : relationSet R n q = (relationMatrix R n q).altRelationSet := by
  rw [relationSet]

/-- Mapping the relation matrix through an algebra morphism gives the relation of the images of
the generic matrix and of the multiplier coordinate. -/
theorem relationMatrix_map {T : Type*} [Ring T] [Algebra R T]
    (phi : ambientHopfAlgebra R n →ₐ[R] T) :
    (relationMatrix R n q).map phi =
      ((matrixCoord R n).map phi)ᵀ *
          (coefficientMatrix q (Pi.basisFun R (Fin n))).map (algebraMap R T) *
          (matrixCoord R n).map phi -
        phi (multiplierCoord R n) •
          (coefficientMatrix q (Pi.basisFun R (Fin n))).map (algebraMap R T) := by
  rw [relationMatrix, Matrix.map_transpose_mul_mul_sub_smul]

/-! ### The three Hopf-ideal closure conditions -/

/-- The counit vanishes on the relation matrix. -/
private theorem counit_relationMatrix :
    (relationMatrix R n q).map (Bialgebra.counitAlgHom R (ambientHopfAlgebra R n)) = 0 := by
  rw [relationMatrix_map, map_counit_matrixCoord, counit_multiplierCoord, Matrix.transpose_one,
    Matrix.one_mul, Matrix.mul_one, one_smul, sub_self]

/-- **The comultiplication of the relation matrix**:
`(Y Z)ᵀ M (Y Z) - r₁ r₂ M = Zᵀ (Yᵀ M Y - r₁ M) Z + r₁ (Zᵀ M Z - r₂ M)`. -/
private theorem relationMatrix_map_comul :
    (relationMatrix R n q).map (Bialgebra.comulAlgHom R (ambientHopfAlgebra R n)) =
      ((matrixCoord R n).map (rightCopy R n))ᵀ * (relationMatrix R n q).map (leftCopy R n) *
          (matrixCoord R n).map (rightCopy R n) +
        leftCopy R n (multiplierCoord R n) • (relationMatrix R n q).map (rightCopy R n) := by
  rw [relationMatrix_map, relationMatrix_map, relationMatrix_map, map_comul_matrixCoord,
    comul_multiplierCoord, Matrix.transpose_mul, Matrix.mul_sub, Matrix.sub_mul, smul_sub,
    Matrix.mul_smul, Matrix.smul_mul, mul_smul]
  simp only [Matrix.mul_assoc]
  abel

/-- The comultiplication of every defining relation lies in the sum of the left and right tensor
ideals of the span of the relations. -/
private theorem comul_relation_mem {x : ambientHopfAlgebra R n} (hx : x ∈ relationSet R n q) :
    Coalgebra.comul (R := R) x ∈
      Ideal.leftTensorIdeal (R := R) (B := ambientHopfAlgebra R n)
          (Ideal.span (relationSet R n q)) ⊔
        Ideal.rightTensorIdeal (R := R) (A := ambientHopfAlgebra R n)
          (Ideal.span (relationSet R n q)) := by
  set J := Ideal.leftTensorIdeal (R := R) (B := ambientHopfAlgebra R n)
      (Ideal.span (relationSet R n q)) ⊔
    Ideal.rightTensorIdeal (R := R) (A := ambientHopfAlgebra R n)
      (Ideal.span (relationSet R n q))
  have hL := (isAltMod_span_altRelationSet (relationMatrix R n q)).map (J := J) (leftCopy R n)
    ((Ideal.leftTensorIdeal_def R (ambientHopfAlgebra R n) _).ge.trans le_sup_left)
  have hR := (isAltMod_span_altRelationSet (relationMatrix R n q)).map (J := J) (rightCopy R n)
    ((Ideal.rightTensorIdeal_def R (ambientHopfAlgebra R n) _).ge.trans le_sup_right)
  have hcomul := (hL.transpose_mul_mul ((matrixCoord R n).map (rightCopy R n))).add
    (hR.smul (leftCopy R n (multiplierCoord R n)))
  rw [← relationMatrix_map_comul] at hcomul
  rw [relationSet_def] at hx
  simpa only [Bialgebra.comulAlgHom_apply] using hcomul.apply_mem_of_map hx

/-- **The antipode of the relation matrix**: for `W = S(X)` and `s = S(r)`,
`Wᵀ M W - s M = -(s Wᵀ (Xᵀ M X - r M) W)`. -/
private theorem relationMatrix_map_antipode :
    (relationMatrix R n q).map
        (HopfAlgebra.antipodeAlgHom (R := R) (A := ambientHopfAlgebra R n)) =
      -(HopfAlgebra.antipodeAlgHom (R := R) (A := ambientHopfAlgebra R n)
            (multiplierCoord R n) •
          (((matrixCoord R n).map
              (HopfAlgebra.antipodeAlgHom (R := R) (A := ambientHopfAlgebra R n)))ᵀ *
            relationMatrix R n q *
            (matrixCoord R n).map
              (HopfAlgebra.antipodeAlgHom (R := R) (A := ambientHopfAlgebra R n)))) := by
  set W := (matrixCoord R n).map
    (HopfAlgebra.antipodeAlgHom (R := R) (A := ambientHopfAlgebra R n))
  set s := HopfAlgebra.antipodeAlgHom (R := R) (A := ambientHopfAlgebra R n) (multiplierCoord R n)
  have hXW : matrixCoord R n * W = 1 :=
    mul_eq_one_comm.mp (map_antipode_matrixCoord_mul R n)
  have hWX : Wᵀ * (matrixCoord R n)ᵀ = 1 := by
    rw [← Matrix.transpose_mul, hXW, Matrix.transpose_one]
  have hsr : s * multiplierCoord R n = 1 := antipode_multiplierCoord_mul R n
  rw [relationMatrix_map, relationMatrix, Matrix.mul_sub, Matrix.sub_mul, smul_sub, neg_sub,
    Matrix.mul_smul, Matrix.smul_mul, smul_smul, hsr, one_smul]
  congr 1
  simp only [← Matrix.mul_assoc, hWX, Matrix.one_mul]
  rw [Matrix.mul_assoc, hXW, Matrix.mul_one]

/-- The antipode carries every defining relation into the span of the relations. -/
private theorem antipode_relation_mem {x : ambientHopfAlgebra R n} (hx : x ∈ relationSet R n q) :
    HopfAlgebra.antipode R x ∈ Ideal.span (relationSet R n q) := by
  have hS := (((isAltMod_span_altRelationSet (relationMatrix R n q)).transpose_mul_mul
    ((matrixCoord R n).map
      (HopfAlgebra.antipodeAlgHom (R := R) (A := ambientHopfAlgebra R n)))).smul
      (HopfAlgebra.antipodeAlgHom (R := R) (A := ambientHopfAlgebra R n)
        (multiplierCoord R n))).neg
  rw [← relationMatrix_map_antipode] at hS
  rw [relationSet_def] at hx ⊢
  simpa only [HopfAlgebra.antipodeAlgHom_apply] using hS.apply_mem_of_map hx

/-! ### The defining Hopf ideal and the group scheme -/

/-- **The Hopf ideal of `GO(q)`**: the ideal of the coordinate Hopf algebra of `GLₙ × 𝔾_m`
generated by the coefficients of `q(X x) - r q(x)`. -/
noncomputable def definingHopfIdeal : HopfIdeal R (ambientHopfAlgebra R n) :=
  HopfIdeal.ofSpan (relationSet R n q)
    (fun _ hx => comul_relation_mem R n q hx)
    (fun _ hx => by
      rw [relationSet_def] at hx
      have h0 : IsAltMod ⊥ ((relationMatrix R n q).map
          (Bialgebra.counitAlgHom R (ambientHopfAlgebra R n))) := by
        rw [counit_relationMatrix]
        exact IsAltMod.zero
      simpa only [Bialgebra.counitAlgHom_apply, Ideal.mem_bot] using
        h0.apply_mem_of_map hx)
    (fun _ hx => antipode_relation_mem R n q hx)

/-- The underlying ideal of the defining Hopf ideal is the span of the defining relations. -/
@[simp]
theorem definingHopfIdeal_toIdeal :
    (definingHopfIdeal R n q).toIdeal = Ideal.span (relationSet R n q) := by
  rw [definingHopfIdeal, HopfIdeal.ofSpan_toIdeal]

/-- **A coordinate morphism kills the defining ideal exactly when the images `X'` of the generic
matrix and `r'` of the multiplier coordinate make `X'ᵀ M X' - r' M` alternating**, that is
`q(X' x) = r' q(x)` on coefficients. -/
theorem definingHopfIdeal_toIdeal_le_ker_iff {T : Type*} [CommRing T] [Algebra R T]
    (phi : ambientHopfAlgebra R n →ₐ[R] T) :
    (definingHopfIdeal R n q).toIdeal ≤ RingHom.ker (phi : _ →+* T) ↔
      IsAltMod ⊥ ((relationMatrix R n q).map phi) := by
  rw [definingHopfIdeal_toIdeal, relationSet_def, span_altRelationSet_le_iff]
  simp only [isAltMod_iff, Matrix.map_apply, RingHom.mem_ker, Ideal.mem_bot, AlgHom.coe_toRingHom,
    map_add]

/-- The coordinate Hopf algebra of `GO(q)`. -/
noncomputable abbrev coordinateHopfAlgebra : _root_.CommHopfAlgCat.{u} R :=
  CommHopfAlgCat.quotient (ambientHopfAlgebra R n) (definingHopfIdeal R n q)

/-- The quotient coordinate morphism from `O(GLₙ × 𝔾_m)` to the coordinate Hopf algebra of
`GO(q)`. -/
noncomputable def coordinateMap : ambientHopfAlgebra R n ⟶ coordinateHopfAlgebra R n q :=
  CommHopfAlgCat.mkQuotient (ambientHopfAlgebra R n) (definingHopfIdeal R n q)

/-- The coordinate map is the canonical quotient morphism by the defining Hopf ideal. -/
theorem coordinateMap_def :
    coordinateMap R n q =
      CommHopfAlgCat.mkQuotient (ambientHopfAlgebra R n) (definingHopfIdeal R n q) := by
  unfold coordinateMap
  rfl

/-- The coordinate morphism sends an ambient coordinate to its quotient class. -/
theorem coordinateMap_apply (h : ambientHopfAlgebra R n) :
    (coordinateMap R n q).hom h = Ideal.Quotient.mkₐ R (definingHopfIdeal R n q).toIdeal h := by
  unfold coordinateMap
  exact CommHopfAlgCat.mkQuotient_apply (ambientHopfAlgebra R n) (definingHopfIdeal R n q) h

/-- Every defining relation vanishes in the coordinate Hopf algebra of `GO(q)`. -/
theorem coordinateMap_eq_zero_of_mem_relationSet {x : ambientHopfAlgebra R n}
    (hx : x ∈ relationSet R n q) : (coordinateMap R n q).hom x = 0 := by
  rw [coordinateMap_def]
  exact (CommHopfAlgCat.mkQuotient_eq_zero_iff _ _ _).mpr
    (HopfIdeal.mem_toIdeal.mp (definingHopfIdeal_toIdeal R n q ▸ Ideal.subset_span hx))

/-- The image of the relation matrix in the coordinate Hopf algebra of `GO(q)` is alternating:
`q(X x) = r q(x)` holds there. -/
theorem isAltMod_map_coordinateMap :
    IsAltMod ⊥ ((relationMatrix R n q).map (coordinateMap R n q).hom) :=
  (isAltMod_span_altRelationSet (relationMatrix R n q)).map _ <|
    Ideal.map_le_iff_le_comap.mpr <| Ideal.span_le.mpr fun _ hx =>
      Ideal.mem_comap.mpr (Ideal.mem_bot.mpr (coordinateMap_eq_zero_of_mem_relationSet R n q
        ((relationSet_def R n q).symm ▸ hx)))

/-- **The orthogonal similitude group scheme `GO(q)`** of a quadratic form on `Rⁿ`: the closed
subgroup scheme of `GLₙ × 𝔾_m` of pairs `(g, c)` with `q(g x) = c q(x)`. -/
noncomputable abbrev groupScheme :=
  CommHopfAlgCat.quotientSpec (ambientHopfAlgebra R n) (definingHopfIdeal R n q)

/-- The orthogonal similitude group scheme is the quotient spectrum of its coordinate Hopf
algebra. -/
theorem groupScheme_def :
    groupScheme R n q =
      CommHopfAlgCat.quotientSpec (ambientHopfAlgebra R n) (definingHopfIdeal R n q) :=
  rfl

/-- The closed-subgroup inclusion of `GO(q)` into `GLₙ × 𝔾_m`. -/
noncomputable def inclusion :
    groupScheme R n q ⟶
      (AlgebraicGeometry.hopfSpec (CommRingCat.of R)).obj
        (Opposite.op (ambientHopfAlgebra R n)) :=
  CommHopfAlgCat.quotientSpecι (ambientHopfAlgebra R n) (definingHopfIdeal R n q)

/-- The inclusion is the quotient-spectrum inclusion at the defining Hopf ideal. -/
theorem inclusion_def :
    inclusion R n q =
      CommHopfAlgCat.quotientSpecι (ambientHopfAlgebra R n) (definingHopfIdeal R n q) := by
  unfold inclusion
  rfl

/-- The inclusion of `GO(q)` into `GLₙ × 𝔾_m` is a closed immersion. -/
instance isClosedImmersion_inclusion :
    AlgebraicGeometry.IsClosedImmersion (inclusion R n q).hom.hom.left := by
  rw [inclusion_def]
  infer_instance

/-- The coordinate morphism `O(𝔾_m) ⟶ O(GO(q))` of the **multiplier character**
`ν : (g, c) ↦ c`: the right tensor inclusion followed by the quotient map. -/
noncomputable def multiplierCoordinateMap :
    _root_.CommHopfAlgCat.of R R[T;T⁻¹] ⟶ coordinateHopfAlgebra R n q :=
  inr R n ≫ coordinateMap R n q

/-- The multiplier coordinate morphism is the right tensor inclusion followed by the quotient
map. -/
theorem multiplierCoordinateMap_def :
    multiplierCoordinateMap R n q = inr R n ≫ coordinateMap R n q := by
  unfold multiplierCoordinateMap
  rfl

/-- **The multiplier character** `ν : GO(q) ⟶ 𝔾_m` of group schemes over `R`. -/
noncomputable def multiplier :
    groupScheme R n q ⟶
      (AlgebraicGeometry.hopfSpec (CommRingCat.of R)).obj
        (Opposite.op (_root_.CommHopfAlgCat.of R R[T;T⁻¹])) :=
  (AlgebraicGeometry.hopfSpec (CommRingCat.of R)).map (multiplierCoordinateMap R n q).op

/-- The multiplier character is the image under `hopfSpec` of its coordinate morphism. -/
theorem multiplier_def :
    multiplier R n q =
      (AlgebraicGeometry.hopfSpec (CommRingCat.of R)).map (multiplierCoordinateMap R n q).op := by
  unfold multiplier
  rfl

/-! ### Algebra-valued points -/

section Points

variable {A : Type w} [CommRing A] [Algebra R A]

/-- **The group `GO(q)(A)`**: pairs `(g, c)` of an invertible matrix and a unit with
`q_A(g x) = c q_A(x)` for every `x ∈ Aⁿ`. -/
def pointsSubgroup (A : Type w) [CommRing A] [Algebra R A] : Subgroup (GL (Fin n) A × Aˣ) where
  carrier := {p | ∀ x, baseChangeForm q A ((p.1 : Matrix (Fin n) (Fin n) A) *ᵥ x) =
    (p.2 : A) * baseChangeForm q A x}
  one_mem' := by simp
  mul_mem' {p p'} hp hp' x := by
    simp only [Set.mem_ofPred_eq, Prod.fst_mul, Prod.snd_mul, Units.val_mul] at hp hp' ⊢
    rw [← Matrix.mulVec_mulVec, hp, hp', mul_assoc]
  inv_mem' {p} hp x := by
    simp only [Set.mem_ofPred_eq, Prod.fst_inv, Prod.snd_inv] at hp ⊢
    have h := hp ((↑(p.1⁻¹) : Matrix (Fin n) (Fin n) A) *ᵥ x)
    rw [Matrix.mulVec_mulVec, ← Matrix.GeneralLinearGroup.coe_mul, mul_inv_cancel,
      Matrix.GeneralLinearGroup.coe_one, Matrix.one_mulVec] at h
    rw [h, ← mul_assoc, Units.inv_mul, one_mul]

/-- Membership in `GO(q)(A)`. -/
@[simp]
theorem mem_pointsSubgroup_iff (p : GL (Fin n) A × Aˣ) :
    p ∈ pointsSubgroup R n q A ↔
      ∀ x, baseChangeForm q A ((p.1 : Matrix (Fin n) (Fin n) A) *ᵥ x) =
        (p.2 : A) * baseChangeForm q A x :=
  Iff.rfl

/-- A pair `(g, c)` is a similitude exactly when `gᵀ M g - c M` is alternating. -/
theorem mem_pointsSubgroup_iff_isAltMod (p : GL (Fin n) A × Aˣ) :
    p ∈ pointsSubgroup R n q A ↔
      IsAltMod ⊥ ((p.1 : Matrix (Fin n) (Fin n) A)ᵀ *
          (coefficientMatrix q (Pi.basisFun R (Fin n))).map (algebraMap R A) *
          (p.1 : Matrix (Fin n) (Fin n) A) -
        (p.2 : A) • (coefficientMatrix q (Pi.basisFun R (Fin n))).map (algebraMap R A)) := by
  simp only [mem_pointsSubgroup_iff, isAltMod_bot_iff, baseChangeForm_apply, Matrix.sub_mulVec,
    dotProduct_sub, Matrix.dotProduct_transpose_mul_mul_mulVec, Matrix.smul_mulVec,
    dotProduct_smul, smul_eq_mul, sub_eq_zero]

/-- **Similitudes with multiplier `1`**: a pair `(g, 1)` is a similitude exactly when `g` is a
point of the orthogonal group scheme. -/
theorem mk_one_mem_pointsSubgroup_iff (g : GL (Fin n) A) :
    (g, 1) ∈ pointsSubgroup R n q A ↔ g ∈ QuadraticOrthogonal.pointsSubgroup R n q A := by
  simp

/-- **The ambient membership criterion**: an ambient point of `GLₙ × 𝔾_m` belongs to the subgroup
cut out by the defining Hopf ideal exactly when its pair `(g, c)` is a similitude of `q`. -/
theorem mem_definingPointsSubgroup_iff
    (g : HopfAlgebra.points (R := R) (H := ambientHopfAlgebra R n) (CommAlgCat.of R A)) :
    g ∈ CommHopfAlgCat.quotientPointsSubgroup (ambientHopfAlgebra R n)
        (definingHopfIdeal R n q) (CommAlgCat.of R A) ↔
      ambientPointsMulEquiv R n A g ∈ pointsSubgroup R n q A := by
  rw [CommHopfAlgCat.mem_quotientPointsSubgroup_iff, mem_pointsSubgroup_iff_isAltMod,
    coe_ambientPointsMulEquiv_fst, coe_ambientPointsMulEquiv_snd, ← relationMatrix_map,
    ← definingHopfIdeal_toIdeal_le_ker_iff]
  exact ⟨fun h x hx => h x (HopfIdeal.mem_toIdeal.mp hx), fun h x hx => h hx⟩

/-- **The points identification**: the group of algebra-valued points of the coordinate Hopf
algebra of `GO(q)` is the group of similitudes `(g, c)` of `q_A`. -/
noncomputable def pointsMulEquiv :
    HopfAlgebra.points (R := R) (H := coordinateHopfAlgebra R n q) (CommAlgCat.of R A) ≃*
      pointsSubgroup R n q A :=
  quotientPointsMulEquiv R n (definingHopfIdeal R n q) (pointsSubgroup R n q A)
    (mem_definingPointsSubgroup_iff R n q)

/-- Under the points identifications, the quotient-point inclusion is the inclusion of
`GO(q)(A)` into `GLₙ(A) × Aˣ`. -/
theorem pointsMulEquiv_coe
    (f : HopfAlgebra.points (R := R) (H := coordinateHopfAlgebra R n q) (CommAlgCat.of R A)) :
    ambientPointsMulEquiv R n A
        (CommHopfAlgCat.quotientPointsHom (ambientHopfAlgebra R n) (definingHopfIdeal R n q)
          (CommAlgCat.of R A) f) =
      (pointsMulEquiv R n q (A := A) f : GL (Fin n) A × Aˣ) :=
  quotientPointsMulEquiv_coe R n _ _ _ f

/-- The multiplier of a point, read through the points identification, is its value on the
multiplier coordinate. -/
theorem pointsMulEquiv_snd
    (f : HopfAlgebra.points (R := R) (H := coordinateHopfAlgebra R n q) (CommAlgCat.of R A)) :
    (((pointsMulEquiv R n q (A := A) f : GL (Fin n) A × Aˣ).2 : Aˣ) : A) =
      f.ofConv ((multiplierCoordinateMap R n q).hom (LaurentPolynomial.T 1)) := by
  rw [pointsMulEquiv, quotientPointsMulEquiv_snd, multiplierCoordinateMap_def, coordinateMap_def,
    CommHopfAlgCat.hom_comp, BialgHom.comp_apply, multiplierCoord_def]

/-- The matrix of a point, read through the points identification, is its value on the image of
the generic matrix in the coordinate Hopf algebra. -/
theorem pointsMulEquiv_fst
    (f : HopfAlgebra.points (R := R) (H := coordinateHopfAlgebra R n q) (CommAlgCat.of R A)) :
    (((pointsMulEquiv R n q (A := A) f : GL (Fin n) A × Aˣ).1 : GL (Fin n) A) :
        Matrix (Fin n) (Fin n) A) =
      (matrixCoord R n).map fun x ↦ f.ofConv ((coordinateMap R n q).hom x) := by
  rw [pointsMulEquiv, quotientPointsMulEquiv_fst, coordinateMap_def]

variable (A) in
/-- **The multiplier on points**, `(g, c) ↦ c`, on the similitudes of `q`. -/
def multiplierPoints : pointsSubgroup R n q A →* Aˣ :=
  (MonoidHom.snd _ _).comp (pointsSubgroup R n q A).subtype

/-- The multiplier of a similitude is its unit component. -/
@[simp]
theorem multiplierPoints_apply (p : pointsSubgroup R n q A) :
    multiplierPoints R n q A p = (p : GL (Fin n) A × Aˣ).2 := by
  unfold multiplierPoints
  rfl

/-- Under the points identification, the multiplier on points is the multiplier character. -/
theorem multiplierPoints_pointsMulEquiv
    (f : HopfAlgebra.points (R := R) (H := coordinateHopfAlgebra R n q) (CommAlgCat.of R A)) :
    ((multiplierPoints R n q A (pointsMulEquiv R n q (A := A) f) : Aˣ) : A) =
      f.ofConv ((multiplierCoordinateMap R n q).hom (LaurentPolynomial.T 1)) := by
  rw [multiplierPoints_apply, pointsMulEquiv_snd]

/-- A similitude lies in the kernel of the multiplier exactly when its multiplier is `1`. -/
theorem mem_ker_multiplierPoints_iff (p : pointsSubgroup R n q A) :
    p ∈ (multiplierPoints R n q A).ker ↔ (p : GL (Fin n) A × Aˣ).2 = 1 := by
  rw [MonoidHom.mem_ker, multiplierPoints_apply]

/-- **For a nondegenerate form of positive rank, `g` determines the multiplier**: if `(g, c)` and
`(g, c')` are similitudes of `q_A`, then `c = c'`. Nondegeneracy is in the sense of
`QuadraticForm.IsDiscrNondegenerate`, with no assumption on `2`. -/
theorem snd_eq_of_fst_eq (hn : 0 < n) (hq : IsDiscrNondegenerate q)
    {p p' : GL (Fin n) A × Aˣ} (hp : p ∈ pointsSubgroup R n q A)
    (hp' : p' ∈ pointsSubgroup R n q A) (h : p.1 = p'.1) : p.2 = p'.2 := by
  have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  -- `(c - c') q_A(x) = 0` for every `x`, and the values of `q_A` generate the unit ideal.
  refine Units.ext (sub_eq_zero.mp (eq_zero_of_forall_mul_eq_zero (Pi.basisFun A (Fin n))
    (hq.baseChangeForm A) fun x ↦ ?_))
  rw [sub_mul, ← hp x, ← hp' x, h, sub_self]

/-- For a nondegenerate form of positive rank, a similitude is determined by its matrix: the
projection `GO(q)(A) → GL_n(A)` is injective. -/
theorem fst_injective (hn : 0 < n) (hq : IsDiscrNondegenerate q) :
    Function.Injective fun p : pointsSubgroup R n q A ↦ (p : GL (Fin n) A × Aˣ).1 :=
  fun p p' h ↦ Subtype.ext (Prod.ext h (snd_eq_of_fst_eq R n q hn hq p.property p'.property h))

variable (A) in
/-- **`O(q)` is the kernel of the multiplier on points**: `(g, 1) ↦ g` identifies the kernel of
the multiplier on `GO(q)(A)` with the group of points of the orthogonal group scheme. -/
def kerMultiplierPointsMulEquiv :
    (multiplierPoints R n q A).ker ≃* QuadraticOrthogonal.pointsSubgroup R n q A where
  toFun p := ⟨((p : pointsSubgroup R n q A) : GL (Fin n) A × Aˣ).1, by
    have hmem := (p : pointsSubgroup R n q A).property
    rw [← Prod.mk.eta (p := ((p : pointsSubgroup R n q A) : GL (Fin n) A × Aˣ)),
      (mem_ker_multiplierPoints_iff R n q _).mp p.property] at hmem
    exact (mk_one_mem_pointsSubgroup_iff R n q _).mp hmem⟩
  invFun g := ⟨⟨((g : GL (Fin n) A), 1), (mk_one_mem_pointsSubgroup_iff R n q _).mpr g.property⟩,
    (mem_ker_multiplierPoints_iff R n q _).mpr rfl⟩
  left_inv p := Subtype.ext <| Subtype.ext <|
    Prod.ext rfl ((mem_ker_multiplierPoints_iff R n q _).mp p.property).symm
  right_inv _ := rfl
  map_mul' _ _ := rfl

/-- The point of `O(q)` attached to a similitude with multiplier `1` is its matrix. -/
@[simp]
theorem coe_kerMultiplierPointsMulEquiv (p : (multiplierPoints R n q A).ker) :
    (kerMultiplierPointsMulEquiv R n q A p : GL (Fin n) A) =
      ((p : pointsSubgroup R n q A) : GL (Fin n) A × Aˣ).1 := by
  unfold kerMultiplierPointsMulEquiv
  rfl

/-- The similitude attached to a point `g` of `O(q)` is `(g, 1)`. -/
@[simp]
theorem coe_kerMultiplierPointsMulEquiv_symm (g : QuadraticOrthogonal.pointsSubgroup R n q A) :
    (((kerMultiplierPointsMulEquiv R n q A).symm g : pointsSubgroup R n q A) :
        GL (Fin n) A × Aˣ) = ((g : GL (Fin n) A), 1) := by
  unfold kerMultiplierPointsMulEquiv
  rfl

variable {B : Type*} [CommRing B] [Algebra R B]

/-- **Change of value algebra on similitudes**: an algebra morphism `phi : A → B` sends a
similitude `(g, c)` of `q_A` to the similitude `(phi g, phi c)` of `q_B`. -/
def pointsSubgroupMap (phi : A →ₐ[R] B) : pointsSubgroup R n q A →* pointsSubgroup R n q B :=
  ((MonoidHom.prodMap (Matrix.GeneralLinearGroup.map (phi : A →+* B))
      (Units.map (phi : A →* B))).comp (pointsSubgroup R n q A).subtype).codRestrict _
    fun p => by
      have h := ((mem_pointsSubgroup_iff_isAltMod R n q _).mp p.property).map phi
        (by rw [Ideal.map_bot])
      rw [Matrix.map_transpose_mul_mul_sub_smul] at h
      rw [mem_pointsSubgroup_iff_isAltMod, MonoidHom.comp_apply, Subgroup.coe_subtype,
        MonoidHom.coe_prodMap, Prod.map_fst, Prod.map_snd, Units.coe_map, MonoidHom.coe_ofClass,
        Matrix.GeneralLinearGroup.val_map_apply, RingHom.coe_coe]
      exact h

/-- The similitude `pointsSubgroupMap phi p` is `p` with `phi` applied to both components. -/
@[simp]
theorem coe_pointsSubgroupMap (phi : A →ₐ[R] B) (p : pointsSubgroup R n q A) :
    (pointsSubgroupMap R n q phi p : GL (Fin n) B × Bˣ) =
      Prod.map (Matrix.GeneralLinearGroup.map (phi : A →+* B)) (Units.map (phi : A →* B))
        (p : GL (Fin n) A × Aˣ) := by
  unfold pointsSubgroupMap
  rfl

/-- **The points identification is natural in the value algebra**: post-composing a point with
`phi` maps its similitude componentwise by `phi`. -/
theorem pointsMulEquiv_mapValue (phi : A →ₐ[R] B)
    (f : HopfAlgebra.points (R := R) (H := coordinateHopfAlgebra R n q) (CommAlgCat.of R A)) :
    pointsMulEquiv R n q (A := B) (AlgHom.mapValue (H := coordinateHopfAlgebra R n q) phi f) =
      pointsSubgroupMap R n q phi (pointsMulEquiv R n q (A := A) f) := by
  apply Subtype.ext
  rw [coe_pointsSubgroupMap]
  exact quotientPointsMulEquiv_mapValue R n _ phi _ _ _ _ f

end Points

end TauCeti.QuadraticSimilitude
