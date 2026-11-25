/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.AntidiagonalSpecialOrthogonal.Basic
public import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.Weight.Torus

/-!
# The diagonal torus of `SO_l^J`

Let `n = l / 2`, so that `l = 2n` or `l = 2n + 1`. This file embeds the rank-`n` split torus in
the special orthogonal group `SO_l^J` of the antidiagonal form `J_l`
(`TauCeti.AntidiagonalSpecialOrthogonal`) as the diagonal matrices

```text
diag(t₁, …, tₙ, (1), tₙ⁻¹, …, t₁⁻¹),
```

with the middle entry `1` present only for odd `l`. The `i`-th diagonal entry is the character
of the weight `εᵢ` for `i < n`, of `-ε_{l-1-i}` for `l - 1 - i < n`, and of `0` in the middle.
These weights are the standard weights `±εᵢ` (and `0` for `l` odd) of the split orthogonal
groups of types `Bₙ` and `Dₙ`.

The coordinate morphism is obtained by factoring the general-linear weight torus
`TauCeti.GeneralLinear.weightTorusCoordinateMap` through the quotient defining `SO_l^J`: the
weights in mirror-image positions are opposite, so the diagonal matrix of their characters
preserves `J_l`, and they sum to zero, so its determinant is one. The weights `εᵢ` occur among
them, so they span the character lattice and the coordinate morphism is surjective over every
commutative base ring; contravariantly, the torus is a closed subgroup of `SO_l^J`.

## Main declarations

* `TauCeti.AntidiagonalSpecialOrthogonal.diagonalTorusWeight`: the weights of the diagonal
  entries.
* `TauCeti.AntidiagonalSpecialOrthogonal.diagonalTorusCoordinateMap` and
  `TauCeti.AntidiagonalSpecialOrthogonal.diagonalTorus`: the coordinate morphism and the
  group-scheme morphism from the rank-`l / 2` split torus to `SO_l^J`.
* `TauCeti.AntidiagonalSpecialOrthogonal.coordinateMap_comp_diagonalTorusCoordinateMap`: its
  composite with `O(GL_l) ⟶ O(SO_l^J)` is the general-linear weight torus.
* `TauCeti.AntidiagonalSpecialOrthogonal.diagonalTorusCoordinateMap_surjective`: the coordinate
  morphism is surjective.
* `TauCeti.AntidiagonalSpecialOrthogonal.pointsMulEquiv_diagonalTorusPoints`: on points, `t` goes
  to the diagonal matrix of the weight characters.
* `TauCeti.AntidiagonalSpecialOrthogonal.diagonalTorusCoordinateMap_baseChange`: compatibility
  with scalar extension.

## References

* J. E. Humphreys, *Linear Algebraic Groups* (1975), §26.3, for the diagonal maximal tori of the
  orthogonal groups in the antidiagonal model.
* The construction follows `TauCeti.Algebra.AlgebraicGroup.SpecialLinear.DiagonalTorus.Basic`.
-/

public section

open CategoryTheory Matrix WithConv

namespace TauCeti.AntidiagonalSpecialOrthogonal

universe u w

/-! ### The weights -/

section Weights

/-- The weight of the `i`-th diagonal entry of the diagonal torus of `SO_l^J`, as a function on
the universe-lifted coordinates of the rank-`l / 2` split torus: `εᵢ` when `i < l / 2`,
`-ε_{l-1-i}` when `l - 1 - i < l / 2`, and `0` for the middle entry of odd `l`. -/
def diagonalTorusWeight (l : ℕ) (i : Fin l) : ULift.{u} (Fin (l / 2)) → ℤ :=
  fun k =>
    (if (i : ℕ) = k.down then 1 else 0) - (if ((Fin.rev i : Fin l) : ℕ) = k.down then 1 else 0)

variable {l : ℕ}

/-- The values of `diagonalTorusWeight`. -/
@[simp]
theorem diagonalTorusWeight_apply (i : Fin l) (k : ULift.{u} (Fin (l / 2))) :
    diagonalTorusWeight.{u} l i k =
      (if (i : ℕ) = k.down then 1 else 0) -
        (if ((Fin.rev i : Fin l) : ℕ) = k.down then 1 else 0) :=
  (rfl)

/-- Weights in mirror-image positions are opposite. -/
theorem diagonalTorusWeight_rev (i : Fin l) :
    diagonalTorusWeight.{u} l (Fin.rev i) = -diagonalTorusWeight.{u} l i := by
  funext k
  simp only [diagonalTorusWeight_apply, Fin.rev_rev, Pi.neg_apply, neg_sub]

/-- The weight of the `k`-th diagonal entry, for `k < l / 2`, is the coordinate weight `ε_k`. -/
@[simp]
theorem diagonalTorusWeight_castLE (k : Fin (l / 2)) :
    diagonalTorusWeight.{u} l (Fin.castLE (Nat.div_le_self l 2) k) =
      Pi.single (ULift.up k) 1 := by
  funext ⟨j⟩
  have hk := k.isLt
  have hj := j.isLt
  rw [diagonalTorusWeight_apply, Fin.val_rev, Fin.val_castLE, Pi.single_apply]
  by_cases h : j = k
  · subst h
    simp only [ite_true]
    rw [ite_eq_right_iff.mpr (fun h => by omega), sub_zero]
  · have h' : (k : ℕ) ≠ j := fun h' => h (Fin.ext h'.symm)
    have h'' : (ULift.up j : ULift.{u} (Fin (l / 2))) ≠ ULift.up k := fun h'' =>
      h (congrArg ULift.down h'')
    simp only [h', h'', ite_false]
    rw [ite_eq_right_iff.mpr (fun h => by omega), sub_zero]

/-- The weight of the mirror image of the `k`-th diagonal entry, for `k < l / 2`, is `-ε_k`. -/
theorem diagonalTorusWeight_rev_castLE (k : Fin (l / 2)) :
    diagonalTorusWeight.{u} l (Fin.rev (Fin.castLE (Nat.div_le_self l 2) k)) =
      -Pi.single (ULift.up k) 1 := by
  rw [diagonalTorusWeight_rev, diagonalTorusWeight_castLE]

/-- The middle entry, neither among the first `l / 2` nor their mirror images, has weight `0`. -/
theorem diagonalTorusWeight_eq_zero {i : Fin l} (hi : l / 2 ≤ i) (hrev : l / 2 ≤ Fin.rev i) :
    diagonalTorusWeight.{u} l i = 0 := by
  funext k
  have hk := k.down.isLt
  rw [diagonalTorusWeight_apply, ite_eq_right_iff.mpr (fun h => by omega),
    ite_eq_right_iff.mpr (fun h => by omega), sub_zero, Pi.zero_apply]

/-- An entry that is its own mirror image, the middle entry for odd `l`, has weight `0`. -/
theorem diagonalTorusWeight_eq_zero_of_rev_eq {i : Fin l} (h : Fin.rev i = i) :
    diagonalTorusWeight.{u} l i = 0 := by
  have h' := congrArg Fin.val h
  rw [Fin.val_rev] at h'
  apply diagonalTorusWeight_eq_zero
  · omega
  · rw [h]
    omega

/-- The weights of the diagonal torus sum to zero. -/
theorem sum_diagonalTorusWeight_eq_zero : ∑ i, diagonalTorusWeight.{u} l i = 0 := by
  funext k
  simp only [Finset.sum_apply, diagonalTorusWeight_apply, Finset.sum_sub_distrib, Pi.zero_apply]
  rw [sub_eq_zero]
  exact (Fintype.sum_equiv Fin.revPerm _ _ fun _ => rfl).symm

/-- The weights of the diagonal torus span the character lattice of the rank-`l / 2` split
torus. -/
theorem span_range_diagonalTorusWeight_eq_top :
    Submodule.span ℤ (Set.range (diagonalTorusWeight.{u} l)) = ⊤ := by
  apply top_unique
  rw [← (Pi.basisFun ℤ (ULift.{u} (Fin (l / 2)))).span_eq]
  apply Submodule.span_mono
  rintro _ ⟨k, rfl⟩
  exact ⟨Fin.castLE (Nat.div_le_self l 2) k.down, by
    rw [diagonalTorusWeight_castLE, Pi.basisFun_apply]⟩

end Weights

/-! ### The coordinate morphism -/

variable (R : Type u) [CommRing R] (l : ℕ)

/-- The diagonal matrix of the weight characters preserves `J_l`. -/
private theorem map_genericMatrix_weightTorusCoordinateMap_preserves :
    (GeneralLinear.genericMatrix R l).map
        (GeneralLinear.weightTorusCoordinateMap (R := R)
          (diagonalTorusWeight.{u} l)).hom.toAlgHom *
        formMatrix _ l *
        ((GeneralLinear.genericMatrix R l).map
          (GeneralLinear.weightTorusCoordinateMap (R := R)
            (diagonalTorusWeight.{u} l)).hom.toAlgHom)ᵀ =
      formMatrix _ l := by
  rw [GeneralLinear.map_genericMatrix_weightTorusCoordinateMap,
    diagonal_mul_formMatrix_mul_transpose_diagonal_eq_iff]
  intro i
  rw [MonoidAlgebra.single_mul_single, mul_one, MonoidAlgebra.one_def]
  congr 1
  apply Multiplicative.toAdd.injective
  ext k
  simp only [toAdd_mul, Finsupp.coe_add, Pi.add_apply, SplitTorus.toAdd_weightCharacter,
    diagonalTorusWeight_rev, Pi.neg_apply, add_neg_cancel, toAdd_one, Finsupp.coe_zero,
    Pi.zero_apply]

/-- **The coordinate morphism of the diagonal torus of `SO_l^J`.** It restricts functions on
`SO_l^J` to the rank-`l / 2` split torus embedded through `diagonalTorusWeight`. Its direction is
opposite to the represented group-scheme morphism. -/
noncomputable def diagonalTorusCoordinateMap :
    coordinateHopfAlgebra R l ⟶
      (DiagonalizableGroup.coordinateRing R
        (SplitTorus.characterGroup (ULift.{u} (Fin (l / 2))))).obj :=
  CommHopfAlgCat.liftQuotient (definingHopfIdeal R l)
    (GeneralLinear.weightTorusCoordinateMap (diagonalTorusWeight l))
    ((definingHopfIdeal_toIdeal_le_ker_iff R l _).2
      ⟨map_genericMatrix_weightTorusCoordinateMap_preserves R l,
        GeneralLinear.weightTorusCoordinateMap_determinantGroupLike _
          sum_diagonalTorusWeight_eq_zero⟩)

/-- Restricting from `GL_l` to `SO_l^J` and then to the diagonal torus is the general-linear
weight torus of `diagonalTorusWeight`. -/
@[simp]
theorem coordinateMap_comp_diagonalTorusCoordinateMap :
    coordinateMap R l ≫ diagonalTorusCoordinateMap R l =
      GeneralLinear.weightTorusCoordinateMap (diagonalTorusWeight l) := by
  rw [coordinateMap_def]
  exact CommHopfAlgCat.mkQuotient_comp_liftQuotient _ _ _

/-- The coordinate morphism of the diagonal torus of `SO_l^J` is surjective over every
commutative base ring. -/
theorem diagonalTorusCoordinateMap_surjective :
    Function.Surjective (diagonalTorusCoordinateMap R l).hom :=
  CommHopfAlgCat.liftQuotient_surjective_of_surjective _ _ _
    (GeneralLinear.weightTorusCoordinateMap_surjective _ span_range_diagonalTorusWeight_eq_top)

/-! ### Algebra-valued points -/

/-- The diagonal-torus homomorphism on `A`-points: the component at `A` of the point map of
`diagonalTorusCoordinateMap`. -/
noncomputable def diagonalTorusPoints (A : Type w) [CommRing A] [Algebra R A] :
    WithConv (MonoidAlgebra R (Multiplicative (ULift.{u} (Fin (l / 2)) →₀ ℤ)) →ₐ[R] A) →*
      WithConv (coordinateHopfAlgebra R l →ₐ[R] A) :=
  ((CommHopfAlgCat.Hom.mapPointsFunctor (diagonalTorusCoordinateMap R l)).app
    (CommAlgCat.of R A)).hom

/-- `diagonalTorusPoints` is the component of the point map of `diagonalTorusCoordinateMap`. -/
theorem diagonalTorusPoints_apply (A : Type w) [CommRing A] [Algebra R A]
    (p : WithConv (MonoidAlgebra R (Multiplicative (ULift.{u} (Fin (l / 2)) →₀ ℤ)) →ₐ[R] A)) :
    diagonalTorusPoints R l A p =
      (CommHopfAlgCat.Hom.mapPointsFunctor (diagonalTorusCoordinateMap R l)).app
        (CommAlgCat.of R A) p :=
  (rfl)

/-- **The diagonal torus of `SO_l^J` on algebra-valued points.** A point `t` of the split torus
goes to the diagonal matrix whose `i`-th entry is the character of `diagonalTorusWeight l i`:
`diag(t₁, …, tₙ, (1), tₙ⁻¹, …, t₁⁻¹)`. -/
theorem pointsMulEquiv_diagonalTorusPoints (A : Type w) [CommRing A] [Algebra R A]
    (p : WithConv (MonoidAlgebra R (Multiplicative (ULift.{u} (Fin (l / 2)) →₀ ℤ)) →ₐ[R] A)) :
    (pointsMulEquiv R l (A := A) (diagonalTorusPoints R l A p) : GL (Fin l) A) =
      diagGL fun i ↦ torusCharacter (SplitTorus.pointsMulEquiv p) (diagonalTorusWeight l i) := by
  have hquot := CommHopfAlgCat.mapPointsFunctor_eq_quotientPointsHom_of_mkQuotient_comp
    (definingHopfIdeal R l) (diagonalTorusCoordinateMap R l)
    (GeneralLinear.weightTorusCoordinateMap (diagonalTorusWeight l))
    (by rw [← coordinateMap_def]; exact coordinateMap_comp_diagonalTorusCoordinateMap R l)
    (CommAlgCat.of R A) p
  rw [← pointsMulEquiv_coe, diagonalTorusPoints_apply, ← hquot]
  exact GeneralLinear.pointsMulEquiv_mapPointsFunctor_weightTorusCoordinateMap _
    (CommAlgCat.of R A) p

/-- The `k`-th diagonal entry of a diagonal-torus point, for `k < l / 2`, is `t_k`. -/
theorem torusCharacter_diagonalTorusWeight_castLE {A : Type w} [CommRing A]
    (s : ULift.{u} (Fin (l / 2)) → Aˣ) (k : Fin (l / 2)) :
    torusCharacter s (diagonalTorusWeight.{u} l (Fin.castLE (Nat.div_le_self l 2) k)) =
      s (ULift.up k) := by
  rw [diagonalTorusWeight_castLE, torusCharacter_single, zpow_one]

/-- The mirror image of the `k`-th diagonal entry of a diagonal-torus point, for `k < l / 2`, is
`t_k⁻¹`. -/
@[simp]
theorem torusCharacter_diagonalTorusWeight_rev_castLE {A : Type w} [CommRing A]
    (s : ULift.{u} (Fin (l / 2)) → Aˣ) (k : Fin (l / 2)) :
    torusCharacter s
        (diagonalTorusWeight.{u} l (Fin.rev (Fin.castLE (Nat.div_le_self l 2) k))) =
      (s (ULift.up k))⁻¹ := by
  rw [diagonalTorusWeight_rev, torusCharacter_neg, torusCharacter_diagonalTorusWeight_castLE]

/-! ### The group-scheme morphism and base change -/

/-- **The coordinate morphism of the diagonal torus of `SO_l^J` commutes with base change.** -/
theorem diagonalTorusCoordinateMap_baseChange (K : Type u) [CommRing K] [Algebra R K] :
    (coordinateHopfAlgebraBaseChangeIso R l K).inv ≫
        CommHopfAlgCat.baseChangeMap (diagonalTorusCoordinateMap R l) ≫
        (DiagonalizableGroup.baseChangeCoordinateHopfAlgebraIso R K
          (SplitTorus.characterGroup (ULift.{u} (Fin (l / 2))))).hom =
      diagonalTorusCoordinateMap K l := by
  have hpre :
      coordinateMap K l ≫ (coordinateHopfAlgebraBaseChangeIso R l K).inv =
        (GeneralLinear.coordinateHopfAlgebraBaseChangeIso R K l).inv ≫
          CommHopfAlgCat.baseChangeMap (coordinateMap R l) := by
    apply (cancel_mono (coordinateHopfAlgebraBaseChangeIso R l K).hom).mp
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id,
      baseChangeMap_coordinateMap_comp_coordinateHopfAlgebraBaseChangeIso_hom,
      Iso.inv_hom_id_assoc]
  apply CommHopfAlgCat.mkQuotient_hom_ext
  rw [← coordinateMap_def K l, ← Category.assoc, hpre, Category.assoc,
    ← Category.assoc (CommHopfAlgCat.baseChangeMap (coordinateMap R l)),
    ← (CommHopfAlgCat.baseChangeFunctor (K := K)).map_comp]
  rw [coordinateMap_comp_diagonalTorusCoordinateMap, coordinateMap_comp_diagonalTorusCoordinateMap]
  rw [← GeneralLinear.weightTorusBaseChangeCoordinateMap_def]
  exact GeneralLinear.weightTorusBaseChangeCoordinateMap_eq R K _

/-- **The diagonal torus of `SO_l^J`** as a group-scheme morphism from the rank-`l / 2` split
torus. -/
noncomputable def diagonalTorus :
    SplitTorus.groupScheme R (ULift.{u} (Fin (l / 2))) ⟶ groupScheme R l :=
  eqToHom
      (DiagonalizableGroup.groupScheme_def R
        (SplitTorus.characterGroup (ULift.{u} (Fin (l / 2))))) ≫
    (AlgebraicGeometry.hopfSpec (CommRingCat.of R)).map (diagonalTorusCoordinateMap R l).op ≫
    eqToHom (groupScheme_def R l).symm

/-- The diagonal torus is relative spectrum applied contravariantly to its coordinate morphism,
transported across the named presentations of the split torus and `SO_l^J`. -/
theorem diagonalTorus_def :
    diagonalTorus R l =
      eqToHom
          (DiagonalizableGroup.groupScheme_def R
            (SplitTorus.characterGroup (ULift.{u} (Fin (l / 2))))) ≫
        (AlgebraicGeometry.hopfSpec (CommRingCat.of R)).map (diagonalTorusCoordinateMap R l).op ≫
        eqToHom (groupScheme_def R l).symm :=
  (rfl)

end TauCeti.AntidiagonalSpecialOrthogonal
