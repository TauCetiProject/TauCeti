/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.DiagonalTorus.Conjugacy
public import TauCeti.Algebra.AlgebraicGroup.SpecialLinear.DiagonalTorus.Maximal

/-!
# Conjugating diagonalizable subgroups of `SL_{r+1}` into the diagonal torus

Over a field `k`, every diagonalizable closed subgroup of `SL_{r+1}` is conjugate, by a rational
point of `SL_{r+1}`, into the diagonal torus. In Hopf coordinates, a closed subgroup is
diagonalizable when the group-like elements span its quotient coordinate Hopf algebra, and
containment is reversed: the conclusion reads `(diagonalTorusDefiningIdeal r k).conjugate g ≤ I`.

The proof views the subgroup inside `GL_{r+1}`. The general-linear argument
`TauCeti.GeneralLinear.exists_mul_map_eq_map_mul_diagGL` supplies a rational matrix `P` whose
columns are weight vectors, so that the generic point `M` of the subgroup satisfies
`M P = P diag(t)`. Rescaling the first column of `P` by `(det P)⁻¹` keeps it a matrix of weight
vectors and makes its determinant one, so the conjugating matrix is a rational point of
`SL_{r+1}`. After conjugation the generic point is diagonal, which is membership in the diagonal
torus of `SL_{r+1}` on points.

As a consequence, every split maximal torus of `SL_{r+1}` is conjugate to the diagonal torus,
and any two split maximal tori are conjugate over the base field. Over an algebraically closed
field every torus is split, so the maximal tori are exactly the conjugates of the diagonal torus,
and any two maximal tori are conjugate.

## Main declarations

* `TauCeti.SpecialLinear.exists_conjugate_diagonalTorusDefiningIdeal_le`: a diagonalizable closed
  subgroup of `SL_{r+1}` is contained in a conjugate of the diagonal torus.
* `TauCeti.SpecialLinear.exists_eq_conjugate_diagonalTorusDefiningIdeal_of_isMaximalTorus`: a
  split maximal torus of `SL_{r+1}` is a conjugate of the diagonal torus.
* `TauCeti.SpecialLinear.exists_conjugate_eq_of_isMaximalTorus_of_split`: any two split maximal
  tori of `SL_{r+1}` over a field are conjugate.
* `TauCeti.SpecialLinear.isMaximalTorus_iff_exists_eq_conjugate_diagonalTorusDefiningIdeal`:
  over an algebraically closed field, the maximal tori are exactly those conjugates.
* `TauCeti.SpecialLinear.exists_conjugate_eq_of_isMaximalTorus`: any two maximal tori of
  `SL_{r+1}` over an algebraically closed field are conjugate.

## References

* J. S. Milne, *Algebraic Groups* (2017), Theorem 12.12 and Section 17.a.
* A. Borel, *Linear Algebraic Groups*, 2nd ed. (1991), Proposition 8.4.
-/

public section

open CategoryTheory WithConv

namespace TauCeti.SpecialLinear

universe u

noncomputable section

variable {k : Type u} [Field k] {r : ℕ}

/-- **A diagonalizable closed subgroup of `SL_{r+1}` is conjugate into the diagonal torus.**

If the quotient coordinate Hopf algebra of `I` is spanned by its group-like elements, then some
rational point `g` of `SL_{r+1}` conjugates the diagonal torus to a closed subgroup containing
the one cut out by `I`. Containment of closed subgroups is the reversed inequality of Hopf
ideals. -/
theorem exists_conjugate_diagonalTorusDefiningIdeal_le
    (I : HopfIdeal k (coordinateHopfAlgebra k (r + 1)))
    (hI : DiagonalizableGroup.groupLikeSpannedProperty k
      (FiniteTypeCommHopfAlgCat.quotient
        ⟨coordinateHopfAlgebra k (r + 1), (finiteTypeCommHopfAlgProperty_iff _).2 inferInstance⟩
        I)) :
    ∃ g : WithConv (coordinateHopfAlgebra k (r + 1) →ₐ[k] k),
      (diagonalTorusDefiningIdeal r k).conjugate g ≤ I := by
  let Q := CommHopfAlgCat.quotient (coordinateHopfAlgebra k (r + 1)) I
  let πS : coordinateHopfAlgebra k (r + 1) →ₐc[k] Q := (CommHopfAlgCat.mkQuotient _ I).hom
  let π : GeneralLinear.coordinateHopfAlgebra k (r + 1) →ₐc[k] Q :=
    πS.comp (coordinateMap k (r + 1)).hom
  obtain ⟨P₀, t, hmat₀⟩ := GeneralLinear.exists_mul_map_eq_map_mul_diagGL (n := r + 1) (Q := Q)
    ((DiagonalizableGroup.groupLikeSpannedProperty_iff k _).mp hI) π
  obtain ⟨P, hdet, hmat⟩ := exists_det_eq_one_mul_map_eq_map_mul_diagGL (algebraMap k Q)
    _ P₀ t hmat₀
  let s : Matrix.SpecialLinearGroup (Fin (r + 1)) k :=
    ⟨P, by rw [← Matrix.GeneralLinearGroup.val_det_apply, hdet, Units.val_one]⟩
  let g : WithConv (coordinateHopfAlgebra k (r + 1) →ₐ[k] k) :=
    (pointsMulEquiv (R := k) (A := k) (r + 1)).symm s⁻¹
  -- The generic point of the subgroup, conjugated by `g`, is diagonal.
  have hdiag : Matrix.SpecialLinearGroup.toGL (pointsMulEquiv (R := k) (A := Q) (r + 1)
      (toConv ((πS : coordinateHopfAlgebra k (r + 1) →ₐ[k] Q).comp
        (HopfAlgebra.pointConjugationAlgHom g)))) = diagGL t := by
    have hπ : Matrix.SpecialLinearGroup.toGL (pointsMulEquiv (R := k) (A := Q) (r + 1)
        (toConv (πS : coordinateHopfAlgebra k (r + 1) →ₐ[k] Q))) =
        GeneralLinear.pointsMulEquiv (r + 1) (toConv (π : _ →ₐ[k] Q)) :=
      -- `quotientPointsHom` precomposes with the quotient map `coordinateMap`, giving `π`.
      (pointsMulEquiv_toGL k (r + 1) _).symm
    have hg : Matrix.SpecialLinearGroup.toGL (pointsMulEquiv (R := k) (A := Q) (r + 1)
        (AlgHom.mapValue (H := coordinateHopfAlgebra k (r + 1)) (Algebra.ofId k Q) g)) =
        Matrix.GeneralLinearGroup.map (algebraMap k Q) P⁻¹ := by
      rw [pointsMulEquiv_mapValue, MulEquiv.apply_symm_apply, map_inv, map_inv, map_inv]
      congr 1
      ext i j
      rw [Matrix.SpecialLinearGroup.coe_GL_coe_matrix,
        Matrix.SpecialLinearGroup.map_apply_coe, Matrix.GeneralLinearGroup.map_apply]
      -- `Algebra.ofId k Q` is `algebraMap k Q` as a ring homomorphism.
      rfl
    calc
      Matrix.SpecialLinearGroup.toGL (pointsMulEquiv (R := k) (A := Q) (r + 1)
          (toConv ((πS : coordinateHopfAlgebra k (r + 1) →ₐ[k] Q).comp
            (HopfAlgebra.pointConjugationAlgHom g)))) =
          Matrix.GeneralLinearGroup.map (algebraMap k Q) P⁻¹ *
            Matrix.SpecialLinearGroup.toGL (pointsMulEquiv (R := k) (A := Q) (r + 1)
              (toConv (πS : coordinateHopfAlgebra k (r + 1) →ₐ[k] Q))) *
            (Matrix.GeneralLinearGroup.map (algebraMap k Q) P⁻¹)⁻¹ := by
        rw [HopfAlgebra.comp_pointConjugationAlgHom, map_mul, map_mul, map_inv,
          map_mul, map_mul, map_inv, hg]
      _ = Matrix.GeneralLinearGroup.map (algebraMap k Q) P⁻¹ *
            GeneralLinear.pointsMulEquiv (r + 1) (toConv (π : _ →ₐ[k] Q)) *
            (Matrix.GeneralLinearGroup.map (algebraMap k Q) P⁻¹)⁻¹ := by rw [hπ]
      _ = (Matrix.GeneralLinearGroup.map (algebraMap k Q) P)⁻¹ *
            (GeneralLinear.pointsMulEquiv (r + 1) (toConv (π : _ →ₐ[k] Q)) *
              Matrix.GeneralLinearGroup.map (algebraMap k Q) P) := by
          rw [map_inv, inv_inv, mul_assoc]
      _ = (Matrix.GeneralLinearGroup.map (algebraMap k Q) P)⁻¹ *
            (Matrix.GeneralLinearGroup.map (algebraMap k Q) P * diagGL t) := by rw [hmat]
      _ = diagGL t := by simp
  have hmem := (mem_quotientPointsSubgroup_diagonalTorusDefiningIdeal_iff r k Q
    (toConv ((πS : coordinateHopfAlgebra k (r + 1) →ₐ[k] Q).comp
      (HopfAlgebra.pointConjugationAlgHom g)))).mpr (by
        rw [hdiag, diagGL_coe]
        exact Matrix.isDiag_diagonal _)
  have hle : diagonalTorusDefiningIdeal r k ≤ I.conjugate g := by
    intro x hx
    rw [HopfIdeal.mem_conjugate, ← HopfIdeal.mem_toIdeal,
      ← CommHopfAlgCat.mkQuotient_eq_zero_iff]
    exact (CommHopfAlgCat.mem_quotientPointsSubgroup_iff _ _ _ _).mp hmem x hx
  exact ⟨g⁻¹, by simpa using HopfIdeal.conjugate_mono g⁻¹ hle⟩

/-- **Split maximal tori of `SL_{r+1}` are conjugate to the diagonal torus.** A maximal torus of
`SL_{r+1}` over `k` which is split over `k` is the conjugate of the diagonal torus by a rational
point. -/
theorem exists_eq_conjugate_diagonalTorusDefiningIdeal_of_isMaximalTorus
    {I : HopfIdeal k (coordinateHopfAlgebra k (r + 1))}
    (hI : HopfIdeal.IsMaximalTorus k (coordinateHopfAlgebra k (r + 1)) I)
    (hsplit : splitTorusCommHopfAlgProperty k
      (FiniteTypeCommHopfAlgCat.quotient
        ⟨coordinateHopfAlgebra k (r + 1), (finiteTypeCommHopfAlgProperty_iff _).2 inferInstance⟩
        I)) :
    ∃ g : WithConv (coordinateHopfAlgebra k (r + 1) →ₐ[k] k),
      I = (diagonalTorusDefiningIdeal r k).conjugate g := by
  exact HopfIdeal.exists_eq_conjugate_of_isMaximalTorus_of_split
    (diagonalTorusDefiningIdeal r k) (isMaximalTorus_diagonalTorusDefiningIdeal r k)
    (exists_conjugate_diagonalTorusDefiningIdeal_le I) hI hsplit

/-- **Any two split maximal tori of `SL_{r+1}` over a field are conjugate** by a rational point
of `SL_{r+1}`. -/
theorem exists_conjugate_eq_of_isMaximalTorus_of_split
    {I J : HopfIdeal k (coordinateHopfAlgebra k (r + 1))}
    (hI : HopfIdeal.IsMaximalTorus k (coordinateHopfAlgebra k (r + 1)) I)
    (hJ : HopfIdeal.IsMaximalTorus k (coordinateHopfAlgebra k (r + 1)) J)
    (hsplitI : splitTorusCommHopfAlgProperty k
      (FiniteTypeCommHopfAlgCat.quotient
        ⟨coordinateHopfAlgebra k (r + 1), (finiteTypeCommHopfAlgProperty_iff _).2 inferInstance⟩
        I))
    (hsplitJ : splitTorusCommHopfAlgProperty k
      (FiniteTypeCommHopfAlgCat.quotient
        ⟨coordinateHopfAlgebra k (r + 1), (finiteTypeCommHopfAlgProperty_iff _).2 inferInstance⟩
        J)) :
    ∃ g : WithConv (coordinateHopfAlgebra k (r + 1) →ₐ[k] k), I.conjugate g = J := by
  exact HopfIdeal.exists_conjugate_eq_of_isMaximalTorus_of_split
    (diagonalTorusDefiningIdeal r k) (isMaximalTorus_diagonalTorusDefiningIdeal r k)
    (exists_conjugate_diagonalTorusDefiningIdeal_le I)
    (exists_conjugate_diagonalTorusDefiningIdeal_le J) hI hJ hsplitI hsplitJ

/-- **Maximal tori of `SL_{r+1}` over an algebraically closed field are exactly the conjugates of
the diagonal torus.** The equality is an equality of defining Hopf ideals, hence of closed
subgroup schemes, rather than only of their rational points. -/
theorem isMaximalTorus_iff_exists_eq_conjugate_diagonalTorusDefiningIdeal [IsAlgClosed k]
    (I : HopfIdeal k (coordinateHopfAlgebra k (r + 1))) :
    HopfIdeal.IsMaximalTorus k (coordinateHopfAlgebra k (r + 1)) I ↔
      ∃ g : WithConv (coordinateHopfAlgebra k (r + 1) →ₐ[k] k),
        I = (diagonalTorusDefiningIdeal r k).conjugate g := by
  exact HopfIdeal.isMaximalTorus_iff_exists_eq_conjugate
    (diagonalTorusDefiningIdeal r k) (isMaximalTorus_diagonalTorusDefiningIdeal r k)
    I (exists_conjugate_diagonalTorusDefiningIdeal_le I)

/-- **Any two maximal tori of `SL_{r+1}` over an algebraically closed field are conjugate** by a
rational point of `SL_{r+1}`. -/
theorem exists_conjugate_eq_of_isMaximalTorus [IsAlgClosed k]
    {I J : HopfIdeal k (coordinateHopfAlgebra k (r + 1))}
    (hI : HopfIdeal.IsMaximalTorus k (coordinateHopfAlgebra k (r + 1)) I)
    (hJ : HopfIdeal.IsMaximalTorus k (coordinateHopfAlgebra k (r + 1)) J) :
    ∃ g : WithConv (coordinateHopfAlgebra k (r + 1) →ₐ[k] k), I.conjugate g = J :=
  HopfIdeal.exists_conjugate_eq_of_isMaximalTorus
    (diagonalTorusDefiningIdeal r k) (isMaximalTorus_diagonalTorusDefiningIdeal r k)
    (exists_conjugate_diagonalTorusDefiningIdeal_le I)
    (exists_conjugate_diagonalTorusDefiningIdeal_le J) hI hJ

end

end TauCeti.SpecialLinear
