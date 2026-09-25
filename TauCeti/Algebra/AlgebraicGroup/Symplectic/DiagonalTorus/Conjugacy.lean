/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.DiagonalTorus.Conjugacy
public import TauCeti.Algebra.AlgebraicGroup.Symplectic.DiagonalTorus.Maximal
import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Symplectic.Diagonal.Diagonalization

/-!
# Conjugating diagonalizable subgroups of `Sp₂ₘ` into the diagonal torus

Over a field `k`, every diagonalizable closed subgroup of `Sp₂ₘ` is conjugate, by a rational
point of `Sp₂ₘ`, into the paired diagonal torus. In Hopf coordinates, a closed subgroup is
diagonalizable when the group-like elements span its quotient coordinate Hopf algebra, and
containment is reversed: the conclusion reads `(diagonalTorusDefiningIdeal k m).conjugate g ≤ I`.

The proof views the subgroup inside `GL₂ₘ`. The general-linear argument
`TauCeti.GeneralLinear.exists_mul_map_eq_map_mul_diagGL` diagonalizes its generic point `M` by a
rational matrix whose columns are weight vectors. Since `M` preserves the standard alternating
form, weight spaces pair trivially unless their weights are mutually inverse, and a homogeneous
symplectic basis of weight vectors turns the diagonalizing matrix into a rational symplectic one,
`TauCeti.GLSymplecticFin.exists_mul_map_eq_map_mul_diagonal`. After conjugation the generic point
is a paired diagonal matrix, which is membership in the diagonal torus of `Sp₂ₘ` on points.

As a consequence, every split maximal torus of `Sp₂ₘ` is conjugate to the diagonal torus, and
any two split maximal tori are conjugate over the base field. Over an algebraically closed field
every torus is split, so the maximal tori are exactly the conjugates of the diagonal torus, and
any two maximal tori are conjugate.

## Main declarations

* `TauCeti.Symplectic.exists_conjugate_diagonalTorusDefiningIdeal_le`: a diagonalizable closed
  subgroup of `Sp₂ₘ` is contained in a conjugate of the diagonal torus.
* `TauCeti.Symplectic.exists_eq_conjugate_diagonalTorusDefiningIdeal_of_isMaximalTorus`: a split
  maximal torus of `Sp₂ₘ` is a conjugate of the diagonal torus.
* `TauCeti.Symplectic.exists_conjugate_eq_of_isMaximalTorus_of_split`: any two split maximal tori
  of `Sp₂ₘ` over a field are conjugate.
* `TauCeti.Symplectic.isMaximalTorus_iff_exists_eq_conjugate_diagonalTorusDefiningIdeal`: over an
  algebraically closed field, the maximal tori are exactly those conjugates.
* `TauCeti.Symplectic.exists_conjugate_eq_of_isMaximalTorus`: any two maximal tori of `Sp₂ₘ` over
  an algebraically closed field are conjugate.

## References

* J. S. Milne, *Algebraic Groups* (2017), Theorem 12.12 and Section 17.a.
* A. Borel, *Linear Algebraic Groups*, 2nd ed. (1991), Proposition 8.4.
* The Hopf-ideal argument follows the general-linear and special-linear cases,
  `TauCeti.GeneralLinear.exists_conjugate_diagonalTorusDefiningIdeal_le` and
  `TauCeti.SpecialLinear.exists_conjugate_diagonalTorusDefiningIdeal_le`.
-/

public section

open CategoryTheory WithConv

namespace TauCeti.Symplectic

universe u

noncomputable section

variable {k : Type u} [Field k] {m : ℕ}

/-- **A diagonalizable closed subgroup of `Sp₂ₘ` is conjugate into the diagonal torus.**

If the quotient coordinate Hopf algebra of `I` is spanned by its group-like elements, then some
rational point `g` of `Sp₂ₘ` conjugates the diagonal torus to a closed subgroup containing the one
cut out by `I`. Containment of closed subgroups is the reversed inequality of Hopf ideals. -/
theorem exists_conjugate_diagonalTorusDefiningIdeal_le
    (I : HopfIdeal k (coordinateHopfAlgebra k m))
    (hI : DiagonalizableGroup.groupLikeSpannedProperty k
      (FiniteTypeCommHopfAlgCat.quotient
        ⟨coordinateHopfAlgebra k m, (finiteTypeCommHopfAlgProperty_iff _).2 inferInstance⟩ I)) :
    ∃ g : WithConv (coordinateHopfAlgebra k m →ₐ[k] k),
      (diagonalTorusDefiningIdeal k m).conjugate g ≤ I := by
  let Q := CommHopfAlgCat.quotient (coordinateHopfAlgebra k m) I
  let πS : coordinateHopfAlgebra k m →ₐc[k] Q := (CommHopfAlgCat.mkQuotient _ I).hom
  let π : GeneralLinear.coordinateHopfAlgebra k (m + m) →ₐc[k] Q :=
    πS.comp (coordinateMap k m).hom
  obtain ⟨P₀, t, hmat₀⟩ := GeneralLinear.exists_mul_map_eq_map_mul_diagGL (Q := Q)
    ((DiagonalizableGroup.groupLikeSpannedProperty_iff k _).mp hI) π
  -- The generic point of the subgroup, read in `GL₂ₘ`, is the general-linear point `π`.
  have hπ : GeneralLinear.pointsMulEquiv (m + m) (toConv (π : _ →ₐ[k] Q)) =
      (pointsMulEquiv k m (A := Q) (toConv (πS : _ →ₐ[k] Q)) : GL (Fin (m + m)) Q) := by
    rw [← pointsMulEquiv_coe, CommHopfAlgCat.quotientPointsHom_apply, ← coordinateMap_def,
      ofConv_toConv, BialgHom.comp_toAlgHom]
  rw [hπ] at hmat₀
  obtain ⟨P, u, hPu⟩ := GLSymplecticFin.exists_mul_map_eq_map_mul_diagonal _ hmat₀
  let τ : WithConv (MonoidAlgebra k (Multiplicative (ULift.{u} (Fin m) →₀ ℤ)) →ₐ[k] Q) :=
    (SplitTorus.pointsMulEquiv (R := k) (A := Q)).symm fun i ↦ u i.down
  let g : WithConv (coordinateHopfAlgebra k m →ₐ[k] k) :=
    (pointsMulEquiv (R := k) (A := k) m).symm P⁻¹
  -- The generic point of the subgroup, conjugated by `g`, is a paired diagonal matrix.
  have hkey : toConv ((πS : coordinateHopfAlgebra k m →ₐ[k] Q).comp
      (HopfAlgebra.pointConjugationAlgHom g)) = diagonalTorusPoints τ := by
    apply (pointsMulEquiv (R := k) (A := Q) m).injective
    rw [HopfAlgebra.comp_pointConjugationAlgHom, map_mul, map_mul, map_inv,
      pointsMulEquiv_mapValue, pointsMulEquiv_diagonalTorusPoints]
    have hτ : GeneralLinear.diagonalTorusCoordinates (SplitTorus.pointsMulEquiv τ) = u := by
      funext i
      rw [GeneralLinear.diagonalTorusCoordinates_apply, MulEquiv.apply_symm_apply]
    rw [hτ, MulEquiv.apply_symm_apply, Algebra.toRingHom_ofId, map_inv, inv_inv, mul_assoc,
      inv_mul_eq_iff_eq_mul]
    exact hPu
  refine ⟨g⁻¹, ?_⟩
  have hle : diagonalTorusDefiningIdeal k m ≤ I.conjugate g := by
    intro x hx
    rw [HopfIdeal.mem_conjugate, ← HopfIdeal.mem_toIdeal,
      ← CommHopfAlgCat.mkQuotient_eq_zero_iff]
    rw [mem_diagonalTorusDefiningIdeal] at hx
    refine (congrArg (fun f ↦ f.ofConv x) hkey).trans ?_
    rw [← mapPointsFunctor_diagonalTorusCoordinateMap_app (A := CommAlgCat.of k Q),
      CommHopfAlgCat.mapPointsFunctor_app_apply_apply, hx, map_zero]
  simpa using HopfIdeal.conjugate_mono g⁻¹ hle

/-- **Split maximal tori of `Sp₂ₘ` are conjugate to the diagonal torus.** A maximal torus of
`Sp₂ₘ` over `k` which is split over `k` is the conjugate of the diagonal torus by a rational
point. -/
theorem exists_eq_conjugate_diagonalTorusDefiningIdeal_of_isMaximalTorus
    {I : HopfIdeal k (coordinateHopfAlgebra k m)}
    (hI : HopfIdeal.IsMaximalTorus k (coordinateHopfAlgebra k m) I)
    (hsplit : splitTorusCommHopfAlgProperty k
      (FiniteTypeCommHopfAlgCat.quotient
        ⟨coordinateHopfAlgebra k m, (finiteTypeCommHopfAlgProperty_iff _).2 inferInstance⟩ I)) :
    ∃ g : WithConv (coordinateHopfAlgebra k m →ₐ[k] k),
      I = (diagonalTorusDefiningIdeal k m).conjugate g :=
  HopfIdeal.exists_eq_conjugate_of_isMaximalTorus_of_split
    (diagonalTorusDefiningIdeal k m) (isMaximalTorus_diagonalTorusDefiningIdeal k m)
    (exists_conjugate_diagonalTorusDefiningIdeal_le I) hI hsplit

/-- **Any two split maximal tori of `Sp₂ₘ` over a field are conjugate** by a rational point of
`Sp₂ₘ`. -/
theorem exists_conjugate_eq_of_isMaximalTorus_of_split
    {I J : HopfIdeal k (coordinateHopfAlgebra k m)}
    (hI : HopfIdeal.IsMaximalTorus k (coordinateHopfAlgebra k m) I)
    (hJ : HopfIdeal.IsMaximalTorus k (coordinateHopfAlgebra k m) J)
    (hsplitI : splitTorusCommHopfAlgProperty k
      (FiniteTypeCommHopfAlgCat.quotient
        ⟨coordinateHopfAlgebra k m, (finiteTypeCommHopfAlgProperty_iff _).2 inferInstance⟩ I))
    (hsplitJ : splitTorusCommHopfAlgProperty k
      (FiniteTypeCommHopfAlgCat.quotient
        ⟨coordinateHopfAlgebra k m, (finiteTypeCommHopfAlgProperty_iff _).2 inferInstance⟩ J)) :
    ∃ g : WithConv (coordinateHopfAlgebra k m →ₐ[k] k), I.conjugate g = J :=
  HopfIdeal.exists_conjugate_eq_of_isMaximalTorus_of_split
    (diagonalTorusDefiningIdeal k m) (isMaximalTorus_diagonalTorusDefiningIdeal k m)
    (exists_conjugate_diagonalTorusDefiningIdeal_le I)
    (exists_conjugate_diagonalTorusDefiningIdeal_le J) hI hJ hsplitI hsplitJ

/-- **Maximal tori of `Sp₂ₘ` over an algebraically closed field are exactly the conjugates of the
diagonal torus.** The equality is an equality of defining Hopf ideals, hence of closed subgroup
schemes, rather than only of their rational points. -/
theorem isMaximalTorus_iff_exists_eq_conjugate_diagonalTorusDefiningIdeal [IsAlgClosed k]
    (I : HopfIdeal k (coordinateHopfAlgebra k m)) :
    HopfIdeal.IsMaximalTorus k (coordinateHopfAlgebra k m) I ↔
      ∃ g : WithConv (coordinateHopfAlgebra k m →ₐ[k] k),
        I = (diagonalTorusDefiningIdeal k m).conjugate g :=
  HopfIdeal.isMaximalTorus_iff_exists_eq_conjugate
    (diagonalTorusDefiningIdeal k m) (isMaximalTorus_diagonalTorusDefiningIdeal k m)
    I (exists_conjugate_diagonalTorusDefiningIdeal_le I)

/-- **Any two maximal tori of `Sp₂ₘ` over an algebraically closed field are conjugate** by a
rational point of `Sp₂ₘ`. -/
theorem exists_conjugate_eq_of_isMaximalTorus [IsAlgClosed k]
    {I J : HopfIdeal k (coordinateHopfAlgebra k m)}
    (hI : HopfIdeal.IsMaximalTorus k (coordinateHopfAlgebra k m) I)
    (hJ : HopfIdeal.IsMaximalTorus k (coordinateHopfAlgebra k m) J) :
    ∃ g : WithConv (coordinateHopfAlgebra k m →ₐ[k] k), I.conjugate g = J :=
  HopfIdeal.exists_conjugate_eq_of_isMaximalTorus
    (diagonalTorusDefiningIdeal k m) (isMaximalTorus_diagonalTorusDefiningIdeal k m)
    (exists_conjugate_diagonalTorusDefiningIdeal_le I)
    (exists_conjugate_diagonalTorusDefiningIdeal_le J) hI hJ

end

end TauCeti.Symplectic
