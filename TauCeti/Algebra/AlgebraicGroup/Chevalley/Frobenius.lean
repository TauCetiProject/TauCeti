/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Chevalley.Datum
import TauCeti.Algebra.Group.End
import TauCeti.Algebra.Lie.UniversalEnveloping.Kostant.RootSubgroup.Scheme.ToralClosure.Frobenius

/-!
# Scalar extension and Frobenius on the points of a Chevalley datum

The points of a Chevalley datum are functorial in the value ring. Their integral Hopf-ideal
presentation supplies the maps, composition and injectivity laws through
`GeneralLinear.IntegralPointsPresentation`; no point-generation theorem is needed.

The endomorphism `ChevalleyDatum.frobenius` is the map induced by the iterated Frobenius of the
value ring. It raises matrix entries, both signs of the numbered root parameters, and the
coordinates of the actual weight-lattice torus to their `p ^ k`-th powers. It commutes with every
homomorphism of value rings. This supplies the field-map factor of ordinary and graph-twisted
Steinberg maps without asserting generation, reductivity, or simplicity of the point group.

The presentation and Frobenius interface follow the existing full-weight type-A and E₆
minuscule interfaces (`SlStd.pointsPresentation` and `E6Minuscule.frobenius`), using the shared
integral-points construction rather than another scalar-extension construction.

## References

* R. Steinberg, *Lectures on Chevalley Groups*, Chapter 10.
* R. W. Carter, *Finite Groups of Lie Type: Conjugacy Classes and Complex Characters*, §1.17.
* J. C. Jantzen, *Representations of Algebraic Groups*, II.1.
-/

public section

namespace TauCeti.DynkinType.ChevalleyDatum

universe v w

open TauCeti.UniversalEnvelopingAlgebra

variable {t : DynkinType} {ht : t.Valid} (D : ChevalleyDatum t ht)

/-- The matrix points of a Chevalley datum, presented by its integral defining Hopf ideal.
The shared presentation API supplies maps of value rings, their functoriality and injectivity,
and the equivalence with quotient-coordinate-algebra points. -/
noncomputable abbrev pointsPresentation (A : Type v) [CommRing A] :
    GeneralLinear.IntegralPointsPresentation D.dim
      (kostantToralDefiningIdeal (t.lieBasis ht).rootGenerator (t.lieBasis ht).h
        D.representation D.lattice D.representation_mem_lattice
        D.isNilpotent_representation_rootGenerator D.basis D.coordinateWeight) A :=
  ⟨D.points A, D.points_def A⟩

variable (p k : ℕ) (A : Type v) [CommRing A] [ExpChar A p]

/-- The `p ^ k`-power Frobenius of the points of a Chevalley datum, induced by Frobenius of the
value ring. This also applies to nonreduced rings; it need not be injective there. -/
noncomputable def frobenius : D.points A →* D.points A :=
  (D.pointsPresentation A).map (D.pointsPresentation A) (iterateFrobenius A p k)

/-- Frobenius is scalar extension along the iterated Frobenius of the value ring. -/
theorem frobenius_def :
    D.frobenius p k A =
      (D.pointsPresentation A).map (D.pointsPresentation A) (iterateFrobenius A p k) :=
  (rfl)

/-- On invertible matrices, the datum's Frobenius is entrywise Frobenius. -/
@[simp]
theorem coe_frobenius (g : D.points A) :
    (D.frobenius p k A g : Matrix.GeneralLinearGroup (Fin D.dim) A) =
      Matrix.GeneralLinearGroup.map (iterateFrobenius A p k) g := by
  rw [frobenius_def, GeneralLinear.IntegralPointsPresentation.coe_map]

/-- Frobenius raises each matrix coefficient to its `p ^ k`-th power. -/
theorem coe_frobenius_apply (g : D.points A) (i j : Fin D.dim) :
    ((D.frobenius p k A g : Matrix.GeneralLinearGroup (Fin D.dim) A) :
        Matrix (Fin D.dim) (Fin D.dim) A) i j =
      ((g : Matrix.GeneralLinearGroup (Fin D.dim) A) :
        Matrix (Fin D.dim) (Fin D.dim) A) i j ^ p ^ k := by
  rw [coe_frobenius, Matrix.GeneralLinearGroup.map_apply, iterateFrobenius_def]

/-- Frobenius raises the additive parameter of every numbered positive or negative simple root
subgroup to its `p ^ k`-th power. -/
@[simp]
theorem frobenius_rootSubgroupMatrix (i : Fin t.rank ⊕ Fin t.rank) (u : Multiplicative A) :
    D.frobenius p k A
        ⟨kostantRootSubgroupMatrix (t.lieBasis ht).rootGenerator (t.lieBasis ht).h
          D.representation D.lattice D.representation_mem_lattice i
          (D.isNilpotent_representation_rootGenerator i) D.basis
          ((AdditiveGroup.gaPointsMulEquiv (R := ℤ) (A := A)).symm u),
          D.kostantRootSubgroupMatrix_mem_points A i _⟩ =
      ⟨kostantRootSubgroupMatrix (t.lieBasis ht).rootGenerator (t.lieBasis ht).h
          D.representation D.lattice D.representation_mem_lattice i
          (D.isNilpotent_representation_rootGenerator i) D.basis
          ((AdditiveGroup.gaPointsMulEquiv (R := ℤ) (A := A)).symm
            (Multiplicative.ofAdd (Multiplicative.toAdd u ^ p ^ k))),
        D.kostantRootSubgroupMatrix_mem_points A i _⟩ := by
  apply Subtype.ext
  rw [coe_frobenius]
  exact map_iterateFrobenius_kostantRootSubgroupMatrix _ _ _ _ _ _ _ p k i u

/-- Frobenius raises the coordinates of the datum's actual weight-lattice torus to their
`p ^ k`-th powers. The coordinate weights, not the full-weight parametrization, are used. -/
@[simp]
theorem frobenius_torusMatrix (s : Fin t.rank → Aˣ) :
    D.frobenius p k A
        ⟨diagGL fun i => torusCharacter s (D.coordinateWeight i), by
          simpa only [kostantTorusMatrix_apply] using D.kostantTorusMatrix_mem_points A s⟩ =
      ⟨kostantTorusMatrix D.lattice D.basis D.coordinateWeight (s ^ p ^ k),
        D.kostantTorusMatrix_mem_points A _⟩ := by
  apply Subtype.ext
  rw [coe_frobenius]
  simpa only [kostantTorusMatrix_apply] using
    map_iterateFrobenius_kostantTorusMatrix D.lattice D.basis D.coordinateWeight p k s

/-- The zeroth Frobenius iterate is the identity. -/
@[simp]
theorem frobenius_zero : D.frobenius p 0 A = MonoidHom.id _ := by
  rw [frobenius_def, iterateFrobenius_zero, GeneralLinear.IntegralPointsPresentation.map_id]

/-- Frobenius iterates add under composition. -/
theorem frobenius_add (m : ℕ) :
    D.frobenius p (k + m) A = (D.frobenius p k A).comp (D.frobenius p m A) := by
  simp only [frobenius_def, iterateFrobenius_add,
    GeneralLinear.IntegralPointsPresentation.map_comp (Q := D.pointsPresentation A)]

/-- Powers of Frobenius multiply its iteration index. -/
-- `Monoid.End` selects composition, rather than pointwise multiplication, for the power.
theorem frobenius_pow (m : ℕ) :
    (show Monoid.End _ from D.frobenius p k A) ^ m = D.frobenius p (k * m) A :=
  Monoid.End.pow_eq_of_add_eq_comp (fun j => D.frobenius p j A) (D.frobenius_zero p A)
    (fun a b => D.frobenius_add p a A b) k m

/-- Scalar extension commutes with Frobenius, even between value rings in different universes. -/
theorem map_frobenius {B : Type w} [CommRing B] [ExpChar B p] (f : A →+* B)
    (g : D.points A) :
    (D.pointsPresentation A).map (D.pointsPresentation B) f (D.frobenius p k A g) =
      D.frobenius p k B ((D.pointsPresentation A).map (D.pointsPresentation B) f g) := by
  refine Subtype.ext (Matrix.GeneralLinearGroup.ext fun i j => ?_)
  simp only [GeneralLinear.IntegralPointsPresentation.coe_map (D.pointsPresentation A)
      (D.pointsPresentation B), coe_frobenius, Matrix.GeneralLinearGroup.map_apply,
    iterateFrobenius_def, map_pow]

end TauCeti.DynkinType.ChevalleyDatum
