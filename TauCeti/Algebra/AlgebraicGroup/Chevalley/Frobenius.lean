/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Chevalley.RootSubgroup
public import TauCeti.Algebra.CharP.Frobenius.Basic
public import TauCeti.LinearAlgebra.Basis.DiagonalTorus.CharacterMap
import TauCeti.Algebra.Group.End

/-!
# Frobenius on the points of a Chevalley datum

For a Chevalley datum `D` and a commutative ring `A` of exponential characteristic `p`,
`D.frobenius p k A` is the endomorphism of the entire point group induced by the
`p ^ k`-power map of `A`. It raises matrix entries and every root parameter to their
`p ^ k`-th powers, commutes with maps of value rings, and satisfies the usual iteration laws.
No generation theorem for field-valued points is needed.

The torus equation uses the actual character lattice of `D`, in its chosen basis, not the
possibly smaller image of the full-weight parametrization. Its character pullback is
`p ^ k • 1`. In particular, applying this construction to
`TauCeti.DynkinType.scChevalleyDatum` gives Frobenius on the simply connected Chevalley
point group, in fundamental-weight coordinates.

The construction uses `GeneralLinear.IntegralPointsPresentation.map`, as in
`TauCeti.TypeDSpinCarrier.frobenius`, with the datum's own integral defining ideal.
The root equation uses the naturality of the all-root divided-power exponentials, so it
includes negative and nonsimple roots over arbitrary, possibly nonreduced value rings.

## References

* R. W. Carter, *Finite Groups of Lie Type: Conjugacy Classes and Complex Characters*, §1.17.
* R. Steinberg, *Lectures on Chevalley Groups*, Chapter 10.
* J. C. Jantzen, *Representations of Algebraic Groups*, II.1.
-/

public section

namespace TauCeti.DynkinType.ChevalleyDatum

universe v v'

noncomputable section

variable {t : DynkinType} {ht : t.Valid} (D : ChevalleyDatum t ht)
variable (p k : ℕ) (A : Type v) [CommRing A] [ExpChar A p]

/-- The `p ^ k`-power Frobenius on all points of a Chevalley datum, induced by the
Frobenius of the value ring. -/
def frobenius : D.points A →* D.points A :=
  (D.pointsPresentation A).map (D.pointsPresentation A) (iterateFrobenius A p k)

/-- Frobenius is the point map induced by the `p ^ k`-power ring endomorphism. -/
theorem frobenius_def :
    D.frobenius p k A =
      (D.pointsPresentation A).map (D.pointsPresentation A) (iterateFrobenius A p k) :=
  (rfl)

/-- On underlying matrices, Frobenius applies the ring Frobenius entrywise. -/
@[simp]
theorem coe_frobenius (g : D.points A) :
    (D.frobenius p k A g : Matrix.GeneralLinearGroup (Fin D.dim) A) =
      Matrix.GeneralLinearGroup.map (iterateFrobenius A p k) g := by
  rw [frobenius_def, GeneralLinear.IntegralPointsPresentation.coe_map]

/-- Each matrix entry is raised to its `p ^ k`-th power. -/
theorem coe_frobenius_apply (g : D.points A) (i j : Fin D.dim) :
    ((D.frobenius p k A g : Matrix.GeneralLinearGroup (Fin D.dim) A) :
        Matrix (Fin D.dim) (Fin D.dim) A) i j =
      (((g : Matrix.GeneralLinearGroup (Fin D.dim) A) :
        Matrix (Fin D.dim) (Fin D.dim) A) i j) ^ p ^ k := by
  rw [coe_frobenius, Matrix.GeneralLinearGroup.map_apply, iterateFrobenius_def]

/-- Frobenius raises the parameter of every numbered root subgroup to its `p ^ k`-th power. -/
@[simp]
theorem frobenius_rootSubgroupPoints (γ : Fin t.numRoots) (u : A) :
    D.frobenius p k A (D.rootSubgroupPoints γ A (Multiplicative.ofAdd u)) =
      D.rootSubgroupPoints γ A (Multiplicative.ofAdd (u ^ p ^ k)) := by
  rw [frobenius_def, map_rootSubgroupPoints, toAdd_ofAdd, iterateFrobenius_def]

/-- On the actual weight-lattice torus, Frobenius raises every coordinate to its
`p ^ k`-th power. -/
@[simp]
theorem frobenius_torusPoints (s : Fin t.rank → Aˣ) :
    D.frobenius p k A (D.torusPoints A s) = D.torusPoints A (s ^ p ^ k) := by
  rw [frobenius_def, map_torusPoints]
  exact congrArg (D.torusPoints A) (map_iterateFrobenius_units_eq_pow A p k s)

/-- The character pullback of Frobenius on the actual torus is multiplication by `p ^ k`. -/
theorem isCharacterMap_frobenius :
    IsCharacterMap (D.torusPoints A) (D.frobenius p k A) ((p ^ k : ℕ) • 1) := by
  refine isCharacterMap_iff.mpr fun s => ?_
  rw [frobenius_torusPoints, torusPointMap_nsmul, torusPointMap_one,
    MonoidHom.pow_apply, MonoidHom.id_apply]

/-- The zeroth Frobenius is the identity on the point group. -/
@[simp]
theorem frobenius_zero : D.frobenius p 0 A = MonoidHom.id _ := by
  rw [frobenius_def, iterateFrobenius_zero, GeneralLinear.IntegralPointsPresentation.map_id]

/-- Addition of Frobenius exponents corresponds to composition. -/
theorem frobenius_add (m : ℕ) :
    D.frobenius p (k + m) A = (D.frobenius p k A).comp (D.frobenius p m A) := by
  rw [frobenius_def, iterateFrobenius_add,
    GeneralLinear.IntegralPointsPresentation.map_comp (Q := D.pointsPresentation A),
    ← frobenius_def, ← frobenius_def]

/-- Taking powers of Frobenius multiplies its iteration index. -/
-- Select the composition monoid on endomorphisms before elaborating powers.
theorem frobenius_pow (m : ℕ) :
    (show _root_.Monoid.End (D.points A) from D.frobenius p k A) ^ m =
      D.frobenius p (k * m) A :=
  Monoid.End.pow_eq_of_add_eq_comp (fun j => D.frobenius p j A)
    (D.frobenius_zero p A) (fun a b => D.frobenius_add p a A b) k m

/-- Frobenius commutes with any homomorphism of value rings of the same exponential
characteristic, including maps between different universes. -/
theorem map_frobenius {B : Type v'} [CommRing B] [ExpChar B p] (f : A →+* B)
    (g : D.points A) :
    (D.pointsPresentation A).map (D.pointsPresentation B) f (D.frobenius p k A g) =
      D.frobenius p k B ((D.pointsPresentation A).map (D.pointsPresentation B) f g) := by
  have h := congrArg ((D.pointsPresentation A).map (D.pointsPresentation B))
    (f.iterateFrobenius_comm p k)
  rw [GeneralLinear.IntegralPointsPresentation.map_comp (Q := D.pointsPresentation A),
    GeneralLinear.IntegralPointsPresentation.map_comp (Q := D.pointsPresentation B)] at h
  simpa only [frobenius_def, MonoidHom.comp_apply] using DFunLike.congr_fun h g

end

end TauCeti.DynkinType.ChevalleyDatum
