/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.GroupAlgebra.Galois.FiniteType
public import TauCeti.Algebra.AlgebraicGroup.GroupAlgebra.Galois.Splitting
public import TauCeti.Algebra.AlgebraicGroup.Torus.Splitting
import Mathlib.Algebra.AffineMonoid.UniqueSums

/-!
# Galois descent produces a torus

Let `L / k` be a finite Galois extension and let `M` be a lattice, that is, a torsion-free
finitely generated abelian group, carrying an integral representation of `Gal(L/k)`. The
invariants of the simultaneous semilinear action on `L[M]` form a finite-type commutative Hopf
algebra over `k` whose scalar extension to `L` is `L[M]` again. This file bundles the resulting
affine group as an object of the finite-type coordinate category and proves that it is a torus,
split by `L`.

This is the existence half of the Galois-descent classification of tori: every integral
representation of a finite Galois group on a lattice is realised by a torus over the base field,
split by the extension the representation is taken over. Identifying the geometric character
lattice of that torus with the given Galois module is a separate step. Nothing here restricts the
characteristic, and the action of `Gal(L/k)` on the lattice is arbitrary; a split torus is the
case of the trivial action.

## Main declarations

* `TauCeti.GaloisDescent.exponentGroup`: the exponent group of the split group algebra, bundled
  as a finitely generated commutative group.
* `TauCeti.GaloisDescent.descendedCoordinateRing`: the descended coordinate Hopf algebra as a
  finite-type object.
* `TauCeti.GaloisDescent.descendedBaseChangeIso`: over `L` it becomes the diagonalizable group
  of the exponent group.
* `TauCeti.GaloisDescent.torusCommHopfAlgProperty_descendedCoordinateRing`: for a torsion-free
  exponent group it is the coordinate Hopf algebra of a torus.
* `TauCeti.GaloisDescent.splitTorusCommHopfAlgProperty_baseChange_descendedCoordinateRing`: that
  torus is split by `L`.

## References

* J. S. Milne, *Algebraic Groups* (2017), Theorem 12.23 and Appendix A.64.

This completes the descent construction of Layer 4, "Tori: split and non-split", of the
ReductiveGroups roadmap: the semilinear action, the invariant algebra, its finite type, its Hopf
structure and its splitting were the preceding steps, and the torus is what they were for.
-/

public section

open CategoryTheory

namespace TauCeti.GaloisDescent

universe u

variable {k L M : Type u} [Field k] [Field L] [Algebra k L] [AddCommGroup M]
variable [FiniteDimensional k L] [IsGalois k L] [Module.Finite ℤ M]

variable (rho : Representation ℤ (L ≃ₐ[k] L) M)

/-- The exponent group of the split group algebra, written multiplicatively and bundled as a
finitely generated commutative group.

Once the descended group is known to be a torus this is its geometric character lattice, but
finite generation alone is what the bundling needs. -/
noncomputable def exponentGroup : FGCommGrpCat.{u} :=
  letI : AddGroup.FG M := Module.Finite.iff_addGroup_fg.mp inferInstance
  FGCommGrpCat.of (Multiplicative M)

/-- The affine group descended from the diagonalizable group `D(M)` along a finite Galois
extension, as an object of the category of finite-type commutative Hopf algebras.

Its coordinate algebra is the invariant subalgebra `(L[M])^{Gal(L/k)}` for the action twisting
both the coefficients and the exponents. -/
noncomputable def descendedCoordinateRing : FiniteTypeCommHopfAlgCat.{u, u} k :=
  FiniteTypeCommHopfAlgCat.of k (groupAlgebraInvariants rho)

/-- **The descended group becomes the diagonalizable group `D(M)` over `L`.**

This is `groupAlgebraInvariantsBaseChangeBialgEquiv` bundled as an isomorphism of finite-type
coordinate Hopf algebras over the splitting field. -/
noncomputable def descendedBaseChangeIso :
    FiniteTypeCommHopfAlgCat.baseChange (K := L) (descendedCoordinateRing rho) ≅
      DiagonalizableGroup.coordinateRing L (exponentGroup (M := M)) :=
  ObjectProperty.isoMk _
    (_root_.CommHopfAlgCat.isoMk (groupAlgebraInvariantsBaseChangeBialgEquiv rho))

/-- **The affine group descended from a Galois lattice is a torus.**

Torsion freeness of the lattice is what rules out the finite groups of multiplicative type such
as `μ_n`; no hypothesis is placed on the characteristic of `k` or on the action of `Gal(L/k)` on
the lattice. -/
theorem torusCommHopfAlgProperty_descendedCoordinateRing [IsAddTorsionFree M] :
    torusCommHopfAlgProperty k (descendedCoordinateRing rho) := by
  have : AddGroup.FG M := Module.Finite.iff_addGroup_fg.mp inferInstance
  have : UniqueProds (exponentGroup (M := M)) :=
    inferInstanceAs (UniqueProds (Multiplicative M))
  exact torusCommHopfAlgProperty.of_baseChange_iso_coordinateRing k L
    (descendedCoordinateRing rho) (exponentGroup (M := M)) (descendedBaseChangeIso rho)

/-- **The descended torus is split by the Galois extension it was descended along.** -/
theorem splitTorusCommHopfAlgProperty_baseChange_descendedCoordinateRing [IsAddTorsionFree M] :
    splitTorusCommHopfAlgProperty L
      (FiniteTypeCommHopfAlgCat.baseChange (K := L) (descendedCoordinateRing rho)) := by
  have : AddGroup.FG M := Module.Finite.iff_addGroup_fg.mp inferInstance
  have : IsMulTorsionFree (exponentGroup (M := M)) :=
    inferInstanceAs (IsMulTorsionFree (Multiplicative M))
  exact (splitTorusCommHopfAlgProperty L).prop_of_iso (descendedBaseChangeIso rho).symm
    (splitTorusCommHopfAlgProperty_coordinateRing L (exponentGroup (M := M)))

end TauCeti.GaloisDescent
