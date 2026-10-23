/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Semisimple.AlgebraicallyClosed
public import TauCeti.Algebra.AlgebraicGroup.Solvable.Radical.AffineQuotient
public import TauCeti.RingTheory.Smooth.GeometricallyReduced
import TauCeti.Algebra.AlgebraicGroup.Smooth.GeometricallyReduced
import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Coinvariants.Exactness

/-!
# The quotient by the solvable radical is semisimple

For a smooth connected affine group over an algebraically closed field, the affine quotient
by its solvable radical is semisimple. The quotient is the actual Hopf algebra of normal
coinvariants, with the original radical as its scheme-theoretic kernel.

The proof combines the trivial-radical theorem from
`TauCeti.Algebra.AlgebraicGroup.Solvable.Radical.AffineQuotient` with the algebraically
closed semisimplicity criterion. Smoothness and geometric connectedness descend along
the injective coordinate morphism. No characteristic assumption is needed.

## References

* J. S. Milne, *Algebraic Groups* (2017), Chapters 19 and 21.
* A. Borel, *Linear Algebraic Groups*, §11.21.
-/

public section

namespace TauCeti

universe u

open CategoryTheory

variable {k : Type u} [Field k] [IsAlgClosed k]

open FiniteTypeCommHopfAlgCat in
/-- Over an algebraically closed field, a faithfully flat quotient of a smooth geometrically
connected affine group whose kernel is the solvable radical is semisimple. -/
theorem semisimpleCommHopfAlgProperty_of_kernel_eq_solvableRadical
    {Q G : FiniteTypeCommHopfAlgCat.{u, u} k}
    (p : Q.obj ⟶ G.obj) (hp : p.hom.toAlgHom.toRingHom.FaithfullyFlat)
    (hsmooth : Algebra.Smooth k G)
    (hconnected : geometricallyConnectedCommHopfAlgProperty k G.obj)
    (hker : CommHopfAlgCat.kernelHopfIdeal p =
      FiniteTypeCommHopfAlgCat.solvableRadicalDefiningIdeal G) :
    semisimpleCommHopfAlgProperty k Q := by
  have hred := geometricallyReducedCommHopfAlgProperty.of_injective p.hom.toAlgHom hp.injective
    (geometricallyReducedCommHopfAlgProperty_of_smooth k G.obj
      ((smoothCommHopfAlgProperty_iff _).mpr hsmooth))
  let _ : Algebra.IsGeometricallyReduced k Q := hred.isGeometricallyReduced
  rw [semisimpleCommHopfAlgProperty_iff_solvableRadicalDefiningIdeal_eq_augmentation]
  exact ⟨(smoothCommHopfAlgProperty_iff Q.obj).mp
      (smoothCommHopfAlgProperty_of_geometricallyReduced k Q.obj hred),
    geometricallyConnectedCommHopfAlgProperty.of_injective
      p.hom.toAlgHom hp.injective hconnected,
    solvableRadicalDefiningIdeal_eq_augmentation_of_kernel_eq_solvableRadical
      p hp hker⟩

namespace FiniteTypeCommHopfAlgCat

/-- The affine quotient of a smooth geometrically connected group by its solvable radical
is semisimple over an algebraically closed field, in every characteristic. -/
theorem semisimple_coinvariants_solvableRadical
    (G : FiniteTypeCommHopfAlgCat.{u, u} k) [Algebra.Smooth k G]
    (hconnected : geometricallyConnectedCommHopfAlgProperty k G.obj) :
    let hR := isNormal_solvableRadicalDefiningIdeal G
    letI := hR.isHopfSubalgebra_coinvariants.hopfAlgebra
    letI : Algebra.IsGeometricallyReduced k G := isGeometricallyReduced_of_smooth k G
    let Q : FiniteTypeCommHopfAlgCat.{u, u} k :=
      ⟨CommHopfAlgCat.coinvariants hR,
        (finiteTypeCommHopfAlgProperty_iff _).mpr hR.finiteType_coinvariants⟩
    semisimpleCommHopfAlgProperty k Q := by
  intro hR Q
  -- Elaboration eliminates the statement's letI bindings; restore the instance needed below.
  let _ : Algebra.IsGeometricallyReduced k G := isGeometricallyReduced_of_smooth k G
  exact semisimpleCommHopfAlgProperty_of_kernel_eq_solvableRadical (Q := Q)
    (CommHopfAlgCat.coinvariantsι hR) (CommHopfAlgCat.faithfullyFlat_coinvariantsι hR)
    inferInstance hconnected (CommHopfAlgCat.kernelHopfIdeal_coinvariantsι_eq hR)

end FiniteTypeCommHopfAlgCat

end TauCeti
