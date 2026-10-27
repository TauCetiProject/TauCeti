/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.IntegralLattice.Discriminant.Pi
public import TauCeti.LinearAlgebra.IntegralLattice.RootLattice.GlueAlphabet.Basic

/-!
# Orthogonal sums of root lattices and their glue words

A reducible simply-laced root system is a finite family `t : ι → DynkinType` of valid simply-laced
components; for an ordered list of components, `ι = Fin n` and the order of the components is the
order of the coordinates.  Its root lattice is the orthogonal sum
`⊥ i, (t i).rootLattice` (`TauCeti.IntegralLattice.pi`), and a glue word records one label of the
glue alphabet `(t i).glueAlphabet` per component (Conway--Sloane, Chapter 4 §3 and
Chapter 16 §1).

This file shows that the orthogonal sum of root lattices is even and positive definite, of rank
`∑ i, rank (t i)`, and identifies the orthogonal sum of the glue alphabets with the actual
discriminant quadratic module of the orthogonal sum of root lattices
(`TauCeti.DynkinType.glueWordIsometry`).  The identification acts componentwise by the
single-component isometries `TauCeti.DynkinType.glueAlphabetIsometry`
(`TauCeti.DynkinType.discriminantGroupPiEquiv_glueWordIsometry`), so a glue word is a coordinate
description of a class in the discriminant group.  Isotropic and Lagrangian subgroups of glue
words correspond to those of the discriminant group by
`TauCeti.FiniteQuadraticModule.Isometry.isIsotropic_map_iff` and
`TauCeti.FiniteQuadraticModule.Isometry.isLagrangian_map_iff`.

## Main declarations

* `TauCeti.DynkinType.isEven_pi_rootLattice`, `TauCeti.DynkinType.isPosDef_pi_rootLattice`,
  `TauCeti.DynkinType.finrank_pi_rootLattice`: the orthogonal sum of root lattices is even,
  positive definite, and of rank the sum of the ranks.
* `TauCeti.DynkinType.glueWordIsometry`: the isometry from the orthogonal sum of glue alphabets
  to the discriminant quadratic module of the orthogonal sum of root lattices.
* `TauCeti.DynkinType.isNondegenerate_pi_glueAlphabet`,
  `TauCeti.DynkinType.natCard_pi_glueAlphabet`: the module of glue words is nondegenerate, of
  order `∏ i, |det (t i).cartanMatrix|`.

## References

* J. H. Conway and N. J. A. Sloane, *Sphere Packings, Lattices and Groups*, Chapter 4, §3, and
  Chapter 16, §1.
* V. V. Nikulin, *Integral symmetric bilinear forms and some of their applications*, §1.
-/

public section

namespace TauCeti.DynkinType

open IntegralLattice

universe v

variable {ι : Type v} [Fintype ι] (t : ι → DynkinType) (ht : ∀ i, (t i).IsSimplyLaced)

/-- The orthogonal sum of the root lattices of simply-laced components is even. -/
theorem isEven_pi_rootLattice : (pi fun i ↦ (t i).rootLattice (ht i)).IsEven :=
  isEven_pi fun i ↦ (t i).isEven_rootLattice (ht i)

/-- The orthogonal sum of the root lattices of simply-laced components is positive definite. -/
theorem isPosDef_pi_rootLattice : (pi fun i ↦ (t i).rootLattice (ht i)).IsPosDef :=
  (isPosDef_pi_iff _).mpr fun i ↦ (t i).isPosDef_rootLattice (ht i)

/-- The rank of the orthogonal sum of the root lattices of simply-laced components is the sum of
the ranks of the components. -/
theorem finrank_pi_rootLattice :
    Module.finrank ℤ (pi fun i ↦ (t i).rootLattice (ht i)) = ∑ i, (t i).rank := by
  simp only [finrank_pi, finrank_rootLattice]

/-- **Glue words are the discriminant classes of an orthogonal sum of root lattices.**  For a
finite family of valid simply-laced components, this is the isometry from the orthogonal sum of
the glue alphabets to the discriminant quadratic module of the orthogonal sum of the root
lattices, acting on each component by `TauCeti.DynkinType.glueAlphabetIsometry`. -/
noncomputable def glueWordIsometry (hv : ∀ i, (t i).Valid) :
    FiniteQuadraticModule.Isometry (FiniteQuadraticModule.pi fun i ↦ (t i).glueAlphabet (ht i))
      ((pi fun i ↦ (t i).rootLattice (ht i)).discriminantQuadraticModule
        (isEven_pi_rootLattice t ht)) :=
  discriminantQuadraticIsometryPiOfIsometry _ fun i ↦ (t i).glueAlphabetIsometry (hv i) (ht i)

/-- The glue-word isometry sends a word to the class whose component in the discriminant group
of each root lattice is the image of the corresponding label. -/
@[simp]
theorem discriminantGroupPiEquiv_glueWordIsometry (hv : ∀ i, (t i).Valid)
    (w : ∀ i, (t i).glueAlphabet (ht i)) (i : ι) :
    discriminantGroupPiEquiv _ (glueWordIsometry t ht hv w) i =
      (t i).glueAlphabetIsometry (hv i) (ht i) (w i) := by
  rw [glueWordIsometry, discriminantQuadraticIsometryPiOfIsometry_apply]
  exact congrFun ((discriminantGroupPiEquiv _).apply_symm_apply
    fun i ↦ (t i).glueAlphabetIsometry (hv i) (ht i) (w i)) i

/-- The module of glue words of a finite family of valid simply-laced components is
nondegenerate. -/
theorem isNondegenerate_pi_glueAlphabet (hv : ∀ i, (t i).Valid) :
    (FiniteQuadraticModule.pi fun i ↦ (t i).glueAlphabet (ht i)).IsNondegenerate :=
  (FiniteQuadraticModule.isNondegenerate_pi_iff _).mpr fun i ↦
    (t i).isNondegenerate_glueAlphabet (hv i) (ht i)

/-- The module of glue words of a finite family of valid simply-laced components has order
`∏ i, |det (t i).cartanMatrix|`, the discriminant of the orthogonal sum of root lattices. -/
theorem natCard_pi_glueAlphabet (hv : ∀ i, (t i).Valid) :
    Nat.card (FiniteQuadraticModule.pi fun i ↦ (t i).glueAlphabet (ht i)) =
      ∏ i, (t i).cartanMatrix.det.natAbs := by
  rw [Nat.card_pi]
  exact Finset.prod_congr rfl fun i _ ↦ (t i).natCard_glueAlphabet (hv i) (ht i)

end TauCeti.DynkinType
