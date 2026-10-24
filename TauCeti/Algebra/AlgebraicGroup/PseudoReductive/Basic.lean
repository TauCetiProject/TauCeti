/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Reductive.Basic
public import TauCeti.Algebra.AlgebraicGroup.Unipotent.Radical.AffineQuotient
public import TauCeti.Algebra.AlgebraicGroup.AdditiveGroup.Scheme
public import TauCeti.RingTheory.Smooth.GeometricallyReduced

import TauCeti.Algebra.AlgebraicGroup.AdditiveGroup.CoordinateBaseChange
import TauCeti.Algebra.AlgebraicGroup.AdditiveGroup.Unipotent
import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Coinvariants.Exactness
import TauCeti.Algebra.AlgebraicGroup.Reductive.AlgebraicallyClosed
import TauCeti.Algebra.AlgebraicGroup.Smooth.GeometricallyReduced
import TauCeti.Algebra.AlgebraicGroup.Unipotent.Radical.Characteristic
import TauCeti.Algebra.AlgebraicGroup.Unipotent.Radical.Isomorphism
import TauCeti.Algebra.AlgebraicGroup.Unipotent.Radical.Reductive.Basic

/-!
# Pseudo-reductive affine groups

A smooth geometrically connected affine group of finite type over a field `k` is
**pseudo-reductive** when its `k`-unipotent radical `R_{u,k}(G)`, the greatest smooth connected
normal unipotent closed subgroup defined over `k`, is trivial. Reductivity asks instead for
triviality of the unipotent radical of the geometric fibre. The geometric radical need not descend
to `k` when `k` is imperfect, so a pseudo-reductive group need not be reductive; this is the class
of groups studied by Conrad, Gabber and Prasad.

This file defines the predicate and establishes its basic theory:

* reductive groups are pseudo-reductive, over every field;
* over an algebraically closed field, pseudo-reductive and reductive groups coincide;
* the affine quotient `G ⧸ R_{u,k}(G)` of a smooth connected group by its `k`-unipotent radical is
  pseudo-reductive, and over an algebraically closed field it is therefore reductive;
* the additive group is not pseudo-reductive.

Equality of the two notions over perfect fields, which requires Galois descent of the geometric
unipotent radical, is not proved here.

## Main declarations

* `TauCeti.pseudoReductiveCommHopfAlgProperty`: pseudo-reductivity of finite-type commutative Hopf
  algebras over a field.
* `TauCeti.pseudoReductiveCommHopfAlgProperty.unipotentRadicalDefiningIdeal_eq_augmentation`:
  the defining property, with the companion accessors `smooth` and `geometricallyConnected`.
* `TauCeti.reductiveCommHopfAlgProperty.pseudoReductive`: reductive groups are pseudo-reductive.
* `TauCeti.pseudoReductiveCommHopfAlgProperty_iff_reductive`: over an algebraically closed field
  the two notions agree.
* `TauCeti.pseudoReductiveCommHopfAlgProperty_of_kernel_eq_unipotentRadical` and
  `TauCeti.FiniteTypeCommHopfAlgCat.pseudoReductive_coinvariants_unipotentRadical`: the quotient
  by the `k`-unipotent radical is pseudo-reductive.
* `TauCeti.FiniteTypeCommHopfAlgCat.reductive_coinvariants_unipotentRadical`: over an
  algebraically closed field, the quotient by the unipotent radical is reductive.
* `TauCeti.AdditiveGroup.not_pseudoReductiveCommHopfAlgProperty`: `𝔾ₐ` is not pseudo-reductive.

## References

* B. Conrad, O. Gabber, G. Prasad, *Pseudo-reductive Groups*, 2nd ed. (2015), §1.1.
* J. S. Milne, *Algebraic Groups* (2017), §§6.45–6.46 and Chapter 19.
-/

public section

open CategoryTheory

namespace TauCeti

universe u

noncomputable section

/-- The object property selecting pseudo-reductive finite-type commutative Hopf algebras over a
field: the represented group is smooth and geometrically connected, and its unipotent radical over
the ground field is the identity subgroup. A Hopf ideal cuts out that subgroup contravariantly, so
triviality means that the radical's defining ideal is the augmentation ideal. -/
def pseudoReductiveCommHopfAlgProperty (k : Type u) [Field k] :
    ObjectProperty (FiniteTypeCommHopfAlgCat.{u, u} k) :=
  fun H ↦ Algebra.Smooth k H ∧ geometricallyConnectedCommHopfAlgProperty k H.obj ∧
    FiniteTypeCommHopfAlgCat.unipotentRadicalDefiningIdeal H = HopfIdeal.augmentation k H

/-- Pseudo-reductivity means smoothness, geometric connectedness and triviality of the unipotent
radical over the ground field. -/
@[simp]
theorem pseudoReductiveCommHopfAlgProperty_iff (k : Type u) [Field k]
    (H : FiniteTypeCommHopfAlgCat.{u, u} k) :
    pseudoReductiveCommHopfAlgProperty k H ↔
      Algebra.Smooth k H ∧ geometricallyConnectedCommHopfAlgProperty k H.obj ∧
        FiniteTypeCommHopfAlgCat.unipotentRadicalDefiningIdeal H =
          HopfIdeal.augmentation k H :=
  Iff.rfl

/-- Pseudo-reductivity is invariant under isomorphisms of finite-type commutative Hopf algebras. -/
instance (k : Type u) [Field k] :
    (pseudoReductiveCommHopfAlgProperty k).IsClosedUnderIsomorphisms where
  of_iso {H K} e := by
    rintro ⟨hsmooth, hconnected, hradical⟩
    let e' := (forget₂ (FiniteTypeCommHopfAlgCat.{u, u} k) (CommHopfAlgCat.{u} k)).mapIso e
    refine ⟨(smoothCommHopfAlgProperty_iff _).mp ((smoothCommHopfAlgProperty k).prop_of_iso e'
      ((smoothCommHopfAlgProperty_iff _).mpr hsmooth)),
      (geometricallyConnectedCommHopfAlgProperty k).prop_of_iso e' hconnected, ?_⟩
    rw [← FiniteTypeCommHopfAlgCat.comapOfSurjective_unipotentRadicalDefiningIdeal e.symm,
      hradical, HopfIdeal.comapOfSurjective_augmentation]

variable {k : Type u} [Field k]

namespace pseudoReductiveCommHopfAlgProperty

variable {H : FiniteTypeCommHopfAlgCat.{u, u} k}

/-- A pseudo-reductive group is smooth. -/
theorem smooth (hH : pseudoReductiveCommHopfAlgProperty k H) : Algebra.Smooth k H :=
  hH.1

/-- A pseudo-reductive group is geometrically connected. -/
theorem geometricallyConnected (hH : pseudoReductiveCommHopfAlgProperty k H) :
    geometricallyConnectedCommHopfAlgProperty k H.obj :=
  hH.2.1

/-- The unipotent radical of a pseudo-reductive group over its ground field is the identity
subgroup. -/
theorem unipotentRadicalDefiningIdeal_eq_augmentation
    (hH : pseudoReductiveCommHopfAlgProperty k H) :
    FiniteTypeCommHopfAlgCat.unipotentRadicalDefiningIdeal H = HopfIdeal.augmentation k H :=
  hH.2.2

end pseudoReductiveCommHopfAlgProperty

/-- **Reductive groups are pseudo-reductive**, over every field. -/
theorem reductiveCommHopfAlgProperty.pseudoReductive {H : FiniteTypeCommHopfAlgCat.{u, u} k}
    (hH : reductiveCommHopfAlgProperty k H) : pseudoReductiveCommHopfAlgProperty k H :=
  ⟨hH.smooth, hH.geometricallyConnected, hH.unipotentRadicalDefiningIdeal_eq_augmentation⟩

/-- Over an algebraically closed field, a finite-type affine group is pseudo-reductive exactly
when it is reductive. -/
theorem pseudoReductiveCommHopfAlgProperty_iff_reductive [IsAlgClosed k]
    (H : FiniteTypeCommHopfAlgCat.{u, u} k) :
    pseudoReductiveCommHopfAlgProperty k H ↔ reductiveCommHopfAlgProperty k H :=
  (reductiveCommHopfAlgProperty_iff_unipotentRadicalDefiningIdeal_eq_augmentation k H).symm

open FiniteTypeCommHopfAlgCat in
/-- A faithfully flat quotient of a smooth geometrically connected affine group whose kernel is the
unipotent radical over the ground field is pseudo-reductive. -/
theorem pseudoReductiveCommHopfAlgProperty_of_kernel_eq_unipotentRadical
    {Q G : FiniteTypeCommHopfAlgCat.{u, u} k}
    (p : Q.obj ⟶ G.obj) (hp : p.hom.toAlgHom.toRingHom.FaithfullyFlat)
    (hsmooth : Algebra.Smooth k G)
    (hconnected : geometricallyConnectedCommHopfAlgProperty k G.obj)
    (hker : CommHopfAlgCat.kernelHopfIdeal p =
      FiniteTypeCommHopfAlgCat.unipotentRadicalDefiningIdeal G) :
    pseudoReductiveCommHopfAlgProperty k Q := by
  have hred := geometricallyReducedCommHopfAlgProperty.of_injective p.hom.toAlgHom hp.injective
    (geometricallyReducedCommHopfAlgProperty_of_smooth k G.obj
      ((smoothCommHopfAlgProperty_iff _).mpr hsmooth))
  let _ : Algebra.IsGeometricallyReduced k Q := hred.isGeometricallyReduced
  exact ⟨(smoothCommHopfAlgProperty_iff Q.obj).mp
      (smoothCommHopfAlgProperty_of_geometricallyReduced k Q.obj hred),
    geometricallyConnectedCommHopfAlgProperty.of_injective p.hom.toAlgHom hp.injective hconnected,
    unipotentRadicalDefiningIdeal_eq_augmentation_of_kernel_eq_unipotentRadical p hp hker⟩

/-- Over an algebraically closed field, a faithfully flat quotient of a smooth geometrically
connected affine group whose kernel is the unipotent radical is reductive. -/
theorem reductiveCommHopfAlgProperty_of_kernel_eq_unipotentRadical [IsAlgClosed k]
    {Q G : FiniteTypeCommHopfAlgCat.{u, u} k}
    (p : Q.obj ⟶ G.obj) (hp : p.hom.toAlgHom.toRingHom.FaithfullyFlat)
    (hsmooth : Algebra.Smooth k G)
    (hconnected : geometricallyConnectedCommHopfAlgProperty k G.obj)
    (hker : CommHopfAlgCat.kernelHopfIdeal p =
      FiniteTypeCommHopfAlgCat.unipotentRadicalDefiningIdeal G) :
    reductiveCommHopfAlgProperty k Q :=
  (pseudoReductiveCommHopfAlgProperty_iff_reductive Q).mp
    (pseudoReductiveCommHopfAlgProperty_of_kernel_eq_unipotentRadical p hp hsmooth hconnected hker)

namespace FiniteTypeCommHopfAlgCat

/-- The affine quotient of a smooth geometrically connected group by its unipotent radical over the
ground field is pseudo-reductive, in every characteristic. -/
theorem pseudoReductive_coinvariants_unipotentRadical
    (G : FiniteTypeCommHopfAlgCat.{u, u} k) [Algebra.Smooth k G]
    (hconnected : geometricallyConnectedCommHopfAlgProperty k G.obj) :
    let hR := isNormal_unipotentRadicalDefiningIdeal G
    letI := hR.isHopfSubalgebra_coinvariants.hopfAlgebra
    letI : Algebra.IsGeometricallyReduced k G := isGeometricallyReduced_of_smooth k G
    let Q : FiniteTypeCommHopfAlgCat.{u, u} k :=
      ⟨CommHopfAlgCat.coinvariants hR,
        (finiteTypeCommHopfAlgProperty_iff _).mpr hR.finiteType_coinvariants⟩
    pseudoReductiveCommHopfAlgProperty k Q := by
  intro hR Q
  -- Elaboration eliminates the statement's letI bindings; restore the instance needed below.
  let _ : Algebra.IsGeometricallyReduced k G := isGeometricallyReduced_of_smooth k G
  exact pseudoReductiveCommHopfAlgProperty_of_kernel_eq_unipotentRadical (Q := Q)
    (CommHopfAlgCat.coinvariantsι hR) (CommHopfAlgCat.faithfullyFlat_coinvariantsι hR)
    inferInstance hconnected (CommHopfAlgCat.kernelHopfIdeal_coinvariantsι_eq hR)

/-- **The quotient by the unipotent radical is reductive.** Over an algebraically closed field,
the affine quotient of a smooth geometrically connected group by its unipotent radical is
reductive, in every characteristic. -/
theorem reductive_coinvariants_unipotentRadical [IsAlgClosed k]
    (G : FiniteTypeCommHopfAlgCat.{u, u} k) [Algebra.Smooth k G]
    (hconnected : geometricallyConnectedCommHopfAlgProperty k G.obj) :
    let hR := isNormal_unipotentRadicalDefiningIdeal G
    letI := hR.isHopfSubalgebra_coinvariants.hopfAlgebra
    letI : Algebra.IsGeometricallyReduced k G := isGeometricallyReduced_of_smooth k G
    let Q : FiniteTypeCommHopfAlgCat.{u, u} k :=
      ⟨CommHopfAlgCat.coinvariants hR,
        (finiteTypeCommHopfAlgProperty_iff _).mpr hR.finiteType_coinvariants⟩
    reductiveCommHopfAlgProperty k Q := by
  intro hR Q
  exact (pseudoReductiveCommHopfAlgProperty_iff_reductive Q).mp
    (pseudoReductive_coinvariants_unipotentRadical G hconnected)

end FiniteTypeCommHopfAlgCat

namespace AdditiveGroup

/-- **The additive group is not pseudo-reductive**: it is itself a nontrivial smooth connected
unipotent group, hence equal to its own unipotent radical. -/
theorem not_pseudoReductiveCommHopfAlgProperty :
    ¬ pseudoReductiveCommHopfAlgProperty k
      (FiniteTypeCommHopfAlgCat.of k (SymmetricAlgebra k k)) := by
  rintro ⟨-, -, hradical⟩
  have hbot := (FiniteTypeCommHopfAlgCat.unipotentRadicalDefiningIdeal_eq_bot_iff
    (FiniteTypeCommHopfAlgCat.of k (SymmetricAlgebra k k))).mpr
      ⟨geometricallyConnectedCommHopfAlgProperty_coordinateHopfAlgebra k,
        smoothUnipotentCommHopfAlgProperty_coordinateHopfAlgebra k⟩
  rw [hbot] at hradical
  -- The primitive generator vanishes under the counit but is nonzero.
  have hmem : SymmetricAlgebra.ι k k 1 ∈
      HopfIdeal.augmentation k (FiniteTypeCommHopfAlgCat.of k (SymmetricAlgebra k k)) := by
    rw [HopfIdeal.mem_augmentation]
    exact SymmetricAlgebra.counit_ι (R := k) (M := k) 1
  rw [← hradical, HopfIdeal.mem_bot, ← pow_one (SymmetricAlgebra.ι k k 1),
    ← monomialBasis_apply] at hmem
  exact (monomialBasis k).ne_zero 1 hmem

end AdditiveGroup

end

end TauCeti
