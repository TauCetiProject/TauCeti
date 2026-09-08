/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Borel.Existence
public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Normal.Product.Basic
public import TauCeti.Algebra.AlgebraicGroup.Solvable.Radical.Semisimple
import TauCeti.Algebra.AlgebraicGroup.Connected.Product
import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Normal.Product.Properties
import TauCeti.Algebra.AlgebraicGroup.Smooth.Product
import TauCeti.Algebra.AlgebraicGroup.Solvable.NormalProduct

/-!
# The radical is contained in every Borel subgroup

Let `H` be the coordinate Hopf algebra of a finite-type affine group over a field. A Borel
candidate is a smooth, geometrically connected, geometrically solvable closed subgroup, and a
Borel subgroup is a maximal one. This file proves that every *normal* Borel candidate is
contained in every maximal one; in particular the solvable radical `R(G)`, and hence the
unipotent radical `R_u(G)`, lies inside every Borel subgroup.

The argument is the standard one and reuses the product machinery that built the two radicals.
Let `B` be a Borel candidate and let `N` be a connected normal smooth solvable closed subgroup.
Since `N` is normal, multiplication is a homomorphism from the conjugation semidirect product of
`N` and `B` into the ambient group, and its scheme-theoretic image `N · B` contains both factors.
That image is again smooth, geometrically connected and geometrically solvable, so it is a Borel
candidate containing `B`. Maximality of `B` forces `N · B = B`, so `N` is contained in `B`.
Normality of `N` is what makes `N · B` a subgroup at all; no hypothesis is needed on `B` beyond
being a Borel candidate, and nothing here needs the ground field to be algebraically closed.

Contravariance is the only thing to keep in mind when reading the statements: Hopf ideals order
oppositely to the closed subgroups they cut out, so `J ≤ I` says that the subgroup defined by `I`
sits inside the subgroup defined by `J`.

Two consequences are recorded. If the radical is the whole group — that is, if the group is
itself smooth, connected and solvable — then it is its own unique Borel subgroup. Conversely, a
smooth geometrically connected group with a trivial geometric Borel subgroup is semisimple, since
its geometric solvable radical is squeezed between the trivial Borel and the identity subgroup.

## Main declarations

* `TauCeti.HopfIdeal.IsBorelCandidate.productOfNormal`: the multiplication image of a connected
  normal smooth solvable closed subgroup with a Borel candidate is a Borel candidate.
* `TauCeti.HopfIdeal.IsBorelCandidate.isSolvableRadicalCandidate`: a normal Borel candidate is a
  solvable-radical candidate.
* `TauCeti.HopfIdeal.IsSolvableRadicalCandidate.le_of_minimal_isBorelCandidate`: **every
  connected normal smooth solvable closed subgroup is contained in every Borel subgroup.**
* `TauCeti.FiniteTypeCommHopfAlgCat.le_solvableRadicalDefiningIdeal_of_minimal_isBorelCandidate`:
  **the solvable radical is contained in every Borel subgroup.**
* `TauCeti.FiniteTypeCommHopfAlgCat.le_unipotentRadicalDefiningIdeal_of_minimal_isBorelCandidate`:
  the unipotent radical is contained in every Borel subgroup.
* `TauCeti.FiniteTypeCommHopfAlgCat.eq_solvableRadicalDefiningIdeal_of_minimal_isBorelCandidate`:
  a normal Borel subgroup is exactly the solvable radical.
* `TauCeti.HopfIdeal.IsBorelOverAlgClosed.le_solvableRadicalDefiningIdeal` and
  `TauCeti.HopfIdeal.IsBorelOverAlgClosed.le_unipotentRadicalDefiningIdeal`: the same two
  containments for the Borel-subgroup predicate over an algebraically closed field.
* `TauCeti.HopfIdeal.IsBorel.baseChangeHopfIdeal_le_solvableRadicalDefiningIdeal` and
  `TauCeti.HopfIdeal.IsBorel.baseChangeHopfIdeal_le_unipotentRadicalDefiningIdeal`: over an
  arbitrary field, the base change of a Borel subgroup contains the two geometric radicals.
* `TauCeti.FiniteTypeCommHopfAlgCat.eq_bot_of_solvableRadicalDefiningIdeal_eq_bot`: a smooth
  connected solvable affine group is its own unique Borel subgroup.
* `TauCeti.semisimpleCommHopfAlgProperty_of_minimal_isBorelCandidate_eq_augmentation`: a smooth
  geometrically connected affine group with a trivial geometric Borel subgroup is semisimple.

## References

* J. S. Milne, *Algebraic Groups* (2017), §§17.a and 19.b.
* A. Borel, *Linear Algebraic Groups*, 2nd ed. (1991), §11.21.
* T. A. Springer, *Linear Algebraic Groups*, §6.2.

The product-image bookkeeping follows the formal organization of
`TauCeti.Algebra.AlgebraicGroup.Solvable.Radical.Product`, where the same three closure
properties are proved for two normal factors.
-/

public section

open CategoryTheory

namespace TauCeti

universe u

noncomputable section

namespace HopfIdeal

variable {k : Type u} [Field k]
variable {H : FiniteTypeCommHopfAlgCat.{u, u} k} {I J : HopfIdeal k H}

/-- The scheme-theoretic multiplication image of a connected normal smooth solvable closed
subgroup with a Borel candidate is again a Borel candidate.

Normality of the solvable factor is what makes multiplication a homomorphism out of the
conjugation semidirect product; the other factor is an arbitrary Borel candidate. -/
theorem IsBorelCandidate.productOfNormal
    (hJ : IsBorelCandidate k H J) (hI : IsSolvableRadicalCandidate H I) :
    IsBorelCandidate k H
      (HopfIdeal.ker (CommHopfAlgCat.productMapOfNormal H.obj I J hI.isNormal).hom) := by
  refine IsBorelCandidate.mk ?_ ?_ ?_
  · exact smoothCommHopfAlgProperty.productOfNormal H.obj I J hI.isNormal
      ((smoothCommHopfAlgProperty_iff _).mpr hI.smooth) hJ.smooth
  · exact geometricallyConnectedCommHopfAlgProperty.productOfNormal H.obj I J hI.isNormal
      hI.geometricallyConnected hJ.geometricallyConnected
  · exact geometricallySolvablePointsCommHopfAlgProperty.productOfNormal H.obj I J hI.isNormal
      ((smoothCommHopfAlgProperty_iff _).mpr hI.smooth) hJ.smooth
      hI.geometricallySolvable hJ.geometricallySolvable

/-- **Every connected normal smooth solvable closed subgroup is contained in every Borel
subgroup.**

In the contravariant Hopf-ideal order, `J ≤ I` says that the subgroup cut out by `I` is contained
in the maximal Borel candidate cut out by `J`. -/
theorem IsSolvableRadicalCandidate.le_of_minimal_isBorelCandidate
    (hI : IsSolvableRadicalCandidate H I) (hJ : Minimal (IsBorelCandidate k H) J) :
    J ≤ I :=
  (hJ.2 (hJ.1.productOfNormal hI)
      (CommHopfAlgCat.ker_productMapOfNormal_le_right H.obj I J hI.isNormal)).trans
    (CommHopfAlgCat.ker_productMapOfNormal_le_left H.obj I J hI.isNormal)

/-- A normal Borel candidate is a solvable-radical candidate: normality is the only condition
separating the two notions. -/
theorem IsBorelCandidate.isSolvableRadicalCandidate
    (hJ : IsBorelCandidate k H J) (hnormal : J.IsNormal) :
    IsSolvableRadicalCandidate H J :=
  IsSolvableRadicalCandidate.mk hnormal hJ.geometricallyConnected
    ((smoothCommHopfAlgProperty_iff _).mp hJ.smooth) hJ.geometricallySolvable

end HopfIdeal

namespace FiniteTypeCommHopfAlgCat

variable {k : Type u} [Field k]

/-- **The solvable radical is contained in every Borel subgroup.** -/
theorem le_solvableRadicalDefiningIdeal_of_minimal_isBorelCandidate
    (H : FiniteTypeCommHopfAlgCat.{u, u} k) {J : HopfIdeal k H}
    (hJ : Minimal (HopfIdeal.IsBorelCandidate k H) J) :
    J ≤ solvableRadicalDefiningIdeal H :=
  (isSolvableRadicalCandidate_solvableRadicalDefiningIdeal H).le_of_minimal_isBorelCandidate hJ

/-- The unipotent radical is contained in every Borel subgroup, since it is contained in the
solvable radical. -/
theorem le_unipotentRadicalDefiningIdeal_of_minimal_isBorelCandidate
    (H : FiniteTypeCommHopfAlgCat.{u, u} k) {J : HopfIdeal k H}
    (hJ : Minimal (HopfIdeal.IsBorelCandidate k H) J) :
    J ≤ unipotentRadicalDefiningIdeal H :=
  (le_solvableRadicalDefiningIdeal_of_minimal_isBorelCandidate H hJ).trans
    (solvableRadicalDefiningIdeal_le_unipotentRadicalDefiningIdeal H)

/-- **A normal Borel subgroup is exactly the solvable radical.**

One containment is maximality of the Borel subgroup, the other is the universal property of the
radical applied to the Borel subgroup, which is a solvable-radical candidate once it is normal. -/
theorem eq_solvableRadicalDefiningIdeal_of_minimal_isBorelCandidate
    (H : FiniteTypeCommHopfAlgCat.{u, u} k) {J : HopfIdeal k H}
    (hnormal : J.IsNormal) (hJ : Minimal (HopfIdeal.IsBorelCandidate k H) J) :
    J = solvableRadicalDefiningIdeal H :=
  le_antisymm (le_solvableRadicalDefiningIdeal_of_minimal_isBorelCandidate H hJ)
    (solvableRadicalDefiningIdeal_le H J (hJ.1.isSolvableRadicalCandidate hnormal))

/-- **A smooth connected solvable affine group is its own unique Borel subgroup.**

The hypothesis says that the solvable radical is the whole group, the closed subgroup cut out by
the zero Hopf ideal. -/
theorem eq_bot_of_solvableRadicalDefiningIdeal_eq_bot
    (H : FiniteTypeCommHopfAlgCat.{u, u} k) {J : HopfIdeal k H}
    (hH : solvableRadicalDefiningIdeal H = ⊥)
    (hJ : Minimal (HopfIdeal.IsBorelCandidate k H) J) :
    J = ⊥ :=
  le_antisymm (hH ▸ le_solvableRadicalDefiningIdeal_of_minimal_isBorelCandidate H hJ) bot_le

end FiniteTypeCommHopfAlgCat

namespace HopfIdeal.IsBorelOverAlgClosed

variable {k : Type u} [Field k] {H : FiniteTypeCommHopfAlgCat.{u, u} k} {I : HopfIdeal k H}

/-- Over an algebraically closed field, the solvable radical is contained in every Borel
subgroup. -/
theorem le_solvableRadicalDefiningIdeal (hI : IsBorelOverAlgClosed k H I) :
    I ≤ FiniteTypeCommHopfAlgCat.solvableRadicalDefiningIdeal H :=
  FiniteTypeCommHopfAlgCat.le_solvableRadicalDefiningIdeal_of_minimal_isBorelCandidate H
    ((isBorelOverAlgClosed_iff k H I).mp hI).2

/-- Over an algebraically closed field, the unipotent radical is contained in every Borel
subgroup. -/
theorem le_unipotentRadicalDefiningIdeal (hI : IsBorelOverAlgClosed k H I) :
    I ≤ FiniteTypeCommHopfAlgCat.unipotentRadicalDefiningIdeal H :=
  FiniteTypeCommHopfAlgCat.le_unipotentRadicalDefiningIdeal_of_minimal_isBorelCandidate H
    ((isBorelOverAlgClosed_iff k H I).mp hI).2

end HopfIdeal.IsBorelOverAlgClosed

namespace HopfIdeal.IsBorel

variable {k : Type u} [Field k] {H : CommHopfAlgCat.{u} k} [Algebra.FiniteType k H]
variable {I : HopfIdeal k H}

/-- Over an arbitrary field, the base change of a Borel subgroup contains the geometric solvable
radical. -/
theorem baseChangeHopfIdeal_le_solvableRadicalDefiningIdeal (hI : IsBorel k H I) :
    CommHopfAlgCat.baseChangeHopfIdeal (K := AlgebraicClosure k) I ≤
      FiniteTypeCommHopfAlgCat.solvableRadicalDefiningIdeal
        (FiniteTypeCommHopfAlgCat.baseChange (K := AlgebraicClosure k)
          ⟨H, (finiteTypeCommHopfAlgProperty_iff H).2 inferInstance⟩) :=
  IsBorelOverAlgClosed.le_solvableRadicalDefiningIdeal
    ((isBorel_iff_isBorelOverAlgClosed_baseChange k H I).mp hI)

/-- Over an arbitrary field, the base change of a Borel subgroup contains the geometric unipotent
radical. -/
theorem baseChangeHopfIdeal_le_unipotentRadicalDefiningIdeal (hI : IsBorel k H I) :
    CommHopfAlgCat.baseChangeHopfIdeal (K := AlgebraicClosure k) I ≤
      FiniteTypeCommHopfAlgCat.unipotentRadicalDefiningIdeal
        (FiniteTypeCommHopfAlgCat.baseChange (K := AlgebraicClosure k)
          ⟨H, (finiteTypeCommHopfAlgProperty_iff H).2 inferInstance⟩) :=
  IsBorelOverAlgClosed.le_unipotentRadicalDefiningIdeal
    ((isBorel_iff_isBorelOverAlgClosed_baseChange k H I).mp hI)

end HopfIdeal.IsBorel

variable {k : Type u} [Field k]

/-- **A smooth geometrically connected affine group with a trivial geometric Borel subgroup is
semisimple.**

The Borel subgroup is taken on the geometric fibre, and triviality means that its defining Hopf
ideal is the augmentation ideal. The geometric solvable radical is then contained in the identity
subgroup, hence equal to it. -/
theorem semisimpleCommHopfAlgProperty_of_minimal_isBorelCandidate_eq_augmentation
    (H : FiniteTypeCommHopfAlgCat.{u, u} k)
    (hsmooth : Algebra.Smooth k H)
    (hconnected : geometricallyConnectedCommHopfAlgProperty k H.obj)
    {J : HopfIdeal (AlgebraicClosure k)
      (FiniteTypeCommHopfAlgCat.baseChange (K := AlgebraicClosure k) H)}
    (hJ : Minimal (HopfIdeal.IsBorelCandidate (AlgebraicClosure k)
      (FiniteTypeCommHopfAlgCat.baseChange (K := AlgebraicClosure k) H)) J)
    (hJtrivial : J = HopfIdeal.augmentation (AlgebraicClosure k)
      (FiniteTypeCommHopfAlgCat.baseChange (K := AlgebraicClosure k) H)) :
    semisimpleCommHopfAlgProperty k H := by
  rw [semisimpleCommHopfAlgProperty_iff_solvableRadicalDefiningIdeal_baseChange_eq_augmentation]
  refine ⟨hsmooth, hconnected, le_antisymm (HopfIdeal.le_augmentation _ _ _) ?_⟩
  exact hJtrivial ▸
    FiniteTypeCommHopfAlgCat.le_solvableRadicalDefiningIdeal_of_minimal_isBorelCandidate _ hJ

end

end TauCeti
