/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Monoidal.SubquotientHull
public import TauCeti.Algebra.Coalgebra.Comodule.Finite.SubquotientHull
public import TauCeti.Algebra.AlgebraicGroup.Connected.HopfSubalgebra
public import TauCeti.AlgebraicGeometry.AffineGroupScheme.Connected

/-!
# The connectedness criterion in an equivalent tensor category

Suppose `C` is monoidally equivalent to the finite comodules of a commutative Hopf algebra `B`
over a field `K`. In characteristic zero, `Spec B` is connected exactly when every object of `C`
which is not a finite sum of tensor units has a finite-sum and subquotient hull that fails to be
closed under tensor products. Over a perfect field, the hull condition still implies
connectedness. Neither statement requires finite type or a tensor generator.

The geometric forms use the identity point of `Spec B`: the Hopf counit is a section of its
structure morphism. Thus ordinary connectedness here is already geometric connectedness.
A neutral reconstruction theorem can supply the monoidal equivalence; the criterion itself
needs neither a choice of fibre functor nor a separate notion of neutral Tannakian category.

## References

* P. Deligne and J. S. Milne, *Tannakian categories*, Corollary 2.22, with
  Propositions 2.20(a) and 2.21(a).
-/

public section

open CategoryTheory Limits MonoidalCategory

namespace TauCeti.Tannaka

universe v u w

variable (K : Type u) [Field K] (B : Type u) [CommRing B] [_root_.HopfAlgebra K B]
  {C : Type w} [Category.{v} C] [Preadditive C] [HasFiniteBiproducts C]
  [MonoidalCategory C]

/-- The absence of nontrivial finite tensor-closed hulls in an equivalent category means that
there are no nontrivial finite-dimensional Hopf subalgebras. This holds in every characteristic.
An object is nontrivial here precisely when it is not a finite sum of tensor units. -/
theorem forall_isHopfSubalgebra_eq_bot_iff_forall_not_tensorLE_subquotientHull
    (E : C ≌ FGComoduleCat.{u, u, u} K B) [E.functor.Monoidal] :
    (∀ A : Subalgebra K B, A.IsHopfSubalgebra → FiniteDimensional K A → A = ⊥) ↔
      ∀ X : C, ¬ IsSumOfUnits X →
        ¬ (subquotientHull X).TensorLE (subquotientHull X) (subquotientHull X) := by
  have h := E.exists_not_isSumOfUnits_tensorLE_subquotientHull_iff.trans
    (FGComoduleCat.exists_not_isSumOfUnits_tensorLE_subquotientHull_iff (K := K) (H := B))
  simpa only [not_exists, not_and, not_not] using (not_congr h).symm

/-- **Connectedness criterion in characteristic zero.** Under a monoidal equivalence with
finite comodules over `B`, its prime spectrum is connected exactly when every object outside
the finite sums of units has a hull that fails tensor closure. -/
theorem connectedSpace_primeSpectrum_iff_forall_not_tensorLE_subquotientHull [CharZero K]
    (E : C ≌ FGComoduleCat.{u, u, u} K B) [E.functor.Monoidal] :
    ConnectedSpace (PrimeSpectrum B) ↔
      ∀ X : C, ¬ IsSumOfUnits X →
        ¬ (subquotientHull X).TensorLE (subquotientHull X) (subquotientHull X) :=
  HopfAlgebra.connectedSpace_primeSpectrum_iff_forall_isHopfSubalgebra_eq_bot.trans
    (forall_isHopfSubalgebra_eq_bot_iff_forall_not_tensorLE_subquotientHull K B E)

/-- Over a perfect field, the categorical hull criterion implies connectedness. The reverse
implication can fail in positive characteristic, for example for `αₚ`. -/
theorem connectedSpace_primeSpectrum_of_forall_not_tensorLE_subquotientHull [PerfectField K]
    (E : C ≌ FGComoduleCat.{u, u, u} K B) [E.functor.Monoidal]
    (h : ∀ X : C, ¬ IsSumOfUnits X →
      ¬ (subquotientHull X).TensorLE (subquotientHull X) (subquotientHull X)) :
    ConnectedSpace (PrimeSpectrum B) :=
  HopfAlgebra.connectedSpace_primeSpectrum_of_forall_isHopfSubalgebra_eq_bot
    ((forall_isHopfSubalgebra_eq_bot_iff_forall_not_tensorLE_subquotientHull K B E).2 h)

/-- The characteristic-zero hull criterion in scheme-theoretic geometric form. -/
theorem geometricallyConnected_hopfSpec_iff_forall_not_tensorLE_subquotientHull [CharZero K]
    (E : C ≌ FGComoduleCat.{u, u, u} K B) [E.functor.Monoidal] :
    AlgebraicGeometry.GeometricallyConnected
        (((AlgebraicGeometry.hopfSpec (CommRingCat.of K)).obj
          (Opposite.op (CommHopfAlgCat.of K B))).X.hom) ↔
      ∀ X : C, ¬ IsSumOfUnits X →
        ¬ (subquotientHull X).TensorLE (subquotientHull X) (subquotientHull X) :=
  (geometricallyConnected_hopfSpec_iff_connectedSpace K (CommHopfAlgCat.of K B)).trans
    (connectedSpace_primeSpectrum_iff_forall_not_tensorLE_subquotientHull K B E)

/-- The characteristic-zero hull criterion for the coordinate-algebra predicate of geometric
connectedness. -/
theorem geometricallyConnectedCommHopfAlgProperty_iff_forall_not_tensorLE_subquotientHull
    [CharZero K]
    (E : C ≌ FGComoduleCat.{u, u, u} K B) [E.functor.Monoidal] :
    geometricallyConnectedCommHopfAlgProperty K (CommHopfAlgCat.of K B) ↔
      ∀ X : C, ¬ IsSumOfUnits X →
        ¬ (subquotientHull X).TensorLE (subquotientHull X) (subquotientHull X) :=
  (geometricallyConnectedCommHopfAlg_iff_geometricallyConnected_hopfSpec K
    (CommHopfAlgCat.of K B)).trans
      (geometricallyConnected_hopfSpec_iff_forall_not_tensorLE_subquotientHull K B E)

/-- Over a perfect field, the hull criterion gives geometric connectedness of the Hopf
spectrum, using its identity section. -/
theorem geometricallyConnected_hopfSpec_of_forall_not_tensorLE_subquotientHull [PerfectField K]
    (E : C ≌ FGComoduleCat.{u, u, u} K B) [E.functor.Monoidal]
    (h : ∀ X : C, ¬ IsSumOfUnits X →
      ¬ (subquotientHull X).TensorLE (subquotientHull X) (subquotientHull X)) :
    AlgebraicGeometry.GeometricallyConnected
      (((AlgebraicGeometry.hopfSpec (CommRingCat.of K)).obj
        (Opposite.op (CommHopfAlgCat.of K B))).X.hom) :=
  (geometricallyConnected_hopfSpec_iff_connectedSpace K (CommHopfAlgCat.of K B)).2
    (connectedSpace_primeSpectrum_of_forall_not_tensorLE_subquotientHull K B E h)

/-- Over a perfect field, the hull criterion gives the coordinate-algebra predicate of
geometric connectedness. -/
theorem geometricallyConnectedCommHopfAlgProperty_of_forall_not_tensorLE_subquotientHull
    [PerfectField K]
    (E : C ≌ FGComoduleCat.{u, u, u} K B) [E.functor.Monoidal]
    (h : ∀ X : C, ¬ IsSumOfUnits X →
      ¬ (subquotientHull X).TensorLE (subquotientHull X) (subquotientHull X)) :
    geometricallyConnectedCommHopfAlgProperty K (CommHopfAlgCat.of K B) :=
  (geometricallyConnectedCommHopfAlg_iff_geometricallyConnected_hopfSpec K
    (CommHopfAlgCat.of K B)).2
      (geometricallyConnected_hopfSpec_of_forall_not_tensorLE_subquotientHull K B E h)

end TauCeti.Tannaka
