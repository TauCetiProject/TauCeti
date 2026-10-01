/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Quiver.Representation.FiniteDimensional
public import TauCeti.Algebra.Category.ModuleCat.KrullSchmidt
public import TauCeti.CategoryTheory.Preadditive.Equivalence

/-!
# The Krull-Schmidt theorem for quiver representations

A pointwise finite-dimensional representation of a finite quiver is a finite biproduct of
indecomposable representations, and the summands of two such decompositions are matched by a
bijection of their index sets under which corresponding summands are isomorphic. This is what makes
"the indecomposable summands of a representation, with multiplicity" an invariant of the
representation, and hence what makes "the indecomposable representations" of a quiver a well-defined
family to count.

The theorem is not proved again here. It is the Krull-Schmidt theorem for modules over the path
algebra, `TauCeti.exists_indecomposable_iso_biproduct` and
`TauCeti.exists_equiv_iso_of_iso_biproduct`, read through the dictionary
`TauCeti.quiverRepEquivalence : QuiverRep k Q ≌ ModuleCat (pathAlgebra k Q)`. Three properties of
that dictionary carry it across: both of its directions are additive, by
`CategoryTheory.Equivalence.functor_additive` and `CategoryTheory.Equivalence.inverse_additive`, so
they carry finite biproducts to finite biproducts; both are fully faithful, so they carry
indecomposable objects to indecomposable objects
(`CategoryTheory.Functor.indecomposable_obj_of_map_bijective`); and a
pointwise finite-dimensional representation of a finite quiver goes to a module that is
finite-dimensional over the base field
(`TauCeti.module_finite_quiverRepEquivalenceFunctorObj_of_isFinDim`), hence Artinian and Noetherian
over the path algebra, which is the finiteness hypothesis the module-level theorem asks for. The
path algebra itself need not be finite-dimensional: over the quiver with one vertex and one loop it
is `k[X]`, and a representation of that quiver is a finite-dimensional vector space with an
endomorphism, whose indecomposable summands are the cyclic modules `k[X] / (p ^ e)` with `p`
irreducible, the Jordan blocks of the endomorphism when `k` is algebraically closed. That
decomposition refines the primary decomposition of the module, whose `p`-primary component is the
sum of all the summands for that `p`.

## Main results

* `TauCeti.QuiverRep.exists_indecomposable_iso_biproduct`: **existence**, a pointwise
  finite-dimensional representation of a finite quiver is isomorphic to a finite biproduct of
  indecomposable representations, themselves pointwise finite-dimensional.
* `TauCeti.QuiverRep.exists_equiv_iso_of_iso_biproduct`: **the Krull-Schmidt theorem**, two
  decompositions of a pointwise finite-dimensional representation into indecomposable summands are
  matched by a bijection of the index sets under which corresponding summands are isomorphic, with
  `TauCeti.QuiverRep.exists_equiv_iso_of_biproduct_iso` the form with no ambient representation.
* `TauCeti.QuiverRep.card_eq_card_of_iso_biproduct` and
  `TauCeti.QuiverRep.eq_of_iso_biproduct_fin`: in particular the two decompositions have the same
  number of summands.
* `TauCeti.QuiverRep.card_iso_eq_card_iso_of_iso_biproduct`: the number of summands isomorphic to a
  fixed representation is the same in any two such decompositions, so the multiplicity of an
  indecomposable summand is an invariant.

## References

See I. Assem, D. Simson, A. Skowroński, *Elements of the Representation Theory of Associative
Algebras, Vol. 1*, Section I.4.
-/

public section

namespace TauCeti

namespace QuiverRep

open CategoryTheory CategoryTheory.Limits
-- the scoped instances of `Mathlib.Algebra.Category.ModuleCat.Algebra` that give an object of
-- `ModuleCat (pathAlgebra k Q)` its `k`-module structure, in which its finiteness is stated
open scoped ModuleCat

universe u v w t

variable {k : Type u} {Q : Type v} [Field k] [Quiver.{w} Q] [Finite Q]

/-- **Existence of an indecomposable decomposition of a quiver representation.** A pointwise
finite-dimensional representation of a finite quiver is a finite biproduct of indecomposable
representations, each of them again pointwise finite-dimensional.

The index type is `Fin n`, the shape `TauCeti.exists_indecomposable_iso_biproduct` produces the
decomposition of the corresponding path-algebra module in. -/
theorem exists_indecomposable_iso_biproduct (M : QuiverRep.{u, v, w, t} k Q)
    (hM : IsFinDim k Q M) :
    ∃ (n : ℕ) (P : Fin n → QuiverRep.{u, v, w, t} k Q),
      (∀ i, Indecomposable (P i)) ∧ (∀ i, IsFinDim k Q (P i)) ∧ Nonempty (M ≅ ⨁ P) := by
  set E := quiverRepEquivalence.{u, v, w, t} k Q
  have hfin : Module.Finite k (E.functor.obj M) :=
    module_finite_quiverRepEquivalenceFunctorObj_of_isFinDim k Q M hM
  have : IsArtinian (pathAlgebra k Q) (E.functor.obj M) := isArtinian_of_tower k inferInstance
  obtain ⟨n, P, hP, ⟨e⟩⟩ := _root_.TauCeti.exists_indecomposable_iso_biproduct (E.functor.obj M)
  set P' : Fin n → QuiverRep.{u, v, w, t} k Q := fun i => E.inverse.obj (P i)
  have eM : M ≅ ⨁ P' := E.unitIso.app M ≪≫ E.inverse.mapIso e ≪≫ E.inverse.mapBiproduct P
  have hbip : IsFinDim k Q (⨁ P') := hM.of_iso eM
  refine ⟨n, P', fun i => ?_, fun i => hbip.of_mono (biproduct.ι P' i), ⟨eM⟩⟩
  exact Functor.indecomposable_obj_of_map_bijective E.inverse (hP i)
    ⟨Functor.map_injective _, Functor.map_surjective _⟩

variable {ι κ : Type} [Finite ι] [Finite κ]
  {P : ι → QuiverRep.{u, v, w, t} k Q} {R : κ → QuiverRep.{u, v, w, t} k Q}

/-- **The Krull-Schmidt theorem for quiver representations.** If a pointwise finite-dimensional
representation of a finite quiver is isomorphic to a finite biproduct of indecomposable
representations in two ways, the two families of summands are matched by a bijection of their index
sets under which corresponding summands are isomorphic.

`TauCeti.QuiverRep.exists_indecomposable_iso_biproduct` supplies such an isomorphism. -/
theorem exists_equiv_iso_of_iso_biproduct {M : QuiverRep.{u, v, w, t} k Q} (hM : IsFinDim k Q M)
    (eP : M ≅ ⨁ P) (eR : M ≅ ⨁ R) (hP : ∀ i, Indecomposable (P i))
    (hR : ∀ j, Indecomposable (R j)) :
    ∃ e : ι ≃ κ, ∀ i, Nonempty (P i ≅ R (e i)) := by
  set E := quiverRepEquivalence.{u, v, w, t} k Q
  have hfin : Module.Finite k (E.functor.obj M) :=
    module_finite_quiverRepEquivalenceFunctorObj_of_isFinDim k Q M hM
  have : IsArtinian (pathAlgebra k Q) (E.functor.obj M) := isArtinian_of_tower k inferInstance
  have : IsNoetherian (pathAlgebra k Q) (E.functor.obj M) := isNoetherian_of_tower k inferInstance
  obtain ⟨e, he⟩ := _root_.TauCeti.exists_equiv_iso_of_iso_biproduct
    (E.functor.mapIso eP ≪≫ E.functor.mapBiproduct P)
    (E.functor.mapIso eR ≪≫ E.functor.mapBiproduct R)
    (fun i => Functor.indecomposable_obj_of_map_bijective E.functor (hP i)
      ⟨Functor.map_injective _, Functor.map_surjective _⟩)
    (fun j => Functor.indecomposable_obj_of_map_bijective E.functor (hR j)
      ⟨Functor.map_injective _, Functor.map_surjective _⟩)
  exact ⟨e, fun i => ⟨E.fullyFaithfulFunctor.preimageIso (he i).some⟩⟩

/-- **The Krull-Schmidt theorem with no ambient representation**: an isomorphism between two finite
biproducts of indecomposable, pointwise finite-dimensional representations matches their summands by
a bijection of the index sets. -/
theorem exists_equiv_iso_of_biproduct_iso (h : IsFinDim k Q (⨁ P))
    (e : (⨁ P : QuiverRep.{u, v, w, t} k Q) ≅ ⨁ R) (hP : ∀ i, Indecomposable (P i))
    (hR : ∀ j, Indecomposable (R j)) :
    ∃ f : ι ≃ κ, ∀ i, Nonempty (P i ≅ R (f i)) :=
  exists_equiv_iso_of_iso_biproduct h (Iso.refl _) e hP hR

/-- Two decompositions of a pointwise finite-dimensional representation as a biproduct of
indecomposable representations have the same number of summands. -/
theorem card_eq_card_of_iso_biproduct {M : QuiverRep.{u, v, w, t} k Q} (hM : IsFinDim k Q M)
    (eP : M ≅ ⨁ P) (eR : M ≅ ⨁ R) (hP : ∀ i, Indecomposable (P i))
    (hR : ∀ j, Indecomposable (R j)) : Nat.card ι = Nat.card κ :=
  let ⟨e, _⟩ := exists_equiv_iso_of_iso_biproduct hM eP eR hP hR
  Nat.card_eq_of_bijective e e.bijective

/-- **The multiplicity of an indecomposable summand of a quiver representation is well defined**:
the number of summands isomorphic to a fixed representation `N` is the same in any two
indecomposable biproduct decompositions of a pointwise finite-dimensional representation. -/
theorem card_iso_eq_card_iso_of_iso_biproduct {M : QuiverRep.{u, v, w, t} k Q}
    (hM : IsFinDim k Q M) (eP : M ≅ ⨁ P) (eR : M ≅ ⨁ R) (hP : ∀ i, Indecomposable (P i))
    (hR : ∀ j, Indecomposable (R j)) (N : QuiverRep.{u, v, w, t} k Q) :
    Nat.card {i : ι // Nonempty (P i ≅ N)} = Nat.card {j : κ // Nonempty (R j ≅ N)} := by
  obtain ⟨e, he⟩ := exists_equiv_iso_of_iso_biproduct hM eP eR hP hR
  exact Nat.card_congr (Equiv.subtypeEquiv e fun i =>
    ⟨fun hf => ⟨(he i).some.symm ≪≫ hf.some⟩, fun hf => ⟨(he i).some ≪≫ hf.some⟩⟩)

/-- The number of summands of an indecomposable biproduct decomposition of a pointwise
finite-dimensional representation is well defined: two `Fin`-indexed decompositions have the same
length. This is the form in which `TauCeti.QuiverRep.exists_indecomposable_iso_biproduct` produces
its decompositions. -/
theorem eq_of_iso_biproduct_fin {M : QuiverRep.{u, v, w, t} k Q} (hM : IsFinDim k Q M) {m n : ℕ}
    {P : Fin m → QuiverRep.{u, v, w, t} k Q} {R : Fin n → QuiverRep.{u, v, w, t} k Q}
    (eP : M ≅ ⨁ P) (eR : M ≅ ⨁ R) (hP : ∀ i, Indecomposable (P i))
    (hR : ∀ j, Indecomposable (R j)) : m = n := by
  simpa using card_eq_card_of_iso_biproduct hM eP eR hP hR

end QuiverRep

end TauCeti
