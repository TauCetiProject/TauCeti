/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.ModuleCat.Biproducts
public import TauCeti.Algebra.Category.ModuleCat.Indecomposable
public import TauCeti.RingTheory.KrullSchmidt.DirectSum

/-!
# The Krull-Schmidt theorem for biproducts in `ModuleCat`

`TauCeti.exists_linearEquiv_directSum_isIndecomposableModule` and
`TauCeti.exists_equiv_linearEquiv_of_directSum` are the two halves of the Krull-Schmidt theorem in
their external module form: a module of finite length is a direct sum `⨁ i, N i` of indecomposable
modules, and any two such direct-sum decompositions are matched by a bijection of their index sets
under which corresponding summands are isomorphic. A client who works with representations meets
the theorem in its categorical form instead, with `CategoryTheory.Limits.biproduct` in place of
`DirectSum` and isomorphisms of objects in place of linear equivalences. This file restates both
halves in that form for `ModuleCat A`.

The transport is `TauCeti.biproductDirectSumEquiv`, which identifies the carrier of a finite
biproduct with the external direct sum of the carriers of the summands, together with
`TauCeti.indecomposable_iff_isIndecomposableModule`, which carries indecomposability across.

## Main results

* `TauCeti.exists_indecomposable_iso_biproduct`: **existence**, categorically: an Artinian object
  of `ModuleCat A` is isomorphic to a finite biproduct of indecomposable objects.
* `TauCeti.exists_equiv_iso_of_iso_biproduct`: **the Krull-Schmidt theorem**, categorically: two
  isomorphisms of an object of finite length with finite biproducts of indecomposable objects are
  matched by a bijection of the index sets under which corresponding summands are isomorphic.
* `TauCeti.exists_equiv_iso_of_biproduct_iso`: the same with no ambient object, for an isomorphism
  between two biproducts.
* `TauCeti.card_eq_card_of_iso_biproduct` and `TauCeti.eq_of_iso_biproduct_fin`: in particular the
  two decompositions have the same number of summands.
* `TauCeti.card_iso_eq_card_iso_of_iso_biproduct`: the number of summands isomorphic to a fixed
  object is the same in any two such decompositions, so the multiplicity of an indecomposable
  summand is an invariant.

## Implementation notes

The index types are taken in `Type`, the generality of Mathlib's `ModuleCat.biproductIsoPi`, while
the summands stay in the universe `v` of the ambient object; nothing is lost, because an index type
of a finite biproduct can be replaced by `Fin n`, which is what the existence theorem produces.

## References

See I. Assem, D. Simson, A. Skowroński, *Elements of the Representation Theory of Associative
Algebras, Vol. 1*, Section I.4.
-/

public section

namespace TauCeti

open CategoryTheory CategoryTheory.Limits DirectSum

universe u v

variable {A : Type u} [Ring A]

/-! ### The two halves of the Krull-Schmidt theorem, categorically -/

/-- **Existence of an indecomposable decomposition**, categorically: an Artinian object of
`ModuleCat A` — in particular one of finite length — is isomorphic to a finite biproduct of
indecomposable objects.

The index type is produced as `Fin n`, so the statement stays inside the index universe in which
`ModuleCat.biproductIsoPi`, and hence `TauCeti.biproductDirectSumEquiv`, is available. -/
theorem exists_indecomposable_iso_biproduct (X : ModuleCat.{v} A) [IsArtinian A X] :
    ∃ (n : ℕ) (P : Fin n → ModuleCat.{v} A),
      (∀ i, Indecomposable (P i)) ∧ Nonempty (X ≅ biproduct P) := by
  classical
  obtain ⟨s, hs, ⟨e⟩⟩ :=
    exists_linearEquiv_directSum_isIndecomposableModule (A := A) (M := (X : Type v))
  let h : (s : Type v) ≃ Fin s.card := s.equivFin
  refine ⟨s.card, fun i ↦ ModuleCat.of A ((h.symm i : Submodule A X) : Type v), fun i ↦ ?_, ⟨?_⟩⟩
  · rw [indecomposable_iff_isIndecomposableModule]
    exact hs _ (h.symm i).2
  · exact (e.trans ((DirectSum.lequivCongrLeft A h).trans
      (biproductDirectSumEquiv
        fun i ↦ ModuleCat.of A ((h.symm i : Submodule A X) : Type v)).symm)).toModuleIso

variable {ι κ : Type} [Finite ι] [Finite κ]
  {P : ι → ModuleCat.{v} A} {Q : κ → ModuleCat.{v} A}

/-- **The Krull-Schmidt theorem for biproducts in `ModuleCat A`.** If an object of finite length is
isomorphic to a finite biproduct of indecomposable objects in two ways, the two families of
summands are matched by a bijection of their index sets under which corresponding summands are
isomorphic.

`TauCeti.exists_indecomposable_iso_biproduct` supplies such an isomorphism, and
`TauCeti.exists_equiv_linearEquiv_of_directSum` is the same statement for external direct sums of
modules. -/
theorem exists_equiv_iso_of_iso_biproduct {X : ModuleCat.{v} A} [IsNoetherian A X] [IsArtinian A X]
    (eP : X ≅ biproduct P) (eQ : X ≅ biproduct Q)
    (hP : ∀ i, Indecomposable (P i)) (hQ : ∀ j, Indecomposable (Q j)) :
    ∃ e : ι ≃ κ, ∀ i, Nonempty (P i ≅ Q (e i)) := by
  let _ := Fintype.ofFinite ι
  let _ := Fintype.ofFinite κ
  obtain ⟨e, he⟩ := exists_equiv_linearEquiv_of_directSum
    (eP.toLinearEquiv.trans (biproductDirectSumEquiv P))
    (eQ.toLinearEquiv.trans (biproductDirectSumEquiv Q))
    (fun i ↦ (indecomposable_iff_isIndecomposableModule (P i)).mp (hP i))
    fun j ↦ (indecomposable_iff_isIndecomposableModule (Q j)).mp (hQ j)
  exact ⟨e, fun i ↦ ⟨(he i).some.toModuleIso⟩⟩

/-- **The Krull-Schmidt theorem with no ambient object**: an isomorphism between two finite
biproducts of indecomposable objects of finite length matches their summands by a bijection of the
index sets. -/
theorem exists_equiv_iso_of_biproduct_iso [IsNoetherian A (biproduct P : ModuleCat.{v} A)]
    [IsArtinian A (biproduct P : ModuleCat.{v} A)]
    (e : (biproduct P : ModuleCat.{v} A) ≅ biproduct Q)
    (hP : ∀ i, Indecomposable (P i)) (hQ : ∀ j, Indecomposable (Q j)) :
    ∃ f : ι ≃ κ, ∀ i, Nonempty (P i ≅ Q (f i)) :=
  exists_equiv_iso_of_iso_biproduct (Iso.refl _) e hP hQ

/-- Two decompositions of an object of finite length as a biproduct of indecomposable objects have
the same number of summands. -/
theorem card_eq_card_of_iso_biproduct {X : ModuleCat.{v} A} [IsNoetherian A X] [IsArtinian A X]
    (eP : X ≅ biproduct P) (eQ : X ≅ biproduct Q)
    (hP : ∀ i, Indecomposable (P i)) (hQ : ∀ j, Indecomposable (Q j)) :
    Nat.card ι = Nat.card κ :=
  let ⟨e, _⟩ := exists_equiv_iso_of_iso_biproduct eP eQ hP hQ
  Nat.card_eq_of_bijective e e.bijective

/-- **The multiplicity of an indecomposable summand is well defined**: the number of summands
isomorphic to a fixed object `N` is the same in any two indecomposable biproduct decompositions of
an object of finite length. This is what makes "the indecomposable summands of `X`, with
multiplicity" an invariant of `X`; `TauCeti.indecomposableMultiplicity` is the module-level
counterpart. -/
theorem card_iso_eq_card_iso_of_iso_biproduct {X : ModuleCat.{v} A} [IsNoetherian A X]
    [IsArtinian A X] (eP : X ≅ biproduct P) (eQ : X ≅ biproduct Q)
    (hP : ∀ i, Indecomposable (P i)) (hQ : ∀ j, Indecomposable (Q j)) (N : ModuleCat.{v} A) :
    Nat.card {i : ι // Nonempty (P i ≅ N)} = Nat.card {j : κ // Nonempty (Q j ≅ N)} := by
  obtain ⟨e, he⟩ := exists_equiv_iso_of_iso_biproduct eP eQ hP hQ
  exact Nat.card_congr (Equiv.subtypeEquiv e fun i ↦
    ⟨fun hf ↦ ⟨(he i).some.symm ≪≫ hf.some⟩, fun hf ↦ ⟨(he i).some ≪≫ hf.some⟩⟩)

/-- The number of summands of an indecomposable biproduct decomposition of an object of finite
length is well defined: two `Fin`-indexed decompositions have the same length. This is the form in
which `TauCeti.exists_indecomposable_iso_biproduct` produces its decompositions. -/
theorem eq_of_iso_biproduct_fin {X : ModuleCat.{v} A} [IsNoetherian A X] [IsArtinian A X]
    {m n : ℕ} {P : Fin m → ModuleCat.{v} A} {Q : Fin n → ModuleCat.{v} A}
    (eP : X ≅ biproduct P) (eQ : X ≅ biproduct Q)
    (hP : ∀ i, Indecomposable (P i)) (hQ : ∀ j, Indecomposable (Q j)) : m = n := by
  simpa using card_eq_card_of_iso_biproduct eP eQ hP hQ

end TauCeti
