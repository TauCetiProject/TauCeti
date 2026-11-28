/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Biproducts
public import Mathlib.Combinatorics.Quiver.ConnectedComponent
public import TauCeti.Algebra.Category.ModuleCat.Algebra
public import TauCeti.CategoryTheory.Preadditive.Radical.IrreducibleMorphismQuiver.Valued
import Mathlib.Algebra.Category.ModuleCat.Simple
import Mathlib.CategoryTheory.Preadditive.Schur
import Mathlib.RingTheory.Spectrum.Prime.Basic
import TauCeti.Algebra.Category.ModuleCat.Indecomposable
import TauCeti.Algebra.Category.ModuleCat.RepresentationFinite

/-!
# Weak components of the valued Auslander–Reiten quiver of a semisimple ring

Over a semisimple ring every indecomposable module is simple, and Schur's lemma leaves no
irreducible maps between simple modules. Thus every vertex of the valued quiver is its own weak
component. In particular, for the product of a field with itself there are two components,
corresponding to the simple modules of the two factors.

The description uses the definition of the valued Auslander–Reiten quiver in Auslander, Reiten
and Smalø, *Representation Theory of Artin Algebras*, Cambridge University Press (1995),
§VII.1, p. 225. The product example illustrates the indecomposability hypothesis in their
connectedness criterion, Theorem VII.2.1.
-/

public section

open CategoryTheory
open scoped ModuleCat.Algebra

namespace TauCeti.IrreducibleMorphismQuiver

universe u v w

variable {R : Type u} {A : Type v} [CommRing R] [Ring A] [Algebra R A] [IsSemisimpleRing A]

/-- The valued quiver of finitely generated modules over a semisimple ring has no arrows. -/
@[simp]
theorem valuationMatrix_eq_none_of_isSemisimpleRing
    (a b : IrreducibleMorphismQuiver R fun M : ModuleCat.{w} A ↦ Module.Finite A M) :
    valuationMatrix R (fun M : ModuleCat.{w} A ↦ Module.Finite A M) a b = none := by
  have hsimple (x : IrreducibleMorphismQuiver R fun M : ModuleCat.{w} A ↦ Module.Finite A M) :
      Simple x.representative :=
    (simple_iff_isSimpleModule' _).mpr
      ((indecomposable_iff_isIndecomposableModule _).mp x.representative_property.2).isSimpleModule
  have := hsimple a
  have := hsimple b
  have : Subsingleton (irreducibleMorphismSpace R a.representative b.representative) :=
    subsingleton_irreducibleMorphismSpace_iff.mpr fun _ hf ↦
      hf.not_isIso (isIso_of_hom_simple hf.ne_zero)
  rw [valuationMatrix_eq_none_iff, irreducibleMorphismValuation_fst,
    Module.finrank_zero_of_subsingleton]
  simp

variable (R A) in
/-- Each vertex of the valued quiver of a semisimple ring gives a distinct weak component,
and every weak component is of this form. -/
noncomputable def equivWeaklyConnectedComponentOfIsSemisimpleRing :
    (IrreducibleMorphismQuiver R fun M : ModuleCat.{w} A ↦ Module.Finite A M) ≃
      Quiver.WeaklyConnectedComponent
        (ValuedQuiver (valuationMatrix R fun M : ModuleCat.{w} A ↦ Module.Finite A M)) :=
  Equiv.ofBijective (fun a ↦ Quiver.WeaklyConnectedComponent.mk (ValuedQuiver.of a)) (by
    constructor
    · intro a b hab
      obtain ⟨p⟩ := (Quiver.WeaklyConnectedComponent.eq _ _).mp hab
      cases p with
      | nil => rfl
      | cons _ f =>
        rcases f with f | f
        all_goals simpa using ValuedQuiver.eq_some_valuation f
    · intro c
      obtain ⟨⟨a⟩, rfl⟩ := Quotient.exists_rep c
      exact ⟨a, rfl⟩)

/-- The component equivalence sends each vertex to the component of that vertex. -/
@[simp]
theorem equivWeaklyConnectedComponentOfIsSemisimpleRing_apply
    (a : IrreducibleMorphismQuiver R fun M : ModuleCat.{w} A ↦ Module.Finite A M) :
    equivWeaklyConnectedComponentOfIsSemisimpleRing R A a =
      Quiver.WeaklyConnectedComponent.mk (ValuedQuiver.of a) :=
  (rfl)

/-- The inverse component equivalence recovers the vertex from its component. -/
@[simp]
theorem equivWeaklyConnectedComponentOfIsSemisimpleRing_symm_mk
    (a : IrreducibleMorphismQuiver R fun M : ModuleCat.{w} A ↦ Module.Finite A M) :
    (equivWeaklyConnectedComponentOfIsSemisimpleRing R A).symm
      (Quiver.WeaklyConnectedComponent.mk (ValuedQuiver.of a)) = a :=
  (equivWeaklyConnectedComponentOfIsSemisimpleRing R A).symm_apply_apply a

/-- The valued Auslander–Reiten quiver of `k × k` has exactly two weak components. -/
theorem card_weaklyConnectedComponent_valuationMatrix_prod_field (k : Type u) [Field k] :
    Nat.card (Quiver.WeaklyConnectedComponent
      (ValuedQuiver (valuationMatrix k fun M : ModuleCat.{u} (k × k) ↦
        Module.Finite (k × k) M))) = 2 := by
  rw [← Nat.card_congr (equivWeaklyConnectedComponentOfIsSemisimpleRing k (k × k)),
    Nat.card_congr IrreducibleMorphismQuiver.equivSkeleton,
    card_skeleton_finite_indecomposable_eq_card_maximalSpectrum,
    ← Nat.card_congr (IsArtinianRing.primeSpectrumEquivMaximalSpectrum (R := k × k)),
    Nat.card_congr (PrimeSpectrum.primeSpectrumProd k k), Nat.card_sum, Nat.card_unique]

end TauCeti.IrreducibleMorphismQuiver
