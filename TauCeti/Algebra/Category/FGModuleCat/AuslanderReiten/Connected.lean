/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Combinatorics.Quiver.ConnectedComponent
public import Mathlib.RingTheory.Length
public import TauCeti.Algebra.Category.FGModuleCat.Basic
public import TauCeti.Algebra.Category.ModuleCat.Algebra
public import TauCeti.Algebra.Category.ModuleCat.RepresentationFinite
public import TauCeti.CategoryTheory.Preadditive.Radical.IrreducibleMorphismQuiver.Valued
public import TauCeti.RingTheory.CentralIdempotent
import Mathlib.RingTheory.HopkinsLevitzki
import TauCeti.Algebra.Category.FGModuleCat.KrullSchmidt
import TauCeti.Algebra.Category.FGModuleCat.RepresentationFinite
import TauCeti.Algebra.Category.ModuleCat.AuslanderReiten.Component
import TauCeti.Combinatorics.Quiver.Reachable

/-!
# Weak components of the valued Auslander–Reiten quiver

A weakly connected component of the valued Auslander–Reiten quiver corresponds to a class of
indecomposable finitely generated modules closed under isomorphism and under irreducible maps in
both directions. Auslander's bounded-length theorem applied to that class shows that over a
connected Artin algebra any bounded-length component contains every vertex, and the algebra is
representation-finite. In particular the valued quiver of a connected representation-finite Artin
algebra is weakly connected.

## References

* M. Auslander, I. Reiten, S. O. Smalø, *Representation Theory of Artin Algebras*,
  Cambridge University Press (1995), Theorems VI.1.4 and VII.2.1.
-/

public section

namespace FGModuleCat

open CategoryTheory TauCeti
open Quiver (WeaklyConnectedComponent)
open Quiver.WeaklyConnectedComponent (mk)
open scoped ModuleCat.Algebra

universe u v w

variable (R : Type u) (A : Type v) [CommRing R] [Ring A] [Algebra R A]

/-- The underlying valued quiver of finitely generated indecomposable modules. For an Artin algebra,
there is an arrow between two classes exactly when they admit an irreducible map. -/
abbrev ValuedARQuiver :=
  ValuedQuiver (IrreducibleMorphismQuiver.valuationMatrix R
    (⊤ : ObjectProperty (FGModuleCat.{w} A)))

namespace ValuedARQuiver

variable {A}

/-- The vertex represented by an indecomposable finitely generated module. -/
def of {X : FGModuleCat.{w} A} (hX : Indecomposable X) : ValuedARQuiver R A :=
  ValuedQuiver.of (IrreducibleMorphismQuiver.of R (P := ⊤) trivial hX)

/-- Two indecomposable modules give the same vertex exactly when they are isomorphic. -/
@[simp]
theorem of_eq_of_iff {X Y : FGModuleCat.{w} A} (hX : Indecomposable X) (hY : Indecomposable Y) :
    of R hX = of R hY ↔ Nonempty (X ≅ Y) := by
  rw [of, of, ValuedQuiver.of.injEq, IrreducibleMorphismQuiver.of_eq_of_iff]

/-- The chosen representative of the vertex of a module is isomorphic to that module. -/
noncomputable def representativeIso {X : FGModuleCat.{w} A} (hX : Indecomposable X) :
    (of R hX).vertex.representative ≅ X :=
  IrreducibleMorphismQuiver.representativeIso R (P := ⊤) trivial hX

/-- Taking the vertex of a chosen representative recovers the original vertex. -/
@[simp]
theorem of_representative (x : ValuedARQuiver.{u, v, w} R A) :
    of R x.vertex.representative_property.2 = x := by
  cases x
  exact congrArg ValuedQuiver.of (IrreducibleMorphismQuiver.of_representative _)

variable {R} [IsArtinianRing R] [Module.Finite R A]

/-- An arrow between the classes of two indecomposable modules exists exactly when there is an
irreducible morphism between the modules. -/
theorem nonempty_hom_of_iff {X Y : FGModuleCat.{w} A}
    (hX : Indecomposable X) (hY : Indecomposable Y) :
    Nonempty (of R hX ⟶ of R hY) ↔ ∃ f : X ⟶ Y, IsIrreducibleMorphism f := by
  have : IsArtinianRing A := IsArtinianRing.of_finite R A
  rw [ValuedQuiver.nonempty_hom_iff]
  let eX := representativeIso R hX
  let eY := representativeIso R hY
  have := isLocalRing_end_of_indecomposable ((indecomposable_obj_iff _).mpr
    (hX.of_iso eX.symm))
  have := isLocalRing_end_of_indecomposable ((indecomposable_obj_iff _).mpr
    (hY.of_iso eY.symm))
  rw [IrreducibleMorphismQuiver.isSome_valuationMatrix_iff]
  exact ⟨fun ⟨f, hf⟩ ↦ ⟨_, (hf.iso_comp eX.inv).comp_iso eY.hom⟩,
    fun ⟨f, hf⟩ ↦ ⟨_, (hf.iso_comp eX.hom).comp_iso eY.inv⟩⟩

end ValuedARQuiver

variable {A} [IsArtinianRing R] [Module.Finite R A] [Small.{w} A]

/-- **Auslander's bounded-component theorem.** If one weak component of a connected Artin
algebra's valued Auslander–Reiten quiver has a uniform bound on the lengths of its modules,
then every vertex belongs to that component and the algebra is representation-finite. -/
theorem forall_weaklyConnectedComponent_eq_and_isRepresentationFinite_of_length_le
    (hA : centralIdempotents A ⊆ {0, 1})
    (c : WeaklyConnectedComponent (ValuedARQuiver.{u, v, w} R A))
    (b : ℕ) (hb : ∀ v : ValuedARQuiver.{u, v, w} R A, mk v = c →
      Module.length A v.vertex.representative.obj ≤ b) :
    (∀ v : ValuedARQuiver.{u, v, w} R A, mk v = c) ∧ IsRepresentationFinite.{w} A := by
  let S : ObjectProperty (FGModuleCat.{w} A) :=
    fun X ↦ ∃ hX : Indecomposable X, mk (ValuedARQuiver.of R hX) = c
  have hSiso : S.IsClosedUnderIsomorphisms := ⟨fun e ⟨hX, hc⟩ ↦ by
    have hY := hX.of_iso e
    have he := (ValuedARQuiver.of_eq_of_iff R hX hY).mpr ⟨e⟩
    exact ⟨hY, (congrArg mk he).symm.trans hc⟩⟩
  have hne : ∃ X, S X := by
    induction c using Quotient.ind' with
    | h v =>
      exact ⟨v.vertex.representative, _, congrArg mk (ValuedARQuiver.of_representative R v)⟩
  have hclosed {X Y : FGModuleCat.{w} A} (f : X ⟶ Y) (hf : IsIrreducibleMorphism f)
      (hX : Indecomposable X.obj) (hY : Indecomposable Y.obj) : S X ↔ S Y := by
    have hX' := (indecomposable_obj_iff X).mp hX
    have hY' := (indecomposable_obj_iff Y).mp hY
    obtain ⟨e⟩ := (ValuedARQuiver.nonempty_hom_of_iff (R := R) hX' hY').mpr ⟨f, hf⟩
    have he := TauCeti.Quiver.weaklyConnectedComponent_mk_eq_of_hom e
    exact ⟨fun ⟨_, h⟩ ↦ ⟨hY', he.symm.trans h⟩, fun ⟨_, h⟩ ↦ ⟨hX', he.trans h⟩⟩
  have hlength (X : FGModuleCat.{w} A) (h : S X) : Module.length A X.obj ≤ b := by
    obtain ⟨hX, hc⟩ := h
    let e := ValuedARQuiver.representativeIso R hX
    exact (isoToLinearEquiv e).length_eq ▸ hb (ValuedARQuiver.of R hX) hc
  obtain ⟨hall, hfinite⟩ := forall_prop_and_isRepresentationFinite_of_length_le R hA S
    (fun X ⟨hX, _⟩ ↦ (indecomposable_obj_iff X).mpr hX) hclosed hne b hlength
  refine ⟨fun v ↦ ?_, hfinite⟩
  obtain ⟨_, hv⟩ := hall v.vertex.representative
    ((indecomposable_obj_iff _).mpr v.vertex.representative_property.2)
  simpa only [ValuedARQuiver.of_representative] using hv

/-- The valued Auslander–Reiten quiver of a connected representation-finite Artin algebra is
weakly connected. This is expressed by saying its type of weak components is a subsingleton,
which also covers the zero algebra. -/
theorem subsingleton_weaklyConnectedComponent_valuedARQuiver
    (hA : centralIdempotents A ⊆ {0, 1}) (h : IsRepresentationFinite.{w} A) :
    Subsingleton (WeaklyConnectedComponent (ValuedARQuiver.{u, v, w} R A)) := by
  have : IsArtinianRing A := IsArtinianRing.of_finite R A
  obtain ⟨b, hb⟩ := h.exists_length_le
  refine ⟨fun c d ↦ ?_⟩
  induction d using Quotient.ind' with
  | h v =>
    exact ((forall_weaklyConnectedComponent_eq_and_isRepresentationFinite_of_length_le R hA c b
      (fun x _ ↦ hb _ inferInstance ((indecomposable_obj_iff _).mpr
        x.vertex.representative_property.2))).1 v).symm

end FGModuleCat
