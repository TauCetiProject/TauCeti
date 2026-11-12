/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Combinatorics.Quiver.Basic
public import Mathlib.Tactic.TypeStar

/-!
# Directed networks with finite bounds

This file defines the carrier shared by finite flow and circulation theory. A network records an
explicit family of arrow types and a lower and upper bound on every arrow. Keeping the arrow
family explicit allows several networks on the same vertex type without competing `Quiver`
instances.
-/

public section

universe u v w

namespace TauCeti

/-- An assignment gives a value to every arrow in an explicitly supplied arrow family. The
endpoints are strict-implicit so that applying an assignment to an arrow infers them from the
arrow. -/
abbrev Assignment (Hom : V → V → Type v) (K : Type w) := ∀ ⦃x y : V⦄, Hom x y → K

namespace Assignment

variable {Hom : V → V → Type v} {K L M : Type*}

/-- Assignment evaluation is invariant under transport of the arrow endpoints. -/
theorem apply_homOfEq (f : Assignment Hom K) {x y x' y' : V} (a : Hom x y) (hx : x = x')
    (hy : y = y') : f (@Quiver.homOfEq V ⟨Hom⟩ x y x' y' a hx hy) = f a := by
  subst x' y'
  rfl

/-- Change the coefficients of an assignment by applying `φ` to its value on every arrow.

This definition is exposed so that flows whose bounds are mapped in different but definitionally
equal ways, such as along `ψ ∘ φ` or along `φ` and then `ψ`, can be compared. -/
@[expose]
def map (f : Assignment Hom K) (φ : K → L) : Assignment Hom L :=
  fun _ _ e ↦ φ (f e)

@[simp]
theorem map_apply (f : Assignment Hom K) (φ : K → L) {x y : V} (e : Hom x y) :
    f.map φ e = φ (f e) :=
  (rfl)

@[simp]
theorem map_id (f : Assignment Hom K) : f.map id = f :=
  (rfl)

@[simp]
theorem map_map (f : Assignment Hom K) (φ : K → L) (ψ : L → M) :
    (f.map φ).map ψ = f.map (ψ ∘ φ) :=
  (rfl)

end Assignment

/-- A directed network with finite lower and upper bounds on every arrow.

The arrow types may contain parallel arrows, arrows in both directions, and loops. Finiteness is
imposed by individual theorems rather than by the network carrier.
-/
structure Network (K : Type w) (V : Type u) [LE K] where
  /-- The type of arrows from one vertex to another. -/
  Hom : V → V → Type v
  /-- The lower bound on each arrow. -/
  lower : Assignment Hom K
  /-- The upper bound on each arrow. -/
  upper : Assignment Hom K
  /-- Every lower bound is at most the corresponding upper bound. -/
  lower_le_upper : ∀ {x y} (e : Hom x y), lower e ≤ upper e

namespace Network

/-- Assignments on the arrow family of a network. -/
abbrev Assignment {K : Type w} {V : Type u} [LE K] (N : Network K V) (R : Type*) :=
  TauCeti.Assignment N.Hom R

/-- Construct an ordinary network with zero lower bounds from nonnegative capacities.

This is exposed so that its dependent arrow family reduces in the exported projection lemmas. -/
@[expose, reducible] def ofCapacity {K : Type w} {V : Type u} [Zero K] [LE K]
    (Hom : V → V → Type v)
    (capacity : TauCeti.Assignment Hom K)
    (hcapacity : ∀ {x y} (e : Hom x y), 0 ≤ capacity e) : Network K V where
  Hom := Hom
  lower := fun {_ _} _ => 0
  upper := capacity
  lower_le_upper := hcapacity

/-- The arrow family of an ordinary network is its supplied arrow family. -/
@[simp]
theorem ofCapacity_Hom {K : Type w} {V : Type u} [Zero K] [LE K]
    (Hom : V → V → Type v) (capacity : TauCeti.Assignment Hom K)
    (hcapacity : ∀ {x y} (e : Hom x y), 0 ≤ capacity e) :
    (ofCapacity Hom capacity hcapacity).Hom = Hom := rfl

@[simp]
theorem ofCapacity_lower {K : Type w} {V : Type u} [Zero K] [LE K]
    (Hom : V → V → Type v) (capacity : TauCeti.Assignment Hom K)
    (hcapacity : ∀ {x y} (e : Hom x y), 0 ≤ capacity e) {x y}
    (e : (ofCapacity Hom capacity hcapacity).Hom x y) :
    (ofCapacity Hom capacity hcapacity).lower e = 0 := rfl

@[simp]
theorem ofCapacity_upper {K : Type w} {V : Type u} [Zero K] [LE K]
    (Hom : V → V → Type v) (capacity : TauCeti.Assignment Hom K)
    (hcapacity : ∀ {x y} (e : Hom x y), 0 ≤ capacity e) {x y}
    (e : (ofCapacity Hom capacity hcapacity).Hom x y) :
    (ofCapacity Hom capacity hcapacity).upper e = capacity e := rfl

end Network

end TauCeti
