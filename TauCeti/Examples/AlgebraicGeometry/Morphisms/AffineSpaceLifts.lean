/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.AffineSpace
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.Algebra.Torsor.Defs

/-!
# Lifts into affine space form a torsor

Let `i : T ⟶ T'` be a morphism of schemes over `S` (via `g : T' ⟶ S`) and `a : T ⟶ 𝔸(n; S)` an
`S`-morphism. An `S`-morphism `T' ⟶ 𝔸(n; S)` is the same as `n` global sections of `T'`, so the
lifts `b : T' ⟶ 𝔸(n; S)` of `a` along `i` are the tuples of global sections of `T'` restricting to
the coordinates of `a`. Two lifts differ by a tuple of sections in the kernel of
`Γ(T', ⊤) → Γ(T, ⊤)`, and adding such a tuple to a lift gives a lift.

* `TauCeti.AffineSpaceLifts.Lifts i g a`: the lifts of `a` along `i` over `S`.
* `TauCeti.AffineSpaceLifts.instAddTorsorLifts`: when a lift exists, the lifts form a torsor under
  `n → ker (Γ(T', ⊤) → Γ(T, ⊤))`.
* `TauCeti.AffineSpaceLifts.nonempty_lifts`: a lift exists when `i` is a closed immersion, `T'`
  is affine and `a` lies over `i ≫ g`.

For `T'` affine, `AlgebraicGeometry.Scheme.Hom.ker_appTop_eq_ideal_ker` (in
`TauCeti.AlgebraicGeometry.IdealSheaf.OfIdealTop`) identifies the kernel with `Γ(T', I)` for the
ideal sheaf `I = i.ker`. So for `n` a singleton and `T'` affine, the lifts of `T ⟶ 𝔸¹_S` along a
closed immersion `T ⟶ T'` form a torsor under `Γ(T', I)`.
-/

public noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace TauCeti.AffineSpaceLifts

variable {n : Type u} {S T T' : Scheme.{u}} (i : T ⟶ T') (g : T' ⟶ S) (a : T ⟶ 𝔸(n; S))

/-- The lifts of `a : T ⟶ 𝔸(n; S)` along `i : T ⟶ T'`, over `g : T' ⟶ S`. -/
structure Lifts : Type u where
  /-- The lifted morphism. -/
  hom : T' ⟶ 𝔸(n; S)
  /-- The lift lies over `g`. -/
  over : hom ≫ 𝔸(n; S) ↘ S = g
  /-- The lift restricts to `a` along `i`. -/
  comp_eq : i ≫ hom = a

variable {i g a}

namespace Lifts

/-- The coordinates of a lift. -/
def coords (b : Lifts i g a) (j : n) : Γ(T', ⊤) := b.hom.appTop (AffineSpace.coord S j)

/-- The coordinates of a lift are the pullbacks of the coordinates of `𝔸(n; S)`. -/
@[simp]
theorem hom_appTop_coord (b : Lifts i g a) (j : n) :
    b.hom.appTop (AffineSpace.coord S j) = b.coords j :=
  (rfl)

/-- The coordinates of a lift restrict to the coordinates of `a`. -/
@[simp]
theorem appTop_coords (b : Lifts i g a) (j : n) :
    i.appTop (b.coords j) = a.appTop (AffineSpace.coord S j) := by
  rw [← hom_appTop_coord, ← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, b.comp_eq]

/-- `a` lies over `i ≫ g` as soon as a lift exists. -/
theorem comp_over (b : Lifts i g a) : a ≫ 𝔸(n; S) ↘ S = i ≫ g := by
  rw [← b.comp_eq, Category.assoc, b.over]

/-- A lift is determined by its coordinates. -/
@[ext]
theorem ext {b b' : Lifts i g a} (h : ∀ j, b.coords j = b'.coords j) : b = b' :=
  match b, b', AffineSpace.hom_ext (by rw [b.over, b'.over]) h with
  | ⟨_, _, _⟩, ⟨_, _, _⟩, rfl => rfl

/-- The lift with given coordinates, provided they restrict to those of `a` and `a` lies over
`i ≫ g`. -/
def mk' (v : n → Γ(T', ⊤)) (hv : ∀ j, i.appTop (v j) = a.appTop (AffineSpace.coord S j))
    (ha : a ≫ 𝔸(n; S) ↘ S = i ≫ g) : Lifts i g a :=
  ⟨AffineSpace.homOfVector g v, AffineSpace.homOfVector_over g v, by
    rw [AffineSpace.comp_homOfVector]
    exact AffineSpace.hom_ext (by simp [ha]) fun j ↦ by simp [hv]⟩

@[simp]
theorem hom_mk' (v : n → Γ(T', ⊤))
    (hv : ∀ j, i.appTop (v j) = a.appTop (AffineSpace.coord S j))
    (ha : a ≫ 𝔸(n; S) ↘ S = i ≫ g) : (mk' v hv ha).hom = AffineSpace.homOfVector g v :=
  (rfl)

@[simp]
theorem coords_mk' (v : n → Γ(T', ⊤))
    (hv : ∀ j, i.appTop (v j) = a.appTop (AffineSpace.coord S j))
    (ha : a ≫ 𝔸(n; S) ↘ S = i ≫ g) (j : n) : (mk' v hv ha).coords j = v j := by
  rw [← hom_appTop_coord, hom_mk', AffineSpace.homOfVector_appTop_coord]

end Lifts

/-- Translating a lift by a tuple of sections of the kernel. -/
instance instVAddLifts : VAdd (n → RingHom.ker i.appTop.hom) (Lifts i g a) where
  vadd k b := Lifts.mk' (fun j ↦ b.coords j + k j)
    (fun j ↦ by simp [RingHom.mem_ker.mp (k j).property]) b.comp_over

@[simp]
theorem Lifts.coords_vadd (k : n → RingHom.ker i.appTop.hom) (b : Lifts i g a) (j : n) :
    (k +ᵥ b).coords j = b.coords j + k j :=
  Lifts.coords_mk' _ _ _ j

/-- The difference of two lifts, a tuple of sections of the kernel. -/
instance instVSubLifts : VSub (n → RingHom.ker i.appTop.hom) (Lifts i g a) where
  vsub b b' j := ⟨b.coords j - b'.coords j, by simp⟩

@[simp]
theorem Lifts.coe_vsub_apply (b b' : Lifts i g a) (j : n) :
    ((b -ᵥ b') j : Γ(T', ⊤)) = b.coords j - b'.coords j :=
  (rfl)

/-- **The lifts form a torsor.** When `a` has a lift along `i`, its lifts form a torsor under
`n → ker (Γ(T', ⊤) → Γ(T, ⊤))`. -/
instance instAddTorsorLifts [Nonempty (Lifts i g a)] :
    AddTorsor (n → RingHom.ker i.appTop.hom) (Lifts i g a) where
  zero_vadd b := Lifts.ext fun j ↦ by simp
  add_vadd k k' b := Lifts.ext fun j ↦ by simp [add_comm, add_left_comm]
  vsub_vadd' b b' := Lifts.ext fun j ↦ by simp
  vadd_vsub' k b := funext fun j ↦ Subtype.ext (by simp)

/-- **Existence of lifts.** If `i` is a closed immersion, `T'` is affine and `a` lies over
`i ≫ g`, then `a` lifts along `i`: the restriction `Γ(T', ⊤) → Γ(T, ⊤)` is surjective. -/
theorem nonempty_lifts [IsAffine T'] [IsClosedImmersion i] (ha : a ≫ 𝔸(n; S) ↘ S = i ≫ g) :
    Nonempty (Lifts i g a) := by
  have hsurj := (IsClosedImmersion.isAffine_surjective_of_isAffine i).2
  choose v hv using fun j ↦ hsurj (a.appTop (AffineSpace.coord S j))
  exact ⟨Lifts.mk' v hv ha⟩

end TauCeti.AffineSpaceLifts
