/-
Copyright (c) 2026 Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: pi
-/
module

public import Mathlib.CategoryTheory.Adjunction.Comma
public import Mathlib.CategoryTheory.FiberedCategory.Fiber
public import Mathlib.CategoryTheory.FiberedCategory.Fibered

/-!
# Fibres and comma categories of a prefibered functor

The strict fibre of `p : C ⥤ D` over `d` embeds fully faithfully into `d ↓ p`.
Cartesian lifts of arrows with source `d` are precisely the universal arrows from
this inclusion. Consequently, `p` is prefibered if and only if all these inclusions
have right adjoints. No closure of Cartesian arrows under composition is needed.

This identifies the fibre-to-comma adjunction used to compare strict fibres with
comma categories in Quillen's theorems. The adjoint and adjunction are available
through `Functor.rightAdjoint` and `Adjunction.ofIsLeftAdjoint`; their counit arrows
are Cartesian by `CostructuredArrow.isCartesian_of_isTerminal` and
`mkTerminalOfRightAdjoint`.

## References

* D. Quillen, *Higher algebraic K-theory: I*, §1, p. 93.
* C. Weibel, *The K-book*, IV.3.7.3.
* A. Grothendieck and M. Raynaud, *SGA 1*, VI.6.1.
-/

public section

universe v₁ v₂ u₁ u₂

namespace CategoryTheory

open Category Limits CategoryTheory.IsHomLift

variable {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]

namespace Functor

open Fiber

variable (p : C ⥤ D) (d : D)

/-- The strict fibre includes in the comma category by the identity base arrow.
The object computation is exposed to retain the original endpoints in morphism types. -/
@[expose]
def fiberToStructuredArrow : Fiber p d ⥤ StructuredArrow d p :=
  (fiberInclusion : Fiber p d ⥤ C).toStructuredArrow d p
    (fun a => eqToHom a.property.symm) (fun {a b} f => by
      calc
        _ = eqToHom a.property.symm ≫
            (eqToHom a.property ≫ 𝟙 d ≫ eqToHom b.property.symm) :=
          congrArg (eqToHom a.property.symm ≫ ·)
            (IsHomLift.fac' p (𝟙 d) (fiberInclusion.map f))
        _ = _ := by simp [fiberInclusion])

@[simp]
lemma fiberToStructuredArrow_obj_right (a : Fiber p d) :
    ((p.fiberToStructuredArrow d).obj a).right = a.val := (rfl)

@[simp]
lemma fiberToStructuredArrow_obj_hom (a : Fiber p d) :
    ((p.fiberToStructuredArrow d).obj a).hom = eqToHom a.property.symm := (rfl)

@[simp]
lemma fiberToStructuredArrow_map_right {a b : Fiber p d} (f : a ⟶ b) :
    ((p.fiberToStructuredArrow d).map f).right = fiberInclusion.map f := (rfl)

/-- Forgetting the base arrow recovers the strict-fibre inclusion. -/
@[simp]
lemma fiberToStructuredArrow_comp_proj :
    p.fiberToStructuredArrow d ⋙ StructuredArrow.proj d p = fiberInclusion := (rfl)

instance : (p.fiberToStructuredArrow d).Faithful where
  map_injective h := Fiber.hom_ext (congrArg CommaMorphism.right h)

variable {d}

/-- A comma morphism out of the strict fibre lifts its target's base arrow. -/
lemma isHomLift_fiberToStructuredArrow_right {a : Fiber p d} {x : StructuredArrow d p}
    (f : (p.fiberToStructuredArrow d).obj a ⟶ x) : p.IsHomLift x.hom f.right :=
  IsHomLift.of_commsq p x.hom f.right a.property rfl (by
    have hw : eqToHom a.property.symm ≫ p.map f.right = x.hom := f.w
    calc
      _ = eqToHom a.property ≫ (eqToHom a.property.symm ≫ p.map f.right) := by
        simp [fiberToStructuredArrow, Functor.toStructuredArrow, fiberInclusion]
      _ = _ := congrArg (eqToHom a.property ≫ ·) hw)

/-- Turn a lift of a base arrow into a morphism out of the strict fibre. -/
def fiberToStructuredArrowHomMk {a : Fiber p d} {x : StructuredArrow d p}
    (f : a.val ⟶ x.right) [hf : p.IsHomLift x.hom f] :
    (p.fiberToStructuredArrow d).obj a ⟶ x :=
  StructuredArrow.homMk f (by
    have h : p.map f = eqToHom a.property ≫ x.hom := by
      simpa using (IsHomLift.fac' p x.hom f)
    calc
      _ = eqToHom a.property.symm ≫ (eqToHom a.property ≫ x.hom) :=
        congrArg (eqToHom a.property.symm ≫ ·) h
      _ = _ := by simp)

@[simp]
lemma fiberToStructuredArrowHomMk_right {a : Fiber p d} {x : StructuredArrow d p}
    (f : a.val ⟶ x.right) [p.IsHomLift x.hom f] :
    (p.fiberToStructuredArrowHomMk f : (p.fiberToStructuredArrow d).obj a ⟶ x).right = f := (rfl)

instance : (p.fiberToStructuredArrow d).Full where
  map_surjective {a b} f := by
    have : p.IsHomLift (eqToHom b.property.symm) f.right :=
      p.isHomLift_fiberToStructuredArrow_right f
    have hf : p.IsHomLift (𝟙 d) f.right := by
      have : p.IsHomLift
          (eqToHom b.property.symm ≫ eqToHom b.property) f.right :=
        IsHomLift.lift_comp_eqToHom p _ f.right b.property
      simpa using this
    exact ⟨⟨f.right, hf⟩, StructuredArrow.hom_ext _ _ rfl⟩

end Functor

namespace CostructuredArrow

open CategoryTheory.Functor CategoryTheory.Functor.Fiber

variable {p : C ⥤ D} {d : D} {x : StructuredArrow d p}

/-- A Cartesian lift is a universal arrow from the strict-fibre inclusion. -/
noncomputable def isTerminalOfIsCartesian
    (t : CostructuredArrow (p.fiberToStructuredArrow d) x)
    [hcart : p.IsCartesian x.hom t.hom.right] : IsTerminal t :=
  IsTerminal.ofUniqueHom
    (fun s => by
      have : p.IsHomLift x.hom s.hom.right := p.isHomLift_fiberToStructuredArrow_right s.hom
      let g := IsCartesian.map p x.hom t.hom.right s.hom.right
      have hg := IsCartesian.map_isHomLift p x.hom t.hom.right s.hom.right
      exact CostructuredArrow.homMk ⟨g, hg⟩
        (by apply StructuredArrow.hom_ext; exact IsCartesian.fac p x.hom t.hom.right s.hom.right))
    (fun s f => by
      apply CostructuredArrow.hom_ext
      apply Fiber.hom_ext
      -- Supply the verticality proof explicitly across the strict-fibre subtype.
      exact @IsCartesian.map_uniq D C _ _ p d _ _ _ x.hom t.hom.right hcart
        _ s.hom.right (p.isHomLift_fiberToStructuredArrow_right s.hom) _ f.left.property
        (congrArg CommaMorphism.right f.w))

/-- The underlying arrow of a universal arrow from the fibre is Cartesian. -/
lemma isCartesian_of_isTerminal (t : CostructuredArrow (p.fiberToStructuredArrow d) x)
    (ht : IsTerminal t) : p.IsCartesian x.hom t.hom.right where
  toIsHomLift := p.isHomLift_fiberToStructuredArrow_right t.hom
  universal_property {a} f hf := by
    have : p.IsHomLift x.hom f := hf
    let a' : Fiber p d := Fiber.mk (domain_eq p x.hom f)
    let s : CostructuredArrow (p.fiberToStructuredArrow d) x :=
      CostructuredArrow.mk
        (p.fiberToStructuredArrowHomMk (d := d) (x := x) (a := a') f (hf := hf))
    refine ⟨fiberInclusion.map (ht.from s).left, ⟨(ht.from s).left.property, ?_⟩, ?_⟩
    · have h := congrArg CommaMorphism.right (ht.from s).w
      dsimp [s, fiberToStructuredArrow, Functor.toStructuredArrow,
        fiberToStructuredArrowHomMk, StructuredArrow.homMk] at h
      exact h
    · rintro g ⟨hg, hgf⟩
      let g' : s ⟶ t := CostructuredArrow.homMk ⟨g, hg⟩ (by
        apply StructuredArrow.hom_ext
        dsimp [s, fiberToStructuredArrow, Functor.toStructuredArrow,
          fiberToStructuredArrowHomMk, StructuredArrow.homMk]
        exact hgf)
      exact congrArg (fun k => fiberInclusion.map k.left) (ht.hom_ext g' (ht.from s))

end CostructuredArrow

namespace Functor

variable (p : C ⥤ D) (d : D)

/-- The comma category of arrows from the strict fibre to a given base arrow
has a terminal object, supplied by a Cartesian lift. -/
instance hasTerminal_costructuredArrow_fiberToStructuredArrow [p.IsPreFibered]
    (x : StructuredArrow d p) :
    HasTerminal (CostructuredArrow (p.fiberToStructuredArrow d) x) := by
  let a : Fiber p d :=
    Fiber.mk (IsPreFibered.pullbackObj_proj (p := p) (a := x.right) rfl x.hom)
  let φ := IsPreFibered.pullbackMap (p := p) (a := x.right) rfl x.hom
  have hφ := IsPreFibered.pullbackMap.IsCartesian (p := p) (a := x.right) rfl x.hom
  let t : CostructuredArrow (p.fiberToStructuredArrow d) x :=
    CostructuredArrow.mk
      (p.fiberToStructuredArrowHomMk (d := d) (x := x) (a := a) φ (hf := hφ.toIsHomLift))
  exact (t.isTerminalOfIsCartesian (hcart := hφ)).hasTerminal

/-- The strict-fibre inclusion into the comma category has a right adjoint for
any prefibered functor. -/
instance [p.IsPreFibered] : (p.fiberToStructuredArrow d).IsLeftAdjoint :=
  isLeftAdjoint_of_costructuredArrowTerminals _

/-- Quillen's comma-adjunction condition is equivalent to the existence of
Cartesian lifts in the sense of SGA 1. -/
theorem isPreFibered_iff_isLeftAdjoint_fiberToStructuredArrow :
    p.IsPreFibered ↔ ∀ d, (p.fiberToStructuredArrow d).IsLeftAdjoint := by
  refine ⟨fun _ _ => inferInstance, fun h => ?_⟩
  constructor
  intro a d f
  have := h d
  let adj := Adjunction.ofIsLeftAdjoint (p.fiberToStructuredArrow d)
  let x : StructuredArrow d p := StructuredArrow.mk f
  exact ⟨((p.fiberToStructuredArrow d).rightAdjoint.obj x).val, (adj.counit.app x).right,
    CostructuredArrow.isCartesian_of_isTerminal _ (mkTerminalOfRightAdjoint _ adj x)⟩

end Functor

end CategoryTheory
