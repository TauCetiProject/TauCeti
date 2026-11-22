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
through `Functor.rightAdjoint` and `Adjunction.ofIsLeftAdjoint`.
`Adjunction.isCartesian_counit_app_right` identifies the underlying counit arrows as Cartesian.

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
    ((p.fiberToStructuredArrow d).obj a).right = fiberInclusion.obj a := (rfl)

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
  IsHomLift.of_fac p x.hom f.right a.property rfl (by
    rw [eqToHom_refl, comp_id]
    have hw := f.w.symm
    rw [fiberToStructuredArrow_obj_hom] at hw
    exact hw)

/-- Turn a lift of a base arrow into a morphism out of the strict fibre. -/
def fiberToStructuredArrowHomMk {a : Fiber p d} {x : StructuredArrow d p}
    (f : fiberInclusion.obj a ⟶ x.right) [hf : p.IsHomLift x.hom f] :
    (p.fiberToStructuredArrow d).obj a ⟶ x :=
  StructuredArrow.homMk f (by
    have h : p.map f = eqToHom a.property ≫ x.hom := by
      have hf' := IsHomLift.fac' p x.hom f
      rw [eqToHom_refl, comp_id] at hf'
      exact hf'
    calc
      _ = eqToHom a.property.symm ≫ (eqToHom a.property ≫ x.hom) :=
        congrArg (eqToHom a.property.symm ≫ ·) h
      _ = _ := by simp)

@[simp]
lemma fiberToStructuredArrowHomMk_right {a : Fiber p d} {x : StructuredArrow d p}
    (f : fiberInclusion.obj a ⟶ x.right) [hf : p.IsHomLift x.hom f] :
    (p.fiberToStructuredArrowHomMk f (hf := hf) :
      (p.fiberToStructuredArrow d).obj a ⟶ x).right = f := (rfl)

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
      have : p.IsHomLift x.hom s.hom.right := p.isHomLift_fiberToStructuredArrow_right s.hom
      let g := ((p.fiberToStructuredArrow d).map f.left).right
      have : p.IsHomLift (𝟙 d) g := f.left.property
      exact IsCartesian.map_uniq p x.hom t.hom.right s.hom.right g
        (congrArg CommaMorphism.right f.w))

/-- The underlying arrow of a universal arrow from the fibre is Cartesian. -/
lemma isCartesian_of_isTerminal (t : CostructuredArrow (p.fiberToStructuredArrow d) x)
    (ht : IsTerminal t) : p.IsCartesian x.hom t.hom.right where
  toIsHomLift := p.isHomLift_fiberToStructuredArrow_right t.hom
  universal_property {a} f hf := by
    have : p.IsHomLift x.hom f := hf
    let a' : Fiber p d := ⟨a, domain_eq p x.hom f⟩
    let s : CostructuredArrow (p.fiberToStructuredArrow d) x :=
      CostructuredArrow.mk
        (p.fiberToStructuredArrowHomMk (d := d) (x := x) (a := a') f (hf := hf))
    have hs : s.hom.right = f :=
      p.fiberToStructuredArrowHomMk_right (a := a') (x := x) f (hf := hf)
    refine ⟨fiberInclusion.map (ht.from s).left, ⟨(ht.from s).left.property, ?_⟩, ?_⟩
    · have hw := congrArg
        (fun k : (p.fiberToStructuredArrow d).obj s.left ⟶ x => k.right) (ht.from s).w
      rw [StructuredArrow.comp_right, fiberToStructuredArrow_map_right, hs] at hw
      exact hw
    · rintro g ⟨hg, hgf⟩
      let g' : s ⟶ t := CostructuredArrow.homMk ⟨g, hg⟩ (by
        apply StructuredArrow.hom_ext
        rw [StructuredArrow.comp_right, fiberToStructuredArrow_map_right, hs]
        exact hgf)
      exact congrArg (fun k => fiberInclusion.map k.left) (ht.hom_ext g' (ht.from s))

end CostructuredArrow

namespace Adjunction

variable {p : C ⥤ D} {d : D} {R : StructuredArrow d p ⥤ Functor.Fiber p d}

/-- The underlying arrow of the counit of a strict-fibre inclusion adjunction is a Cartesian
lift of the base arrow of the structured arrow. -/
lemma isCartesian_counit_app_right (adj : p.fiberToStructuredArrow d ⊣ R)
    (x : StructuredArrow d p) : p.IsCartesian x.hom (adj.counit.app x).right := by
  simpa only [CostructuredArrow.mk_hom_eq_self] using
    CostructuredArrow.isCartesian_of_isTerminal _ (mkTerminalOfRightAdjoint _ adj x)

end Adjunction

namespace Functor

variable (p : C ⥤ D) (d : D)

/-- For a prefibered functor, the comma category of arrows from the strict fibre to a structured
arrow has a terminal object. -/
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
    adj.isCartesian_counit_app_right x⟩

end Functor

end CategoryTheory
