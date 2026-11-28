/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.CommAlgCat.Basic
public import Mathlib.CategoryTheory.Category.Preorder
public import Mathlib.CategoryTheory.Limits.IsLimit
public import Mathlib.Algebra.Colimit.DirectLimit

/-!
# Directed limits in the category of commutative algebras

`CommAlgCat.directLimitIsColimit` equips the algebra `DirectLimit B f` with the
categorical colimit property, using the universal maps of `DirectLimit.Algebra`.
-/

public section

open CategoryTheory Limits

namespace CommAlgCat

universe v w

variable {R : Type*} {ι : Type v} [CommRing R] [Preorder ι]
  (B : ι → Type (max v w)) [∀ i, CommRing (B i)]
  [∀ i, Algebra R (B i)] (f : ∀ i j, i ≤ j → B i →ₐ[R] B j) [DirectedSystem B (f · · ·)]

/-- The diagram in `CommAlgCat R` associated to a directed system of commutative algebras. -/
abbrev directLimitDiagram : ι ⥤ CommAlgCat R where
  obj i := .of R (B i)
  map h := ofHom (f _ _ h.le)
  map_id _ := hom_ext (AlgHom.ext fun x ↦ DirectedSystem.map_self' f x)
  map_comp h k := hom_ext (AlgHom.ext fun x ↦ (DirectedSystem.map_map' f h.le k.le x).symm)

/-- Each object of the directed diagram is the corresponding stage algebra. -/
@[simp]
theorem directLimitDiagram_obj (i : ι) :
    (directLimitDiagram B f).obj i = .of R (B i) := (rfl)

variable [IsDirectedOrder ι] [Nonempty ι]

/-- The cocone with vertex the direct limit and legs the canonical algebra maps. -/
noncomputable abbrev directLimitCocone : Cocone (directLimitDiagram B f) where
  pt := .of R (DirectLimit B f)
  ι.app i := ofHom (DirectLimit.Algebra.of B f i)
  ι.naturality _ _ h := hom_ext (AlgHom.ext fun x ↦ DirectLimit.Algebra.of_f h.le x)

/-- The vertex of the direct-limit cocone is the direct limit of the stage algebras. -/
@[simp]
theorem directLimitCocone_pt :
    (directLimitCocone B f).pt = .of R (DirectLimit B f) := (rfl)

/-- The direct limit of a nonempty directed system of commutative algebras is a colimit in
`CommAlgCat R`. -/
noncomputable def directLimitIsColimit : IsColimit (directLimitCocone B f) :=
  let desc (s : Cocone (directLimitDiagram B f)) : DirectLimit B f →ₐ[R] s.pt :=
    DirectLimit.Algebra.lift B f s.pt (fun i ↦ (s.ι.app i).hom)
      fun _ _ h x ↦ ConcreteCategory.congr_hom (s.w (homOfLE h)) x
  have hfac (s : Cocone (directLimitDiagram B f)) (i : ι) :
      (desc s).comp (DirectLimit.Algebra.of B f i) = (s.ι.app i).hom :=
    DirectLimit.Algebra.lift_comp_of _ _ _
  { desc := fun s ↦ ofHom (desc s)
    fac := fun s i ↦ by
      have h := congrArg (fun g : B i →ₐ[R] s.pt ↦ ofHom g) (hfac s i)
      simpa only [ofHom_comp, ofHom_hom] using h
    uniq := fun s m hm ↦ hom_ext (by
      rw [hom_ofHom]
      refine DirectLimit.Algebra.hom_ext s.pt fun i ↦ ?_
      rw [hfac]
      simpa only [hom_comp, hom_ofHom] using congrArg Hom.hom (hm i)) }

/-- The categorical map to another cocone is the algebraic direct-limit lift. -/
@[simp]
theorem directLimitIsColimit_desc_hom {s : Cocone (directLimitDiagram B f)} :
    ((directLimitIsColimit B f).desc s).hom =
      DirectLimit.Algebra.lift B f s.pt (fun i ↦ (s.ι.app i).hom)
        (fun _ _ h x ↦ ConcreteCategory.congr_hom (s.w (homOfLE h)) x) := (rfl)

end CommAlgCat
