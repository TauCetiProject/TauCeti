/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Action.Basic
public import TauCeti.AlgebraicGeometry.Limits.Descent
public import TauCeti.CategoryTheory.Filtered.Basic

/-!
# Spreading out finite monoid actions

Let `S = lim Dᵢ` be a cofiltered limit of quasi-compact quasi-separated schemes with affine
transition maps. A scheme of finite presentation over `S`, together with an action of a finite
monoid, comes from a scheme of finite presentation with an action over some `Dᵢ`. In particular,
this applies to finite group actions. The comparison is an isomorphism of actions over `S`, so
it preserves the action maps as scheme morphisms, including over nonreduced bases.

The underlying scheme first spreads out by finite presentation. The finitely many action maps
then lift to one common stage, and the unit and multiplication equations hold at a further
common stage. This supplies equivariant models for constructions involving finite group
quotients.

The construction uses `IsLimit.exists_isPullback_of_finitePresentation` for the underlying
scheme, `IsLimit.exists_overPullback_map_comp_eq` for its endomorphisms, and
`IsLimit.exists_overPullback_map_eq_map` for the action equations. It follows the same
finite-stage construction as spreading out group laws in
`TauCeti.AlgebraicGeometry.Limits.GrpObj`.

## References

* A. Grothendieck, *Éléments de géométrie algébrique IV*, Troisième partie, §8.8.
* The Stacks Project, Tags 01ZM and 01ZC.
-/

public section

open CategoryTheory Limits AlgebraicGeometry

universe u v

namespace CategoryTheory.Limits.IsLimit

variable {I : Type u} [Category.{u} I] [IsCofiltered I] {D : I ⥤ Scheme.{u}}
  [∀ {i j} (f : i ⟶ j), IsAffineHom (D.map f)] {c : Cone D} (hc : IsLimit c)
  [∀ i, CompactSpace (D.obj i)]
  {G : Type v} [Monoid G] [Finite G]

include hc in
/-- Candidate action maps intertwining with an action at the limit satisfy the action equations
after passing to a common later stage. -/
private theorem exists_action_of_lifts {i : I} (Y : Over (D.obj i))
    [QuasiCompact Y.hom] [LocallyOfFiniteType Y.hom]
    (A : Action (Over c.pt) G) (e : (Over.pullback (c.π.app i)).obj Y ≅ A.V)
    (r : G → (Y ⟶ Y))
    (hr : ∀ g, (Over.pullback (c.π.app i)).map (r g) ≫ e.hom = e.hom ≫ (A.ρ g).asHom) :
    ∃ (j : I) (f : j ⟶ i) (B : Action (Over (D.obj j)) G),
      B.V = (Over.pullback (D.map f)).obj Y ∧
        Nonempty (((Over.pullback (c.π.app j)).mapAction G).obj B ≅ A) := by
  let F := Over.pullback (c.π.app i)
  have hone : F.map (r 1) = F.map (𝟙 Y) := by
    apply (cancel_mono e.hom).mp
    simp [F, hr]
  have hmul (g h : G) : F.map (r (g * h)) = F.map (r h ≫ r g) := by
    apply (cancel_mono e.hom).mp
    simp [F, hr, reassoc_of% hr]
  let a : Unit ⊕ (G × G) → (Y ⟶ Y) := Sum.elim (fun _ ↦ r 1) (fun p ↦ r (p.1 * p.2))
  let b : Unit ⊕ (G × G) → (Y ⟶ Y) := Sum.elim (fun _ ↦ 𝟙 Y) (fun p ↦ r p.2 ≫ r p.1)
  obtain ⟨j, f, hf⟩ := IsCofiltered.exists_forall_of_stable
    (R := fun t {j} f ↦ (Over.pullback (D.map f)).map (a t) =
      (Over.pullback (D.map f)).map (b t))
    (fun _ {_ _ _} h he ↦ Over.pullback_map_eq_map_of_comp_eq (D.map_comp h _).symm he)
    (fun t ↦ hc.exists_overPullback_map_eq_map (a t) (b t) (by
      cases t with
      | inl t => exact hone
      | inr t => exact hmul t.1 t.2))
  let B : Action (Over (D.obj j)) G :=
    { V := (Over.pullback (D.map f)).obj Y
      ρ :=
        { toFun g := .of ((Over.pullback (D.map f)).map (r g))
          map_one' := by
            apply End.ext
            simpa [a, b] using hf (.inl ())
          map_mul' g h := by
            apply End.ext
            simpa [a, b] using hf (.inr (g, h)) } }
  let E := (Over.pullbackCompIsoOfEq (c.w f)).app Y ≪≫ e
  refine ⟨j, f, B, rfl, ⟨Action.mkIso E fun g ↦ ?_⟩⟩
  have hn := (Over.pullbackCompIsoOfEq (c.w f)).hom.naturality (r g)
  dsimp only [Functor.comp_map] at hn
  exact (Category.assoc _ _ _).symm.trans <|
    (congrArg (· ≫ e.hom) hn).trans <| by simp [E, Category.assoc, hr]

variable [∀ i, QuasiSeparatedSpace (D.obj i)]

include hc in
/-- A scheme of finite presentation over a cofiltered limit of quasi-compact quasi-separated
schemes with affine transition maps, equipped with an action of a finite monoid, has an
equivariant model of finite presentation over a member of the diagram. In particular this
spreads out finite group actions. -/
theorem exists_action_pullback_iso (A : Action (Over c.pt) G)
    [LocallyOfFinitePresentation A.V.hom] [QuasiCompact A.V.hom] [QuasiSeparated A.V.hom] :
    ∃ (j : I) (B : Action (Over (D.obj j)) G),
      LocallyOfFinitePresentation B.V.hom ∧ QuasiCompact B.V.hom ∧ QuasiSeparated B.V.hom ∧
        Nonempty (((Over.pullback (c.π.app j)).mapAction G).obj B ≅ A) := by
  obtain ⟨i₀⟩ := IsCofiltered.nonempty (C := I)
  obtain ⟨i, Y, p, hfp, hqc, hqs, a, hs⟩ :=
    hc.exists_isPullback_of_finitePresentation i₀ A.V.hom
  have := hfp
  have := hqc
  have := hqs
  let X : Over (D.obj i) := Over.mk p
  have : LocallyOfFinitePresentation X.hom := hfp
  have : QuasiCompact X.hom := hqc
  have : QuasiSeparated X.hom := hqs
  let e : (Over.pullback (c.π.app i)).obj X ≅ A.V :=
    Over.isoMk hs.isoPullback.symm (by simp [X])
  let r := e.symm.conj.toMonoidHom.comp A.ρ
  obtain ⟨j, f, hf⟩ := IsCofiltered.exists_forall_of_stable
    (R := fun g {j} f ↦ c.LiftsAlong (r g).asHom f)
    (fun _ {_ _ _} h he ↦ he.precomp h)
    (fun g ↦ hc.exists_overPullback_map_comp_eq (r g).asHom)
  choose s hs using fun g ↦ (Cone.liftsAlong_iff _ _).mp (hf g)
  let e' := (Over.pullbackCompIsoOfEq (c.w f)).app X ≪≫ e
  have : QuasiCompact ((Over.pullback (D.map f)).obj X).hom := by
    simp only [Over.pullback_obj_hom]
    infer_instance
  have : LocallyOfFiniteType ((Over.pullback (D.map f)).obj X).hom := by
    simp only [Over.pullback_obj_hom]
    infer_instance
  have hs' (g : G) : (Over.pullback (c.π.app j)).map (s g) ≫ e'.hom =
      e'.hom ≫ (A.ρ g).asHom := by
    simp [e', reassoc_of% hs, r, Iso.conj_apply_asHom]
  obtain ⟨k, h, B, hB, he⟩ := hc.exists_action_of_lifts
    ((Over.pullback (D.map f)).obj X) A e' s hs'
  refine ⟨k, B, ?_, ?_, ?_, he⟩ <;> rw [hB] <;>
    simp only [Over.pullback_obj_hom] <;> infer_instance

end CategoryTheory.Limits.IsLimit
