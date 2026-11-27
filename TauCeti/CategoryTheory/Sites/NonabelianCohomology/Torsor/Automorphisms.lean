/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.Grp.Limits
public import TauCeti.CategoryTheory.Sites.NonabelianCohomology.Torsor

/-!
# Automorphisms of an abelian torsor

For a torsor under a sheaf of commutative groups, positive translation identifies the
compatible global sections of the group sheaf with the automorphism group of the torsor.
No global section of the torsor or terminal object of the site is needed: the displacement
of an equivariant automorphism is invariant under translation, and descends by the sheaf axiom.

This is the translation description used in Milne, *Étale Cohomology*, IV §2.
-/

public noncomputable section

open CategoryTheory Opposite

universe w v u

namespace CategoryTheory.Sheaf.Torsor

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  {G : Sheaf J GrpCat.{w}} [∀ U, IsMulCommutative (G.obj.obj U)] (P : Torsor G)

/-- Positive translation by a compatible global section, as an equivariant morphism. -/
def translationHom (s : (G.obj ⋙ forget GrpCat).sections) : P ⟶ P where
  hom := ObjectProperty.homMk
    { app U := ↾fun p ↦ GrpCat.sectionsπMonoidHom G.obj U s • p
      naturality U V f := by
        ext p
        exact ((P.map_smul f (GrpCat.sectionsπMonoidHom G.obj U s) p).trans
          (congrArg (fun g : G.obj.obj V ↦ g • P.sheaf.obj.map f p) (s.property f))).symm }
  map_smul U g p := by simp [← mul_smul, mul_comm']

@[simp]
lemma translationHom_hom_app (s : (G.obj ⋙ forget GrpCat).sections) (U : Cᵒᵖ)
    (p : P.sheaf.obj.obj U) : (P.translationHom s).hom.hom.app U p =
      GrpCat.sectionsπMonoidHom G.obj U s • p := (rfl)

/-- Translation gives a homomorphism into the automorphism group of an abelian torsor. -/
def translation : (G.obj ⋙ forget GrpCat).sections →* Aut P where
  toFun s := .of (asIso (P.translationHom s))
  map_one' := by ext U p; simp [translationHom]
  map_mul' s t := by ext U p; simp [translationHom, mul_smul]

@[simp]
lemma translation_hom_app (s : (G.obj ⋙ forget GrpCat).sections) (U : Cᵒᵖ)
    (p : P.sheaf.obj.obj U) : (P.translation s).asIso.hom.hom.hom.app U p =
      GrpCat.sectionsπMonoidHom G.obj U s • p := (rfl)

omit [∀ U, IsMulCommutative (G.obj.obj U)] in
/-- The unique displacement taking a local section `p` to its image under `f`. -/
def displacement (f : P ⟶ P) (U : Cᵒᵖ) (p : P.sheaf.obj.obj U) : G.obj.obj U :=
  (MulAction.exists_smul_eq (G.obj.obj U) p (f.hom.hom.app U p)).choose

omit [∀ U, IsMulCommutative (G.obj.obj U)] in
/-- The displacement acts by positive translation. -/
@[simp]
lemma displacement_smul (f : P ⟶ P) (U : Cᵒᵖ) (p : P.sheaf.obj.obj U) :
    P.displacement f U p • p = f.hom.hom.app U p :=
  (MulAction.exists_smul_eq (G.obj.obj U) p (f.hom.hom.app U p)).choose_spec

omit [∀ U, IsMulCommutative (G.obj.obj U)] in
/-- Displacement commutes with restriction. -/
@[simp]
lemma map_displacement (f : P ⟶ P) {U V : Cᵒᵖ} (a : U ⟶ V) (p : P.sheaf.obj.obj U) :
    G.obj.map a (P.displacement f U p) = P.displacement f V (P.sheaf.obj.map a p) := by
  apply P.smul_left_injective (P.sheaf.obj.map a p)
  dsimp only
  rw [← P.map_smul, displacement_smul, displacement_smul]
  exact (NatTrans.naturality_apply f.hom.hom a p).symm

/-- Equivariance and commutativity make the displacement independent of a local section. -/
@[simp]
lemma displacement_smul_eq (f : P ⟶ P) (U : Cᵒᵖ) (g : G.obj.obj U)
    (p : P.sheaf.obj.obj U) : P.displacement f U (g • p) = P.displacement f U p := by
  apply P.smul_left_injective (g • p)
  dsimp only
  rw [displacement_smul, f.map_smul, ← displacement_smul P f U p]
  simp only [← mul_smul, mul_comm']

/-- The displacement of an equivariant endomorphism descends to a global section. -/
theorem exists_translationHom_eq (f : P ⟶ P) :
    ∃ s : (G.obj ⋙ forget GrpCat).sections, P.translationHom s = f := by
  let d : P.sheaf ⟶ (sheafCompose J (forget GrpCat.{w})).obj G := ObjectProperty.homMk
    { app U := ↾P.displacement f U
      naturality U V a := by ext p; exact (P.map_displacement f a p).symm }
  obtain ⟨s, hs⟩ := P.exists_sections_eq_of_smul_invariant d
    (fun U g p ↦ P.displacement_smul_eq f U g p)
  refine ⟨s, ?_⟩
  ext U p
  have hp : P.displacement f U p = GrpCat.sectionsπMonoidHom G.obj U s := hs U p
  exact (P.translationHom_hom_app s U p).trans
    ((congrArg (fun g : G.obj.obj U ↦ g • p) hp.symm).trans (P.displacement_smul f U p))

/-- Global translations are distinguished even when the torsor has no global section. -/
theorem translation_injective : Function.Injective P.translation := by
  intro s t h
  apply P.coversTop.sections_ext ((sheafCompose J (forget GrpCat.{w})).obj G)
  rintro ⟨U, ⟨p⟩⟩
  apply P.smul_left_injective p
  dsimp only
  simpa [GrpCat.sectionsπMonoidHom] using
    congrArg (fun e : Aut P ↦ e.asIso.hom.hom.hom.app (op U) p) h

/-- Positive translation identifies global sections with automorphisms of an abelian torsor. -/
def translationEquiv : (G.obj ⋙ forget GrpCat).sections ≃* Aut P :=
  MulEquiv.ofBijective P.translation ⟨P.translation_injective, fun f ↦ by
    obtain ⟨s, hs⟩ := P.exists_translationHom_eq f.asIso.hom
    exact ⟨s, by ext1; exact Iso.ext hs⟩⟩

@[simp]
lemma translationEquiv_apply (s : (G.obj ⋙ forget GrpCat).sections) :
    P.translationEquiv s = P.translation s := (rfl)

end CategoryTheory.Sheaf.Torsor
