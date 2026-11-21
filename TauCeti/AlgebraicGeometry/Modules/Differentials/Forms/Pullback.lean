/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Modules.Differentials.Forms.Basic
public import TauCeti.AlgebraicGeometry.Modules.Differentials.Pullback
public import TauCeti.AlgebraicGeometry.Modules.ExteriorPower.Pullback.Coherence
public import TauCeti.AlgebraicGeometry.Modules.GlobalSections
public import Mathlib.RepresentationTheory.Basic

/-!
# Pullback of differential forms

For a morphism `f : X ⟶ Y` of schemes over `Spec R`, the cotangent map
`f^* Ω_{Y/R} ⟶ Ω_{X/R}` induces on `p`-th exterior powers the morphism of `𝒪_X`-modules

`differentialFormsPullbackHom R f p : f^* Ωᵖ_{Y/R} ⟶ Ωᵖ_{X/R}`,

the exterior-power comparison `f^* (⋀ᵖ Ω_{Y/R}) ⟶ ⋀ᵖ (f^* Ω_{Y/R})` followed by `⋀ᵖ` of the
cotangent map. In degree one it is the cotangent map itself. It is the identity for `f = 𝟙 X`
and is contravariantly functorial: the pullback along `f ≫ g` is the pullback along `g` followed
by the pullback along `f`.

On global sections it gives the `R`-linear pullback of global differential forms

`differentialFormsPullback R f p : Γ(Y, Ωᵖ_{Y/R}) →ₗ[R] Γ(X, Ωᵖ_{X/R})`,

again functorial, `(𝟙 X)^* = id` and `(f ≫ g)^* = f^* ∘ g^*`. Consequently the automorphism group
of a scheme over `Spec R` acts on its global `p`-forms. As automorphisms compose as maps and
pullback reverses composition, the left action is by inverse pullback,
`differentialFormsRepresentation R X p g = (g⁻¹)^*`. Its kernel is the group of automorphisms whose
pullback fixes every global `p`-form (`mem_ker_differentialFormsRepresentation_iff`). For the
global two-forms on a surface this is the condition defining symplectic automorphisms.

## Main declarations

* `TauCeti.AlgebraicGeometry.differentialFormsPullbackHom`: the morphism `f^* Ωᵖ_{Y/R} ⟶ Ωᵖ_{X/R}`,
  with `differentialFormsPullbackHom_id`, `differentialFormsPullbackHom_comp` and its degree-one
  case `differentialFormsPullbackHom_one`;
* `TauCeti.AlgebraicGeometry.differentialFormsPullback`: the `R`-linear pullback of global
  `p`-forms, with `differentialFormsPullback_id` and `differentialFormsPullback_comp`;
* `TauCeti.AlgebraicGeometry.differentialFormsRepresentation`: the representation of the
  automorphism group of `X` over `Spec R` on global `p`-forms by inverse pullback.

## References

* R. Hartshorne, *Algebraic Geometry*, Section II.8.
* D. Huybrechts, *Lectures on K3 Surfaces*, Chapter 15, Definition 1.1.
-/

public section

open CategoryTheory AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.Hom

universe u

variable {X : Scheme.{u}} (M : X.Modules) (U : X.Opens)

/-- The identity comparison `(𝟙 X)^* M ≅ M` carries the pullback of a section along the identity
back to the section itself. -/
lemma pullbackSections_id (s : Γ(M, U)) :
    ((Modules.pullbackId X).hom.app M).app U (pullbackSections (𝟙 X) M U s) = s := by
  have h := CategoryTheory.unit_conjugateEquiv Adjunction.id
    (Modules.pullbackPushforwardAdjunction (𝟙 X)) (Modules.pullbackId X).hom M
  rw [Modules.conjugateEquiv_pullbackId_hom] at h
  have h' := congrArg (fun a ↦ a.app U s) h
  simp only [Modules.Hom.comp_app, Modules.pushforward_map_app,
    Modules.pushforwardId_inv_app_app] at h'
  rw [pullbackSections_apply]
  exact h'.symm

end AlgebraicGeometry.Scheme.Hom

namespace TauCeti.AlgebraicGeometry

universe u

noncomputable section

section Sheaf

variable (R : Type u) [CommRing R] {X Y Z : Scheme.{u}}
  [X.Over (Spec (.of R))] [Y.Over (Spec (.of R))] [Z.Over (Spec (.of R))]

/-- The **pullback of differential `p`-forms** `f^* Ωᵖ_{Y/R} ⟶ Ωᵖ_{X/R}` along a morphism
`f : X ⟶ Y` over `Spec R`: the exterior-power comparison `f^* (⋀ᵖ Ω_{Y/R}) ⟶ ⋀ᵖ (f^* Ω_{Y/R})`
followed by the `p`-th exterior power of the cotangent map `f^* Ω_{Y/R} ⟶ Ω_{X/R}`. -/
def differentialFormsPullbackHom (f : X ⟶ Y) [f.IsOver (Spec (.of R))] (p : ℕ) :
    (Scheme.Modules.pullback f).obj (differentialForms R (Y ↘ Spec (.of R)) p) ⟶
      differentialForms R (X ↘ Spec (.of R)) p :=
  (Scheme.Modules.pullbackExteriorPowerComparison f p).app (Y.relativeDifferentials R) ≫
    (SheafOfModules.exteriorPower X.sheaf p).map (cotangentMap R f)

/-- The pullback of differential forms is the exterior-power comparison followed by the exterior
power of the cotangent map. -/
lemma differentialFormsPullbackHom_def (f : X ⟶ Y) [f.IsOver (Spec (.of R))] (p : ℕ) :
    differentialFormsPullbackHom R f p =
      (Scheme.Modules.pullbackExteriorPowerComparison f p).app (Y.relativeDifferentials R) ≫
        (SheafOfModules.exteriorPower X.sheaf p).map (cotangentMap R f) :=
  (rfl)

/-- The pullback of differential forms along the identity is the canonical identification
`(𝟙 X)^* Ωᵖ_{X/R} ≅ Ωᵖ_{X/R}`. -/
@[simp]
theorem differentialFormsPullbackHom_id (p : ℕ) :
    differentialFormsPullbackHom R (𝟙 X) p =
      (Scheme.Modules.pullbackId X).hom.app (differentialForms R (X ↘ Spec (.of R)) p) := by
  rw [differentialFormsPullbackHom_def, cotangentMap_id, pullbackExteriorPowerComparison_id]
  rfl

/-- The pullback of differential forms is contravariantly functorial: along `f ≫ g` it is the
pullback along `g`, pulled back along `f`, followed by the pullback along `f`. -/
@[reassoc]
theorem differentialFormsPullbackHom_comp (f : X ⟶ Y) (g : Y ⟶ Z)
    [f.IsOver (Spec (.of R))] [g.IsOver (Spec (.of R))] (p : ℕ) :
    differentialFormsPullbackHom R (f ≫ g) p =
      (Scheme.Modules.pullbackComp f g).inv.app (differentialForms R (Z ↘ Spec (.of R)) p) ≫
        (Scheme.Modules.pullback f).map (differentialFormsPullbackHom R g p) ≫
          differentialFormsPullbackHom R f p := by
  -- The exterior power as an endofunctor of `X.Modules`, so that compositions are taken there.
  let W : X.Modules ⥤ X.Modules := SheafOfModules.exteriorPower X.sheaf p
  have h₁ : (Scheme.Modules.pullbackExteriorPowerComparison (f ≫ g) p).app
        (Z.relativeDifferentials R) ≫
        W.map ((Scheme.Modules.pullbackComp f g).inv.app (Z.relativeDifferentials R)) =
      (Scheme.Modules.pullbackComp f g).inv.app (differentialForms R (Z ↘ Spec (.of R)) p) ≫
        (Scheme.Modules.pullback f).map
          ((Scheme.Modules.pullbackExteriorPowerComparison g p).app (Z.relativeDifferentials R)) ≫
        (Scheme.Modules.pullbackExteriorPowerComparison f p).app
          ((Scheme.Modules.pullback g).obj (Z.relativeDifferentials R)) :=
    pullbackExteriorPowerComparison_comp f g p _
  have h₂ : (Scheme.Modules.pullbackExteriorPowerComparison f p).app
        ((Scheme.Modules.pullback g).obj (Z.relativeDifferentials R)) ≫
        W.map ((Scheme.Modules.pullback f).map (cotangentMap R g)) =
      (Scheme.Modules.pullback f).map
          ((SheafOfModules.exteriorPower Y.sheaf p).map (cotangentMap R g)) ≫
        (Scheme.Modules.pullbackExteriorPowerComparison f p).app (Y.relativeDifferentials R) :=
    ((Scheme.Modules.pullbackExteriorPowerComparison f p).naturality (cotangentMap R g)).symm
  have e : differentialFormsPullbackHom R (f ≫ g) p
      = (Scheme.Modules.pullbackExteriorPowerComparison (f ≫ g) p).app
            (Z.relativeDifferentials R) ≫
          W.map ((Scheme.Modules.pullbackComp f g).inv.app (Z.relativeDifferentials R)) ≫
          W.map ((Scheme.Modules.pullback f).map (cotangentMap R g)) ≫
          W.map (cotangentMap R f) := by
    rw [← W.map_comp, ← W.map_comp, ← cotangentMap_comp]
    rfl
  rw [e, reassoc_of% h₁]
  -- Rewriting under the comparison morphisms fails at reducible transparency, since their types
  -- mix `X.Modules` with the underlying category of sheaves of modules; compose terms instead.
  refine (Category.assoc _ _ _).trans (congrArg (_ ≫ ·) ((Category.assoc _ _ _).trans ?_))
  exact (congrArg (_ ≫ ·) ((reassoc_of% h₂) _)).trans ((Category.assoc _ _ _).symm.trans
    (congrArg (· ≫ _) ((Scheme.Modules.pullback f).map_comp _ _).symm))

/-- In degree one, the pullback of differential forms is the cotangent map, read through the
identifications `Ω¹ ≅ Ω`. -/
@[reassoc]
theorem differentialFormsPullbackHom_one (f : X ⟶ Y) [f.IsOver (Spec (.of R))] :
    differentialFormsPullbackHom R f 1 ≫ (differentialFormsOneIso R X).hom =
      (Scheme.Modules.pullback f).map (differentialFormsOneIso R Y).hom ≫ cotangentMap R f := by
  have h := (SheafOfModules.exteriorPowerOneIso X.sheaf).hom.naturality (cotangentMap R f)
  have h' := Scheme.Modules.pullbackExteriorPowerComparison_app_comp_exteriorPowerOneIso f
    (Y.relativeDifferentials R)
  rw [differentialFormsOneIso_hom, differentialFormsOneIso_hom]
  -- As in `differentialFormsPullbackHom_comp`, compose the two squares as terms.
  exact (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) h).trans
    ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ _) h')))

end Sheaf

section GlobalSections

open Scheme.Modules

variable (R : Type u) [CommRing R] {X Y Z : Scheme.{u}}
  [X.Over (Spec (.of R))] [Y.Over (Spec (.of R))] [Z.Over (Spec (.of R))]

/-- Pulling back a global function along a morphism over `Spec R` preserves the image of `R`. -/
private lemma appTop_baseRingToGlobalSections (f : X ⟶ Y) [f.IsOver (Spec (.of R))] (r : R) :
    f.appTop (baseRingToGlobalSections R Y r) = baseRingToGlobalSections R X r := by
  rw [baseRingToGlobalSections_apply, baseRingToGlobalSections_apply,
    ← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, HomIsOver.comp_over]

/-- The **pullback of global differential `p`-forms** `Γ(Y, Ωᵖ_{Y/R}) →ₗ[R] Γ(X, Ωᵖ_{X/R})` along a
morphism `f : X ⟶ Y` over `Spec R`: pull a global section back to `f^* Ωᵖ_{Y/R}` and apply
`differentialFormsPullbackHom R f p`. -/
def differentialFormsPullback (f : X ⟶ Y) [f.IsOver (Spec (.of R))] (p : ℕ) :
    Γ(differentialForms R (Y ↘ Spec (.of R)) p, ⊤) →ₗ[R]
      Γ(differentialForms R (X ↘ Spec (.of R)) p, ⊤) where
  -- `f ⁻¹ᵁ ⊤` is `⊤` by definition, as in `Scheme.Hom.appTop`.
  toFun s := (differentialFormsPullbackHom R f p).app ⊤ (f.pullbackSections _ ⊤ s)
  map_add' s t := by
    rw [map_add]
    exact map_add _ _ _
  map_smul' r s := by
    rw [base_smul_globalSections, base_smul_globalSections, map_smulₛₗ, RingHom.id_apply,
      ← appTop_baseRingToGlobalSections R f r]
    exact Scheme.Modules.Hom.app_smul _ _ _

/-- The pullback of a global form is the sheaf pullback applied to the pulled-back section. -/
lemma differentialFormsPullback_apply (f : X ⟶ Y) [f.IsOver (Spec (.of R))] (p : ℕ)
    (s : Γ(differentialForms R (Y ↘ Spec (.of R)) p, ⊤)) :
    differentialFormsPullback R f p s =
      (differentialFormsPullbackHom R f p).app ⊤ (f.pullbackSections _ ⊤ s) :=
  (rfl)

/-- The pullback of global forms along the identity is the identity. -/
@[simp]
theorem differentialFormsPullback_id (p : ℕ) :
    differentialFormsPullback R (𝟙 X) p = LinearMap.id := by
  ext s
  rw [differentialFormsPullback_apply, differentialFormsPullbackHom_id,
    Scheme.Hom.pullbackSections_id, LinearMap.id_apply]

/-- The pullback of global forms is contravariantly functorial: `(f ≫ g)^* = f^* ∘ g^*`. -/
theorem differentialFormsPullback_comp (f : X ⟶ Y) (g : Y ⟶ Z)
    [f.IsOver (Spec (.of R))] [g.IsOver (Spec (.of R))] (p : ℕ) :
    differentialFormsPullback R (f ≫ g) p =
      differentialFormsPullback R f p ∘ₗ differentialFormsPullback R g p := by
  ext s
  rw [differentialFormsPullback_apply, differentialFormsPullbackHom_comp]
  -- `(f ≫ g) ⁻¹ᵁ ⊤` and `f ⁻¹ᵁ (g ⁻¹ᵁ ⊤)` are `⊤` by definition.
  exact pullbackComp_inv_comp_app_pullbackSections f g _ _ ⊤ s

/-- Equal morphisms over `Spec R` induce the same pullback of global forms. -/
lemma differentialFormsPullback_congr {f f' : X ⟶ Y} [f.IsOver (Spec (.of R))]
    [f'.IsOver (Spec (.of R))] (h : f = f') (p : ℕ) :
    differentialFormsPullback R f p = differentialFormsPullback R f' p := by
  subst h
  rfl

/-- Pullback of global forms along a composite, applied to a form. -/
@[simp]
lemma differentialFormsPullback_comp_apply (f : X ⟶ Y) (g : Y ⟶ Z)
    [f.IsOver (Spec (.of R))] [g.IsOver (Spec (.of R))] (p : ℕ)
    (s : Γ(differentialForms R (Z ↘ Spec (.of R)) p, ⊤)) :
    differentialFormsPullback R (f ≫ g) p s =
      differentialFormsPullback R f p (differentialFormsPullback R g p s) := by
  rw [differentialFormsPullback_comp, LinearMap.comp_apply]

end GlobalSections

section Automorphisms

variable (R : Type u) [CommRing R] (X : Scheme.{u}) [X.Over (Spec (.of R))]

/-- The underlying morphism of an endomorphism of `X` in the category of schemes over `Spec R` is a
morphism over `Spec R`, for the given structure morphism of `X`. -/
instance isOver_left (g : Over.mk (X ↘ Spec (.of R)) ⟶ Over.mk (X ↘ Spec (.of R))) :
    Scheme.Hom.IsOver (X := X) (Y := X) g.left (Spec (.of R)) :=
  ⟨Over.w g⟩

/-- The **representation of the automorphism group** of `X` over `Spec R` on global differential
`p`-forms, by inverse pullback `g ↦ (g⁻¹)^*`. Automorphisms compose as maps and pullback reverses
composition, so inverse pullback is the left action. -/
def differentialFormsRepresentation (p : ℕ) :
    Representation R (Aut (Over.mk (X ↘ Spec (.of R))))
      Γ(differentialForms R (X ↘ Spec (.of R)) p, ⊤) where
  toFun g := differentialFormsPullback R (X := X) (Y := X) g.asIso.inv.left p
  map_one' := (differentialFormsPullback_congr R (X := X) (Y := X)
    (by rw [Aut.one_asIso, Iso.refl_inv, Over.id_left]; rfl) p).trans
      (differentialFormsPullback_id R p)
  map_mul' g h := (differentialFormsPullback_congr R (X := X) (Y := X)
    (by rw [Aut.mul_asIso, Iso.trans_inv, Over.comp_left]) p).trans
      (differentialFormsPullback_comp R (X := X) (Y := X) (Z := X) _ _ p)

/-- The automorphism `g` acts on global forms by pullback along its inverse. -/
lemma differentialFormsRepresentation_apply (p : ℕ) (g : Aut (Over.mk (X ↘ Spec (.of R)))) :
    differentialFormsRepresentation R X p g =
      differentialFormsPullback R (X := X) (Y := X) g.asIso.inv.left p :=
  (rfl)

/-- The inverse of `g` acts on global forms by pullback along `g`. -/
lemma differentialFormsRepresentation_inv_apply (p : ℕ) (g : Aut (Over.mk (X ↘ Spec (.of R)))) :
    differentialFormsRepresentation R X p g⁻¹ =
      differentialFormsPullback R (X := X) (Y := X) g.asIso.hom.left p :=
  (rfl)

/-- An automorphism acts trivially on global `p`-forms exactly when its pullback fixes every global
`p`-form: pullback and inverse pullback have the same fixed forms. -/
theorem mem_ker_differentialFormsRepresentation_iff (p : ℕ)
    (g : Aut (Over.mk (X ↘ Spec (.of R)))) :
    g ∈ (differentialFormsRepresentation R X p).ker ↔
      ∀ s, differentialFormsPullback R (X := X) (Y := X) g.asIso.hom.left p s = s := by
  rw [← inv_mem_iff, MonoidHom.mem_ker, differentialFormsRepresentation_inv_apply,
    LinearMap.ext_iff]
  rfl

end Automorphisms

end

end TauCeti.AlgebraicGeometry
