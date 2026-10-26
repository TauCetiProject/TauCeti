/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Linear.FunctorCategory
public import TauCeti.AlgebraicGeometry.Modules.GlobalSections
import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing

/-!
# Local sections as modules over global functions

Restricting global functions to an open equips its sections with a common scalar ring.
Restriction maps are linear over that ring, so differences of restrictions and their
cokernels can be formed as modules, even when the opens have different coordinate rings.
For a scheme over a commutative ring, this action is compatible with that of the base ring
(`AlgebraicGeometry.Scheme.Modules.isScalarTower_sections`).

The sections of a sheaf of modules on a scheme over `R` are thus `R`-modules, and the restriction
maps are `R`-linear: this is the presheaf of `R`-modules
`(Scheme.Modules.sectionsBasePresheafFunctor R).obj M`. Its underlying presheaf of abelian groups
is the presheaf of sections (`Scheme.Modules.sectionsBasePresheafCompForget₂Iso`), and
multiplication by `r : R` on it is induced by multiplication by the global function `r`
(`Scheme.Modules.sectionsBasePresheafFunctor_map_globalSectionsSmul`).

For a family of opens `V i` covering `W`, restriction to the cover
(`Scheme.Modules.sectionsRestrictPiBaseLinear`) and the differences of restrictions to opens
containing the pairwise intersections (`Scheme.Modules.sectionsDiffPiBaseLinear`) are `R`-linear.
By the sheaf condition the first is injective and its image is the kernel of the second
(`Scheme.Modules.sectionsRestrictPiBaseLinear_injective`,
`Scheme.Modules.exact_sectionsRestrictPiBaseLinear`).
-/

public section

open CategoryTheory AlgebraicGeometry Opposite

universe u

namespace AlgebraicGeometry.Scheme.Modules

noncomputable section

variable {X : Scheme.{u}}

/-- Sections over any open are a module over global functions, by restriction of scalars. -/
instance (priority := 900) sectionsGlobalModule (M : X.Modules) (U : X.Opens) :
    Module Γ(X, ⊤) Γ(M, U) :=
  Module.compHom Γ(M, U) (X.presheaf.map U.leTop.op).hom

/-- A global function acts on local sections by its restriction to the open. -/
lemma sectionsGlobal_smul (M : X.Modules) (U : X.Opens)
    (r : Γ(X, ⊤)) (s : Γ(M, U)) :
    r • s = X.presheaf.map U.leTop.op r • s :=
  (rfl)

/-- Restriction of local sections is linear over global functions. -/
def sectionsRestrictionLinear (M : X.Modules) {U V : X.Opens} (i : U ⟶ V) :
    Γ(M, V) →ₗ[Γ(X, ⊤)] Γ(M, U) where
  toFun := M.presheaf.map i.op
  map_add' := map_add _
  map_smul' r s := by
    simp only [sectionsGlobal_smul, RingHom.id_apply, M.map_smul]
    congr 1
    rw [← X.presheaf.map_comp_apply]
    congr 1

@[simp]
lemma sectionsRestrictionLinear_apply (M : X.Modules) {U V : X.Opens}
    (i : U ⟶ V) (s : Γ(M, V)) :
    sectionsRestrictionLinear M i s = M.presheaf.map i.op s :=
  (rfl)

variable (R : Type u) [CommRing R] [X.Over (Spec (.of R))]

/-- For a scheme over a commutative ring `R`, global functions act on local sections compatibly
with `R`, where `R` acts on functions and on sections over `U` through
`Scheme.baseRingToStructurePresheaf`. -/
lemma isScalarTower_sections (M : X.Modules) (U : X.Opens) :
    letI : Algebra R Γ(X, ⊤) := ((X.baseRingToStructurePresheaf R).app (op ⊤)).hom.toAlgebra
    letI : Module R Γ(M, U) :=
      Module.compHom Γ(M, U) ((X.baseRingToStructurePresheaf R).app (op U)).hom
    IsScalarTower R Γ(X, ⊤) Γ(M, U) :=
  letI : Algebra R Γ(X, ⊤) := ((X.baseRingToStructurePresheaf R).app (op ⊤)).hom.toAlgebra
  letI : Module R Γ(M, U) :=
    Module.compHom Γ(M, U) ((X.baseRingToStructurePresheaf R).app (op U)).hom
  .of_algebraMap_smul fun r x ↦ by
    rw [sectionsGlobal_smul, RingHom.algebraMap_toAlgebra, ← CommRingCat.comp_apply,
      ← (X.baseRingToStructurePresheaf R).naturality U.leTop.op]
    simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.id_comp]
    -- `r` acts on sections through `Module.compHom`, by its image in `Γ(X, U)`.
    rfl

/-- The action of `R` on the sections over `W` of a sheaf of modules on a scheme over `R`, through
`Scheme.baseRingToStructurePresheaf`, as in `Scheme.Modules.isScalarTower_sections`. -/
abbrev sectionsBaseModule (M : X.Modules) (W : X.Opens) : Module R Γ(M, W) :=
  Module.compHom Γ(M, W) ((X.baseRingToStructurePresheaf R).app (op W)).hom

/-- Restriction of sections commutes with the action of the base ring through
`Scheme.baseRingToStructurePresheaf`. -/
lemma presheaf_map_baseRingToStructurePresheaf_smul (M : X.Modules) {W V : X.Opens}
    (i : V ⟶ W) (s : R) (x : Γ(M, W)) :
    M.presheaf.map i.op ((X.baseRingToStructurePresheaf R).app (op W) s • x) =
      (X.baseRingToStructurePresheaf R).app (op V) s • M.presheaf.map i.op x := by
  have h := congrArg (fun f ↦ f.hom s) ((X.baseRingToStructurePresheaf R).naturality i.op)
  simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.id_comp,
    CommRingCat.hom_comp, RingHom.comp_apply] at h
  rw [map_smul, ← h]

/-- The presheaf of sections of a sheaf of modules on a scheme over `R`, as a presheaf of
`R`-modules: the sections over `W` keep their carrier and restriction maps, and `R` acts through
`Scheme.baseRingToStructurePresheaf` (`Scheme.Modules.sectionsBaseModule`). The body is exposed
because the carrier of each object is `Γ(M, W)` by definition, which already the statements of
the application lemmas below rely on. -/
@[expose]
def sectionsBasePresheafFunctor : X.Modules ⥤ (X.Opensᵒᵖ ⥤ ModuleCat.{u} R) where
  obj M :=
    { obj W := letI := sectionsBaseModule R M W.unop; ModuleCat.of R Γ(M, W.unop)
      map {W V} i :=
        letI := sectionsBaseModule R M W.unop
        letI := sectionsBaseModule R M V.unop
        ModuleCat.ofHom
          { toFun := M.presheaf.map i
            map_add' := map_add _
            map_smul' := presheaf_map_baseRingToStructurePresheaf_smul R M i.unop }
      map_id W :=
        letI := sectionsBaseModule R M W.unop
        ModuleCat.hom_ext (LinearMap.ext fun x ↦ congrArg (fun f ↦ f.hom x) (M.presheaf.map_id W))
      map_comp {W _ Z} i j :=
        letI := sectionsBaseModule R M W.unop
        letI := sectionsBaseModule R M Z.unop
        ModuleCat.hom_ext (LinearMap.ext fun x ↦
          congrArg (fun f ↦ f.hom x) (M.presheaf.map_comp i j)) }
  map {M N} f :=
    { app W :=
        letI := sectionsBaseModule R M W.unop
        letI := sectionsBaseModule R N W.unop
        ModuleCat.ofHom
          { toFun := f.app W.unop
            map_add' := map_add _
            map_smul' _ _ := Hom.app_smul _ _ _ }
      naturality W V i :=
        letI := sectionsBaseModule R M W.unop
        letI := sectionsBaseModule R N V.unop
        ModuleCat.hom_ext (LinearMap.ext fun x ↦
          congrArg (fun g ↦ g.hom x) (f.mapPresheaf.naturality i)) }
  map_id _ := rfl
  map_comp _ _ := rfl

/-- The restriction maps of the presheaf of `R`-modules of sections are those of `M`. -/
@[simp]
lemma sectionsBasePresheafFunctor_obj_map_hom_apply (M : X.Modules) {W V : X.Opensᵒᵖ}
    (i : W ⟶ V) (x : Γ(M, W.unop)) :
    (((sectionsBasePresheafFunctor R).obj M).map i).hom x = M.presheaf.map i x :=
  rfl

/-- A morphism of sheaves of modules acts on the presheaves of `R`-modules of sections by its
action on sections. -/
@[simp]
lemma sectionsBasePresheafFunctor_map_app_hom_apply {M N : X.Modules} (f : M ⟶ N)
    (W : X.Opensᵒᵖ) (x : Γ(M, W.unop)) :
    (((sectionsBasePresheafFunctor R).map f).app W).hom x = f.app W.unop x :=
  rfl

/-- The underlying presheaf of abelian groups of the presheaf of `R`-modules of sections is the
presheaf of sections. -/
def sectionsBasePresheafCompForget₂Iso (M : X.Modules) :
    (sectionsBasePresheafFunctor R).obj M ⋙ forget₂ (ModuleCat.{u} R) Ab ≅ M.presheaf :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _) fun _ ↦ rfl

/-- The identification `sectionsBasePresheafCompForget₂Iso` is natural in the sheaf of modules. -/
@[reassoc]
lemma sectionsBasePresheafCompForget₂Iso_hom_naturality {M N : X.Modules} (f : M ⟶ N) :
    Functor.whiskerRight ((sectionsBasePresheafFunctor R).map f) (forget₂ (ModuleCat.{u} R) Ab) ≫
        (sectionsBasePresheafCompForget₂Iso R N).hom =
      (sectionsBasePresheafCompForget₂Iso R M).hom ≫ f.mapPresheaf := by
  ext W x
  rfl

/-- Multiplication by `s : R` on the presheaf of `R`-modules of sections is induced by the
multiplication by the global function `s` on the sheaf of modules. -/
lemma sectionsBasePresheafFunctor_map_globalSectionsSmul (M : X.Modules) (s : R) :
    (sectionsBasePresheafFunctor R).map (M.globalSectionsSmul (baseRingToGlobalSections R X s)) =
      s • 𝟙 ((sectionsBasePresheafFunctor R).obj M) := by
  ext W (x : Γ(M, W.unop))
  -- Both sides multiply `x` by the restriction of the global function `s` to `W`.
  change (M.globalSectionsSmul (baseRingToGlobalSections R X s)).app W.unop x =
    (X.baseRingToStructurePresheaf R).app (op W.unop) s • x
  rw [globalSectionsSmul_app, Scheme.baseRingToStructurePresheaf_app]
  rfl

section Restriction

variable (M : X.Modules) {W : X.Opens} {ι : Type*} (V : ι → X.Opens)

/-- The restrictions of the sections over `W` to a family of opens `V i ≤ W`, linear over the
base ring `R`, for any action of `R` on the sections over `W` through functions and for the action
through functions on the sections over each `V i`. -/
def sectionsRestrictPiBaseLinear (hV : ∀ i, V i ≤ W) :
    letI : Algebra R Γ(X, W) := ((X.baseRingToStructurePresheaf R).app (op W)).hom.toAlgebra
    ∀ [Module R Γ(M, W)] [IsScalarTower R Γ(X, W) Γ(M, W)],
      letI := fun i ↦ sectionsBaseModule R M (V i)
      Γ(M, W) →ₗ[R] ∀ i, Γ(M, V i) := by
  letI : Algebra R Γ(X, W) := ((X.baseRingToStructurePresheaf R).app (op W)).hom.toAlgebra
  intro _ _
  letI := fun i ↦ sectionsBaseModule R M (V i)
  exact
    { toFun s i := M.presheaf.map (homOfLE (hV i)).op s
      map_add' _ _ := funext fun _ ↦ map_add _ _ _
      map_smul' t s := funext fun i ↦ by
        rw [← IsScalarTower.algebraMap_smul Γ(X, W) t s, RingHom.id_apply]
        exact presheaf_map_baseRingToStructurePresheaf_smul R M (homOfLE (hV i)) t s }

/-- The components of `sectionsRestrictPiBaseLinear` are the restriction maps. -/
@[simp]
lemma sectionsRestrictPiBaseLinear_apply (hV : ∀ i, V i ≤ W) :
    letI : Algebra R Γ(X, W) := ((X.baseRingToStructurePresheaf R).app (op W)).hom.toAlgebra
    ∀ [Module R Γ(M, W)] [IsScalarTower R Γ(X, W) Γ(M, W)] (s : Γ(M, W)) (i : ι),
      sectionsRestrictPiBaseLinear R M V hV s i = M.presheaf.map (homOfLE (hV i)).op s := by
  intro _ _ _ _
  rfl

/-- A section over `W` is determined by its restrictions to a family of opens covering `W`. -/
lemma sectionsRestrictPiBaseLinear_injective (hV : ∀ i, V i ≤ W) (hW : W ≤ ⨆ i, V i) :
    letI : Algebra R Γ(X, W) := ((X.baseRingToStructurePresheaf R).app (op W)).hom.toAlgebra
    ∀ [Module R Γ(M, W)] [IsScalarTower R Γ(X, W) Γ(M, W)],
      Function.Injective (sectionsRestrictPiBaseLinear R M V hV) := by
  intro _ _ s t h
  exact TopCat.Sheaf.eq_of_locally_eq' (⟨M.presheaf, M.isSheaf⟩ : TopCat.Sheaf AddCommGrpCat X)
    V W (fun i ↦ homOfLE (hV i)) hW s t fun i ↦ congrFun h i

variable {κ : Type*} (W' : κ → X.Opens) (a b : κ → ι) (ha : ∀ p, W' p ≤ V (a p))
  (hb : ∀ p, W' p ≤ V (b p))

/-- The differences `s (a p)|_{W' p} - s (b p)|_{W' p}` of the restrictions of a family of sections
over the `V i` to opens `W' p ≤ V (a p) ⊓ V (b p)`, linear over the base ring `R` acting through
functions. -/
def sectionsDiffPiBaseLinear :
    letI := fun i ↦ sectionsBaseModule R M (V i)
    letI := fun p ↦ sectionsBaseModule R M (W' p)
    (∀ i, Γ(M, V i)) →ₗ[R] ∀ p, Γ(M, W' p) :=
  letI := fun i ↦ sectionsBaseModule R M (V i)
  letI := fun p ↦ sectionsBaseModule R M (W' p)
  LinearMap.pi fun p ↦
    (((sectionsBasePresheafFunctor R).obj M).map (homOfLE (ha p)).op).hom ∘ₗ
        LinearMap.proj (R := R) (φ := fun i ↦ ((sectionsBasePresheafFunctor R).obj M).obj
          (op (V i))) (a p) -
      (((sectionsBasePresheafFunctor R).obj M).map (homOfLE (hb p)).op).hom ∘ₗ
        LinearMap.proj (R := R) (φ := fun i ↦ ((sectionsBasePresheafFunctor R).obj M).obj
          (op (V i))) (b p)

/-- The components of `sectionsDiffPiBaseLinear` are differences of restrictions. -/
@[simp]
lemma sectionsDiffPiBaseLinear_apply (s : ∀ i, Γ(M, V i)) (p : κ) :
    sectionsDiffPiBaseLinear R M V W' a b ha hb s p =
      M.presheaf.map (homOfLE (ha p)).op (s (a p)) -
        M.presheaf.map (homOfLE (hb p)).op (s (b p)) := by
  rfl

/-- Families of sections over the `V i` whose restrictions agree on the opens `W' p` are exactly the
restrictions of the sections over `W`, when the `V i` cover `W` and every pairwise intersection
`V i ⊓ V j` lies in some `W' p` with `a p = i` and `b p = j`. -/
lemma exact_sectionsRestrictPiBaseLinear (hV : ∀ i, V i ≤ W) (hW : W ≤ ⨆ i, V i)
    (hab : ∀ i j, ∃ p, a p = i ∧ b p = j ∧ V i ⊓ V j ≤ W' p) :
    letI : Algebra R Γ(X, W) := ((X.baseRingToStructurePresheaf R).app (op W)).hom.toAlgebra
    ∀ [Module R Γ(M, W)] [IsScalarTower R Γ(X, W) Γ(M, W)],
      Function.Exact (sectionsRestrictPiBaseLinear R M V hV)
        (sectionsDiffPiBaseLinear R M V W' a b ha hb) := by
  intro _ _ x
  let F : TopCat.Sheaf AddCommGrpCat X := ⟨M.presheaf, M.isSheaf⟩
  constructor
  · intro h
    have hc : TopCat.Presheaf.IsCompatible F.obj V x := fun i j ↦ by
      obtain ⟨p, rfl, rfl, hp⟩ := hab i j
      have h' := congrFun h p
      rw [sectionsDiffPiBaseLinear_apply, Pi.zero_apply, sub_eq_zero] at h'
      have := congrArg (M.presheaf.map (homOfLE hp).op) h'
      rw [← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply, ← Functor.map_comp,
        ← Functor.map_comp] at this
      -- Both sides restrict to `V (a p) ⊓ V (b p)`; morphisms between opens are unique.
      exact this
    obtain ⟨z, hz, -⟩ := F.existsUnique_gluing' V W (fun i ↦ homOfLE (hV i)) hW x hc
    exact ⟨z, funext hz⟩
  · rintro ⟨z, rfl⟩
    funext p
    rw [sectionsDiffPiBaseLinear_apply, sectionsRestrictPiBaseLinear_apply,
      sectionsRestrictPiBaseLinear_apply, Pi.zero_apply, sub_eq_zero,
      ← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply, ← Functor.map_comp,
      ← Functor.map_comp]
    -- Both sides restrict `z` to `W' p`; morphisms between opens are unique.
    rfl

end Restriction

end

end AlgebraicGeometry.Scheme.Modules
