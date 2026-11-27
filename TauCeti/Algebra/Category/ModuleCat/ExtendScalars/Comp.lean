/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings

/-!
# Composition isomorphisms of extension of scalars

For morphisms of commutative rings `f₁₂ : R₁ →+* R₂` and `f₂₃ : R₂ →+* R₃`, Mathlib's
`ModuleCat.extendScalarsComp f₁₂ f₂₃` identifies extension of scalars along `f₂₃.comp f₁₂` with
the composite of the two extensions of scalars. Its conjugate along the extension–restriction
adjunctions is the inverse of the composition isomorphism of restriction of scalars
(`ModuleCat.conjugateEquiv_extendScalarsComp_hom`).

Extension of scalars along a ring morphism `f₁₃` that is only propositionally equal to
`f₂₃.comp f₁₂`, such as the structure map of an algebra `S` over `K` compared with the composite
`K → R → S` of the structure map of `R` and a morphism of algebras, is handled by
`ModuleCat.extendScalarsComp'`, the counterpart of Mathlib's `ModuleCat.restrictScalarsComp'`.
Its associativity and unit coherences are those of Mathlib's `ModuleCat.extendScalars_assoc` and
`ModuleCat.extendScalars_comp_id`. For `K`-algebras, conjugating the base change of a module
endomorphism by these isomorphisms is functorial in the morphism of algebras
(`ModuleCat.extendScalarsComp'_conj_id`, `ModuleCat.extendScalarsComp'_conj_comp`) and natural in
the module (`ModuleCat.extendScalarsComp'_conj_naturality`).

For a functor `ω : C ⥤ ModuleCat K` and a commutative `K`-algebra `R`, the scalar extension
`CategoryTheory.Functor.scalarExtension ω R` is `ω` followed by extension of scalars `R ⊗[K] -`.
Base change along a morphism of `K`-algebras and a natural isomorphism `F ⋙ ω' ≅ ω` induce
comparison isomorphisms of scalar extensions (`CategoryTheory.Functor.scalarExtensionCompIso`,
`CategoryTheory.Functor.scalarExtensionIsoOfIso`). Their monoidality is in
`TauCeti.Algebra.Category.ModuleCat.Monoidal.ExtendScalars`.

## Main declarations

* `ModuleCat.extendScalarsComp'`: extension of scalars along a ring morphism equal to a composite.
* `ModuleCat.extendScalarsComp'_assoc` and `ModuleCat.extendScalarsComp'_hom_comp_id`: its
  coherences.
* `CategoryTheory.Functor.scalarExtension`: the scalar extension of a module-valued functor.
-/

public section

open CategoryTheory

universe u u₁ u₂ v₁ v₂

namespace ModuleCat

variable {R₁ R₂ R₃ : Type u} [CommRing R₁] [CommRing R₂] [CommRing R₃]
  (f₁₂ : R₁ →+* R₂) (f₂₃ : R₂ →+* R₃) (f₁₃ : R₁ →+* R₃) (h : f₁₃ = f₂₃.comp f₁₂)

/-- The conjugate of the composition isomorphism of extension of scalars is the inverse of the
composition isomorphism of restriction of scalars. -/
theorem conjugateEquiv_extendScalarsComp_hom :
    conjugateEquiv ((extendRestrictScalarsAdj f₁₂).comp (extendRestrictScalarsAdj f₂₃))
      (extendRestrictScalarsAdj (f₂₃.comp f₁₂)) (extendScalarsComp.{u} f₁₂ f₂₃).hom =
        (restrictScalarsComp f₁₂ f₂₃).inv := by
  rw [extendScalarsComp, ← conjugateIsoEquiv_apply_hom, Equiv.apply_symm_apply, Iso.symm_hom]

/-- Extension of scalars along a ring morphism `f₁₃` equal to a composite `f₂₃.comp f₁₂` is the
composite of the two extensions of scalars. -/
noncomputable def extendScalarsComp' :
    extendScalars.{u, u, u} f₁₃ ≅ extendScalars.{u, u, u} f₁₂ ⋙ extendScalars.{u, u, u} f₂₃ :=
  eqToIso (congrArg extendScalars h) ≪≫ extendScalarsComp f₁₂ f₂₃

/-- For the composite itself, `extendScalarsComp'` is `extendScalarsComp`. -/
@[simp]
theorem extendScalarsComp'_rfl :
    extendScalarsComp' f₁₂ f₂₃ (f₂₃.comp f₁₂) rfl = extendScalarsComp f₁₂ f₂₃ := by
  simp [extendScalarsComp']

section Coherence

variable {R₄ : Type u} [CommRing R₄] (f₃₄ : R₃ →+* R₄) (f₂₄ : R₂ →+* R₄) (f₁₄ : R₁ →+* R₄)

/-- The isomorphisms `extendScalarsComp'` are associative. -/
@[reassoc]
theorem extendScalarsComp'_assoc (h₁₄ : f₁₄ = f₃₄.comp f₁₃) (h₂₄ : f₂₄ = f₃₄.comp f₂₃)
    (h₁₄' : f₁₄ = f₂₄.comp f₁₂) :
    (extendScalarsComp' f₁₃ f₃₄ f₁₄ h₁₄).hom ≫
      Functor.whiskerRight (extendScalarsComp' f₁₂ f₂₃ f₁₃ h).hom _ =
        (extendScalarsComp' f₁₂ f₂₄ f₁₄ h₁₄').hom ≫
          Functor.whiskerLeft _ (extendScalarsComp' f₂₃ f₃₄ f₂₄ h₂₄).hom ≫
            (Functor.associator _ _ _).inv := by
  subst h h₂₄ h₁₄
  simp only [extendScalarsComp'_rfl]
  exact extendScalars_assoc f₁₂ f₂₃ f₃₄

end Coherence

variable {f₂₂ : R₂ →+* R₂} (hf₂₂ : f₂₂ = RingHom.id R₂)

/-- Extension of scalars along a ring endomorphism equal to the identity is isomorphic to the
identity functor. -/
noncomputable def extendScalarsId' : extendScalars.{u, u, u} f₂₂ ≅ 𝟭 _ :=
  eqToIso (congrArg extendScalars hf₂₂) ≪≫ extendScalarsId R₂

/-- For the identity itself, `extendScalarsId'` is `extendScalarsId`. -/
@[simp]
theorem extendScalarsId'_rfl : extendScalarsId' (rfl : RingHom.id R₂ = RingHom.id R₂) =
    extendScalarsId R₂ := by
  simp [extendScalarsId']

/-- Extension of scalars along a morphism followed by a ring endomorphism equal to the identity
is extension of scalars along the morphism. -/
theorem extendScalarsComp'_hom_comp_id (h₁₂ : f₁₂ = f₂₂.comp f₁₂) :
    (extendScalarsComp' f₁₂ f₂₂ f₁₂ h₁₂).hom ≫
      Functor.whiskerLeft _ (extendScalarsId' hf₂₂).hom ≫ (Functor.rightUnitor _).hom = 𝟙 _ := by
  subst hf₂₂
  rw [extendScalarsId', Iso.trans_hom, eqToIso_refl, Iso.refl_hom, Category.id_comp]
  exact extendScalars_comp_id f₁₂


/-! ### Conjugation by the composition isomorphisms of extension of scalars -/

section Conjugation

variable {K : Type u} [CommRing K]
variable {R S T : Type u} [CommRing R] [Algebra K R] [CommRing S] [Algebra K S] [CommRing T]
  [Algebra K T]

/-- Conjugating the extension of scalars of an endomorphism along `R → S` by the composition
isomorphism is functorial in the morphism of algebras: the identity coherence. -/
theorem extendScalarsComp'_conj_id (M : ModuleCat.{u} K)
    (φ : (ModuleCat.extendScalars (algebraMap K R)).obj M ⟶
      (ModuleCat.extendScalars (algebraMap K R)).obj M) :
    (ModuleCat.extendScalarsComp' (algebraMap K R) (AlgHom.id K R : R →+* R) (algebraMap K R)
        (AlgHom.id K R).comp_algebraMap.symm).hom.app M ≫
      (ModuleCat.extendScalars (AlgHom.id K R : R →+* R)).map φ ≫
        (ModuleCat.extendScalarsComp' (algebraMap K R) (AlgHom.id K R : R →+* R)
          (algebraMap K R) (AlgHom.id K R).comp_algebraMap.symm).inv.app M = φ := by
  set σ := ModuleCat.extendScalarsComp' (algebraMap K R) (AlgHom.id K R : R →+* R)
    (algebraMap K R) (AlgHom.id K R).comp_algebraMap.symm
  set ι := ModuleCat.extendScalarsId' (AlgHom.id_toRingHom (R := K) (A := R))
  -- The identity coherence of extension of scalars identifies `σ.inv` with `ι.hom`.
  have h : σ.inv.app M = ι.hom.app _ := by
    have := NatTrans.congr_app (ModuleCat.extendScalarsComp'_hom_comp_id (algebraMap K R)
      (AlgHom.id_toRingHom (R := K) (A := R)) (AlgHom.id K R).comp_algebraMap.symm) M
    simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.rightUnitor_hom_app,
      NatTrans.id_app] at this
    rw [← Iso.app_hom, Iso.hom_comp_eq_id] at this
    -- The target of the identity functor is definitionally the source, so `erw` unfolds
    -- `(𝟭 _).obj` when matching the right identity morphism.
    erw [Category.comp_id] at this
    exact this.symm
  rw [h, ι.hom.naturality, Functor.id_map, ← h, Iso.hom_inv_id_app_assoc]

/-- Conjugating the extension of scalars of an endomorphism by the composition isomorphisms is
functorial in the morphism of algebras: the composition coherence. -/
theorem extendScalarsComp'_conj_comp (f : R →ₐ[K] S) (g : S →ₐ[K] T)
    (M : ModuleCat.{u} K)
    (φ : (ModuleCat.extendScalars (algebraMap K R)).obj M ⟶
      (ModuleCat.extendScalars (algebraMap K R)).obj M) :
    (ModuleCat.extendScalarsComp' (algebraMap K R) (g.comp f : R →+* T) (algebraMap K T)
        (g.comp f).comp_algebraMap.symm).hom.app M ≫
      (ModuleCat.extendScalars (g.comp f : R →+* T)).map φ ≫
        (ModuleCat.extendScalarsComp' (algebraMap K R) (g.comp f : R →+* T) (algebraMap K T)
          (g.comp f).comp_algebraMap.symm).inv.app M =
    (ModuleCat.extendScalarsComp' (algebraMap K S) (g : S →+* T) (algebraMap K T)
        g.comp_algebraMap.symm).hom.app M ≫
      (ModuleCat.extendScalars (g : S →+* T)).map
        ((ModuleCat.extendScalarsComp' (algebraMap K R) (f : R →+* S) (algebraMap K S)
            f.comp_algebraMap.symm).hom.app M ≫
          (ModuleCat.extendScalars (f : R →+* S)).map φ ≫
            (ModuleCat.extendScalarsComp' (algebraMap K R) (f : R →+* S) (algebraMap K S)
              f.comp_algebraMap.symm).inv.app M) ≫
        (ModuleCat.extendScalarsComp' (algebraMap K S) (g : S →+* T) (algebraMap K T)
          g.comp_algebraMap.symm).inv.app M := by
  set σf := ModuleCat.extendScalarsComp' (algebraMap K R) (f : R →+* S) (algebraMap K S)
    f.comp_algebraMap.symm
  set σg := ModuleCat.extendScalarsComp' (algebraMap K S) (g : S →+* T) (algebraMap K T)
    g.comp_algebraMap.symm
  set σgf := ModuleCat.extendScalarsComp' (algebraMap K R) (g.comp f : R →+* T) (algebraMap K T)
    (g.comp f).comp_algebraMap.symm
  set τ := ModuleCat.extendScalarsComp' (f : R →+* S) (g : S →+* T) (g.comp f : R →+* T)
    (AlgHom.comp_toRingHom g f)
  -- The associativity coherence of extension of scalars along `K → R → S → T`.
  have hA : σg.hom.app M ≫ (ModuleCat.extendScalars (g : S →+* T)).map (σf.hom.app M) =
      σgf.hom.app M ≫ τ.hom.app _ := by
    simpa using NatTrans.congr_app (ModuleCat.extendScalarsComp'_assoc (algebraMap K R)
      (f : R →+* S) (algebraMap K S) f.comp_algebraMap.symm (g : S →+* T)
      (g.comp f : R →+* T) (algebraMap K T) g.comp_algebraMap.symm (AlgHom.comp_toRingHom g f)
      (g.comp f).comp_algebraMap.symm) M
  rw [← cancel_mono (σg.hom.app M ≫ (ModuleCat.extendScalars (g : S →+* T)).map (σf.hom.app M))]
  have hA_assoc := reassoc_of% hA
  simp only [Functor.map_comp, Category.assoc, Iso.inv_hom_id_app_assoc]
  simp only [hA, Iso.inv_hom_id_app_assoc, ← Functor.map_comp, Iso.inv_hom_id_app]
  simp only [Functor.comp_obj, Category.comp_id, Functor.map_comp, hA_assoc]
  exact congrArg (σgf.hom.app M ≫ ·) (τ.hom.naturality φ)

/-- Conjugation by the composition isomorphism of extension of scalars is natural in the
module. -/
theorem extendScalarsComp'_conj_naturality (f : R →ₐ[K] S) {M N : ModuleCat.{u} K}
    (u : M ⟶ N) (v : N ⟶ M) (φ : (ModuleCat.extendScalars (algebraMap K R)).obj M ⟶
      (ModuleCat.extendScalars (algebraMap K R)).obj M) :
    (ModuleCat.extendScalars (algebraMap K S)).map v ≫
        ((ModuleCat.extendScalarsComp' (algebraMap K R) (f : R →+* S) (algebraMap K S)
            f.comp_algebraMap.symm).hom.app M ≫
          (ModuleCat.extendScalars (f : R →+* S)).map φ ≫
            (ModuleCat.extendScalarsComp' (algebraMap K R) (f : R →+* S) (algebraMap K S)
              f.comp_algebraMap.symm).inv.app M) ≫
        (ModuleCat.extendScalars (algebraMap K S)).map u =
      (ModuleCat.extendScalarsComp' (algebraMap K R) (f : R →+* S) (algebraMap K S)
          f.comp_algebraMap.symm).hom.app N ≫
        (ModuleCat.extendScalars (f : R →+* S)).map
          ((ModuleCat.extendScalars (algebraMap K R)).map v ≫ φ ≫
            (ModuleCat.extendScalars (algebraMap K R)).map u) ≫
          (ModuleCat.extendScalarsComp' (algebraMap K R) (f : R →+* S) (algebraMap K S)
            f.comp_algebraMap.symm).inv.app N := by
  have h := (ModuleCat.extendScalarsComp' (algebraMap K R) (f : R →+* S) (algebraMap K S)
    f.comp_algebraMap.symm).inv.naturality u
  simp only [Functor.comp_map] at h
  simp only [Functor.map_comp, Category.assoc, NatTrans.naturality_assoc, h, Functor.comp_map]

end Conjugation

end ModuleCat

namespace CategoryTheory.Functor

variable {K : Type u} [CommRing K]
variable {C : Type u₁} [Category.{v₁} C]
variable (ω : C ⥤ ModuleCat.{u} K)

/-- The scalar extension of a functor to `K`-modules along a commutative `K`-algebra `R`: the
composite of `ω` with extension of scalars `R ⊗[K] -`. It is lax (strong) monoidal when `ω`
is. -/
noncomputable abbrev scalarExtension (R : Type u) [CommRing R] [Algebra K R] :
    C ⥤ ModuleCat.{u} R :=
  ω ⋙ ModuleCat.extendScalars (algebraMap K R)

variable {R S : Type u} [CommRing R] [Algebra K R] [CommRing S] [Algebra K S]

/-- Extending the scalars of `ω.scalarExtension R` along a morphism `f : R →ₐ[K] S` of
`K`-algebras is `ω.scalarExtension S`. -/
noncomputable def scalarExtensionCompIso (f : R →ₐ[K] S) :
    ω.scalarExtension R ⋙ ModuleCat.extendScalars (f : R →+* S) ≅ ω.scalarExtension S :=
  Functor.associator _ _ _ ≪≫ isoWhiskerLeft ω
    (ModuleCat.extendScalarsComp' (algebraMap K R) (f : R →+* S) (algebraMap K S)
      f.comp_algebraMap.symm).symm

/-- `scalarExtensionCompIso` is the associator followed by the left whiskering of the inverse of
the composition isomorphism of extension of scalars. -/
-- Not `simp`: the component lemmas below are the simp normal form.
theorem scalarExtensionCompIso_hom (f : R →ₐ[K] S) :
    (ω.scalarExtensionCompIso f).hom = (Functor.associator _ _ _).hom ≫ whiskerLeft ω
      (ModuleCat.extendScalarsComp' (algebraMap K R) (f : R →+* S) (algebraMap K S)
        f.comp_algebraMap.symm).inv :=
  (rfl)

/-- The components of the inverse of `scalarExtensionCompIso` are those of the composition
isomorphism of extension of scalars. -/
@[simp]
theorem scalarExtensionCompIso_inv_app (f : R →ₐ[K] S) (X : C) :
    (ω.scalarExtensionCompIso f).inv.app X =
      (ModuleCat.extendScalarsComp' (algebraMap K R) (f : R →+* S) (algebraMap K S)
        f.comp_algebraMap.symm).hom.app (ω.obj X) := by
  simp [scalarExtensionCompIso]

/-- The components of `scalarExtensionCompIso` are those of the inverse of the composition
isomorphism of extension of scalars. -/
@[simp]
theorem scalarExtensionCompIso_hom_app (f : R →ₐ[K] S) (X : C) :
    (ω.scalarExtensionCompIso f).hom.app X =
      (ModuleCat.extendScalarsComp' (algebraMap K R) (f : R →+* S) (algebraMap K S)
        f.comp_algebraMap.symm).inv.app (ω.obj X) := by
  simp [scalarExtensionCompIso]

section IsoOfIso

variable {D : Type u₂} [Category.{v₂} D] (F : C ⥤ D)
variable {ω} {ω' : D ⥤ ModuleCat.{u} K} (ι : F ⋙ ω' ≅ ω)

/-- The scalar extension of `ω'` precomposed with `F` is that of `ω`, through `ι`. -/
noncomputable def scalarExtensionIsoOfIso (R : Type u) [CommRing R] [Algebra K R] :
    F ⋙ ω'.scalarExtension R ≅ ω.scalarExtension R :=
  (Functor.associator _ _ _).symm ≪≫ isoWhiskerRight ι _

/-- `scalarExtensionIsoOfIso` is the inverse associator followed by the extension of scalars of
`ι`. -/
-- Not `simp`: the component lemmas below are the simp normal form.
theorem scalarExtensionIsoOfIso_hom (R : Type u) [CommRing R] [Algebra K R] :
    (scalarExtensionIsoOfIso F ι R).hom = (Functor.associator _ _ _).inv ≫
      whiskerRight ι.hom (ModuleCat.extendScalars (algebraMap K R)) :=
  (rfl)

/-- The components of `scalarExtensionIsoOfIso` are the scalar extensions of those of `ι`. -/
@[simp]
theorem scalarExtensionIsoOfIso_hom_app (R : Type u) [CommRing R] [Algebra K R] (X : C) :
    (scalarExtensionIsoOfIso F ι R).hom.app X = (ModuleCat.extendScalars (algebraMap K R)).map
      (ι.hom.app X) := by
  simp [scalarExtensionIsoOfIso]

/-- The components of the inverse of `scalarExtensionIsoOfIso` are the scalar extensions of those
of `ι.inv`. -/
@[simp]
theorem scalarExtensionIsoOfIso_inv_app (R : Type u) [CommRing R] [Algebra K R] (X : C) :
    (scalarExtensionIsoOfIso F ι R).inv.app X = (ModuleCat.extendScalars (algebraMap K R)).map
      (ι.inv.app X) := by
  simp [scalarExtensionIsoOfIso]

end IsoOfIso

end CategoryTheory.Functor
