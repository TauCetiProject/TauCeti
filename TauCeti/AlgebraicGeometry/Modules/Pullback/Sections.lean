/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Modules.Pullback.Basic

/-!
# Pullback of local sections

The unit of pullback and pushforward gives a semilinear map on sections over every open.
These maps commute with coefficient maps, restriction, and composition of scheme morphisms.
`Scheme.Hom.pullbackSectionsLE` also restricts the pullback to any smaller open in the source.
The composition equation identifies direct and iterated pullback through the canonical
pullback-composition isomorphism, so sections can be compared across successive morphisms.
Along the inclusion `U.ι` of an open, pulling back sections over `U` is a bijection onto the global
sections of the pullback (`Scheme.Modules.bijective_pullbackSectionsLE_ι`).
-/

public section

open CategoryTheory AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme.Modules

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Hom

variable {X Y : Scheme.{u}} (g : Y ⟶ X) (M : X.Modules) (U : X.Opens)
/-- Pulling back sections along `g`, as a semilinear map over pullback of local functions. -/
def pullbackSections : Γ(M, U) →ₛₗ[(g.app U).hom]
    Γ((pullback g).obj M, g ⁻¹ᵁ U) where
  toFun := ((pullbackPushforwardAdjunction g).unit.app M).app U
  map_add' := map_add _
  map_smul' r s := ((pullbackPushforwardAdjunction g).unit.app M).app_smul r s
/-- Pullback of sections is the component of the pullback--pushforward adjunction unit. -/
lemma pullbackSections_apply (s : Γ(M, U)) :
    pullbackSections g M U s = ((pullbackPushforwardAdjunction g).unit.app M).app U s := (rfl)
/-- Pullback of sections is natural in the coefficient sheaf. -/
lemma pullbackSections_naturality {N : X.Modules} (f : M ⟶ N) (s : Γ(M, U)) :
    ((pullback g).map f).app (g ⁻¹ᵁ U) (pullbackSections g M U s) =
      pullbackSections g N U (f.app U s) := by
  exact congr($((pullbackPushforwardAdjunction g).unit.naturality f).app U s).symm
/-- Pullback of sections commutes with restriction to smaller opens. -/
lemma pullbackSections_restrict {V : X.Opens} (i : V ⟶ U) (s : Γ(M, U)) :
    ((pullback g).obj M).presheaf.map ((TopologicalSpace.Opens.map g.base).map i).op
      (pullbackSections g M U s) = pullbackSections g M V (M.presheaf.map i.op s) := by
  exact (PresheafOfModules.naturality_apply
    ((pullbackPushforwardAdjunction g).unit.app M).val i.op s).symm
variable {Z : Scheme.{u}} (f : Z ⟶ Y)
/-- The composition comparison carries the pullback of a section to its iterated pullback. -/
lemma pullbackSections_comp (s : Γ(M, U)) :
    ((pullbackComp f g).inv.app M).app ((f ≫ g) ⁻¹ᵁ U)
      (pullbackSections (f ≫ g) M U s) =
    pullbackSections f ((pullback g).obj M) (g ⁻¹ᵁ U)
      (pullbackSections g M U s) := by
  have h := CategoryTheory.unit_conjugateEquiv
    ((pullbackPushforwardAdjunction g).comp (pullbackPushforwardAdjunction f))
    (pullbackPushforwardAdjunction (f ≫ g)) (pullbackComp f g).inv M
  rw [conjugateEquiv_pullbackComp_inv] at h
  exact (congrArg (fun a ↦ a.app U s) h).symm

variable (V : Y.Opens) (hV : V ≤ g ⁻¹ᵁ U)
/-- Pull back a section along `g` and restrict it to an open contained in its inverse image. -/
def pullbackSectionsLE : Γ(M, U) →ₛₗ[(g.appLE U V hV).hom] Γ((pullback g).obj M, V) where
  toFun s := ((pullback g).obj M).presheaf.map (homOfLE hV).op (Scheme.Hom.pullbackSections g M U s)
  map_add' := by simp
  map_smul' r s := by
    rw [map_smulₛₗ, map_smul]
    rfl
/-- Pullback to a smaller open is restriction of the pullback to the full inverse image. -/
lemma pullbackSectionsLE_apply (s : Γ(M, U)) :
    pullbackSectionsLE g M U V hV s =
      ((pullback g).obj M).presheaf.map (homOfLE hV).op (g.pullbackSections M U s) :=
  (rfl)
/-- Pullback to a smaller open commutes with restriction of the section in the target. -/
lemma pullbackSectionsLE_map {U' : X.Opens} (i : U' ⟶ U) (hV' : V ≤ g ⁻¹ᵁ U') (s : Γ(M, U)) :
    pullbackSectionsLE g M U' V hV' (M.presheaf.map i.op s) = pullbackSectionsLE g M U V hV s := by
  rw [pullbackSectionsLE_apply, pullbackSectionsLE_apply, ← pullbackSections_restrict,
    ← ConcreteCategory.comp_apply, ← Functor.map_comp]
  -- Both sides restrict along a morphism `V ⟶ g⁻¹ U`, and `congr` uses that there is only one.
  congr 2
/-- Pullback to the full inverse image agrees with the canonical section pullback. -/
@[simp] lemma pullbackSectionsLE_self (s : Γ(M, U)) :
    pullbackSectionsLE g M U (g ⁻¹ᵁ U) le_rfl s = Scheme.Hom.pullbackSections g M U s := by
  simp [pullbackSectionsLE]
/-- Pullback to a smaller open is natural in the coefficient sheaf. -/
lemma pullbackSectionsLE_naturality {N : X.Modules} (φ : M ⟶ N) (s : Γ(M, U)) :
    ((pullback g).map φ).app V (pullbackSectionsLE g M U V hV s) =
      pullbackSectionsLE g N U V hV (φ.app U s) := by
  have hn := PresheafOfModules.naturality_apply ((pullback g).map φ).val
    (homOfLE hV).op (Scheme.Hom.pullbackSections g M U s)
  have hu := Scheme.Hom.pullbackSections_naturality g M U φ s
  exact hn.trans (congrArg (((pullback g).obj N).presheaf.map (homOfLE hV).op) hu)
/-- The pullback comparison for equal scheme morphisms preserves pulled-back sections. -/
lemma pullbackSectionsLE_congr {g' : Y ⟶ X} (h : g = g') (s : Γ(M, U)) :
    ((pullbackCongr h).hom.app M).app V (pullbackSectionsLE g M U V hV s) =
      pullbackSectionsLE g' M U V (by simpa [← h] using hV) s := by
  subst h
  simp [pullbackCongr]
/-- The composition comparison carries direct pullback to iterated pullback on smaller opens. -/
lemma pullbackSectionsLE_comp {W : Z.Opens} (hW : W ≤ f ⁻¹ᵁ V) (s : Γ(M, U)) :
    ((pullbackComp f g).inv.app M).app W
      (pullbackSectionsLE (f ≫ g) M U W (hW.trans (Set.preimage_mono hV)) s) =
    pullbackSectionsLE f ((pullback g).obj M) V W hW
      (pullbackSectionsLE g M U V hV s) := by
  have h := Scheme.Hom.pullbackSections_comp g M U f s
  have hn := PresheafOfModules.naturality_apply ((pullbackComp f g).inv.app M).val
    (homOfLE (show W ≤ (f ≫ g) ⁻¹ᵁ U from hW.trans
      (Set.preimage_mono (show (V : Set Y) ⊆ (g ⁻¹ᵁ U : Set Y) from hV)))).op
    (Scheme.Hom.pullbackSections (f ≫ g) M U s)
  dsimp only [pullbackSectionsLE, LinearMap.coe_mk, AddHom.coe_mk]
  -- The naturality equation uses the ModuleCat components before forgetting to groups.
  erw [hn]
  erw [h]
  have hr := Scheme.Hom.pullbackSections_restrict f ((pullback g).obj M) (g ⁻¹ᵁ U)
    (homOfLE hV) (Scheme.Hom.pullbackSections g M U s)
  rw [← hr, ← ((pullback f).obj ((pullback g).obj M)).presheaf.map_comp_apply]
  rfl
/-- The forward composition comparison carries iterated pullback to direct pullback. -/
lemma pullbackSectionsLE_comp_hom {W : Z.Opens} (hW : W ≤ f ⁻¹ᵁ V)
    (s : Γ(M, U)) :
    ((pullbackComp f g).hom.app M).app W
      (pullbackSectionsLE f ((pullback g).obj M) V W hW
        (pullbackSectionsLE g M U V hV s)) =
    pullbackSectionsLE (f ≫ g) M U W
      (hW.trans (Set.preimage_mono (show (V : Set Y) ⊆ (g ⁻¹ᵁ U : Set Y) from hV))) s := by
  rw [← pullbackSectionsLE_comp g M U f V hV hW]
  simpa only [Iso.app_hom, Iso.app_inv, Modules.Hom.comp_app, Modules.Hom.id_app,
    ConcreteCategory.comp_apply, ConcreteCategory.id_apply] using congrArg
    (fun a : (pullback (f ≫ g)).obj M ⟶ (pullback (f ≫ g)).obj M ↦ a.app W
      (pullbackSectionsLE (f ≫ g) M U W _ s)) ((pullbackComp f g).app M).inv_hom_id

/-- Pulling back sections over `U` along the open immersion `U.ι : U ⟶ Y` identifies them with the
global sections of the pullback to `U`. The global open is given as any `T` equal to `⊤`, such as
the preimage of `⊤` under a morphism into `U`. -/
theorem _root_.AlgebraicGeometry.Scheme.Modules.bijective_pullbackSectionsLE_ι {Y : Scheme.{u}}
    (P : Y.Modules) (U : Y.Opens) (T : U.toScheme.Opens) (hT : T = ⊤) :
    Function.Bijective (U.ι.pullbackSectionsLE P U T (hT ▸ by simp)) := by
  subst hT
  have hu := Adjunction.unit_leftAdjointUniq_hom_app (restrictAdjunction U.ι)
    (pullbackPushforwardAdjunction U.ι) P
  have h₁ : IsIso (((restrictAdjunction U.ι).unit.app P).app U) :=
    isIso_restrictAdjunction_unit_app_app U P le_rfl
  have h₂ : IsIso (((pullback U.ι).obj P).presheaf.map
      (homOfLE (show ⊤ ≤ U.ι ⁻¹ᵁ U by simp)).op) :=
    have : homOfLE (show ⊤ ≤ U.ι ⁻¹ᵁ U by simp) = eqToHom (by simp) := Subsingleton.elim _ _
    this ▸ inferInstance
  -- The pullback of sections along `U.ι` is the restriction-pushforward unit followed by the
  -- comparison of restriction with pullback, then restriction from `U.ι ⁻¹ᵁ U` to `⊤`.
  have h₃ : (U.ι.pullbackSectionsLE P U ⊤ (by simp) : Γ(P, U) → _) =
      ((pullback U.ι).obj P).presheaf.map (homOfLE (show ⊤ ≤ U.ι ⁻¹ᵁ U by simp)).op ∘
        ((restrictFunctorIsoPullback U.ι).hom.app P).app (U.ι ⁻¹ᵁ U) ∘
        ((restrictAdjunction U.ι).unit.app P).app U := by
    ext s
    rw [pullbackSectionsLE_apply, pullbackSections_apply, ← hu]
    rfl
  rw [h₃]
  exact (ConcreteCategory.bijective_of_isIso _).comp
    ((ConcreteCategory.bijective_of_isIso _).comp (ConcreteCategory.bijective_of_isIso _))

/-- For `h : f ≫ g = gf`, pulling a global section back along `gf` and identifying
`gf^* M ≅ f^* g^* M` gives its iterated pullback along `g` and then `f`. -/
lemma pullbackSections_comp_of_eq {gf : Z ⟶ X} (h : f ≫ g = gf) (s : Γ(M, ⊤)) :
    ((pullbackComp f g).inv.app M).app ⊤ (((pullbackCongr h).inv.app M).app ⊤
      (pullbackSections gf M ⊤ s)) =
    pullbackSections f ((pullback g).obj M) ⊤ (pullbackSections g M ⊤ s) := by
  subst h
  exact pullbackSections_comp g M ⊤ f s

open MonoidalCategory in
/-- The pullback of the global section `1` of the structure sheaf is the global section `1`,
under the identification `g^* 𝒪_X ≅ 𝒪_Y`. -/
lemma pullbackObjUnitIso_inv_app_one :
    (pullbackObjUnitIso g).inv.app ⊤ (1 : Γ(Y, ⊤)) =
      pullbackSections g (𝟙_ X.Modules) ⊤ (1 : Γ(X, ⊤)) := by
  -- The transpose of `g^* 𝒪_X ≅ 𝒪_Y` sends `1` to `g^♯ 1 = 1`.
  have h := congr($(pullbackPushforwardAdjunction_homEquiv_pullbackObjUnitIso_hom g).val.app
    (op ⊤) (1 : Γ(X, ⊤)))
  rw [Adjunction.homEquiv_unit] at h
  have h' : (pullbackObjUnitIso g).hom.app ⊤ (pullbackSections g (𝟙_ X.Modules) ⊤ (1 : Γ(X, ⊤))) =
      (1 : Γ(Y, ⊤)) :=
    (congrArg (fun x ↦ (pullbackObjUnitIso g).hom.app ⊤ x)
      (pullbackSections_apply g (𝟙_ X.Modules) ⊤ (1 : Γ(X, ⊤)))).trans
        (h.trans (map_one g.appTop.hom))
  exact (congrArg (fun x ↦ (pullbackObjUnitIso g).inv.app ⊤ x) h').symm.trans
    congr($((pullbackObjUnitIso g).hom_inv_id).app ⊤
      (pullbackSections g (𝟙_ X.Modules) ⊤ (1 : Γ(X, ⊤))))

end AlgebraicGeometry.Scheme.Hom
