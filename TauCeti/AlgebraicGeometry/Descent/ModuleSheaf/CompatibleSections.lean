/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axel Delaval, Jie Xu, Shitan Xu
-/
module

public import TauCeti.AlgebraicGeometry.Descent.QuasicoherentSheaf.Basic
public import TauCeti.AlgebraicGeometry.Modules.Pullback.Sections
import TauCeti.AlgebraicGeometry.Modules.Sheaf
import TauCeti.Topology.Sheaves.Presheaf

/-!
# Compatible sections of module descent data

For native module descent data along an arbitrary family of scheme morphisms, compatible
families of sections form a sheaf of modules on the base. Its projection to every member of
the family is adjoint to a canonical pullback comparison. No covering or quasi-coherence
hypothesis is needed for this construction.
-/


open CategoryTheory Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules

universe u

noncomputable section

namespace TauCeti.AlgebraicGeometry.Descent.ModuleSheaf

variable {S : Scheme.{u}} {ι : Type u} {X : ι → Scheme.{u}} {p : ∀ i, X i ⟶ S}
  (D : modulesPseudofunctor.DescentData p)

-- These typed presentations keep all section and morphism operations in native module
-- categories when the descent datum is stored in the Cat-valued pseudofunctor.
private abbrev datumObj (i : ι) : (X i).Modules := D.obj i

private abbrev datumHom {Y : Scheme.{u}} (q : Y ⟶ S) {i j : ι}
    (a : Y ⟶ X i) (b : Y ⟶ X j) (ha : a ≫ p i = q) (hb : b ≫ p j = q) :
    (pullback a).obj (datumObj D i) ⟶ (pullback b).obj (datumObj D j) :=
  D.hom q a b ha hb

/-- Sections over the inverse images of `U` agree when pulled back to any common test scheme
and identified by the native descent isomorphisms. -/
public def Compatible (U : S.Opens) {i j : ι} (s : Γ((D.obj i : (X i).Modules), p i ⁻¹ᵁ U))
    (t : Γ((D.obj j : (X j).Modules), p j ⁻¹ᵁ U)) : Prop :=
  ∀ ⦃Y : Scheme.{u}⦄ (a : Y ⟶ X i) (b : Y ⟶ X j) (h : a ≫ p i = b ≫ p j)
    (V : Y.Opens) (ha : V ≤ a ⁻¹ᵁ p i ⁻¹ᵁ U) (hb : V ≤ b ⁻¹ᵁ p j ⁻¹ᵁ U),
    (datumHom D (a ≫ p i) a b rfl h.symm).app V
        (a.pullbackSectionsLE (datumObj D i) _ V ha s) =
      b.pullbackSectionsLE (datumObj D j) _ V hb t

/-- Compatibility can be checked by comparing the pulled-back sections on every common test
scheme, using the given descent morphism to identify their pullback modules. -/
public theorem compatible_iff (U : S.Opens) {i j : ι}
    (s : Γ((D.obj i : (X i).Modules), p i ⁻¹ᵁ U))
    (t : Γ((D.obj j : (X j).Modules), p j ⁻¹ᵁ U)) :
    Compatible D U s t ↔
      ∀ ⦃Y : Scheme.{u}⦄ (a : Y ⟶ X i) (b : Y ⟶ X j) (h : a ≫ p i = b ≫ p j)
        (V : Y.Opens) (ha : V ≤ a ⁻¹ᵁ p i ⁻¹ᵁ U) (hb : V ≤ b ⁻¹ᵁ p j ⁻¹ᵁ U),
        let transition : (pullback a).obj (D.obj i) ⟶ (pullback b).obj (D.obj j) :=
          D.hom (a ≫ p i) a b rfl h.symm
        transition.app V (a.pullbackSectionsLE (D.obj i) _ V ha s) =
          b.pullbackSectionsLE (D.obj j) _ V hb t :=
  (Iff.rfl)

namespace Compatible

variable {D} {U : S.Opens} {i j : ι}
  {s s' : Γ(datumObj D i, p i ⁻¹ᵁ U)} {t t' : Γ(datumObj D j, p j ⁻¹ᵁ U)}

lemma zero : Compatible D U (0 : Γ(datumObj D i, p i ⁻¹ᵁ U))
    (0 : Γ(datumObj D j, p j ⁻¹ᵁ U)) := by
  intro Y a b h V ha hb
  simp

lemma add (hs : Compatible D U s t) (hs' : Compatible D U s' t') :
    Compatible D U (s + s') (t + t') := by
  intro Y a b h V ha hb
  simp only [map_add, hs a b h V ha hb, hs' a b h V ha hb]

lemma neg (hs : Compatible D U s t) : Compatible D U (-s) (-t) := by
  intro Y a b h V ha hb
  simp only [map_neg, hs a b h V ha hb]

lemma smul (hs : Compatible D U s t) (r : Γ(S, U)) :
    Compatible D U ((p i).app U r • s) ((p j).app U r • t) := by
  intro Y a b h V ha hb
  rw [(a.pullbackSectionsLE (datumObj D i) _ V ha).map_smulₛₗ,
    (b.pullbackSectionsLE (datumObj D j) _ V hb).map_smulₛₗ,
    Hom.app_smul, hs a b h V ha hb]
  congr 1
  have appLE_eq (f g : Y ⟶ S) (hfg : f = g)
      (hf : V ≤ f ⁻¹ᵁ U) (hg : V ≤ g ⁻¹ᵁ U) :
      f.appLE U V hf r = g.appLE U V hg r := by
    subst g
    rfl
  rw [Scheme.Hom.app_eq_appLE, Scheme.Hom.app_eq_appLE, ← CommRingCat.comp_apply,
    ← CommRingCat.comp_apply, Scheme.Hom.appLE_comp_appLE, Scheme.Hom.appLE_comp_appLE]
  exact appLE_eq _ _ h _ _

lemma restrict (hs : Compatible D U s t) {U' : S.Opens} (f : U' ⟶ U) :
    Compatible D U'
      ((datumObj D i).presheaf.map (homOfLE ((p i).preimage_mono f.le)).op s)
      ((datumObj D j).presheaf.map (homOfLE ((p j).preimage_mono f.le)).op t) := by
  intro Y a b h V ha hb
  have ha' : V ≤ a ⁻¹ᵁ p i ⁻¹ᵁ U := ha.trans (a.preimage_mono ((p i).preimage_mono f.le))
  have hb' : V ≤ b ⁻¹ᵁ p j ⁻¹ᵁ U := hb.trans (b.preimage_mono ((p j).preimage_mono f.le))
  rw [Scheme.Hom.pullbackSectionsLE_map a (datumObj D i) _ V ha'
    (homOfLE ((p i).preimage_mono f.le)) ha s,
    Scheme.Hom.pullbackSectionsLE_map b (datumObj D j) _ V hb'
      (homOfLE ((p j).preimage_mono f.le)) hb t]
  exact hs a b h V ha' hb'

end Compatible

/-- The additive subgroup of compatible families of sections over `U`. -/
def sections (U : S.Opens) : AddSubgroup (∀ i, Γ(datumObj D i, p i ⁻¹ᵁ U)) where
  carrier := {s | ∀ i j, Compatible D U (s i) (s j)}
  add_mem' hs ht i j := (hs i j).add (ht i j)
  zero_mem' _ _ := Compatible.zero
  neg_mem' hs i j := (hs i j).neg

variable {D} in
@[ext]
lemma sections.ext {U : S.Opens} {s t : sections D U}
    (h : ∀ i, s.val i = t.val i) : s = t :=
  Subtype.ext (funext h)

@[instance_reducible]
instance (U : S.Opens) : SMul Γ(S, U) (sections D U) where
  smul r s := ⟨fun i ↦ (p i).app U r • s.val i, fun i j ↦ (s.property i j).smul r⟩

variable {D} in
@[simp]
lemma sections.smul_apply {U : S.Opens} (r : Γ(S, U)) (s : sections D U) (i : ι) :
    (r • s).val i = (p i).app U r • s.val i :=
  rfl

@[instance_reducible]
instance (U : S.Opens) : Module Γ(S, U) (sections D U) where
  one_smul s := by ext; simp
  mul_smul r r' s := by ext; simp [mul_smul]
  smul_zero r := by ext; simp
  smul_add r s s' := by ext; simp
  add_smul r r' s := by ext; simp [add_smul]
  zero_smul s := by ext; simp

/-- The presheaf of compatible families of sections, with componentwise restriction. -/
def presheaf : S.Opensᵒᵖ ⥤ AddCommGrpCat.{u} where
  obj U := AddCommGrpCat.of (sections D U.unop)
  map {U U'} f := AddCommGrpCat.ofHom
    { toFun s := ⟨fun i ↦ (datumObj D i).presheaf.map
          (homOfLE ((p i).preimage_mono f.unop.le)).op (s.val i),
        fun i j ↦ (s.property i j).restrict f.unop⟩
      map_zero' := by ext; simp
      map_add' _ _ := by ext; simp }
  map_id U := by
    ext s i
    exact TopCat.Presheaf.map_apply_eq_self _ _ _
  map_comp f g := by
    ext s i
    exact (TopCat.Presheaf.map_map_apply _ _ _ _ _).symm

@[instance_reducible]
instance (U : S.Opensᵒᵖ) : Module (S.ringCatSheaf.obj.obj U) ((presheaf D).obj U) :=
  inferInstanceAs (Module Γ(S, U.unop) (sections D U.unop))

lemma presheaf_map_smul {U U' : S.Opensᵒᵖ} (f : U ⟶ U')
    (r : S.ringCatSheaf.obj.obj U) (s : (presheaf D).obj U) :
    (presheaf D).map f (r • s) = S.ringCatSheaf.obj.map f r • (presheaf D).map f s := by
  refine sections.ext fun i ↦ ?_
  have h := congr($((p i).naturality f) r)
  exact (map_smul _ _ _ _).trans (congrArg (· • _) h.symm)

/-- Compatible families glue componentwise, and their gluing is compatible with the descent
isomorphisms because that assertion is local on every test scheme. -/
theorem isSheaf_presheaf : TopCat.Presheaf.IsSheaf (presheaf D) := by
  rw [TopCat.Presheaf.isSheaf_iff_isSheafUniqueGluing]
  intro κ U sf hsf
  have hc (i : ι) : TopCat.Presheaf.IsCompatible (datumObj D i).presheaf
      (fun k ↦ p i ⁻¹ᵁ U k) (fun k ↦ (sf k).val i) :=
    fun k l ↦ congrArg (fun s : sections D (U k ⊓ U l) ↦ s.val i) (hsf k l)
  choose t ht htu using fun i ↦ TopCat.Sheaf.existsUnique_gluing'
    ⟨(datumObj D i).presheaf, (datumObj D i).isSheaf⟩ (fun k ↦ p i ⁻¹ᵁ U k)
    (p i ⁻¹ᵁ iSup U) (fun k ↦ homOfLE ((p i).preimage_mono (le_iSup U k)))
    ((p i).preimage_iSup U).le _ (hc i)
  have hmem (i j : ι) : Compatible D (iSup U) (t i) (t j) := by
    intro Y a b h V ha hb
    refine TopCat.Sheaf.eq_of_locally_eq'
      ⟨((pullback b).obj (datumObj D j)).presheaf, isSheaf _⟩
      (fun k ↦ V ⊓ a ⁻¹ᵁ p i ⁻¹ᵁ U k) V (fun k ↦ homOfLE inf_le_left)
      ?_ _ _ fun k ↦ ?_
    · intro x hx
      obtain ⟨k, hk⟩ := TopologicalSpace.Opens.mem_iSup.mp (ha hx)
      exact TopologicalSpace.Opens.mem_iSup.mpr ⟨k, hx, hk⟩
    · have hA : V ⊓ a ⁻¹ᵁ p i ⁻¹ᵁ U k ≤ a ⁻¹ᵁ p i ⁻¹ᵁ U k := inf_le_right
      have hB : V ⊓ a ⁻¹ᵁ p i ⁻¹ᵁ U k ≤ b ⁻¹ᵁ p j ⁻¹ᵁ U k :=
        inf_le_right.trans (congrArg (fun q ↦ q ⁻¹ᵁ U k) h).le
      have ea : a.pullbackSectionsLE (datumObj D i) _ _ (inf_le_left.trans ha) (t i) =
          a.pullbackSectionsLE (datumObj D i) _ _ hA ((sf k).val i) := by
        rw [← ht i k]
        exact (Scheme.Hom.pullbackSectionsLE_map a (datumObj D i) _ _ _ _ _ _).symm
      have eb : b.pullbackSectionsLE (datumObj D j) _ _ (inf_le_left.trans hb) (t j) =
          b.pullbackSectionsLE (datumObj D j) _ _ hB ((sf k).val j) := by
        rw [← ht j k]
        exact (Scheme.Hom.pullbackSectionsLE_map b (datumObj D j) _ _ _ _ _ _).symm
      refine (Hom.naturality_apply (datumHom D (a ≫ p i) a b rfl h.symm) _ _).symm.trans ?_
      rw [Scheme.Hom.presheaf_map_pullbackSectionsLE,
        Scheme.Hom.presheaf_map_pullbackSectionsLE, ea, eb]
      exact (sf k).property i j a b h _ hA hB
  refine ⟨⟨t, hmem⟩, fun k ↦ sections.ext fun i ↦ ht i k,
    fun s hs ↦ sections.ext fun i ↦ htu i _ fun k ↦ ?_⟩
  exact congrArg (fun s : sections D (U k) ↦ s.val i) (hs k)

/-- The sheaf of modules on the base whose sections are compatible local sections of `D`. -/
public def descendedModule : S.Modules where
  val := PresheafOfModules.ofPresheaf (presheaf D)
    fun _ _ f r s ↦ presheaf_map_smul D f r s
  isSheaf := isSheaf_presheaf D

/-- Projection of a descended section to the `i`-th member of the family. -/
public def sectionπ {U : S.Opens} (i : ι) :
    Γ(descendedModule D, U) →+ Γ((D.obj i : (X i).Modules), p i ⁻¹ᵁ U) :=
  (Pi.evalAddMonoidHom (fun i ↦ Γ(datumObj D i, p i ⁻¹ᵁ U)) i).comp (sections D U).subtype

variable {D}

/-- The projections of a descended section agree under the descent identification. -/
public theorem sectionπ_compatible {U : S.Opens} (s : Γ(descendedModule D, U)) (i j : ι) :
    Compatible D U (sectionπ D i s) (sectionπ D j s) :=
  s.property i j

/-- The projections to the members of the family determine a descended section. -/
@[ext]
public theorem section_ext {U : S.Opens} {s t : Γ(descendedModule D, U)}
    (h : ∀ i, sectionπ D i s = sectionπ D i t) : s = t :=
  Subtype.ext (funext h)

/-- Every compatible family comes from a section of the descended module. -/
public theorem exists_sectionπ_eq {U : S.Opens}
    (s : ∀ i, Γ((D.obj i : (X i).Modules), p i ⁻¹ᵁ U))
    (hs : ∀ i j, Compatible D U (s i) (s j)) :
    ∃ t : Γ(descendedModule D, U), ∀ i, sectionπ D i t = s i :=
  ⟨⟨s, hs⟩, fun _ ↦ rfl⟩

private theorem sectionπ_smul {U : S.Opens} (r : Γ(S, U)) (s : Γ(descendedModule D, U)) (i : ι) :
    let t : Γ(datumObj D i, p i ⁻¹ᵁ U) := sectionπ D i s
    sectionπ D i (r • s) = (p i).app U r • t :=
  rfl

/-- Restriction of descended sections acts on each component by restriction along the preimage. -/
public theorem sectionπ_restrict {U U' : S.Opens} (f : U' ⟶ U)
    (s : Γ(descendedModule D, U)) (i : ι) :
    sectionπ D i ((descendedModule D).presheaf.map f.op s) =
      (D.obj i : (X i).Modules).presheaf.map (homOfLE ((p i).preimage_mono f.le)).op
        (sectionπ D i s) :=
  (rfl)

variable (D) in
/-- Projection to the direct image of the `i`-th component. -/
def π (i : ι) : descendedModule D ⟶ (pushforward (p i)).obj (datumObj D i) :=
  ⟨PresheafOfModules.homMk
    { app _ := AddCommGrpCat.ofHom (sectionπ D i)
      naturality _ _ _ := rfl }
    fun _ _ _ ↦ rfl⟩

theorem π_app (i : ι) {U : S.Opens} (s : Γ(descendedModule D, U)) :
    (π D i).app U s = sectionπ D i s :=
  rfl

variable (D) in
/-- The pullback comparison, adjoint to the projection to the `i`-th component. -/
def comparison (i : ι) : (pullback (p i)).obj (descendedModule D) ⟶ datumObj D i :=
  ((pullbackPushforwardAdjunction (p i)).homEquiv _ _).symm (π D i)

@[simp]
theorem comparison_app_pullbackSections (i : ι) {U : S.Opens} (s : Γ(descendedModule D, U)) :
    (comparison D i).app (p i ⁻¹ᵁ U) ((p i).pullbackSections (descendedModule D) U s) =
      sectionπ D i s := by
  have h := pullbackPushforwardAdjunction_homEquiv_app_apply (p i) (comparison D i) U s
  rw [comparison, Equiv.apply_symm_apply, π_app] at h
  exact h.symm

private lemma comparisonFromBase_app {Y : Scheme.{u}} {q : Y ⟶ S} {i : ι}
    (a : Y ⟶ X i) (ha : a ≫ p i = q) (U : S.Opens) (s : Γ(descendedModule D, U)) :
    ((pullbackCongr ha).inv.app (descendedModule D) ≫
      (pullbackComp a (p i)).inv.app (descendedModule D) ≫
      (pullback a).map (comparison D i)).app (q ⁻¹ᵁ U)
        (q.pullbackSections (descendedModule D) U s) =
      a.pullbackSectionsLE (datumObj D i) (p i ⁻¹ᵁ U) (q ⁻¹ᵁ U)
        (congrArg (fun f : Y ⟶ S ↦ f ⁻¹ᵁ U) ha).ge (sectionπ D i s) := by
  subst q
  rw [pullbackCongr, eqToIso_refl, Iso.refl_inv, NatTrans.id_app, Category.id_comp]
  rw [Hom.comp_app, ConcreteCategory.comp_apply, Scheme.Hom.pullbackSections_comp]
  have hn := Scheme.Hom.pullbackSections_naturality a ((pullback (p i)).obj (descendedModule D))
    (p i ⁻¹ᵁ U) (comparison D i) ((p i).pullbackSections (descendedModule D) U s)
  rw [comparison_app_pullbackSections] at hn
  exact hn.trans (Scheme.Hom.pullbackSectionsLE_self a (datumObj D i) _ _).symm

private lemma comparison_comm {Y : Scheme.{u}} (q : Y ⟶ S) {i j : ι}
    (a : Y ⟶ X i) (b : Y ⟶ X j) (ha : a ≫ p i = q) (hb : b ≫ p j = q) :
    (pullback a).map (comparison D i) ≫ datumHom D q a b ha hb =
      (pullbackComp a (p i)).hom.app (descendedModule D) ≫
        (pullbackCongr ha).hom.app (descendedModule D) ≫
        (pullbackCongr hb).inv.app (descendedModule D) ≫
        (pullbackComp b (p j)).inv.app (descendedModule D) ≫ (pullback b).map (comparison D j) := by
  subst q
  apply (cancel_epi ((pullbackComp a (p i)).inv.app (descendedModule D))).mp
  have hrefl : a ≫ p i = a ≫ p i := rfl
  rw [Iso.inv_hom_id_app_assoc]
  apply (cancel_epi ((pullbackCongr hrefl).inv.app (descendedModule D))).mp
  rw [Iso.inv_hom_id_app_assoc]
  apply pullback_hom_ext
  intro U s
  have hi := comparisonFromBase_app (D := D) a rfl U s
  have hj := comparisonFromBase_app (D := D) b hb U s
  simp only [← Category.assoc] at hi hj ⊢
  rw [Hom.comp_app, ConcreteCategory.comp_apply, hi, hj]
  exact s.property i j a b hb.symm _ le_rfl (congrArg (fun f : Y ⟶ S ↦ f ⁻¹ᵁ U) hb).ge

variable (D) in
/-- The adjoint comparisons from the descended module commute with the descent isomorphisms. -/
public def comparisonHom :
    Pseudofunctor.DescentData.ofObj (F := modulesPseudofunctor) (f := p)
      (descendedModule (D := D)) ⟶ D where
  hom i := comparison D i
  comm Y q i j a b ha hb := by
    have h := Pseudofunctor.DescentData.ofObj_hom (F := modulesPseudofunctor) (f := p)
      (descendedModule D) Y q i j a b ha hb
    have ha' := modulesPseudofunctor_mapComp'_inv_toNatTrans_app (p i) a q ha (descendedModule D)
    have hb' := modulesPseudofunctor_mapComp'_hom_toNatTrans_app (p j) b q hb (descendedModule D)
    have h' := h.trans (congrArg₂ (fun f g ↦ f ≫ g) ha' hb')
    have h'' := congrArg (fun φ : (pullback a).obj ((pullback (p i)).obj (descendedModule D)) ⟶
        (pullback b).obj ((pullback (p j)).obj (descendedModule D)) ↦
      φ ≫ (pullback b).map (comparison D j)) h'
    have hAssoc :
        (((pullbackComp a (p i)).hom.app (descendedModule D) ≫
          (pullbackCongr ha).hom.app (descendedModule D)) ≫
          (pullbackCongr hb).inv.app (descendedModule D) ≫
          (pullbackComp b (p j)).inv.app (descendedModule D)) ≫
            (pullback b).map (comparison D j) =
          (pullbackComp a (p i)).hom.app (descendedModule D) ≫
            (pullbackCongr ha).hom.app (descendedModule D) ≫
            (pullbackCongr hb).inv.app (descendedModule D) ≫
            (pullbackComp b (p j)).inv.app (descendedModule D) ≫
            (pullback b).map (comparison D j) := by
      simp only [Category.assoc]
    exact (comparison_comm q a b ha hb).trans (hAssoc.symm.trans h''.symm)

variable {M : S.Modules}

private abbrev component
    (φ : Pseudofunctor.DescentData.ofObj (F := modulesPseudofunctor) (f := p) M ⟶ D)
    (i : ι) : (pullback (p i)).obj M ⟶ datumObj D i :=
  φ.hom i

private lemma component_app_compatible
    (φ : Pseudofunctor.DescentData.ofObj (F := modulesPseudofunctor) (f := p) M ⟶ D)
    (U : S.Opens) (s : Γ(M, U)) (i j : ι) :
    Compatible D U ((component φ i).app _ ((p i).pullbackSections M U s))
      ((component φ j).app _ ((p j).pullbackSections M U s)) := by
  intro Y a b h V ha hb
  let q := a ≫ p i
  let aa := ((pullbackComp a (p i)).app M).symm
  let bb := ((pullbackCongr h.symm).app M).symm ≪≫ ((pullbackComp b (p j)).app M).symm
  have he :
      datumHom (Pseudofunctor.DescentData.ofObj (F := modulesPseudofunctor) (f := p) M)
        q a b rfl h.symm = aa.inv ≫ bb.hom := by
    have h₀ := Pseudofunctor.DescentData.ofObj_hom (F := modulesPseudofunctor) (f := p)
      M Y q i j a b rfl h.symm
    have h₁ := modulesPseudofunctor_mapComp'_inv_toNatTrans_app (p i) a q rfl M
    have h₂ := modulesPseudofunctor_mapComp'_hom_toNatTrans_app (p j) b q h.symm M
    rw [pullbackCongr, eqToIso_refl, Iso.refl_hom, NatTrans.id_app, Category.comp_id] at h₁
    exact h₀.trans (congrArg₂ (fun f g ↦ f ≫ g) h₁ h₂)
  have hcomm :
      (pullback a).map (component φ i) ≫ datumHom D q a b rfl h.symm =
      datumHom (Pseudofunctor.DescentData.ofObj (F := modulesPseudofunctor) (f := p) M)
        q a b rfl h.symm ≫ (pullback b).map (component φ j) :=
    φ.comm q a b rfl h.symm
  rw [he] at hcomm
  have hc : aa.hom ≫ (pullback a).map (component φ i) ≫ datumHom D q a b rfl h.symm =
      bb.hom ≫ (pullback b).map (component φ j) := by
    calc
      _ = aa.hom ≫ (aa.inv ≫ bb.hom) ≫ (pullback b).map (component φ j) :=
        congrArg (aa.hom ≫ ·) hcomm
      _ = _ := by rw [Category.assoc, Iso.hom_inv_id_assoc]
  have ha' : aa.hom.app V (q.pullbackSectionsLE M U V ha s) =
      a.pullbackSectionsLE ((pullback (p i)).obj M) _ V ha ((p i).pullbackSections M U s) := by
    dsimp only [aa, q, Iso.symm_hom, Iso.app_inv]
    simpa only [Scheme.Hom.pullbackSectionsLE_self] using
      Scheme.Hom.pullbackSectionsLE_comp (p i) M U a (p i ⁻¹ᵁ U) le_rfl ha s
  have hb' : bb.hom.app V (q.pullbackSectionsLE M U V ha s) =
      b.pullbackSectionsLE ((pullback (p j)).obj M) _ V hb ((p j).pullbackSections M U s) := by
    dsimp only [bb, Iso.trans_hom, Iso.symm_hom, Iso.app_inv]
    rw [Hom.comp_app, ConcreteCategory.comp_apply]
    have hh := Scheme.Hom.pullbackSectionsLE_congr q M U V ha h s
    have inv_congr {x y : Y ⟶ S} (e : x = y) :
        (pullbackCongr e.symm).inv = (pullbackCongr e).hom := by
      subst y
      rfl
    rw [inv_congr h, hh]
    simpa only [Scheme.Hom.pullbackSectionsLE_self] using
      Scheme.Hom.pullbackSectionsLE_comp (p j) M U b (p j ⁻¹ᵁ U) le_rfl hb s
  have hsec := congrArg (fun k : (pullback q).obj M ⟶ (pullback b).obj (datumObj D j) ↦
    k.app V (q.pullbackSectionsLE M U V ha s)) hc
  simp only [Hom.comp_app, ConcreteCategory.comp_apply] at hsec
  rw [ha', hb', Scheme.Hom.pullbackSectionsLE_naturality, Scheme.Hom.pullbackSectionsLE_naturality]
    at hsec
  exact hsec

private def liftSections
    (φ : Pseudofunctor.DescentData.ofObj (F := modulesPseudofunctor) (f := p) M ⟶ D)
    (U : S.Opens) : Γ(M, U) →+ Γ(descendedModule D, U) where
  toFun s := ⟨fun i ↦ (component φ i).app _ ((p i).pullbackSections M U s),
    component_app_compatible φ U s⟩
  map_zero' := sections.ext fun i ↦ by
    change (component φ i).app _ ((p i).pullbackSections M U 0) = 0
    simp
  map_add' s t := sections.ext fun i ↦ by
    change (component φ i).app _ ((p i).pullbackSections M U (s + t)) =
      (component φ i).app _ ((p i).pullbackSections M U s) +
        (component φ i).app _ ((p i).pullbackSections M U t)
    simp

private lemma sectionπ_liftSections
    (φ : Pseudofunctor.DescentData.ofObj (F := modulesPseudofunctor) (f := p) M ⟶ D)
    (U : S.Opens) (s : Γ(M, U)) (i : ι) :
    sectionπ D i (liftSections φ U s) = (component φ i).app _ ((p i).pullbackSections M U s) :=
  rfl

private def liftToGlued
    (φ : Pseudofunctor.DescentData.ofObj (F := modulesPseudofunctor) (f := p) M ⟶ D) :
    M ⟶ descendedModule D :=
  ⟨PresheafOfModules.homMk
    { app U := AddCommGrpCat.ofHom (liftSections φ U.unop)
      naturality U U' f := by
        ext s
        refine section_ext fun i ↦ ?_
        let g : p i ⁻¹ᵁ U'.unop ⟶ p i ⁻¹ᵁ U.unop :=
          (TopologicalSpace.Opens.map (p i).base).map f.unop
        exact ((Hom.naturality_apply (component φ i) g
          ((p i).pullbackSections M U.unop s)).symm.trans
            (congrArg ((component φ i).app _) (Scheme.Hom.pullbackSections_restrict
              (p i) M U.unop f.unop s))).symm }
    fun U r s ↦ section_ext fun i ↦ by
      -- The additive component of the presheaf morphism is the bundled section lift.
      let r' : Γ(S, U.unop) := r
      let s' : Γ(M, U.unop) := s
      change sectionπ D i (liftSections φ U.unop (r' • s')) =
        sectionπ D i (r' • liftSections φ U.unop s')
      rw [sectionπ_smul, sectionπ_liftSections, sectionπ_liftSections]
      exact (congrArg ((component φ i).app _)
        (((p i).pullbackSections M U.unop).map_smulₛₗ r' s')).trans
          (Hom.app_smul (component φ i) _ _)⟩

/-- A morphism of descent data from the pullbacks of a module induces a map to compatible
sections by evaluating each component on the corresponding pulled-back section. -/
public def lift
    (φ : Pseudofunctor.DescentData.ofObj (F := modulesPseudofunctor) (f := p) M ⟶ D) :
    M ⟶ descendedModule (D := D) :=
  liftToGlued φ

private lemma pullback_map_lift_comp_comparison
    (φ : Pseudofunctor.DescentData.ofObj (F := modulesPseudofunctor) (f := p) M ⟶ D) (i : ι) :
    (pullback (p i)).map (liftToGlued φ) ≫ comparison D i = component φ i := by
  apply pullback_hom_ext
  intro U s
  rw [Hom.comp_app, ConcreteCategory.comp_apply, Scheme.Hom.pullbackSections_naturality,
    comparison_app_pullbackSections]
  rfl

/-- The map to compatible sections factors the original morphism of descent data. -/
public theorem toDescentData_map_lift_comp_comparisonHom
    (φ : Pseudofunctor.DescentData.ofObj (F := modulesPseudofunctor) (f := p) M ⟶ D) :
    (modulesPseudofunctor.toDescentData p).map (lift φ) ≫ comparisonHom D = φ :=
  Pseudofunctor.DescentData.hom_ext fun i ↦ pullback_map_lift_comp_comparison φ i

/-- A morphism into the module of compatible sections is determined by its pullbacks followed
by the comparison on every member of the family. -/
public theorem hom_ext_of_comparisonHom
    {φ ψ : M ⟶ descendedModule (D := D)}
    (h : (modulesPseudofunctor.toDescentData p).map φ ≫ comparisonHom D =
      (modulesPseudofunctor.toDescentData p).map ψ ≫ comparisonHom D) :
    φ = ψ := by
  apply Scheme.Modules.hom_ext
  intro U
  apply AddCommGrpCat.hom_ext
  apply AddMonoidHom.ext
  intro s
  refine section_ext fun i ↦ ?_
  have hi : (pullback (p i)).map φ ≫ comparison D i =
      (pullback (p i)).map ψ ≫ comparison D i :=
    congrArg (fun (k : Pseudofunctor.DescentData.ofObj (F := modulesPseudofunctor) M ⟶ D) ↦
      k.hom i) h
  have eval (k : M ⟶ descendedModule D) :
      ((pullback (p i)).map k ≫ comparison D i).app _ ((p i).pullbackSections M U s) =
        sectionπ D i (k.app U s) := by
    rw [Hom.comp_app, ConcreteCategory.comp_apply, Scheme.Hom.pullbackSections_naturality,
      comparison_app_pullbackSections]
  exact (eval φ).symm.trans
    ((congrArg (fun k : (pullback (p i)).obj M ⟶ datumObj D i ↦
      k.app _ ((p i).pullbackSections M U s)) hi).trans (eval ψ))

/-- Morphisms into the compatible-section module are equivalent to morphisms from the
pullback descent datum. The equivalence sends a morphism to its pullback followed by the
canonical comparison. -/
public def homEquiv :
    (M ⟶ descendedModule (D := D)) ≃
      (Pseudofunctor.DescentData.ofObj (F := modulesPseudofunctor) (f := p) M ⟶ D) where
  toFun φ := (modulesPseudofunctor.toDescentData p).map φ ≫ comparisonHom D
  invFun := lift
  left_inv _ := hom_ext_of_comparisonHom (toDescentData_map_lift_comp_comparisonHom _)
  right_inv := toDescentData_map_lift_comp_comparisonHom

end TauCeti.AlgebraicGeometry.Descent.ModuleSheaf
