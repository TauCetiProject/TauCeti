/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axel Delaval, Jie Xu, Shitan Xu
-/
module

public import TauCeti.AlgebraicGeometry.Descent.QuasicoherentSheaf.Prestack
public import TauCeti.AlgebraicGeometry.Modules.Gluing
public import Mathlib.CategoryTheory.Sites.Descent.IsStack
import TauCeti.AlgebraicGeometry.Modules.Quasicoherent.Restriction
import TauCeti.AlgebraicGeometry.Modules.Pushforward.Basic
import Mathlib.AlgebraicGeometry.Morphisms.OpenImmersion
import Mathlib.CategoryTheory.Sites.Descent.Precoverage

/-!
# Zariski descent of quasi-coherent modules

Quasi-coherent modules glue over Zariski coverings. The construction uses the limit gluing
of modules over the open subschemes belonging to a covering sieve. The local isomorphisms
commute with every comparison map in Mathlib's native descent data.

## Main declarations

* `ZariskiGlue.exists_module_descentIso` constructs a quasi-coherent module inducing a module
  descent datum on a covering lower set of opens.
* `ZariskiGlue.exists_quasicoherentSheaf_descentIso` gives the corresponding isomorphism of
  quasi-coherent descent data.
* `ZariskiGlue.isEquivalence_toDescentData_of_iSup_eq_top` is the equivalence for such a family.
* `ZariskiGlue.isStack_zariskiTopology` proves the Zariski stack property.

## References

* The Stacks Project, Section 26.24, *Functoriality for quasi-coherent modules*, Tag 01LA.
* The Stacks Project, Section 35.5, *Descent of quasi-coherent modules*, Tag 023T.
-/

public section

open CategoryTheory Limits Opposite AlgebraicGeometry

namespace TauCeti.AlgebraicGeometry.Descent

universe u

noncomputable section

section NativeCompatibility

variable {ι : Type u} {S : Scheme.{u}} {X : ι → Scheme.{u}} (p : ∀ i, X i ⟶ S)

private def underlyingDatum (D : qcohPseudofunctor.DescentData p) :
    modulesPseudofunctor.DescentData p where
  obj i := (D.obj i).obj
  hom Y q i j a b ha hb := (D.hom q a b ha hb).hom
  pullHom_hom Z Y g q q' hq i j a b ha hb a' b' ha' hb' := by
    rw [← qcohPseudofunctor_pullHom_hom]
    exact congrArg (fun f ↦ f.hom) (D.pullHom_hom g q q' hq a b ha hb a' b' ha' hb')
  hom_self Y q i a ha := congrArg (fun f ↦ f.hom) (D.hom_self q a ha)
  hom_comp Y q i j k a b c ha hb hc := congrArg (fun f ↦ f.hom)
    (D.hom_comp q a b c ha hb hc)

private def moduleDatumIsoComponent {D E : modulesPseudofunctor.DescentData p}
    (e : D ≅ E) (i : ι) : (D.obj i : (X i).Modules) ≅ (E.obj i : (X i).Modules) where
  hom := e.hom.hom i
  inv := e.inv.hom i
  hom_inv_id := by
    simpa only [Pseudofunctor.DescentData.comp_hom, Pseudofunctor.DescentData.id_hom] using
      congrArg (fun φ ↦ φ.hom i) e.hom_inv_id
  inv_hom_id := by
    simpa only [Pseudofunctor.DescentData.comp_hom, Pseudofunctor.DescentData.id_hom] using
      congrArg (fun φ ↦ φ.hom i) e.inv_hom_id

private def liftDatumIso (D : qcohPseudofunctor.DescentData p) (M : QuasicoherentSheaf S)
    (e : Pseudofunctor.DescentData.ofObj (F := modulesPseudofunctor) (f := p) M.obj ≅
      underlyingDatum p D) :
    Pseudofunctor.DescentData.ofObj (F := qcohPseudofunctor) (f := p) M ≅ D :=
  Pseudofunctor.DescentData.isoMk
    (fun i ↦ ObjectProperty.isoMk _ (moduleDatumIsoComponent p e i))
    (by
      intro Y q i j a b ha hb
      apply ObjectProperty.hom_ext
      exact e.hom.comm q a b ha hb)

-- These typed presentations keep pullback coherence in the native module categories.
-- Repeatedly unfolding the Cat-valued presentations in the comparison proofs is expensive.
private abbrev datumObj (D : modulesPseudofunctor.DescentData p) (i : ι) : (X i).Modules := D.obj i

private abbrev datumHom (D : modulesPseudofunctor.DescentData p) {Y : Scheme.{u}}
    (q : Y ⟶ S) {i j : ι} (a : Y ⟶ X i) (b : Y ⟶ X j)
    (ha : a ≫ p i = q) (hb : b ≫ p j = q) :
    (Scheme.Modules.pullback a).obj (datumObj p D i) ⟶
      (Scheme.Modules.pullback b).obj (datumObj p D j) := D.hom q a b ha hb

private lemma datumHom_pull (D : modulesPseudofunctor.DescentData p) {Y Z : Scheme.{u}}
    (g : Z ⟶ Y) (q : Y ⟶ S) (q' : Z ⟶ S) (hq : g ≫ q = q') {i j : ι}
    (a : Y ⟶ X i) (b : Y ⟶ X j) (ha : a ≫ p i = q) (hb : b ≫ p j = q)
    (a' : Z ⟶ X i) (b' : Z ⟶ X j) (ha' : g ≫ a = a') (hb' : g ≫ b = b') :
    (Scheme.Modules.pullbackCongr ha').inv.app (datumObj p D i) ≫
      (Scheme.Modules.pullbackComp g a).inv.app (datumObj p D i) ≫
        (Scheme.Modules.pullback g).map (datumHom p D q a b ha hb) ≫
          (Scheme.Modules.pullbackComp g b).hom.app (datumObj p D j) ≫
            (Scheme.Modules.pullbackCongr hb').hom.app (datumObj p D j) =
      datumHom p D q' a' b'
        (by rw [← ha', Category.assoc, ha, hq])
        (by rw [← hb', Category.assoc, hb, hq]) := by
  exact (modulesPseudofunctor_pullHom (M₁ := datumObj p D i) (M₂ := datumObj p D j)
    (datumHom p D q a b ha hb) g a' b' ha' hb').symm.trans
      (D.pullHom_hom g q q' hq a b ha hb a' b' ha' hb')

private lemma datumHom_comp (D : modulesPseudofunctor.DescentData p) {Y : Scheme.{u}}
    (q : Y ⟶ S) {i j k : ι} (a : Y ⟶ X i) (b : Y ⟶ X j) (c : Y ⟶ X k)
    (ha : a ≫ p i = q) (hb : b ≫ p j = q) (hc : c ≫ p k = q) :
    datumHom p D q a b ha hb ≫ datumHom p D q b c hb hc =
      datumHom p D q a c ha hc := D.hom_comp q a b c ha hb hc

private lemma datumHom_self (D : modulesPseudofunctor.DescentData p) {Y : Scheme.{u}}
    (q : Y ⟶ S) {i : ι} (a : Y ⟶ X i) (ha : a ≫ p i = q) :
    datumHom p D q a a ha ha = 𝟙 _ := D.hom_self q a ha

private def pullbackHom (D : modulesPseudofunctor.DescentData p) {i j : ι} (a : X i ⟶ X j)
    (ha : a ≫ p j = p i) :
    (Scheme.Modules.pullback a).obj (datumObj p D j) ⟶ datumObj p D i :=
  datumHom p D (p i) a (𝟙 (X i)) ha (Category.id_comp _) ≫
    (Scheme.Modules.pullbackId (X i)).hom.app (datumObj p D i)

private def pushforwardHom (D : modulesPseudofunctor.DescentData p) {i j : ι} (a : X i ⟶ X j)
    (ha : a ≫ p j = p i) :
    datumObj p D j ⟶ (Scheme.Modules.pushforward a).obj (datumObj p D i) :=
  (Scheme.Modules.pullbackPushforwardAdjunction a).homEquiv _ _ (pullbackHom p D a ha)

private lemma pullbackHom_comp (D : modulesPseudofunctor.DescentData p) {i j k : ι}
    (a : X i ⟶ X j) (b : X j ⟶ X k) (ha : a ≫ p j = p i) (hb : b ≫ p k = p j)
    (hab : (a ≫ b) ≫ p k = p i) :
    pullbackHom p D (a ≫ b) hab =
      (Scheme.Modules.pullbackComp a b).inv.app (datumObj p D k) ≫
        (Scheme.Modules.pullback a).map (pullbackHom p D b hb) ≫ pullbackHom p D a ha := by
  have hp := datumHom_pull p D a (p j) (p i) ha b (𝟙 (X j)) hb (Category.id_comp _)
    (a ≫ b) a rfl (Category.comp_id _)
  have hc : datumHom p D (p i) (a ≫ b) a hab ha = _ := hp.symm
  unfold pullbackHom
  rw [← datumHom_comp p D (p i) (a ≫ b) a (𝟙 (X i)) hab ha (Category.id_comp _), hc]
  simp only [Scheme.Modules.pullbackCongr, eqToIso_refl, Iso.refl_inv, NatTrans.id_app,
    Category.id_comp, Functor.map_comp, Category.assoc]
  have hu := Scheme.Modules.pullbackComp_id_hom a (datumObj p D j)
  dsimp only [Scheme.Modules.pullbackCongr] at hu
  rw [reassoc_of% hu]

private lemma pushforwardHom_comp (D : modulesPseudofunctor.DescentData p) {i j k : ι}
    (a : X i ⟶ X j) (b : X j ⟶ X k) (ha : a ≫ p j = p i) (hb : b ≫ p k = p j)
    (hab : (a ≫ b) ≫ p k = p i) :
    pushforwardHom p D (a ≫ b) hab =
      pushforwardHom p D b hb ≫
        (Scheme.Modules.pushforward b).map (pushforwardHom p D a ha) ≫
          (Scheme.Modules.pushforwardComp a b).hom.app (datumObj p D i) := by
  unfold pushforwardHom
  rw [pullbackHom_comp p D a b ha hb hab, homEquiv_pullbackComp]
  simp only [Adjunction.comp_homEquiv, Equiv.trans_apply]
  rw [Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_naturality_right]
  simp only [Category.assoc]

private lemma pushforwardHom_id_app (D : modulesPseudofunctor.DescentData p) {i : ι}
    (a : X i ⟶ X i) (ha : a ≫ p i = p i) (h : a = 𝟙 (X i))
    (V : (X i).Opens) (s : Γ(datumObj p D i, V)) :
    (datumObj p D i).presheaf.map
      (eqToHom (show V = a ⁻¹ᵁ V by rw [h]; rfl)).op
      ((pushforwardHom p D a ha).app V s) = s := by
  subst h
  unfold pushforwardHom pullbackHom
  rw [datumHom_self]
  have hu := CategoryTheory.unit_conjugateEquiv Adjunction.id
    (Scheme.Modules.pullbackPushforwardAdjunction (𝟙 (X i)))
    (Scheme.Modules.pullbackId (X i)).hom (datumObj p D i)
  rw [Scheme.Modules.conjugateEquiv_pullbackId_hom] at hu
  have hres : (datumObj p D i).presheaf.map
      (eqToHom (show V = (𝟙 (X i)) ⁻¹ᵁ V from rfl)).op = 𝟙 _ :=
    (datumObj p D i).presheaf.map_id (op V)
  rw [hres]
  simp only [Category.id_comp, Adjunction.homEquiv_unit]
  exact congrArg (fun φ ↦ φ.app V s) hu.symm

private lemma pushforwardHom_comp_app (D : modulesPseudofunctor.DescentData p) {i j k : ι}
    (a : X i ⟶ X j) (b : X j ⟶ X k) (c : X i ⟶ X k)
    (ha : a ≫ p j = p i) (hb : b ≫ p k = p j) (hc : c ≫ p k = p i)
    (h : c = a ≫ b) (V : (X k).Opens) (s : Γ(datumObj p D k, V)) :
    (datumObj p D i).presheaf.map
      (eqToHom (show a ⁻¹ᵁ b ⁻¹ᵁ V = c ⁻¹ᵁ V by rw [h]; rfl)).op
      ((pushforwardHom p D c hc).app V s) =
    (pushforwardHom p D a ha).app (b ⁻¹ᵁ V) ((pushforwardHom p D b hb).app V s) := by
  subst h
  rw [pushforwardHom_comp p D a b ha hb hc]
  have hres : (datumObj p D i).presheaf.map
      (eqToHom (show a ⁻¹ᵁ b ⁻¹ᵁ V = (a ≫ b) ⁻¹ᵁ V from rfl)).op = 𝟙 _ :=
    (datumObj p D i).presheaf.map_id _
  rw [hres]
  simp only [Scheme.Modules.Hom.comp_app, ConcreteCategory.comp_apply,
    Scheme.Modules.pushforwardComp_hom_app_app]
  rfl

private instance (D : modulesPseudofunctor.DescentData p) {i j : ι}
    (a : X i ⟶ X j) (ha : a ≫ p j = p i) : IsIso (pullbackHom p D a ha) :=
  ((D.iso (i₁ := j) (i₂ := i) (p i) a (𝟙 (X i)) ha (Category.id_comp _)) ≪≫
    (Scheme.Modules.pullbackId (X i)).app (datumObj p D i)).isIso_hom

private lemma bijective_pushforwardHom_app (D : modulesPseudofunctor.DescentData p) {i j : ι}
    (a : X i ⟶ X j) [IsOpenImmersion a] (ha : a ≫ p j = p i)
    (V : (X j).Opens) (hV : V ≤ a.opensRange) :
    Function.Bijective ((pushforwardHom p D a ha).app V) := by
  have := Scheme.Modules.isIso_pullbackPushforwardAdjunction_homEquiv_app a
    (datumObj p D j) (datumObj p D i) (pullbackHom p D a ha) V hV
  unfold pushforwardHom
  exact ConcreteCategory.bijective_of_isIso _

private lemma datumHom_comm_pull (D E : modulesPseudofunctor.DescentData p)
    (φ : ∀ i, D.obj i ⟶ E.obj i) {Y Z : Scheme.{u}} (q : Y ⟶ S)
    {i j : ι} (a : Y ⟶ X i) (b : Y ⟶ X j)
    (ha : a ≫ p i = q) (hb : b ≫ p j = q)
    (h : (modulesPseudofunctor.map a.op.toLoc).toFunctor.map (φ i) ≫ E.hom q a b ha hb =
      D.hom q a b ha hb ≫ (modulesPseudofunctor.map b.op.toLoc).toFunctor.map (φ j))
    (g : Z ⟶ Y) (q' : Z ⟶ S) (hq : g ≫ q = q')
    (a' : Z ⟶ X i) (b' : Z ⟶ X j) (ha' : g ≫ a = a') (hb' : g ≫ b = b') :
    (modulesPseudofunctor.map a'.op.toLoc).toFunctor.map (φ i) ≫
      E.hom q' a' b' (by rw [← ha', Category.assoc, ha, hq])
        (by rw [← hb', Category.assoc, hb, hq]) =
    D.hom q' a' b' (by rw [← ha', Category.assoc, ha, hq])
        (by rw [← hb', Category.assoc, hb, hq]) ≫
      (modulesPseudofunctor.map b'.op.toLoc).toFunctor.map (φ j) := by
  rw [← E.pullHom_hom g q q' hq a b ha hb a' b' ha' hb',
    ← D.pullHom_hom g q q' hq a b ha hb a' b' ha' hb']
  dsimp only [Pseudofunctor.LocallyDiscreteOpToCat.pullHom]
  rw [NatTrans.naturality_assoc]
  dsimp
  rw [← Functor.map_comp_assoc, h, Functor.map_comp_assoc,
    Pseudofunctor.mapComp'_inv_naturality]
  simp only [Category.assoc]

private lemma datumHom_comm_of_pullbackHom (D E : modulesPseudofunctor.DescentData p)
    (φ : ∀ i, datumObj p D i ⟶ datumObj p E i) {i j k : ι}
    (a : X k ⟶ X i) (b : X k ⟶ X j)
    (ha : a ≫ p i = p k) (hb : b ≫ p j = p k)
    (h₁ : (Scheme.Modules.pullback a).map (φ i) ≫ pullbackHom p E a ha =
      pullbackHom p D a ha ≫ φ k)
    (h₂ : (Scheme.Modules.pullback b).map (φ j) ≫ pullbackHom p E b hb =
      pullbackHom p D b hb ≫ φ k) :
    (Scheme.Modules.pullback a).map (φ i) ≫ datumHom p E (p k) a b ha hb =
      datumHom p D (p k) a b ha hb ≫ (Scheme.Modules.pullback b).map (φ j) := by
  have hcomm {l : ι} (c : X k ⟶ X l) (hc : c ≫ p l = p k)
      (h : (Scheme.Modules.pullback c).map (φ l) ≫ pullbackHom p E c hc =
        pullbackHom p D c hc ≫ φ k) :
      (Scheme.Modules.pullback c).map (φ l) ≫
        datumHom p E (p k) c (𝟙 (X k)) hc (Category.id_comp _) =
      datumHom p D (p k) c (𝟙 (X k)) hc (Category.id_comp _) ≫
        (Scheme.Modules.pullback (𝟙 (X k))).map (φ k) := by
    apply (cancel_mono ((Scheme.Modules.pullbackId (X k)).hom.app (datumObj p E k))).1
    rw [Category.assoc, Category.assoc, (Scheme.Modules.pullbackId (X k)).hom.naturality]
    exact h
  have : IsIso (datumHom p E (p k) b (𝟙 (X k)) hb (Category.id_comp _)) :=
    (E.iso (p k) b (𝟙 (X k)) hb (Category.id_comp _)).isIso_hom
  apply (cancel_mono (datumHom p E (p k) b (𝟙 (X k)) hb (Category.id_comp _))).1
  rw [Category.assoc, datumHom_comp, hcomm a ha h₁]
  rw [Category.assoc, hcomm b hb h₂, ← Category.assoc, datumHom_comp]

private def ofObjHomNative (M : S.Modules) {Y : Scheme.{u}} (q : Y ⟶ S) {i j : ι}
    (a : Y ⟶ X i) (b : Y ⟶ X j) (ha : a ≫ p i = q) (hb : b ≫ p j = q) :
    (Scheme.Modules.pullback a).obj ((Scheme.Modules.pullback (p i)).obj M) ⟶
      (Scheme.Modules.pullback b).obj ((Scheme.Modules.pullback (p j)).obj M) :=
  (Pseudofunctor.DescentData.ofObj (F := modulesPseudofunctor) (f := p) M).hom q a b ha hb

private lemma ofObjHomNative_eq (M : S.Modules) {Y : Scheme.{u}} (q : Y ⟶ S) {i j : ι}
    (a : Y ⟶ X i) (b : Y ⟶ X j) (ha : a ≫ p i = q) (hb : b ≫ p j = q) :
    ofObjHomNative p M q a b ha hb =
      (Scheme.Modules.pullbackComp a (p i)).hom.app M ≫
        (Scheme.Modules.pullbackCongr ha).hom.app M ≫
          (Scheme.Modules.pullbackCongr hb).inv.app M ≫
            (Scheme.Modules.pullbackComp b (p j)).inv.app M := by
  have h := Pseudofunctor.DescentData.ofObj_hom (F := modulesPseudofunctor) (f := p)
    M Y q i j a b ha hb
  have h₁ := modulesPseudofunctor_mapComp'_inv_toNatTrans_app (p i) a q ha M
  have h₂ := modulesPseudofunctor_mapComp'_hom_toNatTrans_app (p j) b q hb M
  exact h.trans ((congrArg₂ (fun f g ↦ f ≫ g) h₁ h₂).trans (Category.assoc _ _ _))

private lemma pullbackHom_ofObj (M : S.Modules) {i j : ι} (a : X i ⟶ X j)
    (ha : a ≫ p j = p i) :
    pullbackHom p (Pseudofunctor.DescentData.ofObj (F := modulesPseudofunctor) M) a ha =
      (Scheme.Modules.pullbackComp a (p j)).hom.app M ≫
        (Scheme.Modules.pullbackCongr ha).hom.app M := by
  have h : pullbackHom p (Pseudofunctor.DescentData.ofObj (F := modulesPseudofunctor) M) a ha =
      ofObjHomNative p M (p i) a (𝟙 (X i)) ha (Category.id_comp _) ≫
        (Scheme.Modules.pullbackId (X i)).hom.app ((Scheme.Modules.pullback (p i)).obj M) := rfl
  rw [h, ofObjHomNative_eq]
  simp only [Category.assoc]
  rw [Scheme.Modules.pseudofunctor_right_unitality_app]
  simp only [Scheme.Modules.pullbackCongr, eqToIso.inv, eqToHom_app]
  erw [eqToHom_trans, eqToHom_refl, Category.comp_id]

private def homOfPullbackHom (D E : modulesPseudofunctor.DescentData p)
    (φ : ∀ i, datumObj p D i ⟶ datumObj p E i)
    (h : ∀ i j, ∃ (k : ι) (a : X k ⟶ X i) (b : X k ⟶ X j)
      (ha : a ≫ p i = p k) (hb : b ≫ p j = p k),
      IsPullback a b (p i) (p j) ∧
      (Scheme.Modules.pullback a).map (φ i) ≫ pullbackHom p E a ha =
        pullbackHom p D a ha ≫ φ k ∧
      (Scheme.Modules.pullback b).map (φ j) ≫ pullbackHom p E b hb =
        pullbackHom p D b hb ≫ φ k) : D ⟶ E where
  hom i := φ i
  comm Y q i j a b ha hb := by
    obtain ⟨k, c, d, hc, hd, hpb, h₁, h₂⟩ := h i j
    obtain ⟨r, hr₁, hr₂⟩ := hpb.exists_lift a b (ha.trans hb.symm)
    have hr : r ≫ p k = q := by
      rw [← hc, ← Category.assoc, hr₁, ha]
    have hpair := datumHom_comm_of_pullbackHom p D E φ c d hc hd h₁ h₂
    exact datumHom_comm_pull p D E φ (p k) c d hc hd hpair r q hr a b hr₁ hr₂

end NativeCompatibility

namespace ZariskiGlue

variable {X : Scheme.{u}} (P : LowerSet X.Opens)

/-- Open subschemes satisfying the predicate used for a Zariski gluing. -/
private abbrev Index := {U : X.Opens // U ∈ P}

private def inclusion {U V : Index P} (h : U ⟶ V) : U.val.toScheme ⟶ V.val.toScheme :=
  X.homOfLE h.le

private lemma inclusion_id (U : Index P) : inclusion P (𝟙 U) = 𝟙 _ :=
  X.homOfLE_rfl U.val

private lemma inclusion_comp {U V W : Index P} (f : U ⟶ V) (g : V ⟶ W) :
    inclusion P (f ≫ g) = inclusion P f ≫ inclusion P g :=
  (X.homOfLE_homOfLE f.le g.le).symm

/-- The diagram of the open subschemes used for gluing. -/
private abbrev diagram : Index P ⥤ Scheme.{u} :=
  { obj U := U.val.toScheme
    map h := inclusion P h
    map_id U := inclusion_id P U
    map_comp f g := inclusion_comp P f g }

private lemma diagram_map_ι {U V : Index P} (h : U ⟶ V) :
    (diagram P).map h ≫ V.val.ι = U.val.ι := X.homOfLE_ι h.le

private instance {U V : Index P} (h : U ⟶ V) : IsOpenImmersion ((diagram P).map h) :=
  inferInstanceAs (IsOpenImmersion (X.homOfLE h.le))

private instance : (diagram P ⋙ Scheme.forget).IsLocallyDirected where
  cond {i j k} fi fj xi xj h := by
    dsimp only [Functor.comp_obj, Functor.comp_map, diagram] at xi xj h
    have hx : xi.val = xj.val := by
      exact (X.homOfLE_apply fi.le xi).symm.trans
        ((congrArg Subtype.val h).trans (X.homOfLE_apply fj.le xj))
    let l : Index P := ⟨i.val ⊓ j.val, P.lower inf_le_left i.property⟩
    refine ⟨l, homOfLE (show i.val ⊓ j.val ≤ i.val from inf_le_left),
      homOfLE (show i.val ⊓ j.val ≤ j.val from inf_le_right),
      ⟨xi.val, xi.property, hx ▸ xj.property⟩, ?_, ?_⟩
    · apply Subtype.ext
      exact X.homOfLE_apply inf_le_left _
    · apply Subtype.ext
      exact (X.homOfLE_apply inf_le_right _).trans hx

/-- The cocone of open inclusions into the base scheme. -/
private def cocone : Cocone (diagram P) where
  pt := X
  ι.app U := U.val.ι
  ι.naturality _ _ h := by simp [diagram, inclusion]

/-- The morphism from the glued open subschemes to their union. -/
private def toBase : colimit (diagram P) ⟶ X := colimit.desc _ (cocone P)

@[reassoc (attr := simp)]
private lemma ι_toBase (U : Index P) : colimit.ι (diagram P) U ≫ toBase P = U.val.ι :=
  colimit.ι_desc _ _

private lemma toBase_injective : Function.Injective (toBase P) := by
  intro x y h
  obtain ⟨U, x, rfl⟩ := Scheme.IsLocallyDirected.ι_jointly_surjective (diagram P) x
  obtain ⟨V, y, rfl⟩ := Scheme.IsLocallyDirected.ι_jointly_surjective (diagram P) y
  dsimp only [diagram] at x y
  have hxy : x.val = y.val := by
    have hU := congrArg (fun f : U.val.toScheme ⟶ X ↦ f x) (ι_toBase P U)
    have hV := congrArg (fun f : V.val.toScheme ⟶ X ↦ f y) (ι_toBase P V)
    exact hU.symm.trans (h.trans hV)
  let W : Index P := ⟨U.val ⊓ V.val, P.lower inf_le_left U.property⟩
  have hx : x.val ∈ W.val := ⟨x.property, hxy ▸ y.property⟩
  exact (Scheme.IsLocallyDirected.ι_eq_ι_iff (diagram P)).2
    ⟨W, homOfLE (show U.val ⊓ V.val ≤ U.val from inf_le_left),
      homOfLE (show U.val ⊓ V.val ≤ V.val from inf_le_right), ⟨x.val, hx⟩,
      Subtype.ext (X.homOfLE_apply inf_le_left _),
      Subtype.ext ((X.homOfLE_apply inf_le_right _).trans hxy)⟩

private abbrev family (U : Index P) : U.val.toScheme ⟶ X := U.val.ι

private abbrev obj (D : modulesPseudofunctor.DescentData (family P))
    (U : Index P) : U.val.toScheme.Modules := datumObj (family P) D U

private abbrev glueData (D : modulesPseudofunctor.DescentData (family P)) :
    ModulesGlueData (diagram P) where
  obj U := obj P D U
  map h := pushforwardHom (family P) D ((diagram P).map h) (diagram_map_ι P h)
  map_id U V s := pushforwardHom_id_app (family P) D _ (diagram_map_ι P (𝟙 U))
    ((diagram P).map_id U) V s
  map_comp f g V s := pushforwardHom_comp_app (family P) D _ _ _
    (diagram_map_ι P f) (diagram_map_ι P g) (diagram_map_ι P (f ≫ g))
    ((diagram P).map_comp f g) V s

private lemma glueData_bijective (D : modulesPseudofunctor.DescentData (family P))
    {U V : Index P} (h : U ⟶ V) (W : V.val.toScheme.Opens)
    (hW : W ≤ ((diagram P).map h).opensRange) :
    Function.Bijective (((glueData P D).map h).app W) :=
  bijective_pushforwardHom_app (family P) D _ (diagram_map_ι P h) W hW

private abbrev gluedBase (D : modulesPseudofunctor.DescentData (family P)) : X.Modules :=
  (Scheme.Modules.pushforward (toBase P)).obj (glueData P D).glued

private def πBase (D : modulesPseudofunctor.DescentData (family P)) (U : Index P) :
    gluedBase P D ⟶ (Scheme.Modules.pushforward U.val.ι).obj (obj P D U) :=
  (Scheme.Modules.pushforward (toBase P)).map ((glueData P D).π U) ≫
    (Scheme.Modules.pushforwardComp (colimit.ι (diagram P) U) (toBase P)).hom.app _ ≫
      (Scheme.Modules.pushforwardCongr (ι_toBase P U)).hom.app _

private lemma preimage_le_colimit_opensRange (U : Index P) (V : X.Opens)
    (hV : V ≤ U.val.ι.opensRange) :
    (toBase P) ⁻¹ᵁ V ≤ (colimit.ι (diagram P) U).opensRange := by
  intro z hz
  obtain ⟨u, hu⟩ := hV hz
  refine ⟨u, toBase_injective P ?_⟩
  exact (congrArg (fun f : U.val.toScheme ⟶ X ↦ f u) (ι_toBase P U)).trans hu

private lemma πBase_bijective (D : modulesPseudofunctor.DescentData (family P))
    (U : Index P) (V : X.Opens) (hV : V ≤ U.val.ι.opensRange) :
    Function.Bijective ((πBase P D U).app V) :=
  bijective_pushforward_composite_app (colimit.ι (diagram P) U) (toBase P) U.val.ι
    (ι_toBase P U) (obj P D U) (glueData P D).glued ((glueData P D).π U) V
      ((glueData P D).bijective_π_app (glueData_bijective P D)
        (preimage_le_colimit_opensRange P U V hV))

private lemma πBase_transition (D : modulesPseudofunctor.DescentData (family P))
    {U V : Index P} (h : U ⟶ V) :
    πBase P D V ≫ (Scheme.Modules.pushforward V.val.ι).map ((glueData P D).map h) ≫
      (Scheme.Modules.pushforwardComp ((diagram P).map h) V.val.ι).hom.app _ ≫
        (Scheme.Modules.pushforwardCongr (diagram_map_ι P h)).hom.app _ = πBase P D U := by
  exact pushforward_compatible (colimit.ι (diagram P) U) (colimit.ι (diagram P) V)
    (toBase P) ((diagram P).map h) U.val.ι V.val.ι (colimit.w (diagram P) h)
    (ι_toBase P U) (ι_toBase P V)
    (glueData P D).glued (obj P D U) (obj P D V)
    ((glueData P D).π U) ((glueData P D).π V) ((glueData P D).map h)
    (fun W s ↦ by
      exact ((glueData P D).transition_app_apply h W
        (((glueData P D).π V).app W s)).symm.trans
          ((glueData P D).transition_app_π_app h W s))

private def φBase (D : modulesPseudofunctor.DescentData (family P)) (U : Index P) :
    (Scheme.Modules.pullback U.val.ι).obj (gluedBase P D) ⟶ obj P D U :=
  ((Scheme.Modules.pullbackPushforwardAdjunction U.val.ι).homEquiv _ _).symm (πBase P D U)

private instance isIso_φBase (D : modulesPseudofunctor.DescentData (family P)) (U : Index P) :
    IsIso (φBase P D U) :=
  Scheme.Modules.isIso_pullbackPushforwardAdjunction_homEquiv_symm_of_bijective U.val.ι
    (gluedBase P D) (obj P D U) (πBase P D U)
    (πBase_bijective P D U)

private lemma φBase_comp (D : modulesPseudofunctor.DescentData (family P))
    {U V : Index P} (h : U ⟶ V) :
    φBase P D U =
      (Scheme.Modules.pullbackCongr (diagram_map_ι P h)).inv.app (gluedBase P D) ≫
        (Scheme.Modules.pullbackComp ((diagram P).map h) V.val.ι).inv.app (gluedBase P D) ≫
          (Scheme.Modules.pullback ((diagram P).map h)).map (φBase P D V) ≫
            pullbackHom (family P) D ((diagram P).map h) (diagram_map_ι P h) := by
  apply ((Scheme.Modules.pullbackPushforwardAdjunction U.val.ι).homEquiv _ _).injective
  rw [homEquiv_pullbackComp_congr]
  simp only [Adjunction.comp_homEquiv, Equiv.trans_apply]
  rw [Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_naturality_right]
  simp only [φBase, Equiv.apply_symm_apply]
  exact (πBase_transition P D h).symm

private lemma φBase_pullbackHom_comm (D : modulesPseudofunctor.DescentData (family P))
    {U V : Index P} (h : U ⟶ V) :
    (Scheme.Modules.pullback ((diagram P).map h)).map (φBase P D V) ≫
      pullbackHom (family P) D ((diagram P).map h) (diagram_map_ι P h) =
    pullbackHom (family P)
      (Pseudofunctor.DescentData.ofObj (F := modulesPseudofunctor) (gluedBase P D))
        ((diagram P).map h) (diagram_map_ι P h) ≫ φBase P D U := by
  -- Give cancellation a native module type before rewriting the Cat-valued datum presentation.
  have hcancel :
      (Scheme.Modules.pullback ((diagram P).map h)).map (φBase P D V) ≫
        pullbackHom (family P) D ((diagram P).map h) (diagram_map_ι P h) =
      ((Scheme.Modules.pullbackComp ((diagram P).map h) V.val.ι).hom.app (gluedBase P D) ≫
        (Scheme.Modules.pullbackCongr (diagram_map_ι P h)).hom.app (gluedBase P D)) ≫
          φBase P D U := by
    rw [φBase_comp P D h]
    simp only [Category.assoc, Iso.hom_inv_id_app_assoc]
  rw [pullbackHom_ofObj]
  exact hcancel

private def descentHom (D : modulesPseudofunctor.DescentData (family P)) :
    Pseudofunctor.DescentData.ofObj (F := modulesPseudofunctor) (f := family P)
      (gluedBase P D) ⟶ D := by
  apply homOfPullbackHom (family P) _ D (φBase P D)
  intro U V
  let W : Index P := ⟨U.val ⊓ V.val, P.lower inf_le_left U.property⟩
  let f : W ⟶ U := homOfLE (show U.val ⊓ V.val ≤ U.val from inf_le_left)
  let g : W ⟶ V := homOfLE (show U.val ⊓ V.val ≤ V.val from inf_le_right)
  exact ⟨W, (diagram P).map f, (diagram P).map g,
    diagram_map_ι P f, diagram_map_ι P g, isPullback_opens_inf U.val V.val,
    φBase_pullbackHom_comm P D f, φBase_pullbackHom_comm P D g⟩

private def localPullbackIso (D : modulesPseudofunctor.DescentData (family P)) (U : Index P) :
    (Scheme.Modules.pullback U.val.ι).obj (gluedBase P D) ≅ obj P D U := by
  have := isIso_φBase P D U
  exact asIso (φBase P D U)

private def descentIso (D : modulesPseudofunctor.DescentData (family P)) :
    Pseudofunctor.DescentData.ofObj (F := modulesPseudofunctor) (f := family P)
      (gluedBase P D) ≅ D :=
  Pseudofunctor.DescentData.isoMk
    (fun U ↦ localPullbackIso P D U)
    (fun {_} q {_ _} a b ha hb ↦ (descentHom P D).comm q a b ha hb)

private lemma isQuasicoherent_gluedBase (D : modulesPseudofunctor.DescentData (family P))
    (hD : ∀ U : Index P, (obj P D U).IsQuasicoherent)
    (hcover : iSup (fun U : Index P ↦ U.val) = (⊤ : X.Opens)) :
    (gluedBase P D).IsQuasicoherent := by
  apply ((gluedBase P D).isQuasicoherent_iff_of_iSup_eq_top (fun U : Index P ↦ U.val)
    hcover).2
  intro U
  have := isIso_φBase P D U
  exact (SheafOfModules.isQuasicoherent U.val.toScheme.ringCatSheaf).prop_of_iso
    (((Scheme.Modules.restrictFunctorIsoPullback U.val.ι).app (gluedBase P D)) ≪≫
      asIso (φBase P D U)).symm (hD U)

/-- Native module descent data with quasi-coherent objects on a covering lower set of open
subschemes are induced, compatibly with their comparison maps, by a quasi-coherent module. -/
theorem exists_module_descentIso
    (D : modulesPseudofunctor.DescentData
      (fun U : {U : X.Opens // U ∈ P} ↦ U.val.ι))
    (hD : ∀ U : {U : X.Opens // U ∈ P}, (D.obj U).IsQuasicoherent)
    (hcover : iSup (fun U : {U : X.Opens // U ∈ P} ↦ U.val) = (⊤ : X.Opens)) :
    ∃ M : X.Modules, M.IsQuasicoherent ∧
      Nonempty ((modulesPseudofunctor.toDescentData
        (fun U : {U : X.Opens // U ∈ P} ↦ U.val.ι)).obj M ≅ D) :=
  ⟨gluedBase P D, isQuasicoherent_gluedBase P D hD hcover, ⟨descentIso P D⟩⟩

/-- Quasi-coherent descent data on a covering lower set of open subschemes are effective. -/
theorem exists_quasicoherentSheaf_descentIso
    (D : qcohPseudofunctor.DescentData
      (fun U : {U : X.Opens // U ∈ P} ↦ U.val.ι))
    (hcover : iSup (fun U : {U : X.Opens // U ∈ P} ↦ U.val) = (⊤ : X.Opens)) :
    ∃ M : QuasicoherentSheaf X, Nonempty ((qcohPseudofunctor.toDescentData
      (fun U : {U : X.Opens // U ∈ P} ↦ U.val.ι)).obj M ≅ D) := by
  obtain ⟨M, hM, ⟨e⟩⟩ := exists_module_descentIso P (underlyingDatum (family P) D)
    (fun U ↦ (D.obj U).property) hcover
  exact ⟨⟨M, hM⟩, ⟨liftDatumIso (family P) D ⟨M, hM⟩ e⟩⟩

private def openCover
    (hcover : iSup (fun U : Index P ↦ U.val) = (⊤ : X.Opens)) : X.OpenCover :=
  Scheme.Cover.mkOfCovers (Index P) (fun U ↦ U.val.toScheme) (family P) (fun x ↦ by
    have hx : x ∈ ⨆ U : Index P, U.val := by rw [hcover]; trivial
    obtain ⟨U, hx⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
    exact ⟨U, ⟨x, hx⟩, rfl⟩)

/-- Restriction to a covering lower set of open subschemes is an equivalence with native
quasi-coherent descent data. -/
theorem isEquivalence_toDescentData_of_iSup_eq_top
    (hcover : iSup (fun U : {U : X.Opens // U ∈ P} ↦ U.val) = (⊤ : X.Opens)) :
    (qcohPseudofunctor.toDescentData
      (fun U : {U : X.Opens // U ∈ P} ↦ U.val.ι)).IsEquivalence := by
  have h := qcohPseudofunctor.fullyFaithfulToDescentData (family P)
    (Scheme.zariskiTopology_le_fpqcTopology X (openCover P hcover).mem_grothendieckTopology)
  have := h.full
  have := h.faithful
  have : (qcohPseudofunctor.toDescentData (family P)).EssSurj :=
    ⟨fun D ↦ exists_quasicoherentSheaf_descentIso P D hcover⟩
  exact { }

private def lowerOpens (R : Sieve X) : LowerSet X.Opens where
  carrier := {U | R U.ι}
  lower' := by
    intro U V hUV hV
    -- Membership in the carrier is the assertion that the open inclusion lies in the sieve.
    -- Here `hUV : V ≤ U`, so downward closure precomposes `U.ι` with `X.homOfLE hUV`.
    change R V.ι
    rw [← X.homOfLE_ι hUV]
    exact R.downward_closed hV (X.homOfLE hUV)

private lemma mem_lowerOpens (R : Sieve X) (U : X.Opens) :
    U ∈ lowerOpens R ↔ R U.ι := Iff.rfl

private lemma lowerOpens_cover (R : Sieve X) (hR : R ∈ Scheme.zariskiTopology X) :
    iSup (fun U : {U : X.Opens // U ∈ lowerOpens R} ↦ U.val) = ⊤ := by
  apply top_unique
  obtain ⟨𝒰, h𝒰⟩ := Scheme.exists_cover_of_mem_grothendieckTopology hR
  intro x _
  obtain ⟨i, y, hy⟩ := 𝒰.exists_eq x
  have : IsOpenImmersion (𝒰.f i) := 𝒰.map_prop i
  have hi : (𝒰.f i).opensRange ∈ lowerOpens R := by
    rw [mem_lowerOpens]
    simpa only [Scheme.Hom.isoOpensRange_inv_comp] using
      R.downward_closed (h𝒰 _ _ ⟨i⟩) (𝒰.f i).isoOpensRange.inv
  exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨_, hi⟩, ⟨y, hy⟩⟩

/-- The pseudofunctor of quasi-coherent sheaves is a stack for the Zariski topology. -/
instance isStack_zariskiTopology :
    qcohPseudofunctor.{u}.IsStack Scheme.zariskiTopology :=
  Pseudofunctor.IsStack.of_isStackFor fun X R hR ↦ by
    let P := lowerOpens R
    have hcover := lowerOpens_cover R hR
    have := isEquivalence_toDescentData_of_iSup_eq_top P hcover
    rw [Pseudofunctor.isStackFor_iff]
    apply Pseudofunctor.DescentData.isEquivalence_toDescentData_of_sieve_le qcohPseudofunctor
      (J := Scheme.fpqcTopology)
      (f' := family P)
      (Scheme.zariskiTopology_le_fpqcTopology X (openCover P hcover).mem_grothendieckTopology)
    rw [Sieve.ofArrows_category, Sieve.ofArrows, Sieve.generate_le_iff]
    rintro _ _ ⟨U⟩
    exact U.property

end ZariskiGlue

end

end TauCeti.AlgebraicGeometry.Descent
