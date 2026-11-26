/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Filtered.Final
public import Mathlib.Topology.Sheaves.Functors
public import Mathlib.Topology.Sheaves.KSheaf
public import TauCeti.Topology.Sets.Compacts
public import TauCeti.Topology.Sheaves.KSheaf.Equivalence
public import TauCeti.Topology.Sheaves.KSheaf.Homotopy

/-!
# Pushforward of K-sheaves along proper maps

A K-presheaf on a space `X` (`TopCat.KPresheaf`) is a contravariant functor on the compact
subsets of `X`. A proper map `f : X ⟶ Y` pulls compact subsets of `Y` back to compact subsets of
`X` (`TopologicalSpace.Compacts.comap`), so a K-presheaf `P` on `X` pushes forward to the
K-presheaf `f_* P` on `Y` with

`(f_* P)(K) = P(f⁻¹(K))`

(`TopCat.KPresheaf.pushforward`). This file proves that pushforward preserves K-sheaves when `X`
and `Y` are Hausdorff and `Y` is locally compact (`TopCat.KPresheaf.IsKSheaf.pushforward`), which
is the K-sheaf case of Pardon's Lemma A.3.3. Taking preimages preserves `⊥`, `⊔` and `⊓`, so
the first two K-sheaf axioms for `f_* P` are those of `P` at the preimages. The third, that
`(f_* P)(K)` is the colimit of `(f_* P)(L)` over the compact neighbourhoods `L` of `K`, rests on
the preimages of these `L` being cofinal among the compact neighbourhoods of `f⁻¹(K)`
(`TopologicalSpace.Compacts.exists_comap_le_of_mem_compactNhds`).

Local compactness of `Y` is needed. In `ℚ` the compact set `{0}` has no compact neighbourhood,
so the third axiom at `{0}` asks for an initial object; but the inclusion `{0} → ℚ` is proper,
and the pushforward along it of a K-sheaf on the point takes its value at the point there.

Pushforward of K-sheaves is the functor `TopCat.KSheaf.pushforward`.

**Homotopy K-sheaves.** The same argument applies to K-presheaves of cochain complexes: the
pushforward of a homotopy K-sheaf (Pardon, Definition A.2.5) along a proper map is a homotopy
K-sheaf (`TopCat.KPresheaf.IsHomotopyKSheaf.pushforward`), which is the homotopy case of Pardon's
Lemma A.3.3. Its Mayer–Vietoris maps are those of `F` at the preimages, and a colimit of `F`
over the compact neighbourhoods of `f⁻¹(K)`, restricted along the cofinal preimages of the compact
neighbourhoods of `K`, is a colimit of `f_* F` with the same comparison map to `F(f⁻¹(K))`.

**Compatibility with the equivalence of sheaves and K-sheaves.** The K-presheaf
`TopCat.Presheaf.toKPresheaf` of a presheaf `P` takes `K` to the germs of `P` along `K`. For a
proper map `f`, the germs of `f_* P` along `K` are the germs of `P` along `f⁻¹(K)`
(`TopCat.Presheaf.toKPresheafPushforwardIso`): a closed map takes the complement of an open
neighbourhood `V` of `f⁻¹(K)` to a closed set missing `K`, so the preimages of the open
neighbourhoods of `K` are cofinal among the open neighbourhoods of `f⁻¹(K)`. This holds for every
presheaf, naturally (`TopCat.Presheaf.pushforwardToKPresheafFunctorIso`), with no separation
hypothesis. On locally compact Hausdorff spaces it says that pushforward of sheaves and pushforward
of K-sheaves correspond under the equivalence `TopCat.sheafEquivKSheaf`
(`TopCat.Sheaf.pushforwardSheafEquivKSheafFunctorIso`), which is Pardon's Definition A.3.4.

## References

* J. Pardon, *An algebraic approach to virtual fundamental cycles on moduli spaces of
  pseudo-holomorphic curves*, Geom. Topol. 20 (2016), Appendix A.3, Lemma A.3.3 and
  Definition A.3.4.
-/

@[expose] public section

universe w v u

open CategoryTheory Limits Opposite TopologicalSpace

namespace TopCat

variable {A : Type u} [Category.{v} A] {X Y : TopCat.{w}}

namespace KPresheaf

/-- The pushforward of K-presheaves along a proper map `f : X ⟶ Y`: the value of the pushforward
of `P` on a compact `K ⊆ Y` is the value of `P` on the compact preimage `f⁻¹(K)`. -/
def pushforward (f : X ⟶ Y) (hf : IsProperMap f) : KPresheaf A X ⥤ KPresheaf A Y :=
  (Functor.whiskeringLeft _ _ A).obj (Compacts.comap_mono f hf).functor.op

variable (f : X ⟶ Y) (hf : IsProperMap f)

@[simp]
lemma pushforward_obj_obj (P : KPresheaf A X) (K : (Compacts Y)ᵒᵖ) :
    ((pushforward f hf).obj P).obj K = P.obj (op (Compacts.comap f hf K.unop)) :=
  (rfl)

@[simp]
lemma pushforward_obj_map (P : KPresheaf A X) {K L : (Compacts Y)ᵒᵖ} (g : K ⟶ L) :
    ((pushforward f hf).obj P).map g =
      P.map (opHomOfLE (Compacts.comap_mono f hf (leOfHom g.unop))) :=
  (rfl)

@[simp]
lemma pushforward_map_app {P Q : KPresheaf A X} (φ : P ⟶ Q) (K : (Compacts Y)ᵒᵖ) :
    ((pushforward f hf).map φ).app K = φ.app (op (Compacts.comap f hf K.unop)) :=
  (rfl)

/-- The preimages under a proper map `f` of the compact neighbourhoods of `K`, as compact
neighbourhoods of `f⁻¹(K)`. -/
private def comapCompactNhds (K : Compacts Y) :
    K.compactNhds → (Compacts.comap f hf K).compactNhds :=
  fun L ↦ ⟨_, Compacts.comap_mem_compactNhds f hf L.property⟩

private lemma comapCompactNhds_mono (K : Compacts Y) : Monotone (comapCompactNhds f hf K) :=
  fun _ _ h ↦ Compacts.comap_mono f hf h

variable [T2Space X] [T2Space Y]

omit [T2Space X] in
/-- The preimages of the compact neighbourhoods of `K` are cofinal among the compact
neighbourhoods of `f⁻¹(K)`, so colimits over the latter restrict to colimits over the former. -/
private instance initial_comapCompactNhds [LocallyCompactSpace Y] (K : Compacts Y) :
    (comapCompactNhds_mono f hf K).functor.Initial := by
  rw [Monotone.initial_functor_iff]
  intro L'
  obtain ⟨L, hL, hle⟩ := Compacts.exists_comap_le_of_mem_compactNhds f hf L'.property
  exact ⟨⟨L, hL⟩, hle⟩

/-- **Pushforward along a proper map preserves K-sheaves** (Pardon, Lemma A.3.3). If `X` and
`Y` are Hausdorff, `Y` is locally compact and `P` is a K-sheaf on `X`, then its pushforward
`K ↦ P(f⁻¹(K))` along a proper map `f : X ⟶ Y` is a K-sheaf on `Y`. -/
theorem IsKSheaf.pushforward [LocallyCompactSpace Y] {P : KPresheaf A X} (hP : P.IsKSheaf) :
    ((KPresheaf.pushforward f hf).obj P).IsKSheaf where
  nonempty_isTerminal := by
    simpa only [pushforward_obj_obj, unop_op, Compacts.comap_bot] using hP.nonempty_isTerminal
  -- The square of the pushforward is, by definition, the square of `P` at the preimages.
  isPullback {K₁ K₂ K₃ K₄} h :=
    hP.isPullback (K₁ := Compacts.comap f hf K₁) (K₄ := Compacts.comap f hf K₄)
      ⟨by rw [← Compacts.comap_sup, h.sup_eq], by rw [← Compacts.comap_inf, h.inf_eq]⟩
  -- By definition of `pushforward`, the cocone of the pushforward at `K` is the cocone of `P` at
  -- `f⁻¹(K)` whiskered along `comapCompactNhds`.
  nonempty_isColimit_coconeOfCompacts K :=
    ⟨(Functor.Final.isColimitWhiskerEquiv (comapCompactNhds_mono f hf K).functor.op _).symm
      (hP.nonempty_isColimit_coconeOfCompacts _).some⟩

end KPresheaf

namespace KSheaf

variable [T2Space X] [T2Space Y] [LocallyCompactSpace Y]

/-- The pushforward of K-sheaves along a proper map `f : X ⟶ Y` of Hausdorff spaces with `Y`
locally compact: the K-sheaf `K ↦ P(f⁻¹(K))` (`TopCat.KPresheaf.IsKSheaf.pushforward`). -/
def pushforward (f : X ⟶ Y) (hf : IsProperMap f) : KSheaf A X ⥤ KSheaf A Y :=
  ObjectProperty.lift _ (ObjectProperty.ι _ ⋙ KPresheaf.pushforward f hf)
    fun P ↦ P.property.pushforward f hf

variable (f : X ⟶ Y) (hf : IsProperMap f)

@[simp]
lemma pushforward_obj_obj (P : KSheaf A X) :
    ((pushforward f hf).obj P).obj = (KPresheaf.pushforward f hf).obj P.obj :=
  (rfl)

@[simp]
lemma pushforward_map_hom {P Q : KSheaf A X} (φ : P ⟶ Q) :
    ((pushforward f hf).map φ).hom = (KPresheaf.pushforward f hf).map φ.hom :=
  (rfl)

end KSheaf

end TopCat

end

public section

universe w v u

open CategoryTheory Limits Opposite TopologicalSpace

namespace TopCat

namespace KPresheaf

variable {C : Type u} [Category.{v} C] [Abelian C] {X Y : TopCat.{w}} [T2Space X] [T2Space Y]
  (f : X ⟶ Y) (hf : IsProperMap f)

/-- **Pushforward along a proper map preserves homotopy K-sheaves** (Pardon, Lemma A.3.3). If `X`
and `Y` are Hausdorff, `Y` is locally compact and `F` is a homotopy K-sheaf of cochain complexes
on `X`, then its pushforward `K ↦ F(f⁻¹(K))` along a proper map `f : X ⟶ Y` is a homotopy
K-sheaf on `Y`. -/
theorem IsHomotopyKSheaf.pushforward [LocallyCompactSpace Y]
    {F : KPresheaf (CochainComplex C ℤ) X} (hF : F.IsHomotopyKSheaf) :
    ((KPresheaf.pushforward f hf).obj F).IsHomotopyKSheaf where
  acyclic_bot := by
    simpa only [pushforward_obj_obj, unop_op, Compacts.comap_bot] using hF.acyclic_bot
  quasiIso_mayerVietorisDesc {K₁ K₂ K₃ K₄} h := by
    have := hF.quasiIso_mayerVietorisDesc (K₁ := Compacts.comap f hf K₁)
      (K₂ := Compacts.comap f hf K₂) (K₃ := Compacts.comap f hf K₃)
      (K₄ := Compacts.comap f hf K₄)
      ⟨by rw [← Compacts.comap_sup, h.sup_eq], by rw [← Compacts.comap_inf, h.inf_eq]⟩
    -- The Mayer–Vietoris map of the pushforward is, by definition of `pushforward`, that of `F`
    -- at the preimages.
    rw [F.mayerVietorisDesc_eq_desc] at this
    rw [mayerVietorisDesc_eq_desc]
    exact this
  exists_isColimit_quasiIso_desc K := by
    obtain ⟨c, hc, _⟩ := hF.exists_isColimit_quasiIso_desc (Compacts.comap f hf K)
    -- Whiskered along the cofinal preimages of the compact neighbourhoods of `K`, the colimit `c`
    -- of `F` is a colimit of the pushforward. By definition of `pushforward`, the cocone of the
    -- pushforward at `K` is the cocone of `F` at `f⁻¹(K)` whiskered, so the two comparison maps
    -- agree.
    let hc' :=
      (Functor.Final.isColimitWhiskerEquiv (comapCompactNhds_mono f hf K).functor.op c).symm hc
    refine ⟨_, hc', ?_⟩
    rwa [← hc'.uniq (((KPresheaf.pushforward f hf).obj F).coconeOfCompacts K)
      (hc.desc (F.coconeOfCompacts (Compacts.comap f hf K))) fun L ↦ hc.fac _ _]

end KPresheaf

/-- Under a proper map `f`, the preimage of a compact set inside an open set `U` lies inside the
preimage of `U`. -/
theorem _root_.TopologicalSpace.Compacts.coe_comap_subset_map_obj {X Y : TopCat.{w}} (f : X ⟶ Y)
    (hf : IsProperMap f) {K : Compacts Y} {U : Opens Y} (h : (K : Set Y) ⊆ U) :
    (Compacts.comap f hf K : Set X) ⊆ (Opens.map f).obj U := by
  rw [Compacts.coe_comap, Opens.map_coe]
  exact Set.preimage_mono h

namespace Presheaf

variable {C : Type u} [Category.{v} C] [HasColimitsOfSize.{w, w} C] {X Y : TopCat.{w}}
  (f : X ⟶ Y) (hf : IsProperMap f)

/-- The preimages under a proper map `f` of the open neighbourhoods of `K`, as open
neighbourhoods of `f⁻¹(K)`. -/
private def comapOpenNhds (K : Compacts Y) :
    K.openNhds → (Compacts.comap f hf K).openNhds :=
  fun U ↦ ⟨(Opens.map f).obj U, Compacts.coe_comap_subset_map_obj f hf U.property⟩

private lemma comapOpenNhds_mono (K : Compacts Y) : Monotone (comapOpenNhds f hf K) :=
  fun _ _ h ↦ (Opens.map f).monotone h

/-- The preimages of the open neighbourhoods of `K` are cofinal among the open neighbourhoods of
`f⁻¹(K)`: since `f` is closed, an open neighbourhood `V` of `f⁻¹(K)` contains the preimage of the
open neighbourhood `Set.kernImage f V` of `K`. -/
private instance initial_comapOpenNhds (K : Compacts Y) :
    (comapOpenNhds_mono f hf K).functor.Initial := by
  rw [Monotone.initial_functor_iff]
  exact fun V ↦ ⟨⟨⟨Set.kernImage f V.val, isClosedMap_iff_kernImage.mp hf.isClosedMap V.val.isOpen⟩,
    Set.subset_kernImage_iff.mpr (Compacts.coe_comap f hf K ▸ V.property)⟩,
    Set.subset_kernImage_iff.mp subset_rfl⟩

/-- The comparison of the germs of `f_* P` along `K` with the germs of `P` along `f⁻¹(K)`: the
diagram of `f_* P` on the open neighbourhoods of `K` is, by definition of `pushforward`, that of
`P` on their preimages, which are cofinal among the open neighbourhoods of `f⁻¹(K)`, so the germs
of `P` along `f⁻¹(K)`, restricted to these preimages, are a colimit of it. -/
private noncomputable def toKPresheafPushforwardIsoApp (P : Presheaf C X) (K : Compacts Y) :
    ((pushforward C f).obj P).toKPresheaf.obj (op K) ≅
      P.toKPresheaf.obj (op (Compacts.comap f hf K)) :=
  ((pushforward C f).obj P).isColimitKGermCocone K |>.coconePointUniqueUpToIso <|
    (Functor.Final.isColimitWhiskerEquiv (comapOpenNhds_mono f hf K).functor.op _).symm
      (P.isColimitKGermCocone (Compacts.comap f hf K))

@[reassoc]
private lemma kGerm_toKPresheafPushforwardIsoApp_hom (P : Presheaf C X) (K : Compacts Y)
    (U : Opens Y) (h : (K : Set Y) ⊆ U) :
    kGerm ((pushforward C f).obj P) K U h ≫ (toKPresheafPushforwardIsoApp f hf P K).hom =
      P.kGerm (Compacts.comap f hf K) ((Opens.map f).obj U)
        (Compacts.coe_comap_subset_map_obj f hf h) :=
  IsColimit.comp_coconePointUniqueUpToIso_hom (((pushforward C f).obj P).isColimitKGermCocone K)
    ((Functor.Final.isColimitWhiskerEquiv (comapOpenNhds_mono f hf K).functor.op _).symm
      (P.isColimitKGermCocone (Compacts.comap f hf K))) (op (⟨U, h⟩ : ↥K.openNhds))

/-- **Germs of a pushforward along a proper map** (Pardon, Definition A.3.4). For a proper map
`f : X ⟶ Y`, the germs of the pushforward `f_* P` along a compact `K ⊆ Y` are the germs of `P`
along `f⁻¹(K)`: the K-presheaf of `f_* P` is the pushforward of the K-presheaf of `P`. -/
noncomputable def toKPresheafPushforwardIso (P : Presheaf C X) :
    ((pushforward C f).obj P).toKPresheaf ≅ (KPresheaf.pushforward f hf).obj P.toKPresheaf :=
  NatIso.ofComponents (fun K ↦ toKPresheafPushforwardIsoApp f hf P K.unop)
    -- both composites send the germ of a section of `f_* P` along `K` to its germ along `f⁻¹(L)`
    fun {K L} g ↦ toKPresheaf_hom_ext _ fun U hU ↦
      (kGerm_toKPresheaf_map_assoc _ g U hU _).trans <|
        (kGerm_toKPresheafPushforwardIsoApp_hom f hf P L.unop U _).trans <|
          (P.kGerm_toKPresheaf_map _ _ _).symm.trans
            (kGerm_toKPresheafPushforwardIsoApp_hom_assoc f hf P K.unop U hU _).symm

/-- `toKPresheafPushforwardIso` sends the germ along `K` of a section of `f_* P` over `U` to the
germ along `f⁻¹(K)` of the same section of `P` over `f⁻¹(U)`. -/
@[reassoc (attr := simp)]
theorem kGerm_toKPresheafPushforwardIso_hom_app (P : Presheaf C X) (K : Compacts Y) (U : Opens Y)
    (h : (K : Set Y) ⊆ U) :
    kGerm ((pushforward C f).obj P) K U h ≫ (P.toKPresheafPushforwardIso f hf).hom.app (op K) =
      P.kGerm (Compacts.comap f hf K) ((Opens.map f).obj U)
        (Compacts.coe_comap_subset_map_obj f hf h) :=
  kGerm_toKPresheafPushforwardIsoApp_hom f hf P K U h

/-- `(toKPresheafPushforwardIso f hf P).inv` sends the germ along `f⁻¹(K)` of a section of `P`
over the preimage of `U` to the germ along `K` of the same section of `f_* P`. -/
@[simp, reassoc]
theorem kGerm_toKPresheafPushforwardIso_inv_app (P : Presheaf C X) (K : Compacts Y) (U : Opens Y)
    (h : (K : Set Y) ⊆ U) :
    P.kGerm (Compacts.comap f hf K) ((Opens.map f).obj U)
          (Compacts.coe_comap_subset_map_obj f hf h) ≫
        (P.toKPresheafPushforwardIso f hf).inv.app (op K) =
      kGerm ((pushforward C f).obj P) K U h :=
  (Iso.comp_inv_eq ((P.toKPresheafPushforwardIso f hf).app (op K))).2
    (kGerm_toKPresheafPushforwardIso_hom_app f hf P K U h).symm

/-- **Pushforward commutes with taking K-presheaves.** For a proper map `f : X ⟶ Y`, taking
K-presheaves of presheaves pushed forward along `f` is, naturally, pushing forward their
K-presheaves along `f`. -/
noncomputable def pushforwardToKPresheafFunctorIso :
    pushforward C f ⋙ toKPresheafFunctor C Y ≅
      toKPresheafFunctor C X ⋙ KPresheaf.pushforward f hf :=
  NatIso.ofComponents (fun P ↦ P.toKPresheafPushforwardIso f hf) fun {P Q} φ ↦
    NatTrans.ext <| funext fun ⟨K⟩ ↦ toKPresheaf_hom_ext _ fun U hU ↦
      -- both composites send the germ of a section of `f_* P` along `K` to the germ of its image
      -- under `φ` along `f⁻¹(K)`
      (kGerm_toKPresheafMap_app_assoc _ K U hU _).trans <|
        (congrArg (_ ≫ ·) (kGerm_toKPresheafPushforwardIso_hom_app f hf Q K U hU)).trans <|
          (kGerm_toKPresheafMap_app φ _ _ _).symm.trans
            (kGerm_toKPresheafPushforwardIso_hom_app_assoc f hf P K U hU _).symm

@[simp]
theorem pushforwardToKPresheafFunctorIso_hom_app (P : Presheaf C X) :
    (pushforwardToKPresheafFunctorIso f hf).hom.app P = (P.toKPresheafPushforwardIso f hf).hom :=
  (rfl)

@[simp]
theorem pushforwardToKPresheafFunctorIso_inv_app (P : Presheaf C X) :
    (pushforwardToKPresheafFunctorIso f hf).inv.app P = (P.toKPresheafPushforwardIso f hf).inv :=
  (rfl)

end Presheaf

namespace Sheaf

variable {C : Type u} [Category.{v} C] [HasLimitsOfSize.{w, w} C] [HasColimitsOfSize.{w, w} C]
  {FC : C → C → Type*} {CC : C → Type w} [∀ X Y, FunLike (FC X Y) (CC X) (CC Y)]
  [ConcreteCategory C FC] [(CategoryTheory.forget C).ReflectsIsomorphisms]
  [PreservesLimitsOfSize.{w, w} (CategoryTheory.forget C)]
  [PreservesFilteredColimitsOfSize.{w, w} (CategoryTheory.forget C)] {X Y : TopCat.{w}}
  [T2Space X] [LocallyCompactSpace X] [T2Space Y] [LocallyCompactSpace Y]
  (f : X ⟶ Y) (hf : IsProperMap f)

/-- **Pushforward commutes with the equivalence of sheaves and K-sheaves** (Pardon,
Definition A.3.4). For a proper map `f : X ⟶ Y` of locally compact Hausdorff spaces, pushing a
sheaf forward along `f` and then taking its K-sheaf is, naturally, taking its K-sheaf and then
pushing that forward along `f`. -/
noncomputable def pushforwardSheafEquivKSheafFunctorIso :
    pushforward C f ⋙ (sheafEquivKSheaf C Y).functor ≅
      (sheafEquivKSheaf C X).functor ⋙ KSheaf.pushforward f hf :=
  NatIso.ofComponents
    (fun P ↦ ObjectProperty.isoMk _ (Presheaf.toKPresheafPushforwardIso f hf P.obj))
    fun φ ↦ ObjectProperty.hom_ext _
      ((Presheaf.pushforwardToKPresheafFunctorIso f hf).hom.naturality φ.hom)

@[simp]
theorem pushforwardSheafEquivKSheafFunctorIso_hom_app_hom (P : Sheaf C X) :
    ((pushforwardSheafEquivKSheafFunctorIso f hf).hom.app P).hom =
      (Presheaf.toKPresheafPushforwardIso f hf P.obj).hom :=
  (rfl)

@[simp]
theorem pushforwardSheafEquivKSheafFunctorIso_inv_app_hom (P : Sheaf C X) :
    ((pushforwardSheafEquivKSheafFunctorIso f hf).inv.app P).hom =
      (Presheaf.toKPresheafPushforwardIso f hf P.obj).inv :=
  (rfl)

end Sheaf

end TopCat
