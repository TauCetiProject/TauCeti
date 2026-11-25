/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.FormalScheme.Spf.Morphism
public import TauCeti.AlgebraicGeometry.FormalScheme.Spf.SectionsTopology
public import TauCeti.Topology.Category.TopCommRingCat.Adic

import TauCeti.Geometry.RingedSpace.PresheafedSpace.Basic
import TauCeti.Topology.Sheaves.Presheaf

/-!
# Full faithfulness of `Spf` and automatic continuity

For complete separated adic rings `A`, `B` of finite ideal type, every `g : Spf B ⟶ Spf A` of
locally ringed spaces induces `sectionsHom g : A →+* B` via `topSectionsIso`. Naturality of residue
evaluation shows `g.base` pulls open primes back along `sectionsHom g`, giving automatic continuity
(`continuous_sectionsHom`), full faithfulness `homEquiv : (Spf B ⟶ Spf A) ≃ {φ // Continuous φ}`
(`map_sectionsHom`, bundled as
`functor : (TopCommRingCat.isAdicRing.FullSubcategory)ᵒᵖ ⥤ LocallyRingedSpace` with
`fullyFaithfulFunctor`; EGA I, Ch. I, 10.2.2; Stacks Tag 0AHY), the induced homeomorphism
`isHomeomorph_isoToRingEquiv` for `Spf B ≅ Spf A` with round-trip laws (`isoToRingEquiv_mapIso`,
`mapIso_isoToRingEquiv`), and continuity on all open section rings for `quotientSectionsTopology`
(`continuous_c_app`).
-/

public section
open CategoryTheory TopologicalSpace Opposite AlgebraicGeometry
universe u
namespace TauCeti.FormalScheme.Spf

section HomEquiv

variable {A B C : Type u} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [IsAdicRing A]
  [CommRing B] [TopologicalSpace B] [IsTopologicalRing B] [IsAdicRing B]
  [CommRing C] [TopologicalSpace C] [IsTopologicalRing C] [IsAdicRing C]

/-- The ring homomorphism `A →+* B` induced on global sections by a morphism of locally ringed
spaces `g : Spf B ⟶ Spf A`, read through `topSectionsIso`. -/
noncomputable def sectionsHom (g : Spf B ⟶ Spf A) : A →+* B :=
  ((topSectionsIso A).inv ≫ (g.c.app (op ⊤) :
    (Spf A).presheaf.obj (op ⊤) ⟶ (Spf B).presheaf.obj (op ⊤)) ≫ (topSectionsIso B).hom).hom

/-- Evaluation formula for `sectionsHom`. -/
theorem sectionsHom_apply (g : Spf B ⟶ Spf A) (a : A) : sectionsHom g a =
    (topSectionsIso B).hom (g.c.app (op ⊤) ((topSectionsIso A).inv a)) := (rfl)
/-- Categorical form of `sectionsHom`. -/
theorem ofHom_sectionsHom (g : Spf B ⟶ Spf A) : CommRingCat.ofHom (sectionsHom g) =
    (topSectionsIso A).inv ≫ (g.c.app (op ⊤) :
      (Spf A).presheaf.obj (op ⊤) ⟶ (Spf B).presheaf.obj (op ⊤)) ≫ (topSectionsIso B).hom := (rfl)

/-- `sectionsHom g` intertwines the global-section identifications of `Spf A` and `Spf B`. -/
@[reassoc] theorem topSectionsIso_inv_comp_c_app_top (g : Spf B ⟶ Spf A) :
    (topSectionsIso A).inv ≫ (g.c.app (op ⊤) :
        (Spf A).presheaf.obj (op ⊤) ⟶ (Spf B).presheaf.obj (op ⊤)) =
      CommRingCat.ofHom (sectionsHom g) ≫ (topSectionsIso B).inv :=
  (cancel_mono (topSectionsIso B).hom).mp <| (Category.assoc _ _ _).trans (by simp [sectionsHom])

/-- Dual form of `topSectionsIso_inv_comp_c_app_top` with `(topSectionsIso _).hom`. -/
@[reassoc] theorem c_app_top_comp_topSectionsIso_hom (g : Spf B ⟶ Spf A) :
    (g.c.app (op ⊤) : (Spf A).presheaf.obj (op ⊤) ⟶ (Spf B).presheaf.obj (op ⊤)) ≫
        (topSectionsIso B).hom = (topSectionsIso A).hom ≫ CommRingCat.ofHom (sectionsHom g) :=
  (cancel_epi (topSectionsIso A).inv).mp (by simp [sectionsHom])

/-- Taking global sections of `Spf.map φ hφ` recovers `φ`. -/
@[simp] theorem sectionsHom_map (φ : A →+* B) (hφ : Continuous φ) :
    sectionsHom (map φ hφ) = φ := by
  have := (IsAdicRing.ideal_spec A).2.2; have := (IsAdicRing.ideal_spec B).2.2
  have h := c_app_top_comp_topSectionsIso_hom (map φ hφ)
  rw [topSectionsIso_def A, topSectionsIso_def B] at h
  exact congrArg CommRingCat.Hom.hom <|
    (cancel_epi (globalSectionsIso (IsAdicRing.ideal_spec A).2.1).hom).mp
      (h.symm.trans (map_globalSections φ hφ))

/-- On points, `g : Spf B ⟶ Spf A` pulls every open prime ideal of `B` back along
`sectionsHom g`. -/
@[simp] theorem mem_base_asIdeal_iff (g : Spf B ⟶ Spf A) (q : carrier B) (a : A) :
    a ∈ (g.base q).val.asIdeal ↔ sectionsHom g a ∈ q.val.asIdeal := by
  let q' : Spf B := q
  have hval : (LocallyRingedSpace.residueFieldMap g q')
        ((Spf A).Γevaluation (g.base q') ((topSectionsIso A).inv a)) =
      (Spf B).Γevaluation q' ((topSectionsIso B).inv (sectionsHom g a)) :=
    (LocallyRingedSpace.Γevaluation_naturality_apply g q' _).trans <| congrArg _ <|
      ConcreteCategory.congr_hom (topSectionsIso_inv_comp_c_app_top g) a
  rw [← Γevaluation_topSectionsIso_inv_eq_zero_iff (g.base q') a,
    ← Γevaluation_topSectionsIso_inv_eq_zero_iff q' (sectionsHom g a),
    ← (LocallyRingedSpace.residueFieldMap g q').hom.map_eq_zero_iff]
  exact (congrArg (· = 0) hval).to_iff

/-- **Automatic continuity** (EGA I, Ch. I, 10.2.2): the global-section homomorphism induced by any
morphism of locally ringed spaces `Spf B ⟶ Spf A` is continuous. -/
theorem continuous_sectionsHom (g : Spf B ⟶ Spf A) : Continuous (sectionsHom g) := by
  obtain ⟨hIAfg, hIA, -⟩ := IsAdicRing.ideal_spec A; obtain ⟨-, hIB, -⟩ := IsAdicRing.ideal_spec B
  refine hIA.continuous_of_map_le_radical hIB hIAfg (Ideal.map_le_iff_le_comap.mpr fun a ha ↦ ?_)
  rw [Ideal.mem_comap, Ideal.radical_eq_sInf, Ideal.mem_sInf]; rintro p ⟨hBp, hp⟩
  exact (mem_base_asIdeal_iff g ⟨⟨p, hp⟩, (mem_carrier_iff_le hIB).mpr hBp⟩ a).mp
    (((mem_carrier_iff_le hIA).mp (g.base ⟨⟨p, hp⟩, (mem_carrier_iff_le hIB).mpr hBp⟩).property) ha)

/-- The underlying continuous map of `g : Spf B ⟶ Spf A` is `comap (sectionsHom g) _`. -/
theorem base_eq_comap_sectionsHom (g : Spf B ⟶ Spf A) :
    g.base = TopCat.ofHom (comap (sectionsHom g) (continuous_sectionsHom g)) :=
  ConcreteCategory.hom_ext _ _ fun q ↦ Subtype.ext <| PrimeSpectrum.ext <| SetLike.ext fun a ↦
    (mem_base_asIdeal_iff g q a).trans <| by
      rw [← Ideal.mem_comap (f := sectionsHom g), ← PrimeSpectrum.comap_asIdeal,
        ← coe_comap_apply (sectionsHom g) (continuous_sectionsHom g) q]
      -- `(Spf B).toTopCat` is definitionally `TopCat.of (carrier B)` and `TopCat.ofHom` applies
      -- definitionally as `comap _ _ q`, preventing `TopCat.ofHom_apply` from rewriting directly.
      rfl

private theorem base_eq_map_sectionsHom (g : Spf B ⟶ Spf A) :
    g.base = (map (sectionsHom g) (continuous_sectionsHom g)).base :=
  (base_eq_comap_sectionsHom g).trans (map_base _ _).symm

private theorem c_app_top_eq_map_sectionsHom (g : Spf B ⟶ Spf A) :
    (g.c.app (op ⊤) : (Spf A).presheaf.obj (op ⊤) ⟶ (Spf B).presheaf.obj (op ⊤)) =
      (map (sectionsHom g) (continuous_sectionsHom g)).c.app (op ⊤) :=
  (cancel_mono (topSectionsIso B).hom).mp <|
    (c_app_top_comp_topSectionsIso_hom g).trans <|
      (congrArg ((topSectionsIso A).hom ≫ CommRingCat.ofHom ·)
        (sectionsHom_map _ _).symm).trans
      (c_app_top_comp_topSectionsIso_hom (map (sectionsHom g) (continuous_sectionsHom g))).symm

private theorem appLE_top (k : Spf B ⟶ Spf A) (W : Opens (Spf B))
    (hle : W ≤ (Opens.map k.base).obj (⊤ : Opens (Spf A)) := fun _ _ ↦ trivial) :
    k.toHom.appLE (⊤ : Opens (Spf A)) W hle =
      (k.c.app (op ⊤) : (Spf A).presheaf.obj (op ⊤) ⟶ (Spf B).presheaf.obj (op ⊤)) ≫
        (Spf B).presheaf.map (homOfLE (le_top : W ≤ ⊤)).op :=
  (PresheafedSpace.Hom.appLE_def k.toHom _ _ _).trans <|
    congrArg (_ ≫ (Spf B).presheaf.map ·) (Quiver.Hom.unop_inj (Subsingleton.elim _ _))

@[reassoc]
private theorem algebraMap_comp_basicOpenSectionsIso_inv_comp_appLE (k : Spf B ⟶ Spf A) (a : A)
    (W : Opens (Spf B))
    (hW : W ≤ (Opens.map k.base).obj (basicOpen a : Opens (Spf A))) :
    CommRingCat.ofHom (algebraMap A (AdicRing.CompletedAway A a)) ≫
        (basicOpenSectionsIso (IsAdicRing.ideal_spec A).2.1 (IsAdicRing.ideal_spec A).1 a).inv ≫
          k.toHom.appLE (basicOpen a : Opens (Spf A)) W hW =
      (topSectionsIso A).inv ≫
        k.toHom.appLE (⊤ : Opens (Spf A)) W (fun _ _ ↦ trivial) :=
  (Category.assoc _ _ _).symm.trans <|
    (congrArg (· ≫ k.toHom.appLE _ W hW) (algebraMap_comp_basicOpenSectionsIso_inv a)).trans <|
    (Category.assoc _ _ _).trans <|
    congrArg ((topSectionsIso A).inv ≫ ·) (PresheafedSpace.Hom.map_appLE k.toHom hW _)

private theorem topSectionsIso_inv_comp_res_comp_quotientProjection (W : Opens (Spf B)) (n : ℕ) :
    let hIB := (IsAdicRing.ideal_spec B).2.1
    (topSectionsIso B).inv ≫ (Spf B).presheaf.map (homOfLE (le_top : W ≤ ⊤)).op ≫
        (quotientProjection hIB n).hom.app (op W) =
      CommRingCat.ofHom (Ideal.Quotient.mk (IsAdicRing.ideal B ^ (n + 1))) ≫
        (quotientSheafGlobalSectionsIso (is_ideal_adic_pow hIB n.succ_pos)).inv ≫
        (quotientSheaf (is_ideal_adic_pow hIB n.succ_pos)).obj.map
          (homOfLE (le_top : W ≤ ⊤)).op := by
  intro hIB
  have := (IsAdicRing.ideal_spec B).2.2
  let W' : Opens (carrier B) := ⟨W.carrier, W.is_open'⟩
  have hnat : ((quotientProjection hIB n).hom.app (op ⊤) :
        (structureSheaf hIB).obj.obj (op ⊤) ⟶ _) ≫
        (quotientSheaf (is_ideal_adic_pow hIB n.succ_pos)).obj.map
          (homOfLE (le_top : W' ≤ ⊤)).op =
      (structureSheaf hIB).obj.map (homOfLE (le_top : W' ≤ ⊤)).op ≫
        (quotientProjection hIB n).hom.app (op W') :=
    ((quotientProjection hIB n).hom.naturality (homOfLE (le_top : W' ≤ ⊤)).op).symm
  have hgs : (globalSectionsIso hIB).inv ≫
        (structureSheaf hIB).obj.map (homOfLE (le_top : W' ≤ ⊤)).op ≫
        (quotientProjection hIB n).hom.app (op W') =
      CommRingCat.ofHom (Ideal.Quotient.mk (IsAdicRing.ideal B ^ (n + 1))) ≫
        (quotientSheafGlobalSectionsIso (is_ideal_adic_pow hIB n.succ_pos)).inv ≫
        (quotientSheaf (is_ideal_adic_pow hIB n.succ_pos)).obj.map
          (homOfLE (le_top : W' ≤ ⊤)).op := by
    rw [← hnat, ← Category.assoc, globalSectionsIso_inv_comp_quotientProjection, Category.assoc]
  exact (congrArg (·.inv ≫ _) (topSectionsIso_def B)).trans hgs

private theorem topSectionsIso_inv_comp_map_appLE_comp_quotientProjection (φ : A →+* B)
    (hφ : Continuous φ) (W : Opens (Spf B)) (n : ℕ) :
    let hIB := (IsAdicRing.ideal_spec B).2.1
    (topSectionsIso A).inv ≫
        (map φ hφ).toHom.appLE (⊤ : Opens (Spf A)) W (fun _ _ ↦ trivial) ≫
        (quotientProjection hIB n).hom.app (op W) =
      CommRingCat.ofHom ((Ideal.Quotient.mk (IsAdicRing.ideal B ^ (n + 1))).comp φ) ≫
        (quotientSheafGlobalSectionsIso (is_ideal_adic_pow hIB n.succ_pos)).inv ≫
        (quotientSheaf (is_ideal_adic_pow hIB n.succ_pos)).obj.map
          (homOfLE (le_top : W ≤ ⊤)).op := by
  intro hIB
  have h1 : (topSectionsIso A).inv ≫
        (map φ hφ).toHom.appLE (⊤ : Opens (Spf A)) W (fun _ _ ↦ trivial) ≫
        (quotientProjection hIB n).hom.app (op W) =
      ((topSectionsIso A).inv ≫ ((map φ hφ).c.app (op ⊤) : _ ⟶ _)) ≫
        (Spf B).presheaf.map (homOfLE (le_top : W ≤ ⊤)).op ≫
        (quotientProjection hIB n).hom.app (op W) :=
    (congrArg ((topSectionsIso A).inv ≫ ·)
      (congrArg (· ≫ (quotientProjection hIB n).hom.app (op W)) (appLE_top (map φ hφ) W))).trans <|
      (congrArg ((topSectionsIso A).inv ≫ ·) (Category.assoc _ _ _)).trans
        (Category.assoc _ _ _).symm
  have h2 : ((topSectionsIso A).inv ≫ ((map φ hφ).c.app (op ⊤) :
          (Spf A).presheaf.obj (op ⊤) ⟶ (Spf B).presheaf.obj (op ⊤))) ≫
        (Spf B).presheaf.map (homOfLE (le_top : W ≤ ⊤)).op ≫
        (quotientProjection hIB n).hom.app (op W) =
      CommRingCat.ofHom φ ≫ (topSectionsIso B).inv ≫
        (Spf B).presheaf.map (homOfLE (le_top : W ≤ ⊤)).op ≫
        (quotientProjection hIB n).hom.app (op W) :=
    (congrArg (· ≫ _) ((topSectionsIso_inv_comp_c_app_top (map φ hφ)).trans
      (congrArg (· ≫ _) (congrArg CommRingCat.ofHom (sectionsHom_map φ hφ))))).trans
      (Category.assoc _ _ _)
  exact h1.trans <| h2.trans <|
    (congrArg (CommRingCat.ofHom φ ≫ ·)
      (topSectionsIso_inv_comp_res_comp_quotientProjection W n)).trans <|
    (Category.assoc _ _ _).symm.trans <| congrArg (· ≫ _) (CommRingCat.ofHom_comp _ _).symm

private theorem exists_pow_map_quotient_eq_bot_of_map (φ : A →+* B) (hφ : Continuous φ)
    (W : Opens (Spf B)) (n : ℕ) :
    ∃ k : ℕ, (IsAdicRing.ideal A ^ (k + 1)).map (((topSectionsIso A).inv ≫
      (map φ hφ).toHom.appLE (⊤ : Opens (Spf A)) W (fun _ _ ↦ trivial) ≫
      (quotientProjection (IsAdicRing.ideal_spec B).2.1 n).hom.app (op W)).hom) = ⊥ := by
  let hIA := (IsAdicRing.ideal_spec A).2.1; let hIB := (IsAdicRing.ideal_spec B).2.1
  obtain ⟨k, hk⟩ := hIA.exists_pow_succ_le_comap (hIB.isOpen_pow (n + 1)) hφ
  refine ⟨k, (Ideal.map_eq_bot_iff_le_ker _).mpr fun r hr ↦ RingHom.mem_ker.mpr ?_⟩
  let W' : Opens (Spf.carrier B) := ⟨W.carrier, W.is_open'⟩
  have hcomp := congrArg (fun m : CommRingCat.of A ⟶ _ ↦ m.hom r)
    (topSectionsIso_inv_comp_map_appLE_comp_quotientProjection φ hφ W n)
  have hrhs : (CommRingCat.ofHom ((Ideal.Quotient.mk (IsAdicRing.ideal B ^ (n + 1))).comp φ) ≫
      (quotientSheafGlobalSectionsIso (is_ideal_adic_pow hIB n.succ_pos)).inv ≫
      (quotientSheaf (is_ideal_adic_pow hIB n.succ_pos)).obj.map
        (homOfLE (le_top : W' ≤ ⊤)).op).hom r = 0 := by
    simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom,
      (Ideal.Quotient.eq_zero_iff_mem (I := IsAdicRing.ideal B ^ (n + 1))).mpr (hk hr),
      map_zero]
  exact hcomp.trans hrhs

private theorem algebraMap_comp_basicOpenSectionsIso_inv_comp_quotientProjection
    (m k : Spf B ⟶ Spf A) (a : A) (W : Opens (Spf B))
    (hWk : W ≤ (Opens.map k.base).obj (basicOpen a : Opens (Spf A)))
    (htop : (k.c.app (op ⊤) : (Spf A).presheaf.obj (op ⊤) ⟶ (Spf B).presheaf.obj (op ⊤)) =
      m.c.app (op ⊤)) (n : ℕ) :
    ((basicOpenSectionsIso (IsAdicRing.ideal_spec A).2.1 (IsAdicRing.ideal_spec A).1 a).inv ≫
        k.toHom.appLE (basicOpen a : Opens (Spf A)) W hWk ≫
        (quotientProjection (IsAdicRing.ideal_spec B).2.1 n).hom.app (op W)).hom.comp
        (algebraMap A (AdicRing.CompletedAway A a)) =
      ((topSectionsIso A).inv ≫
        m.toHom.appLE (⊤ : Opens (Spf A)) W (fun _ _ ↦ trivial) ≫
        (quotientProjection (IsAdicRing.ideal_spec B).2.1 n).hom.app (op W)).hom := by
  let hIB := (IsAdicRing.ideal_spec B).2.1
  let πn : (Spf B).presheaf.obj (op W) ⟶
      (quotientSheaf (is_ideal_adic_pow hIB n.succ_pos)).obj.obj (op W) :=
    (quotientProjection hIB n).hom.app (op W)
  have h1 : CommRingCat.ofHom (algebraMap A (AdicRing.CompletedAway A a)) ≫
      (basicOpenSectionsIso (IsAdicRing.ideal_spec A).2.1 (IsAdicRing.ideal_spec A).1 a).inv ≫
        k.toHom.appLE (basicOpen a : Opens (Spf A)) W hWk =
      (topSectionsIso A).inv ≫ m.toHom.appLE (⊤ : Opens (Spf A)) W (fun _ _ ↦ trivial) := by
    rw [algebraMap_comp_basicOpenSectionsIso_inv_comp_appLE, appLE_top, appLE_top]
    exact congrArg (fun f : (Spf A).presheaf.obj (op ⊤) ⟶ (Spf B).presheaf.obj (op ⊤) ↦
      (topSectionsIso A).inv ≫ f ≫ (Spf B).presheaf.map (homOfLE (le_top : W ≤ ⊤)).op) htop
  rw [← CommRingCat.hom_ofHom (algebraMap A (AdicRing.CompletedAway A a)), ← CommRingCat.hom_comp]
  refine congrArg CommRingCat.Hom.hom ?_
  have h2 := congrArg (· ≫ πn) h1
  simp only [Category.assoc] at h2; exact h2

private theorem c_app_basicOpen_eq_map_sectionsHom (g : Spf B ⟶ Spf A) (a : A) :
    g.c.app (op (basicOpen a)) ≫ (Spf B).presheaf.map (eqToHom
        (congrArg (fun f ↦ (Opens.map f).obj (basicOpen a)) (base_eq_map_sectionsHom g).symm)).op =
      (map (sectionsHom g) (continuous_sectionsHom g)).c.app (op (basicOpen a)) := by
  let φ := sectionsHom g; let hφ := continuous_sectionsHom g; let m := map φ hφ
  let U : Opens (Spf A) := basicOpen a
  let W : Opens (Spf B) := (Opens.map m.base).obj U
  have hWg : W ≤ (Opens.map g.base).obj U :=
    (congrArg (fun f ↦ (Opens.map f).obj U) (base_eq_map_sectionsHom g).symm).le
  have happ : g.toHom.appLE U W hWg = m.toHom.appLE U W le_rfl := by
    -- Cancel `basicOpenSectionsIso` and reduce to each quotient thickening `B ⧸ J ^ (n + 1)`
    -- via `structureSheaf.sections_ext`; both candidates agree on `A`, and a power of the ideal
    -- of definition of `A` maps to `0`, so `algHom_ext_of_map_pow_eq_bot` applies.
    refine (cancel_epi (basicOpenSectionsIso (IsAdicRing.ideal_spec A).2.1
      (IsAdicRing.ideal_spec A).1 a).inv).mp ?_
    ext x
    refine structureSheaf.sections_ext (IsAdicRing.ideal_spec B).2.1 fun n ↦ ?_
    let hIB := (IsAdicRing.ideal_spec B).2.1
    let Rn := (quotientSheaf (is_ideal_adic_pow hIB n.succ_pos)).obj.obj (op W)
    let πn : (Spf B).presheaf.obj (op W) ⟶ Rn := (quotientProjection hIB n).hom.app (op W)
    let bIso := (basicOpenSectionsIso (IsAdicRing.ideal_spec A).2.1
      (IsAdicRing.ideal_spec A).1 a).inv
    let γ₁ := (bIso ≫ g.toHom.appLE U W hWg ≫ πn).hom
    let γ₂ := (bIso ≫ m.toHom.appLE U W le_rfl ≫ πn).hom
    have hA₁ := algebraMap_comp_basicOpenSectionsIso_inv_comp_quotientProjection m g a W hWg
      (c_app_top_eq_map_sectionsHom g) n
    have hA₂ :=
      algebraMap_comp_basicOpenSectionsIso_inv_comp_quotientProjection m m a W le_rfl rfl n
    let _ : Algebra A Rn := (γ₂.comp (algebraMap A (AdicRing.CompletedAway A a))).toAlgebra
    obtain ⟨k, hk⟩ := exists_pow_map_quotient_eq_bot_of_map φ hφ W n
    exact congr($(AdicRing.CompletedAway.algHom_ext_of_map_pow_eq_bot (hA₂ ▸ hk)
      (⟨γ₁, fun r ↦ congr($(hA₁.trans hA₂.symm) r)⟩ : _ →ₐ[A] Rn) ⟨γ₂, fun _ ↦ rfl⟩) x)
  exact ((congrArg (g.c.app (op U) ≫ (Spf B).presheaf.map ·)
    (Quiver.Hom.unop_inj (Subsingleton.elim _ _))).trans <|
    (PresheafedSpace.Hom.appLE_def g.toHom U W hWg).symm.trans happ).trans
    (PresheafedSpace.Hom.appLE_eq_app m.toHom U)

/-- Every morphism `g : Spf B ⟶ Spf A` of locally ringed spaces is `Spf.map` of its induced
continuous homomorphism on global sections (EGA I, Ch. I, 10.2.2; Stacks Tag 0AHY). -/
@[simp] theorem map_sectionsHom (g : Spf B ⟶ Spf A) :
    map (sectionsHom g) (continuous_sectionsHom g) = g :=
  (LocallyRingedSpace.Hom.ext' <| PresheafedSpace.Hom.ext _ _ (base_eq_map_sectionsHom g) <|
    TopCat.Sheaf.hom_ext _ ((TopCat.Sheaf.pushforward CommRingCat
      (map (sectionsHom g) (continuous_sectionsHom g)).base).obj (Spf B).sheaf)
    isBasis_basicOpen fun a ↦ by
      rw [NatTrans.comp_app, ← c_app_basicOpen_eq_map_sectionsHom g a]
      exact congrArg (g.c.app (op (basicOpen a)) ≫ ·) (congrArg (Spf B).presheaf.map
        (Quiver.Hom.unop_inj (Subsingleton.elim _ _)))).symm

/-- Two morphisms `Spf B ⟶ Spf A` with the same induced global-section homomorphism are equal. -/
theorem sectionsHom_injective : Function.Injective (sectionsHom (A := A) (B := B)) := by
  intro g₁ g₂ h
  rw [← map_sectionsHom g₁, ← map_sectionsHom g₂]
  congr 1
@[simp] theorem sectionsHom_id : sectionsHom (𝟙 (Spf A)) = RingHom.id A := by
  rw [← map_id, sectionsHom_map]
@[simp] theorem sectionsHom_comp (f : Spf C ⟶ Spf B) (g : Spf B ⟶ Spf A) :
    sectionsHom (f ≫ g) = (sectionsHom f).comp (sectionsHom g) := by
  conv_lhs => rw [← map_sectionsHom f, ← map_sectionsHom g, ← map_comp, sectionsHom_map]

/-- **Full faithfulness of `Spf`** (EGA I, Ch. I, 10.2.2; Stacks Tag 0AHY, eq. 87.2.0.1):
morphisms of locally ringed spaces `Spf B ⟶ Spf A` correspond bijectively to continuous ring
homomorphisms `A →+* B`. -/
noncomputable def homEquiv : (Spf B ⟶ Spf A) ≃ {φ : A →+* B // Continuous φ} where
  toFun g := ⟨sectionsHom g, continuous_sectionsHom g⟩; invFun φ := map φ.val φ.property
  left_inv := map_sectionsHom; right_inv φ := Subtype.ext (sectionsHom_map φ.val φ.property)

@[simp] theorem homEquiv_apply_coe (g : Spf B ⟶ Spf A) :
    (homEquiv g : A →+* B) = sectionsHom g := (rfl)
@[simp] theorem homEquiv_symm_apply (φ : {φ : A →+* B // Continuous φ}) :
    homEquiv.symm φ = map φ.val φ.property := (rfl)

/-- `Spf` as a contravariant functor from complete separated adic rings of finite ideal type
(`TopCommRingCat.isAdicRing.FullSubcategory`) to locally ringed spaces (EGA I, Ch. I, 10.2.2). -/
-- Expose so `functor.obj R` reduces to `Spf R.unop.obj` in the exported type of `functor_map`.
@[expose] noncomputable def functor :
    (TopCommRingCat.isAdicRing.{u}.FullSubcategory)ᵒᵖ ⥤ LocallyRingedSpace.{u} where
  obj R := Spf R.unop.obj; map φ := map φ.unop.hom.val φ.unop.hom.property
  map_id _ := map_id; map_comp _ _ := map_comp _ _ _ _

@[simp] theorem functor_obj (R : (TopCommRingCat.isAdicRing.{u}.FullSubcategory)ᵒᵖ) :
    functor.obj R = Spf R.unop.obj := (rfl)
@[simp] theorem functor_map {R S : (TopCommRingCat.isAdicRing.{u}.FullSubcategory)ᵒᵖ}
    (φ : R ⟶ S) :
    functor.map φ = map φ.unop.hom.val φ.unop.hom.property := (rfl)

/-- `Spf.functor` is fully faithful (EGA I, Ch. I, 10.2.2; Stacks Tag 0AHY). -/
noncomputable def fullyFaithfulFunctor : functor.{u}.FullyFaithful where
  preimage f := (ObjectProperty.homMk (homEquiv (f : Spf _ ⟶ Spf _))).op
  map_preimage f := by rw [functor_map]; exact map_sectionsHom _
  preimage_map _ := Quiver.Hom.unop_inj <| ObjectProperty.hom_ext _ <| Subtype.ext (by simp)

instance : functor.{u}.Full := fullyFaithfulFunctor.full
instance : functor.{u}.Faithful := fullyFaithfulFunctor.faithful

/-- Every isomorphism `Spf B ≅ Spf A` of locally ringed spaces induces a ring isomorphism
`A ≃+* B` on global sections. -/
noncomputable def isoToRingEquiv (e : Spf B ≅ Spf A) : A ≃+* B :=
  { sectionsHom e.hom with
    invFun := sectionsHom e.inv
    left_inv a := by simpa [e.inv_hom_id] using (congr($(sectionsHom_comp e.inv e.hom) a)).symm
    right_inv b := by simpa [e.hom_inv_id] using (congr($(sectionsHom_comp e.hom e.inv) b)).symm }

@[simp] theorem isoToRingEquiv_toRingHom (e : Spf B ≅ Spf A) :
    (isoToRingEquiv e : A →+* B) = sectionsHom e.hom := (rfl)
@[simp] theorem isoToRingEquiv_apply (e : Spf B ≅ Spf A) (a : A) :
    isoToRingEquiv e a = sectionsHom e.hom a := (rfl)
@[simp] theorem isoToRingEquiv_symm (e : Spf B ≅ Spf A) :
    (isoToRingEquiv e).symm = isoToRingEquiv e.symm := by ext; rfl
@[simp] theorem isoToRingEquiv_mapIso (e : A ≃+* B) (h₁ : Continuous e)
    (h₂ : Continuous e.symm) : isoToRingEquiv (mapIso e h₁ h₂) = e := RingEquiv.ext fun _ ↦ by simp
@[simp] theorem mapIso_isoToRingEquiv (e : Spf B ≅ Spf A) (h₁ : Continuous (isoToRingEquiv e))
    (h₂ : Continuous (isoToRingEquiv e).symm) : mapIso (isoToRingEquiv e) h₁ h₂ = e :=
  Iso.ext (by simp [mapIso_hom])

/-- The ring isomorphism `A ≃+* B` induced by `Spf B ≅ Spf A` is a homeomorphism of topological
rings: both directions are induced by morphisms of formal spectra, hence are continuous. -/
theorem isHomeomorph_isoToRingEquiv (e : Spf B ≅ Spf A) : IsHomeomorph (isoToRingEquiv e) :=
  (Homeomorph.mk (isoToRingEquiv e).toEquiv
    (continuous_sectionsHom e.hom) (continuous_sectionsHom e.inv)).isHomeomorph

/-- Every morphism `g : Spf B ⟶ Spf A` is continuous on rings of sections over all opens `U`,
equipped with `quotientSectionsTopology` (EGA I, Ch. I, 10.2.2 and 10.4.5). -/
theorem continuous_c_app (g : Spf B ⟶ Spf A) (U : Opens (Spf A)) :
    @Continuous _ _ (quotientSectionsTopology (IsAdicRing.ideal_spec A).2.1 U)
      (quotientSectionsTopology (IsAdicRing.ideal_spec B).2.1 ((Opens.map g.base).obj U))
      ((g.c.app (op U) : (Spf A).presheaf.obj (op U) ⟶
        (Spf B).presheaf.obj (op ((Opens.map g.base).obj U)))) := by
  have heq : g.toHom = ⟨TopCat.ofHom (comap (sectionsHom g) (continuous_sectionsHom g)),
      (structureSheafMap _ _ (IsAdicRing.ideal_spec A).2.1 (IsAdicRing.ideal_spec B).2.1).hom⟩ :=
    (congrArg LocallyRingedSpace.Hom.toHom (map_sectionsHom g).symm).trans (map_toHom _ _)
  generalize g.toHom = f at heq ⊢; subst heq
  exact continuous_structureSheafMap_quotientSectionsTopology _ (continuous_sectionsHom g)
    (IsAdicRing.ideal_spec A).2.1 (IsAdicRing.ideal_spec B).2.1 U
end HomEquiv
end TauCeti.FormalScheme.Spf
