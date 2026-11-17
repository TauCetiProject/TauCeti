/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.FormalScheme.Spf.Morphism
public import TauCeti.AlgebraicGeometry.FormalScheme.Spf.SectionsTopology

import TauCeti.Geometry.RingedSpace.PresheafedSpace.Basic

/-!
# Full faithfulness of `Spf` and automatic continuity

For complete separated adic rings `A`, `B` of finite ideal type, every `g : Spf B ⟶ Spf A` of
locally ringed spaces induces `sectionsHom g : A →+* B` via `topSectionsIso`. Naturality of residue
evaluation shows `g.base` pulls open primes back along `sectionsHom g`, giving automatic continuity
(`continuous_sectionsHom`), full faithfulness `homEquiv : (Spf B ⟶ Spf A) ≃ {φ // Continuous φ}`
(`map_sectionsHom`; EGA I, Ch. I, 10.2.2; Stacks Tag 0AHY), the induced homeomorphism
`isHomeomorph_isoToRingEquiv` for `Spf B ≅ Spf A`, and continuity on all open section rings for
`quotientSectionsTopology` (`continuous_c_app`).
-/

public section

open CategoryTheory TopologicalSpace Opposite AlgebraicGeometry

universe u

namespace TauCeti.FormalScheme.Spf

section ResidueEvaluation

variable {A : Type u} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [IsAdicRing A]

/-- The global sections of `Spf A` are canonically isomorphic to `A` (EGA I, Ch. I, 10.1.3). -/
noncomputable def topSectionsIso (A : Type u) [CommRing A] [TopologicalSpace A]
    [IsTopologicalRing A] [IsAdicRing A] : (Spf A).presheaf.obj (op ⊤) ≅ CommRingCat.of A :=
  have := (IsAdicRing.ideal_spec A).2.2; globalSectionsIso (IsAdicRing.ideal_spec A).2.1

/-- `topSectionsIso A` is a homeomorphism from `(Γ(⊤, O_{Spf A}), quotientSectionsTopology _ ⊤)`
onto `A` (EGA I, Ch. I, 10.1.3). -/
theorem isHomeomorph_topSectionsIso (A : Type u) [CommRing A] [TopologicalSpace A]
    [IsTopologicalRing A] [IsAdicRing A] :
    @IsHomeomorph _ _ (quotientSectionsTopology (IsAdicRing.ideal_spec A).2.1 ⊤)
      ‹TopologicalSpace A› (topSectionsIso A).hom :=
  by obtain ⟨-, h, _⟩ := IsAdicRing.ideal_spec A; exact isHomeomorph_globalSectionsIso h

/-- Restricting a global section of `Spf A` to `basicOpen a` corresponds under `topSectionsIso`
and `basicOpenSectionsIso` to `algebraMap A (CompletedAway A a)`. -/
@[reassoc] theorem algebraMap_comp_basicOpenSectionsIso_inv (a : A) :
    CommRingCat.ofHom (algebraMap A (AdicRing.CompletedAway A a)) ≫
        (basicOpenSectionsIso (IsAdicRing.ideal_spec A).2.1 (IsAdicRing.ideal_spec A).1 a).inv =
      (topSectionsIso A).inv ≫ (Spf A).presheaf.map (homOfLE (le_top : basicOpen a ≤ ⊤)).op := by
  have := (IsAdicRing.ideal_spec A).2.2; refine (Iso.comp_inv_eq _).mpr ?_
  -- `topSectionsIso` and `(Spf A).presheaf` unfold to `globalSectionsIso` and `structureSheaf`.
  erw [Category.assoc, globalSectionsIso_inv_comp_basicOpenSectionsIso_hom]

/-- Under `stalkResidueFieldEquiv`, evaluating the global section attached to `a ∈ A` at an open
prime `p` produces the image of `a` in `Frac(A ⧸ p)`. -/
theorem stalkResidueFieldEquiv_Γevaluation_topSectionsIso_inv (p : carrier A) (a : A) :
    stalkResidueFieldEquiv p ((Spf A).Γevaluation p ((topSectionsIso A).inv a)) =
      algebraMap (A ⧸ (p : PrimeSpectrum A).asIdeal)
        (FractionRing (A ⧸ (p : PrimeSpectrum A).asIdeal)) (Ideal.Quotient.mk _ a) := by
  have := (IsAdicRing.ideal_spec A).2.2
  let u : BasicNeighbourhood p :=
    ⟨1, by simpa using (Ideal.ne_top_iff_one _).mp (p : PrimeSpectrum A).isPrime.ne_top⟩
  have hsec : (basicOpenSectionsIso (IsAdicRing.ideal_spec A).2.1
        (IsAdicRing.ideal_spec A).1 u.elem).inv (algebraMap A _ a) =
      (Spf A).presheaf.map (homOfLE (le_top : basicOpen u.elem ≤ ⊤)).op
        ((topSectionsIso A).inv a) :=
    ConcreteCategory.congr_hom (algebraMap_comp_basicOpenSectionsIso_inv u.elem) a
  have hgerm := TopCat.Presheaf.germ_res_apply (Spf A).presheaf
    (homOfLE (le_top : basicOpen u.elem ≤ ⊤)) p (mem_basicOpen.mpr u.notMem)
    ((topSectionsIso A).inv a)
  -- Unfold `Γevaluation` to `residue ∘ germ` so `hgerm` applies.
  rw [← stalkResidueFieldEquiv_residue_germ u a, hsec]; erw [hgerm]; rfl

/-- The global section attached to `a ∈ A` vanishes in the residue field of `Spf A` at `p` if and
only if `a ∈ p`. -/
@[simp] theorem Γevaluation_topSectionsIso_inv_eq_zero_iff (p : carrier A) (a : A) :
    (Spf A).Γevaluation p ((topSectionsIso A).inv a) = 0 ↔ a ∈ (p : PrimeSpectrum A).asIdeal := by
  have : IsDomain (A ⧸ (p : PrimeSpectrum A).asIdeal) :=
    Ideal.Quotient.isDomain (p : PrimeSpectrum A).asIdeal
  rw [← (stalkResidueFieldEquiv p).map_eq_zero_iff,
    stalkResidueFieldEquiv_Γevaluation_topSectionsIso_inv,
    IsFractionRing.to_map_eq_zero_iff, Ideal.Quotient.eq_zero_iff_mem]

end ResidueEvaluation

section HomEquiv

variable {A B C : Type u} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [IsAdicRing A]
  [CommRing B] [TopologicalSpace B] [IsTopologicalRing B] [IsAdicRing B]
  [CommRing C] [TopologicalSpace C] [IsTopologicalRing C] [IsAdicRing C]

/-- The ring homomorphism `A →+* B` induced on global sections by a morphism of locally ringed
spaces `g : Spf B ⟶ Spf A`, read through `topSectionsIso`. -/
noncomputable def sectionsHom (g : Spf B ⟶ Spf A) : A →+* B :=
  ((topSectionsIso A).inv ≫
    (g.c.app (op ⊤) : (Spf A).presheaf.obj (op ⊤) ⟶ (Spf B).presheaf.obj (op ⊤)) ≫
    (topSectionsIso B).hom).hom

/-- Evaluation formula for `sectionsHom`. -/
theorem sectionsHom_apply (g : Spf B ⟶ Spf A) (a : A) :
    sectionsHom g a = (topSectionsIso B).hom (g.c.app (op ⊤) ((topSectionsIso A).inv a)) := (rfl)
/-- Categorical form of `sectionsHom`. -/
theorem ofHom_sectionsHom (g : Spf B ⟶ Spf A) :
    CommRingCat.ofHom (sectionsHom g) = (topSectionsIso A).inv ≫
      (g.c.app (op ⊤) : (Spf A).presheaf.obj (op ⊤) ⟶ (Spf B).presheaf.obj (op ⊤)) ≫
      (topSectionsIso B).hom := (rfl)

/-- `sectionsHom g` intertwines the global-section identifications of `Spf A` and `Spf B`. -/
@[reassoc] theorem topSectionsIso_inv_comp_c_app_top (g : Spf B ⟶ Spf A) :
    (topSectionsIso A).inv ≫
        (g.c.app (op ⊤) : (Spf A).presheaf.obj (op ⊤) ⟶ (Spf B).presheaf.obj (op ⊤)) =
      CommRingCat.ofHom (sectionsHom g) ≫ (topSectionsIso B).inv :=
  (cancel_mono (topSectionsIso B).hom).mp <| (Category.assoc _ _ _).trans (by simp [sectionsHom])

/-- Dual form of `topSectionsIso_inv_comp_c_app_top` with `(topSectionsIso _).hom`. -/
@[reassoc] theorem c_app_top_comp_topSectionsIso_hom (g : Spf B ⟶ Spf A) :
    (g.c.app (op ⊤) : (Spf A).presheaf.obj (op ⊤) ⟶ (Spf B).presheaf.obj (op ⊤)) ≫
        (topSectionsIso B).hom =
      (topSectionsIso A).hom ≫ CommRingCat.ofHom (sectionsHom g) :=
  (cancel_epi (topSectionsIso A).inv).mp (by simp [sectionsHom])

/-- Taking global sections of `Spf.map φ hφ` recovers `φ`. -/
@[simp] theorem sectionsHom_map (φ : A →+* B) (hφ : Continuous φ) :
    sectionsHom (map φ hφ) = φ := by
  have := (IsAdicRing.ideal_spec A).2.2; have := (IsAdicRing.ideal_spec B).2.2
  exact congrArg CommRingCat.Hom.hom <|
    (cancel_epi (globalSectionsIso (IsAdicRing.ideal_spec A).2.1).hom).mp
      ((c_app_top_comp_topSectionsIso_hom (map φ hφ)).symm.trans (map_globalSections φ hφ))

/-- On points, `g : Spf B ⟶ Spf A` pulls every open prime ideal of `B` back along
`sectionsHom g`. -/
@[simp] theorem mem_base_asIdeal_iff (g : Spf B ⟶ Spf A) (q : carrier B) (a : A) :
    a ∈ (g.base q).1.asIdeal ↔ sectionsHom g a ∈ q.1.asIdeal := by
  let q' : Spf B := q
  have hsec : (g.c.app (op ⊤) : (Spf A).presheaf.obj (op ⊤) ⟶ (Spf B).presheaf.obj (op ⊤))
      ((topSectionsIso A).inv a) = (topSectionsIso B).inv (sectionsHom g a) :=
    ConcreteCategory.congr_hom (topSectionsIso_inv_comp_c_app_top g) a
  have hval : (LocallyRingedSpace.residueFieldMap g q')
        ((Spf A).Γevaluation (g.base q') ((topSectionsIso A).inv a)) =
      (Spf B).Γevaluation q' ((topSectionsIso B).inv (sectionsHom g a)) :=
    (LocallyRingedSpace.Γevaluation_naturality_apply g q' _).trans
      (congrArg ((Spf B).Γevaluation q') hsec)
  rw [← Γevaluation_topSectionsIso_inv_eq_zero_iff (g.base q') a,
    ← Γevaluation_topSectionsIso_inv_eq_zero_iff q (sectionsHom g a),
    ← (LocallyRingedSpace.residueFieldMap g q').hom.map_eq_zero_iff]
  exact iff_of_eq (congrArg (· = 0) hval)

/-- **Automatic continuity** (EGA I, Ch. I, 10.2.2): the global-section homomorphism induced by any
morphism of locally ringed spaces `Spf B ⟶ Spf A` is continuous. -/
theorem continuous_sectionsHom (g : Spf B ⟶ Spf A) : Continuous (sectionsHom g) := by
  obtain ⟨hIAfg, hIA, -⟩ := IsAdicRing.ideal_spec A; obtain ⟨-, hIB, -⟩ := IsAdicRing.ideal_spec B
  refine hIA.continuous_of_map_le_radical hIB hIAfg (Ideal.map_le_iff_le_comap.mpr fun a ha ↦ ?_)
  rw [Ideal.mem_comap, Ideal.radical_eq_sInf, Ideal.mem_sInf]; rintro p ⟨hBp, hp⟩
  let q : carrier B := ⟨⟨p, hp⟩, (mem_carrier_iff_le hIB).mpr hBp⟩
  exact (mem_base_asIdeal_iff g q a).mp (((mem_carrier_iff_le hIA).mp (g.base q).2) ha)

/-- The underlying continuous map of `g : Spf B ⟶ Spf A` is `comap (sectionsHom g) _`. -/
theorem base_eq_comap_sectionsHom (g : Spf B ⟶ Spf A) :
    g.base = TopCat.ofHom (comap (sectionsHom g) (continuous_sectionsHom g)) := by
  apply ConcreteCategory.hom_ext; intro (q : carrier B); apply Subtype.ext; ext a
  exact (mem_base_asIdeal_iff g q a).trans <| by
    rw [← Ideal.mem_comap (f := sectionsHom g), ← PrimeSpectrum.comap_asIdeal,
      ← coe_comap_apply (sectionsHom g) (continuous_sectionsHom g) q]; rfl

private theorem base_eq_map_sectionsHom (g : Spf B ⟶ Spf A) :
    g.base = (map (sectionsHom g) (continuous_sectionsHom g)).base :=
  (base_eq_comap_sectionsHom g).trans (map_base _ _).symm

private theorem res_c_app_basicOpen_eq_map_sectionsHom (g : Spf B ⟶ Spf A) (a : A) :
    (Spf A).presheaf.map (homOfLE (le_top : basicOpen a ≤ ⊤)).op ≫
        (g.c.app (op (basicOpen a)) ≫
          (Spf B).presheaf.map (eqToHom (congrArg (fun f ↦ (Opens.map f).obj (basicOpen a))
            (base_eq_map_sectionsHom g).symm)).op) =
      (Spf A).presheaf.map (homOfLE (le_top : basicOpen a ≤ ⊤)).op ≫
        (map (sectionsHom g) (continuous_sectionsHom g)).c.app (op (basicOpen a)) := by
  obtain ⟨-, hIB, _⟩ := IsAdicRing.ideal_spec B
  let m := map (sectionsHom g) (continuous_sectionsHom g)
  have htop : (g.c.app (op ⊤) : (Spf A).presheaf.obj (op ⊤) ⟶ (Spf B).presheaf.obj (op ⊤)) =
      m.c.app (op ⊤) :=
    (cancel_mono (globalSectionsIso hIB).hom).mp <|
      (c_app_top_comp_topSectionsIso_hom g).trans (map_globalSections _ _).symm
  have hres :
      (Spf B).presheaf.map ((Opens.map g.base).map (homOfLE (le_top : basicOpen a ≤ ⊤))).op ≫
        (Spf B).presheaf.map (eqToHom (congrArg (fun f ↦ (Opens.map f).obj (basicOpen a))
          (base_eq_map_sectionsHom g).symm)).op =
      (Spf B).presheaf.map ((Opens.map m.base).map (homOfLE (le_top : basicOpen a ≤ ⊤))).op := by
    rw [← (Spf B).presheaf.map_comp]
    exact congrArg (Spf B).presheaf.map (Quiver.Hom.unop_inj (Subsingleton.elim _ _))
  -- Rewrite via `g.c.naturality`, `hres`, and `htop` (`erw` unfolds `pushforward` and `Spf`).
  erw [← Category.assoc, g.c.naturality (homOfLE (le_top : basicOpen a ≤ ⊤)).op,
    Category.assoc, hres, htop]
  exact (m.c.naturality (homOfLE le_top).op).symm

private theorem exists_pow_map_quotient_eq_bot_of_map (φ : A →+* B) (hφ : Continuous φ)
    (W : Opens (carrier B)) (n : ℕ) :
    ∃ k : ℕ, (IsAdicRing.ideal A ^ (k + 1)).map
      (((topSectionsIso A).inv ≫ (map φ hφ).c.app (op ⊤) ≫
        (Spf B).presheaf.map (homOfLE (le_top : W ≤ ⊤)).op ≫
        (quotientProjection (IsAdicRing.ideal_spec B).2.1 n).hom.app (op W)).hom) = ⊥ := by
  let hIA := (IsAdicRing.ideal_spec A).2.1; let hIB := (IsAdicRing.ideal_spec B).2.1
  have := (IsAdicRing.ideal_spec A).2.2; have := (IsAdicRing.ideal_spec B).2.2
  obtain ⟨k, hk⟩ := hIA.exists_pow_succ_le_comap (hIB.isOpen_pow (n + 1)) hφ
  refine ⟨k, (Ideal.map_eq_bot_iff_le_ker _).mpr fun r hr ↦ RingHom.mem_ker.mpr ?_⟩
  have htop : (topSectionsIso A).inv ≫ ((map φ hφ).c.app (op ⊤) :
        (Spf A).presheaf.obj (op ⊤) ⟶ (Spf B).presheaf.obj (op ⊤)) =
      CommRingCat.ofHom φ ≫ (topSectionsIso B).inv := by
    simpa only [sectionsHom_map] using topSectionsIso_inv_comp_c_app_top (map φ hφ)
  have hcomp : (topSectionsIso A).inv ≫ (map φ hφ).c.app (op ⊤) ≫
        (Spf B).presheaf.map (homOfLE (le_top : W ≤ ⊤)).op ≫
        (quotientProjection hIB n).hom.app (op W) =
      CommRingCat.ofHom ((Ideal.Quotient.mk (IsAdicRing.ideal B ^ (n + 1))).comp φ) ≫
        (quotientSheafGlobalSectionsIso (is_ideal_adic_pow hIB n.succ_pos)).inv ≫
        (quotientSheaf (is_ideal_adic_pow hIB n.succ_pos)).obj.map
          (homOfLE (le_top : W ≤ ⊤)).op := by
    -- Unfold `topSectionsIso`/`(Spf B).presheaf` to `globalSectionsIso`/`structureSheaf`.
    erw [← Category.assoc, htop, Category.assoc,
      (quotientProjection hIB n).hom.naturality (homOfLE (le_top : W ≤ ⊤)).op,
      globalSectionsIso_inv_comp_quotientProjection_assoc, ← Category.assoc,
      ← CommRingCat.ofHom_comp]
  rw [ConcreteCategory.congr_hom hcomp r, ConcreteCategory.comp_apply]
  have hzero : Ideal.Quotient.mk (IsAdicRing.ideal B ^ (n + 1)) (φ r) = 0 :=
    (Ideal.Quotient.eq_zero_iff_mem (I := IsAdicRing.ideal B ^ (n + 1))).mpr (hk hr)
  -- Unfold `CommRingCat.ofHom` application to match `hzero`.
  erw [hzero, map_zero]

private theorem c_app_basicOpen_eq_map_sectionsHom (g : Spf B ⟶ Spf A) (a : A) :
    g.c.app (op (basicOpen a)) ≫
        (Spf B).presheaf.map (eqToHom (congrArg (fun f ↦ (Opens.map f).obj (basicOpen a))
          (base_eq_map_sectionsHom g).symm)).op =
      (map (sectionsHom g) (continuous_sectionsHom g)).c.app (op (basicOpen a)) := by
  let hIAfg := (IsAdicRing.ideal_spec A).1; let hIA := (IsAdicRing.ideal_spec A).2.1
  let hIB := (IsAdicRing.ideal_spec B).2.1
  let φ := sectionsHom g; let hφ := continuous_sectionsHom g; let m := map φ hφ
  let W : Opens (carrier B) := (Opens.map m.base).obj (basicOpen a)
  let α := g.c.app (op (basicOpen a)) ≫ (Spf B).presheaf.map (eqToHom
    (congrArg (fun f ↦ (Opens.map f).obj (basicOpen a)) (base_eq_map_sectionsHom g).symm)).op
  refine (cancel_epi (basicOpenSectionsIso hIA hIAfg a).inv).mp ?_
  ext x; refine structureSheaf.sections_ext hIB fun n ↦ ?_
  let Rn := (quotientSheaf (is_ideal_adic_pow hIB n.succ_pos)).obj.obj (op W)
  let πn : (Spf B).presheaf.obj (op W) ⟶ Rn := (quotientProjection hIB n).hom.app (op W)
  let γ₁ := ((basicOpenSectionsIso hIA hIAfg a).inv ≫ α ≫ πn).hom
  let γ₂ := ((basicOpenSectionsIso hIA hIAfg a).inv ≫ m.c.app (op (basicOpen a)) ≫ πn).hom
  have hA : γ₁.comp (algebraMap A (AdicRing.CompletedAway A a)) =
      γ₂.comp (algebraMap A (AdicRing.CompletedAway A a)) := by
    have hres := reassoc_of% (res_c_app_basicOpen_eq_map_sectionsHom g a)
    have hcat : CommRingCat.ofHom (algebraMap A (AdicRing.CompletedAway A a)) ≫
          (basicOpenSectionsIso hIA hIAfg a).inv ≫ α ≫ πn =
        CommRingCat.ofHom (algebraMap A (AdicRing.CompletedAway A a)) ≫
          (basicOpenSectionsIso hIA hIAfg a).inv ≫ m.c.app (op (basicOpen a)) ≫ πn := by
      -- Unfold `(Spf A).presheaf` to `structureSheaf` for the next rewrite.
      erw [algebraMap_comp_basicOpenSectionsIso_inv_assoc a,
        algebraMap_comp_basicOpenSectionsIso_inv_assoc a, Category.assoc, Category.assoc, hres,
        Category.assoc]; rfl
    exact congrArg CommRingCat.Hom.hom hcat
  let _ : Algebra A Rn := (γ₂.comp (algebraMap A (AdicRing.CompletedAway A a))).toAlgebra
  let g₁ : AdicRing.CompletedAway A a →ₐ[A] Rn := ⟨γ₁, fun r ↦ congr($hA r)⟩
  let g₂ : AdicRing.CompletedAway A a →ₐ[A] Rn := ⟨γ₂, fun _ ↦ rfl⟩
  obtain ⟨k, hk⟩ := exists_pow_map_quotient_eq_bot_of_map φ hφ W n
  have halg : algebraMap A Rn = (((topSectionsIso A).inv ≫ m.c.app (op ⊤) ≫
      (Spf B).presheaf.map (homOfLE (le_top : W ≤ ⊤)).op ≫ πn).hom) := by
    have hnat := reassoc_of% (m.c.naturality (homOfLE (le_top : basicOpen a ≤ ⊤)).op)
    have hcat : CommRingCat.ofHom (algebraMap A (AdicRing.CompletedAway A a)) ≫
          (basicOpenSectionsIso hIA hIAfg a).inv ≫ m.c.app (op (basicOpen a)) ≫ πn =
        (topSectionsIso A).inv ≫ m.c.app (op ⊤) ≫
          (Spf B).presheaf.map (homOfLE (le_top : W ≤ ⊤)).op ≫ πn := by
      -- Unfold `(Spf A).presheaf` and `pushforward` for the next rewrite.
      erw [algebraMap_comp_basicOpenSectionsIso_inv_assoc a, Category.assoc, hnat]; rfl
    exact congrArg CommRingCat.Hom.hom hcat
  exact congr($(AdicRing.CompletedAway.algHom_ext_of_map_pow_eq_bot (halg.symm ▸ hk) g₁ g₂) x)

/-- Every morphism `g : Spf B ⟶ Spf A` of locally ringed spaces is `Spf.map` of its induced
continuous homomorphism on global sections (EGA I, Ch. I, 10.2.2; Stacks Tag 0AHY). -/
@[simp] theorem map_sectionsHom (g : Spf B ⟶ Spf A) :
    map (sectionsHom g) (continuous_sectionsHom g) = g := by
  symm; apply LocallyRingedSpace.Hom.ext'
  refine PresheafedSpace.Hom.ext _ _ (base_eq_map_sectionsHom g) ?_
  refine TopCat.Sheaf.hom_ext _ ((TopCat.Sheaf.pushforward CommRingCat
    (map (sectionsHom g) (continuous_sectionsHom g)).base).obj (Spf B).sheaf)
    isBasis_basicOpen fun a ↦ ?_
  rw [NatTrans.comp_app, ← c_app_basicOpen_eq_map_sectionsHom g a]
  exact congrArg (g.c.app (op (basicOpen a)) ≫ ·)
    (congrArg (Spf B).presheaf.map (Quiver.Hom.unop_inj (Subsingleton.elim _ _)))

/-- Two morphisms `Spf B ⟶ Spf A` with the same induced global-section homomorphism are equal. -/
theorem sectionsHom_injective : Function.Injective (sectionsHom (A := A) (B := B)) := by
  intro g₁ g₂ h; rw [← map_sectionsHom g₁, ← map_sectionsHom g₂]; congr 1

@[simp] theorem sectionsHom_id : sectionsHom (𝟙 (Spf A)) = RingHom.id A := by
  rw [← map_id, sectionsHom_map]
@[simp] theorem sectionsHom_comp (f : Spf C ⟶ Spf B) (g : Spf B ⟶ Spf A) :
    sectionsHom (f ≫ g) = (sectionsHom f).comp (sectionsHom g) := by
  conv_lhs => rw [← map_sectionsHom f, ← map_sectionsHom g, ← map_comp, sectionsHom_map]

/-- **Full faithfulness of `Spf`** (EGA I, Ch. I, 10.2.2; Stacks Tag 0AHY, eq. 87.2.0.1):
morphisms of locally ringed spaces `Spf B ⟶ Spf A` correspond bijectively to continuous ring
homomorphisms `A →+* B`. -/
noncomputable def homEquiv : (Spf B ⟶ Spf A) ≃ {φ : A →+* B // Continuous φ} where
  toFun g := ⟨sectionsHom g, continuous_sectionsHom g⟩
  invFun φ := map φ.1 φ.2
  left_inv := map_sectionsHom
  right_inv φ := Subtype.ext (sectionsHom_map φ.1 φ.2)

@[simp] theorem homEquiv_apply_coe (g : Spf B ⟶ Spf A) :
    (homEquiv g : A →+* B) = sectionsHom g := (rfl)
@[simp] theorem homEquiv_symm_apply (φ : {φ : A →+* B // Continuous φ}) :
    homEquiv.symm φ = map φ.1 φ.2 := (rfl)

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

/-- The ring isomorphism `A ≃+* B` induced by `Spf B ≅ Spf A` is a homeomorphism of topological
rings: both directions are induced by morphisms of formal spectra, hence are continuous. -/
theorem isHomeomorph_isoToRingEquiv (e : Spf B ≅ Spf A) : IsHomeomorph (isoToRingEquiv e) :=
  (Homeomorph.mk (isoToRingEquiv e).toEquiv
    (continuous_sectionsHom e.hom) (continuous_sectionsHom e.inv)).isHomeomorph

private theorem continuous_structureSheafMap_sectionsTopology (φ : A →+* B) (hφ : Continuous φ)
    (U : Opens (carrier A)) :
    let hIA := (IsAdicRing.ideal_spec A).2.1; let hIB := (IsAdicRing.ideal_spec B).2.1
    @Continuous _ _ (sectionsTopology hIA U)
      (sectionsTopology hIB ((Opens.map (TopCat.ofHom (comap φ hφ))).obj U))
      ((structureSheafMap φ hφ hIA hIB).hom.app (op U) :
        (structureSheaf hIA).obj.obj (op U) ⟶ _) := by
  intro hIA hIB
  let W := (Opens.map (TopCat.ofHom (comap φ hφ))).obj U; let _ := sectionsTopology hIA U
  refine (continuous_iff_sectionsTopology hIB W).mpr fun n ↦ ?_
  obtain ⟨m, hm⟩ := hIA.exists_pow_succ_le_comap (hIB.isOpen_pow (n + 1)) hφ
  have hN := is_ideal_adic_pow hIA m.succ_pos
  have hproj := congrArg (fun η ↦ η.hom.app (op U))
    (structureSheafMap_comp_quotientProjection φ hφ hIA hIB hN n hm)
  let _ : TopologicalSpace ((quotientSheaf (is_ideal_adic_pow hIB n.succ_pos)).obj.obj (op W)) := ⊥
  exact (@Continuous.comp _ _ _ (sectionsTopology hIA U) ⊥ ⊥ _ _ continuous_bot
    (continuous_toQuotientSheaf_app hIA hN U)).congr fun x ↦
      (ConcreteCategory.congr_hom hproj x).symm

private theorem continuous_structureSheafMap_quotientSectionsTopology (φ : A →+* B)
    (hφ : Continuous φ) (U : Opens (carrier A)) :
    let hIA := (IsAdicRing.ideal_spec A).2.1; let hIB := (IsAdicRing.ideal_spec B).2.1
    @Continuous _ _ (quotientSectionsTopology hIA U)
      (quotientSectionsTopology hIB ((Opens.map (TopCat.ofHom (comap φ hφ))).obj U))
      ((structureSheafMap φ hφ hIA hIB).hom.app (op U) :
        (structureSheaf hIA).obj.obj (op U) ⟶ _) := by
  intro hIA hIB; let fBase := TopCat.ofHom (comap φ hφ)
  let η : (structureSheaf hIA).obj ⟶ (TopCat.Presheaf.pushforward CommRingCat fBase).obj
      (structureSheaf hIB).obj := (structureSheafMap φ hφ hIA hIB).hom
  let _ := quotientSectionsTopology hIA U
  refine (continuous_iff_quotientSectionsTopology hIB _).mpr fun b hb ↦ ?_
  let V (i : { a : A // basicOpen a ≤ U }) : Opens (carrier B) := basicOpen (b * φ i.1)
  have hVle (i) : V i ≤ basicOpen b := by simp only [V, basicOpen_mul]; exact inf_le_left
  have hVcov : basicOpen b ≤ ⨆ i, V i := fun q hqb ↦ by
    obtain ⟨a, hqa, haU⟩ := exists_basicOpen_le (Opens.mem_map.mp (hb hqb))
    exact Opens.mem_iSup.mpr ⟨⟨a, haU⟩, by
      simp only [V, basicOpen_mul]; exact ⟨hqb, by rwa [← comap_basicOpen φ hφ a]⟩⟩
  let _ := quotientSectionsTopology hIB (basicOpen b)
  let _ (i) := quotientSectionsTopology hIB (V i)
  rw [← quotientSectionsTopology_basicOpen hIB b,
    (quotientSectionsTopology_glue hIB hVle hVcov).isInducing.continuous_iff, continuous_pi_iff]
  intro ⟨a, haU⟩; let _ := sectionsTopology hIA (basicOpen a)
  let _ := sectionsTopology hIB ((Opens.map fBase).obj (basicOpen a))
  have hVφ : V ⟨a, haU⟩ ≤ (Opens.map fBase).obj (basicOpen a) := by
    have hpre : (Opens.map fBase).obj (basicOpen a) = basicOpen (φ a) := comap_basicOpen φ hφ a
    rw [hpre]; simp only [V, basicOpen_mul]; exact inf_le_right
  have hc3 : @Continuous _ _ (sectionsTopology hIB ((Opens.map fBase).obj (basicOpen a)))
      (quotientSectionsTopology hIB (V ⟨a, haU⟩)) ((structureSheaf hIB).obj.map (homOfLE hVφ).op) :=
    (quotientSectionsTopology_basicOpen hIB _).symm ▸ sectionsTopology_restrict hIB hVφ
  have hhom : (homOfLE hb).op ≫ (homOfLE (hVle ⟨a, haU⟩)).op =
      ((Opens.map fBase).map (homOfLE haU)).op ≫ (homOfLE hVφ).op :=
    Quiver.Hom.unop_inj (Subsingleton.elim _ _)
  have hnat : (η.app (op U) : (structureSheaf hIA).obj.obj (op U) ⟶ _) ≫
        (structureSheaf hIB).obj.map (homOfLE hb).op ≫
        (structureSheaf hIB).obj.map (homOfLE (hVle ⟨a, haU⟩)).op =
      (structureSheaf hIA).obj.map (homOfLE haU).op ≫ (η.app (op (basicOpen a)) : _ ⟶ _) ≫
        (structureSheaf hIB).obj.map (homOfLE hVφ).op := by
    rw [← (structureSheaf hIB).obj.map_comp, hhom, (structureSheaf hIB).obj.map_comp,
      ← Category.assoc]
    exact congrArg (· ≫ _) (η.naturality (homOfLE haU).op).symm
  refine (hc3.comp ((continuous_structureSheafMap_sectionsTopology φ hφ (basicOpen a)).comp
    (continuous_restrict_basicOpen_sectionsTopology hIA haU))).congr fun x ↦
      (ConcreteCategory.congr_hom hnat x).symm

/-- Every morphism `g : Spf B ⟶ Spf A` is continuous on rings of sections over all opens `U`,
equipped with `quotientSectionsTopology` (EGA I, Ch. I, 10.2.2 and 10.4.5). -/
theorem continuous_c_app (g : Spf B ⟶ Spf A) (U : Opens (Spf A)) :
    @Continuous _ _ (quotientSectionsTopology (IsAdicRing.ideal_spec A).2.1 U)
      (quotientSectionsTopology (IsAdicRing.ideal_spec B).2.1 ((Opens.map g.base).obj U))
      ((g.c.app (op U) : (Spf A).presheaf.obj (op U) ⟶
        (Spf B).presheaf.obj (op ((Opens.map g.base).obj U)))) := by
  have heq : g.toHom = {
      base := TopCat.ofHom (comap (sectionsHom g) (continuous_sectionsHom g))
      c := (structureSheafMap (sectionsHom g) (continuous_sectionsHom g)
        (IsAdicRing.ideal_spec A).2.1 (IsAdicRing.ideal_spec B).2.1).hom } :=
    (congrArg LocallyRingedSpace.Hom.toHom (map_sectionsHom g).symm).trans (map_toHom _ _)
  generalize g.toHom = f at heq ⊢; subst heq
  exact continuous_structureSheafMap_quotientSectionsTopology (sectionsHom g)
    (continuous_sectionsHom g) U

end HomEquiv

end TauCeti.FormalScheme.Spf
