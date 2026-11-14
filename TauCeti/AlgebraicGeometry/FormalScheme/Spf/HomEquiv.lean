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

For complete separated adic rings `A` and `B` of finite ideal type, every morphism
`g : Spf B ⟶ Spf A` of locally ringed spaces induces `sectionsHom g : A →+* B` on global sections.
Naturality of residue evaluation shows `g.base` pulls open primes back along `sectionsHom g`, so
`sectionsHom g` maps `IsAdicRing.ideal A` into the radical of `IsAdicRing.ideal B` and is
automatically continuous (EGA I, Ch. I, 10.2.2; Stacks Tag 0AHY). Projecting basic-open sections
to thickenings and applying `TauCeti.AdicRing.CompletedAway.algHom_ext_of_map_pow_eq_bot` yields
`g = Spf.map (sectionsHom g) _`.

## Main definitions

* `TauCeti.FormalScheme.Spf.topSectionsIso`: `(Spf A).presheaf.obj (op ⊤) ≅ CommRingCat.of A`.
* `TauCeti.FormalScheme.Spf.sectionsHom`: the homomorphism `A →+* B` induced by `Spf B ⟶ Spf A`.
* `TauCeti.FormalScheme.Spf.homEquiv`: `(Spf B ⟶ Spf A) ≃ {φ : A →+* B // Continuous φ}`.
* `TauCeti.FormalScheme.Spf.mapIso`, `TauCeti.FormalScheme.Spf.isoToRingEquiv`: equivalence of
  isomorphisms `Spf B ≅ Spf A` and topological ring isomorphisms `A ≃+* B`.

## Main results

* `TauCeti.FormalScheme.Spf.homEquiv_pow`,
  `TauCeti.FormalScheme.Spf.continuous_iff_exists_pos_pow_map_le`: power criterion for continuity.
* `TauCeti.FormalScheme.Spf.continuous_sectionsHom`, `TauCeti.FormalScheme.Spf.map_sectionsHom`:
  automatic continuity and full faithfulness of `Spf`.
* `TauCeti.FormalScheme.Spf.isHomeomorph_isoToRingEquiv`,
  `TauCeti.FormalScheme.Spf.continuous_c_app`: topological ring classification of `Spf B ≅ Spf A`
  and continuity on `quotientSectionsTopology`.
-/

public section

open CategoryTheory TopologicalSpace Opposite AlgebraicGeometry

universe u

namespace TauCeti.FormalScheme.Spf

section ContinuityCriterion

variable {A B : Type*} [CommRing A] [CommRing B] {I : Ideal A} {J : Ideal B}

/-- If `I` is finitely generated, `φ(I) ⊆ √J` holds if and only if `φ(I ^ k) ⊆ J` for some
positive integer `k`. -/
theorem map_le_radical_iff_exists_pos_pow_map_le (hIfg : I.FG) {φ : A →+* B} :
    I.map φ ≤ J.radical ↔ ∃ k > 0, (I ^ k).map φ ≤ J := by
  refine ⟨fun h ↦ ?_, fun ⟨k, _, hk⟩ x hx ↦ ⟨k, hk (Ideal.map_pow φ I k ▸ Ideal.pow_mem_pow hx k)⟩⟩
  obtain ⟨k, hk⟩ := Ideal.exists_pow_le_of_le_radical_of_fg h (hIfg.map φ)
  rw [← Ideal.map_pow] at hk
  rcases Nat.eq_zero_or_pos k with rfl | hkpos
  · exact ⟨1, Nat.one_pos,
      (Ideal.map_mono le_top).trans (by simpa [pow_zero, Ideal.one_eq_top] using hk)⟩
  · exact ⟨k, hkpos, hk⟩

variable [TopologicalSpace A] [TopologicalSpace B]

/-- For a finitely generated ideal of definition `I` of `A` and an ideal of definition `J` of `B`,
a ring homomorphism `φ : A →+* B` is continuous if and only if `(I ^ k).map φ ≤ J` for some `k > 0`
(EGA I, Ch. 0, 7.1.3–7.1.4; Ch. I, 10.2.2). -/
theorem continuous_iff_exists_pos_pow_map_le (hI : IsAdic I) (hIfg : I.FG) (hJ : IsAdic J)
    {φ : A →+* B} : Continuous φ ↔ ∃ k > 0, (I ^ k).map φ ≤ J :=
  (hI.continuous_iff_map_le_radical hJ hI hIfg).trans
    (map_le_radical_iff_exists_pos_pow_map_le hIfg)

/-- Continuity of `φ : A →+* B` is equivalent to `I.map φ ≤ J.radical`, which in turn is equivalent
to `(I ^ k).map φ ≤ J` for some positive integer `k` (EGA I, Ch. I, 10.2.2). -/
theorem homEquiv_pow (hI : IsAdic I) (hIfg : I.FG) (hJ : IsAdic J) (φ : A →+* B) :
    (Continuous φ ↔ I.map φ ≤ J.radical) ∧ (I.map φ ≤ J.radical ↔ ∃ k > 0, (I ^ k).map φ ≤ J) :=
  ⟨hI.continuous_iff_map_le_radical hJ hI hIfg, map_le_radical_iff_exists_pos_pow_map_le hIfg⟩

end ContinuityCriterion

section ResidueEvaluation

variable {A : Type u} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [IsAdicRing A]

/-- The global sections of `Spf A` are canonically isomorphic to `A` (EGA I, Ch. I, 10.1.3). -/
noncomputable def topSectionsIso (A : Type u) [CommRing A] [TopologicalSpace A]
    [IsTopologicalRing A] [IsAdicRing A] : (Spf A).presheaf.obj (op ⊤) ≅ CommRingCat.of A :=
  have := (IsAdicRing.ideal_spec A).2.2
  globalSectionsIso (IsAdicRing.ideal_spec A).2.1

/-- `topSectionsIso A` is a homeomorphism from `(Γ(⊤, O_{Spf A}), quotientSectionsTopology _ ⊤)`
onto `A` (EGA I, Ch. I, 10.1.3). -/
theorem isHomeomorph_topSectionsIso (A : Type u) [CommRing A] [TopologicalSpace A]
    [IsTopologicalRing A] [IsAdicRing A] :
    @IsHomeomorph _ _ (quotientSectionsTopology (IsAdicRing.ideal_spec A).2.1 ⊤)
      ‹TopologicalSpace A› (topSectionsIso A).hom :=
  have := (IsAdicRing.ideal_spec A).2.2
  isHomeomorph_globalSectionsIso (IsAdicRing.ideal_spec A).2.1

private theorem algebraMap_comp_basicOpenSectionsIso_inv (a : A) :
    have := (IsAdicRing.ideal_spec A).2.2
    CommRingCat.ofHom (algebraMap A (AdicRing.CompletedAway A a)) ≫
        (basicOpenSectionsIso (IsAdicRing.ideal_spec A).2.1 (IsAdicRing.ideal_spec A).1 a).inv =
      (topSectionsIso A).inv ≫ (Spf A).presheaf.map (homOfLE (le_top : basicOpen a ≤ ⊤)).op :=
  have := (IsAdicRing.ideal_spec A).2.2
  (Iso.comp_inv_eq _).mpr ((Category.assoc _ _ _).symm.trans
    (globalSectionsIso_inv_comp_basicOpenSectionsIso_hom _ _ a)).symm

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
  exact (congrArg (fun z ↦ stalkResidueFieldEquiv p ((Spf A).residue p z))
    (hgerm.symm.trans (congrArg _ hsec.symm))).trans (stalkResidueFieldEquiv_residue_germ u a)

/-- The global section attached to `a ∈ A` vanishes in the residue field of `Spf A` at `p` if and
only if `a ∈ p`. -/
@[simp]
theorem Γevaluation_topSectionsIso_inv_eq_zero_iff (p : carrier A) (a : A) :
    (Spf A).Γevaluation p ((topSectionsIso A).inv a) = 0 ↔
      a ∈ (p : PrimeSpectrum A).asIdeal := by
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

/-- `sectionsHom g` intertwines the global-section identifications of `Spf A` and `Spf B`. -/
@[reassoc]
theorem globalSectionsIso_inv_comp_c_app_top (g : Spf B ⟶ Spf A) :
    (topSectionsIso A).inv ≫
        (g.c.app (op ⊤) : (Spf A).presheaf.obj (op ⊤) ⟶ (Spf B).presheaf.obj (op ⊤)) =
      CommRingCat.ofHom (sectionsHom g) ≫ (topSectionsIso B).inv :=
  (cancel_mono (topSectionsIso B).hom).mp <| (Category.assoc _ _ _).trans (by simp [sectionsHom])

/-- Dual form of `globalSectionsIso_inv_comp_c_app_top` with `(topSectionsIso _).hom`. -/
@[reassoc]
theorem c_app_top_comp_globalSectionsIso_hom (g : Spf B ⟶ Spf A) :
    (g.c.app (op ⊤) : (Spf A).presheaf.obj (op ⊤) ⟶ (Spf B).presheaf.obj (op ⊤)) ≫
        (topSectionsIso B).hom =
      (topSectionsIso A).hom ≫ CommRingCat.ofHom (sectionsHom g) :=
  (cancel_epi (topSectionsIso A).inv).mp (by simp [sectionsHom])

/-- Taking global sections of `Spf.map φ hφ` recovers `φ`. -/
@[simp]
theorem sectionsHom_map (φ : A →+* B) (hφ : Continuous φ) : sectionsHom (map φ hφ) = φ := by
  have := (IsAdicRing.ideal_spec A).2.2; have := (IsAdicRing.ideal_spec B).2.2
  exact congrArg CommRingCat.Hom.hom <|
    (cancel_epi (globalSectionsIso (IsAdicRing.ideal_spec A).2.1).hom).mp
      ((c_app_top_comp_globalSectionsIso_hom (map φ hφ)).symm.trans (map_globalSections φ hφ))

/-- On points, `g : Spf B ⟶ Spf A` pulls every open prime ideal of `B` back along
`sectionsHom g`. -/
@[simp]
theorem mem_base_asIdeal_iff (g : Spf B ⟶ Spf A) (q : carrier B) (a : A) :
    a ∈ (g.base q).1.asIdeal ↔ sectionsHom g a ∈ q.1.asIdeal := by
  let q' : Spf B := q
  have hnat : LocallyRingedSpace.residueFieldMap g q'
        ((Spf A).Γevaluation (g.base q') ((topSectionsIso A).inv a)) =
      (Spf B).Γevaluation q' ((topSectionsIso B).inv (sectionsHom g a)) :=
    (LocallyRingedSpace.Γevaluation_naturality_apply g q' _).trans
      (congrArg ((Spf B).Γevaluation q')
        (ConcreteCategory.congr_hom (globalSectionsIso_inv_comp_c_app_top g) a))
  exact (Γevaluation_topSectionsIso_inv_eq_zero_iff (g.base q') a).symm.trans <|
    (((LocallyRingedSpace.residueFieldMap g q').hom.map_eq_zero_iff).symm.trans
      (congrArg (· = 0) hnat).to_iff).trans
      (Γevaluation_topSectionsIso_inv_eq_zero_iff q (sectionsHom g a))

/-- **Automatic continuity** (EGA I, Ch. I, 10.2.2): the global-section homomorphism induced by any
morphism of locally ringed spaces `Spf B ⟶ Spf A` is continuous. -/
theorem continuous_sectionsHom (g : Spf B ⟶ Spf A) : Continuous (sectionsHom g) := by
  obtain ⟨hIAfg, hIA, -⟩ := IsAdicRing.ideal_spec A
  obtain ⟨-, hIB, -⟩ := IsAdicRing.ideal_spec B
  refine hIA.continuous_of_map_le_radical hIB hIAfg (Ideal.map_le_iff_le_comap.mpr fun a ha ↦ ?_)
  rw [Ideal.mem_comap, Ideal.radical_eq_sInf, Ideal.mem_sInf]
  rintro p ⟨hBp, hp⟩
  let q : carrier B := ⟨⟨p, hp⟩, (mem_carrier_iff_le hIB).mpr hBp⟩
  exact (mem_base_asIdeal_iff g q a).mp (((mem_carrier_iff_le hIA).mp (g.base q).2) ha)

/-- The underlying continuous map of `g : Spf B ⟶ Spf A` is `comap (sectionsHom g) _`. -/
theorem base_eq_comap_sectionsHom (g : Spf B ⟶ Spf A) :
    g.base = TopCat.ofHom (comap (sectionsHom g) (continuous_sectionsHom g)) := by
  apply ConcreteCategory.hom_ext; intro q; apply Subtype.ext
  have hcoe := coe_comap_apply (sectionsHom g) (continuous_sectionsHom g) q
  ext a
  exact (mem_base_asIdeal_iff g q a).trans (by
    change sectionsHom g a ∈ q.1.asIdeal ↔
      a ∈ (comap (sectionsHom g) (continuous_sectionsHom g) q : PrimeSpectrum A).asIdeal
    rw [hcoe]; rfl)

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
  let eqW := eqToHom (congrArg (fun f ↦ (Opens.map f).obj (basicOpen a))
    (base_eq_map_sectionsHom g).symm)
  have htop : (g.c.app (op ⊤) : (Spf A).presheaf.obj (op ⊤) ⟶ (Spf B).presheaf.obj (op ⊤)) =
      m.c.app (op ⊤) :=
    (cancel_mono (globalSectionsIso hIB).hom).mp <|
      (c_app_top_comp_globalSectionsIso_hom g).trans (map_globalSections _ _).symm
  have hmap : ((TopCat.Presheaf.pushforward CommRingCat g.base).obj (Spf B).presheaf).map
        (homOfLE (le_top : basicOpen a ≤ ⊤)).op ≫ (Spf B).presheaf.map eqW.op =
      (Spf B).presheaf.map (homOfLE (le_top : (Opens.map m.base).obj (basicOpen a) ≤ ⊤)).op :=
    ((Spf B).presheaf.map_comp _ _).symm.trans
      (congrArg (Spf B).presheaf.map (Quiver.Hom.unop_inj (Subsingleton.elim _ _)))
  exact (Category.assoc _ _ _).symm.trans <|
    (congrArg (· ≫ (Spf B).presheaf.map eqW.op) (g.c.naturality _)).trans <|
      (Category.assoc _ _ _).trans <| (congrArg _ hmap).trans <|
        (congrArg (· ≫ _) htop).trans (m.c.naturality (homOfLE le_top).op).symm

private theorem exists_pow_map_quotient_eq_bot_of_map (φ : A →+* B) (hφ : Continuous φ)
    (W : Opens (carrier B)) (n : ℕ) :
    have := (IsAdicRing.ideal_spec A).2.2
    ∃ k : ℕ, (IsAdicRing.ideal A ^ (k + 1)).map
      (((globalSectionsIso (IsAdicRing.ideal_spec A).2.1).inv ≫ (map φ hφ).c.app (op ⊤) ≫
        (Spf B).presheaf.map (homOfLE (le_top : W ≤ ⊤)).op ≫
        (quotientProjection (IsAdicRing.ideal_spec B).2.1 n).hom.app (op W)).hom) = ⊥ := by
  obtain ⟨-, hIA, _⟩ := IsAdicRing.ideal_spec A
  obtain ⟨-, hIB, _⟩ := IsAdicRing.ideal_spec B
  let m := map φ hφ
  let πn := (quotientProjection hIB n).hom.app (op W)
  obtain ⟨k, hk⟩ := hIA.exists_pow_succ_le_comap (hIB.isOpen_pow (n + 1)) hφ
  refine ⟨k, ?_⟩
  rw [Ideal.map_eq_bot_iff_le_ker]; intro r hr; rw [RingHom.mem_ker]
  have hcomp : (globalSectionsIso hIA).inv ≫ m.c.app (op ⊤) ≫
        (Spf B).presheaf.map (homOfLE (le_top : W ≤ ⊤)).op ≫ πn =
      CommRingCat.ofHom ((Ideal.Quotient.mk (IsAdicRing.ideal B ^ (n + 1))).comp φ) ≫
        (quotientSheafGlobalSectionsIso (is_ideal_adic_pow hIB n.succ_pos)).inv ≫
        (quotientSheaf (is_ideal_adic_pow hIB n.succ_pos)).obj.map
          (homOfLE (le_top : W ≤ ⊤)).op := by
    refine (Category.assoc _ _ _).symm.trans <|
      (congrArg (· ≫ _) (globalSectionsIso_inv_comp_c_app_top m)).trans ?_
    rw [sectionsHom_map]
    change (CommRingCat.ofHom φ ≫ (globalSectionsIso hIB).inv) ≫
      ((structureSheaf hIB).obj.map (homOfLE (le_top : W ≤ ⊤)).op ≫ πn) = _
    rw [Category.assoc, (quotientProjection hIB n).hom.naturality,
      globalSectionsIso_inv_comp_quotientProjection_assoc, CommRingCat.ofHom_comp, Category.assoc]
  have hmk : Ideal.Quotient.mk (IsAdicRing.ideal B ^ (n + 1)) (φ r) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (hk hr)
  simpa [hmk] using ConcreteCategory.congr_hom hcomp r

private theorem c_app_basicOpen_eq_map_sectionsHom (g : Spf B ⟶ Spf A) (a : A) :
    g.c.app (op (basicOpen a)) ≫
        (Spf B).presheaf.map (eqToHom (congrArg (fun f ↦ (Opens.map f).obj (basicOpen a))
          (base_eq_map_sectionsHom g).symm)).op =
      (map (sectionsHom g) (continuous_sectionsHom g)).c.app (op (basicOpen a)) := by
  obtain ⟨hIAfg, hIA, _⟩ := IsAdicRing.ideal_spec A
  obtain ⟨-, hIB, -⟩ := IsAdicRing.ideal_spec B
  let φ := sectionsHom g; let hφ := continuous_sectionsHom g; let m := map φ hφ
  let W : Opens (carrier B) := (Opens.map m.base).obj (basicOpen a)
  let α := g.c.app (op (basicOpen a)) ≫ (Spf B).presheaf.map
    (eqToHom (congrArg (fun f ↦ (Opens.map f).obj (basicOpen a))
      (base_eq_map_sectionsHom g).symm)).op
  let β := m.c.app (op (basicOpen a))
  have hassoc (δ : (Spf A).presheaf.obj (op (basicOpen a)) ⟶ (Spf B).presheaf.obj (op W))
      {S : CommRingCat.{u}} (π : (Spf B).presheaf.obj (op W) ⟶ S) :
      CommRingCat.ofHom (algebraMap A (AdicRing.CompletedAway A a)) ≫
          ((basicOpenSectionsIso hIA hIAfg a).inv ≫ δ ≫ π) =
        (globalSectionsIso hIA).inv ≫
          ((Spf A).presheaf.map (homOfLE (le_top : basicOpen a ≤ ⊤)).op ≫ δ) ≫ π :=
    (Category.assoc _ _ _).symm.trans <|
      (congrArg (· ≫ (δ ≫ π)) (algebraMap_comp_basicOpenSectionsIso_inv a)).trans <|
        (Category.assoc _ _ _).trans
          (congrArg ((globalSectionsIso hIA).inv ≫ ·) (Category.assoc _ _ _).symm)
  refine (cancel_epi (basicOpenSectionsIso hIA hIAfg a).inv).mp ?_
  ext x; refine structureSheaf.sections_ext hIB fun n ↦ ?_
  let Rn := (quotientSheaf (is_ideal_adic_pow hIB n.succ_pos)).obj.obj (op W)
  let πn : (Spf B).presheaf.obj (op W) ⟶ Rn := (quotientProjection hIB n).hom.app (op W)
  let γ₁ := ((basicOpenSectionsIso hIA hIAfg a).inv ≫ α ≫ πn).hom
  let γ₂ := ((basicOpenSectionsIso hIA hIAfg a).inv ≫ β ≫ πn).hom
  have hA : γ₁.comp (algebraMap A (AdicRing.CompletedAway A a)) =
      γ₂.comp (algebraMap A (AdicRing.CompletedAway A a)) :=
    congrArg CommRingCat.Hom.hom <| (hassoc α πn).trans <|
      (congrArg (fun t ↦ (globalSectionsIso hIA).inv ≫ t ≫ πn)
        (res_c_app_basicOpen_eq_map_sectionsHom g a)).trans (hassoc β πn).symm
  let _ : Algebra A Rn := (γ₂.comp (algebraMap A (AdicRing.CompletedAway A a))).toAlgebra
  let g₁ : AdicRing.CompletedAway A a →ₐ[A] Rn := ⟨γ₁, fun r ↦ congr($hA r)⟩
  let g₂ : AdicRing.CompletedAway A a →ₐ[A] Rn := ⟨γ₂, fun _ ↦ rfl⟩
  obtain ⟨k, hk⟩ := exists_pow_map_quotient_eq_bot_of_map φ hφ W n
  have halg : algebraMap A Rn = (((globalSectionsIso hIA).inv ≫ m.c.app (op ⊤) ≫
      (Spf B).presheaf.map (homOfLE (le_top : W ≤ ⊤)).op ≫ πn).hom) :=
    congrArg CommRingCat.Hom.hom <| (hassoc β πn).trans <|
      congrArg ((globalSectionsIso hIA).inv ≫ ·) <|
        (congrArg (· ≫ πn) (m.c.naturality (homOfLE (le_top : basicOpen a ≤ ⊤)).op)).trans
          (Category.assoc _ _ _)
  exact congr($(AdicRing.CompletedAway.algHom_ext_of_map_pow_eq_bot (halg.symm ▸ hk) g₁ g₂) x)

/-- Every morphism `g : Spf B ⟶ Spf A` of locally ringed spaces is `Spf.map` of its induced
continuous homomorphism on global sections (EGA I, Ch. I, 10.2.2; Stacks Tag 0AHY). -/
@[simp]
theorem map_sectionsHom (g : Spf B ⟶ Spf A) :
    map (sectionsHom g) (continuous_sectionsHom g) = g := by
  symm; apply LocallyRingedSpace.Hom.ext'
  refine PresheafedSpace.Hom.ext _ _ (base_eq_map_sectionsHom g) ?_
  refine TopCat.Sheaf.hom_ext _
    ((TopCat.Sheaf.pushforward CommRingCat
      (map (sectionsHom g) (continuous_sectionsHom g)).base).obj (Spf B).sheaf)
    isBasis_basicOpen fun a ↦ (NatTrans.comp_app _ _ (op (basicOpen a))).trans <|
      (congrArg (g.c.app (op (basicOpen a)) ≫ ·)
        (congrArg (Spf B).presheaf.map (Quiver.Hom.unop_inj (Subsingleton.elim _ _)))).trans
        (c_app_basicOpen_eq_map_sectionsHom g a)

/-- Two morphisms `Spf B ⟶ Spf A` with the same induced global-section homomorphism are equal. -/
theorem sectionsHom_injective : Function.Injective (sectionsHom (A := A) (B := B)) := by
  intro g₁ g₂ h; rw [← map_sectionsHom g₁, ← map_sectionsHom g₂]; congr 1

@[simp]
theorem sectionsHom_id : sectionsHom (𝟙 (Spf A)) = RingHom.id A := by
  rw [← map_id, sectionsHom_map]

@[simp]
theorem sectionsHom_comp (f : Spf C ⟶ Spf B) (g : Spf B ⟶ Spf A) :
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

@[simp]
theorem homEquiv_apply_coe (g : Spf B ⟶ Spf A) : (homEquiv g : A →+* B) = sectionsHom g := (rfl)

@[simp]
theorem homEquiv_symm_apply (φ : {φ : A →+* B // Continuous φ}) :
    homEquiv.symm φ = map φ.1 φ.2 := (rfl)

/-- A ring isomorphism `e : A ≃+* B` that is continuous in both directions induces an isomorphism
of formal spectra `Spf B ≅ Spf A`. -/
noncomputable def mapIso (e : A ≃+* B) (h₁ : Continuous e) (h₂ : Continuous e.symm) :
    Spf B ≅ Spf A where
  hom := map e.toRingHom h₁
  inv := map e.symm.toRingHom h₂
  hom_inv_id := by
    have h₁' : Continuous e.toRingHom := h₁; have h₂' : Continuous e.symm.toRingHom := h₂
    rw [show map e.toRingHom h₁ ≫ map e.symm.toRingHom h₂ = _ from (map_comp _ h₁' _ h₂').symm]
    simp
  inv_hom_id := by
    have h₁' : Continuous e.toRingHom := h₁; have h₂' : Continuous e.symm.toRingHom := h₂
    rw [show map e.symm.toRingHom h₂ ≫ map e.toRingHom h₁ = _ from (map_comp _ h₂' _ h₁').symm]
    simp

@[simp]
theorem mapIso_hom (e : A ≃+* B) (h₁ : Continuous e) (h₂ : Continuous e.symm) :
    (mapIso e h₁ h₂).hom = map e.toRingHom h₁ := (rfl)

@[simp]
theorem mapIso_inv (e : A ≃+* B) (h₁ : Continuous e) (h₂ : Continuous e.symm) :
    (mapIso e h₁ h₂).inv = map e.symm.toRingHom h₂ := (rfl)

/-- Every isomorphism `Spf B ≅ Spf A` of locally ringed spaces induces a ring isomorphism
`A ≃+* B` on global sections. -/
noncomputable def isoToRingEquiv (e : Spf B ≅ Spf A) : A ≃+* B :=
  { sectionsHom e.hom with
    invFun := sectionsHom e.inv
    left_inv a := by simpa [e.inv_hom_id] using (congr($(sectionsHom_comp e.inv e.hom) a)).symm
    right_inv b := by simpa [e.hom_inv_id] using (congr($(sectionsHom_comp e.hom e.inv) b)).symm }

theorem isoToRingEquiv_toRingHom (e : Spf B ≅ Spf A) :
    (isoToRingEquiv e).toRingHom = sectionsHom e.hom := (rfl)

@[simp]
theorem isoToRingEquiv_coe_ringHom (e : Spf B ≅ Spf A) :
    (isoToRingEquiv e : A →+* B) = sectionsHom e.hom := (rfl)

@[simp]
theorem isoToRingEquiv_apply (e : Spf B ≅ Spf A) (a : A) :
    isoToRingEquiv e a = sectionsHom e.hom a := (rfl)

@[simp]
theorem isoToRingEquiv_symm (e : Spf B ≅ Spf A) :
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
  let W := (Opens.map (TopCat.ofHom (comap φ hφ))).obj U
  let _ := sectionsTopology hIA U
  refine (continuous_iff_sectionsTopology hIB W).mpr fun n ↦ ?_
  obtain ⟨m, hm⟩ := hIA.exists_pow_succ_le_comap (hIB.isOpen_pow (n + 1)) hφ
  have hN := is_ideal_adic_pow hIA m.succ_pos
  have hproj := congrArg (fun η ↦ η.hom.app (op U))
    (structureSheafMap_comp_quotientProjection φ hφ hIA hIB hN n hm)
  have hfun : (((quotientProjection hIB n).hom.app (op W)) : _ → _) ∘
        (((structureSheafMap φ hφ hIA hIB).hom.app (op U) :
          (structureSheaf hIA).obj.obj (op U) ⟶ (structureSheaf hIB).obj.obj (op W))) =
      (((quotientMap φ hφ hN (is_ideal_adic_pow hIB n.succ_pos) hm).hom.app (op U) :
          (quotientSheaf hN).obj.obj (op U) ⟶
            (quotientSheaf (is_ideal_adic_pow hIB n.succ_pos)).obj.obj (op W))) ∘
        ((toQuotientSheaf hIA hN).hom.app (op U)) :=
    funext (ConcreteCategory.congr_hom hproj)
  rw [hfun]
  exact @Continuous.comp _ _ _ (sectionsTopology hIA U) ⊥ ⊥ _ _ continuous_bot
    (continuous_toQuotientSheaf_app hIA hN U)

private theorem continuous_structureSheafMap_quotientSectionsTopology
    (φ : A →+* B) (hφ : Continuous φ) (U : Opens (carrier A)) :
    let hIA := (IsAdicRing.ideal_spec A).2.1; let hIB := (IsAdicRing.ideal_spec B).2.1
    @Continuous _ _ (quotientSectionsTopology hIA U)
      (quotientSectionsTopology hIB ((Opens.map (TopCat.ofHom (comap φ hφ))).obj U))
      ((structureSheafMap φ hφ hIA hIB).hom.app (op U) :
        (structureSheaf hIA).obj.obj (op U) ⟶ _) := by
  intro hIA hIB
  let fBase := TopCat.ofHom (comap φ hφ)
  let W := (Opens.map fBase).obj U
  let η : (structureSheaf hIA).obj ⟶ (TopCat.Presheaf.pushforward CommRingCat fBase).obj
      (structureSheaf hIB).obj := (structureSheafMap φ hφ hIA hIB).hom
  let _ := quotientSectionsTopology hIA U
  refine (continuous_iff_quotientSectionsTopology hIB W).mpr fun b hb ↦ ?_
  let Idx := { a : A // basicOpen a ≤ U }
  let V (i : Idx) : Opens (carrier B) := basicOpen (b * φ i.1)
  have hVle (i : Idx) : V i ≤ basicOpen b := by simp only [V, basicOpen_mul]; exact inf_le_left
  have hVcov : basicOpen b ≤ ⨆ i : Idx, V i := fun q hqb ↦ by
    obtain ⟨a, hqa, haU⟩ := exists_basicOpen_le (show comap φ hφ q ∈ U from hb hqb)
    exact Opens.mem_iSup.mpr ⟨⟨a, haU⟩, by
      simp only [V, basicOpen_mul]; exact ⟨hqb, by rwa [← comap_basicOpen φ hφ a]⟩⟩
  let _ := quotientSectionsTopology hIB (basicOpen b)
  let _ (i : Idx) := quotientSectionsTopology hIB (V i)
  rw [← quotientSectionsTopology_basicOpen hIB b,
    (quotientSectionsTopology_glue hIB hVle hVcov).isInducing.continuous_iff, continuous_pi_iff]
  intro ⟨a, haU⟩
  let _ := sectionsTopology hIA (basicOpen a)
  let _ := sectionsTopology hIB ((Opens.map fBase).obj (basicOpen a))
  have hVφ : V ⟨a, haU⟩ ≤ (Opens.map fBase).obj (basicOpen a) := by
    rw [show (Opens.map fBase).obj (basicOpen a) = basicOpen (φ a) from comap_basicOpen φ hφ a]
    simp only [V, basicOpen_mul]; exact inf_le_right
  have hc3 : @Continuous _ _ (sectionsTopology hIB ((Opens.map fBase).obj (basicOpen a)))
      (quotientSectionsTopology hIB (V ⟨a, haU⟩))
      ((structureSheaf hIB).obj.map (homOfLE hVφ).op) := by
    rw [quotientSectionsTopology_basicOpen hIB]; exact sectionsTopology_restrict hIB hVφ
  refine (hc3.comp ((continuous_structureSheafMap_sectionsTopology φ hφ (basicOpen a)).comp
    (continuous_restrict_basicOpen_sectionsTopology hIA haU))).congr fun x ↦ ?_
  have hcomm : (η.app (op U) : (structureSheaf hIA).obj.obj (op U) ⟶ _) ≫
        (structureSheaf hIB).obj.map (homOfLE hb).op ≫
        (structureSheaf hIB).obj.map (homOfLE (hVle ⟨a, haU⟩)).op =
      (structureSheaf hIA).obj.map (homOfLE haU).op ≫ (η.app (op (basicOpen a)) : _ ⟶ _) ≫
        (structureSheaf hIB).obj.map (homOfLE hVφ).op := by
    rw [← (structureSheaf hIB).obj.map_comp,
      show (homOfLE hb).op ≫ (homOfLE (hVle ⟨a, haU⟩)).op =
        ((Opens.map fBase).map (homOfLE haU)).op ≫ (homOfLE hVφ).op from
        Quiver.Hom.unop_inj (Subsingleton.elim _ _),
      (structureSheaf hIB).obj.map_comp, ← Category.assoc]
    exact congrArg (· ≫ _) (η.naturality (homOfLE haU).op).symm
  exact (ConcreteCategory.congr_hom hcomm x).symm

/-- Every morphism `g : Spf B ⟶ Spf A` is continuous on rings of sections over all opens `U`,
equipped with `quotientSectionsTopology` (EGA I, Ch. I, 10.2.2 and 10.4.5). -/
theorem continuous_c_app (g : Spf B ⟶ Spf A) (U : Opens (Spf A)) :
    @Continuous _ _ (quotientSectionsTopology (IsAdicRing.ideal_spec A).2.1 U)
      (quotientSectionsTopology (IsAdicRing.ideal_spec B).2.1 ((Opens.map g.base).obj U))
      ((g.c.app (op U) : (Spf A).presheaf.obj (op U) ⟶
        (Spf B).presheaf.obj (op ((Opens.map g.base).obj U)))) := by
  have hg : g.toHom =
      { base := TopCat.ofHom (comap (sectionsHom g) (continuous_sectionsHom g))
        c := (structureSheafMap (sectionsHom g) (continuous_sectionsHom g)
          (IsAdicRing.ideal_spec A).2.1 (IsAdicRing.ideal_spec B).2.1).hom } :=
    (congrArg LocallyRingedSpace.Hom.toHom (map_sectionsHom g).symm).trans (map_toHom _ _)
  change @Continuous _ _ (quotientSectionsTopology (IsAdicRing.ideal_spec A).2.1 U)
    (quotientSectionsTopology (IsAdicRing.ideal_spec B).2.1 ((Opens.map g.toHom.base).obj U))
    ((g.toHom.c.app (op U) : (Spf A).presheaf.obj (op U) ⟶
      (Spf B).presheaf.obj (op ((Opens.map g.toHom.base).obj U))))
  rw [hg]
  exact continuous_structureSheafMap_quotientSectionsTopology
    (sectionsHom g) (continuous_sectionsHom g) U

end HomEquiv

end TauCeti.FormalScheme.Spf
