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

Let `A` and `B` be adic rings of finite ideal type. Every morphism of locally ringed spaces
`g : Spf B ⟶ Spf A` induces a homomorphism `sectionsHom g : A →+* B` on global sections via
`globalSectionsIso`. Because `g` induces local ring homomorphisms on stalks, naturality of residue
evaluation shows that `g.base` pulls open primes of `B` back along `sectionsHom g`. In particular,
every open prime of `B` contains the image of `IsAdicRing.ideal A`, so `sectionsHom g` carries a
finitely generated ideal of definition of `A` into the radical of an ideal of definition of `B` and
is automatically continuous (EGA I, Ch. I, 10.2.2; Stacks Tag 0AHY).

Comparing `g` and `Spf.map (sectionsHom g) _` over each basic open `D(a)` of `Spf A` reduces, via
projection to the thickenings of `B` and the algebraic uniqueness theorem
`TauCeti.AdicRing.CompletedAway.algHom_ext_of_map_pow_eq_bot`, to their agreement on global
sections. Hence `g = Spf.map (sectionsHom g) _`: `Spf` is a fully faithful contravariant functor
from complete separated adic rings of finite ideal type with continuous ring homomorphisms to
locally ringed spaces, every isomorphism `Spf B ≅ Spf A` induces a topological ring isomorphism
`A ≃+* B`, and every morphism `Spf B ⟶ Spf A` is continuous on rings of sections for
`quotientSectionsTopology`.

## Main definitions

* `TauCeti.FormalScheme.Spf.topSectionsIso`: the canonical isomorphism
  `(Spf A).presheaf.obj (op ⊤) ≅ CommRingCat.of A`.
* `TauCeti.FormalScheme.Spf.sectionsHom`: the ring homomorphism `A →+* B` induced on global
  sections by a morphism `Spf B ⟶ Spf A`.
* `TauCeti.FormalScheme.Spf.homEquiv`: the equivalence
  `(Spf B ⟶ Spf A) ≃ {φ : A →+* B // Continuous φ}`.
* `TauCeti.FormalScheme.Spf.mapIso`: the isomorphism `Spf B ≅ Spf A` induced by a topological ring
  isomorphism `A ≃+* B`.
* `TauCeti.FormalScheme.Spf.isoToRingEquiv`: the ring isomorphism `A ≃+* B` induced by an
  isomorphism `Spf B ≅ Spf A`.

## Main results

* `TauCeti.FormalScheme.Spf.homEquiv_pow`,
  `TauCeti.FormalScheme.Spf.continuous_iff_exists_pos_pow_map_le`: for a finitely generated ideal of
  definition `I ⊆ A` and an ideal of definition `J ⊆ B`, continuity of `φ : A →+* B` is equivalent
  to `I.map φ ≤ J.radical` and to `∃ k > 0, (I ^ k).map φ ≤ J`.
* `TauCeti.FormalScheme.Spf.continuous_sectionsHom`: `sectionsHom g` is automatically continuous.
* `TauCeti.FormalScheme.Spf.map_sectionsHom`: `Spf.map (sectionsHom g) _ = g`.
* `TauCeti.FormalScheme.Spf.isHomeomorph_isoToRingEquiv`: `isoToRingEquiv e` is a homeomorphism.
* `TauCeti.FormalScheme.Spf.continuous_c_app`: every morphism `Spf B ⟶ Spf A` is continuous on
  section rings equipped with `quotientSectionsTopology`.

## References

* A. Grothendieck and J. Dieudonné, *Éléments de géométrie algébrique I*, Ch. 0, 7.1.3–7.1.4, and
  Ch. I, 10.2.2.
* [Stacks Project, Tag 0AHY](https://stacks.math.columbia.edu/tag/0AHY).
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
  refine ⟨fun h ↦ ?_, ?_⟩
  · obtain ⟨k, hk⟩ := Ideal.exists_pow_le_of_le_radical_of_fg h (hIfg.map φ)
    rw [← Ideal.map_pow] at hk
    rcases Nat.eq_zero_or_pos k with rfl | hkpos
    · have hJtop : J = ⊤ := by
        simpa only [pow_zero, Ideal.one_eq_top, Ideal.map_top, top_le_iff] using hk
      exact ⟨1, Nat.one_pos, by simp [hJtop]⟩
    · exact ⟨k, hkpos, hk⟩
  · rintro ⟨k, -, hk⟩ x hx
    exact ⟨k, hk (by rw [Ideal.map_pow]; exact Ideal.pow_mem_pow hx k)⟩

variable [TopologicalSpace A] [TopologicalSpace B]

/-- For a finitely generated ideal of definition `I` of `A` and an ideal of definition `J` of `B`,
a ring homomorphism `φ : A →+* B` is continuous if and only if `(I ^ k).map φ ≤ J` for some `k > 0`
(EGA I, Ch. 0, 7.1.3–7.1.4; Ch. I, 10.2.2). -/
theorem continuous_iff_exists_pos_pow_map_le (hI : IsAdic I) (hIfg : I.FG) (hJ : IsAdic J)
    {φ : A →+* B} :
    Continuous φ ↔ ∃ k > 0, (I ^ k).map φ ≤ J :=
  (hI.continuous_iff_map_le_radical hJ hI hIfg).trans
    (map_le_radical_iff_exists_pos_pow_map_le hIfg)

/-- Continuity of `φ : A →+* B` is equivalent to `I.map φ ≤ J.radical`, which in turn is equivalent
to `(I ^ k).map φ ≤ J` for some positive integer `k` (EGA I, Ch. I, 10.2.2). -/
theorem homEquiv_pow (hI : IsAdic I) (hIfg : I.FG) (hJ : IsAdic J) (φ : A →+* B) :
    (Continuous φ ↔ I.map φ ≤ J.radical) ∧
      (I.map φ ≤ J.radical ↔ ∃ k > 0, (I ^ k).map φ ≤ J) :=
  ⟨hI.continuous_iff_map_le_radical hJ hI hIfg, map_le_radical_iff_exists_pos_pow_map_le hIfg⟩

end ContinuityCriterion

section ResidueEvaluation

variable {A : Type u} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [IsAdicRing A]

/-- The global sections of `Spf A` are canonically isomorphic to `A` (EGA I, Ch. I, 10.1.3). -/
noncomputable def topSectionsIso (A : Type u) [CommRing A] [TopologicalSpace A]
    [IsTopologicalRing A] [IsAdicRing A] :
    (Spf A).presheaf.obj (op ⊤) ≅ CommRingCat.of A :=
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

/-- Under `stalkResidueFieldEquiv`, evaluating the global section attached to `a ∈ A` at an open
prime `p` produces the image of `a` in `Frac(A ⧸ p)`. -/
theorem stalkResidueFieldEquiv_Γevaluation_topSectionsIso_inv (p : carrier A) (a : A) :
    stalkResidueFieldEquiv p ((Spf A).Γevaluation p ((topSectionsIso A).inv a)) =
      algebraMap (A ⧸ (p : PrimeSpectrum A).asIdeal)
        (FractionRing (A ⧸ (p : PrimeSpectrum A).asIdeal)) (Ideal.Quotient.mk _ a) := by
  have := (IsAdicRing.ideal_spec A).2.2
  let hIA := (IsAdicRing.ideal_spec A).2.1
  let hIAfg := (IsAdicRing.ideal_spec A).1
  let u : BasicNeighbourhood p :=
    ⟨1, by simpa using (Ideal.ne_top_iff_one _).mp (p : PrimeSpectrum A).isPrime.ne_top⟩
  have hsec : (basicOpenSectionsIso hIA hIAfg u.elem).inv
        (algebraMap A (AdicRing.CompletedAway A u.elem) a) =
      (Spf A).presheaf.map (homOfLE (le_top : basicOpen u.elem ≤ ⊤)).op
        ((topSectionsIso A).inv a) := by
    have h : CommRingCat.ofHom (algebraMap A (AdicRing.CompletedAway A u.elem)) ≫
          (basicOpenSectionsIso hIA hIAfg u.elem).inv =
        (topSectionsIso A).inv ≫
          (Spf A).presheaf.map (homOfLE (le_top : basicOpen u.elem ≤ ⊤)).op :=
      (Iso.comp_inv_eq (basicOpenSectionsIso hIA hIAfg u.elem)).mpr
        ((Category.assoc _ _ _).symm.trans
          (globalSectionsIso_inv_comp_basicOpenSectionsIso_hom hIA hIAfg u.elem)).symm
    exact ConcreteCategory.congr_hom h a
  have hgerm : (Spf A).presheaf.germ (basicOpen u.elem) p (mem_basicOpen.mpr u.notMem)
        ((Spf A).presheaf.map (homOfLE (le_top : basicOpen u.elem ≤ ⊤)).op
          ((topSectionsIso A).inv a)) =
      (Spf A).presheaf.germ ⊤ p trivial ((topSectionsIso A).inv a) :=
    TopCat.Presheaf.germ_res_apply (Spf A).presheaf (homOfLE (le_top : basicOpen u.elem ≤ ⊤)) p
      (mem_basicOpen.mpr u.notMem) ((topSectionsIso A).inv a)
  have heval : (Spf A).residue p ((Spf A).presheaf.germ ⊤ p trivial
        ((topSectionsIso A).inv a)) =
      (Spf A).Γevaluation p ((topSectionsIso A).inv a) := rfl
  simpa only [hsec, hgerm, heval] using stalkResidueFieldEquiv_residue_germ u a

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
      CommRingCat.ofHom (sectionsHom g) ≫ (topSectionsIso B).inv := by
  refine (cancel_mono (topSectionsIso B).hom).mp ?_
  exact ((Category.assoc _ _ _).trans <|
    (congrArg (CommRingCat.ofHom (sectionsHom g) ≫ ·) (Iso.inv_hom_id _)).trans
      (Category.comp_id _)).symm

/-- Dual form of `globalSectionsIso_inv_comp_c_app_top` with `(topSectionsIso _).hom`. -/
@[reassoc]
theorem c_app_top_comp_globalSectionsIso_hom (g : Spf B ⟶ Spf A) :
    (g.c.app (op ⊤) : (Spf A).presheaf.obj (op ⊤) ⟶ (Spf B).presheaf.obj (op ⊤)) ≫
        (topSectionsIso B).hom =
      (topSectionsIso A).hom ≫ CommRingCat.ofHom (sectionsHom g) := by
  refine (cancel_epi (topSectionsIso A).inv).mp ?_
  exact (Category.assoc _ _ _).symm.trans (Iso.inv_hom_id_assoc _ _).symm

/-- On points, `g : Spf B ⟶ Spf A` pulls every open prime ideal of `B` back along
`sectionsHom g`. -/
@[simp]
theorem mem_base_asIdeal_iff (g : Spf B ⟶ Spf A) (q : carrier B) (a : A) :
    a ∈ (g.base q).1.asIdeal ↔ sectionsHom g a ∈ q.1.asIdeal := by
  let q' : Spf B := q
  have hsec : g.c.app (op ⊤) ((topSectionsIso A).inv a) =
      (topSectionsIso B).inv (sectionsHom g a) :=
    ConcreteCategory.congr_hom (globalSectionsIso_inv_comp_c_app_top g) a
  have hnat : LocallyRingedSpace.residueFieldMap g q'
        ((Spf A).Γevaluation (g.base q') ((topSectionsIso A).inv a)) =
      (Spf B).Γevaluation q' ((topSectionsIso B).inv (sectionsHom g a)) :=
    (LocallyRingedSpace.Γevaluation_naturality_apply g q' ((topSectionsIso A).inv a)).trans
      (congrArg ((Spf B).Γevaluation q') hsec)
  have hmid : (Spf A).Γevaluation (g.base q') ((topSectionsIso A).inv a) = 0 ↔
      (Spf B).Γevaluation q' ((topSectionsIso B).inv (sectionsHom g a)) = 0 :=
    ((LocallyRingedSpace.residueFieldMap g q').hom.map_eq_zero_iff).symm.trans
      (congrArg (· = 0) hnat).to_iff
  exact (Γevaluation_topSectionsIso_inv_eq_zero_iff (g.base q') a).symm.trans
    (hmid.trans (Γevaluation_topSectionsIso_inv_eq_zero_iff q (sectionsHom g a)))

/-- **Automatic continuity** (EGA I, Ch. I, 10.2.2): the global-section homomorphism induced by any
morphism of locally ringed spaces `Spf B ⟶ Spf A` is continuous. -/
theorem continuous_sectionsHom (g : Spf B ⟶ Spf A) : Continuous (sectionsHom g) := by
  obtain ⟨hIAfg, hIA, -⟩ := IsAdicRing.ideal_spec A
  obtain ⟨-, hIB, -⟩ := IsAdicRing.ideal_spec B
  refine hIA.continuous_of_map_le_radical hIB hIAfg ?_
  rw [Ideal.map_le_iff_le_comap]
  intro a ha
  rw [Ideal.mem_comap, Ideal.radical_eq_sInf, Ideal.mem_sInf]
  rintro p ⟨hBp, hp⟩
  let q : carrier B := ⟨⟨p, hp⟩, (mem_carrier_iff_le hIB).mpr hBp⟩
  exact (mem_base_asIdeal_iff g q a).mp (((mem_carrier_iff_le hIA).mp (g.base q).2) ha)

/-- The underlying continuous map of `g : Spf B ⟶ Spf A` is `comap (sectionsHom g) _`. -/
theorem base_eq_comap_sectionsHom (g : Spf B ⟶ Spf A) :
    g.base = TopCat.ofHom (comap (sectionsHom g) (continuous_sectionsHom g)) := by
  apply ConcreteCategory.hom_ext
  intro q
  apply Subtype.ext
  have hcoe := coe_comap_apply (sectionsHom g) (continuous_sectionsHom g) q
  ext a
  refine (mem_base_asIdeal_iff g q a).trans ?_
  -- Express `TopCat.ofHom (comap _ _) q` as the underlying `comap` point to rewrite via `hcoe`.
  change sectionsHom g a ∈ q.1.asIdeal ↔
    a ∈ (comap (sectionsHom g) (continuous_sectionsHom g) q : PrimeSpectrum A).asIdeal
  rw [hcoe]
  rfl

private theorem base_eq_map_sectionsHom (g : Spf B ⟶ Spf A) :
    g.base = (map (sectionsHom g) (continuous_sectionsHom g)).base :=
  (base_eq_comap_sectionsHom g).trans (map_base _ _).symm

/-- Helper: `g` and `Spf.map (sectionsHom g) _` agree after restricting from `⊤` to `D(a)`. -/
private theorem res_c_app_basicOpen_eq_map_sectionsHom (g : Spf B ⟶ Spf A) (a : A) :
    (Spf A).presheaf.map (homOfLE (le_top : basicOpen a ≤ ⊤)).op ≫
        (g.c.app (op (basicOpen a)) ≫
          (Spf B).presheaf.map
            (eqToHom (congrArg (fun f ↦ (Opens.map f).obj (basicOpen a))
              (base_eq_map_sectionsHom g).symm)).op) =
      (Spf A).presheaf.map (homOfLE (le_top : basicOpen a ≤ ⊤)).op ≫
        (map (sectionsHom g) (continuous_sectionsHom g)).c.app (op (basicOpen a)) := by
  obtain ⟨-, hIB, hIBC⟩ := IsAdicRing.ideal_spec B
  let φ := sectionsHom g
  let hφ := continuous_sectionsHom g
  let m := map φ hφ
  let W : Opens (carrier B) := (Opens.map m.base).obj (basicOpen a)
  let eqW := eqToHom (congrArg (fun f ↦ (Opens.map f).obj (basicOpen a))
    (base_eq_map_sectionsHom g).symm)
  have htop : (g.c.app (op ⊤) : (Spf A).presheaf.obj (op ⊤) ⟶ (Spf B).presheaf.obj (op ⊤)) =
      (m.c.app (op ⊤) : (Spf A).presheaf.obj (op ⊤) ⟶ (Spf B).presheaf.obj (op ⊤)) :=
    (cancel_mono (globalSectionsIso hIB).hom).mp <|
      (c_app_top_comp_globalSectionsIso_hom g).trans (map_globalSections φ hφ).symm
  have hg : (Spf A).presheaf.map (homOfLE (le_top : basicOpen a ≤ ⊤)).op ≫
        (g.c.app (op (basicOpen a)) ≫ (Spf B).presheaf.map eqW.op) =
      (g.c.app (op ⊤) : (Spf A).presheaf.obj (op ⊤) ⟶ (Spf B).presheaf.obj (op ⊤)) ≫
        (((TopCat.Presheaf.pushforward CommRingCat g.base).obj (Spf B).presheaf).map
          (homOfLE (le_top : basicOpen a ≤ ⊤)).op ≫ (Spf B).presheaf.map eqW.op) :=
    (Category.assoc _ _ _).symm.trans <|
      (congrArg (· ≫ (Spf B).presheaf.map eqW.op)
        (g.c.naturality (homOfLE (le_top : basicOpen a ≤ ⊤)).op)).trans (Category.assoc _ _ _)
  have hm := m.c.naturality (homOfLE (le_top : basicOpen a ≤ ⊤)).op
  have hmap : ((TopCat.Presheaf.pushforward CommRingCat g.base).obj (Spf B).presheaf).map
        (homOfLE (le_top : basicOpen a ≤ ⊤)).op ≫ (Spf B).presheaf.map eqW.op =
      (Spf B).presheaf.map (homOfLE (le_top : W ≤ ⊤)).op :=
    ((Spf B).presheaf.map_comp _ _).symm.trans
      (congrArg (Spf B).presheaf.map (Quiver.Hom.unop_inj (Subsingleton.elim _ _)))
  exact hg.trans <| (congrArg _ hmap).trans <| (congrArg (· ≫ _) htop).trans hm.symm

/-- Helper: under `(globalSectionsIso hIA).inv` followed by `Spf.map φ hφ` and projection to the
`n`-th thickening over `W`, some positive power of `IsAdicRing.ideal A` maps to `⊥`. -/
private theorem exists_pow_map_quotient_eq_bot_of_map (φ : A →+* B) (hφ : Continuous φ)
    (W : Opens (carrier B)) (n : ℕ) :
    have := (IsAdicRing.ideal_spec A).2.2
    ∃ k : ℕ,
      (IsAdicRing.ideal A ^ (k + 1)).map
        (((globalSectionsIso (IsAdicRing.ideal_spec A).2.1).inv ≫
          (map φ hφ).c.app (op ⊤) ≫
          (Spf B).presheaf.map (homOfLE (le_top : W ≤ ⊤)).op ≫
          (quotientProjection (IsAdicRing.ideal_spec B).2.1 n).hom.app (op W)).hom) = ⊥ := by
  obtain ⟨-, hIA, hIAC⟩ := IsAdicRing.ideal_spec A
  obtain ⟨-, hIB, hIBC⟩ := IsAdicRing.ideal_spec B
  let m := map φ hφ
  let πn := (quotientProjection hIB n).hom.app (op W)
  obtain ⟨k, hk⟩ := hIA.exists_pow_succ_le_comap (hIB.isOpen_pow (n + 1)) hφ
  refine ⟨k, ?_⟩
  rw [Ideal.map_eq_bot_iff_le_ker]
  intro r hr
  rw [RingHom.mem_ker]
  have hproj_nat := (quotientProjection hIB n).hom.naturality (homOfLE (le_top : W ≤ ⊤)).op
  have hmk : Ideal.Quotient.mk (IsAdicRing.ideal B ^ (n + 1)) (sectionsHom m r) = 0 := by
    have hm_φ : sectionsHom m = φ := congrArg CommRingCat.Hom.hom <|
      (cancel_epi (globalSectionsIso hIA).hom).mp
        ((c_app_top_comp_globalSectionsIso_hom m).symm.trans (map_globalSections φ hφ))
    rw [hm_φ, Ideal.Quotient.eq_zero_iff_mem]
    exact hk hr
  have hcomp : (globalSectionsIso hIA).inv ≫ m.c.app (op ⊤) ≫
        (Spf B).presheaf.map (homOfLE (le_top : W ≤ ⊤)).op ≫ πn =
      CommRingCat.ofHom (Ideal.Quotient.mk (IsAdicRing.ideal B ^ (n + 1)) |>.comp
        (sectionsHom m)) ≫
        (quotientSheafGlobalSectionsIso (is_ideal_adic_pow hIB n.succ_pos)).inv ≫
        (quotientSheaf (is_ideal_adic_pow hIB n.succ_pos)).obj.map
          (homOfLE (le_top : W ≤ ⊤)).op := by
    have h1 := globalSectionsIso_inv_comp_c_app_top m
    refine (Category.assoc _ _ _).symm.trans <| (congrArg (· ≫ _) h1).trans ?_
    -- Rewrite on `structureSheaf` directly so `rw` sees concrete `CommRingCat` morphisms.
    change (CommRingCat.ofHom (sectionsHom m) ≫ (globalSectionsIso hIB).inv) ≫
        ((structureSheaf hIB).obj.map (homOfLE (le_top : W ≤ ⊤)).op ≫ πn) = _
    rw [Category.assoc, hproj_nat, globalSectionsIso_inv_comp_quotientProjection_assoc,
      CommRingCat.ofHom_comp, Category.assoc]
  simpa [hmk] using ConcreteCategory.congr_hom hcomp r

private theorem algebraMap_comp_basicOpenSectionsIso_inv_assoc (a : A) {R S : CommRingCat.{u}}
    (δ : (Spf A).presheaf.obj (op (basicOpen a)) ⟶ R) (π : R ⟶ S) :
    have := (IsAdicRing.ideal_spec A).2.2
    CommRingCat.ofHom (algebraMap A (AdicRing.CompletedAway A a)) ≫
        ((basicOpenSectionsIso (IsAdicRing.ideal_spec A).2.1 (IsAdicRing.ideal_spec A).1 a).inv ≫
          δ ≫ π) =
      (globalSectionsIso (IsAdicRing.ideal_spec A).2.1).inv ≫
        ((Spf A).presheaf.map (homOfLE (le_top : basicOpen a ≤ ⊤)).op ≫ δ) ≫ π := by
  obtain ⟨hIAfg, hIA, hIAC⟩ := IsAdicRing.ideal_spec A
  have hcoeff : CommRingCat.ofHom (algebraMap A (AdicRing.CompletedAway A a)) ≫
        (basicOpenSectionsIso hIA hIAfg a).inv =
      (globalSectionsIso hIA).inv ≫
        (Spf A).presheaf.map (homOfLE (le_top : basicOpen a ≤ ⊤)).op :=
    (Iso.comp_inv_eq (basicOpenSectionsIso hIA hIAfg a)).mpr
      ((Category.assoc _ _ _).symm.trans
        (globalSectionsIso_inv_comp_basicOpenSectionsIso_hom hIA hIAfg a)).symm
  exact (Category.assoc _ _ _).symm.trans <|
    (congrArg (· ≫ (δ ≫ π)) hcoeff).trans <|
      (Category.assoc _ _ _).trans <|
        congrArg ((globalSectionsIso hIA).inv ≫ ·) (Category.assoc _ _ _).symm

/-- Helper: on a basic open `D(a)` of `Spf A`, any morphism `g : Spf B ⟶ Spf A` agrees on sections
with `Spf.map (sectionsHom g) _`. -/
private theorem c_app_basicOpen_eq_map_sectionsHom (g : Spf B ⟶ Spf A) (a : A) :
    g.c.app (op (basicOpen a)) ≫
        (Spf B).presheaf.map
          (eqToHom (congrArg (fun f ↦ (Opens.map f).obj (basicOpen a))
            (base_eq_map_sectionsHom g).symm)).op =
      (map (sectionsHom g) (continuous_sectionsHom g)).c.app (op (basicOpen a)) := by
  obtain ⟨hIAfg, hIA, hIAC⟩ := IsAdicRing.ideal_spec A
  obtain ⟨-, hIB, -⟩ := IsAdicRing.ideal_spec B
  let φ := sectionsHom g
  let hφ := continuous_sectionsHom g
  let m := map φ hφ
  let W : Opens (carrier B) := (Opens.map m.base).obj (basicOpen a)
  let eqW := eqToHom (congrArg (fun f ↦ (Opens.map f).obj (basicOpen a))
    (base_eq_map_sectionsHom g).symm)
  let α := g.c.app (op (basicOpen a)) ≫ (Spf B).presheaf.map eqW.op
  let β := m.c.app (op (basicOpen a))
  have hres := res_c_app_basicOpen_eq_map_sectionsHom g a
  refine (cancel_epi (basicOpenSectionsIso hIA hIAfg a).inv).mp ?_
  ext x
  refine structureSheaf.sections_ext hIB fun n ↦ ?_
  let Rn := (quotientSheaf (is_ideal_adic_pow hIB n.succ_pos)).obj.obj (op W)
  let πn : (Spf B).presheaf.obj (op W) ⟶ Rn := (quotientProjection hIB n).hom.app (op W)
  let γ₁ : AdicRing.CompletedAway A a →+* Rn :=
    ((basicOpenSectionsIso hIA hIAfg a).inv ≫ α ≫ πn).hom
  let γ₂ : AdicRing.CompletedAway A a →+* Rn :=
    ((basicOpenSectionsIso hIA hIAfg a).inv ≫ β ≫ πn).hom
  have hA : γ₁.comp (algebraMap A (AdicRing.CompletedAway A a)) =
      γ₂.comp (algebraMap A (AdicRing.CompletedAway A a)) :=
    congrArg CommRingCat.Hom.hom <|
      (algebraMap_comp_basicOpenSectionsIso_inv_assoc a α πn).trans <|
        (congrArg (fun t ↦ (globalSectionsIso hIA).inv ≫ t ≫ πn) hres).trans
          (algebraMap_comp_basicOpenSectionsIso_inv_assoc a β πn).symm
  let _ : Algebra A Rn := (γ₂.comp (algebraMap A (AdicRing.CompletedAway A a))).toAlgebra
  let g₁ : AdicRing.CompletedAway A a →ₐ[A] Rn := ⟨γ₁, fun r ↦ congr($hA r)⟩
  let g₂ : AdicRing.CompletedAway A a →ₐ[A] Rn := ⟨γ₂, fun _ ↦ rfl⟩
  obtain ⟨k, hk⟩ := exists_pow_map_quotient_eq_bot_of_map φ hφ W n
  have halg : algebraMap A Rn =
      (((globalSectionsIso hIA).inv ≫ m.c.app (op ⊤) ≫
        (Spf B).presheaf.map (homOfLE (le_top : W ≤ ⊤)).op ≫ πn).hom) :=
    congrArg CommRingCat.Hom.hom <|
      (algebraMap_comp_basicOpenSectionsIso_inv_assoc a β πn).trans <|
        congrArg ((globalSectionsIso hIA).inv ≫ ·) <|
          (congrArg (· ≫ πn) (m.c.naturality (homOfLE (le_top : basicOpen a ≤ ⊤)).op)).trans
            (Category.assoc _ _ _)
  have hvan : (IsAdicRing.ideal A ^ (k + 1)).map (algebraMap A Rn) = ⊥ := halg.symm ▸ hk
  exact congr($(AdicRing.CompletedAway.algHom_ext_of_map_pow_eq_bot hvan g₁ g₂) x)

/-- Every morphism `g : Spf B ⟶ Spf A` of locally ringed spaces is `Spf.map` of its induced
continuous homomorphism on global sections (EGA I, Ch. I, 10.2.2; Stacks Tag 0AHY). -/
@[simp]
theorem map_sectionsHom (g : Spf B ⟶ Spf A) :
    map (sectionsHom g) (continuous_sectionsHom g) = g := by
  symm
  apply LocallyRingedSpace.Hom.ext'
  have hbase : g.base = (map (sectionsHom g) (continuous_sectionsHom g)).base :=
    base_eq_map_sectionsHom g
  refine PresheafedSpace.Hom.ext _ _ hbase ?_
  let F' : TopCat.Sheaf CommRingCat (TopCat.of (carrier A)) :=
    (TopCat.Sheaf.pushforward CommRingCat
      (map (sectionsHom g) (continuous_sectionsHom g)).base).obj (Spf B).sheaf
  refine TopCat.Sheaf.hom_ext _ F' isBasis_basicOpen fun a ↦ ?_
  refine (NatTrans.comp_app _ _ (op (basicOpen a))).trans <|
    (congrArg (g.c.app (op (basicOpen a)) ≫ ·) ?_).trans
      (c_app_basicOpen_eq_map_sectionsHom g a)
  exact congrArg (Spf B).presheaf.map (Quiver.Hom.unop_inj (Subsingleton.elim _ _))

/-- Taking global sections of `Spf.map φ hφ` recovers `φ`. -/
@[simp]
theorem sectionsHom_map (φ : A →+* B) (hφ : Continuous φ) :
    sectionsHom (map φ hφ) = φ := by
  have := (IsAdicRing.ideal_spec A).2.2
  have := (IsAdicRing.ideal_spec B).2.2
  have h := (cancel_epi (globalSectionsIso (IsAdicRing.ideal_spec A).2.1).hom).mp
    ((c_app_top_comp_globalSectionsIso_hom (map φ hφ)).symm.trans (map_globalSections φ hφ))
  exact congrArg CommRingCat.Hom.hom h

/-- Two morphisms `Spf B ⟶ Spf A` with the same induced global-section homomorphism are equal. -/
theorem sectionsHom_injective : Function.Injective (sectionsHom (A := A) (B := B)) := by
  intro g₁ g₂ h
  rw [← map_sectionsHom g₁, ← map_sectionsHom g₂]
  congr 1

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
  left_inv g := map_sectionsHom g
  right_inv φ := Subtype.ext (sectionsHom_map φ.1 φ.2)

@[simp]
theorem homEquiv_apply_coe (g : Spf B ⟶ Spf A) :
    (homEquiv g : A →+* B) = sectionsHom g := (rfl)

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
    have h₁' : Continuous e.toRingHom := h₁
    have h₂' : Continuous e.symm.toRingHom := h₂
    rw [show map e.toRingHom h₁ ≫ map e.symm.toRingHom h₂ =
      map (e.toRingHom.comp e.symm.toRingHom) (h₁'.comp h₂') from (map_comp _ h₁' _ h₂').symm]
    simp
  inv_hom_id := by
    have h₁' : Continuous e.toRingHom := h₁
    have h₂' : Continuous e.symm.toRingHom := h₂
    rw [show map e.symm.toRingHom h₂ ≫ map e.toRingHom h₁ =
      map (e.symm.toRingHom.comp e.toRingHom) (h₂'.comp h₁') from (map_comp _ h₂' _ h₁').symm]
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
    left_inv a := by
      have h := congr($(sectionsHom_comp e.inv e.hom) a)
      simpa [e.inv_hom_id] using h.symm
    right_inv b := by
      have h := congr($(sectionsHom_comp e.hom e.inv) b)
      simpa [e.hom_inv_id] using h.symm }

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
    (isoToRingEquiv e).symm = isoToRingEquiv e.symm := by
  ext b
  rfl

/-- The ring isomorphism `A ≃+* B` induced by `Spf B ≅ Spf A` is a homeomorphism of topological
rings: both directions are induced by morphisms of formal spectra, hence are continuous. -/
theorem isHomeomorph_isoToRingEquiv (e : Spf B ≅ Spf A) :
    IsHomeomorph (isoToRingEquiv e) := by
  have h₁ : Continuous (isoToRingEquiv e).toEquiv := continuous_sectionsHom e.hom
  have h₂ : Continuous (isoToRingEquiv e).toEquiv.symm := continuous_sectionsHom e.inv
  exact (Homeomorph.mk (isoToRingEquiv e).toEquiv h₁ h₂).isHomeomorph

/-- Helper: `(structureSheafMap φ hφ hIA hIB).hom.app (op U)` is continuous for `sectionsTopology`
over every open `U`. -/
private theorem continuous_structureSheafMap_sectionsTopology (φ : A →+* B) (hφ : Continuous φ)
    (U : Opens (carrier A)) :
    @Continuous _ _ (sectionsTopology (IsAdicRing.ideal_spec A).2.1 U)
      (sectionsTopology (IsAdicRing.ideal_spec B).2.1
        ((Opens.map (TopCat.ofHom (comap φ hφ))).obj U))
      (((structureSheafMap φ hφ (IsAdicRing.ideal_spec A).2.1
          (IsAdicRing.ideal_spec B).2.1).hom.app (op U) :
        (structureSheaf (IsAdicRing.ideal_spec A).2.1).obj.obj (op U) ⟶
          (structureSheaf (IsAdicRing.ideal_spec B).2.1).obj.obj
            (op ((Opens.map (TopCat.ofHom (comap φ hφ))).obj U)))) := by
  let hIA := (IsAdicRing.ideal_spec A).2.1
  let hIB := (IsAdicRing.ideal_spec B).2.1
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
        ((toQuotientSheaf hIA hN).hom.app (op U)) := by
    ext s
    exact ConcreteCategory.congr_hom hproj s
  rw [hfun]
  exact @Continuous.comp _ _ _ (sectionsTopology hIA U) ⊥ ⊥ _ _ continuous_bot
    (continuous_toQuotientSheaf_app hIA hN U)

/-- Helper: on a refined basic open `D(b * φ a)` with `D(a) ≤ U` and `D(b) ≤ φ*(U)`, the
composite restriction of `(structureSheafMap φ hφ hIA hIB).hom.app (op U)` is continuous. -/
private theorem continuous_structureSheafMap_basicOpen_mul
    (φ : A →+* B) (hφ : Continuous φ) {U : Opens (carrier A)} {b : B}
    (hb : basicOpen b ≤ (Opens.map (TopCat.ofHom (comap φ hφ))).obj U) {a : A}
    (haU : basicOpen a ≤ U) :
    let hIA := (IsAdicRing.ideal_spec A).2.1
    let hIB := (IsAdicRing.ideal_spec B).2.1
    let fBase := TopCat.ofHom (comap φ hφ)
    @Continuous _ _ (quotientSectionsTopology hIA U)
      (quotientSectionsTopology hIB (basicOpen (b * φ a)))
      ((structureSheaf hIB).obj.map
          (homOfLE (by simp only [basicOpen_mul]; exact inf_le_left :
            basicOpen (b * φ a) ≤ basicOpen b)).op ∘
        (structureSheaf hIB).obj.map (homOfLE hb).op ∘
        ((structureSheafMap φ hφ hIA hIB).hom.app (op U) :
          (structureSheaf hIA).obj.obj (op U) ⟶
            (structureSheaf hIB).obj.obj (op ((Opens.map fBase).obj U)))) := by
  intro hIA hIB fBase
  let W := (Opens.map fBase).obj U
  let η : (structureSheaf hIA).obj ⟶ (TopCat.Presheaf.pushforward CommRingCat fBase).obj
      (structureSheaf hIB).obj := (structureSheafMap φ hφ hIA hIB).hom
  let _ := quotientSectionsTopology hIA U
  let _ := sectionsTopology hIA (basicOpen a)
  let _ := sectionsTopology hIB ((Opens.map fBase).obj (basicOpen a))
  let _ := quotientSectionsTopology hIB (basicOpen (b * φ a))
  have hVle : basicOpen (b * φ a) ≤ basicOpen b := by
    simp only [basicOpen_mul]; exact inf_le_left
  have hVφ : basicOpen (b * φ a) ≤ (Opens.map fBase).obj (basicOpen a) := by
    rw [show (Opens.map fBase).obj (basicOpen a) = basicOpen (φ a) from comap_basicOpen φ hφ a]
    simp only [basicOpen_mul]; exact inf_le_right
  have hc1 := continuous_restrict_basicOpen_sectionsTopology hIA haU
  have hc2 := continuous_structureSheafMap_sectionsTopology φ hφ (basicOpen a)
  have hc3 : @Continuous _ _ (sectionsTopology hIB ((Opens.map fBase).obj (basicOpen a)))
      (quotientSectionsTopology hIB (basicOpen (b * φ a)))
      ((structureSheaf hIB).obj.map (homOfLE hVφ).op) := by
    rw [quotientSectionsTopology_basicOpen hIB (b * φ a)]
    exact sectionsTopology_restrict hIB hVφ
  refine (hc3.comp (hc2.comp hc1)).congr fun x ↦ ?_
  have heq : (homOfLE hb).op ≫ (homOfLE hVle).op =
      ((Opens.map fBase).map (homOfLE haU)).op ≫ (homOfLE hVφ).op :=
    Quiver.Hom.unop_inj (Subsingleton.elim _ _)
  have hcomm : (η.app (op U) : (structureSheaf hIA).obj.obj (op U) ⟶
        (structureSheaf hIB).obj.obj (op W)) ≫
        (structureSheaf hIB).obj.map (homOfLE hb).op ≫
        (structureSheaf hIB).obj.map (homOfLE hVle).op =
      (structureSheaf hIA).obj.map (homOfLE haU).op ≫
        (η.app (op (basicOpen a)) :
          (structureSheaf hIA).obj.obj (op (basicOpen a)) ⟶
            (structureSheaf hIB).obj.obj (op ((Opens.map fBase).obj (basicOpen a)))) ≫
        (structureSheaf hIB).obj.map (homOfLE hVφ).op := by
    rw [← (structureSheaf hIB).obj.map_comp, heq, (structureSheaf hIB).obj.map_comp,
      ← Category.assoc]
    exact congrArg (· ≫ (structureSheaf hIB).obj.map (homOfLE hVφ).op)
      (η.naturality (homOfLE haU).op).symm
  exact (ConcreteCategory.congr_hom hcomm x).symm

/-- Helper: `(structureSheafMap φ hφ hIA hIB).hom.app (op U)` is continuous for
`quotientSectionsTopology` over every open `U`. -/
private theorem continuous_structureSheafMap_quotientSectionsTopology
    (φ : A →+* B) (hφ : Continuous φ) (U : Opens (carrier A)) :
    @Continuous _ _ (quotientSectionsTopology (IsAdicRing.ideal_spec A).2.1 U)
      (quotientSectionsTopology (IsAdicRing.ideal_spec B).2.1
        ((Opens.map (TopCat.ofHom (comap φ hφ))).obj U))
      (((structureSheafMap φ hφ (IsAdicRing.ideal_spec A).2.1
          (IsAdicRing.ideal_spec B).2.1).hom.app (op U) :
        (structureSheaf (IsAdicRing.ideal_spec A).2.1).obj.obj (op U) ⟶
          (structureSheaf (IsAdicRing.ideal_spec B).2.1).obj.obj
            (op ((Opens.map (TopCat.ofHom (comap φ hφ))).obj U)))) := by
  let hIA := (IsAdicRing.ideal_spec A).2.1
  let hIB := (IsAdicRing.ideal_spec B).2.1
  let fBase := TopCat.ofHom (comap φ hφ)
  let W := (Opens.map fBase).obj U
  let _ := quotientSectionsTopology hIA U
  refine (continuous_iff_quotientSectionsTopology hIB W).mpr fun b hb ↦ ?_
  let Idx := { a : A // basicOpen a ≤ U }
  let V (i : Idx) : Opens (carrier B) := basicOpen (b * φ i.1)
  have hVle (i : Idx) : V i ≤ basicOpen b := by simp only [V, basicOpen_mul]; exact inf_le_left
  have hVcov : basicOpen b ≤ ⨆ i : Idx, V i := by
    intro q hqb
    obtain ⟨a, hqa, haU⟩ := exists_basicOpen_le (show comap φ hφ q ∈ U from hb hqb)
    have hqφa : q ∈ basicOpen (φ a) := by rw [← comap_basicOpen φ hφ a]; exact hqa
    exact Opens.mem_iSup.mpr ⟨⟨a, haU⟩, by simp only [V, basicOpen_mul]; exact ⟨hqb, hqφa⟩⟩
  let _ := quotientSectionsTopology hIB (basicOpen b)
  let _ (i : Idx) := quotientSectionsTopology hIB (V i)
  have hind := (quotientSectionsTopology_glue hIB hVle hVcov).isInducing
  rw [← quotientSectionsTopology_basicOpen hIB b, hind.continuous_iff, continuous_pi_iff]
  exact fun i ↦ continuous_structureSheafMap_basicOpen_mul φ hφ hb i.2

/-- Every morphism `g : Spf B ⟶ Spf A` is continuous on rings of sections over all opens `U`,
equipped with `quotientSectionsTopology` (EGA I, Ch. I, 10.2.2 and 10.4.5). -/
theorem continuous_c_app (g : Spf B ⟶ Spf A) (U : Opens (Spf A)) :
    @Continuous _ _ (quotientSectionsTopology (IsAdicRing.ideal_spec A).2.1 U)
      (quotientSectionsTopology (IsAdicRing.ideal_spec B).2.1 ((Opens.map g.base).obj U))
      ((g.c.app (op U) : (Spf A).presheaf.obj (op U) ⟶
        (Spf B).presheaf.obj (op ((Opens.map g.base).obj U)))) := by
  let φ := sectionsHom g
  let hφ := continuous_sectionsHom g
  have hg : g.toHom =
      { base := TopCat.ofHom (comap φ hφ)
        c := (structureSheafMap φ hφ (IsAdicRing.ideal_spec A).2.1
          (IsAdicRing.ideal_spec B).2.1).hom } :=
    (congrArg LocallyRingedSpace.Hom.toHom (map_sectionsHom g).symm).trans (map_toHom φ hφ)
  have hbase : g.base = TopCat.ofHom (comap φ hφ) := base_eq_comap_sectionsHom g
  have hle : (Opens.map g.base).obj U ≤ (Opens.map (TopCat.ofHom (comap φ hφ))).obj U :=
    (congrArg (fun f ↦ (Opens.map f).obj U) hbase).le
  let _ := quotientSectionsTopology (IsAdicRing.ideal_spec A).2.1 U
  let _ := quotientSectionsTopology (IsAdicRing.ideal_spec B).2.1
    ((Opens.map (TopCat.ofHom (comap φ hφ))).obj U)
  let _ := quotientSectionsTopology (IsAdicRing.ideal_spec B).2.1 ((Opens.map g.base).obj U)
  have hcont := continuous_structureSheafMap_quotientSectionsTopology φ hφ U
  have hres := quotientSectionsTopology_restrict (IsAdicRing.ideal_spec B).2.1 hle
  refine (hres.comp hcont).congr fun x ↦ ?_
  have hc : (g.c.app (op U) : (Spf A).presheaf.obj (op U) ⟶
        (Spf B).presheaf.obj (op ((Opens.map g.base).obj U))) =
      ((structureSheafMap φ hφ (IsAdicRing.ideal_spec A).2.1
          (IsAdicRing.ideal_spec B).2.1).hom.app (op U) :
        (Spf A).presheaf.obj (op U) ⟶
          (Spf B).presheaf.obj (op ((Opens.map (TopCat.ofHom (comap φ hφ))).obj U))) ≫
        (Spf B).presheaf.map (homOfLE hle).op := by
    refine (PresheafedSpace.congr_app hg (op U)).trans (congrArg _ (congrArg _ ?_))
    exact Quiver.Hom.unop_inj (Subsingleton.elim _ _)
  exact (ConcreteCategory.congr_hom hc x).symm

end HomEquiv

end TauCeti.FormalScheme.Spf
