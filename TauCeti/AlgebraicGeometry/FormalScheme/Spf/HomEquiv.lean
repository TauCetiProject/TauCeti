/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.FormalScheme.Spf.Morphism
public import TauCeti.AlgebraicGeometry.FormalScheme.Spf.Restrict
public import TauCeti.AlgebraicGeometry.FormalScheme.Spf.SectionsTopology

import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing
import TauCeti.Geometry.RingedSpace.LocallyRingedSpace.Sections

/-!
# Morphisms between formal spectra and automatic continuity

For adic rings `A` and `B` of finite ideal type, global sections send any locally ringed space
morphism `f : Spf B ⟶ Spf A` to `Spf.sectionsHom f : A →+* B`. Local stalk maps force `f` to pull
back open primes along `sectionsHom f`, so `sectionsHom f` is automatically continuous
(`Spf.continuous_sectionsHom`). Restricting to basic opens and using sheaf separatedness yields
`f = Spf.map (sectionsHom f) _` (`Spf.eq_map_sectionsHom`), the bijection
`Spf.homEquiv : (Spf B ⟶ Spf A) ≃ { φ : A →+* B // Continuous φ }` (EGA I, Ch. I, 10.2.2;
Stacks Tag 0AHY), and automatic continuity on sections over every open (`Spf.continuous_c_app`).

## Main definitions

* `TauCeti.FormalScheme.Spf.sectionsHom`: `A →+* B` induced on global sections by `Spf B ⟶ Spf A`.
* `TauCeti.FormalScheme.Spf.homEquiv`: `(Spf B ⟶ Spf A) ≃ { φ : A →+* B // Continuous φ }`.

## Main results

* `TauCeti.FormalScheme.Spf.mem_asIdeal_iff_Γevaluation_eq_zero`,
  `TauCeti.FormalScheme.Spf.mem_radical_iff_forall_Γevaluation_eq_zero`: residue-field criteria for
  open primes and radicals of ideals of definition.
* `TauCeti.FormalScheme.Spf.continuous_sectionsHom`, `TauCeti.FormalScheme.Spf.eq_map_sectionsHom`,
  `TauCeti.FormalScheme.Spf.isHomeomorph_sectionsHom_of_iso`,
  `TauCeti.FormalScheme.Spf.continuous_quotientSectionsTopology_of_cover`,
  `TauCeti.FormalScheme.Spf.continuous_c_app`: automatic continuity and full faithfulness on `Spf`.

## References

* A. Grothendieck and J. Dieudonné, *Éléments de géométrie algébrique I*, Ch. I, 10.2.2.
* [Stacks Project, Tag 0AHY](https://stacks.math.columbia.edu/tag/0AHY).
-/

public section

open CategoryTheory TopologicalSpace Opposite AlgebraicGeometry Topology

namespace TauCeti.FormalScheme.Spf

universe u

variable {A B C : Type u} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [IsAdicRing A]
  [CommRing B] [TopologicalSpace B] [IsTopologicalRing B] [IsAdicRing B]
  [CommRing C] [TopologicalSpace C] [IsTopologicalRing C] [IsAdicRing C]

/-- The canonical global-sections isomorphism `Γ(Spf A, O_{Spf A}) ≅ A` for an adic ring `A` of
finite ideal type, specializing `globalSectionsIso` to `IsAdicRing.ideal A`. -/
noncomputable abbrev globalSectionsIsoOfIsAdicRing (A : Type u) [CommRing A] [TopologicalSpace A]
    [IsTopologicalRing A] [IsAdicRing A] : (Spf A).presheaf.obj (op ⊤) ≅ CommRingCat.of A :=
  @globalSectionsIso A _ _ _ _ (IsAdicRing.ideal_spec A).2.2 (IsAdicRing.ideal_spec A).2.1

/-- The ring homomorphism `A →+* B` induced on global sections by a morphism `f : Spf B ⟶ Spf A`
of locally ringed spaces. -/
noncomputable def sectionsHom (f : Spf B ⟶ Spf A) : A →+* B :=
  ((globalSectionsIsoOfIsAdicRing A).inv ≫ f.c.app (op ⊤) ≫
    (globalSectionsIsoOfIsAdicRing B).hom).hom

private theorem ofHom_sectionsHom (f : Spf B ⟶ Spf A) :
    CommRingCat.ofHom (sectionsHom f) =
      (globalSectionsIsoOfIsAdicRing A).inv ≫ f.c.app (op ⊤) ≫
        (globalSectionsIsoOfIsAdicRing B).hom :=
  rfl

/-- Under the global-section identifications, `f.c.app (op ⊤)` corresponds to `sectionsHom f`. -/
@[reassoc]
theorem c_app_top_comp_globalSectionsIso_hom (f : Spf B ⟶ Spf A) :
    f.c.app (op ⊤) ≫ (globalSectionsIsoOfIsAdicRing B).hom =
      (globalSectionsIsoOfIsAdicRing A).hom ≫ CommRingCat.ofHom (sectionsHom f) := by
  -- `erw`: `TopCat.Presheaf.pushforward` unfolds to `(Spf _).presheaf`.
  erw [ofHom_sectionsHom, Iso.hom_inv_id_assoc]

/-- Under the global-section identifications, `(globalSectionsIso _).inv ≫ f.c.app (op ⊤)` equals
`sectionsHom f` followed by `(globalSectionsIso _).inv`. -/
@[reassoc]
theorem globalSectionsIso_inv_comp_c_app_top (f : Spf B ⟶ Spf A) :
    (globalSectionsIsoOfIsAdicRing A).inv ≫ f.c.app (op ⊤) =
      CommRingCat.ofHom (sectionsHom f) ≫ (globalSectionsIsoOfIsAdicRing B).inv := by
  -- `erw`: `TopCat.Presheaf.pushforward` unfolds to `(Spf _).presheaf`.
  erw [ofHom_sectionsHom, Category.assoc, Category.assoc, Iso.hom_inv_id, Category.comp_id]; rfl

private theorem c_app_top_eq_of_sectionsHom_eq {f g : Spf B ⟶ Spf A}
    (h : sectionsHom f = sectionsHom g) :
    (f.c.app (op ⊤) : (Spf A).presheaf.obj (op ⊤) ⟶ (Spf B).presheaf.obj (op ⊤)) =
      g.c.app (op ⊤) := by
  -- `erw`: `TopCat.Presheaf.pushforward` unfolds to `(Spf B).presheaf`.
  erw [← cancel_epi (globalSectionsIsoOfIsAdicRing A).inv, globalSectionsIso_inv_comp_c_app_top,
    globalSectionsIso_inv_comp_c_app_top, h]

/-- The identity morphism induces the identity ring homomorphism on global sections. -/
@[simp]
theorem sectionsHom_id : sectionsHom (𝟙 (Spf A)) = RingHom.id A :=
  RingHom.ext fun a ↦ ConcreteCategory.congr_hom (globalSectionsIsoOfIsAdicRing A).inv_hom_id a

/-- Global-section homomorphisms are contravariantly functorial. -/
@[simp]
theorem sectionsHom_comp (g : Spf C ⟶ Spf B) (f : Spf B ⟶ Spf A) :
    sectionsHom (g ≫ f) = (sectionsHom g).comp (sectionsHom f) :=
  RingHom.ext fun a ↦ by
    have hc := ConcreteCategory.congr_hom (LocallyRingedSpace.comp_c_app g f (op ⊤))
      ((globalSectionsIsoOfIsAdicRing A).inv a)
    have hfb : (globalSectionsIsoOfIsAdicRing B).inv
        ((globalSectionsIsoOfIsAdicRing B).hom
          (f.c.app (op ⊤) ((globalSectionsIsoOfIsAdicRing A).inv a))) =
        f.c.app (op ⊤) ((globalSectionsIsoOfIsAdicRing A).inv a) :=
      ConcreteCategory.congr_hom (globalSectionsIsoOfIsAdicRing B).hom_inv_id _
    -- `erw`: `TopCat.Presheaf.pushforward` unfolds to `(Spf _).presheaf`, and `(Opens.map _).obj ⊤`
    -- is `⊤` (`Opens.map_top`).
    erw [ConcreteCategory.comp_apply] at hc
    dsimp only [sectionsHom, CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply] at hfb ⊢
    -- `erw`: `(globalSectionsIsoOfIsAdicRing B).inv ≫ (globalSectionsIsoOfIsAdicRing B).hom`
    -- cancels up to `Spf.structureSheaf` unfolding.
    erw [hfb]
    exact congrArg (globalSectionsIsoOfIsAdicRing C).hom hc

/-- Applying `sectionsHom` to `Spf.map φ hφ` recovers `φ`. -/
@[simp]
theorem sectionsHom_map (φ : A →+* B) (hφ : Continuous φ) :
    sectionsHom (map φ hφ) = φ :=
  RingHom.ext fun a ↦ by
    have hmap := ConcreteCategory.congr_hom (map_globalSections φ hφ)
      ((globalSectionsIsoOfIsAdicRing A).inv a)
    have ha : (globalSectionsIsoOfIsAdicRing A).hom ((globalSectionsIsoOfIsAdicRing A).inv a) = a :=
      ConcreteCategory.congr_hom (globalSectionsIsoOfIsAdicRing A).inv_hom_id a
    -- `erw`: `TopCat.Presheaf.pushforward` unfolds to `(Spf B).presheaf`.
    erw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply] at hmap
    dsimp only [sectionsHom, CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply]
    -- `erw`: `sectionsHom` unfolds to
    -- `(globalSectionsIsoOfIsAdicRing _).hom ∘ ... ∘ (globalSectionsIsoOfIsAdicRing _).inv`.
    erw [hmap, ha]; rfl

section ResidueEvaluation

/-- The residue-field isomorphism at an open prime `p` sends the global evaluation of `a ∈ A` to
the image of `a` in `Frac(A ⧸ p)`. -/
@[simp]
theorem stalkResidueFieldEquiv_Γevaluation (p : carrier A) (a : A) :
    stalkResidueFieldEquiv p
        ((Spf A).Γevaluation p ((globalSectionsIsoOfIsAdicRing A).inv a)) =
      algebraMap (A ⧸ (p : PrimeSpectrum A).asIdeal)
        (FractionRing (A ⧸ (p : PrimeSpectrum A).asIdeal)) (Ideal.Quotient.mk _ a) := by
  have := (IsAdicRing.ideal_spec A).2.2
  let u : BasicNeighbourhood p := ⟨1, p.1.isPrime.one_notMem⟩
  let iso1 := basicOpenSectionsIso (IsAdicRing.ideal_spec A).2.1 (IsAdicRing.ideal_spec A).1 1
  have hres : iso1.inv (algebraMap A (AdicRing.CompletedAway A 1) a) =
      (Spf A).presheaf.map (homOfLE (le_top : basicOpen (1 : A) ≤ ⊤)).op
        ((globalSectionsIsoOfIsAdicRing A).inv a) := by
    have h1 := ConcreteCategory.congr_hom (globalSectionsIso_inv_comp_basicOpenSectionsIso_hom
      (IsAdicRing.ideal_spec A).2.1 (IsAdicRing.ideal_spec A).1 (1 : A)) a
    simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply,
      CommRingCat.hom_ofHom] at h1
    rw [← h1]; exact ConcreteCategory.congr_hom iso1.hom_inv_id _
  have hgerm : (Spf A).presheaf.germ (basicOpen u.elem) p (mem_basicOpen.mpr u.notMem)
      (iso1.inv (algebraMap A (AdicRing.CompletedAway A u.elem) a)) =
      (Spf A).presheaf.germ ⊤ p trivial ((globalSectionsIsoOfIsAdicRing A).inv a) := by
    -- `u.elem = 1` definitionally.
    change (Spf A).presheaf.germ (basicOpen 1) p _ _ = _; rw [hres]
    exact TopCat.Presheaf.germ_res_apply (Spf A).presheaf
      (homOfLE (le_top : basicOpen (1 : A) ≤ ⊤)) p (mem_basicOpen.mpr u.notMem) _
  have h0 := stalkResidueFieldEquiv_residue_germ u a
  dsimp only [iso1] at hgerm
  -- `u.elem = 1` definitionally, matching `iso1`.
  change stalkResidueFieldEquiv p ((Spf A).residue p ((Spf A).presheaf.germ (basicOpen u.elem) p
    (mem_basicOpen.mpr u.notMem) (iso1.inv (algebraMap A _ a)))) = _ at h0
  rwa [hgerm] at h0

/-- An element `a ∈ A` lies in an open prime `p` of `A` if and only if its global section vanishes
in the residue field of `Spf A` at `p`. -/
theorem mem_asIdeal_iff_Γevaluation_eq_zero (p : carrier A) (a : A) :
    a ∈ (p : PrimeSpectrum A).asIdeal ↔
      (Spf A).Γevaluation p ((globalSectionsIsoOfIsAdicRing A).inv a) = 0 := by
  have : p.1.asIdeal.IsPrime := p.1.isPrime
  rw [← Ideal.Quotient.eq_zero_iff_mem,
    ← (IsFractionRing.injective (A ⧸ p.1.asIdeal) (FractionRing (A ⧸ p.1.asIdeal))).eq_iff,
    map_zero, ← stalkResidueFieldEquiv_Γevaluation p a, ← map_zero (stalkResidueFieldEquiv p),
    (stalkResidueFieldEquiv p).injective.eq_iff]

/-- For any ideal of definition `I` of `A`, an element `a ∈ A` belongs to `I.radical` if and only if
its global section vanishes in the residue field of `Spf A` at every point. -/
theorem mem_radical_iff_forall_Γevaluation_eq_zero {I : Ideal A} (hI : IsAdic I) (a : A) :
    a ∈ I.radical ↔
      ∀ p : carrier A, (Spf A).Γevaluation p ((globalSectionsIsoOfIsAdicRing A).inv a) = 0 := by
  rw [Ideal.radical_eq_sInf, Ideal.mem_sInf]
  exact ⟨fun ha p ↦ (mem_asIdeal_iff_Γevaluation_eq_zero p a).mp
      (ha ⟨(mem_carrier_iff_le hI).mp p.2, p.1.isPrime⟩),
    fun ha P ⟨hIP, hP⟩ ↦ (mem_asIdeal_iff_Γevaluation_eq_zero
      ⟨⟨P, hP⟩, (mem_carrier_iff_le hI).mpr hIP⟩ a).mpr (ha _)⟩

end ResidueEvaluation

section ContinuityAndFullness

/-- On open prime ideals, every morphism `f : Spf B ⟶ Spf A` acts by preimage along
`sectionsHom f`. -/
theorem asIdeal_base_apply (f : Spf B ⟶ Spf A) (q : carrier B) :
    ((f.base q : carrier A).1).asIdeal =
      (q : PrimeSpectrum B).asIdeal.comap (sectionsHom f) := by
  let q' : Spf B := q; ext a
  rw [Ideal.mem_comap, mem_asIdeal_iff_Γevaluation_eq_zero (f.base q') a,
    mem_asIdeal_iff_Γevaluation_eq_zero q (sectionsHom f a),
    ← map_eq_zero_iff (LocallyRingedSpace.residueFieldMap f q').hom
      (LocallyRingedSpace.residueFieldMap f q').hom.injective]
  have hfa := ConcreteCategory.congr_hom (globalSectionsIso_inv_comp_c_app_top f) a
  -- `erw`: `TopCat.Presheaf.pushforward` unfolds to `(Spf B).presheaf`, identifying `q'` with `q`.
  erw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply] at hfa
  -- `Spf B` agrees definitionally with `Spf.carrier B` (`q' = q`).
  change (LocallyRingedSpace.residueFieldMap f q')
      ((Spf A).Γevaluation (f.base q') ((globalSectionsIsoOfIsAdicRing A).inv a)) = 0 ↔ _
  -- `erw`: match `Γevaluation` after unfolding `Spf` structure sheaf.
  erw [LocallyRingedSpace.Γevaluation_naturality_apply f q'
      ((globalSectionsIsoOfIsAdicRing A).inv a), hfa]
  rfl

/-- **Automatic continuity on affine formal spectra.** Every morphism `f : Spf B ⟶ Spf A` of
locally ringed spaces induces a continuous ring homomorphism `A →+* B` on global sections
(EGA I, Ch. I, 10.2.2). -/
theorem continuous_sectionsHom (f : Spf B ⟶ Spf A) : Continuous (sectionsHom f) := by
  refine IsAdic.continuous_of_map_le_radical (IsAdicRing.ideal_spec A).2.1
    (IsAdicRing.ideal_spec B).2.1 (IsAdicRing.ideal_spec A).1 ?_
  rw [Ideal.map_le_iff_le_comap]; intro a ha
  rw [Ideal.mem_comap, Ideal.radical_eq_sInf, Ideal.mem_sInf]; rintro P ⟨hJP, hP⟩
  let q : carrier B := ⟨⟨P, hP⟩, (mem_carrier_iff_le (IsAdicRing.ideal_spec B).2.1).mpr hJP⟩
  rw [← Ideal.mem_comap (f := sectionsHom f), ← asIdeal_base_apply f q]
  exact (mem_carrier_iff_le (IsAdicRing.ideal_spec A).2.1).mp (f.base q : carrier A).2 ha

/-- The underlying continuous map of `f : Spf B ⟶ Spf A` is `comap (sectionsHom f)`. -/
theorem base_eq_comap_sectionsHom (f : Spf B ⟶ Spf A) :
    f.base = TopCat.ofHom (comap (sectionsHom f) (continuous_sectionsHom f)) := by
  ext q : 2; refine Subtype.ext (PrimeSpectrum.ext ?_); rw [asIdeal_base_apply f q]
  exact (congrArg PrimeSpectrum.asIdeal
    (coe_comap_apply (sectionsHom f) (continuous_sectionsHom f) q)).symm

/-- The preimage of a basic open `D(a)` under `f : Spf B ⟶ Spf A` is `D(sectionsHom f a)`. -/
theorem preimage_basicOpen (f : Spf B ⟶ Spf A) (a : A) :
    (Opens.map f.base).obj (basicOpen a) = basicOpen (sectionsHom f a) := by
  rw [base_eq_comap_sectionsHom f]
  exact comap_basicOpen (sectionsHom f) (continuous_sectionsHom f) a

private theorem sectionsHom_basicOpenι_lhs (f : A) :
    let Af := AdicRing.CompletedAway A f
    let _ := (IsAdicRing.ideal_spec Af).2.2
    let hAf := (IsAdicRing.ideal_spec Af).2.1
    (globalSectionsIsoOfIsAdicRing A).inv ≫
        (Spf A).presheaf.map (eqToHom (congrArg op (basicOpen_one (A := A)).symm)) ≫
        (basicOpenι f).c.app (op (basicOpen (1 : A))) ≫
        (Spf Af).presheaf.map (eqToHom (congrArg op (basicOpenι_preimage_basicOpen f 1))) ≫
        (basicOpenSectionsIso hAf (IsAdicRing.ideal_spec Af).1 (algebraMap A Af 1)).hom =
      CommRingCat.ofHom (sectionsHom (basicOpenι f)) ≫
        CommRingCat.ofHom (algebraMap Af (AdicRing.CompletedAway Af (algebraMap A Af 1))) := by
  intro Af _ hAf
  have htop : (⊤ : Opens (Spf A)) = basicOpen (1 : A) := (basicOpen_one (A := A)).symm
  rw [← Category.assoc ((Spf A).presheaf.map _),
    (basicOpenι f).c.naturality (eqToHom (congrArg op htop)), Category.assoc]
  -- `erw`: `Spf` unfolds so `Opens (carrier _)` matches `Opens (Spf _).toTopCat`.
  erw [← Category.assoc, globalSectionsIso_inv_comp_c_app_top, Category.assoc]
  refine congrArg (CommRingCat.ofHom (sectionsHom (basicOpenι f)) ≫ ·) ?_
  have hmap : ((TopCat.Presheaf.pushforward CommRingCat (basicOpenι f).base).obj
        (Spf Af).presheaf).map (eqToHom (congrArg op htop)) ≫
      (Spf Af).presheaf.map (eqToHom (congrArg op (basicOpenι_preimage_basicOpen f 1))) =
      (Spf Af).presheaf.map (homOfLE (le_top : basicOpen (algebraMap A Af 1) ≤ ⊤)).op := by
    -- `erw`: `pushforward` functor map unfolds to `(Spf Af).presheaf.map` on `Opens.map`.
    erw [← (Spf Af).presheaf.map_comp]
    exact congrArg _ (Quiver.Hom.unop_inj (Subsingleton.elim _ _))
  exact (congrArg ((globalSectionsIsoOfIsAdicRing Af).inv ≫ ·)
    ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ _) hmap))).trans
    (globalSectionsIso_inv_comp_basicOpenSectionsIso_hom hAf (IsAdicRing.ideal_spec Af).1 _)

private theorem sectionsHom_basicOpenι_rhs (f : A) :
    have := (IsAdicRing.ideal_spec A).2.2
    let hA := (IsAdicRing.ideal_spec A).2.1
    (globalSectionsIsoOfIsAdicRing A).inv ≫
        (Spf A).presheaf.map (eqToHom (congrArg op (basicOpen_one (A := A)).symm)) ≫
        (Spf A).presheaf.map (homOfLE ((basicOpen_mul f 1).le.trans inf_le_right) :
          basicOpen (f * 1) ⟶ basicOpen (1 : A)).op ≫
        (basicOpenSectionsIso hA (IsAdicRing.ideal_spec A).1 (f * 1)).hom ≫
        (AdicRing.CompletedAway.iterateEquiv f 1).symm.toCommRingCatIso.hom =
      CommRingCat.ofHom (algebraMap A (AdicRing.CompletedAway A (f * 1))) ≫
        (AdicRing.CompletedAway.iterateEquiv f 1).symm.toCommRingCatIso.hom := by
  intro _ hA
  -- `erw`: `Opens (carrier A)` matches `Opens (Spf A).toPresheafedSpace`.
  erw [← (Spf A).presheaf.map_comp_assoc,
    (Quiver.Hom.unop_inj (Subsingleton.elim _ _) :
      eqToHom (congrArg op (basicOpen_one (A := A)).symm) ≫ (homOfLE _).op =
        (homOfLE (le_top : basicOpen (f * 1) ≤ ⊤)).op)]
  exact globalSectionsIso_inv_comp_basicOpenSectionsIso_hom_assoc
    hA (IsAdicRing.ideal_spec A).1 (f * 1) _

/-- On global sections, the open immersion `basicOpenι f : Spf A_{f} ⟶ Spf A` induces the
canonical map `A → A_{f}`. -/
@[simp]
theorem sectionsHom_basicOpenι (f : A) :
    sectionsHom (basicOpenι f) = algebraMap A (AdicRing.CompletedAway A f) := by
  have := (IsAdicRing.ideal_spec A).2.2
  have := (IsAdicRing.ideal_spec (AdicRing.CompletedAway A f)).2.2
  have hpre := congrArg (fun g ↦ (globalSectionsIsoOfIsAdicRing A).inv ≫
    (Spf A).presheaf.map (eqToHom (congrArg op (basicOpen_one (A := A)).symm)) ≫ g)
    (basicOpenι_c_app f 1)
  ext a
  have ha := ConcreteCategory.congr_hom
    ((sectionsHom_basicOpenι_lhs f).symm.trans (hpre.trans (sectionsHom_basicOpenι_rhs f))) a
  simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply,
    CommRingCat.hom_ofHom, RingEquiv.toCommRingCatIso_hom, RingEquiv.coe_toRingHom] at ha
  have ha' := congrArg (AdicRing.CompletedAway.iterateEquiv f 1) ha
  have hmem : f * 1 ∈ (Ideal.span {f} ⊔ IsAdicRing.ideal A).radical :=
    Ideal.le_radical (Ideal.mem_sup_left (Ideal.mem_span_singleton.mpr (dvd_mul_right f 1)))
  rw [AdicRing.CompletedAway.iterateEquiv_algebraMap f 1 hmem, RingEquiv.apply_symm_apply,
    ← (AdicRing.CompletedAway.restrict (A := A) (f := f) (g := f * 1) hmem).commutes a] at ha'
  have h_inj : ∀ (g : A) (_ : g = f) (hg : g ∈ (Ideal.span {f} ⊔ IsAdicRing.ideal A).radical),
      Function.Injective (AdicRing.CompletedAway.restrict (A := A) (f := f) (g := g) hg) := by
    rintro _ rfl hg; rw [AdicRing.CompletedAway.restrict_self]; exact Function.injective_id
  exact h_inj (f * 1) (mul_one f) hmem ha'

private theorem isIso_basicOpenι_c_app_self (f : A) :
    IsIso ((basicOpenι f).c.app (op (basicOpen f))) := by
  have heq : (isOpenImmersion_basicOpenι f).base_open.functor.obj ⊤ = basicOpen f := by
    ext p
    -- Unfold `IsOpenMap.functor.obj ⊤` to the image of `Set.univ`.
    change p ∈ (basicOpenι f).base '' Set.univ ↔ _
    rw [Set.image_univ, range_basicOpenι]; rfl
  rw [← heq]; exact (isOpenImmersion_basicOpenι f).c_iso ⊤

private theorem base_eq_of_sectionsHom_eq {f g : Spf B ⟶ Spf A}
    (h : sectionsHom f = sectionsHom g) : f.base = g.base := by
  ext q : 2; refine Subtype.ext (PrimeSpectrum.ext ?_)
  rw [asIdeal_base_apply f q, asIdeal_base_apply g q, h]

private theorem lift_basicOpenι_c_app_eq {f g : Spf B ⟶ Spf A}
    (h : sectionsHom f = sectionsHom g) (a : A) :
    let ιφ := basicOpenι (sectionsHom f a)
    let Ua : Opens (Spf A) := basicOpen a
    (ιφ ≫ f).c.app (op Ua) ≫ (Spf (AdicRing.CompletedAway B (sectionsHom f a))).presheaf.map
        (eqToHom (congrArg op (congrArg (fun k ↦ (Opens.map k).obj Ua)
          (by rw [LocallyRingedSpace.comp_base, LocallyRingedSpace.comp_base,
            base_eq_of_sectionsHom_eq h] : (ιφ ≫ f).base = (ιφ ≫ g).base)))) =
      (ιφ ≫ g).c.app (op Ua) := by
  intro ιφ Ua; let ιa := basicOpenι a
  have hrange_f : Set.range (ιφ ≫ f).base ⊆ Set.range ιa.base := by
    rintro _ ⟨q, rfl⟩
    rw [range_basicOpenι, LocallyRingedSpace.comp_base, TopCat.coe_comp, Function.comp_apply]
    -- `Opens.mem_map` identifies membership in `(Opens.map f.base).obj` with `f.base _ ∈ _`.
    change ιφ.base q ∈ (Opens.map f.base).obj (basicOpen a)
    rw [preimage_basicOpen f a]
    exact (range_basicOpenι (sectionsHom f a)).le (Set.mem_range_self q)
  have hrange_g : Set.range (ιφ ≫ g).base ⊆ Set.range ιa.base := by
    rwa [LocallyRingedSpace.comp_base, ← base_eq_of_sectionsHom_eq h]
  let fa := LocallyRingedSpace.IsOpenImmersion.lift ιa (ιφ ≫ f) hrange_f
  let ga := LocallyRingedSpace.IsOpenImmersion.lift ιa (ιφ ≫ g) hrange_g
  have hfa : fa ≫ ιa = ιφ ≫ f := LocallyRingedSpace.IsOpenImmersion.lift_fac _ _ hrange_f
  have hga : ga ≫ ιa = ιφ ≫ g := LocallyRingedSpace.IsOpenImmersion.lift_fac _ _ hrange_g
  have hc_top : fa.c.app (op ⊤) = ga.c.app (op ⊤) := c_app_top_eq_of_sectionsHom_eq <|
    AdicRing.CompletedAway.ringHom_ext A a (continuous_sectionsHom fa)
      (continuous_sectionsHom ga) <| by
      rw [← sectionsHom_basicOpenι a, ← sectionsHom_comp fa ιa, ← sectionsHom_comp ga ιa,
        hfa, hga, sectionsHom_comp, sectionsHom_comp]
      exact congrArg (sectionsHom ιφ).comp h
  have htop_a : (Opens.map ιa.base).obj Ua = ⊤ := by
    ext q; exact iff_true_intro ((range_basicOpenι a).le (Set.mem_range_self q))
  rw [PresheafedSpace.congr_app (congrArg LocallyRingedSpace.Hom.toHom hfa.symm) (op Ua),
    PresheafedSpace.congr_app (congrArg LocallyRingedSpace.Hom.toHom hga.symm) (op Ua),
    LocallyRingedSpace.comp_c_app_of_map_eq_top fa ιa htop_a,
    LocallyRingedSpace.comp_c_app_of_map_eq_top ga ιa htop_a]
  simp only [Category.assoc]; rw [hc_top]; congr 3
  rw [← Functor.map_comp, ← Functor.map_comp, ← Functor.map_comp]
  exact congrArg _ (Quiver.Hom.unop_inj (Subsingleton.elim _ _))

private theorem c_app_basicOpen_eq_of_sectionsHom_eq {f g : Spf B ⟶ Spf A}
    (h : sectionsHom f = sectionsHom g) (a : A) :
    f.c.app (op (basicOpen a)) ≫
        (Spf B).presheaf.map (eqToHom (congrArg op (by
          rw [preimage_basicOpen f a, preimage_basicOpen g a, h]))) =
      g.c.app (op (basicOpen a)) := by
  let ιφ := basicOpenι (sectionsHom f a)
  have hpre_fg : (Opens.map f.base).obj (basicOpen a) = (Opens.map g.base).obj (basicOpen a) :=
    congrArg (fun k ↦ (Opens.map k).obj (basicOpen a)) (base_eq_of_sectionsHom_eq h)
  have hiso : IsIso (ιφ.c.app (op ((Opens.map g.base).obj (basicOpen a)))) := by
    have hpre_g : (Opens.map g.base).obj (basicOpen a) = basicOpen (sectionsHom f a) := by
      rw [preimage_basicOpen g a, h]
    rw [hpre_g]; exact isIso_basicOpenι_c_app_self (sectionsHom f a)
  rw [← cancel_mono (ιφ.c.app (op ((Opens.map g.base).obj (basicOpen a)))), Category.assoc,
    ιφ.c.naturality (eqToHom (congrArg op hpre_fg)), ← Category.assoc,
    ← LocallyRingedSpace.comp_c_app ιφ f (op (basicOpen a)),
    ← LocallyRingedSpace.comp_c_app ιφ g (op (basicOpen a))]
  exact (congrArg ((ιφ ≫ f).c.app (op (basicOpen a)) ≫ ·)
    (congrArg (Spf (AdicRing.CompletedAway B (sectionsHom f a))).presheaf.map
      (Quiver.Hom.unop_inj (Subsingleton.elim _ _)))).trans (lift_basicOpenι_c_app_eq h a)

/-- **Morphisms between formal spectra are determined by their action on global sections.** -/
theorem hom_ext_of_sectionsHom_eq {f g : Spf B ⟶ Spf A} (h : sectionsHom f = sectionsHom g) :
    f = g := by
  have hbase : f.base = g.base := base_eq_of_sectionsHom_eq h
  apply LocallyRingedSpace.Hom.ext'; refine PresheafedSpace.Hom.ext _ _ hbase ?_
  ext U : 1; refine CommRingCat.hom_ext (RingHom.ext fun s ↦ ?_)
  let U' : Opens (carrier A) := U
  let Vp (p : { a : A // basicOpen a ≤ U' }) : Opens (Spf A) := basicOpen p.1
  have hcov : (Opens.map g.base).obj U ≤
      ⨆ p : { a : A // basicOpen a ≤ U' }, (Opens.map g.base).obj (Vp p) := fun q hq ↦
    let ⟨a, ha, haU⟩ := exists_basicOpen_le (U := U') hq; Opens.mem_iSup.mpr ⟨⟨a, haU⟩, ha⟩
  refine TopCat.Sheaf.eq_of_locally_eq' (Spf B).sheaf
    (fun p : { a : A // basicOpen a ≤ U' } ↦ (Opens.map g.base).obj (Vp p))
    ((Opens.map g.base).obj U) (fun p ↦ (Opens.map g.base).map (homOfLE p.2))
    hcov _ _ fun p ↦ ?_
  have hnat_g := ConcreteCategory.congr_hom (g.c.naturality (homOfLE p.2).op) s
  have hnat_f := ConcreteCategory.congr_hom (f.c.naturality (homOfLE p.2).op) s
  have hbas := ConcreteCategory.congr_hom (c_app_basicOpen_eq_of_sectionsHom_eq h p.1)
    ((Spf A).presheaf.map (homOfLE p.2).op s)
  have hpre_p : (Opens.map f.base).obj (Vp p) = (Opens.map g.base).obj (Vp p) :=
    congrArg (fun k ↦ (Opens.map k).obj (Vp p)) hbase
  have hcomm : (Spf B).presheaf.map ((eqToHom (congrArg (fun k ↦ (Opens.map k).op) hbase)).app
        (op U)) ≫ (Spf B).presheaf.map ((Opens.map g.base).map (homOfLE p.2)).op =
      (Spf B).presheaf.map ((Opens.map f.base).map (homOfLE p.2)).op ≫
        (Spf B).presheaf.map (eqToHom (congrArg op hpre_p)) := by
    rw [← Functor.map_comp, ← Functor.map_comp]
    exact congrArg (Spf B).presheaf.map (Quiver.Hom.unop_inj (Subsingleton.elim _ _))
  have hcs := ConcreteCategory.congr_hom hcomm (f.c.app (op U) s)
  simp only [CommRingCat.hom_comp, RingHom.coe_comp] at hnat_g hnat_f hbas hcs
  exact hcs.trans ((congrArg ((Spf B).presheaf.map (eqToHom (congrArg op hpre_p)))
    hnat_f.symm).trans (hbas.trans hnat_g))

/-- **Fullness of `Spf`.** Every morphism `f : Spf B ⟶ Spf A` of locally ringed spaces is induced
by its continuous global-section homomorphism `sectionsHom f` (EGA I, Ch. I, 10.2.2). -/
theorem eq_map_sectionsHom (f : Spf B ⟶ Spf A) :
    f = map (sectionsHom f) (continuous_sectionsHom f) :=
  hom_ext_of_sectionsHom_eq (by simp)

/-- The open immersion `basicOpenι f : Spf A_{f} ⟶ Spf A` is `Spf.map` of `A → A_{f}`. -/
theorem basicOpenι_eq_map (f : A) :
    basicOpenι f = map (algebraMap A (AdicRing.CompletedAway A f))
      (AdicRing.CompletedAway.continuous_algebraMap A f) := by
  rw [eq_map_sectionsHom (basicOpenι f)]; congr 1; exact sectionsHom_basicOpenι f

/-- **The morphism correspondence for affine formal schemes.** Morphisms `Spf B ⟶ Spf A` of locally
ringed spaces correspond bijectively to continuous ring homomorphisms `A →+* B`
(EGA I, Ch. I, 10.2.2; Stacks Tag 0AHY). -/
noncomputable def homEquiv : (Spf B ⟶ Spf A) ≃ { φ : A →+* B // Continuous φ } where
  toFun f := ⟨sectionsHom f, continuous_sectionsHom f⟩
  invFun φ := map φ.1 φ.2
  left_inv f := (eq_map_sectionsHom f).symm
  right_inv φ := Subtype.ext (sectionsHom_map φ.1 φ.2)

/-- The forward direction of `homEquiv` sends a morphism `Spf B ⟶ Spf A` to `sectionsHom`. -/
@[simp]
theorem homEquiv_apply_val (f : Spf B ⟶ Spf A) : (homEquiv f).1 = sectionsHom f := (rfl)

/-- The inverse of `homEquiv` sends a continuous ring homomorphism to `Spf.map`. -/
@[simp]
theorem homEquiv_symm_apply (φ : { φ : A →+* B // Continuous φ }) :
    homEquiv.symm φ = map φ.1 φ.2 := (rfl)

/-- An isomorphism `Spf B ≅ Spf A` induces a continuous ring equivalence `A ≃+* B` whose inverse is
also continuous. -/
theorem isHomeomorph_sectionsHom_of_iso (e : Spf B ≅ Spf A) :
    IsHomeomorph (sectionsHom e.hom) :=
  (Homeomorph.mk (RingEquiv.ofRingHom (sectionsHom e.hom) (sectionsHom e.inv)
    (by rw [← sectionsHom_comp, Iso.hom_inv_id, sectionsHom_id])
    (by rw [← sectionsHom_comp, Iso.inv_hom_id, sectionsHom_id])).toEquiv
    (continuous_sectionsHom e.hom) (continuous_sectionsHom e.inv)).isHomeomorph

end ContinuityAndFullness

section AutomaticContinuityOnSections

omit [IsAdicRing B] in
/-- Continuity of a map into `Γ(U, O_{Spf B})` for `quotientSectionsTopology` reduces to
continuity after restricting to every member of an open cover `V i ≤ U`. -/
theorem continuous_quotientSectionsTopology_of_cover {Z ι : Type*} [TopologicalSpace Z]
    {I : Ideal B} (hI : IsAdic I) {U : Opens (carrier B)} {V : ι → Opens (carrier B)}
    (hV : ∀ i, V i ≤ U) (hcov : U ≤ ⨆ i, V i) (k : Z → (structureSheaf hI).obj.obj (op U))
    (hk : ∀ i, @Continuous _ _ _ (quotientSectionsTopology hI (V i))
      (fun s ↦ (structureSheaf hI).obj.map (homOfLE (hV i)).op (k s))) :
    @Continuous _ _ _ (quotientSectionsTopology hI U) k := by
  let _ : TopologicalSpace ((structureSheaf hI).obj.obj (op U)) := quotientSectionsTopology hI U
  let _ (i : ι) : TopologicalSpace ((structureSheaf hI).obj.obj (op (V i))) :=
    quotientSectionsTopology hI (V i)
  exact (quotientSectionsTopology_glue hI hV hcov).isInducing.continuous_iff.mpr (continuous_pi hk)

private theorem continuous_structureSheafMap_sectionsTopology (φ : A →+* B) (hφ : Continuous φ)
    (U : Opens (carrier A)) :
    @Continuous _ _
      (sectionsTopology (IsAdicRing.ideal_spec A).2.1 U)
      (sectionsTopology (IsAdicRing.ideal_spec B).2.1
        ((Opens.map (TopCat.ofHom (comap φ hφ))).obj U))
      ((structureSheafMap φ hφ (IsAdicRing.ideal_spec A).2.1
        (IsAdicRing.ideal_spec B).2.1).hom.app (op U)) := by
  let hA := (IsAdicRing.ideal_spec A).2.1; let hB := (IsAdicRing.ideal_spec B).2.1
  let _ : TopologicalSpace ((structureSheaf hA).obj.obj (op U)) := sectionsTopology hA U
  refine (continuous_iff_sectionsTopology hB
    ((Opens.map (TopCat.ofHom (comap φ hφ))).obj U)).mpr fun n ↦ ?_
  obtain ⟨m, hm⟩ := hA.exists_pow_succ_le_comap (hB.isOpen_pow (n + 1)) hφ
  have hsheaf := structureSheafMap_comp_quotientProjection φ hφ hA hB
    (is_ideal_adic_pow hA m.succ_pos) n hm
  rw [toQuotientSheaf_pow_succ] at hsheaf
  have hfun :
      (((quotientProjection hB n).hom.app (op ((Opens.map (TopCat.ofHom (comap φ hφ))).obj U))) :
          _ → _) ∘ ((structureSheafMap φ hφ hA hB).hom.app (op U)) =
        ((quotientMap φ hφ (is_ideal_adic_pow hA m.succ_pos) (is_ideal_adic_pow hB n.succ_pos)
          hm).hom.app (op U)) ∘ ((quotientProjection hA m).hom.app (op U)) :=
    funext fun s ↦ ConcreteCategory.congr_hom (congrArg (fun η ↦ η.hom.app (op U)) hsheaf) s
  rw [hfun]
  exact @Continuous.comp _ _ _ (sectionsTopology hA U) ⊥ ⊥ _ _ continuous_bot
    (continuous_quotientProjection_app hA U m)

private theorem structureSheafMap_restrict_basicOpen_apply (φ : A →+* B) (hφ : Continuous φ)
    {U : Opens (carrier A)} {b : B}
    (hb : basicOpen b ≤ (Opens.map (TopCat.ofHom (comap φ hφ))).obj U)
    {a : A} (haU : basicOpen a ≤ U) (hWle : basicOpen (b * φ a) ≤ basicOpen b)
    (hWpre : basicOpen (b * φ a) ≤ (Opens.map (TopCat.ofHom (comap φ hφ))).obj (basicOpen a))
    (s : (structureSheaf (IsAdicRing.ideal_spec A).2.1).obj.obj (op U)) :
    (structureSheaf (IsAdicRing.ideal_spec B).2.1).obj.map (homOfLE hWle).op
        ((structureSheaf (IsAdicRing.ideal_spec B).2.1).obj.map (homOfLE hb).op
          ((structureSheafMap φ hφ (IsAdicRing.ideal_spec A).2.1
            (IsAdicRing.ideal_spec B).2.1).hom.app (op U) s)) =
      (structureSheaf (IsAdicRing.ideal_spec B).2.1).obj.map (homOfLE hWpre).op
        ((structureSheafMap φ hφ (IsAdicRing.ideal_spec A).2.1
          (IsAdicRing.ideal_spec B).2.1).hom.app (op (basicOpen a))
            ((structureSheaf (IsAdicRing.ideal_spec A).2.1).obj.map (homOfLE haU).op s)) := by
  let hA := (IsAdicRing.ideal_spec A).2.1; let hB := (IsAdicRing.ideal_spec B).2.1
  let σ := structureSheafMap φ hφ hA hB
  have h1 := ConcreteCategory.congr_hom
    ((structureSheaf hB).obj.map_comp (homOfLE hb).op (homOfLE hWle).op) (σ.hom.app (op U) s)
  have h2 := congrArg ((structureSheaf hB).obj.map (homOfLE hWpre).op)
    (ConcreteCategory.congr_hom (σ.hom.naturality (homOfLE haU).op) s)
  have h3 := ConcreteCategory.congr_hom ((structureSheaf hB).obj.map_comp
    ((Opens.map (TopCat.ofHom (comap φ hφ))).map (homOfLE haU)).op (homOfLE hWpre).op)
    (σ.hom.app (op U) s)
  simp only [CommRingCat.hom_comp, RingHom.coe_comp] at h1 h3
  have hsub := congrArg (structureSheaf hB).obj.map (Quiver.Hom.unop_inj (Subsingleton.elim
    (homOfLE hWle ≫ homOfLE hb)
    (homOfLE hWpre ≫ (Opens.map (TopCat.ofHom (comap φ hφ))).map (homOfLE haU))))
  exact h1.symm.trans
    ((ConcreteCategory.congr_hom hsub (σ.hom.app (op U) s)).trans (h3.trans h2.symm))

private theorem continuous_structureSheafMap_quotientSectionsTopology (φ : A →+* B)
    (hφ : Continuous φ) (U : Opens (carrier A)) :
    @Continuous _ _
      (quotientSectionsTopology (IsAdicRing.ideal_spec A).2.1 U)
      (quotientSectionsTopology (IsAdicRing.ideal_spec B).2.1
        ((Opens.map (TopCat.ofHom (comap φ hφ))).obj U))
      ((structureSheafMap φ hφ (IsAdicRing.ideal_spec A).2.1
        (IsAdicRing.ideal_spec B).2.1).hom.app (op U)) := by
  let hA := (IsAdicRing.ideal_spec A).2.1; let hB := (IsAdicRing.ideal_spec B).2.1
  let f := TopCat.ofHom (comap φ hφ); let σ := structureSheafMap φ hφ hA hB
  let _ : TopologicalSpace ((structureSheaf hA).obj.obj (op U)) := quotientSectionsTopology hA U
  refine (continuous_iff_quotientSectionsTopology hB ((Opens.map f).obj U)).mpr fun b hb ↦ ?_
  rw [← quotientSectionsTopology_basicOpen hB b]
  have hcomap (a : A) : (Opens.map f).obj (basicOpen a) = basicOpen (φ a) :=
    comap_basicOpen φ hφ a
  have hWle (p : { a : A // basicOpen a ≤ U }) : basicOpen (b * φ p.1) ≤ basicOpen b := by
    rw [basicOpen_mul]; exact inf_le_left
  have hWpre (p : { a : A // basicOpen a ≤ U }) :
      basicOpen (b * φ p.1) ≤ (Opens.map f).obj (basicOpen p.1) := by
    rw [basicOpen_mul, hcomap p.1]; exact inf_le_right
  have hcov : basicOpen b ≤ ⨆ p : { a : A // basicOpen a ≤ U }, basicOpen (b * φ p.1) := by
    intro q hqb
    obtain ⟨a, ha, haU⟩ := exists_basicOpen_le (U := U) (hb hqb)
    exact Opens.mem_iSup.mpr ⟨⟨a, haU⟩, by
      rw [basicOpen_mul]; exact ⟨hqb, (hcomap a).symm ▸ ha⟩⟩
  refine continuous_quotientSectionsTopology_of_cover hB hWle hcov
    (fun s ↦ (structureSheaf hB).obj.map (homOfLE hb).op (σ.hom.app (op U) s)) fun p ↦ ?_
  have hfun : (fun s ↦ (structureSheaf hB).obj.map (homOfLE (hWle p)).op
        ((structureSheaf hB).obj.map (homOfLE hb).op (σ.hom.app (op U) s))) =
      ((structureSheaf hB).obj.map (homOfLE (hWpre p)).op) ∘ (σ.hom.app (op (basicOpen p.1))) ∘
        ((structureSheaf hA).obj.map (homOfLE p.2).op) :=
    funext fun s ↦ structureSheafMap_restrict_basicOpen_apply φ hφ hb p.2 (hWle p) (hWpre p) s
  rw [hfun]
  refine @Continuous.comp _ _ _ (quotientSectionsTopology hA U)
    (quotientSectionsTopology hB ((Opens.map f).obj (basicOpen p.1)))
    (quotientSectionsTopology hB (basicOpen (b * φ p.1))) _ _
    (quotientSectionsTopology_restrict hB (hWpre p))
    (@Continuous.comp _ _ _ (quotientSectionsTopology hA U) (sectionsTopology hA (basicOpen p.1))
      (quotientSectionsTopology hB ((Opens.map f).obj (basicOpen p.1))) _ _
      ((by rw [hcomap p.1]; exact quotientSectionsTopology_basicOpen hB (φ p.1) :
          quotientSectionsTopology hB ((Opens.map f).obj (basicOpen p.1)) =
            sectionsTopology hB ((Opens.map f).obj (basicOpen p.1))) ▸
        continuous_structureSheafMap_sectionsTopology φ hφ (basicOpen p.1))
      (continuous_restrict_basicOpen_sectionsTopology hA p.2))

/-- **Automatic continuity on sections over every open of a formal spectrum.** For every morphism
`f : Spf B ⟶ Spf A` of locally ringed spaces and every open `U` of `Spf A`, the section map
`f.c.app (op U) : Γ(U, O_{Spf A}) → Γ(f⁻¹ U, O_{Spf B})` is continuous for
`Spf.quotientSectionsTopology` (EGA I, Ch. I, 10.4.5). -/
theorem continuous_c_app (f : Spf B ⟶ Spf A) (U : Opens (carrier A)) :
    @Continuous _ _
      (quotientSectionsTopology (IsAdicRing.ideal_spec A).2.1 U)
      (quotientSectionsTopology (IsAdicRing.ideal_spec B).2.1 ((Opens.map f.base).obj U))
      (f.c.app (op U)) := by
  obtain ⟨φ, hφ, rfl⟩ : ∃ (φ : A →+* B) (hφ : Continuous φ), f = map φ hφ :=
    ⟨sectionsHom f, continuous_sectionsHom f, eq_map_sectionsHom f⟩
  have h : ∀ g : (Spf B).toPresheafedSpace ⟶ (Spf A).toPresheafedSpace,
      g = ⟨TopCat.ofHom (comap φ hφ), (structureSheafMap φ hφ _ _).hom⟩ →
      @Continuous _ _ (quotientSectionsTopology (IsAdicRing.ideal_spec A).2.1 U)
        (quotientSectionsTopology (IsAdicRing.ideal_spec B).2.1 ((Opens.map g.base).obj U))
        (g.c.app (op U)) := fun _ hg ↦
    hg ▸ continuous_structureSheafMap_quotientSectionsTopology φ hφ U
  exact h (map φ hφ).toHom (map_toHom φ hφ)

end AutomaticContinuityOnSections

end TauCeti.FormalScheme.Spf
