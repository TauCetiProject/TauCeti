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

/-!
# Morphisms between formal spectra and automatic continuity

Let `A` and `B` be adic rings of finite ideal type. Taking global sections identifies every
morphism `f : Spf B ⟶ Spf A` of locally ringed spaces with a ring homomorphism
`Spf.sectionsHom f : A →+* B`.

Because stalk maps are local and residue-field maps are injective, `f` acts on open prime ideals by
pulling them back along `sectionsHom f`. Consequently, `sectionsHom f` sends any ideal of definition
of `A` into every open prime of `B`, hence into the radical of any ideal of definition of `B`.
Since `A` admits a finitely generated ideal of definition, this implies that `sectionsHom f` is
automatically continuous (`Spf.continuous_sectionsHom`).

Applying automatic continuity to the restrictions `Spf B_{φ(a)} ⟶ Spf A_{a}` over basic open sets
shows that the induced maps on completed localisations are continuous and agree on the image of
`A`, hence coincide by `TauCeti.AdicRing.CompletedAway.ringHom_ext`. By sheaf separatedness on the
basis of basic open sets, `f` equals `Spf.map (sectionsHom f) (continuous_sectionsHom f)`
(`Spf.eq_map_sectionsHom`), yielding the bijection
`(Spf B ⟶ Spf A) ≃ { φ : A →+* B // Continuous φ }` (`Spf.homEquiv`; EGA I, Ch. I, 10.2.2;
Stacks Tag 0AHY).

As immediate consequences, every isomorphism `Spf B ≅ Spf A` induces a homeomorphic ring
equivalence `A ≃+* B`, and every morphism `f : Spf B ⟶ Spf A` is continuous on rings of sections
over every open subset for `Spf.quotientSectionsTopology` (`Spf.continuous_c_app`).

## Main definitions

* `TauCeti.FormalScheme.Spf.sectionsHom`: the ring homomorphism `A →+* B` induced on global
  sections by a morphism `Spf B ⟶ Spf A`.
* `TauCeti.FormalScheme.Spf.homEquiv`: the bijection between morphisms `Spf B ⟶ Spf A` and
  continuous ring homomorphisms `A →+* B`.

## Main results

* `TauCeti.FormalScheme.Spf.mem_asIdeal_iff_Γevaluation_eq_zero`: an element `a ∈ A` lies in an
  open prime `p` iff its global section vanishes in the residue field of `Spf A` at `p`.
* `TauCeti.FormalScheme.Spf.mem_radical_iff_forall_Γevaluation_eq_zero`: for any ideal of
  definition `I` of `A`, `a ∈ I.radical` iff its global section vanishes in every residue field.
* `TauCeti.FormalScheme.Spf.continuous_sectionsHom`: every morphism `Spf B ⟶ Spf A` induces a
  continuous ring homomorphism `A →+* B`.
* `TauCeti.FormalScheme.Spf.eq_map_sectionsHom`: every morphism `Spf B ⟶ Spf A` is `Spf.map` of
  its global-section homomorphism.
* `TauCeti.FormalScheme.Spf.isHomeomorph_sectionsHom_of_iso`: an isomorphism `Spf B ≅ Spf A`
  induces a homeomorphism `A → B`.
* `TauCeti.FormalScheme.Spf.continuous_c_app`: every morphism `Spf B ⟶ Spf A` is continuous on
  sections over every open for `Spf.quotientSectionsTopology`.

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

/-- Shorthand for `globalSectionsIso` using the chosen ideal of definition of `A`. -/
private noncomputable abbrev globalIso (A : Type u) [CommRing A] [TopologicalSpace A]
    [IsTopologicalRing A] [IsAdicRing A] : (Spf A).presheaf.obj (op ⊤) ≅ CommRingCat.of A :=
  @globalSectionsIso A _ _ _ _ (IsAdicRing.ideal_spec A).2.2 (IsAdicRing.ideal_spec A).2.1

/-- The global-sections map `Γ(⊤, Spf A) ⟶ Γ(⊤, Spf B)` of a morphism `f : Spf B ⟶ Spf A`, typed
directly between the global-section objects (avoiding pushforward definitional unfolding). -/
private noncomputable abbrev globalApp (f : Spf B ⟶ Spf A) :
    (Spf A).presheaf.obj (op ⊤) ⟶ (Spf B).presheaf.obj (op ⊤) :=
  f.c.app (op ⊤)

/-- The ring homomorphism `A →+* B` induced on global sections by a morphism `f : Spf B ⟶ Spf A`
of locally ringed spaces. -/
noncomputable def sectionsHom (f : Spf B ⟶ Spf A) : A →+* B :=
  ((globalIso A).inv ≫ globalApp f ≫ (globalIso B).hom).hom

/-- Under the global-section identifications, `f.c.app (op ⊤)` corresponds to `sectionsHom f`. -/
@[reassoc]
theorem c_app_top_comp_globalSectionsIso_hom (f : Spf B ⟶ Spf A) :
    f.c.app (op ⊤) ≫
        (@globalSectionsIso B _ _ _ _ (IsAdicRing.ideal_spec B).2.2
          (IsAdicRing.ideal_spec B).2.1).hom =
      (@globalSectionsIso A _ _ _ _ (IsAdicRing.ideal_spec A).2.2
          (IsAdicRing.ideal_spec A).2.1).hom ≫
        CommRingCat.ofHom (sectionsHom f) := by
  change globalApp f ≫ (globalIso B).hom =
    (globalIso A).hom ≫ ((globalIso A).inv ≫ globalApp f ≫ (globalIso B).hom)
  rw [Iso.hom_inv_id_assoc]

/-- Under the global-section identifications, `(globalSectionsIso _).inv ≫ f.c.app (op ⊤)` equals
`sectionsHom f` followed by `(globalSectionsIso _).inv`. -/
@[reassoc]
theorem globalSectionsIso_inv_comp_c_app_top (f : Spf B ⟶ Spf A) :
    (@globalSectionsIso A _ _ _ _ (IsAdicRing.ideal_spec A).2.2
        (IsAdicRing.ideal_spec A).2.1).inv ≫ f.c.app (op ⊤) =
      CommRingCat.ofHom (sectionsHom f) ≫
        (@globalSectionsIso B _ _ _ _ (IsAdicRing.ideal_spec B).2.2
          (IsAdicRing.ideal_spec B).2.1).inv := by
  change (globalIso A).inv ≫ globalApp f =
    ((globalIso A).inv ≫ globalApp f ≫ (globalIso B).hom) ≫ (globalIso B).inv
  rw [Category.assoc, Category.assoc, Iso.hom_inv_id, Category.comp_id]

private theorem globalIso_inv_comp_globalApp (f : Spf B ⟶ Spf A) :
    (globalIso A).inv ≫ globalApp f = CommRingCat.ofHom (sectionsHom f) ≫ (globalIso B).inv :=
  globalSectionsIso_inv_comp_c_app_top f

private theorem globalApp_eq_of_sectionsHom_eq {f g : Spf B ⟶ Spf A}
    (h : sectionsHom f = sectionsHom g) : globalApp f = globalApp g := by
  rw [← cancel_epi (globalIso A).inv, globalIso_inv_comp_globalApp,
    globalIso_inv_comp_globalApp, h]

/-- The identity morphism induces the identity ring homomorphism on global sections. -/
@[simp]
theorem sectionsHom_id : sectionsHom (𝟙 (Spf A)) = RingHom.id A := by
  ext a
  have hid : globalApp (𝟙 (Spf A)) = 𝟙 _ := rfl
  change ((globalIso A).inv ≫ globalApp (𝟙 (Spf A)) ≫ (globalIso A).hom) a = a
  rw [hid, Category.id_comp, Iso.inv_hom_id]
  rfl

/-- Global-section homomorphisms are contravariantly functorial. -/
@[simp]
theorem sectionsHom_comp (g : Spf C ⟶ Spf B) (f : Spf B ⟶ Spf A) :
    sectionsHom (g ≫ f) = (sectionsHom g).comp (sectionsHom f) := by
  have hcomp : globalApp (g ≫ f) = globalApp f ≫ globalApp g :=
    LocallyRingedSpace.comp_c_app g f (op ⊤)
  have heq : (globalIso A).inv ≫ globalApp (g ≫ f) ≫ (globalIso C).hom =
      ((globalIso A).inv ≫ globalApp f ≫ (globalIso B).hom) ≫
        ((globalIso B).inv ≫ globalApp g ≫ (globalIso C).hom) := by
    rw [hcomp]
    simp only [Category.assoc, Iso.hom_inv_id_assoc]
  exact congrArg CommRingCat.Hom.hom heq

/-- Applying `sectionsHom` to `Spf.map φ hφ` recovers `φ`. -/
@[simp]
theorem sectionsHom_map (φ : A →+* B) (hφ : Continuous φ) :
    sectionsHom (map φ hφ) = φ := by
  have h : globalApp (map φ hφ) ≫ (globalIso B).hom = (globalIso A).hom ≫ CommRingCat.ofHom φ :=
    map_globalSections φ hφ
  ext a
  change ((globalIso A).inv ≫ globalApp (map φ hφ) ≫ (globalIso B).hom) a = φ a
  rw [h, Iso.inv_hom_id_assoc]
  rfl

section ResidueEvaluation

/-- The residue-field isomorphism at an open prime `p` sends the global evaluation of `a ∈ A` to
the image of `a` in `Frac(A ⧸ p)`. -/
@[simp]
theorem stalkResidueFieldEquiv_Γevaluation (p : carrier A) (a : A) :
    stalkResidueFieldEquiv p
        ((Spf A).Γevaluation p
          ((@globalSectionsIso A _ _ _ _ (IsAdicRing.ideal_spec A).2.2
            (IsAdicRing.ideal_spec A).2.1).inv a)) =
      algebraMap (A ⧸ (p : PrimeSpectrum A).asIdeal)
        (FractionRing (A ⧸ (p : PrimeSpectrum A).asIdeal)) (Ideal.Quotient.mk _ a) := by
  have := (IsAdicRing.ideal_spec A).2.2
  let u : BasicNeighbourhood p := ⟨1, p.1.isPrime.one_notMem⟩
  let iso1 := basicOpenSectionsIso (IsAdicRing.ideal_spec A).2.1 (IsAdicRing.ideal_spec A).1 (1 : A)
  have hsec := globalSectionsIso_inv_comp_basicOpenSectionsIso_hom
    (IsAdicRing.ideal_spec A).2.1 (IsAdicRing.ideal_spec A).1 (1 : A)
  have hres : iso1.inv (algebraMap A (AdicRing.CompletedAway A (1 : A)) a) =
      (Spf A).presheaf.map (homOfLE (le_top : basicOpen (1 : A) ≤ ⊤)).op ((globalIso A).inv a) := by
    have h1 := ConcreteCategory.congr_hom hsec a
    simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply,
      CommRingCat.hom_ofHom] at h1
    rw [← h1]
    exact ConcreteCategory.congr_hom iso1.hom_inv_id _
  have hgerm : (Spf A).presheaf.germ (basicOpen u.elem) p (mem_basicOpen.mpr u.notMem)
      (iso1.inv (algebraMap A (AdicRing.CompletedAway A u.elem) a)) =
      (Spf A).presheaf.germ ⊤ p trivial ((globalIso A).inv a) := by
    change (Spf A).presheaf.germ (basicOpen (1 : A)) p (mem_basicOpen.mpr u.notMem)
      (iso1.inv (algebraMap A (AdicRing.CompletedAway A (1 : A)) a)) = _
    rw [hres]
    exact TopCat.Presheaf.germ_res_apply (Spf A).presheaf (homOfLE (le_top : basicOpen (1 : A) ≤ ⊤))
      p (mem_basicOpen.mpr u.notMem) ((globalIso A).inv a)
  have h0 := stalkResidueFieldEquiv_residue_germ u a
  change stalkResidueFieldEquiv p ((Spf A).residue p
      ((Spf A).presheaf.germ (basicOpen u.elem) p (mem_basicOpen.mpr u.notMem)
        (iso1.inv (algebraMap A (AdicRing.CompletedAway A u.elem) a)))) = _ at h0
  rw [hgerm] at h0
  exact h0

/-- An element `a ∈ A` lies in an open prime `p` of `A` if and only if its global section vanishes
in the residue field of `Spf A` at `p`. -/
theorem mem_asIdeal_iff_Γevaluation_eq_zero (p : carrier A) (a : A) :
    a ∈ (p : PrimeSpectrum A).asIdeal ↔
      (Spf A).Γevaluation p
        ((@globalSectionsIso A _ _ _ _ (IsAdicRing.ideal_spec A).2.2
          (IsAdicRing.ideal_spec A).2.1).inv a) = 0 := by
  have : p.1.asIdeal.IsPrime := p.1.isPrime
  rw [← Ideal.Quotient.eq_zero_iff_mem,
    ← (IsFractionRing.injective (A ⧸ p.1.asIdeal)
      (FractionRing (A ⧸ p.1.asIdeal))).eq_iff, map_zero,
    ← stalkResidueFieldEquiv_Γevaluation p a,
    ← map_zero (stalkResidueFieldEquiv p), (stalkResidueFieldEquiv p).injective.eq_iff]

/-- For any ideal of definition `I` of `A`, an element `a ∈ A` belongs to `I.radical` if and only if
its global section vanishes in the residue field of `Spf A` at every point. -/
theorem mem_radical_iff_forall_Γevaluation_eq_zero {I : Ideal A} (hI : IsAdic I) (a : A) :
    a ∈ I.radical ↔
      ∀ p : carrier A,
        (Spf A).Γevaluation p
          ((@globalSectionsIso A _ _ _ _ (IsAdicRing.ideal_spec A).2.2
            (IsAdicRing.ideal_spec A).2.1).inv a) = 0 := by
  rw [Ideal.radical_eq_sInf, Ideal.mem_sInf]
  constructor
  · intro ha p
    exact (mem_asIdeal_iff_Γevaluation_eq_zero p a).mp
      (ha ⟨(mem_carrier_iff_le hI).mp p.2, p.1.isPrime⟩)
  · rintro ha P ⟨hIP, hP⟩
    let p : carrier A := ⟨⟨P, hP⟩, (mem_carrier_iff_le hI).mpr hIP⟩
    exact (mem_asIdeal_iff_Γevaluation_eq_zero p a).mpr (ha p)

end ResidueEvaluation

section ContinuityAndFullness

/-- On open prime ideals, every morphism `f : Spf B ⟶ Spf A` acts by preimage along
`sectionsHom f`. -/
theorem asIdeal_base_apply (f : Spf B ⟶ Spf A) (q : carrier B) :
    ((f.base q : carrier A).1).asIdeal =
      (q : PrimeSpectrum B).asIdeal.comap (sectionsHom f) := by
  let q' : Spf B := q
  let p : carrier A := f.base q'
  ext a
  rw [Ideal.mem_comap, mem_asIdeal_iff_Γevaluation_eq_zero p a,
    mem_asIdeal_iff_Γevaluation_eq_zero q (sectionsHom f a)]
  have hinj : Function.Injective (LocallyRingedSpace.residueFieldMap f q').hom :=
    (LocallyRingedSpace.residueFieldMap f q').hom.injective
  have hnat := LocallyRingedSpace.Γevaluation_naturality_apply f q' ((globalIso A).inv a)
  have hsec : f.c.app (op ⊤) ((globalIso A).inv a) = (globalIso B).inv (sectionsHom f a) := by
    have h := ConcreteCategory.congr_hom (globalIso_inv_comp_globalApp f) a
    exact h
  rw [← map_eq_zero_iff (LocallyRingedSpace.residueFieldMap f q').hom hinj]
  change (LocallyRingedSpace.residueFieldMap f q')
      ((Spf A).Γevaluation (f.base q') ((globalIso A).inv a)) = 0 ↔ _
  rw [hnat, hsec]
  rfl

/-- **Automatic continuity on affine formal spectra.** Every morphism `f : Spf B ⟶ Spf A` of
locally ringed spaces induces a continuous ring homomorphism `A →+* B` on global sections
(EGA I, Ch. I, 10.2.2). -/
theorem continuous_sectionsHom (f : Spf B ⟶ Spf A) : Continuous (sectionsHom f) := by
  refine IsAdic.continuous_of_map_le_radical (IsAdicRing.ideal_spec A).2.1
    (IsAdicRing.ideal_spec B).2.1 (IsAdicRing.ideal_spec A).1 ?_
  rw [Ideal.map_le_iff_le_comap]
  intro a ha
  rw [Ideal.mem_comap, Ideal.radical_eq_sInf, Ideal.mem_sInf]
  rintro P ⟨hJP, hP⟩
  let q : carrier B := ⟨⟨P, hP⟩, (mem_carrier_iff_le (IsAdicRing.ideal_spec B).2.1).mpr hJP⟩
  let p : carrier A := f.base q
  have hmem : a ∈ p.1.asIdeal :=
    (mem_carrier_iff_le (IsAdicRing.ideal_spec A).2.1).mp p.2 ha
  rw [asIdeal_base_apply f q] at hmem
  exact hmem

/-- The underlying continuous map of `f : Spf B ⟶ Spf A` is `comap (sectionsHom f)`. -/
theorem base_eq_comap_sectionsHom (f : Spf B ⟶ Spf A) :
    f.base = TopCat.ofHom (comap (sectionsHom f) (continuous_sectionsHom f)) := by
  ext q : 2
  refine Subtype.ext (PrimeSpectrum.ext ?_)
  rw [asIdeal_base_apply f q]
  exact (congrArg PrimeSpectrum.asIdeal
    (coe_comap_apply (sectionsHom f) (continuous_sectionsHom f) q)).symm

/-- The preimage of a basic open `D(a)` under `f : Spf B ⟶ Spf A` is `D(sectionsHom f a)`. -/
theorem preimage_basicOpen (f : Spf B ⟶ Spf A) (a : A) :
    (Opens.map f.base).obj (basicOpen a) = basicOpen (sectionsHom f a) := by
  rw [base_eq_comap_sectionsHom f]
  exact comap_basicOpen (sectionsHom f) (continuous_sectionsHom f) a

/-- On global sections, the open immersion `basicOpenι f : Spf A_{f} ⟶ Spf A` induces the
canonical map `A → A_{f}`. -/
@[simp]
theorem sectionsHom_basicOpenι (f : A) :
    sectionsHom (basicOpenι f) = algebraMap A (AdicRing.CompletedAway A f) := by
  have := (IsAdicRing.ideal_spec A).2.2
  have := (IsAdicRing.ideal_spec (AdicRing.CompletedAway A f)).2.2
  have h := basicOpenι_c_app f 1
  let U1 : Opens (Spf A) := basicOpen (1 : A)
  let Uf1 : Opens (Spf A) := basicOpen (f * 1)
  have htop_eq : (⊤ : Opens (Spf A)) = U1 := (basicOpen_one (A := A)).symm
  have hpre := congrArg (fun g ↦ (globalIso A).inv ≫
    (Spf A).presheaf.map (eqToHom (congrArg op htop_eq)) ≫ g) h
  -- Rewrite the LHS using naturality of `(basicOpenι f).c` and `globalIso_inv_comp_globalApp`.
  have hlhs : (globalIso A).inv ≫
      (Spf A).presheaf.map (eqToHom (congrArg op htop_eq)) ≫
      (basicOpenι f).c.app (op U1) ≫
      (Spf (AdicRing.CompletedAway A f)).presheaf.map
        (eqToHom (congrArg op (basicOpenι_preimage_basicOpen f 1))) ≫
      (basicOpenSectionsIso (IsAdicRing.ideal_spec (AdicRing.CompletedAway A f)).2.1
        (IsAdicRing.ideal_spec (AdicRing.CompletedAway A f)).1
        (algebraMap A (AdicRing.CompletedAway A f) 1)).hom =
      CommRingCat.ofHom (sectionsHom (basicOpenι f)) ≫
      CommRingCat.ofHom (algebraMap (AdicRing.CompletedAway A f)
        (AdicRing.CompletedAway (AdicRing.CompletedAway A f)
          (algebraMap A (AdicRing.CompletedAway A f) 1))) := by
    have hnat := (basicOpenι f).c.naturality (eqToHom (congrArg op htop_eq))
    rw [← Category.assoc ((Spf A).presheaf.map _), hnat, Category.assoc]
    change (globalIso A).inv ≫ globalApp (basicOpenι f) ≫ _ = _
    -- `erw` unfolds `Spf` so `Opens (carrier _)` matches `Opens (Spf _).toTopCat`.
    erw [← Category.assoc, globalIso_inv_comp_globalApp, Category.assoc]
    congr 1
    have hmap : ((TopCat.Presheaf.pushforward CommRingCat (basicOpenι f).base).obj
          (Spf (AdicRing.CompletedAway A f)).presheaf).map (eqToHom (congrArg op htop_eq)) ≫
        (Spf (AdicRing.CompletedAway A f)).presheaf.map
          (eqToHom (congrArg op (basicOpenι_preimage_basicOpen f 1))) =
        (Spf (AdicRing.CompletedAway A f)).presheaf.map
          (homOfLE (le_top : basicOpen (algebraMap A (AdicRing.CompletedAway A f) 1) ≤ ⊤)).op := by
      change (Spf (AdicRing.CompletedAway A f)).presheaf.map
          ((Opens.map (basicOpenι f).base).map (eqToHom htop_eq.symm)).op ≫ _ = _
      -- `erw`: `Opens.map` functor object matches at default transparency.
      erw [← Functor.map_comp]
      exact congrArg (Spf (AdicRing.CompletedAway A f)).presheaf.map
        (Quiver.Hom.unop_inj (Subsingleton.elim _ _))
    exact (congrArg ((globalIso (AdicRing.CompletedAway A f)).inv ≫ ·)
      ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ _) hmap))).trans
      (globalSectionsIso_inv_comp_basicOpenSectionsIso_hom
        (IsAdicRing.ideal_spec (AdicRing.CompletedAway A f)).2.1
        (IsAdicRing.ideal_spec (AdicRing.CompletedAway A f)).1 _)
  -- Rewrite the RHS using `globalSectionsIso_inv_comp_basicOpenSectionsIso_hom`.
  have hrhs : (globalIso A).inv ≫
      (Spf A).presheaf.map (eqToHom (congrArg op htop_eq)) ≫
      (Spf A).presheaf.map (homOfLE ((basicOpen_mul f 1).le.trans inf_le_right) :
        Uf1 ⟶ U1).op ≫
      (basicOpenSectionsIso (IsAdicRing.ideal_spec A).2.1 (IsAdicRing.ideal_spec A).1 (f * 1)).hom ≫
      (AdicRing.CompletedAway.iterateEquiv f 1).symm.toCommRingCatIso.hom =
      CommRingCat.ofHom (algebraMap A (AdicRing.CompletedAway A (f * 1))) ≫
      (AdicRing.CompletedAway.iterateEquiv f 1).symm.toCommRingCatIso.hom := by
    rw [← Functor.map_comp_assoc]
    have hle : (eqToHom (congrArg op htop_eq) ≫
        (homOfLE ((basicOpen_mul f 1).le.trans inf_le_right) : Uf1 ⟶ U1).op) =
        (homOfLE (le_top : Uf1 ≤ ⊤)).op :=
      Quiver.Hom.unop_inj (Subsingleton.elim _ _)
    rw [hle]
    exact globalSectionsIso_inv_comp_basicOpenSectionsIso_hom_assoc
      (IsAdicRing.ideal_spec A).2.1 (IsAdicRing.ideal_spec A).1 (f * 1) _
  have hpre' : CommRingCat.ofHom (sectionsHom (basicOpenι f)) ≫
      CommRingCat.ofHom (algebraMap (AdicRing.CompletedAway A f)
        (AdicRing.CompletedAway (AdicRing.CompletedAway A f)
          (algebraMap A (AdicRing.CompletedAway A f) 1))) =
      CommRingCat.ofHom (algebraMap A (AdicRing.CompletedAway A (f * 1))) ≫
      (AdicRing.CompletedAway.iterateEquiv f 1).symm.toCommRingCatIso.hom :=
    hlhs.symm.trans (hpre.trans hrhs)
  ext a
  have ha := ConcreteCategory.congr_hom hpre' a
  simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply,
    CommRingCat.hom_ofHom, RingEquiv.toCommRingCatIso_hom, RingEquiv.coe_toRingHom] at ha
  have ha' := congrArg (AdicRing.CompletedAway.iterateEquiv f 1) ha
  have hmem : f * 1 ∈ (Ideal.span {f} ⊔ IsAdicRing.ideal A).radical :=
    Ideal.le_radical (Ideal.mem_sup_left (Ideal.mem_span_singleton.mpr (dvd_mul_right f 1)))
  rw [AdicRing.CompletedAway.iterateEquiv_algebraMap f 1 hmem, RingEquiv.apply_symm_apply,
    ← (AdicRing.CompletedAway.restrict (A := A) (f := f) (g := f * 1) hmem).commutes a] at ha'
  have h_inj : ∀ (g : A) (_ : g = f)
      (hmem' : g ∈ (Ideal.span {f} ⊔ IsAdicRing.ideal A).radical),
      Function.Injective (AdicRing.CompletedAway.restrict (A := A) (f := f) (g := g) hmem') := by
    rintro _ rfl hmem'
    rw [AdicRing.CompletedAway.restrict_self]
    exact Function.injective_id
  exact h_inj (f * 1) (mul_one f) hmem ha'

/-- On `basicOpen f`, the sheaf component of `basicOpenι f` is an isomorphism. -/
private theorem isIso_basicOpenι_c_app_self (f : A) :
    IsIso ((basicOpenι f).c.app (op (basicOpen f))) := by
  have heq : (isOpenImmersion_basicOpenι f).base_open.functor.obj ⊤ = basicOpen f := by
    ext p
    change p ∈ (basicOpenι f).base '' Set.univ ↔ _
    rw [Set.image_univ, range_basicOpenι]
    rfl
  rw [← heq]
  exact (isOpenImmersion_basicOpenι f).c_iso ⊤

/-- When `(Opens.map j.base).obj U = ⊤`, the component of `k ≫ j` at `U` factors through
`k.c.app (op ⊤)`. -/
private theorem comp_c_app_eq_globalApp {X Y Z : LocallyRingedSpace.{u}} (k : X ⟶ Y) (j : Y ⟶ Z)
    {U : Opens Z} (hU : (Opens.map j.base).obj U = ⊤) :
    (k ≫ j).c.app (op U) =
      j.c.app (op U) ≫ Y.presheaf.map (eqToHom (congrArg op hU)) ≫
        k.c.app (op ⊤) ≫
        X.presheaf.map (eqToHom (congrArg op (by
          change (Opens.map k.base).obj ⊤ = (Opens.map (k ≫ j).base).obj U
          rw [LocallyRingedSpace.comp_base, Opens.map_comp_obj, hU]))) := by
  rw [LocallyRingedSpace.comp_c_app]
  have hnat := k.c.naturality (eqToHom (congrArg op hU))
  have hstep : Y.presheaf.map (eqToHom (congrArg op hU)) ≫ k.c.app (op ⊤) ≫
      X.presheaf.map (eqToHom (congrArg op (by
        change (Opens.map k.base).obj ⊤ = (Opens.map (k ≫ j).base).obj U
        rw [LocallyRingedSpace.comp_base, Opens.map_comp_obj, hU]))) =
      k.c.app (op ((Opens.map j.base).obj U)) := by
    rw [← Category.assoc, hnat, Category.assoc]
    have hmap : ((TopCat.Presheaf.pushforward CommRingCat k.base).obj X.presheaf).map
          (eqToHom (congrArg op hU)) ≫
        X.presheaf.map (eqToHom (congrArg op (by
          change (Opens.map k.base).obj ⊤ = (Opens.map (k ≫ j).base).obj U
          rw [LocallyRingedSpace.comp_base, Opens.map_comp_obj, hU]))) = 𝟙 _ := by
      change X.presheaf.map ((Opens.map k.base).map (eqToHom hU.symm)).op ≫ _ = 𝟙 _
      rw [← Functor.map_comp]
      have hid : ((Opens.map k.base).map (eqToHom hU.symm)).op ≫
          eqToHom (congrArg op (by
            change (Opens.map k.base).obj ⊤ = (Opens.map (k ≫ j).base).obj U
            rw [LocallyRingedSpace.comp_base, Opens.map_comp_obj, hU])) = 𝟙 _ :=
        Quiver.Hom.unop_inj (Subsingleton.elim _ _)
      rw [hid, CategoryTheory.Functor.map_id]
    rw [hmap, Category.comp_id]
  exact congrArg (j.c.app (op U) ≫ ·) hstep.symm

private theorem base_eq_of_sectionsHom_eq {f g : Spf B ⟶ Spf A}
    (h : sectionsHom f = sectionsHom g) : f.base = g.base := by
  ext q : 2
  refine Subtype.ext (PrimeSpectrum.ext ?_)
  rw [asIdeal_base_apply f q, asIdeal_base_apply g q, h]

/-- **Morphisms between formal spectra agree on basic opens as soon as they agree on global
sections.** -/
private theorem c_app_basicOpen_eq_of_sectionsHom_eq {f g : Spf B ⟶ Spf A}
    (h : sectionsHom f = sectionsHom g) (a : A) :
    f.c.app (op (basicOpen a)) ≫
        (Spf B).presheaf.map (eqToHom (congrArg op (by
          rw [preimage_basicOpen f a, preimage_basicOpen g a, h]))) =
      g.c.app (op (basicOpen a)) := by
  have hbase : f.base = g.base := base_eq_of_sectionsHom_eq h
  let φ := sectionsHom f
  let Ua : Opens (Spf A) := basicOpen a
  have hrange_f : Set.range (basicOpenι (φ a) ≫ f).base ⊆ Set.range (basicOpenι a).base := by
    rintro _ ⟨q, rfl⟩
    rw [range_basicOpenι, LocallyRingedSpace.comp_base, TopCat.coe_comp, Function.comp_apply]
    have hq : (basicOpenι (φ a)).base q ∈ basicOpen (φ a) :=
      (range_basicOpenι (φ a)).le (Set.mem_range_self q)
    change (basicOpenι (φ a)).base q ∈ (Opens.map f.base).obj (basicOpen a)
    rwa [preimage_basicOpen f a]
  have hrange_g : Set.range (basicOpenι (φ a) ≫ g).base ⊆ Set.range (basicOpenι a).base := by
    rw [LocallyRingedSpace.comp_base, ← hbase]
    exact hrange_f
  let fa : Spf (AdicRing.CompletedAway B (φ a)) ⟶ Spf (AdicRing.CompletedAway A a) :=
    LocallyRingedSpace.IsOpenImmersion.lift (basicOpenι a) (basicOpenι (φ a) ≫ f) hrange_f
  let ga : Spf (AdicRing.CompletedAway B (φ a)) ⟶ Spf (AdicRing.CompletedAway A a) :=
    LocallyRingedSpace.IsOpenImmersion.lift (basicOpenι a) (basicOpenι (φ a) ≫ g) hrange_g
  have hfa : fa ≫ basicOpenι a = basicOpenι (φ a) ≫ f :=
    LocallyRingedSpace.IsOpenImmersion.lift_fac _ _ hrange_f
  have hga : ga ≫ basicOpenι a = basicOpenι (φ a) ≫ g :=
    LocallyRingedSpace.IsOpenImmersion.lift_fac _ _ hrange_g
  have hsec_eq : sectionsHom fa = sectionsHom ga := by
    refine AdicRing.CompletedAway.ringHom_ext A a (continuous_sectionsHom fa)
      (continuous_sectionsHom ga) ?_
    rw [← sectionsHom_basicOpenι a, ← sectionsHom_comp fa (basicOpenι a),
      ← sectionsHom_comp ga (basicOpenι a), hfa, hga, sectionsHom_comp, sectionsHom_comp, h]
  have hc_top : globalApp fa = globalApp ga := globalApp_eq_of_sectionsHom_eq hsec_eq
  have htop_a : (Opens.map (basicOpenι a).base).obj Ua = ⊤ := by
    ext q
    change (basicOpenι a).base q ∈ basicOpen a ↔ True
    exact iff_true_intro ((range_basicOpenι a).le (Set.mem_range_self q))
  have hbase_comp : (basicOpenι (φ a) ≫ f).base = (basicOpenι (φ a) ≫ g).base := by
    rw [LocallyRingedSpace.comp_base, LocallyRingedSpace.comp_base, hbase]
  have hcomp_eq : (basicOpenι (φ a) ≫ f).c.app (op Ua) ≫
      (Spf (AdicRing.CompletedAway B (φ a))).presheaf.map
        (eqToHom (congrArg op (congrArg (fun k ↦ (Opens.map k).obj Ua) hbase_comp))) =
      (basicOpenι (φ a) ≫ g).c.app (op Ua) := by
    have hf_app := PresheafedSpace.congr_app (congrArg LocallyRingedSpace.Hom.toHom hfa.symm)
      (op Ua)
    have hg_app := PresheafedSpace.congr_app (congrArg LocallyRingedSpace.Hom.toHom hga.symm)
      (op Ua)
    have hfa_top := comp_c_app_eq_globalApp fa (basicOpenι a) htop_a
    have hga_top := comp_c_app_eq_globalApp ga (basicOpenι a) htop_a
    rw [hf_app, hg_app, hfa_top, hga_top]
    simp only [Category.assoc]
    change _ ≫ _ ≫ globalApp fa ≫ _ = _ ≫ _ ≫ globalApp ga ≫ _
    rw [hc_top]
    congr 3
    rw [← Functor.map_comp, ← Functor.map_comp, ← Functor.map_comp]
    exact congrArg (Spf (AdicRing.CompletedAway B (φ a))).presheaf.map
      (Quiver.Hom.unop_inj (Subsingleton.elim _ _))
  have hpre_fg : (Opens.map f.base).obj Ua = (Opens.map g.base).obj Ua :=
    congrArg (fun k ↦ (Opens.map k).obj Ua) hbase
  have hpre_g : (Opens.map g.base).obj Ua = basicOpen (φ a) := by
    change (Opens.map g.base).obj (basicOpen a) = basicOpen (sectionsHom f a)
    rw [preimage_basicOpen g a, h]
  have hiso : IsIso ((basicOpenι (φ a)).c.app (op ((Opens.map g.base).obj Ua))) := by
    rw [hpre_g]
    exact isIso_basicOpenι_c_app_self (φ a)
  change f.c.app (op Ua) ≫ (Spf B).presheaf.map (eqToHom (congrArg op hpre_fg)) = g.c.app (op Ua)
  rw [← cancel_mono ((basicOpenι (φ a)).c.app (op ((Opens.map g.base).obj Ua)))]
  rw [Category.assoc]
  have hnat := (basicOpenι (φ a)).c.naturality (eqToHom (congrArg op hpre_fg))
  rw [hnat]
  have h1 : f.c.app (op Ua) ≫
      (basicOpenι (φ a)).c.app (op ((Opens.map f.base).obj Ua)) =
      (basicOpenι (φ a) ≫ f).c.app (op Ua) :=
    (LocallyRingedSpace.comp_c_app (basicOpenι (φ a)) f (op Ua)).symm
  have h2 : g.c.app (op Ua) ≫
      (basicOpenι (φ a)).c.app (op ((Opens.map g.base).obj Ua)) =
      (basicOpenι (φ a) ≫ g).c.app (op Ua) :=
    (LocallyRingedSpace.comp_c_app (basicOpenι (φ a)) g (op Ua)).symm
  rw [← Category.assoc, h1, h2]
  exact (congrArg ((basicOpenι (φ a) ≫ f).c.app (op Ua) ≫ ·)
    (congrArg (Spf (AdicRing.CompletedAway B (φ a))).presheaf.map
      (Quiver.Hom.unop_inj (Subsingleton.elim _ _)))).trans hcomp_eq

/-- **Morphisms between formal spectra are determined by their action on global sections.** -/
theorem hom_ext_of_sectionsHom_eq {f g : Spf B ⟶ Spf A} (h : sectionsHom f = sectionsHom g) :
    f = g := by
  have hbase : f.base = g.base := base_eq_of_sectionsHom_eq h
  apply LocallyRingedSpace.Hom.ext'
  refine PresheafedSpace.Hom.ext _ _ hbase ?_
  ext U : 1
  refine CommRingCat.hom_ext (RingHom.ext fun s ↦ ?_)
  let U' : Opens (carrier A) := U
  let Vp (p : { a : A // basicOpen a ≤ U' }) : Opens (Spf A) := basicOpen p.1
  have hle (p : { a : A // basicOpen a ≤ U' }) : Vp p ≤ U := p.2
  have hcov : (Opens.map g.base).obj U ≤
      ⨆ p : { a : A // basicOpen a ≤ U' }, (Opens.map g.base).obj (Vp p) := by
    intro q hq
    obtain ⟨a, ha, haU⟩ := exists_basicOpen_le (U := U') hq
    exact Opens.mem_iSup.mpr ⟨⟨a, haU⟩, ha⟩
  refine TopCat.Sheaf.eq_of_locally_eq' (Spf B).sheaf
    (fun p : { a : A // basicOpen a ≤ U' } ↦ (Opens.map g.base).obj (Vp p))
    ((Opens.map g.base).obj U)
    (fun p ↦ (Opens.map g.base).map (homOfLE (hle p))) hcov _ _ fun p ↦ ?_
  have hnat_g := ConcreteCategory.congr_hom (g.c.naturality (homOfLE (hle p)).op) s
  have hnat_f := ConcreteCategory.congr_hom (f.c.naturality (homOfLE (hle p)).op) s
  have hbas := ConcreteCategory.congr_hom (c_app_basicOpen_eq_of_sectionsHom_eq h p.1)
    ((Spf A).presheaf.map (homOfLE (hle p)).op s)
  let hwh_mor : op ((Opens.map f.base).obj U) ⟶ op ((Opens.map g.base).obj U) :=
    (eqToHom (congrArg (fun k ↦ (Opens.map k).op) hbase)).app (op U)
  have hpre_p : (Opens.map f.base).obj (Vp p) = (Opens.map g.base).obj (Vp p) :=
    congrArg (fun k ↦ (Opens.map k).obj (Vp p)) hbase
  have hcomm :
      (Spf B).presheaf.map hwh_mor ≫
        (Spf B).presheaf.map ((Opens.map g.base).map (homOfLE (hle p))).op =
      (Spf B).presheaf.map ((Opens.map f.base).map (homOfLE (hle p))).op ≫
        (Spf B).presheaf.map (eqToHom (congrArg op hpre_p)) := by
    rw [← Functor.map_comp, ← Functor.map_comp]
    exact congrArg (Spf B).presheaf.map (Quiver.Hom.unop_inj (Subsingleton.elim _ _))
  have hcomm_s := ConcreteCategory.congr_hom hcomm (f.c.app (op U) s)
  simp only [CommRingCat.hom_comp, RingHom.coe_comp] at hnat_g hnat_f hbas hcomm_s
  have hgoal : (Spf B).presheaf.map ((Opens.map g.base).map (homOfLE (hle p))).op
      ((Spf B).presheaf.map hwh_mor (f.c.app (op U) s)) =
    (Spf B).presheaf.map ((Opens.map g.base).map (homOfLE (hle p))).op (g.c.app (op U) s) := by
    calc (Spf B).presheaf.map ((Opens.map g.base).map (homOfLE (hle p))).op
          ((Spf B).presheaf.map hwh_mor (f.c.app (op U) s))
        = (Spf B).presheaf.map (eqToHom (congrArg op hpre_p))
          ((Spf B).presheaf.map ((Opens.map f.base).map (homOfLE (hle p))).op
            (f.c.app (op U) s)) := hcomm_s
      _ = (Spf B).presheaf.map (eqToHom (congrArg op hpre_p))
          (f.c.app (op (Vp p)) ((Spf A).presheaf.map (homOfLE (hle p)).op s)) :=
            congrArg ((Spf B).presheaf.map (eqToHom (congrArg op hpre_p))) hnat_f.symm
      _ = g.c.app (op (Vp p)) ((Spf A).presheaf.map (homOfLE (hle p)).op s) := hbas
      _ = (Spf B).presheaf.map ((Opens.map g.base).map (homOfLE (hle p))).op
            (g.c.app (op U) s) := hnat_g
  exact hgoal

/-- **Fullness of `Spf`.** Every morphism `f : Spf B ⟶ Spf A` of locally ringed spaces is induced
by its continuous global-section homomorphism `sectionsHom f` (EGA I, Ch. I, 10.2.2). -/
theorem eq_map_sectionsHom (f : Spf B ⟶ Spf A) :
    f = map (sectionsHom f) (continuous_sectionsHom f) :=
  hom_ext_of_sectionsHom_eq (by simp)

/-- The open immersion `basicOpenι f : Spf A_{f} ⟶ Spf A` is `Spf.map` of `A → A_{f}`. -/
theorem basicOpenι_eq_map (f : A) :
    basicOpenι f =
      map (algebraMap A (AdicRing.CompletedAway A f))
        (AdicRing.CompletedAway.continuous_algebraMap A f) := by
  rw [eq_map_sectionsHom (basicOpenι f)]
  congr 1
  exact sectionsHom_basicOpenι f

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
theorem homEquiv_apply_val (f : Spf B ⟶ Spf A) : (homEquiv f).1 = sectionsHom f :=
  (rfl)

/-- The inverse of `homEquiv` sends a continuous ring homomorphism to `Spf.map`. -/
@[simp]
theorem homEquiv_symm_apply (φ : { φ : A →+* B // Continuous φ }) :
    homEquiv.symm φ = map φ.1 φ.2 :=
  (rfl)

/-- An isomorphism `Spf B ≅ Spf A` induces a continuous ring equivalence `A ≃+* B` whose inverse is
also continuous. -/
theorem isHomeomorph_sectionsHom_of_iso (e : Spf B ≅ Spf A) :
    IsHomeomorph (sectionsHom e.hom) := by
  let eqv : A ≃+* B :=
    RingEquiv.ofRingHom (sectionsHom e.hom) (sectionsHom e.inv)
      (by rw [← sectionsHom_comp, Iso.hom_inv_id, sectionsHom_id])
      (by rw [← sectionsHom_comp, Iso.inv_hom_id, sectionsHom_id])
  exact (Homeomorph.mk eqv.toEquiv (continuous_sectionsHom e.hom)
    (continuous_sectionsHom e.inv)).isHomeomorph

end ContinuityAndFullness

section AutomaticContinuityOnSections

/-- Every continuous ring homomorphism `φ : A →+* B` induces a continuous map on sections over
every open `U` equipped with `sectionsTopology`. -/
private theorem continuous_structureSheafMap_sectionsTopology (φ : A →+* B) (hφ : Continuous φ)
    (U : Opens (carrier A)) :
    @Continuous _ _
      (sectionsTopology (IsAdicRing.ideal_spec A).2.1 U)
      (sectionsTopology (IsAdicRing.ideal_spec B).2.1
        ((Opens.map (TopCat.ofHom (comap φ hφ))).obj U))
      ((structureSheafMap φ hφ (IsAdicRing.ideal_spec A).2.1
        (IsAdicRing.ideal_spec B).2.1).hom.app (op U)) := by
  let _ : TopologicalSpace ((structureSheaf (IsAdicRing.ideal_spec A).2.1).obj.obj (op U)) :=
    sectionsTopology (IsAdicRing.ideal_spec A).2.1 U
  refine (continuous_iff_sectionsTopology (IsAdicRing.ideal_spec B).2.1
    ((Opens.map (TopCat.ofHom (comap φ hφ))).obj U)).mpr fun n ↦ ?_
  obtain ⟨m, hm⟩ := (IsAdicRing.ideal_spec A).2.1.exists_pow_succ_le_comap
    ((IsAdicRing.ideal_spec B).2.1.isOpen_pow (n + 1)) hφ
  have hsheaf := structureSheafMap_comp_quotientProjection φ hφ
    (IsAdicRing.ideal_spec A).2.1 (IsAdicRing.ideal_spec B).2.1
    (is_ideal_adic_pow (IsAdicRing.ideal_spec A).2.1 m.succ_pos) n hm
  rw [toQuotientSheaf_pow_succ] at hsheaf
  have hfun :
      (((quotientProjection (IsAdicRing.ideal_spec B).2.1 n).hom.app
          (op ((Opens.map (TopCat.ofHom (comap φ hφ))).obj U))) : _ → _) ∘
        ((structureSheafMap φ hφ (IsAdicRing.ideal_spec A).2.1
          (IsAdicRing.ideal_spec B).2.1).hom.app (op U)) =
      ((quotientMap φ hφ
        (is_ideal_adic_pow (IsAdicRing.ideal_spec A).2.1 m.succ_pos)
        (is_ideal_adic_pow (IsAdicRing.ideal_spec B).2.1 n.succ_pos) hm).hom.app (op U)) ∘
        ((quotientProjection (IsAdicRing.ideal_spec A).2.1 m).hom.app (op U)) := by
    ext s
    exact ConcreteCategory.congr_hom (congrArg (fun η ↦ η.hom.app (op U)) hsheaf) s
  rw [hfun]
  exact @Continuous.comp _ _ _ (sectionsTopology (IsAdicRing.ideal_spec A).2.1 U) ⊥ ⊥ _ _
    continuous_bot (continuous_quotientProjection_app (IsAdicRing.ideal_spec A).2.1 U m)

omit [IsTopologicalRing A] [IsAdicRing A] [IsTopologicalRing B] [IsAdicRing B] in
private theorem comap_basicOpen_obj (φ : A →+* B) (hφ : Continuous φ) (a : A) :
    (Opens.map (TopCat.ofHom (comap φ hφ))).obj (basicOpen a) = basicOpen (φ a) :=
  comap_basicOpen φ hφ a

/-- Every continuous ring homomorphism `φ : A →+* B` induces a continuous map on sections over
every open `U` equipped with `quotientSectionsTopology`. -/
private theorem continuous_structureSheafMap_quotientSectionsTopology (φ : A →+* B)
    (hφ : Continuous φ) (U : Opens (carrier A)) :
    @Continuous _ _
      (quotientSectionsTopology (IsAdicRing.ideal_spec A).2.1 U)
      (quotientSectionsTopology (IsAdicRing.ideal_spec B).2.1
        ((Opens.map (TopCat.ofHom (comap φ hφ))).obj U))
      ((structureSheafMap φ hφ (IsAdicRing.ideal_spec A).2.1
        (IsAdicRing.ideal_spec B).2.1).hom.app (op U)) := by
  let σ := structureSheafMap φ hφ (IsAdicRing.ideal_spec A).2.1 (IsAdicRing.ideal_spec B).2.1
  let _ : TopologicalSpace ((structureSheaf (IsAdicRing.ideal_spec A).2.1).obj.obj (op U)) :=
    quotientSectionsTopology (IsAdicRing.ideal_spec A).2.1 U
  refine (continuous_iff_quotientSectionsTopology (IsAdicRing.ideal_spec B).2.1
    ((Opens.map (TopCat.ofHom (comap φ hφ))).obj U)).mpr fun b hb ↦ ?_
  rw [← quotientSectionsTopology_basicOpen (IsAdicRing.ideal_spec B).2.1 b]
  let P := { a : A // basicOpen a ≤ U }
  have hWle (p : P) : basicOpen (b * φ p.1) ≤ basicOpen b := by
    rw [basicOpen_mul]
    exact inf_le_left
  have hWpre (p : P) :
      basicOpen (b * φ p.1) ≤ (Opens.map (TopCat.ofHom (comap φ hφ))).obj (basicOpen p.1) := by
    rw [basicOpen_mul, comap_basicOpen_obj]
    exact inf_le_right
  have hcov : basicOpen b ≤ ⨆ p : P, basicOpen (b * φ p.1) := by
    intro q hqb
    obtain ⟨a, ha, haU⟩ := exists_basicOpen_le (U := U) (hb hqb)
    refine Opens.mem_iSup.mpr ⟨⟨a, haU⟩, ?_⟩
    rw [basicOpen_mul]
    refine ⟨hqb, ?_⟩
    change q ∈ (Opens.map (TopCat.ofHom (comap φ hφ))).obj (basicOpen a) at ha
    rwa [comap_basicOpen_obj] at ha
  let _ : TopologicalSpace
      ((structureSheaf (IsAdicRing.ideal_spec B).2.1).obj.obj (op (basicOpen b))) :=
    quotientSectionsTopology (IsAdicRing.ideal_spec B).2.1 (basicOpen b)
  let _ (p : P) : TopologicalSpace
      ((structureSheaf (IsAdicRing.ideal_spec B).2.1).obj.obj (op (basicOpen (b * φ p.1)))) :=
    quotientSectionsTopology (IsAdicRing.ideal_spec B).2.1 (basicOpen (b * φ p.1))
  have hind := (quotientSectionsTopology_glue (IsAdicRing.ideal_spec B).2.1
    (V := fun p : P ↦ basicOpen (b * φ p.1)) hWle hcov).isInducing
  rw [hind.continuous_iff]
  refine continuous_pi fun p ↦ ?_
  have hfact :
      (fun a : (structureSheaf (IsAdicRing.ideal_spec A).2.1).obj.obj (op U) ↦
        (structureSheaf (IsAdicRing.ideal_spec B).2.1).obj.map (homOfLE (hWle p)).op
          ((structureSheaf (IsAdicRing.ideal_spec B).2.1).obj.map (homOfLE hb).op
            (σ.hom.app (op U) a))) =
      ((structureSheaf (IsAdicRing.ideal_spec B).2.1).obj.map (homOfLE (hWpre p)).op) ∘
        (σ.hom.app (op (basicOpen p.1))) ∘
        ((structureSheaf (IsAdicRing.ideal_spec A).2.1).obj.map (homOfLE p.2).op) := by
    ext s
    have hnat := ConcreteCategory.congr_hom (σ.hom.naturality (homOfLE p.2).op) s
    simp only [Function.comp_apply, CommRingCat.hom_comp, RingHom.coe_comp] at hnat ⊢
    change ((structureSheaf (IsAdicRing.ideal_spec B).2.1).obj.map (homOfLE hb).op ≫
        (structureSheaf (IsAdicRing.ideal_spec B).2.1).obj.map (homOfLE (hWle p)).op)
        (σ.hom.app (op U) s) =
      (structureSheaf (IsAdicRing.ideal_spec B).2.1).obj.map (homOfLE (hWpre p)).op
        (σ.hom.app (op (basicOpen p.1))
          ((structureSheaf (IsAdicRing.ideal_spec A).2.1).obj.map (homOfLE p.2).op s))
    have hnat' : σ.hom.app (op (basicOpen p.1))
        ((structureSheaf (IsAdicRing.ideal_spec A).2.1).obj.map (homOfLE p.2).op s) =
      (structureSheaf (IsAdicRing.ideal_spec B).2.1).obj.map
        ((Opens.map (TopCat.ofHom (comap φ hφ))).map (homOfLE p.2)).op
        (σ.hom.app (op U) s) := hnat
    rw [hnat']
    change ((structureSheaf (IsAdicRing.ideal_spec B).2.1).obj.map (homOfLE hb).op ≫
        (structureSheaf (IsAdicRing.ideal_spec B).2.1).obj.map (homOfLE (hWle p)).op)
        (σ.hom.app (op U) s) =
      ((structureSheaf (IsAdicRing.ideal_spec B).2.1).obj.map
          ((Opens.map (TopCat.ofHom (comap φ hφ))).map (homOfLE p.2)).op ≫
        (structureSheaf (IsAdicRing.ideal_spec B).2.1).obj.map (homOfLE (hWpre p)).op)
        (σ.hom.app (op U) s)
    rw [← Functor.map_comp, ← Functor.map_comp]
    congr 2
  change Continuous (fun a ↦
    (structureSheaf (IsAdicRing.ideal_spec B).2.1).obj.map (homOfLE (hWle p)).op
      ((structureSheaf (IsAdicRing.ideal_spec B).2.1).obj.map (homOfLE hb).op
        (σ.hom.app (op U) a)))
  rw [hfact]
  have h1 : @Continuous _ _
      (quotientSectionsTopology (IsAdicRing.ideal_spec A).2.1 U)
      (sectionsTopology (IsAdicRing.ideal_spec A).2.1 (basicOpen p.1))
      ((structureSheaf (IsAdicRing.ideal_spec A).2.1).obj.map (homOfLE p.2).op) :=
    continuous_restrict_basicOpen_sectionsTopology (IsAdicRing.ideal_spec A).2.1 p.2
  have h2 : @Continuous _ _
      (sectionsTopology (IsAdicRing.ideal_spec A).2.1 (basicOpen p.1))
      (quotientSectionsTopology (IsAdicRing.ideal_spec B).2.1
        ((Opens.map (TopCat.ofHom (comap φ hφ))).obj (basicOpen p.1)))
      (σ.hom.app (op (basicOpen p.1))) := by
    have hq_eq : quotientSectionsTopology (IsAdicRing.ideal_spec B).2.1
        ((Opens.map (TopCat.ofHom (comap φ hφ))).obj (basicOpen p.1)) =
        sectionsTopology (IsAdicRing.ideal_spec B).2.1
          ((Opens.map (TopCat.ofHom (comap φ hφ))).obj (basicOpen p.1)) := by
      rw [comap_basicOpen_obj, quotientSectionsTopology_basicOpen]
    exact hq_eq.symm ▸ continuous_structureSheafMap_sectionsTopology φ hφ (basicOpen p.1)
  have h3 : @Continuous _ _
      (quotientSectionsTopology (IsAdicRing.ideal_spec B).2.1
        ((Opens.map (TopCat.ofHom (comap φ hφ))).obj (basicOpen p.1)))
      (quotientSectionsTopology (IsAdicRing.ideal_spec B).2.1 (basicOpen (b * φ p.1)))
      ((structureSheaf (IsAdicRing.ideal_spec B).2.1).obj.map (homOfLE (hWpre p)).op) :=
    quotientSectionsTopology_restrict (IsAdicRing.ideal_spec B).2.1 (hWpre p)
  exact @Continuous.comp _ _ _
    (quotientSectionsTopology (IsAdicRing.ideal_spec A).2.1 U)
    (quotientSectionsTopology (IsAdicRing.ideal_spec B).2.1
      ((Opens.map (TopCat.ofHom (comap φ hφ))).obj (basicOpen p.1)))
    (quotientSectionsTopology (IsAdicRing.ideal_spec B).2.1 (basicOpen (b * φ p.1))) _ _ h3
    (@Continuous.comp _ _ _
      (quotientSectionsTopology (IsAdicRing.ideal_spec A).2.1 U)
      (sectionsTopology (IsAdicRing.ideal_spec A).2.1 (basicOpen p.1))
      (quotientSectionsTopology (IsAdicRing.ideal_spec B).2.1
        ((Opens.map (TopCat.ofHom (comap φ hφ))).obj (basicOpen p.1))) _ _ h2 h1)

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
  have h : ∀ (g : (Spf B).toPresheafedSpace ⟶ (Spf A).toPresheafedSpace),
      g = { base := TopCat.ofHom (comap φ hφ)
            c := (structureSheafMap φ hφ (IsAdicRing.ideal_spec A).2.1
              (IsAdicRing.ideal_spec B).2.1).hom } →
      @Continuous _ _
        (quotientSectionsTopology (IsAdicRing.ideal_spec A).2.1 U)
        (quotientSectionsTopology (IsAdicRing.ideal_spec B).2.1 ((Opens.map g.base).obj U))
        (g.c.app (op U)) := by
    rintro _ rfl
    exact continuous_structureSheafMap_quotientSectionsTopology φ hφ U
  exact h (map φ hφ).toHom (map_toHom φ hφ)

end AutomaticContinuityOnSections

end TauCeti.FormalScheme.Spf
