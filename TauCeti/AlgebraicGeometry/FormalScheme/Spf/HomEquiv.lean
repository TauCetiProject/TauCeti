/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Category.TopCommRingCat
public import TauCeti.AlgebraicGeometry.FormalScheme.Spf.Morphism
public import TauCeti.AlgebraicGeometry.FormalScheme.Spf.SectionsTopology

import TauCeti.Geometry.RingedSpace.PresheafedSpace.Basic

/-!
# Full faithfulness of `Spf` and automatic continuity

For complete separated adic rings `A`, `B` of finite ideal type, every `g : Spf B ⟶ Spf A` of
locally ringed spaces induces `sectionsHom g : A →+* B` via `topSectionsIso`. Naturality of residue
evaluation shows `g.base` pulls open primes back along `sectionsHom g`, giving automatic continuity
(`continuous_sectionsHom`), full faithfulness `homEquiv : (Spf B ⟶ Spf A) ≃ {φ // Continuous φ}`
(`map_sectionsHom`, bundled as `functor : (isAdicRing.FullSubcategory)ᵒᵖ ⥤ LocallyRingedSpace` with
`fullyFaithfulFunctor`; EGA I, Ch. I, 10.2.2; Stacks Tag 0AHY), the induced homeomorphism
`isHomeomorph_isoToRingEquiv` for `Spf B ≅ Spf A` with round-trip laws (`isoToRingEquiv_mapIso`,
`mapIso_isoToRingEquiv`), and continuity on all open section rings for `quotientSectionsTopology`
(`continuous_c_app`).
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
      ‹TopologicalSpace A› (topSectionsIso A).hom := by
  obtain ⟨-, h, _⟩ := IsAdicRing.ideal_spec A; exact isHomeomorph_globalSectionsIso h

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
  rw [← stalkResidueFieldEquiv_residue_germ u a]
  erw [ConcreteCategory.congr_hom (algebraMap_comp_basicOpenSectionsIso_inv u.elem) a,
    TopCat.Presheaf.germ_res_apply (Spf A).presheaf
    (homOfLE (le_top : basicOpen u.elem ≤ ⊤)) p (mem_basicOpen.mpr u.notMem)]; rfl

/-- The global section attached to `a ∈ A` vanishes in the residue field of `Spf A` at `p` if and
only if `a ∈ p`. -/
@[simp] theorem Γevaluation_topSectionsIso_inv_eq_zero_iff (p : carrier A) (a : A) :
    (Spf A).Γevaluation p ((topSectionsIso A).inv a) = 0 ↔ a ∈ (p : PrimeSpectrum A).asIdeal := by
  have : IsDomain (A ⧸ (p : PrimeSpectrum A).asIdeal) := Ideal.Quotient.isDomain _
  rw [← (stalkResidueFieldEquiv p).map_eq_zero_iff,
    stalkResidueFieldEquiv_Γevaluation_topSectionsIso_inv, IsFractionRing.to_map_eq_zero_iff,
    Ideal.Quotient.eq_zero_iff_mem]

end ResidueEvaluation

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
  exact congrArg CommRingCat.Hom.hom <|
    (cancel_epi (globalSectionsIso (IsAdicRing.ideal_spec A).2.1).hom).mp
      ((c_app_top_comp_topSectionsIso_hom (map φ hφ)).symm.trans (map_globalSections φ hφ))

/-- On points, `g : Spf B ⟶ Spf A` pulls every open prime ideal of `B` back along
`sectionsHom g`. -/
@[simp] theorem mem_base_asIdeal_iff (g : Spf B ⟶ Spf A) (q : carrier B) (a : A) :
    a ∈ (g.base q).1.asIdeal ↔ sectionsHom g a ∈ q.1.asIdeal := by
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
    (((mem_carrier_iff_le hIA).mp (g.base ⟨⟨p, hp⟩, (mem_carrier_iff_le hIB).mpr hBp⟩).2) ha)

/-- The underlying continuous map of `g : Spf B ⟶ Spf A` is `comap (sectionsHom g) _`. -/
theorem base_eq_comap_sectionsHom (g : Spf B ⟶ Spf A) :
    g.base = TopCat.ofHom (comap (sectionsHom g) (continuous_sectionsHom g)) :=
  ConcreteCategory.hom_ext _ _ fun q ↦ Subtype.ext <| PrimeSpectrum.ext <| SetLike.ext fun a ↦
    (mem_base_asIdeal_iff g q a).trans <| by
      rw [← Ideal.mem_comap (f := sectionsHom g), ← PrimeSpectrum.comap_asIdeal,
        ← coe_comap_apply (sectionsHom g) (continuous_sectionsHom g) q]; rfl

private theorem base_eq_map_sectionsHom (g : Spf B ⟶ Spf A) :
    g.base = (map (sectionsHom g) (continuous_sectionsHom g)).base :=
  (base_eq_comap_sectionsHom g).trans (map_base _ _).symm

private theorem res_c_app_basicOpen_eq_map_sectionsHom (g : Spf B ⟶ Spf A) (a : A) :
    (Spf A).presheaf.map (homOfLE (le_top : basicOpen a ≤ ⊤)).op ≫ (g.c.app (op (basicOpen a)) ≫
      (Spf B).presheaf.map (eqToHom (congrArg (fun f ↦ (Opens.map f).obj (basicOpen a))
        (base_eq_map_sectionsHom g).symm)).op) = (Spf A).presheaf.map (homOfLE (le_top :
      basicOpen a ≤ ⊤)).op ≫ (map (sectionsHom g) (continuous_sectionsHom g)).c.app
      (op (basicOpen a)) := by
  obtain ⟨-, hIB, _⟩ := IsAdicRing.ideal_spec B
  let m := map (sectionsHom g) (continuous_sectionsHom g)
  -- Rewrite via naturality, `Presheaf.map_comp`, and `map_globalSections`.
  erw [← Category.assoc, g.c.naturality (homOfLE (le_top : basicOpen a ≤ ⊤)).op, Category.assoc,
    ← (Spf B).presheaf.map_comp, show ((Opens.map g.base).map (homOfLE (le_top :
      basicOpen a ≤ ⊤))).op ≫ (eqToHom _).op = ((Opens.map m.base).map (homOfLE le_top)).op from
      Quiver.Hom.unop_inj (Subsingleton.elim _ _), (cancel_mono (globalSectionsIso hIB).hom).mp <|
      (c_app_top_comp_topSectionsIso_hom g).trans (map_globalSections _ _).symm]
  exact (m.c.naturality (homOfLE le_top).op).symm

private theorem exists_pow_map_quotient_eq_bot_of_map (φ : A →+* B) (hφ : Continuous φ)
    (W : Opens (carrier B)) (n : ℕ) :
    ∃ k : ℕ, (IsAdicRing.ideal A ^ (k + 1)).map (((topSectionsIso A).inv ≫
      (map φ hφ).c.app (op ⊤) ≫ (Spf B).presheaf.map (homOfLE (le_top : W ≤ ⊤)).op ≫
      (quotientProjection (IsAdicRing.ideal_spec B).2.1 n).hom.app (op W)).hom) = ⊥ := by
  let hIA := (IsAdicRing.ideal_spec A).2.1; let hIB := (IsAdicRing.ideal_spec B).2.1
  have := (IsAdicRing.ideal_spec A).2.2; have := (IsAdicRing.ideal_spec B).2.2
  obtain ⟨k, hk⟩ := hIA.exists_pow_succ_le_comap (hIB.isOpen_pow (n + 1)) hφ
  refine ⟨k, (Ideal.map_eq_bot_iff_le_ker _).mpr fun r hr ↦ RingHom.mem_ker.mpr ?_⟩
  have hcomp : (topSectionsIso A).inv ≫ (map φ hφ).c.app (op ⊤) ≫ (Spf B).presheaf.map
        (homOfLE (le_top : W ≤ ⊤)).op ≫ (quotientProjection hIB n).hom.app (op W) =
      CommRingCat.ofHom ((Ideal.Quotient.mk (IsAdicRing.ideal B ^ (n + 1))).comp φ) ≫
        (quotientSheafGlobalSectionsIso (is_ideal_adic_pow hIB n.succ_pos)).inv ≫
        (quotientSheaf (is_ideal_adic_pow hIB n.succ_pos)).obj.map (homOfLE le_top).op := by
    -- Unfold `topSectionsIso`/`(Spf B).presheaf` to `globalSectionsIso`/`structureSheaf`.
    erw [← Category.assoc, show (topSectionsIso A).inv ≫ ((map φ hφ).c.app (op ⊤) :
        _ ⟶ (Spf B).presheaf.obj (op ⊤)) = CommRingCat.ofHom φ ≫ (topSectionsIso B).inv from by
        simpa using topSectionsIso_inv_comp_c_app_top (map φ hφ), Category.assoc,
      (quotientProjection hIB n).hom.naturality (homOfLE (le_top : W ≤ ⊤)).op,
      globalSectionsIso_inv_comp_quotientProjection_assoc, ← Category.assoc,
      ← CommRingCat.ofHom_comp]
  rw [ConcreteCategory.congr_hom hcomp r, ConcreteCategory.comp_apply]
  -- Unfold `CommRingCat.ofHom` application to match `Ideal.Quotient.eq_zero_iff_mem`.
  erw [(Ideal.Quotient.eq_zero_iff_mem (I := IsAdicRing.ideal B ^ (n + 1))).mpr (hk hr), map_zero]

private theorem c_app_basicOpen_eq_map_sectionsHom (g : Spf B ⟶ Spf A) (a : A) :
    g.c.app (op (basicOpen a)) ≫ (Spf B).presheaf.map (eqToHom
        (congrArg (fun f ↦ (Opens.map f).obj (basicOpen a)) (base_eq_map_sectionsHom g).symm)).op =
      (map (sectionsHom g) (continuous_sectionsHom g)).c.app (op (basicOpen a)) := by
  obtain ⟨hIAfg, hIA, -⟩ := IsAdicRing.ideal_spec A; obtain ⟨-, hIB, -⟩ := IsAdicRing.ideal_spec B
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
      γ₂.comp (algebraMap A (AdicRing.CompletedAway A a)) := congrArg CommRingCat.Hom.hom <|
    show CommRingCat.ofHom (algebraMap A _) ≫ (basicOpenSectionsIso hIA hIAfg a).inv ≫ α ≫ πn =
      CommRingCat.ofHom (algebraMap A _) ≫ (basicOpenSectionsIso hIA hIAfg a).inv ≫
        m.c.app (op (basicOpen a)) ≫ πn from by
      -- Unfold `(Spf A).presheaf` to `structureSheaf` for the next rewrite.
      erw [algebraMap_comp_basicOpenSectionsIso_inv_assoc a,
        algebraMap_comp_basicOpenSectionsIso_inv_assoc a, Category.assoc, Category.assoc,
        reassoc_of% (res_c_app_basicOpen_eq_map_sectionsHom g a), Category.assoc]; rfl
  let _ : Algebra A Rn := (γ₂.comp (algebraMap A (AdicRing.CompletedAway A a))).toAlgebra
  obtain ⟨k, hk⟩ := exists_pow_map_quotient_eq_bot_of_map φ hφ W n
  have halg : algebraMap A Rn = (((topSectionsIso A).inv ≫ m.c.app (op ⊤) ≫
      (Spf B).presheaf.map (homOfLE (le_top : W ≤ ⊤)).op ≫ πn).hom) :=
    congrArg CommRingCat.Hom.hom <| show CommRingCat.ofHom (algebraMap A _) ≫
        (basicOpenSectionsIso hIA hIAfg a).inv ≫ m.c.app (op (basicOpen a)) ≫ πn =
      (topSectionsIso A).inv ≫ m.c.app (op ⊤) ≫
        (Spf B).presheaf.map (homOfLE (le_top : W ≤ ⊤)).op ≫ πn from by
      -- Unfold `(Spf A).presheaf` and `pushforward` for the next rewrite.
      erw [algebraMap_comp_basicOpenSectionsIso_inv_assoc a, Category.assoc,
        reassoc_of% (m.c.naturality (homOfLE (le_top : basicOpen a ≤ ⊤)).op)]; rfl
  exact congr($(AdicRing.CompletedAway.algHom_ext_of_map_pow_eq_bot (halg.symm ▸ hk)
    (⟨γ₁, fun r ↦ congr($hA r)⟩ : _ →ₐ[A] Rn) ⟨γ₂, fun _ ↦ rfl⟩) x)

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
theorem sectionsHom_injective : Function.Injective (sectionsHom (A := A) (B := B)) :=
  fun g₁ g₂ h ↦ (map_sectionsHom g₁).symm.trans <| ((by
    rintro _ _ _ _ rfl; rfl : ∀ φ₁ φ₂ h₁ h₂, φ₁ = φ₂ → map φ₁ h₁ = map φ₂ h₂)
    _ _ _ _ h).trans (map_sectionsHom g₂)
@[simp] theorem sectionsHom_id : sectionsHom (𝟙 (Spf A)) = RingHom.id A := by
  rw [← map_id, sectionsHom_map]
@[simp] theorem sectionsHom_comp (f : Spf C ⟶ Spf B) (g : Spf B ⟶ Spf A) :
    sectionsHom (f ≫ g) = (sectionsHom f).comp (sectionsHom g) := by
  conv_lhs => rw [← map_sectionsHom f, ← map_sectionsHom g, ← map_comp, sectionsHom_map]

/-- **Full faithfulness of `Spf`** (EGA I, Ch. I, 10.2.2; Stacks Tag 0AHY, eq. 87.2.0.1):
morphisms of locally ringed spaces `Spf B ⟶ Spf A` correspond bijectively to continuous ring
homomorphisms `A →+* B`. -/
noncomputable def homEquiv : (Spf B ⟶ Spf A) ≃ {φ : A →+* B // Continuous φ} where
  toFun g := ⟨sectionsHom g, continuous_sectionsHom g⟩; invFun φ := map φ.1 φ.2
  left_inv := map_sectionsHom; right_inv φ := Subtype.ext (sectionsHom_map φ.1 φ.2)

@[simp] theorem homEquiv_apply_coe (g : Spf B ⟶ Spf A) :
    (homEquiv g : A →+* B) = sectionsHom g := (rfl)
@[simp] theorem homEquiv_symm_apply (φ : {φ : A →+* B // Continuous φ}) :
    homEquiv.symm φ = map φ.1 φ.2 := (rfl)

/-- The property of a `TopCommRingCat` being a complete separated adic ring of finite ideal type. -/
def isAdicRing : ObjectProperty TopCommRingCat.{u} := fun R ↦ IsAdicRing R
@[simp] theorem isAdicRing_iff (R : TopCommRingCat.{u}) : isAdicRing R ↔ IsAdicRing R := Iff.rfl
instance (R : isAdicRing.{u}.FullSubcategory) : IsAdicRing R.obj := R.property

/-- `Spf` as a contravariant functor from complete separated adic rings of finite ideal type
(`isAdicRing.FullSubcategory`) to locally ringed spaces (EGA I, Ch. I, 10.2.2). -/
@[expose] noncomputable def functor :
    (isAdicRing.{u}.FullSubcategory)ᵒᵖ ⥤ LocallyRingedSpace.{u} where
  obj R := Spf R.unop.obj; map φ := map φ.unop.hom.1 φ.unop.hom.2
  map_id _ := map_id; map_comp _ _ := map_comp _ _ _ _

@[simp] theorem functor_obj (R : (isAdicRing.{u}.FullSubcategory)ᵒᵖ) :
    functor.obj R = Spf R.unop.obj := (rfl)
@[simp] theorem functor_map {R S : (isAdicRing.{u}.FullSubcategory)ᵒᵖ} (φ : R ⟶ S) :
    functor.map φ = map φ.unop.hom.1 φ.unop.hom.2 := (rfl)

/-- `Spf.functor` is fully faithful (EGA I, Ch. I, 10.2.2; Stacks Tag 0AHY). -/
noncomputable def fullyFaithfulFunctor : functor.{u}.FullyFaithful where
  preimage f := (ObjectProperty.homMk (homEquiv (f : Spf _ ⟶ Spf _))).op
  map_preimage f := by change map (sectionsHom (f : Spf _ ⟶ Spf _)) _ = _; exact map_sectionsHom _
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

private theorem continuous_structureSheafMap_sectionsTopology (φ : A →+* B) (hφ : Continuous φ)
    (U : Opens (carrier A)) :
    let hIA := (IsAdicRing.ideal_spec A).2.1; let hIB := (IsAdicRing.ideal_spec B).2.1
    @Continuous _ _ (sectionsTopology hIA U)
      (sectionsTopology hIB ((Opens.map (TopCat.ofHom (comap φ hφ))).obj U))
      ((structureSheafMap φ hφ hIA hIB).hom.app (op U) :
        (structureSheaf hIA).obj.obj (op U) ⟶ _) := by
  intro hIA hIB; let W := (Opens.map (TopCat.ofHom (comap φ hφ))).obj U
  let _ := sectionsTopology hIA U; refine (continuous_iff_sectionsTopology hIB W).mpr fun n ↦ ?_
  obtain ⟨m, hm⟩ := hIA.exists_pow_succ_le_comap (hIB.isOpen_pow (n + 1)) hφ
  let _ : TopologicalSpace ((quotientSheaf (is_ideal_adic_pow hIB n.succ_pos)).obj.obj (op W)) := ⊥
  exact (@Continuous.comp _ _ _ (sectionsTopology hIA U) ⊥ ⊥ _ _ continuous_bot
    (continuous_toQuotientSheaf_app hIA (is_ideal_adic_pow hIA m.succ_pos) U)).congr fun x ↦
      (ConcreteCategory.congr_hom (congrArg (·.hom.app (op U))
        (structureSheafMap_comp_quotientProjection φ hφ hIA hIB _ n hm)) x).symm

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
  have hVcov : basicOpen b ≤ ⨆ i, V i := fun q hqb ↦
    let ⟨a, _, haU⟩ := exists_basicOpen_le (Opens.mem_map.mp (hb hqb))
    Opens.mem_iSup.mpr ⟨⟨a, haU⟩, by
      simp only [V, basicOpen_mul]; exact ⟨hqb, by rwa [← comap_basicOpen φ hφ a]⟩⟩
  let _ := quotientSectionsTopology hIB (basicOpen b)
  let _ (i) := quotientSectionsTopology hIB (V i)
  rw [← quotientSectionsTopology_basicOpen hIB b,
    (quotientSectionsTopology_glue hIB hVle hVcov).isInducing.continuous_iff, continuous_pi_iff]
  intro ⟨a, haU⟩; let _ := sectionsTopology hIA (basicOpen a)
  let _ := sectionsTopology hIB ((Opens.map fBase).obj (basicOpen a))
  have hVφ : V ⟨a, haU⟩ ≤ (Opens.map fBase).obj (basicOpen a) :=
    (le_of_eq (basicOpen_mul _ _)).trans (inf_le_right.trans (comap_basicOpen φ hφ a).ge)
  have hnat : (η.app (op U) : _ ⟶ _) ≫ (structureSheaf hIB).obj.map (homOfLE hb).op ≫
        (structureSheaf hIB).obj.map (homOfLE (hVle ⟨a, haU⟩)).op =
      (structureSheaf hIA).obj.map (homOfLE haU).op ≫ (η.app (op (basicOpen a)) : _ ⟶ _) ≫
        (structureSheaf hIB).obj.map (homOfLE hVφ).op := by
    rw [← (structureSheaf hIB).obj.map_comp, show (homOfLE hb).op ≫ (homOfLE (hVle _)).op =
        ((Opens.map fBase).map (homOfLE haU)).op ≫ (homOfLE hVφ).op from
        Quiver.Hom.unop_inj (Subsingleton.elim _ _), (structureSheaf hIB).obj.map_comp,
      ← Category.assoc]
    exact congrArg (· ≫ _) (η.naturality (homOfLE haU).op).symm
  refine (((quotientSectionsTopology_basicOpen hIB _).symm ▸ sectionsTopology_restrict hIB
    hVφ : @Continuous _ _ (sectionsTopology hIB ((Opens.map fBase).obj (basicOpen a)))
      (quotientSectionsTopology hIB (V ⟨a, haU⟩)) _).comp
    ((continuous_structureSheafMap_sectionsTopology φ hφ (basicOpen a)).comp
      (continuous_restrict_basicOpen_sectionsTopology hIA haU))).congr fun x ↦
    (ConcreteCategory.congr_hom hnat x).symm

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
  exact continuous_structureSheafMap_quotientSectionsTopology _ (continuous_sectionsHom g) U
end HomEquiv
end TauCeti.FormalScheme.Spf
