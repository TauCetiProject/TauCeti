/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.FormalScheme.Spf.StructureSheaf
public import TauCeti.RingTheory.Localization.Away.Quotient

/-!
# Sections of the formal spectrum over basic open sets

Let `A` be a topological ring whose topology is defined by an ideal `I`, and let `f ∈ A`. Over the
basic open set `D(f)` of `Spf A`, the structure sheaf `O_{Spf A} = lim_n O_{I ^ (n + 1)}` has
sections the `I`-adic completion of the localisation `A_f`, the completed localisation
`A_{f}` (EGA I, Ch. I, 10.1.4).

Nothing is completed at a finite level: for an ideal of definition `J`, the sheaf `O_J` is the
structure sheaf of `Spec (A ⧸ J)`, whose sections over `D(f)` are the localisation of `A ⧸ J` away
from the image of `f`, that is `A_f ⧸ J A_f` (`IsLocalization.Away.quotient`). These
identifications are compatible with the reduction maps `O_J → O_K`, so taking sections over `D(f)`
turns the diagram of the thickenings into the diagram `n ↦ A_f ⧸ (I A_f) ^ (n + 1)`, whose limit
is the adic completion (`AdicCompletion.isLimitQuotientPowSuccCone`). Since taking sections
commutes with limits of sheaves, this identifies the sections of `O_{Spf A}` over `D(f)`.

For the chosen ideal of definition of an adic ring `A`, the completion of `A_f` along `I A_f` is
by definition the ring `TauCeti.AdicRing.CompletedAway A f`.

## Main definitions

* `TauCeti.FormalScheme.Spf.quotientSheafBasicOpenIso`: for an ideal of definition `J`, the
  sections of `O_J` over `D(f)` are `A_f ⧸ J A_f`.
* `TauCeti.FormalScheme.Spf.basicOpenSectionsIso`: the sections of `O_{Spf A}` over `D(f)` are the
  `I A_f`-adic completion of `A_f`.

## Main results

* `TauCeti.FormalScheme.Spf.map_quotientInclusion_basicOpen`: the basic open set `D(f)` of `Spf A`
  corresponds to the basic open set of the image of `f` in `Spec (A ⧸ J)`.
* `quotientSheafGlobalSectionsIso_inv_comp_map_comp_quotientSheafBasicOpenIso_hom`,
  `quotientTransition_app_comp_quotientSheafBasicOpenIso_hom`: the
  identification of the sections of `O_J` over `D(f)` sends the restriction of the global section
  `a ∈ A ⧸ J` to the class of `a`, and is compatible with the reduction maps.
* `TauCeti.FormalScheme.Spf.basicOpenSectionsIso_inv_comp_quotientProjection`: under
  `basicOpenSectionsIso`, the projection to the `n`-th thickening is the reduction of the
  completion modulo `(I A_f) ^ (n + 1)`.
* `TauCeti.FormalScheme.Spf.globalSectionsIso_inv_comp_map_comp_basicOpenSectionsIso_hom`: for
  `I`-adically complete `A`, restricting the global section `a ∈ A` to `D(f)` gives the image of
  `a` in the completion of `A_f`.

## References

* A. Grothendieck and J. Dieudonné, *Éléments de géométrie algébrique I*, Ch. I, §10.1 (10.1.4).
* [Stacks Project, Tag 0AHY](https://stacks.math.columbia.edu/tag/0AHY).
-/

public section

universe u

open CategoryTheory Limits TopologicalSpace Opposite AlgebraicGeometry

namespace TauCeti.FormalScheme.Spf

variable {A : Type u} [CommRing A] [TopologicalSpace A] {J K : Ideal A}

/-- For an ideal of definition `J`, the basic open set `D(f)` of `Spf A` corresponds to the basic
open set of the image of `f` in `Spec (A ⧸ J)`. -/
@[simp]
theorem map_quotientInclusion_basicOpen (hJ : IsAdic J) (f : A) :
    (Opens.map (quotientInclusion hJ)).obj (basicOpen f) =
      PrimeSpectrum.basicOpen (Ideal.Quotient.mk J f) := by
  ext q
  rw [Opens.map_coe, Set.mem_preimage, SetLike.mem_coe, mem_basicOpen, quotientInclusion_apply,
    coe_homeomorphSpecQuotient_symm_apply]
  exact (PrimeSpectrum.mem_basicOpen _ _).symm

/-- The sections of `O_J` over `D(f)` are the localisation of `A ⧸ J` away from the image of `f`. -/
instance (hJ : IsAdic J) (f : A) :
    IsLocalization.Away (Ideal.Quotient.mk J f)
      ((quotientSheaf hJ).obj.obj (op (basicOpen f))) := by
  have key : ∀ U, U = PrimeSpectrum.basicOpen (Ideal.Quotient.mk J f) →
      IsLocalization.Away (Ideal.Quotient.mk J f)
        ((Spec.structureSheaf (A ⧸ J)).obj.obj (op U)) := by
    rintro _ rfl
    infer_instance
  exact key _ (map_quotientInclusion_basicOpen hJ f)

/-- For an ideal of definition `J`, the sections over `D(f)` of the structure sheaf `O_J` of
`Spec (A ⧸ J)` are `A_f ⧸ J A_f`, as localisations of `A ⧸ J` away from the image of `f`. -/
noncomputable def quotientSheafBasicOpenIso (hJ : IsAdic J) (f : A) :
    (quotientSheaf hJ).obj.obj (op (basicOpen f)) ≅
      CommRingCat.of (Localization.Away f ⧸ J.map (algebraMap A (Localization.Away f))) :=
  (IsLocalization.algEquiv (Submonoid.powers (Ideal.Quotient.mk J f))
    ((quotientSheaf hJ).obj.obj (op (basicOpen f)))
    (Localization.Away f ⧸ J.map (algebraMap A (Localization.Away f)))
    ).toRingEquiv.toCommRingCatIso

/-- The identification of the sections of `O_J` over `D(f)` with `A_f ⧸ J A_f` sends the
restriction of the global section `a ∈ A ⧸ J` to the class of `a`. -/
@[reassoc]
theorem quotientSheafGlobalSectionsIso_inv_comp_map_comp_quotientSheafBasicOpenIso_hom
    (hJ : IsAdic J) (f : A) :
    (quotientSheafGlobalSectionsIso hJ).inv ≫ (quotientSheaf hJ).obj.map (homOfLE le_top).op ≫
        (quotientSheafBasicOpenIso hJ f).hom =
      CommRingCat.ofHom (algebraMap (A ⧸ J)
        (Localization.Away f ⧸ J.map (algebraMap A (Localization.Away f)))) := by
  rw [quotientSheafGlobalSectionsIso_inv, algebraMap_comp_quotientSheaf_map_assoc]
  ext x
  exact (IsLocalization.algEquiv (Submonoid.powers (Ideal.Quotient.mk J f))
    ((quotientSheaf hJ).obj.obj (op (basicOpen f)))
    (Localization.Away f ⧸ J.map (algebraMap A (Localization.Away f)))).commutes x

/-- Homomorphisms out of the sections of `O_J` over `D(f)` are determined by their values on the
restrictions of global sections, since these sections are a localisation of `A ⧸ J`. -/
private theorem quotientSheaf_basicOpen_hom_ext (hJ : IsAdic J) (f : A) {X : CommRingCat.{u}}
    {g h : (quotientSheaf hJ).obj.obj (op (basicOpen f)) ⟶ X}
    (H : (quotientSheafGlobalSectionsIso hJ).inv ≫ (quotientSheaf hJ).obj.map (homOfLE le_top).op ≫
        g = (quotientSheafGlobalSectionsIso hJ).inv ≫
          (quotientSheaf hJ).obj.map (homOfLE le_top).op ≫ h) :
    g = h := by
  rw [quotientSheafGlobalSectionsIso_inv, algebraMap_comp_quotientSheaf_map_assoc,
    algebraMap_comp_quotientSheaf_map_assoc] at H
  exact CommRingCat.hom_ext <| IsLocalization.ringHom_ext
    (Submonoid.powers (Ideal.Quotient.mk J f)) (CommRingCat.hom_ext_iff.mp H)

/-- For ideals of definition `J ≤ K`, the identifications of the sections over `D(f)` with
`A_f ⧸ J A_f` and `A_f ⧸ K A_f` carry the reduction map `O_J → O_K` to the quotient map. -/
@[reassoc]
theorem quotientTransition_app_comp_quotientSheafBasicOpenIso_hom (hJ : IsAdic J) (hK : IsAdic K)
    (hJK : J ≤ K) (f : A) :
    (quotientTransition hJ hK hJK).hom.app (op (basicOpen f)) ≫
        (quotientSheafBasicOpenIso hK f).hom =
      (quotientSheafBasicOpenIso hJ f).hom ≫
        CommRingCat.ofHom (Ideal.Quotient.factor (Ideal.map_mono hJK)) := by
  apply quotientSheaf_basicOpen_hom_ext hJ f
  rw [(quotientTransition hJ hK hJK).hom.naturality_assoc,
    quotientSheafGlobalSectionsIso_inv_comp_quotientTransition_assoc,
    quotientSheafGlobalSectionsIso_inv_comp_map_comp_quotientSheafBasicOpenIso_hom,
    quotientSheafGlobalSectionsIso_inv_comp_map_comp_quotientSheafBasicOpenIso_hom_assoc]
  ext a
  simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.comp_apply,
    Ideal.Quotient.algebraMap_quotient_map_quotient, Ideal.Quotient.factor_mk]

section StructureSheaf

variable [IsTopologicalRing A] {I : Ideal A}

/-- The sections over `D(f)` of the `n`-th thickening are `A_f ⧸ (I A_f) ^ (n + 1)`. -/
private noncomputable def levelIso (hI : IsAdic I) (f : A) (n : ℕ) :
    (quotientSheaf (is_ideal_adic_pow hI n.succ_pos)).obj.obj (op (basicOpen f)) ≅
      CommRingCat.of (Localization.Away f ⧸ I.map (algebraMap A (Localization.Away f)) ^ (n + 1)) :=
  quotientSheafBasicOpenIso (is_ideal_adic_pow hI n.succ_pos) f ≪≫
    (Ideal.quotEquivOfEq (Ideal.map_pow _ _ _)).toCommRingCatIso

/-- The isomorphisms `levelIso` are compatible with the reduction maps. -/
private theorem quotientTransition_app_comp_levelIso_hom (hI : IsAdic I) (f : A) {m n : ℕ}
    (h : m ≤ n) :
    (quotientTransition (is_ideal_adic_pow hI n.succ_pos) (is_ideal_adic_pow hI m.succ_pos)
        (Ideal.pow_le_pow_right (Nat.succ_le_succ h))).hom.app (op (basicOpen f)) ≫
        (levelIso hI f m).hom =
      (levelIso hI f n).hom ≫ CommRingCat.ofHom
        (Ideal.Quotient.factor (Ideal.pow_le_pow_right (Nat.succ_le_succ h))) := by
  rw [levelIso, levelIso, Iso.trans_hom, Iso.trans_hom,
    quotientTransition_app_comp_quotientSheafBasicOpenIso_hom_assoc, Category.assoc]
  congr 1
  ext x
  simp

/-- On sections over `D(f)`, the diagram of the thickenings is the diagram of the quotients of
`A_f` by the powers of `I A_f`. -/
private noncomputable def quotientDiagramBasicOpenIso (hI : IsAdic I) (f : A) :
    quotientDiagram hI ⋙ sheafToPresheaf _ CommRingCat ⋙
        (evaluation _ CommRingCat).obj (op (basicOpen f)) ≅
      Ideal.quotientPowSuccDiagram (I.map (algebraMap A (Localization.Away f))) :=
  NatIso.ofComponents (fun n ↦ levelIso hI f n.unop)
    fun g ↦ quotientTransition_app_comp_levelIso_hom hI f (leOfHom g.unop)

/-- The sections over the basic open set `D(f)` of the structure sheaf of `Spf A` are the
`I A_f`-adic completion of the localisation `A_f` (EGA I, Ch. I, 10.1.4). -/
noncomputable def basicOpenSectionsIso (hI : IsAdic I) (f : A) :
    (structureSheaf hI).obj.obj (op (basicOpen f)) ≅
      CommRingCat.of (AdicCompletion (I.map (algebraMap A (Localization.Away f)))
        (Localization.Away f)) :=
  sectionsIsoLimit hI (op (basicOpen f)) ≪≫
    HasLimit.isoOfNatIso (quotientDiagramBasicOpenIso hI f) ≪≫
    (limit.isLimit _).conePointUniqueUpToIso (AdicCompletion.isLimitQuotientPowSuccCone _)

/-- Under `basicOpenSectionsIso`, the projection from the sections of `O_{Spf A}` over `D(f)` to
the sections of the `n`-th thickening is the reduction of the completion modulo
`(I A_f) ^ (n + 1)`, followed by the identification of `A_f ⧸ I ^ (n + 1) A_f` with these
sections. -/
@[reassoc (attr := simp)]
theorem basicOpenSectionsIso_inv_comp_quotientProjection (hI : IsAdic I) (f : A) (n : ℕ) :
    (basicOpenSectionsIso hI f).inv ≫ (quotientProjection hI n).hom.app (op (basicOpen f)) =
      CommRingCat.ofHom (AdicCompletion.evalₐ _ (n + 1)).toRingHom ≫
        (Ideal.quotEquivOfEq (Ideal.map_pow _ _ _)).toCommRingCatIso.inv ≫
        (quotientSheafBasicOpenIso (is_ideal_adic_pow hI n.succ_pos) f).inv := by
  have hb := HasLimit.isoOfNatIso_inv_π (quotientDiagramBasicOpenIso hI f) (op n)
  have hc := (limit.isLimit _).conePointUniqueUpToIso_inv_comp
    (AdicCompletion.isLimitQuotientPowSuccCone (I.map (algebraMap A (Localization.Away f)))) (op n)
  -- Unfold the inverse along its three factors, as for `globalSectionsIso`. `erw` is needed
  -- because the coercions of `carrier A` to a topological space in the factors agree only up to
  -- unfolding `TopCat.of`.
  unfold basicOpenSectionsIso
  erw [Iso.trans_inv, Iso.trans_inv, Category.assoc, Category.assoc,
    sectionsIsoLimit_inv_comp_quotientProjection]
  refine (congrArg (_ ≫ ·) hb).trans ?_
  refine (Category.assoc _ _ _).symm.trans ?_
  -- The components of `quotientDiagramBasicOpenIso` are the isomorphisms `levelIso`, whose
  -- inverses are by definition the two displayed factors.
  exact (congrArg (· ≫ _) hc).trans rfl

/-- If `A` is `I`-adically complete, restricting the global section `a ∈ A` of the structure sheaf
of `Spf A` to `D(f)` gives the image of `a` in the completion of `A_f`. -/
@[reassoc (attr := simp)]
theorem globalSectionsIso_inv_comp_map_comp_basicOpenSectionsIso_hom [IsAdicComplete I A]
    (hI : IsAdic I) (f : A) :
    (globalSectionsIso hI).inv ≫ (structureSheaf hI).obj.map (homOfLE le_top).op ≫
        (basicOpenSectionsIso hI f).hom =
      CommRingCat.ofHom (algebraMap A (AdicCompletion (I.map (algebraMap A (Localization.Away f)))
        (Localization.Away f))) := by
  rw [← Category.assoc, ← Iso.eq_comp_inv]
  refine structureSheaf.sections_hom_ext hI fun n ↦ ?_
  rw [Category.assoc, (quotientProjection hI n).hom.naturality,
    globalSectionsIso_inv_comp_quotientProjection_assoc, Category.assoc,
    basicOpenSectionsIso_inv_comp_quotientProjection]
  simp only [← Category.assoc]
  rw [Iso.eq_comp_inv, Category.assoc, Category.assoc,
    quotientSheafGlobalSectionsIso_inv_comp_map_comp_quotientSheafBasicOpenIso_hom]
  ext a
  simp [← Ideal.Quotient.mk_algebraMap]

end StructureSheaf

end TauCeti.FormalScheme.Spf
