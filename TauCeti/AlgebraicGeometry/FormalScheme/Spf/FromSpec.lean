/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.FormalScheme.Spf.Discrete
public import TauCeti.AlgebraicGeometry.FormalScheme.Spf.HomEquiv
public import Mathlib.AlgebraicGeometry.Scheme

import TauCeti.Geometry.RingedSpace.LocallyRingedSpace.Basic

/-!
# Factorization of morphisms from affine schemes into formal spectra

Let `C` be a complete separated adic ring of finite ideal type and `R` a commutative ring. Any
morphism of locally ringed spaces `α : Spec R ⟶ Spf C` induces a ring homomorphism
`fromSpecGlobalMap α : C →+* R` on global sections (`Γ(Spf C) ≅ C` and `R ≅ Γ(Spec R)`).

Equipping `R` with the discrete topology identifies `Spec R` with `Spf R` via `discreteIsoSpec R`,
under which `fromSpecGlobalMap α` is `Spf.sectionsHom ((discreteIsoSpec R).hom ≫ α)`. By automatic
continuity (`Spf.continuous_sectionsHom`) and full faithfulness (`Spf.sectionsHom_injective`), every
finitely generated ideal of definition `I` of `C` has a power `I ^ (m + 1)` contained in
`RingHom.ker (fromSpecGlobalMap α)`, and for any ideal of definition
`K ≤ RingHom.ker (fromSpecGlobalMap α)`, `α` factors as `Spec R ⟶ Spec (C ⧸ K) ⟶ Spf C`
(`specMap_fromSpecLift_comp_fromSpecQuotient`; EGA I, Ch. I, 10.6.2). Consequently, if `α` has an
open-embedding base map (resp. surjective stalk maps), then so does
`Spec.map (CommRingCat.ofHom (fromSpecLift α hK_ker))`.

## Main definitions

* `TauCeti.FormalScheme.Spf.fromSpecGlobalMap`: the ring homomorphism `C →+* R` induced on global
  sections by `α : Spec R ⟶ Spf C`.
* `TauCeti.FormalScheme.Spf.fromSpecLift`: the quotient homomorphism `C ⧸ K →+* R` induced by
  `fromSpecGlobalMap α` whenever `K ≤ RingHom.ker (fromSpecGlobalMap α)`.

## Main results

* `TauCeti.FormalScheme.Spf.asIdeal_base_eq_comap_fromSpecGlobalMap`: on underlying points, `α.base`
  is `PrimeSpectrum.comap (fromSpecGlobalMap α)`.
* `TauCeti.FormalScheme.Spf.exists_pow_le_ker_fromSpecGlobalMap`,
  `TauCeti.FormalScheme.Spf.exists_ideal_pow_le_ker_fromSpecGlobalMap`: for any finitely generated
  ideal of definition `I` of `C`, some power `I ^ (m + 1)` lies in
  `RingHom.ker (fromSpecGlobalMap α)`.
* `TauCeti.FormalScheme.Spf.specMap_fromSpecLift_comp_fromSpecQuotient`: `α` factors through
  `fromSpecQuotient hK : Spec (C ⧸ K) ⟶ Spf C` via `fromSpecLift α hK_ker`.
* `TauCeti.FormalScheme.Spf.isOpenEmbedding_comap_fromSpecLift`: if `α.base` is an open embedding,
  so is `PrimeSpectrum.comap (fromSpecLift α hK_ker)`.
* `TauCeti.FormalScheme.Spf.stalkMap_fromSpecLift_surjective`: if `α` has surjective stalk maps, so
  does `Spec.map (CommRingCat.ofHom (fromSpecLift α hK_ker))`.

## References

* A. Grothendieck and J. Dieudonné, *Éléments de géométrie algébrique I*, Ch. I, §§10.1–10.2,
  10.6.2.
* [Stacks Project, Tag 0AHY](https://stacks.math.columbia.edu/tag/0AHY).
-/

public section

open CategoryTheory TopologicalSpace Opposite AlgebraicGeometry

universe u

namespace TauCeti.FormalScheme.Spf

variable {C R : Type u} [CommRing C] [TopologicalSpace C] [IsTopologicalRing C] [IsAdicRing C]
  [CommRing R]

/-- The ring homomorphism `C →+* R` induced on global sections by a morphism of locally ringed
spaces `α : Spec R ⟶ Spf C`. -/
noncomputable def fromSpecGlobalMap
    (α : Spec.locallyRingedSpaceObj (CommRingCat.of R) ⟶ Spf C) : C →+* R :=
  ((topSectionsIso C).inv ≫
    LocallyRingedSpace.Γ.map α.op ≫
    (asIso (toSpecΓ (CommRingCat.of R))).inv).hom

/-- Applying `toSpecΓ R` to `fromSpecGlobalMap α c` recovers the image of `c` under the
global-sections map of `α`. -/
theorem toSpecΓ_fromSpecGlobalMap
    (α : Spec.locallyRingedSpaceObj (CommRingCat.of R) ⟶ Spf C) (c : C) :
    toSpecΓ (CommRingCat.of R) (fromSpecGlobalMap α c) =
      LocallyRingedSpace.Γ.map α.op ((topSectionsIso C).inv c) :=
  Iso.inv_hom_id_apply (asIso (toSpecΓ (CommRingCat.of R)))
    (LocallyRingedSpace.Γ.map α.op ((topSectionsIso C).inv c))

/-- `fromSpecGlobalMap α` followed by `toSpecΓ R` agrees with the global-sections map of `α` after
`topSectionsIso`. -/
@[reassoc]
theorem ofHom_fromSpecGlobalMap_toSpecΓ
    (α : Spec.locallyRingedSpaceObj (CommRingCat.of R) ⟶ Spf C) :
    CommRingCat.ofHom (fromSpecGlobalMap α) ≫ toSpecΓ (CommRingCat.of R) =
      (topSectionsIso C).inv ≫ LocallyRingedSpace.Γ.map α.op := by
  ext c
  exact toSpecΓ_fromSpecGlobalMap α c

private theorem sectionsHom_discreteIsoSpec_hom_comp [TopologicalSpace R] [DiscreteTopology R]
    (α : Spec.locallyRingedSpaceObj (CommRingCat.of R) ⟶ Spf C) :
    sectionsHom ((discreteIsoSpec R).hom ≫ α) = fromSpecGlobalMap α := by
  have := (IsAdicRing.ideal_spec R).2.2
  ext c
  apply (ConcreteCategory.bijective_of_isIso (toSpecΓ (CommRingCat.of R))).injective
  rw [sectionsHom_apply]
  let x := LocallyRingedSpace.Γ.map α.op ((topSectionsIso C).inv c)
  let s : (Spf R).presheaf.obj (op ⊤) := (discreteIsoSpec R).hom.c.app (op ⊤) x
  have hs : ((discreteIsoSpec R).hom ≫ α).c.app (op ⊤) ((topSectionsIso C).inv c) = s :=
    ConcreteCategory.congr_hom (LocallyRingedSpace.Γ.map_comp α.op (discreteIsoSpec R).hom.op) _
  have hd0 : (topSectionsIso R).inv ≫ (discreteIsoSpec R).inv.c.app (op ⊤) =
      toSpecΓ (CommRingCat.of R) := by
    rw [topSectionsIso_def R]
    exact discreteIsoSpec_inv_globalSections R
  have hd : toSpecΓ (CommRingCat.of R) ((topSectionsIso R).hom s) =
      (discreteIsoSpec R).inv.c.app (op ⊤) ((topSectionsIso R).inv ((topSectionsIso R).hom s)) :=
    (ConcreteCategory.congr_hom hd0 ((topSectionsIso R).hom s)).symm
  have hcancel : (discreteIsoSpec R).inv.c.app (op ⊤) s = x :=
    ConcreteCategory.congr_hom
      (LocallyRingedSpace.iso_hom_c_app_top_comp_inv (discreteIsoSpec R)) x
  exact (congrArg (fun t ↦ toSpecΓ (CommRingCat.of R) ((topSectionsIso R).hom t)) hs).trans <|
    hd.trans <| (congrArg ((discreteIsoSpec R).inv.c.app (op ⊤))
      (Iso.hom_inv_id_apply (topSectionsIso R) s)).trans <|
    hcancel.trans (toSpecΓ_fromSpecGlobalMap α c).symm

/-- On underlying points, any morphism `α : Spec R ⟶ Spf C` acts as preimage of prime ideals along
`fromSpecGlobalMap α`. -/
theorem asIdeal_base_eq_comap_fromSpecGlobalMap
    (α : Spec.locallyRingedSpaceObj (CommRingCat.of R) ⟶ Spf C) (q : PrimeSpectrum R) :
    (α.base q).val.asIdeal = q.asIdeal.comap (fromSpecGlobalMap α) := by
  let _ : TopologicalSpace R := ⊥
  have : DiscreteTopology R := ⟨rfl⟩
  let q₀ : Spec.locallyRingedSpaceObj (CommRingCat.of R) := q
  let x : carrier R := (discreteIsoSpec R).inv.base q₀
  have hx_base : ((discreteIsoSpec R).hom ≫ α).base x = α.base q₀ :=
    congrArg α.base (LocallyRingedSpace.iso_inv_base_hom_base_apply (discreteIsoSpec R) q₀)
  have hx_val : x.val = q := discreteIsoSpec_inv_base_apply R q
  ext c
  rw [← hx_base, mem_base_asIdeal_iff, sectionsHom_discreteIsoSpec_hom_comp, hx_val,
    Ideal.mem_comap]

/-- For any morphism `α : Spec R ⟶ Spf C` and any finitely generated ideal of definition `I` of
`C`, some power `I ^ (m + 1)` lies in the kernel of `fromSpecGlobalMap α`. -/
theorem exists_pow_le_ker_fromSpecGlobalMap
    (α : Spec.locallyRingedSpaceObj (CommRingCat.of R) ⟶ Spf C) {I : Ideal C}
    (hI : IsAdic I) (hIfg : I.FG) :
    ∃ m : ℕ, I ^ (m + 1) ≤ RingHom.ker (fromSpecGlobalMap α) := by
  let ψ := fromSpecGlobalMap α
  have hle_rad : I.map ψ ≤ (⊥ : Ideal R).radical := by
    rw [Ideal.radical_eq_sInf, Ideal.map_le_iff_le_comap]
    intro c hc
    rw [Ideal.mem_comap, Ideal.mem_sInf]
    rintro P ⟨_, hP⟩
    let q : PrimeSpectrum R := ⟨P, hP⟩
    have hc' : c ∈ (α.base q).val.asIdeal :=
      (mem_carrier_iff_le hI).mp (α.base q).property hc
    rwa [asIdeal_base_eq_comap_fromSpecGlobalMap α q, Ideal.mem_comap] at hc'
  obtain ⟨n, hn⟩ := Ideal.exists_pow_le_of_le_radical_of_fg hle_rad (hIfg.map ψ)
  refine ⟨n, ?_⟩
  have hpow : (I.map ψ) ^ (n + 1) = ⊥ :=
    le_bot_iff.mp ((Ideal.pow_le_pow_right (Nat.le_succ n)).trans hn)
  rwa [← Ideal.map_pow, Ideal.map_eq_bot_iff_le_ker] at hpow

/-- Specialization of `exists_pow_le_ker_fromSpecGlobalMap` to `IsAdicRing.ideal C`. -/
theorem exists_ideal_pow_le_ker_fromSpecGlobalMap
    (α : Spec.locallyRingedSpaceObj (CommRingCat.of R) ⟶ Spf C) :
    ∃ m : ℕ, IsAdicRing.ideal C ^ (m + 1) ≤ RingHom.ker (fromSpecGlobalMap α) :=
  exists_pow_le_ker_fromSpecGlobalMap α (IsAdicRing.ideal_spec C).2.1 (IsAdicRing.ideal_spec C).1

/-- The quotient ring homomorphism `C ⧸ K →+* R` induced by `fromSpecGlobalMap α` whenever
`K ≤ RingHom.ker (fromSpecGlobalMap α)`. -/
noncomputable def fromSpecLift
    (α : Spec.locallyRingedSpaceObj (CommRingCat.of R) ⟶ Spf C) {K : Ideal C}
    (hK_ker : K ≤ RingHom.ker (fromSpecGlobalMap α)) : C ⧸ K →+* R :=
  Ideal.Quotient.lift K (fromSpecGlobalMap α) fun _ ha ↦ RingHom.mem_ker.mp (hK_ker ha)

@[simp]
theorem fromSpecLift_mk
    (α : Spec.locallyRingedSpaceObj (CommRingCat.of R) ⟶ Spf C) {K : Ideal C}
    (hK_ker : K ≤ RingHom.ker (fromSpecGlobalMap α)) (c : C) :
    fromSpecLift α hK_ker (Ideal.Quotient.mk K c) = fromSpecGlobalMap α c :=
  (rfl)

@[simp]
theorem comp_mk_fromSpecLift
    (α : Spec.locallyRingedSpaceObj (CommRingCat.of R) ⟶ Spf C) {K : Ideal C}
    (hK_ker : K ≤ RingHom.ker (fromSpecGlobalMap α)) :
    (fromSpecLift α hK_ker).comp (Ideal.Quotient.mk K) = fromSpecGlobalMap α := by
  ext c
  exact fromSpecLift_mk α hK_ker c

/-- **Factorization through thickenings** (EGA I, Ch. I, 10.6.2): for any ideal of definition `K`
of `C` with `K ≤ RingHom.ker (fromSpecGlobalMap α)`, `α : Spec R ⟶ Spf C` factors through
`fromSpecQuotient hK : Spec (C ⧸ K) ⟶ Spf C` via `fromSpecLift α hK_ker`. -/
@[reassoc (attr := simp)]
theorem specMap_fromSpecLift_comp_fromSpecQuotient
    (α : Spec.locallyRingedSpaceObj (CommRingCat.of R) ⟶ Spf C) {K : Ideal C}
    (hK : IsAdic K) (hK_ker : K ≤ RingHom.ker (fromSpecGlobalMap α)) :
    Spec.locallyRingedSpaceMap (CommRingCat.ofHom (fromSpecLift α hK_ker)) ≫
      fromSpecQuotient hK = α := by
  let _ : TopologicalSpace R := ⊥
  have : DiscreteTopology R := ⟨rfl⟩
  have := (IsAdicRing.ideal_spec C).2.2
  let ψbar := fromSpecLift α hK_ker
  let fSpec := Spec.locallyRingedSpaceMap (CommRingCat.ofHom ψbar)
  refine (cancel_epi (discreteIsoSpec R).hom).mp (sectionsHom_injective ?_)
  rw [sectionsHom_discreteIsoSpec_hom_comp (fSpec ≫ fromSpecQuotient hK),
    sectionsHom_discreteIsoSpec_hom_comp α]
  ext c
  apply (ConcreteCategory.bijective_of_isIso (toSpecΓ (CommRingCat.of R))).injective
  rw [toSpecΓ_fromSpecGlobalMap, op_comp, LocallyRingedSpace.Γ.map_comp]
  have hq0 : (topSectionsIso C).inv ≫ LocallyRingedSpace.Γ.map (fromSpecQuotient hK).op =
      CommRingCat.ofHom (Ideal.Quotient.mk K) ≫ toSpecΓ (CommRingCat.of (C ⧸ K)) := by
    rw [topSectionsIso_def C]
    exact globalSectionsIso_inv_comp_fromSpecQuotient hK
  have hq : LocallyRingedSpace.Γ.map (fromSpecQuotient hK).op ((topSectionsIso C).inv c) =
      toSpecΓ (CommRingCat.of (C ⧸ K)) (Ideal.Quotient.mk K c) :=
    ConcreteCategory.congr_hom hq0 c
  have hnat : LocallyRingedSpace.Γ.map fSpec.op
      (toSpecΓ (CommRingCat.of (C ⧸ K)) (Ideal.Quotient.mk K c)) =
      toSpecΓ (CommRingCat.of R) (ψbar (Ideal.Quotient.mk K c)) :=
    ConcreteCategory.congr_hom (Spec_Γ_naturality (CommRingCat.ofHom ψbar)).symm
      (Ideal.Quotient.mk K c)
  exact (ConcreteCategory.comp_apply _ _ _).trans <|
    (congrArg (LocallyRingedSpace.Γ.map fSpec.op) hq).trans <|
    hnat.trans (fromSpecLift_mk α hK_ker c ▸ rfl)

/-- If `α : Spec R ⟶ Spf C` is an open embedding on underlying spaces, then so is the map on prime
spectra induced by `fromSpecLift α hK_ker`. -/
theorem isOpenEmbedding_comap_fromSpecLift
    (α : Spec.locallyRingedSpaceObj (CommRingCat.of R) ⟶ Spf C)
    (hα : Topology.IsOpenEmbedding α.base) {K : Ideal C} (hK : IsAdic K)
    (hK_ker : K ≤ RingHom.ker (fromSpecGlobalMap α)) :
    Topology.IsOpenEmbedding (PrimeSpectrum.comap (fromSpecLift α hK_ker)) := by
  have hfac : (fromSpecQuotient hK).base ∘
      (Spec.locallyRingedSpaceMap (CommRingCat.ofHom (fromSpecLift α hK_ker))).base = α.base :=
    funext fun q ↦ congrArg (fun f ↦ f.base q)
      (specMap_fromSpecLift_comp_fromSpecQuotient α hK hK_ker)
  exact (fromSpecQuotient_isHomeomorph hK).isOpenEmbedding.of_comp _ (hfac.symm ▸ hα)

/-- If `α : Spec R ⟶ Spf C` has surjective stalk maps at all points of `Spec R`, then so does the
scheme morphism `Spec.map (CommRingCat.ofHom (fromSpecLift α hK_ker))`. -/
theorem stalkMap_fromSpecLift_surjective
    (α : Spec.locallyRingedSpaceObj (CommRingCat.of R) ⟶ Spf C)
    (hα_stalk : ∀ q, Function.Surjective (α.stalkMap q)) {K : Ideal C} (hK : IsAdic K)
    (hK_ker : K ≤ RingHom.ker (fromSpecGlobalMap α)) (q : PrimeSpectrum R) :
    Function.Surjective ((Spec.map (CommRingCat.ofHom (fromSpecLift α hK_ker))).stalkMap q) := by
  let fSpec := Spec.locallyRingedSpaceMap (CommRingCat.ofHom (fromSpecLift α hK_ker))
  have hsurj : Function.Surjective ((fSpec ≫ fromSpecQuotient hK).stalkMap q) := by
    rw [specMap_fromSpecLift_comp_fromSpecQuotient]
    exact hα_stalk q
  intro t
  obtain ⟨w, rfl⟩ := hsurj t
  have hcomp := PresheafedSpace.stalkMap.comp fSpec.toHom (fromSpecQuotient hK).toHom q
  exact ⟨(fromSpecQuotient hK).stalkMap (fSpec.base q) w,
    ((ConcreteCategory.congr_hom hcomp w).trans (ConcreteCategory.comp_apply _ _ w)).symm⟩

end TauCeti.FormalScheme.Spf
