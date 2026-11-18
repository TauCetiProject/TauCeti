/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.FormalScheme.Spf.Discrete
public import Mathlib.AlgebraicGeometry.Scheme
import TauCeti.Geometry.RingedSpace.LocallyRingedSpace.ResidueField

/-!
# Factorization of morphisms from affine schemes into formal spectra

Let `C` be a complete separated adic ring of finite ideal type with chosen ideal of definition
`I = IsAdicRing.ideal C`, and let `R` be a commutative ring. Any morphism of locally ringed spaces
`α : Spec R ⟶ Spf C` induces a ring homomorphism `fromSpecGlobalMap α : C →+* R` on global
sections (`Γ(Spf C) ≅ C` and `R ≅ Γ(Spec R)`).

Because every point `α(q) ∈ Spf C` is an open prime containing `I`, the image of `I` in `R` lies in
every prime ideal of `R`, hence in the nilradical of `R`. Since `I` is finitely generated, some
power `I ^ (m + 1)` maps to zero in `R`, yielding a quotient homomorphism
`fromSpecQuotientLift α hm : C ⧸ I ^ (m + 1) →+* R`. Whenever `α` has open-embedding base map (resp.
surjective stalk maps), the induced scheme morphism `Spec R ⟶ Spec (C ⧸ I ^ (m + 1))` inherits an
open-embedding base map (resp. surjective stalk maps).

## Main definitions

* `TauCeti.FormalScheme.Spf.fromSpecGlobalMap`: the ring homomorphism `C →+* R` induced on global
  sections by `α : Spec R ⟶ Spf C`.
* `TauCeti.FormalScheme.Spf.fromSpecQuotientLift`: the induced homomorphism
  `C ⧸ IsAdicRing.ideal C ^ (m + 1) →+* R` once `IsAdicRing.ideal C ^ (m + 1)` lies in the kernel.

## Main results

* `TauCeti.FormalScheme.Spf.asIdeal_base_eq_comap_fromSpecGlobalMap`: on underlying points, `α.base`
  is `PrimeSpectrum.comap (fromSpecGlobalMap α)`.
* `TauCeti.FormalScheme.Spf.exists_ideal_pow_le_ker_fromSpecGlobalMap`: some power
  `IsAdicRing.ideal C ^ (m + 1)` lies in `RingHom.ker (fromSpecGlobalMap α)`.
* `TauCeti.FormalScheme.Spf.isOpenEmbedding_comap_fromSpecQuotientLift`: if `α.base` is an open
  embedding, so is `PrimeSpectrum.comap (fromSpecQuotientLift α hm)`.
* `TauCeti.FormalScheme.Spf.stalkMap_fromSpecQuotientLift_surjective`: if `α` has surjective stalk
  maps, so does `Spec.map (CommRingCat.ofHom (fromSpecQuotientLift α hm))`.

## References

* A. Grothendieck and J. Dieudonné, *Éléments de géométrie algébrique I*, Ch. I, §§10.1–10.2, 10.6.
* [Stacks Project, Tag 0AHY](https://stacks.math.columbia.edu/tag/0AHY).
-/

public section

open CategoryTheory TopologicalSpace Opposite AlgebraicGeometry

universe u

namespace TauCeti.FormalScheme.Spf

/-- The ring homomorphism `C →+* R` induced on global sections by a morphism of locally ringed
spaces `α : Spec R ⟶ Spf C`. -/
noncomputable def fromSpecGlobalMap {C R : Type u} [CommRing C] [TopologicalSpace C]
    [IsTopologicalRing C] [IsAdicRing C] [CommRing R]
    (α : Spec.locallyRingedSpaceObj (CommRingCat.of R) ⟶ Spf C) : C →+* R :=
  have := (IsAdicRing.ideal_spec C).2.2
  ((globalSectionsIso (IsAdicRing.ideal_spec C).2.1).inv ≫
    LocallyRingedSpace.Γ.map α.op ≫
    (asIso (toSpecΓ (CommRingCat.of R))).inv).hom

/-- Applying `toSpecΓ R` to `fromSpecGlobalMap α c` recovers the image of `c` under the
global-sections map of `α`. -/
theorem toSpecΓ_fromSpecGlobalMap {C R : Type u} [CommRing C] [TopologicalSpace C]
    [IsTopologicalRing C] [IsAdicRing C] [CommRing R]
    (α : Spec.locallyRingedSpaceObj (CommRingCat.of R) ⟶ Spf C) (c : C) :
    have := (IsAdicRing.ideal_spec C).2.2
    toSpecΓ (CommRingCat.of R) (fromSpecGlobalMap α c) =
      LocallyRingedSpace.Γ.map α.op
        ((globalSectionsIso (IsAdicRing.ideal_spec C).2.1).inv c) := by
  intro
  exact Iso.inv_hom_id_apply (asIso (toSpecΓ (CommRingCat.of R)))
    (LocallyRingedSpace.Γ.map α.op ((globalSectionsIso (IsAdicRing.ideal_spec C).2.1).inv c))

/-- `fromSpecGlobalMap α` followed by `toSpecΓ R` agrees with the global-sections map of `α` after
`globalSectionsIso`. -/
@[reassoc]
theorem ofHom_fromSpecGlobalMap_toSpecΓ {C R : Type u} [CommRing C] [TopologicalSpace C]
    [IsTopologicalRing C] [IsAdicRing C] [CommRing R]
    (α : Spec.locallyRingedSpaceObj (CommRingCat.of R) ⟶ Spf C) :
    have := (IsAdicRing.ideal_spec C).2.2
    CommRingCat.ofHom (fromSpecGlobalMap α) ≫ toSpecΓ (CommRingCat.of R) =
      (globalSectionsIso (IsAdicRing.ideal_spec C).2.1).inv ≫ LocallyRingedSpace.Γ.map α.op := by
  intro
  ext c
  exact toSpecΓ_fromSpecGlobalMap α c

/-- On underlying points, any morphism `α : Spec R ⟶ Spf C` acts as preimage of prime ideals along
`fromSpecGlobalMap α`. -/
theorem asIdeal_base_eq_comap_fromSpecGlobalMap {C R : Type u} [CommRing C]
    [TopologicalSpace C] [IsTopologicalRing C] [IsAdicRing C] [CommRing R]
    (α : Spec.locallyRingedSpaceObj (CommRingCat.of R) ⟶ Spf C) (q : PrimeSpectrum R) :
    (α.base q).1.asIdeal = q.asIdeal.comap (fromSpecGlobalMap α) := by
  have := (IsAdicRing.ideal_spec C).2.2
  let : TopologicalSpace R := ⊥
  have : DiscreteTopology R := ⟨rfl⟩
  have := (IsAdicRing.ideal_spec R).2.2
  let d := discreteIsoSpec R
  let q₀ : Spec.locallyRingedSpaceObj (CommRingCat.of R) := q
  let x : Spf R := d.inv.base q₀
  have hx_base : (d.hom ≫ α).base x = α.base q₀ :=
    congrArg α.base (LocallyRingedSpace.iso_inv_base_hom_base_apply d q₀)
  have hx_val : x.1 = q := discreteIsoSpec_inv_base_apply R q
  have hsec (c : C) : LocallyRingedSpace.Γ.map (d.hom ≫ α).op
      ((globalSectionsIso (IsAdicRing.ideal_spec C).2.1).inv c) =
      (globalSectionsIso (IsAdicRing.ideal_spec R).2.1).inv (fromSpecGlobalMap α c) := by
    have hd_comp : LocallyRingedSpace.Γ.map (d.hom ≫ α).op ≫
        LocallyRingedSpace.Γ.map d.inv.op = LocallyRingedSpace.Γ.map α.op := by
      rw [← LocallyRingedSpace.Γ.map_comp, ← op_comp, Iso.inv_hom_id_assoc]
    apply (ConcreteCategory.bijective_of_isIso (LocallyRingedSpace.Γ.map d.inv.op)).1
    have h1 := ConcreteCategory.congr_hom hd_comp
      ((globalSectionsIso (IsAdicRing.ideal_spec C).2.1).inv c)
    have h2 : LocallyRingedSpace.Γ.map d.inv.op
        ((globalSectionsIso (IsAdicRing.ideal_spec R).2.1).inv (fromSpecGlobalMap α c)) =
        toSpecΓ (CommRingCat.of R) (fromSpecGlobalMap α c) :=
      ConcreteCategory.congr_hom (discreteIsoSpec_inv_globalSections R) (fromSpecGlobalMap α c)
    exact h1.trans ((toSpecΓ_fromSpecGlobalMap α c).symm.trans h2.symm)
  ext c
  let sC : (Spf C).presheaf.obj (op ⊤) :=
    (globalSectionsIso (IsAdicRing.ideal_spec C).2.1).inv c
  have h1 : c ∈ (α.base q₀).1.asIdeal ↔
      (Spf C).Γevaluation ((d.hom ≫ α).base x) sC = 0 :=
    (Γevaluation_globalSectionsIso_inv_eq_zero_iff (α.base q₀) c).symm.trans
      (Iff.of_eq (congrArg (fun p ↦ (Spf C).Γevaluation p sC = 0) hx_base.symm))
  have hnat : (Spf C).Γevaluation ((d.hom ≫ α).base x) sC = 0 ↔
      (Spf R).Γevaluation x (LocallyRingedSpace.Γ.map (d.hom ≫ α).op sC) = 0 :=
    (LocallyRingedSpace.residueFieldMap_eq_zero_iff (d.hom ≫ α) x _).symm.trans
      (Iff.of_eq (congrArg (· = 0)
        (LocallyRingedSpace.Γevaluation_naturality_apply (d.hom ≫ α) x sC)))
  have hevR : (Spf R).Γevaluation x
      ((globalSectionsIso (IsAdicRing.ideal_spec R).2.1).inv (fromSpecGlobalMap α c)) = 0 ↔
      fromSpecGlobalMap α c ∈ x.1.asIdeal :=
    Γevaluation_globalSectionsIso_inv_eq_zero_iff x (fromSpecGlobalMap α c)
  have h2 : (Spf R).Γevaluation x (LocallyRingedSpace.Γ.map (d.hom ≫ α).op sC) = 0 ↔
      c ∈ q.asIdeal.comap (fromSpecGlobalMap α) :=
    (Iff.of_eq (congrArg (fun t ↦ (Spf R).Γevaluation x t = 0) (hsec c))).trans
      (hevR.trans (by rw [hx_val, Ideal.mem_comap]))
  exact (h1.trans hnat).trans h2

/-- For any morphism `α : Spec R ⟶ Spf C`, some power `IsAdicRing.ideal C ^ (m + 1)` of the chosen
ideal of definition of `C` lies in the kernel of `fromSpecGlobalMap α`. -/
theorem exists_ideal_pow_le_ker_fromSpecGlobalMap {C R : Type u} [CommRing C]
    [TopologicalSpace C] [IsTopologicalRing C] [IsAdicRing C] [CommRing R]
    (α : Spec.locallyRingedSpaceObj (CommRingCat.of R) ⟶ Spf C) :
    ∃ m : ℕ, IsAdicRing.ideal C ^ (m + 1) ≤ RingHom.ker (fromSpecGlobalMap α) := by
  let ψ := fromSpecGlobalMap α
  let I := IsAdicRing.ideal C
  have hIfg : I.FG := (IsAdicRing.ideal_spec C).1
  have hI : IsAdic I := (IsAdicRing.ideal_spec C).2.1
  have hle_rad : I.map ψ ≤ (⊥ : Ideal R).radical := by
    rw [Ideal.radical_eq_sInf, Ideal.map_le_iff_le_comap]
    intro c hc
    rw [Ideal.mem_comap, Ideal.mem_sInf]
    rintro P ⟨_, hP⟩
    let q : PrimeSpectrum R := ⟨P, hP⟩
    have hc' : c ∈ (α.base q).1.asIdeal :=
      (mem_carrier_iff_le hI).mp (α.base q).2 hc
    rwa [asIdeal_base_eq_comap_fromSpecGlobalMap α q, Ideal.mem_comap] at hc'
  obtain ⟨n, hn⟩ := Ideal.exists_pow_le_of_le_radical_of_fg hle_rad (hIfg.map ψ)
  refine ⟨n, ?_⟩
  have hpow : (I.map ψ) ^ (n + 1) = ⊥ :=
    le_bot_iff.mp ((Ideal.pow_le_pow_right (Nat.le_succ n)).trans hn)
  rw [← Ideal.map_pow, Ideal.map_eq_bot_iff_le_ker] at hpow
  exact hpow

/-- The quotient ring homomorphism `C ⧸ IsAdicRing.ideal C ^ (m + 1) →+* R` induced by
`fromSpecGlobalMap α` when `IsAdicRing.ideal C ^ (m + 1)` lies in its kernel. -/
noncomputable def fromSpecQuotientLift {C R : Type u} [CommRing C] [TopologicalSpace C]
    [IsTopologicalRing C] [IsAdicRing C] [CommRing R]
    (α : Spec.locallyRingedSpaceObj (CommRingCat.of R) ⟶ Spf C) {m : ℕ}
    (hm : IsAdicRing.ideal C ^ (m + 1) ≤ RingHom.ker (fromSpecGlobalMap α)) :
    C ⧸ IsAdicRing.ideal C ^ (m + 1) →+* R :=
  Ideal.Quotient.lift (IsAdicRing.ideal C ^ (m + 1)) (fromSpecGlobalMap α)
    fun _ ha ↦ RingHom.mem_ker.mp (hm ha)

@[simp]
theorem fromSpecQuotientLift_mk {C R : Type u} [CommRing C] [TopologicalSpace C]
    [IsTopologicalRing C] [IsAdicRing C] [CommRing R]
    (α : Spec.locallyRingedSpaceObj (CommRingCat.of R) ⟶ Spf C) {m : ℕ}
    (hm : IsAdicRing.ideal C ^ (m + 1) ≤ RingHom.ker (fromSpecGlobalMap α)) (c : C) :
    fromSpecQuotientLift α hm (Ideal.Quotient.mk (IsAdicRing.ideal C ^ (m + 1)) c) =
      fromSpecGlobalMap α c :=
  (rfl)

@[simp]
theorem comp_mk_fromSpecQuotientLift {C R : Type u} [CommRing C] [TopologicalSpace C]
    [IsTopologicalRing C] [IsAdicRing C] [CommRing R]
    (α : Spec.locallyRingedSpaceObj (CommRingCat.of R) ⟶ Spf C) {m : ℕ}
    (hm : IsAdicRing.ideal C ^ (m + 1) ≤ RingHom.ker (fromSpecGlobalMap α)) :
    (fromSpecQuotientLift α hm).comp (Ideal.Quotient.mk (IsAdicRing.ideal C ^ (m + 1))) =
      fromSpecGlobalMap α := by
  ext c
  exact fromSpecQuotientLift_mk α hm c

/-- If `α : Spec R ⟶ Spf C` is an open embedding on underlying spaces, then so is the map on prime
spectra induced by `fromSpecQuotientLift α hm`. -/
theorem isOpenEmbedding_comap_fromSpecQuotientLift {C R : Type u} [CommRing C]
    [TopologicalSpace C] [IsTopologicalRing C] [IsAdicRing C] [CommRing R]
    (α : Spec.locallyRingedSpaceObj (CommRingCat.of R) ⟶ Spf C)
    (hα : Topology.IsOpenEmbedding α.base) {m : ℕ}
    (hm : IsAdicRing.ideal C ^ (m + 1) ≤ RingHom.ker (fromSpecGlobalMap α)) :
    Topology.IsOpenEmbedding (PrimeSpectrum.comap (fromSpecQuotientLift α hm)) := by
  let K := IsAdicRing.ideal C ^ (m + 1)
  have hK : IsAdic K := is_ideal_adic_pow (IsAdicRing.ideal_spec C).2.1 m.succ_pos
  let ψbar := fromSpecQuotientLift α hm
  let qK := fromSpecQuotient hK
  let fSpec : Spec.locallyRingedSpaceObj (CommRingCat.of R) ⟶
      Spec.locallyRingedSpaceObj (CommRingCat.of (C ⧸ K)) :=
    Spec.locallyRingedSpaceMap (CommRingCat.ofHom ψbar)
  have hcomp : qK.base ∘ fSpec.base = α.base := by
    ext q : 1
    let q' : PrimeSpectrum R := q
    apply Subtype.ext
    apply PrimeSpectrum.ext
    have hpts : (qK.base (fSpec.base q)).1 =
        PrimeSpectrum.comap (Ideal.Quotient.mk K) (PrimeSpectrum.comap ψbar q') :=
      (congrArg Subtype.val (fromSpecQuotient_points hK _)).trans
        (coe_homeomorphSpecQuotient_symm_apply hK _)
    refine (congrArg PrimeSpectrum.asIdeal hpts).trans ?_
    refine Eq.trans ?_ (asIdeal_base_eq_comap_fromSpecGlobalMap α q').symm
    ext c
    simp only [PrimeSpectrum.comap_asIdeal, Ideal.mem_comap]
    exact Iff.of_eq (congrArg (· ∈ q'.asIdeal) (fromSpecQuotientLift_mk α hm c))
  have hhomeo : IsHomeomorph qK.base := fromSpecQuotient_isHomeomorph hK
  exact hhomeo.isOpenEmbedding.of_comp _ (hcomp.symm ▸ hα)

private theorem germ_basicOpen_toStalk {C R : Type u} [CommRing C] [TopologicalSpace C]
    [IsTopologicalRing C] [IsAdicRing C] [CommRing R]
    (α : Spec.locallyRingedSpaceObj (CommRingCat.of R) ⟶ Spf C) (q : PrimeSpectrum R)
    (a : C) (hqa : α.base q ∈ basicOpen a) (c : C) :
    let Ua : Opens (Spf C) := basicOpen a
    (Spec.structureSheaf R).presheaf.germ ((Opens.map α.base).obj Ua) q hqa
      (α.c.app (op Ua)
        ((basicOpenSectionsIso (IsAdicRing.ideal_spec C).2.1
          (IsAdicRing.ideal_spec C).1 a).inv
          (algebraMap C (AdicRing.CompletedAway C a) c))) =
      StructureSheaf.toStalk R q (fromSpecGlobalMap α c) := by
  intro Ua
  have := (IsAdicRing.ideal_spec C).2.2
  let hIC := (IsAdicRing.ideal_spec C).2.1
  let hICfg := (IsAdicRing.ideal_spec C).1
  have hres : (basicOpenSectionsIso hIC hICfg a).inv
      (algebraMap C (AdicRing.CompletedAway C a) c) =
      (Spf C).presheaf.map (homOfLE (le_top : Ua ≤ ⊤)).op
        ((globalSectionsIso hIC).inv c) := by
    apply (basicOpenSectionsIso hIC hICfg a).commRingCatIsoToRingEquiv.injective
    have h1 := ConcreteCategory.congr_hom
      (globalSectionsIso_inv_comp_basicOpenSectionsIso_hom hIC hICfg a) c
    exact (Iso.inv_hom_id_apply (basicOpenSectionsIso hIC hICfg a) _).trans h1.symm
  have hnat := ConcreteCategory.congr_hom
    (α.c.naturality (homOfLE (le_top : Ua ≤ ⊤)).op)
    ((globalSectionsIso hIC).inv c)
  rw [hres]
  have hnat' : α.c.app (op Ua)
      ((Spf C).presheaf.map (homOfLE (le_top : Ua ≤ ⊤)).op
        ((globalSectionsIso hIC).inv c)) =
      (Spec.structureSheaf R).presheaf.map
        (homOfLE (le_top : (Opens.map α.base).obj Ua ≤ ⊤)).op
        (LocallyRingedSpace.Γ.map α.op ((globalSectionsIso hIC).inv c)) := hnat
  have hgerm : (Spec.structureSheaf R).presheaf.germ
      ((Opens.map α.base).obj Ua) q hqa
      ((Spec.structureSheaf R).presheaf.map
        (homOfLE (le_top : (Opens.map α.base).obj Ua ≤ ⊤)).op
        (LocallyRingedSpace.Γ.map α.op ((globalSectionsIso hIC).inv c))) =
      (Spec.structureSheaf R).presheaf.germ ⊤ q (Opens.mem_top q)
        (LocallyRingedSpace.Γ.map α.op ((globalSectionsIso hIC).inv c)) :=
    TopCat.Presheaf.germ_res_apply (Spec.structureSheaf R).presheaf
      (homOfLE (le_top : (Opens.map α.base).obj Ua ≤ ⊤)) q hqa _
  rw [hnat']
  exact hgerm.trans (congrArg ((Spec.structureSheaf R).presheaf.germ ⊤ q (Opens.mem_top q))
    (toSpecΓ_fromSpecGlobalMap α c).symm)

private theorem exists_stalk_preimage_completedAway {C R : Type u} [CommRing C]
    [TopologicalSpace C] [IsTopologicalRing C] [IsAdicRing C] [CommRing R]
    (α : Spec.locallyRingedSpaceObj (CommRingCat.of R) ⟶ Spf C) {m : ℕ}
    (hm : IsAdicRing.ideal C ^ (m + 1) ≤ RingHom.ker (fromSpecGlobalMap α))
    (q : PrimeSpectrum R) (a : C) (hqa : α.base q ∈ basicOpen a)
    (w : AdicRing.CompletedAway C a) :
    ∃ z, (Spec.map (CommRingCat.ofHom (fromSpecQuotientLift α hm))).stalkMap q z =
      (Spec.structureSheaf R).presheaf.germ ((Opens.map α.base).obj (basicOpen a)) q hqa
        (α.c.app (op (basicOpen a))
          ((basicOpenSectionsIso (IsAdicRing.ideal_spec C).2.1
            (IsAdicRing.ideal_spec C).1 a).inv w)) := by
  let K := IsAdicRing.ideal C ^ (m + 1)
  let ψbar := fromSpecQuotientLift α hm
  let φ := CommRingCat.ofHom ψbar
  let g₁ : AdicRing.CompletedAway C a →+* (Spec.structureSheaf R).presheaf.stalk q :=
    ((basicOpenSectionsIso (IsAdicRing.ideal_spec C).2.1
      (IsAdicRing.ideal_spec C).1 a).inv ≫ α.c.app (op (basicOpen a)) ≫
      (Spec.structureSheaf R).presheaf.germ ((Opens.map α.base).obj (basicOpen a)) q hqa).hom
  have hg₁_alg (c : C) : g₁ (algebraMap C (AdicRing.CompletedAway C a) c) =
      StructureSheaf.toStalk R q (fromSpecGlobalMap α c) :=
    germ_basicOpen_toStalk α q a hqa c
  have hker : ∀ x ∈ (IsAdicRing.ideal C).map (algebraMap C (AdicRing.CompletedAway C a)) ^ (m + 1),
      g₁ x = 0 := by
    suffices (IsAdicRing.ideal C).map (algebraMap C (AdicRing.CompletedAway C a)) ^ (m + 1) ≤
        RingHom.ker g₁ from fun x hx ↦ RingHom.mem_ker.mp (this hx)
    rw [← Ideal.map_pow, Ideal.map_le_iff_le_comap]
    intro c hc
    rw [Ideal.mem_comap, RingHom.mem_ker, hg₁_alg c, RingHom.mem_ker.mp (hm hc), map_zero]
    rfl
  let abar : C ⧸ K := Ideal.Quotient.mk K a
  let liftG₁ := Ideal.Quotient.lift _ g₁ hker
  let eqv := AdicRing.CompletedAway.quotientPowEquiv C a (m + 1)
  let h₁ : Localization.Away abar →+* (Spec.structureSheaf R).presheaf.stalk q :=
    liftG₁.comp eqv.symm.toRingHom
  let p : PrimeSpectrum (C ⧸ K) := PrimeSpectrum.comap ψbar q
  have hp_mem : abar ∈ p.asIdeal.primeCompl := by
    have ha_notMem : a ∉ (α.base q).1.asIdeal := mem_basicOpen.mp hqa
    rwa [asIdeal_base_eq_comap_fromSpecGlobalMap] at ha_notMem
  let ιLoc : Localization.Away abar →+* (Spec.structureSheaf (C ⧸ K)).presheaf.stalk p :=
    IsLocalization.Away.lift abar
      (IsLocalization.map_units ((Spec.structureSheaf (C ⧸ K)).presheaf.stalk p) ⟨abar, hp_mem⟩)
  have heq : (((Spec.map φ).stalkMap q).hom).comp ιLoc = h₁ := by
    refine IsLocalization.ringHom_ext (Submonoid.powers abar)
      (Ideal.Quotient.ringHom_ext (RingHom.ext fun c ↦ ?_))
    let cbar := Ideal.Quotient.mk K c
    have hq_eq : eqv.symm (algebraMap (C ⧸ K) (Localization.Away abar) cbar) =
        Ideal.Quotient.mk _ (algebraMap C (AdicRing.CompletedAway C a) c) :=
      eqv.injective ((eqv.apply_symm_apply _).trans (eqv.commutes c).symm)
    have he₁ : ((Spec.map φ).stalkMap q).hom
        (ιLoc (algebraMap (C ⧸ K) (Localization.Away abar) cbar)) =
        ((Spec.map φ).stalkMap q).hom (StructureSheaf.toStalk (C ⧸ K) p cbar) :=
      congrArg ((Spec.map φ).stalkMap q).hom (IsLocalization.Away.lift_eq _ _ cbar)
    have he₂ : ((Spec.map φ).stalkMap q).hom (StructureSheaf.toStalk (C ⧸ K) p cbar) =
        StructureSheaf.toStalk R q (fromSpecGlobalMap α c) := stalkMap_toStalk_apply φ q cbar
    have he₃ : g₁ (algebraMap C (AdicRing.CompletedAway C a) c) =
        h₁ (algebraMap (C ⧸ K) (Localization.Away abar) cbar) :=
      (Ideal.Quotient.lift_mk _ g₁ hker).symm.trans (congrArg liftG₁ hq_eq.symm)
    exact he₁.trans (he₂.trans ((hg₁_alg c).symm.trans he₃))
  exact ⟨ιLoc (eqv (Ideal.Quotient.mk _ w)), (RingHom.congr_fun heq _).trans
    ((congrArg liftG₁ (eqv.symm_apply_apply _)).trans (Ideal.Quotient.lift_mk _ g₁ hker))⟩

/-- If `α : Spec R ⟶ Spf C` has surjective stalk maps at all points of `Spec R`, then so does the
scheme morphism `Spec.map (CommRingCat.ofHom (fromSpecQuotientLift α hm))`. -/
theorem stalkMap_fromSpecQuotientLift_surjective {C R : Type u} [CommRing C]
    [TopologicalSpace C] [IsTopologicalRing C] [IsAdicRing C] [CommRing R]
    (α : Spec.locallyRingedSpaceObj (CommRingCat.of R) ⟶ Spf C)
    (hα_stalk : ∀ q, Function.Surjective (α.stalkMap q)) {m : ℕ}
    (hm : IsAdicRing.ideal C ^ (m + 1) ≤ RingHom.ker (fromSpecGlobalMap α))
    (q : PrimeSpectrum R) :
    Function.Surjective
      ((Spec.map (CommRingCat.ofHom (fromSpecQuotientLift α hm))).stalkMap q) := by
  intro t
  obtain ⟨s, rfl⟩ := hα_stalk q t
  obtain ⟨U, hxU, u, rfl⟩ := (Spf C).presheaf.exists_germ_eq s
  obtain ⟨_, ⟨a, rfl⟩, hqa, haU⟩ :=
    (Opens.isBasis_iff_nbhd.mp isBasis_basicOpen) hxU
  let hIC := (IsAdicRing.ideal_spec C).2.1
  let hICfg := (IsAdicRing.ideal_spec C).1
  let w : AdicRing.CompletedAway C a :=
    (basicOpenSectionsIso hIC hICfg a).hom ((Spf C).presheaf.map (homOfLE haU).op u)
  obtain ⟨z, hz⟩ := exists_stalk_preimage_completedAway α hm q a hqa w
  refine ⟨z, hz.trans ?_⟩
  have hgerm : (Spf C).presheaf.germ (basicOpen a) (α.base q) hqa
      ((basicOpenSectionsIso hIC hICfg a).inv w) =
      (Spf C).presheaf.germ U (α.base q) hxU u :=
    (congrArg ((Spf C).presheaf.germ (basicOpen a) (α.base q) hqa)
      (Iso.hom_inv_id_apply (basicOpenSectionsIso hIC hICfg a) _)).trans
      (TopCat.Presheaf.germ_res_apply (Spf C).presheaf (homOfLE haU) (α.base q) hqa u)
  exact (PresheafedSpace.stalkMap_germ_apply α.toHom (basicOpen a) q hqa _).symm.trans
    (congrArg (α.stalkMap q) hgerm)

end TauCeti.FormalScheme.Spf
