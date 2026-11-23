/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Points.Equalizer
public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Points.Order
public import TauCeti.GroupTheory.FixedSubgroup

/-!
# Fixed-point closed subgroup schemes of affine group schemes

For a commutative Hopf algebra `H` over `R` and endomorphisms `f : ι → (H ⟶ H)`, the Hopf ideal
`fixedPointsHopfIdeal f := ⨆ i, equalizerHopfIdeal (f i) (𝟙 H)` defines the coordinate Hopf algebra
`fixedPoints f := H ⧸ fixedPointsHopfIdeal f` of `(Spec H)^f`, whose `A`-points are
`{ g | ∀ i, BialgHom.mapDomain (f i).hom g = g }`.

## Main declarations

* `TauCeti.CommHopfAlgCat.fixedPointsHopfIdeal`, `fixedPoints`, `mkFixedPoints`, `liftFixedPoints`:
  fixed-point Hopf ideal, coordinate Hopf algebra, quotient morphism, and coequalizer lift.
* `TauCeti.CommHopfAlgCat.fixedPointsIsoOfEqId`, `fixedPointsIsoOfEqOne`: canonical isomorphisms
  `fixedPoints f ≅ H` for identity families and trivial monoid actions.
* `TauCeti.CommHopfAlgCat.range_mapDomain_mkFixedPoints`, `fixedPointsMulEquiv`: `A`-points of
  `fixedPoints f` as the subgroup of `f`-fixed `A`-points of `H`.
* `TauCeti.FiniteTypeCommHopfAlgCat.fixedPoints`, `mkFixedPoints`, `liftFixedPoints`,
  `fixedPointsIsoOfEqId`, `fixedPointsIsoOfEqOne`, `fixedPointsMulEquiv`: finite-type counterparts.

## References

* J. S. Milne, *Algebraic Groups*, Cambridge University Press, 2017, §1.h.
* B. Edixhoven, *Néron models and tame ramification*, Compositio Math. 81 (1992), §3, pp. 293–295.
-/

public section

open _root_.CommHopfAlgCat _root_.CommHopfAlgCat.Hom CategoryTheory WithConv

namespace TauCeti

universe u v w w'

namespace CommHopfAlgCat

variable {R : Type u} [CommRing R]

section Algebraic

variable {H K : _root_.CommHopfAlgCat.{v} R} {ι : Type w}

/-- The **fixed-point Hopf ideal** `⨆ i, equalizerHopfIdeal (f i) (𝟙 H)` of `f : ι → (H ⟶ H)`. -/
noncomputable def fixedPointsHopfIdeal (f : ι → (H ⟶ H)) : HopfIdeal R H :=
  ⨆ i, equalizerHopfIdeal (f i) (𝟙 H)

/-- Explicit `iSup` presentation of `fixedPointsHopfIdeal f`. -/
theorem fixedPointsHopfIdeal_def (f : ι → (H ⟶ H)) :
    fixedPointsHopfIdeal f = ⨆ i, equalizerHopfIdeal (f i) (𝟙 H) := by rfl

/-- `(fixedPointsHopfIdeal f).toIdeal` is the supremum of the displacement ideals. -/
@[simp]
theorem fixedPointsHopfIdeal_toIdeal (f : ι → (H ⟶ H)) :
    (fixedPointsHopfIdeal f).toIdeal =
      ⨆ i, Ideal.span (Set.range fun a : H ↦ (f i).hom a - a) := by
  rw [fixedPointsHopfIdeal_def, HopfIdeal.iSup_toIdeal]; congr 1; ext i : 1
  rw [equalizerHopfIdeal_toIdeal, HopfIdeal.equalizerIdeal_eq_span]; rfl

/-- Every displacement `(f i).hom a - a` lies in `fixedPointsHopfIdeal f`. -/
theorem sub_mem_fixedPointsHopfIdeal (f : ι → (H ⟶ H)) (i : ι) (a : H) :
    (f i).hom a - a ∈ fixedPointsHopfIdeal f := by
  have hmem := sub_mem_equalizerHopfIdeal (f i) (𝟙 H) a
  rw [TauCeti.CommHopfAlgCat.hom_id_eq_bialgHom_id, BialgHom.id_apply] at hmem
  exact (le_sSup (Set.mem_range_self (f := fun j ↦ equalizerHopfIdeal (f j) (𝟙 H)) i)) hmem

/-- Universal property of `fixedPointsHopfIdeal` among Hopf ideals of `H`. -/
@[simp]
theorem fixedPointsHopfIdeal_le_iff {f : ι → (H ⟶ H)} {J : HopfIdeal R H} :
    fixedPointsHopfIdeal f ≤ J ↔ ∀ i a, (f i).hom a - a ∈ J := by
  simp [fixedPointsHopfIdeal_def, iSup, sSup_le_iff, equalizerHopfIdeal_le_iff]

/-- `φ : H →+* A` kills `fixedPointsHopfIdeal f` iff it equalizes every `f i` with `𝟙 H`. -/
theorem fixedPointsHopfIdeal_le_ker_iff {A : Type*} [Ring A] (f : ι → (H ⟶ H)) (φ : H →+* A) :
    (fixedPointsHopfIdeal f).toIdeal ≤ RingHom.ker φ ↔ ∀ i a, φ ((f i).hom a) = φ a := by
  rw [fixedPointsHopfIdeal_def, HopfIdeal.iSup_toIdeal, iSup_le_iff]
  exact forall_congr' fun i ↦ equalizerHopfIdeal_le_ker_iff (f i) (𝟙 H) φ

/-- `p : H ⟶ K` kills `fixedPointsHopfIdeal f` iff `∀ i, f i ≫ p = p`. -/
theorem fixedPointsHopfIdeal_toIdeal_le_ker_iff (f : ι → (H ⟶ H)) (p : H ⟶ K) :
    (fixedPointsHopfIdeal f).toIdeal ≤ RingHom.ker p.hom.toAlgHom.toRingHom ↔
      ∀ i, f i ≫ p = p := by
  rw [fixedPointsHopfIdeal_def, HopfIdeal.iSup_toIdeal, iSup_le_iff]
  exact forall_congr' fun i ↦ by rw [equalizerHopfIdeal_toIdeal_le_ker_iff, Category.id_comp]

/-- `fixedPointsHopfIdeal f` vanishes iff every `f i` is `𝟙 H`. -/
@[simp]
theorem fixedPointsHopfIdeal_eq_bot_iff (f : ι → (H ⟶ H)) :
    fixedPointsHopfIdeal f = ⊥ ↔ ∀ i, f i = 𝟙 H := by
  rw [← le_bot_iff, fixedPointsHopfIdeal_def, iSup, sSup_le_iff]
  simp [le_bot_iff, equalizerHopfIdeal_eq_bot_iff]

/-- The coordinate commutative Hopf algebra `H ⧸ fixedPointsHopfIdeal f` of `(Spec H)^f`. -/
noncomputable abbrev fixedPoints (f : ι → (H ⟶ H)) : _root_.CommHopfAlgCat.{v} R :=
  quotient H (fixedPointsHopfIdeal f)

/-- The quotient morphism `H ⟶ fixedPoints f` representing `(Spec H)^f ↪ Spec H`. -/
noncomputable abbrev mkFixedPoints (f : ι → (H ⟶ H)) : H ⟶ fixedPoints f :=
  mkQuotient H (fixedPointsHopfIdeal f)

/-- The quotient morphism onto `fixedPoints f` is surjective. -/
theorem mkFixedPoints_surjective (f : ι → (H ⟶ H)) :
    Function.Surjective ⇑(mkFixedPoints f).hom :=
  mkQuotient_surjective H (fixedPointsHopfIdeal f)

/-- Each endomorphism `f i` is coequalized with the identity by `mkFixedPoints f`. -/
@[reassoc]
theorem comp_mkFixedPoints (f : ι → (H ⟶ H)) (i : ι) :
    f i ≫ mkFixedPoints f = mkFixedPoints f :=
  ((fixedPointsHopfIdeal_toIdeal_le_ker_iff f (mkFixedPoints f)).1
    (mkQuotient_ker H (fixedPointsHopfIdeal f)).ge) i

/-- **Coequalizer universal property** of `fixedPoints f`. -/
noncomputable def liftFixedPoints {f : ι → (H ⟶ H)} (p : H ⟶ K) (hp : ∀ i, f i ≫ p = p) :
    fixedPoints f ⟶ K :=
  liftQuotient (fixedPointsHopfIdeal f) p ((fixedPointsHopfIdeal_toIdeal_le_ker_iff f p).2 hp)

/-- `liftFixedPoints p hp` restricts along `mkFixedPoints f` to `p`. -/
@[reassoc (attr := simp)]
theorem mkFixedPoints_comp_liftFixedPoints {f : ι → (H ⟶ H)} (p : H ⟶ K)
    (hp : ∀ i, f i ≫ p = p) : mkFixedPoints f ≫ liftFixedPoints p hp = p :=
  mkQuotient_comp_liftQuotient _ _ _

/-- `liftFixedPoints p hp` is the unique morphism out of `fixedPoints f` restricting to `p`. -/
theorem liftFixedPoints_unique {f : ι → (H ⟶ H)} (p : H ⟶ K) (hp : ∀ i, f i ≫ p = p)
    (q : fixedPoints f ⟶ K) (hq : mkFixedPoints f ≫ q = p) : q = liftFixedPoints p hp :=
  liftQuotient_unique _ _ _ q hq

/-- When every `f i = 𝟙 H`, `fixedPoints f` is canonically isomorphic to `H`. -/
noncomputable def fixedPointsIsoOfEqId {f : ι → (H ⟶ H)} (hf : ∀ i, f i = 𝟙 H) :
    fixedPoints f ≅ H :=
  eqToIso (congrArg (quotient H) ((fixedPointsHopfIdeal_eq_bot_iff f).2 hf)) ≪≫ quotientBotIso H

/-- Composing `mkFixedPoints f` with `(fixedPointsIsoOfEqId hf).hom` is `𝟙 H`. -/
@[reassoc (attr := simp)]
theorem mkFixedPoints_comp_fixedPointsIsoOfEqId_hom {f : ι → (H ⟶ H)} (hf : ∀ i, f i = 𝟙 H) :
    mkFixedPoints f ≫ (fixedPointsIsoOfEqId hf).hom = 𝟙 H := by
  rw [fixedPointsIsoOfEqId, Iso.trans_hom, eqToIso.hom, ← Category.assoc,
    mkQuotient_comp_eqToHom ((fixedPointsHopfIdeal_eq_bot_iff f).2 hf).symm,
    ← quotientBotIso_inv, Iso.inv_hom_id]

/-- The inverse of `fixedPointsIsoOfEqId hf` is `mkFixedPoints f`. -/
@[simp]
theorem fixedPointsIsoOfEqId_inv {f : ι → (H ⟶ H)} (hf : ∀ i, f i = 𝟙 H) :
    (fixedPointsIsoOfEqId hf).inv = mkFixedPoints f := by
  rw [← cancel_mono (fixedPointsIsoOfEqId hf).hom, Iso.inv_hom_id,
    mkFixedPoints_comp_fixedPointsIsoOfEqId_hom]

/-- For the trivial action `ρ = 1`, `fixedPoints (fun θ ↦ (ρ θ).asIso.hom)` is isomorphic to `H`. -/
noncomputable def fixedPointsIsoOfEqOne {Θ : Type w} [MulOneClass Θ] {ρ : Θ →* Aut H}
    (hρ : ρ = 1) : fixedPoints (fun θ ↦ (ρ θ).asIso.hom) ≅ H :=
  fixedPointsIsoOfEqId fun θ ↦ by simp [hρ]

/-- Composing `mkFixedPoints` with `(fixedPointsIsoOfEqOne hρ).hom` is `𝟙 H`. -/
@[reassoc (attr := simp)]
theorem mkFixedPoints_comp_fixedPointsIsoOfEqOne_hom {Θ : Type w} [MulOneClass Θ]
    {ρ : Θ →* Aut H} (hρ : ρ = 1) :
    mkFixedPoints (fun θ ↦ (ρ θ).asIso.hom) ≫ (fixedPointsIsoOfEqOne hρ).hom = 𝟙 H := by
  rw [fixedPointsIsoOfEqOne, mkFixedPoints_comp_fixedPointsIsoOfEqId_hom]

/-- The inverse of `fixedPointsIsoOfEqOne hρ` is `mkFixedPoints`. -/
@[simp]
theorem fixedPointsIsoOfEqOne_inv {Θ : Type w} [MulOneClass Θ] {ρ : Θ →* Aut H} (hρ : ρ = 1) :
    (fixedPointsIsoOfEqOne hρ).inv = mkFixedPoints (fun θ ↦ (ρ θ).asIso.hom) := by
  rw [fixedPointsIsoOfEqOne, fixedPointsIsoOfEqId_inv]

end Algebraic

section Points

variable {H : _root_.CommHopfAlgCat.{v} R} {ι : Type w}

/-- On `A`-points, `fixedPointsHopfIdeal f` cuts out the locus fixed by every `(f i).hom`. -/
theorem mem_quotientPointsSubgroup_fixedPointsHopfIdeal_iff (f : ι → (H ⟶ H))
    (A : CommAlgCat.{w'} R) (x : HopfAlgebra.points (R := R) (H := H) A) :
    x ∈ quotientPointsSubgroup H (fixedPointsHopfIdeal f) A ↔
      ∀ i, BialgHom.mapDomain (f i).hom x = x := by
  rw [fixedPointsHopfIdeal_def, quotientPointsSubgroup_iSup, Subgroup.mem_iInf]
  exact forall_congr' fun i ↦ by
    rw [mem_quotientPointsSubgroup_equalizerHopfIdeal_iff,
      TauCeti.CommHopfAlgCat.hom_id_eq_bialgHom_id, BialgHom.mapDomain_id, MonoidHom.id_apply]

section PointsAlgebra

variable (f : ι → (H ⟶ H)) (A : Type w') [CommRing A] [Algebra R A]

/-- As subgroups of `H(A)`, the range of `mkFixedPoints f` is `⨅ i, fixedSubgroup ...`. -/
theorem range_mapDomain_mkFixedPoints_subgroup :
    (BialgHom.mapDomain (A := A) (mkFixedPoints f).hom).range =
      ⨅ i, fixedSubgroup (BialgHom.mapDomain (A := A) (f i).hom) := by
  rw [← quotientPointsHom_hom (fixedPointsHopfIdeal f) (CommAlgCat.of R A),
    ← quotientPointsSubgroup]
  ext g; rw [mem_quotientPointsSubgroup_fixedPointsHopfIdeal_iff, Subgroup.mem_iInf]
  simp only [mem_fixedSubgroup]

/-- The image of the `A`-points of `fixedPoints f` in `H(A)` is the set of `f`-fixed points. -/
theorem range_mapDomain_mkFixedPoints :
    Set.range (BialgHom.mapDomain (A := A) (mkFixedPoints f).hom) =
      {g | ∀ i, BialgHom.mapDomain (A := A) (f i).hom g = g} := by
  rw [← MonoidHom.coe_range, range_mapDomain_mkFixedPoints_subgroup]
  ext g; simp [mem_fixedSubgroup]

/-- The group of `A`-points of `fixedPoints f` is isomorphic to the subgroup of `f`-fixed points. -/
noncomputable def fixedPointsMulEquiv :
    WithConv ((fixedPoints f : Type v) →ₐ[R] A) ≃*
      ↥(⨅ i, fixedSubgroup (BialgHom.mapDomain (A := A) (f i).hom)) :=
  (MonoidHom.ofInjective (BialgHom.mapDomain_injective_of_surjective (A := A)
    (mkFixedPoints f).hom (mkFixedPoints_surjective f))).trans
    (MulEquiv.subgroupCongr (range_mapDomain_mkFixedPoints_subgroup f A))

/-- `fixedPointsMulEquiv` embeds `A`-points by precomposition with `mkFixedPoints f`. -/
@[simp]
theorem coe_fixedPointsMulEquiv (x : WithConv ((fixedPoints f : Type v) →ₐ[R] A)) :
    (fixedPointsMulEquiv f A x : WithConv (H →ₐ[R] A)) =
      BialgHom.mapDomain (A := A) (mkFixedPoints f).hom x := by
  rw [fixedPointsMulEquiv, MulEquiv.coe_trans, Function.comp_apply, MulEquiv.subgroupCongr_apply,
    MonoidHom.ofInjective_apply]

/-- Precomposing `(fixedPointsMulEquiv f A).symm g` with `mkFixedPoints f` recovers `g`. -/
theorem mapDomain_mkFixedPoints_fixedPointsMulEquiv_symm
    (g : ↥(⨅ i, fixedSubgroup (BialgHom.mapDomain (A := A) (f i).hom))) :
    BialgHom.mapDomain (A := A) (mkFixedPoints f).hom ((fixedPointsMulEquiv f A).symm g) = g := by
  rw [← coe_fixedPointsMulEquiv, MulEquiv.apply_symm_apply]

/-- `simp`-normal form of `mapDomain_mkFixedPoints_fixedPointsMulEquiv_symm` after `mapDomain`. -/
@[simp]
theorem fixedPointsMulEquiv_symm_ofConv_comp_mkₐ
    (g : ↥(⨅ i, fixedSubgroup (BialgHom.mapDomain (A := A) (f i).hom))) :
    (((fixedPointsMulEquiv f A).symm g).ofConv).comp
        (Ideal.Quotient.mkₐ R (fixedPointsHopfIdeal f).toIdeal) = g.val.ofConv := by
  simpa using congrArg WithConv.ofConv (mapDomain_mkFixedPoints_fixedPointsMulEquiv_symm f A g)

/-- Evaluating `(fixedPointsMulEquiv f A).symm g` on `Ideal.Quotient.mk _ a` gives `g.1 a`. -/
@[simp]
theorem fixedPointsMulEquiv_symm_ofConv_mk
    (g : ↥(⨅ i, fixedSubgroup (BialgHom.mapDomain (A := A) (f i).hom))) (a : H) :
    (((fixedPointsMulEquiv f A).symm g).ofConv)
        (Ideal.Quotient.mk (fixedPointsHopfIdeal f).toIdeal a) = g.val.ofConv a :=
  AlgHom.congr_fun (fixedPointsMulEquiv_symm_ofConv_comp_mkₐ f A g) a

/-- Evaluating `(fixedPointsMulEquiv f A).symm g` on `(mkFixedPoints f).hom a` gives `g.1 a`. -/
theorem fixedPointsMulEquiv_symm_ofConv_mkFixedPoints
    (g : ↥(⨅ i, fixedSubgroup (BialgHom.mapDomain (A := A) (f i).hom))) (a : H) :
    (((fixedPointsMulEquiv f A).symm g).ofConv) ((mkFixedPoints f).hom a) = g.val.ofConv a :=
  fixedPointsMulEquiv_symm_ofConv_mk f A g a

end PointsAlgebra

end Points

end CommHopfAlgCat

namespace FiniteTypeCommHopfAlgCat

variable {R : Type u} [CommRing R] {H K : FiniteTypeCommHopfAlgCat.{u, v} R} {ι : Type w}

/-- The fixed-point Hopf ideal of `f : ι → (H ⟶ H)` in `FiniteTypeCommHopfAlgCat R`. -/
noncomputable abbrev fixedPointsHopfIdeal (f : ι → (H ⟶ H)) : HopfIdeal R H :=
  CommHopfAlgCat.fixedPointsHopfIdeal fun i ↦ (f i).hom

/-- The finite-type coordinate Hopf algebra `H ⧸ fixedPointsHopfIdeal f` of `(Spec H)^f`. -/
noncomputable abbrev fixedPoints (f : ι → (H ⟶ H)) : FiniteTypeCommHopfAlgCat.{u, v} R :=
  quotient H (fixedPointsHopfIdeal f)

/-- The surjective quotient morphism `H ⟶ fixedPoints f` in `FiniteTypeCommHopfAlgCat R`. -/
noncomputable abbrev mkFixedPoints (f : ι → (H ⟶ H)) : H ⟶ fixedPoints f :=
  mkQuotient H (fixedPointsHopfIdeal f)

/-- `mkFixedPoints f` is surjective on underlying coordinate rings. -/
theorem mkFixedPoints_surjective (f : ι → (H ⟶ H)) :
    Function.Surjective (toBialgHom (mkFixedPoints f)) :=
  CommHopfAlgCat.mkQuotient_surjective H.obj (fixedPointsHopfIdeal f)

/-- Each `f i` is coequalized with `𝟙 H` by `mkFixedPoints f`. -/
@[reassoc]
theorem comp_mkFixedPoints (f : ι → (H ⟶ H)) (i : ι) : f i ≫ mkFixedPoints f = mkFixedPoints f := by
  apply ObjectProperty.hom_ext; exact CommHopfAlgCat.comp_mkFixedPoints (fun j ↦ (f j).hom) i

/-- **Coequalizer universal property** of `fixedPoints f` in `FiniteTypeCommHopfAlgCat R`. -/
noncomputable def liftFixedPoints {f : ι → (H ⟶ H)} (p : H ⟶ K) (hp : ∀ i, f i ≫ p = p) :
    fixedPoints f ⟶ K :=
  ObjectProperty.homMk (CommHopfAlgCat.liftFixedPoints p.hom fun i ↦ congrArg (·.hom) (hp i))

/-- `liftFixedPoints p hp` restricts along `mkFixedPoints f` to `p`. -/
@[reassoc (attr := simp)]
theorem mkFixedPoints_comp_liftFixedPoints {f : ι → (H ⟶ H)} (p : H ⟶ K) (hp : ∀ i, f i ≫ p = p) :
    mkFixedPoints f ≫ liftFixedPoints p hp = p := by
  apply ObjectProperty.hom_ext
  exact CommHopfAlgCat.mkFixedPoints_comp_liftFixedPoints p.hom fun i ↦ congrArg (·.hom) (hp i)

/-- `liftFixedPoints p hp` is the unique morphism out of `fixedPoints f` restricting to `p`. -/
theorem liftFixedPoints_unique {f : ι → (H ⟶ H)} (p : H ⟶ K) (hp : ∀ i, f i ≫ p = p)
    (q : fixedPoints f ⟶ K) (hq : mkFixedPoints f ≫ q = p) : q = liftFixedPoints p hp :=
  mkQuotient_hom_ext (hq.trans (mkFixedPoints_comp_liftFixedPoints p hp).symm)

/-- When every `f i = 𝟙 H`, `fixedPoints f ≅ H` in `FiniteTypeCommHopfAlgCat R`. -/
noncomputable def fixedPointsIsoOfEqId {f : ι → (H ⟶ H)} (hf : ∀ i, f i = 𝟙 H) :
    fixedPoints f ≅ H :=
  eqToIso (congrArg (quotient H) ((CommHopfAlgCat.fixedPointsHopfIdeal_eq_bot_iff
    (fun i ↦ (f i).hom)).2 fun i ↦ congrArg (·.hom) (hf i))) ≪≫ quotientBotIso H

/-- Composing `mkFixedPoints f` with `(fixedPointsIsoOfEqId hf).hom` is `𝟙 H`. -/
@[reassoc (attr := simp)]
theorem mkFixedPoints_comp_fixedPointsIsoOfEqId_hom {f : ι → (H ⟶ H)} (hf : ∀ i, f i = 𝟙 H) :
    mkFixedPoints f ≫ (fixedPointsIsoOfEqId hf).hom = 𝟙 H := by
  rw [fixedPointsIsoOfEqId, Iso.trans_hom, eqToIso.hom, ← Category.assoc, mkQuotient_comp_eqToHom
    ((CommHopfAlgCat.fixedPointsHopfIdeal_eq_bot_iff _).2 fun i ↦ congrArg (·.hom) (hf i)).symm,
    ← quotientBotIso_inv, Iso.inv_hom_id]

/-- The inverse of `fixedPointsIsoOfEqId hf` is `mkFixedPoints f`. -/
@[simp]
theorem fixedPointsIsoOfEqId_inv {f : ι → (H ⟶ H)} (hf : ∀ i, f i = 𝟙 H) :
    (fixedPointsIsoOfEqId hf).inv = mkFixedPoints f := by
  rw [← cancel_mono (fixedPointsIsoOfEqId hf).hom, Iso.inv_hom_id,
    mkFixedPoints_comp_fixedPointsIsoOfEqId_hom]

section TrivialAction

variable {Θ : Type w} [MulOneClass Θ] {ρ : Θ →* Aut H} (hρ : ρ = 1)

/-- For the trivial action `ρ = 1`, `fixedPoints (fun θ ↦ (ρ θ).asIso.hom) ≅ H`. -/
noncomputable def fixedPointsIsoOfEqOne : fixedPoints (fun θ ↦ (ρ θ).asIso.hom) ≅ H :=
  fixedPointsIsoOfEqId fun θ ↦ by simp [hρ]

/-- Composing `mkFixedPoints` with `(fixedPointsIsoOfEqOne hρ).hom` is `𝟙 H`. -/
@[reassoc (attr := simp)]
theorem mkFixedPoints_comp_fixedPointsIsoOfEqOne_hom :
    mkFixedPoints (fun θ ↦ (ρ θ).asIso.hom) ≫ (fixedPointsIsoOfEqOne hρ).hom = 𝟙 H := by
  rw [fixedPointsIsoOfEqOne, mkFixedPoints_comp_fixedPointsIsoOfEqId_hom]

/-- The inverse of `fixedPointsIsoOfEqOne hρ` is `mkFixedPoints`. -/
@[simp]
theorem fixedPointsIsoOfEqOne_inv :
    (fixedPointsIsoOfEqOne hρ).inv = mkFixedPoints (fun θ ↦ (ρ θ).asIso.hom) := by
  rw [fixedPointsIsoOfEqOne, fixedPointsIsoOfEqId_inv]

end TrivialAction

/-- On `A`-points, `fixedPoints f` represents the `A`-points of `H` fixed by every `f i`. -/
theorem range_mapDomain_mkFixedPoints (f : ι → (H ⟶ H)) (A : Type w') [CommRing A] [Algebra R A] :
    Set.range (BialgHom.mapDomain (A := A) (toBialgHom (mkFixedPoints f))) =
      {g | ∀ i, BialgHom.mapDomain (A := A) (toBialgHom (f i)) g = g} :=
  CommHopfAlgCat.range_mapDomain_mkFixedPoints (fun i ↦ (f i).hom) A

/-- The group of `A`-points of `fixedPoints f` is isomorphic to the subgroup of `f`-fixed points. -/
noncomputable abbrev fixedPointsMulEquiv (f : ι → (H ⟶ H)) (A : Type w')
    [CommRing A] [Algebra R A] :
    WithConv ((fixedPoints f : Type v) →ₐ[R] A) ≃*
      ↥(⨅ i, fixedSubgroup (BialgHom.mapDomain (A := A) (toBialgHom (f i)))) :=
  CommHopfAlgCat.fixedPointsMulEquiv (fun i ↦ (f i).hom) A

end FiniteTypeCommHopfAlgCat

end TauCeti
